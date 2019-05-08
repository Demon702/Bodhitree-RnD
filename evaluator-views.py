"""
Views for evaluate module
"""

from __future__ import absolute_import

import difflib
import json
import os
import tempfile

from bs4 import BeautifulSoup
from celery import group
from django.conf import settings
from django.contrib.auth.decorators import login_required
from django.core.exceptions import PermissionDenied
from django.core.urlresolvers import reverse
from django.http import Http404, HttpResponse, HttpResponseForbidden, HttpResponseNotFound, HttpResponseRedirect
from django.shortcuts import get_object_or_404, render_to_response
from django.template import RequestContext
from django.utils import timezone

from assignments.models import Program as ProgramModel
from assignments.models import Assignment, Testcase
from assignments.views import file_download, isCourseModerator, isEnrolledInCourse
from elearning_academy.celeryapp import app
from evaluate.models import AssignmentResults, TestcaseResult
from evaluate.tasks import evaluate_assignment
from evaluate.utils.checkOutput import CustomTestcase
from evaluate.utils.errorcodes import error_codes, error_msg
from evaluate.utils.evaluator import Evaluate, Results
from upload.models import LatestSubmission, Upload
from utils.archives import read_file


def evaluate(request, submissionID, program_type):
    '''
    Function to evaluate a submission (passed as submissionID).
    Takes as input the request, submission ID, the section type (evaluate or practice)
    '''
    submission = get_object_or_404(Upload, pk=submissionID)
    assignment = submission.assignment
    # Checking if the user sending the request is either the owner of the submission or
    # the assignment creator (the only people authorized to evaluate).
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not (request.user == submission.owner or is_moderator):
        raise PermissionDenied

    # Evaluating the submission, asynchronously
    evaluate_object = Evaluate(submission)

    # getResults returns the ids of celery groups(each section testcases are grouped and run asynchronously
    # id will help us to track the status of the evaluation which will be rendered to user
    group_id_list, num_tasks = evaluate_object.getResults(program_type=program_type)
    return group_id_list, num_tasks


@login_required
def evaluation_status(request, submissionID):
    '''
    Function which replies to ajax reauest asking about the status of the evaluation
    '''
    submission = get_object_or_404(Upload, pk=submissionID)
    response = submission.evaluate_eval_status
    if response == "Execution Finished" or response == "Compilation Error":
        submission = get_object_or_404(Upload, pk=submissionID)
        # try:
        #     re_evaluate = Upload.objects.get(owner=submission.owner, assignment=submission.assignment)
        # except (Upload.DoesNotExist, Upload.MultipleObjectsReturned):
        #     raise Http404("DB Unique Key Error")
        submission.to_be_evaluated = False
        submission.evaluate_eval_status = "None"
        submission.save()              # Saving the database object as directory is deleted and evaluation is finished
    data = {'currentStatus': response, 'marks': submission.final_marks + submission.manualmark,
            'dontStop': submission.to_be_evaluated}
    return HttpResponse(json.dumps(data), content_type='application/json')


def evaluate_turtle(request, submissionID, testcaseID, program_type):
    '''
    for graphics
    '''
    submission = get_object_or_404(Upload, pk=submissionID)
    assignment = submission.assignment

    # Checking if the user sending the request is either the owner of the submission or the assignment creator
    # (the only people authorized to evaluate).
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not (request.user == submission.owner or is_moderator):
        raise PermissionDenied

    # Evaluating the submission.
    # global lock
    # lock.acquire()
    current_dir = os.getcwd()
    try:
        # remove below return if request is not ajax "work around"
        try:
            x = Evaluate(submission).getResults_turtle(request, testcaseID, program_type=program_type)
            return HttpResponse(x, content_type="application/json")
        except Exception as e:
            print e
    except Exception as e:
        print e
    finally:
        os.chdir(current_dir)
    return HttpResponseRedirect(request.META.get('HTTP_REFERER'))


@login_required
def evaluateAssignment(request, submissionID):
    '''
    Function to evaluate an assignment submission. Called by either the student who
    submitted the solution or the instructor.
    Takes as input the submission ID and calls evaluate() function above appropriately.
    Compile student's submission run all test cases and display results on html page.
    '''
    submission = get_object_or_404(Upload, pk=submissionID)
    assignment = submission.assignment

    # Checking if the user sending the request is either the owner of the submission or the assignment creator
    # (the only people authorized to evaluate).
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not (request.user == submission.owner or is_moderator):
        raise PermissionDenied

    if submission.to_be_evaluated:
        evaluate_assignment.delay(submissionID, "Evaluate")
        i = app.control.inspect()
        data = i.stats()
        if data is not None:
            node_name = list(data)[0]
            queue_position = len(i.reserved().get(node_name))
        else:
            queue_position = "Unknown"
        return render_to_response('evaluate/evaluate_ajax.html',
                                  {'submissionID': submissionID, 'assignment': assignment, 'position': queue_position,
                                   'path': request.get_host()}, context_instance=RequestContext(request))
    is_student = True if (request.user == submission.owner) else False
    is_due = (assignment.deadline <= timezone.now())

    try:
        results = Results(submission, program_type="Evaluate")
    except Results.DoesNotExist:
        raise Http404("Results not created yet")

    return render_to_response('evaluate/results.html',
                              {'submission': submission, 'assignment': assignment, 'results': results,
                               'error_code': error_codes, 'is_student': is_student, 'is_due': is_due,
                               'error_msg': error_msg, 'is_moderator': is_moderator},
                              context_instance=RequestContext(request))


@login_required
def evaluateSubmission(request, submissionID):
    '''
    Redundant function, but not removed so as to not break the code.
    '''
    return evaluateAssignment(request, submissionID)


@login_required
def checkOutput(request, programID):
    '''
    Function that evaluates the result for custom input.
    Takes as input the section ID for which the testing is done with custom input.
    '''
    # Checking if the request method is POST
    if request.method == 'POST':
        temp_fname = ''
        # This stores the input text. If this is not present then a custom testcase file was uploaded (else).
        if request.POST.get('inputText'):
            # Create a temporary file, and open it as inputFile variable.
            # Read the custom testcase and store it in the file object.
            _, temp_fname = tempfile.mkstemp(prefix='user_input')
            inputFile = open(temp_fname, 'wb+')
            for a_char in request.POST.get('inputText'):
                inputFile.write(a_char)
            inputFile.close()
            inputFile = open(temp_fname)
        else:
            # If the custom testcase was not given in the text box, then a file was uploaded.
            # It is read from the inputFile attribute of the request.
            inputFile = request.FILES.get('inputFile')

        # Get the section, assignment and the submission using the programID and user of the requestgiven as input.
        program = get_object_or_404(ProgramModel, pk=programID)
        assignment = program.assignment
        submission_object = LatestSubmission.objects.filter(owner=request.user, assignment=assignment)
        if submission_object:
            submission_object = submission_object[0]
        else:
            HttpResponseRedirect(request.META["HTTP_REFERER"])
        submission = Upload.objects.get(pk=submission_object.submission.id)
        # Handle error if there was no submission.
        # Create a testcase object using the input file, the section and the submission.
        # Get the results for this custom testcase.
        testcaseObject = CustomTestcase(inputFile, program, submission)
        old_pwd = os.getcwd()
        try:
            results = testcaseObject.getResult()
        finally:
            # Clear all temp files.
            if inputFile:
                inputFile.close()
            if os.path.isfile(temp_fname):
                os.remove(temp_fname)
            os.chdir(old_pwd)
        return render_to_response('evaluate/customTestResults.html', {'assignment': assignment, 'error_msg': error_msg,
                                                                      'results': results, 'error_code': error_codes,
                                                                      'program': program},
                                  context_instance=RequestContext(request))
    else:
        raise Http404


@login_required
def showResult(request, submissionID):
    '''
    Function to show results for a submission. This is different from the above functions
    in the sense that the other functions are called to evaluate
    a subsmission while this function is called to retrieve the results for a submission (already evaluated).
    '''
    # Retrieve the submission object and then retrieve the results of that submission using the Results class.
    submission = get_object_or_404(Upload, pk=submissionID)
    try:
        assignment_result = AssignmentResults.objects.filter(submission=submission)
    except AssignmentResults.DoesNotExist:
        return HttpResponse("Assignment is not yet evaluated")
    if not assignment_result and not submission.assignment.graphics_program:
        return HttpResponse("Assignment is not yet evaluated")
    results = Results(submission, program_type="Evaluate")
    course = submission.assignment.course
    is_moderator = isCourseModerator(course, request.user)
    # If any results were found then render them.
    is_due = (timezone.now() >= submission.assignment.deadline)
    if results:
        manual_marks = submission.manualmark
        total_marks = results.marks + manual_marks
        assignment = submission.assignment
        is_student = True if (request.user == submission.owner) else False
        is_moderator = isCourseModerator(assignment.course, request.user)
        is_due = (assignment.deadline <= timezone.now())
        return render_to_response('evaluate/result_table.html',
                                  {'submission': submission, 'assignment': assignment, 'error_msg': error_msg,
                                   'results': results, 'error_code': error_codes, 'is_student': is_student,
                                   'is_due': is_due, 'is_moderator': is_moderator, 'manual_marks': manual_marks,
                                   'total_marks': total_marks}, context_instance=RequestContext(request))
    return None


@login_required
def eval_all_submissions(request, assignmentID):
    '''
    Function to evaluate all submissions of an assignment.
    Takes as input the assignment ID for which all submissions needs to be evaluated.
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                              .filter(assignment=assignment)]
    all_submissions = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                            pk__in=list_of_assignment_ids, is_stale=False).order_by("-uploaded_on")
    # all_submissions = Upload.objects.filter(assignment=assignment)
    # print all_submissions
    job_list = []
    for submission in all_submissions:
        if submission.to_be_evaluated:
            job_list.append(evaluate_assignment.s(submission.id, "Evaluate"))

    if job_list:
        job = group(job_list)
        result = job.apply_async()
        result.save()
        num_of_tasks = len(job_list)

        progress = str(100 * result.completed_count() / num_of_tasks)
        context = {
            'data': progress,
            'task_id': result.id,
            'num_of_tasks': num_of_tasks,
            'assignment': assignment,
            'path': request.get_host(),
        }
        return render_to_response("evaluate/evaluateAll_progress.html", context,
                                  context_instance=RequestContext(request))
    return HttpResponseRedirect(reverse('upload_showAllSubmissions',
                                        kwargs={'assignmentID': assignmentID, 'flag': 1}))


@login_required
def poll_state_evaluate_all(request):
    """ A view to report the progress to the user """
    data = {}
    if request.is_ajax():
        data_dict = json.loads(request.POST.get('json_data'))
        task_id = data_dict['task_id']
        total_tasks = data_dict['num_of_tasks']
        task = app.GroupResult.restore(task_id)
        progress = str(100 * task.completed_count() / int(total_tasks))
        data = {'progress': progress}
    else:
        data = {'progress': str(-1.0)}
    json_data = json.dumps(data)
    return HttpResponse(json_data, content_type='application/json')


@login_required
def run_practice_test(request, submissionID):
    '''
    Function to run practice testcases on the submission.
    Takes as input the submission ID and calls evaluate() function.
    '''
    submission = get_object_or_404(Upload, pk=submissionID)
    assignment = submission.assignment

    # Checking if the user sending the request is either the owner of the submission or the assignment
    # creator (the only people authorized to evaluate).
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not (request.user == submission.owner or is_moderator):
        raise PermissionDenied

    if submission.to_be_practiced:
        evaluate_assignment.delay(submissionID, "Practice")
        i = app.control.inspect()
        data = i.stats()
        if data is not None:
            node_name = list(data)[0]
            queue_position = len(i.reserved().get(node_name))
        else:
            queue_position = "Unknown"
        return render_to_response('evaluate/practice_ajax.html',
                                  {'submissionID': submissionID, 'assignment': assignment, 'position': queue_position,
                                   'path': request.get_host()}, context_instance=RequestContext(request))
    else:
        is_student = True if (request.user == submission.owner) else False
        is_due = (assignment.deadline <= timezone.now())

        try:
            results = Results(submission, program_type="Practice")
        except Results.DoesNotExist:
            raise Http404("Results not created yet")

        return render_to_response('evaluate/practice_results.html',
                                  {'submission': submission, 'assignment': assignment, 'results': results,
                                   'error_code': error_codes, 'is_student': is_student, 'is_due': is_due,
                                   'error_msg': error_msg, 'is_moderator': is_moderator},
                                  context_instance=RequestContext(request))


@login_required
def practice_status(request, submissionID):
    '''
    status of execution
    '''
    submission = get_object_or_404(Upload, pk=submissionID)
    response = submission.practice_eval_status
    if response == "Execution Finished" or response == "Compilation Error":
        submission.to_be_practiced = False
        submission.practice_eval_status = "None"
        submission.save()  # Saving the database object as directory is deleted and evaluation is finished
    data = {'currentStatus': response}
    return HttpResponse(json.dumps(data), content_type='application/json')


@login_required
def final_results(request, programType, submissionID):
    '''
    final results
    '''
    submission = get_object_or_404(Upload, pk=submissionID)
    assignment = submission.assignment

    # Checking if the user sending the request is either the owner of the submission or
    # the assignment creator (the only people authorized to evaluate).
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not (request.user == submission.owner or is_moderator):
        raise PermissionDenied

    # Checking if the user is a student. Checking if the assignment is past its due date.
    is_student = True if (request.user == submission.owner) else False
    is_due = (assignment.deadline <= timezone.now())

    if programType == "practice":
        try:
            results = Results(submission, program_type="Practice")
        except Results.DoesNotExist:
            raise Http404("Results not created yet")
        return render_to_response('evaluate/practice_results.html',
                                  {'submission': submission, 'assignment': assignment, 'results': results,
                                   'error_code': error_codes, 'is_student': is_student, 'is_due': is_due,
                                   'error_msg': error_msg, 'is_moderator': is_moderator},
                                  context_instance=RequestContext(request))
    try:
        results = Results(submission, program_type="Evaluate")
    except Results.DoesNotExist:
        raise Http404("Results not created yet")
    return render_to_response('evaluate/results.html',
                              {'submission': submission, 'assignment': assignment, 'results': results,
                               'error_code': error_codes, 'is_student': is_student, 'is_due': is_due,
                               'error_msg': error_msg, 'is_moderator': is_moderator},
                              context_instance=RequestContext(request))


@login_required
def evaluation_details(request, submissionID):
    '''
    Function to evaluate submission and render a detailed table of results.
    Takes as input the submission ID and calls evaluate() function.
    The details of the results are rendered to evaluate/result_table.html.
    '''
    return evaluateAssignment(request, submissionID)


def get_all_results_json(assignmentID):
    '''
    JSON FORMAT:
        [
            {
                'id':userid,
                'name':username,
                'submissionId':submissionId,
                'programs':
                [
                    {
                        'name': prgram_name,
                        'marks':marks,
                        'testcases':
                        [
                            {
                                'id' : testcase_result_id,
                                'name':name,
                                'marks':marks,
                            }
                        ]
                    }
                ]
                'remarks':'remarks'
            }
        ]
    get results in json format
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                              .filter(assignment=assignment)]
    allSubmission = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                          pk__in=list_of_assignment_ids).order_by("-uploaded_on")
    assignment_results = []
    for submission in allSubmission:
        if not submission.is_stale:
            try:
                # Gather the results for the submission.
                results = Results(submission, program_type="Evaluate")
                # Retrieve the marks and submission ID for each section. This is all we need.
                assignment_result_row = {}
                assignment_result_row['id'] = submission.owner.id
                assignment_result_row['name'] = submission.owner.username
                assignment_result_row['submissionId'] = submission.id
                assignment_result_row['programs'] = []
                for prgm_rslt in results.program_results:
                    program_dict = {}
                    program_dict['name'] = prgm_rslt.program_result.program.name
                    program_dict['marks'] = prgm_rslt.marks
                    program_dict['testcases'] = []

                    for tst_case in prgm_rslt.testResults:
                        testcase_dict = {}
                        testcase_dict['id'] = tst_case.id
                        testcase_dict['name'] = tst_case.test_case.name
                        testcase_dict['marks'] = tst_case.marks
                        program_dict['testcases'].append(testcase_dict)
                    if program_dict['testcases']:
                        assignment_result_row['programs'].append(program_dict)

                assignment_result_row['remarks'] = submission.comments
                assignment_result_row['manualmark'] = submission.manualmark
                if assignment_result_row["programs"]:
                    assignment_results.append(assignment_result_row)

            except AssignmentResults.DoesNotExist:
                return {}
    return assignment_results


def get_evaluation_details_in_csv(request, assignmentID):
    '''
    get_evaluation_details_in_csv
    save a file in safeexec/results
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                              .filter(assignment=assignment)]
    allSubmission = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                          pk__in=list_of_assignment_ids).order_by("-uploaded_on")
    line = ""
    header = ""
    count = 0
    for submission in allSubmission:
        if submission.is_stale:
            continue
        try:
            results = Results(submission, program_type="Evaluate")
            line += str(submission.owner.username) + ","
            if count == 0:
                header += "username,"
                header += "manualmark,"
            line += str(submission.manualmark) + ","
            for prgm_rslt in results.program_results:
                for tst_case in prgm_rslt.testResults:
                    line += str(tst_case.marks) + ","
                    if count == 0:
                        header += str(tst_case.test_case.name) + ","
                if count == 0:
                    header += str(prgm_rslt.program_result.program.name) + ","
                line += str(prgm_rslt.marks + submission.manualmark) + ","
                line += str(prgm_rslt.marks) + ","

        except AssignmentResults.DoesNotExist:
            return {}
        line += "\n"
        count += 1
    line = header + "\n" + line
    response = HttpResponse(content_type="text/plain")
    response['Content-Disposition'] = 'attachment; filename=%s.csv' % (assignment.name)
    response.write(line)
    return response


@login_required
def complete_evaluation_details(request, assignmentID):
    '''
    Function to retrieve the results of all submissions and render in a good format.
    Takes as input the assignment ID and gathers the results of all submissions.
    '''
    # Gather the assignment object and then all submissions and section of this assignment.
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    all_assignments = Assignment.objects.filter(course=assignment.course).filter(trash=False).order_by(
        '-serial_number')
    is_moderator = isCourseModerator(assignment.course, request.user)
    if is_moderator:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if a.publish_on <= timezone.now()]
    assignment_results = get_all_results_json(assignmentID)
    if assignment_results:
        table_main_headers = [{"name": "Name", "colspan": 1, "rowspan": 2}]
        table_secondary_headers = []
        for ar in assignment_results[0]["programs"]:
            table_main_headers.append({"name": ar["name"], "colspan": len(ar["testcases"])})
            for tc in ar["testcases"]:
                table_secondary_headers.append({"name": tc["name"]})
        content = []
        for ar in assignment_results:
            row = {"name": ar["name"]}
            row["testcases"] = []
            for pr in ar["programs"]:
                for tc in pr["testcases"]:
                    row["testcases"].append({"marks": tc["marks"], "id": tc["id"]})
            row["submissionId"] = ar["submissionId"]
            row["Manual_marks"] = ar["manualmark"]
            row["remarks"] = ar["remarks"]
            content.append(row)
        table_main_headers.append({"name": "Manual marks", "colspan": 1, "rowspan": 2})
        table_main_headers.append({"name": "remarks", "colspan": 1, "rowspan": 2})
        return render_to_response("evaluate/students_result_table.html",
                                  {'assignment': assignment, "table_main_headers": table_main_headers,
                                   "table_secondary_headers": table_secondary_headers, "content": content,
                                   'course': assignment.course, 'assignments': assignments, 'date_time': timezone.now(),
                                   'is_moderator': is_moderator, 'data': True},
                                  context_instance=RequestContext(request))
    return render_to_response("evaluate/students_result_table.html", {'assignment': assignment,
                                                                      'course': assignment.course,
                                                                      'assignments': assignments,
                                                                      'date_time': timezone.now(),
                                                                      'is_moderator': is_moderator},
                              context_instance=RequestContext(request))


@login_required
def get_evaluation_details_in_json(request, assignmentID):
    '''
    details json format
    '''
    assignment_results = get_all_results_json(assignmentID)
    return HttpResponse(json.dumps(assignment_results), content_type="application/json")


@login_required
def edit_evaluation_details(request, assignmentID):
    '''
    details edit
    '''
    template = "evaluate/excel.html"
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    return render_to_response(template, {"assignment": assignment}, context_instance=RequestContext(request))


@login_required
def format_json_for_excel(request, assignmentID):
    '''
    change format
    '''
    assignment_results = get_all_results_json(assignmentID)
    response_data = {}
    colheaders = ["name"]
    for ar in assignment_results[0]["programs"]:
        for tc in ar["testcases"]:
            colheaders.append(ar["name"] + " | " + tc["name"])
    response_data["data"] = colheaders
    return HttpResponse(json.dumps(response_data), content_type="application/json")


@login_required
def edit_testcase_marks(request):
    '''
    edit marks
    '''
    if request.method == "POST":
        pk = request.POST["pk"]
        value = request.POST["value"]
        t = TestcaseResult.objects.get(id=pk)
        course = t.test_case.program.assignment.course
        is_moderator = isCourseModerator(course, request.user)
        if is_moderator:
            t.marks = value
            t.save()
            return HttpResponse("true")
        else:
            raise Http404
    else:
        raise Http404


@login_required
def edit_manual_marks(request):
    """
    edit manual marks
    """
    if request.method == "POST":
        pk = request.POST["pk"]
        value = request.POST["value"]
        try:
            value = float(value)
        except ValueError:
            return HttpResponse("true")
        row = Upload.objects.get(id=pk)
        course = row.assignment.course
        is_moderator = isCourseModerator(course, request.user)
        if is_moderator:
            row.manualmark = value
            row.save()
            return HttpResponse("true")
        else:
            raise Http404
    else:
        raise Http404


@login_required
def edit_testcase_comments(request):
    '''
    comments edit
    '''
    if request.method == "POST":
        pk = request.POST["pk"]
        value = request.POST["value"]
        t = Upload.objects.get(id=pk)
        course = t.assignment.course
        is_moderator = isCourseModerator(course, request.user)
        if is_moderator:
            t.comments = value
            t.save()
            return HttpResponse("true")
        else:
            raise Http404
    else:
        raise Http404


@login_required
def compare_files(request, testcaseresultid):
    '''Function to visually compare expected output and actual output'''
    testcaseresult = get_object_or_404(TestcaseResult, pk=testcaseresultid)
    expected_output = os.path.join(settings.MEDIA_ROOT, testcaseresult.test_case.output_files.path)
    test_input = os.path.join(settings.MEDIA_ROOT, testcaseresult.test_case.input_files.path)
    actual_output_tar = os.path.join(settings.MEDIA_ROOT, testcaseresult.output_files.path)
    input_lines = "\n".join(read_file(name=test_input, readthis=testcaseresult.test_case.std_in_file_name))
    soup = BeautifulSoup(difflib.HtmlDiff().make_file(read_file(name=expected_output, readthis=testcaseresult.test_case.std_out_file_name),
                                                      read_file(name=actual_output_tar)))
    for row in soup.find('table').findAll('tr'):
        for col in row.find_all('td'):
            if col.has_attr('nowrap'):
                del col['nowrap']
    soup.table.tbody.insert_before(soup.new_tag("thead"))
    soup.table.thead.append(soup.new_tag("th"))
    for s in ['Line Number', 'Expected Output', None, 'Line Number', 'Actual Output']:
        new_tag = soup.new_tag("th")
        if s:
            new_tag.string = s
        soup.table.thead.append(new_tag)
    soup.table = soup.find("table", {"rules": "groups"})
    soup.table['width'] = "100%"
    soup.table.insert_after(soup.new_tag('br'))
    new_tag = soup.new_tag("style", type='text/css')
    soup.style.insert_after(new_tag)
    new_tag.append(" table {border-collapse:collapse; table-layout:fixed;}table td {border:solid 1px; "
                   "width:100px; word-wrap:break-word;} table th{border:solid 1px;text-align:center;}")
    new_tag_style = soup.new_tag("style", type='text/css')
    new_tag.insert_after(new_tag_style)
    new_tag_style.append("td.diff_header {text-align:center}")
    for new_tag in soup.find_all('colgroup'):
        new_tag.extract()
    colgroup_tag = soup.new_tag('colgroup')
    soup.thead.insert_before(colgroup_tag)
    for w in ['2%', '8%', '40%', '2%', '8%', '40%']:
        colgroup_tag.append(soup.new_tag('col', width=w))
    assignment = testcaseresult.test_case.program.assignment
    return render_to_response("evaluate/fileComparison.html",
                              {'course': assignment.course, 'assignment': assignment, 'tst': testcaseresult,
                               'inp': input_lines,
                               'table': str(soup), 'error_msg': error_msg}, context_instance=RequestContext(request))


@login_required
def downloadInputfile(request, TestcaseID):
    '''
    std in file download
    '''
    testcase = get_object_or_404(Testcase, pk=TestcaseID)
    program = testcase.program
    assignment = program.assignment
    is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course

    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")

    if not testcase.input_files:
        return HttpResponseNotFound("File not found")

    is_moderator = isCourseModerator(course, request.user)

    if(is_moderator or program.program_type == "Practice" or is_due):
        return file_download(testcase.input_files)

    return HttpResponseForbidden("Forbidden 403")


@login_required
def showTurtleTestcases(request, submissionID):
    '''this function is to display all testcases in turtle assignment'''
    submission = get_object_or_404(Upload, pk=submissionID)
    assignment = submission.assignment
    course = assignment.course
    # assignment = get_object_or_404(Assignment, pk=assignment_id)
    is_moderator = isCourseModerator(course, request.user)
    programs = ProgramModel.objects.filter(assignment=submission.assignment, program_type="Practice")
    if is_moderator:
        programs = ProgramModel.objects.filter(assignment=submission.assignment)
    testcases = []
    testcasesList = []
    for program in programs:
        testcasesList = Testcase.objects.filter(program=program)
        testcases.append([program, testcasesList])

    return render_to_response('evaluate/showTurtleTestcase.html',
                              {'testcases': testcases, 'assignment': assignment, 'course': course,
                               'submission': submission, 'is_moderator': is_moderator},
                              context_instance=RequestContext(request))


@login_required
def evaluate_turtle_testcase(request, submissionID, testcaseID):
    '''function to evaluate simplecpp graphics testcases'''
    if testcaseID == '00':
        request.META['custom_input'] = 1
        testcaseID = None
        programs = ProgramModel.objects.filter(assignment=get_object_or_404(Upload, pk=submissionID).assignment,
                                               program_type="Practice")
        for program in programs:
            for testcase in Testcase.objects.filter(program=program):
                testcaseID = testcase.id
                break
            if testcaseID is not None:
                break
    else:
        if not isCourseModerator(get_object_or_404(Upload, pk=submissionID).assignment.course, request.user):
            if Testcase.objects.filter(id=testcaseID):
                if Testcase.objects.filter(id=testcaseID)[0].program.program_type == 'Evaluate':
                    return Http404("^v^ Forbidden ^o^")
    return evaluate_turtle(request, submissionID, testcaseID, "Practice")
