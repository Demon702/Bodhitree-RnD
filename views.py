"""
Created on May 20, 2013
@author: aryaveer
Views for assignment module
"""
import copy
import csv
import datetime as DateTime
import json
import mimetypes
import os
import pickle
import re
import shutil
import tarfile
import tempfile
import zipfile
from ast import literal_eval as make_tuple
from copy import deepcopy
from datetime import datetime, timedelta
from wsgiref.util import FileWrapper

import pytz
from django.conf import settings
from django.contrib import messages
from django.contrib.auth.decorators import login_required
from django.contrib.auth.models import User
from django.contrib.contenttypes.models import ContentType
from django.core.exceptions import PermissionDenied
from django.core.files import File
from django.core.files.storage import default_storage
from django.core.mail import send_mail
from django.core.urlresolvers import reverse
from django.db import transaction
from django.db.models import Max
from django.forms import model_to_dict
from django.http import Http404, HttpResponse, HttpResponseForbidden, HttpResponseNotFound, HttpResponseRedirect
from django.shortcuts import get_object_or_404, render_to_response
from django.template import RequestContext
from django.utils import timezone
from django.utils.encoding import smart_str
from django.utils.safestring import mark_safe
# from eventlog.models import log
from formtools.wizard.views import SessionWizardView
from netaddr import iter_iprange
from rest_framework import status
from rest_framework.response import Response

from assignments.assignments_utils import create_output
from assignments.assignments_utils.check_dup_submission import check, create_upload
from assignments.forms import (AssignmentForm, AssignmentImportForm, AssignmentMetaForm, CheckerCodeForm,
                               CreateTestcaseArray, CreateTestcaseMatrix, CreateTestcaseNumber, ProgramFormCandE,
                               ProgramFormCNotE, ProgramFormE, SafeExecForm, bulk_add_check, check_allocation_doc)
from assignments.models import (Assignment, AssignmentErrors, AssignmentImport, AssignmentScript, Checker,
                                CheckerErrors, Program, ProgramErrors, SafeExec, TA_allocation, Testcase,
                                TestcaseErrors)
from assignments.serializers import AssignmentDetailsSerializer
from assignments.tasks import delete_redundant_files
from courseware.models import Course, CourseHistory, CourseInfo
# from courseware.views import course
from elearning_academy.celeryapp import app
from elearning_academy.decorators import is_moderator_check
from elearning_academy.permissions import get_mode
from evaluate.models import AssignmentResults, ProgramResults, TestcaseResult
from evaluate.tasks import evaluate_assignment
from evaluate.utils.checkOutput import CustomTestcase
from evaluate.utils.evaluator import Results
from exam.models import Pausetimer, Proctoring
from exam.views import validateuser
from report_grading_app.helper import is_valid_ip
from upload.forms import UploadForm
from upload.models import LatestSubmission, ServerSavedSubmission, Upload
from util.core import local2utc
from utils.archives import Archive, extract_or_copy, get_file_name_list, read_file
from utils.filetypes import (README_LINKS, get_compilation_command, get_compiler_name, get_execution_command,
                             get_extension, get_interpreter_name, is_valid, language_category)


def isCourseCreator(course, user):
    '''function returns true if user is owner of the course'''
    try:
        course_history = CourseHistory.objects.get(
            course_id=course, user_id=user.id)
        return course_history.is_owner
    except Exception:
        return False


def iscourse_owner(course, user):
    '''function returns true if user is owner of the course'''
    course_history = CourseHistory.objects.get(
        course_id=course, user_id=user.id)
    return course_history.is_creator


def isCourseModerator(course, user):
    '''function returns true if user is instructor for the course'''
    try:
        course_history = CourseHistory.objects.get(
            course_id=course, user_id=user.id)
        return course_history.is_owner or course_history.is_moderator
    except Exception:
        return False


def isEnrolledInCourse(course, user):
    '''function returns true if user is student of the course'''
    try:
        course_history = CourseHistory.objects.filter(
            course_id=course, user_id=user.id)
        return len(course_history) > 0
    except Exception:
        return False


def club_output_testfile(testcases, new_testcase, program_dir, io_filename_parts, each_testfile):
    """
    Clubs output file with the corresponding input file


    Searches in the section folder for the io files with the same identifier and if found,
    it clubs them, stores them in the filesystem and the corresponding paths are stored in the database

    Args:
        testcases: testfile
        new_testcase:testcase instance
        program_dir: section folder
        io_filename_parts: parts of the testfile mame
        each_testfile: each testfile

    Returns: new testcase

    """
    out_file_found = False
    for each_testfile_again in testcases:
        if os.path.isfile(program_dir + '/' + each_testfile_again) and not \
                (each_testfile_again in ['makefile', 'Makefile', 'source.tar.gz'] and
                 each_testfile == each_testfile_again):
            if not out_file_found:
                io_filename_parts_again = each_testfile_again.split('_')
                if io_filename_parts[0] == io_filename_parts_again[0] and io_filename_parts_again[1] == 'out':
                    out_file_found = True
                    base2 = os.path.basename(
                        program_dir + '/' + each_testfile_again)
                    io_dir2 = program_dir + '/' + os.path.splitext(base2)[0]
                    if not os.path.exists(io_dir2):
                        os.makedirs(io_dir2)
                    shutil.move(program_dir + '/' + each_testfile_again,
                                io_dir2 + '/' + each_testfile_again)
                    io_dir2_tar = io_dir2 + '.tar.gz'
                    # creating a tarfile for testcase file
                    with tarfile.open(io_dir2_tar, "w:gz") as tar:
                        tar.add(io_dir2, arcname=os.path.basename(io_dir2))
                    io_dir2_tarfile = file(io_dir2_tar)
                    new_testcase.output_files = File(io_dir2_tarfile)
                    shutil.rmtree(io_dir2)
                    os.remove(io_dir2_tar)
                    new_testcase.std_out_file_name = each_testfile_again
                    if new_testcase.name == '':
                        new_testcase.name = (
                            io_dir2.split('/')[-1]).split('_')[2]
                # to remove extra input files with same identifier
                elif io_filename_parts[0] == io_filename_parts_again[0] and io_filename_parts_again[1] == 'inp':
                    os.remove(program_dir + '/' + each_testfile_again)
                else:  # to put some dummy values
                    new_testcase.output_files = None
                    new_testcase.std_out_file_name = ''
    return new_testcase


def club_input_testfile(testcases, new_testcase, program_dir, io_filename_parts, each_testfile):
    """
    Clubs ipnut file with the corresponding output file

    Searches in the section folder for the io files with the same identifier and if found,
    it clubs them, stores them in the filesystem and the corresponding paths are stored in the database

    Args:
        testcases: testfile
        new_testcase:testcase instance
        program_dir: section folder
        io_filename_parts: parts of the testfile mame
        each_testfile: each testfile

    Returns: new testcase

    """
    inp_file_found = False
    for each_testfile_again in testcases:
        if os.path.isfile(program_dir + '/' + each_testfile_again) and not \
                (each_testfile_again in ['makefile', 'Makefile', 'source.tar.gz'] and
                 each_testfile == each_testfile_again):
            if not inp_file_found:
                io_filename_parts_again = each_testfile_again.split('_')
                if io_filename_parts[0] == io_filename_parts_again[0] and io_filename_parts_again[1] == 'inp':
                    inp_file_found = True
                    base2 = os.path.basename(
                        program_dir + '/' + each_testfile_again)
                    io_dir2 = program_dir + '/' + os.path.splitext(base2)[0]
                    if not os.path.exists(io_dir2):
                        os.makedirs(io_dir2)
                    shutil.move(program_dir + '/' + each_testfile_again,
                                io_dir2 + '/' + each_testfile_again)
                    io_dir2_tar = io_dir2 + '.tar.gz'
                    # creating a tarfile for testcase file
                    with tarfile.open(io_dir2_tar, "w:gz") as tar:
                        tar.add(io_dir2, arcname=os.path.basename(io_dir2))
                    io_dir2_tarfile = file(io_dir2_tar)
                    new_testcase.input_files = File(io_dir2_tarfile)
                    shutil.rmtree(io_dir2)
                    os.remove(io_dir2_tar)
                    new_testcase.std_in_file_name = each_testfile_again
                    if new_testcase.name == '':
                        new_testcase.name = (
                            io_dir2.split('/')[-1]).split('_')[2]
                elif io_filename_parts[0] == io_filename_parts_again[0] and io_filename_parts_again[1] == 'out':
                    # to remove extra output files with the same identifier
                    os.remove(program_dir + '/' + each_testfile_again)
                else:  # to put some dummy values
                    new_testcase.input_files = None
                    new_testcase.std_in_file_name = ''
    return new_testcase


def adding_testcases(testcases, program_dir, new_program):
    """
    for adding the test cases in bulk

    finds the values for different fields of the model testcase and assigns them to it
    For example, it calls the club_output_testfile() function to get std_out_file_name and output_files

    Args:
        testcases: test cases
        program_dir: section folder
        new_program: new section

    Returns: it simpy adds the testcases

    """
    for each_testfile in testcases:
        if os.path.isfile(program_dir + '/' + each_testfile) and \
                (each_testfile not in ['makefile', 'Makefile', 'source.tar.gz']):
            io_file = program_dir + '/' + each_testfile  # indicates the input/output files
            io_filename_parts = each_testfile.split('_')
            if len(io_filename_parts) == 3:
                new_testcase = Testcase()
                new_testcase.program = new_program
                new_testcase.description = ''

                io_dir = program_dir + '/' + \
                    os.path.splitext(os.path.basename(io_file))[0]
                if not os.path.exists(io_dir):
                    os.makedirs(io_dir)
                shutil.move(io_file, io_dir + '/' + each_testfile)
                io_dir_tar = io_dir + '.tar.gz'
                # creating a tarfile for the testcase file
                with tarfile.open(io_dir_tar, "w:gz") as tar:
                    tar.add(io_dir, arcname=os.path.basename(io_dir))
                io_dir_tarfile = file(io_dir_tar)
                if io_filename_parts[1] == "inp":
                    new_testcase.name = (io_dir.split('/')[-1]).split('_')[2]
                    new_testcase.input_files = File(io_dir_tarfile)
                    shutil.rmtree(io_dir)
                    os.remove(io_dir_tar)
                    new_testcase.std_in_file_name = each_testfile
                    # for every input file, checking if there is a corresponding output file
                    new_testcase = club_output_testfile(testcases, new_testcase, program_dir, io_filename_parts,
                                                        each_testfile)
                elif io_filename_parts[1] == 'out':
                    new_testcase.name = (io_dir.split('/')[-1]).split('_')[2]
                    new_testcase.output_files = File(io_dir_tarfile)
                    shutil.rmtree(io_dir)
                    os.remove(io_dir_tar)
                    new_testcase.std_out_file_name = each_testfile
                    # for every output file, checking if there is a corresponding input file
                    new_testcase = club_input_testfile(testcases, new_testcase, program_dir, io_filename_parts,
                                                       each_testfile)
                if new_testcase.name == '':  # to put some dummy name when no name is provided
                    new_testcase.name = 'testcase' + io_filename_parts[0]
                new_testcase.progam_line_args = ''
                new_testcase.marks = 0
                new_testcase.save()


def get_compiler_and_exceution_command(new_program, new_assignment):
    """
    gets the compiler and execution commands
    Args:
        new_program: new program
        new_assignment: new assignment

    Returns: new program

    """
    assignment = get_object_or_404(Assignment, pk=new_assignment.id)
    objs = Program.objects.filter(assignment=assignment)
    lang_category = language_category(assignment.program_language)
    if objs:
        if lang_category == 0:
            comp_command = pickle.loads(objs[0].compiler_command)
            new_program.compiler_command = pickle.dumps(
                [comp_command[0], '', ''])
        elif lang_category == 1:
            comp_command = pickle.loads(objs[0].compiler_command)
            new_program.compiler_command = pickle.dumps(
                [comp_command[0], '', ''])
            exe_command = pickle.loads(objs[0].execution_command)
            new_program.execution_command = pickle.dumps(
                [exe_command[0], '', ''])
        elif lang_category == 2:
            exe_command = pickle.loads(objs[0].execution_command)
            new_program.execution_command = pickle.dumps(
                [exe_command[0], '', ''])
    else:
        if lang_category == 0:
            comp_command = get_compiler_name(assignment.program_language)
            new_program.compiler_command = pickle.dumps([comp_command, '', ''])
        elif lang_category == 1:
            comp_command = get_compiler_name(assignment.program_language)
            new_program.compiler_command = pickle.dumps([comp_command, '', ''])
            exe_command = get_interpreter_name(assignment.program_language)
            new_program.execution_command = pickle.dumps([exe_command, '', ''])
        elif lang_category == 2:
            exe_command = get_interpreter_name(assignment.program_language)
            new_program.execution_command = pickle.dumps([exe_command, '', ''])
    return new_program


def add_source_and_makefile(program_dir, new_program):
    """
    stores the source and makefile in the new program
    Args:
        program_dir: section folder
        new_program: new program

    Returns: jnew program

    """
    temp_src = program_dir + '/source'
    temp_makefile = program_dir + '/makefile'
    temp_makefile2 = program_dir + '/Makefile'

    if os.path.isdir(temp_src):
        src_tar = program_dir + '/source.tar.gz'
        with tarfile.open(src_tar, "w:gz") as tar:
            tar.add(temp_src, arcname=os.path.basename(temp_src))
        src_tarfile = file(src_tar)
        new_program.program_files = File(src_tarfile)
        shutil.rmtree(temp_src)
        os.remove(src_tar)

    if os.path.isfile(temp_makefile):
        make_file = file(temp_makefile)
        new_program.makefile = File(make_file)
        os.remove(temp_makefile)
    elif os.path.isfile(temp_makefile2):
        make_file = file(temp_makefile2)
        new_program.makefile = File(make_file)
        os.remove(temp_makefile2)
    return new_program


def section_bulk_add(new_assignment):
    """
    for adding the sections and perhaps the testcases in bulk
    Args:
        new_assignment: new assignment

    Returns: just adds the new assignment

    """
    # in the variable temp_dir[num],
    # num indicates the level at which we are in the assignment folder uploaded
    # extracting the uploaded file
    temp_file2 = new_assignment.bulk_add
    temp_file = os.path.join(settings.MEDIA_ROOT, str(temp_file2))
    temp_dirarr = temp_file.split("/")
    level = 0
    temp_dir = ''
    for each_dir_element in temp_dirarr:
        if level <= 4:
            temp_dir = temp_dir + each_dir_element + '/'
            level += 1
    # temp_dir indicates the folder in which assignment resides
    temp_dir = temp_dir[:-1]
    extract_or_copy(src=temp_file, dest=temp_dir)

    # distributing the sections of the files
    # temp_dir now indicates the assignment folder
    temp_dir = temp_dir + '/' + new_assignment.name
    for index1 in xrange(0, 2):
        if index1 == 0:
            temp_dir2 = temp_dir + '/Evaluate/'
        else:
            temp_dir2 = temp_dir + '/Practice/'
        if os.path.isdir(temp_dir2):
            sections = os.listdir(temp_dir2)
            for each_section in sections:
                new_program = Program()
                new_program.assignment = new_assignment
                temp_dir3 = temp_dir2 + each_section

                new_program = add_source_and_makefile(temp_dir3, new_program)
                new_program = get_compiler_and_exceution_command(
                    new_program, new_assignment)
                new_program.name = each_section
                if temp_dir2.endswith('/Evaluate/'):
                    new_program.program_type = 'Evaluate'
                elif temp_dir2.endswith('/Practice/'):
                    new_program.program_type = 'Practice'
                new_program.description = ''
                new_program.is_sane = True
                new_program.language = new_assignment.program_language
                new_program.solution_ready = True
                new_program.save()

                if os.path.isdir(temp_dir3):
                    for each_testfile in os.listdir(temp_dir3):
                        if each_testfile not in ['makefile', 'Makefile', 'source.tar.gz'] and \
                                os.path.splitext(each_testfile)[-1].lower() == "":
                            os.rename(temp_dir3 + "/" + each_testfile,
                                      temp_dir3 + "/" + each_testfile + ".txt")

                    # distributing the test cases of each section
                    testcases = os.listdir(temp_dir3)
                    adding_testcases(testcases, temp_dir3, new_program)

    # removing the extracted folder
    shutil.rmtree(temp_dir)


def testcase_bulk_add(new_program):
    """
    creates a new sections and adds the testcases in bulk
    Args:
        new_program: section

    Returns: just adds the test cases

    """
    # extracting the uploaded file
    temp_file2 = new_program.testcase_bulk_add
    temp_file = os.path.join(settings.MEDIA_ROOT, str(temp_file2))
    temp_dirarr = temp_file.split("/")
    level = 0
    temp_dir = ''
    for each_dirname in temp_dirarr:
        if level <= 4:
            temp_dir = temp_dir + each_dirname + '/'
            level += 1
    temp_dir = temp_dir[:-1]
    extract_or_copy(src=temp_file, dest=temp_dir)

    # distributing the testcases of the section
    temp_dir2 = temp_dir + '/' + new_program.name
    testcases = os.listdir(temp_dir2)
    adding_testcases(testcases, temp_dir2, new_program)

    # deleting the extracted folder
    shutil.rmtree(temp_dir2)


@login_required
def index(request, courseID):
    """ List all assignments for courseID. courseID is automatically generated
    in Course table."""
    course = get_object_or_404(Course, pk=courseID)
    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')

    if CourseHistory.objects.filter(course_id=course, user_id=request.user.id).count() == 0:
        return HttpResponseForbidden("Forbidden 403")

    course_history = CourseHistory.objects.get(
        course_id=course, user_id=request.user.id)
    course_info = CourseInfo.objects.get(pk=course.course_info_id)
    is_creator = isCourseCreator(course, request.user)
    is_moderator = isCourseModerator(course, request.user)
    mode = get_mode(request)
    if is_moderator or is_creator:
        assignments = all_assignments
        leave_course = False
        number_of_students = 0
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
        leave_course = True
        number_of_students = 0
    return render_to_response(
        'assignments/index.html',
        {'assignments': assignments, 'mode': mode, 'is_moderator': is_moderator, 'course_info': course_info,
         'date_time': timezone.now(),
         'course': course, 'leave_course': bool(leave_course),
         'number_of_students': number_of_students, 'course_history': course_history},
        context_instance=RequestContext(request))


@login_required
def deleteSubmission(request, uploadID):
    '''
    Logic to delete submission
    '''
    upload = get_object_or_404(Upload, pk=uploadID)
    if not request.user == upload.owner:
        return HttpResponseForbidden("Forbidden 403")
    assignmentID = upload.assignment.id
    upload.delete()
    filepath = os.path.join(settings.MEDIA_ROOT, str(upload.filePath))
    filepath = filepath.rsplit('/', 1)[0]
    shutil.rmtree(filepath)
    return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignmentID}))


@login_required
def get_ta_allocation(request, assignmentID):
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course
    ta_list = {}
    if isCourseModerator(course, request.user):
        ta_allocation = TA_allocation.objects.filter(assignment=assignment)
        for ta_object in ta_allocation:
            ta = ta_object.assistant.username
            student = ta_object.student.username
            if ta in ta_list.keys():
                ta_list[ta].append(student)
            else:
                ta_list[ta] = [student]
    return ta_list


@login_required
def detailsAssignment(request, assignmentID):
    '''
    Logic to display assignment
    '''
    number_of_submissions = 0
    allowed_exam_status = True
    submission_allowed = None   # New initialize
    is_due = None   # New initialize
    rem_time = None
    assignment = get_object_or_404(Assignment, pk=assignmentID)

    if not isEnrolledInCourse(assignment.course, request.user):
        return HttpResponseRedirect("/courseware/courseslist/")

    course = assignment.course
    hide_val = assignment.hide
    is_moderator = isCourseModerator(course, request.user)
    trash_val = assignment.trash
    if trash_val or (not is_moderator and hide_val):
        raise PermissionDenied
    is_creator = isCourseCreator(course, request.user)
    is_moderator = isCourseModerator(course, request.user)
    mode = get_mode(request)
    formData = AssignmentForm(initial=model_to_dict(
        assignment), courseID=assignment.course.id)

    if (timezone.now() < assignment.publish_on if assignment.publish_on else True) or assignment.hide:
        if not is_moderator and not is_creator:
            raise PermissionDenied
    # changes by jitendra
    deadline = get_assignment_deadline(request, assignment)
    que = 'SELECT DISTINCT submission_id as id FROM upload_latestsubmission WHERE assignment_id =' + assignmentID + ';'
    number_of_submissions = LatestSubmission.objects.raw(que)
    number_of_submissions = len(list(number_of_submissions))

    if assignment.type_of_lab == "Lab":
        rem_time = int(
            (assignment.deadline - datetime.now(pytz.timezone('UTC'))).total_seconds())
    elif assignment.type_of_lab == "Exam":
        (rem_time, _, allowed_exam_status) = get_object_from_proctoring(
            assignment.exam_group_id, request.user)

    ipaddress = assignment.ipaddress
    ip_correct = False
    try:
        ipadd = request.META["HTTP_X_FORWARDED_FOR"]
    except KeyError:
        ipadd = request.META.get('REMOTE_ADDR')
    if ipaddress:
        ip_allowed = []
        list1 = ipaddress.split(",")
        for ip_add in list1:

            match = re.search("-", ip_add)
            if match:
                list2 = ip_add.split("-")
                ip_list = list(iter_iprange(list2[0], list2[1]))
                for ip2 in ip_list:
                    ip_allowed.append(str(ip2))
            else:
                ip_allowed.append(ip_add)

        if ipadd in ip_allowed:
            ip_correct = True
    else:
        ip_correct = True
    has_joined = CourseHistory.objects.filter(
        course_id=course, user_id=request.user.id)

    if assignment.deadline is not None:
        submission_allowed = (
            timezone.now() <= assignment.deadline) and bool(has_joined)
        is_due = (timezone.now() >= assignment.deadline) and bool(has_joined)

    perror_ctype = ContentType.objects.get_for_model(ProgramErrors)
    terror_ctype = ContentType.objects.get_for_model(TestcaseErrors)
    program_errors = []
    test_errors = []

    for error in AssignmentErrors.objects.filter(assignment=assignment, content_type=terror_ctype):
        test_errors.extend(TestcaseErrors.objects.filter(pk=error.object_id))

    for error in AssignmentErrors.objects.filter(assignment=assignment, content_type=perror_ctype):
        program_errors.extend(ProgramErrors.objects.filter(pk=error.object_id))
    course = assignment.course
    programs = Program.objects.filter(assignment=assignment)
    evaluate_program = [
        a_program for a_program in programs if a_program.program_type == "Evaluate"]
    practice_program = [
        a_program for a_program in programs if a_program.program_type == "Practice"]
    programs_with_errors = []

    for aprogram in programs:
        if not aprogram.is_sane:
            try:
                p_error = ProgramErrors.objects.get(program=aprogram)
                programs_with_errors.append(p_error)
            except ProgramErrors.DoesNotExist:
                p_error = None

    submittedFiles = [s.submission for s in LatestSubmission.objects.filter(
        owner=request.user, assignment=assignment)]
    if submittedFiles:
        best_submission = submittedFiles[0]
    else:
        best_submission = ""
    program_not_ready = False
    disable_grading = False
    if programs_with_errors or submission_allowed is False and assignment.deadline is not None:
        program_not_ready = True
    if submittedFiles and submittedFiles[0].is_stale:
        disable_grading = True

    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')
    courseHistory = CourseHistory.objects.get(user=request.user, course=course)
    if courseHistory.is_owner:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
    total_sumissions = Upload.objects.filter(assignment=assignment).count()
    isSubmitted = Upload.objects.filter(assignment=assignment).count() > 0
    get_params = {'source': 'assignment', 'id': assignmentID}
    allowed_exam = False
    timer = timedelta(seconds=0)
    if is_moderator:
        allowed_exam = True
    elif assignment.type_of_lab != 'Exam' or assignment.deadline < timezone.now():
        allowed_exam = True
    elif not ip_correct:
        submission_allowed = False

    elif assignment.type_of_lab == 'Exam' and ip_correct and submission_allowed and not is_moderator:
        oldproc = Proctoring.objects.filter(
            owner=request.user,
            key=assignment.exam_group_id
        )
        if oldproc:
            # print "Curr time :",datetime.utcnow()
            correct = validateuser(request, assignment)
            if correct:
                try:
                    obj = Proctoring.objects.get(
                        owner=request.user, key=assignment.exam_group_id)
                    timer = obj.time
                except Proctoring.DoesNotExist:
                    timer = timedelta(seconds=0)

                allowed_exam = True
            else:
                allowed_exam = False

        else:
            elapsed_time = timezone.now() - assignment.publish_on
            # elapsed_time = datetime.utcnow() - assignment.publish_on
            # print elapsed_time,assignment.publish_on
            if elapsed_time > assignment.late_duration:

                late_time = assignment.timeduration - elapsed_time
                if late_time <= timedelta(seconds=0):
                    times = timedelta(seconds=0)
                else:
                    times = late_time
            else:
                times = assignment.timeduration
            # print times
            proc = Proctoring(
                owner=request.user,
                assignment=assignment,
                ipAddress=ipadd,
                time=times,
                pause=False,
                status=True,
                addtime=timedelta(seconds=0),
                key=assignment.exam_group_id,
                starttime=DateTime.datetime.now()
            )
            proc.save()
            if not Pausetimer.objects.filter(key=assignment.exam_group_id):
                pausetimer = Pausetimer(
                    assignment=assignment,
                    pause=False,
                    key=assignment.exam_group_id,
                    additionaltime=timedelta(seconds=0),
                )
                pausetimer.save()
            timer = times
            allowed_exam = True
        if timer <= timedelta(seconds=1):
            is_due = True
            submission_allowed = False

    # All submission changes by Jitendra
    deadline = get_assignment_deadline(request, assignment)
    que = 'SELECT DISTINCT submission_id as id FROM upload_latestsubmission WHERE assignment_id =' + assignmentID + ';'
    number_of_submissions = LatestSubmission.objects.raw(que)
    number_of_submissions = len(list(number_of_submissions))
    if assignment.type_of_lab == "Lab":
        rem_time = int(
            (assignment.deadline - datetime.now(pytz.timezone('UTC'))).total_seconds())
    elif assignment.type_of_lab == "Exam":
        (rem_time, __, allowed_exam_status) = get_object_from_proctoring(
            assignment.exam_group_id, request.user)

    pause_all = Pausetimer.objects.filter(key=assignment.exam_group_id)

    if pause_all and pause_all[0].pause:
        student_ = Proctoring.objects.filter(
            owner=request.user,
            key=assignment.exam_group_id
        )
        for obj in student_:
            obj.pause = True
            obj.save()
        allowed_exam_status = False
        allowed_exam = False

    if request.method == "POST" and submission_allowed and ip_correct and assignment.deadline is not None:
        form = UploadForm(request.POST, request.FILES,
                          assignment_model_obj=assignment)
        if form.is_valid():
            new_upload = Upload(
                owner=request.user,
                assignment=assignment,
                filePath=request.FILES['docfile']
            )
            new_upload.save()

            submissions = Upload.objects.filter(
                assignment=new_upload.assignment).order_by('-uploaded_on')
            submission_to_evaluate = LatestSubmission.objects.filter(assignment=new_upload.assignment).filter(
                owner=request.user)
            if submission_to_evaluate:
                submission_to_evaluate[0].submission = submissions[0]
                submission_to_evaluate[0].save()
            else:
                submission_to_evaluate = LatestSubmission()
                submission_to_evaluate.assignment = new_upload.assignment
                submission_to_evaluate.owner = request.user
                submission_to_evaluate.submission = new_upload
                submission_to_evaluate.save()

            return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignmentID}))
    else:
        form = UploadForm()

    return render_to_response(
        'assignments/details.html',
        {'assignment': assignment, 'timer': timer, 'course': course, 'has_joined': has_joined,
         'is_moderator': is_moderator, 'programs': programs, 'form': form,
         'submission_allowed': submission_allowed, 'allowed_exam': allowed_exam, 'submittedFiles': submittedFiles,
         'programs_with_errors': programs_with_errors, 'disable_grading': disable_grading,
         'program_not_ready': program_not_ready, 'practice_program': practice_program,
         'assignments': assignments, 'program_errors': program_errors, 'test_errors': test_errors,
         'published': assignment.publish_on, 'is_due': is_due, 'rem_time': rem_time,
         'isSubmitted': isSubmitted, 'date_time': timezone.now(), 'get_params': get_params,
         'total_sumissions': total_sumissions, 'mode': mode, 'best_submission': best_submission,
         'assignmentID': assignmentID, 'now': timezone.now(), 'evaluate_program': evaluate_program,
         'formData': formData, 'number_of_submissions': number_of_submissions, 'user_id': request.user,
         'allowed_exam_status': allowed_exam_status, 'taList': get_ta_allocation(request, assignmentID),
         'deadline': deadline},
        context_instance=RequestContext(request),
    )


def get_assignment_deadline(request, _assignment):
    """
    :param request:
    :param _assignment:
    :return: Return dealine of assignment
    """
    # tz1 = timedelta(minutes=330)
    if _assignment.type_of_lab == 'Exam':
        if _assignment.deadline < timezone.now():
            return _assignment.deadline
        proctor = Proctoring.objects.filter(
            owner=request.user, assignment=_assignment)
        if not proctor:
            return timezone.now() + _assignment.timeduration
        time_left = proctor[0].time - (timezone.now() - proctor[0].starttime)
        if time_left.days < 0:
            return proctor[0].starttime + proctor[0].time
        return timezone.now() + time_left
    return _assignment.deadline


@login_required
def assignments_hide(request, assignment_id):
    """
    Hidding assignment from students from assignment page
    """
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment = Assignment.objects.filter(trash=False).get(id=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment.hide = True
    # log(request.user,'Hid ASSIGNMENT',{'hide':assignment.hide})
    assignment.save()
    return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignment_id}))


@login_required
def assignments_hide1(request, pk, assignment_id):
    """
    Hiding assignment from students from exam page
    """
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment = Assignment.objects.filter(trash=False).get(id=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment.hide = True
    assignment.save()
    return HttpResponseRedirect(reverse('course', kwargs={'pk': pk, 'ref': "exams"}))


@login_required
def assignments_unhide(request, assignment_id):
    """
    Unhide assignment for students from assignment page
    """
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment = Assignment.objects.filter(trash=False).get(id=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment.hide = False
    # log(request.user,'UnHid ASSIGNMENT',{'hide':assignment.hide})
    assignment.save()
    return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignment_id}))


@login_required
def assignments_unhide1(request, pk, assignment_id):
    """
    Unhide assignment for students from exam page
    """
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment = Assignment.objects.filter(trash=False).get(id=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    assignment.hide = False
    assignment.save()
    return HttpResponseRedirect(reverse('course', kwargs={'pk': pk, 'ref': "exams"}))


@login_required
def editAssignment(request, assignmentID, tabID):
    ''' Only creator of the course can edit this assignment'''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    course = assignment.course.id
    # For listing of assignments in the sidebar
    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')
    courseHistory = CourseHistory.objects.get(user=request.user, course=course)
    if courseHistory.is_owner:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]

    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    if request.method == 'POST':
        request.POST['courseID'] = assignment.course.id
        form = AssignmentForm(request.POST, request.FILES,
                              initial=model_to_dict(assignment))
        form.assignment_model = assignment

        if form.is_valid():
            # check if duration field is changed
            if 'duration' in form.changed_data:
                assignment.publish_type = "On Demand"
                assignment.deadline = None
                assignment.freezing_deadline = None

            # check if new file is uploaded
            if 'document' in form.changed_data:
                if assignment.document:
                    assignment.document.delete(save=False)
                if not form.cleaned_data['document']:
                    form.cleaned_data.pop('document')

            if 'helper_code' in form.changed_data:
                if assignment.helper_code:
                    assignment.helper_code.delete(save=False)
                if not form.cleaned_data['helper_code']:
                    form.cleaned_data.pop('helper_code')

            if 'model_solution' in form.changed_data:
                if assignment.model_solution:
                    assignment.model_solution.delete(save=False)
                if not form.cleaned_data['model_solution']:
                    form.cleaned_data.pop('model_solution')

            if 'freezing_deadline' in form.changed_data:
                app.control.revoke(
                    assignment.deletesubmissions_task_id, terminate=True)
                delete_task = delete_redundant_files.apply_async((assignment.id,),
                                                                 eta=form.cleaned_data['freezing_deadline'])
                assignment.deletesubmissions_task_id = delete_task.id

            if 'ta_allocation_document' in form.changed_data:
                if assignment.ta_allocation_document:
                    assignment.ta_allocation_document.delete(save=False)
                if not form.cleaned_data['ta_allocation_document']:
                    form.cleaned_data.pop('ta_allocation_document')

            if 'type_of_allocation' in form.changed_data or 'previous_allocation_policy' in form.changed_data:
                if form.cleaned_data['type_of_allocation'] == 'Use Previous Allocation Policy':
                    assignment.previous_allocation_policy = form.cleaned_data[
                        'previous_allocation_policy']
                    assignment.save()
                    previous_assignment_id = assignment.previous_allocation_policy.id
                    perform_ta_allocation(request, assignment.id, form.cleaned_data, allocation_type='Previous',
                                          previous_assignment_id=previous_assignment_id)
                elif form.cleaned_data['type_of_allocation'] == 'Automated':
                    perform_ta_allocation(request, assignment.id, form.cleaned_data, allocation_type='Automated',
                                          previous_assignment_id=None)
                else:
                    pass
            if 'bulk_add' in form.changed_data:
                if assignment.bulk_add:
                    assignment.bulk_add.delete(save=False)
                    progid = Program.objects.filter(
                        assignment_id=assignment.id)
                    for row in progid:  # deleting all the sections and their testcases on ticking clear
                        row.delete()

                    creater = get_object_or_404(User, pk=assignment.creater_id)
                    creater_name = User.objects.filter(username=creater)
                    creater_name = (
                        (str(creater_name).split(':')[-1])[:-2])[1:]

                    course = get_object_or_404(Course, pk=assignment.course_id)
                    course_name = Course.objects.filter(title=course)
                    course_name = ((str(course_name).split(':')[-1])[:-2])[1:]

                    folder_name = os.path.join(
                        settings.MEDIA_ROOT, creater_name, course_name, assignment.name)

                    if os.path.isdir(folder_name):
                        shutil.rmtree(folder_name)

                if not form.cleaned_data['bulk_add']:
                    form.cleaned_data.pop('bulk_add')
            for key in form.cleaned_data.keys():
                setattr(assignment, key, form.cleaned_data[key])

            for afield in ['model_solution', 'student_program_files', 'program_language']:
                if afield in form.changed_data:
                    assignment.verify_programs = True
                    assignment.program_model = Program
                    assignment.changed_list = form.changed_data
                    break
            assignment.save()

            if 'ta_allocation_document' in form.changed_data and 'ta_allocation_document' in form.cleaned_data:
                perform_ta_allocation(request, assignment.id, form.cleaned_data, allocation_type='New',
                                      previous_assignment_id=None)

            if 'bulk_add' in form.changed_data and assignment.bulk_add:
                section_bulk_add(assignment)

            if any(f in ['student_program_files'] for f in form.changed_data):
                all_submissions = Upload.objects.select_related('owner').select_for_update().\
                    filter(assignment=assignment)
                all_submissions.update(is_stale=True)

                subject_line = "Please re-submit assignment '{0}' of the course '{1}'".format(assignment.name,
                                                                                              assignment.course.title)
                message = "Course '{0}' assignment '{1}' specification has been changed since you submit\
                 your assignment last time. \
                You are required to submit your assignment again. \
                Your current submission will not be considered.".format(assignment.course.title, assignment.name)
                message_from = 'noreply@evalpro'
                with transaction.atomic():
                    message_to = [a.owner.email for a in all_submissions]
                try:
                    send_mail(subject_line, message, message_from,
                              message_to, fail_silently=False)
                    messages.add_message(request, messages.SUCCESS,
                                         "Students have been successfully informed about the changes.")
                except Exception as e:
                    print e.message, type(e)
                    messages.add_message(
                        request, messages.ERROR, "Students have not been informed about the changes.")
            tabid = int(request.POST.get('name_tabid', 0))
            if request.POST.get("Publish"):
                return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignmentID}))
            return HttpResponseRedirect(reverse('assignments_edit', kwargs={'assignmentID': assignmentID,
                                                                            'tabID': tabid}))
    else:
        form = AssignmentForm(initial=model_to_dict(
            assignment), courseID=assignment.course.id)
    course = assignment.course
    return render_to_response(
        'assignments/edit.html',
        {'assignment': assignment, 'form': form, 'course': course, 'is_moderator': is_moderator,
         'assignments': assignments, 'tabID': tabID, 'taList': get_ta_allocation(request, assignmentID)},
        context_instance=RequestContext(request))


@login_required
def createAssignment(request, courseID, exams=0):
    '''
    Logic for creating assignment
    '''
    course = get_object_or_404(Course, pk=courseID)
    is_moderator = isCourseModerator(course, request.user)
    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')
    courseHistory = CourseHistory.objects.get(user=request.user, course=course)
    if courseHistory.is_owner:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    if request.method == 'POST':
        # if "save-as-draft" in request.POST:

        if exams == 0:
            request.POST['courseID'] = courseID
            form = AssignmentForm(request.POST, request.FILES)
            form.this_course = course
            tabid = int(request.POST.get('name_tabid', 1))
            if form.is_valid():
                check_duration_field = form.cleaned_data['duration']
                if check_duration_field is not None:   # on-demand
                    form.cleaned_data['assignment_type'] = False
                new_assignment = Assignment(**form.cleaned_data)
                new_assignment.course = course
                new_assignment.creater = request.user
                new_assignment.serial_number = (Assignment.objects.filter(course=course).filter(trash=False)
                                                .aggregate(Max('serial_number'))
                                                ['serial_number__max'] or 0) + 1
                if new_assignment.correctness is None:
                    new_assignment.correctness = False
                if new_assignment.order is None:
                    new_assignment.order = False
                if new_assignment.error is None:
                    new_assignment.error = 0.0

                new_assignment.save()

                if new_assignment.publish_type == "On Demand":
                    pass
                else:
                    delete_task = delete_redundant_files.apply_async((new_assignment.id,),
                                                                     eta=new_assignment.freezing_deadline)
                    new_assignment.deletesubmissions_task_id = delete_task.id
                new_assignment.save()
                if new_assignment.bulk_add:
                    section_bulk_add(new_assignment)

                link = reverse('assignments_createprogram', kwargs={
                               'assignmentID': new_assignment.id})
                messages.success(request, 'Assignment Created! Now <a href="{0}">ADD</a> programs to assignment.'
                                 .format(link), extra_tags='safe')
                if new_assignment.type_of_allocation == 'New Allocation Policy':
                    perform_ta_allocation(request, new_assignment.id, form.cleaned_data, allocation_type='New',
                                          previous_assignment_id=None)
                elif new_assignment.type_of_allocation == 'Use Previous Allocation Policy':
                    previous_assignment_id = new_assignment.previous_allocation_policy.id
                    perform_ta_allocation(request, new_assignment.id, form.cleaned_data, allocation_type='Previous',
                                          previous_assignment_id=previous_assignment_id)
                else:
                    perform_ta_allocation(request, new_assignment.id, form.cleaned_data, allocation_type='Automated',
                                          previous_assignment_id=None)
                tabid = int(request.POST.get('name_tabid', 1))
                if request.POST.get("Publish"):
                    return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID':
                                                                                       new_assignment.id}))
                return HttpResponseRedirect(reverse('assignments_edit', kwargs={'assignmentID': new_assignment.id,
                                                                                'tabID': tabid}))
        else:
            try:
                _ = Assignment.objects.get(
                    name=request.POST['name'], course=course)
                data = {"success": False,
                        "error": 'This assignment already exists in this course.'}
            except Assignment.DoesNotExist:
                try:
                    new_assignment = Assignment(
                        course_id=courseID,
                        name=request.POST['name'],
                        type_of_lab=request.POST['type_of_lab'],
                        publish_type=request.POST['publish_type'],
                        description=request.POST['description'],
                        type_of_allocation=request.POST['type_of_allocation']
                    )
                    tabid = int(request.POST.get('name_tabid', 1))
                    new_assignment.creater = request.user
                    new_assignment.serial_number = (Assignment.objects.filter(course=course).filter(trash=False)
                                                    .aggregate(Max('serial_number'))
                                                    ['serial_number__max'] or 0) + 1
                    data = {'success': True}
                    if 'indentation' in request.POST and request.POST['indentation'] == "True":
                        new_assignment.indentation = request.POST['indentation']
                    if 'force_notify' in request.POST and request.POST['force_notify'] == "True":
                        new_assignment.force_notify = request.POST['force_notify']
                    if 'execution_time_allowed' in request.POST and request.POST['execution_time_allowed'] == "True":
                        new_assignment.execution_time_allowed = request.POST['execution_time_allowed']
                    if 'force_notify' in request.POST and request.POST['force_notify'] == "True":
                        new_assignment.force_notify = request.POST['force_notify']
                    serializer = AssignmentDetailsSerializer(data=request.POST)
                    if not serializer.is_valid():
                        return Response(serializer.errors, status.HTTP_400_BAD_REQUEST)
                    if 'publish_on' in request.POST:
                        new_assignment.publish_on = local2utc(
                            serializer.validated_data['publish_on'])
                    if 'deadline' in request.POST:
                        new_assignment.deadline = local2utc(
                            serializer.validated_data['deadline'])
                    if 'hard_deadline' in request.POST:
                        if 'deadline' in request.POST and request.POST['deadline'] > request.POST['hard_deadline']:
                            data = {
                                "success": False, "error": 'Hard deadline should be later than deadline.'}
                        new_assignment.freezing_deadline = local2utc(
                            serializer.validated_data['hard_deadline'])
                    if new_assignment.publish_type == "Scheduled":
                        delete_task = delete_redundant_files.apply_async((new_assignment.id,),
                                                                         eta=new_assignment.freezing_deadline)
                        new_assignment.deletesubmissions_task_id = delete_task.id
                    if 'duration' in request.POST:
                        new_assignment.duration = request.POST['duration']
                    if 'freezing_duration' in request.POST:
                        new_assignment.freezing_duration = request.POST['freezing_duration']
                    if 'student_program_files' in request.POST:
                        new_assignment.student_program_files = request.POST['student_program_files']
                        err_msg = check_program_files(request)
                        if err_msg != '':
                            data = {"success": False, "error": err_msg}
                    if 'ipaddress' in request.POST:
                        if is_valid_ip(request.POST['ipaddress']):
                            new_assignment.ipaddress = request.POST['ipaddress']
                        else:
                            data = {"success": False,
                                    "error": 'Invalid ipaddress'}
                    if new_assignment.type_of_lab == 'Exam':
                        if 'timeduration' in request.POST:
                            new_assignment.timeduration = request.POST['timeduration']
                        else:
                            data = {"success": False,
                                    "error": 'Enter a timeduration for exam.'}
                        if 'exam_group_id' in request.POST:
                            new_assignment.exam_group_id = request.POST['exam_group_id']
                        else:
                            data = {"success": False,
                                    "error": 'Enter a group key  for exam.'}
                        if 'late_duration' in request.POST:
                            new_assignment.late_duration = request.POST['late_duration']
                        else:
                            data = {
                                "success": False, "error": 'Enter a late start timeduration for exam.'}
                    if 'only_uploads' in request.POST and request.POST['only_uploads'] == "True":
                        new_assignment.only_uploads = request.POST['only_uploads']
                    if 'program_language' in request.POST:
                        new_assignment.program_language = request.POST['program_language']
                        if 'graphics_program' in request.POST and request.POST['graphics_program'] == "True":
                            new_assignment.graphics_program = request.POST['graphics_program']
                    if 'force_upload' in request.POST:
                        new_assignment.force_upload = request.POST['force_upload']
                    if 'correctness' in request.POST and request.POST['correctness'] == "True":
                        new_assignment.correctness = request.POST['correctness']

                    if 'order' in request.POST and request.POST['order'] == "True":
                        new_assignment.order = request.POST['order']
                    if 'error' in request.POST:
                        new_assignment.error = float(request.POST['error'])
                    if 'document' in request.FILES:
                        new_assignment.document = request.FILES['document']
                    if 'helper_code' in request.FILES:
                        new_assignment.helper_code = request.FILES['helper_code']
                    if 'model_solution' in request.FILES:
                        new_assignment.model_solution = request.FILES['model_solution']
                        with Archive(fileobj=request.FILES['model_solution']) as archive:
                            if not archive.is_archive() and not is_valid(filename=request.FILES['model_solution'].name,
                                                                         lang=data['program_language']):
                                data = {
                                    "success": False, "error": 'Enter valid model solution files.'}
                    if not data['success']:
                        return HttpResponse(json.dumps(data), content_type="application/json")
                    new_assignment.save()
                    if new_assignment.type_of_allocation == 'New Allocation Policy':
                        msg = check_allocation_doc(
                            request.FILES['ta_allocation_document'], courseID)
                        if msg != '':
                            data = {"success": False, "error": msg}
                        else:
                            new_assignment.ta_allocation_document = request.FILES[
                                'ta_allocation_document']
                            perform_ta_allocation(request, new_assignment.id,
                                                  {'ta_allocation_document': request.FILES['ta_allocation_document']},
                                                  allocation_type='New', previous_assignment_id=None)
                    elif new_assignment.type_of_allocation == 'Use Previous Allocation Policy':
                        try:
                            previous_assignment = Assignment.objects.get(
                                pk=request.POST['previous_allocation_policy'])
                            new_assignment.previous_allocation_policy = previous_assignment
                            previous_assignment_id = new_assignment.previous_allocation_policy.id
                            perform_ta_allocation(request, new_assignment.id, {}, allocation_type='Previous',
                                                  previous_assignment_id=previous_assignment_id)
                        except Exception, e:
                            data = {"success": False, "error": e}
                    else:
                        perform_ta_allocation(request, new_assignment.id, {},
                                              allocation_type='Automated',
                                              previous_assignment_id=None)

                    if 'bulk_add' in request.FILES:
                        new_assignment.bulk_add = request.FILES['bulk_add']
                        bulk_add_check(request.FILES)
                        section_bulk_add(new_assignment)
                    if not data['success']:
                        return HttpResponse(json.dumps(data), content_type="application/json")

                    new_assignment.save()
                    data = {"success": True}
                except Exception, e:
                    data = {"success": False, "error": e}
            return HttpResponse(json.dumps(data), content_type="application/json")
    else:
        form = AssignmentForm(courseID=courseID)
        tabid = 1
    return render_to_response(
        'assignments/createAssignment.html',
        {'form': form, 'course': course, 'is_moderator': is_moderator, 'assignments': assignments,
         'tabID': tabid},
        context_instance=RequestContext(request))


@login_required
def perform_ta_allocation(request, assignment_id, data, allocation_type, previous_assignment_id):
    '''function to map students with TA '''
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    course = assignment.course
    allocation_entries = TA_allocation.objects.filter(assignment=assignment)
    if allocation_entries:
        for allocation_object in allocation_entries:
            allocation_object.delete()

    if allocation_type == 'New':
        allocation_file = data['ta_allocation_document']
        if allocation_file:
            filepath = os.path.join(settings.MEDIA_ROOT, str(
                assignment.ta_allocation_document))
            with open(filepath, 'rb') as csvfile:
                reader = csv.reader(csvfile, delimiter=',')
                count = 0
                for row in reader:
                    row[0] = str(row[0]).strip()
                    row[1] = str(row[1]).strip()
                    if count == 0:
                        pass
                    else:
                        student = User.objects.filter(username=str(row[0]))
                        teaching_assistant = User.objects.filter(
                            username=str(row[1]))
                        new_ta_allocation = TA_allocation()
                        new_ta_allocation.assignment = assignment
                        new_ta_allocation.student = student[0]
                        new_ta_allocation.assistant = teaching_assistant[0]
                        new_ta_allocation.save()
                    count = count + 1

    elif allocation_type == 'Previous':
        previous_assignment = get_object_or_404(
            Assignment, pk=previous_assignment_id)
        allocation_objects = TA_allocation.objects.filter(
            assignment=previous_assignment)
        for allocation_object in allocation_objects:
            new_allocation = deepcopy(allocation_object)
            new_allocation.id = None
            new_allocation.assignment = assignment
            new_allocation.save()

    else:
        ta_list = CourseHistory.objects.filter(course=course).filter(
            is_creator=False).filter(is_owner=True)
        student_list = CourseHistory.objects.filter(
            course=course).filter(is_creator=False).filter(is_owner=False)
        if not ta_list or not student_list:
            return
        mod_variable = len(ta_list)
        if mod_variable == 0:
            mod_variable = 1
        count = 1
        for student in student_list:
            new_ta_allocation = TA_allocation()
            new_ta_allocation.assignment = assignment
            student_object = get_object_or_404(User, pk=student.user.id)
            new_ta_allocation.student = student_object
            ta_object = get_object_or_404(
                User, pk=ta_list[count % mod_variable].user.id)
            new_ta_allocation.assistant = ta_object
            new_ta_allocation.save()
            count = count+1

    return


def check_program_files(request):
    '''
    Function to validate student_program_files field
    :param request: request
    :return:
    '''
    err_msg = ''
    file_list = request.POST['student_program_files'].split()
    language = request.POST['program_language']
    for afile in file_list:
        if not is_valid(afile, language) and not request.POST['force_upload']:
            err_msg = "Only {1} files are accepted for {0} language.\
                        ".format(language, " ".join(get_extension(language)))
            return err_msg
    students_file = set(request.POST['student_program_files'].split())
    solution_file = []
    if 'model_solution' in request.FILES:
        with Archive(fileobj=request.FILES['model_solution']) as archive:
            if not archive.is_archive():
                if is_valid(filename=request.FILES['model_solution'].name, lang=request.POST['program_language']):
                    solution_file = [request.FILES['model_solution'].name]
                else:
                    err_msg = "Invalid file in model solution"
                    return err_msg
            else:
                solution_file = [a.split("/")[-1]
                                 for a in archive.getfile_members()]
        missing_file = students_file - set(solution_file)

        if missing_file and solution_file:
            err_msg = "{0} was not found. Please upload \
                        {1}".format(" ".join(missing_file), request.FILES['student_program_files'])

    return err_msg


@login_required
def removeAssignment(request, assignmentID):
    '''
    Logic for deleting assignment from assignment page
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course

    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    creater = get_object_or_404(User, pk=assignment.creater_id)
    creater_name = User.objects.filter(username=creater)
    creater_name = ((str(creater_name).split(':')[-1])[:-2])[1:]

    course = get_object_or_404(Course, pk=assignment.course_id)
    course_name = Course.objects.filter(title=course)
    course_name = ((str(course_name).split(':')[-1])[:-2])[1:]

    if not assignment.trash:
        assignment.trash = True
        assignment.save()
        return HttpResponseRedirect(reverse('assignments_index', kwargs={'courseID': course.id}))
    else:
        folder_name = os.path.join(
            settings.MEDIA_ROOT, creater_name, course_name, assignment.name)
        if os.path.isdir(folder_name):
            shutil.rmtree(folder_name)
        assignment.delete()
        return HttpResponseRedirect(reverse('assignments_trash', kwargs={'courseID': course.id}))


@login_required
@is_moderator_check
def removeAssignment1(request, assignmentID):
    '''
    Delete of assignment from exam page
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course

    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    creater = get_object_or_404(User, pk=assignment.creater_id)
    creater_name = User.objects.filter(username=creater)
    creater_name = ((str(creater_name).split(':')[-1])[:-2])[1:]

    course = get_object_or_404(Course, pk=assignment.course_id)
    course_name = Course.objects.filter(title=course)
    course_name = ((str(course_name).split(':')[-1])[:-2])[1:]

    if not assignment.trash:
        assignment.trash = True
        assignment.save()
        return HttpResponseRedirect(reverse('course', kwargs={'pk': assignment.course_id, 'ref': "exams"}))
    else:
        folder_name = os.path.join(
            settings.MEDIA_ROOT, creater_name, course_name, assignment.name)
        if os.path.isdir(folder_name):
            shutil.rmtree(folder_name)
        assignment.delete()
        return HttpResponseRedirect(reverse('assignments_trash', kwargs={'courseID': course.id}))


@login_required
@is_moderator_check
def restoreAssignment(request, assignmentID):
    '''function to restore assignments from trash'''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course
    if assignment.trash:
        assignment.trash = False
        assignment.save()
    return HttpResponseRedirect(reverse('assignments_trash', kwargs={'courseID': course.id}))


@login_required
@is_moderator_check
def showAssignmentsTrash(request, courseID):
    '''function to show trash assignments'''
    course = get_object_or_404(Course, pk=courseID)
    trashAssignments = course.get_assignments.all().filter(trash=True)
    return render_to_response(
        'assignments/showAssignmentsTrash.html',
        {'course': course, 'trashAssignments': trashAssignments},
        context_instance=RequestContext(request))


@login_required
def createProgram(request, assignmentID):
    '''
    Only creator of course can create new program in assignment.
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course

    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if request.method == 'POST':
        lang_category = language_category(assignment.program_language)
        if lang_category == 0:  # Compilation needed. Execution not needed. C and C++
            form = ProgramFormCNotE(request.POST, request.FILES)
        elif lang_category == 1:  # Compilation and execution needed.
            form = ProgramFormCandE(request.POST, request.FILES)
        elif lang_category == 2:  # Execution needed. Python and bash
            form = ProgramFormE(request.POST, request.FILES)
        form.assignment = assignment  # files submitted by student
        if form.is_valid():
            new_program = Program(**form.cleaned_data)
            new_program.assignment = assignment
            new_program.is_sane = True
            new_program.compile_now = True
            new_program.execute_now = True
            new_program.language = assignment.program_language
            new_program.save()

            if new_program.testcase_bulk_add:
                testcase_bulk_add(new_program)

            link = reverse('assignments_createtestcase',
                           kwargs={'programID': new_program.id})
            messages.success(request,
                             'Section Created! Now <a href="{0}">ADD</a> testcase for this program.'.format(
                                 link),
                             extra_tags='safe')
            list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                                      .filter(assignment=assignment)]
            all_submissions = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                                    pk__in=list_of_assignment_ids).order_by("-uploaded_on")
            AssignmentResults.objects.filter(
                submission__in=all_submissions).update(is_stale=True)
            return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignmentID}))
    else:
        objs = Program.objects.filter(assignment=assignment)
        initial = {}
        lang_category = language_category(assignment.program_language)
        if objs:
            if lang_category == 0:
                comp_command = pickle.loads(objs[0].compiler_command)
                initial['compiler_command'] = pickle.dumps(
                    [comp_command[0], '', ''])
            elif lang_category == 1:
                comp_command = pickle.loads(objs[0].compiler_command)
                initial['compiler_command'] = pickle.dumps(
                    [comp_command[0], '', ''])
                exe_command = pickle.loads(objs[0].execution_command)
                initial['execution_command'] = pickle.dumps(
                    [exe_command[0], '', ''])
            elif lang_category == 2:
                exe_command = pickle.loads(objs[0].execution_command)
                initial['execution_command'] = pickle.dumps(
                    [exe_command[0], '', ''])
        else:
            if lang_category == 0:
                comp_command = get_compiler_name(assignment.program_language)
                initial['compiler_command'] = pickle.dumps(
                    [comp_command, '', ''])
            elif lang_category == 1:
                comp_command = get_compiler_name(assignment.program_language)
                initial['compiler_command'] = pickle.dumps(
                    [comp_command, '', ''])
                exe_command = get_interpreter_name(assignment.program_language)
                initial['execution_command'] = pickle.dumps(
                    [exe_command, '', ''])
            elif lang_category == 2:
                exe_command = get_interpreter_name(assignment.program_language)
                initial['execution_command'] = pickle.dumps(
                    [exe_command, '', ''])
        if lang_category == 0:  # Compilation needed. Execution not needed. C and C++
            form = ProgramFormCNotE(initial=initial)
        elif lang_category == 1:  # Compilation and execution needed.
            form = ProgramFormCandE(initial=initial)
        elif lang_category == 2:  # Execution needed. Python and bash
            form = ProgramFormE(initial=initial)
    mark_submissions_false(assignment.id)
    course = assignment.course
    all_assignments = Assignment.objects.filter(course=course).filter(trash=False).order_by('-deadline')
    is_moderator = isCourseModerator(course, request.user)
    if is_moderator:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
    return render_to_response(
        'assignments/createProgram.html',
        {'form': form, 'assignment': assignment,
         'course': course, 'is_moderator': is_moderator, 'assignments': assignments},
        context_instance=RequestContext(request))


@login_required
def editProgram(request, programID):
    '''
    Logic for edit section
    '''
    program = get_object_or_404(Program, pk=programID)
    is_moderator = isCourseModerator(program.assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if request.method == 'POST':
        # form is initialized by model then overwritten by request data and files.
        lang_category = language_category(program.assignment.program_language)
        if lang_category == 0:  # Compilation needed. Execution not needed. C and C++
            form = ProgramFormCNotE(
                request.POST, request.FILES, initial=model_to_dict(program))
        elif lang_category == 1:  # Compilation and execution needed.
            form = ProgramFormCandE(
                request.POST, request.FILES, initial=model_to_dict(program))
        elif lang_category == 2:  # Execution needed. Python and bash
            form = ProgramFormE(request.POST, request.FILES,
                                initial=model_to_dict(program))
        form.assignment = program.assignment
        form.program_model = program
        if form.is_valid():
            # check if new file is uploaded
            if 'program_files' in form.changed_data:  # program_files are changed."
                if program.program_files:  # delete older file if any.
                    program.program_files.delete(save=False)
                # if file is being cleared.
                if not form.cleaned_data['program_files']:
                    form.cleaned_data.pop('program_files')

            if 'makefile' in form.changed_data:
                if program.makefile:
                    program.makefile.delete(save=False)
                if not form.cleaned_data['makefile']:
                    form.cleaned_data.pop('makefile')

            if 'testcase_bulk_add' in form.changed_data:
                if program.testcase_bulk_add:
                    folder_name = os.path.join(settings.MEDIA_ROOT, '/'.join(
                        (str(program.testcase_bulk_add)).split('/')[:-1]))
                    program.testcase_bulk_add.delete(save=False)
                    if not os.listdir(folder_name):
                        shutil.rmtree(folder_name)

                    testcaseid = Testcase.objects.filter(program_id=program.id)
                    for row in testcaseid:  # deleting all the testcases under that section on ticking clear
                        folder_name2 = ''
                        folder_name3 = ''
                        if row.input_files != '':
                            folder_name2 = os.path.join(settings.MEDIA_ROOT, '/'.join(
                                (str(row.input_files)).split('/')[:-1]))
                        if row.output_files != '':
                            folder_name3 = os.path.join(settings.MEDIA_ROOT, '/'.join(
                                (str(row.output_files)).split('/')[:-1]))
                        row.delete()
                        if folder_name2 != '' and os.listdir(folder_name2) == []:
                            shutil.rmtree(folder_name2)

                        if folder_name3 != '' and os.listdir(folder_name3) == []:
                            shutil.rmtree(folder_name3)

                if not form.cleaned_data['testcase_bulk_add']:
                    form.cleaned_data.pop('testcase_bulk_add')

            for key in form.cleaned_data.keys():
                setattr(program, key, form.cleaned_data[key])

            program.delete_error_message()
            program.is_sane = True
            for afield in ['program_files', 'compiler_command', 'makefile', 'execution_command']:
                if afield in form.changed_data:
                    program.compile_now = True
                    program.execute_now = True
                    break
            program.save()

            if 'testcase_bulk_add' in form.changed_data and program.testcase_bulk_add:
                testcase_bulk_add(program)

            # Mark all assignment results to stale if program_files/compiler_command/execution_command changed
            changed_fields = ['program_files']
            if program.compiler_command:
                changed_fields.append('compiler_command')
            if program.execution_command:
                changed_fields.append('execution_command')
            if set(changed_fields) - set(form.changed_data):
                list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                                          .filter(assignment=program.assignment)]
                all_submissions = Upload.objects.filter(assignment=program.assignment, assignment__trash=False,
                                                        pk__in=list_of_assignment_ids).order_by("-uploaded_on")
                AssignmentResults.objects.filter(
                    submission__in=all_submissions).update(is_stale=True)

            mark_submissions_false(program.assignment.id)
            return HttpResponseRedirect(reverse('assignments_detailsprogram', kwargs={'programID': programID}))
    else:
        lang_category = language_category(program.assignment.program_language)
        if lang_category == 0:  # Compilation needed. Execution not needed. C and C++
            form = ProgramFormCNotE(initial=model_to_dict(program))
        elif lang_category == 1:  # Compilation and execution needed.
            form = ProgramFormCandE(initial=model_to_dict(program))
        elif lang_category == 2:  # Execution needed. Python and bash
            form = ProgramFormE(initial=model_to_dict(program))
        mark_submissions_false(program.assignment.id)
    course = program.assignment.course
    all_assignments = Assignment.objects.filter(course=course).filter(trash=False).order_by('-deadline')
    all_programs = Program.objects.filter(assignment=program.assignment)
    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator and program.assignment.hide:
        raise PermissionDenied
    if is_moderator:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
    return render_to_response(
        'assignments/editProgram.html',
        {'form': form, 'program': program, 'course': course, 'assignments': assignments, 'programs': all_programs},
        context_instance=RequestContext(request)
    )


@login_required
def detailProgram(request, programID):
    ''' Section/Program display as per profile'''
    program = get_object_or_404(Program, pk=programID)
    testcases = Testcase.objects.filter(program=program)
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course
    has_submitted = Upload.objects.filter(owner=request.user, assignment=assignment)
    all_assignments = Assignment.objects.filter(course=course).filter(trash=False).order_by('-deadline')
    all_programs = Program.objects.filter(assignment=assignment)

    is_moderator = isCourseModerator(course, request.user)
    mode = get_mode(request)
    if not is_moderator and assignment.hide:
        raise PermissionDenied
    if is_moderator:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
    compiler_command = get_compilation_command(program)
    execution_command = get_execution_command(program)
    program_errors = None
    if not program.is_sane:
        try:
            program_errors = ProgramErrors.objects.get(program=program)
        except ProgramErrors.DoesNotExist:
            program_errors = None
    testcase_errors = []
    terror_ctype = ContentType.objects.get_for_model(TestcaseErrors)
    for error in AssignmentErrors.objects.filter(assignment=program.assignment, content_type=terror_ctype):
        testcase_errors.extend(
            TestcaseErrors.objects.filter(pk=error.object_id))
    get_params = {'source': 'section', 'id': programID}
    formData = ProgramFormCNotE(initial=model_to_dict(program))

    try:
        checker = Checker.objects.filter(program=program)
    except Checker.DoesNotExist:
        checker = None
    if checker:
        checker = checker[0]
    if request.method == "POST":
        try:
            if 'getstd' in request.POST:
                if request.POST.get('testID'):
                    testcaseid = int(request.POST.get('testID'))
                    testcase = Testcase.objects.filter(id=testcaseid)
                    if testcase:
                        testcase = testcase[0]
                        if testcase.program.program_type == 'Evaluate' and not is_moderator and not is_due:
                            response = HttpResponse(json.dumps({'stdin': mark_safe("HIDDEN :P"),
                                                                'stdout': mark_safe('HIDDEN :P')}),
                                                    content_type="application/json")
                            return response
                        std_in = ''
                        std_out = ''
                        try:
                            std_in = read_file(readthis=testcase.std_in_file_name,
                                               name=testcase.input_files.file.name)
                            testcase.input_files.close()
                        except Exception:
                            pass
                        try:
                            std_out = read_file(readthis=testcase.std_out_file_name,
                                                name=testcase.output_files.file.name)
                            testcase.output_files.close()
                        except Exception as e:
                            print e
                        std_in = ''.join(std_in)
                        std_out = ''.join(std_out)
                        try:
                            response = HttpResponse(json.dumps({'stdin': mark_safe(std_in),
                                                                'stdout': mark_safe(std_out)}),
                                                    content_type="application/json")
                            return response
                        except Exception as e:
                            print e
                            response = HttpResponse(json.dumps({'stdin': mark_safe("Can't display"),
                                                                'stdout': mark_safe('Can\'t Display')}),
                                                    content_type="application/json")
                            return response
            # if 'update' in request.POST:
            #     if request.POST.get('testID'):
            #         testcaseid = int(request.POST.get('testID'))
            #         testcase = Testcase.objects.filter(id=testcaseid)
            #         if testcase:
            #             std_in = request.POST.get('std_in')
            #             std_out = request.POST.get('std_out')
            #             i = Archive(name=testcase.input_files.file.name).open_file(testcase.std_in_file_name, 'w')
            #             i.write(std_in)
            #             i.close()
            #             testcase.input_files.close()
            #             o = Archive(name=testcase.input_files.file.name).open_file(testcase.std_in_file_name, 'w')
            #             o.write(std_in)
            #             o.close()
            #             testcase.output_files.close()
        finally:
            pass

    return render_to_response(
        'assignments/detailsProgram.html',
        {'programs': all_programs, 'program': program, 'testcases': testcases, 'assignment': assignment,
         'checker': checker, 'assignments': assignments, 'date_time': timezone.now(),
         'program_errors': program_errors, 'compiler_command': compiler_command,
         'execution_command': execution_command, 'course': course, 'is_moderator': is_moderator,
         'is_due': is_due, 'has_submitted': has_submitted, 'get_params': get_params, 'mode': mode,
         'testcase_errors': testcase_errors, 'programID': programID, 'formData': formData},
        context_instance=RequestContext(request)
    )


@login_required
def removeProgram(request, programID):
    '''Deletion logic for section/program'''
    program = get_object_or_404(Program, pk=programID)
    is_moderator = isCourseModerator(program.assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    assignment = program.assignment
    program.delete()
    return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignment.id}))


class CreateTestcaseWizard(SessionWizardView):
    '''
    Create testcase wizard class
    '''
    file_storage = default_storage
    template_name = 'assignments/createTestcasewizard.html'
    solution_ready = False  # Resolve defined outside __init__
    assignment_id = None  # Resolve defined outside __init__
    program_id = None
    testcase_id = None

    def dispatch(self, request, *args, **kwargs):
        '''
        dispatch function
        '''
        program_id = kwargs['programID']
        program = get_object_or_404(Program, pk=program_id)
        # self.solution_ready is used in from clean method.
        self.assignment_id = program.assignment.id
        self.program_id = program_id
        if Testcase.objects.filter(program=program):
            self.solution_ready = program.solution_ready
        else:
            self.solution_ready = bool(
                program.program_files or program.assignment.model_solution)

        is_moderator = isCourseModerator(
            program.assignment.course, request.user)
        if is_moderator:
            return super(CreateTestcaseWizard, self).dispatch(request, *args, **kwargs)
        return HttpResponseForbidden("Forbidden 403")

    def get_form_kwargs(self, step=None):
        if step == '0':
            return {'solution_ready': self.solution_ready, 'assignment_id': self.assignment_id,
                    'program_id': self.program_id}
        if step == '1':
            choice_dict = {}
            if self.storage.get_step_files('0'):
                if self.storage.get_step_files('0').get('0-input_files', ""):
                    f_in_obj = self.storage.get_step_files(
                        '0').get('0-input_files')
                    f_in_obj.open()
                    choice_dict['in_file_choices'] = [
                        (a, a) for a in get_file_name_list(fileobj=f_in_obj)]

                if self.storage.get_step_files('0').get('0-output_files', ""):
                    f_out_obj = self.storage.get_step_files(
                        '0').get('0-output_files')
                    f_out_obj.open()
                    choice_dict['out_file_choices'] = [
                        (b, b) for b in get_file_name_list(fileobj=f_out_obj)]
            choice_dict['assignment_id'] = self.assignment_id
            choice_dict['program_id'] = self.program_id
            return choice_dict
        else:
            return super(CreateTestcaseWizard, self).get_form_kwargs(step)

    def get_context_data(self, form, **kwargs):
        context = super(CreateTestcaseWizard, self).get_context_data(
            form=form, **kwargs)
        program = Program.objects.get(pk=self.kwargs['programID'])
        compiler_command = get_compilation_command(program)
        execution_command = get_execution_command(program)
        context.update({'program': program, 'compiler_command': compiler_command,
                        'execution_command': execution_command, 'assignment_id': program.assignment.id})
        return context

    def done(self, form_list, **kwargs):
        frmdict = form_list[0].cleaned_data
        frmdict.update(form_list[1].cleaned_data)
        program = Program.objects.get(pk=self.kwargs['programID'])
        frmdict.update({'program': program})

        Testcase.objects.create(**frmdict)

        # Remove temporary files
        if self.storage.get_step_files('0'):
            for a in self.storage.get_step_files('0').values():
                try:
                    os.remove(os.path.join(settings.MEDIA_ROOT, a.name))
                except Exception:
                    pass
        list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                                  .filter(assignment=program.assignment)]
        all_submissions = Upload.objects.filter(assignment=program.assignment, assignment__trash=False,
                                                pk__in=list_of_assignment_ids).order_by("-uploaded_on")
        AssignmentResults.objects.filter(
            submission__in=all_submissions).update(is_stale=True)
        mark_submissions_false(program.assignment.id)
        return HttpResponseRedirect(reverse('assignments_detailsprogram', kwargs={'programID':
                                                                                  self.kwargs['programID']}))


class EditTestcaseWizard(SessionWizardView):
    '''
    Edit testcase form
    '''
    file_storage = default_storage
    template_name = 'assignments/editTestcasewizard.html'
    solution_ready = False
    assignment_id = None
    program_id = None
    testcase_id = None

    def dispatch(self, request, *args, **kwargs):
        testcase_id = kwargs['testcaseID']
        testcase = get_object_or_404(Testcase, pk=testcase_id)
        program = testcase.program
        self.assignment_id = program.assignment.id
        self.program_id = program.id
        self.testcase_id = testcase_id
        # self.solution_ready is used in from clean method.
        self.solution_ready = bool(
            program.program_files or program.assignment.model_solution)
        is_moderator = isCourseModerator(
            program.assignment.course, request.user)
        if is_moderator:
            return super(EditTestcaseWizard, self).dispatch(request, *args, **kwargs)
        return HttpResponseForbidden("Forbidden 403")

    def get_form_initial(self, step):
        testcase = Testcase.objects.get(pk=self.kwargs['testcaseID'])
        return model_to_dict(testcase)

    def get_form_kwargs(self, step=None):
        if step == '0':
            return {'solution_ready': self.solution_ready, 'assignment_id': self.assignment_id,
                    'program_id': self.program_id}
        if step == '1':
            choice_dict = {}
            testcase = Testcase.objects.get(pk=self.kwargs['testcaseID'])
            # if there is at least one file.
            if self.storage.get_step_files('0'):
                # if input_file is uploaded.
                if self.storage.get_step_files('0').get('0-input_files', ""):
                    f_in_obj = self.storage.get_step_files(
                        '0').get('0-input_files')
                    f_in_obj.open()
                    choice_dict['in_file_choices'] = [(a, a)
                                                      for a in get_file_name_list(fileobj=f_in_obj)]
                elif testcase.input_files:  # provide options from older file.
                    choice_dict['in_file_choices'] = [(b, b)
                                                      for b in get_file_name_list(fileobj=testcase.input_files.file)]

                # if output_file is uploaded.
                if self.storage.get_step_files('0').get('0-output_files', ""):
                    f_out_obj = self.storage.get_step_files(
                        '0').get('0-output_files')
                    f_out_obj.open()
                    choice_dict['out_file_choices'] = [(b, b)
                                                       for b in get_file_name_list(fileobj=f_out_obj)]
                elif testcase.output_files:  # provide options from older file.
                    choice_dict['out_file_choices'] = [(b, b)
                                                       for b in get_file_name_list(fileobj=testcase.output_files.file)]

            else:  # No file uploaded in step 0
                if '0-input_files-clear' not in self.storage.get_step_data('0') and testcase.input_files:
                    choice_dict['in_file_choices'] = [(b, b)
                                                      for b in get_file_name_list(fileobj=testcase.input_files.file)]
                else:
                    pass
                if '0-output_files-clear' not in self.storage.get_step_data('0') and testcase.output_files:
                    choice_dict['out_file_choices'] = [(b, b)
                                                       for b in get_file_name_list(fileobj=testcase.output_files.file)]
            choice_dict['assignment_id'] = self.assignment_id
            choice_dict['program_id'] = self.program_id
            return choice_dict
        else:
            return super(EditTestcaseWizard, self).get_form_kwargs(step)

    def get_context_data(self, form, **kwargs):
        context = super(EditTestcaseWizard, self).get_context_data(
            form=form, **kwargs)

        testcase = Testcase.objects.get(pk=self.kwargs['testcaseID'])
        program = testcase.program
        compiler_command = get_compilation_command(program)
        execution_command = get_execution_command(program)
        context.update({'testcase': testcase, 'compiler_command': compiler_command,
                        'execution_command': execution_command})
        return context

    def done(self, form_list, **kwargs):
        frmdict = form_list[0].cleaned_data
        # consolidated list from both steps.
        frmdict.update(form_list[1].cleaned_data)
        testcase = Testcase.objects.get(pk=self.kwargs['testcaseID'])

        # either new file is being uploaded or older is cleared
        if 'input_files' in form_list[0].changed_data:
            if testcase.input_files:  # there was an older file in test-case
                testcase.input_files.delete(save=False)  # delete older file.
            if not form_list[0].cleaned_data['input_files']:  # no new file so do nothing
                form_list[0].cleaned_data.pop('input_files')

        if 'output_files' in form_list[0].changed_data:
            if testcase.output_files:
                testcase.output_files.delete(save=False)
            if not form_list[0].cleaned_data['output_files']:
                form_list[0].cleaned_data.pop('output_files')
        for key in frmdict.keys():  # update database table row.
            setattr(testcase, key, frmdict[key])
        testcase.save()

        files_change = set(['input_files', 'output_files']
                           ) - set(form_list[0].changed_data)
        stdIO_change = set(
            ['std_in_file_name', 'std_out_file_name']) - set(form_list[1].changed_data)
        if files_change or stdIO_change:
            testcase = Testcase.objects.get(pk=self.kwargs['testcaseID'])
            list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                                      .filter(assignment=testcase.program.assignment)]
            all_submissions = Upload.objects.filter(assignment=testcase.program.assignment, assignment__trash=False,
                                                    pk__in=list_of_assignment_ids).order_by("-uploaded_on")
            AssignmentResults.objects.filter(
                submission__in=all_submissions).update(is_stale=True)

        # Remove temporary files
        if self.storage.get_step_files('0'):
            for a in self.storage.get_step_files('0').values():
                try:
                    os.remove(os.path.join(settings.MEDIA_ROOT, a.name))
                except Exception:
                    pass
        mark_submissions_false(testcase.program.assignment.id)
        return HttpResponseRedirect(reverse('assignments_detailstestcase',
                                            kwargs={'testcaseID': self.kwargs['testcaseID']}))


def mark_submissions_false(assignment_id):
    """
        This functions marks all the submissions' evaluation status of a particular assignment as false.
         In case when we edit or add sections, test-cases, then evaluate all the submissions again.
    """
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    # list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
    #                           .filter(assignment=assignment)]
    all_submissions = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                            # pk__in=list_of_assignment_ids
                                            ).order_by("-uploaded_on")
    for submission in all_submissions:
        submission.to_be_evaluated = True
        submission.to_be_practiced = True
        submission.save()


@login_required
def detailTestcase(request, testcaseID):
    '''
    Detail of a testcase based on testcaseID
    '''
    testcase = get_object_or_404(Testcase, pk=testcaseID)
    course = testcase.program.assignment.course
    all_assignments = Assignment.objects.filter(course=course).filter(trash=False).order_by('-deadline')
    all_programs = Program.objects.filter(assignment=testcase.program.assignment)
    all_tc = Testcase.objects.filter(program=testcase.program)
    is_moderator = isCourseModerator(course, request.user)
    mode = get_mode(request)
    if not is_moderator and testcase.program.assignment.hide:
        raise PermissionDenied
    if is_moderator:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
    is_due = None
    if testcase.program.assignment.deadline is not None:
        is_due = (timezone.now() >= testcase.program.assignment.deadline)
    get_params = {'source': 'testcase', 'id': testcaseID}
    testcase_errors = TestcaseErrors.objects.filter(testcase=testcase)
    return render_to_response(
        'assignments/detailsTestcase.html',
        {'testcases': all_tc, 'programs': all_programs, 'testcase': testcase, 'assignments': assignments,
         'date_time': timezone.now(), 'course': course, 'is_due': is_due, 'is_moderator': is_moderator,
         'testcase_errors': testcase_errors, 'mode': mode, 'get_params': get_params},
        context_instance=RequestContext(request)
    )


@login_required
def removeTestcase(request, testcaseID):
    '''
    Deletion of testcase
    '''
    testcase = get_object_or_404(Testcase, pk=testcaseID)
    course = testcase.program.assignment.course
    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    program = testcase.program
    testcase.delete()
    return HttpResponseRedirect(reverse('assignments_detailsprogram', kwargs={'programID': program.id}))


@login_required
def config_safeexec_params(request, assignmentID):
    '''
    Logic to provide configuration for program or testcase
    set to default configuration; if no configuration change
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course
    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if request.method == 'POST':
        form = SafeExecForm(request.POST)
        source = request.POST.get('page_source', '')
        test_ids = request.POST.getlist('testcases_cbx')
        if form.is_valid():
            for test_id in test_ids:
                testcase_obj = get_object_or_404(Testcase, pk=test_id)
                obj = SafeExec.objects.filter(testcase=testcase_obj)

                if obj:
                    form.cleaned_data['testcase'] = testcase_obj
                    obj.update(**form.cleaned_data)
                else:
                    form.cleaned_data['testcase'] = testcase_obj
                    SafeExec.objects.create(**form.cleaned_data)

            return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignmentID}))
    else:
        default_limits = {'cpu_time': 10, 'clock_time': 60,
                          'memory': 32768, 'stack_size': 8192,
                          'child_processes': 0, 'open_files': 512,
                          'file_size': 1024}
        form = SafeExecForm(initial=default_limits)
        source = request.GET.get('source', '')
    if source == "section":
        section_id = request.GET.get('id', '')
        program = get_object_or_404(Program, pk=section_id)
        test_cases = Testcase.objects.filter(program=program)
        title = program.name
    elif source == "testcase":
        testcase_id = request.GET.get('id', '')
        test_cases = get_object_or_404(Testcase, pk=testcase_id)
        title = test_cases.name
    else:
        programs = Program.objects.filter(
            assignment=assignment).order_by('name')
        test_cases = []
        for a_program in programs:
            test_cases.append(Testcase.objects.filter(
                program=a_program).order_by('name'))
        title = assignment.name

    return render_to_response(
        'assignments/safeexec_params.html',
        {'form': form, 'testcases': test_cases, 'source': source,
            'title': title, 'assignment': assignment},
        context_instance=RequestContext(request)
    )


@login_required
def programList(request):
    '''
    Logic for displaying section/program list
    '''
    data = ''
    if request.is_ajax():
        if request.method == 'GET':
            assignmentID = request.GET['asgnid']
            assignment = get_object_or_404(Assignment, pk=assignmentID)
            programs = Program.objects.filter(
                assignment=assignment).order_by('-program_type', 'id')
            if programs:
                for program in programs:
                    link = reverse('assignments_detailsprogram',
                                   kwargs={'programID': program.id})
                    data = data + '<a class="list-group-item"  href="%s" id="prog_id-' + \
                        str(program.id) + '">'
                    data = data + '<span data-toggle="collapse" data-parent="#a%s" href="#p' + str(program.id) + \
                        '" class="sign programs"><span class="glyphicon glyphicon-plus"></span></span> '
                    data = data + program.name + \
                        ' (' + program.program_type + ')'
                    data = data + '<input type="hidden" class="progid" value="' + \
                        str(program.id) + '" />'
                    data = data + '<input type="hidden" class="loaded-testcases" value="1" /></a>'
                    data = data + '<div class="collapse list-group-submenu programs" id="p' + \
                        str(program.id) + '">'
                    data = data % (link, str(assignmentID))
                    program = get_object_or_404(Program, pk=program.id)
                    testcases = Testcase.objects.filter(
                        program=program).order_by('id')
                    if testcases:
                        for testcase in testcases:
                            link = reverse('assignments_detailstestcase', kwargs={
                                           'testcaseID': testcase.id})
                            data = data + '<a id="testcase_id-' + \
                                str(testcase.id)
                            data = data + \
                                '" class="list-group-item" href="{0}">' + \
                                testcase.name + '</a></li>'
                            data = data.format(link)
                    else:
                        data += '<a class="list-group-item">No testcases for this program</a>'
                    data = data + '</div>'

            else:
                if not assignment.only_uploads:
                    data = '<a  class="list-group-item">No programs for this assignment</a>'
        else:
            data = 'Error occurred'
    else:
        data = 'Error occurred'
    return HttpResponse(data)


@login_required
def testcaseList(request):
    '''
    Logic to display testcaselist
    '''
    data = ''
    if request.is_ajax():
        if request.method == 'GET':
            programID = request.GET['progid']
            program = get_object_or_404(Program, pk=programID)
            testcases = Testcase.objects.filter(program=program).order_by('id')
            if testcases:
                for testcase in testcases:
                    link = reverse('assignments_detailstestcase',
                                   kwargs={'testcaseID': testcase.id})
                    data = data + \
                        '<a class="list-group-item" href="{0}">' + \
                        testcase.name + '</a></li>'
                    data = data.format(link)
            else:
                data = '<a class="list-group-item">No testcases for this program</a>'
        else:
            data = 'Error occurred'
    else:
        data = 'Error occurred'
    return HttpResponse(data)


@login_required
def createChecker(request, programID):
    '''
    Logic for create checks
    '''
    program = get_object_or_404(Program, pk=programID)
    course = program.assignment.course

    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    try:
        checker = Checker.objects.filter(program=program)
    except Checker.DoesNotExist:
        checker = None
    if checker:
        messages.success(request, 'Checker Code already exists for this section!!',
                         extra_tags='safe')
        return HttpResponseRedirect(reverse('assignments_detailschecker', kwargs={'checkerID': checker[0].id}))

    if request.method == 'POST':
        form = CheckerCodeForm(request.POST, request.FILES)
        if form.is_valid():
            newChecker = Checker(**form.cleaned_data)
            newChecker.program = program
            newChecker.save()
            return HttpResponseRedirect(reverse('assignments_detailschecker', kwargs={'checkerID': newChecker.id}))
    else:
        initial = {}
        initial['execution_command'] = pickle.dumps(['python', '', ''])
        form = CheckerCodeForm(initial=initial)

    return render_to_response(
        'assignments/createChecker.html',
        {'form': form, 'program': program,
         'course': course, 'is_moderator': is_moderator},
        context_instance=RequestContext(request)
    )


@login_required
def editChecker(request, checkerID):
    '''
    Logic for checking modifications
    '''
    checker = get_object_or_404(Checker, pk=checkerID)
    is_moderator = isCourseModerator(
        checker.program.assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if request.method == 'POST':
        # form is initialized by model then overwritten by request data and files.
        form = CheckerCodeForm(request.POST, request.FILES,
                               initial=model_to_dict(checker))
        form.checker_model = checker
        if form.is_valid():
            # check if new file is uploaded
            if 'checker_files' in form.changed_data:  # program_files are changed."
                if checker.checker_files:  # delete older file if any.
                    checker.checker_files.delete(save=False)
                # if file is being cleared.
                if not form.cleaned_data['checker_files']:
                    form.cleaned_data.pop('checker_files')

            for key in form.cleaned_data.keys():
                setattr(checker, key, form.cleaned_data[key])

            checker.delete_error_message()
            checker.save()

            # Mark all assignment results to stale if program_files/compiler_command/execution_command changed
            changed_fields = ['checker_files']
            if checker.execution_command:
                changed_fields.append('execution_command')
            if set(changed_fields) - set(form.changed_data):
                list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                                          .filter(assignment=checker.program.assignment)]
                all_submissions = Upload.objects.filter(assignment=checker.program.assignment, assignment__trash=False,
                                                        pk__in=list_of_assignment_ids).order_by("-uploaded_on")
                # all_submissions = Upload.objects.filter(assignment=checker.program.assignment)
                AssignmentResults.objects.filter(
                    submission__in=all_submissions).update(is_stale=True)

            return HttpResponseRedirect(reverse('assignments_detailschecker', kwargs={'checkerID': checkerID}))
    else:
        form = CheckerCodeForm(initial=model_to_dict(checker))

    program = checker.program
    return render_to_response(
        'assignments/editChecker.html',
        {'form': form, 'checker': checker, 'program': program},
        context_instance=RequestContext(request)
    )


@login_required
def detailChecker(request, checkerID):
    '''
    Logic for getting errors for checks
    '''
    checker = get_object_or_404(Checker, pk=checkerID)
    course = checker.program.assignment.course

    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    program = checker.program
    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')

    execution_command = get_execution_command(program)
    checker_errors = None
    try:
        checker_errors = CheckerErrors.objects.get(checker=checker)
    except CheckerErrors.DoesNotExist:
        checker_errors = None

    all_testcases = Testcase.objects.filter(program=checker.program)

    return render_to_response(
        'assignments/detailsChecker.html',
        {'program': program, 'checker': checker, 'assignments': all_assignments,
         'assignment': program.assignment, 'testcases': all_testcases,
         'checker_errors': checker_errors, 'execution_command': execution_command,
         'course': course, 'is_moderator': is_moderator},
        context_instance=RequestContext(request)
    )


@login_required
def removeChecker(request, checkerID):
    '''
    For deleting checker
    '''
    checker = get_object_or_404(Checker, pk=checkerID)
    is_moderator = isCourseModerator(
        checker.program.assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    checker.delete()
    program = checker.program
    return HttpResponseRedirect(reverse('assignments_detailsprogram', kwargs={'programID': program.id}))


@login_required
def readme(request, courseID, topic):
    '''
    Readme file for course
    '''
    course = get_object_or_404(Course, pk=courseID)
    is_moderator = isCourseModerator(course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if topic in README_LINKS.keys():
        return render_to_response(
            README_LINKS[topic],
            {'course': course},
            context_instance=RequestContext(request)
        )
    return HttpResponseRedirect(reverse('assignments_index', kwargs={'courseID': courseID}))


@login_required
def createAssignmentImport(request, courseID):
    '''
    Logic for importing an assignment
    '''
    course = get_object_or_404(Course, pk=courseID)

    is_moderator = isCourseModerator(course, request.user)

    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if request.method == 'POST':
        form = AssignmentImportForm(request.POST, request.FILES)
        form.this_course = course
        if form.is_valid():
            new_assignment_import = AssignmentImport(**form.cleaned_data)
            new_assignment_import.creater = request.user
            new_assignment_import.course = course
            file_name = request.FILES['assignment_archive'].name
            file_name = file_name.split('.')[0]
            new_assignment_import.save()

            new_assignment = createAssignmentFromArchive(
                request, new_assignment_import.assignment_archive, course)

            new_assignment = addCommand(
                request, new_assignment_import.assignment_archive, course, new_assignment)
            if os.path.exists(file_name) and os.path.isdir(file_name):
                shutil.rmtree(file_name)
            if os.path.exists("elearning_academy/"+file_name) and os.path.isdir("elearning_academy/"+file_name):
                shutil.rmtree("elearning_academy/"+file_name)
            return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': new_assignment.id}))
    else:
        form = AssignmentImportForm()
    return render_to_response(
        'assignments/createAssignmentImport.html',
        {'form': form, 'course': course, 'is_moderator': is_moderator},
        context_instance=RequestContext(request)
    )


@login_required
def download_demo_assignment_files(request):
    '''
    This view let instructor download sample bulk assignment
    '''
    temp_file = os.path.join(settings.MEDIA_ROOT)
    file_path = temp_file + 'assignment_sample.tar.gz'
    file_name = "assignment_sample.tar.gz"
    try:
        mime = mimetypes.guess_type(file_path)
    except StandardError:
        mime = make_tuple('application/octet-stream')
    wrapper = FileWrapper(open(file_path, "r"))
    response = HttpResponse(wrapper, content_type=mime)
    response['Content-Length'] = os.stat(file_path).st_size
    response['Content-Disposition'] = 'inline; filename=%s' % smart_str(
        os.path.basename(file_name))
    response['X-Accel-Redirect'] = smart_str(os.path.join('/media', file_name))
    return response


@login_required
def createAssignmentScript(request, courseID):
    '''
    Logic for creating assignment through script.
    '''
    course = get_object_or_404(Course, pk=courseID)

    is_moderator = isCourseModerator(course, request.user)

    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if request.method == 'POST':
        form = AssignmentMetaForm(request.POST, request.FILES)
        form.this_course = course
        if form.is_valid():
            new_assignment_script = AssignmentScript(**form.cleaned_data)
            new_assignment_script.creater = request.user
            new_assignment_script.course = course
            new_assignment_script.save()
            metajson = json.load(new_assignment_script.meta_file.file)
            temp_dir = tempfile.mkdtemp(prefix="solution")
            os.chdir(temp_dir)
            extract_or_copy(
                src=new_assignment_script.assignment_archive.file.name, dest=os.getcwd())
            new_assignment_script.assignment_archive.close()
            next_dir = os.listdir(os.getcwd())
            os.chdir(next_dir[0])
            new_assignment = createAssignmentFromJson(
                request, metajson, course)
            new_assignment.save()
            createProgramTestcasesFromJson(request, new_assignment, metajson)
            return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': new_assignment.id}))
    else:
        form = AssignmentMetaForm()
    return render_to_response(
        'assignments/createAssignmentScript.html',
        {'form': form, 'course': course, 'is_moderator': is_moderator},
        context_instance=RequestContext(request)
    )


@login_required
def addCommand(request, importedTar, course, assignment):
    '''
    This will add all compiler commands and execution commands provided in importedTar
    '''
    temp = importedTar.name.split('/')
    tar_name = temp[-1].split('.')
    tar_name = tar_name[0]
    asgn_name = tar_name

    temp = os.path.join(settings.MEDIA_ROOT, str(importedTar))
    temp_dirarr = temp.split("/")
    level = 0
    temp_dir = ''
    for each_dir_element in temp_dirarr:
        if level <= 4:
            temp_dir = temp_dir + each_dir_element + '/'
            level += 1
    temp_dir = temp_dir[:-1]

    extract_or_copy(src=temp, dest=temp_dir)
    # temp_dir now indicates the assignment folder
    temp_dir = temp_dir + '/' + asgn_name

    desc_dir = temp_dir + '/Configuration/'
    filename = desc_dir + 'Configuration.txt'
    lines = [line.rstrip('\n') for line in open(filename)]

    for lineno in range(len(lines)):
        if lines[lineno].split():
            if lines[lineno].split(':')[0].strip() == "SectionType":
                programType = lines[lineno].split(':')[1].strip()
                lineno = lineno + 1
                program = None
                compiler_command = None
                execution_command = None
                description = None
                section_name_flag = 0
                comp_command_flag = 0
                exec_command_flag = 0
                description_flag = 0
                while(lineno < len(lines) and
                      (not section_name_flag or (not comp_command_flag and
                                                 not exec_command_flag) or not description_flag)):
                    if lines[lineno].split():
                        keyword = lines[lineno].split(':', 1)[0].strip()
                        value = lines[lineno].split(':', 1)[1].strip()

                        if keyword == "SectionName":
                            program = value
                            section_name_flag = 1
                        if keyword == "CompilerCommand":
                            compiler_command = value
                            comp_command_flag = 1
                        if keyword == "ExecutionCommand":
                            execution_command = value
                            exec_command_flag = 1
                        if keyword == "Description":
                            description = value.strip("\"")
                            description_flag = 1
                    lineno = lineno + 1
                obj = Program.objects.filter(
                    assignment=assignment, program_type=programType, name=program)
                editprogram = get_object_or_404(Program, pk=obj[0].id)
                editprogram.description = description

                temp_dir1 = temp_dir + '/' + programType + '/' + program
                if os.path.exists(temp_dir1):
                    for f in os.listdir(temp_dir1):
                        if str(f) == "makefile.txt":
                            fd = open(str(temp_dir1) + '/' + str(f))
                            editprogram.makefile.save(str(f), File(fd))

                temp_dir1 = temp_dir + '/' + programType + '/' + program + '/program_files'
                if os.path.exists(temp_dir1):
                    for f in os.listdir(temp_dir1):
                        fd = open(str(temp_dir1) + '/' + str(f))
                        editprogram.program_files.save(str(f), File(fd))

                if comp_command_flag:
                    if compiler_command != '' and len(compiler_command.split('|')) > 1:
                        editprogram.compiler_command = pickle.dumps([compiler_command.split('|')[0].strip(" "),
                                                                     compiler_command.split(
                                                                         '|')[1].strip(" "),
                                                                     compiler_command.split('|')[2].strip(" ")])

                if exec_command_flag:
                    if execution_command != '' and len(execution_command.split('|')) > 1:
                        editprogram.execution_command = pickle.dumps([execution_command.split('|')[0].strip(" "),
                                                                      execution_command.split(
                                                                          '|')[1].strip(" "),
                                                                      execution_command.split('|')[2].strip(" ")])
                editprogram.save()

                while True:
                    if lineno >= len(lines):
                        break
                    if lines[lineno].split():
                        if lines[lineno].split(':')[0].strip() == "SectionType":
                            lineno = lineno - 1
                            break
                        if lines[lineno].split(':')[0].strip() == "TestcaseName":
                            testcase_name = lines[lineno].split(':')[1].strip()
                            lineno = lineno + 1
                            command_line_args = None
                            marks = None
                            description = None
                            keep_partial_marks = False
                            args_flag = 0
                            marks_flag = 0
                            description_flag = 0
                            keep_partial_marks_flag = 0
                            while(lineno < len(lines) and
                                  (not args_flag or not marks_flag or not
                                   description_flag or not keep_partial_marks_flag)):
                                if lines[lineno].split():
                                    keyword = lines[lineno].split(':', 1)[
                                        0].strip()
                                    try:
                                        value = lines[lineno].split(':', 1)[
                                            1].strip()
                                    except Exception:
                                        value = ''

                                    if keyword == "CommandLineArguments":
                                        command_line_args = value
                                        args_flag = 1
                                    if keyword == "Marks":
                                        marks = value
                                        marks_flag = 1
                                    if keyword == "Description":
                                        description = value.strip("\"")
                                        description_flag = 1
                                    if keyword == "TestcaseLevelPartialMarkingScheme?":
                                        keep_partial_marks = (value == "True")
                                        keep_partial_marks_flag = 1

                                lineno = lineno + 1

                            obj1 = Testcase.objects.filter(
                                program=obj, name=str(testcase_name))
                            if obj1:
                                editTestcase = get_object_or_404(
                                    Testcase, pk=obj1[0].id)
                                editTestcase.description = description
                                editTestcase.marks = marks
                                editTestcase.keep_partial_marks = keep_partial_marks
                                editTestcase.command_line_args = command_line_args
                                editTestcase.save()
                    lineno = lineno + 1
    assignment.save()
    return assignment


@login_required
def createAssignmentFromArchive(request, importedTar, course):
    '''
    Create assignment from importedTar
    '''

    temp = importedTar.name.split('/')
    tar_name = temp[-1].split('.')
    tar_name = tar_name[0]
    asgn_name = tar_name
    temp = os.path.join(settings.MEDIA_ROOT, str(importedTar))
    temp_dirarr = temp.split("/")
    level = 0
    temp_dir = ''
    for each_dir_element in temp_dirarr:
        if level <= 4:
            temp_dir = temp_dir + each_dir_element + '/'
            level += 1
    temp_dir = temp_dir[:-1]

    extract_or_copy(src=temp, dest=temp_dir)
    # temp_dir now indicates the assignment folder
    temp_dir = temp_dir + '/' + asgn_name

    desc_dir = temp_dir + '/Configuration/'
    filename = desc_dir + 'Configuration.txt'
    lines = [line.rstrip('\n') for line in open(filename)]

    type_of_assgn = None
    description = None
    publish_date = None
    soft_deadline = None
    freezing_deadline = None
    assignment_duration = None
    extra_duration = None
    language = None
    student_files = None
    assignment_duration = None
    extra_duration = None
    for line in lines:
        if line.strip():
            if len(line.split(':', 1)) >= 2:
                keyword = line.split(':', 1)[0].strip()
                value = line.split(':', 1)[1].strip()

                if keyword == "AssignmentType":
                    type_of_assgn = value
                elif keyword == "PublishType":
                    publish_type = value
                elif keyword == "Description":
                    description = value.replace(r"\r\n", "\r\n").strip("\"")
                elif keyword == "AssignmentDuration":
                    values = value.split(":")
                    assignment_duration = timedelta(hours=int(values[0]), minutes=int(values[1]),
                                                    seconds=int(values[2]))
                elif keyword == "ExtraFreezingTime":
                    values = value.split(":")
                    extra_duration = timedelta(hours=int(values[0]), minutes=int(
                        values[1]), seconds=int(values[2]))

                elif keyword == "PublishOn":
                    deadline_str = local2utc(value)
                    publish_date = deadline_str
                elif keyword == "Deadline":
                    deadline_str = local2utc(value)
                    soft_deadline = deadline_str
                elif keyword == "FreezingDeadline":
                    deadline_str = local2utc(value)
                    freezing_deadline = deadline_str
                elif keyword == "CalculateExecutionTime?":
                    execution_time_allowed = (
                        (value == "True") or (value == "true"))
                elif keyword == "SendGradingEmailsToAll?":
                    force_notify = ((value == "True") or (value == "true"))
                elif keyword == "AdvanceCorrectnessChecker?":
                    correctness = ((value == "True") or (value == "true"))
                elif keyword == "OrderIsImportant?":
                    order = ((value == "True") or (value == "true"))
                elif keyword == "EnterValueOfErrorRate":
                    error = value
                elif keyword == "SeeHowWellStudentsIndentTheirCode?":
                    indentation = ((value == "True") or (value == "true"))
                elif keyword == "GraphicsProgram?":
                    graphics = ((value == "True") or (value == "true"))
                elif keyword == "ProgrammingLanguage":
                    language = value
                elif keyword == "FilesToBeSubmitted":
                    student_files = value
            if(type_of_assgn and description and
               ((publish_date and soft_deadline and
                 freezing_deadline) or (assignment_duration and extra_duration)) and language and student_files):
                break
    new_assignment = Assignment(name=asgn_name, publish_type=publish_type,
                                type_of_lab=type_of_assgn, program_language=language,
                                duration=assignment_duration, freezing_duration=extra_duration,
                                deadline=soft_deadline, freezing_deadline=freezing_deadline,
                                publish_on=publish_date, student_program_files=student_files,
                                description=description.replace("\\n", "\n"), bulk_add=importedTar,
                                execution_time_allowed=execution_time_allowed, hide=True,
                                force_notify=force_notify, correctness=correctness,
                                error=error, indentation=indentation, graphics_program=graphics,
                                order=order)
    new_assignment.course = course
    new_assignment.creater = request.user
    new_assignment.serial_number = (Assignment.objects.filter(course=course).filter(trash=False).
                                    aggregate(Max('serial_number'))
                                    ['serial_number__max'] or 0) + 1

    documents = temp_dir + '/Documents/'
    if os.path.exists(documents):
        for f in os.listdir(documents):
            fd = open(str(documents) + '/' + str(f))
            new_assignment.document.save(str(f), File(fd))

    helper_code = temp_dir + '/Helper-code/'
    if os.path.exists(helper_code):
        for f in os.listdir(helper_code):
            fd = open(str(helper_code) + '/' + str(f))
            new_assignment.helper_code.save(str(f), File(fd))

    solution_code = temp_dir + '/Solution-code/'
    if os.path.exists(solution_code):
        for f in os.listdir(solution_code):
            fd = open(str(solution_code) + '/' + str(f))
            new_assignment.model_solution.save(str(f), File(fd))

    new_assignment.save()

    Evaluate = temp_dir + '/Evaluate/'
    Practice = temp_dir + '/Practice/'
    if os.path.exists(Evaluate) or os.path.exists(Practice):
        section_bulk_add(new_assignment)
    return new_assignment


@login_required
def createAssignmentFromJson(request, jsonobject, course):
    '''
    Logic for generating assignment creation form
    '''
    asgn_name = jsonobject["assignment_name"]

    deadline_str = jsonobject["soft_deadline"]
    year = int(deadline_str.split()[0])
    month = int(deadline_str.split()[1])
    day = int(deadline_str.split()[2])
    hour = int(deadline_str.split()[3].split(":")[0])
    minute = int(deadline_str.split()[3].split(":")[1])
    soft_deadline = DateTime.datetime(year, month, day, hour, minute)

    deadline_str = jsonobject["freezing_deadline"]
    year = int(deadline_str.split()[0])
    month = int(deadline_str.split()[1])
    day = int(deadline_str.split()[2])
    hour = int(deadline_str.split()[3].split(":")[0])
    minute = int(deadline_str.split()[3].split(":")[1])
    freezing_deadline = DateTime.datetime(year, month, day, hour, minute)

    language = jsonobject["language"]
    student_files = jsonobject["student_files"]

    if "documents" in jsonobject:
        documents = jsonobject["documents"]
    else:
        documents = None

    if "helper_code" in jsonobject:
        helper_code = jsonobject["helper_code"]
    else:
        helper_code = None

    if "solution_code" in jsonobject:
        solution_code = jsonobject["solution_code"]
    else:
        solution_code = None

    deadline_str = jsonobject["publish_date"]
    year = int(deadline_str.split()[0])
    month = int(deadline_str.split()[1])
    day = int(deadline_str.split()[2])
    hour = int(deadline_str.split()[3].split(":")[0])
    minute = int(deadline_str.split()[3].split(":")[1])
    publish_date = DateTime.datetime(year, month, day, hour, minute)

    description = jsonobject["asgn_description"]

    new_assignment = Assignment(name=asgn_name, program_language=language, deadline=soft_deadline,
                                freezing_deadline=freezing_deadline, publish_on=publish_date,
                                student_program_files=student_files, description=description)
    new_assignment.course = course
    new_assignment.creater = request.user
    new_assignment.serial_number = (Assignment.objects.filter(course=course).filter(trash=False).
                                    aggregate(Max('serial_number'))
                                    ['serial_number__max'] or 0) + 1
    if documents:
        with open(documents) as f:
            new_assignment.document.save(documents, File(f))
    if helper_code:
        with open(helper_code) as f:
            new_assignment.helper_code.save(helper_code, File(f))
    if solution_code:
        with open(solution_code) as f:
            new_assignment.model_solution.save(solution_code, File(f))
    new_assignment.save()
    return new_assignment


@login_required
def createProgramTestcasesFromJson(request, assignment, jsonobject):
    '''
    Logic for creating Testcases inside sections
    '''
    if "sections" in jsonobject:
        for progjson in jsonobject["sections"]:
            section_name = progjson["section_name"]
            section_type = progjson["section_type"]

            if "compilation_command" in progjson:
                compilation_command = pickle.dumps(
                    progjson["compilation_command"])
            else:
                compilation_command = None

            if "execution_command" in progjson:
                execution_command = pickle.dumps(progjson["execution_command"])
            else:
                execution_command = None

            if "section_files" in progjson:
                program_files = progjson["section_files"]
            else:
                program_files = None

            if "sec_description" in progjson:
                description = progjson["sec_description"]
            else:
                description = None

            new_program = Program(name=section_name, program_type=section_type)

            if program_files:
                with open(program_files) as f:
                    new_program.program_files.save(program_files, File(f))
            if compilation_command:
                new_program.compiler_command = compilation_command
            if execution_command:
                new_program.execution_command = execution_command
            if description:
                new_program.description = description

            new_program.assignment = assignment
            new_program.is_sane = True
            new_program.compile_now = True
            new_program.execute_now = True
            new_program.language = assignment.program_language
            new_program.save()

            if "testcases" in progjson:
                for testjson in progjson["testcases"]:
                    test_name = testjson["testcase_name"]

                    if "input_files" in testjson:
                        input_files = testjson["input_files"]
                        std_input = testjson["std_in_file_name"]
                    else:
                        input_files = None
                        std_input = None

                    if "output_files" in testjson:
                        output_files = testjson["output_files"]
                        std_output = testjson["std_out_file_name"]
                    else:
                        output_files = None
                        std_output = None

                    if "command_line_args" in testjson:
                        command_line_args = testjson["command_line_args"]
                    else:
                        command_line_args = None

                    if "marks" in testjson:
                        marks = testjson["marks"]
                    else:
                        marks = None

                    if "test_description" in testjson:
                        tdescription = testjson["test_description"]
                    else:
                        tdescription = None

                    new_testcase = Testcase(
                        name=test_name, program=new_program)

                    if std_input:
                        new_testcase.std_in_file_name = std_input
                    else:
                        new_testcase.std_in_file_name = "None"
                    if std_output:
                        new_testcase.std_out_file_name = std_output
                    else:
                        new_testcase.std_out_file_name = "None"
                    if command_line_args:
                        new_testcase.command_line_args = command_line_args
                    if marks:
                        new_testcase.marks = marks
                    if tdescription:
                        new_testcase.tdescription = tdescription
                    if input_files:
                        with open(input_files) as f:
                            new_testcase.input_files.save(input_files, File(f))
                    if output_files:
                        with open(output_files) as f:
                            new_testcase.output_files.save(
                                output_files, File(f))

                    new_testcase.save()


def file_download(file_recv):
    ''' Normal file download'''
    file_name = file_recv.name.split('.')[-1]
    if file_name in ['tar', 'gz', 'gz2', 'gzip', 'bz2', 'zip']:
        pass
    try:
        mime = mimetypes.guess_type(file_recv.path)
    except StandardError:
        mime = make_tuple('application/octet-stream')
    wrapper = FileWrapper(open(file_recv.path, "r"))
    response = HttpResponse(wrapper, content_type=mime)
    response['Content-Length'] = os.stat(file_recv.path).st_size
    response['Content-Type'] = 'text/plain'
    response['Content-Disposition'] = 'inline; filename=%s' % smart_str(
        os.path.basename(file_recv.name))
    response['X-Accel-Redirect'] = smart_str(
        os.path.join('/media', file_recv.name))
    return response


def file_download_pdf(pdf_file):
    """ Logic for downloading PDF files"""
    try:
        mime = mimetypes.guess_type(pdf_file.path)
    except StandardError:
        mime = make_tuple('application/octet-stream')
    wrapper = FileWrapper(open(pdf_file.path, "r"))
    response = HttpResponse(wrapper, content_type=mime)
    response['Content-Length'] = os.stat(pdf_file.path).st_size
    response['Content-Type'] = 'application/pdf'
    response['Content-Disposition'] = 'inline; filename=%s' % smart_str(
        os.path.basename(pdf_file.name))
    response['X-Accel-Redirect'] = smart_str(
        os.path.join('/media', pdf_file.name))
    return response


def file_download_nonpdf(nonpdf_file):
    """ Logic for downloading non-PDF files eg .txt, .c, .cpp, .java, .py, etc"""
    try:
        mime = mimetypes.guess_type(nonpdf_file.path)
    except StandardError:
        mime = make_tuple('application/octet-stream')
    wrapper = FileWrapper(open(nonpdf_file.path, "r"))
    response = HttpResponse(wrapper, content_type=mime)
    response['Content-Length'] = os.stat(nonpdf_file.path).st_size
    response['Content-Type'] = 'text/plain'
    response['Content-Disposition'] = 'inline; filename=%s' % smart_str(
        os.path.basename(nonpdf_file.name))
    response['X-Accel-Redirect'] = smart_str(
        os.path.join('/media', nonpdf_file.name))
    return response


@login_required
def solutionDownload(request, assignmentID):
    '''
    Only creator of course can download solution file in assignment.
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course

    is_moderator = isCourseModerator(course, request.user)
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    if not is_moderator and not is_due:
        return HttpResponseForbidden("Forbidden 403")

    if not assignment.model_solution:
        return HttpResponseNotFound("File not found")
    return file_download(assignment.model_solution)


@login_required
def documentDownload(request, assignmentID):
    '''
    Additional document can be downloade by enrolled accounts.
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course
    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")
    is_moderator = isCourseModerator(course, request.user)
    if timezone.now() < assignment.publish_on and not is_moderator:
        return HttpResponseNotFound("Assignment not published")
    if not assignment.document:
        return HttpResponseNotFound("File not found")
    document_name = assignment.document.name.split('.')
    if document_name[-1] == 'pdf':
        return file_download_pdf(assignment.document)
    return file_download_nonpdf(assignment.document)


@login_required
def helperCodeDownload(request, assignmentID):
    '''
    Only enrolled accounts can download Helper code assignment.
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    course = assignment.course

    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")
    is_moderator = isCourseModerator(course, request.user)
    if timezone.now() < assignment.publish_on and not is_moderator:
        return HttpResponseNotFound("Assignment not published")
    if not assignment.helper_code:
        return HttpResponseNotFound("File not found")
    return file_download_nonpdf(assignment.helper_code)


@login_required
def programFileDownload(request, programID):
    '''
     Logic for downloading program file.
     Program file can be downloaded by enrolled accounts.
    '''
    program = get_object_or_404(Program, pk=programID)
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course
    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")
    if not program.program_files:
        return HttpResponseNotFound("File not found")
    is_moderator = isCourseModerator(course, request.user)
    if(is_moderator or program.program_type == "Practice" or is_due):
        return file_download(program.program_files)
    return HttpResponseForbidden("Forbidden 403")


@login_required
def makefileDownload(request, programID):
    '''
    Logic for downloading makefile of a section/program
    '''
    program = get_object_or_404(Program, pk=programID)
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course

    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")

    if not program.makefile:
        return HttpResponseNotFound("File not found")

    is_moderator = isCourseModerator(course, request.user)

    if(is_moderator or program.program_type == "Practice" or is_due):
        return file_download_nonpdf(program.makefile)

    return HttpResponseForbidden("Forbidden 403")


def extract_file(filename, path):
    '''
      This view let user to extract tar files
    '''
    opener, mode = tarfile.open, 'r:gz'
    tar = opener(filename, mode)
    try:
        tar.extractall(path)
    finally:
        tar.close()


@login_required
def testcaseInputDownload(request, testcaseID):
    '''
    Logic for downloading single testcase input file
    '''
    testcase = get_object_or_404(Testcase, pk=testcaseID)
    program = testcase.program
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
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
def testcaseOutputDownload(request, testcaseID):
    '''
    Logic for downloading single testcase output file
    '''
    testcase = get_object_or_404(Testcase, pk=testcaseID)
    program = testcase.program
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course

    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")

    if not testcase.output_files:
        return HttpResponseNotFound("File not found")

    is_moderator = isCourseModerator(course, request.user)

    if(is_moderator or program.program_type == "Practice" or is_due):
        return file_download(testcase.output_files)

    return HttpResponseForbidden("Forbidden 403")


@login_required
def chekerDownload(request, checkerID):
    '''
    Download practice testcases
    '''
    checker = get_object_or_404(Checker, pk=checkerID)
    program = checker.program
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course

    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")

    if not checker.checker_files:
        return HttpResponseNotFound("File not found")

    is_moderator = isCourseModerator(course, request.user)

    if(is_moderator or program.program_type == "Practice" or is_due):
        return file_download(checker.checker_files)

    return HttpResponseForbidden("Forbidden 403")


@login_required
def autotestcase(request, programID):
    """
    Funtion to autogenerate testcases
    """
    program = get_object_or_404(Program, pk=programID)
    testcases = Testcase.objects.filter(program=program)
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course
    has_submitted = Upload.objects.filter(
        owner=request.user, assignment=assignment)
    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')

    is_moderator = isCourseModerator(course, request.user)
    if is_moderator:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and
                                                     (timezone.now() > a.publish_on if a.publish_on else False))]
    compiler_command = get_compilation_command(program)
    execution_command = get_execution_command(program)
    if request.method == 'POST':
        specification = dict()
        specification['programid'] = programID
        specification['user'] = request.user
        specification['course'] = course
        specification['assignment'] = assignment.name
        specification['min_integer'] = int(request.POST['min_integer'])
        specification['max_integer'] = int(request.POST['max_integer'])
        specification['marks'] = int(request.POST['marks'])
        specification['no_of_testcase'] = int(request.POST['no_of_testcase'])

        if 'number' in str(request.get_full_path()):
            specification['input_type'] = 1
            specification['count_of_numbers'] = int(
                request.POST['count_of_numbers'])
        elif 'array' in str(request.get_full_path()):
            specification['input_type'] = 2
            specification['array_size'] = int(request.POST['array_size'])
            specification['array'] = int(request.POST['array'])
        else:
            specification['input_type'] = 3
            specification['row_size'] = int(request.POST['row_size'])
            specification['column_size'] = int(request.POST['column_size'])
            specification['matrix'] = int(request.POST['matrix'])

        obj = create_output.CreateTestcase(specification)
        obj.testcasecreation()
        return HttpResponseRedirect(reverse('assignments_detailsprogram', kwargs={'programID': programID}))
    else:
        if 'number' in str(request.get_full_path()):
            form = CreateTestcaseNumber()
        elif 'array' in str(request.get_full_path()):
            form = CreateTestcaseArray()
        else:
            form = CreateTestcaseMatrix()
    program_errors = None
    if not program.is_sane:
        try:
            program_errors = ProgramErrors.objects.get(program=program)
        except ProgramErrors.DoesNotExist:
            program_errors = None
    testcase_errors = []
    terror_ctype = ContentType.objects.get_for_model(TestcaseErrors)
    for error in AssignmentErrors.objects.filter(assignment=program.assignment, content_type=terror_ctype):
        testcase_errors.extend(
            TestcaseErrors.objects.filter(pk=error.object_id))
    get_params = {'source': 'section', 'id': programID}

    try:
        checker = Checker.objects.filter(program=program)
    except Checker.DoesNotExist:
        checker = None
    if checker:
        checker = checker[0]
    return render_to_response(
        'assignments/createautomaticTestcase.html',
        {'form': form, 'program': program, 'testcases': testcases, 'assignment': assignment, 'checker': checker,
         'assignments': assignments, 'date_time': timezone.now(),
         'program_errors': program_errors, 'compiler_command': compiler_command, 'execution_command': execution_command,
         'course': course, 'is_moderator': is_moderator,
         'is_due': is_due, 'has_submitted': has_submitted, 'get_params': get_params,
         'testcase_errors': testcase_errors},
        context_instance=RequestContext(request)
    )


@login_required
def modelsolution_changestatus(request, assignment_id):
    '''this function changes the model solution status from
    publish to unpublish and vice versa'''
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    if assignment.model_solution_published:
        assignment.model_solution_published = False
    else:
        assignment.model_solution_published = True
    assignment.save()

    return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignment_id}))


@login_required
@is_moderator_check
def course_scoreboard(request, courseID):
    '''
    generate scorecard for all students who made atleast one submission for that course
    '''
    course = get_object_or_404(Course, pk=courseID)
    all_students = CourseHistory.objects.filter(
        course=course, active='A', is_owner=False).select_related('user')
    all_assignment = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-publish_on')
    assignment_list = []
    ismoderator = isCourseModerator(course, request.user)
    for assignment in all_assignment:
        assignment_list.append(assignment.name)
    student_list = []
    for students in all_students:
        submission_list = []
        submission_list.append(students.user.username)
        total_submission_available = False
        total_marks = 0
        for assignment in all_assignment:
            student_assignment_marks = 0
            try:
                list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                                          .filter(assignment=assignment, owner=students.user)]
                student_assignment_submission = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                                                      pk__in=list_of_assignment_ids).\
                    order_by("-uploaded_on")
            except Upload.DoesNotExist:
                student_assignment_marks = 0
            if student_assignment_submission:
                total_submission_available = True
                # scoreboard saving final marks changes
                marks = student_assignment_submission[0].final_marks
                if marks:
                    student_assignment_marks = marks + \
                        student_assignment_submission[0].manualmark
                else:
                    student_assignment_marks = 0 + \
                        student_assignment_submission[0].manualmark
            submission_list.append(str(student_assignment_marks))
            total_marks += student_assignment_marks
        submission_list.append(str(total_marks))
        if total_submission_available:
            student_list.append(submission_list)

    return render_to_response(
        'assignments/Scoreboard.html',
        {'is_moderator': ismoderator, 'student_list': student_list, 'assignment_list': assignment_list,
         'course': course, 'assignments': all_assignment},
        context_instance=RequestContext(request)
    )


@login_required
@is_moderator_check
def get_scoreboard_in_csv(request, courseID):
    '''
    download the whiole scoreboard as csv file for the course
    '''
    course = get_object_or_404(Course, pk=courseID)
    all_students = CourseHistory.objects.filter(
        course=course, active='A', is_owner=False).select_related('user')
    all_assignment = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('publish_on')
    line = ""
    header = ""
    header += "Username ,"
    for assignment in all_assignment:
        header += str(assignment.name) + ", "
    header += "Total Marks \n"

    for students in all_students:
        submission_list = []
        total_submission_available = False
        total_marks = 0
        for assignment in all_assignment:
            student_assignment_marks = 0
            try:
                list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                                          .filter(assignment=assignment, owner=students.user)]
                student_assignment_submission = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                                                      pk__in=list_of_assignment_ids).\
                    order_by("-uploaded_on")
            except Upload.DoesNotExist:
                student_assignment_marks = 0
            if student_assignment_submission:
                total_submission_available = True
                marks = student_assignment_submission[0].final_marks
                if marks:
                    student_assignment_marks = marks + \
                        student_assignment_submission[0].manualmark
                else:
                    student_assignment_marks = 0 + \
                        student_assignment_submission[0].manualmark
            submission_list.append(student_assignment_marks)
            total_marks += student_assignment_marks
        if total_submission_available:
            line += str(students.user.username) + ", "
            for mark_list in submission_list:
                line += str(mark_list) + ", "
            line += str(total_marks) + "\n"

    line = header + line
    response = HttpResponse(content_type="text/plain")
    response['Content-Disposition'] = 'attachment; filename=Scorecard of %s.csv' % (
        course.title)
    response.write(line)
    return response


@login_required
def paste_assignment(request, assignment_id, course_id):
    '''This function pastes the selected assignment'''
    course = get_object_or_404(Course, pk=course_id)
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    duplicate_assignment = Assignment.objects.filter(course=course).filter(
        name=assignment.name)
    if assignment.name.find("Copy") != -1:
        return HttpResponse(
            "Assignment with same name already exists in Repository")
    if duplicate_assignment and course.title == "Repository":
        return HttpResponse(
            "Assignment with same name already exists in Repository")
    new_assignment = copy.deepcopy(assignment)
    new_assignment.id = None
    new_assignment.course = course
    new_assignment.trash = False
    new_assignment.backup = False
    if duplicate_assignment:
        new_assignment.name = new_assignment.name + " (Copy)"
        duplicate_assignment_copy = Assignment.objects.filter(course=course).filter(
            name=new_assignment.name)
        if duplicate_assignment_copy:
            new_assignment.name = new_assignment.name + " (Copy)"
    if assignment.course.title == "Repository":
        new_assignment.backup = True
    new_assignment.save()
    program_list = []
    program_list = Program.objects.filter(assignment=assignment)
    if program_list:
        for program in program_list:
            temp_program = copy.deepcopy(program)
            temp_program.id = None
            temp_program.assignment = new_assignment
            temp_program.save()
            testcase_list = Testcase.objects.filter(program=program)
            for testcase in testcase_list:
                temp_testcase = copy.deepcopy(testcase)
                temp_testcase.id = None
                temp_testcase.program = temp_program
                testcase_filepath = str(testcase.input_files.file.name)
                testcase_filepath.replace(assignment.name, new_assignment.name)
                testcase_filepath.replace(
                    assignment.creater.username, request.user.username)
                testcase_filepath.replace(
                    assignment.course.title, course.title)
                file_handler = open(testcase.input_files.file.name)
                old_file = File(file_handler)
                temp_testcase.input_files.save(
                    testcase_filepath, old_file, save=True)
                testcase_filepath = str(testcase.output_files.file.name)
                testcase_filepath.replace(assignment.name, new_assignment.name)
                testcase_filepath.replace(
                    assignment.creater.username, request.user.username)
                testcase_filepath.replace(
                    assignment.course.title, course.title)
                file_handler = open(testcase.output_files.file.name)
                old_file = File(file_handler)
                temp_testcase.output_files.save(
                    testcase_filepath, old_file, save=True)
                temp_testcase.save()
    return HttpResponseRedirect(
        reverse('assignments_index', kwargs={'courseID': course.id}))


@login_required
def view_assignmentdetails(request, assignment_id):
    '''Function to view minimum details of an assignment while copying it from one course to another'''
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    programs = Program.objects.filter(assignment=assignment)
    testcaselist = []
    for program in programs:
        testcases = Testcase.objects.filter(program=program)
        testcaselist.append(testcases)
    course = assignment.course
    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')
    get_params = {'source': 'assignment', 'id': assignment_id}
    mode = get_mode(request)
    evaluate_program = [
        a_program for a_program in programs if a_program.program_type == "Evaluate"]
    practice_program = [
        a_program for a_program in programs if a_program.program_type == "Practice"]
    formData = AssignmentForm(initial=model_to_dict(
        assignment), courseID=course.id)
    return render_to_response(
        'assignments/details.html',
        {'assignment': assignment, 'timer': None, 'course': course, 'has_joined': True,
         'is_moderator': True, 'programs': programs, 'form': [],
         'submission_allowed': False, 'allowed_exam': True, 'submittedFiles': [],
         'programs_with_errors': [], 'disable_grading': False,
         'program_not_ready': False, 'practice_program': practice_program,
         'assignments': all_assignments, 'program_errors': [], 'test_errors': [],
         'published': assignment.publish_on, 'is_due': False, 'rem_time': 0,
         'isSubmitted': False, 'date_time': timezone.now(), 'get_params': get_params,
         'total_sumissions': 0, 'mode': mode, 'best_submission': "",
         'assignmentID': assignment_id, 'now': timezone.now(), 'evaluate_program': evaluate_program,
         'formData': formData, 'number_of_submissions': 0, 'user_id': request.user,
         'allowed_exam_status': False, 'taList': [],
         'deadline': timezone.now()},
        context_instance=RequestContext(request),
    )


@login_required
@is_moderator_check
def show_repository(request, course_id):
    '''This function displays the assignments present in repository'''
    repository_course = Course.objects.filter(title='Repository')
    if not repository_course:
        course = Course()
        course.title = 'Repository'
        course.category_id = 1
        course.save()
    course_ids = [history_object.course_id for history_object in CourseHistory.objects.filter(
        user=request.user)]
    if course_ids:
        courses = Course.objects.filter(pk__in=course_ids)
    assignments = Assignment.objects.filter(course=repository_course)
    course = get_object_or_404(Course, pk=course_id)
    repository_course = get_object_or_404(Course, title='Repository')
    return render_to_response(
        'assignments/showRepository.html',
        {'assignments': assignments, 'courses': courses, 'course': course,
         'Repository': repository_course},
        context_instance=RequestContext(request))


@login_required
def select_assignment(request, course_id):
    '''Function to show the assignments from repository'''
    course = get_object_or_404(Course, pk=course_id)
    repository_course = Course.objects.filter(title="Repository")
    assignments = Assignment.objects.filter(course=repository_course)
    return render_to_response(
        'assignments/selectAssignments.html',
        {'assignments': assignments, 'course': course},
        context_instance=RequestContext(request))


@login_required
def save_assignment(request, assignment_id):
    '''This function copies  an assignment to repository'''
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    is_moderator = isCourseModerator(assignment.course, request.user)
    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")
    if not assignment.backup:
        assignment.backup = True
    else:
        return HttpResponseForbidden(
            "Already created backup for this Assignment")
    assignment.save()
    course = get_object_or_404(Course, title='Repository')
    paste_assignment(request, assignment_id, course.id)
    return HttpResponseRedirect(
        reverse('assignments_details', kwargs={'assignmentID': assignment_id}))


@login_required
def allcompile(request, new_upload, programs):
    '''compiles a code against all programs....here programs is an array of triple...programs[i][0] being program'''
    _, temp_fname = tempfile.mkstemp(prefix='user_input')
    input_file = open(temp_fname, 'wb+')
    input_file.write('')
    input_file.close()
    input_file = open(temp_fname)
    compileresults = ''
    for program in programs:
        compileall = CustomTestcase(input_file, program[0], new_upload, True)
        compileall.setup()
        compileall.compile()
        result = ''
        for inp in compileall.compileResult.get_stderr():
            result += inp.decode('utf-8')
            result += "\n"
        if result == '':
            result = 'In section ' + program[0].name + ' there are no errors'
        else:
            result = 'In section ' + program[0].name + '\n' + result
        compileresults += result + '\n'
    deleteSubmission(request, new_upload.id)
    new_upload.delete()
    return HttpResponse(json.dumps({'0': mark_safe(compileresults)}), content_type="application/json")


@login_required
def custom_input(request, new_upload):
    '''
    Function for handling custom input from editor
    '''
    pre_dir = os.getcwd()
    program = Program.objects.filter(id=request.POST.get('programID'))[0]
    test = request.POST.get('test')
    _, temp_fname = tempfile.mkstemp(prefix='user_input')
    input_file = open(temp_fname, 'wb+')
    input_file.write(request.POST.get('inputText'))
    input_file.close()
    input_file = open(temp_fname)
    custom_input_recv = CustomTestcase(
        input_file, program, new_upload, True).getResult()
    shutil.rmtree(temp_fname, ignore_errors=True)
    deleteSubmission(request, new_upload.id)
    new_upload.delete()
    result = ''
    if custom_input_recv.compilable:
        if custom_input_recv.compileResult.returnCode == 0:
            for inp in custom_input_recv.actualOutput.get_stdout():
                result += inp
                result += "\n"
            for inp in custom_input_recv.actualOutput.get_stderr():
                result += (inp)
                result += "\n"
        else:
            for inp in custom_input_recv.compileResult.get_stderr():
                result += (inp)
                result += "\n"
    else:
        if custom_input_recv.actualOutput.returnCode == 0:
            for inp in custom_input_recv.actualOutput.get_stdout():
                result += (inp)
                result += "\n"
            for inp in custom_input_recv.actualOutput.get_stderr():
                result += (inp)
                result += "\n"
        else:
            for inp in custom_input_recv.actualOutput.get_stderr():
                result += (inp)
                result += "\n"
    os.chdir(pre_dir)
    custom_input_recv.cleanUp()
    shutil.rmtree(temp_fname, ignore_errors=True)
    return HttpResponse(json.dumps({'0': mark_safe(result), '1': test}), content_type="application/json")


@login_required
def practiceresults(request):
    '''fetch results'''
    submission = get_object_or_404(Upload, pk=request.POST.get('submissionID'))
    assignment = submission.assignment
    if not submission.to_be_practiced:
        try:
            results = Results(submission, program_type="Practice")
            html = '<h4>Practice-Tests results for Assignment ' + \
                str(assignment.serial_number) + ' '
            html += assignment.name + '</h4><div class="span12">'
            for prgrm in results.program_results:
                html += '<h5 style="color:green;">' + prgrm.program_result.program.name + '</h5>'
                if prgrm.program_result.missing_file_names:
                    html += '<div class="accordion" id="accordion' + \
                        str(prgrm.program_result.program.id) + 'pro">'
                    html += '<div class="accordion-group"><div class="accordion-heading">'
                    html += '<a class="accordion-toggle" data-toggle="collapse"'
                    html += 'data-parent="#accordion' + \
                        str(prgrm.program_result.program.id)
                    html += 'pro" href="#collapse'
                    html += str(prgrm.program_result.program.id) + \
                        'innerpro">Files are not found.</a></div>'
                    html += '<div id="collapse' + \
                        str(prgrm.program_result.program.id)
                    html += 'innerpro" class="accordion-body collapse"> '
                    html += '<div style="padding-left:40px" class="accordion-inner"> '
                    html += '<div class="row"><h5>Bad configuration '
                    html += 'for this section. We couldn\'t find following files -</h5>'
                    html += prgrm.program_result.missing_file_names
                    html += '<br/><h5>Your tar contains following files -</h5>'
                    html += results.assignment_result.submitted_files
                    html += '</div></div></div></div></div>'
                elif prgrm.program_result.compiler_return_code == 0:
                    html += '<div class="accordion" id="accordion' + \
                        str(prgrm.program_result.program.id) + 'pro">'
                    html += '<table id="" class="table table-striped datatable"><thead><tr><th>'
                    html += 'Test Case ID</th><th>Status</th>'
                    html += '<th>Marks Awarded</th><th>Input file</th><th>Display I/O</th><th>Compare Output file</th>'
                    if assignment.execution_time_allowed:
                        html += '<th>Execution Time</th>'
                    html += '</tr></thead><tbody>'
                    for tst in prgrm.testResults:
                        html += '<tr><td>' + tst.test_case.name + '</td><td>'
                        if tst.return_code == 0 and tst.test_passed:
                            html += 'PASS'
                        else:
                            html += 'FAIL'
                        html += '</td><td>' + \
                            str(tst.marks) + '</td><td><a id="' + \
                            str(tst.test_case.id)
                        html += '-linkin" href="/assignments/testcase/input/download/'
                        html += str(tst.test_case.id) + \
                            '" target="_blank">Input file</a><textarea readonly="True"'
                        html += ' title="Click toggle to get download link for inputfiles" style="display: none; '
                        html += 'background: black; color: white;" class="form-control" id=\''
                        html += str(tst.test_case.id) + \
                            '-in\' rows="2" cols="11"></textarea></td><td>'
                        html += '<label class="switch"><input type="checkbox" '
                        html += ' checked><span title="Switch between download link and stdin" '
                        html += 'class="slider round" onclick="getstd(\''
                        html += str(tst.test_case.id) + '\', \'' + \
                            str(tst.test_case.program.id)
                        html += '\')"></span></label></td><td>'
                        html += '<a href="/evaluate/compare/' + str(tst.id)
                        html += '" target="formpopup" onclick="window.open(\'\', '
                        html += '\'formpopup2\',\'width=auto,height=400,resizable,scrollbars\').focus();'
                        html += 'this.target=\'formpopup2\';"> Compare </a></td>'
                        if assignment.execution_time_allowed:
                            html += '<td>' + str(tst.executiontime) + '<td>'
                        html += '</tr>'
                    html += '</tr></tbody></table></div>'
                else:
                    html += '<div class="accordion" id="accordion' + \
                        'prgrm.program_result.program.id' + 'pro">'
                    html += '<div class="accordion-group"><div class="accordion-heading"><a class="accordion-toggle"'
                    html += ' data-toggle="collapse"'
                    html += 'data-parent="#accordion' + \
                        str(prgrm.program_result.program.id) + \
                        'pro"href="#collapse'
                    html += str(prgrm.program_result.program.id) + \
                        'innerpro">Compilation failed.</a></div>'
                    html += '<div id="collapse' + \
                        str(prgrm.program_result.program.id)
                    html += 'innerpro" class="accordion-body collapse"> <div style="padding-left:40px"'
                    html += 'class="accordion-inner"><div class="row">Compile command:' + \
                        prgrm.compiler_command
                    html += '<br/>Return Code: ' + \
                        str(prgrm.program_result.compiler_return_code)
                    html += '<br/><h6 style="color:red;">Error Message</h6>' + \
                        prgrm.program_result.compiler_errors
                    html += '</div></div></div></div></div>'
            html += '</div>'
            return HttpResponse(json.dumps({'html': html}), content_type="application/json")
        except Results.DoesNotExist:
            return HttpResponse(json.dumps({'html': 'Results not created yet'}), content_type="application/json")
    return HttpResponse(json.dumps({'html': 'done'}), content_type="application/json")


@login_required
def evaluateresults(request):
    '''fetch results'''
    submission = get_object_or_404(Upload, pk=request.POST.get('submissionID'))
    assignment = submission.assignment
    is_moderator = isCourseModerator(assignment.course, request.user)
    is_due = (assignment.deadline <= timezone.now())
    if not submission.to_be_evaluated:
        try:
            results = Results(submission, program_type="Evaluate")
            html = '<h4>Evaluate-test results for Assignment ' + \
                str(assignment.serial_number) + ' '
            html += assignment.name + '</h4><div class="span12">'
            for prgrm in results.program_results:
                html += '<h5 style="color:green;">' + prgrm.program_result.program.name + '</h5>'
                if prgrm.program_result.missing_file_names:
                    html += '<div class="accordion" id="accordion' + \
                        str(prgrm.program_result.program.id) + 'pro">'
                    html += '<div class="accordion-group"><div class="accordion-heading">'
                    html += '<a class="accordion-toggle" data-toggle="collapse"'
                    html += 'data-parent="#accordion' + \
                        str(prgrm.program_result.program.id) + \
                        'pro" href="#collapse'
                    html += str(prgrm.program_result.program.id) + \
                        'innerpro">Files are not found.</a></div>'
                    html += '<div id="collapse' + \
                        str(prgrm.program_result.program.id)
                    html += 'innerpro" class="accordion-body collapse"> '
                    html += '<div style="padding-left:40px" class="accordion-inner">'
                    html += '<div class="row"><h5>Bad configuration '
                    html += 'for this section. We couldn\'t find following files -</h5>'
                    html += prgrm.program_result.missing_file_names
                    html += '<br/><h5>Your tar contains following files -</h5>'
                    html += results.assignment_result.submitted_files
                    html += '</div></div></div></div></div>'
                elif prgrm.program_result.compiler_return_code == 0:
                    html += '<div class="accordion" id="accordion' + \
                        str(prgrm.program_result.program.id)+'pro">'
                    html += '<table id="" class="table table-striped datatable">'
                    html += '<thead><tr><th>Test Case ID</th><th>Status</th>'
                    html += '<th>Marks Awarded</th><th>Input file</th><th>Compare Output file</th>'
                    if assignment.execution_time_allowed:
                        html += '<th>Execution Time</th>'
                    html += '</tr></thead><tbody>'
                    for tst in prgrm.testResults:
                        html += '<tr><td>' + tst.test_case.name + '</td><td>'
                        if tst.return_code == 0 and tst.test_passed:
                            html += 'PASS'
                        else:
                            html += 'FAIL'
                        html += '</td><td>' + str(tst.marks) + '</td><td>'
                        if is_due or is_moderator:
                            html += '<a id="' + str(tst.test_case.id)
                            html += '-linkin" href="/assignments/testcase/input/download/'
                            html += str(tst.test_case.id) + \
                                '" target="_blank">Input file</a>'
                        else:
                            html += 'Hidden'
                        html += '</td>'
                        html += '<td>'
                        if is_due or is_moderator:
                            html += '<a href="/evaluate/compare/' + \
                                str(tst.id) + '" target="formpopup" '
                            html += 'onclick="window.open(\'\', '
                            html += '\'formpopup2\',\'width=auto,height=400,resizable,scrollbars\').focus();'
                            html += 'this.target=\'formpopup2\';"> Compare </a>'
                        else:
                            html += 'Hidden'
                        html += '</td>'
                        if assignment.execution_time_allowed:
                            html += '<td>' + str(tst.executiontime) + '<td>'
                        html += '</tr>'
                    html += '</tr></tbody></table></div>'
                else:
                    html += '<div class="accordion" id="accordion' + \
                        'prgrm.program_result.program.id' + 'pro">'
                    html += '<div class="accordion-group"><div class="accordion-heading">'
                    html += '<a class="accordion-toggle" data-toggle="collapse"'
                    html += 'data-parent="#accordion' + \
                        str(prgrm.program_result.program.id) + \
                        'pro"href="#collapse'
                    html += str(prgrm.program_result.program.id) + \
                        'innerpro">Compilation failed.</a></div>'
                    html += '<div id="collapse' + \
                        str(prgrm.program_result.program.id)
                    html += 'innerpro" class="accordion-body collapse"> <div style="padding-left:40px"'
                    html += 'class="accordion-inner"><div class="row">Compile command:' + \
                        prgrm.compiler_command
                    html += '<br/>Return Code: ' + \
                        str(prgrm.program_result.compiler_return_code)
                    html += '<br/><h6 style="color:red;">Error Message</h6>' + \
                        prgrm.program_result.compiler_errors
                    html += '</div></div></div></div></div>'
            html += '</div>'
            return HttpResponse(json.dumps({'html': html}), content_type="application/json")
        except Results.DoesNotExist:
            return HttpResponse(json.dumps({'html': 'Results not created yet'}), content_type="application/json")
    return HttpResponse(json.dumps({'html': 'done'}), content_type="application/json")


def practicerun(request, submission):
    '''puts task of practice run of assignment in queue'''
    try:
        assignment = submission.assignment

        # Checking if the user sending the request is either the owner of the submission or the assignment
        # creator (the only people authorized to evaluate).
        is_moderator = isCourseModerator(assignment.course, request.user)
        if not (request.user == submission.owner or is_moderator):
            raise PermissionDenied

        if submission.to_be_practiced:
            evaluate_assignment.delay(submission.id, "Practice")
            i = app.control.inspect()
            data = i.stats()
            if data is not None:
                node_name = list(data)[0]
                queue_position = len(i.reserved().get(node_name))
            else:
                queue_position = "Unknown"
        else:
            # is_student = True if (request.user == submission.owner) else False
            # is_due = (assignment.deadline <= timezone.now())

            try:
                __ = Results(submission, program_type="Practice")
                return HttpResponse(json.dumps({'results': 1, 'submissionID': submission.id}),
                                    content_type="application/json")
            except Results.DoesNotExist:
                raise Http404("Results not created yet")
    except Exception as e:
        print e
    return HttpResponse(json.dumps({'submissionID': submission.id, 'position': queue_position,
                                    'html': '<h4>Practice-Tests Results for Assignment' +
                                            str(assignment.serial_number) + ' ' + assignment.name +
                                            '</h4><div><p style="font-size: 16px;">' +
                                            'Evaluation Status:<span id="current-status" style="color: orange;">' +
                                            ' </span></p></div><table class="table table-bordered"><thead><tr><th>' +
                                            'Phase</th><th>Status</th></tr></thead><tbody><tr><td> <b> Compilation ' +
                                            '</b> </td><td><i name="compile" class="fa fa-circle-o-notch fa-spin" ' +
                                            'style="font-size:24px"></i></td></tr><tr ><td> <b> Execution </b> </td>' +
                                            '<td><i name="execute" class="fa fa-circle-o-notch fa-spin" ' +
                                            'style="font-size:24px"></i></td></tr></tbody></table>'}),
                        content_type="application/json")


def evaluaterun(request, submission):
    '''puts task of evaluation of assignment in queue'''
    try:
        assignment = submission.assignment

        # Checking if the user sending the request is either the owner of the submission or the assignment
        # creator (the only people authorized to evaluate).
        is_moderator = isCourseModerator(assignment.course, request.user)
        if not (request.user == submission.owner or is_moderator):
            raise PermissionDenied
        if submission.to_be_evaluated:
            evaluate_assignment.delay(submission.id, "Evaluate")
            i = app.control.inspect()
            data = i.stats()
            if data is not None:
                node_name = list(data)[0]
                queue_position = len(i.reserved().get(node_name))
            else:
                queue_position = "Unknown"
        else:
            try:
                __ = Results(submission, program_type="Evaluate")
                return HttpResponse(json.dumps({'results': 1, 'submissionID': submission.id,
                                                'position': 'queue_position'}),
                                    content_type="application/json")
            except Results.DoesNotExist:
                raise Http404("Results not created yet")
    except Exception as e:
        print e
    return HttpResponse(json.dumps({'submissionID': submission.id, 'position': queue_position,
                                    'html': '<h4>Evaluate-Tests Results for Assignment' +
                                            str(assignment.serial_number) + ' ' + assignment.name +
                                            '</h4><div><p style="font-size: 16px;">' +
                                            'Evaluation Status:<span id="current-status" style="color: orange;">' +
                                            ' </span></p></div><table class="table table-bordered"><thead><tr><th>' +
                                            'Phase</th><th>Status</th></tr></thead><tbody><tr><td> <b> Compilation ' +
                                            '</b> </td><td><i name="compile" class="fa fa-circle-o-notch fa-spin" ' +
                                            'style="font-size:24px"></i></td></tr><tr ><td> <b> Execution </b> </td>' +
                                            '<td><i name="execute" class="fa fa-circle-o-notch fa-spin" ' +
                                            'style="font-size:24px"></i></td></tr></tbody></table>'}),
                        content_type="application/json")


@login_required
def online_editor(request, assignment_id):
    '''
    function for in-browser editor
    '''
    # pause_status = True
    allowed_exam_status = True
    if not request.user.is_authenticated:
        return HttpResponseForbidden("Forbidden 403")

    assignment = get_object_or_404(Assignment, pk=assignment_id)
    if not isEnrolledInCourse(assignment.course, request.user):
        return HttpResponseRedirect("/courseware/courseslist/")
    if assignment.type_of_lab == "Lab":
        rem_time = int(
            (assignment.deadline - datetime.now(pytz.timezone('UTC'))).total_seconds())
    else:
        rem_time, __, allowed_exam_status = get_object_from_proctoring(
            assignment.exam_group_id, request.user)
        if not allowed_exam_status:
            return HttpResponseForbidden("Forbidden 403")
        if not validateuser(request, assignment):
            return HttpResponseForbidden("Forbidden 403")
    programs = Program.objects.filter(
        assignment=assignment, program_type="Practice")
    new_prog = []
    for x in programs:
        new_prog.append([x, get_compilation_command(x),
                         get_execution_command(x)])
    programs = new_prog
    course = assignment.course
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    if (is_due or assignment.program_language == "Others" or
            assignment.hide is True or not assignment.student_program_files):
        return HttpResponseForbidden("Forbidden 403")
    if request.method == 'POST':
        if 'practiceresults' in request.POST:
            return practiceresults(request)
        if 'evaluateresults' in request.POST:
            return evaluateresults(request)
    if request.method == 'POST' and 'postID' not in request.POST:
        files_to_be_submitted = assignment.student_program_files.split(' ')
        data = request.POST
        student_code = []
        for x in files_to_be_submitted:
            student_code.append(request.POST[x])
        if [""]*len(student_code) == student_code:
            if 'inputText' in request.POST or 'compileall' in request.POST:
                reerror = mark_safe(
                    "Error occured during input!!<br>Please check submission.")
                return HttpResponse(json.dumps({'0': reerror, '1': request.POST.get('test')}),
                                    content_type="application/json")
            return HttpResponseRedirect(request.META["HTTP_REFERER"])
        if 'autosave' in request.POST:
            try:
                in_memory_file = create_upload(request, assignment, student_code,
                                               files_to_be_submitted, 'autosavedsub.zip')
                if ServerSavedSubmission.objects.filter(assignment=assignment, owner=request.user).exists():
                    server_saved_submission = ServerSavedSubmission.objects.filter(assignment=assignment,
                                                                                   owner=request.user)
                else:
                    server_saved_submission = False
                if server_saved_submission:
                    filepath = os.path.join(settings.MEDIA_ROOT, str(
                        server_saved_submission[0].submission.filePath))
                    filepath = filepath.rsplit('/', 1)[0]
                    shutil.rmtree(filepath)
                    server_saved_submission[0].submission.filePath = in_memory_file
                    server_saved_submission[0].submission.uploaded_on = timezone.now(
                    )
                    server_saved_submission[0].submission.save()
                    server_saved_submission[0].save()
                else:
                    new_upload = Upload(
                        owner=request.user,
                        assignment=assignment,
                        filePath=in_memory_file
                    )
                    new_upload.save()
                    new_server_sub = ServerSavedSubmission(
                        assignment=new_upload.assignment,
                        owner=request.user,
                        submission=new_upload
                    )
                    new_server_sub.save()
                return HttpResponse(json.dumps({'FailedAutosave': "0"}), content_type="application/json")
            except Exception:
                return HttpResponse(json.dumps({'FailedAutosave': "1"}), content_type="application/json")
        in_memory_file = create_upload(
            request, assignment, student_code, files_to_be_submitted, 'submission.zip')
        new_upload = Upload(
            owner=request.user,
            assignment=assignment,
            filePath=in_memory_file
        )
        if 'inputText' in request.POST or 'compileall' in request.POST:
            new_upload.save()
            if 'compileall' in request.POST:
                try:
                    programs = Program.objects.filter(
                        assignment=assignment, program_type="Practice")
                    new_prog = []
                    for x in programs:
                        new_prog.append(
                            [x, get_compilation_command(x), get_execution_command(x)])
                    programs = new_prog
                    return allcompile(request, new_upload, programs)
                except Exception as e:
                    print e
            return custom_input(request, new_upload)
        else:
            if LatestSubmission.objects.filter(assignment=assignment, owner=request.user).exists():
                latest_submission = LatestSubmission.objects.filter(
                    assignment=assignment, owner=request.user)
            else:
                latest_submission = False
            if latest_submission:
                if check(assignment, request.POST, latest_submission[0].submission):
                    new_upload.save()
                    if latest_submission:
                        latest_submission[0].submission = new_upload
                        latest_submission[0].save()
            else:
                new_upload.save()
                submission_to_evaluate = LatestSubmission(
                    assignment=new_upload.assignment,
                    owner=request.user,
                    submission=new_upload
                )
                submission_to_evaluate.save()
            latest_submission = LatestSubmission.objects.filter(
                assignment=assignment, owner=request.user)
        if 'run' in data:
            return practicerun(request, latest_submission[0].submission)
        if 'evaluate' in data:
            return evaluaterun(request, latest_submission[0].submission)
        if 'graphics' in data:
            return HttpResponseRedirect("/evaluate/testcases/"+str(latest_submission[0].submission.id))
        return HttpResponseRedirect(request.META["HTTP_REFERER"])
    else:
        sub_id = 0
        files_and_content = []
        valid = True
        submission_allowed = None
        is_due = None
        all_uploads = Upload.objects.filter(assignment_id=assignment_id, owner=request.user,
                                            assignment__trash=False).order_by("-uploaded_on")
        for a_submission in all_uploads:
            a_submission.marks_v = a_submission.manualmark + a_submission.final_marks
        has_joined = CourseHistory.objects.filter(
            course_id=course, user_id=request.user.id)
        if assignment.deadline is not None:
            submission_allowed = (
                timezone.now() <= assignment.deadline) and bool(has_joined)
            is_due = (timezone.now() >= assignment.deadline) and bool(
                has_joined)
        for x in assignment.student_program_files.split(' '):
            if x != '':
                files_and_content.append([x, ""])
        if ServerSavedSubmission.objects.filter(assignment=assignment, owner=request.user).exists():
            server_upload = ServerSavedSubmission.objects.filter(
                assignment=assignment, owner=request.user)
            older_upload = Upload.objects.filter(
                id=server_upload[0].submission.id)
            y11 = []
            for x in all_uploads:
                if x.id != older_upload[0].id:
                    y11.append(x)
            all_uploads = y11
        older_upload = Upload.objects.filter(
            assignment=assignment, owner=request.user).order_by("-uploaded_on")
        if older_upload:
            student_file = os.path.join(
                settings.MEDIA_ROOT, str(older_upload[0].filePath))
            if 'postID' in request.POST:
                sub_id = int(request.POST['postID'])
                older_upload = Upload.objects.filter(
                    id=sub_id, assignment=assignment, owner=request.user)
                student_file = os.path.join(
                    settings.MEDIA_ROOT, str(older_upload[0].filePath))
            loc = student_file
            i = 0
            while True:
                if loc[-1] == '/':
                    break
                else:
                    loc = loc[:-1]
            archive = []
            content = []
            files_and_content = []
            files_to_be_submitted = []
            f = ""
            if ('.tar' in student_file or '.zip' in student_file) and os.path.exists(student_file):
                if '.tar' in student_file:
                    f = tarfile.open(student_file, 'r')
                    archive = f.getmembers()
                    for single_file in archive:
                        if single_file.name.split('/')[-1] in assignment.student_program_files.split():
                            student_code = f.extractfile(single_file).read()
                            content.append(student_code)
                            file_name = single_file.name.split('/')[-1]
                            files_and_content.append([file_name, student_code])
                            files_to_be_submitted.append(file_name)
                    f.close()
                else:
                    f = zipfile.ZipFile(student_file, 'r')
                    for file_in_zip in f.namelist():
                        if file_in_zip.split('/')[-1] in assignment.student_program_files.split():
                            student_code = f.open(file_in_zip).read()
                            content.append(student_code)
                            file_name = file_in_zip.split('/')[-1]
                            files_and_content.append([file_name, student_code])
                            files_to_be_submitted.append(file_name)

            else:
                archive = [student_file.split('/')[-1]]
                for file_in_archive in archive:
                    if os.path.exists(loc+file_in_archive):
                        student_code = open(loc+file_in_archive, 'r').read()
                        content.append(student_code)
                        file_name = file_in_archive.split('/')[-1]
                        files_and_content.append([file_name, student_code])
                        files_to_be_submitted.append(file_name)
            i = 0
            for x in files_and_content:
                if x[0] not in assignment.student_program_files.split(' '):
                    files_and_content.pop(i)
                i += 1
            for y in assignment.student_program_files.split(' '):
                if y not in files_to_be_submitted:
                    files_and_content.append([y, ""])
            if 'postID' in request.POST:
                return HttpResponse(json.dumps(files_and_content), content_type="application/json")
            programs = Program.objects.filter(
                assignment=assignment, program_type="Practice")
            new_prog = []
            for x in programs:
                new_prog.append(
                    [x, get_compilation_command(x), get_execution_command(x)])
            programs = new_prog
            return render_to_response(
                'assignments/editor.html',
                {'valid': valid, 'form': files_and_content, 'programs': programs, 'all_uploads': all_uploads,
                 'submission_allowed': submission_allowed, 'is_due': is_due, 'rem_time': rem_time,
                 'files_to_be_submitted': files_to_be_submitted, 'course': course, 'assignment': assignment,
                 'allowed_exam_status': allowed_exam_status},
                context_instance=RequestContext(request))
        else:
            programs = Program.objects.filter(
                assignment=assignment, program_type="Practice")
            new_prog = []
            for x in programs:
                new_prog.append(
                    [x, get_compilation_command(x), get_execution_command(x)])
            programs = new_prog
            return render_to_response(
                'assignments/editor.html',
                {'valid': valid, 'form': files_and_content, 'programs': programs, 'all_uploads': all_uploads,
                 'submission_allowed': submission_allowed, 'is_due': is_due, 'rem_time': rem_time,
                 'files_to_be_submitted': assignment.student_program_files.split(' '), 'course': course,
                 'assignment': assignment, 'allowed_exam_status': allowed_exam_status},
                context_instance=RequestContext(request))
    return HttpResponseRedirect(request.META["HTTP_REFERER"])


@login_required
@is_moderator_check
def assignment_stats(request, assignmentID):
    '''
    generate stats for an assignment so that it could be plotted
    '''
    assignment = get_object_or_404(Assignment, pk=assignmentID)
    list_of_assignment_ids = [instance.submission.id for instance in LatestSubmission.objects
                              .filter(assignment=assignment)]
    numsubmissions = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                           pk__in=list_of_assignment_ids).order_by("-uploaded_on").count()
    all_programs = Program.objects.filter(
        assignment=assignment).order_by('name')
    course = assignment.course
    all_assignments = Assignment.objects.filter(
        course=course).filter(trash=False).order_by('-deadline')
    testcase_list = []
    failure_count = []
    pass_count = []
    testcase_list.append('Compilation')
    all_submissions = Upload.objects.filter(assignment=assignment, assignment__trash=False,
                                            pk__in=list_of_assignment_ids).order_by("-uploaded_on")
    all_assign_results = AssignmentResults.objects.filter(
        submission__in=all_submissions)
    all_prog_results = ProgramResults.objects.filter(program=all_programs[0], compiler_return_code=1,
                                                     assignment_result__in=all_assign_results)
    numcomperrors = len(all_prog_results)
    all_prog_results = ProgramResults.objects.filter(
        assignment_result__in=all_assign_results)
    failure_count.append(numcomperrors)
    pass_count.append(numsubmissions-numcomperrors)
    for program in all_programs:
        all_testcases = Testcase.objects.filter(
            program=program).order_by('name')
        for testcase in all_testcases:
            testcase_list.append(str(testcase.name))
            failedtestcases = TestcaseResult.objects.filter(test_case=testcase, test_passed=False,
                                                            program_result__in=all_prog_results).count()
            failure_count.append(failedtestcases)
            pass_count.append(numsubmissions-(numcomperrors + failedtestcases))
    assignment_results = AssignmentResults.objects.filter(
        submission__in=all_submissions)
    marks_list = []
    count_list = []
    for submission in all_submissions:
        marks = [s.get_marks()
                 for s in assignment_results if s.submission == submission]
        if marks:
            total = marks[0] + submission.manualmark
        else:
            total = submission.manualmark
        total = str(total)
        if total in marks_list:
            count_list[marks_list.index(total)] += 1
        else:
            marks_list.append(total)
            count_list.append(1)

    for passnum in range(len(marks_list)-1, 0, -1):
        for ind in range(passnum):
            if float(marks_list[ind]) > float(marks_list[ind+1]):
                temp = marks_list[ind]
                marks_list[ind] = marks_list[ind+1]
                marks_list[ind+1] = temp
                temp = count_list[ind]
                count_list[ind] = count_list[ind+1]
                count_list[ind+1] = temp
    marks_list.append("No Submission")
    count_list.append(CourseHistory.objects.filter(course=course, active='A',
                                                   is_owner=False).select_related('user').count() - numsubmissions)
    return render_to_response(
        'assignments/testcasestats.html',
        {'course': course, 'failurecount': failure_count, 'passcount': pass_count, 'assignment': assignment,
         'numSubmission': numsubmissions, 'testcases_list': mark_safe(testcase_list), 'assignments': all_assignments,
         'marks_list': mark_safe(marks_list), 'count_list': count_list, 'is_moderator': True},
        context_instance=RequestContext(request)
    )


@login_required
def config_testcase(request, testcaseID):
    '''
    function to process Safe Execute parameters at testcase level
    '''
    testcase_obj = get_object_or_404(Testcase, pk=testcaseID)
    assignment_id = testcase_obj.program.assignment.id
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    title = testcase_obj.name
    source = 'testcase'
    is_moderator = isCourseModerator(
        testcase_obj.program.assignment.course, request.user)

    if not is_moderator:
        return HttpResponseForbidden("Forbidden 403")

    if request.method == 'POST':
        form = SafeExecForm(request.POST, request.FILES,
                            initial=model_to_dict(testcase_obj))
        if form.is_valid():
            obj = SafeExec.objects.all().filter(testcase=testcase_obj)
            length_object = len(obj)
            if length_object != 0:
                form.cleaned_data['testcase'] = testcase_obj
                obj.update(**form.cleaned_data)

            else:
                form.cleaned_data['testcase'] = testcase_obj
                SafeExec.objects.create(**form.cleaned_data)
            return HttpResponseRedirect(reverse('assignments_detailstestcase', kwargs={'testcaseID': testcaseID}))
        else:
            form = SafeExecForm(initial=model_to_dict(
                SafeExec.objects.get(testcase_id=testcaseID)))
            return render_to_response('assignments/safeexec_params.html',
                                      {'form': form, 'testcases': testcase_obj, 'source': source,
                                       'title': title, 'assignment': assignment},
                                      context_instance=RequestContext(request))

    else:
        default_limits = {'cpu_time': 10, 'clock_time': 60,
                          'memory': 32768, 'stack_size': 8192,
                          'child_processes': 0, 'open_files': 512,
                          'file_size': 1024}
        form = SafeExecForm(initial=default_limits)
        if SafeExec.objects.filter(testcase_id=testcaseID).exists():
            form = SafeExecForm(initial=model_to_dict(
                SafeExec.objects.get(testcase_id=testcaseID)))
        return render_to_response('assignments/safeexec_params.html',
                                  {'form': form, 'testcases': testcase_obj, 'source': source, 'title': title,
                                   'assignment': assignment, 'is_moderator': is_moderator},
                                  context_instance=RequestContext(request))


@login_required
def edit_tc_marks(request):
    '''
    edit testcase marks
    '''
    if request.method == "POST":
        pk = request.POST["pk"]
        value = request.POST["value"]
        testcase = Testcase.objects.get(id=pk)
        course = testcase.program.assignment.course
        is_moderator = isCourseModerator(course, request.user)
        mode = get_mode(request)
        try:
            value = float(value)
        except ValueError:
            return HttpResponse("true")
        if value < 0:
            return HttpResponse("true")
        if is_moderator and mode != 'S':
            testcase.marks = value
            testcase.save()
            mark_submissions_false(testcase.program.assignment.id)
            return HttpResponse("true")
        else:
            raise Http404
    else:
        raise Http404


@login_required
def reevaluate(request):
    '''
    edit testcase marks
    '''
    if request.method == "POST":
        pk = request.POST["pk"]
        submission = Upload.objects.filter(id=pk)[0]
        evaluaterun(request, submission)
        return HttpResponse(json.dumps({'success': True}), content_type='application/json')
    return HttpResponse(json.dumps({'success': False}), content_type='application/json')


@login_required
def publish_on_demand(request, assignment_id):
    """ View for assignments to be published on-demand"""
    submission_allowed = None   # New initialize
    is_due = None   # New initialize
    assignment = get_object_or_404(Assignment, pk=assignment_id)
    course = assignment.course
    is_creator = isCourseCreator(course, request.user)
    is_moderator = isCourseModerator(course, request.user)
    mode = get_mode(request)
    assignment.publish_on = timezone.now()
    if not assignment.deadline:
        assignment.deadline = timezone.now() + timedelta(days=9999)
        assignment.freezing_deadline = assignment.deadline

    # Updating the database table
    this_asgnmnt = Assignment.objects.get(id=assignment_id)
    this_asgnmnt.publish_on = assignment.publish_on
    this_asgnmnt.deadline = assignment.deadline
    this_asgnmnt.freezing_deadline = assignment.freezing_deadline
    delete_task = delete_redundant_files.apply_async(
        (assignment.id,), eta=assignment.freezing_deadline)
    this_asgnmnt.deletesubmissions_task_id = delete_task.id
    this_asgnmnt.hide = False

    this_asgnmnt.save()
    formData = AssignmentForm(initial=model_to_dict(
        assignment), courseID=assignment.course.id)
    if not is_creator and not is_moderator:
        raise PermissionDenied

    has_joined = CourseHistory.objects.filter(
        course_id=course, user_id=request.user.id)

    submission_allowed = (
        timezone.now() <= assignment.deadline) and bool(has_joined)
    is_due = (timezone.now() >= assignment.deadline)    # and bool(has_joined)

    if request.method == "POST" and submission_allowed:
        form = UploadForm(request.POST, request.FILES,
                          assignment_model_obj=assignment)
        if form.is_valid():
            older_upload = Upload.objects.filter(
                owner=request.user,
                assignment=assignment
            )
            if older_upload:
                older_upload[0].delete()
            new_upload = Upload(
                owner=request.user,
                assignment=assignment,
                filePath=request.FILES['docfile']
            )
            new_upload.save()

            return HttpResponseRedirect(reverse('assignments_details', kwargs={'assignmentID': assignment_id,
                                                                               'formData': formData}))
    else:
        form = UploadForm()

    perror_ctype = ContentType.objects.get_for_model(ProgramErrors)
    terror_ctype = ContentType.objects.get_for_model(TestcaseErrors)
    program_errors = []
    test_errors = []

    for error in AssignmentErrors.objects.filter(assignment=assignment, content_type=terror_ctype):
        test_errors.extend(TestcaseErrors.objects.filter(pk=error.object_id))

    for error in AssignmentErrors.objects.filter(assignment=assignment, content_type=perror_ctype):
        program_errors.extend(ProgramErrors.objects.filter(pk=error.object_id))

    course = assignment.course
    programs = Program.objects.filter(assignment=assignment)

    practice_program = [
        a_program for a_program in programs if a_program.program_type == "Practice"]
    programs_with_errors = []

    for aprogram in programs:
        if not aprogram.is_sane:
            try:
                p_error = ProgramErrors.objects.get(program=aprogram)
                programs_with_errors.append(p_error)
            except ProgramErrors.DoesNotExist:
                p_error = None

    submitted_files = Upload.objects.filter(
        owner=request.user, assignment=assignment)

    program_not_ready = False
    disable_grading = False
    if programs_with_errors or assignment.deadline is not None and submission_allowed is False:
        program_not_ready = True
    if submitted_files and submitted_files[0].is_stale:
        disable_grading = True

    all_assignments = Assignment.objects.filter(
        course=course).order_by('-deadline')
    course_history = CourseHistory.objects.get(
        user=request.user, course=course)
    if course_history.is_owner:
        assignments = all_assignments
    else:
        assignments = [a for a in all_assignments if(not a.hide and (timezone.now() > a.publish_on if a.publish_on else
                                                                     False))]
    total_sumissions = Upload.objects.filter(assignment=assignment).count()
    is_submitted = Upload.objects.filter(assignment=assignment).count() > 0
    get_params = {'source': 'assignment', 'id': assignment_id}
    formData = AssignmentForm(initial=model_to_dict(
        assignment), courseID=assignment.course.id)
    allowed_exam = True
    if assignment.deadline is not None:
        submission_allowed = (
            timezone.now() <= assignment.deadline) and bool(has_joined)
        is_due = (timezone.now() >= assignment.deadline) and bool(has_joined)
        # for remaining time
        rem_time = int(
            (assignment.deadline - datetime.now(pytz.timezone('UTC'))).total_seconds())
    return render_to_response(
        'assignments/details.html',
        {'assignment': assignment, 'course': course, 'has_joined': has_joined, 'is_moderator': is_moderator,
         'programs': programs, 'form': form, 'submission_allowed': submission_allowed,
         'submitted_files': submitted_files, 'programs_with_errors': programs_with_errors,
         'disable_grading': disable_grading, 'rem_time': rem_time,
         'program_not_ready': program_not_ready, 'practice_program': practice_program,
         'assignments': assignments, 'program_errors': program_errors, 'test_errors': test_errors,
         'published': assignment.publish_on, 'now': timezone.now(), 'is_due': is_due,
         'is_submitted': is_submitted, 'date_time': timezone.now(), 'get_params': get_params,
         'total_sumissions': total_sumissions, 'formData': formData, 'mode': mode, 'allowed_exam': allowed_exam},
        context_instance=RequestContext(request)
    )

@login_required
def testcaseInputChange(request, testcaseID):
    '''
    Logic for downloading single testcase output file
    '''
    print("Reached herem\n")
    testcase = get_object_or_404(Testcase, pk=testcaseID)
    print("Reached here\n")

    program = testcase.program
    assignment = program.assignment
    is_due = None
    if assignment.deadline is not None:
        is_due = (timezone.now() >= assignment.deadline)
    course = assignment.course

    if not isEnrolledInCourse(course, request.user):
        return HttpResponseForbidden("Forbidden 403")

    if not testcase.output_files:
        return HttpResponseNotFound("File not found")

    is_moderator = isCourseModerator(course, request.user)

    if(is_moderator or program.program_type == "Practice" or is_due):
        input_file = open(testcase.input_files.name,'w')
        input_file.write(request.POST['new_input'])
        input_file.close()
        return HttpResponseRedirect(reverse('assignments_detailstestcase',
                                            kwargs={'testcaseID': testcaseID}))


    return HttpResponseForbidden("Forbidden 403")


def get_object_from_proctoring(exam_id, user_id):
    '''
    This function return remaining time and pause status for that corresponding exam_id
    and user_id in Proctoring model in exam module
    '''
    time_left = Proctoring.objects.filter(key=exam_id, owner=user_id)
    if not list(time_left):
        return 3600, "True", 1
    time = time_left[0].time - \
        (datetime.now(pytz.timezone('UTC')) - time_left[0].starttime)
    rem = time.seconds + time.days * 86400
    return rem, time_left[0].pause, time.days >= 0
