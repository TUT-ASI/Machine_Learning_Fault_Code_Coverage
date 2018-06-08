# Copyright (C) 2017 Siavoosh Payandeh Azad
# License: GNU GENERAL PUBLIC LICENSE Version 3

import sys
import os
from package import *


def print_help():
	"""
	prints tools man to the console!
	returns None
	"""
	print "This program parses the properties fed in rtf format and generates a testbench for each property"
	print "program arguments:"
	print "\t-i [filename]:	recieves property file in rtf format. Important note, the properties should not use any internal signals!" 
	print "\t-o [filename]:	generated vhdl testbench" 
	#TODO:
	print "\nTODO:"
	print "     * We need to improve the property parser (for both condition and symptom)... its very primitive now!"
	print "     * The parser doesnt parse different inputs... somehow we need to fix that!"
	print "     * the coverage parser should be extended to also provide the branch and other coverage results!"
	print "\nExample:"
	print "		* python main.py -i [path/to/your/property/file] -o [prefered/name/for/testbench]"
	return None


def parse_arguments(sys_args, package_arguments):
	"""
	Parses the argumets passed to the tool and updates the package arguments accordingly
	Returns package arguement in form of a dictionary
	"""

	if "--help" in sys.argv[:]:
		print_help()
		sys.exit()

	if "-i" in sys.argv[:]:
		package_arguments["input_property_file"] = sys.argv[sys.argv.index("-i")+1]
		if not os.path.isfile(package_arguments["input_property_file"]):
			print "input propoerty file path is not valid"
			sys.exit()
	else:
		raise ValueError ("a valid property file is needed!")

	if "-o" in sys.argv[:]:
		package_arguments["testbench_file"] = sys.argv[sys.argv.index("-o")+1]
	else:
		package_arguments["testbench_file"] = "tb.vhd"
	return package_arguments


def generate_folders():
	"""
	Generates the folder structure as follows:
	
	|_results
		|
		|___TB 					for storing all generated testbenches
		|___do_files 			for storing all generated testbenches
		|___cov_files 			for storing all generated coverage reports
		|		|___detailed 	for storing all generated detailed coverage reports
		|___reports 			stors tool generated reports!

	cleans the folders if some files are remaining from previous runs. however, it only
	removes the files with .vhd extention from TB folder and with .do extention from 
	do_files folder.
	returns None
	"""
	if not os.path.exists(results_path):
		os.makedirs(results_path)

	if not os.path.exists(tb_path):
		os.makedirs(tb_path)
	else:
		file_list = [vhd_file for vhd_file in os.listdir(tb_path) if vhd_file.endswith(".vhd")]
		for vhd_file in file_list:
			os.remove(tb_path+"/"+vhd_file)

	if not os.path.exists(do_path):
		os.makedirs(do_path)
	else:
		file_list = [do_file for do_file in os.listdir(do_path) if do_file.endswith(".do")]
		for do_file in file_list:
			os.remove(do_path+"/"+do_file)

	if not os.path.exists(cov_path):
		os.makedirs(cov_path)
	else:
		file_list = [cov_file for cov_file in os.listdir(cov_path)if cov_file.endswith(".txt") or cov_file.endswith(".ucdb")]
		for cov_file in file_list:
			os.remove(cov_path+'/'+cov_file)

	if not os.path.exists(cov_detailed_path):
		os.makedirs(cov_detailed_path)
	else:
		file_list = [cov_file for cov_file in os.listdir(cov_detailed_path)if cov_file.endswith(".txt")]
		for cov_file in file_list:
			os.remove(cov_detailed_path+'/'+cov_file)

	if not os.path.exists(reports_path):
		os.makedirs(reports_path)
	else:
		file_list = [report_file for report_file in os.listdir(reports_path)if report_file.endswith(".txt")]
		for report_file in file_list:
			os.remove(reports_path+"/"+report_file)

	return None




