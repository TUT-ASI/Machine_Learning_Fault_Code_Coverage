# Copyright (C) 2017 Siavoosh Payandeh Azad
# License: GNU GENERAL PUBLIC LICENSE Version 3
from package import *
import os 
import numpy as np
import string
from math import log10


def parse_cov_reports():
	"""
	parses the short coverage reports! 
	will generate a table where each row i shows different coverage parameters for property i
	also, will provide some statistic in form of a histogram showing number of properties vs. 
	their statement coverage.
	returns None
	"""
	covg_dictionary = {}
	for filename in os.listdir(cov_path):
		if filename.endswith(".txt"):
			property_number = int(filename[filename.index("_")+1:filename.index(".")])
			covg_dictionary[property_number] =[]
			file = open(cov_path+"/"+filename, 'r')
			for line in file:
				if "Stmts" in line:
					covg_dictionary[property_number].append(line.split()[-1])
				if "Branches" in line:
					covg_dictionary[property_number].append(line.split()[-1])
				if "States" in line:
					covg_dictionary[property_number].append(line.split()[-1])
				if "Transitions" in line:
					covg_dictionary[property_number].append(line.split()[-1])
				if "Toggle" in line:
					covg_dictionary[property_number].append(line.split()[-1])
				if "Total" in line:
					covg_dictionary[property_number].append(line.split()[-1])

	max_total = 0
	best_property = None
	total_coverage_list = []
	file = open(reports_path+"/general_stmt_coverage_report.txt","w")
	file.write("#\t stmt\t branch\t state\t trans\t tggl\t total\n")
	file.write("-------------------------------------------------------\n")
	for item in range(0, len(covg_dictionary.keys())):
		file.write( str(item)+ "\t")
		for percentage in covg_dictionary[item]:
			file.write( '%5s' %str(percentage)+"\t")
		file.write("\n") 
		total_coverage_list.append(float(covg_dictionary[item][-1][:-1]))
		if max_total < float(covg_dictionary[item][-1][:-1]):
			max_total = float(covg_dictionary[item][-1][:-1])
			best_property = item
	file.write("-------------------------------------------------------\n")
	file.write("max total coverage for single property:" +str(max_total)+"\n")
	file.write("best property:" +str(best_property)+"\n")
	file.close()

	print "-------------------------------------------------------"
	print "histogram of total coverage of properties"
	bins = 20
	h,b = np.histogram(sorted(total_coverage_list+[max_total+1]), bins)

	for i in range (0, bins-1):
		print string.rjust(`b[i]`, 7)[:int(log10(np.amax(b)))+5], '| ', '*'*int(70*h[i-1]/np.amax(h))
	print string.rjust(`b[bins]`, 7)[:int(log10(np.amax(b)))+5] 
	print "-------------------------------------------------------"
	return None


def parse_det_cov_report():
	"""
	parses the detailed coverage and prints the list of properties that hit each statement in the design
	returns stmt_covg_dictionary which is a dictionary with line numbers as keys and list of properties covering
	that line as value:
		stmt_covg_dictionary = { line_number_0: [list of properties covering line 0],
					  		   line_number_1: [list of properties covering line 1],
					  		   ...
		}
	"""
	print "parsing statement coverage"
	print "--------------"
	stmt_covg_dictionary = {}
	for filename in os.listdir(cov_detailed_path):
		if filename.endswith(".txt"):
			file = open(cov_detailed_path+"/"+filename, 'r')
			enable = False
			tb_number = int(filename[filename.index("_")+1:filename.index(".")][:-4])
			for line in file:
				if "Branch Coverage:" in line:
					enable = False
					break
				if enable:
					parameters = []
					for item in line[:50].split(" "):
						if item != '' : 
							parameters.append(item)
					if len(parameters)> 1:
						if parameters[2] != '***0***':
							if int(parameters[0]) not in stmt_covg_dictionary.keys():
								stmt_covg_dictionary[int(parameters[0])]= [tb_number]
							else:
								if tb_number not in stmt_covg_dictionary[int(parameters[0])]:
									stmt_covg_dictionary[int(parameters[0])].append(tb_number)
				if "Statement Coverage for" in line:
					enable = True
			file.close()
	file = open(reports_path+"/detailed_stmt_coverage_report.txt","w")
	for index in sorted(stmt_covg_dictionary.keys()):
		# print index, "\t", sorted(stmt_covg_dictionary[index])
		file.write('%5s' %("#"+str(index))+"\t\t")
		for item in stmt_covg_dictionary[index]:
			file.write(str(item)+" ,")
		file.write("\n")
	file.close()
	return stmt_covg_dictionary


def remove_covered_statements(stmt_covg_dictionary, property_id):
	"""
	removes statemets from property dictionary "stmt_covg_dictionary" which are covered by property "property_id"
	returns refined stmt_covg_dictionary
	"""
	# TODO: check if stmt_covg_dictionary is dictionary, check property_id
	deletion_list = []
	for item in stmt_covg_dictionary.keys():
		if property_id in stmt_covg_dictionary[item]:
			deletion_list.append(item)
	for del_item in deletion_list:
		del stmt_covg_dictionary[del_item]
	return stmt_covg_dictionary


def find_most_covering_prop (covg_dictionary):
	"""
	goes thorugh the property dictionary with the following strucutre:
		covg_dictionary = { line_number_0: [list of properties covering line 0],
							line_number_1: [list of properties covering line 1],
					  		...
		}
	and returns the property which covers most number of lines.

	"""
	big_list = []
	for item in covg_dictionary.keys():
		big_list += covg_dictionary[item]
	most_covering_prop =  max(set(big_list), key=big_list.count)
	return most_covering_prop


def find_minimal_set_of_properties(covg_dictionary):
	"""
	returns a list of properties that cover all the statements in the cov_dictionary. 
	"""
	print "Starting the process of finding a sub-set of properties that cover everything covered by initial set!"
	taken_properties = []
	while (len(covg_dictionary.keys())>0):
		best_prop = find_most_covering_prop(covg_dictionary)
		taken_properties.append(best_prop)
		remove_covered_statements(covg_dictionary, best_prop)

	print "number of properties in the sub-set:", len(taken_properties) 
	print "final set:", taken_properties
	print "----------------------------------------"
	return taken_properties


def parse_det_branch_coverage():
	print "parsing branch coverage"
	print "--------------"
	branch_covg_dictionary = {}
	for filename in os.listdir(cov_detailed_path):
		if filename.endswith(".txt"):
			file = open(cov_detailed_path+"/"+filename, 'r')
			enable = False
			tb_number = int(filename[filename.index("_")+1:filename.index(".")][:-4])
			for line in file:
				if "Condition Details" in line:
					enable = False
					break
				if enable:
					splited_line = line[:50].split()
					if len(splited_line) >= 3:
						if splited_line[0].isdigit():
							if int(splited_line[0]) > 1000:
								print tb_number, splited_line
							if splited_line[2] != '***0***':
								if int(splited_line[0]) not in branch_covg_dictionary.keys():
									branch_covg_dictionary[int(splited_line[0])]= [tb_number]
								else:
									if tb_number not in branch_covg_dictionary[int(splited_line[0])]:
										branch_covg_dictionary[int(splited_line[0])].append(tb_number)
				if "Branch Details" in line:
					enable = True
			file.close()
	file = open(reports_path+"/detailed_branch_coverage_report.txt","w")
	for index in sorted(branch_covg_dictionary.keys()):
		# print index, "\t", sorted(branch_covg_dictionary[index])
		file.write('%5s' %("#"+str(index))+"\t\t")
		for item in branch_covg_dictionary[index]:
			file.write(str(item)+" ,")
		file.write("\n")
	file.close()
	return branch_covg_dictionary


def parse_FSM_Transition_coverage():
	print "parsing FSM transitions"
	print "--------------"
	transition_dict = {}
	for filename in os.listdir(cov_detailed_path):
		if filename.endswith(".txt"):
			file = open(cov_detailed_path+"/"+filename, 'r')
			enable = False
			tb_number = int(filename[filename.index("_")+1:filename.index(".")][:-4])
			old_line = None
			for line in file:
				if " Uncovered States :" in line or "Uncovered Transitions" in line:
					enable = False
					break
				if enable == True: 
					if line.split()[0].isdigit():
						transition  = line.split()[3]+line.split()[4]+line.split()[5]
						if transition in transition_dict.keys():
							transition_dict[transition].append(tb_number)
						else:
							transition_dict[transition] = [tb_number]
				if  "Line            Trans_ID           Hit_count          Transition    " in line:
					enable = True
				old_line  =line
			file.close()

	file = open(reports_path+"/detailed_FSM_transiton_report.txt","w")
	for index in sorted(transition_dict.keys()):
		# print index, "\t", sorted(transition_dict[index])
		file.write(str(index)+"\t\t"+'%5s' %str(len(transition_dict[index]))+" items\t\t\t")
		for item in transition_dict[index]:
			file.write(str(item)+" ,")
		file.write("\n")
	file.close()	

	return transition_dict


def parse_FSM_states_coverage():
	print "parsing FSM covered states"
	print "--------------"
	state_dict = {}
	for filename in os.listdir(cov_detailed_path):
		if filename.endswith(".txt"):
			file = open(cov_detailed_path+"/"+filename, 'r')
			enable = False
			tb_number = int(filename[filename.index("_")+1:filename.index(".")][:-4])
			for line in file:
				if "Covered Transitions" in line or "Uncovered States" in line:
					enable = False
					break
				if enable == True: 
					if len(line.split())>1:
						if line.split()[1].isdigit():
							covered_state = line.split()[0]
							if covered_state in state_dict.keys():
								state_dict[covered_state].append(tb_number)
							else:
								state_dict[covered_state]=[tb_number]
				if  "Covered States" in line and "Uncovered States" not in line:
					enable = True
			file.close()

	file = open(reports_path+"/detailed_FSM_report.txt","w")
	for index in sorted(state_dict.keys()):
		# print index, "\t", sorted(state_dict[index])
		file.write(str(index)+"\t\t"+'%5s' %str(len(state_dict[index]))+" items\t\t\t")
		for item in state_dict[index]:
			file.write(str(item)+" ,")
		file.write("\n")
	file.close()

	return state_dict


def parse_all_coverage_reports():
	# here we have all the coverage reports 
	# moving to parsing phase!
	parse_cov_reports()		# parse normal coverage reports and provide statistics
	covg_dictionary = parse_det_cov_report() # parse detail coverage reports!
	#TODO: test the covg_dictionary
	find_minimal_set_of_properties(covg_dictionary)	# finds minimal set of properties that covers every statement.

	branch_dictionary = parse_det_branch_coverage()
	find_minimal_set_of_properties(branch_dictionary)

	FSM_transiton_dict = parse_FSM_Transition_coverage()
	find_minimal_set_of_properties(FSM_transiton_dict)

	FSM_state_dict = parse_FSM_states_coverage()
	find_minimal_set_of_properties(FSM_state_dict)
	return None 