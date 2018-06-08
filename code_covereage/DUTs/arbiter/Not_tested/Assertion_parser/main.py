# Copyright (C) 2017 Siavoosh Payandeh Azad
# License: GNU GENERAL PUBLIC LICENSE Version 3

import copy
import sys
import os
import numpy as np
import string
from math import log10

directory = "Faulty_Designs/"
results_directory = "results/"


def find_set_coverage(assertions_dictionary, chosen_properties, debug):
	if debug:		
		print "-----"*10
		print "checking properties:", sorted(chosen_properties)
	covered_designs = []
	for i in range(0, len(assertions_dictionary[assertions_dictionary.keys()[0]])):
		covered_designs.append(0)

	for prop in chosen_properties:
		#print prop, assertions_dictionary[prop]
		for i in range(0, len(assertions_dictionary[prop])):
			if int(assertions_dictionary[prop][i]) >0:
				if covered_designs[i]==0:
					covered_designs[i] = 1
	if debug:
		print "covered",covered_designs.count(1), "cases out of", len(covered_designs) 
	return covered_designs.count(1)




def parse_assertion_reports():
	"""
	parses the assertion reports:
		assertion_dictionary = { ?? }
	"""
	print "Parsing assertions"
	print "--------------"
	assertions_dictionary = {}
	for filename in os.listdir(results_directory):
		if filename.endswith(".txt"):
			assertion_file = open(results_directory+filename, 'r')
			print assertion_file
			line = assertion_file.readline()
			property_number = None
			while line != "":
				
				if "arbiter_tb.sv" in line:
					parameters = []

					for item in line[:55].split(" "):
						if item != '' : 
							parameters.append(item)
							parameters[0]="Assertion number " + str(property_number)
					if property_number in assertions_dictionary.keys():
						assertions_dictionary[property_number].append(parameters[1])
					else:
						assertions_dictionary[property_number] = [parameters[1]]
					print parameters
				else:
					if "property_" in line:
						property_number = int(line[:-1].split("_")[2])
				line = assertion_file.readline()
			assertion_file.close()
	print "-------------------------------------"
	for key in assertions_dictionary.keys():
		print key, "\t",assertions_dictionary[key]

	max_covered_cases = 0
	chosen_prop = []
	best_result = []
	full_set_covered_cases = find_set_coverage(assertions_dictionary, assertions_dictionary.keys(),True)
	while max_covered_cases <	full_set_covered_cases:
		for prop in assertions_dictionary.keys():
			if prop not in chosen_prop:
				current_list = copy.deepcopy(chosen_prop)+[prop]
				covered_cases = find_set_coverage(assertions_dictionary, current_list,True)
				if covered_cases > max_covered_cases:
					best_result = copy.deepcopy(current_list)
					max_covered_cases = covered_cases

		chosen_prop = copy.deepcopy(best_result)
	print "====="*10
	print "subset that covers everything:", sorted(chosen_prop)
	print find_set_coverage(assertions_dictionary, chosen_prop,True)
	for item in assertions_dictionary.keys():
		print item, find_set_coverage(assertions_dictionary, [item], False)
	return assertions_dictionary


# os.system("rm -rf do_files") 
# os.system("rm -rf results") 

# os.system("mkdir do_files") 
# os.system("mkdir results") 

file_counter = 0

print "Directory has " + str(len(os.listdir(directory))) + " files."

for filename in os.listdir(directory):
	if filename.startswith("faulty_design"):
		do_filename = open("do_files/sim_faulty_design_"+str(file_counter)+".do", "w")

		do_filename.write("#---------------------------------------------\n")
		do_filename.write("#-- THIS FILE IS GENERATED AUTOMATICALLY    --\n")
		do_filename.write("#--           DO NOT EDIT                   --\n")
		do_filename.write("#---------------------------------------------\n")
		do_filename.write("\n")

		do_filename.write("# Include files and compile them\n")
		do_filename.write("vlog -work work  \"state_defines.v\"\n")
		do_filename.write("vlog -work work  \"parameters.v\"\n")
		do_filename.write("vlog -work work -cover bcesfx -vopt +incdir+ -cover bcesfx \"" + directory + filename + "\"\n")
		do_filename.write("vlog -sv \"arbiter_tb.sv\"\n")
		do_filename.write("\n")

		do_filename.write("# Start the simulation\n")
		do_filename.write("vsim -assertdebug -coverage -voptargs=\"+cover=bcestfx\" work.arbiter_tb\n")
		do_filename.write("\n")

		do_filename.write("# View Assertions\n")
		do_filename.write("view assertions\n")
		do_filename.write("\n")

		do_filename.write("# Run the simulation\n")
		do_filename.write("run -all\n")
		do_filename.write("\n")

		do_filename.write("# save the coverage reports\n")
		do_filename.write("coverage save results/coverage_arbiter_"+str(file_counter)+".ucdb\n")


		do_filename.write("vcover report -assert -detail -output results/assertion_report_det_"+str(file_counter)+".txt results/coverage_arbiter_" + str(file_counter) + ".ucdb\n")
		do_filename.write("\n")

		do_filename.write("# Exit Modelsim after simulation\n")
		do_filename.write("exit\n")

	 	do_filename.close()
		file_counter += 1

design_number = 1
do_files_directory = "do_files/"


# for filename in os.listdir(do_files_directory):
# 	print "-------------------------------------------------------------------------------------------"
# 	print "\033[32mNow processing file: ",str(filename),"\033[39m"
# 	os.system("vsim -do " + do_files_directory + filename + " -batch")
# 	print "Simulated faulty design " + str(design_number)
# 	design_number += 1

parse_assertion_reports()

