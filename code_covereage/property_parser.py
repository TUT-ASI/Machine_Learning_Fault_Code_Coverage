# Copyright (C) 2017 Siavoosh Payandeh Azad
# License: GNU GENERAL PUBLIC LICENSE Version 3
import copy


def report_prop_dictonary(prop_dict):
	"""
	prints the property dictionary to the console
	returns None
	"""
	if not isinstance(prop_dict, dict):
		raise ValueError("prop_dict is not a dictionary!")
	print "-----------------------------------------------------"
	print "parsed properties:"
	for item in prop_dict.keys():
		print item, "\t", prop_dict[item]
	# exit()
	return None


def remove_spaces(item_str):
	"""
	gets a string item "item_str" and returns a final_str which is the same but
	the spaces are removed!
	"""
	if not isinstance(item_str, str):
		raise ValueError("Item is not string!")
	final_str = ""
	for char in item_str:
		if char != " ":
			final_str += char 
	return final_str


def parse_condition_symptom_in_line(parse_line):
	"""
	This function gets a property as a line to parse and returns a list "condition_symptom" which 
	contains the condition or the symptom!
	the problem is that if we have a signal with X in its name, parsing might get messed 
	up!
	"""
	X_counter = 0	# this counts the number of Xs we see during parsing
	condition_symptom = []	
	while parse_line.count("X")>0:
		sub_line = ""
		X_start = 0
		counter = 0
		for char in parse_line:
			counter += 1
			if X_start == 0 and char == "X":	# this is the first X we see!
				X_start = 1
			elif X_start == 1 and char !="X":	# this is the end of Xs
				for item in sub_line.split("&"):
					if item != " ":
						condition_symptom.append(X_counter*"X"+remove_spaces(item))
				parse_line = parse_line[counter-1:]
				X_counter += 1
				break
			elif X_start == 1 and char =="X":	# still parsing Xs
				X_counter += 1
			else:
				if char != "(" and char != ")":	# its not an X, we remove the paranthesis and add the signal
					sub_line += char
	sub_line = ""
	for char in parse_line:
		if char != "(" and char != ")":
			sub_line += char
	for item in sub_line.split("&"):
		if item != " ":
			condition_symptom.append(X_counter*"X"+remove_spaces(item))
	return condition_symptom


def generate_prop_dictionary(prop_file_name):
	"""
	Parses the property file fed by the user and returns a dictionary with 
	property number as the key and a list of conditions as value.
	"""
	if not isinstance(prop_file_name, str):
		raise ValueError("prop_file_name is not a string!")
	print "-----------------------------------------------------"
	print "starting parsing the property file!"
	prop_file = open(prop_file_name, 'r')
	counter = 0
	prop_cond_dict = {}
	prop_symp_dict = {}
	for line in prop_file:
		if "id:" in line:
			#print line.split()
			property_id = line.split( )[1]
		if "G" in line:
			condition_section = line.split("->")[0][2:]
			prop_cond_dict[property_id] = copy.deepcopy(parse_condition_symptom_in_line(condition_section))

			#TODO: parse the symptom!
			symptom_section = line.split("->")[1]
			later_symptom = ""
			for char in symptom_section:
				if char != "(" and char != ")" and char != "\n" and char != "\r":
					later_symptom += char
			
			prop_symp_dict[property_id] = copy.deepcopy(parse_condition_symptom_in_line(later_symptom))
			counter += 1
	print "finished parsing property file... closing file!"
	prop_file.close()
	return prop_cond_dict, prop_symp_dict
