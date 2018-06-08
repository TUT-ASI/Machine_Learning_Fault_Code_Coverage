# Copyright (C) 2017 Siavoosh Payandeh Azad
# License: GNU GENERAL PUBLIC LICENSE Version 3

import copy
import sys
from functions import *
from package import sys_arguments
from run_sim import run_simulator
from testing import *
from gen_files import *
from coverage_parser import *
from property_parser import *
from sva_parser import *

# TODO: check if everything is ok with the user's system! if there is a library dependency missing etc...
# TOOD: we need unit testing!


# system prep
sys_arguments = copy.deepcopy(parse_arguments(sys.argv, sys_arguments))					# parse the user inputs
# TODO: check sys_arguments 
generate_folders()		# generates folder structure
# starting...
if ".rtf" in sys_arguments["input_property_file"]:
	prop_cond_dict, prop_symp_dict = generate_prop_dictionary(sys_arguments["input_property_file"])		# parse the property recieved from input file 
	report_prop_dictonary(prop_cond_dict)		# prints contents of the the property dictionary to console
else:
	prop_cond_dict, prop_symp_dict = generate_prop_dictionary_sva(sys_arguments["input_property_file"])

test_prop_dicts(prop_cond_dict,prop_symp_dict)
generate_SV_properties(prop_cond_dict, prop_symp_dict)

# here the property dictionaries are ready... 
# moving to file genration
generate_tb(sys_arguments["testbench_file"], prop_cond_dict, prop_symp_dict)	# generates the TB lists
generate_do_file(sys_arguments["testbench_file"], prop_cond_dict)	# generates the do files
# tb and do files are generated! 
# starting the simulator phase
run_simulator(prop_cond_dict.keys(), sys_arguments["testbench_file"])	# runs the simulator and generates the coverage reports!

parse_all_coverage_reports()
