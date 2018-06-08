# Copyright (C) 2017 Siavoosh Payandeh Azad and Tsotne Putkaradze
# License: GNU GENERAL PUBLIC LICENSE Version 3

import os
from package import *

#TODO: get the simulator return value and check if it actually finished successfully or not!

def run_simulator(list_of_properties, tb_file_name):
	file = open("transcript", 'w')
	file.close()
	initial_file_name = tb_file_name.split(".")[0]
	for i in list_of_properties:
		print "-------------------------------------------------------------------------------------------"
		print "\033[32mrunning testbench: ",i,"\033[39m"
		do_file_name = "results/do_files/sim_"+str(i)+".do"
		return_value = os.system("vsim -do " + do_file_name + " -batch")
		os.rename("coverage_"+str(i)+".txt", "results/cov_files/coverage_"+str(i)+".txt")
		os.rename("coverage_"+str(i)+"_det.txt", "results/cov_files/detailed/coverage_"+str(i)+"_det.txt")
		os.rename("coverage_"+str(i)+".ucdb", "results/cov_files/coverage_"+str(i)+".ucdb")
		file = open("transcript", 'r')
		for line in file:
			if "Error" in line:
				print line
				error_numbers =  int(line.split()[2][:line.split()[2].index(",")])
				if error_numbers > 0:
					raise ValueError("the simulation has error(s)!")
	return None
