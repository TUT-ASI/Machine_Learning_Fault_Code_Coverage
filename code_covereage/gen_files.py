# Copyright (C) 2017 Siavoosh Payandeh Azad
# License: GNU GENERAL PUBLIC LICENSE Version 3
from package import *
import sys

def generate_SV_properties(prop_cond_dict, prop_symp_dict):
	tb_file = open("results/SV_Assertions.sv", "w")
	prop_counter = 0
	for prop in prop_cond_dict.keys():
		tb_file.write("property property_" + str(prop_counter) + "; \n@(negedge clk) \n\t(")
		item_counter = 0
		for item in prop_cond_dict[prop]:
			if item_counter == len(prop_cond_dict[prop])-1:
				tb_file.write(item + ") |-> ")
				for item2 in prop_symp_dict[prop]:
					tb_file.write(item2 + "; \nendproperty\n")
			else:
				tb_file.write(item + " && ")
			item_counter += 1
		prop_counter += 1
		tb_file.write("\n")
	prop_counter = 0
	for prop in prop_cond_dict.keys():
		tb_file.write("property_"+str(prop_counter)+"_assert : assert property (property_"+str(prop_counter)+") else $error(\"property_"+str(prop_counter)+" not held!\");")
		prop_counter += 1
		tb_file.write("\n")
	tb_file.close()

	return None

def generate_tb(tb_file_name, prop_cond_dict, prop_symp_dict):
	"""
	generates a test bench for each property and stores it in results/TB/
	returns None
	"""
	if not isinstance(tb_file_name, str):
		raise ValueError("tb_file_name is not a string!")
	if not isinstance(prop_cond_dict, dict):
		raise ValueError("prop_cond_dict is not a dictionary!")
	if not isinstance(prop_symp_dict, dict):
		raise ValueError("prop_symp_dict is not a dictionary!")
	# TODO: we have to decide if it is fair that we have a wait statement for 1 clk cycle at the beginning of each testbench
	initial_file_name = tb_file_name.split(".")[0]

	for prop in prop_cond_dict.keys():
		if prop not in prop_symp_dict.keys():
			print prop_cond_dict.keys()
			print prop_symp_dict.keys()
			raise ValueError("property not in prop_symp_dict keys")
		tb_name = "results/TB/"+initial_file_name+"_"+str(prop)+".vhd"
		print "-----------------------------------------------------"
		print "starting generation of Testbench file:", tb_name
		tb_file = open(tb_name, "w")
		tb_file.write("---------------------------------------------\n")
		tb_file.write("-- THIS FILE IS GENERATED AUTOMATICALLY    --\n")
		tb_file.write("--           DO NOT EDIT                   --\n")
		tb_file.write("---------------------------------------------\n")
		tb_file.write("--Copyright (C) 2017  Siavoosh Payandeh Azad \n")
		tb_file.write("--License: GNU GENERAL PUBLIC LICENSE Version 3 \n\n")

		tb_file.write("library ieee;\n")
		tb_file.write("use ieee.std_logic_1164.all;\n")
		tb_file.write("use IEEE.STD_LOGIC_UNSIGNED.ALL;\n")
		tb_file.write("use IEEE.NUMERIC_STD.all;\n\n")

		tb_file.write("entity property_tb is\n")
		tb_file.write("end property_tb;\n\n")

		tb_file.write("architecture behavior of property_tb is\n\n")

		tb_file.write("-- component decleration\n")
		tb_file.write("component arbiter is\n")
		tb_file.write("port (\n")
		tb_file.write("    clk, rst: in std_logic;\n")
		tb_file.write("    Lflit_id, Nflit_id, Eflit_id, Wflit_id, Sflit_id: in std_logic_vector(2 downto 0);\n")
		tb_file.write("    Llength, Nlength, Elength, Wlength, Slength: in std_logic_vector(11 downto 0);\n")
		tb_file.write("    Lreq, Nreq, Ereq, Wreq, Sreq: in std_logic;\n")
		tb_file.write("    nextstate: out std_logic_vector(5 downto 0)\n")
		tb_file.write(");\n")
		tb_file.write("end component;\n\n")

		tb_file.write("signal nextstate: std_logic_vector(5 downto 0) := (others => '0');\n")
		tb_file.write("signal Lflit_id, Nflit_id, Eflit_id, Wflit_id, Sflit_id: std_logic_vector(2 downto 0):= (others => '0');\n")
		tb_file.write("signal Llength, Nlength, Elength, Wlength, Slength: std_logic_vector(11 downto 0):= (others => '0');\n")
		tb_file.write("signal Lreq, Nreq, Ereq, Wreq, Sreq: std_logic := '0';\n")
		tb_file.write("signal clk, rst : std_logic := '1';\n")
		tb_file.write("constant clk_period : time := 1 ns;\n")
		tb_file.write("\nbegin\n\n")

		tb_file.write("-- clock generation!\n")
		tb_file.write("    clk_process :process\n")
		tb_file.write("    begin\n")
		tb_file.write("        clk <= '0';\n")
		tb_file.write("        wait for clk_period/2;\n")
		tb_file.write("        clk <= '1';\n")
		tb_file.write("        wait for clk_period/2;\n")
		tb_file.write("    end process;\n\n")

		tb_file.write("\n\n-- instantiate the compoent\n")
		tb_file.write("DUT: arbiter\n")
		tb_file.write("     port map(clk, rst, Lflit_id, Nflit_id, Eflit_id, Wflit_id, Sflit_id, Llength, Nlength, Elength, Wlength, Slength, Lreq, Nreq, Ereq, Wreq, Sreq, nextstate);")

		tb_file.write("\n\n-- applying the stimuli\n")
		tb_file.write("    process begin\n")
		# tb_file.write("        -- list  of stimuli:"+str(prop_cond_dict[prop])+"\n")
		next_clk = False
		# we go through all the items and first sort the ones without X and then move to X and XX
		item_counter = 0	# items already written in the file
		clock_cycle = 0		# current clock cycle
		while (item_counter != len(prop_cond_dict[prop])):
			tb_file.write("        wait for 1.5 ns;\n")
			this_clock_signals = []
			for item in prop_cond_dict[prop]:
				if item.count('X') == clock_cycle:
					item_counter += 1
					if "!" in item:
						index = item.index("!")
						signal_name = item[index+1:]
						digit =  [int(s) for s in signal_name if s.isdigit()]
						if len(digit)>0:
							signal_name = signal_name[:signal_name.index(str(digit[0]))-1]+"("+str(digit[0])+")"
						tb_file.write("        "+signal_name+" <= '0'; ")
					else:
						if item != "1":
							signal_name = item[clock_cycle:]
							digit =  [int(s) for s in signal_name if s.isdigit()]
							if len(digit)>0:
								signal_name = signal_name[:signal_name.index(str(digit[0]))-1]+"("+str(digit[0])+")"
							tb_file.write("        "+signal_name+" <= '1'; ")
			clock_cycle += 1
			tb_file.write("\n")
		tb_file.write("        wait;\n")
		tb_file.write("    end process;\n\n")

		tb_file.write("\n\n-- checking the symptom\n")
		tb_file.write("    process begin\n")
		item_counter = 0	# items already written in the file
		clock_cycle = 0		# current clock cycle
		tb_file.write("     -- symptom list:"+str(prop_symp_dict[prop])+"\n")
		tb_file.write("        wait for 2 ns;\n")
		idle_counter = 0
		found = False
		while (item_counter != len(prop_symp_dict[prop])):

			for symptom in prop_symp_dict[prop]:
				if symptom.count('X') == clock_cycle:
					item_counter += 1
					value = 1
					symptom = symptom.replace("[", "(")
					symptom = symptom.replace("]", ")")
					if clock_cycle > 0:
						symptom = symptom[symptom.index("X"*clock_cycle)+clock_cycle:]
					if "!" in symptom:
						symptom = symptom[symptom.index("!")+1:]
						value = 0
					if idle_counter > 0:
						tb_file.write("        wait for "+str(idle_counter)+" ns;\n")
					tb_file.write("        assert ("+str(symptom)+" = '"+ str(value)+ "') report \"ASSERTION ["+str(clock_cycle)+"X"+str(symptom)+" = "+ str(value)+"] FAILED\" severity error;\n")
					idle_counter = 0
			clock_cycle += 1
			idle_counter += 1


		tb_file.write("        wait;\n")
		tb_file.write("    end process;\n\n")

		tb_file.write("\nEND;\n")

		print "finished generation of Testbench... closing the file!"
		tb_file.close()
	return None


def generate_do_file(tb_file_name, prop_dictionary):
	"""
	generates a do file for modelsim for each property and stores it in results/do_files/
	returns None
	"""
	if not isinstance(tb_file_name, str):
		raise ValueError("tb_file_name is not a string!")
	if not isinstance(prop_dictionary, dict):
		raise ValueError("prop_dictionary is not a dictionary!")
	initial_file_name = tb_file_name.split(".")[0]
	for prop in prop_dictionary:
		#sim_length = len(prop_dictionary[prop])+10
		sim_length = 1000
		tb_name = "results/TB/"+initial_file_name+"_"+str(prop)+".vhd"
		do_file = open("results/do_files/sim_"+str(prop)+".do", "w")

		do_file.write("#---------------------------------------------\n")
		do_file.write("#-- THIS FILE IS GENERATED AUTOMATICALLY    --\n")
		do_file.write("#--           DO NOT EDIT                   --\n")
		do_file.write("#---------------------------------------------\n")
		do_file.write("\n")

		do_file.write("vlib work\n")
		do_file.write("\n")
		do_file.write("# Include files and compile them\n")
		do_file.write("vlog -work work  \""+DUT_path+"state_defines.v\"\n")
		do_file.write("vlog -work work  \""+DUT_path+"parameters.v\"\n")
		do_file.write("vlog -work work -cover bcesfx -vopt +incdir+ -cover bcesfx  \""+DUT_path+"arbiter.v\"\n")
		do_file.write("vcom \""+tb_name+"\"\n")
		do_file.write("\n")
		do_file.write("# Start the simulation\n")
		do_file.write("vsim -coverage -voptargs=\"+cover=bcestfx\" work.property_tb\n")
		do_file.write("\n")
		do_file.write("# Run the simulation\n")
		do_file.write("run "+str(sim_length)+" ns\n")
		do_file.write("\n")
		do_file.write("# save the coverage reports\n")
		do_file.write("coverage save coverage_"+str(prop)+".ucdb\n")
		do_file.write("vcover report -output coverage_"+str(prop)+".txt coverage_"+str(prop)+".ucdb\n\n")
		do_file.write("vcover report -detail -output coverage_"+str(prop)+"_det.txt coverage_"+str(prop)+".ucdb\n\n")
		# do_file.write("write transcript transcript.txt\n")
		do_file.write("# Exit Modelsim after simulation\n")
		do_file.write("exit\n")
	do_file.close()
	return None
