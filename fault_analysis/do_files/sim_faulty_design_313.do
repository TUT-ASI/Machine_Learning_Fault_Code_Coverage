#---------------------------------------------
#-- THIS FILE IS GENERATED AUTOMATICALLY    --
#--           DO NOT EDIT                   --
#---------------------------------------------

# Include files and compile them
vlog -work work  "DUTs/state_defines.v"
vlog -work work  "DUTs/parameters.v"
vlog -work work -cover bcesfx -vopt +incdir+ -cover bcesfx "Faulty_Designs/arbiter/10_2.v"
vlog -sv "Testbench/bfm_arbiter.sv"
vlog -sv "Testbench/tb_userinterface.sv"

# Start the simulation
vsim -assertdebug -coverage -voptargs="+cover=bcestfx" work.tb_userinterface

# View Assertions
view assertions

# Run the simulation
run -all

# save the coverage reports
coverage save results/coverage_arbiter_313.ucdb
vcover report -assert -detail -output results/assertion_report_det_313.txt results/coverage_arbiter_313.ucdb

# Exit Modelsim after simulation
exit
