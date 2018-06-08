# Copyright (C) 2017 Siavoosh Payandeh Azad 
# License: GNU GENERAL PUBLIC LICENSE Version 3
import sys


def test_prop_cond_dict(prop_cond_dict):
	print "starting property condition dictionary test..."
	for item in prop_cond_dict.keys():
		if isinstance(prop_cond_dict[item], list):
			for sub_item in prop_cond_dict[item]:
				if not isinstance(sub_item, str):
					print "the item "+str(sub_item)+"is not string!"
					return False
		else:
			print "property "+str(item)+"is not containing a list!"
			return False
	return True


def test_prop_symp_dict(prop_symp_dict):
	print "starting property symptom dictionary test..."
	for item in prop_symp_dict.keys():
		if isinstance(prop_symp_dict[item], list):
			for sub_item in prop_symp_dict[item]:
				if not isinstance(sub_item, str):
					print "the item "+str(sub_item)+"is not string!"
					return False
		else:
			print "property "+str(item)+"is not containing a list!"
			return False
	return True


def test_prop_dicts(prop_cond_dict,prop_symp_dict):
	print "----------------------------------------------"
	print "starting testing..."
	if not test_prop_cond_dict(prop_cond_dict):
		print "=>    prop_cond_dict test faild..."
		sys.exit()
	else:
		print "=>    prop_cond_dict test passed..."

	if not test_prop_symp_dict(prop_symp_dict):
		print "=>    prop_symp_dict test faild..."
		sys.exit()
	else:
		print "=>    prop_symp_dict test passed..."
	return None
