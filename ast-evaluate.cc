
/*********************************************************************************************

                                cfglp : A CFG Language Processor
                                --------------------------------

               About:
               Implemented by Uday Khedker (http://www.cse.iitb.ac.in/~uday) for 
               the courses cs302+cs306: Language Processors (theory and lab) at
               IIT Bombay. Release date Jan 6, 2013. Copyrights reserved by Uday
               Khedker. This implemenation has been made available purely for
               academic purposes without any warranty of any kind.

               Please see the README file for some details. A doxygen generated
               documentation can be found at http://www.cse.iitb.ac.in/~uday/cfglp


***********************************************************************************************/

#include <iostream>
#include <ostream>
#include <sstream>
#include <cstdlib>
#include <string>
#include <vector>

using namespace std;

#include "common-classes.hh"
#include "evaluate.hh"
#include "reg-alloc.hh"
#include "symtab.hh"
#include "ast.hh"
#include "program.hh"
#include "support.hh"
#include "options.hh"

eval_Result asgn_Ast::evaluate()
{
    CHECK_INVARIANT (right != NULL, "Right child of an assignment tree node cannot be NULL")
    eval_Result res = right->evaluate(); 

    CHECK_INVARIANT (left != NULL, "Left child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT (left->get_Tree_Op() == name_Leaf, "LHS of an assignment should be a name")
    left->set_Value_of_Evaluation(res);

    /* 
       Here we really do not need to return the result but since 
       the type of the evaluate function has to remain identical 
       across all derived classes, we return a dummy object which
       has been declared globally.
    */
    print_Eval_Result(this);
    return dummy_result;
}


eval_Result name_Ast::evaluate()
{
    CHECK_INVARIANT (sym_entry != NULL, "Left child of an assignment tree node cannot be NULL")
    return this->get_Value_of_Evaluation();
}

eval_Result int_num_Ast::evaluate()
{
    eval_Result res(num, NULL, int_Res);
    return res;
}

eval_Result num_Ast::evaluate()
{
    CHECK_INVARIANT (false, "evaluate cannot be called for num_Ast")
}

eval_Result ret_Ast::evaluate()
{
    /* 
       In this version, we have void procedures only
       hence we return the dummy value which is void.
        
    */
    return dummy_result;
}

eval_Result name_Ast::get_Value_of_Evaluation()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Value_of_Evaluation();
}

void name_Ast::set_Value_of_Evaluation(eval_Result res)
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    sym_entry->set_Value_of_Evaluation(res);
}

eval_Result ast_Node::get_Value_of_Evaluation()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Value_of_Evaluation cannot be called on a non-name-Ast")
}

void ast_Node::set_Value_of_Evaluation(eval_Result res)
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "set_Value_of_Evaluation cannot be called on a non-name-Ast")
}


eval_Result arith_Ast::evaluate()
{
    CHECK_INVARIANT(false, "should not be called for arith_Ast class")
}

eval_Result exp_var_Ast::evaluate() 
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "evaluate for exp var called")
    return dummy_result;
}

eval_Result float_num_Ast::evaluate()
{
    eval_Result res(num, NULL, float_Res);
    return res;
}

eval_Result mult_Ast::evaluate()
{
	eval_Result l_eval = left->evaluate();
	eval_Result r_eval = right->evaluate();
	CHECK_INVARIANT(l_eval.which_Result() == r_eval.which_Result(), "Type mismatch in * expression")
	res_Type r = l_eval.which_Result();
	float d_num;
	int i_num;
	if(r == float_Res) {
	    d_num = l_eval.get_Float_Val() * r_eval.get_Float_Val();
	    eval_Result res(d_num, NULL, float_Res);
        return res;
	} else {
	    i_num = l_eval.get_Int_Val() * r_eval.get_Int_Val();
	    eval_Result res(i_num, NULL, int_Res);
        return res;
	}    
}

eval_Result plus_Ast::evaluate()
{
	eval_Result l_eval = left->evaluate();
	eval_Result r_eval = right->evaluate();
	CHECK_INVARIANT(l_eval.which_Result() == r_eval.which_Result(), "Type mismatch in * expression")
	res_Type r= l_eval.which_Result();
	float d_num;
	int i_num;
	if(r == float_Res) {
	    d_num = l_eval.get_Float_Val() + r_eval.get_Float_Val();
	    eval_Result res(d_num, NULL, float_Res);
        return res;
	} else {
	    i_num = l_eval.get_Int_Val() + r_eval.get_Int_Val();
	    eval_Result res(i_num, NULL, int_Res);
        return res;
	}
}

eval_Result minus_Ast::evaluate()
{
	eval_Result l_eval = left->evaluate();
	eval_Result r_eval = right->evaluate();
	CHECK_INVARIANT(l_eval.which_Result() == r_eval.which_Result(), "Type mismatch in * expression")
	res_Type r = l_eval.which_Result();
	float d_num;
	int i_num;
	if(r == float_Res) {
	    d_num = l_eval.get_Float_Val() - r_eval.get_Float_Val();
	    eval_Result res(d_num, NULL, float_Res);
        return res;
	} else {
	    i_num = l_eval.get_Int_Val() - r_eval.get_Int_Val();
	    eval_Result res(i_num, NULL, int_Res);
        return res;
	}
}

eval_Result div_Ast::evaluate()
{
	eval_Result l_eval = left->evaluate();
	eval_Result r_eval = right->evaluate();
	CHECK_INVARIANT(l_eval.which_Result() == r_eval.which_Result(), "Type mismatch in * expression")
	res_Type r= l_eval.which_Result();
	float d_num;
	int i_num;
	if(r == float_Res) {
	    d_num = l_eval.get_Float_Val() / r_eval.get_Float_Val();
	    eval_Result res(d_num, NULL, float_Res);
        return res;
	} else {
	    i_num = l_eval.get_Int_Val() / r_eval.get_Int_Val();
	    eval_Result res(i_num, NULL, int_Res);
        return res;
	}
}

eval_Result uminus_Ast::evaluate()
{
	eval_Result l_eval = left->evaluate();
	res_Type r = l_eval.which_Result();
	float d_num;
	int i_num;
	if(r == float_Res) {
	    d_num =  -1.0 * l_eval.get_Float_Val();
	    eval_Result res(d_num, NULL, float_Res);
        return res;
	} else {
	    i_num = -1 * l_eval.get_Int_Val();
	    eval_Result res(i_num, NULL, int_Res);
        return res;
	}
}

