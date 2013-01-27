
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
#include "options.hh"
#include "support.hh"
#include "icode.hh"

/* 
    Please see the documentation in file ast.hh for a description of the
    classes. Here we provide an implementation of the class methods.
*/

/************* Methods for class asgn_Ast ******************/

void asgn_Ast::print_Node(ostream * asgn_fp)
{
    *asgn_fp << " Asgn: (LHS ";
    left->print_Node(asgn_fp);
    *asgn_fp << ", RHS ";
    right->print_Node(asgn_fp);
    *asgn_fp << ")\n";
}

void name_Ast::print_Node(ostream * name_fp)
{
    *name_fp << "(Name:(" << name << "))";
}

void int_num_Ast::print_Node(ostream * num_fp)
{
    *num_fp << "(Num:(" << num << "))";
}

void ret_Ast::print_Node(ostream * ret_fp) 
{ 
    *ret_fp << " Return\n";
}

static ostream * eval_fp = NULL;

void asgn_Ast::print_Eval_Result(asgn_Ast * ast)
{
     
   eval_fp = cmd_options.output_File();

   *eval_fp << " Statement ";

   ast->print_Node(eval_fp);

   *eval_fp << " After evaluation ";

   sym_Entry_Ptr se_P = ast->left->get_Sym_Entry();

   se_P->print_Sym_Entry_Eval_Details(eval_fp);
}

void exp_var_Ast::print_Node(ostream * name_fp)
{
    *name_fp << "(Name:(" << name << "))";
}

void float_num_Ast::print_Node(ostream * num_fp)
{
    *num_fp << "(Num:(" << num << "))";
}

void num_Ast::print_Node(ostream * num_fp)
{
    CHECK_INVARIANT(false, "print_Node() called on wrong node")
}


/************* Methods for class mult_Ast ******************/

void mult_Ast::print_Node(ostream * mult_fp) {
    *mult_fp<<"(MULT: ("; 
    left->print_Node(mult_fp);
    *mult_fp<<", ";
    right->print_Node(mult_fp);
    *mult_fp<<"))";
}

void plus_Ast::print_Node(ostream * plus_fp) {
    *plus_fp<<"(PLUS: (";
    left->print_Node(plus_fp);
    *plus_fp<<", ";
    right->print_Node(plus_fp);
    *plus_fp<<"))";
}

void minus_Ast::print_Node(ostream * minus_fp) {
    *minus_fp<<"(MINUS: (";
    left->print_Node(minus_fp);
    *minus_fp<<", ";
    right->print_Node(minus_fp);
    *minus_fp<<"))";
}

void div_Ast::print_Node(ostream * div_fp) {
    *div_fp<<"(DIV: (";
    left->print_Node(div_fp);
    *div_fp<<", ";
    right->print_Node(div_fp);
    *div_fp<<"))";
}

void uminus_Ast::print_Node(ostream * uminus_fp) {
    *uminus_fp<<"(UMINUS: (";
    left->print_Node(uminus_fp);
    *uminus_fp<<"))";
}

void arith_Ast::print_Node(ostream* fp) {
    CHECK_INVARIANT(false, "should not be called for arith_ast")
}
