
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
#include "support.hh"

/* 
    Please see the documentation in file ast.hh for a description of the
    classes. Here we provide an implementation of the class methods.
*/

/************* Methods for class asgn_Ast ******************/

void asgn_Ast::type_Check()
{
    value_Type l_val_t = left->get_Val_Type();

    entity_Type l_en_t = left->get_Entity_Type();
    value_Type r_val_t = right->get_Val_Type();


    stringstream sn1; 
    sn1 << lineno;

    string mesg = "Name `" + left->get_Name() + "' is a procedure and hence cannot appear on the LHS of an assignment on line "
                      + sn1.str() + "."; 
    report_Violation_of_Condition(l_en_t != entity_Proc, mesg); 

    ast_Op oprn= right->get_Tree_Op();
    
    if (oprn == name_Leaf)
    {
         entity_Type r_en_t = right->get_Entity_Type();
         string mesg = "Name `" + right->get_Name() + "' is a procedure and hence cannot appear on the RHS of an assignment "
                      + sn1.str() + "."; 
         report_Violation_of_Condition(r_en_t != entity_Proc, mesg);
    }

    if(r_val_t != l_val_t)
    {
        string str = (oprn == name_Leaf || oprn == arti_var_Leaf  || oprn == exp_var_Leaf ) ? "`" + right->get_Name() + "'": "Expression";
        mesg = "Type mismatch between LHS `" + left->get_Name() + "' and RHS " + str + " on line "
                      + sn1.str() + ".";
        report_Violation_of_Condition(r_val_t == l_val_t, mesg);
    }    
    
    
}

entity_Type asgn_Ast::get_Entity_Type()
{
    CHECK_INVARIANT (SHOULD_NOT_REACH, "get_Entity_Type method cannot be called for an assignment statement")
}

int asgn_Ast::get_Line_Number()
{
    return lineno;
}


value_Type name_Ast::get_Val_Type()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Value_Type();
}

entity_Type name_Ast::get_Entity_Type()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Entity_Type();
}

string name_Ast::get_Name()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Name();
}

value_Type int_num_Ast::get_Val_Type()
{
    return int_Val;
}

string int_num_Ast::get_Name()
{
    /* We simply return a printable version of the number */

    stringstream snum; 
    snum << num;
    return snum.str();
}


value_Type num_Ast::get_Val_Type()
{
  CHECK_INVARIANT(false, "get_Val_Type() cannot be called for this node")
}


string num_Ast::get_Name()
{
  CHECK_INVARIANT(SHOULD_NOT_REACH, "get_Name() cannot be called for this node")
}



/**************** Default bodies for virtual functions **************/

value_Type ast_Node::get_Val_Type() 
{
     CHECK_INVARIANT(SHOULD_NOT_REACH, "undefined get_Val_Type method called for an ast_Node Object")
}

entity_Type ast_Node::get_Entity_Type() 
{
     CHECK_INVARIANT(SHOULD_NOT_REACH, "undefined get_Entity_Type method called for an ast_Node Object")
}

string ast_Node::get_Name() 
{
     CHECK_INVARIANT(SHOULD_NOT_REACH, "undefined get_Name method called for an ast_Node Object")
}

void ast_Node::type_Check() 
{
     CHECK_INVARIANT(SHOULD_NOT_REACH, "undefined type_Check method called for an ast_Node Object")
}

sym_Entry_Ptr ast_Node::get_Sym_Entry()
{
     CHECK_INVARIANT(SHOULD_NOT_REACH, "undefined get_Sym_Entry method called for an ast_Node Object")
}

value_Type exp_var_Ast::get_Val_Type()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Value_Type();
}

entity_Type exp_var_Ast::get_Entity_Type()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Entity_Type();
}

string exp_var_Ast::get_Name()
{
    CHECK_INVARIANT(sym_entry, "Sym entry of symbol cannot be NULL")
    return sym_entry->get_Name();
}



/* methods for class float_num_Ast*/
value_Type float_num_Ast::get_Val_Type()
{
    return float_Val;
}

string float_num_Ast::get_Name()
{
    /* We simply return a printable version of the number */
    stringstream snum; 
    snum << num;
    return snum.str();
}


