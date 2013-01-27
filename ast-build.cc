
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

asgn_Ast::asgn_Ast(ast_Ptr  l, ast_Ptr  r, int line)
{
    t_op = asgn;
    node_arity = binary;
    CHECK_INVARIANT(l != NULL, "Left child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != num_Leaf, "Left child of an assignment tree node cannot be a number")
    CHECK_INVARIANT(r != NULL, "Right child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != asgn, "Left child cannot be an assignment node")
    CHECK_INVARIANT(r->get_Tree_Op() != asgn, "Right child cannot be an assignment node")
    left = l;
    right = r;
    lineno = line;
}

asgn_Ast& asgn_Ast::operator=(const asgn_Ast& rhs)
{
    t_op = rhs.t_op;          
    node_arity = rhs.node_arity;
    left = rhs.left;
    right = rhs.right;
    lineno = rhs.lineno;
    return *this;
}

/************* Methods for class name_Ast ******************/

name_Ast::name_Ast(string n)
{
        t_op = name_Leaf;
        name = n;
        node_arity = zero_Arity;
        sym_entry = symtab_in_scope_P->get_Sym_Entry(n);
}

sym_Entry_Ptr name_Ast::get_Sym_Entry()
{
        return sym_entry;
}

/************* Methods for class int_num_Ast ******************/

int_num_Ast::int_num_Ast(int n)
{
    t_op = num_Leaf;
    num = n;
    node_arity = zero_Arity;
}

/************* Methods for class ret_Ast ******************/

ret_Ast::ret_Ast() 
{
    t_op = ret;
    node_arity = zero_Arity;
}

exp_var_Ast::exp_var_Ast(string n)
{
        t_op = exp_var_Leaf;
        name = n;
        node_arity = zero_Arity;
        sym_entry = symtab_in_scope_P->get_Sym_Entry(n);
}

exp_var_Ast::exp_var_Ast(string n, sym_Entry_Ptr s)
{
        t_op = arti_var_Leaf;
        name = n;
        node_arity = zero_Arity;
        sym_entry = s;
}

sym_Entry_Ptr exp_var_Ast::get_Sym_Entry()
{
        return sym_entry;
}

/* methods for class float_num_Ast */
float_num_Ast::float_num_Ast(double n)
{
    t_op = num_Leaf;
    num = n;
    node_arity = zero_Arity;
}


/************* Methods for class mult_Ast ******************/

mult_Ast::mult_Ast(ast_Ptr  l, ast_Ptr  r)
{
    t_op = mult_tree;
    node_arity = binary;
    CHECK_INVARIANT(l != NULL, "Left child of an multiply tree node cannot be NULL")
    //CHECK_INVARIANT(l->get_Tree_Op() != num_Leaf, "Left child of an assignment tree node cannot be a number")
    CHECK_INVARIANT(r != NULL, "Right child of an multiply tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != asgn, "Left child cannot be an assignment node")
    CHECK_INVARIANT(r->get_Tree_Op() != asgn, "Right child cannot be an assignment node")
    left = l;
    right = r;
    data_type = left->get_Val_Type();
}

/************* Methods for class plus_Ast ******************/

plus_Ast::plus_Ast(ast_Ptr  l, ast_Ptr  r)
{
    t_op = plus_tree;
    node_arity = binary;
    CHECK_INVARIANT(l != NULL, "Left child of an plus tree node cannot be NULL")
    //CHECK_INVARIANT(l->get_Tree_Op() != num_Leaf, "Left child of an assignment tree node cannot be a number")
    CHECK_INVARIANT(r != NULL, "Right child of an plus tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != asgn, "Left child cannot be an assignment node")
    CHECK_INVARIANT(r->get_Tree_Op() != asgn, "Right child cannot be an assignment node")
    left = l;
    right = r;
    data_type = left->get_Val_Type();
}

/************* Methods for class minus_Ast ******************/

minus_Ast::minus_Ast(ast_Ptr  l, ast_Ptr  r)
{
    t_op = minus_tree;
    node_arity = binary;
    CHECK_INVARIANT(l != NULL, "Left child of an minus tree node cannot be NULL")
    //CHECK_INVARIANT(l->get_Tree_Op() != num_Leaf, "Left child of an assignment tree node cannot be a number")
    CHECK_INVARIANT(r != NULL, "Right child of an minus tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != asgn, "Left child cannot be an assignment node")
    CHECK_INVARIANT(r->get_Tree_Op() != asgn, "Right child cannot be an assignment node")
    left = l;
    right = r;
    data_type = left->get_Val_Type();
}

/************* Methods for class div_Ast ******************/

div_Ast::div_Ast(ast_Ptr  l, ast_Ptr  r)
{
    t_op = divide_tree;
    node_arity = binary;
    CHECK_INVARIANT(l != NULL, "Left child of an div tree node cannot be NULL")
    //CHECK_INVARIANT(l->get_Tree_Op() != num_Leaf, "Left child of an assignment tree node cannot be a number")
    CHECK_INVARIANT(r != NULL, "Right child of an div tree node cannot be NULL")
    CHECK_INVARIANT(l->get_Tree_Op() != asgn, "Left child cannot be an assignment node")
    CHECK_INVARIANT(r->get_Tree_Op() != asgn, "Right child cannot be an assignment node")
    left = l;
    right = r;
    data_type = left->get_Val_Type();
}

/************* Methods for class uminus_Ast ******************/

uminus_Ast::uminus_Ast(ast_Ptr p)
{
    t_op = uminus;
    node_arity = unary;
    CHECK_INVARIANT(p != NULL, "Child of an uminus tree node cannot be NULL")
    //CHECK_INVARIANT(l->get_Tree_Op() != num_Leaf, "Left child of an assignment tree node cannot be a number")
    CHECK_INVARIANT(p->get_Tree_Op() != asgn, "Child cannot be an assignment node")
    left = p;
    right = NULL;
    data_type = left->get_Val_Type();
}

