
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

void num_Ast::print_Node(ostream * num_fp)
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

/* new crude implementation */
//-----------------------------------------------------------
//-----------------------------------------------------------
//-----------------------------------------------------------
//-----------------------------------------------------------
//-----------------------------------------------------------
//-----------------------------------------------------------
//void arti_var_Ast::print_Node(ostream * name_fp)
//{
//    //CHECK_INVARIANT(SHOULD_NOT_REACH, "arti var should can not be called for print_Node")
//    *name_fp << "(Name:(" << name << "))";
//}

void exp_var_Ast::print_Node(ostream * name_fp)
{
    *name_fp << "(Name:(" << name << "))";
}

void float_num_Ast::print_Node(ostream * num_fp)
{
    *num_fp << "(Num:(" << num << "))";
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
    pt->print_Node(uminus_fp);
    *uminus_fp<<"))";
}


/*
Expanding AST
*/


void check_for_arti(ast_Ptr root)
{
	ast_Ptr ptr;
	
	if (root->get_Node_Arity() == binary)
	{
		if ((root->get_Left())->get_Tree_Op() == arti_var_Leaf)
		{
			
			string str = get_Var_Name((root->get_Left())->get_Name());
			ptr = new name_Ast(str);
			root->assign_Left(ptr);
		}
		
		if ((root->get_Right())->get_Tree_Op() == arti_var_Leaf)
		{
			ptr = new name_Ast(get_Var_Name((root->get_Right())->get_Name()));
			root->assign_Right(ptr);
		}
		
		check_for_arti(root->get_Left());
		check_for_arti(root->get_Right());
	}
	
	else if (root->get_Node_Arity() == unary)
	{
		if ((root->get_Pt())->get_Tree_Op() == arti_var_Leaf)
		{
			ptr = new name_Ast(get_Var_Name((root->get_Right())->get_Name()));
			root->assign_Pt(ptr);
		}
		
		check_for_arti(root->get_Pt());
	}
}

void check_for_exp(ast_Ptr root, std::map<string,ast_Ptr> exp)
{
	sym_Entry_Ptr sym_ptr;
	if (root->get_Tree_Op() == asgn)
	{
		if ((root->get_Right())->get_Tree_Op() == exp_var_Leaf)
		{
			//cout<<exp[(root->get_Right())->get_Name()]<<endl;
			
			sym_ptr = symtab_in_scope_P->get_Sym_Entry((root->get_Right())->get_Name());
			root->assign_Right(sym_ptr->get_Sym_Entry_Ptr());
			
			//root->assign_Right(exp[(root->get_Right())->get_Name()]);
		}
		check_for_exp(root->get_Right(),exp);
	}
	
	else if (root->get_Node_Arity() == binary)
	{
		if ((root->get_Right())->get_Tree_Op() == exp_var_Leaf)
		{
			//cout<<exp[(root->get_Right())->get_Name()]<<endl;
			if (exp[(root->get_Right())->get_Name()] != 0)
			{
				sym_ptr = symtab_in_scope_P->get_Sym_Entry((root->get_Right())->get_Name());
				root->assign_Right(sym_ptr->get_Sym_Entry_Ptr());
				
				//root->assign_Right(exp[(root->get_Right())->get_Name()]);
			}
		}
		
		if ((root->get_Left())->get_Tree_Op() == exp_var_Leaf)
		{
			//cout<<exp[(root->get_Left())->get_Name()]<<endl;
			if (exp[(root->get_Left())->get_Name()] != 0)
			{
				sym_ptr = symtab_in_scope_P->get_Sym_Entry((root->get_Left())->get_Name());
				root->assign_Left(sym_ptr->get_Sym_Entry_Ptr());
				
				//root->assign_Left(exp[(root->get_Left())->get_Name()]);
			}
		}
		 		
		check_for_exp(root->get_Left(),exp);
		check_for_exp(root->get_Right(),exp);
	}
	
	else if (root->get_Node_Arity() == unary)
	{
		if ((root->get_Pt())->get_Tree_Op() == exp_var_Leaf)
		{
			//cout<<"U"<<endl;
			//cout<<exp[(root->get_Pt())->get_Name()]<<endl;
			if (exp[(root->get_Pt())->get_Name()] != 0)
			{
				sym_ptr = symtab_in_scope_P->get_Sym_Entry((root->get_Pt())->get_Name());
				root->assign_Pt(sym_ptr->get_Sym_Entry_Ptr());
				
				//root->assign_Pt(exp[(root->get_Pt())->get_Name()]);
			}
		}
	
		check_for_exp(root->get_Pt(),exp);
	}
}

void clean_Ast_List(ast_List_Ptr alist)
{
	list<ast_Ptr>::iterator it, temp_it;
	ast_Ptr flag[alist->size()];
	int count = 0,i;
	std::map<string,ast_Ptr> exp_list;
	for (it=alist->begin() ; it != alist->end() ; ++it)
	{
		check_for_arti(*it);
	}
	
	for (it=alist->begin() ; it != alist->end() ; ++it)
	{	
		if ( ((*it)->get_Tree_Op() == asgn) )
		{
			if ( (((*it)->get_Left())->get_Tree_Op() == name_Leaf) && (((*it)->get_Right())->get_Tree_Op() == name_Leaf) )
			{
				if ( ((*it)->get_Left())->get_Name() == ((*it)->get_Right())->get_Name() )
				{
					flag[count] = *it;
					count++;
				}
			}
			
		}
	}
	for (i = 0 ; i<count ; i++)
	{
		alist->remove(flag[i]);
	}
	
	ast_Ptr root;
	
	for (it = alist->begin() ; it != alist->end() ; ++it)
	{	
		check_for_exp(*it,exp_list);
		
		if ( ((*it)->get_Tree_Op() == asgn) && (((*it)->get_Left())->get_Tree_Op() == exp_var_Leaf) )
		{
			exp_list[((*it)->get_Left())->get_Name()] = (*it)->get_Right();
			
			sym_Entry_Ptr sym_ptr = symtab_in_scope_P->get_Sym_Entry(((*it)->get_Left())->get_Name());
			sym_ptr->set_Sym_Entry_Ptr((*it)->get_Right());
			//cout<<((*it)->get_Left())->get_Name()<<" "<<exp_list[((*it)->get_Left())->get_Name()]<<endl;
		}
	}
	
	count = 0;
	for (it = alist->begin() ; it != alist->end() ; ++it)
	{
		root = *it;
		if ((root->get_Tree_Op() == asgn) && ((root->get_Left())->get_Tree_Op() == exp_var_Leaf))
		{
			flag[count] = *it;
			count++;
		}
	}
	for (i = 0 ; i<count ; i++)
	{
		alist->remove(flag[i]);
	}
	
	
}
