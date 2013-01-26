
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


%skeleton "lalr1.cc"
%language "C++"
%defines
%locations

%define parser_class_name "cfglp"

%{
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <list>
#include <map>

using namespace std;

#include "common-classes.hh"
#include "evaluate.hh"
#include "support.hh"
#include "cfglp-ctx.hh"

#include "reg-alloc.hh"
#include "symtab.hh"
#include "ast.hh"
#include "icode.hh"
#include "program.hh"

#include "options.hh"

%}

%parse-param { cfglp_ctx &ctx }
%lex-param   { cfglp_ctx &ctx }

%union 
{
    int ival;
    double fval;
    std::string *sval;
    ast_Ptr ast_P;
    ast_List_Ptr ast_L;
    sym_Entry_Ptr sym_P;
    proc_Ptr proc_P;
    program_Ptr prog_P;
};

/* declare tokens */
%left '+' '-'
%left '*' '/'
%left '(' ')'
%token <ival> I_NUM
%token <fval> D_NUM
%token <sval> ID
%token <sval> ARTIFICIAL_VAR
%token <sval> EXP_VAR
%token <sval> BB_ID
%token INT RETURN STATIC FLOAT DOUBLE

%type <ast_P> exe_Stmt
%type <ast_P> expr
%type <ast_L> exe_Stmt_List
%type <sym_P> decl_Stmt 
%type <ival> bb_Decl
%type <proc_P> procedure
%type <prog_P> program

%{
  extern int yylex(yy::cfglp::semantic_type *yylval,
       yy::cfglp::location_type* yylloc,
       cfglp_ctx &ctx);

/* Some auxiliary local functions */

  static program_Ptr build_Program(proc_Ptr proc_P, sym_List_Ptr gsym_lp);
  static proc_Ptr build_Procedure (string name, int bb_num, ast_List_Ptr ast_lp,  
                sym_List_Ptr sym_lp, sym_List_Ptr sym_gp);
  static sym_Entry_Ptr redeclaration_Error(string name);
  static ast_Ptr missing_Declaration_Error(bool lhs_d, string lhs_n, bool rhs_d, string rhs_n, int line);
  static ast_Ptr process_Asgn_Name_Name(string lhs, string rhs, int line);
  static ast_Ptr process_Asgn_Name_Num(string lhs, int rhs, int line);
  static ast_Ptr process_Expr_equals_Id(string id, int arti_var, int line);
  static ast_Ptr process_Asgn_Name_Expr(string lhs, ast_Ptr rhs, int line, int arti_var);
  static ast_Ptr process_operator_Expr_Expr(ast_Ptr e1, ast_Ptr e2, char opr, int line);
  extern   int yylineno;
/* 
   Currently our program structure supports global declarations
   and a single procedure without any return type (we need to 
   check that it is the main procedure). We also do not support
   control flow or function calls and our RHS of assignments are 
   simple variables or number and have type INT.

   The complete grammar that we currently support is:

   program: decl_Stmt_List procedure
    |  procedure 
    ;
   procedure: ID '(' ')' '{' decl_Stmt_List bb_Decl exe_Stmt_List '}'
    ;
   decl_Stmt_List: decl_Stmt decl_Stmt_List
    |  decl_Stmt
    ;
   exe_Stmt_List: exe_Stmt_List exe_Stmt 
    |  exe_Stmt 
    ;
   decl_Stmt: static_kw INT ID ';'
    ;
   static_kw: 
    |  STATIC
    ;
   exe_Stmt : ID '=' ID ';'
    |  ID '=' I_NUM ';'
    |  RETURN ';' 
    ;
   bb_Decl: '<' ID I_NUM '>' ':'
    ;

   Observe that with a left recursive grammar declaration processing requires 
   inherited attributes because we need to compare current declarations with
   past declarations. 

   Building AST without type checking does not require such a check. Hence it
   can use synthesized attributes. However, type checking during AST building
   requires inherited attributes.

   Synthesized attributes are supported well by bison using the $ notation.
   Inherited attributes limited to a grammar rules can be implemented by
   using $i where i is the position of a grammar symbol in RHS but on the 
   left of current symbol.

   Since bison does not support L-attributed definitions, we do not have a 
   direct mechanism of implementing inherited attributes across grammar 
   rules. Hence we store sym_list in symtab_in_current_scope_P extract it 
   wherever required.

*/
%}

%initial-action {
 // Filename for locations here
 @$.begin.filename = @$.end.filename = new std::string("stdin");
}
%%

start: 
    {
        symtab_in_scope_P = new symtab_In_Scope;
        symtab_in_scope_P->allocate_Sym_List(); 
    }
    program[prg]
    {
        program_object_P = $prg;
        symtab_in_scope_P->deallocate_Sym_List(); 
    }
 ;

program: 
    decl_Stmt_List procedure[proc]
    {
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Top_List(); 
        $$=build_Program($proc, sym_lp);
    }
 |  procedure[proc] 
    {
        $$=build_Program($proc, NULL);
    }
 ;


procedure: 
    ID[id] 
    {
        string name = *$id;

        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
            symtab_in_scope_P->enter_Procedure_Name(name, yylineno);
        else
            redeclaration_Error(name);
        symtab_in_scope_P->allocate_Sym_List(); 
    }
    '(' ')' '{' decl_Stmt_List bb_Decl[bbn] exe_Stmt_List[slist] '}'
    {
        string name = *$id;
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Local_List(); 
        sym_List_Ptr sym_gp = symtab_in_scope_P->get_Symtab_Global_List(); 
        int bb_num = $bbn;
        ast_List_Ptr ast_lp = $slist;
        
        clean_Ast_List(ast_lp);
        
        $$ = build_Procedure (name, bb_num, ast_lp, sym_lp, sym_gp);
        symtab_in_scope_P->deallocate_Sym_List(); 
    }
 ;

exe_Stmt_List:   
    exe_Stmt_List[list] exe_Stmt[item] 
    {
        if ($list && $item)
        {
            ast_List_Ptr ast_lp = $list;
            ast_lp->push_back($item);
            $$ = ast_lp;
        }
        else if ($list && !$item)
        {
            $$ = $list;
        }
        else if (!$list && $item)
        {   
            ast_List_Ptr ast_lp = new list<ast_Ptr>;
            ast_lp->push_back($item);    
            $$ = ast_lp;
        }
        else $$ = NULL;
    }
                
 |  exe_Stmt[stmt] 
    {
        if ($stmt)
        { 
            ast_List_Ptr ast_lp = new list<ast_Ptr>;
            ast_lp->push_back($stmt);    
            $$ = ast_lp;
        }
        else $$ = NULL;
    }
 ;

decl_Stmt_List: 
    decl_Stmt_List decl_Stmt[item]
    {
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Top_List(); 
        if ($item)
            sym_lp->insert_Sym_Entry($item);
    }
 |  decl_Stmt[item]
    {
        sym_List_Ptr sym_lp = symtab_in_scope_P->get_Symtab_Top_List(); 
        if ($item)
            sym_lp->insert_Sym_Entry($item);
    }
 ;

decl_Stmt: 
    static_kw INT ID[id] ';'
    {
        string name = *$id;
        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
        {
            sym_Entry_Ptr s = new sym_Entry_for_Int_Var(name, yylineno, real);
            $$ = s;
        }
        else
            $$ = redeclaration_Error(name);
    }
    
  | static_kw DECIMALS ID[id] ';'
    {
    	string name = *$id;
        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
        {
            sym_Entry_Ptr s = new sym_Entry_for_Float_Var(name, yylineno, real);
            $$ = s;
        }
        else
            $$ = redeclaration_Error(name);
    }    
    
    //rules for artificial variable declaration
    //check: arti_var has been derived from a basic var
    //check: redeclared arti_var works!!
    
 |  static_kw INT ARTIFICIAL_VAR[id] ';'
    {
        string name = *$id;
        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
        {
            if(symtab_in_scope_P->declared_In_Visible_Scope(get_Var_Name(name), anywhere)) //derived from a base var or not
            {
                //sym_Entry_Ptr s = new sym_Entry_for_Int_Var(name, yylineno, artificial);
                $$ = NULL;
            } else
            {
                stringstream mesg; 
                mesg << "Declaration of artificial version of variable " << get_Var_Name(name)<<" on line " << yylineno <<" should have been preceded by a global declaration.";
                report_Violation_of_Condition(false, mesg.str());
            }
        }
        else
            $$ = redeclaration_Error(name);
    }
    
  | static_kw DECIMALS ARTIFICIAL_VAR[id] ';'
    {
    	string name = *$id;
        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false) //chcking for redeclaration
        {
            if(symtab_in_scope_P->declared_In_Visible_Scope(get_Var_Name(name), anywhere)) //derived from a base var or not
            {
                //sym_Entry_Ptr s = new sym_Entry_for_Float_Var(name, yylineno, artificial);
                $$ = NULL;
            } else
            {
                stringstream mesg; 
                mesg << "Declaration of artificial version of variable " << get_Var_Name(name)<<" on line " << yylineno <<" should have been preceded by a global declaration.";
                report_Violation_of_Condition(false, mesg.str());
            }       
        }
        else
            $$ = redeclaration_Error(name);
    }

    
 |  static_kw INT EXP_VAR[id] ';'
    {
        string name = *$id;
        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
        {
            sym_List_Ptr gl = symtab_in_scope_P->get_Symtab_Global_List();
            //if(gl->find_Name(get_Var_Name(name))) //derived from a base global var or not
            //{
                sym_Entry_Ptr s = new sym_Entry_for_Int_Var(name, yylineno, exp);
                $$ = s;    
            //}
//            else 
//            {
//                stringstream mesg; 
//                mesg << "Declaration of artificial version of variable " << get_Var_Name(name)<<" on line " << yylineno <<" should have been preceded by a global declaration.\n";
//                report_Violation_of_Condition(false, mesg.str());
//            }
            
        }
        else
            $$ = redeclaration_Error(name);
    }
    
  | static_kw DECIMALS EXP_VAR[id] ';'
    {
    	string name = *$id;
        if (symtab_in_scope_P->declared_In_Visible_Scope(name, symtab_Top) == false)
        {
//            sym_List_Ptr gl = symtab_in_scope_P->get_Symtab_Global_List();
//            if(gl->find_Name(get_Var_Name(name))) //derived from a base global var or not
//            {
                sym_Entry_Ptr s = new sym_Entry_for_Float_Var(name, yylineno, exp);
                $$ = s;
//            }
//            else 
//            {
//                stringstream mesg; 
//                mesg << "Declaration of artificial version of variable " << get_Var_Name(name)<<" on line " << yylineno <<" should have been preceded by a global declaration.\n";
//                report_Violation_of_Condition(false, mesg.str());
//            }
        }
        else
            $$ = redeclaration_Error(name);
    }
    
 ;

static_kw:  /* empty */
 | STATIC
 ;

bb_Decl: 
    BB_ID[id] ':'
    {
        string s = *$id;
        int index = s.find(' ');
        string str = s.substr(1, index - 1);
        int num = atoi(s.substr(index+1, str.length() - 2 - index).c_str());
        CHECK_INVARIANT (str == "bb", "Basic block is expected to be identified by the lexeme bb.\n")
        $$ = num;
    }
 ;

DECIMALS:
    FLOAT
    {}
 |  DOUBLE
    {}
;

exe_Stmt : 
     
    ID[lhs] '=' expr[rhs] ';'
 	{
 		/* things to check:
 		1. lhs has been declared or not
 		2. lhs-rhs type matches or not
 		*/
 		$$ = process_Asgn_Name_Expr(*$lhs, $rhs, yylineno, 0);
 	}
 |  ARTIFICIAL_VAR[lhs] '=' expr[rhs] ';'
 	{
 		/* things to check:
 		1. lhs has been declared or not  
 		2. lhs-rhs type matches or not
 		*/
 		$$ = process_Asgn_Name_Expr(*$lhs, $rhs, yylineno, 1);
 	}	
 |  EXP_VAR[lhs] '=' expr[rhs] ';'
 	{
 		/* things to check:
 		1. lhs has been declared or not  
 		2. lhs-rhs type matches or not
 		*/
 		$$ = process_Asgn_Name_Expr(*$lhs, $rhs, yylineno, 2);
 	}	
 |  RETURN ';' 
    {
        $$ = new ret_Ast();
    }
 ;
 
expr :
	ID[id]
	{
		//things to check: id declared or not
		$$ = process_Expr_equals_Id(*$id, 0, yylineno);
	}
 |  ARTIFICIAL_VAR[id]
 	{
        //things to check: extra_var declared or not
        $$ = process_Expr_equals_Id(*$id, 1, yylineno);
 	}	
 |  EXP_VAR[id]
 	{
        //things to check: extra_var declared or not
        $$ = process_Expr_equals_Id(*$id, 2, yylineno);
 	}	
 |  I_NUM[num]
	{
	    //nothing to check
	    $$ = new num_Ast($num);
	}
 |  D_NUM[num]
	{
        //nothing to check
        $$ = new float_num_Ast($num);
	}
 |   '(' DECIMALS ')' expr[e] 
	{
        //expr should be float
        $$ = $e;
	}
 |  '-' expr[e]
	{
        //nothing to check
        $$ = new uminus_Ast($e);
	}	
 |  expr[e1] '*' expr[e2] 
	{
	    //e1 type should match e2 type
	    $$ = process_operator_Expr_Expr($e1, $e2, '*', yylineno);
	}
 |  expr[e1] '-' expr[e2]
	{
	    //e1 type should match e2 type
	    $$ = process_operator_Expr_Expr($e1, $e2, '-', yylineno);
	}
 |  expr[e1] '+' expr[e2] 
	{
	    //e1 type should match e2 type
	    $$ = process_operator_Expr_Expr($e1, $e2, '+', yylineno);
	}
 |  expr[e1] '/' expr[e2]
	{
	    //e1 type should match e2 type
	    $$ = process_operator_Expr_Expr($e1, $e2, '/', yylineno);
	}
;

%%

/* Auxiliary functions called in the parser script alone. */

program_Ptr build_Program (proc_Ptr proc_P, sym_List_Ptr gsym_lp) 
{
    /*
       We make a pointer to a list of procedure (in this version 
       we have a single procedure).
    */
    proc_Map_Ptr proc_list = new map <string, proc_Ptr>;
    string proc_name = proc_P->get_Name();
    (*proc_list)[proc_name] = proc_P;
    /*
       Now we create a new program object. In this rule of the
       grammar, we have no global declarations.
    */
    program_Ptr prog_P = new program(gsym_lp, proc_list);

    return prog_P;
}

proc_Ptr build_Procedure (string name, int bb_num, ast_List_Ptr ast_lp,  sym_List_Ptr sym_lp, sym_List_Ptr sym_gp) 
{
     /*  
         We create a basic block and then add it to a list. In 
         this version the list contains a single basic block.
     */

     bb_Ptr bbp = new basic_Block(bb_num, ast_lp);
     bb_List_Ptr bblp = new list<bb_Ptr>;
     bblp->push_back(bbp);

     /*
         Then we use the procedure name and declaration list to 
         create a procedure object.
     */ 
    
     proc_Ptr proc_P = new procedure (name, sym_lp, sym_gp, bblp);

     return proc_P;
    }


sym_Entry_Ptr redeclaration_Error(string name)
{
    entity_Type en_t = symtab_in_scope_P->get_Entity_Type(name, anywhere);
    value_Type val_t = symtab_in_scope_P->get_Value_Type(name, anywhere);

    string en_s = "";
    string val_s = "";
    en_s = (en_t == entity_Var)? "variable" : "procedure";
    //val_s = (val_t == int_Val)? "INT" : "VOID";
    
    if(val_t == int_Val)
        val_s = "INT";
    else if(val_t == float_Val)
        val_s = "FLOAT";
    else val_s = "VOID";
    
    stringstream snum1; 
    snum1 << yylineno;

    string mesg = "Redeclaration of name `" + name + "' in the same scope on line " + snum1.str() + ". ";

    int old_line_no = symtab_in_scope_P->get_Line_Number(name);

    stringstream snum2; 
    snum2 << old_line_no;

    mesg = mesg + "Earlier declaration was as a " + en_s + " of type " + val_s + " on line " + snum2.str() + ". ";
    report_Violation_of_Condition(SHOULD_NOT_REACH, mesg);

    return NULL; 
}

ast_Ptr missing_Declaration_Error(bool lhs_d, string lhs_n, bool rhs_d, string rhs_n, int line)
{
	stringstream sn1; 
	stringstream mesg; 
	sn1 << line;

	if ((lhs_d == false) && (rhs_d == false))
			mesg << "Undeclared variables " << lhs_n << "and " << rhs_n << " on line " << line << ".";
	if (lhs_d == false)
		mesg << "Undeclared variable " << lhs_n << " on line " << line <<  ".";
	else if (rhs_d == false)
		mesg << "Undeclared variable " << rhs_n << " on line " << line <<  ".";
	else
		 CHECK_INVARIANT(SHOULD_NOT_REACH, "Both LHS and RHS variables seem to be declared")

	report_Violation_of_Condition (SHOULD_NOT_REACH, mesg.str());

	return NULL; 
}

ast_Ptr process_Asgn_Name_Name(string lhs, string rhs, int line)
{

    ast_Ptr asgn;

    bool lhs_d = symtab_in_scope_P->declared_In_Visible_Scope(lhs, anywhere); 
    bool rhs_d = symtab_in_scope_P->declared_In_Visible_Scope(rhs, anywhere); 

    if (lhs_d && rhs_d)
    {
        ast_Ptr ast_l = new name_Ast(lhs);
        ast_Ptr ast_r = new name_Ast(rhs);
        asgn = new asgn_Ast(ast_l, ast_r, line);
        asgn->type_Check(); 
    }
    else 
        asgn = missing_Declaration_Error(lhs_d, lhs, rhs_d, rhs, line);

    return asgn;
}

ast_Ptr process_Asgn_Name_Num(string lhs, int rhs, int line)
{

    ast_Ptr asgn = NULL;

    bool lhs_d = symtab_in_scope_P->declared_In_Visible_Scope(lhs, anywhere); 

    if (lhs_d)
    {
        ast_Ptr ast_l = new name_Ast(lhs);
        ast_Ptr ast_r = new num_Ast(rhs);
        asgn = new asgn_Ast(ast_l, ast_r, line);
        asgn->type_Check(); 
    }
    else 
       asgn = missing_Declaration_Error(lhs_d, lhs, true, "dummy_string", line);

    return asgn;
}


/*
------------------------------------------------
------------------------------------------------
------------------------------------------------
------------------------------------------------
*/
/* new implementation */


ast_Ptr process_operator_Expr_Expr(ast_Ptr e1, ast_Ptr e2, char opr, int line)
{
    //things to check: e1 type should match e2 type
    ast_Ptr asgn = NULL;
    
    if(e1 != NULL && e2!= NULL){
        bool correct = (e1->get_Val_Type() == e2->get_Val_Type());
        stringstream mesg;
        mesg << "Type Mismatch in " << opr << " expression on line " << line << ".\n";
        if(correct) 
        {
            switch (opr)
            {
                case '+':
                    asgn = new plus_Ast(e1, e2);
                    break;
                case '-':
                    asgn = new minus_Ast(e1, e2);
                    break;
                case '*':
                    asgn = new mult_Ast(e1, e2);
                    break;
                case '/':
                    asgn = new div_Ast(e1, e2);
                    break;
                default :
                    stringstream ss;
                    ss << "Operator "<< opr << " is unknown to the program.\n";
                    CHECK_INVARIANT(SHOULD_NOT_REACH, ss.str());
            }
        } 
        else
            report_Violation_of_Condition(SHOULD_NOT_REACH, mesg.str());
        return asgn;
    } else {
        return NULL;
    }
    
    
}

ast_Ptr process_Asgn_Name_Expr(string lhs, ast_Ptr rhs, int line, int arti_var) 
{
    /* things to check:
	1. lhs has been declared or not
	2. lhs-rhs type matches or not (function asgn->type_Check() does it)
	*/
	if(rhs == NULL && error_Status() == true)
	    return NULL;
	ast_Ptr asgn = NULL;
	bool lhs_d;
	if(arti_var == 1)
	    lhs_d = symtab_in_scope_P->declared_In_Visible_Scope(get_Var_Name(lhs), anywhere); 
	else 
	    lhs_d = symtab_in_scope_P->declared_In_Visible_Scope(lhs, anywhere); 
	    
	if (lhs_d)
    {
        ast_Ptr ast_l;
        switch(arti_var)
        {
            case 0:
                ast_l = new name_Ast(lhs);
                break;
            case 1:
                ast_l = new name_Ast(get_Var_Name(lhs));
                break;
            case 2:
                ast_l = new exp_var_Ast(lhs);
                break;
            default:
                CHECK_INVARIANT(false, "error at switch case for process_expr_equals_id\n")
        }
        ast_Ptr ast_r = rhs;
        asgn = new asgn_Ast(ast_l, ast_r, line);
        asgn->type_Check(); 
    }
    else 
       asgn = missing_Declaration_Error(lhs_d, lhs, true, "dummy_string", line);
	
	return asgn;
}

ast_Ptr process_Expr_equals_Id(string id, int arti_var, int line) 
{
    //things to check : id declared or not
    // 0 , 1 , 2: 
    ast_Ptr asgn = NULL;
    
	bool lhs_d;
	
	lhs_d = (arti_var == 1) ? symtab_in_scope_P->declared_In_Visible_Scope(get_Var_Name(id), anywhere) : symtab_in_scope_P->declared_In_Visible_Scope(id, anywhere); 
    
    
    if (lhs_d)
    {
        switch(arti_var)
        {
            case 0:
                asgn = new name_Ast(id);
                break;
            case 1:
                asgn = new name_Ast(get_Var_Name(id));
                break;
            case 2:
                asgn = new exp_var_Ast(id);
                break;
            default:
                CHECK_INVARIANT(false, "switch case for process_expr_equals_id")  
        }
    }
    else 
       asgn = missing_Declaration_Error(lhs_d, id, true, "dummy_string", line);
	//cout<< yylineno<<"\t"<<lhs_d<<"\n";
	return asgn;
}


//ast_Ptr process_typecast_Expr(ast_Ptr e, int line) 
//{
//    //things to check: e is float or not
//    ast_Ptr asgn = NULL;
//    stringstream mesg;
//    mesg << "Type Mismatch in between LHS and RHS expression on line " << line << ".\n";
//    if(e->get_Val_Type() == float_Num) 
//    {
//        asgn = e;
//    }
//    else
//        report_Violation_of_Condition(SHOULD_NOT_REACH, mesg.str());
//    return asgn;
//}
