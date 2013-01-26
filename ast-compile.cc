
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
#include "icode.hh"


ast_Code_Ptr asgn_Ast::compile()
{
    /* 
       An assignment x = y where y is a variable is compiled as a combination of load and
       store statements:
       (load) R <- y 
       (store) x <- R
       If y is a constant, the statement is compiled as 
       (imm_Load) R <- y 
       (store) x <- R
       where imm_Load denotes the load immediate operation.
    */

    ast_Code_Ptr ast_code; 
    ics_Opd_Ptr mem_opd, reg_opd, opd1, opd2;
    reg_Desc_Ptr source_reg, load_reg;
    icode_Stmt_Ptr load_stmt, store_stmt; 
    sym_Entry_Ptr source_sym, dest_sym;

    bool do_lra = cmd_options.do_Lra();

    ast_code = NULL;
    source_sym = dest_sym = NULL;
    load_stmt = store_stmt = NULL;
    mem_opd = reg_opd = opd1 = opd2 = NULL;
    source_reg = load_reg = NULL;

    CHECK_INVARIANT (right != NULL, "Right child of an assignment tree node cannot be NULL")

    /*  
        The load instruction is generated for the right hand side. 
        The resulting register is used in the store instruction for
        for the left hand side.
    */

    switch (right->get_Tree_Op())
    {
        /* 
           We are processing the source of the assignment. The outcome of
           this processing is
           - a res_reg that is used as opd1 in the store statement
           - an optional load instruction that loads the source
             into res_reg
        */
        case name_Leaf:
            source_sym = right->get_Sym_Entry();
            source_reg = source_sym->get_Reg();
    
            if (do_lra)
            {
                lra_Outcome lra_result = allocate_Local_Registers(m2m, left, right);
               
                load_reg = lra_result.get_Reg();
    
                if (lra_result.is_Load_Needed())
                {
                    /* create the operand, result and then generate a load instruction */
                    opd1 = new mem_Addr_Opd(source_sym);
                    reg_opd = new reg_Addr_Opd(load_reg);
                    load_stmt = new move_IC_Stmt(load, opd1,reg_opd);
                }
                else
                {
                   /* We don't need to load but a store will be required 
                      and opd1 for store will have to be created
                   */
                    reg_opd = new reg_Addr_Opd(load_reg);
                }
            }
            else
            {
                opd1 = new mem_Addr_Opd(source_sym);
                load_reg = get_New_Reg();
                reg_opd = new reg_Addr_Opd(load_reg);
                load_stmt = new move_IC_Stmt(load, opd1,reg_opd);
            }
            break;
        case num_Leaf:
            if (do_lra)
            {
                lra_Outcome lra_result = allocate_Local_Registers(c2m, left, right);
                load_reg = lra_result.get_Reg();
            }
            else
                load_reg = get_New_Reg();

            reg_opd = new reg_Addr_Opd(load_reg);
            opd1 = new const_Opd(right->get_Num());
            load_stmt = new move_IC_Stmt(imm_Load, opd1,reg_opd);
            break;
        default:
            CHECK_INVARIANT (SHOULD_NOT_REACH, "RHS can only be either name or number")
    }
     
    /* 
       Now generate the store in destination using the 
       reg_opd created above 
    */
  
    CHECK_INVARIANT (left != NULL, "Left child of an assignment tree node cannot be NULL")
    CHECK_INVARIANT (left->get_Tree_Op() == name_Leaf, "LHS of an assignment should be a name")

    dest_sym = left->get_Sym_Entry();
    mem_opd = new mem_Addr_Opd(dest_sym);
    store_stmt = new move_IC_Stmt(store, reg_opd, mem_opd);

    if (do_lra == false)
        free_Reg(load_reg, dest_sym); 

    /* 
       Create the object to be returned by joining the load and 
       store statements. When we include the compute operations,
       we will have to suffix these load and store statements to
       the statements generated for the right hand side.
    */
    icode_Stmt_List ic_L;
    if (load_stmt)
    	ic_L.push_back(load_stmt);
    if (store_stmt)
    	ic_L.push_back(store_stmt);

    if (ic_L.empty() == false)
        ast_code = new code_for_Ast(load_reg, ic_L);

    //ast_code->print_Icode(&cout);

    return ast_code;
}

ast_Code_Ptr ret_Ast::compile()
{
    /* code for return */
}

ast_Code_Ptr ast_Node::compile()
{
    CHECK_INVARIANT(SHOULD_NOT_REACH, "compile method cannot be called on a non-asgn-Ast")
}

