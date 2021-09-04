(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun E'( itree(inode("expr",_),
            [
                or_expr
            ]
        ),
        m0
  ) = E'(or_expr,m0)

   | E'(itree(inode("or_expr",_),
            [
                and_expr
            ]
        ),
        m0
  ) = E'(and_expr, m0)
  
   | E'(itree(inode("or_expr",_),
            [
                or_expr,
                itree(inode("||",_), [] ),
                and_expr
            ]
        ),
        m0
  ) =   let
            val(v1, m1) = E'(or_expr,m0)
        in
            if v1 then (v1, m1)
            else E'(and_expr,m1)
        end
  
   | E'(itree(inode("and_expr",_),
            [
                equality_expr
            ]
        ),
        m0
  ) = E'(equality_expr, m0)
  
   | E'(itree(inode("and_expr",_),
            [
                and_expr,
                itree(inode("&&",_), [] ),
                equality_expr
            ]
        ),
        m0
  ) =   let
            val(v1, m1) = E'(and_expr,m0)
        in
            if v1 then E'(equality_expr,m1)
            else (v1, m1)
        end
  
   | E'(itree(inode("equality_expr",_),
            [
                relational_expr
            ]
        ),
        m0
  ) = E'(relational_expr, m0)

   | E'(itree(inode("equality_expr",_),
            [
                equality_expr,
                itree(inode("==",_), [] ),
                relational_expr
            ]
        ),
        m0
  ) =   let
            val(v1, m1) = E'(equality_expr,m0)
            val(v2, m2) = E'(relational_expr,m1)
        in
            (v1 = v2, m2)
        end
  
   | E'(itree(inode("equality_expr",_),
            [
                equality_expr,
                itree(inode("!=",_), [] ),
                relational_expr
            ]
        ),
        m0
  ) =   let
            val(v1, m1) = E'(equality_expr,m0)
            val(v2, m2) = E'(relational_expr,m1)
        in
            (v1 <> v2, m2)
        end
  
   | E'(itree(inode("relational_expr",_),
            [
                additive_expr
            ]
        ),
        m0
  ) = E'(additive_expr, m0)

   | E'(itree(inode("relational_expr",_),
            [
                relational_expr,
                itree(inode(">",_), [] ),
                additive_expr
            ]
        ),
        m0
  ) =   let
            val(v1, m1) = E'(relational_expr,m0)
            val(v2, m2) = E'(additive_expr,m1)
        in
            (1 > 2, m2) (* TODO: need to fix this *)
        end
  
   | E'(itree(inode("relational_expr",_),
            [
                relational_expr,
                itree(inode("<",_), [] ),
                additive_expr
            ]
        ),
        m0
  ) =   let
            val(v1, m1) = E'(relational_expr,m0)
            val(v2, m2) = E'(additive_expr,m1)
        in
            (1 < 2, m2)  (* TODO: need to fix this *)
        end
  
   | E'(itree(inode("additive_expr",_),
            [
                multiplicative_expr
            ]
        ),
        m0
  ) = E'(multiplicative_expr, m0)

   | E'(itree(inode("additive_expr",_),
            [
                additive_expr,
                itree(inode("+",_), [] ),
                multiplicative_expr
            ]
        ),
        m0
  ) =   (true,m0)  (* TODO: need to fix this *)
        
   | E'(itree(inode("additive_expr",_),
            [
                additive_expr,
                itree(inode("-",_), [] ),
                multiplicative_expr
            ]
        ),
        m0
  ) =   (true,m0)  (* TODO: need to fix this *)
  
   | E'(itree(inode("multiplicative_expr",_),
            [
                unary_expr
            ]
        ),
        m0
  ) = E'(unary_expr, m0)

   | E'(itree(inode("multiplicative_expr",_),
            [
                multiplicative_expr,
                itree(inode("*",_), [] ),
                unary_expr
            ]
        ),
        m0
  ) =   (true,m0)  (* TODO: need to fix this *)
  
   | E'(itree(inode("multiplicative_expr",_),
            [
                multiplicative_expr,
                itree(inode("/",_), [] ),
                unary_expr
            ]
        ),
        m0
  ) =   (true,m0)  (* TODO: need to fix this *)
  
   | E'(itree(inode("unary_expr",_),
            [
                exponential_expr
            ]
        ),
        m0
  ) = E'(exponential_expr, m0)

   | E'(itree(inode("unary_expr",_),
            [
                itree(inode("-",_), [] ),
                unary_expr
            ]
        ),
        m0
  ) =   (true,m0)  (* TODO: need to fix this *)
  
   | E'(itree(inode("unary_expr",_),
            [
                itree(inode("!",_), [] ),
                unary_expr
            ]
        ),
        m0
  ) =   (true,m0)  (* TODO: need to fix this *)
  
   | E'(itree(inode("exponential_expr",_),
            [
                base
            ]
        ),
        m0
  ) = E'(base, m0)

   | E'(itree(inode("exponential_expr",_),
            [
                base,
                itree(inode("^",_), [] ),
                exponential_expr
            ]
        ),
        m0
  ) =   (true,m0)  (* TODO: need to fix this *)
  
   | E'(itree(inode("base",_),
            [
                decorated_id
            ]
        ),
        m0
  ) = E'(decorated_id, m0)

   | E'(itree(inode("value",_),
            [
                value
            ]
        ),
        m0
  ) = E'(value, m0)

   | E'(itree(inode("integer",_),
            [
                integer
            ]
        ),
        m0
  ) = E'(integer, m0)

   | E'(itree(inode("boolean",_),
            [
                boolean
            ]
        ),
        m0
  ) = E'(boolean, m0)

   | E'(itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E' root = " ^ x_root ^ "\n\n")
   
   | E' _ = raise Fail("error in Semantics.E' - this should never occur")
   
fun M(  itree(inode("prog",_), 
                [ 
                    statement_list
                ] 
             ), 
        m
    ) = M( statement_list, m )
    
  | M(  itree(inode("statement_list",_), 
                [ 
                    statement,
                    statement_list
                ] 
             ), 
        m
    ) = M( statement_list, M(statement, m ) )
  
  | M(  itree(inode("statement_list",_), 
                [ 
                    epsilon
                ] 
             ), 
        m
    ) = M(epsilon, m ) 

    | M( itree(inode("statement",_),
                [
                    statement
                ]
            ),
        m
    ) = M( statement, m)

   | M( itree(inode("statement",_),
                [
                    statement,
                    itree(inode(";",_), [] )
                ]
            ),
        m
    ) = M( statement, m)

    | M( itree(inode("declaration",_),
                [
                    itree(inode("int",_), [] ),
                    id
                ]
            ),
        m0
    ) = updateEnv(getLeaf(id), INT, new(), m0)
    
    | M( itree(inode("declaration",_),
                [
                    itree(inode("boolean",_), [] ),
                    id
                ]
            ),
        m0
    ) = updateEnv(getLeaf(id), BOOL, new(), m0)

    | M( itree(inode("assignment",_),
                [
                    id,
                    itree(inode("=",_), [] ),
                    expression
                ]
            ),
        m0
    ) = let 
            val (v, m1) = E'(expression, m0)
            val loc = getLoc(accessEnv(getLeaf(id), m1))
            val m2 = updateStore(loc, Boolean v, m1)
        in
            m2
        end        

    | M( itree(inode("block",_),
                [
                    itree(inode("{",_), [] ),
                    statement_list,
                    itree(inode("}",_), [] )
                ]
            ),
        m
    ) = M( statement_list, m)     (* TODO: need to fix this *)

   | M( itree(inode("loop",_),
                [
                    loop
                ]
            ),
        m
    ) = M( loop, m)  

   | M( itree(inode("for_loop",_),
                [
                    itree(inode("for",_), [] ),
                    itree(inode("(",_), [] ),
                    assignment,
                    itree(inode(";",_), [] ),
                    expression,
                    itree(inode(";",_), [] ),
                    increment,
                    itree(inode(")",_), [] ),
                    block
                ]
            ),
        m0
    ) = m0
       

   | M( itree(inode("while_loop",_),
                [
                    itree(inode("while",_), [] ),
                    itree(inode("(",_), [] ),
                    expression,
                    itree(inode(")",_), [] ),
                    block
                ]
            ),
        m
    ) = M( block, m)    (* TODO: need to fix this *)

   | M( itree(inode("conditional",_),
                [
                    conditional
                ]
            ),
        m
    ) = M( conditional, m)

   | M( itree(inode("if_else_statement",_),
                [
                    itree(inode("if",_), [] ),
                    itree(inode("(",_), [] ),
                    expression,
                    itree(inode(")",_), [] ),
                    block1,
                    itree(inode("else",_), [] ),
                    block2
                ]
            ),
        m0
    ) = let 
          val (v, m1) = E'(expression, m0)
        in
            if v then M(block1, m1) 
            else M(block2, m1)
        end
    
  | M(  itree(inode("epsilon",_), 
                [ 
                    itree(inode("",_), [] )
                ] 
             ), 
        m
    ) = m

   | M( itree(inode("print_statement",_),
                [
                    itree(inode("print",_), [] ),
                    itree(inode("(",_), [] ),
                    expression,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) = m     (* TODO: need to fix this *)

    | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")
  


(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








