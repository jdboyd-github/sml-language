(* =========================================================================================================== *)
structure TypeChecker =
struct

open Model;
open CONCRETE_REPRESENTATION;

(* =========================================================================================================== *)
(*
    Here is where your typeCheck and typeOf definitions go. The primary challenge here is to translate the parse 
    expression notation we used in M2 to the actual SML tree patterns used in the TL System. See the comments in
    the semantics.sml file for a more detailed discussion on this topic. 
*)

fun typeOf( itree(inode("expr",_), [ or_expr1 ] ), m ) = typeOf( or_expr1, m )

    | typeOf( itree(inode("or_expr",_), [ and_expr1 ] ), m) = typeOf( and_expr1, m )

    | typeOf( itree(inode("or_expr",_), 
            [ 
                or_expr1,
                itree(inode("||",_),[]),
                and_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( or_expr1, m )
                val t2 = typeOf ( and_expr1, m )
            in
                if t1 = t2 andalso t1 = BOOL then BOOL
                else ERROR
            end

    | typeOf( itree(inode("and_expr",_), [ equality_expr1 ] ), m) = typeOf( equality_expr1, m )

    | typeOf( itree(inode("and_expr",_), 
            [ 
                and_expr1,
                itree(inode("&&",_),[]),
                equality_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( and_expr1, m )
                val t2 = typeOf ( equality_expr1, m )
            in
                if t1 = t2 andalso t1 = BOOL then BOOL
                else ERROR
            end

    | typeOf( itree(inode("equality_expr",_), [ relational_expr1 ] ), m) = typeOf( relational_expr1, m )
    
    | typeOf( itree(inode("equality_expr",_), 
            [ 
                equality_expr1,
                itree(inode("==",_),[]),
                relational_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( equality_expr1, m )
		val t2 = typeOf ( relational_expr1, m )
            in
		if t1 = t2 andalso ( t1 = INT orelse t1 = BOOL ) then BOOL
		else ERROR
            end
    
    | typeOf( itree(inode("equality_expr",_), 
            [ 
                equality_expr1,
                itree(inode("!=",_),[]),
                relational_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( equality_expr1, m )
		val t2 = typeOf ( relational_expr1, m )
            in
		if t1 = t2 andalso ( t1 = INT orelse t1 = BOOL ) then BOOL
		else ERROR
            end
            
    | typeOf( itree(inode("relational_expr",_), [ additive_expr1 ] ), m) = typeOf( additive_expr1, m )
    
    | typeOf( itree(inode("relational_expr",_), 
            [ 
                relational_expr1,
                itree(inode(">",_),[]),
                additive_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( relational_expr1, m )
                val t2 = typeOf ( additive_expr1, m )
            in
		if t1 = t2 andalso t1 = INT then BOOL
		else ERROR
            end
            
    | typeOf( itree(inode("relational_expr",_), 
            [ 
                relational_expr1,
                itree(inode("<",_),[]),
                additive_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( relational_expr1, m )
                val t2 = typeOf ( additive_expr1, m )
            in
		if t1 = t2 andalso t1 = INT then BOOL
		else ERROR
            end
            
    | typeOf( itree(inode("additive_expr",_), [ multiplicative_expr1 ] ), m) = typeOf( multiplicative_expr1, m )
    
    | typeOf( itree(inode("additive_expr",_), 
            [ 
                additive_expr1,
                itree(inode("+",_),[]),
                multiplicative_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( additive_expr1, m )
		val t2 = typeOf ( multiplicative_expr1, m )
            in
                if t1 = t2 andalso t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("additive_expr",_), 
            [ 
                additive_expr1,
                itree(inode("-",_),[]),
                multiplicative_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( additive_expr1, m )
		val t2 = typeOf ( multiplicative_expr1, m )
            in
                if t1 = t2 andalso t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("multiplicative_expr",_), [ unary_expr1 ] ), m) = typeOf( unary_expr1, m )
    
    | typeOf( itree(inode("multiplicative_expr",_), 
            [ 
                multiplicative_expr1,
                itree(inode("*",_),[]),
                unary_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( multiplicative_expr1, m )
		val t2 = typeOf ( unary_expr1, m )
            in
		if t1 = t2 andalso t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("multiplicative_expr",_), 
            [ 
                multiplicative_expr1,
                itree(inode("/",_),[]),
                unary_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( multiplicative_expr1, m )
		val t2 = typeOf ( unary_expr1, m )
            in
		if t1 = t2 andalso t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("multiplicative_expr",_), 
            [ 
                multiplicative_expr1,
                itree(inode("%",_),[]),
                unary_expr1

            ] 
        ), m ) = 
            let
                val t1 = typeOf ( multiplicative_expr1, m )
		val t2 = typeOf ( unary_expr1, m )
            in
		if t1 = t2 andalso t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("unary_expr",_), [ exponential_expr1 ] ), m) = typeOf( exponential_expr1, m )
    
    | typeOf( itree(inode("unary_expr",_), 
            [ 
                itree(inode("-",_),[]),
                unary_expr1
            ] 
        ), m ) = 
            let
                val t1 = typeOf ( unary_expr1, m )
            in
		if t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("unary_expr",_), 
            [ 
                itree(inode("!",_),[]),
                unary_expr1
            ] 
        ), m ) = 
            let
                val t1 = typeOf ( unary_expr1, m )
            in
		if t1 = BOOL then BOOL
		else ERROR
            end
            
    | typeOf( itree(inode("exponential_expr",_), [ base1 ] ), m) = typeOf( base1, m )
    
    | typeOf( itree(inode("exponential_expr",_), 
            [ 
                base1,
                itree(inode("^",_),[]),
                exponential_expr1
            ] 
        ), m ) = 
            let
                val t1 = typeOf ( base1, m )
		val t2 = typeOf ( exponential_expr1, m )
            in
		if t1 = t2 andalso t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("base",_), [ decorated_id1 ] ), m) = typeOf( decorated_id1, m )
    
    | typeOf( itree(inode("decorated_id",_), 
            [ 
                id1,
                itree(inode("++",_),[])
            ] 
        ), m ) = 
            let
                val t1 = getType(accessEnv(getLeaf( id1 ), m))
            in
                if t1 = INT then INT
                else ERROR
            end
            
    | typeOf( itree(inode("decorated_id",_), 
            [ 
                id1,
                itree(inode("--",_),[])
            ] 
        ), m ) = 
            let
                val t1 = getType(accessEnv(getLeaf( id1 ), m))
            in
                if t1 = INT then INT
                else ERROR
            end
            
    | typeOf( itree(inode("decorated_id",_), 
            [ 
                itree(inode("++",_),[]),
                id1
            ] 
        ), m ) = 
            let
                val t1 = getType(accessEnv(getLeaf( id1 ), m))
            in
                if t1 = INT then INT
                else ERROR
            end
            
    | typeOf( itree(inode("decorated_id",_), 
            [ 
                itree(inode("--",_),[]),
                id1
            ] 
        ), m ) = 
            let
                val t1 = getType(accessEnv(getLeaf( id1 ), m))
            in
                if t1 = INT then INT
                else ERROR
            end
    
    | typeOf( itree(inode("base",_), [ itree(inode("(",_),[]), expr1, itree(inode(")",_),[]) ] ), m ) = 
            typeOf( expr1, m )
            
    | typeOf( itree(inode("base",_), 
            [ 
                itree(inode("abs",_),[]),
                itree(inode("(",_),[]),
                expr1,
                itree(inode(")",_),[])
            ] 
        ), m ) = 
            let
                val t1 = typeOf ( expr1, m )
            in
		if t1 = INT then INT
		else ERROR
            end
            
    | typeOf( itree(inode("value",_), [ integer ] ), m) = INT
    
   (* | typeOf( itree(inode("value",_), [ bool ] ), m) = BOOL *)
            
    | typeOf( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeOf root = " ^ x_root ^ "\n\n")
    | typeOf _ = raise Fail("Error in Model.typeCheck - this should never occur")

fun typeCheck( itree(inode("prog",_), [ statement_list1 ] ), m) = typeCheck( statement_list1, m )
  
  | typeCheck( itree(inode("statement_list",_), [ statement1, statement_list1 ]), m0 ) =
        let
            val m1 = typeCheck( statement1, m0 )
            val m2 = typeCheck( statement_list1, m1 )
        in
            m2
        end
        
  | typeCheck( itree(inode("statement_list",_), [ epsilon ]), m ) = m
  
  | typeCheck( itree(inode("statement",_), [ statement1, itree(inode(";",_), [] ) ]), m ) = 
        typeCheck( statement1, m )
        
  | typeCheck( itree(inode("declaration",_), [ itree(inode("int",_),[]), id1 ]), m ) = 
        updateEnv( getLeaf( id1 ), INT, new(), m)
        
  | typeCheck( itree(inode("declaration",_), [ itree(inode("bool",_),[]), id1 ]), m ) = 
        updateEnv( getLeaf( id1 ), BOOL, new(), m)
        
  | typeCheck( itree(inode("assignment",_), [ id1, itree(inode("=",_),[]), expr1 ] ), m ) = 
        let
            val t1 = typeOf( expr1, m )
            val t2 = getType(accessEnv( getLeaf( id1 ), m ))
        in
            if t1 = t2 then m else raise model_error
	end
        
  | typeCheck( itree(inode("increment",_), [ increment1, itree(inode(";",_), [] ) ]), m ) = 
        typeCheck( increment1, m )
        
  | typeCheck( itree(inode("pre_increment",_), [ itree(inode("++",_),[]), id1 ] ), m ) = 
        let
            val t1 = getType(accessEnv( getLeaf( id1 ), m ))
	in
            if t1 = INT then m else raise model_error
	end
        
  | typeCheck( itree(inode("post_increment",_), [ id1, itree(inode("++",_),[]) ] ), m ) = 
        let
            val t1 = getType(accessEnv( getLeaf( id1 ), m ))
	in
            if t1 = INT then m else raise model_error
	end
        
  | typeCheck( itree(inode("pre_decrement",_), [ itree(inode("--",_),[]), id1 ] ), m ) = 
        let
            val t1 = getType(accessEnv( getLeaf( id1 ), m ))
	in
            if t1 = INT then m else raise model_error
	end
        
  | typeCheck( itree(inode("post_decrement",_), [ id1, itree(inode("--",_),[]) ] ), m ) = 
        let
            val t1 = getType(accessEnv( getLeaf( id1 ), m ))
	in
            if t1 = INT then m else raise model_error
	end
        
  | typeCheck( itree(inode("if_statement",_), 
        [ 
            itree(inode("if",_),[]),
            itree(inode("(",_),[]),
            expr1,
            itree(inode(")",_),[]),
            block1
        ]
    ), m0 ) = 
        let
            val t = typeOf( expr1, m0 )
            val m1 = typeCheck( block1, m0 )
	in
            if t = BOOL then m0 else raise model_error
        end
        
    | typeCheck( itree(inode("if_else_statement",_), 
        [ 
            itree(inode("if",_),[]),
            itree(inode("(",_),[]),
            expr1,
            itree(inode(")",_),[]),
            block1,
            itree(inode("else",_),[]),
            block2
        ]
    ), m0 ) = 
        let
            val t = typeOf( expr1, m0 )
            val m1 = typeCheck( block1, m0 )
            val m2 = typeCheck( block2, m0 )
        in
            if t = BOOL then m0 else raise model_error
        end
        
  | typeCheck( itree(inode("loop",_), [ loop1 ]), m ) = 
        typeCheck( loop1, m )
        
  | typeCheck( itree(inode("while_loop",_), 
        [ 
            itree(inode("while",_),[]),
            itree(inode("(",_),[]),
            expr1,
            itree(inode(")",_),[]),
            block1
        ]
    ), m0 ) = 
        let
            val t = typeOf( expr1, m0 )
            val m1 = typeCheck( block1, m0 )
	in
            if t = BOOL then m0 else raise model_error
	end
        
  | typeCheck( itree(inode("for_loop",_), 
        [ 
            itree(inode("for",_),[]),
            itree(inode("(",_),[]),
            assignment1,
            itree(inode(";",_),[]),
            expr1,
            itree(inode(";",_),[]),
            increment1,
            itree(inode(")",_),[]),
            block1
        ]
    ), m0 ) = 
        let
            val m1 = typeCheck( assignment1, m0 )
            val t = typeOf( expr1, m0 )
            val m2 = typeCheck( increment1, m0 )
            val m3 = typeCheck( block1, m0 )
	in
            if t = BOOL then m0 else raise model_error
        end
        
  | typeCheck( itree(inode("block",_), [ itree(inode("{",_),[]), statement_list1, itree(inode("}",_),[]) ] ), m) = 
        typeCheck( statement_list1, m )
        
  | typeCheck( itree(inode("print_statement",_), 
        [ 
            itree(inode("print",_),[]),
            itree(inode("(",_),[]),
            expr1,
            itree(inode(")",_),[])
        ]
    ), m ) = 
        let
            val t = typeOf ( expr1, m )
	in
            if t = ERROR then raise model_error else m
        end
  
  | typeCheck( itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn typeCheck root = " ^ x_root ^ "\n\n")
  | typeCheck _ = raise Fail("Error in Model.typeCheck - this should never occur")

(* =========================================================================================================== *)  
end (* struct *)
(* =========================================================================================================== *)








