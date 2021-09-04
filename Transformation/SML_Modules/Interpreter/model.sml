(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and error) in your language. *)
datatype types = INT | BOOL | ERROR;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value =  Boolean of bool 
                          | Integer of int;

type loc   = int;
type env   = (string * types * loc) list;
type store = (loc * denotable_value) list;
type model = env * store;


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented.*)
val initialModel = ( [], []);

(* Error Handling *)

exception runtime_error;
exception model_error;
fun error msg = ( print msg; raise runtime_error );

(* accessEnv *)

fun accessEnv ( id1, (env, s) : model ) =
    let
        val msg = "Error: accessEnv " ^ id1 ^ " not found.";

        fun aux [] = error msg
          | aux ( (id, t, loc)::env ) =
                if id1 = id then (t, loc)
                else aux env;
        in
            aux env
        end;

(* updateEnv *)

fun new() = nil;

fun getListLength [] = 0
  | getListLength ( l::ls ) =
        1 + getListLength ( ls );

fun updateEnv ( id1, t1, _, (env, s) : model ) =
    let
        val msg = "Error: updateEnv " ^ id1 ^ " variable already exists.";

        fun aux [] = ( (id1, t1, getListLength ( env ))::env, s )
          | aux ( (id, t, loc)::env ) =
                if id1 = id then (env, s)
                else aux env;
    in
        aux env : model
    end;
    
(* accessStore *)

fun accessStore ( loc1 : loc, (env, s) : model ) =
    let
        val msg = "Error: accessEnv " ^ Int.toString(loc1) ^ " not found.";

        fun aux [] = error msg
          | aux ( (loc, v)::s ) =
                if loc1 = loc then v
                else aux s;
        in
            aux s
        end;
        
(* updateStore *)

fun updateStore ( loc1, v1, (env, s) : model ) =
    let 
        fun aux ( [], (loc1, v1) ) = [ (loc1, v1) ]
          | aux ( (loc, v)::a, (loc1, v1) ) =
                if loc1 = loc then (loc1, v1)::a 
                else (loc, v)::aux ( a, (loc1, v1) );
    in
        ( env, aux ( s, (loc1, v1 )) ) : model
    end;

(* getLoc *)
fun getLoc ( type1 : types, loc1 : loc ) = loc1;

(* getType *)
fun getType ( type1 : types, loc1 : loc ) = type1;

(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)