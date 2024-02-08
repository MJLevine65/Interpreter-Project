#use "./../../../classlib/OCaml/MyOCaml.ml";;

(*

Please implement the interp function following the
specifications described in CS320_Fall_2023_Project-2.pdf

Notes:
1. You are only allowed to use library functions defined in MyOCaml.ml
   or ones you implement yourself.
2. You may NOT use OCaml standard library functions directly.

*)

type const = 
| Int of int
| Bool of bool
| Unit of unit
| Sym of string

type expr =
  | Add | Mul | Sub | Div | And | Or | Not | Gt | Lt | Trace 
  |Pop | Push of const | Swap | If of expr list | Else of expr list | IfElse of (expr list) * (expr list) | End
  | Bind | Lookup | Fun of expr list | Call | Return 

type value = Closure of (string * var list * expr list) | Const of const

and var = Var of string * value

let rec whitespaces (cs: char list) : char list = 
   match cs with
   | [] -> []
   | c :: ct -> if char_iswhitespace c then whitespaces ct else cs

let rec next (cs: char list): string * char list = 
   match cs with 
   | [] -> ("", [])
   | c :: ct ->
      if char_isalphanum c then 
         match next ct with
         | (cc,ctt) -> ((string_cons c cc), (ctt))
      else ("",cs)

let rec get_pos(cs: char list)(i: int): (const * char list) option = 
   match cs with
   | [] -> Some(Int i, cs)
   | c:: ct -> 
      if char_isdigit c then get_pos ct (i*10 + (digit_of_char c))
      else Some(Int i,cs)

let get_neg(cs:char list): (const * char list) option = 
      match get_pos cs 0 with
      | Some(Int i,ct) -> Some(Int (-1*i),ct)
      | _ -> None

let get_sym(s: string): const option = 
   let s1 = string_head s in
   if (char_isdigit s1) then None else
   if string_forall s (fun c -> if ((char_islower c) || (char_isdigit c)) then true else false) then
      Some(Sym s) else None
      

let rec get_const(cs:char list): (const * char list) option =
   match cs with
   | [] -> None
   | c :: ct ->  
      if char_isdigit c then get_pos cs 0
      else if c = '-' then get_neg ct
      else match next cs with
      | ("True", css) -> Some(Bool true, css)
      | ("False", css) -> Some(Bool false, css)
      | ("Unit", css) -> Some(Unit (), css)
      | (pos_sym, css) -> match get_sym pos_sym with | Some(symbol) -> Some(symbol, css) | None -> None

let rec get_if (es: expr list): (expr list * expr list) option = 
   let rec loop(es: expr list) (if_exprs:expr list): (expr list * expr list) option = 
      match (list_reverse es) with
      | [] -> None
      | e :: ess -> 
         match e with
            | If []-> Some(if_exprs,ess)
            | _ -> loop (list_reverse ess) (e :: if_exprs)
      in loop es []

let rec get_elsefun (es: expr list): (expr list * expr list * expr) option = 
   let rec loop(es: expr list) (elsefun_exprs:expr list): (expr list * expr list *expr) option = 
      match (list_reverse es) with
      | [] -> None
      | e :: ess -> 
         match e with
            | Else []-> Some(elsefun_exprs, ess, Else [])
            | Fun [] -> Some(elsefun_exprs, ess, Fun [])
            | _ -> loop (list_reverse ess) (e :: elsefun_exprs)
      in loop es []
   

let rec end_expr(e: expr)(cs: char list): (expr list * char list) option = 
   match cs with
   | [] -> Some(e::[],[])
   | c :: ct ->
      match c with
      | ';' -> Some(e::[],ct)
      | _ -> None

let next_expr (cs: char list): (expr list * char list) option = 
   match next(whitespaces cs) with
   | ("Mul", css) -> end_expr Mul (whitespaces css) 
   | ("Add",css) -> end_expr Add (whitespaces css) 
   | ("Sub", css) -> end_expr Sub (whitespaces css) 
   | ("Div",css) -> end_expr Div (whitespaces css) 
   | ("And", css) -> end_expr And (whitespaces css) 
   | ("Or", css) -> end_expr Or (whitespaces css) 
   | ("Not",css) -> end_expr Not (whitespaces css) 
   | ("Gt", css) -> end_expr Gt (whitespaces css) 
   | ("Lt",css) -> end_expr Lt (whitespaces css) 
   | ("Trace",css) -> end_expr Trace (whitespaces css) 
   | ("Pop",css) -> end_expr Pop (whitespaces css) 
   | ("Push",css) -> (match get_const (whitespaces css) with 
                     | Some(con, csss) -> end_expr (Push con) (whitespaces csss) 
                     | None -> None)
   |("Swap",css) -> end_expr Swap (whitespaces css) 
   |("If",css) -> Some((If []) :: [], (whitespaces css))
   |("Else", css) -> Some((Else []) :: [], (whitespaces css))
   |("End", css) -> end_expr End (whitespaces css)
   |("Bind", css) -> end_expr Bind (whitespaces css)
   |("Lookup", css) -> end_expr Lookup (whitespaces css)
   |("Fun",css) -> Some((Fun []) ::[], (whitespaces css))
   |("Call",css) -> end_expr Call (whitespaces css)
   |("Return",css) -> end_expr Return (whitespaces css)
   | (_,css) -> None

let rec parse(es : expr list) (cs: char list): (expr list * char list) option = 
   match whitespaces(cs) with
   | [] ->  Some(es, [])
   | _ ->
      match next_expr cs with
      | Some((Else []):: [], css) -> 
         (match get_if  es with 
         | Some(if_exprs,prev_exprs) -> parse (list_append (list_append  prev_exprs ((If if_exprs) :: [] ) ) ((Else []) :: []) ) css
         | None -> None)
      | Some(End :: [], css) -> 
         (
         match get_elsefun es with 
            | None -> None
            | Some(else_exprs,prev_exprs, Else []) ->
               (match prev_exprs with 
               | (If if_exprs) :: prev_exprs2 -> parse  (list_append  prev_exprs2  ( (IfElse(if_exprs,else_exprs)) :: []) ) css 
               | _ -> None )
            | Some(fun_exprs,prev_exprs, Fun []) ->  parse  (list_append (list_reverse prev_exprs) ( (Fun fun_exprs) :: []) ) css 
            | _ -> None
                
         )
      | Some(new_expr, css) -> parse (list_append es new_expr) (css)
      | None -> None

let string_of_digit(n:int) : string = 
if n >= 0 then
match n with 0 -> "0"| 1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4"
|5 -> "5"| 6 -> "6" | 7 -> "7" | 8 -> "8" | 9 -> "9" | _ -> ""
else
   let i = 
   match (-1*n) with | 0 -> "0" |1 -> "1" | 2 -> "2" | 3 -> "3" | 4 -> "4"
   |5 -> "5"| 6 -> "6" | 7 -> "7" | 8 -> "8" | 9 -> "9" | x -> let () = print_int (x) in let () = print_endline ("") in "a" in 
   string_append "-" i
    
let rec int_to_string (n:int): string =
if  (n < 10) && (n> -10) then string_of_digit n 
else string_append ( int_to_string (n / 10)) (string_of_digit (n mod 10))

let rec process (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option =
      match es with
      [] -> Some(trace)
      | e :: et ->
         match e with
         | Add -> add stack trace vs et
         | Mul -> mul stack trace vs et
         | Sub -> sub stack trace vs et
         | Div -> div stack trace vs et
         | And -> and_func stack trace vs et
         | Or -> or_func stack trace vs et
         | Not -> not_func stack trace vs et 
         | Gt -> gt stack trace vs et
         | Lt -> lt stack trace vs et
         | Trace -> trace_fun stack trace vs et 
         | Pop -> pop stack trace vs et
         | (Push v) -> process (Const v :: stack) trace vs et
         | Swap -> swap stack trace vs et
         | IfElse(a1,a2)  -> ifelse stack trace vs et a1 a2
         | Bind -> bind stack trace vs et
         | Lookup -> lookup stack trace vs et
         | (Fun c) -> fun_fun stack trace vs et c
         | Call -> call_fun stack trace vs et
         | Return -> return_fun stack trace vs et
         | _ -> fail trace

and fail (trace: string list) : string list option = 
   process [] ("Panic" :: trace) [] []

and add (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Int i), Const(Int j) -> process ( Const(Int (i+j)) :: cont) trace vs es
         | _,_ -> fail trace)
      | _ -> fail trace

and mul (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option  = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Int i), Const(Int j) -> process ( Const(Int (i*j)) :: cont) trace vs es
         | _,_ -> fail trace)
      | _ -> fail trace

and sub (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option  = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Int i), Const(Int j) -> process ( Const(Int (i-j)) :: cont) trace vs es
         | _,_ -> fail trace)
      | _ -> fail trace

and div (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Int i), Const(Int j) -> ( match j with | 0 -> (fail trace) | _ ->  (process ( Const(Int (i/j)) :: cont) trace vs es ) )
         | _,_ -> fail trace)
      | _ -> fail trace


and and_func (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Bool b), Const(Bool b2) -> (match b, b2 with |true,true -> process (Const(Bool true) :: cont) trace vs es | _,_ -> process (Const(Bool false) :: cont) trace vs es )
         | _,_ -> fail trace)
      | _ -> fail trace

and or_func (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Bool b), Const(Bool b2) -> (match b, b2 with |false,false -> process (Const(Bool false) :: cont) trace vs es | _,_ -> process (Const(Bool true) :: cont) trace vs es )
         | _,_ -> fail trace)
      | _ -> fail trace
  

and not_func (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with 
   | [] -> fail trace
   | con :: cont -> 
      match con with
      |Const(Bool b) -> (match b with | true -> process (Const(Bool false) :: cont) trace vs es | false -> process (Const(Bool true) :: cont) trace vs es)
      | _ -> fail trace

and gt (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Int i), Const(Int j) ->  if i > j then process (Const(Bool true) :: cont) trace vs es 
            else  process (Const(Bool false) :: cont) trace vs es
         | _,_ -> fail trace)
      | _ -> fail trace

and lt (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
      | [] -> fail trace
      | con :: con2 :: cont ->
         ( match con,con2 with
         | Const(Int i), Const(Int j) ->  if i < j then process (Const(Bool true) :: cont) trace vs es 
            else  process (Const(Bool false) :: cont) trace vs es
         | _,_ -> fail trace)
      | _ -> fail trace

and trace_fun (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
   | [] -> fail trace
   | con :: cont -> 
      let str = 
      match con with 
      | Const(Bool true) -> "True"
      | Const(Bool false) -> "False"
      | Const(Unit ()) -> "Unit"
      | Const(Sym s) -> s
      | Const(Int i) -> int_to_string i
      | Closure(s,vars,fun_exprs) -> (string_append (string_append "Fun<" s) ">")
      in
      process (Const(Unit ()) :: cont) (str :: trace) vs es

and pop (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
   | con :: cont -> process cont trace vs es
   | [] -> fail trace

and swap (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
   | con :: con2 :: cont -> process (con2 :: con :: cont) trace vs es
   | _ -> fail trace

and ifelse (stack: value list) (trace: string list) (vs:var list) (es: expr list) (if_block: expr list) (else_block: expr list): string list option = 
   match stack with 
   | Const(Bool b) :: cont -> 
      (match b with
         | true -> process cont trace vs (list_append if_block es)
         | false -> process cont trace vs (list_append else_block es) )
   | _ -> fail trace

and bind (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option = 
   match stack with
   | Const(Sym s) :: Const con :: cont -> process cont trace ((Var(s, Const con)) :: vs) es
   | Const(Sym s) :: Closure con:: cont -> process cont trace ((Var(s, Closure con)) :: vs) es
   | _ -> fail trace

and lookup (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option =
   let rec loop (s: string) (vs: var list): value option =
      match vs with
         | [] -> None
         | Var(s2,con) :: vss -> 
            if s = s2 then Some(con) else loop s vss
   in
   match stack with 
      | Const(Sym s) :: cont -> 
         (match loop s vs with
            | None -> fail trace | Some(con) -> process (con :: cont) trace vs es)
      | _ -> fail trace

and fun_fun (stack: value list) (trace: string list) (vs: var list) (es: expr list) (fun_es:expr list): string list option =
   match stack with
   | Const(Sym s) :: cont -> process (Closure(s,vs,fun_es) :: cont) trace vs es
   | _ -> fail trace

and call_fun (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option =
   match stack with
      | Closure(fun_name,fun_vars,fun_exprs)  :: a :: cont -> 
         process (a :: Closure("cc",vs,es) :: cont) trace (Var(fun_name,Closure(fun_name,fun_vars,fun_exprs)) :: fun_vars) fun_exprs
      | _ -> fail trace

and return_fun (stack: value list) (trace: string list) (vs:var list) (es: expr list): string list option =
   match stack with
      | Closure(fun_name,fun_vars,fun_exprs) :: a :: cont -> process (a::cont) trace fun_vars fun_exprs
      | _ -> fail trace
      
let interp (s : string) : string list option = 
  match parse [] (string_listize s) with 
  | None -> None
  | Some(es,_) -> process [] [] [] es

let interp_exprs (s : string) : expr list option = 
  match parse [] (string_listize s) with 
  | None -> None
  | Some(es,_) ->  Some(es)


