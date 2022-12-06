(* Module de la passe de génération de code *)
(* doit être conforme à l'interface Passe *)

open Ast
open Type
open Tds
open Tam

type t1 = AstPlacement.programme
type t2 = String


(* analyse_code_expression : AstPlacement.expression -> String *)
(* Paramètre e : l'expression à analyser *)
(* Tranforme l'expression en une expression de type String *)
let rec analyse_code_expression e =
  match e with
  | AstType.AppelFonction (info, lc) ->
    let c = String.concat " " (List.map analyse_code_expression lc) in
    (match (info_ast_to_info info) with
    | InfoFun(f, _, _) -> c^call "ST" f
    | _ -> failwith "InternalError")
  | AstType.Ident info -> 
    (match (info_ast_to_info info) with
    | InfoVar (_, t, depl, reg) -> load (getTaille t) depl reg 
    | _ -> failwith "InternalError")
  | AstType.Booleen b ->
    if b then loadl_int 1 else loadl_int 0
  | AstType.Entier i -> loadl_int i
  | AstType.Unaire (op, e1) ->
    let c = analyse_code_expression e1 in
    (match op with
    | AstType.Numerateur -> c ^ pop 0 1 
    | AstType.Denominateur -> c ^ pop 1 1)
  | AstType.Binaire (op, e1, e2) -> 
    let c1 = analyse_code_expression e1 in
    let c2 = analyse_code_expression e2 in
    (match op with
    | AstType.Fraction -> c1 ^ c2 ^ call "ST" "norm"
    | AstType.PlusInt -> c1 ^ c2 ^ subr "IAdd"
    | AstType.PlusRat -> c1 ^ c2 ^ call "ST" "Radd"
    | AstType.MultInt -> c1 ^ c2 ^ subr "IMul"
    | AstType.MultRat -> c1 ^ c2 ^ call "ST" "Rmul"
    | AstType.EquInt -> c1 ^ c2 ^ subr "IEq"
    | AstType.EquBool -> c1 ^ subr "B2I" ^ c2 ^ subr "B2I" ^ subr "IEq" 
    | AstType.Inf -> c1 ^ c2 ^ subr "ILss") (* VERIFIER *)
    
    

(* analyse_code_instruction : AstPlacement.instruction -> String *)
(* Paramètre i : l'instruction à analyser *)
(* Transforme l'instruction en un String *)
let rec analyse_code_instruction i =
  match i with
  | AstPlacement.Declaration (info, e) ->
    begin
      (match (info_ast_to_info info) with
      | InfoVar(_, t, depl, reg) -> 
        ((push (getTaille t))^(let ne = analyse_code_expression e in
        ne)^(store (getTaille t) depl reg))
      | _ -> failwith "Internal Error")
    end
  | AstPlacement.Affectation (info,e) ->
    begin
      (match (info_ast_to_info info) with
      | InfoVar(_, t, depl, reg) -> 
        ((load (getTaille t) depl reg)^(let ne = analyse_code_expression e in
        ne)^(store (getTaille t) depl reg))
      | _ -> failwith "Internal Error")
    end
  | AstPlacement.AffichageInt e ->
    let ne = analyse_code_expression e in (ne^(subr "Iout"))
  | AstPlacement.AffichageRat e ->
    let ne =analyse_code_expression e in (ne^(call "" "Rout"))
  | AstPlacement.AffichageBool e ->
    let ne = analyse_code_expression e in (ne^(subr "Bout"))
  | AstPlacement.Conditionnelle (e,b1,b2) ->
    let ne = analyse_code_expression e in
    let nb1 = analyse_code_bloc b1 in
    let nb2 = analyse_code_bloc b2 in
    (ne ^ jumpif 0 "b2" ^ nb1 ^ jump "fin" ^ label "b2" ^ nb2 ^ label "fin")
  | AstPlacement.TantQue (e,b) ->
    let ne = analyse_code_expression e in
    let while1 = label "while1" in
    let endwhile = label "endwhile" in   
    let nb = analyse_code_bloc b  in
    (while1^ne^(jumpif 0 endwhile)^nb^(jump while1)^endwhile)
  | AstPlacement.Retour (e, tailleRet, tailleParam) ->
      begin
        let ne = analyse_code_expression e in
        (ne^(return tailleRet tailleParam))
      end
  | AstPlacement.Empty -> ""


(* analyse_code_bloc : AstPlacement.bloc*Int -> String *)
(* Paramètre li : la liste d'instruction à analyser *)
(* Paramètre taille : la taille du bloc *)
(* Transforme le bloc en un String *)
and analyse_code_bloc (li,_) = String.concat " " (List.map analyse_code_instruction li)


(* analyse_code_fonction : AstPlacement.fonction -> String *)
(* Paramètre : la fonction à analyser *)
(* Transforme la fonction en un String *)
let analyse_code_fonction (AstPlacement.Fonction (info, linfo, bloc)) = failwith "to do"




(* analyser : AstPlacement.programme -> Astcode.Programme *)
(* Paramètre : le programme à analyser *)
(* Transforme le programme en une expression de type String *)
let analyser (AstPlacement.Programme (fonctions,prog)) =
  let nf = String.concat " " (List.map analyse_code_fonction fonctions) in
  let nb = analyse_code_bloc prog in
  (nf ^ nb)
