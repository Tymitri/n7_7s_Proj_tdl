(* Module de la passe de génération de code *)
(* doit être conforme à l'interface Passe *)

open Ast
open Type
open Tds
open Tam
open Code

type t1 = AstPlacement.programme
type t2 = string


(* analyse_code_affectable : AstPlacement.affectable -> String *)
(* Paramètre a : l'affectable à analyser *)
(* Transforme l'affectable en une expression de type String *)
let rec analyse_code_affectable a = 
  match a with
  | AstType.Ident info -> 
    begin
      match info_ast_to_info info with
      | InfoVar(_, t, depl, reg) -> load (getTaille t) depl reg 
      | _ -> failwith "Internal Error"
    end
  | AstType.Valeur v -> failwith "TODO"
  


(* analyse_code_expression : AstPlacement.expression -> String *)
(* Paramètre e : l'expression à analyser *)
(* Transforme l'expression en une expression de type String *)
let rec analyse_code_expression e =
  match e with
  | AstType.AppelFonction (info, lc) ->
    let c = String.concat " " (List.map analyse_code_expression lc) in
    (match (info_ast_to_info info) with
    | InfoFun(f, _, _) -> c^call "ST" f
    | _ -> failwith "InternalError")
  | AstType.Affectable a -> failwith "TODO"
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
  | AstType.Null -> loadl_int 0     (* TODO : vérifier *)
  | AstType.New t -> loadl_int (getTaille t) ^ subr "Malloc"     (* TODO : vérifier *)
  | AstType.Adress info ->        
    begin
      match info_ast_to_info info with
      | InfoVar(_, _, depl, reg) -> loada depl reg                             (* TODO : vérifier *)
      | _ -> failwith "Internal Error"
    end


    

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
  | AstPlacement.Affectation (a,e) ->
    begin
      let na = analyse_code_affectable a in
      let ne = analyse_code_expression e in
      ne^na                                   (* TODO : vérifier faut-il un STOREI ??? *)                     
      (* (match (info_ast_to_info info) with
      | InfoVar(_, t, depl, reg) -> 
        ((load (getTaille t) depl reg)^(let ne = analyse_code_expression e in
        ne)^(store (getTaille t) depl reg))
      | _ -> failwith "Internal Error") *)
    end
  | AstPlacement.AffichageInt e ->
    let ne = analyse_code_expression e in (ne^(subr "Iout"))
  | AstPlacement.AffichageRat e ->
    let ne =analyse_code_expression e in (ne^(call "ST" "Rout"))
  | AstPlacement.AffichageBool e ->
    let ne = analyse_code_expression e in (ne^(subr "Bout"))
  | AstPlacement.Conditionnelle (e,b1,b2) ->
    let ne = analyse_code_expression e in
    let nb1 = analyse_code_bloc b1 in
    let nb2 = analyse_code_bloc b2 in
    let b2label = "If_Bloc2_" ^ getEtiquette () in 
    let endiflabel = "If_End_" ^ getEtiquette () in 
    (ne 
      ^ jumpif 0 b2label 
      ^ nb1 
      ^ jump endiflabel 
      ^ label b2label 
      ^ nb2 
      ^ label endiflabel)
  | AstPlacement.TantQue (e,b) ->
    let ne = analyse_code_expression e in
    let while1 = "While_Start_" ^ getEtiquette() in
    let endwhile = "While_End_" ^ getEtiquette() in   
    let nb = analyse_code_bloc b  in
    (label while1 
      ^ ne
      ^ jumpif 0 endwhile 
      ^ nb
      ^ (jump while1)
      ^ label endwhile)
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
and analyse_code_bloc (li,t) = String.concat " " (List.map analyse_code_instruction li) ^ (pop 0 t)


(* analyse_code_fonction : AstPlacement.fonction -> String *)
(* Paramètre : la fonction à analyser *)
(* Transforme la fonction en un String *)
let analyse_code_fonction (AstPlacement.Fonction (info, _, bloc)) =
  match (info_ast_to_info info) with
  | InfoFun(n, _, _) ->
    let nb = analyse_code_bloc bloc in
    label n ^ nb ^ halt ^ "\n"
  | _ -> failwith "Internal Error"
  


(* analyser : AstPlacement.programme -> Astcode.Programme *)
(* Paramètre : le programme à analyser *)
(* Transforme le programme en une expression de type String *)
let analyser (AstPlacement.Programme (fonctions,prog)) =
  let nf = String.concat " " (List.map analyse_code_fonction fonctions) in
  let nb = analyse_code_bloc prog in
  (getEntete () ^ nf ^ label "main" ^ nb ^ halt)
