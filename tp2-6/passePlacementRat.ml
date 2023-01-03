(* Module de la passe de placement mémoire *)
(* doit être conforme à l'interface Passe *)

open Ast
open Type
open Tds

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme

let getTailleList liste = List.fold_right (fun r e -> getTaille r + e) liste 0

(* analyse_placement_affectable : AstType.affectable -> AstPlacement.affectable *)
(* Paramètre a : l'affectable à analyser *)
(* Vérifie le bon placement mémoire et transforme l'affectable
en une expression de type AstPlacement.affectable *)
(* Erreur si mauvais placement mémoire *)
let analyse_placement_affectable a = a

(* analyse_placement_expression : AstType.expression -> AstPlacement.expression *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie le bon placement mémoire et tranforme l'expression
en une expression de type AstPlacement.expression *)
(* Erreur si mauvais placement mémoire *)
let analyse_placement_expression e = e


(* analyse_placement_instruction : AstType.instruction*int*string -> AstPlacement.instruction*int *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre depl : Déplacement *)
(* Paramètre reg : Registre *)
(* Vérifie le bon placement mémoire  et transforme l'instruction
en une instruction de type AstPlacement.instruction *)
(* Erreur si mauvais placement mémoire *)
let rec analyse_placement_instruction (i, depl, reg) =
  match i with
  | AstType.Declaration (info, e) ->
    begin
      (match (info_ast_to_info info) with
      | InfoVar(_, t, _, _) -> 
        (modifier_adresse_variable depl reg info;
        (AstPlacement.Declaration(info, e), getTaille t))
      | _ -> failwith "Internal Error")
    end
  | AstType.Affectation (a,e) ->
    (AstPlacement.Affectation(a, e), 0)
  | AstType.AffichageInt e ->
    (AstPlacement.AffichageInt e, 0)
  | AstType.AffichageRat e ->
    (AstPlacement.AffichageRat e, 0)
  | AstType.AffichageBool e ->
    (AstPlacement.AffichageBool e, 0)
  | AstType.Conditionnelle (e,b1,b2) ->
    let nb1 = analyse_placement_bloc b1 depl reg in
    let nb2 = analyse_placement_bloc b2 depl reg in
    (AstPlacement.Conditionnelle(e, nb1, nb2), 0)
  | AstType.TantQue (e,b) ->
    let nb = analyse_placement_bloc b depl reg in
    (AstPlacement.TantQue (e, nb), 0)
  | AstType.Retour (e, info) ->
      begin
        (match (info_ast_to_info info) with
        | InfoFun(_,typ,lp) -> 
          (AstPlacement.Retour (e, getTaille typ, getTailleList lp), 0)
        | _ -> failwith "Internal Error")
      end
  | AstType.Empty -> AstPlacement.Empty, 0


(* analyse_placement_bloc : AstType.bloc*Int*String -> AstPlacementBloc*Int *)
(* Vérifie le bon placement mémoire et tranforme le bloc en un bloc de type AstPlacement.bloc *)
(* Erreur si mauvais placement mémoire *)
and analyse_placement_bloc li depl reg =
  match li with
  | [] -> ([], 0)
  | i::li2 -> 
    let (ni, taille) = analyse_placement_instruction (i, depl, reg) in 
    let (nli, tli) = analyse_placement_bloc li2 (depl + taille) reg in
    (ni::nli , taille + tli)


(* analyse_placement_fonction : AstType.fonction -> AstPlacement.fonction*)
(* Paramètre : la fonction à analyser *)
(* Vérifie le bon placement mémoire et tranforme la fonction
en une fonction de type AstPlacement.fonction *)
(* Erreur si mauvais placement mémoire *)
let analyse_placement_fonction (AstType.Fonction (info, linfo, bloc)) =
  let rec modifier_adresse_variable_param li depl =
    match li with
    | [] -> ();
    | t::q -> 
      match (info_ast_to_info t) with
      | InfoVar(_,typ,_,_) -> 
        modifier_adresse_variable (depl-(getTaille typ)) "LB" t;
        modifier_adresse_variable_param q (depl-(getTaille typ));
      | _ -> failwith "Internal error"
  in

  let (nb,tb) = analyse_placement_bloc bloc 3 "LB" in
  modifier_adresse_variable_param (List.rev linfo) 0;

  AstPlacement.Fonction(info, linfo, (nb, tb))


  
  



(* analyser : AstType.programme -> AstPlacement.Programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie le bon placement mémoire et tranforme le programme
en un programme de type AstPlacement.programme *)
(* Erreur si mauvais placement mémoire *)
let analyser (AstType.Programme (fonctions,prog)) =
  let nf = List.map analyse_placement_fonction fonctions in
  let nb = analyse_placement_bloc prog 0 "SB" in
  AstPlacement.Programme (nf,nb)
