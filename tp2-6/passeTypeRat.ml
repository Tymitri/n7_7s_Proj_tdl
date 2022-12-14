(* Module de la passe de typage *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme

let getType info =
  match (info_ast_to_info info) with 
  | InfoVar(_, typ, _, _) -> typ
  | _ -> failwith "Internal error"


(* analyse_type_affectable : AstTds.affectable -> AstType.affectable * type *)
(* Paramètre a : l'affectable à analyser *)
(* Vérifie le bon typage et tranforme l'affectable en (AstType.affectable * typ) *)
(* Erreur si mauvais typage *)
let rec analyse_type_affectable a = 
  match a with
  | AstTds.Ident info -> 
    begin
      match info_ast_to_info info with
      | InfoVar (_, t,_,_) -> (AstType.Ident info, t)
      | InfoConst _ -> (AstType.Ident info, Int)
      | _ -> failwith ("Internal Eror : symbol not found")
    end
  | AstTds.Valeur a -> 
    begin
      match analyse_type_affectable a with
      | (na, Pointeur t) -> (AstType.Valeur na, t)
      | _ -> raise NotAPointer
    end  
  

(* analyse_type_expression : AstTds.expression -> AstType.expression * type *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie le bon typage et tranforme l'expression
en une expression de type AstType.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_expression e = 
  match e with
  (* Appel de fonction représenté par le nom de la fonction et la liste des paramètres réels *)
  | AstTds.AppelFonction (info, el) ->
    (match (info_ast_to_info info) with 
    | InfoFun(_, typ, typList) -> 
      let (listInstr, typList2) = List.split (List.map analyse_type_expression el) in
      if (Type.est_compatible_list typList typList2) 
      then (AstType.AppelFonction(info, listInstr), typ)
      else raise (TypesParametresInattendus (typList, typList2)) 
    | _ -> failwith "Internal Error")
  (* Accès à un identifiant représenté par son nom *)
  | AstTds.Affectable a -> 
    let (na, t) = analyse_type_affectable a in 
    (AstType.Affectable na, t)
  (* Booléen *)
  | AstTds.Booleen b -> (AstType.Booleen b, Type.Bool)
  (* Entier *)
  | AstTds.Entier e -> (AstType.Entier e, Type.Int)
  (* Opération unaire représentée par l'opérateur et l'opérande *)
  | AstTds.Unaire (op, e1) -> 
    let (ne1, te1) = analyse_type_expression e1 in 
      (match (op, te1) with
      | (AstSyntax.Numerateur, Type.Rat) -> (AstType.Unaire(AstType.Numerateur, ne1), Type.Int)
      | (AstSyntax.Denominateur, Type.Rat) -> (AstType.Unaire(AstType.Denominateur, ne1), Type.Int)
      | _ -> raise (TypeInattendu(te1, Type.Rat)))
  (* Opération binaire représentée par l'opérateur, l'opérande gauche et l'opérande droite *)
  | AstTds.Binaire (op, e1, e2) -> 
    let (ne1, te1) = analyse_type_expression e1 in
    let (ne2, te2) = analyse_type_expression e2 in
    (match (op, te1, te2) with
    | (AstSyntax.Plus, Type.Int, Type.Int ) -> AstType.Binaire(AstType.PlusInt, ne1, ne2), Type.Int
    | (AstSyntax.Plus, Type.Rat, Type.Rat ) -> AstType.Binaire(AstType.PlusRat, ne1, ne2), Type.Rat
    | (AstSyntax.Mult, Type.Int, Type.Int ) -> AstType.Binaire(AstType.MultInt, ne1, ne2), Type.Int
    | (AstSyntax.Mult, Type.Rat, Type.Rat ) -> AstType.Binaire(AstType.MultRat, ne1, ne2), Type.Rat
    | (AstSyntax.Equ, Type.Int, Type.Int ) -> AstType.Binaire(AstType.EquInt, ne1, ne2), Type.Bool
    | (AstSyntax.Equ, Type.Bool, Type.Bool ) -> AstType.Binaire(AstType.EquBool, ne1, ne2), Type.Bool
    | (AstSyntax.Inf, Type.Int, Type.Int ) -> AstType.Binaire(AstType.Inf, ne1, ne2), Type.Bool
    | (AstSyntax.Fraction, Type.Int, Type.Int ) -> AstType.Binaire(AstType.Fraction, ne1, ne2), Type.Rat
    | _ -> raise (TypeBinaireInattendu (op, te1, te2)))
  | AstTds.Null -> Null, Pointeur Undefined
  | AstTds.New t -> New t, Pointeur t
  | AstTds.Adress info -> 
    begin
      match info_ast_to_info info with
      | InfoVar _ -> (AstType.Adress info, Pointeur (getType info))
      | _ -> failwith ("Internal Error")
    end
  | AstTds.Ternaire (e1, e2, e3) -> 
    let (ne1, te1) = analyse_type_expression e1 in
    let (ne2, te2) = analyse_type_expression e2 in
    let (ne3, te3) = analyse_type_expression e3 in
    if te1 = Type.Bool 
    then 
      if (te2 = te3) then (AstType.Ternaire (ne1, ne2, ne3), te2)
      else raise (TypeInattendu (te2, te3))
    else raise (TypeInattendu (te1, Bool))


(* analyse_type_instruction : AstTds.instruction -> AstType.instruction *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie le bon typage et transforme l'instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvais typage *)
let rec analyse_type_instruction i =
  match i with
  | AstTds.Affectation (a,e) ->
      begin
        let (na, ta) = analyse_type_affectable a in
        let (ne,te) = analyse_type_expression e in
          if Type.est_compatible ta te 
          then AstType.Affectation (na, ne) 
          else raise (TypeInattendu (te, ta)) 
      end
  | AstTds.Affichage e ->
      let (x, t) = analyse_type_expression e in
      (match t with
      | Type.Int -> AstType.AffichageInt x
      | Type.Bool -> AstType.AffichageBool x
      | Type.Rat -> AstType.AffichageRat x
      | _ -> failwith "Internal Error")
  | AstTds.Conditionnelle (e,b1,b2) ->
      let (ne, t) = analyse_type_expression e in
      if (t = Type.Bool) 
      then AstType.Conditionnelle (ne, analyse_type_bloc b1, analyse_type_bloc b2)
      else raise (TypeInattendu (t, Type.Bool))
  | AstTds.TantQue (e,b) ->
    let (ne, t) = analyse_type_expression e in
      if (t = Type.Bool) 
      then AstType.TantQue (ne, analyse_type_bloc b)
      else raise (TypeInattendu (t, Type.Bool))
  | AstTds.Retour (e, info) ->
      begin
        let (ne,t) = analyse_type_expression e in
        (match (info_ast_to_info info) with
        | InfoFun(_,typ,_) -> 
          if (typ = t) 
          then AstType.Retour (ne, info)
          else raise (TypeInattendu (t, typ))
        | _ -> failwith "Internal Error")
      end
  | AstTds.Declaration (t, info, e) ->
    begin
      let (ne,te) = analyse_type_expression e in
      if (Type.est_compatible t te) then
        (modifier_type_variable t info;
        AstType.Declaration(info, ne))
      else raise (TypeInattendu (te, t))
    end
  | AstTds.Empty -> AstType.Empty
  | AstTds.Boucle(info, b) ->
    begin
      let nb = analyse_type_bloc b in 
      AstType.Boucle(info, nb)
    end
  | AstTds.Arret info -> AstType.Arret info
  | AstTds.Continue info -> AstType.Continue info

(* analyse_type_bloc : AstTds.bloc -> AstTypeBloc*)
(* Vérifie le bon typage et tranforme le bloc en un bloc de type AstType.bloc *)
(* Erreur si mauvais typage *)
and analyse_type_bloc bloc =
  List.map analyse_type_instruction bloc


(* analyse_type_fonction : AstTds.fonction -> AstType.fonction*)
(* Paramètre : la fonction à analyser *)
(* Vérifie le bon typage et tranforme la fonction
en une fonction de type AstType.fonction *)
(* Erreur si mauvais typage *)
let analyse_type_fonction (AstTds.Fonction (typ, info, lp, bloc)) =
  List.iter (fun (argTyp, argInfo) -> modifier_type_variable argTyp argInfo) lp;

  let (paramTypeList, paramInfoList) = List.split lp in
  modifier_type_fonction typ paramTypeList info;
  let nb = analyse_type_bloc bloc in
  AstType.Fonction(info, paramInfoList, nb)
  
  



(* analyser : AstTds.programme -> AstType.Programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie le bon typage et tranforme le programme
en un programme de type AstType.programme *)
(* Erreur si mauvais typage *)
let analyser (AstTds.Programme (fonctions,prog)) =
  let nf = List.map analyse_type_fonction fonctions in
  let nb = analyse_type_bloc prog in
  AstType.Programme (nf,nb)
