Require Import bcv.vmtype.
Require Import bcv.abstract_correct.

(* FICHIER À implanter complètement: les deux dernière fonctions du
fichier doivent être les suivantes: *)

(* Vérification d'une méthode *)
Definition bcv_one_meth (meth:MethodDef): bool:= false. (* TODO *)
  
(** Vérification indépendante de chaque méthode de la liste, en
    supposant que les autres se comporte correctement (prennent le bon
    nombre d'argument et retourne le bon type). *)
Definition bcv (lmeth:list MethodDef): bool:=
  false. (* TODO *)
