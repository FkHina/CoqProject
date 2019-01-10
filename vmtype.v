(** * Les types de base de la machine virtuelle *)

Require Export bcv.lib.

(** Toutes les adresses sont des entiers naturels ([nat]). *)
Definition heap_idx := nat.
Definition reg_idx := nat.
Definition pc_idx := nat.
Definition fld_idx := nat.
Definition class_id := nat.
Definition meth_id := nat.

(** Les types, y compris les types nécessaires au vérificateur. *)
Inductive VMType:Set := Tint | Tref (id:class_id) | Object | Top | Trefnull.

(** Profil d'une classe = type des champs (map: numero de champ --> type). *)
Notation ClasseDef := (Dico.t VMType).

(** Ensemble de tous les profils de classes (map: numero de classe --> type ). *)
Notation AllClassesDef := (Dico.t ClasseDef).

(** Les instructions. Notez que les instructions sont fortement
    typées. C'est-à-dire qu'elles comportent la classe attendue sur la
    pile avant l'opération (ex: Rstore,Getfield,Putfield) et/ou la
    classe attendu sur la pile après l'opération (ex:
    Rload,Getfield,Putfield). Notez qu'il n'y a pas d'appel de méthode
    en l'état actuel, pour l'instant on va programmer un vérificateur
    de méthode isolée. Ajouter l'appel de méthode est une option du projet. *)
Inductive Instr : Set :=
| Iconst (i:nat)
| Iadd
| Iload (ridx:reg_idx)
| Rload (cl:class_id) (ridx:reg_idx)
| Istore (ridx:reg_idx)
| Rstore (cl:class_id) (ridx:reg_idx)
| Iifle (pc:pc_idx)
| Goto (pc:pc_idx)
| Getfield (cl:class_id) (fldrf:fld_idx) (typ:VMType)
| Putfield (cl:class_id) (fldrf:fld_idx) (typ:VMType)
| New (clid:class_id)
| ret.

(* TODO: pour les plus audacieux: | invokestatic (m:meth_id) *)


(** Méthode = type arguments + type retour  + dictionnaire d'instructions. *)
Record MethodDef := { instrs:(Dico.t Instr); argstype: list VMType; restype:VMType }.

