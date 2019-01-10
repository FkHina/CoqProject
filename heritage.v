(** * Définition de la notion de relation d'héritage + propriétés associées. *)
Require Import bcv.vmtype.

Module Type Herit.
(** L'héritage est un ordre [Sub] large sur les class_id, il en découle un ordre
    [Compat] sur les types. On en déduira un ordre sur les états de machines
    virtuelles plus loin. Par ailleurs, quand c1 <=_Sub c2, cela signifie que les
    champs de c2 existent dans c1 et on le même type *)
  
  Parameter sub: class_id -> class_id -> bool.
  Parameter allcl: Dico.t ClasseDef.

  Definition Sub x y:Prop := sub x y = true.
  Parameter Sub_refl:forall x: class_id, Sub x x.
  Parameter Sub_trans:forall x y z: class_id, Sub x y -> Sub y z -> Sub x z.
  Parameter sub_only_def1: forall c1 c2, Sub c1 c2 -> Dico.find c1 allcl <> None.
  Parameter sub_only_def2: forall c1 c2:Dico.key, Sub c1 c2 -> Dico.find c2 allcl <> None.

  (** Héritage: les champs hérités ont *exactement le même* type. *)
  Parameter sub_preserves_fields: forall c1 c2:Dico.key, forall cl1 cl2:ClasseDef,
    Sub c1 c2 -> 
    Dico.find c1 allcl = Some cl1 -> 
    Dico.find c2 allcl = Some cl2 -> 
    forall i fldt2, Dico.find i cl2 = Some fldt2 ->
      exists fldt1, Dico.find i cl1 = Some fldt1
        /\ fldt1 = fldt2.

  Lemma Sub_okl: forall cl1 cl2, Sub cl1 cl2 -> exists cldef, FIND cl1 allcl = Some cldef.
  Proof.
    intros cl1 cl2 H. 
    specialize sub_only_def1 with (1:=H) as h.
    destruct (FIND cl1 allcl);eauto.
    destruct h;auto.
  Qed.
    
  Lemma Sub_okr: forall cl1 cl2, Sub cl1 cl2 -> exists cldef, FIND cl2 allcl = Some cldef.
  Proof.
    intros cl1 cl2 H. 
    specialize sub_only_def2 with (1:=H) as h.
    destruct (FIND cl2 allcl);eauto.
    destruct h;auto.
  Qed.

  Lemma sub_Sub: forall x y, Sub x y <-> sub x y = true.
  Proof.
    intros x y.
    unfold Sub.
    split;auto.
  Qed.

  (** On peut utiliser les tactiques transitivity et reflexivity sur
  des buts de la forme Sub X Y. *)
  Add Parametric Relation: class_id Sub reflexivity proved by Sub_refl transitivity proved by Sub_trans as Sub_rel.

  (** [compat t1 t2] signifie qu'on peut utiliser une valeur de
      type t1 à la place d'une valeur de type t2. *)
  Function compat (t1 t2:VMType): bool :=
    match t1,t2 with
      | Tint,Tint => true
      | Tref id1, Tref id2 => sub id1 id2
      | Object, Object => true
      | Tref _,Object =>  true
      | Trefnull,Object => true
      | Top,Top => true
      | Trefnull,Tref _ => true
      | Trefnull,Trefnull => true
      | _ , _ => false
    end.

  Definition Compat x y:Prop := compat x y = true.

  Lemma Compat_refl : forall x, Compat x x.
  Proof.
    unfold Compat.
    destruct x;simpl;try reflexivity.
    apply Sub_refl.
  Qed.

  Lemma Compat_trans : forall x y z, Compat x y -> Compat y z -> Compat x z.
  Proof.
    intros x y z H H0.
    unfold Compat in *.
    destruct x;destruct y;destruct z;simpl in *;intros;try discriminate;try reflexivity.
    apply Sub_trans with id0;assumption.
  Qed.

  (** On peut utiliser les tactiques transitivity et reflexivity sur
      des buts de la forme Trans X Y. *)
  Add Parametric Relation: VMType Compat reflexivity proved by Compat_refl transitivity proved by Compat_trans as Compat_rel.

End Herit.
