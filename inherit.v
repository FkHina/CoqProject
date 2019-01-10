
Require Export Ccpo.
Require Export FMapList.
Require FMapFacts.

Module Type Inheritance (dictionnaire:FMapInterface.WS).
  Parameter type: Type.
  Parameter sub: ord type.
  Instance subcl: ord type := sub.
End Inheritance.

Module Type typeSystem.
  Parameter class_id: Type.
  Parameter baseType: Type.
  Inductive type : Type := 
  | class: class_id
  | val: baseType.



Module ClassMap (dictionnaire:FMapInterface.WS) (Inherit:Inheritance(dictionnaire)).

  Import Inherit.
  Module dictionnairefacts:=FMapFacts.WFacts(dictionnaire).
  Module dictionnaireprops:=FMapFacts.WProperties(dictionnaire).


  Definition classdef := (dictionnaire.t type).
  Definition allclassdef := (dictionnaire.t classdef).

  Section cldef.
    Variable allcl:allclassdef.

    Axiom sub_only_def1: forall c1 c2:type, 
      c1 <= c2 -> dictionnaire.find c1 allcl <> None.

    Axiom sub_only_def2: forall c1 c2:dictionnaire.key, 
      c1 <= c2 -> dictionnaire.find c2 allcl <> None.

    Axiom sub_preserves_fileds: forall c1 c2:dictionnaire.key, forall cl1 cl2:classdef,
      c1 <= c2 -> 
      dictionnaire.find c1 allcl = Some cl1 -> 
      dictionnaire.find c2 allcl = Some cl2 -> 
      forall i fldt2, dictionnaire.find i cl2 = Some fldt2
        -> exists fldt1, dictionnaire.find i cl1 = Some fldt1 /\ fldt1 <= fldt2.



Section ClassDef.
  Variable classe:Set.
  Variable 

Definition inherit A {o:ord A} := cpo A.



Class inherit {A} (O:cpo (ord A)) : :=



(* xxx tentative de systématisation des
   raisonnement sur les safe state. Bof. *)
  Definition dico_diff_p A (P:A -> Prop) (d1 d2:Dico.t A):Prop :=
    forall k x, Dico.MapsTo k x d1 -> ~Dico.MapsTo k x d2 -> P x.

  Definition stack_diff_p A (P:A -> Prop) (s1 s2:list A):Prop := 
    forall x, List.In x s1 -> ~List.In x s2 -> P x.

  Definition frame_diff_p P f1 f2 : Prop := 
    dico_diff_p _ P (f1.(D.regs)) (f2.(D.regs))
    /\ stack_diff_p _ P (f1.(D.stack)) (f2.(D.stack)).

  Definition obj_diff_p P o1 o2: Prop := 
    dico_diff_p _ P (o1.(D.objfields)) (o2.(D.objfields)).

  Definition state_diff_p P s1 s2 : Prop := 
    frame_diff_p P (s1.(D.frame)) (s2.(D.frame))
    /\ (s1.(D.framestack)) = (s2.(D.framestack))
    /\ (s1.(D.heap)) = (s2.(D.heap)).

  Lemma dico_diff_p_refl A P: reflexive _ (dico_diff_p A P).
  Proof.
    red.  
    intros x.
    red.
    intros k x0 H H0.
    contradiction.
  Qed.

  Lemma stack_diff_p_refl A P: reflexive _ (stack_diff_p A P).
  Proof.
    red.  
    intros x.
    red.
    intros x0 H H0.
    contradiction.
  Qed.

  Lemma frame_diff_p_refl P: reflexive _ (frame_diff_p P).
  Proof.
    red.  
    intros x.
    red.
    split.
    apply dico_diff_p_refl.
    apply stack_diff_p_refl.
  Qed.

(* 
  Lemma frame_eq_sym : symmetric _ frame_eq.
  Proof.
    red.  
    intros x y H.
    destruct H.
    constructor;auto.
    apply Dicofacts.Equal_sym.
    assumption.
  Qed.
 *)

  Lemma toto : forall A k (x:A) m,
    (forall a b:A, {a=b} + {a<>b}) -> 
    {Dico.MapsTo k x m} + {~ Dico.MapsTo k x m}.
  Proof.
    intros A k x m H.
    destruct_with_eqn (Dico.find k m).
    destruct (H x a).
    subst;auto.
    left.
    apply Dico.find_2;assumption.
    assert (~(FIND  k m = Some x)).
    intro abs.
    rewrite Heqo in abs.
    inversion abs. clear abs. subst.
    elim n;auto.
    right.
    intro abs.
    apply Dico.find_1 in abs.
    contradiction.
    right.
    intro abs.
    apply Dico.find_1 in abs.
    rewrite abs in Heqo.
    discriminate Heqo.
  Qed.


  Lemma dico_eq_trans A {hdec:forall x y:A, {x=y} + {x<>y}} P : transitive _ (dico_diff_p A P).
  Proof.
    red.  
    intros x y z H H0.
    red in H.
    red in H0.
    red.
    intros k x0 H1 H2.
    specialize (H k x0 H1).
    destruct (toto _ k x0 y);auto.
    apply H0 with k;auto.
  Qed.

  Lemma stack_eq_trans A {hdec:forall x y:A, {x=y} + {x<>y}} P : transitive _ (stack_diff_p A P).
  Proof.
    red.  
    intros x y z H H0.
    red in H.
    red in H0.
    red.
    intros x0 H1 H2.
    destruct (in_dec hdec x0 y).
    eauto.
    eauto.
  Qed.

  Lemma frame_diff_trans P :
    transitive _ (frame_diff_p P).
  Proof.
    red.  
    intros x y z H H0.
    destruct H.
    destruct H0.
    split.
    eapply dico_eq_trans;eauto.
    apply DefVal.val_eq_dec.
    eapply stack_eq_trans;eauto.
    apply DefVal.val_eq_dec.
  Qed.

  Add Parametric Relation : Frame (frame_eq )
    reflexivity proved by (frame_eq_refl)
    symmetry proved by (frame_eq_sym)
      transitivity proved by (frame_eq_trans)
        as frame_eq_rel.


    Add Parametric Morphism: Build_Frame with signature (@eq Method ==> @Dico.Equal Val ==> @eq Stack ==> @eq pc_idx ==> frame_eq) as build_frame_morphism.
      intros y x y0 H y1 y2.
      constructor;auto.
    Qed.





(* xxx *)


