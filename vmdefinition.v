(** * Définition d'une machine virtuelle, paramétrée par le type des valeurs et la définition de l'héritage.

On utilisera ce foncteur pour définir les trois machines virtuelles
(défensive, offensive, abstraite). *)

From bcv Require Import heritage vmtype LibHypsNaming TacNewHyps.
Require Import Setoid.

(** Ceci sera un paramètre de VM: le type des valeurs manipulées par la
    VM + la fonction de typage de ces valeurs. *)
Module Type VMVal.
  Parameter Inline Val:Set.
  Parameter Inline v2t: Val -> VMType.
End VMVal.

(** Une VM est paramétrée par le type des valeurs et sa fonction de
    typage, ainsi qu'une relation d'héritage sur les classes . *)
Module VMDefinition(V:VMVal)(H:Herit).
  (* Include H. *)
  (* Include V. *)

  (** * Représentation de l'état interne da la VM. *)

  (** Un objet, même offensif est un nom de classe + la valeur des champs. *)
  Record Obj: Type :=
    { objclass: class_id; (** La classe de l'objet *)
      objfields: (Dico.t V.Val) (** les valeurs des champs *) }.

  Notation Stack := (list V.Val).
  Notation Registers := (Dico.t V.Val).
  Notation Heap := (Dico.t Obj).

  (** Une frame contient les données d'exécution d'une méthode, la
  définition de la méthode, les registres locaux à la méthode, sa pile
  d'opérande et le compteur programme pointant sur l'opération courante. *)
  Record Frame : Type := 
    Build_Frame
      { mdef: MethodDef;
        regs:  Registers;
        stack: Stack;
        pc: pc_idx }.

  (** La pile des frame en cours d'exécution *)
  Definition Framestack := list Frame.

  (** L'Etat de la machine virtuelle: la pile des frame + le tas. *)
  Record State := Build_State { frame:  Frame; framestack: Framestack; heap: Heap }.

  (** * Egalité et compatibilité sur les frame, les stack, les états etc

 Ainsi que les propriétés permettant de les utiliser avec rewrite. *)

  Record frame_eq f1 f2 : Prop := 
    frame_eq_C { _: f1.(mdef)=f2.(mdef);
                 _: Dico.Equal f1.(regs) f2.(regs);
                 _: f1.(stack) = f2.(stack);
                 _: f1.(pc)=f1.(pc) }.

  Inductive obj_eq r1 r2 : Prop :=
    reg_eq_C : Dico.Equal r1.(objfields) r2.(objfields)
               -> r1.(objclass) = r2.(objclass) -> obj_eq r1 r2.

  Inductive heap_eq h1 h2 : Prop :=
    heap_eq_C : Dico.Equiv obj_eq h1 h2 -> heap_eq h1 h2.

  Inductive state_eq s1 s2 : Prop := 
    state_eq_C : frame_eq s1.(frame) s2.(frame) -> s1.(framestack) = s2.(framestack) ->
                 heap_eq s1.(heap) s2.(heap) -> state_eq s1 s2.

  (** ** Compatibilité entre deux stack, frame state...       

     a Compatible avec b = a a une type compatible avec celui de b. *)
  Definition compat_val_type v t := H.compat (V.v2t v) t.
  Definition Compat_val_type v t := compat_val_type v t = true.
  Definition compat_val v1 v2 := H.compat (V.v2t v1) (V.v2t v2).
  Definition Compat_val v1 v2 := compat_val v1 v2 = true.

  Inductive compat_stack: Stack -> Stack -> Prop :=
    comstacknil: compat_stack nil nil
  | comstackcons: forall x y e f, 
                    compat_stack x y -> H.Compat (V.v2t e) (V.v2t f)
                    -> compat_stack (e::x) (f::y).

  Definition compat_regs (x y:Registers) := 
    forall i a, Dico.find i y = Some a
                -> exists b, Dico.find i x = Some b /\ Compat_val a b.

  (** La compatibilité entre états: compatiilté du tas et de tous les
     morceaux de la pile de frame. *)
  Record compat_state s s' :=
    { compat_st: (compat_stack (s.(frame).(stack)) (s'.(frame).(stack)));
      compat_rg: (compat_regs (s.(frame).(regs)) (s'.(frame).(regs)));
      compat_stk: (s.(framestack) = s'.(framestack));
      compat_hp: (heap_eq (s.(heap)) (s'.(heap)));
      compat_fr:((s.(frame).(mdef)) = (s'.(frame).(mdef))) }.

Ltac rename_vmdef h th := fail.

(** Mécanique de nommage automatique des hypothèses. Ne pas redéfinir
    ceci, redéfinir rename_vmdef comme ci-dessous. *)
Ltac rename_hyp h th ::=
  match th with
  | _ => (rename_vmdef h th)
  | _ => (LibHypsNaming.rename_hyp_neg h th)
  end.


Ltac rename_vm1 h th :=
  match th with
    | frame_eq ?x ?y => fresh "frEq_" x "_" y
    | frame_eq ?x ?y => fresh "frEq_" x
    | frame_eq ?x ?y => fresh "frEq"

    | state_eq ?x ?y => fresh "stEq_" x "_" y
    | state_eq ?x ?y => fresh "stEq_" x
    | state_eq ?x ?y => fresh "stEq"

    | heap_eq ?x ?y => fresh "hpEq_" x "_" y
    | heap_eq ?x ?y => fresh "hpEq_" x
    | heap_eq ?x ?y => fresh "hpEq"

    | obj_eq ?x ?y => fresh "obEq_" x "_" y
    | obj_eq ?x ?y => fresh "obEq_" x
    | obj_eq ?x ?y => fresh "obEq"


    | compat_val ?x ?y => fresh "compVal_" x "_" y
    | compat_val ?x ?y => fresh "compVal_" x
    | compat_val ?x ?y => fresh "compVal"

    | Compat_val ?x ?y => fresh "CompVal_" x "_" y
    | Compat_val ?x ?y => fresh "CompVal_" x
    | Compat_val ?x ?y => fresh "CompVal"

    | Compat_val_type ?x ?y => fresh "compVT_" x "_" y
    | Compat_val_type ?x ?y => fresh "compVT_" x
    | Compat_val_type ?x ?y => fresh "compVT"

    | compat_val_type ?x ?y => fresh "CompVT_" x "_" y
    | compat_val_type ?x ?y => fresh "CompVT_" x
    | compat_val_type ?x ?y => fresh "CompVT"

    | compat_stack ?x ?y => fresh "comp_stk_" x "_" y
    | compat_stack ?x _ => fresh "comp_stk_" x
    | compat_stack _ _ => fresh "comp_stk"

    | compat_regs ?x ?y => fresh "comp_reg_" x "_" y
    | compat_regs ?x _ => fresh "comp_reg_" x
    | compat_regs _ _ => fresh "comp_reg"

    | Dico.Equal ?x ?y => fresh "DEq_" x "_" y
    | Dico.Equal ?x ?y => fresh "DEq_" x
    | @Dico.Equal ?t _ _ => fresh "DEq" t
    | Dico.Equal ?x ?y => fresh "DEq"
  end.

Ltac rename_vmdef ::= rename_vm1.

  (** Propriété des relations de compatibilité et d'égalité

 (en vue de pouvoir les utiliser dans rewrite). *)

  Lemma Compat_val_refl : reflexive _ Compat_val.
  Proof.
    unfold Compat_val, compat_val.
    red.
    intros.
    rewrite H.Compat_refl;auto.
  Qed.

  Lemma Compat_val_trans : transitive _ Compat_val.
  Proof.
    unfold Compat_val, compat_val.
    red.
    intros.
    rewrite H.Compat_trans with (V.v2t x) (V.v2t y) (V.v2t z);auto.
  Qed.

  Add Parametric Relation: V.Val Compat_val reflexivity proved by Compat_val_refl transitivity proved by Compat_val_trans as Compat_val_rel.

  Lemma frame_eq_refl : reflexive _ frame_eq.
  Proof.
    red.  
    intros x.
    destruct x;constructor;auto.
    apply Dicomore.Equal_refl.
  Qed.

  Lemma frame_eq_sym : symmetric _ frame_eq.
  Proof.
    red.
    !intros.
    !destruct h_frEq_x_y.
    constructor;auto.
    apply Dicomore.Equal_sym.
    assumption.
  Qed.

  Lemma frame_eq_trans : transitive _ frame_eq.
  Proof.
    red.  
    !intros.
    !destruct h_frEq_x_y.
    !destruct h_frEq_y_z.
    constructor;auto.
    - rewrite <- heq_mdef_y.
      assumption.
    - apply Dicomore.Equal_trans with (regs y);assumption.
    - rewrite heq_stack_x;auto.
  Qed.

  (** On peut utiliser les tactique [reflexivity], [symmetry] et
  [transitivity]. Ainsi que [rewrite] à condition de déclarer
  suffisemment de morphismes [Proper] comme ci-dessous. *)
  Add Parametric Relation : Frame (frame_eq )
                                  reflexivity proved by (frame_eq_refl)
                                  symmetry proved by (frame_eq_sym)
                                  transitivity proved by (frame_eq_trans)
                                  as frame_eq_rel.
  

  Add Parametric Morphism: Build_Frame with signature
      (@eq MethodDef ==> @Dico.Equal V.Val ==> @eq Stack ==> @eq pc_idx ==> frame_eq)
        as build_frame_morphism.
  Proof.
    !intros.
    constructor;auto.
  Qed.



  Lemma obj_eq_refl : reflexive _ obj_eq.
  Proof.
    red.  
    intros x.
    split.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma obj_eq_sym : symmetric _ obj_eq.
  Proof.
    red.  
    !intros.
    destruct h_obEq_x_y.
    split.
    - symmetry.
      assumption.
    - symmetry;assumption.
  Qed.

  Lemma obj_eq_trans : transitive _ obj_eq.
  Proof.
    red.  
    !intros.
    !destruct h_obEq_x_y.
    !destruct h_obEq_y_z.
    split.
    - transitivity (objfields y);auto.
    - transitivity (objclass y);auto.
  Qed.

  Add Parametric Relation : Obj (obj_eq )
                                  reflexivity proved by (obj_eq_refl)
                                  symmetry proved by (obj_eq_sym)
                                  transitivity proved by (obj_eq_trans)
                                  as obj_eq_rel.


  Lemma equiv_obj_eq_refl : reflexive _ (Dico.Equiv obj_eq).
  Proof.
    red.  
    intros x.
    red.
    split;!intros.
    - reflexivity .
    - intros h h'. rewrite (Dicomore.MapsTo_fun h h') .    
      reflexivity.
  Qed.

  Lemma equiv_obj_eq_sym : symmetric _ (Dico.Equiv obj_eq).
  Proof.
    red.  
    intros x y H.
    destruct H.
    split;intros.
    - rewrite H.
      reflexivity.
    - symmetry.
      apply H0 with k;assumption.
  Qed.

  Lemma equiv_obj_eq_trans : transitive _ (Dico.Equiv obj_eq).
  Proof.
    red.  
    intros x y z H H0.
    destruct H.
    destruct H0.
    split;intros.
    - transitivity (Dico.In (elt:=Obj) k y);auto.
    - assert (Dico.In (elt:=Obj) k y).
      apply H.
      exists e.
      apply H3.
      destruct H5.
      assert (obj_eq e x0).
      apply H1 with k;assumption.
      assert (obj_eq x0 e').
      apply H2 with k;auto.
      transitivity x0;assumption.
  Qed.

  

  Add Parametric Relation: (Dico.t Obj) (Dico.Equiv obj_eq)
                                        reflexivity proved by (equiv_obj_eq_refl)
                                        symmetry proved by (equiv_obj_eq_sym)
                                        transitivity proved by (equiv_obj_eq_trans)
                                        as equiv_obj_eq_rel.


  Lemma heap_eq_refl : reflexive _ heap_eq.
  Proof.
    red.  
    intros x.
    split.
    reflexivity.
  Qed.

  Lemma heap_eq_sym : symmetric _ heap_eq.
  Proof.
    red.  
    intros x y H.
    destruct H.
    split.
    symmetry.
    assumption.
  Qed.

  Lemma heap_eq_trans : transitive _ heap_eq.
  Proof.
    red.  
    intros x y z H H0.
    destruct H.
    destruct H0.
    split.
    transitivity y;auto.
  Qed.

  Add Parametric Relation : Heap (heap_eq )
                                  reflexivity proved by (heap_eq_refl)
                                  symmetry proved by (heap_eq_sym)
                                  transitivity proved by (heap_eq_trans)
                                  as heap_eq_rel.


  Lemma state_eq_refl : reflexive _ state_eq.
  Proof.
    red.  
    intros x.
    destruct x;constructor;auto.
    - apply frame_eq_refl.
    - reflexivity.
  Qed.

  Lemma state_eq_sym : symmetric _ state_eq.
  Proof.
    red.  
    intros x y H.
    destruct H.
    constructor;auto.
    - symmetry.
      assumption.
    - symmetry.
      assumption.
  Qed.

  Lemma state_eq_trans : transitive _ state_eq.
  Proof.
    red.  
    intros x y z H H0.
    destruct H.
    destruct H0.
    constructor;auto.
    - apply frame_eq_trans with (frame y);assumption.
    - rewrite <- H3;auto.
    - transitivity (heap y);assumption.
  Qed.

  Add Parametric Relation : State (state_eq )
                                  reflexivity proved by (state_eq_refl)
                                  symmetry proved by (state_eq_sym)
                                  transitivity proved by (state_eq_trans)
                                  as state_eq_rel.


  Add Parametric Morphism: Build_State with signature (frame_eq ==> @eq Framestack ==> Dico.Equiv obj_eq ==> state_eq)
                                       as build_state_morphism.
  intros x y H y0 x0 y1 H0.
  constructor;auto.
  constructor.
  simpl.
  assumption.
  Qed.



  Lemma compat_stack_refl : reflexive _ compat_stack.
  Proof.
    red.   
    intros x.
    induction x;auto.
    - constructor.
    - constructor.
      + assumption.
      + apply H.Compat_refl;auto.
  Qed.

  Lemma compat_stack_trans : transitive _ compat_stack.
  Proof.
    red.   
    intros x y z h h'.
    generalize x h.
    clear x h.
    induction h';auto.
    intros x0 h.
    inversion h;subst;auto.
    constructor.
    - apply IHh';assumption.
    - apply H.Compat_trans with (V.v2t e);assumption.
  Qed.


  Add Parametric Relation: Stack compat_stack
                                 reflexivity proved by compat_stack_refl
                                 transitivity proved by compat_stack_trans
                                 as compat_stack_rel.

  Lemma compat_regs_refl : reflexive _ compat_regs.
  Proof.
    red.   
    intros x.
    red.
    intros i a H.
    exists a;intuition.
  Qed.

  Lemma compat_regs_trans : transitive _ compat_regs.
  Proof.
    red.   
    unfold compat_regs.
    intros x y z H H0.
    intros i a H1.
    assert (H0':=H0 i a H1).
    destruct H0'.
    destruct H2.
    assert (H':= H i x0 H2).
    destruct H'.
    destruct H4.
    exists x1;intuition.
    apply Compat_val_trans with (y:=x0);auto.
  Qed.



  Add Parametric Relation: Registers compat_regs
                                     reflexivity proved by compat_regs_refl
                                     transitivity proved by compat_regs_trans
                                     as compat_regs_rel.

  Add Parametric Morphism: (compat_regs) with signature
                                         (Dico.Equal ==> Dico.Equal ==> iff) as compat_regs_morphism.
  Proof.
    intros x y H x0 y0 H0.
    split;intros h.
    - red;intros.
      rewrite <- H0 in H1.
      red in h.
      assert (hh:=h i a H1).
      destruct hh.
      rewrite H in H2.
      exists x1;auto.

    - red;intros.
      rewrite H0 in H1.
      red in h.
      assert (hh:=h i a H1).
      destruct hh.
      rewrite <- H in H2.
      exists x1;auto.
  Qed.

  
  Add Parametric Morphism: compat_state with signature 
                                        (state_eq ==> state_eq ==> iff) as compat_state_morphism.
  Proof.
    intros x x' hxx' y y' hyy'.
    destruct hxx' as (hxx' , hxfrst, hxhp).
    destruct hxx' as (hxmdef, hxregs, hxst, hxpc).
    destruct hyy' as (hyy' , hyfrst, hyhp).
    destruct hyy' as (hymdef, hyregs, hyst, hypc).
    split;intro hxy; destruct hxy as (hst,hregs,hfrst,hhp,hmdef).
    { split.
      - rewrite <- hxst.
        transitivity (stack (frame y)).
        assumption.
        rewrite <- hyst.
        apply compat_stack_refl. 
      - rewrite <- hxregs.    
        transitivity ((regs (frame y))).
        assumption.    
        rewrite <- hyregs.
        reflexivity.
      - rewrite <- hxfrst.
        rewrite hfrst.
        assumption.
      - transitivity(heap x).
        symmetry;assumption.
        transitivity(heap y); assumption.
      - transitivity (mdef (frame x)).
        symmetry;assumption.
        transitivity (mdef (frame y)); assumption. }
    { split.
      - rewrite hxst.
        rewrite hst.
        rewrite hyst.
        reflexivity.
      - rewrite hxregs.    
        rewrite hregs.
        rewrite hyregs.
        reflexivity.
      - rewrite hxfrst.
        rewrite hyfrst.
        assumption.
      - rewrite hxhp ,hyhp.
        assumption.
      - rewrite hymdef, hxmdef.
        assumption. }
  Qed.

  Lemma compat_state_refl : reflexive _ compat_state.
  Proof.
    red.
    intros x.
    split;auto.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.


  Lemma compat_state_eq' : forall x y, state_eq x y -> compat_state x y.
  Proof.
    intros x y H.
    rewrite H.
    apply compat_state_refl.
  Qed.

  Lemma compat_state_trans : transitive _ compat_state.
  Proof.
    red.
    intros x y z hxy hyz.
    destruct hxy as (hxst,hxregs,hxfrst,hxhp,hxmdef). 
    destruct hyz as (hyst,hyregs,hyfrst,hyhp,hymdef).
    constructor.
    - transitivity (stack (frame y)); assumption.
    - transitivity (regs (frame y)); assumption.
    - transitivity (framestack y); assumption.
    - transitivity (heap y); assumption.
    - transitivity (mdef (frame y)); assumption.
  Qed.

  Add Parametric Relation: State compat_state
                                 reflexivity proved by compat_state_refl
                                 transitivity proved by compat_state_trans
                                 as compat_state_rel.

  (** Pour plus de praticité on rend accessiblt tout H et V
      directement dans Vmdefinition. *)
  Include H.
  Include V.
End VMDefinition.



