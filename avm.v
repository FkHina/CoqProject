From bcv Require Import heritage vmtype vmdefinition  LibHypsNaming.
Require Import List .
Import ListNotations.

(** * Valeurs de la machine abstraite

   On abstrait les défintions ci-dessus: on enlève les valeurs et les adresses
   mémoire et on les remplace par les types. *)

Module AbsVal <: VMVal.

  Definition Val := VMType.
  
  (** Calcul du type d'une valeur défensive. *)
  Definition v2t (v:Val): VMType := v.

End AbsVal.


Module A (Import H:Herit).
  Module Abs := VMDefinition(AbsVal)(H).
  Include Abs.

  Ltac rename_avm h th := fail.

  (* Hypothesis renaming stuff from other files + current file.
     DO NOT REDEFINE IN THIS FILE. Redefine rename_avm instead. *)
  Ltac rename_hyp h th ::=
    match th with
    | _ => (rename_avm h th)
    | _ => (Abs.rename_vmdef h th)
    | _ => (LibHypsNaming.rename_hyp_neg h th)
    end.


(** * Exécution de la machine défensive.
   Pas de vérif de overflow. pas de nb négatifs. *)
  Function exec_step (s:State): list (option State) :=
    []. (* FAUX. À REMPLIR *) 


(** * Tests *)

  Notation "k --> i , d" := (Dico.add k i d) (at level 55, right associativity).

  Definition prog:MethodDef := 
    {| instrs := (0 --> Iload 1 ,
                  1 --> Istore 2 ,
                  2 --> ret ,
                  Dico.empty ) ;
       argstype := Tint :: Tint:: nil;
       restype := Tint |}.

  Definition startstate:State := 
    {| 
      framestack := nil;
      heap:= Dico.empty ;
      frame := {|
        mdef:= prog ; 
        regs:= (0 --> Tint , 1 --> Tint, Dico.empty);
        pc:= 0;
        stack:= nil
        |}
      |}.

  Fixpoint exec_n (s : State) (n:nat) {struct n}: list (option State) :=
    match n with
      | 0 => [ Some s ]
      | S n' =>
        let ls' := exec_step s in
          (fix exec_l_n (ls:list (option State)) {struct ls}: list (option State) :=
          match ls with
            | nil => nil
            | None :: ls' => None :: exec_l_n ls'
            | Some s' :: ls' => List.app (exec_n s' n') (exec_l_n ls')
          end) ls'
    end.

  Eval simpl in exec_n startstate 1.
  Eval simpl in exec_n startstate 2.
  Eval simpl in exec_n startstate 5.

  Lemma essai : forall s x,
    exec_step s = [ Some x ] -> 
    x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.

  Lemma essai2 : forall s x y,
    exec_step s = [ Some x ; Some y] -> 
    x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.

End A.

