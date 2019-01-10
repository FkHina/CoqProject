(** 
   Version très simplifiée des idée de: "Java bytecode verification: algorithms
   and formalizations", Xavier Leroy (Journal of Automated Reasoning,
   30(3-4):235-269, 2003).

   Dont voici l'abstract:
   
   "Bytecode verification is a crucial security component for Java applets, on
   the Web and on embedded devices such as smart cards. This paper reviews the
   various bytecode verification algorithms that have been proposed, recasts
   them in a common framework of dataflow analysis, and surveys the use of proof
   assistants to specify bytecode verification and prove its correctness."

 *)



Require Import OrderedType OrderedTypeEx OrderedTypeAlt DecidableType
        DecidableTypeEx RelationClasses  Omega.
From bcv Require Import LibHypsNaming heritage vmtype vmdefinition.


(** * Valeurs de la machine offensive

   La définition des types, classes et instruction est fixée dans [vmtype]. *)

Module OffVal <: VMVal.
  Definition Val := nat.

  (** Calcul du type d'une valeur offensive. *)
  Definition v2t (v:Val): VMType := Top.

  Lemma val_eq_dec : forall v1 v2:Val, {v1=v2}+{v1<>v2}.
  Proof.
    intros v1 v2.
    decide equality.
  Qed.

End OffVal.



Module O (Import H:Herit).


  (** États offensifs. *)
  Module Off := VMDefinition(OffVal)(H).
  Include Off.
  Ltac rename_ovm h th := fail.

  (* Hypothesis renaming stuff from other files + current file.
     DO NOT REDEFINE IN THIS FILE. Redefine rename_ovm instead. *)
  Ltac rename_hyp h th ::=
    match th with
    | _ => (rename_ovm h th)
    | _ => (Off.rename_vmdef h th)
    | _ => (LibHypsNaming.rename_hyp_neg h th)
    end.

  (** test *)
  (*
    Definition obj1:Obj := {| objclass:=1; objfields:=Dico.empty _|}.
    Definition heap1:Heap := Dico.empty _ .
    Definition heap2:Heap := Dico.add 1 obj1 heap1.
    Definition heap3:Heap := Dico.add 2 obj1 heap2.
    Eval vm_compute in (maxkey heap3).
    Eval vm_compute in (maxkey heap2).
   *)
  (* fin test *)


  (** * Construction d'objet frais pour le bytecode [New]. *)

  (** Construit un Dico de valeur par défaut à partir d'un Dico de
      types. + preuve que [build_flds] est un morphisme pour [Dico.Equal]. *)
  Definition build_flds: ClasseDef -> (Dico.t Val) :=
    Dico.map 
      (fun t:VMType =>
         match t with
         | Tint => 0
         | Tref id => 0 (** null = 0 *)
         | Object => 0 (** null = 0 *)
         | Top => 0 (** Should never happen *)
         | Trefnull => 0 (** Should never happen *)
         end).

  Add Parametric Morphism: O.build_flds with signature (Dico.Equal ==> Dico.Equal) as build_flds_morphism.
    intros x y H.
    unfold O.build_flds.
    setoid_rewrite H.
    apply  Dicomore.F.Equal_refl.
  Qed.
  (*
  Lemma build_flds_no_vref:forall t i x, FIND i (build_flds t) <> Some x.
  Proof.
    intros t.
    pattern t.
    apply  Dicomore.map_induction_bis;simpl;intros.          
    setoid_rewrite <- H.
    apply H0.
    vm_compute.
    intro abs; discriminate abs.
    unfold O.build_flds.
    rewrite Dicomore.add_map.
    destruct (Dico.E.eq_dec i x);simpl in *; subst.
    rewrite Dicofacts.add_eq_o;auto.
    destruct e;simpl;intro;discriminate.

    rewrite Dicofacts.add_neq_o;auto.
  Qed.
   *)

  (** [new cldefs clid heap] vérifie que clid existe bien, puis retourne une
    reference [r] un nouveau [Heap] [h] et telle que [heap(r) = None] et [h(r) =
    Some(o)] où [o] est un objet "frais" et toutes les adresses de [heap] sont
    identiques dans [h]. *)
  Function new (clid:class_id) (heap:Heap) : option (heap_idx * Heap) :=
    match Dico.find clid allcl with
    | None => None (** Classe inconnue *)
    | Some cldef =>
      let flds:Obj := {| objclass := clid; objfields := build_flds cldef |} in
      let newhpidx: nat := maxkey heap in
      Some((S newhpidx), Dico.add (S newhpidx) flds heap)
    end.


  Lemma new_one_change : forall clid hp hpidx newhp,
      new clid hp = Some (hpidx, newhp) ->
      forall idx,
        FIND idx newhp = FIND idx hp \/ idx=hpidx.
  Proof.
    intros clid hp.
    !functional induction new clid hp;intros;simpl;try solve [discriminate].
    inversion heq_Some;clear heq_Some;subst.
    destruct (Dico.E.eq_dec idx (S (maxkey hp)));simpl.
    - right;auto.
    - rewrite Dicomore.add_neq_o;auto.
  Qed.


  Lemma build_flds_empty :  Dico.Equal (build_flds Dico.empty) Dico.empty.
  Proof.
    unfold build_flds.
    apply Dicomore.empty_map.
  Qed.

  (** * Fonction d'exécution offensive d'*un* bytecode *)

  (** Pas de vérif de overflow. pas de nb négatifs. *)
  Definition exec_step (s:State): option State :=
    let frm:Frame := s.(frame) in
    let pc: pc_idx := frm.(pc) in
    let instr_opt := Dico.find pc (frm.(mdef).(instrs)) in
    match instr_opt with
    | None => None
    | Some instr =>
      match instr with
      | ret => Some s
      | Iconst i =>
        Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            pc:= pc + 1;
                            stack:= i :: s.(frame).(stack)
                         |}
             |}
      | Iadd =>
        match s.(frame).(stack) with
        | i1 :: i2 :: stack' =>
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= (i1+i2) :: stack'
                           |}
               |}
        | nil | _ :: nil => None (** Stack underflow *)
        end

      | Iload ridx =>
        match Dico.find ridx (s.(frame).(regs)) with
        | Some i =>
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef); regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= i :: s.(frame).(stack)
                           |}
               |}
        | None => None (** Bad register number *)
        end

      | Rload clid ridx =>
        match Dico.find ridx (s.(frame).(regs)) with
        | Some r =>
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= pc + 1;
                              stack:= r :: s.(frame).(stack)
                           |}
               |}
        | None => None (** Bad register number *)
        end

      | Istore ridx =>
        match s.(frame).(stack) with
        | i :: stack' =>
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ;
                              regs:= Dico.add ridx i (s.(frame).(regs));
                              pc:= pc + 1;
                              stack:= stack'
                           |}
               |}
        | nil => None (** Stack underflow *)
        end

      | Rstore clid ridx =>
        match s.(frame).(stack) with
        | i :: stack' =>
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ;
                              regs:= Dico.add ridx i (s.(frame).(regs));
                              pc:= pc + 1;
                              stack:= stack'
                           |}
               |}
        | nil => None (** Stack underflow *)
        end

      | Iifle jmp => (** ifeqe *)
        match s.(frame).(stack) with
        | 0 :: stack' => (** = 0  --> jump *)
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= jmp;
                              stack:= stack'
                           |}
               |}
        | _ :: stack' => (** <> 0  --> pc+1 *)
          Some {| framestack := s.(framestack); heap := s.(heap);
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              pc:= pc+1;
                              stack:= stack'
                           |}
               |}
        | nil => None (** Stack underflow *)
        end

      | Goto jmp =>
        Some {| framestack := s.(framestack); heap := s.(heap);
                frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                            stack:= s.(frame).(stack);
                            pc:= jmp
                         |}
             |}

      | Getfield cl namefld typ =>
        match s.(frame).(stack) with
        | hpidx :: stack' =>
          match Dico.find hpidx s.(heap) with
          | None => None (** adresse inconnue *)
          | Some {|objclass:= objcl; objfields:= flds |} => (* TODO: vérifier le type retourné? *)
            match Dico.find namefld flds with
            | None => None (** Champ de classe inconnu ou pas initialisé *)
            | Some v =>
              Some {| framestack := s.(framestack); heap := s.(heap);
                      frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                                  pc:= pc+1;
                                  stack:= v :: stack'
                               |}
                   |}
            end
          end
        | nil => None (** Stack underflow *)
        end

      | Putfield cl namefld typ =>
        match s.(frame).(stack) with
        | hpidx :: v :: stack' =>
          match Dico.find hpidx s.(heap) with
          | None => None (** adresse inconnue, objet non alloué *)
          | Some {| objclass:= objcl; objfields:= flds |}=>
            let newflds := {| objclass:= objcl;
                              objfields:=Dico.add namefld v flds |} in
            let newheap := Dico.add hpidx newflds s.(heap) in
            Some {| framestack := s.(framestack);
                    heap := newheap;
                    frame := {| mdef:=s.(frame).(mdef) ;
                                regs:= s.(frame).(regs);
                                pc:= pc+1;
                                stack:= stack'
                             |}
                 |}
          end
        | nil | _ :: nil => None (** Stack underflow *)
        end

      | New clid =>
        match new clid s.(heap) with
        | None => None (** Classe inconnue *)
        | Some (newobj,newhp) =>
          Some {| framestack := s.(framestack); heap := newhp;
                  frame := {| mdef:=s.(frame).(mdef) ; regs:= s.(frame).(regs);
                              stack:= newobj :: s.(frame).(stack);
                              pc:= pc+1
                           |}
               |}

        end
      end
    end.

  Functional Scheme exec_step_ind := Induction for exec_step Sort Prop.

  (** * Tests *)

  Notation "k --> i , d" := (Dico.add k i d) (at level 55, right associativity).


  Definition prog:MethodDef :=
    {| instrs := (0 --> Iload 1 ,
                  1 --> Istore 2 ,
                  2 --> ret ,
                  Dico.empty) ;
       argstype :=(Tint :: Tint:: nil);
       restype := Tint |}.

  Definition startstate:State :=
    {|
      framestack := nil;
      heap := Dico.empty ;
      frame := {|
                mdef:= prog ;
                regs:= (0 --> 32 , 1--> 11, Dico.empty);
                pc:= 0;
                stack:= nil
              |}
    |}.

  Fixpoint exec_n (s : State) (n:nat) {struct n}: option State :=
    match n with
    | 0 => Some s
    | S n' =>
      match exec_step s with
      | None => None
      | Some s' => exec_n s' n'
      end
    end.
  (*
    Eval simpl in exec_n startstate 1.
    Eval simpl in exec_n startstate 2.
    Eval simpl in exec_n startstate 5.
   *)
  (* Eval simpl in exec_n (fun x y => false) (Dico.empty _) startstate 2. *)


  (** Exemple de preuve très simple sur la fonction d'exécution *)

  Lemma essai : forall s x,
      exec_step s = Some x ->
      x.(framestack) = s.(framestack).
  Proof.
    intros s.
    functional induction exec_step s;intros ;simpl;
      try solve [discriminate | inversion H; subst;simpl;reflexivity] .
  Qed.


End O.


