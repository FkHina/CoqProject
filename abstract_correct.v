Require Import OrderedType OrderedTypeEx OrderedTypeAlt DecidableType DecidableTypeEx.
Require Import RelationClasses.
Require Import List  bcv.LibHypsNaming bcv.lib.
Import ListNotations Omega.
From bcv Require Import heritage lib vmtype dvm avm.

Module Abstraite_correcte (H:Herit).

  Module D:= D(H).
  Module A:= A(H).
  Import H.
  Import DefVal.
  (* [s.frame] désigne par défaut [s.(D.Frame)], pour la vm abstraite, il faudra
     toujours mettre s.(A.frame) *)
  Import D.

  Ltac rename_abs_cor h th := fail.

  (* Hypothesis renaming stuff from other files + current file.
     DO NOT REDEFINE IN THIS FILE. Redefine rename_sparkprf instead. *)
  Ltac rename_hyp h th ::=
    match th with
    | _ => rename_abs_cor h th
    | _ => D.rename_dvm h th
    | _ => lib.rename_lib h th
    | _ => A.rename_avm h th
    | _ => LibHypsNaming.rename_hyp_neg h th
    end.


  (** * Les fonctions d'abstraction. *)

  Notation abstract_value := D.v2t.

  Definition abstract_regs rgs: A.Registers := Dico.map abstract_value rgs.

  Definition abstract_stack st: A.Stack := List.map abstract_value st.

  Definition abstract_state (s:D.State) : A.State :=
    let fr :=
        {| A.mdef := s.(frame).(mdef);
           A.regs := abstract_regs (s.(frame).(regs));
           A.stack := abstract_stack (s.(frame).(stack));
           A.pc:=s.(frame).(pc) |} in
    {| A.frame := fr;
       A.framestack := nil;
       A.heap := Dico.empty |}.

  (** Extention au type option de la fonction d'abstraction *)
  Notation abstract_opt_value := (option_map v2t).  
  Notation abstract_opt_state:= (option_map abstract_state).

  (** ** Preuve d'invariance par abstraction de certaines parties des états. *)

  Lemma pc_ok: forall s,  (s.(frame)).(pc) = (A.frame (abstract_state s)).(A.pc).
    destruct s;simpl;reflexivity.
  Qed.

  Lemma mdef_ok: forall s, D.mdef(s.(frame)) = A.mdef(A.frame(abstract_state s)).
  Proof.
    destruct s;simpl;reflexivity.
  Qed.

  (* commutation de find et abstract_ot_value *)
  Lemma find_abstract_ok : forall rgs ridx, 
    Dico.find ridx (abstract_regs rgs) 
    = abstract_opt_value (Dico.find ridx rgs).
  Proof.
    intros rgs ridx.
    apply Dicomore.map_o.
  Qed.


  

   (*PREUVE DE COMMUTATION:
   Lemma abstract_ok_final : forall(s s':D.State),
      safe s -> D.exec_step s = Some s' -> 
      safe s'
      /\ Incompat (Some (abstract_state s')) (A.exec_step (abstract_state s)).
   *)
   



End Abstraite_correcte.

