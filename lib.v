Require Import FMapList.
Require Import Omega.
Require FMapFacts.
Require Import Relations.
Require Import OrderedType OrderedTypeEx OrderedTypeAlt.
Require Import DecidableType DecidableTypeEx.

(** Un module pour regrouper les propriétés sur les maps. On met tout
    ce qu'il y a dans WProperties et WFacts + qq propriétés
    supplémentaires prouvées ci-dessous. Voir à la fin du fichier pour
    le module Dico qui servira partout dans ce développement. *)
Module MoreMaps (Dico:FMapInterface.S).

  (** Toutes celles de la lib standard... *)
  Include FMapFacts.WProperties(Dico).
  Include FMapFacts.WFacts(Dico).
  
  Import Dico.
  Arguments empty {elt}.

  (** Plus quelques autres. *)
  Lemma Empty_eq: forall (elt : Type) (x y : t elt),
      Empty x -> Empty (elt:=elt) y -> Equal x y.
  Proof.
    intros elt x y H H0.
    red.
    intros y0.
    red in H.
    red in H0.
    destruct_with_eqn (find y0 x).
    - rewrite <- find_mapsto_iff in Heqo.
      destruct (H _ _ Heqo).
    - destruct_with_eqn (find y0 y).
      rewrite <- find_mapsto_iff in Heqo0.
      + destruct (H0 _ _ Heqo0).
      + reflexivity.
  Qed.

  Lemma Empty_eq_empty:
    forall (elt : Type) (x : t elt),
      Empty x
      ->   Equal x empty .
  Proof.
    intros elt x H.
    apply Empty_eq.
    - assumption.
    - apply empty_1.
  Qed.

  Lemma add_map : forall A B k (x:A) l (f:A -> B),
    Equal
    (map f (add k x l))
    (add k (f x) (map f l)).
  Proof.
    unfold Equal.
    intros A B k x l f y.
    setoid_rewrite map_o.
    setoid_rewrite add_o.
    rewrite map_o.
    destruct (E.eq_dec k y);subst;auto.
  Qed.


  Lemma add_map2 : forall A B k (x:A) l (f:A -> B) P,
    (forall m m' : t B, Equal m m' -> P m -> P m') -> 
    P(map f (add k x l)) -> 
    P(add k (f x) (map f l)).
    intros A B k x l f P h h'.
    apply h with (m:=(map f (add k x l))).
    - apply add_map.
    - assumption.
  Qed.


  Lemma empty_map : forall A B (f:A -> B),
      Equal (map f empty) empty.
  Proof.
    intros A B f.
    unfold Equal.
    intros y.
    rewrite empty_o, map_o, empty_o;auto.
  Qed.

  Lemma Equiv_refl_Equal : forall elt (Req:elt -> elt -> Prop) (Req_refl:reflexive _ Req) (m m' : t elt),
      Equal m m' -> Equiv Req m m'.
  Proof.
    intros elt Req Req_refl m m' H.
    red.
    split.
    - intros k.
      red in H.
      specialize (H k).
      red;split;red;intros; red in H0; destruct H0.
      + exists x.
        rewrite  find_mapsto_iff in H0.
        rewrite H0 in H.
        apply find_2.
        auto.
      + exists x.
        rewrite  find_mapsto_iff in H0.
        rewrite H0 in H.
        apply find_2.
        auto.
    - intros k e e' H0 H1.
      red in H.
      specialize (H k).
      rewrite  find_mapsto_iff in H0.
      rewrite  find_mapsto_iff in H1.
      rewrite H0 in H.
      rewrite H1 in H.
      inversion H.
      apply Req_refl.
  Qed.

End MoreMaps.




(** * [Dico]et [Dicomore] formalisent les maps (dictionnaires) ayant pour clés des [nat] et polymorphes sur les valeurs.

Il serviront pour représenter la mémoire, les programmes etc. *)

(* Les définitions et propriétés de base sont dans [Dico]. *)
Module Dico:=Make(Nat_as_OT).

(** Tout le reste (définition supplémentaire et très nombreuses
propriétés) est dans [Dicomore]. *)
Module Dicomore:=MoreMaps(Dico).

(** Une notation plus compacte pour find. *)
Notation FIND := (@Dico.find _).

(** Ce qui suit est spécifique à Dico car utilise le fait que les clés
    sont des entiers. *)

(** * Génération de clés <<fraîches>>. *)

(** Fonction auxiliaire: retourne le plus grand index utilisé dans [hp]. Permet
    de retourner un index "frais" dans la suite. *)
Definition maxkey {A} (hp:(Dico.t A)) :=
  Dico.fold
    (fun k e acc => if (Compare_dec.lt_dec acc k) then k else acc) hp 0.

(** Propriété basique de maxkey: l'index retourné est bien "frais". *)
Lemma maxkey_correct : forall A (h:Dico.t A) k, k>(maxkey h) -> 
  ~Dico.mem k h = true.
Proof.
  intros A h k.
  unfold maxkey.
  pattern h ,
    (Dico.fold
      (fun (k0 : Dico.key) (_ : A) (acc : nat) =>
        if Compare_dec.lt_dec acc k0 then k0 else acc) h 0).
  apply Dicomore.fold_rec;intros;intro.
  - assert (ass:Dico.Equal m Dico.empty).
    + apply Dicomore.Empty_eq_empty.
      assumption.
    + setoid_rewrite ass in H1.
      setoid_rewrite Dicomore.empty_a in H1.
      discriminate.
  - red in H1.
    setoid_rewrite (Dicomore.mem_find_b) in H4.
    setoid_rewrite H1 in H4.
    setoid_rewrite <- (Dicomore.mem_find_b) in H4.
    setoid_rewrite (@Dicomore.F.add_neq_b _ m' k0 k e) in H4.
    + apply H2;try assumption.
      destruct (Compare_dec.lt_dec a k0);omega.
    + destruct (Compare_dec.lt_dec a k0);omega.
Qed.


(* Nommage eutomatique d'hypothèses: *)
Ltac rename_lib h th :=
  match th with
  | List.In ?x ?l => fresh "inL_" x "_" l
  | List.In ?x ?l => fresh "inL_" x
  | List.In ?x ?l => fresh "inL"
  end.
