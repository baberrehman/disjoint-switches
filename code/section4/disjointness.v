(*

-> Section 4 in paper
-> Union Types + Null + Intersection Types
-> Nominal types
-> Subtyping Distributivity

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Metalib.FSetExtra.
Require Import Metalib.FSetWeakNotin.
Require Import Coq.MSets.MSets.
Require Import Metalib.CoqMSetDecide.
Require equivalence.
Require typing.

Module Typ.

  Export equivalence.

  Definition eq_dec : forall x y : typ, {x = y} + {x <> y}.
  Proof.
    repeat decide equality.
  Defined.

  Definition t := typ.

  Include HasUsualEq <+ UsualIsEq <+ UsualIsEqOrig.

End Typ.

(* Automatically unfold Typ.eq *)
Global Arguments Typ.eq /.

(** Finite sets of types *)
Module Import TypSetImpl : FSetExtra.WSfun Typ :=
  FSetExtra.Make Typ.

Notation types :=
  TypSetImpl.t.

(** The [TypSetDecide] module provides the [fsetdec] tactic for
    solving facts about finite sets of atoms. *)

Module Export TypSetDecide := Coq.FSets.FSetDecide.WDecide_fun Typ TypSetImpl.

(** The [TypSetNotin] module provides the [destruct_notin] and
    [solve_notin] for reasoning about non-membership in finite sets of
    atoms, as well as a variety of lemmas about non-membership. *)

Module Export TypSetNotin := FSetWeakNotin.Notin_fun Typ TypSetImpl.

(** Given the [fsetdec] tactic, we typically do not need to refer to
    specific lemmas about finite sets.  However, instantiating
    functors from the FSets library makes a number of setoid rewrites
    available.  These rewrites are crucial to developments since they
    allow us to replace a set with an extensionally equal set (see the
    [Equal] relation on finite sets) in propositions about finite
    sets. *)

Module TypSetFacts := FSetFacts.WFacts_fun Typ TypSetImpl.
Module TypSetProperties := FSetProperties.WProperties_fun Typ TypSetImpl.

Export TypSetFacts.
Export Typ.
(******************************************************************************)
Notation "{{ }}" := empty (at level 0, only parsing).
Notation "{{ x }}" := (singleton x) (at level 0, only parsing).

Notation "E \union F" := (union E F)
  (at level 65, right associativity, format "E \union '/' F").
Notation "E \u F" := (E \union F).

Notation "E \inter F" := (inter E F)
                      (at level 65, right associativity, format "E  \inter  '/' F").

Notation "PG ||= A <: B" := (declarative_subtyping PG A B) (at level 80).

#[export] Hint Extern 1 => match goal with
                 | H: wft nil (t_prim _) |- _ => inverts H
                           end : FalseHd.

#[export] Hint Resolve FSetDecideTestCases.test_In_singleton union_2 union_3 inter_3 : core.

Local Ltac inter_inv H := forwards : inter_1 H; forwards : inter_2 H; clear H.

Local Ltac union_inv H := forwards [?|?]: union_1 H; clear H.
Local Ltac single_inv H := let Heq := fresh "Heq" in
                           forwards Heq: singleton_1 H; try injects Heq; subst; clear H.

#[export] Hint Extern 1 => match goal with
                 | H : In _ empty |- _ => false; applys notin_empty_1 H
                 | H : In _ (singleton _ ) |- _ => single_inv H; fail
                 end : FalseHd.

(****************************************)
(**********  FindSubtypes    ************)
(****************************************)

(* issupertype returns true if A <: B under l *)
(* and false otherwise *)
(* It works for the transitive closure *)
(* It works for supertypes having multiple unrelated subtypes *)
Function issupertype (l: envp) (A B: var) : bool :=
    match l with
    | nil => false
    | (i, t) :: xs => match A==i with
                      | left _ => match t with
                                  | t_top => false
                                  | t_prim t' => match B==t' with
                                                 | left _ => true
                                                 | right _ => issupertype xs t' B
                                                 end
                                  | _ => false
                                  end
                     | right _ => issupertype xs A B
                    end
    end.

Function get_all_subtypes (l : envp) (A : var) : types :=
  match l with
  | nil => {{ }}
  | (i, t) :: xs => match (issupertype l i A) with
                      | true  => {{ t_prim i }} \union (get_all_subtypes xs A)
                      | false => get_all_subtypes xs A
                      end
  end.

Function all_prim_types (l : envp) : types :=
  match l with
  | nil => {{ }}
  | (i, t) :: xs => {{ t_prim i }} \union (all_prim_types xs)
  end.

(* Find Least Ordinary Subtypes (LOS) *)

Fixpoint FindSubtypes (PG:envp) (A: typ) : types :=
    match A with
    | t_top         =>  {{ t_int }} \u {{ t_arrow t_top t_bot }} \u {{ t_unit }}
                        \u (all_prim_types PG)
    | t_bot         => {{ }}
    | t_arrow A1 B1 => {{ t_arrow t_top t_bot }}
    | t_union A1 B1 => (FindSubtypes PG A1) \u (FindSubtypes PG B1)
    | t_and A1 B1   => (FindSubtypes PG A1) \inter (FindSubtypes PG B1)
    | t_prim i      => {{ t_prim i }} \u (get_all_subtypes PG i)
    | _ => {{ A }}
    end.

(***********************************)
(****  FindSubtypes Properties  ****)
(***********************************)

Lemma is_supertype_in_domain : forall G n A,
  issupertype G n A = true -> n `in` dom G.
Proof with solve_false.
  introv Heq.
  induction G...
  destruct a.
  unfold issupertype in Heq.
  case_if.
  destruct t0...
  - case_if; subst; rewrite dom_cons; eauto.
  - rewrite dom_cons. forwards* : IHG Heq.
Qed.

Lemma is_supertype_weakening : forall p G n1 n2,
  issupertype G n1 n2 = true ->
  okenvp (p :: G) ->
  issupertype (p :: G) n1 n2 = true.
Proof.
  introv Hsup Ok.
  destruct p.
  unfolds.
  case_if.
  - forwards:  is_supertype_in_domain Hsup.
    apply okenvp_uniq in Ok. inverts Ok.
    subst. solve_false.
  - assumption.
Qed.

Lemma prim_type_in_all_prim_types : forall (A : typ) PG,
  In A (all_prim_types PG) ->
  exists i, A = t_prim i.
Proof with solve_false.
  introv H.
  induction PG; simpl in H; solve_false.
  - destruct a. repeat case_if...
    union_inv H.
    + single_inv H0. now eauto.
    + applys~ IHPG.
Qed.

Lemma prim_type_in_all_subtypes : forall (A : typ) PG n,
  In A (get_all_subtypes PG n) ->
  exists i, A = t_prim i.
Proof with solve_false.
  introv H.
  induction PG; simpl in H; solve_false.
  - destruct a. repeat case_if...
    + destruct* t0...
      case_if; subst...
      * union_inv H; subst.
        ** single_inv H0; subst*.
        ** applys~ IHPG.
      * union_inv H; subst.
        ** single_inv H0. now eauto.
        ** applys~ IHPG.
    + applys~ IHPG.
Qed.

Local Ltac prim_inv_1 H := let Heq := fresh "Heq" in
                           forwards (?&Heq): prim_type_in_all_prim_types H; try injects Heq; subst.

Local Ltac prim_inv_2 H := let Heq := fresh "Heq" in
                           forwards (?&Heq): prim_type_in_all_subtypes H; try injects Heq; subst.

Local Ltac auto_in_inv :=
  match goal with
  | H: In _ _ |- _ => union_inv H + single_inv H + inter_inv H
                      + prim_inv_1 H + prim_inv_2 H; clear H
  end.

Lemma arrow_in_top_bot : forall PG A B C,
    In (t_arrow A B) (FindSubtypes PG C) ->
    t_arrow A B = t_arrow t_top t_bot.
Proof with solve_false.
  introv H.
  induction C; simpl in H; repeat auto_in_inv; solve_false; eauto.
Qed.

Local Ltac arrow_inv H := let Heq := fresh "Heq" in
                          forwards Heq: arrow_in_top_bot H; try injects Heq; subst.

Lemma prim_in_all : forall PG i,
    wft PG (t_prim i) -> In (t_prim i) (all_prim_types PG).
Proof.
  introv Wf.
  induction PG; simple.
  - inverts Wf. solve_false.
  - destruct a. case_eq (a==i); intros; subst*.
    apply wft_strenthen_prim in Wf; eauto.
Qed.

Lemma get_all_subtypes_subset : forall PG i j A,
    (get_all_subtypes PG i) [<=] (get_all_subtypes ((j, A) :: PG) i).
Proof.
  introv. gen i j.
  induction PG; intros; eauto.
  now simpl; repeat case_if; fsetdec.
  destruct a; simpl; repeat case_if; fsetdec.
Qed.

Lemma prim_in_subtypes_issuprtype: forall i PG j,
    In (t_prim i) (get_all_subtypes PG j) -> okenvp PG ->
    issupertype PG i j = true.
Proof with solve_false.
  introv Hin Ok.
  induction PG; simpl in Hin...
  destruct a.
  repeat case_if.
  - destruct t0; simpl in C...
    case_if; subst.
    + auto_in_inv.
      * auto_in_inv. simpl; repeat case_if; eauto.
      * forwards: IHPG H. inverts* Ok. rewrite* is_supertype_weakening.
    + simpl. repeat case_if; eauto.
      union_inv Hin.
      * false. apply C2. auto_in_inv...
      * applys~ IHPG. inverts~ Ok.
  - rewrite* is_supertype_weakening.
Qed.

Lemma prim_in_subtype : forall PG i j,
    declarative_subtyping PG (t_prim i) (t_prim j) ->
    In (t_prim i) (singleton (t_prim j) \u get_all_subtypes PG j).
Proof.
  introv Sub.
  apply dsub2asub in Sub. gen i j.
  induction PG; intros; inverts Sub; solve_false.
  - eauto.
  - forwards: IHPG H5.
    lets: get_all_subtypes_subset PG j i0 A.
    fsetdec.
  - forwards: IHPG H4.
    union_inv H.
    + auto_in_inv. simpl.
      case_eq (i==i); solve_false; intros.
      case_eq (j0==j0); solve_false; intros.
      eauto.
    + forwards* : prim_in_subtypes_issuprtype H0.
      simpl.
      repeat (case_if; solve_false; intros; eauto).
Qed.


Lemma okenvp_wft_inv : forall PG i A,
    okenvp ((i, A) :: PG) -> wft PG A.
Proof.
  introv Ok. inverts~ Ok.
Qed.

#[export] Hint Resolve okenvp_wft_inv : core.

Lemma in_prim_types_wft : forall PG A,
    okenvp PG ->
    In A (all_prim_types PG) -> wft PG A.
Proof.
  introv okp HIn. gen A.
  induction PG; intros; simpl in HIn.
  - solve_false.
  - destruct a. union_inv HIn.
    + auto_in_inv. now eauto.
    + eauto using wf_typ_weakening.
Qed.


Lemma get_all_subtypes_subset_all_prim : forall PG i,
    (get_all_subtypes PG i) [<=] (all_prim_types PG).
Proof.
  intros. induction PG; simpl; try fsetdec.
  - destruct a.
    1: repeat case_if.
    all: fsetdec.
Qed.

Lemma wft_prim_in_all_prim : forall PG i,
    wft PG (t_prim i) -> In (t_prim i) (all_prim_types PG).
Proof.
  introv Wf.
  inductions Wf.
  induction PG; solve_false.
  destruct a. forwards [ (?&?) | ? ]: binds_cons_1 H.
  - subst. simpl. eauto.
  - simpl. forwards* : IHPG H0.
Qed.

Lemma in_get_all_subtypes_wft : forall PG A i,
    okenvp PG ->
    In A (get_all_subtypes PG i) -> wft PG A.
Proof.
  introv okp HIn.
  lets HIn': get_all_subtypes_subset_all_prim HIn.
  lets~ : in_prim_types_wft PG A HIn'.
Qed.

#[export] Hint Immediate in_prim_types_wft in_get_all_subtypes_wft : core.


Lemma in_findsubtypes_wft : forall PG A B,
    okenvp PG ->
    In A (FindSubtypes PG B) -> wft PG B -> wft PG A.
Proof.
  introv okp HIn. gen A B.
  induction PG; intros.
  - induction B; simpl in HIn.
    all: try solve [repeat auto_in_inv; solve_false; eauto].
  - destruct a. induction B; simpl in HIn.
    all: try solve [repeat auto_in_inv; solve_false; eauto using wf_typ_weakening].
    repeat union_inv HIn.
    + auto_in_inv. eauto.
    + repeat union_inv H0; try solve [auto_in_inv; eauto].
      repeat union_inv H1; try solve [auto_in_inv; eauto].
      repeat union_inv H0; try solve [auto_in_inv; eauto].
      applys* wf_typ_weakening.
      apply okenvp_inv in okp.
      applys* in_prim_types_wft.
Qed.

#[export] Hint Immediate in_findsubtypes_wft : core.

Lemma wft_prim_inv : forall i n A PG,
  wft ((i, A) :: PG) (t_prim n) -> i=n \/ wft PG (t_prim n).
Proof.
  introv Wf.
  lets: wft_strenthen_prim Wf.
  case_eq (i==n); intros; subst*.
Qed.


Lemma FindSubtypes_subset_prim : forall PG n,
    wft PG (t_prim n) -> FindSubtypes PG (t_prim n) [<=] FindSubtypes PG t_top.
Proof.
  introv Wf. gen n.
  induction PG; intros.
  - solve_false.
  - lets: get_all_subtypes_subset_all_prim PG n.
    destruct a. forwards [?|?]: wft_prim_inv Wf; subst.
    + simpl. repeat case_if. destruct t0; solve_false. all: fsetdec.
    + forwards ~: wft_prim_in_all_prim PG n.
      simpl. repeat case_if. all: fsetdec.
Qed.

Lemma FindSubtypes_subset : forall PG A,
    wft PG A -> FindSubtypes PG A  [<=]  FindSubtypes PG t_top.
Proof.
  introv Wf.
  induction A; try solve [simpl; fsetdec].
  - inverts_all_wft.
    remember (FindSubtypes PG t_top) as Set1.
    forwards~ : IHA1. forwards~ : IHA2.
    simpl. fsetdec.
  - inverts_all_wft.
    remember (FindSubtypes PG t_top) as Set1.
    forwards~ : IHA1. forwards~ : IHA2.
    simpl. fsetdec.
  - applys~ FindSubtypes_subset_prim.
Qed.
#[export] Hint Resolve DS_refl DS_top DS_bot DS_arrow DS_or DS_orl DS_orr : core.


Lemma is_supertype_sound : forall G n1 n2,
  issupertype G n1 n2 = true ->
  okenvp G ->
  declarative_subtyping G (t_prim n1) (t_prim n2).
Proof.
  introv Heq Ok. gen n1 n2.
  induction G; intros; simpl in Heq; solve_false.
  destruct a. repeat case_if.
  - destruct t0; simpl; subst; solve_false.
    case_if; subst.
    + applys* DS_prim.
    + forwards*: IHG.
      applys DS_trans. now applys* DS_prim.
      applys dsub2asub. applys~ algo_sub_weakening. applys~ dsub2asub.
  - forwards*: IHG.
    applys dsub2asub. applys~ algo_sub_weakening. applys~ dsub2asub.
Qed.

Lemma issupertype_wft : forall PG i n,
    issupertype PG i n = true -> okenvp PG -> wft PG (t_prim n).
Proof.
  intros.
  forwards~: is_supertype_sound H.
  apply dsub2asub in H1. applys* algo_sub_wft.
Qed.

Lemma in_get_all_subtypes_wft_prim : forall B PG n,
    In B (get_all_subtypes PG n) -> okenvp PG -> wft PG (t_prim n).
Proof.
  introv HIn Ok. gen B.
  induction PG; intros; simpl in HIn; solve_false.
  destruct a. case_eq (n==a); intros; subst*.
  applys~ wf_typ_weakening.
  repeat case_if.
  - destruct t0; simpl; solve_false.
    case_if; intros; subst.
    + inverts~ Ok.
    + inverts~ Ok. applys* issupertype_wft.
  - apply okenvp_inv in Ok.
    forwards~ : IHPG Ok HIn.
Qed.

(******************************************************************************)
Import typing. (* for the definition of Ord *)

#[export] Hint Extern 1 => match goal with
                 | H: typing.Ord _ |- _ => inverts H; fail
end : FalseHd.

Lemma sub_and : forall PG A B C,
    declarative_subtyping PG A (t_and B C) ->
    (declarative_subtyping PG A B) /\ (declarative_subtyping PG A C).
Proof.
  intros.
  forwards Sub: H. apply dsub2asub in Sub. apply algo_sub_wft in Sub. destruct_conj.
  split; applys DS_trans H.
  applys* DS_andl.
  applys* DS_andr.
Qed.

(* Completeness of LOS *)

(* Lemma 20 *)

Lemma ord_in_findsubtypes : forall A PG B,
    Ord A -> declarative_subtyping PG A B ->
    In A (FindSubtypes PG B) \/
    (exists t1 t2, A = t_arrow t1 t2 /\ In (t_arrow t_top t_bot) (FindSubtypes PG B)).
Proof with destruct_conj; subst; simpl; auto; solve_false.
  introv Ord Sub. gen PG B.
  induction Ord; intros...
    (*int case*)
  - induction B...
   + apply ord_sub_or_unique in Sub...
     destruct Sub.
    * destruct IHB1...
    * destruct IHB2...
   + apply sub_and in Sub. destruct Sub.
     * destruct IHB1...
       destruct IHB2...
    (*arrow case*)
  - induction B...
   + right. exists* t1 t2.
   + right. exists* t1 t2.
   + apply ord_sub_or_unique in Sub...
     destruct Sub.
     * destruct IHB1... injects* H0.
       right. exists* x x0. 
     * destruct IHB2... injects* H0.
       right. exists* x x0.
   + apply sub_and in Sub. destruct Sub.
     * destruct~ IHB1; try arrow_inv H1;
         destruct~ IHB2; try arrow_inv H2...
       injects H1. injects* H2.
       right. exists* x x0.
    (*null case*)
  - induction B...
   + apply ord_sub_or_unique in Sub...
     destruct Sub.
    * destruct IHB1...
    * destruct IHB2...
   + apply sub_and in Sub. destruct Sub.
     * destruct IHB1...
       destruct IHB2...
    (*P case*)
  - induction B...
    + left*. assert (wft PG (t_prim i)).
      { apply dsub2asub in Sub. apply algo_sub_wft in Sub. tauto. }
      eauto using prim_in_all.
    + apply ord_sub_or_unique in Sub...
     destruct Sub.
      * destruct IHB1...
      * destruct IHB2...
    + apply sub_and in Sub. destruct Sub.
      * destruct~ IHB1; destruct~ IHB2...
    + apply prim_in_subtype in Sub.
      eauto.
Qed.

(* Soundness of LOS *)

(* Lemma 19 *)

Lemma elem_in_findsubtypes_sub : forall PG A B,
    okenvp PG ->
    wft PG A ->
    wft PG B ->
    In B (FindSubtypes PG A) -> declarative_subtyping PG B A.
Proof.
  introv Ok Wf1 Wf2 HIn.
  induction A.
  all: try solve [simpl in HIn; solve_false; auto_in_inv; eauto].
  - inverts_all_wft. simpl in HIn. union_inv HIn.
    now forwards* :IHA1; applys* DS_trans.
    now forwards* :IHA2; applys* DS_trans.
  - inverts_all_wft. simpl in HIn. inter_inv HIn.
    forwards* :IHA1. forwards* :IHA2.
    applys~ DS_and.
  - simpl in HIn. union_inv HIn.
    + auto_in_inv. eauto.
    + gen n. induction PG; intros; solve_false.
      destruct a.
      simpl in H. repeat case_if.
      * destruct t0; solve_false.
        assert (declarative_subtyping PG (t_prim n0) (t_prim n)). {
          case_if; subst; eauto using is_supertype_sound.
        }
        repeat union_inv H.
        ** auto_in_inv; eauto.
           applys DS_trans. applys~ DS_prim.
           applys dsub2asub. applys~ algo_sub_weakening. applys~ dsub2asub.
        ** applys dsub2asub. applys~ algo_sub_weakening. applys dsub2asub.
           applys* IHPG.
           apply in_get_all_subtypes_wft in H1; auto.
           apply okenvp_inv in Ok; auto.
           apply dsub2asub in H0. applys~ algo_sub_wft.
      * applys dsub2asub. applys~ algo_sub_weakening. applys dsub2asub.
        applys* IHPG.
        apply in_get_all_subtypes_wft in H; auto.
        apply okenvp_inv in Ok; auto.
        forwards [?|?]: wft_prim_inv Wf1; subst*.
        applys* in_get_all_subtypes_wft_prim.
Qed.

(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec PG A B := forall C, Ord C -> not (declarative_subtyping PG C (t_and A B)).
Notation "PG |- A *s B" := (DisjSpec PG A B) (at level 80).

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

Definition DisjAlgo PG A B := ((FindSubtypes PG (t_and A B))) [=] empty.
Notation "PG |- A *a B" := (DisjAlgo PG A B) (at level 80).

(* Disjointness Equivalence *)

(* Theorem 18 (a) *)

Lemma Disj_soundness : forall PG A B, PG |- A *a B -> PG |- A *s B.
Proof.
  intros.
  unfold DisjAlgo in H.
  unfold DisjSpec. unfold not. intros.
  forwards~ : ord_in_findsubtypes H0 H1.
  firstorder.
  1: rewrite H in H2.
  2: rewrite H in H3.
  all: solve_false.
Qed.

(* Theorem 18 (b) *)

Lemma Disj_completeness : forall PG A B,
  okenvp PG -> wft PG A -> wft PG B ->
  PG |- A *s B -> PG |- A *a B.
Proof.
  introv OK WFT1 WFT2 Disj.
  unfold DisjSpec in Disj. unfold not in Disj.
  unfold DisjAlgo.
  remember (t_and A B) as T. assert (WF: wft PG T) by subst*. clear WFT1 WFT2 HeqT.
  applys TypSetProperties.empty_is_empty_1.
  introv HIn.
  forwards~ Sub: FindSubtypes_subset PG T.
  forwards HIn2: TypSetProperties.in_subset HIn Sub.
  repeat auto_in_inv.
  all: applys Disj; [ | applys~ elem_in_findsubtypes_sub HIn];
    now eauto.
Qed.
