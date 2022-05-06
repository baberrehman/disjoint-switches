(*

-> Section 5.2 in paper
-> Union Types + Null + Intersection Types
-> Intersection introduction
-> Nominal types
-> A * B -> A & B <: Bottom
-> Generalized subtyping for empty types

*)

Require Import TLC.LibLN.
Require Import syntax.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.

(** definitions *)

(* defns value *)
Inductive value : exp -> Prop :=    (* defn value *)
 | val_int : forall i5,
     value (e_lit i5)
 | val_abs : forall e,
     lc_exp (e_abs e) ->
     value (e_abs e)
 | val_null :
     value e_null
 | val_new  : forall P,
     value  (e_new P).

(* defns FindType *)
Inductive findtype : exp -> typ -> Prop :=    (* defn findtype *)
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (e:exp),
     lc_exp (e_abs e) ->
     findtype  (e_abs e) (t_arrow t_top t_bot)
 | findtype_null :
     findtype e_null t_unit
 | find_type_new : forall P,
     findtype (e_new P) (t_prim P).

#[export]
Hint Constructors value findtype : core.

(* defns Typing *)
Reserved Notation "PG , G |- e : A" (at level 80, G at next level, e at next level).
Inductive typing (PG:envp) : env -> exp -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      okt  G  ->
      okenvp PG ->
      PG , G |- (e_lit i5) : t_int
 | typ_null : forall G,
      okt G ->
      okenvp PG ->
      typing PG G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      okt  G  ->
      okenvp PG -> wft PG A ->
      binds  x A G  ->
     typing PG G (e_var_f x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     okenvp PG -> wft PG A -> wft PG B ->
     typing PG G e1 (t_arrow A B) ->
     typing PG G e2 A ->
     typing PG G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing PG G e B ->
     PG |- B <: A ->
     typing PG G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      okenvp PG -> wft PG A -> wft PG B ->
      ( forall x , x \notin  L  -> typing PG  (G & x ~: A )   ( open_exp_wrt_exp e (e_var_f x) ) B )  ->
     typing PG G (e_abs e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     okenvp PG -> wft PG A -> wft PG B -> wft PG C ->
     typing PG G e (t_union A B) ->
     ( forall x , x \notin  L  -> typing PG (G & x ~: A )   ( open_exp_wrt_exp e1 (e_var_f x) ) C ) ->
     ( forall x , x \notin  L  -> typing PG (G & x ~: B )   ( open_exp_wrt_exp e2 (e_var_f x) ) C ) ->
     PG |- A *s B ->
     typing PG G (e_typeof e A e1 B e2) C
 | typ_inter : forall G e A B,
     okenvp PG -> wft PG A -> wft PG B ->
     typing PG G e A ->
     typing PG G e B ->
     typing PG G e (t_and A B)
 | typ_prim : forall i G,
    okt G ->
    okenvp PG -> wft PG (t_prim i) ->
     typing PG G (e_new i) (t_prim i)
where "PG , G |- e : A" := (typing PG G e A).

(* defns Reduction *)
Reserved Notation "PG |- e --> e'" (at level 80, e at next level).
Inductive step (PG: envp) : exp -> exp -> Prop :=    (* defn step *)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     PG |- e1 --> e1' ->
     PG |- (e_app e1 e2) --> (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     PG |- e --> e' ->
     PG |- (e_app v e) --> (e_app v e')
 | step_beta : forall (e:exp) (v:exp),
     lc_exp (e_abs e) ->
     value v ->
     PG |- e_app  (e_abs e) v --> (open_exp_wrt_exp e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     PG |- e --> e' ->
     PG |- (e_typeof e A e1 B e2) --> (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     sub PG C A ->
     PG |- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     sub PG C B ->
     PG |- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp  e2 v )
where "PG |- e --> e'" := (step PG e e') : env_scope.

#[export]
Hint Constructors typing step : core.

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let D := gather_vars_with (fun x : exp => fv_exp x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u D \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- sub _ ?E _ _  => E
  | |- typing _ ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; autos*.


(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
open_exp_wrt_exp_rec j v e = open_exp_wrt_exp_rec i u (open_exp_wrt_exp_rec j v e) ->
  e = open_exp_wrt_exp_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_ee_rec_term : forall u e,
  lc_exp e -> forall k, e = open_exp_wrt_exp_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e 0 (e_var_f x)).
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (e_var_f x)).
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e2 0 (e_var_f x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_exp e -> subst_exp u x e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, lc_exp u ->
subst_exp u x (open_exp_wrt_exp t1 t2) =
open_exp_wrt_exp (subst_exp u x t1) (subst_exp u x t2).
Proof.
  intros. unfold open_exp_wrt_exp. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> lc_exp u ->
  (subst_exp u x e) open_ee_var y = subst_exp u x (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_exp e -> lc_exp u ->
  open_exp_wrt_exp e u = subst_exp u x (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_ee_term : forall e1 Z e2,
lc_exp e1 -> lc_exp e2 -> lc_exp (subst_exp e2 Z e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
 - apply_fresh* lc_e_abs as y.
   rewrite* subst_ee_open_ee_var.
 - apply_fresh* lc_e_typeof as y.
   rewrite* subst_ee_open_ee_var.
   rewrite* subst_ee_open_ee_var.
Qed.

#[export]
Hint Resolve subst_ee_term : core.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1; auto.
Qed.

#[export]
Hint Extern 1 (ok _) => apply ok_from_okt : core.


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E x T,
  okt (E & x ~: T) -> okt E /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. autos.
Qed.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F:env),
  okt (E & x ~: T & F) ->
  okt (E & F).
Proof.
  introv O. induction F using env_ind.
  rewrite concat_empty_r in *. apply okt_push_inv in O. destruct~ O.
  rewrite concat_assoc in *.
  apply okt_push_inv in O.
  destruct O. apply IHF in H.
  apply okt_typ; autos*.
Qed.

(** Automation *)

#[export]
Hint Immediate okt_strengthen : core.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall PG E e T,
  typing PG E e T -> okt E /\ lc_exp e /\ okenvp PG /\ wft PG T.
Proof.
  induction 1; try splits*.
 - lets (?&WFT1&WFT2): subtyping_regular H0. auto.
 - pick_fresh y. specializes H3 y. destructs~ H3.
  apply okt_push_inv in H3. destruct~ H3.
 - apply lc_e_abs with (L:=L). intros.
  specializes H3 x. destructs~ H3.
 - apply lc_e_typeof with (L:=L); intros.
   destruct IHtyping. destruct~ H10.
   specialize (H5 x H9). destruct H5. destruct~ H10.
   specialize (H7 x H9). destruct H7. destruct~ H10.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> lc_exp t.
Proof.
  induction 1; autos*.
Qed.

#[export]
Hint Immediate value_regular : core.

(* ********************************************************************** *)
(** Weakening *)


Lemma typing_weakening : forall PG E F G e T,
   typing PG (E & G) e T ->
   okt (E & F & G) ->
   typing PG (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_null.
  - apply* typ_var. apply* binds_weaken.
  - eapply typ_app. auto. apply H0. auto. auto. auto.
  - apply* typ_sub.
  - eapply typ_abs with (L:=((((L \u fv_exp e) \u dom E) \u dom G) \u dom F)); intros; auto.
    forwards~: (H2 x).
    apply_ih_bind (H3 x); eauto.
  - eapply typ_typeof with (L:=(((((L \u fv_exp e) \u fv_exp e1) \u fv_exp e2) \u dom E) \u dom G) \u dom F); auto; intros.
    forwards~: (H3 x). apply_ih_bind (H4 x); eauto.
    forwards~: (H5 x). apply_ih_bind (H6 x); eauto.
  - apply* typ_inter.
  - apply* typ_prim.
Qed.

(************************************************************************ *)
(** Term Substitution preserves types *)

Require Import Program.Equality.

Lemma typing_through_subst_ee : forall PG E F x T e u U,
   typing PG (E & x ~: U & F) e T ->
   typing PG E u U ->
   typing PG (E & F) (subst_exp u x e) T.
Proof.
introv TypT TypU.
lets TypT': TypT.
inductions TypT; introv; simpl.
(*case int*)
 - apply* typ_lit.
 - (*case null*)
   apply* typ_null.
(*case var*)
 - case_var.
  + binds_get H2.
    lets M: (typing_weakening PG E F empty u U).
    do 2 rewrite concat_empty_r in M.
    apply* M.
  + binds_cases H2; apply* typ_var.
(*case app*)
 - eapply typ_app. auto. apply H0. auto.
   eapply IHTypT1; auto.
   eapply IHTypT2; auto.
(*case sub*)
 - eapply typ_sub. eapply IHTypT; auto. auto.
(*case abs*)
 - eapply typ_abs with (L:=((((L \u \{ x}) \u fv_exp u) \u fv_exp e) \u dom E) \u dom F); intros; auto.
   assert (x0 \notin L) by auto.
   rewrite~ subst_ee_open_ee_var.
   lets TEMP1: H3 x0 H5 E (F & x0 ~: A) x.
   lets TEMP2: TEMP1 U.
   forwards~ : (TEMP1); try solve [rewrite~ concat_assoc]. auto.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destruct TypU. destruct~ H7.
(*case typeof*)
 - eapply typ_typeof with (L:=((((((L \u \{ x}) \u fv_exp u) \u fv_exp e) \u fv_exp e1) \u fv_exp e2) \u
   dom E) \u dom F); intros; auto. eapply IHTypT; auto.
  + assert (x0 \notin L) by auto.
    rewrite~ subst_ee_open_ee_var.
    lets TEMP1: H4 x0 H9 E (F & x0 ~: A) x. lets TEMP2: TEMP1 U.
    forwards~: TEMP2; try solve [rewrite~ concat_assoc].
    rewrite~ <- concat_assoc.
    apply typing_regular in TypU. destruct TypU as [OK [LC _]]. auto.
  + assert (x0 \notin L) by auto.
    rewrite~  subst_ee_open_ee_var.
    lets TEMP1: H6 x0 H9 E (F & x0 ~: B) x. lets TEMP2: TEMP1 U.
    forwards~: TEMP2; try solve [rewrite~ concat_assoc].
    rewrite~ <- concat_assoc.
    apply typing_regular in TypU. destruct TypU as [OK [LC _]]. auto.
 - apply typ_inter; auto.
   eapply IHTypT1; auto.
   eapply IHTypT2; auto.
 - apply typ_prim; auto.
   apply okt_strengthen in H. auto.
Qed.


(* ********************************************************************** *)
(** Typing Inversion Properties *)

Lemma inv_int : forall PG E A i5,
typing PG E (e_lit i5) A -> typing PG E (e_lit i5) t_int /\ sub PG t_int A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - specialize (IHTyp i5).
  forwards*: IHTyp. destruct H0.
  split*.
  eapply sub_transitivity; eauto.
  - forwards*: IHTyp1. destruct H2.
    forwards*: IHTyp2.
Qed.

Lemma abs_typ_arrow_sub : forall PG G e A,
typing PG G (e_abs e) A ->
exists A1 B1, sub PG (t_arrow A1 B1) A.
Proof.
    introv Typ.
    inductions Typ.
    - lets* (OK&WFT1&WFT2): subtyping_regular H.
      forwards* (x1&x2&Sub): IHTyp. 
      exists x1 x2. eapply sub_transitivity; eauto.
    - exists* A B.
    - forwards* (x1&x2&Sub1): IHTyp1.
      forwards* (x3&x4&Sub2): IHTyp2.
      exists t_top t_bot.
      apply* s_anda.
      forwards* (?&WFT1&WFT2): subtyping_regular Sub1. inverts WFT1.
      assert (sub PG (t_arrow t_top t_bot) (t_arrow x1 x2)); eauto.
      eapply sub_transitivity; eauto.
      forwards* (?&WFT1&WFT2): subtyping_regular Sub2. inverts WFT1.
      assert (sub PG (t_arrow t_top t_bot) (t_arrow x3 x4)); eauto.
      eapply sub_transitivity; eauto.
Qed.

Lemma inv_and_arrow : forall PG G e A1 A2 B1 B2,
  typing PG G (e_abs e) (t_and A1 A2) ->
  sub PG (t_and A1 A2) (t_arrow B1 B2) ->
  sub PG A1 (t_arrow B1 B2) \/ sub PG A2 (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inverts Sub; eauto.
  apply abs_typ_arrow_sub in Typ; auto.
  destruct Typ as [A3 [A4]].
  apply (findsubtypes_empty_not_ord PG (t_and A1 A2) (t_arrow A3 A4)) in H; auto.
  false. apply H. auto.
  forwards*: subtyping_regular H3.
Qed.

Lemma inv_abs_sub : forall PG G e A B1 B2,
    typing PG G (e_abs e) A ->
    sub PG A (t_arrow B1 B2) ->
         exists C1 C2,
           (exists L, forall x , x \notin  L -> typing PG (G & x ~: C1) (e open_ee_var x) C2)
           /\ sub PG (t_arrow C1 C2) (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: sub PG B (t_arrow B1 B2)) by applys sub_transitivity H Sub.
    forwards* (?&?&?&?): IHTyp HS.
  - assert (Typ:(PG, G |- e_abs e : (t_and A B))) by auto.
    lets : inv_and_arrow G Typ Sub. destruct~ H2.
Qed.

Lemma inv_arrow : forall PG G e A1 A2,
    typing PG G (e_abs e) (t_arrow A1 A2) ->
    exists B1 B2, (exists L, forall x , x \notin  L -> typing PG (G & x ~: B1) (e open_ee_var x) B2)
                  /\ sub PG (t_arrow B1 B2) (t_arrow A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards*: inv_abs_sub H.
  - exists* A1 A2.
Qed.


Lemma inv_abs_union : forall PG G e A A1 A2,
    typing PG G (e_abs e) A ->
    sub PG A (t_union A1 A2) ->
    typing PG G (e_abs e) A1 \/ typing PG G (e_abs e) A2.
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - eapply sub_transitivity in Sub; eauto.
  - inverts Sub. clear H6 H7 H8 H3 H10. eauto. eauto.
    inverts H7.
  - inverts Sub; auto.
    clear H5 H6 H8. eauto.
    clear H5 H6 H8. eauto.
    assert (Typ:(PG, G |- e_abs e : (t_and A B))) by auto.
    apply abs_typ_arrow_sub in Typ.
    destruct Typ as [x1 [x2 Sub]].
    lets: ord_sub_findsubtypes_not_empty Sub. auto. contradiction.
Qed.


Lemma inv_null : forall PG E A,
typing PG E e_null A -> typing PG E e_null t_unit /\ sub PG t_unit A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - forwards*: IHTyp. destruct H0.
   split*.
   eapply sub_transitivity; eauto.
 - forwards*: IHTyp1.
Qed.

Lemma inv_P : forall PG E P A,
typing PG E (e_new P) A -> typing PG E (e_new P) (t_prim P) /\ sub PG (t_prim P) A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - forwards*: IHTyp. destruct H0.
   split*.
   eapply sub_transitivity; eauto.
  (*case typ_sub*)
 - forwards*: IHTyp1.
   forwards*: IHTyp2.
   forwards*: subtyping_regular H2.
 - split*.
Qed.

Lemma check_or_typ : forall PG E e A B,
   value e ->
   typing PG E e (t_union A B) ->
   typing PG E e A \/ typing PG E e B.
Proof.
  introv Val Typ.
  inverts Val.
  (*subsumption again*)
 - apply inv_int in Typ. destruct Typ.
   inverts H0. left*. right*. inverts H4.
 - inverts Typ.
   eapply inv_abs_union in H0; eauto.
 - apply inv_null in Typ. destruct Typ.
   inverts H0. left*. right*. inverts H4.
 - apply inv_P in Typ; auto. destruct Typ.
   inverts H0. left*. right*. inverts H4.
Qed.


Lemma val_check_disjoint_types : forall PG E v A B,
PG |- A *s B ->
value v ->
typing PG E v A ->
typing PG E v B -> False.
Proof.
  introv Disj Val Typ1 Typ2.
  unfold DisjSpec in Disj. unfold not in Disj.
  inverts Val.
  - apply inv_int in Typ1; auto. destruct Typ1.
    apply inv_int in Typ2; auto. destruct Typ2.
    forwards*(?&WFT1&WFT2): subtyping_regular H2.
    forwards*(?&WFT11&WFT21): subtyping_regular H0.
  - apply abs_typ_arrow_sub in Typ1; auto.
    destruct Typ1 as [A1 [B1]].
    lets (?&WFT1&WFT2): subtyping_regular H0. inverts WFT1.
    assert (sub PG (t_arrow t_top t_bot) (t_arrow A1 B1)); auto.
    apply abs_typ_arrow_sub in Typ2; auto.
    destruct Typ2 as [A2 [B2]].
    lets(?&WFT3&WFT4): subtyping_regular H3. inverts WFT3.
    assert (sub PG (t_arrow t_top t_bot) (t_arrow A2 B2)). auto.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A1 B1)) (C:=A) in H2; auto.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A2 B2)) (C:=B) in H7; auto.
    forwards*: Disj (t_arrow t_top t_bot).
  - apply inv_null in Typ1; auto. destruct Typ1.
    apply inv_null in Typ2; auto. destruct Typ2.
    lets(?&WFT1&WFT2): subtyping_regular H2.
    lets(?&WFT3&WFT4): subtyping_regular H0.
    forwards*: Disj t_unit.
  - apply inv_P in Typ1; auto. destruct Typ1.
    apply inv_P in Typ2; auto. destruct Typ2.
    lets(?&WFT1&WFT2): subtyping_regular H2.
    lets(?&WFT3&WFT4): subtyping_regular H0.
    forwards*: Disj (t_prim P).
Qed.

Lemma check_find_type : forall PG E e A B,
typing PG E e A ->
findtype e B ->
sub PG B A.
Proof.
  introv Typ Find.
  inductions Find.
  - apply inv_int in Typ; auto.
    destruct~ Typ.
  - apply abs_typ_arrow_sub in Typ; auto.
    destruct Typ as [A1 [B1]].
    lets(?&WFT1&WFT2): subtyping_regular H0. inverts WFT1.
    assert (sub PG (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
    eapply sub_transitivity; eauto.
  - apply inv_null in Typ; auto. destruct~ Typ.
  - apply inv_P in Typ; auto. destruct Typ. auto. 
Qed.

(*******************************)
(****  Preservation Lemma  *****)
(*******************************)

(* Theorem 7 *)

Lemma preservation : forall PG E e e' T,
  typing PG E e T ->
  PG |- e --> e' ->
  typing PG E e' T.
Proof.
  introv Typ. gen e'.
  inductions Typ; introv Red; try solve [ inverts Red ].
  - (* app *)
    inverts Red.
    eapply typ_app. auto. apply H0. auto.
    apply IHTyp1; auto. auto.
    eapply typ_app. auto. apply H0. auto. auto.
    apply IHTyp2. auto.
    (* beta *)
        forwards (A1&B1&TEMP1&Sub): inv_arrow Typ1.
        destruct TEMP1 as [L TEMP2].
        pick_fresh x.
        assert (NOTIN: (x \notin L)) by auto.
        lets TEMP3: TEMP2 x NOTIN.
        assert (EQ: (G & x ~: A1 = G & x ~: A1 & empty)).
        rewrite* concat_empty_r.
        rewrite EQ in TEMP3.
        assert (EQ2: (G = G & empty)).
        rewrite* concat_empty_r. rewrite EQ2.
        lets TEMP4: typing_through_subst_ee.
        inverts Sub.
        lets TEMP5: typ_sub Typ2 H13. clear Typ2.
        forwards: TEMP4 TEMP3 TEMP5.
        rewrite* (@subst_ee_intro x).
        inverts H7.
  - (*case subsumption*)
    inverts* Red.
  - (* typeof *)
    inverts Red. 
    + eapply typ_typeof with (L:=L); auto.
    + (* value checks against disjoint types *)
      lets temp1: check_or_typ PG G e A B.
      lets DisjOr: temp1 H15 Typ.
      destruct DisjOr.
     * (*true goal*)
       pick_fresh y. assert (NOTIN: (y \notin L)) by auto.
       forwards temp2: H3 NOTIN.
       assert  (EQ1: (G & y ~: A = G & y ~: A & empty)).
       rewrite* concat_empty_r. rewrite EQ1 in temp2.
       assert (temp3: (G = G & empty)).
       rewrite* concat_empty_r.
       rewrite temp3.
       lets temp4: typing_through_subst_ee PG temp2 H8.
       rewrite* (@subst_ee_intro y).
     * (*false goal, value e checks against disjoint types A and B*)
       lets temp2: check_find_type PG G e B C0.
       lets SubB: temp2 H8 H16.
       unfold DisjSpec in H7. unfold not in H7.
       destruct H16.
       forwards FF: H7 t_int; auto; inverts FF.
       forwards FF: H7 (t_arrow t_top t_bot); auto; inverts FF.
       forwards FF: H7 t_unit; auto; inverts FF.
       forwards (_&WFT&_) : subtyping_regular H17.
       forwards FF: H7 (t_prim P); auto; inverts FF.
    +  (* value checks against disjoint types *)
      lets temp: check_or_typ PG G e A B.
      lets DisjOr: temp H15 Typ.
      destruct DisjOr.
     * (*false goal, value e checks against disjoint types A and B*)
        lets temp1: check_find_type PG G e A C0.
        lets SubA: temp1 H8 H16.
        unfold DisjSpec in H7. unfold not in H7.
        destruct H16.
        forwards FF: H7 t_int; auto; inverts FF.
        forwards FF: H7 (t_arrow t_top t_bot); auto; inverts FF.
        forwards FF: H7 t_unit; auto; inverts FF.
        forwards (_&WFT&_): subtyping_regular SubA.
        forwards FF: H7 (t_prim P); auto; inverts FF.
     * (*true goal*)
        pick_fresh y. assert (NOTIN: (y \notin L)) by auto.
        forwards temp2: H5 NOTIN.
        assert  (EQ1: (G & y ~: B = G & y ~: B & empty)).
        rewrite* concat_empty_r. rewrite EQ1 in temp2.
        assert (EQ2: (G = G & empty)).
        rewrite* concat_empty_r.
        rewrite EQ2.
        lets : typing_through_subst_ee PG temp2 H8.
        rewrite* (@subst_ee_intro y).
    - forwards*: IHTyp1.
Qed.


(*******************************)
(******  Progress Lemma  *******)
(*******************************)

(* Theorem 8 *)

Lemma progress : forall PG e T,
typing PG empty e T -> (value e) \/ (exists e', PG |- e --> e').
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
(*case int*)
 - left*.
 (*case null*)
 - left*.
 (*case var*)
 - apply binds_empty_inv in H2. inversion H2.
 (*case typ-app*)
 - right. destruct* IHTyp1.
  + destruct* IHTyp2.
   * inverts* H2.
     (*false cases infers arrow*)
     apply inv_int in Typ1; auto.
     destruct Typ1 as [_ Sub].
     inverts Sub. inverts H6.
     apply inv_null in Typ1; auto.
     destruct Typ1 as [_ Sub].
     inverts Sub. inverts H6.
     apply inv_P in Typ1; auto. 
     destruct Typ1 as [_ Sub].
     inverts Sub. inverts H6.
     (*case step-appl*)
   * destruct H3 as [x temp1].
     exists* (e_app e1 x).
   (*case step-appr*)
  + destruct H2 as [x temp1].
    exists (e_app x e2). apply* step_appl.
    forwards*: typing_regular Typ2.
(*case typ-sub*)
 - destruct~ IHTyp.
(*case typ-abs*)
 - left. forwards*: typing_regular Typ'.
(*case typ-typeof*)
 - right. destruct* IHTyp.
  + apply check_or_typ in Typ; auto.
    destruct Typ.
    (*case typeofl*)
   * destruct H8.
     { (*case e = int*)
      apply inv_int in H9; auto. destruct H9.
      exists (open_exp_wrt_exp e1 (e_lit i5)).
      pick_fresh y.
      assert (NOTIN: (y \notin L)) by auto.
      lets: H3 y NOTIN.
      eapply step_typeofl with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H9; auto.
      destruct H9 as [A1 [B1]].
      lets(_&WFT1&_): subtyping_regular H9. inverts WFT1.
      assert (sub PG (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
      eapply sub_transitivity in H9; eauto.
      exists (open_exp_wrt_exp e1 (e_abs e)).
      pick_fresh y.
      assert (NOTIN: (y \notin L)) by auto.
      lets temp1: H3 y NOTIN.
      eapply step_typeofl with (C:=(t_arrow t_top t_bot)); eauto.
      forwards*: typing_regular Typ'.
     }
     {
       (*case e = null*)
       apply inv_null in H9; auto. destruct H9.
       exists (open_exp_wrt_exp e1 e_null).
       pick_fresh y.
       assert (NOTIN: (y \notin L)) by auto.
       lets: H3 y NOTIN.
       eapply step_typeofl with (C:=t_unit); eauto.
       forwards*: typing_regular Typ'.
     }
     {
       apply inv_P in H9; auto. destruct H9.
       exists (open_exp_wrt_exp e1 (e_new P)).
       pick_fresh y.
       assert (NOTIN: (y \notin L)) by auto.
       lets: H3 y NOTIN.
       eapply step_typeofl with (C:=(t_prim P)); eauto.
       forwards*: typing_regular Typ'.
     }
   * (*case typeofr*)
     destruct H8.
     apply inv_int in H9; auto. destruct H9.
     { (*case e = int*)
      exists (open_exp_wrt_exp e2 (e_lit i5)).
      pick_fresh y.
      assert (NOTIN: (y \notin L)) by auto.
      lets: H5 y NOTIN.
      eapply step_typeofr with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H9; auto.
      destruct H9 as [A1 [B1]].
      lets(_&WFT1&_): subtyping_regular H9. inverts WFT1.
      assert (sub PG (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
      eapply sub_transitivity in H9; eauto.
      exists (open_exp_wrt_exp e2 (e_abs e)).
      pick_fresh y.
      assert (NOTIN: (y \notin L)) by auto.
      lets: H5 y NOTIN.
      eapply step_typeofr with (C:=(t_arrow t_top t_bot)); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = null*)
       apply inv_null in H9; auto. destruct H9.
       exists (open_exp_wrt_exp e2 e_null).
       pick_fresh y.
       assert (NOTIN: (y \notin L)) by auto.
       lets: H5 y NOTIN.
       eapply step_typeofr with (C:=t_unit); eauto.
       forwards*: typing_regular Typ'.
     }
     {
      apply inv_P in H9; auto. destruct H9.
      exists (open_exp_wrt_exp e2 (e_new P)).
      pick_fresh y.
      assert (NOTIN: (y \notin L)) by auto.
      lets: H5 y NOTIN.
      eapply step_typeofr with (C:=(t_prim P)); eauto.
      forwards*: typing_regular Typ'.
     }
  + (*case typeof*)
    destruct H8 as [x temp].
    exists (e_typeof x A e1 B e2).
    apply step_typeof; auto.
    forwards*: typing_regular Typ'.
  - destruct~ IHTyp1.
  - left*.
    (* we make e_new a value? *)
Qed.


(* ********************************************************************** *)
(** More Typing Inversion Properties *)

Lemma inv_app : forall PG E e1 e2 A,
typing PG E (e_app e1 e2) A ->
exists A1 B1, typing PG E e1 (t_arrow A1 B1) /\ typing PG E e2 A1.
Proof.
  introv Typ.
  inductions Typ.
 - exists* A B.
 - specialize (IHTyp e1 e2).
  forwards*: IHTyp.
 - forwards*: IHTyp1.
Qed.

Lemma inv_typeof : forall PG E e e1 e2 A B C,
typing PG E (e_typeof e A e1 B e2) C ->
exists D, typing PG E e D /\ PG |- A *s B.
Proof.
  introv Typ.
  inductions Typ.
  - specialize (IHTyp e e1 e2 A B).
    forwards*: IHTyp.
  - exists* (t_union A B).
  - forwards*: IHTyp1.
Qed.

(*******************************)
(*****  Determinism Lemma  *****)
(*******************************)

(* Theorem 10 *)

Lemma determinism : forall PG E e e1 e2 A, typing PG E e A ->
PG |- e --> e1 -> PG |- e --> e2 -> e1 = e2.
Proof.
  introv Typ He1. gen e2 A.
  induction He1; introv Typ He2.
  (*case step-appl*)
  - inverts* He2.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards*: IHHe1. rewrite* H3.
   + inverts* H2; inverts He1.
   + inverts* He1.
(*case step-appr*)
  - inverts* He2.
   + inverts* H; inverts* H4.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards*: IHHe1 H1. rewrite* H3.
   + inverts H4; inverts He1.
(*case step-beta*)
  - inverts* He2.
   + inverts* H5.
   + inverts H0; inverts H5.
(*case step-typeof*)
 - inverts* He2.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H0.
    forwards*: IHHe1. rewrite* H2.
  + inverts H8; inverts He1.
  + inverts H8; inverts He1.
(*case step-typeofl*)
 - inverts* He2.
  + inverts H0. inverts H10. inverts H10. inverts H10. inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [H3 Disj].
    inverts H0.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      lets(OK&WFT1&WFT2): subtyping_regular H12.
      lets(?&WFT3&WFT4): subtyping_regular H2.
      forwards*: Disj t_int.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      lets(?&WFT1&WFT2): subtyping_regular H2.
      lets(?&WFT3&WFT4): subtyping_regular H12.
      forwards*: Disj (t_arrow t_top t_bot).
    * inverts H1. inverts H11.
      forwards*: Disj t_unit.
      lets(?&WFT1&WFT2): subtyping_regular H2.
      lets(?&WFT3&WFT4): subtyping_regular H12.
      assert (sub PG t_unit (t_and A B)) by auto.
      contradiction.
    * inverts H1. inverts H11.
    lets(?&WFT1&WFT2): subtyping_regular H2.
    lets(?&WFT3&WFT4): subtyping_regular H12.
      assert (PG |- (t_prim P) <: (t_and A B)) by auto.
      forwards*: Disj (t_prim P).
(*case step-typeofr*)
- inverts* He2.
  + inverts H0; inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [H3 Disj].
    lets(?&WFT1&WFT2): subtyping_regular H2.
    lets(?&WFT3&WFT4): subtyping_regular H12.
    inverts H0.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj t_int.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj (t_arrow t_top t_bot).
    * inverts H1. inverts H11.
      forwards*: Disj t_unit.
      assert (sub PG t_unit (t_and A B)) by auto.
      contradiction.
    * inverts H1. inverts H11.
      assert (PG |- (t_prim P) <: (t_and A B)) by auto.
      forwards*: Disj (t_prim P).
Qed.

(**************************************************)
(* Lemma: Intersection Types Disjoint *)

Lemma intersection_type_disjointness : 
  forall PG A B C,
  okenvp PG -> wft PG A -> 
  wft PG B -> wft PG C ->
  DisjSpec PG A C \/ DisjSpec PG B C ->
  DisjSpec PG (t_and A B) C.
Proof.
  introv Ok WFA WFB WFC Disj.
  unfold DisjSpec in *. unfold not in *.
  destruct Disj as [Disj | Disj]; introv ORD SUB.
  apply sub_and in SUB. destruct SUB.
  apply sub_and in H. destruct H.
  forwards*: subtyping_regular H0.
  apply sub_and in SUB. destruct SUB.
  apply sub_and in H. destruct H.
  forwards*: subtyping_regular H0.
Qed.