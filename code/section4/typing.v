(*

-> Section 4 in paper
-> Union Types + Null + Intersection Types
-> Nominal types
-> Subtyping Distributivity

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
Require Import Lists.List.
Require Import equivalence.


(** definitions *)

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_int   : Ord t_int
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2)
| o_unit  : Ord t_unit
| o_prim  : forall i, Ord (t_prim i).

#[export]
Hint Constructors Ord : core.

(* borrowed from syntax.v *)
Lemma ord_eq : forall A, Ord A -> ordu A.
Proof.
 induction A; intros; eauto.
 inversion H. inversion H.
 apply OU_null.
 apply OU_prim.
Defined.

Lemma ord_sub_or_unique : forall PG A B C, Ord A ->
  declarative_subtyping PG A (t_union B C) ->
  declarative_subtyping PG A B \/ declarative_subtyping PG A C.
Proof.
  intros.
  apply ord_eq in H.
  apply dsub2asub in H0.
  assert (splu (t_union B C) B C) by auto.
  lets: algo_sub_orlr_inv A (t_union B C) B C H0.
  lets: H2 H H1.
  destruct H3.
  apply dsub2asub in H3; auto.
  apply dsub2asub in H3; auto.
Qed.
(****************************************)
(**********  Dijoint Specs    ***********)
(****************************************)

Definition DisjSpec PG A B := forall C, Ord C -> not (declarative_subtyping PG C (t_and A B)).
Notation "PG ||- A *s B" := (DisjSpec PG A B) (at level 80).

#[export] Hint Extern 1 => match goal with
                           | H: declarative_subtyping _ _ _ |- _ => apply dsub2asub in H; inverts H; fail
                           end : FalseHd.




#[export] Hint Extern 1 => match goal with
                           | H: declarative_subtyping _ _ _ |- _ => apply dsub2asub in H; inverts H; fail
                           end : FalseHd.

Lemma top_sub_int_false : forall PG,
  declarative_subtyping PG t_top t_int -> False.
Proof.
  intros. apply dsub2asub in H.
  inverts* H; try solve
  [inversion H0; inversion H1; inversion H2; inversion H3].
Defined.

Lemma top_sub_bot_false : forall PG,
  declarative_subtyping PG t_top t_bot -> False.
Proof.
  intros. apply dsub2asub in H.
  inverts* H;
  try solve [inversion H0; inversion H1; inversion H2; inversion H3].
Defined.

Lemma top_sub_arrow_false : forall PG A B,
declarative_subtyping PG t_top (t_arrow A B) -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H. inverts H.
  forwards*: IHalgo_sub1.
  forwards*: IHalgo_sub1.
  inverts H0. inverts H0. inverts H. inverts H0. inverts H0.
Defined.

Lemma int_sub_bot_false : forall PG,
declarative_subtyping PG t_int t_bot -> False.
Proof.
  intros. apply dsub2asub in H.
  inverts H;
  try solve [inversion H0; inversion H1; inversion H2; inversion H3].
Defined.

Lemma int_sub_arrow_false : forall PG A B,
  declarative_subtyping PG t_int (t_arrow A B) -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H.
  forwards*: IHalgo_sub1.
  forwards*: IHalgo_sub1.
  inverts H0. inverts H0. inverts H.
  inverts H0. inverts H0.
Defined.

Lemma int_sub_null_false : forall PG,
  declarative_subtyping PG t_int t_unit -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma int_sub_prim_false : forall PG i,
  declarative_subtyping PG t_int (t_prim i) -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma arrow_sub_int_false : forall PG A B,
  declarative_subtyping PG (t_arrow A B) t_int -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0.
  forwards*: IHalgo_sub.
  forwards*: IHalgo_sub.
  inverts H0.
  forwards*: IHalgo_sub.
  forwards*: IHalgo_sub.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma arrow_sub_bot_false : forall PG A B,
declarative_subtyping PG (t_arrow A B) t_bot -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H.
  inverts H0; forwards*: IHalgo_sub.
  inverts H0; forwards*: IHalgo_sub.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma arrow_sub_null_false : forall PG A B,
  declarative_subtyping PG (t_arrow A B) t_unit -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0.
  forwards*: IHalgo_sub.
  forwards*: IHalgo_sub.
  inverts H0.
  forwards*: IHalgo_sub.
  forwards*: IHalgo_sub.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma arrow_sub_prim_false : forall PG A B i,
  declarative_subtyping PG (t_arrow A B) (t_prim i) -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0.
  forwards*: IHalgo_sub.
  forwards*: IHalgo_sub.
  inverts H0.
  forwards*: IHalgo_sub.
  forwards*: IHalgo_sub.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma null_sub_arrow_false : forall PG A B,
  declarative_subtyping PG t_unit (t_arrow A B) -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H.
  forwards*: IHalgo_sub1.
  forwards*: IHalgo_sub1.
  inverts H0. inverts H0. inverts H. inverts H0. inverts H0.
Defined.

Lemma null_sub_int_false : forall PG,
  declarative_subtyping PG t_unit t_int -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma null_sub_prim_false : forall PG i,
  declarative_subtyping PG t_unit (t_prim i) -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma null_sub_bot_false : forall PG,
  declarative_subtyping PG t_unit t_bot -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma prim_sub_arrow_false : forall PG A B i,
  declarative_subtyping PG (t_prim i) (t_arrow A B) -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H.
  forwards*: IHalgo_sub1.
  forwards*: IHalgo_sub1.
  inverts H0. inverts H0. inverts H. inverts H0. inverts H0.
Defined.

Lemma prim_sub_int_false : forall PG i,
  declarative_subtyping PG (t_prim i) t_int -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma prim_sub_null_false : forall PG i,
  declarative_subtyping PG (t_prim i) t_unit -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

Lemma prim_sub_bot_false : forall PG i,
  declarative_subtyping PG (t_prim i) t_bot -> False.
Proof.
  intros. apply dsub2asub in H.
  inductions H.
  inverts H. inverts H0. inverts H0.
  inverts H. inverts H0. inverts H0.
Defined.

#[export] Hint Immediate top_sub_int_false top_sub_bot_false top_sub_arrow_false int_sub_bot_false int_sub_arrow_false
int_sub_null_false int_sub_prim_false arrow_sub_int_false arrow_sub_bot_false arrow_sub_null_false
arrow_sub_prim_false null_sub_arrow_false null_sub_int_false null_sub_prim_false null_sub_bot_false
prim_sub_arrow_false prim_sub_int_false prim_sub_null_false prim_sub_bot_false : FalseHd.

Module Typing_part.

Export Notations.
(** syntax *)

Inductive exp : Set :=  (*r expression *)
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp
 | e_new    : MetatheoryAtom.Atom.atom -> exp.


(** Binding are mapping to term variables.
 [x ~: T] is a typing assumption *)

 Inductive bind : Set :=
 | bind_typ : typ -> bind.

Notation "x ~: T" := (x ~ T)
 (at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)

 Definition env := LibEnv.env typ.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => If (k = nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
  | (e_null) => e_null
  | e_new A  => e_new A
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (L:vars) (e:exp),
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2))
 | lec_e_null :
     lc_exp e_null
 | lc_e_new : forall A,
     lc_exp (e_new A).

(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => \{}
  | (e_var_f x) => \{x}
  | (e_lit i5) => \{}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
  | (e_null) => \{}
  | e_new A  => \{}
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (If x = x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
  | (e_null) => e_null
  | (e_new A) => e_new A
  end.

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
Inductive typing (PG:envp) : env -> exp -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      ok  G  ->
      okenvp PG ->
     typing PG G (e_lit i5) t_int
 | typ_null : forall G,
      ok G ->
      okenvp PG ->
      typing PG G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      ok  G  ->
      okenvp PG ->
      wft PG A ->
      binds  x A G  ->
     typing PG G (e_var_f x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     okenvp PG -> wft PG A -> wft PG B ->
     typing PG G e1 (t_arrow A B) ->
     typing PG G e2 A ->
     typing PG G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing PG G e B ->
     declarative_subtyping PG B A ->
     typing PG G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      okenvp PG -> wft PG A -> wft PG B ->
      ( forall x , x \notin  L  -> typing PG (G & x ~: A )   ( open_exp_wrt_exp e (e_var_f x) ) B )  ->
     typing PG G (e_abs e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing PG G e (t_union A B) ->
     ( forall x , x \notin  L  -> typing PG  (G & x ~: A )   ( open_exp_wrt_exp e1 (e_var_f x) ) C ) ->
     ( forall x , x \notin  L  -> typing PG  (G & x ~: B )   ( open_exp_wrt_exp e2 (e_var_f x) ) C ) ->
     PG ||- A *s B ->
     typing PG G (e_typeof e A e1 B e2) C
 | typ_prim : forall i G,
    ok G ->
    okenvp PG -> wft PG (t_prim i) ->
     typing PG G (e_new i) (t_prim i).

(* defns Reduction *)
Reserved Notation "PG ||- e --> e'" (at level 80).
Inductive step (PG:envp) : exp -> exp -> Prop :=    (* defn step *)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     PG ||- e1 --> e1' ->
     PG ||- (e_app e1 e2) --> (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     PG ||- e --> e' ->
     PG ||- (e_app v e) --> (e_app v e')
 | step_beta : forall (e:exp) (v:exp),
     lc_exp (e_abs e) ->
     value v ->
     PG ||- e_app  (e_abs e) v --> (open_exp_wrt_exp e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     PG ||- e --> e' ->
     PG ||- (e_typeof e A e1 B e2) --> (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     declarative_subtyping PG C A ->
     PG ||- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     declarative_subtyping PG C B ->
     PG ||- (e_typeof v A e1 B e2) -->  (open_exp_wrt_exp  e2 v )
where "PG ||- e --> e'" := (step PG e e') : env_scope.

#[export]
Hint Constructors typing step : core.


#[export]
Hint Constructors lc_exp ok ok : core.
#[export]
Hint Resolve DS_refl DS_top DS_bot DS_arrow DS_or : core.
#[export]
Hint Resolve DS_orl DS_orl DS_and DS_andl DS_andr : core.
#[export]
Hint Resolve DS_distArr DS_distArrRev DS_distArrU DS_distArrURev DS_distOr DS_distAnd DS_prim : core.

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
  | |- declarative_subtyping _ ?E _ _  => E
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


(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Inversion lemma *)

Lemma okt_push_inv : forall (E:env) x T,
  ok (E & x ~: T) -> ok E /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). subst. autos.
Qed.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma subtyping_regular : forall PG A B,
  declarative_subtyping PG A B -> okenvp PG /\ wft PG A /\ wft PG B.
Proof.
  introv Sub. apply dsub2asub in Sub.
  applys algo_sub_wft Sub.
Qed.

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall PG (E:env) e T,
  typing PG E e T -> ok E /\ lc_exp e /\ okenvp PG /\ wft PG T.
Proof.
  induction 1; try splits*.
 - lets (?&WFT1&WFT2): subtyping_regular H0. auto.
 - pick_fresh y. specializes H3 y. destructs~ H3.
 - apply lc_e_abs with (L:=L). intros.
  specializes H3 x. destructs~ H3.
 - apply lc_e_typeof with (L:=L); intros. destructs~ IHtyping.
   specialize (H1 x H5). destructs~ H1.
   specialize (H3 x H5). destructs~ H3.
 - pick_fresh y.
   destructs~ (H3 y).
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


Lemma typing_weakening : forall PG (E F G:env) e T,
   typing PG (E & G) e T ->
   ok (E & F & G) ->
   typing PG (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_null.
  - apply* typ_var. apply* binds_weaken.
  - forwards*: IHTyp1 E G F.
  - apply* typ_sub.
  - pick_fresh y.
    apply typ_abs with (L:=((((L \u fv_exp e) \u dom E) \u dom G) \u dom F)); auto.
    intros.
    forwards~: (H2 x).
    apply_ih_bind (H3 x); eauto.
  - pick_fresh y.
    apply typ_typeof with (L:=((((((L \u fv_exp e) \u fv_exp e1) \u
      fv_exp e2) \u dom E) \u dom G) \u dom F)); auto; intros.
    forwards*: H x. apply_ih_bind (H0 x); eauto.
    forwards*: H1 x. apply_ih_bind (H2 x); eauto.
  - apply* typ_prim.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution *)

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
 (*case unit*)
 - apply* typ_null.
(*case var*)
 - case_var.
  + binds_get H2.
    lets M: (typing_weakening PG E F empty u U).
    do 2 rewrite concat_empty_r in M.
    apply* M.
  + binds_cases H2; apply* typ_var.
(*case app*)
 - forwards*: IHTypT1.
(*case sub*)
 - eapply typ_sub; eauto.
   forwards~ (?&?&?&?): typing_regular TypT'.
(*case abs*)
 - pick_fresh y.
   apply typ_abs with (L:=(((((L \u \{ x}) \u fv_exp u) \u
     fv_exp e) \u dom E) \u dom F)); auto; intros.
   assert (x0 \notin L) by auto.
   specialize (H3 x0 H5).
   rewrite* subst_ee_open_ee_var.
   lets TEMP1: H3 E (F & x0 ~: A) x.
   lets TEMP2: TEMP1 U; auto.
   rewrite~ concat_assoc in TEMP2.
   rewrite~ concat_assoc in TEMP2.
   apply typing_regular in TypU. destructs~ TypU.
(*case typeof*)
 - pick_fresh y.
   apply typ_typeof with (L:=(((((((L \u \{ x}) \u fv_exp u) \u
     fv_exp e) \u fv_exp e1) \u fv_exp e2) \u dom E) \u dom F)); eauto; intros.
  + assert (x0 \notin L) by auto.
    rewrite* subst_ee_open_ee_var.
    lets TEMP1: H x0 H5.
    lets TEMP2: H0 x0 H5 E (F & x0 ~: A) x.
    lets TEMP3: TEMP2 U.
    rewrite~ concat_assoc in TEMP3.
    rewrite~ concat_assoc in TEMP3.
    apply typing_regular in TypU. destructs~ TypU.
  + assert (x0 \notin L) by auto.
    rewrite* subst_ee_open_ee_var.
    lets TEMP1: H1 x0 H5.
    lets TEMP2: H2 x0 H5 E (F & x0 ~: B) x.
    lets TEMP3: TEMP2 U.
    rewrite~ concat_assoc in TEMP3.
    rewrite~ concat_assoc in TEMP3.
    apply typing_regular in TypU. destructs~ TypU.
 - (*case P*)
    apply* typ_prim.
Qed.


(* ********************************************************************** *)
(** Typing Inversion Lemmas *)

Lemma inv_int : forall PG E A i5,
typing PG E (e_lit i5) A -> typing PG E (e_lit i5) t_int /\ declarative_subtyping PG t_int A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - specialize (IHTyp i5).
  forwards*: IHTyp. destruct H0.
  split*.
  eapply DS_trans; eauto.
Qed.

Lemma abs_typ_arrow_sub : forall PG G e A,
typing PG G (e_abs e) A ->
exists A1 B1, declarative_subtyping PG (t_arrow A1 B1) A.
Proof.
    introv Typ.
    inductions Typ.
    - forwards*: IHTyp. destruct H0 as [x1[x2 H3]].
      exists x1 x2. eapply DS_trans; eauto.
    - exists* A B.
Qed.


Lemma inv_abs_sub : forall PG G e A B1 B2,
    typing PG G (e_abs e) A ->
    declarative_subtyping PG A (t_arrow B1 B2) ->
         exists C1 C2,
           (exists L, forall x , x \notin  L -> typing PG (G & x ~: C1) (e open_ee_var x) C2)
           /\ declarative_subtyping PG (t_arrow C1 C2) (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: declarative_subtyping PG B (t_arrow B1 B2)) by applys DS_trans H Sub.
    forwards* (?&?&?&?): IHTyp HS.
Qed.

Lemma inv_arrow : forall PG G e A1 A2,
    typing PG G (e_abs e) (t_arrow A1 A2) ->
    exists B1 B2, (exists L, forall x , x \notin  L -> typing PG (G & x ~: B1) (e open_ee_var x) B2)
                  /\ declarative_subtyping PG (t_arrow B1 B2) (t_arrow A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards*: inv_abs_sub H.
  - exists* A1 A2.
Qed.

(*

e = \x.x
\x.x : (Int -> Int) /\ (Bool -> Bool) | (Int -> Int) /\ (Bool -> Bool)

\x.x : (Int -> Int) /\ (Bool -> Bool)
\x.x : (Int -> Int) /\ (Bool -> Bool)

*)


Lemma inv_abs_union : forall PG G e A A1 A2,
    typing PG G (e_abs e) A ->
    declarative_subtyping PG A (t_union A1 A2) ->
    typing PG G (e_abs e) A1 \/ typing PG G (e_abs e) A2.
Proof.
  introv Typ. gen A1 A2.
  inductions Typ; introv Sub; eauto.
  - eapply DS_trans in Sub; eauto.
  - apply ord_sub_or_unique in Sub; auto.
    destruct Sub.
    left*. right*.
Qed.

Lemma inv_null : forall PG E A,
typing PG E e_null A -> typing PG E e_null t_unit /\ declarative_subtyping PG t_unit A.
Proof.
  introv Typ.
  inductions Typ.
  (** case null *)
 - split*.
  (*case typ_sub*)
 - forwards*: IHTyp. destruct H0.
  split*.
  eapply DS_trans; eauto.
Qed.

Lemma inv_P : forall PG E P A,
typing PG E (e_new P) A -> typing PG E (e_new P) (t_prim P) /\ declarative_subtyping PG (t_prim P) A.
Proof.
  introv Typ.
  inductions Typ.
  (* case typ_prim *)
 - forwards*: IHTyp. destruct H0.
   split*.
   eapply DS_trans; eauto.
  (*case typ_sub*)
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
   apply ord_sub_or_unique in H0; auto.
   destruct H0. left*. right*.
 - inverts Typ.
   eapply inv_abs_union; eauto.
 - apply inv_null in Typ. destruct Typ.
   apply ord_sub_or_unique in H0; auto.
   destruct H0. left*. right*.
 - apply inv_P in Typ; auto. destruct Typ.
   apply ord_sub_or_unique in H0; auto.
   destruct H0. left*. right*.
Qed.

(* Value cannot check against disjoint types *)

Lemma val_check_disjoint_types : forall PG E v A B,
PG ||- A *s B ->
value v ->
typing PG E v A ->
typing PG E v B -> False.
Proof.
  introv Disj Val Typ1 Typ2.
  unfold DisjSpec in Disj. unfold not in Disj.
  inverts Val.
  - apply inv_int in Typ1. destruct Typ1.
    apply inv_int in Typ2. destruct Typ2.
    forwards*: Disj t_int.
  - apply abs_typ_arrow_sub in Typ1.
    destruct Typ1 as [A1 [B1]].
    forwards*(?&WFT1&WFT2): subtyping_regular H0.
    forwards*(?&WFT11&WFT21): typing_regular Typ2.
    assert (declarative_subtyping PG (t_arrow t_top t_bot) (t_arrow A1 B1)); auto.
    apply abs_typ_arrow_sub in Typ2.
    destruct Typ2 as [A2 [B2]].
    forwards*(_&WFT3&WFT4): subtyping_regular H4.
    assert (declarative_subtyping PG (t_arrow t_top t_bot) (t_arrow A2 B2)); auto.
    eapply DS_trans with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A1 B1)) (C:=A) in H3; auto.
    eapply DS_trans with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A2 B2)) (C:=B) in H5; auto.
    forwards*: Disj (t_arrow t_top t_bot).
  - apply inv_null in Typ1; auto. destruct Typ1.
    apply inv_null in Typ2; auto. destruct Typ2.
    (* lets(?&WFT1&WFT2): subtyping_regular H2.
    lets(?&WFT3&WFT4): subtyping_regular H0. *)
    forwards*: Disj t_unit.
  - apply inv_P in Typ1; auto. destruct Typ1.
    apply inv_P in Typ2; auto. destruct Typ2.
    (* lets(?&WFT1&WFT2): subtyping_regular H2.
    lets(?&WFT3&WFT4): subtyping_regular H0. *)
    forwards*: Disj (t_prim P).
Qed.

Lemma check_find_type : forall PG E e A B,
typing PG E e A ->
findtype e B ->
declarative_subtyping PG B A.
Proof.
  introv Typ Find.
  inductions Find.
  - apply inv_int in Typ.
    destruct~ Typ.
  - apply abs_typ_arrow_sub in Typ.
    destruct Typ as [A1 [B1]].
    forwards*(Ok&WFT1&WFT2): subtyping_regular H0.
    assert (declarative_subtyping PG (t_arrow t_top t_bot) (t_arrow A1 B1)); auto.
    eapply DS_trans; eauto.
  - apply inv_null in Typ; auto. destruct~ Typ.
  - apply inv_P in Typ; auto. destruct Typ. auto.
Qed.

(*******************************)
(****  Preservation Lemma  *****)
(*******************************)

(* Theorem 21 *)

Lemma preservation : forall PG E e e' T,
  typing PG E e T ->
  PG ||- e --> e' ->
  typing PG E e' T.
Proof.
  introv Typ. gen e'.
  induction Typ; introv Red; try solve [ inverts* Red ].
  - (* app *)
    inverts* Red.
    (* beta *)
        forwards* : inv_arrow Typ1.
        destruct H2 as [A1[B1 [TEMP1 TEMP2]]].
        destruct TEMP1 as [L].
        pick_fresh x.
        assert (NOTIN: x \notin L) by auto.
        lets TEMP1: H2 x NOTIN.
        rewrite <- (concat_empty_r (G & x ~: A1))  in TEMP1.
        rewrite <- (concat_empty_r G).
        lets TEMP3: typing_through_subst_ee.
        apply dsub2asub in TEMP2.
        apply algo_sub_arrow_inv in TEMP2. destruct TEMP2 as [H' H''].
        apply dsub2asub in H'.
        apply dsub2asub in H''.
        forwards*: TEMP3 TEMP1.
        rewrite* (@subst_ee_intro x).
  - (* typeof *)
    inverts* Red.

    + (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*true goal*)
       pick_fresh y. assert (y \notin L) by auto.
       forwards*: H H5.
       assert  (G & y ~: A = G & y ~: A & empty).
       rewrite* concat_empty_r. rewrite H7 in H6.
       assert (G = G & empty).
       rewrite* concat_empty_r.
       rewrite H8.
       forwards*: typing_through_subst_ee.
       rewrite* (@subst_ee_intro y).
     * (*false goal, value e checks against disjoint types A and B*)
       lets temp1: check_find_type G e B C0 H4.
       lets SubB: temp1 H12.
       unfold DisjSpec in H3. unfold not in H3.
       destruct H12.
       forwards*: H3 t_int.
       forwards*: H3 (t_arrow t_top t_bot).
       forwards*: H3 t_unit.
       forwards*: H3 (t_prim P).
    +  (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*false goal, value e checks against disjoint types A and B*)
        lets temp1: check_find_type G e A C0 H4.
        lets SubA: temp1 H12.
        unfold DisjSpec in H3. unfold not in H3.
        destruct H12.
        forwards*: H3 t_int.
        forwards*: H3 (t_arrow t_top t_bot).
        forwards*: H3 t_unit.
        forwards*: H3 (t_prim P).
     * (*true goal*)
        pick_fresh y. assert (y \notin L) by auto.
        forwards*: H1 H5.
        assert  (G & y ~: B = G & y ~: B & empty).
        rewrite* concat_empty_r. rewrite H7 in H6.
        assert (G = G & empty).
        rewrite* concat_empty_r.
        rewrite H8.
        forwards*: typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
Qed.

(*******************************)
(******  Progress Lemma  *******)
(*******************************)

(* Theorem 22 *)

Lemma progress : forall PG e T,
    typing PG empty e T -> (value e) \/ (exists e', PG ||- e --> e').
Proof with solve_false.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
(*case int*)
 - left*.
 - (*case null*)
   left*.
 (*case var*)
 - apply binds_empty_inv in H2. inversion H2.
 (*case typ-app*)
 - right. destruct* IHTyp1.
  + destruct* IHTyp2.
   * inverts* H2.
     (*i infers arrow*)
     apply inv_int in Typ1.
     destruct Typ1...
     (*null infers arrow*)
     apply inv_null in Typ1.
     destruct Typ1...
     (*i infers arrow*)
     apply inv_P in Typ1.
     destruct Typ1...
     (*case step-appl*)
   * destruct H3.
     exists* (e_app e1 x).
   (*case step-appr*)
  + destruct H2.
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
   * destruct H4.
     { (*case e = int*)
      apply inv_int in H5. destruct H5.
      exists (open_exp_wrt_exp e1 (e_lit i5)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H y H6.
      eapply step_typeofl with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H5.
      destruct H5 as [A1 [B1]].
      forwards*(Ok&WFT1&WFT2): subtyping_regular H5.
      assert (declarative_subtyping PG (t_arrow t_top t_bot) (t_arrow A1 B1)); auto.
      eapply DS_trans in H5; eauto.
      exists (open_exp_wrt_exp e1 (e_abs e)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H y H7.
      eapply step_typeofl with (C:=(t_arrow t_top t_bot)); eauto.
      forwards*: typing_regular Typ'.
     }
    { (*case e = unit*)
      apply inv_null in H5. destruct H5.
      exists (open_exp_wrt_exp e1 e_null).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H y H6.
      eapply step_typeofl with (C:=t_unit); eauto.
      forwards*: typing_regular Typ'.
     }
    { (*case e = P*)
      apply inv_P in H5. destruct H5.
      exists (open_exp_wrt_exp e1 (e_new P)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H y H6.
      eapply step_typeofl with (C:=(t_prim P)); eauto.
      forwards*: typing_regular Typ'.
     }
   * (*case typeofr*)
     destruct H4.
     apply inv_int in H5. destruct H5.
     { (*case e = int*)
      exists (open_exp_wrt_exp e2 (e_lit i5)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H1 y H6.
      eapply step_typeofr with (C:=t_int); eauto.
      forwards*: typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H5.
      destruct H5 as [A1 [B1]].
      forwards*(Ok&WFT1&WFT2): subtyping_regular H5.
      assert (declarative_subtyping PG (t_arrow t_top t_bot) (t_arrow A1 B1)); auto.
      eapply DS_trans in H5; eauto.
      exists (open_exp_wrt_exp e2 (e_abs e)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H1 y H7.
      eapply step_typeofr with (C:=(t_arrow t_top t_bot)); eauto.
      forwards*: typing_regular Typ'.
     }
    { (*case e = unit*)
      apply inv_null in H5. destruct H5.
      exists (open_exp_wrt_exp e2 e_null).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H1 y H6.
      eapply step_typeofr with (C:=t_unit); eauto.
      forwards*: typing_regular Typ'.
     }
    { (*case e = P*)
      apply inv_P in H5. destruct H5.
      exists (open_exp_wrt_exp e2 (e_new P)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H1 y H6.
      eapply step_typeofr with (C:=(t_prim P)); eauto.
      forwards*: typing_regular Typ'.
    }
  + (*case typeof*)
    destruct H4.
    exists (e_typeof x A e1 B e2).
    apply step_typeof; auto.
    forwards*: typing_regular Typ'.
  - (*case P*)
    left*.
Qed.

(* More Typing Inversion *)

Lemma inv_app : forall PG E e1 e2 A,
typing PG E (e_app e1 e2) A ->
exists A1 B1, typing PG E e1 (t_arrow A1 B1) /\ typing PG E e2 A1.
Proof.
  introv Typ.
  inductions Typ.
 - exists* A B.
 - specialize (IHTyp e1 e2).
  forwards*: IHTyp.
Qed.

Lemma inv_typeof : forall PG E e e1 e2 A B C,
typing PG E (e_typeof e A e1 B e2) C ->
exists D, typing PG E e D /\ PG ||- A *s B.
Proof.
  introv Typ.
  inductions Typ.
  - specialize (IHTyp e e1 e2 A B).
    forwards*: IHTyp.
  - exists* (t_union A B).
Qed.

(*******************************)
(*****  Determinism Lemma  *****)
(*******************************)

(* Theorem 23 *)

Lemma determinism : forall PG E e e1 e2 A, typing PG E e A ->
 PG ||- e --> e1 -> PG ||- e --> e2 -> e1 = e2.
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
      forwards*: Disj t_int.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj (t_arrow t_top t_bot).
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj t_unit.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj (t_prim P).
(*case step-typeofr*)
- inverts* He2.
  + inverts H0; inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [H3 Disj].
    inverts H0.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj t_int.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj (t_arrow t_top t_bot).
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj t_unit.
    * inverts H1.
      inverts H11.
      unfold DisjSpec in Disj. unfold not in Disj.
      forwards*: Disj (t_prim P).
Qed.

End Typing_part.