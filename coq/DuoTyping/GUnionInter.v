(**************************************************************************************************
* Preservation and Progress for STLC with duotyping, union and intersection types                   *
* Based on original code by: Brian Aydemir & Arthur Charguéraud, March 2007, Coq v8.1   
* Modifications by Bruno C. d. S. Oliveira, Shaobo Cui and Baber Rehman, January 2020, Coq v8.7.0   *
***************************************************************************************************)

Set Implicit Arguments.
Require Import TLC.LibLN.
Implicit Types x : var.
Implicit Types X : var.

(* ***********************************************************************)
(** * Description of the Language *)

(** Representation of types *)

Inductive typ : Set :=
  | typ_btm   : typ
  | typ_top   : typ
  | typ_int   : typ
  | typ_arrow : typ -> typ -> typ
  | typ_and   : typ -> typ -> typ
  | typ_or    : typ -> typ -> typ.

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm.

Inductive Mode := Sub | Sup.

Definition flip (m : Mode) : Mode :=
  match m with
  | Sub => Sup
  | Sup => Sub
  end.

Definition mode_to_sub m := match m with
  | Sub => typ_top
  | Sup => typ_btm end.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_abs V e1  => trm_abs V (open_ee_rec (S k) f e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).

(** Binding are mapping to term variables. 
 [x ~: T] is a typing assumption *)

Inductive bind : Set :=
  | bind_typ : typ -> bind.

Notation "x ~: T" := (x ~ T)
  (at level 23, left associativity) : env_scope.

Definition env := LibEnv.env typ.

(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_var : forall x,
      term (trm_fvar x)
  | term_abs : forall L V e1,
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs V e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2).

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_typ : forall E x T,
      okt E -> x # E -> okt (E & x ~: T).

Definition BindPosVariance m1 m2 :=
  match m1 with
    | Sup => m2
    | Sub => flip m2 end.

Definition SelectBound m1:= 
  match m1 with
    | Sup => typ_btm
    | Sub => typ_top end.

Definition choose (m : Mode) : typ -> typ -> typ :=
  match m with
  | Sub => typ_and
  | Sup => typ_or
  end.

Inductive R : Mode -> typ -> typ -> Prop :=
  | SInt : forall m, R m typ_int typ_int
  | STB1 : forall A m, R m A (mode_to_sub m)
  | STB2 : forall A m, R m (mode_to_sub (flip m)) A
  | SFun : forall A B C D m, R (flip m) A C -> R m B D -> R m (typ_arrow A B) (typ_arrow C D)
  | SLeft1  : forall A B C m, R m A C -> R m (choose m A B) C
  | SLeft2  : forall A B C m, R m A B -> R m A (choose (flip m) B C)
  | SRight1 : forall A B C m, R m B C -> R m (choose m A B) C
  | SRight2 : forall A B C m, R m A C -> R m A (choose (flip m) B C)
  | SBoth1  : forall A B C m, R m A B -> R m A C -> R m A (choose m B C)
  | SBoth2  : forall A B C m, R m A C -> R m B C -> R m (choose (flip m) A B) C.

Hint Constructors R.

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_var : forall E x T,
      okt E ->
      binds x T E ->
      typing E (trm_fvar x) T
  | typing_abs : forall L E V e1 T1,
      (forall x, x \notin L ->
        typing (E & x ~: V) (e1 open_ee_var x) T1) ->
      typing E (trm_abs V e1) (typ_arrow V T1)
  | typing_app : forall T1 E e1 e2 T2,
      typing E e1 (typ_arrow T1 T2) ->
      typing E e2 T1 ->
      typing E (trm_app e1 e2) T2
  | typing_sub : forall S E e T,
      typing E e S ->
      R Sub S T ->
      typing E e T.

(** Values *)

Inductive value : trm -> Prop :=
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1).

(** One-step reduction *)

Inductive red : trm -> trm -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      term e2 ->
      red e1 e1' ->
      red (trm_app e1 e2) (trm_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (trm_app e1 e2) (trm_app e1 e2')
  | red_abs : forall V e1 v2,
      term (trm_abs V e1) ->
      value v2 ->
      red (trm_app (trm_abs V e1) v2) (open_ee e1 v2).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E e e' T,
  typing E e T -> 
  red e e' -> 
  typing E e' T.

Definition progress := forall e T,
  typing empty e T -> 
     value e 
  \/ exists e', red e e'.

(** Computing free term variables in a type *)

Fixpoint fv_ee (e : trm) {struct e} : vars :=
  match e with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs V e1  => (fv_ee e1)
  | trm_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs V e1  => trm_abs V (subst_ee z u e1)
  | trm_app e1 e2 => trm_app (subst_ee z u e1) (subst_ee z u e2)
  end.

(* ********************************************************************** *)
(** * Tactics *)

(** Constructors as hints. *)

Hint Constructors term ok okt value red.

Hint Resolve 
  STB1 STB2 SInt SFun
  typing_var typing_app typing_sub.

(** Gathering free names already used in the proofs *)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let D := gather_vars_with (fun x : trm => fv_ee x) in
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
  | |- R ?E _ _ _  => E
  | |- typing ?E _ _ => E
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
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_ee_rec_term : forall u e,
  term e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_ee. pick_fresh x. 
   apply* (@open_ee_rec_term_core e1 0 (trm_fvar x)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_ee e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*. 
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, term u ->
  subst_ee x u (open_ee t1 t2) =
  open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> term u ->
  (subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e, 
  x \notin fv_ee e -> term u ->
  open_ee e u = subst_ee x u (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

Lemma subst_ee_term : forall e1 Z e2,
  term e1 -> term e2 -> term (subst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
Qed.

Hint Resolve subst_ee_term.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1; auto. 
Qed.

Hint Extern 1 (ok _) => apply ok_from_okt.

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
  rewrite concat_empty_r in *. lets*: (okt_push_inv O).
  rewrite concat_assoc in *.
  apply okt_push_inv in O.
  destruct O. apply IHF in H.
  apply okt_typ; autos*.  
Qed.

Hint Immediate okt_strengthen.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ term e.
Proof. 
  induction 1; try splits*.
   pick_fresh y. specializes H0 y. destructs~ H0.
  apply okt_push_inv in H0. destruct H0. auto. 
   apply_fresh* term_abs as y. 
      specializes H0 y. destructs~ H0.
Qed. 

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> term t.
Proof.
  induction 1; autos*.
Qed.

(** The reduction relation is restricted to well-formed objects. *)

Lemma red_regular : forall t t',
  red t t' -> term t /\ term t'.
Proof.
  induction 1; split; autos* value_regular.
  inversions H. pick_fresh y. rewrite* (@subst_ee_intro y). 
Qed.

(** Automation *)

Hint Extern 1 (okt ?E) =>
  match goal with
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end.

Hint Extern 1 (term ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: red ?e _ |- _ => apply (proj1 (red_regular H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular H))
  end.

(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma refl : forall A m, R m A A.
  induction A; intros; destruct m; simpl in *; try (constructor; fail); eauto.
  - apply SBoth1. apply SLeft1; eauto. apply SRight1; eauto.
  - apply SBoth2. apply SLeft2; eauto. apply SRight2; eauto.
  - apply SBoth2. apply SLeft2; eauto. apply SRight2; eauto.
  - apply SBoth1. apply SLeft1; eauto. apply SRight1; eauto.
Defined.

(* ********************************************************************** *)
(** Symmetry*)

(*Lemma m_flip_inv : forall m, m = flip (flip m).
Proof. intros. destruct* m. Qed.*)

Lemma sym1 : forall A B m, R m A B -> R (flip m) B A.
  intros. induction H.
  - autos.
  - destruct m; apply* STB2.
  - destruct m; apply* STB1.
  - apply* SFun.
  - destruct m; simpl in *; apply SLeft2; auto.
  - destruct m; simpl in *; apply SLeft1; auto.
  - destruct m; simpl in *; apply SRight2; auto.
  - destruct m; simpl in *; apply SRight1; auto.
  - destruct m; simpl in *; apply SBoth2; auto.
  - destruct m; simpl in *; apply SBoth1; auto.
Defined.

Corollary sym2 : forall A B m, R m A B <-> R (flip m) B A.
destruct m; split; apply sym1.
Defined. 

Corollary sym : forall A B, R Sub A B <-> R Sup B A.
  intros. split; apply sym1.
Defined.

(* ********************************************************************** *)
(** Narrowing and Transitivity (3) *)

Definition transitivity_on Q := forall m S T,
  R m S Q -> R m Q T -> R m S T.

Hint Unfold transitivity_on.

Require Import Program.Equality.

Lemma invChoose : forall m A B C, R m A (choose m B C) -> R m A B /\ R m A C.
  intros m A B C r.
  dependent induction r; eauto; try (destruct m; inversion x).
  - destruct (IHr _ _ eq_refl). split; apply SLeft1; auto.
  - destruct (IHr _ _ eq_refl). split; apply SRight1; auto.
  - subst; split; auto.
  - subst; split; auto.
  - destruct (IHr1 _ _ eq_refl).
    destruct (IHr2 _ _ eq_refl).
    split; apply SBoth2; eauto.
Defined.

Lemma flip_flip : forall m A C, R (flip (flip m)) A C -> R m A C.
  intros.
  destruct m; simpl in *; eauto.
Defined.

Lemma invChoose2 : forall m A B C, R m (choose (flip m) A B) C -> R m A C /\ R m B C.
  intros.
  apply sym1 in H. apply invChoose in H. destruct H.
  apply sym1 in H. apply sym1 in H0.
  apply flip_flip in H. apply flip_flip in H0.
  split; auto.
Defined.

Lemma invBound : forall m C, R m (mode_to_sub m) C -> forall A, R m A C.
  intros m C r.
  destruct m; dependent induction r; intros; eauto.
Defined.

Lemma trans : forall m A B, R m A B -> forall C, R m B C -> R m A C.
  intros m A B r.
  induction r; intros; simpl; auto.
  - apply invBound. auto.
  - dependent induction H; simpl in *; auto; try (destruct m; inversion x); eauto.
  - apply invChoose2 in H. destruct H. apply IHr. auto.
  - apply invChoose2 in H. destruct H. apply IHr. auto.
  - dependent induction H; simpl in *; try (destruct m; inversion x; fail); try (econstructor; eauto; fail).
    destruct m; simpl in x; inversion x; subst; eauto.
    destruct m; simpl in x; inversion x; subst; eauto.
Defined.

(* ********************************************************************** *)
(** * Properties of Typing *)

(* ********************************************************************** *)
(** Weakening (5) *)

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T -> 
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof. 
  introv Typ. gen F. inductions Typ; introv Ok.
  apply* typing_var. apply* binds_weaken.
  apply_fresh* typing_abs as x. forwards~ K: (H x).
   apply_ih_bind (H0 x); eauto.
  apply* typing_app.
  apply* typing_sub.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma typing_through_subst_ee : forall U E F x T e u,
  typing (E & x ~: U & F) e T ->
  typing E u U ->
  typing (E & F) (subst_ee x u e) T.
Proof.
  introv TypT TypU. inductions TypT; introv; simpl.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  lets M:TypU. apply typing_regular in M. destruct M. auto.
  apply* typing_app. 
  apply* typing_sub.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution (11) *)


(* ********************************************************************** *)
(** * Preservation *)

(* ********************************************************************** *)
(** Inversions for Typing (13) *)

Lemma typing_inv_abs : forall E S1 e1 T,
  typing E (trm_abs S1 e1) T -> 
  (forall U1 U2, R Sub T (typ_arrow U1 U2) ->
     R Sub U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) S2 /\ R Sup U2 S2).
Proof.
  introv Typ. gen_eq e: (trm_abs S1 e1). gen S1 e1.
  induction Typ; intros S1 b1 EQ U1 U2 R; inversions EQ.
  inversions* R. split.
  rewrite <- sym2 in H5. auto.
  exists T1. exists L. split; autos.
  rewrite sym2. apply H7.
  apply IHTyp. autos. eapply trans.
  apply H. apply R.
Qed.

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red;
   try solve [ inversion Red ].
  (* case: app *) 
  - inversions Red; try solve [ apply* typing_app ].
  destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* refl. (*apply typing_regular in Typ1. destruct Typ1. 
    destruct H0.*)
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).  
       apply* (@typing_sub S2). apply* sym2.
       autos*.
    apply* value_regular.
  (* case sub *)
  - apply* typing_sub.
Qed.

(* ********************************************************************** *)
(** * Progress *)

(* ********************************************************************** *)
(** Canonical Forms (14) *)

Lemma canonical_form_abs : forall t U1 U2,
  value t -> typing empty t (typ_arrow U1 U2) -> 
  exists V, exists e1, t = trm_abs V e1.
Proof.

  introv Val Typ. 
  gen_eq T: (typ_arrow U1 U2). intro st. assert (R Sub T (typ_arrow U1 U2)). { rewrite st. apply refl. }
  clear st. gen_eq E: (@empty typ). gen U1 U2.
  induction Typ; introv EQT EQE; 
   try solve [ inversion Val | inversion EQT | eauto ].
    subst. assert (R Sub S (typ_arrow U1 U2)). { eapply trans. 
    apply H. apply EQT. } eapply IHTyp. apply Val. apply H0. reflexivity. Qed. 

(* ********************************************************************** *)
(** Progress Result (16) *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty typ). lets Typ': Typ. remember empty as Env.
  induction Typ; intros EQ; subst.
  left*. 
  (* case: var *)
  false* binds_empty_inv.
  (* case: abs *) 
  left*. apply value_abs. apply* typing_regular.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (open_ee e3 e2). apply red_abs.
        apply* typing_regular. auto.
        exists (trm_app e1' e2). apply red_app_1. apply* typing_regular. auto.
  (* case: sub *)
  autos*.
Qed.