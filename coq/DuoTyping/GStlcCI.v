(* Simply Typed Lambda Calculus with Generalized Subtyping:
A variation that includes a custom induction principle to simplify 
some proofs.
 *)


Set Implicit Arguments.
Require Import LibLN.
Implicit Types x : var.
Implicit Types X : var.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of types *)

Inductive typ : Set :=
  | typ_btm   : typ
  | typ_top   : typ
  | typ_int   : typ
  | typ_arrow : typ -> typ -> typ.

(** Representation of pre-terms *)

Inductive trm : Set :=
  | trm_unit : trm
  | trm_bvar : nat -> trm
  | trm_fvar : var -> trm
  | trm_nval : nat -> trm
  | trm_nsucc: trm -> trm
  | trm_nind : trm -> trm -> trm -> trm
  | trm_abs  : typ -> trm -> trm
  | trm_app  : trm -> trm -> trm.

(** Generalized Subtyping Judgements *)

Inductive Mode := Sub | Sup.

Definition flip (m : Mode) : Mode :=
  match m with
  | Sub => Sup
  | Sup => Sub
  end.

Definition mode_to_sub m := match m with
  | Sub => typ_top
  | Sup => typ_btm end.

Inductive R : Mode -> typ -> typ -> Prop :=
| SInt : forall m, R m typ_int typ_int
| STB1 : forall A m, R m A (mode_to_sub m)
| STB2 : forall A m, R m (mode_to_sub (flip m)) A
| SFun : forall A B C D m, R (flip m) A C -> R m B D -> R m (typ_arrow A B) (typ_arrow C D).

Lemma indR : 
    forall (P : Mode -> typ -> typ -> Prop),
      (forall m : Mode, P m typ_int typ_int) ->
      (forall (A : typ) (m : Mode), P m A (mode_to_sub m)) ->
      (forall (A B C D : typ) (m : Mode),
          R (flip m) A C ->
          P (flip m) A C -> R m B D -> P m B D -> P m (typ_arrow A B) (typ_arrow C D)) ->
      (forall A B m, R (flip m) B A -> P (flip m) B A -> P m A B) ->
      forall (m : Mode) (t t0 : typ),
    R m t t0 ->
    P m t t0.
  intros.
  induction H3; eauto.
  apply H2. apply STB1. apply H0.
Defined.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k : nat) (f : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_unit      => trm_unit
  | trm_bvar i    => If k = i then f else (trm_bvar i)
  | trm_fvar x    => trm_fvar x
  | trm_nval v    => trm_nval v
  | trm_nsucc s   => trm_nsucc (open_ee_rec k f s)
  | trm_nind i z s => trm_nind (open_ee_rec k f i) (open_ee_rec k f z) (open_ee_rec k f s)
  | trm_abs V e1  => trm_abs V (open_ee_rec (S k) f e1)
  | trm_app e1 e2 => trm_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_ee t (trm_fvar x)) (at level 67).


(** Terms as locally closed pre-terms *)

Inductive term : trm -> Prop :=
  | term_unit : term trm_unit
  | term_var : forall x,
      term (trm_fvar x)
  | term_nval : forall v,
      term (trm_nval v)
  | term_nsucc : forall t,
    term t -> term (trm_nsucc t)
  | term_nind : forall t1 t2 t3,
    term t1 ->
    term t2 ->
    term t3 ->
    term (trm_nind t1 t2 t3)
  | term_abs : forall L V e1,
      (forall x, x \notin L -> term (e1 open_ee_var x)) ->
      term (trm_abs V e1)
  | term_app : forall e1 e2,
      term e1 ->
      term e2 ->
      term (trm_app e1 e2).

(** Binding are mapping term variables to types.
 [x ~: T] is a typing assumption *)



Notation "x ~: T" := (x ~ T)
  (at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. *)

Definition env := LibEnv.env typ.

(** A environment E is well-formed if it contains no duplicate bindings *)

Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_typ : forall E x T,
      okt E ->  x # E -> okt (E & x ~: T).

(** Subtyping relation *)

Inductive typing : env -> trm -> typ -> Prop :=
  | typing_unit : forall E, okt E ->typing E trm_unit typ_top
  | typing_var : forall E x T,
      okt E ->
      binds x T E ->
      typing E (trm_fvar x) T
  | typing_nval : forall E v,
      okt E ->
   typing E (trm_nval v) typ_int
  | typing_nsucc : forall E t,
    okt E ->
    typing E t typ_int ->
    typing E (trm_nsucc t) typ_int
  | typing_nind : forall E V t1 t2 t3,
    okt E ->
    typing E t1 typ_int ->
    typing E t2 V ->
    typing E t3 (typ_arrow V V) ->
    typing E (trm_nind t1 t2 t3) V
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
  | value_unit : value trm_unit
  | value_abs  : forall V e1, term (trm_abs V e1) ->
                 value (trm_abs V e1)
  | value_ival : forall v, value (trm_nval v).

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
      red (trm_app (trm_abs V e1) v2) (open_ee e1 v2)
  | red_succ_can : forall v,
      red (trm_nsucc (trm_nval v)) (trm_nval (S v))
  | red_succ_red : forall t t',
      red t t'->
      red (trm_nsucc t) (trm_nsucc t')
  | red_ind_nred : forall t1 t1' t2 t3,
      red t1 t1' ->
      term t2 ->
      term t3 ->
      red (trm_nind t1 t2 t3) (trm_nind t1' t2 t3)
  | red_ind_icase : forall t1 t2 t3 t3',
      value t1 ->
      term t2 ->
      red t3 t3' ->
      red (trm_nind t1 t2 t3) (trm_nind t1 t2 t3')
  | red_ind_izero : forall t2 t3,
      term t2 ->
      value t3 ->
      red (trm_nind (trm_nval 0) t2 t3) t2
  | red_ind_isucc : forall k t2 t3,
      term t2 ->
      value t3 ->
      red (trm_nind (trm_nval (S k)) t2 t3) (trm_app t3 (trm_nind (trm_nval k) t2 t3)).

(** Our goal is to prove preservation and progress *)

Definition preservation := forall E e e' T,
  typing E e T -> 
  red e e' -> 
  typing E e' T.

Definition progress := forall e T,
  typing empty e T -> 
     value e 
  \/ exists e', red e e'.

(** * Additional Definitions Used in the Proofs *)

(** Computing free term variables in a type *)

Fixpoint fv_ee (e : trm) {struct e} : vars :=
  match e with
  | trm_unit      => \{}
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_nval _    => \{}
  | trm_nsucc t   => fv_ee t
  | trm_nind t1 t2 t3 => (fv_ee t1) \u (fv_ee t2) \u (fv_ee t3)
  | trm_abs V e1  => (fv_ee e1)
  | trm_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : trm) (e : trm) {struct e} : trm :=
  match e with
  | trm_unit      => trm_unit
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_nval i    => trm_nval i
  | trm_nsucc t   => trm_nsucc (subst_ee z u t)
  | trm_nind t1 t2 t3 => trm_nind (subst_ee z u t1) (subst_ee z u t2) (subst_ee z u t3)
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
(** * Properties of Substitutions *)
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

(** Substitutions preserve local closure. *)
Lemma subst_ee_term : forall e1 Z e2,
  term e1 -> term e2 -> term (subst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* term_abs as y. rewrite* subst_ee_open_ee_var.
Qed.

Hint Resolve subst_ee_term.


(* ********************************************************************** *)
(** * Properties of well-formedness of a type in an environment *)


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

(** Extraction from a subtyping assumption in a well-formed environments *)

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

(** Automation *)

Hint Immediate okt_strengthen.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

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


(** In parentheses are given the label of the corresponding
  lemma in the description of the POPLMark Challenge. *)


(* ********************************************************************** *)
(** * Properties of Subtyping *)

(* ********************************************************************** *)
(** Reflexivity (1) *)

Lemma refl : forall A m, R m A A.
  induction A; eauto; intros.
  - destruct m. apply STB2. apply STB1. 
  - destruct m. apply STB1. apply STB2.
Defined.


(* ********************************************************************** *)
(** Transitivity (3) *)

Lemma trans : forall A B m, R m A B -> forall C, R m B C -> R m A C.
  intros A B m s.
  induction s; intros; simpl; destruct m; inversion H; auto.
Defined.

(* ********************************************************************** *)
(** Symmetry and antisymmetry *)

Lemma sym1 : forall A B m, R m A B -> R (flip m) B A.
  intros A B m r.
  induction r using indR; eauto.
  destruct m; simpl in *; apply STB2.
Defined.

Corollary sym2 : forall A B m, R m A B <-> R (flip m) B A.
destruct m; split; apply sym1.
Defined. 

Corollary sym : forall A B, R Sub A B <-> R Sup B A.
  intros. split; apply sym1.
Defined.


Lemma subtyp_antisymm : forall m T T', R m T T' -> R m T' T -> T = T'.
Proof. introv R1 R2. induction R1; try (inversion R2; reflexivity).
inversion R2; try reflexivity.
destruct m; inversion H1. destruct m; inversion H.
inversion R2; try reflexivity.
destruct m; inversion H2. destruct m; inversion H.
inversion R2. destruct m; inversion H2.
destruct m; inversion H1. 
subst. apply IHR1_1 in H3. apply IHR1_2 in H5. subst. auto. Qed. 

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
  apply* typing_unit.
  apply* typing_var. apply* binds_weaken.
  apply* typing_nval.
  apply* typing_nsucc.
  apply* typing_nind. 
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
  apply* typing_unit.
  case_var.
    binds_get H0. apply_empty* typing_weakening.
    binds_cases H0; apply* typing_var.
  apply* typing_nval.
  apply* typing_nsucc.
  apply* typing_nind. 
  apply_fresh* typing_abs as y.
    rewrite* subst_ee_open_ee_var.
    apply_ih_bind* H0.
  apply typing_regular in TypU. destruct TypU. auto.
  apply* typing_app.
  apply* typing_sub.
Qed.

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
  apply IHTyp. auto. 
  eapply trans. apply H. apply R. 
Qed.

Fact typing_inv_abs_not_sup : ~(forall E S1 e1 T,
  typing E (trm_abs S1 e1) T -> 
  (forall U1 U2, R Sup T (typ_arrow U1 U2) ->
     R Sup U1 S1
  /\ exists S2, exists L, forall x, x \notin L ->
     typing (E & x ~: S1) (e1 open_ee_var x) S2 /\ R Sup U2 S2)).
Proof. 
  intros contra. 
  assert (R Sup typ_int typ_top).
  { specialize (@contra empty typ_top (trm_nval 0) typ_top).
    assert (typing empty (trm_abs typ_top (trm_nval 0)) typ_top).
    { eapply typing_sub. apply typing_abs with (L:=\{}). introv X.
      assert (trm_nval 0 open_ee_var x = trm_nval 0).
      { unfold open_ee. simpl. reflexivity. }
      rewrite H. apply typing_nval.
      autos. apply STB1.    }
    apply contra with (U1 := typ_int) (U2 := typ_top) in H.
    destruct H. apply H. apply STB2. 
  } 
  inversion H. Qed.


(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma preservation_result : preservation.
Proof.
  introv Typ. gen e'. induction Typ; introv Red; 
   try solve [ inversion Red ].
  - inversion Red. apply* typing_nval.
    apply* typing_nsucc.
  - inversion Red; try solve [apply* typing_nind].
    subst. auto.
    subst. apply* typing_app. induction k; apply* typing_nind.
      + apply* typing_nval.
      + apply* typing_nval. 
  (* case: app *) 
  - inversions Red; try solve [ apply* typing_app ].
  destruct~ (typing_inv_abs Typ1 (U1:=T1) (U2:=T2)) as [P1 [S2 [L P2]]].
    apply* refl.
    pick_fresh X. forwards~ K: (P2 X). destruct K.
     rewrite* (@subst_ee_intro X).
     apply_empty (@typing_through_subst_ee V).  
       apply* (@typing_sub S2). apply* sym2. 
       autos*. apply* value_regular.
  (* case: tapp *)
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

Lemma canonical_form_nat : forall t,
  value t -> typing empty t typ_int -> 
  exists v, t = trm_nval v.
Proof.
  introv Val Typ. 
  gen_eq T: typ_int. intro st. assert (R Sub T typ_int). { rewrite st. apply refl. }
  clear st. gen_eq E: (@empty typ).
  induction Typ; introv EQE; 
   try solve [ inversion Val | inversion EQE | eauto | inversion H ].
  eapply IHTyp. apply Val. eapply trans. apply H0. apply H. apply EQE. Qed. 

(* ********************************************************************** *)
(** Progress Result (16) *)

Lemma progress_result : progress.
Proof.
  introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
  induction Typ; intros EQ; subst.
  left*. 
  (* case: var *)
  false* binds_empty_inv.
  (* case: nval *)
  left*.
  (* case: succ *)
  right*. 
  destruct* IHTyp as [Val1 | R1].
    destruct (canonical_form_nat Val1 Typ) as [ v ].
    subst. exists (trm_nval (S v)). auto.
    destruct R1. exists (trm_nsucc x). auto.
  (* case : ind *)
  right*.
  {
    assert (value t1 \/ (exists e', red t1 e')). { auto. }
    assert (value t2 \/ (exists e', red t2 e')). { auto. }
    assert (value t3 \/ (exists e', red t3 e')). { auto. }
    clear IHTyp1 IHTyp2 IHTyp3. destruct H0; subst.
    - destruct (canonical_form_nat H0 Typ1) as [ v ].
     destruct H2. 
      + subst. destruct v. 
        * exists t2. apply red_ind_izero; auto. apply typing_regular in Typ2. destruct Typ2; auto. 
        * exists (trm_app t3 (trm_nind (trm_nval v) t2 t3)). 
        apply red_ind_isucc. apply* typing_regular. auto.
      + destruct* H2. subst. exists (trm_nind (trm_nval v) t2 x).  
       apply red_ind_icase; auto. apply* typing_regular.
    - destruct* H0. exists (trm_nind x t2 t3). apply* red_ind_nred; apply* typing_regular.  }
  (* case: abs *) 
  left*. apply value_abs. apply* typing_regular.
  (* case: app *)
  right. destruct* IHTyp1 as [Val1 | [e1' Rede1']].
    destruct* IHTyp2 as [Val2 | [e2' Rede2']].
      destruct (canonical_form_abs Val1 Typ1) as [S [e3 EQ]].
        subst. exists* (open_ee e3 e2).  apply red_abs. 
        apply* typing_regular. auto. 
        exists (trm_app e1' e2). apply red_app_1. apply* typing_regular. 
        auto. 
  (* case: tabs *)
  (* case: tapp *)
  (* case: sub *)
  autos*.
Qed.



