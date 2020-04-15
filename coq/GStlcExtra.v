Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import GStlc.

(* 

RS is the declarative specification of subtyping, which
includes the built-in Sym rule.

*)

Inductive RS : Mode -> typ -> typ -> Prop :=
| RSInt : forall m, RS m typ_int typ_int
| RSTB1 : forall A m, RS m A (mode_to_sub m)
| RSFun : forall A B C D m, RS (flip m) A C -> RS m B D -> RS m (typ_arrow A B) (typ_arrow C D)
| RSSym : forall m A B, RS (flip m) B A -> RS m A B.

Hint Constructors RS.
    
Lemma sound : forall m A B, R m A B -> RS m A B.
  intros.
  induction H; eauto.
Defined.

Lemma complete : forall m A B, RS m A B -> R m A B.
  intros.
  induction H; eauto.
  apply sym2.
  auto.
Defined.

(* 

R2 an algorithmic version that exploits duality for economy 
of code. 

*)

Inductive R2 : bool -> Mode -> typ -> typ -> Prop :=
| R2Int : forall b m, R2 b m typ_int typ_int
| R2TB1 : forall b A m, R2 b m A (mode_to_sub m)
| R2Fun : forall b A B C D m,
    R2 true (flip m) A C ->
    R2 true m B D ->
    R2 b m (typ_arrow A B) (typ_arrow C D)
| R2Sym : forall m A B,
    R2 false (flip m) B A -> R2 true m A B.

Hint Constructors R2.

(* Soundness of R2 *)

Lemma completeR : forall m A B, R m A B -> R2 true m A B.
  intros.
  induction H; eauto.
Defined.

Lemma soundR : forall m b A B, R2 b m A B -> R m A B.
  intros.
  induction H; eauto.
  apply sym2. auto.
Defined.



























(* Not necessary *)

Lemma refl_btm : forall m, R2 true m typ_btm typ_btm.
  destruct m.
  apply R2Sym. simpl.
  apply R2TB1. apply R2TB1.
Defined.

Lemma refl_top : forall m, R2 true m typ_top typ_top.
  destruct m.
  apply R2TB1.
  apply R2Sym. simpl.
  apply R2TB1.
Defined.

Hint Resolve refl_btm refl_top.

Lemma refl : forall A m, R2 true m A A.
  induction A; intros; eauto.
Defined.

Require Import Program.Equality.

Lemma bound : forall b m C, R2 b m (mode_to_sub m) C -> forall A, R2 b m A C.
  intros b m C r.
  dependent induction r; intros; eauto.
  - destruct m; inversion x.
  - destruct m; inversion x.
  - clear IHr.
    destruct m; simpl in r.
    dependent destruction r.
    dependent destruction r.
Defined.

Hint Resolve bound.

Lemma flip_flip : forall m, flip (flip m) = m.
  destruct m; simpl; eauto.
Defined.

Lemma flip_lemma : forall m A B, R2 false m A B -> R2 true m A B.
  intros.
  dependent induction H; eauto.
Defined.

Hint Resolve flip_lemma.

Lemma sym : forall m A B, R2 true m A B -> R2 true (flip m) B A.
  intros m A B r.
  dependent induction r; eauto.
  - constructor. rewrite flip_flip. eauto.
Defined.

Lemma sym2 : forall m A B, R2 true (flip m) A B -> R2 true m B A.
  intros. destruct m; simpl in *.
  assert (Sub = flip Sup) by eauto.
  rewrite H0.
  apply sym; eauto.
  assert (Sup = flip Sub) by eauto.
  rewrite H0.
  apply sym; eauto.
Defined.


Lemma trans : forall A B b m, R2 b m A B -> forall C, R2 b m B C -> R2 b m A C.
  intros A B b m r.
  dependent induction r; intros; eauto.
  - dependent destruction H; eauto. 
    dependent destruction H; simpl in *.
    destruct m; inversion x.
    apply sym2 in H.
    apply sym2 in H0; eauto.
  - dependent induction r; eauto.
    clear IHr1. clear IHr2.
    dependent induction H; eauto.
    apply sym2 in r1.
    apply sym2 in r2.
    
    
                     

Fixpoint check (n : nat) (b : bool) (m : Mode) (A : typ) (B : typ) : option bool :=
  match (n, b, A, B) with
  | (_, _,typ_int, typ_int) => Some true
  | (S i, _, typ_arrow A1 A2, typ_arrow B1 B2) =>
    match (check i true (flip m) A1 B1, check i true m A2 B2) with
    | (Some b1, Some b2) => Some (andb b1 b2)
    | _ => None
    end
  | (S i, true,_,_) => check i false (flip m) B A
  | _ => Some false
  end.

Definition RCheck m A B := exists n, check n true m A B = Some true.

Lemma decideCheck : forall n b m A B,
    check n b m A B = Some true \/ not (check n b m A B = Some true).
  induction n; intros; eauto.
  - destruct b; destruct A; destruct B; simpl; eauto;
      try (right; unfold not; intros I; inversion I; fail).
  - destruct b; destruct A; destruct B; simpl;
      try (right; unfold not; intros I; inversion I; fail); eauto.
    + destruct (IHn true (flip m) A1 B1).
      rewrite H.
      destruct (IHn true m A2 B2).
      rewrite H0; eauto.
      destruct (check n true m A2 B2); eauto.
      destruct (check n true (flip m) A1 B1); eauto.
      destruct b; eauto.
      destruct (IHn true m A2 B2); eauto.
      rewrite H0; eauto.
      destruct (check n true m A2 B2); eauto.
    + destruct (IHn true (flip m) A1 B1).
      rewrite H.
      destruct (IHn true m A2 B2).
      rewrite H0; eauto.
      destruct (check n true m A2 B2); eauto.
      destruct (check n true (flip m) A1 B1); eauto.
      destruct b; eauto.
      destruct (IHn true m A2 B2); eauto.
      rewrite H0; eauto.
      destruct (check n true m A2 B2); eauto.
Defined.      

Lemma soundAlg : forall n b m A B, check n b m A B = Some true -> RS m A B.
  induction n; intros; eauto.
  - destruct b; destruct A; destruct B; simpl in H; try (inversion H; fail); eauto.
  - destruct b; destruct A; destruct B; simpl in H; try (inversion H; fail); eauto.
    + destruct (decideCheck n true (flip m) A1 B1).
      rewrite H0 in H; eauto.
      destruct (decideCheck n true m A2 B2); eauto.
      destruct (check n true m A2 B2); try contradiction.
      destruct (check n true (flip m) A1 B1); try contradiction.
      destruct b; simpl in *; try contradiction.
      destruct (check n true m A2 B2); try contradiction.
      inversion H.
    + destruct (decideCheck n true (flip m) A1 B1).
      rewrite H0 in H; eauto.
      destruct (decideCheck n true m A2 B2); eauto.
      destruct (check n true m A2 B2); try contradiction.
      destruct (check n true (flip m) A1 B1); try contradiction.
      destruct b; simpl in *; try contradiction.
      destruct (check n true m A2 B2); try contradiction.
      inversion H.
Defined.

Lemma monotoneCheck :
  forall i j,
    i >= j -> forall b m A B, 
      check j b m A B = Some true -> check i b m A B = Some true.
  induction j; intros; eauto.
  - destruct b; destruct A; destruct B; simpl in H0; try (inversion H0; fail); eauto.
    induction i; eauto.
    induction i; eauto.
  - destruct b; destruct A; destruct B; simpl in H0; try (inversion H0; fail); eauto.
Admitted.

Lemma rcheck_sym : forall m A B, RCheck m A B -> RCheck (flip m) B A.
  intros.
  unfold RCheck in *.
  destruct H.
  exists (S x).
  destruct A. admit. admit.
  destruct B. admit. admit.
  simpl in *; auto.
  destruct x; simpl in *. eauto.
  destruct x; simpl in *; eauto.
  simpl in *; eauto.
Admitted.

Lemma rcheck_sym2 : forall m A B, RCheck (flip m) A B -> RCheck m B A.
  destruct m; intros.
  simpl in H.
  assert (Sub = flip Sup) by eauto.
  rewrite H0. apply rcheck_sym. auto.
  simpl in H.
  assert (Sup = flip Sub) by eauto.
  rewrite H0. apply rcheck_sym. auto.
Defined.

Lemma completeAlg : forall m A B, RS m A B -> RCheck m A B.
  intros.
  induction H.
  - exists 0. simpl; auto.
  - admit.
  - destruct IHRS1. destruct IHRS2.
    exists (S (max x x0)).
    simpl.
    assert (check (Nat.max x x0) true (flip m) A C = Some true) by admit.
    rewrite H3.
    assert (check (Nat.max x x0) true m B D = Some true) by admit.
    rewrite H4. simpl. auto.
  - apply rcheck_sym2. auto.
Admitted.