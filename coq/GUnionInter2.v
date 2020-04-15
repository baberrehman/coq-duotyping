
Set Implicit Arguments.

(* ********************************************************************** *)
(** * Description of the Language *)

(** Representation of types *)

Inductive typ : Set :=
  | typ_btm   : typ
  | typ_top   : typ
  | typ_int   : typ
  | typ_arrow : typ -> typ -> typ
  | And       : typ -> typ -> typ
  | Or        : typ -> typ -> typ.


(** Representation of pre-terms *)

(** Generalized Subtyping Judgements *)

Inductive Mode := Sub | Sup.

Definition flip (m : Mode) : Mode :=
  match m with
  | Sub => Sup
  | Sup => Sub
  end.

Definition choose (m : Mode) : typ -> typ -> typ :=
  match m with
  | Sub => And
  | Sup => Or
  end.

Definition mode_to_sub m :=
  match m with
  | Sub => typ_top
  | Sup => typ_btm
  end.

Inductive R : Mode -> typ -> typ -> Prop :=
  | SInt   : forall m, R m typ_int typ_int
  | STB1   : forall A m, R m A (mode_to_sub m)
  | STB2   : forall A m, R m (mode_to_sub (flip m)) A
  | SFun   : forall A B C D m, R (flip m) A C -> R m B D -> R m (typ_arrow A B) (typ_arrow C D)
  | SLeft1  : forall A B C m, R m A C -> R m (choose m A B) C
  | SLeft2  : forall A B C m, R m A B -> R m A (choose (flip m) B C)
  | SRight1 : forall A B C m, R m B C -> R m (choose m A B) C
  | SRight2 : forall A B C m, R m A C -> R m A (choose (flip m) B C)
  | SBoth1  : forall A B C m, R m A B -> R m A C -> R m A (choose m B C)
  | SBoth2  : forall A B C m, R m A C -> R m B C -> R m (choose (flip m) A B) C.

Hint Constructors R.

Lemma sym : forall A B m, R m A B -> R (flip m) B A.
  intros.
  induction H; eauto.
  - destruct m; simpl; apply STB2.
  - destruct m; simpl in *; apply SLeft2; auto.    
  - destruct m; simpl in *; apply SRight2; auto.
  - destruct m; simpl in *; apply SBoth2; auto.
Defined.    

Lemma refl : forall A m, R m A A.
  induction A; intros; eauto; destruct m; simpl in *; eauto.
  - apply STB2.
  - apply STB1.
  - apply STB1.
  - apply STB2.
  - apply SBoth1. apply SLeft1; eauto. apply SRight1; eauto.
  - apply SBoth2. apply SLeft2; eauto. apply SRight2; eauto.
  - apply SBoth2. apply SLeft2; eauto. apply SRight2; eauto.
  - apply SBoth1. apply SLeft1; eauto. apply SRight1; eauto.
Defined.

Require Import Program.Equality.

Inductive BoundLike (m : Mode) (A : typ) :=.

Inductive Bound m : typ -> typ -> Prop :=
  | Bnd : forall C, (forall A, R m A C) -> Bound m (mode_to_sub m) C
  | Choose : forall A B C, R m A C -> R m B C -> Bound m (choose (flip m) A B) C
  | Base : forall A C, BoundLike m C -> Bound m A C
  | Int : Bound m typ_int typ_int
  | ArrowInd : forall A B C D, Bound (flip m) A C -> Bound m B D -> Bound m (typ_arrow A B) (typ_arrow C D).

Hint Constructors Bound.

Lemma c : forall m A B, Bound m A B -> R m A B.
  intros.
  induction H; eauto.
Admitted.

Lemma s : forall m A B, R m A B -> Bound m A B.
Admitted.

Lemma trans : forall A B m, R m A B -> forall C, Bound m B C -> R m A C.
  induction 1; intros; eauto.
  - apply c in H. auto.
  - dependent destruction H; eauto.
    destruct m; inversion x.
    admit.
    destruct m; inversion x.
    destruct m; inversion x.
  - dependent induction H1; eauto.
    destruct m; inversion x.
    admit.
  - dependent destruction H0; eauto.
    destruct m; dependent destruction x.
    apply IHR. apply s. auto.
    
  
  
  
Admitted.

Lemma invChoose : forall m A B C, R m A (choose m B C) -> R m A B /\ R m A C.
  intros m A B C r.
  dependent induction r; eauto.
  destruct m; simpl in x; inversion x.
  destruct m; simpl in x; inversion x.
  destruct m; simpl in x; inversion x.
  destruct (IHr _ _ eq_refl). split; apply SLeft1; auto.
  destruct m; simpl in x; inversion x.
  destruct (IHr _ _ eq_refl). split; apply SRight1; auto.
  destruct m; simpl in x; inversion x.
  destruct m; simpl in x; inversion x; subst; split; auto.
  destruct (IHr1 _ _ eq_refl).
  destruct (IHr2 _ _ eq_refl).
  split; apply SBoth2; eauto.
Defined.

Lemma flip_flip : forall m A C, R (flip (flip m)) A C -> R m A C.
  intros.
  destruct m; simpl in *; eauto.
Defined.

Lemma invChoose2 : forall m A B C, R m (choose (flip m) A B) C -> R m A C /\ R m B C.
  intros.
  apply sym in H. apply invChoose in H. destruct H.
  apply sym in H. apply sym in H0.
  apply flip_flip in H. apply flip_flip in H0.
  split; auto.
Defined.
 
Lemma invBound : forall m C, R m (mode_to_sub m) C -> forall A, R m A C.
  intros m C r.
  destruct m; dependent induction r; intros; eauto.
Defined.

Lemma invBound2 : forall m A, R m A (mode_to_sub (flip m)) -> forall C, R m A C.
  intros m A r.
  destruct m; dependent induction r; intros; eauto.
Defined.

Lemma trans : forall A B m, R m A B -> forall C, R m B C -> R m A C.
  intros A B m r.
  induction r; intros; eauto.
  - apply invBound. auto.
  - dependent induction H; simpl in *; auto.
    destruct m; simpl in x; inversion x.
    destruct m; simpl in x; inversion x.
    apply SLeft2. eapply IHR; eauto.
    destruct m; simpl in x; inversion x.
    apply SRight2. eapply IHR; eauto.
    apply SBoth1; eauto.
    destruct m; simpl in x; inversion x.
  - apply invChoose2 in H. destruct H. apply IHr. auto.
  - apply invChoose2 in H. destruct H. apply IHr. auto.
  - dependent induction H; simpl in *; auto.
    destruct m; simpl in x; inversion x.
    destruct m; simpl in x; inversion x.
    destruct m; simpl in x; inversion x.
    destruct m; simpl in x; inversion x; subst; eauto.
    apply SLeft2; apply (IHR B C); eauto.
    destruct m; simpl in x; inversion x; subst; eauto.
    apply SRight2; apply (IHR B C); eauto.
    apply SBoth1.
    eapply (IHR1 B C); eauto. 
    eapply (IHR2 B C); eauto.
    destruct m; simpl in x; inversion x; subst; eauto.
Defined.

(* An equivalent formulation *)

Inductive S : Mode -> typ -> typ -> Prop :=
  | SSInt   : forall m, S m typ_int typ_int
  | SSTB   : forall A m, S m A (mode_to_sub m)
  | SSFun   : forall A B C D m, S (flip m) A C -> S m B D -> S m (typ_arrow A B) (typ_arrow C D)
  | SSLeft  : forall A B C m, S m A C -> S m (choose m A B) C
  | SSRight : forall A B C m, S m B C -> S m (choose m A B) C
  | SSBoth  : forall A B C m, S m A B -> S m A C -> S m A (choose m B C)
  | SSSym   : forall A B m, S (flip m) B A -> S m A B.

Hint Constructors S.

Lemma sound : forall m A B, R m A B -> S m A B.
  intros.
  induction H; eauto.
  destruct m; simpl in *. apply SSSym. simpl.
  apply SSLeft. apply SSSym. simpl. auto.
  apply SSSym. simpl.
  apply SSLeft. apply SSSym. simpl. auto.
  destruct m; simpl in *. apply SSSym. simpl.
  apply SSRight. apply SSSym. simpl. auto.
  apply SSSym. simpl.
  apply SSRight. apply SSSym. simpl. auto.
  destruct m; simpl in *. apply SSSym. simpl.
  apply SSBoth. apply SSSym. simpl. auto.
  apply SSSym. simpl. auto.
  apply SSSym. simpl.
  apply SSBoth. apply SSSym. simpl. auto.
  apply SSSym. simpl. auto.
Defined.

Lemma complete : forall m A B, S m A B -> R m A B.
  intros.
  induction H; eauto.
  apply sym in IHS. apply flip_flip in IHS.
  auto.
Defined.