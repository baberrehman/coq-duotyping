Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import GUnionInter.

(* 

RS is the declarative specification of subtyping, which
includes the built-in Sym rule.

*)

Inductive RS : Mode -> typ -> typ -> Prop :=
| RSInt : forall m, RS m typ_int typ_int
| RSTB1 : forall A m, RS m A (mode_to_sub m)
| RSFun : forall A B C D m, RS (flip m) A C -> RS m B D -> RS m (typ_arrow A B) (typ_arrow C D)
| RLeft  : forall A B C m, RS m A C -> RS m (choose m A B) C
| RRight : forall A B C m, RS m B C -> RS m (choose m A B) C
| RBoth  : forall A B C m, RS m A B -> RS m A C -> RS m A (choose m B C)
| RSSym : forall m A B, RS (flip m) B A -> RS m A B.

Hint Constructors RS.

Lemma flip_flip : forall m, flip (flip m) = m.
  destruct m; simpl; eauto.
Defined.

Lemma invSym : forall m A B, RS m A B -> RS (flip m) B A.
  intros.
  rewrite <- (flip_flip m) in H.
  apply RSSym in H.
  auto.
Defined.
  
Lemma sound : forall m A B, R m A B -> RS m A B.
  intros.
  induction H; eauto.
  - apply RSSym.
    apply invSym in IHR.
    apply RLeft. auto.
  - apply RSSym.
    apply invSym in IHR.
    apply RRight. auto.
  - apply RSSym.
    apply invSym in IHR1.
    apply invSym in IHR2.
    apply RBoth; auto.
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
| R2Left  : forall A B C b m, R2 true m A C -> R2 b m (choose m A B) C
| R2Right : forall A B C b m, R2 true m B C -> R2 b m (choose m A B) C
| R2Both  : forall A B C b m, R2 true m A B -> R2 true m A C -> R2 b m A (choose m B C)
| R2Sym : forall m A B,
    R2 false (flip m) B A -> R2 true m A B.

Hint Constructors R2.

(* Soundness of R2 *)

Require Import Program.Equality.

Lemma soundR : forall m b A B, R2 b m A B -> R m A B.
  intros.
  induction H; eauto.
  apply sym2. auto.
Defined.

Lemma R2_false : forall m A B, R2 false m A B -> R2 true m A B.
  intros.
  dependent induction H; eauto.
Defined.

Lemma invR2 : forall b m A B, R2 b m A B -> R2 true (flip m) B A.
  intros. 
  induction H; eauto.
  - apply R2Sym. rewrite flip_flip. eauto.
  - apply R2Sym. rewrite flip_flip. eauto.
  - apply R2Sym. rewrite flip_flip. eauto.
  - apply R2Sym. rewrite flip_flip. eauto.
  - apply R2_false. auto.
Defined.
 
Lemma completeR : forall m A B, R m A B -> R2 true m A B.
  intros.
  induction H; eauto.
  - apply R2Sym.
    apply R2Left.
    apply (@invR2 true).
    auto.
  - apply R2Sym.
    apply R2Right.
    apply (@invR2 true).
    auto.
  - apply R2Sym.
    apply R2Both.
    apply (@invR2 true).
    auto.
    apply (@invR2 true).
    auto.
Defined.
