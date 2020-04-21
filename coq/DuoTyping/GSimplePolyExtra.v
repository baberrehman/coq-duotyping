Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import GSimplePoly.

(* 

RS is the declarative specification of subtyping, which
includes the built-in Sym rule.

*)

Inductive RS : Mode -> typ -> typ -> Prop :=
| RSInt : forall m, RS m typ_int typ_int
| RSTB1 : forall A m, RS m A (mode_to_sub m)
| RSFun : forall A B C D m, RS (flip m) A C -> RS m B D -> RS m (typ_arrow A B) (typ_arrow C D)
| RSVarRefl : forall X m, RS m (typ_fvar X) (typ_fvar X)
| RSAll : forall L m T1 T2,
    (forall X, X \notin L ->
               RS m (T1 open_tt_var X) (T2 open_tt_var X)) ->
    RS m (typ_all T1) (typ_all T2)
| RSSym : forall m A B, RS (flip m) B A -> RS m A B.

Hint Constructors RS.
    
Lemma sound : forall m A B, R m A B -> RS m A B.
  intros.
  induction H; eauto.
Defined.

Lemma complete : forall m A B, RS m A B -> R m A B.
  intros.
  induction H; eauto.
  - apply SAll with (L := L). auto.
  - apply sym2.
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
| R2VarRefl : forall X m b, R2 b m (typ_fvar X) (typ_fvar X)
| R2All : forall L m T1 T2 b,
    (forall X, X \notin L ->
               R2 true m (T1 open_tt_var X) (T2 open_tt_var X)) ->
    R2 b m (typ_all T1) (typ_all T2)
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
  - apply SAll with (L := L). auto.
  - apply sym2. auto.
Defined.












