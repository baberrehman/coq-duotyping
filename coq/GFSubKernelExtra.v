Set Implicit Arguments.
Require Import TLC.LibLN.
Require Import GFSubKernel.

(* 

RS is the declarative specification of subtyping, which
includes the built-in Sym rule.

*)

Inductive RS : env -> Mode -> typ -> typ -> Prop :=
| RSInt : forall m E, okt E -> RS E m typ_int typ_int
| RSTB1 : forall A m E, okt E -> wft E A -> RS E m A (mode_to_sub m)
| RSFun : forall A B C D m E, RS E (flip m) A C -> RS E m B D -> RS E m (typ_arrow A B) (typ_arrow C D)
| RSVarRefl : forall E X m, okt E -> wft E (typ_fvar X) -> RS E m (typ_fvar X) (typ_fvar X)
| RSVarBnd : forall E X m T F, binds X (bind_tRel m T) E -> RS E m T F -> RS E m (typ_fvar X) F
| RSAll : forall E L m1 m2 T1 T2 T3,
    ( forall X, X \notin L ->
                RS (E&(X !: m1 <>: T1)) m2 (T2 open_tt_var X) (T3 open_tt_var X)) -> 
    RS E m2 (typ_all m1 T1 T2) (typ_all m1 T1 T3)
| RSSym : forall m A B E, RS E (flip m) B A -> RS E m A B.

Hint Constructors RS.

Lemma flip_flip : forall m, flip (flip m) = m.
  destruct m; simpl; eauto.
Defined.
    
Lemma sound : forall m A B E, R E m A B -> RS E m A B.
  intros.
  induction H; eauto.
  - apply RSSym.
    apply RSSym in IHR.
    rewrite flip_flip. eauto.
Defined.

Lemma complete : forall m A B E, RS E m A B -> R E m A B.
  intros.
  induction H; eauto.
  - apply SVarBnd with (T := T); eauto.
  - apply SAll with (L := L). auto.
  - apply sym2.
    auto.
Defined.

(* 

R2 an algorithmic version that exploits duality for economy 
of code. 

*)

Inductive R2 : env -> bool -> Mode -> typ -> typ -> Prop :=
| R2Int : forall b m E, okt E -> R2 E b m typ_int typ_int
| R2TB1 : forall b A m E, okt E -> wft E A -> R2 E b m A (mode_to_sub m)
| R2Fun : forall b A B C D m E,
    R2 E true (flip m) A C ->
    R2 E true m B D ->
    R2 E b m (typ_arrow A B) (typ_arrow C D)
| R2VarRefl : forall E X m b, okt E -> wft E (typ_fvar X) -> R2 E b m (typ_fvar X) (typ_fvar X)
| R2VarBnd : forall E X m T F b, binds X (bind_tRel m T) E -> R2 E true m T F -> R2 E b m (typ_fvar X) F
| R2All : forall E L m1 m2 T1 T2 T3 b,
    ( forall X, X \notin L ->
                R2 (E&(X !: m1 <>: T1)) true m2 (T2 open_tt_var X) (T3 open_tt_var X)) -> 
    R2 E b m2 (typ_all m1 T1 T2) (typ_all m1 T1 T3)
| R2Sym : forall m A B E,
    R2 E false (flip m) B A -> R2 E true m A B.

Hint Constructors R2.

(* Soundness of R2 *)

Require Import Program.Equality.

Lemma R2_false : forall m A B E, R2 E false m A B -> R2 E true m A B.
  intros.
  dependent induction H; eauto.
Defined.

Lemma invR2 : forall b m A B E, R2 E b m A B -> R2 E true (flip m) B A.
  intros. 
  induction H; eauto.
  - apply R2Sym. rewrite flip_flip. eauto.
  - apply R2Sym. rewrite flip_flip. eauto.
  - apply R2_false. auto.
Defined.

Lemma completeR : forall m A B E, R E m A B -> R2 E true m A B.
  intros.
  induction H; eauto.
  - apply invR2 in IHR.
    apply R2Sym.
    rewrite flip_flip in *.
    eauto.
Defined.

Lemma soundR : forall m b A B E, R2 E b m A B -> R E m A B.
  intros.
  induction H; eauto.
  - apply SVarBnd with (T := T); eauto.
  - apply SAll with (L := L). auto.
  - apply sym2. auto.
Defined.




