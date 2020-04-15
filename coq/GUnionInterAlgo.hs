import Prelude hiding (flip, and, or)

data Op = And | Or deriving (Show,Eq)

data Typ = TInt | TArrow Typ Typ | TOp Op Typ Typ | TBot | TTop deriving (Show, Eq)

data Mode = Sub | Sup deriving Show

mode_to_sub Sub = TTop
mode_to_sub Sup = TBot

flip Sub = Sup
flip Sup = Sub

choose Sub = And
choose Sup = Or

duo :: Bool -> Mode -> Typ -> Typ -> Bool
duo f m TInt TInt                        = True
duo f m _ b | b == mode_to_sub m         = True
duo f m (TArrow a b) (TArrow c d)        = duo True (flip m) a c && duo True m b d
duo f m (TOp op a b) c | choose m == op  = duo True m a c || duo True m b c
duo f m a (TOp op b c) | choose m == op  = duo True m a b && duo True m a c
duo True m a b                           = duo False (flip m) b a
duo _ _ _ _                              = False

sub = duo True Sub

and = TOp And

or = TOp Or

t1 = TInt

t2 = and TInt TInt

t3 = and TInt (TArrow TInt TInt)

t4 = or TInt (TArrow TInt TInt)

t5 = or TInt TInt