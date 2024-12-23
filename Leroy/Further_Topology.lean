import Leroy.Closed_Sublocals
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]

def Nucleus.interior (x : Nucleus E) := sSup {z : Open E | z ≤ x}

def Nucleus.closure (x : Nucleus E) := sInf {z : Closed E | x ≤ z.nucleus}

def Nucleus.rand (x : Nucleus E) := x.closure.nucleus ⊓ (complement x.interior)

def Nucleus.exterior (x : Nucleus E) := sSup {z : Open E | z.nucleus ⊓ x = ⊥}
