import Leroy.Measure.Regular

variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]
variable (E' : Type*) [Order.Frame E']

variable {m : @Measure E' _}


-- TODO Infrastruktur, dass man Sublocals als Local ansehen kann

def e_μ (u : E') : E' := (sSup {w : Open E' | w ≤ u ∧ m.toFun w = m.toFun u}).element

def μ_Reduction : Nucleus E' where
  toFun := e_μ E'
  idempotent := sorry
  increasing := sorry
  preserves_inf := sorry
