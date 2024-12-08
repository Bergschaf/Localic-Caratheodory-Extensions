import Leroy.Open_Subframes
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]

-- complement..


def compl (e : Nucleus E) : Nucleus E where
  toFun := -- TODO noa fragen
