import Leroy.Nucleus
import Leroy.Subframes
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice

open CategoryTheory
variable {X F E: Type u} [Order.Frame X] [Order.Frame F] [frm_e : Order.Frame E]

--def Im (f : FrameHom X Y) : Subframe Y := sInf {y : Subframe Y | }
-- Leroy CH 5
--def f_obenster_f_untenstern_nucleus (f : FrameHom X Y )
--def nucleus_embedding (e : E ⥤ E) [Nucleus e]: ∃ f : FrameHom E E, Leroy_Embedding f:= sorry
def nucleus_embedding (e : Nucleus E) : FrameHom E E := sorry
  -- falsch wahrscheinlich

def direct_image (f : FrameHom F E) : Nucleus E → Nucleus F := by
  intro e
  let c := FrameHom.comp (nucleus_embedding e) f
  let nucleus := (f_obenstern c) ⋙ (f_untenstern c)
  have h : (∃ X, ∃ (x : Order.Frame X),∃ (f : FrameHom F X), nucleus.obj = (f_obenstern f ⋙ f_untenstern f).obj) := by
    use E
    use frm_e
    use c
  let nucleus_nucleus := frameHom_nucleus h
  exact Classical.choose nucleus_nucleus
