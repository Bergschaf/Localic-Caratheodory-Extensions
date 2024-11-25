import Leroy.Nucleus
import Leroy.Subframes
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice

open CategoryTheory
variable {X F E: Type u} [Order.Frame X] [Order.Frame F] [Order.Frame E]

--def Im (f : FrameHom X Y) : Subframe Y := sInf {y : Subframe Y | }
-- Leroy CH 5
--def f_obenster_f_untenstern_nucleus (f : FrameHom X Y )
--def nucleus_embedding (e : E ⥤ E) [Nucleus e]: ∃ f : FrameHom E E, Leroy_Embedding f:= sorry
def nucleus_embedding (e : E ⥤ E) [Nucleus e]: FrameHom E E := sorry


def direct_image (f : FrameHom F E) : Subframe E → Subframe F := by
  intro e
  let n := e.nucleus
  let c := FrameHom.comp (nucleus_embedding e.e) f
  let nucleus := (f_obenstern c) ⋙ (f_untenstern c)
  let nucleus_nucleus : Nucleus nucleus := sorry
  let s : Subframe F := ⟨nucleus, nucleus_nucleus⟩
  exact s
