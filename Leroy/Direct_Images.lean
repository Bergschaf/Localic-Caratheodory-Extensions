import Leroy.Nucleus
import Leroy.Subframes
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice

open CategoryTheory
variable {X F E: Type u} [Order.Frame X] [Order.Frame F] [frm_e : Order.Frame E]


noncomputable def direct_image (f : FrameHom F E) : Nucleus E → Nucleus F := by
  intro e
  let i := (@nucleus_frameHom E frm_e e)
  let c := FrameHom.comp i.val f
  let nucleus := (f_obenstern c) ⋙ (f_untenstern c)
  have h : (∃ X, ∃ (x : Order.Frame X),∃ (f : FrameHom F X), nucleus.obj = (f_obenstern f ⋙ f_untenstern f).obj) := by
    use (e : Set E)
    let x := image_frame e
    use x
    use c
  let nucleus_nucleus := frameHom_nucleus h
  exact Classical.choose nucleus_nucleus
