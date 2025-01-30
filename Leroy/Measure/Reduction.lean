import Leroy.Measure.Regular

--variable {E : Type*} [e_frm : Order.Frame E] [e_regular : Fact (regular E)]
variable {E' : Type*} [Order.Frame E']

variable {m : @Measure E' _}


-- TODO Infrastruktur, dass man Sublocals als Local ansehen kann

def e_μ (m : @Measure E' _) (u : E') : E' := (sSup {w : Open E' | w ≤ u ∧ m.toFun w = m.toFun u}).element

lemma e_μ_idempotent (m : @Measure E' _) : ∀ (x : E'), e_μ m (e_μ m x) ≤ e_μ m x := by
  simp [e_μ, ← Open.le_iff]
  intro x a h1 h2
  apply le_sSup
  simp
  simp [Open.le_iff] at h1
  rw [← Open.le_iff] at h1
  apply And.intro
  . apply le_trans h1
    simp only [sSup_le_iff, Set.mem_setOf_eq, and_imp]
    intro a b c
    exact Open.le_iff.mpr b
  . rw [h2]
    apply Measure.monotone
    ext
    simp
    rw [← Open.ext_iff]
    simp only [le_antisymm_iff, sSup_le_iff, Set.mem_setOf_eq, and_imp, le_refl, and_self, le_sSup,
      and_true]
    exact fun b a a_1 a_2 => a


lemma e_μ_le_apply (m : @Measure E' _) : ∀ (x : E'), x ≤ e_μ m x := by
  intro x
  simp [e_μ]
  rw [← Open.le_iff]
  apply le_sSup
  simp

lemma e_μ_map_inf (m : @Measure E' _) : ∀ (x y : E'), e_μ m (x ⊓ y) = e_μ m x ⊓ e_μ m y := by
  intro x y
  sorry

def μ_Reduction (m : @Measure E' _): Nucleus E' where
  toFun := e_μ m
  idempotent' x := e_μ_idempotent m x
  le_apply' x := e_μ_le_apply m x
  map_inf' x y:= e_μ_map_inf m x y
