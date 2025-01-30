import Leroy.Sublocale
import Mathlib.Order.CompleteLattice
import Mathlib.Tactic
variable {E : Type*} [Order.Frame E]

instance : SupSet (Nucleus E) := OrderDual.supSet (Sublocale E)

instance Nucleus.instCompleteLattice : CompleteLattice (Nucleus E) where
  sup x y := sSup {x, y}
  le_sup_left := (by simp )
  le_sup_right := (by simp )
  sup_le := (by simp ;exact fun a b c a_1 a_2 =>
    ⟨a_1, a_2⟩)
  __ := completeLatticeOfCompleteSemilatticeInf (Nucleus E)

lemma Nucleus.min_eq (a b : Nucleus E) : a ⊓ b = sInf {a, b} := by rfl

lemma Nucleus.max_eq (a b : Nucleus E) : a ⊔ b = sSup {a, b} := rfl

lemma Sublocale.max_eq (a b : Sublocale E) : a ⊔ b = sSup {a, b} := rfl

lemma Sublocale.min_eq {a b : Sublocale E} : a ⊓ b = sInf {a, b} := by rfl

lemma Sublocale_le_Nucleus (a : Sublocale E) (b : Nucleus E) : a ≤ b ↔ b ≤ a.nucleus:= by
  rw [@Sublocale.le_iff]
  simp [Sublocale.nucleus]
  exact Iff.symm (Eq.to_iff rfl)

lemma Sublocale.top_eq :∀ x, (⊤ : Sublocale E) x = x := by
  exact fun x => rfl

lemma Sublocale.bot_eq : ∀ x, (⊥ : Sublocale E) x = ⊤ := by
  exact fun x => rfl

@[simp]
lemma Nucleus_mem_sublocale {a : Nucleus E} {s : Set (Sublocale E)} : a ∈ s ↔ a ∈ (Sublocale.nucleus '' s):= by
  exact Iff.symm (Set.mem_image_iff_of_inverse (congrFun rfl) (congrFun rfl))

lemma Nucleus_mem_sublocale' {a : Nucleus E} {s : Set (Sublocale E)} {p : Nucleus E → Prop} : (∀ a ∈ s, p a) ↔ (∀ a ∈ (Sublocale.nucleus '' s), p a) := by
  exact Iff.symm Set.forall_mem_image
lemma Nucleus.le_iff : ∀ a b : Nucleus E, a ≤ b ↔ ∀ i, a i ≤ b i := by exact fun a b => Eq.to_iff rfl

lemma mal_wieder : ∀ (a : Nucleus E) (s : Set (Nucleus E)), a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b := by
  intro a s
  simp only [iSup_le_iff, le_iSup_iff]
  intro b h
  simp [sSup, sInf, Nucleus.min_eq, Nucleus.le_iff]
  rw [← Nucleus.toFun_eq_coe]
  simp [sInf_fun]
  --
  intro i
  rw [sInf_le_iff]
  simp [lowerBounds]
  intro c h1
  have h3 : c ≤ a i := by
    let h1 := @h1 (a i)
    simp at h1
    exact h1

  let h4 := @h1 ((sSup s) i)
  simp [sInf, sSup] at h4
  repeat rw [← Nucleus.toFun_eq_coe] at h4
  simp [sInf_fun] at h4





  let j : Nucleus E := sorry
  have h5 : j ∈ s := by sorry
  let h6 := h j h5
  rw [Nucleus.le_iff] at h6
  apply le_trans' (h6 i)
  rw [Nucleus.min_eq]
  simp_rw [sInf]
  rw [← Nucleus.toFun_eq_coe]
  simp [sInf_fun]
  intro b h7
  cases h7 with
  | inl h => exact le_of_le_of_eq h3 h
  | inr h =>
    let h8 := h4 (sSup s)
    rw [Nucleus_mem_sublocale] at h8
    simp at h8
    let h9 := h8 (sSup s) (by exact fun a a_1 => CompleteLattice.le_sSup s a a_1) (by simp [Sublocale.nucleus];exact
      rfl)
    apply le_trans h9
    rw [← h]




















def minax : Order.Frame.MinimalAxioms (Nucleus E) where
  inf_sSup_le_iSup_inf := mal_wieder


-- Temporary until the frame problem gets better
instance (priority := high): BoundedOrder (Sublocale E) := by exact OrderDual.instBoundedOrder (Nucleus E)

instance (priority := high) : OrderTop (Sublocale E) := by exact OrderDual.instOrderTop (Nucleus E)
---
instance (priority := 0) Nucleus.instFrame : Order.Frame (Nucleus E) :=
  Order.Frame.ofMinimalAxioms minax

example : ∀ (u : Sublocale E), ⊤ ≤ u ↔ u = ⊤ := fun u => top_le_iff
