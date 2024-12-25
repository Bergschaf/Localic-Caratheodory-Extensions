import Leroy.Open_Subframes
import Mathlib.Tactic.Propose

variable {X Y E: Type u} [x_frm : Order.Frame X] [Order.Frame Y] [Order.Frame E]


def alt_sInf_fun (s : Set (Nucleus X)) (a : X) := sSup {j a | j ∈ s}





lemma increasing : ∀ (x : X), x ≤ alt_sInf_fun s x := by

  simp [alt_sInf_fun]
  intro x
  apply le_sSup_iff.mpr
  simp [upperBounds]
  intro b h
  sorry -- gilt nur wenn s nicht leer ist



lemma idempotent : ∀ (x : X), alt_sInf_fun s (alt_sInf_fun s x) = alt_sInf_fun s x := by
  sorry


lemma preserves_inf : ∀ (x y : X), alt_sInf_fun s (x ⊓ y) = alt_sInf_fun s x ⊓ alt_sInf_fun s y := by
  simp only [alt_sInf_fun]
  intro x y
  sorry



def alt_sInf (s : Set (Nucleus X)) : Nucleus X where
  toFun := alt_sInf_fun s
  idempotent := sorry
  increasing := sorry
  preserves_inf := sorry


lemma le_alt_sInf :  ∀ (s : Set (Nucleus E)) (a : Nucleus E), (∀ b ∈ s, a ≤ b) → a ≤ alt_sInf s := by
  intro s a h
  simp [alt_sInf, alt_sInf_fun]
  intro v
  simp only [Nucleus.toFun_eq_coe]
  simp [alt_sInf_fun]
  intro a1 h1
  exact h a1 h1 v

lemma alt_sInf_le : ∀ (s : Set (Nucleus E)), ∀ a ∈ s, alt_sInf s ≤ a := by
  intro s x h1 e
  simp [alt_sInf, alt_sInf_fun]
  apply le_sSup
  simp
  exact Filter.frequently_principal.mp fun a => a h1 rfl


/--
Source : https://proofwiki.org/wiki/Infimum_is_Unique
-/
lemma alt_sInf_eq_sInf (s : Set (Nucleus X)): sInf s = alt_sInf s := by
  have h : ∀ x ∈ lowerBounds s, x ≤ sInf s := by
    exact fun x a => Nucleus_le_sInf s x a
  have h1 : ∀ x ∈ lowerBounds s, x ≤ alt_sInf s := by
    exact fun x a => le_alt_sInf s x a

  have h2 : sInf s ∈ lowerBounds s := by
    simp [lowerBounds]
    intro a h
    apply sInf_le
    exact h

  have h3 : alt_sInf s ∈ lowerBounds s := by
    simp [lowerBounds]
    intro a h
    exact alt_sInf_le s a h

  apply le_antisymm
  . exact h1 (sInf s) h2
  . exact h (alt_sInf s) h3

#print axioms alt_sInf_eq_sInf


lemma sup_closed  (f : FrameHom X Y)  (x y : ↑(Set.range ⇑f)) : ↑x ⊔ ↑y ∈ Set.range ⇑f := by
  refine Set.mem_range.mpr ?_
  have h1 (x : Set.range f) : ∃ x1, f x1 = x := by
    have h : x.val ∈ Set.range f := by
      exact Subtype.coe_prop x
    rw [Set.mem_range] at h
    exact h
  let x1 := Classical.choose (h1 x)
  let y1 := Classical.choose (h1 y)
  use x1 ⊔ y1
  rw [@map_sup]
  let hx1 := Classical.choose_spec (h1 x)
  rw [hx1]
  let hx2 := Classical.choose_spec (h1 y)
  rw [hx2]


def FrameHom_image_Frame (f : FrameHom X Y) : Order.Frame ↑(Set.range f) where
  sup x y := ⟨x ⊔ y, sup_closed f x y⟩
  le_sup_left := (by simp only [Subtype.forall, Set.mem_range, forall_exists_index,
    Subtype.mk_le_mk, le_sup_left, implies_true])
  le_sup_right := (by simp only [Subtype.forall, Set.mem_range, Subtype.mk_le_mk, le_sup_right,
    implies_true])
  sup_le := (by simp only [Subtype.forall, Set.mem_range, Subtype.mk_le_mk, sup_le_iff,forall_exists_index, forall_apply_eq_imp_iff];exact
    fun a a_1 a_2 a_3 a_4 => ⟨a_3, a_4⟩)
  inf x y := ⟨x ⊓ y, sorry⟩
