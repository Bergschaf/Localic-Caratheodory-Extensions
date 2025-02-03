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

lemma Nucleus.min_eq' (a b : Nucleus E) : ∀ i, (a ⊓ b) i = a i ⊓ b i := by
  intro i
  simp_rw [Nucleus.min_eq, sInf]
  simp [sInf_fun,Set.setOf_or]
  exact inf_comm (b i) (a i)

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


instance {α : Type*} [CompleteLattice α] [HeytingAlgebra α] : Order.Frame α := sorry

def himp_toFun (x y : Nucleus E) (a : E) :=
  ⨅ b ≥ a, x b ⇨ y b


def himp_idempotent (x y : Nucleus E) (a : E) :
    himp_toFun x y (himp_toFun x y a) ≤  himp_toFun x y a := by
  simp [himp_toFun]
  intro i hi
  simp [iInf]
  rw [← sInf_pair]
  rw [sInf_le_iff]
  simp [lowerBounds]
  intro b h1 h2
  sorry

def himp_le_apply (x y : Nucleus E) (a : E) :
    a ≤ himp_toFun x y a := by
  simp [himp_toFun]
  intro i hi
  refine inf_le_of_left_le ?_
  apply le_trans hi y.le_apply

def himp_Nucleus (x y : Nucleus E) : Nucleus E where
  toFun := himp_toFun x y
  idempotent' a := himp_idempotent x y a
  le_apply' a := himp_le_apply x y a
  map_inf' a b := sorry

instance : HImp (Nucleus E) where
  himp x y := himp_Nucleus x y

lemma le_himp_iff'' : ∀ (a b c : Nucleus E), a ≤ b ⇨ c ↔ a ⊓ b ≤ c := by
  intro a b c
  simp [himp, himp_Nucleus]
  apply Iff.intro
  . intro h
    simp [Nucleus.le_iff, himp_toFun, Nucleus.min_eq'] at *
    intro i
    apply h i i
    rfl
  . intro h
    simp [Nucleus.le_iff, himp_toFun, Nucleus.min_eq'] at *
    intro i j h1
    have h2 : a i ⊓ b j ≤ a j ⊓ b j := by
      simp
      apply inf_le_of_left_le
      exact OrderHomClass.GCongr.mono a h1
    apply le_trans h2
    apply h

lemma le_sup_inf_Nucleus : ∀ (x y z : Nucleus E), (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z := by
  intro x y z
  simp_rw [Nucleus.le_iff,Nucleus.min_eq, Nucleus.max_eq]
  simp_rw [sInf, sSup]
  simp [sInf_fun, Set.setOf_or]
  intro i
  simp_rw [Sublocale.min_eq, sInf]
  simp [sSup, sInf_fun]
  intro a h1
  rw [Nucleus_mem_sublocale] at h1
  simp [Sublocale.nucleus] at h1
  rcases h1 with ⟨h1, h2⟩
  simp [Sublocale.le_iff, sInf_fun, Set.setOf_or] at h2
  --
  apply le_trans' (h2 i)
  simp only [le_inf_iff]
  apply And.intro
  . rw [← sInf_pair]
    rw [sInf_le_iff]
    simp [lowerBounds]
    intro b h3 h4

    let h5 := h4 (a ⊔ y) (by rw [Nucleus_mem_sublocale]; simp [Sublocale.nucleus];sorry)
    simp_rw [Nucleus.max_eq, sSup,sInf] at h5
    simp [sSup, sInf_fun] at h5

    sorry
  sorry


instance : DistribLattice (Nucleus E) where
  le_sup_inf := le_sup_inf_Nucleus

/--
Source: Stone Spaces pp. 51
-/
instance : HeytingAlgebra (Nucleus E) := HeytingAlgebra.ofHImp (· ⇨ ·) le_himp_iff''


-- Temporary until the frame problem gets better
instance (priority := high): BoundedOrder (Sublocale E) := by exact OrderDual.instBoundedOrder (Nucleus E)

instance (priority := high) : OrderTop (Sublocale E) := by exact OrderDual.instOrderTop (Nucleus E)
---


example : ∀ (u : Sublocale E), ⊤ ≤ u ↔ u = ⊤ := fun u => top_le_iff
