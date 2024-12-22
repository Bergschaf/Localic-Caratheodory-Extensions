import Leroy.Open_Subframes
import Mathlib.Order.CompleteSublattice

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]



-- complement..

noncomputable def complement (e : Open E) : Nucleus E where
  toFun x := (e.element) ⊔ x
  idempotent := (by simp)
  increasing := (by simp)
  preserves_inf := (by simp;exact fun x y => sup_inf_left e.element x y)


def complement_injective : Function.Injective (@complement E e_frm)  := by
  simp [Function.Injective, complement]
  intro a1 a2 h
  ext
  have h1 : ∀ x, a1.element ⊔ x = a2.element ⊔ x := by
    exact fun x => congrFun h x
  let h2 := h1 ⊥
  simp at h2
  exact h2


lemma inf_complement (X : Open E) : X.nucleus ⊓ (complement X) = ⊥ := by
  apply le_antisymm
  . simp only [Nucleus_min, sInf]
    apply sSup_le
    intro b h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, Set.mem_setOf_eq] at h
    rcases h with ⟨h1, h2⟩
    simp [Nucleus_bot]
    intro v
    rw [← Nucleus.idempotent']
    refine eq_top_iff.mpr ?_
    have h : X.nucleus (b v) ≤ b (b v) := by
      simp at h1
      exact h1 (b v)

    have h2 : X.nucleus (complement X v) ≤ X.nucleus (b v) := by
      simp at h2
      simp at h
      let h2 := h2 v
      apply_fun X.nucleus.toFun at h2
      simp at h2
      exact h2
      simp [Nucleus.monotone]

    apply le_trans ?_ h
    apply le_trans ?_ h2
    simp [complement, Open.nucleus, eckig, e_U]
    refine sup_eq_top_of_top_mem ?_
    simp only [Set.mem_setOf_eq, le_top, inf_of_le_right, le_sup_left]
  . simp [Nucleus_bot]


lemma sup_comp_eq_top (X : Open E)  : X.nucleus ⊔ (complement X) = ⊤ := by
  ext y
  simp [Nucleus_top]

  apply le_antisymm
  .
    apply le_trans (union_pointwise_le y)
    simp [complement]
    rw [@inf_sup_left]
    simp only [sup_le_iff, inf_le_right, and_true]
    simp [Open.nucleus, eckig, e_U]
    rw [@sSup_inf_eq]

    simp only [Set.mem_setOf_eq, iSup_le_iff, imp_self, implies_true]

  . exact Nucleus.increasing' (↑X ⊔ complement X)

@[ext]
structure Closed (E : Type*) [Order.Frame E] where
  element : E

noncomputable def Closed.nucleus (c : Closed E) : Nucleus E :=
  complement ⟨c.element⟩

@[simp]
instance : LE (Closed E) where
  le x y := x.nucleus ≤ y.nucleus


lemma le_antisymm' :  ∀ (a b : Closed E), a ≤ b → b ≤ a → a = b := by
  intro a b h1 h2
  ext
  simp_all [Closed.nucleus]
  have h : complement ⟨a.element⟩ = complement ⟨b.element⟩ := by
    ext x
    apply le_antisymm
    exact h2 x
    exact h1 x
  apply_fun (fun x ↦ (⟨x⟩ : Open E))
  apply_fun (fun x ↦ complement x)
  simp
  exact h
  exact complement_injective
  simp [Function.Injective]


instance Closed_sSup : PartialOrder (Closed E) where
  le_refl := (by simp)
  le_trans x y z := (by simp[le];exact fun a a_1 v => Preorder.le_trans (z.nucleus v) (y.nucleus v) (x.nucleus v) (a_1 v) (a v))
  le_antisymm  := le_antisymm'

def Nucleus.closure (x : Nucleus X) : Closeds X := ⟨sInf {w : Nucleus X | is_closed w ∧ x ≤ w}, (by sorry)⟩

noncomputable def complement_closeds (x : Closeds X ) : Opens X :=
  Classical.choose x.prop
