import Leroy.Sublocale
import Mathlib.Order.CompleteLattice

variable {E : Type*} [Order.Frame E]

instance : SupSet (Nucleus E) := OrderDual.supSet (Sublocale E)

instance Nucleus.instCompleteLattice : CompleteLattice (Nucleus E) where
  sup x y := sSup {x, y}
  le_sup_left := (by simp only [sSup_insert, csSup_singleton, le_sup_left, implies_true])
  le_sup_right := (by simp only [sSup_insert, csSup_singleton, le_sup_right, implies_true])
  sup_le := (by simp only [sSup_insert, csSup_singleton, sup_le_iff];exact fun a b c a_1 a_2 =>
    ⟨a_1, a_2⟩)
  __ := completeLatticeOfCompleteSemilatticeInf (Nucleus E)


lemma Nucleus.min_eq (a b : Nucleus E) : a ⊓ b = sInf {a, b} := by rfl

lemma Nucleus.max_eq (a b : Nucleus E) : a ⊔ b = sSup {a, b} := rfl

lemma Sublocale.max_eq (a b : Sublocale E) : a ⊔ b = sSup {a, b} := rfl

lemma Sublocale.min_eq {a b : Sublocale E} : a ⊓ b = sInf {a, b} := by rfl

lemma Sublocale_le_Nucleus (a : Sublocale E) (b : Nucleus E) : a ≤ b ↔ b ≤ a.nucleus:= by
  rw [@Sublocale.le_iff]
  simp [Sublocale.nucleus]
  exact Iff.symm Nucleus.le_iff

lemma Sublocale.top_eq :∀ x, (⊤ : Sublocale E) x = x := by
  exact fun x => rfl

lemma Sublocale.bot_eq : ∀ x, (⊥ : Sublocale E) x = ⊤ := by
  exact fun x => rfl

@[simp]
lemma Nucleus_mem_sublocale {a : Nucleus E} {s : Set (Sublocale E)} : a ∈ s ↔ a ∈ (Sublocale.nucleus '' s):= by
  exact Iff.symm (Set.mem_image_iff_of_inverse (congrFun rfl) (congrFun rfl))



lemma Nucleus_Coframe_minimal_Axioms : ∀ (a : Nucleus E) (s : Set (Nucleus E)), ⨅ b ∈ s, a ⊔ b ≤ a ⊔ sInf s := by
  intro a s

  by_cases hC : s.Nonempty
  simp [sInf, iInf, Nucleus.le_iff, sInf_fun]
  simp_rw [Nucleus.max_eq, sSup, sInf]
  intro v
  simp only [sSup, sInf, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    Nucleus.fun_of, sInf_fun, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro b h
  rw [Nucleus_mem_sublocale] at h
  simp at h
  rcases h with ⟨c, ⟨⟨h1, h3⟩, h2⟩⟩
  simp [Sublocale.nucleus] at h2
  --
  rw [h2] at h3
  rw [Sublocale.le_iff] at h3
  simp[sInf_fun] at h3
  simp_rw [sInf_le_iff] at h3
  simp [lowerBounds] at h3
  --
  apply sInf_le_of_le


  rw [sInf_le_iff]
  simp [lowerBounds, sInf_fun]
  intro d  h4

  rw [Set.Nonempty] at hC
  rcases hC with ⟨e, hC⟩
  let h5 := h4 e hC
  apply h5
  rw [Nucleus_mem_sublocale]
  simp [Sublocale.nucleus]
  apply And.intro
  . exact le_of_eq_of_le (id (Eq.symm h2)) h1
  . rw [Sublocale.le_iff]
    intro u
    simp only [Nucleus.toFun_eq_coe]
    apply h3
    simp











instance Nucleus.instCoframe : Order.Coframe (Nucleus E) :=
  Order.Coframe.ofMinimalAxioms ⟨Nucleus_Coframe_minimal_Axioms⟩

--instance Nucleus.instFrame : Order.Frame (Nucleus E) :=
--  Order.Frame.ofMinimalAxioms ⟨Nucleus_Frame_minimal_Axioms⟩
