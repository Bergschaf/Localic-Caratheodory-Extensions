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








--instance Nucleus.instCoframe : Order.Coframe (Nucleus E) :=
--  Order.Coframe.ofMinimalAxioms ⟨Nucleus_Coframe_minimal_Axioms⟩

instance Nucleus.instFrame : Order.Frame (Nucleus E) :=
  Order.Frame.ofMinimalAxioms ⟨sorry⟩
