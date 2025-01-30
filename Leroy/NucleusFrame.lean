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











structure Prenucleus (E : Type*) [CompleteLattice E] extends InfHom E E where
  le_apply' (x : E) : x ≤ toFun x

instance : FunLike (Prenucleus E) E E where
  coe x := x.toFun
  coe_injective' f g h := by  obtain ⟨⟨_, _⟩, _⟩ := f; congr!


lemma toFun_eq_coe (n : Prenucleus E) : n.toFun = n := rfl
@[simp] lemma coe_toInfHom (n : Prenucleus E) : ⇑n.toInfHom = n := rfl

variable (n : Prenucleus E) (x : E)

lemma le_apply : x ≤ n x := by
  rw [← toFun_eq_coe]
  exact n.le_apply' x

lemma map_inf : n (x ⊓ y) = n x ⊓ n y := by
  rw [← toFun_eq_coe]
  exact n.map_inf' x y

def Prenucleus.comp (n m : Prenucleus E) : Prenucleus E where
  toFun := n ∘ m
  map_inf' := (by sorry)
  le_apply' := (by simp; intro x; apply le_trans (m.le_apply' x);exact le_apply n (m.toFun x))


lemma mal_wieder : ∀ (a : Nucleus E) (s : Set (Nucleus E)), a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b := by
  sorry


def minax : Order.Frame.MinimalAxioms (Nucleus E) where
  inf_sSup_le_iSup_inf := mal_wieder


-- Temporary until the frame problem gets better
instance (priority := high): BoundedOrder (Sublocale E) := by exact OrderDual.instBoundedOrder (Nucleus E)

instance (priority := high) : OrderTop (Sublocale E) := by exact OrderDual.instOrderTop (Nucleus E)
---
instance (priority := 0) Nucleus.instFrame : Order.Frame (Nucleus E) :=
  Order.Frame.ofMinimalAxioms minax

example : ∀ (u : Sublocale E), ⊤ ≤ u ↔ u = ⊤ := fun u => top_le_iff
