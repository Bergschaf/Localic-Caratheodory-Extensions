import Leroy.Nucleus
import Mathlib.Topology.Bases
import Mathlib.Order.CompleteSublattice
open CategoryTheory

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]



instance le : LE (Nucleus X) where
  le x y := ∀ v : X, y.toFun v ≤ x.toFun v

@[simp]
lemma Nucleus.le_iff {n m : Nucleus X} : n ≤ m ↔ ∀ v : X, m.toFun v ≤ n.toFun v := by rfl

def Nucleus_to_subtype (s : Nucleus X) : Type u := (s : Set X)

-- Leroy CH 3


def e_V (X_i : Set (Nucleus E)) (V : E) := sSup {w : E | ∀ x_i ∈ X_i, w ≤ x_i.toFun V}


def e_V_increasing : (x : E) → x ≤ (e_V X_i) x := by
  intro x
  simp [e_V]
  apply le_sSup
  simp only [Set.mem_setOf_eq]
  exact fun x_i a => x_i.increasing x


lemma e_V_idempotent :  ∀ (x : E), (e_V X_i) (e_V X_i x) = e_V X_i x := by
  intro x
  simp [e_V]
  apply le_antisymm_iff.mpr
  apply And.intro
  . apply sSup_le_sSup
    simp only [Set.setOf_subset_setOf]
    intro x1 h1 h2 h3
    let h4 := h1 h2 h3
    have h5 : h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) ≤ h2.toFun x := by
      have h7 : (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) ≤ h2.toFun x := by
        simp
        intro b h6
        exact h6 h2 h3
      apply_fun h2.toFun at h7
      rw [h2.idempotent] at h7
      exact h7
      exact h2.monotone
    exact
      Preorder.le_trans x1 (h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x})) (h2.toFun x)
        (h1 h2 h3) h5
  . apply sSup_le_sSup
    simp
    intro a h1 h2 h3
    let h4 := h1 h2 h3
    have h5 : h2.toFun x ≤ h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) := by
      have h6 : x ≤ (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}) := by
        apply le_sSup
        simp only [Set.mem_setOf_eq]
        intro x1 x2
        exact (x1.increasing x)
      apply_fun h2.toFun at h6
      exact h6
      exact h2.monotone
    exact
      Preorder.le_trans a (h2.toFun x) (h2.toFun (sSup {w | ∀ x_i ∈ X_i, w ≤ x_i.toFun x}))
        (h1 h2 h3) h5


lemma e_V_preserves_inf : ∀ (x y : E), (e_V X_i) (x ⊓ y) = (e_V X_i) x ⊓ e_V X_i y := by
  intro x y
  have h (W : E) : W ≤ e_V X_i (x ⊓ y)  ↔ W ≤  e_V X_i x ⊓ e_V X_i y := by
    have h1 : W ≤ e_V X_i (x ⊓ y) ↔ ∀ x_i ∈ X_i, W ≤ x_i.toFun (x ⊓ y) := by
      apply Iff.intro
      . intro h x_i h1
        have h2 : e_V X_i (x ⊓ y) ≤ x_i.toFun (x ⊓ y) := by
          simp [e_V]
          intro b h2
          exact h2 x_i h1
        exact Preorder.le_trans W (e_V X_i (x ⊓ y)) (x_i.toFun (x ⊓ y)) h h2
      . intro h
        simp [e_V]
        apply le_sSup
        simp only [Set.mem_setOf_eq]
        exact fun x_i a => h x_i a


    have h2 : (∀ x_i ∈ X_i, W ≤ x_i.toFun (x ⊓ y)) ↔ ∀ x_i ∈ X_i, W ≤ x_i.toFun x ⊓ x_i.toFun y := by
      apply Iff.intro
      . intro h x_i h1
        rw [← x_i.preserves_inf]
        exact h x_i h1
      . intro h x_i h1
        rw [x_i.preserves_inf]
        exact h x_i h1


    have h3 : (∀ x_i ∈ X_i, W ≤ x_i.toFun x ⊓ x_i.toFun y) ↔  W ≤  e_V X_i x ⊓ e_V X_i y := by
      apply Iff.intro
      . intro h
        simp [e_V]
        simp at h
        apply And.intro
        . apply le_sSup
          simp
          intro x_i h1
          let h := h x_i h1
          apply h.left
        . apply le_sSup
          simp
          intro x_i h1
          let h := h x_i h1
          apply h.right
      . intro h x_i h1
        simp only [le_inf_iff]
        simp [e_V] at h
        rcases h with ⟨h2, h3⟩
        simp only [le_sSup_iff, upperBounds, Set.mem_setOf_eq] at h2 h3
        let h2 := h2 (x_i.toFun x)
        let h3 := h3 ((x_i.toFun y))
        apply And.intro
        . apply h2
          intro a h3
          exact h3 x_i h1
        . apply h3
          intro a h3
          exact h3 x_i h1

    apply Iff.trans h1
    apply Iff.trans h2 h3

  apply le_antisymm_iff.mpr

  apply And.intro
  . have h1 := h (e_V X_i (x ⊓ y))
    rcases h1 with ⟨h1, h2⟩
    apply (h1 (by rfl))
  . have h1 := h (e_V X_i x ⊓ e_V X_i y )
    rcases h1 with ⟨h1, h2⟩
    apply (h2 (by rfl))



def e_V_nucleus (X_i : Set (Nucleus E)) : Nucleus E where
  toFun := e_V X_i
  idempotent := e_V_idempotent
  increasing := e_V_increasing
  preserves_inf := e_V_preserves_inf


instance : SupSet (Nucleus X) where
  sSup X_i := e_V_nucleus X_i

instance : InfSet (Nucleus X) where
  sInf := fun X_i ↦ sSup {w : Nucleus X | ∀ x_i ∈ X_i, w ≤ x_i}

-- TODO stimmt das??
instance Nucleus_bot : Bot (Nucleus X) where
  bot := ⟨fun x ↦ ⊤, (by simp), (by simp), (by simp)⟩

instance Nucleus_top : Top (Nucleus X) where
  top := ⟨fun x ↦ x, (by simp only [implies_true]), (by simp only [le_refl, implies_true]), (by simp only [implies_true])⟩

lemma all_le_top : ∀ (x : Nucleus X), x ≤ ⊤ := by
  intro x
  simp [Nucleus_top]
  intro v
  exact Nucleus.increasing' x

instance Nucleus_min : Min (Nucleus X) where
  min x y := sInf {x, y}

instance Nucleus_max : Max (Nucleus X) where
  max x y := sSup {x, y}


instance : PartialOrder (Nucleus X) where
  le_refl := (by simp [le])
  le_trans := (by simp [le]; exact fun a b c a_1 a_2 v =>
    Preorder.le_trans (c v) (b v) (a v) (a_2 v) (a_1 v))
  le_antisymm := (by intro a b h i; simp only [le, Nucleus.toFun_eq_coe] at *; ext x; simp only [Nucleus.toFun_eq_coe]; apply le_antisymm; exact i x; exact h x )

lemma Nucleus_le_sSup (s : Set (Nucleus E)) (a : Nucleus E) : a ∈ s → a ≤ sSup s := by
  simp [sSup, e_V_nucleus]
  intro h v
  simp [e_V]
  intro b h1
  exact h1 a h

lemma Nucleus_sSup_le  (s : Set (Nucleus E)) (a : Nucleus E) : (∀ b ∈ s, b ≤ a) → sSup s ≤ a := by
  intro h
  simp [sSup, e_V_nucleus, e_V]
  intro v
  apply le_sSup
  simp
  intro xi hxi
  let h1 := h xi hxi
  simp at h1
  exact h xi hxi v

instance : CompleteSemilatticeSup (Nucleus E) where
  le_sSup := Nucleus_le_sSup
  sSup_le := Nucleus_sSup_le

lemma Nucleus_le_inf :  ∀ (a b c : Nucleus E), a ≤ b → a ≤ c → a ≤ (fun a b => a ⊓ b) b c := by
  simp
  intro a b c h1 h2
  simp only [min, sInf, sSup, e_V_nucleus, Set.mem_insert_iff, Set.mem_singleton_iff,
    Nucleus.le_iff, Nucleus.toFun_eq_coe, forall_eq_or_imp, forall_eq, Nucleus.toFun_eq_coe', e_V,
    Set.mem_setOf_eq, and_imp, sSup_le_iff]
  intro v b1 h
  let h3 := h a h1 h2
  exact h a h1 h2

lemma sublocal_union_pointwise (X_i : Set (Nucleus E)) : ∀ (v : E), sSup {x v | x ∈ X_i} ≤ (sInf X_i) v := by
  intro v
  apply sSup_le
  intro b h
  simp at h
  simp only [sInf, sSup, e_V_nucleus, Nucleus.le_iff, Nucleus.toFun_eq_coe, Nucleus.toFun_eq_coe',
    e_V, Set.mem_setOf_eq]
  apply le_sSup
  simp only [Set.mem_setOf_eq]
  intro xi h1
  rcases h with ⟨a,⟨h2, h3⟩⟩
  let h1 := h1 a h2 v
  rw [h3] at h1
  exact h1

-- todo später allgemein vlt
lemma union_pointwise_le {U V : Nucleus E} :∀ x, (U ⊔ V) x ≤ U x ⊓ V x := by
  intro x
  simp [max, sSup, e_V_nucleus, e_V]
  intro b h1 h2
  exact h1

-- TODO in die mathlib rein
variable {X : Type*}
instance CompleteSemilatticeSup_to_SemilatticeSup [CompleteSemilatticeSup X] : SemilatticeSup X where
  sup x y := sSup {x, y}
  le_sup_left := (by simp; intro a b; apply le_sSup;simp only [Set.mem_insert_iff,Set.mem_singleton_iff, true_or])
  le_sup_right := (by simp; intro a b; apply le_sSup; simp only [Set.mem_insert_iff,   Set.mem_singleton_iff, or_true])
  sup_le := (by intro a b c h1 h2; simp; exact ⟨h1, h2⟩)

instance : Lattice (Nucleus E) where
  inf a b := a ⊓ b
  inf_le_left := (by intro a b; simp [Nucleus_min, sInf]; exact fun b_1 a a_1 v => a v)
  inf_le_right := (by intro a b; simp [Nucleus_min, sInf])
  le_inf := Nucleus_le_inf

lemma Nucleus_le_sInf :  ∀ (s : Set (Nucleus E)) (a : Nucleus E), (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
  simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe, sInf]
  intro s a h v
  simp only [sSup, e_V_nucleus, Nucleus.toFun_eq_coe', e_V, Set.mem_setOf_eq, Nucleus.toFun_eq_coe,
    sSup_le_iff]
  intro b h1
  let h2 := h1 a h
  exact h2


instance : CompleteLattice (Nucleus E) where
  le_sSup := (by exact fun s a a_1 => Nucleus_le_sSup s a a_1)
  sSup_le := (by exact fun s a a_1 => Nucleus_sSup_le s a a_1)
  sInf_le := (by simp[sInf]; exact fun s a a_1 b a_2 v => a_2 a a_1 v)
  le_sInf := Nucleus_le_sInf
  le_top := all_le_top
  bot_le := (by simp only [Nucleus_bot, Nucleus.le_iff, Nucleus.toFun_eq_coe, le_top, implies_true])


lemma Nucleus.top_eq : (⊤ : Nucleus E) = ⟨fun x ↦ x, (by simp only [implies_true]), (by simp only [le_refl, implies_true]), (by simp only [implies_true])⟩:= by
  rfl

--lemma Nucleus.bot_eq : (⊥)

lemma Nucleus_Frame_minimal_axioms : ∀ (a : Nucleus E) (s : Set (Nucleus E)), a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b := by
  intro a s
  apply le_iSup_iff.mpr
  intro b h
  simp at h
  simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe]
  intro v
  simp_rw [Nucleus_min, sInf, sSup, e_V_nucleus] at *
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Nucleus.le_iff, Nucleus.toFun_eq_coe,
    forall_eq_or_imp, forall_eq, Nucleus.toFun_eq_coe', e_V, Set.mem_setOf_eq, and_imp,
    sSup_le_iff] at *
  have h1 : ∀ (v : E), b v ≤ sInf { sSup {w | ∀ (x_i : Nucleus E), (∀ (v : E), a v ≤ x_i v) → (∀ (v : E), i v ≤ x_i v) → w ≤ x_i v} | i ∈ s} := by
    intro v
    apply le_sInf
    intro b1 h1
    simp at h1
    rcases h1 with ⟨i, hi, h1⟩
    let h:= h i hi v
    rw [← h1]
    apply h

  have h2 :  sInf {x | ∃ i ∈ s, sSup {w | ∀ (x_i : Nucleus E), (∀ (v : E), a v ≤ x_i v) → (∀ (v : E), i v ≤ x_i v) → w ≤ x_i v} = x} ≤ sSup
    {w | ∀ (x_i : Nucleus E), (∀ (v : E), a v ≤ x_i v) → (∀ (v b : E), (∀ x_i ∈ s, b ≤ x_i v) → b ≤ x_i v) → w ≤ x_i v} := by
      apply le_sSup_iff.mpr
      simp_rw [upperBounds]
      intro b hb
      simp only [Set.mem_setOf_eq] at hb
      apply sInf_le_iff.mpr
      intro b1 hb1
      simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂] at hb1
      apply hb
      intro xi h1 h2
      apply h2
      intro x1 hx1
      let h3 := hb1 x1 hx1
      have h4 : sSup {w | ∀ (x_i : Nucleus E), (∀ (v : E), a v ≤ x_i v) → (∀ (v : E), x1 v ≤ x_i v) → w ≤ x_i v} ≤ x1 v := by
        sorry
      sorry

  exact
    Preorder.le_trans (b v)
      (sInf
        {x |
          ∃ i ∈ s,
            sSup
                {w |
                  ∀ (x_i : Nucleus E),
                    (∀ (v : E), a v ≤ x_i v) → (∀ (v : E), i v ≤ x_i v) → w ≤ x_i v} =
              x})
      (sSup
        {w |
          ∀ (x_i : Nucleus E),
            (∀ (v : E), a v ≤ x_i v) →
              (∀ (v b : E), (∀ x_i ∈ s, b ≤ x_i v) → b ≤ x_i v) → w ≤ x_i v})
      (h1 v) h2




instance : Order.Frame (Nucleus E) := Order.Frame.ofMinimalAxioms ⟨Nucleus_Frame_minimal_axioms⟩
