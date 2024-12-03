import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Open_Subframes

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [Order.Frame E]


def increasingly_filtered (s : Set (Nucleus X)) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w

def increasingly_filtered' (s : Set (Opens X)) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w


structure Measure where
  toFun : (Opens X) → NNReal
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Opens X), U ≤ V → toFun U ≤ toFun V
  pseudosymm : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set (Opens X)), increasingly_filtered' s → toFun (sSup s) = iSup (fun (x : s) ↦ toFun x)

def Neighbourhood (u : Nucleus X) : Set (Opens X) := {v : Opens X | u ≤ v}

-- subframes???
noncomputable def Measure.caratheodory {m : @Measure X h} (a : Nucleus X) : NNReal :=
  sInf (m.toFun '' Neighbourhood a)

def increasing (s :  ℕ → Nucleus X) : Prop :=
  ∀ (n : ℕ), s n ≤ s (n + 1)

variable (m : @Measure X h)(X_n : ℕ → Nucleus X)
#check m.caratheodory
#check X_n

lemma Caratheodory_opens (m : @Measure X h) : ∀ x : Opens X, m.caratheodory x = m.toFun x := by
  simp [Measure.caratheodory]
  intro x
  simp [Neighbourhood]
  apply le_antisymm
  sorry
  sorry

lemma Neighbourhood_nonempty (x : Nucleus X) : Nonempty (Neighbourhood x) := by sorry

lemma preserves_sup (m : @Measure X h) (X_n : ℕ → Nucleus X) (h : increasing X_n) : m.caratheodory (iSup X_n) = iSup (m.caratheodory ∘ X_n) := by
  simp [Measure.caratheodory]
  have h_epsilon : ∃ r : NNReal, r > 0 := by
    use 1
    exact Real.zero_lt_one
  let ε := Classical.choose h_epsilon
  have h_epsilon' : ε > 0 := by
    simp [ε]
    apply Classical.choose_spec
  have h_epsilon_n :  ∃ (e_n : ℕ → NNReal),∀ n : ℕ, ∑ i ∈ Finset.range n, e_n i <  ε := by
    let d (n : ℕ) := (0.5 * ε) / (2 ^ n)
    use d
    intro n
    simp [d]
    sorry
  let e_n := Classical.choose h_epsilon_n
  let N := Neighbourhood ∘ X_n
  have h_0 : ∀ n : ℕ,  m.caratheodory (X_n n) + ε >  sInf (m.toFun '' Neighbourhood (X_n n)) := by
    intro n
    simp [Measure.caratheodory]
    exact h_epsilon'

  have h_1 : ∀ n : ℕ, ∃ neighbour : Neighbourhood (X_n n), m.caratheodory (X_n n) + ε > m.caratheodory neighbour := by
    by_cases hC : ∀ n : ℕ, ∃ neighbour : Neighbourhood (X_n n), m.caratheodory (X_n n) + ε > m.caratheodory neighbour
    . exact fun n => hC n
    . simp [Caratheodory_opens] at hC
      simp [Measure.caratheodory] at hC
      rcases hC with ⟨n, hC⟩
      sorry

  let V_n (n : ℕ) := Classical.choose (h_1 n)
  sorry
