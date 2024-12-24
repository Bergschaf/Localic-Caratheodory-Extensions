import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Open_Subframes
import Leroy.Further_Topology

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [Order.Frame E]


def increasingly_filtered (s : Set (Nucleus X)) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w

def increasingly_filtered' (s : Set (Open X)) : Prop :=
  ∀ (u v : s), ∃ (w : s), u ≤ w ∧ v ≤ w


structure Measure where
  toFun : (Open X) → NNReal -- Evtl ENNReal (brauchen wir ⊤)
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Open X), U ≤ V → toFun U ≤ toFun V
  pseudosymm : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : Set (Open X)), increasingly_filtered' s → toFun (sSup s) = iSup (fun (x : s) ↦ toFun x)

def Open_Neighbourhood (u : Nucleus X) : Set (Open X) := {v : Open X | u ≤ v}

def Neighbourhood (u : Nucleus X) : Set (Nucleus X) := {v | ∃ w ∈ Open_Neighbourhood u, w ≤ v}


noncomputable def Measure.caratheodory {m : @Measure X h} (a : Nucleus X) : NNReal :=
  sInf (m.toFun '' Open_Neighbourhood a)

def increasing (s :  ℕ → Nucleus X) : Prop :=
  ∀ (n : ℕ), s n ≤ s (n + 1)


lemma Measure.all_le_top {m : @Measure X h} : ∀ a : Open X, m.toFun a ≤ m.toFun ⊤ := by
  intro a
  apply m.mono
  exact OrderTop.le_top a


lemma Caratheodory_opens {m : @Measure X h} : ∀ x : Open X, m.caratheodory x = m.toFun x := by
  simp [Measure.caratheodory]
  intro x
  simp [Open_Neighbourhood]
  apply le_antisymm
  . apply csInf_le'
    simp only [Set.mem_image, Set.mem_setOf_eq]
    use x
    simp only [le_refl, implies_true, and_self]
  . rw [le_csInf_iff]
    simp
    intro a h
    exact m.mono x a h
    exact OrderBot.bddBelow (m.toFun '' {v | x ≤ v})
    simp [Set.Nonempty]
    use m.toFun x
    use x
    simp only [le_refl, implies_true, and_self]


lemma Open_Neighbourhood_nonempty (x : Nucleus X) : Nonempty (Open_Neighbourhood x) := by
  simp [Set.Nonempty]
  use ⊤
  rw [Open_Neighbourhood]
  simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe, Set.mem_setOf_eq, Open.top_nucleus]
  exact fun v => Nucleus.increasing' x

lemma Open_Neighbourhood.top_mem {x : Nucleus X}: ⊤ ∈ Open_Neighbourhood x := by
  rw [Open_Neighbourhood]
  simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe, Set.mem_setOf_eq, Open.top_nucleus]
  exact all_le_top x



lemma preserves_sup (m : @Measure X h) (X_n : ℕ → Nucleus X) (h : increasing X_n) : m.caratheodory (iSup X_n) = iSup (m.caratheodory ∘ X_n) := by
  simp [Measure.caratheodory]
  have h_epsilon : ∃ r : NNReal, r > 0 := by
    use 1
    exact Real.zero_lt_one
  let ε := Classical.choose h_epsilon
  have h_epsilon' : ε > 0 := by
    simp [ε]
    apply Classical.choose_spec
  have h_epsilon_n :  ∃ (e_n : ℕ → NNReal),∀ n : ℕ,( ∑ i ∈ Finset.range n, e_n i < ε) ∧ 0 < e_n n := by
    let d (n : ℕ) := (0.5 * ε) / (2 ^ n)
    use d
    intro n
    simp [d]
    sorry
  let e_n := Classical.choose h_epsilon_n
  have h_e_n : ∀ n : ℕ, 0 < e_n n := by
    intro n
    simp [e_n]
    let x := Classical.choose_spec h_epsilon_n n
    exact x.right

  let N := Open_Neighbourhood ∘ X_n
  have h_0 : ∀ n : ℕ,  m.caratheodory (X_n n) + ε >  sInf (m.toFun '' Open_Neighbourhood (X_n n)) := by
    intro n
    simp [Measure.caratheodory]
    exact h_epsilon'

  have h_1 : ∀ n : ℕ, ∃ neighbour ∈ Open_Neighbourhood (X_n n), m.toFun neighbour - m.caratheodory (X_n n) < e_n n :=  by
    intro n
    simp [Measure.caratheodory]
    -- TODO noa fragen
    --- ggf sInf kommutiert mit measure
    sorry


  let V_n (n : ℕ) := Classical.choose (h_1 n)

  let W_n (n : ℕ) := iSup (fun (x : Fin n) ↦ V_n x)

  let W := iSup (W_n)

  have h_2 : W = iSup (V_n) := by
    simp [W, W_n]
    sorry

  have h_3 : ∀ n : ℕ, m.toFun (W_n n) - m.caratheodory (X_n n) ≤ ∑ i ∈ Finset.range (n), e_n i := by sorry

  have h_4 : m.toFun (W) ≤ ε + iSup (fun n ↦ (m.caratheodory (X_n n))) := by sorry


  have h_trivial : ∀ n : ℕ, iSup (m.caratheodory ∘ X_n) ≤ m.caratheodory (iSup X_n) := by
    intro n

    apply ciSup_le
    intro x
    simp [Measure.caratheodory]
    apply csInf_le_csInf'
    simp
    let x := Open_Neighbourhood_nonempty (iSup  X_n)
    apply @Set.nonempty_of_nonempty_subtype _ _
    --
    refine Set.image_mono ?H.h.h
    simp [Open_Neighbourhood]
    intro a h v
    sorry -- sieht schlecht auss

  sorry



/--
Leroy definition
TODO Stone spaces als quelle anschauen
da steht covered -> Muss da U ≤ sSup ... stehen?
-/
def regular (E : Type*)  [Order.Frame E]: Prop :=
  ∀ (U : Open E), U = sSup {V : Open E | V.nucleus.closure.nucleus ≤ U}


variable {E : Type*} [e_frm : Order.Frame E] [Fact (regular E)]

variable {m : @Measure E e_frm}(X_n : ℕ → Nucleus E)

/--
Leroy Lemme 2.2
TODO stone spaces als quelle vlt
Seite 81. 1.2
-/
lemma sublocal_intersection_of_neighbours {A : Nucleus E} : A = sInf (Neighbourhood A) := by

  apply le_antisymm
  . apply le_sInf_iff.mpr
    simp [Neighbourhood]
    intro b e h1 h2 v
    let h3 := h2 v
    apply le_trans h3
    simp [Open_Neighbourhood] at h1
    exact h1 v

  . apply sInf_le_iff.mpr
    intro b h
    simp only [lowerBounds, Nucleus.toFun_eq_coe, Set.mem_setOf_eq] at h

    -- we have to construct an element of Neighbourhood x which is ≤ x
    sorry




lemma Measure.add_complement {m : @Measure E e_frm} {U : Open E} : m.caratheodory U + m.caratheodory (complement U) = m.caratheodory (⊤ : Open E) := by
  rw [Caratheodory_opens]
  rw [Caratheodory_opens]

  apply le_antisymm
  . let V_a := Neighbourhood (complement U)
    let W_a := (Nucleus.exterior '' V_a)
    have h : increasingly_filtered' W_a := by
      simp [increasingly_filtered']
      intro a h1 b h2
      sorry
    have h1 : sSup W_a = U := by sorry
    have h2 : m.toFun U = ⨆ x : W_a, m.toFun x := by
      rw [← h1]
      let h3 := m.filtered W_a h
      rw [h3]
    sorry


  . sorry --trival anscheinend

omit [Fact (regular E)] in

lemma Caratheodory_monotonic {A B : Nucleus E} : A ≤ B → m.caratheodory A ≤ m.caratheodory B := by
  intro h
  simp_rw [Measure.caratheodory]
  apply csInf_le_csInf
  . simp only [BddBelow, Set.Nonempty, lowerBounds, Set.mem_image, forall_exists_index, and_imp,
     forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
    use 0
    intro a ha
    simp only [zero_le]
  . simp [Set.Nonempty, Open_Neighbourhood]
    use m.toFun ⊤
    use ⊤
    simp only [Open.top_nucleus, Nucleus_top, Nucleus.toFun_eq_coe', and_true]
    exact fun v => Nucleus.increasing' B
  . simp only [Open_Neighbourhood, Nucleus.le_iff, Nucleus.toFun_eq_coe, Set.image_subset_iff]
    rw [@Set.setOf_subset]
    intro x h1
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
    use x
    simp at h
    apply And.intro
    . exact fun v => Preorder.le_trans (x.nucleus v) (B v) (A v) (h1 v) (h v)
    . rfl
