import Mathlib.Data.Real.Basic
import Leroy.Basic
import Leroy.Open_Sublocales
import Leroy.Further_Topology

variable {X Y E: Type*} [h : Order.Frame X] [Order.Frame Y] [Order.Frame E]

abbrev ι := ℕ  -- TODO darf man das?

variable {Z : Type*} [PartialOrder Z]
def increasing (s : ι → Z) : Prop :=
  ∀ i : ι, s i ≤ s (i + 1)

def filtered (s : ι → Z) : Prop :=
  ∀ i j, ∃ k, s i ≤ s k ∧ s j ≤ s k

def increasingly_filtered (s : ι → Z) : Prop :=
  increasing s ∧ filtered s

structure Measure where
  toFun : (Open X) → NNReal -- Evtl ENNReal (brauchen wir ⊤)
  empty : toFun ⊥ = 0
  mono : ∀ (U V : Open X), U ≤ V → toFun U ≤ toFun V
  pseudosymm : toFun (U ⊔ V) = toFun U + toFun V - toFun (U ⊓ V)
  filtered : ∀ (s : ι → Open X), increasingly_filtered s → toFun (iSup s) = iSup (toFun ∘ s)

def Open_Neighbourhood (u : Sublocale X) : Set (Open X) := {v : Open X | u ≤ v}

def Neighbourhood (u : Sublocale X) : Set (Sublocale X) := {v | ∃ w ∈ Open_Neighbourhood u, w ≤ v}


noncomputable def Measure.caratheodory {m : @Measure X h} (a : Sublocale X) : NNReal :=
  sInf (m.toFun '' Open_Neighbourhood a)



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
  . rw [le_csInf_iff]
    simp
    intro a h
    exact m.mono x a h
    exact OrderBot.bddBelow (m.toFun '' {v | x ≤ v})
    simp [Set.Nonempty]
    use m.toFun x
    use x


lemma Caratheodory_monotonic (m : Measure) {A B : Sublocale E} : A ≤ B → m.caratheodory A ≤ m.caratheodory B := by
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

    simp only [Open.top_sublocale, Nucleus.top, Nucleus.toFun_eq_coe, and_true]
    exact fun v => Nucleus.increasing' B
  . simp only [Open_Neighbourhood, Nucleus.le_iff, Nucleus.toFun_eq_coe, Set.image_subset_iff]
    rw [@Set.setOf_subset]
    intro x h1
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_setOf_eq]
    use x
    rw [Sublocale.le_iff] at h
    apply And.intro
    . exact fun v => Preorder.le_trans (x.sublocale v) (B v) (A v) (h1 v) (h v)
    . rfl

lemma le_Neighbourhood {a : Sublocale E} : ∀ x ∈ Neighbourhood a, a ≤ x := by
  intro x h
  simp only [Neighbourhood, Open_Neighbourhood, Set.mem_setOf_eq] at h
  rcases h with ⟨w, ⟨h1,h2⟩⟩
  exact Preorder.le_trans a w.sublocale x h1 h2


lemma Open_Neighbourhood_nonempty (x : Sublocale X) : Nonempty (Open_Neighbourhood x) := by
  simp [Set.Nonempty]
  use ⊤
  rw [Open_Neighbourhood]
  simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe, Set.mem_setOf_eq, Open.top_sublocale]
  exact fun v => Nucleus.increasing' x

lemma Open_Neighbourhood.top_mem {x : Nucleus X}: ⊤ ∈ Open_Neighbourhood x := by
  rw [Open_Neighbourhood]
  simp only [Set.mem_setOf_eq, Open.top_sublocale, le_top]


lemma preserves_sup (m : @Measure X h) (X_n : ℕ → Sublocale X) (h : increasing X_n) : m.caratheodory (iSup X_n) = iSup (m.caratheodory ∘ X_n) := by
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
    --apply @Set.nonempty_of_nonempty_subtype _ _
    --
    sorry -- sieht schlecht auss
    sorry

  sorry


def well_inside (U V : Open E) := U.sublocale.closure.sublocale ≤ V

infix:100 " ≪ " => well_inside

/--
Stone spaces s.80
und auch Sketches of an Elephant 501...
-/
def well_inside_iff (U V : Open E) : U ≪ V ↔ ∃ c, c ⊓ U = ⊥ ∧ c ⊔ V = ⊤ := by
  rw [well_inside]

  sorry

/--
Leroy definition
TODO Stone spaces als quelle anschauen
Steht auch in Sketches of an Elephant 501
da steht covered -> Muss da U ≤ sSup ... stehen?
-/
def regular (E : Type*)  [Order.Frame E]: Prop :=
  ∀ (U : Open E), U = sSup {V : Open E | V.sublocale.closure.sublocale ≤ U}


variable {E : Type*} [e_frm : Order.Frame E] [Fact (regular E)]

variable {m : @Measure E e_frm}(X_n : ℕ → Sublocale E)

/--
Leroy Lemme 2.2
TODO stone spaces als quelle vlt
Seite 81. 1.2
Maybe depends on:
Nucleus.eq_join_open_closed
-/
def E_to_Open (x : E) : Open E := ⟨x⟩

/--
TODO dass muss weiter nach vorne
-/
lemma E_le_iff (x y : E) : x ≤ y ↔ E_to_Open x ≤ E_to_Open y := by
  repeat rw [E_to_Open]
  apply Iff.intro
  . intro h
    exact Open.le_iff.mpr h
  . intro h
    exact eckig_preserves_inclusion.mpr h

@[simp]
lemma E_to_Open_Open (x : Open E) : E_to_Open ↑x = x := by rfl


lemma sublocal_intersection_of_neighbours {a : Sublocale E} : a = sInf (Neighbourhood a) := by
  apply le_antisymm
  . apply le_sInf
    exact fun b a_1 => le_Neighbourhood b a_1


  rw [Sublocale.le_iff]
  intro H
  simp
  let K := a H
  have h (W : Open E) (h : W.sublocale.closure.sublocale ≤ (⟨K⟩ : Open E)) :
    W.sublocale.closure.sublocale ≤ E_to_Open (a H) := by
    let V := W.sublocale.closure.complement ⊔ ⟨H⟩
    have h_V : V ∈ Open_Neighbourhood a := by sorry

    have h : W ⊓ V = W ⊓ (⟨H⟩ : Open E) := by sorry
    have h1 : W ⊓ ⟨H⟩ ≤ ⟨H⟩ := by sorry
    sorry

  have h1 : E_to_Open (a H) = sSup {W : Open E | W.sublocale.closure.sublocale ≤ (⟨K⟩ : Open E)} := by
    sorry

  rw [E_le_iff]
  rw [h1]














lemma Measure.add_complement {m : @Measure E e_frm} {U : Open E} : m.caratheodory U + m.caratheodory (complement U) = m.caratheodory (⊤ : Open E) := by
  rw [Caratheodory_opens]
  rw [Caratheodory_opens]

  apply le_antisymm
  . let V_a := Neighbourhood (complement U)
    let W_a := (Sublocale.exterior '' V_a)
    have h : increasingly_filtered' W_a := by
      simp [increasingly_filtered']
      intro a h1 b h2

      sorry
    have h1 : sSup W_a = U := by
      sorry
    have h2 : m.toFun U = ⨆ x : W_a, m.toFun x := by
      rw [← h1]
      let h3 := m.filtered W_a h
      rw [h3]

    have h3 : ∀ w_a ∈ W_a, ∀ v_a ∈ V_a, m.caratheodory w_a + m.caratheodory v_a = m.caratheodory ⊤ := by
      sorry
    sorry

  . simp only [caratheodory, Open_Neighbourhood, complement, Sublocale.le_iff, Nucleus.toFun_eq_coe]
    sorry
