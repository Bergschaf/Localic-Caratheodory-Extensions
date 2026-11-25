module

public import Leroy.Sublocale
public import Mathlib.Order.CompleteSublattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic

/-!
# Further topology on frames: neighbourhoods, complements, interior, closure and exterior

This file develops point-set style constructions for sublocales of a frame: systems of
open neighbourhoods of a sublocale, the closed complement on opens (Leroy Lemme 8 and
8 bis), and the interior, closure, boundary (`rand`) and exterior operators.  It is part
of the port of Leroy's thesis on localic measure theory and supports the Caratheodory
extension development.
-/

@[expose] public section

variable {X Y E : Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]
open Sublocale

/-- The set of open elements of `X` containing the sublocale `u`, i.e. those opens `v`
with `u ≤ v`; these form the system of open neighbourhoods of `u`. -/
def Sublocale.Open_Neighbourhood (u : Sublocale X) : Set (Open X) := {v : Open X | u ≤ v}

/-- The set of sublocales containing some open element above `u`: the usual system of
neighbourhoods of the sublocale `u`. -/
def Sublocale.Neighbourhood (u : Sublocale X) : Set (Sublocale X) :=
  {v | ∃ w ∈ Open_Neighbourhood u, w ≤ v}

/-- Every sublocale in the neighbourhood system of `a` contains `a` itself. -/
lemma Sublocale.Neighourhood.le {a : Sublocale E} : ∀ x ∈ Neighbourhood a, a ≤ x := by
  intro x h
  simp only [Neighbourhood, Open_Neighbourhood, Set.mem_ofPred_eq] at h
  rcases h with ⟨w, ⟨h1, h2⟩⟩
  exact Preorder.le_trans a w.toSublocale x h1 h2

/-- The largest open element `⊤` of `X` contains every sublocale, hence is an open
neighbourhood of any `x`. -/
lemma Sublocale.Open_Neighbourhood.top_mem {x : Sublocale X} : ⊤ ∈ Open_Neighbourhood x := by
  simp [Open_Neighbourhood]

/-- The open neighbourhood system of any sublocale is nonempty: the open element `⊤`
always belongs to it. -/
@[simp]
lemma Sublocale.Open_Neighbourhood.Nonempty (x : Sublocale X) :
    (Open_Neighbourhood x).Nonempty := by
  use ⊤
  exact top_mem

/-- The open neighbourhood system of any sublocale is nonempty as an inhabited set,
witnessed by the open element `⊤`. -/
@[simp]
lemma Sublocale.Nonempty_Open_Neighbourhood (x : Sublocale X) :
    Nonempty (Open_Neighbourhood x) := by
  use ⊤
  exact Open_Neighbourhood.top_mem

-- TODO restliche Neighbourhood lemmas
/-- The top sublocale is a neighbourhood of every sublocale `x`, since it contains the
open neighbourhood `⊤`. -/
lemma Sublocale.Neighbourhood.top_mem (x : Sublocale X) : ⊤ ∈ Neighbourhood x := by
  simp only [Neighbourhood, Set.mem_ofPred_eq, le_top, and_true]
  use ⊤
  exact Open_Neighbourhood.top_mem

/-- The neighbourhood system of any sublocale is nonempty, witnessed by the top
sublocale. -/
lemma Sublocale.Nonempty_Neighbourhood (x : Sublocale X) : Nonempty (Neighbourhood x) := by
  use ⊤
  exact Neighbourhood.top_mem x

/-- The open neighbourhoods of a sublocale are closed under binary meet: if the opens
`U` and `V` both contain `x`, then so does the open `U ⊓ V`. -/
lemma Sublocale.Open_Neighbourhood.inf_closed {x : Sublocale E} :
    ∀ U ∈ Open_Neighbourhood x, ∀ V ∈ Open_Neighbourhood x, U ⊓ V ∈ Open_Neighbourhood x := by
  simp only [Open_Neighbourhood, Set.mem_ofPred_eq]
  intro U h1 V h2
  rw [Open.preserves_inf]
  exact le_inf h1 h2

/-- The neighbourhoods of a sublocale are closed under binary meet: if each of `U` and
`V` contains an open element above `x`, then `U ⊓ V` contains one as well. -/
lemma Sublocale.Neighbourhood.inf_closed (x : Sublocale E) :
    ∀ U ∈ Neighbourhood x, ∀ V ∈ Neighbourhood x, U ⊓ V ∈ Neighbourhood x := by
  simp only [Neighbourhood, Open_Neighbourhood, Set.mem_ofPred_eq, le_inf_iff,
    forall_exists_index, and_imp]
  intro a x1 h1 h2 n x2 h3 h4
  use x1 ⊓ x2
  simp_all only [Open.preserves_inf, le_inf_iff, and_self, true_and]
  apply And.intro
  · exact inf_le_of_left_le h2
  · exact inf_le_of_right_le h4

-- Properties of Complement

/--
Leroy Lemme 8
-/
lemma sup_eq_top_iff_compl_le (V : Open E) (x : Sublocale E) :
    V.toSublocale ⊔ x = ⊤ ↔ V.compl ≤ x := by
  constructor
  · intro h
    apply (Sublocale.le_iff _ _).mpr
    intro i
    have h_eval := congrArg (fun s : Sublocale E => s (i ⊔ V.element)) h
    rw [Sublocale.sup_apply, Sublocale.top_apply] at h_eval
    have h_fixed : x (i ⊔ V.element) = i ⊔ V.element := by
      rw [Open.toSublocale_apply, himp_eq_top_iff.mpr le_sup_right, top_inf_eq] at h_eval
      exact h_eval
    calc
      x i ≤ x (i ⊔ V.element) := x.toNucleus.monotone le_sup_left
      _ = i ⊔ V.element := h_fixed
      _ = V.element ⊔ i := sup_comm _ _
      _ = V.compl.toSublocale i := by
        simpa [Open.compl] using (Closed.toSublocale_apply V.compl i).symm
  · intro h
    apply le_antisymm le_top
    calc
      ⊤ = V.toSublocale ⊔ V.compl.toSublocale := (Open.sup_compl_eq_top V).symm
      _ ≤ V.toSublocale ⊔ x := sup_le_sup_left h _

/-- Another of Leroy's Lemme 8: the meet of an open sublocale `V` with a sublocale `x`
is the bottom element exactly when `x` is contained in the closed complement `V.compl`.
The forward direction builds an explicit nucleus interpolating between `V` and `x`, and
its associated sublocale is shown to be a common lower bound. -/
lemma inf_eq_bot_iff_le_compl (V : Open E) (x : Sublocale E) :
    V.toSublocale ⊓ x = ⊥ ↔ x ≤ V.compl := by
  constructor
  · intro h
    have h_inf : ∀ i, (⨅ j ∈ lowerBounds {V.toSublocale, x}, j i) = ⊤ := by
      intro i
      have h_eval := congrArg (fun s : Sublocale E => s i) h
      simpa only [Sublocale.inf_apply, Sublocale.bot_apply] using h_eval
    let help_nucleus : Nucleus E :=
      ⟨⟨fun a => V.element ⇨ x a, by
        intro a b
        change V.element ⇨ x.toNucleus (a ⊓ b) =
          (V.element ⇨ x.toNucleus a) ⊓ (V.element ⇨ x.toNucleus b)
        rw [x.toNucleus.map_inf, himp_inf_distrib]⟩,
        by
          intro a
          change V.element ⇨ x (V.element ⇨ x a) ≤ V.element ⇨ x a
          have h_x : x (V.element ⇨ x a) ≤ V.element ⇨ x a := by
            apply le_himp_iff.mpr
            calc
              x (V.element ⇨ x a) ⊓ V.element ≤
                  x (V.element ⇨ x a) ⊓ x V.element :=
                inf_le_inf_left _ x.toNucleus.le_apply
              _ = x ((V.element ⇨ x a) ⊓ V.element) := x.toNucleus.map_inf.symm
              _ ≤ x (x a) := x.toNucleus.monotone
                (show (V.element ⇨ x a) ⊓ V.element ≤ x a from himp_inf_le)
              _ = x a := x.toNucleus.idempotent a
          calc
            V.element ⇨ x (V.element ⇨ x a) ≤ V.element ⇨ (V.element ⇨ x a) :=
              himp_le_himp_left h_x
            _ = V.element ⇨ x a := by rw [himp_himp, inf_idem],
        by
          intro a
          apply le_himp_iff.mpr
          exact le_trans inf_le_left x.toNucleus.le_apply⟩
    have h_helpV : help_nucleus.toSublocale ≤ V.toSublocale := by
      change help_nucleus.toSublocale ≤ V.toNucleus.toSublocale
      rw [Nucleus.toSublocale_le_toSublocale]
      intro i
      have hi : i ≤ x i := Nucleus.le_apply (n := x.toNucleus) (x := i)
      apply le_himp_iff.mpr
      exact (himp_inf_le : (V.element ⇨ i) ⊓ V.element ≤ i).trans hi
    have h_helpx : help_nucleus.toSublocale ≤ x := by
      have h_help_nucleus : help_nucleus.toSublocale.toNucleus = help_nucleus := by
        apply Nucleus.ext
        intro i
        simp
      apply (Sublocale.toNucleus_le_toNucleus
        (S := x) (T := help_nucleus.toSublocale)).mp
      intro i
      rw [h_help_nucleus]
      exact le_himp_iff.mpr
        (inf_le_left : x.toNucleus i ⊓ V.element ≤ x.toNucleus i)
    have h_help : help_nucleus.toSublocale ∈ lowerBounds {V.toSublocale, x} := by
      intro a ha
      rcases ha with ha | ha
      · rw [ha]
        exact h_helpV
      · rw [ha]
        exact h_helpx
    apply (Sublocale.le_iff _ _).mpr
    intro i
    rw [Closed.toSublocale_apply]
    have h_top : ⊤ ≤ help_nucleus.toSublocale i := by
      rw [← h_inf i]
      exact iInf_le_of_le _ (iInf_le_of_le h_help le_rfl)
    have h_open : V.element ≤ x i := by
      apply himp_eq_top_iff.mp
      simpa [help_nucleus] using h_top
    exact sup_le h_open x.toNucleus.le_apply
  · intro h
    apply le_antisymm
    · exact le_trans (inf_le_inf_left _ h) (by rw [Open.inf_compl_eq_bot V])
    · exact bot_le


/--
Leroy Lemme 8 bis
-/
lemma sup_compl_eq_top_iff {x : Sublocale E} {u : Open E} : u ≤ x ↔ x ⊔ (u.compl) = ⊤ := by
  constructor
  · intro h
    apply le_antisymm le_top
    calc
      ⊤ = u.toSublocale ⊔ u.compl.toSublocale := (Open.sup_compl_eq_top u).symm
      _ ≤ x ⊔ u.compl.toSublocale := sup_le_sup_right h _
  · intro h
    apply (Sublocale.le_iff _ _).mpr
    intro i
    rw [Open.toSublocale_apply]
    have h_eval := congrArg (fun s : Sublocale E => s i) h
    rw [Sublocale.sup_apply, Sublocale.top_apply, Closed.toSublocale_apply] at h_eval
    apply le_himp_iff.mpr
    have h_inf : x i ⊓ u.element ≤ i := by
      calc
        x i ⊓ u.element ≤ x i ⊓ (u.element ⊔ i) :=
          inf_le_inf_left _ le_sup_left
        _ = i := h_eval
    simpa [inf_comm] using h_inf

/-
lemma inf_compl_eq_bot_iff {x : Sublocale E} {u : Open E} : x ≤ u ↔ x ⊓ (u.compl) = ⊥ := by
  apply Iff.intro
  · intro h
    apply le_antisymm
    ·
      apply_fun (fun x ↦ x ⊓ u.compl.toSublocale) at h
      dsimp at h
      rw [Open.inf_compl_eq_bot] at h
      exact h
      simp only [Monotone, le_inf_iff, inf_le_right, and_true, OrderDual.forall,
        OrderDual.toDual_le_toDual]
      exact fun a a_1 a_2 => inf_le_of_left_le a_2
    · exact OrderBot.bot_le (x ⊓ u.compl.toSublocale)
  ·
    intro h i
    rw [Nucleus.ext_iff] at h

    simp [Open.compl, Closed.toSublocale, complement] at h
    conv at h =>
      enter [2]
      rw [Sublocale.inf_apply]
      rw [Sublocale.bot_apply]

    simp [Sublocale.le_iff, Sublocale.bot_apply] at h


    rw [Nucleus.coe_mk, InfHom.coe_mk] at h
    let h1 := h i (x)
    simp at h1
    simp [Open.toSublocale, himp_eq_sSup]
    intro b h2




    sorry -/

/-- The complement operator on opens sends joins to meets: the complement of `U ⊔ V` is
the meet `U.compl ⊓ V.compl`.  This is adjoined with the closed-to-sublocale embedding,
so both sides must be equal as closed elements. -/
lemma compl_sup_eq_inf_compl {U V : Open E} : (U ⊔ V).compl = U.compl ⊓ V.compl := by
  apply_fun ((fun x ↦ ↑x) : Closed E → Sublocale E) using
    Function.Injective.of_eq_imp_le fun {x y} a => (by exact (Closed.le_iff x y).mpr (by grind))
  simp only [Closed.toSublocale, complement, Open.compl]
  ext x
  simp [Closed.inf_def, Open.sup_def]
  --

-- Definitions

/-- The interior of a sublocale `x`: the join of all opens contained in `x`, i.e. the
largest open sublocale below `x`. -/
def Sublocale.interior (x : Sublocale E) := sSup {z : Open E | z ≤ x}
/-- Opens are fixed points of the interior operator: the interior of the open sublocale
associated to `a` is `a` itself. -/
lemma Open_interior_eq_id : ∀ a : Open E, a.toSublocale.interior = a := by
  simp only [Sublocale.interior]
  intro a
  apply le_antisymm
  · simp only [sSup_le_iff, Set.mem_ofPred_eq]
    exact fun b a_1 => Open.le_iff.mpr a_1
  · apply le_sSup
    simp only [Set.mem_ofPred_eq, le_refl]

/-- The interior of an open element is itself; the interior operator is trivial on
opens. -/
def Open.interior (x : Sublocale E) := x
/-- The interior of a closed element, obtained by regarding it as a sublocale and taking
the join of all opens contained in it. -/
noncomputable def Closed.interior (x : Closed E) : Open E := x.toSublocale.interior

/-- The closure of a sublocale `x`: the meet of all closed elements containing `x`, i.e.
the smallest closed covering `x`. -/
def Sublocale.closure (x : Sublocale E) : Closed E := sInf {z : Closed E | x ≤ z}
/-- The closure of an open element: the smallest closed element whose associated
sublocale contains the open. -/
def Open.closure (x : Open E) : Closed E := sInf {z : Closed E | x ≤ z.toSublocale}

/-- The boundary (French `rand`) of a sublocale `x`: the meet of its closure with the
complement of its interior. -/
noncomputable def Sublocale.rand (x : Sublocale E) : Sublocale E :=
  x.closure.toSublocale ⊓ x.interior.compl.toSublocale

/-- The exterior of a sublocale `x`: the join of all opens whose associated sublocale is
disjoint from `x`. -/
def Sublocale.exterior (x : Sublocale E) := sSup {z : Open E | z.toSublocale ⊓ x = ⊥}
/-- The exterior of an open element: the join of all opens disjoint from `x`. -/
def Open.exterior (x : Open E) := sSup {z : Open E | z ⊓ x = ⊥}
/-- The exterior of a closed element: the join of all opens disjoint from the closed. -/
def Closed.exterior (x : Closed E) := sSup {z : Open E | z.toSublocale ⊓ x = ⊥}

/-- An open element is disjoint from its own exterior. -/
lemma Open.inf_Exterior_eq_bot (x : Open E) : x ⊓ x.exterior = ⊥ := by
  simp only [exterior]
  ext
  simp only [inf_def, sSup_def, bot_element]
  rw [inf_sSup_eq]
  simp only [Set.mem_image, Set.mem_ofPred_eq, iSup_exists]
  apply le_antisymm
  · simp only [le_bot_iff, iSup_eq_bot, and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    rw [inf_comm]
    rw [Open.ext_iff] at h
    exact h
  · exact OrderBot.bot_le _


--lemma Open.compl_le_exterior_iff {U V : Open E} :
--    U.compl ≤ V.exterior.toSublocale ↔ V.closure ≤ U.toSublocale := by sorry

--lemma Open.exterior_compl_eq_self {U : Open E} : U.compl.exterior = U := by sorry

--lemma Open.exterior_inf_eq_sup {U V : Open E} :
--    (U ⊓ V).exterior = U.exterior ⊔ V.exterior := by sorry


/-- The complement of the closure of an open element equals its exterior: the largest
open disjoint from `U` is the complement of the smallest closed containing `U`. -/
lemma Closure_compl_eq_exterior (U : Open E) : U.closure.compl = U.exterior := by
  ext
  simp only [Open.closure, Closed.toSublocale, Closed.sInf_def, Closed.compl, Open.exterior,
    complement, Open.sSup_def, Open.toSublocale, Sublocale.le_iff]
  apply le_antisymm
  · simp only [le_sSup_iff, upperBounds, Set.mem_image, Set.mem_ofPred_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sSup_le_iff]
    intro b h1 c h2
    have hbot := h2 ⊥
    simp only [Nucleus.toSublocale_apply, Nucleus.coe_mk, InfHom.coe_mk,
      Open.toNucleus, sup_bot_eq] at hbot
    have h3' : c.element ⊓ U.element = ⊥ :=
      le_antisymm (le_himp_iff.mp hbot) bot_le
    exact h1 ⟨c.element⟩ (by
      ext
      simpa [Open.inf_def] using h3')
  · simp only [le_sSup_iff, upperBounds, Set.mem_image, Set.mem_ofPred_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sSup_le_iff]
    intro b h a ha
    have h_help : (∀ (i : E), (a.element ⊔ i) ⊓ U.element ≤ i) := by
      intro i
      rw [@inf_sup_right]
      simp [Open.inf_def, Open.ext_iff] at ha
      simp [ha]
    have h_open : ∀ i, a.element ≤ U.element ⇨ i ∧ i ≤ U.element ⇨ i := by
      intro i
      constructor
      · apply le_himp_iff.mpr
        exact le_trans (inf_le_inf_right _ le_sup_left) (h_help i)
      · exact le_himp_iff.mpr inf_le_left
    exact h ⟨a.element⟩ (by
      intro i
      simp only [Nucleus.toSublocale_apply, Nucleus.coe_mk, InfHom.coe_mk,
        Open.toNucleus]
      exact le_himp_iff.mpr (h_help i))


/-- The closed element generated by the set-theoretic complement of the underlying
element of `V` equals the complement of the closure of `V`. -/
lemma Sublocale.compl_element_eq_compl_closure (V : Open E) :
    ⟨V.elementᶜ⟩ = V.closure.compl := by
  simp only [Closed.compl, Open.closure, Closed.sInf_def, Open.mk.injEq]
  rw [← himp_bot, himp_eq_sSup]
  apply le_antisymm
  · simp only [le_bot_iff, le_sSup_iff, upperBounds, Set.mem_image, Set.mem_ofPred_eq,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, sSup_le_iff]
    intro b h1 b1 h2
    have h4 : V.toSublocale ≤ (⟨b1⟩ : Closed E).toSublocale := by
      rw [Sublocale.le_iff]
      intro i
      rw [Closed.toSublocale_apply, Open.toSublocale_apply]
      apply le_himp_iff.mpr
      rw [inf_sup_right]
      simp [h2]
    exact h1 ⟨b1⟩ h4
  · simp only [le_bot_iff, sSup_le_iff, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂]
    intro a h
    simp only [le_sSup_iff, upperBounds, Set.mem_ofPred_eq]
    intro b h1
    simp only [Open.toSublocale, Closed.toSublocale, complement, le_iff, apply_eq_toNucleus,
      toNucleus_apply, Nucleus.restrict_toSublocale, Nucleus.coe_mk, InfHom.coe_mk,
      sup_le_iff] at h
    have h3 : a.element ⊓ V.element = ⊥ := by
      let h2 := h ⊥
      simp only [bot_le, and_true] at h2
      exact le_antisymm (le_himp_iff.mp h2) bot_le
    exact h1 h3


/-- The closed element generated by the set-theoretic complement of an open `U` equals
the exterior of `U`; it follows by combining the complement-of-closure and
closure-complement-identifications. -/
lemma Open.compl_element_eq_exterior (U : Open E) : ⟨U.elementᶜ⟩ = U.exterior := by
  rw [Sublocale.compl_element_eq_compl_closure]
  rw [@Closure_compl_eq_exterior]

/-- Every open element is contained in its double exterior; in particular the exterior
operator is extensive on opens. -/
lemma Open.le_exterior_exterior (x : Open E) : x ≤ x.exterior.exterior := by
  rw [← Open.compl_element_eq_exterior, ← Open.compl_element_eq_exterior]
  simp only [le_def]
  exact le_compl_compl

/-- Complements are order-reversing: if the closed element `c` is contained in the open
element `U`, then the complement of `U` is contained in the complement of `c`. -/
lemma Open_compl_le_Closed_compl (U : Open E) (c : Closed E)
    (h : c.toSublocale ≤ U.toSublocale) : U.compl.toSublocale ≤ c.compl.toSublocale := by
  have h : ∀ i, U.element ⇨ i ≤ c.element ⊔ i := by
    intro i
    have hi := (Sublocale.le_iff c.toSublocale U.toSublocale).mp h i
    simpa only [Open.toSublocale_apply, Closed.toSublocale_apply,
      Nucleus.toSublocale_apply] using hi
  have htop : c.element ⊔ U.element = ⊤ := by
    have hU := h U.element
    apply le_antisymm le_top
    simpa [himp_self] using hU
  rw [Sublocale.le_iff]
  intro i
  rw [Open.toSublocale_apply, Closed.toSublocale_apply]
  calc
    c.element ⇨ i = (c.element ⇨ i) ⊓ ⊤ := (inf_top_eq _).symm
    _ = (c.element ⇨ i) ⊓ (c.element ⊔ U.element) := by rw [htop]
    _ = ((c.element ⇨ i) ⊓ c.element) ⊔ ((c.element ⇨ i) ⊓ U.element) := by
      rw [inf_sup_left]
    _ ≤ i ⊔ U.element :=
      sup_le (le_trans himp_inf_le le_sup_left) (le_trans inf_le_right le_sup_right)
    _ = U.element ⊔ i := sup_comm _ _

/-
Dependency: Leroy lemma 8
Leroy 1.10.1

lemma closure_eq_compl_ext (x : Sublocale E) : x.closure = x.exterior.compl := by
  simp [Sublocale.closure,Sublocale.exterior, Open.compl]
  sorry
-/

/-- The closed element generated by the set-theoretic complement of the underlying
element of `V` is contained in the closed complement of `V`: the latter is the largest
disjoint closed. -/
lemma compl_element_le_compl (V : Open E) :
    (⟨V.elementᶜ⟩ : Open E) ≤ V.compl.toSublocale := by
  rw [Sublocale.le_iff]
  intro i
  rw [Open.toSublocale_apply, Closed.toSublocale_apply]
  apply le_himp_iff.mpr
  rw [inf_sup_right]
  simp

/--
Quelle: Johnstone Lemma C 1.1.17 (S· 485)
-/
lemma Sublocale.eq_intersection_open_closed (j : Sublocale E) :
  j = ⨅ a : E, (⟨a⟩ : Open E).toSublocale ⊔ (⟨j a⟩ : Closed E) := by
    apply le_antisymm
    · rw [le_iInf_iff]
      intro a
      rw [Sublocale.le_iff]
      intro l
      rw [Sublocale.sup_apply, Open.toSublocale_apply, Closed.toSublocale_apply]
      rw [inf_sup_left]
      apply sup_le
      · calc
          (a ⇨ l) ⊓ j a ≤ j (a ⇨ l) ⊓ j a :=
            inf_le_inf (Nucleus.le_apply (n := j.toNucleus) (x := a ⇨ l)) le_rfl
          _ = j ((a ⇨ l) ⊓ a) := (j.toNucleus.map_inf).symm
          _ ≤ j l := j.toNucleus.monotone himp_inf_le
      · exact le_trans inf_le_right j.toNucleus.le_apply
    · simp only [iInf_le_iff]
      intro a h i hi
      have h_le : j i ≤ a i := by
        have h_i := (Sublocale.le_iff a
          ((⟨i⟩ : Open E).toSublocale ⊔ (⟨j i⟩ : Closed E).toSublocale)).mp (h i)
        have hji : j i ⊔ i = j i := sup_eq_left.mpr j.toNucleus.le_apply
        simpa only [Sublocale.sup_apply, Open.toSublocale_apply,
          Closed.toSublocale_apply, himp_self, hji, top_inf_eq] using h_i i
      have h_ai : a i = i := by
        have h_restrict :=
          congrArg Subtype.val (Sublocale.restrict_of_mem (S := a) hi)
        simpa using h_restrict
      have h_ji : j.toNucleus i = i := by
        apply le_antisymm
        · simpa [Sublocale.apply_eq_toNucleus, h_ai] using h_le
        · exact j.toNucleus.le_apply
      have h_eq : j.toNucleus.toSublocale = j := by
        change nucleusIsoSublocale (OrderDual.toDual j.toNucleus) = j
        exact nucleusIsoSublocale.right_inv j
      rw [← h_eq]
      exact (Nucleus.mem_toSublocale (n := j.toNucleus) (x := i)).2 ⟨i, h_ji⟩


/-
lemma closure_eq_compl_ext (x : Sublocale E) : x.closure.sublocale = complement (x.sublocale) := by
  rw [Nucleus.exterior, Nucleus.closure, Closed.nucleus]
  have h : ({ element := (sInf {z : Closed E | x ≤ z.nucleus}).element } : Open E) =
      (sSup {z | z.nucleus ⊓ x = ⊥}) := by
    simp [sSup, sInf]
    apply le_antisymm
    · apply sSup_le_sSup
      simp only [Set.image_subset_iff]
      rw [@Set.ofPred_subset]
      intro a h
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
      use ⟨a.element⟩
      simp only [and_true]
      sorry --wahrscheinlich leroy lemme 8
    · apply sSup_le_sSup
      simp only [Set.image_subset_iff]
      rw [@Set.ofPred_subset]
      intro xi hxi
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
      use ⟨xi.element⟩
      simp only [and_true]
      sorry --wahrscheinlich wieder leroy lemme 8
W

  apply_fun complement at h
  exact h -/

/-
lemma rand_eq_compl_int_ext (x : Sublocale E) :
    x.rand = complement (x.interior ⊔ x.exterior) := by sorry

lemma int_rand_eq_closure (x : Sublocale E) :
    x.interior.sublocale ⊔ x.rand = x.closure.sublocale := by sorry

lemma ext_rand_eq_comp_int (x : Sublocale E) :
    ↑x.exterior ⊔ x.rand = complement (x.interior) := by sorry -/
