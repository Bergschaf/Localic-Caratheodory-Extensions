module

public import Leroy.Sublocale
public import Mathlib.Order.CompleteSublattice
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Tactic

/-!
# Further topology on frames: neighbourhoods, complements, interior, closure and exterior

This file develops point-set style constructions for sublocales of a frame: systems of
open neighbourhoods of a sublocale, the closed complement on opens (Leroy Lemme 8 and
8 bis), and the interior, closure, boundary and exterior operators.  It is part
of the port of Leroy's thesis on localic measure theory and supports the Caratheodory
extension development.
-/

@[expose] public section

variable {X Y E : Type u} [Order.Frame X] [Order.Frame Y] [e_frm : Order.Frame E]
open Sublocale

/-- The set of open elements of `X` containing the sublocale `u`, i.e. those opens `v`
with `u ≤ v`; these form the system of open neighbourhoods of `u`. -/
def Sublocale.openNhds (u : Sublocale X) : Set (Open X) := {v : Open X | u ≤ v}

/-- The set of sublocales containing some open element above `u`: the usual system of
neighbourhoods of the sublocale `u`. -/
def Sublocale.nhds (u : Sublocale X) : Set (Sublocale X) :=
  {v | ∃ w ∈ openNhds u, w ≤ v}

/-- Every sublocale in the neighbourhood system of `a` contains `a` itself. -/
lemma Sublocale.le_of_mem_nhds {a : Sublocale E} : ∀ x ∈ nhds a, a ≤ x := by
  intro x h
  simp only [nhds, openNhds, Set.mem_ofPred_eq] at h
  rcases h with ⟨w, ⟨h1, h2⟩⟩
  exact Preorder.le_trans a w.toSublocale x h1 h2

/-- The largest open element `⊤` of `X` contains every sublocale, hence is an open
neighbourhood of any `x`. -/
lemma Sublocale.openNhds_top_mem {x : Sublocale X} : ⊤ ∈ openNhds x := by
  simp [openNhds]

/-- The open neighbourhood system of any sublocale is nonempty: the open element `⊤`
always belongs to it. -/
@[simp]
lemma Sublocale.openNhds_nonempty (x : Sublocale X) :
    (openNhds x).Nonempty := by
  use ⊤
  exact openNhds_top_mem

/-- The open neighbourhood system of any sublocale is nonempty as an inhabited set,
witnessed by the open element `⊤`. -/
@[simp]
lemma Sublocale.nonempty_openNhds (x : Sublocale X) :
    Nonempty (openNhds x) := by
  use ⊤
  exact openNhds_top_mem

-- TODO: remaining neighbourhood lemmas (e.g. upward closure of the neighbourhood system)
/-- The top sublocale is a neighbourhood of every sublocale `x`, since it contains the
open neighbourhood `⊤`. -/
lemma Sublocale.top_mem_nhds (x : Sublocale X) : ⊤ ∈ nhds x := by
  simp only [nhds, Set.mem_ofPred_eq, le_top, and_true]
  use ⊤
  exact openNhds_top_mem

/-- The neighbourhood system of any sublocale is nonempty, witnessed by the top
sublocale. -/
lemma Sublocale.nonempty_nhds (x : Sublocale X) : Nonempty (nhds x) := by
  use ⊤
  exact top_mem_nhds x

/-- The open neighbourhoods of a sublocale are closed under binary meet: if the opens
`U` and `V` both contain `x`, then so does the open `U ⊓ V`. -/
lemma Sublocale.openNhds_inf_closed {x : Sublocale E} :
    ∀ U ∈ openNhds x, ∀ V ∈ openNhds x, U ⊓ V ∈ openNhds x := by
  simp only [openNhds, Set.mem_ofPred_eq]
  intro U h1 V h2
  rw [Open.preserves_inf]
  exact le_inf h1 h2

/-- The neighbourhoods of a sublocale are closed under binary meet: if each of `U` and
`V` contains an open element above `x`, then `U ⊓ V` contains one as well. -/
lemma Sublocale.nhds_inf_closed (x : Sublocale E) :
    ∀ U ∈ nhds x, ∀ V ∈ nhds x, U ⊓ V ∈ nhds x := by
  simp only [nhds, openNhds, Set.mem_ofPred_eq, le_inf_iff,
    forall_exists_index, and_imp]
  intro a x1 h1 h2 n x2 h3 h4
  use x1 ⊓ x2
  simp_all only [Open.preserves_inf, le_inf_iff, and_self, true_and]
  apply And.intro
  · exact inf_le_of_left_le h2
  · exact inf_le_of_right_le h4

-- Properties of Complement

/-- Leroy's Lemme 8: an open sublocale `V` joins with a sublocale `x` to the top
exactly when `x` contains the closed complement `V.compl`. -/
lemma Open.sup_eq_top_iff_compl_le (V : Open E) (x : Sublocale E) :
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

/-- Leroy's Lemme 8: the meet of an open sublocale `V` with a sublocale `x`
is the bottom element exactly when `x` is contained in the closed complement `V.compl`.
The forward direction uses the pointwise nucleus `a ↦ V.element ⇨ x a`
(`Nucleus.openHimp`), which lies below both `V.toSublocale` and `x`. -/
lemma Open.inf_eq_bot_iff_le_compl (V : Open E) (x : Sublocale E) :
    V.toSublocale ⊓ x = ⊥ ↔ x ≤ V.compl := by
  constructor
  · intro h
    have h_inf : ∀ i, (⨅ j ∈ lowerBounds {V.toSublocale, x}, j i) = ⊤ := by
      intro i
      have h_eval := congrArg (fun s : Sublocale E => s i) h
      simpa only [Sublocale.inf_apply, Sublocale.bot_apply] using h_eval
    have h_helpV : (Nucleus.openHimp V.element x.toNucleus).toSublocale ≤ V.toSublocale :=
      Nucleus.openHimp_le_open V.element x.toNucleus
    have h_helpx : (Nucleus.openHimp V.element x.toNucleus).toSublocale ≤ x := by
      have h := Nucleus.openHimp_le V.element x.toNucleus
      rwa [Sublocale.toNucleus_toSublocale] at h
    have h_help : (Nucleus.openHimp V.element x.toNucleus).toSublocale
        ∈ lowerBounds {V.toSublocale, x} := by
      intro a ha
      rcases ha with ha | ha
      · rw [ha]; exact h_helpV
      · rw [ha]; exact h_helpx
    apply (Sublocale.le_iff _ _).mpr
    intro i
    rw [Closed.toSublocale_apply]
    have h_top : ⊤ ≤ (Nucleus.openHimp V.element x.toNucleus).toSublocale i := by
      rw [← h_inf i]
      exact iInf_le_of_le _ (iInf_le_of_le h_help le_rfl)
    have h_open : V.element ≤ x i := by
      apply himp_eq_top_iff.mp
      simpa [Nucleus.openHimp] using h_top
    exact sup_le h_open x.toNucleus.le_apply
  · intro h
    apply le_antisymm
    · exact le_trans (inf_le_inf_left _ h) (by rw [Open.inf_compl_eq_bot V])
    · exact bot_le


/--
Leroy Lemme 8 bis
-/
lemma Open.le_iff_sup_compl_eq_top {x : Sublocale E} {u : Open E} : u ≤ x ↔ x ⊔ (u.compl) = ⊤ := by
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


/-- The complement operator on opens sends joins to meets: the complement of `U ⊔ V` is
the meet `U.compl ⊓ V.compl`.  This is adjoined with the closed-to-sublocale embedding,
so both sides must be equal as closed elements. -/
lemma Open.compl_sup_eq_inf_compl {U V : Open E} : (U ⊔ V).compl = U.compl ⊓ V.compl := by
  apply_fun ((fun x ↦ ↑x) : Closed E → Sublocale E) using
    Function.Injective.of_eq_imp_le fun {x y} a => (by exact (Closed.le_iff x y).mpr (by grind))
  simp only [Closed.toSublocale, Open.complNucleus, Open.compl]
  ext x
  simp [Closed.inf_def, Open.sup_def]
  --

-- Definitions

/-- The interior of a sublocale `x`: the join of all opens contained in `x`, i.e. the
largest open sublocale below `x`. -/
def Sublocale.interior (x : Sublocale E) := sSup {z : Open E | z ≤ x}
/-- Opens are fixed points of the interior operator: the interior of the open sublocale
associated to `a` is `a` itself. -/
lemma Open.toSublocale_interior : ∀ a : Open E, a.toSublocale.interior = a := by
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

/-- The boundary (French `boundary`) of a sublocale `x`: the meet of its closure with the
complement of its interior. -/
noncomputable def Sublocale.boundary (x : Sublocale E) : Sublocale E :=
  x.closure.toSublocale ⊓ x.interior.compl.toSublocale

/-- The exterior of a sublocale `x`: the join of all opens whose associated sublocale is
disjoint from `x`. -/
def Sublocale.exterior (x : Sublocale E) := sSup {z : Open E | z.toSublocale ⊓ x = ⊥}
/-- The exterior of an open element: the join of all opens disjoint from `x`. -/
def Open.exterior (x : Open E) := sSup {z : Open E | z ⊓ x = ⊥}
/-- The exterior of a closed element: the join of all opens disjoint from the closed. -/
def Closed.exterior (x : Closed E) := sSup {z : Open E | z.toSublocale ⊓ x = ⊥}

/-- An open element is disjoint from its own exterior. -/
lemma Open.inf_exterior_eq_bot (x : Open E) : x ⊓ x.exterior = ⊥ := by
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



/-- The complement of the closure of an open element equals its exterior: the largest
open disjoint from `U` is the complement of the smallest closed containing `U`. -/
lemma Open.closure_compl_eq_exterior (U : Open E) : U.closure.compl = U.exterior := by
  ext
  simp only [Open.closure, Closed.toSublocale, Closed.sInf_def, Closed.compl, Open.exterior,
    Open.complNucleus, Open.sSup_def, Open.toSublocale, Sublocale.le_iff]
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
    simp only [Open.toSublocale, Closed.toSublocale, Open.complNucleus, le_iff, apply_eq_toNucleus,
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
  rw [@Open.closure_compl_eq_exterior]

/-- Every open element is contained in its double exterior; in particular the exterior
operator is extensive on opens. -/
lemma Open.le_exterior_exterior (x : Open E) : x ≤ x.exterior.exterior := by
  rw [← Open.compl_element_eq_exterior, ← Open.compl_element_eq_exterior]
  simp only [le_def]
  exact le_compl_compl

/-- Complements are order-reversing: if the closed element `c` is contained in the open
element `U`, then the complement of `U` is contained in the complement of `c`. -/
lemma Open.compl_le_Closed_compl (U : Open E) (c : Closed E)
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


/-- The closed element generated by the set-theoretic complement of the underlying
element of `V` is contained in the closed complement of `V`: the latter is the largest
disjoint closed. -/
lemma Open.compl_element_le (V : Open E) :
    (⟨V.elementᶜ⟩ : Open E) ≤ V.compl.toSublocale := by
  rw [Sublocale.le_iff]
  intro i
  rw [Open.toSublocale_apply, Closed.toSublocale_apply]
  apply le_himp_iff.mpr
  rw [inf_sup_right]
  simp

/-- Every sublocale is the intersection of the open sublocales containing it and the
closed sublocales it is contained in (Johnstone, *Sketches of an Elephant*,
Lemma C1.1.17, p. 485). -/
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



