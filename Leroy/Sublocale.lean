/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
module

import Mathlib.Tactic.Widget.Conv
import Mathlib.Tactic.ApplyFun
public import Mathlib.Order.Sublocale
public import Leroy.Nucleus

/-!
# Sublocales

Open and closed sublocales of a frame, and the lattice operations they inherit.
-/

@[expose] public section

variable {E : Type*} [Order.Frame E]


open Nucleus

/-- Sublocales embed faithfully into nuclei: two sublocales with the same nucleus are equal. -/
lemma Sublocale.toNucleus_injective : Function.Injective (@Sublocale.toNucleus E _) := by
  intro a b h
  calc
    a = nucleusIsoSublocale (OrderDual.toDual a.toNucleus) := by
      exact (nucleusIsoSublocale.right_inv a).symm
    _ = nucleusIsoSublocale (OrderDual.toDual b.toNucleus) :=
      congrArg nucleusIsoSublocale (congrArg OrderDual.toDual h)
    _ = b := nucleusIsoSublocale.right_inv b

/-- Sublocales act on points of the frame through their associated nucleus. -/
instance : FunLike (Sublocale E) E E where
  coe x := x.toNucleus
  coe_injective f g h := by
    have hfg : f.toNucleus = g.toNucleus := DFunLike.coe_injective h
    exact Sublocale.toNucleus_injective hfg

/-- Applying the sublocale dual to a nucleus agrees with applying the nucleus. -/
@[simp] lemma Sublocale.symm_apply (S : Sublocale E) (x : E) :
    OrderDual.ofDual (nucleusIsoSublocale.symm S) x = S x := by
  change S.toNucleus x = S.toNucleus x
  rfl

/-- Taking the nucleus of the sublocale of a nucleus reproduces the nucleus: the
nucleus–sublocale correspondence is a two-sided iso on nuclei. -/
@[simp] lemma Sublocale.toNucleus_toSublocale (S : Sublocale E) :
    S.toNucleus.toSublocale = S := by
  change nucleusIsoSublocale (OrderDual.toDual S.toNucleus) = S
  exact nucleusIsoSublocale.right_inv S

/-- The nucleus of the sublocale dual to a nucleus is the nucleus itself. -/
@[simp] lemma Sublocale.symm_toNucleus (S : Sublocale E) :
    OrderDual.ofDual (nucleusIsoSublocale.symm S) = S.toNucleus := by
  ext x
  exact Sublocale.symm_apply S x

/-- Application of a sublocale to a point is the same as restriction to that point. -/
@[simp] lemma Sublocale.apply_eq_toNucleus (S : Sublocale E) (x : E) :
    S x = S.toNucleus x := rfl

/-- Restriction of a sublocale to a point computes the nucleus action at that point. -/
lemma Sublocale.coe_restrict (S : Sublocale E) (x : E) :
    (S.restrict x : E) = S x := rfl

/-- A sublocale is coerced to its nucleus. -/
instance : Coe (Sublocale E) (Nucleus E) where
  coe := Sublocale.toNucleus

/-- Sublocales are closures: applying one twice is the same as applying it once. -/
@[simp] lemma Sublocale.idempotent (S : Sublocale E) (x : E) :
    S (S x) = S x := S.toNucleus.idempotent x

/-- Sublocales preserve finite meets of the frame pointwise. -/
@[simp] lemma Sublocale.map_inf (S : Sublocale E) (x y : E) :
    S (x ⊓ y) = S x ⊓ S y := S.toNucleus.map_inf' x y

/-- Sublocales are inflationary closure operators. -/
@[simp] lemma Sublocale.le_apply (S : Sublocale E) (x : E) : x ≤ S x :=
  S.toNucleus.le_apply

/-- Sublocales are monotone. -/
lemma Sublocale.monotone (S : Sublocale E) : Monotone S :=
  S.toNucleus.monotone

/-- The order on sublocales is pointwise reverse: `u ≤ v` iff `v` maps every point below
`u`'s image. This matches the convention that the top sublocale is the identity and `sup`
corresponds to intersection. -/
lemma Sublocale.le_iff (u v : Sublocale E) : u ≤ v ↔ ∀ i, v i ≤ u i := by
  constructor
  · intro h i
    exact (Sublocale.toNucleus_le_toNucleus (S := v) (T := u)).2 h i
  · intro h
    apply (Sublocale.toNucleus_le_toNucleus (S := v) (T := u)).1
    intro i
    exact h i

/-- Extensionality for sublocales: equal at every point of the frame means equal. -/
@[ext]
lemma ext (a b : Sublocale E) (h : ∀ x, a x = b x) : a = b := by
  exact Sublocale.toNucleus_injective (Nucleus.ext h)

/-- The sublocale of a nucleus acts on points exactly like the nucleus. -/
@[simp] lemma Nucleus.toSublocale_apply (n : Nucleus E) (x : E) :
    n.toSublocale x = n x := by
  change (n.toSublocale.restrict x).val = n x
  simp

/-- Suprema of sublocales are computed pointwise: applying a supremum intersects the nuclei of
its members (echoing the reverse order convention). -/
@[simp] lemma Sublocale.sSup_apply (s : Set (Sublocale E)) (x : E) : sSup s x = ⨅ j ∈ s, j x := by
  change (OrderDual.ofDual (nucleusIsoSublocale.symm (sSup s))) x = _
  rw [(nucleusIsoSublocale.symm).map_sSup]
  simp only [ofDual_iSup, Nucleus.iInf_apply, Sublocale.symm_toNucleus]
  refine iInf_congr fun j => ?_
  by_cases hj : j ∈ s <;> simp [hj, Sublocale.apply_eq_toNucleus]

/-- Infima of sublocales are computed pointwise over the lower bounds (in the reverse order
convention an infimum is a supremum of nuclei). -/
@[simp] lemma Sublocale.sInf_apply (s : Set (Sublocale E)) (x : E) :
    sInf s x = ⨅ j ∈ lowerBounds s, j x := by
  rw [← sSup_lowerBounds_eq_sInf]
  exact Sublocale.sSup_apply (lowerBounds s) x

/-- Pointwise computation of the join of a family of sublocales. -/
@[simp]
lemma Sublocale.iSup_apply {ι : Type*} (f : ι → Sublocale E) (x : E) : iSup f x = ⨅ j, f j x := by
  simp only [iSup, sSup_apply, Set.mem_range, iInf_exists]
  refine le_antisymm ?_ (by simpa using fun a => iInf_le (fun j => (f j) x) a)
  simp only [le_iInf_iff, iInf_le_iff, forall_apply_eq_imp_iff]
  exact fun i b a => a i

/-- The join of two sublocales acts by intersecting their nuclei: `u x ⊓ v x`. -/
@[simp] lemma Sublocale.sup_apply (u v : Sublocale E) (x : E) : (u ⊔ v) x = u x ⊓ v x := by
  change (OrderDual.ofDual (nucleusIsoSublocale.symm (u ⊔ v))) x = _
  rw [(nucleusIsoSublocale.symm).map_sup]
  rfl

/-- The meet of two sublocales acts by joining nuclei of the lower bounds of the pair. -/
@[simp]
lemma Sublocale.inf_apply (u v : Sublocale E) (x : E) :
    (u ⊓ v) x = ⨅ j ∈ lowerBounds {u, v}, j x := by
  rw [← sInf_pair, Sublocale.sInf_apply]

/-- The intersection of the carriers of two sublocales is again the carrier of a sublocale:
`x` in both `u` and `v` implies `x` in their meet. -/
lemma Sublocale.mem_inf_of_mem {u v : Sublocale E} {x : E} (hu : x ∈ u) (hv : x ∈ v) :
    x ∈ u ⊓ v := by
  let C : Sublocale E := {
    carrier := (u : Set E) ∩ v
    sInf_mem' := by
      intro s hs
      exact ⟨u.sInf_mem (by
        intro y hy
        exact (hs hy).1), v.sInf_mem (by
        intro y hy
        exact (hs hy).2)⟩
    himp_mem' := by
      intro a b hb
      exact ⟨u.himp_mem hb.1, v.himp_mem hb.2⟩
  }
  have hCu : C ≤ u := SetLike.coe_subset_coe.mp (by
    intro y hy
    change y ∈ (u : Set E) ∩ v at hy
    exact hy.1)
  have hCv : C ≤ v := SetLike.coe_subset_coe.mp (by
    intro y hy
    change y ∈ (u : Set E) ∩ v at hy
    exact hy.2)
  have hC : C ≤ u ⊓ v := le_inf hCu hCv
  have hxC : x ∈ C := by
    change x ∈ (u : Set E) ∩ v
    exact Set.mem_inter hu hv
  exact (SetLike.coe_subset_coe.mpr hC) hxC

/-- A point belongs to a meet of sublocales iff it belongs to both
(via the intersection carrier). -/
@[simp] lemma Sublocale.mem_inf (u v : Sublocale E) {x : E} :
    x ∈ u ⊓ v ↔ x ∈ u ∧ x ∈ v := by
  constructor
  · intro hx
    exact ⟨(SetLike.coe_subset_coe.mpr inf_le_left) hx,
      (SetLike.coe_subset_coe.mpr inf_le_right) hx⟩
  · rintro ⟨hu, hv⟩
    exact Sublocale.mem_inf_of_mem hu hv

/-- Membership in a sublocale is captured by the nucleus fixing the point. -/
lemma Sublocale.mem_iff_apply_eq (S : Sublocale E) (x : E) :
    x ∈ S ↔ S x = x := by
  have hS : S.toNucleus.toSublocale = S := by
    change nucleusIsoSublocale (OrderDual.toDual S.toNucleus) = S
    exact nucleusIsoSublocale.right_inv S
  rw [← hS, Nucleus.mem_toSublocale]
  constructor
  · rintro ⟨y, rfl⟩
    simpa only [Nucleus.toSublocale_apply] using S.toNucleus.idempotent y
  · intro hx
    exact ⟨x, by simpa only [Nucleus.toSublocale_apply] using hx⟩

/-- The top sublocale is the identity nucleus: it fixes every point. -/
@[simp] lemma Sublocale.top_apply (x : E) : (⊤ : Sublocale E) x = x := by
  change (OrderDual.ofDual (nucleusIsoSublocale.symm (⊤ : Sublocale E))) x = x
  rw [(nucleusIsoSublocale.symm).map_top]
  simp

/-- The bottom sublocale maps every point to the top of the frame. -/
@[simp] lemma Sublocale.bot_apply (x : E) : (⊥ : Sublocale E) x = ⊤ := by
  change (OrderDual.ofDual (nucleusIsoSublocale.symm (⊥ : Sublocale E))) x = ⊤
  rw [(nucleusIsoSublocale.symm).map_bot]
  simp

/-- An open sublocale of a frame: an element `U` of the frame as the nucleus `x ↦ U ⇨ x`.
Its carrier is closed under arbitrary suprema and under implication. -/
@[ext]
structure Open (E : Type*) [Order.Frame E] where
  element : E

namespace Open

variable {U V : Open E}

/-- The nucleus `x ↦ U ⇨ x` associated with an open element `U`. -/
protected def toNucleus (U : Open E) : Nucleus E where
  toFun x := U.element ⇨ x
  map_inf' x y := himp_inf_distrib U.element x y
  idempotent' x := by simp
  le_apply' x := by simp

/-- An open element gives a sublocale via its associated Heyting nucleus. -/
protected def toSublocale (U : Open E) : Sublocale E := U.toNucleus.toSublocale

/-- Applying the sublocale of an open element is Heyting implication by that element. -/
@[simp] lemma toSublocale_apply (U : Open E) (x : E) :
    U.toSublocale x = U.element ⇨ x := by
  simp [Open.toSublocale, Open.toNucleus]

/-- The pointwise Heyting implication nucleus `a ↦ V ⇨ n a` lies below the open nucleus
`a ↦ V ⇨ a`. -/
lemma Nucleus.openHimp_le_open (V : E) (n : Nucleus E) :
    (Nucleus.openHimp V n).toSublocale ≤ (⟨V⟩ : Open E).toNucleus.toSublocale := by
  rw [Nucleus.toSublocale_le_toSublocale]
  intro a
  exact le_himp_iff.mpr ((himp_inf_le : (V ⇨ a) ⊓ V ≤ a).trans n.le_apply)

/-- An open element is coerced to its underlying frame element. -/
instance : Coe (Open E) E where
  coe x := x.element

/-- An open element is coerced to its open sublocale. -/
instance : Coe (Open E) (Sublocale E) where
  coe x := x.toSublocale

/-- The order on opens is the order of the underlying frame elements. -/
instance : LE (Open E) where
  le x y := x.element ≤ y.element


/-- Opens of a frame form a partial order, inherited from the frame. -/
instance : PartialOrder (Open E) where
  le_refl a := by rfl
  le_trans a b c h1 h2 := by exact Preorder.le_trans a.element b.element c.element h1 h2
  le_antisymm a b h1 h2 := by ext; exact le_antisymm h1 h2

/-- The order on opens is exactly the order of their elements. -/
lemma le_def : U ≤ V ↔ U.element ≤ V.element := by rfl
/-- The strict order on opens is exactly the strict order of their elements. -/
lemma lt_def : U < V ↔ U.element < V.element := lt_iff_lt_of_le_iff_le' le_def le_def

/-- The map sending an open to its sublocale is monotone. -/
lemma toSublocale.mono : Monotone (@Open.toSublocale E _) := by
  intro a b h
  rw [Sublocale.le_iff]
  intro i
  simp only [Open.toSublocale_apply]
  exact himp_le_himp_right h

/-- The constructor of an open is monotone. -/
lemma mk_mono : Monotone (@Open.mk E _) := by
  simp [Monotone, Open.le_def]

/-- The opens of a frame form a bounded order with the same top and bottom as the frame. -/
instance instBoundedOrder : BoundedOrder (Open E) where
  top := ⟨⊤⟩
  le_top x := OrderTop.le_top x.element
  bot := ⟨⊥⟩
  bot_le x := OrderBot.bot_le x.element

/-- The top open has the top of the frame as element. -/
@[simp] lemma top_element : (⊤ : Open E).element = ⊤ := rfl
/-- The bottom open has the bottom of the frame as element. -/
@[simp] lemma bot_element : (⊥ : Open E).element = ⊥ := rfl
/-- The top open gives the top sublocale. -/
@[simp] lemma top_toSublocale : (⊤ : Open E).toSublocale = ⊤ := by
  ext x
  simp only [Open.toSublocale_apply, top_element, top_himp, Sublocale.top_apply]

/-- The bottom open gives the bottom sublocale. -/
@[simp] lemma bot_toSublocale : (⊥ : Open E).toSublocale = ⊥ := by
  ext x
  simp only [Open.toSublocale_apply, bot_element, bot_himp, Sublocale.bot_apply]

/-- Opens of a frame admit suprema computed in the underlying frame. -/
instance instCompleteSemilatticeSup : CompleteSemilatticeSup (Open E) where
  sSup s := ⟨sSup (Open.element '' s)⟩
  isLUB_sSup s := by
    refine ⟨?_, ?_⟩
    · intro U hU
      change U.element ≤ sSup (Open.element '' s)
      exact le_sSup (Set.mem_image_of_mem Open.element hU)
    · intro U hU
      change sSup (Open.element '' s) ≤ U.element
      change ∀ V ∈ s, V ≤ U at hU
      apply sSup_le
      rintro x ⟨V, hV, rfl⟩
      exact hU V hV

/-- Suprema of opens are elementwise suprema in the frame. -/
lemma sSup_def (s : Set (Open E)) : sSup s = ⟨sSup (Open.element '' s)⟩ := rfl

/-- Opens of a frame admit binary meets computed in the underlying frame. -/
instance instSemilatticeInf : SemilatticeInf (Open E) where
  inf x y := ⟨x ⊓ y⟩
  inf_le_left x y := by simp [le_def]
  inf_le_right x y := by simp [le_def]
  le_inf x y z h1 h2 := by simpa [le_def] using ⟨h1, h2⟩

/-- The opens of a frame form a complete lattice, mirroring the frame itself. -/
instance : CompleteLattice (Open E) where
  __ := instBoundedOrder
  __ := instSemilatticeInf
  __ := completeLatticeOfCompleteSemilatticeSup (Open E)

/-- Binary joins of opens are elementwise joins in the frame. -/
lemma sup_def (u v : Open E) : u ⊔ v = ⟨u.element ⊔ v.element⟩ := by
  rw [← sSup_pair, sSup_def, Set.image_pair, sSup_pair]

/-- Binary meets of opens are elementwise meets in the frame. -/
lemma inf_def (u v : Open E) : u ⊓ v = ⟨u ⊓ v⟩ := rfl

/-- An open wrapped back up is itself. -/
@[simp] lemma mk_element (U : Open E) : ⟨U.element⟩ = U := rfl

/-- The sublocale of an open fixes its own element, i.e. the element is "open" in the sublocale. -/
@[simp] lemma apply_self (U : Open E) : U.toSublocale U.element = ⊤ := by
  change U.toNucleus.toSublocale U.element = ⊤
  simp [Open.toNucleus]
  rfl

/-- Inclusion of opens agrees with inclusion of their sublocales. -/
lemma le_iff : U ≤ V ↔ U.toSublocale ≤ V.toSublocale := by
  apply Iff.intro
  · simp only [Sublocale.le_iff, toSublocale_apply]
    intro h i
    exact himp_le_himp_right h
  · simp only [Sublocale.le_iff, toSublocale_apply]
    intro h
    let h1 := h V
    simp only [himp_self, le_himp_iff, le_top, inf_of_le_right] at h1
    exact h1


/-- The map from opens to sublocales is injective: opens embed in the lattice of sublocales. -/
lemma toSublocale_injective : Function.Injective (@Open.toSublocale E _) := by
  rw [Function.Injective]
  intro a1 a2 h
  apply le_antisymm
  · exact le_iff.mpr (le_of_eq h)
  · exact le_iff.mpr (ge_of_eq h)

/-- Open elements are equal exactly when their sublocales are. -/
lemma eq_iff : U = V ↔ U.toSublocale = V.toSublocale := by
  apply Iff.intro
  · exact fun h => congrArg Open.toSublocale h
  · exact fun h => toSublocale_injective h

/-- The carrier of a literally given sublocale is its defining set. -/
@[simp] lemma Sublocale.coe_mk (f : Set E) (h2 : ∀ s ⊆ f, sInf s ∈ f)
    (h3 : ∀ a b : E, b ∈ f → a ⇨ b ∈ f) :
    (⟨f, h2, h3⟩ : Sublocale E) = f := rfl

/-- Meets of opens are sent to meets of sublocales: the embedding is inf-preserving.

Both inclusions are proved pointwise after unfolding all four sublocale actions:
`≤` uses that a lower bound of `U.toSublocale` and `V.toSublocale` fixes every point
of the form `x ⊓ V.element` (then idempotence closes the chain), while `≥` evaluates
the meet at the open `U.element ⊓ V.element` itself. -/
lemma preserves_inf (U V : Open E) : (U ⊓ V).toSublocale = U.toSublocale ⊓ V.toSublocale := by
  ext x
  simp only [inf_def, toSublocale_apply, Sublocale.inf_apply, lowerBounds_insert,
    lowerBounds_singleton, Set.Iic_inter_Iic, Set.mem_Iic, le_inf_iff]
  apply le_antisymm
  · simp only [le_iInf_iff, and_imp]
    intro a h1 h2
    have h1' : ∀ i, U.element ⇨ i ≤ a i := by
      simpa only [Open.toSublocale_apply] using (Sublocale.le_iff a U.toSublocale).mp h1
    have h2' : ∀ i, V.element ⇨ i ≤ a i := by
      simpa only [Open.toSublocale_apply] using (Sublocale.le_iff a V.toSublocale).mp h2
    simp only [himp_eq_sSup, sSup_le_iff, Set.mem_ofPred_eq] at *
    intro b h3
    let h1 := h1' x (b ⊓ V) (by rw  [inf_assoc, inf_comm V.element]; exact h3)
    let h2 := h2' (a x) b h1
    apply le_trans h2
    change a.toNucleus (a.toNucleus x) ≤ a.toNucleus x
    exact (a.toNucleus.idempotent x).le
  · rw [iInf_le_iff]
    intro b h
    let h1 := h ((⟨U.element ⊓ V.element⟩ :Open E) : Sublocale E)
    simp only [le_iInf_iff, and_imp] at h1
    simpa only [Open.toSublocale_apply] using h1
      (Open.toSublocale.mono inf_le_left) (Open.toSublocale.mono inf_le_right)

/-- Suprema of opens are sent to suprema of sublocales: the embedding preserves all joins.

Pointwise, the statement reduces to the fact that Heyting implication exchanges
suprema on the left for infima on the right:
`(sSup (Open.element '' s)) ⇨ x = ⨅ U ∈ s, U.element ⇨ x`. -/
lemma preserves_sSup (s : Set (Open E)) : (sSup s).toSublocale = sSup (Open.toSublocale '' s) := by
  ext x
  simp only [sSup_def, toSublocale_apply, Sublocale.sSup_apply, Set.mem_image, iInf_exists]
  apply le_antisymm
  · simp only [le_iInf_iff, and_imp, forall_apply_eq_imp_iff₂, toSublocale_apply, le_himp_iff]
    intro a h
    rw [@sSup_image, himp_eq_sSup, sSup_inf_eq]
    simp only [Set.mem_ofPred_eq, iSup_le_iff]
    intro i h1
    apply le_trans' h1
    simpa using inf_le_of_right_le <| le_biSup element h
  · rw [iInf_le_iff]
    simp only [le_iInf_iff, and_imp, forall_apply_eq_imp_iff₂, toSublocale_apply, le_himp_iff]
    intro b h
    rw [inf_sSup_eq]
    simp only [Set.mem_image, iSup_exists, iSup_le_iff, and_imp, forall_apply_eq_imp_iff₂]
    exact h

/-- Joins of families of opens are sent to joins of the corresponding sublocales. -/
lemma preserves_iSup (f : ι → Open E) : (iSup f).toSublocale = ⨆ i : ι, (f i).toSublocale := by
  rw [iSup]
  rw [preserves_sSup]
  rw [sSup_image']
  exact iSup_range' Open.toSublocale f

/-- Binary joins of opens are sent to joins of sublocales. -/
lemma preserves_sup : (U ⊔ V).toSublocale = U.toSublocale ⊔ V.toSublocale := by
  rw [← sSup_pair, preserves_sSup, Set.image_pair, sSup_pair]


end Open

/-- The closed nucleus `x ↦ U ⊔ x` associated with an open element `U`; its sublocale is the
closed sublocale complementary to `U`. -/
def Open.complNucleus (U : Open E) : Nucleus E where
  toFun x := U ⊔ x
  map_inf' x y := sup_inf_left U.element x y
  idempotent' x := by simp
  le_apply' x := by simp

/-- A closed sublocale of a frame: an element `c` of the frame as the closed nucleus `x ↦ c ⊔ x`. -/
@[ext]
structure Closed (E : Type*) [Order.Frame E] where
  element : E

namespace Closed

/-- The closed sublocale of a closed element, via the complementary Heyting nucleus. -/
protected def toSublocale (c : Closed E) : Sublocale E :=
  (Open.complNucleus ⟨c.element⟩).toSublocale

/-- Applying the sublocale of a closed element is the join with that element. -/
lemma toSublocale_apply (c : Closed E) (x : E) : c.toSublocale x = c.element ⊔ x := by
  simp [Closed.toSublocale, Open.complNucleus]

/-- A closed element is coerced to its closed sublocale. -/
instance : Coe (Closed E) (Sublocale E) where
  coe x := x.toSublocale

/-- The order on closed sublocales is the reverse of the frame order on their elements. -/
instance : LE (Closed E) where
  le x y := y.element ≤ x.element

/-- The order on closed sublocales is the reverse of the order of their elements. -/
lemma le_def (x y : Closed E) : x ≤ y ↔ y.element ≤ x.element := by rfl

/-- Inclusion of closed sublocales agrees with the reversed element order. -/
lemma le_iff (x y : Closed E) : x ≤ y ↔ x.toSublocale ≤ y.toSublocale := by
  rw [Sublocale.le_iff]
  simp only [Closed.le_def, Closed.toSublocale_apply]
  constructor
  · intro h i
    exact sup_le_sup_right h _
  · intro h
    simpa using h ⊥

/-- The open element underlying a closed sublocale's complementary nucleus. -/
def compl (c : Closed E) : Open E := ⟨c.element⟩

/-- The complement of a closed has exactly that element. -/
@[simp] lemma element_compl (c : Closed E) : c.compl.element = (⟨c.element⟩ : Open E) := by
  rfl

/-- Closed elements admit infima, computed as suprema of elements (order is reversed). -/
instance instInfSet : InfSet (Closed E) where
  sInf x := ⟨sSup (Closed.element '' x)⟩

/-- Infima of closed sublocales are elementwise suprema of the underlying elements. -/
lemma sInf_def (s : Set (Closed E)) : sInf s = ⟨sSup (Closed.element '' s)⟩ := by rfl

/-- Sending closed sublocales to their sublocales turns infima into infima.

Since the order on closed elements is reversed, the infimum of a set of closed elements
has underlying element the supremum of the underlying elements; the pointwise statement
is that `sSup (Closed.element '' s) ⊔ x = ⨅ c ∈ s, (c.element ⊔ x)`. -/
lemma preserves_sInf (s : Set (Closed E)) :
    (sInf s).toSublocale = sInf (Closed.toSublocale '' s) := by
  ext x
  simp only [Closed.sInf_def, Closed.toSublocale_apply, Sublocale.sInf_apply]
  apply le_antisymm
  · rw [le_iInf_iff]
    intro j
    rw [le_iInf_iff]
    intro hj
    change ∀ t ∈ Closed.toSublocale '' s, j ≤ t at hj
    apply sup_le
    · apply sSup_le
      rintro _ ⟨c, hc, rfl⟩
      have h := hj (c.toSublocale) (Set.mem_image_of_mem Closed.toSublocale hc)
      exact le_trans le_sup_left <| by
        simpa only [Closed.toSublocale_apply] using
          (Sublocale.le_iff j c.toSublocale).mp h x
    · exact j.toNucleus.le_apply
  · rw [iInf_le_iff]
    intro b h
    have hlow : (sInf s).toSublocale ∈ lowerBounds (Closed.toSublocale '' s) := by
      intro j hj
      rcases hj with ⟨c, hc, rfl⟩
      rw [Sublocale.le_iff]
      intro i
      simpa only [Closed.sInf_def, Closed.toSublocale_apply] using
        (sup_le_sup_right (le_sSup (Set.mem_image_of_mem Closed.element hc)) i)
    have h1 := h (sInf s).toSublocale
    have h2 : b ≤ (sInf s).toSublocale x := by simpa [hlow] using h1
    simpa only [Closed.sInf_def, Closed.toSublocale_apply] using h2

/-- Closed elements form a semilattice with meets given by joins of the underlying elements
(reversed order). -/
instance : SemilatticeInf (Closed E) where
  le_refl x := by rfl
  le_trans x y z h1 h2  := Preorder.le_trans z.element y.element x.element h2 h1
  le_antisymm x y h1 h2 := by ext; exact le_antisymm h2 h1
  inf x y := ⟨x.element ⊔ y.element⟩
  inf_le_left x y := by simp [le_def]
  inf_le_right x y := by simp [le_def]
  le_inf x y z h1 h2 := by simpa [le_def] using ⟨h1, h2⟩

/-- Closed elements admit greatest lower bounds, computed elementwise as suprema. -/
instance : CompleteSemilatticeInf (Closed E) where
  isGLB_sInf s := by
    refine ⟨?_, ?_⟩
    · intro c hc
      change c.element ≤ sSup (Closed.element '' s)
      exact le_sSup (Set.mem_image_of_mem Closed.element hc)
    · intro c hc
      change sSup (Closed.element '' s) ≤ c.element
      change ∀ d ∈ s, c ≤ d at hc
      apply sSup_le
      rintro x ⟨d, hd, rfl⟩
      exact hc d hd

/-- Binary meets of closed elements are joins of the underlying elements (reversed order). -/
theorem inf_def (x y : Closed E) : x ⊓ y = ⟨x.element ⊔ y.element⟩ := rfl

/-- Meets of closed sublocales are sent to meets of sublocales: the embedding preserves
binary meets. -/
theorem preserves_inf (x y : Closed E) :
    (x ⊓ y).toSublocale = x.toSublocale ⊓ y.toSublocale := by
  calc
    (x ⊓ y).toSublocale = (sInf ({x, y} : Set (Closed E))).toSublocale := by
      rw [sInf_pair]
    _ = sInf (Closed.toSublocale '' {x, y}) := preserves_sInf _
    _ = x.toSublocale ⊓ y.toSublocale := by
      rw [Set.image_pair, sInf_pair]

end Closed

/-- The closed element underlying an open's complement. -/
def Open.compl (U : Open E) : Closed E := ⟨U.element⟩

/-- The complement of an open has the same underlying element. -/
@[simp] lemma Open.compl_element (U : Open E) : U.compl.element = U.element := by
  rfl

/-- An open sublocale and its closed complement only meet in the bottom sublocale. -/
lemma Open.inf_compl_eq_bot (U : Open E) : U.toSublocale ⊓ U.compl = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Sublocale.le_iff]
  simp only [Sublocale.bot_apply, Open.toSublocale, Closed.toSublocale, Open.complNucleus, compl,
    Sublocale.inf_apply, lowerBounds_insert, lowerBounds_singleton, Set.Iic_inter_Iic, Set.mem_Iic,
    le_inf_iff, Sublocale.le_iff, le_iInf_iff, top_le_iff, and_imp, Nucleus.toSublocale_apply,
    Open.toNucleus]
  intro i a h1 h2
  have h3 : U.element ≤ a i := le_trans le_sup_left (h2 i)
  have h4 : ⊤ ≤ U.element ⇨ a i := by
    rw [le_himp_iff]
    simpa using h3
  apply le_antisymm le_top
  calc
    ⊤ ≤ U.element ⇨ a i := h4
    _ ≤ a (a i) := h1 (a i)
    _ = a i := a.toNucleus.idempotent i

/-- An open sublocale and its closed complement jointly cover the whole frame of sublocales. -/
lemma Open.sup_compl_eq_top (U : Open E) : U.toSublocale ⊔ U.compl = ⊤ := by
  refine le_antisymm le_top ?_
  rw [Sublocale.le_iff]
  simp only [Open.toSublocale, Closed.toSublocale, Open.complNucleus, compl_element,
    Sublocale.sup_apply, Sublocale.top_apply, Nucleus.toSublocale_apply, Open.toNucleus]
  intro i
  change (U.element ⇨ i) ⊓ (U.element ⊔ i) ≤ i
  rw [himp_eq_sSup, sSup_inf_eq]
  simp only [Set.mem_ofPred_eq, iSup_le_iff]
  intro j h
  rw [inf_sup_left]
  simp only [sup_le_iff, inf_le_right, and_true]
  exact h

/-- Complementation of opens is antitone. -/
lemma Open.compl_le_compl (U V : Open E) (h : U ≤ V) : V.compl ≤ U.compl := by
  exact h

/-- Complementation of closed sublocales is antitone. -/
lemma Closed.compl_le_compl (c d : Closed E) (h : c ≤ d) : d.compl ≤ c.compl := by
  exact h

/-- An open contained in a closed sublocale has its closed complement contained in the open's
complement: complements reverse inclusions across open/closed types. -/
lemma Closed.compl_le_Open_compl (U : Open E) (c : Closed E) (h : U.toSublocale ≤ c.toSublocale) :
    c.compl.toSublocale ≤ U.compl.toSublocale := by
  rw [Sublocale.le_iff] at h ⊢
  simp only [Closed.compl, Open.compl, Closed.toSublocale_apply, Open.toSublocale_apply] at h ⊢
  intro i
  rw [le_himp_iff, inf_sup_right]
  have h₁ : U.element ⊓ c.element ≤ i := by
    have h₂ : c.element ≤ U.element ⇨ i := le_trans le_sup_left (h i)
    simpa [inf_comm] using (le_himp_iff.mp h₂)
  exact sup_le h₁ inf_le_left
