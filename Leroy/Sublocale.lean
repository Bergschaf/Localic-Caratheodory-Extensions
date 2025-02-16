import Leroy.Nucleus
import Mathlib.Tactic.Widget.Conv
import Mathlib.Tactic.ApplyFun
variable {E : Type*} [Order.Frame E]


abbrev Sublocale (E : Type*) [Order.Frame E] := (Nucleus E)ᵒᵈ

open Nucleus

instance : FunLike (Sublocale E) E E where
  coe x := x.toFun
  coe_injective' f g h := (by cases f;cases g; simp_all)

lemma Sublocale.le_iff (u v : Sublocale E) : u ≤ v ↔ ∀ i, v i ≤ u i := by exact Eq.to_iff rfl

@[ext]
lemma ext (a b : Sublocale E) (h : ∀ x, a x = b x) : a = b := by
  exact Nucleus.ext h

@[simp] lemma Sublocale.sSup_apply (s : Set (Sublocale E)) (x : E) : sSup s x = ⨅ j ∈ s, j x := by
  simp [OrderDual.supSet]
  exact rfl

@[simp] lemma Sublocale.iSup_apply {ι : Type*} (f : ι → Sublocale E) (x : E) : iSup f x = ⨅ j, f j x := by
  simp only [iSup, sSup_apply, Set.mem_range, iInf_exists]
  refine le_antisymm ?_ (by simp; exact fun a => iInf_le (fun j => (f j) x) a)
  simp only [le_iInf_iff, iInf_le_iff, forall_apply_eq_imp_iff]
  exact fun i b a => a i

@[simp] lemma Sublocale.sup_apply (u v : Sublocale E) (x : E) : (u ⊔ v) x = u x ⊓ v x := by
  simp [OrderDual.instSup]
  rw [Nucleus.inf_apply]

@[simp] lemma Sublocale.inf_apply (u v : Sublocale E) (x : E) : (u ⊓ v) x = ⨅ j ∈ lowerBounds {u, v}, j x := by
  simp only [OrderDual.instInf, Set.Ici_inter_Ici,Set.mem_Ici, sup_le_iff]
  rw [Nucleus.sup_apply]
  simp only [upperBounds_insert, upperBounds_singleton, Set.Ici_inter_Ici, Set.mem_Ici, sup_le_iff,
    lowerBounds_insert, lowerBounds_singleton, Set.Iic_inter_Iic, Set.mem_Iic, le_inf_iff]
  exact rfl


@[simp] lemma Sublocale.top_apply (x : E) : (⊤ : Sublocale E) x = x := rfl
@[simp] lemma Sublocale.bot_apply (x : E) : (⊥ : Sublocale E) x = ⊤ := rfl

@[ext]
structure Open (E : Type*) [Order.Frame E] where
  element : E

namespace Open

variable {U V : Open E}

protected def toSublocale (U : Open E) : Sublocale E where
  toFun x := U.element ⇨ x
  map_inf' x y := himp_inf_distrib U.element x y
  idempotent' x := by simp
  le_apply' x := by simp


instance : Coe (Open E) E where
  coe x := x.element

instance : Coe (Open E) (Sublocale E) where
  coe x := x.toSublocale

instance : LE (Open E) where
  le x y := x.element ≤ y.element


instance : PartialOrder (Open E) where
  le_refl a := by rfl
  le_trans a b c h1 h2 := by exact Preorder.le_trans a.element b.element c.element h1 h2
  le_antisymm a b h1 h2 := by ext; exact le_antisymm h1 h2

lemma le_def : U ≤ V ↔ U.element ≤ V.element := by rfl
lemma lt_def : U < V ↔ U.element < V.element := lt_iff_lt_of_le_iff_le' le_def le_def


instance instBoundedOrder : BoundedOrder (Open E) where
  top := ⟨⊤⟩
  le_top x := OrderTop.le_top x.element
  bot := ⟨⊥⟩
  bot_le x := OrderBot.bot_le x.element

@[simp] lemma top_element : (⊤ : Open E).element = ⊤ := rfl
@[simp] lemma bot_element : (⊥ : Open E).element = ⊥ := rfl
@[simp] lemma top_toSublocale : (⊤ : Open E).toSublocale = ⊤ := by
  ext x
  simp only [Open.toSublocale, top_element, top_himp, Sublocale.top_apply]
  exact rfl
@[simp] lemma bot_toSublocale : (⊥ : Open E).toSublocale = ⊥ := by
  ext x
  simp only [Open.toSublocale, bot_element, bot_himp, Sublocale.bot_apply]
  exact rfl

instance instCompleteSemilatticeSup : CompleteSemilatticeSup (Open E) where
  sSup s := ⟨sSup (Open.element '' s)⟩
  le_sSup s x h := by
    simp [LE.le]
    apply le_sSup (Set.mem_image_of_mem element h)
  sSup_le s x h := by simpa [LE.le] using h

lemma sSup_def (s : Set (Open E)) : sSup s = ⟨sSup (Open.element '' s)⟩ := rfl


instance instSemilatticeInf : SemilatticeInf (Open E) where
  inf x y := ⟨x ⊓ y⟩
  inf_le_left x y := by simp [le_def]
  inf_le_right x y := by simp [le_def]
  le_inf x y z h1 h2 := by simp [le_def]; exact ⟨h1, h2⟩

instance : CompleteLattice (Open E) where
  __ := instBoundedOrder
  __ := instSemilatticeInf
  __ := completeLatticeOfCompleteSemilatticeSup (Open E)


lemma sup_def (u v : Open E) : u ⊔ v = ⟨u.element ⊔ v.element⟩ := by
  rw [← sSup_pair, sSup_def, Set.image_pair, sSup_pair]

lemma inf_def (u v : Open E) : u ⊓ v = ⟨u ⊓ v⟩ := rfl

@[simp] lemma toSublocale_apply (U : Open E) (x : E) : U.toSublocale x = U.element ⇨ x := rfl

@[simp] lemma apply_self (U : Open E) : U.toSublocale U.element = ⊤ := by simp

lemma le_iff : U ≤ V ↔ U.toSublocale ≤ V.toSublocale := by
  apply Iff.intro
  . simp only [Sublocale.le_iff, toSublocale_apply]
    intro h i
    exact himp_le_himp_right h
  . simp only [Sublocale.le_iff, toSublocale_apply]
    intro h
    let h1 := h V
    simp only [himp_self, le_himp_iff, le_top, inf_of_le_right] at h1
    exact h1


lemma toSublocale_injective : Function.Injective (@Open.toSublocale E _) := by
  rw [Function.Injective]
  intro a1 a2 h
  apply le_antisymm
  . exact le_iff.mpr (le_of_eq h)
  . exact le_iff.mpr (ge_of_eq h)

lemma eq_iff : U = V ↔ U.toSublocale = V.toSublocale := by
  apply Iff.intro
  . exact fun a => congrArg Open.toSublocale a
  . intro h
    apply_fun (fun x ↦ x.toSublocale)
    exact h
    exact toSublocale_injective

lemma preserves_inf (U V : Open E) : (U ⊓ V).toSublocale = U.toSublocale ⊓ V.toSublocale := by
  ext x
  simp [inf_def, Sublocale.inf_apply]
  apply le_antisymm
  . sorry
  . sorry

lemma preserves_sSup (s : Set (Open E)) : (sSup s).toSublocale = sSup (Open.toSublocale '' s) := by
  ext x
  simp [sSup_def]
  apply le_antisymm
  . simp only [le_iInf_iff, and_imp, forall_apply_eq_imp_iff₂, toSublocale_apply, le_himp_iff]
    intro a h
    rw [@sSup_image]
    simp [himp_eq_sSup]
    rw [sSup_inf_eq]
    simp [iInf_le_iff]
    intro i h1
    apply le_trans' h1
    simp only [le_inf_iff, inf_le_left, true_and]
    apply inf_le_of_right_le
    exact le_biSup element h
  .
    have h : ⨅ j, ⨅ i, ⨅ (_ : i ∈ s ∧ i.toSublocale = j), j x = ⨅ j ∈ (Open.toSublocale '' s), j x  := by simp
    rw [h]
    sorry

lemma preserves_sup : (U ⊔ V).toSublocale = U.toSublocale ⊔ V.toSublocale := by
  rw [← sSup_pair, preserves_sSup, Set.image_pair, sSup_pair]


end Open

def complement (U : Open E) : Sublocale E where
  toFun x := U ⊔ x
  map_inf' x y := by simp; exact sup_inf_left U.element x y
  idempotent' x := by simp
  le_apply' x := by simp

@[ext]
structure Closed (E : Type*) [Order.Frame E] where
  element : E

namespace Closed

protected def toSublocale (c : Closed E) : Sublocale E := complement ⟨c.element⟩

lemma toSublocale_apply (c : Closed E) (x : E) : c.toSublocale x = c.element ⊔ x := by rfl

instance : Coe (Closed E) (Sublocale E) where
  coe x := x.toSublocale

instance : LE (Closed E) where
  le x y := y.element ≤ x.element

lemma le_def (x y : Closed E) : x ≤ y ↔ y.element ≤ x.element := by rfl

lemma le_iff (x y : Closed E) : x ≤ y ↔ x.toSublocale ≤ y.toSublocale := by
  simp [le_def, Closed.toSublocale, complement, LE.le]
  apply Iff.intro
  . exact fun h i => le_sup_of_le_left h
  . intro h
    let h1 := h ⊥
    simp only [bot_le, sup_of_le_left] at h1
    exact h1

def compl (c : Closed E) : Open E := ⟨c.element⟩

@[simp] lemma element_compl (c : Closed E) : c.compl.element = (⟨c.element⟩ : Open E) := by
  rfl

instance instInfSet : InfSet (Closed E) where
  sInf x := ⟨sSup (Closed.element '' x)⟩

lemma sInf_def (s : Set (Closed E)) : sInf s = ⟨sSup (Closed.element '' s)⟩ := by rfl

lemma preserves_sInf (s : Set (Closed E)) : (sInf s).toSublocale = sInf (Closed.toSublocale '' s) := by
  ext x
  simp only [Closed.toSublocale, complement, sInf]
  rw [Nucleus.coe_mk,InfHom.coe_mk] -- why no simp??
  rw [Nucleus.sSup_apply]
  simp only [upperBounds, Set.mem_image, LE.le, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, coe_mk, InfHom.coe_mk, sup_le_iff, Set.mem_setOf_eq]
  sorry

instance : CompleteSemilatticeInf (Closed E) where
  __ := instInfSet
  le_refl x := by rfl
  le_trans x y z h1 h2  := Preorder.le_trans z.element y.element x.element h2 h1
  le_antisymm x y h1 h2 := by ext; exact le_antisymm h2 h1
  sInf_le s a h := by
    simp [sInf_def, le_def, sSup_image]
    exact le_biSup element h
  le_sInf s a h := by
    simp [sInf_def, le_def]
    exact h

instance : SemilatticeInf (Closed E) where
  inf x y := ⟨x.element ⊔ y.element⟩
  inf_le_left x y := by simp [le_def]
  inf_le_right x y := by simp [le_def]
  le_inf x y z h1 h2 := by simp [le_def]; exact ⟨h1, h2⟩

def inf_def (x y : Closed E) : x ⊓ y = ⟨x.element ⊔ y.element⟩ := rfl

def preserves_inf (x y : Closed E) : (x ⊓ y).toSublocale = x.toSublocale ⊓ y.toSublocale := by
  rw [← sInf_pair]
  rw [← Set.image_pair]
  rw [← preserves_sInf]
  rw [@sInf_def, inf_def, Set.image_pair, sSup_pair]

end Closed

def Open.compl (U : Open E) : Closed E := ⟨U.element⟩

@[simp] lemma Open.compl_element (U : Open E) : U.compl.element = U.element := by
  rfl

lemma Open.inf_compl_eq_bot (U : Open E) : U.toSublocale ⊓ U.compl = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [Sublocale.le_iff]
  sorry

lemma Open.sup_compl_eq_top (U : Open E) : U.toSublocale ⊔ U.compl = ⊤ := by
  sorry
