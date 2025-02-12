import Leroy.Nucleus

variable {E : Type*} [Order.Frame E]


abbrev Sublocale (E : Type*) [Order.Frame E] := (Nucleus E)ᵒᵈ

open Nucleus

instance : FunLike (Sublocale E) E E where
  coe x := x.toFun
  coe_injective' f g h := (by cases f;cases g; simp_all)

lemma Sublocale.le_iff (u v : Sublocale E): u ≤ v ↔ ∀ i, v i ≤ u i := by exact Eq.to_iff rfl

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

lemma Sublocale.min_apply (u v : Sublocale E) (x : E) : (u ⊓ v) x = ⨅ j ∈ lowerBounds {u, v}, j x := by
  simp only [OrderDual.instInf, Set.Ici_inter_Ici,Set.mem_Ici, sup_le_iff]
  rw [Nucleus.sup_apply]
  simp only [upperBounds_insert, upperBounds_singleton, Set.Ici_inter_Ici, Set.mem_Ici, sup_le_iff,
    lowerBounds_insert, lowerBounds_singleton, Set.Iic_inter_Iic, Set.mem_Iic, le_inf_iff]
  exact rfl


@[ext]
structure Open (E : Type*) [Order.Frame E] where
  element : E

namespace Open

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

lemma le_def (x y : Open E): x ≤ y ↔ x.element ≤ y.element := by rfl

instance : PartialOrder (Open E) where
  le_refl a := by rfl
  le_trans a b c h1 h2 := by exact Preorder.le_trans a.element b.element c.element h1 h2
  le_antisymm a b h1 h2 := by ext; exact le_antisymm h1 h2

instance : CompleteSemilatticeSup (Open E) where
  sSup s := ⟨sSup (Open.element '' s)⟩
  le_sSup s x h := by
    simp [LE.le]
    apply le_sSup (Set.mem_image_of_mem element h)
  sSup_le s x h := by simpa [LE.le] using h

lemma sSup_def (s : Set (Open E)) : sSup s = ⟨sSup (Open.element '' s)⟩ := rfl

instance : SemilatticeInf (Open E) where
  inf x y := ⟨x ⊓ y⟩
  inf_le_left x y := by simp [le_def]
  inf_le_right x y := by simp [le_def]
  le_inf x y z h1 h2 := by simp [le_def]; exact ⟨h1, h2⟩

lemma inf_def (u v : Open E) : u ⊓ v = ⟨u ⊓ v⟩ := rfl

@[simp] lemma toSublocale_apply (U : Open E) (x : E) : U.toSublocale x = U.element ⇨ x := rfl

@[simp] lemma apply_self (U : Open E) : U.toSublocale U.element = ⊤ := by simp

lemma le_iff (U V : Open E) : U ≤ V ↔ U.toSublocale ≤ V := by
  apply Iff.intro
  . simp only [Sublocale.le_iff, toSublocale_apply]
    intro h i
    exact himp_le_himp_right h
  . simp only [Sublocale.le_iff, toSublocale_apply]
    intro h
    let h1 := h V
    simp only [himp_self, le_himp_iff, le_top, inf_of_le_right] at h1
    exact h1

lemma preserves_inf (U V : Open E) : (U ⊓ V).toSublocale = U.toSublocale ⊓ V.toSublocale := by
  ext x
  simp [inf_def, Sublocale.min_apply]
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
    calc
      _ = ⨅ j ∈ (Open.toSublocale '' s), j x  := by simp

    end





def complement (U :Open E) : Sublocale E where
  toFun x := U ⊔ x
  map_inf' x y := by simp; exact sup_inf_left U.element x y
  idempotent' x := by simp
  le_apply' x := by simp

end Open

@[ext]
structure Closed (E : Type*) [Order.Frame E] where
  element : E

namespace Closed

protected def toSublocale (c : Closed E) : Sublocale E := Open.complement ⟨c.element⟩

instance : Coe (Closed E) (Sublocale E) where
  coe x := x.toSublocale
