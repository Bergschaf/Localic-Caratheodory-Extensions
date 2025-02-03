/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.Nucleus

open Nucleus

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]

def sInf_fun (s : Set (Nucleus X)) (a : X) := sInf {j a | j ∈ s}

def sInf_fun_increasing :  ∀ (x : E), x ≤ sInf_fun s x := by
  simp [sInf_fun, le_apply]

def sInf_fun_idempotent : ∀ (x : E), sInf_fun s (sInf_fun s x) ≤ sInf_fun s x := by
  intro x
  simp only [sInf_fun, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro a ha
  apply sInf_le_iff.mpr
  simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro b h
  rw [← idempotent]
  apply le_trans (h a ha)
  refine OrderHomClass.GCongr.mono a ?_
  apply sInf_le_iff.mpr
  simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun b a_1 => a_1 a ha


def sInf_preserves_inf : ∀ (x y : E), sInf_fun s (x ⊓ y) = sInf_fun s x ⊓ sInf_fun s y := by
  simp [sInf_fun]
  intro x y
  apply le_antisymm
  . apply sInf_le_iff.mpr
    simp [lowerBounds]
    intro b h
    apply And.intro
    . intro a h1
      simp_all only
    . intro a h1
      simp_all only
  . apply le_sInf_iff.mpr
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a ha
    refine inf_le_inf ?_ ?_
    . apply sInf_le_iff.mpr
      simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact fun b a_1 => a_1 a ha
    . apply sInf_le_iff.mpr
      simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      exact fun b a_1 => a_1 a ha

/--
Quelle Stonespaces S.51
-/
instance : InfSet (Nucleus E) where
  sInf s := ⟨⟨sInf_fun s, sInf_preserves_inf⟩, sInf_fun_idempotent, sInf_fun_increasing⟩

@[simp]
lemma sInf_coe (s : Set (Nucleus E)) : ∀ x : E, (sInf s) x = sInf_fun s x := by
  exact fun x => rfl

lemma _le_sInf : ∀ (s : Set (Nucleus E)) (a : Nucleus E), (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
  intro s a h
  simp [LE.le, sInf_fun]
  exact fun i a a_1 => h a a_1 i

lemma _sInf_le :  ∀ (s : Set (Nucleus E)), ∀ a ∈ s, sInf s ≤ a := by
  intro s a h
  simp [LE.le, sInf_fun]
  intro v
  apply sInf_le
  simp only [Set.mem_setOf_eq]
  use a

instance Nucleus.instCompleteSemilatticeInf : CompleteSemilatticeInf (Nucleus E) where
  le_antisymm a b h1 h2 := (by ext x; apply le_antisymm;exact h1 x;exact h2 x)
  sInf_le := _sInf_le
  le_sInf := _le_sInf
