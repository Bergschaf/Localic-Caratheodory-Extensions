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
  intro x
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
      apply le_trans (h a h1)
      apply Nucleus.monotone
      exact inf_le_left
    . intro a h1
      apply le_trans (h a h1)
      apply Nucleus.monotone
      exact inf_le_right
  . apply le_sInf_iff.mpr
    simp only [Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro a ha
    rw [Nucleus.preserves_inf']
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
  sInf s := ⟨sInf_fun s, sInf_fun_idempotent, sInf_fun_increasing, sInf_preserves_inf⟩

lemma Nucleus_le_sInf : ∀ (s : Set (Nucleus E)) (a : Nucleus E), (∀ b ∈ s, a ≤ b) → a ≤ sInf s := by
  intro s a h
  simp only [sInf,Nucleus.le_iff, Nucleus.toFun_eq_coe, sInf_fun, le_sInf_iff, Set.mem_setOf_eq,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact fun v a a_1 => h a a_1 v


lemma Nucleus_sInf_le :  ∀ (s : Set (Nucleus E)), ∀ a ∈ s, sInf s ≤ a := by
  intro s a h
  simp only [sInf, Nucleus.le_iff, sInf_fun, Nucleus.toFun_eq_coe]
  intro v
  apply sInf_le
  simp only [Set.mem_setOf_eq]
  use a


instance {α : Type*} [CompleteSemilatticeInf α] : CompleteSemilatticeSup αᵒᵈ where
  le_sSup := @CompleteSemilatticeInf.sInf_le α _
  sSup_le := @CompleteSemilatticeInf.le_sInf α _


instance Nucleus.instCompleteSemilatticeInf : CompleteSemilatticeInf (Nucleus E) where
  le_antisymm a b h1 h2 := (by ext x; simp only [Nucleus.le_iff, Nucleus.toFun_eq_coe] at *; apply le_antisymm;exact h1 x;exact h2 x)
  sInf_le := Nucleus_sInf_le
  le_sInf := Nucleus_le_sInf
