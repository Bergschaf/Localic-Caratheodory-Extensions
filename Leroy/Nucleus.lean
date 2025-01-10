/-
Copyright (c) 2024 Christian Krause. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chriara Cimino, Christian Krause
-/
import Mathlib.Order.CompleteLattice
import Mathlib.Order.CompleteSublattice
import Mathlib.Tactic.ApplyFun

/-!
# Nucleus
Locales are the dual concept to Frames.
A Nucleus is a function between Frames which corresponds to a sublocale.
https://ncatlab.org/nlab/show/nucleus
-/
variable {X : Type*} [CompleteLattice X]

/--
The Type of Nuclei on a Frame.
-/
structure Nucleus (X : Type*) [SemilatticeInf X] where
  /-- The function of the nucleus.-/
  toFun : X → X
  /-- A Nucleus is idempotent.-/
  idempotent (x : X) : toFun (toFun x) ≤ toFun x
  /-- A Nucleus is increasing.-/
  increasing (x : X) : x ≤ toFun x
  /-- A Nucleus preserves infima.-/
  preserves_inf (x y : X) : toFun (x ⊓ y) = toFun x ⊓ toFun y

def bot : Nucleus X where
  toFun := fun x ↦ x
  idempotent x := (by rfl)
  increasing x := (by rfl)
  preserves_inf x y := (by rfl)

/--
A stronger version of Nucleus.idempotent which follows from Nucleus.increasing.
-/
lemma Nucleus.idempotent' {n : Nucleus X} {x : X} : n.toFun (n.toFun x) = n.toFun x := by
  apply le_antisymm
  · exact n.idempotent x
  · exact n.increasing (n.toFun x)

instance : FunLike (Nucleus X) X X where
  coe := Nucleus.toFun
  coe_injective' f g h := by cases f; cases g; congr

/--
`NucleusClass F X` states that F is a type of Nuclei.
-/
class NucleusClass (F X : Type*) [SemilatticeInf X] [FunLike F X X] : Prop where
  /-- A Nucleus is idempotent.-/
  idempotent (x : X) (f : F) : f (f x) ≤ f x
  /-- A Nucleus is increasing.-/
  increasing (x : X) (f : F) : x ≤ f x
  /-- A Nucleus preserves infima.-/
  preserves_inf (x y : X) (f : F) : f (x ⊓ y) = f x ⊓ f y


instance (F X : Type*) [SemilatticeInf X] [FunLike F X X] [n : NucleusClass F X]
  : OrderHomClass F X X where
  map_rel := fun f a b h => by
    have h1 : a ⊓ b = a := inf_eq_left.mpr h
    have h2 := n.preserves_inf a b
    rw [h1] at h2
    exact left_eq_inf.mp (h2 f)

lemma Nucleus.coe_eq_toFun (n : Nucleus X) {x : X} : n x = n.toFun x := by rfl


instance : NucleusClass (Nucleus X) X where
  idempotent := (by simp[Nucleus.coe_eq_toFun];exact fun x f ↦ f.idempotent x)
  increasing := (by simp[Nucleus.coe_eq_toFun];exact fun x f ↦ f.increasing x)
  preserves_inf := (by simp[Nucleus.coe_eq_toFun]; exact fun x y f ↦ f.preserves_inf x y)


/--
We can proove that two Nuclei are equal by showing that their functions are the same.
-/
@[ext]
lemma Nucleus.ext {n m : Nucleus X} (h: ∀ a, n.toFun a = m.toFun a) : n = m :=
  DFunLike.ext n m h



/--
A Nucleus preserves ⊤
-/
lemma nucleus_preserves_top (n : Nucleus X) : n.toFun ⊤ = ⊤ :=
   top_le_iff.mp (n.increasing ⊤)


instance Nucleus.le : LE (Nucleus X) where
  le x y := ∀ v : X, x.toFun v ≤ y.toFun v

lemma Nucleus.le_iff {n m : Nucleus X} : m ≤ n ↔ ∀ v : X, m.toFun v ≤ n.toFun v := by rfl

instance : Preorder (Nucleus X) where
  le_refl := (by simp only [Nucleus.le_iff, le_refl, implies_true])
  le_trans := (by simp only [Nucleus.le_iff]; exact fun a b c a_1 a_2 v ↦
    Preorder.le_trans (a.toFun v) (b.toFun v) (c.toFun v) (a_1 v) (a_2 v))

/--
The smallest Nucleus is the identity Nucleus.
-/
instance Nucleus.bot : Bot (Nucleus X) where
  bot := ⟨fun x ↦ x, Preorder.le_refl,Preorder.le_refl, fun _ _ ↦ rfl⟩

instance : OrderBot (Nucleus X) where
  bot_le := (by simp only [Nucleus.bot];exact fun a v ↦ a.increasing v)

/--
The biggest Nucleus sends everything to ⊤.
-/
instance Nucleus.top : Top (Nucleus X) where
  top := ⟨fun _ ↦ ⊤,(by simp only [le_refl, implies_true]), OrderTop.le_top,
    fun _ _ ↦ Eq.symm (top_inf_eq _)⟩
-- Question for the reviewer: Should these small proofs be simp's or written out statements?

instance : OrderTop (Nucleus X) where
  le_top := (by simp only [Nucleus.top, Nucleus.le_iff, le_top, implies_true])

@[simp]
lemma Nucleus.fun_of {tf : X → X} {h1 : ∀ (x : X), tf (tf x) ≤ tf x} {h2 : ∀ (x : X), x ≤ tf x} {h3 : ∀ (x y : X), tf (x ⊓ y) = tf x ⊓ tf y} {v : X} : ({toFun := tf, idempotent := h1, increasing := h2, preserves_inf := h3} : Nucleus X) v = tf v := by rfl

@[simp]
lemma Nucleus.toFun_eq_coe (n : Nucleus X) : n.toFun = n := rfl

lemma Nucleus.idempotent'' (n : Nucleus X) {x : X} : n (n x) = n x := by
  rw [← n.toFun_eq_coe]
  exact n.idempotent'

lemma Nucleus.increasing' (n : Nucleus X) {x : X} : x ≤ n x := by
  rw [← n.toFun_eq_coe]
  exact n.increasing x

lemma Nucleus.preserves_inf' (n : Nucleus X) {x y : X} : n (x ⊓ y) = n x ⊓ n y := by
  rw [← n.toFun_eq_coe]
  exact n.preserves_inf x y


/--
A Nucleus is montone
-/
lemma Nucleus.monotone (n : Nucleus X) : Monotone n := by
  rw [Monotone]
  intro a b h
  have h1 : a ⊓ b = a := inf_eq_left.mpr h
  have h2 := n.preserves_inf a b
  rw [h1] at h2
  exact left_eq_inf.mp h2

variable {X Y E: Type u} [Order.Frame X] [Order.Frame Y] [Order.Frame E]

def sInf_fun (s : Set (Nucleus X)) (a : X) := sInf {j a | j ∈ s}

def sInf_fun_increasing :  ∀ (x : E), x ≤ sInf_fun s x := by
  intro x
  simp [sInf_fun]
  exact fun a a_1 => Nucleus.increasing' a

def sInf_fun_idempotent : ∀ (x : E), sInf_fun s (sInf_fun s x) ≤ sInf_fun s x := by
  intro x
  simp only [sInf_fun, le_sInf_iff, Set.mem_setOf_eq, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro a ha
  apply sInf_le_iff.mpr
  simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro b h
  rw [← Nucleus.idempotent'']
  apply le_trans (h a ha)
  apply Nucleus.monotone
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
