import Leroy.Basic

open CategoryTheory

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

class Nucleus (e : O X ⥤ O X) where
  idempotent (x : O X) : e.obj (e.obj x) = x
  increasing (x : O X) : x ⟶ e.obj x
  preserves_inf (x y : O X) : e.obj (x ⊓ y) = e.obj x ⊓ e.obj y

structure Subframe (X : Type*) [TopologicalSpace X] where
  func : O X ⥤ O X
  nucleus : Nucleus func

-- Leroy CH 3
instance : LE (Subframe X) where
  le x y := ∀ v : O X, y.func.obj v ≤ x.func.obj v

def Image (s : Subframe X) : Set (O X) :=
  {v : O X | s.func.obj v = v}


-- können wir Embedding einfach verwenden?
