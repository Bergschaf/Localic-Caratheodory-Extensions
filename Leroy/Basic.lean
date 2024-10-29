import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.CategoryTheory.Limits.Creates
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Topology.Defs.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Sets.Opens
import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Topology.ContinuousMap.Defs


open CategoryTheory

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
--- Geschweifte klammern sind wichtig


abbrev O := TopologicalSpace.Opens

def comap (f : C(X, Y)) := TopologicalSpace.Opens.comap f

lemma map_map_inf (f: C(X, Y)) :  (fun x => sSup {y | (comap f) y ≤ x}) (a ⊓ b) =
  (fun x => sSup {y | (comap f) y ≤ x}) a ⊓ (fun x => sSup {y | (comap f) y ≤ x}) b := by
  simp
  ext x1
  apply Iff.intro
  simp
  intro x2 h1 h2 h3
  apply And.intro
  . use x2
  . use x2
  simp
  intro x2 h1 h2 x3 h3 h4
  use (sSup {y | (comap f) y ≤ a} ⊓ sSup {y | (comap f) y ≤ b})
  apply And.intro
  . apply And.intro
    . simp  [inf_le_of_left_le]
    . simp [inf_le_of_right_le]
  . rw [@sSup_inf_sSup]
    simp
    use x2
    apply And.intro
    . exact h2
    . use x3

lemma map_map_sSup (f  : C(X, Y)) : sSup {y | (comap f) y ≤ sSup s} = sSup ((fun a => sSup {y | (comap f) y ≤ a}) '' s) := by
  apply TopologicalSpace.Opens.ext
  simp
  refine Set.eq_of_forall_subset_iff ?h.h
  simp
  intro x
  apply Iff.intro
  . intro h1 h2 h3 x2 h4
    apply h1
    have h5 : h2 ≤ sSup s:= by
      exact CompleteLattice.le_sSup s h2 h3
    exact fun ⦃a⦄ a_1 => h5 (h4 a_1)
  . intro h x1 h2


    sorry

    /--
    apply h (sSup s) _ x1
    exact h2
    rw?-/




def map (f : C(X, Y)) : FrameHom (O X) (O Y) where
  toFun x := sSup {y : O Y | comap f y ≤ x}
  map_inf' a b := map_map_inf f
  map_top' := (by simp)
  map_sSup' s :=  (by simp_all; exact map_map_sSup f)


theorem map_mono (f : C(X,Y)) {s t : O X} (h : s ≤ t) : map f s ≤ map f t :=
  OrderHomClass.mono (map f) h


def f_obenstern (f : C(X, Y)) : O Y ⥤ O X where
  obj := TopologicalSpace.Opens.comap f
  map := (by intro x y; intro h; apply homOfLE; apply TopologicalSpace.Opens.comap_mono; exact leOfHom h)

/--def f_untenstern (f : C(X, Y)) : O X ⥤ O Y where
  obj :=  (map f)
  map := (by intro x y h; apply homOfLE; apply map_mono; exact leOfHom h)
-/

def f_untenstern_map (f: C(X,Y)) : {X_1 Y_1 : O X} → (X_1 ⟶ Y_1) → ((fun x => sSup {y | (comap f) y ≤ x}) X_1 ⟶ (fun x => sSup {y | (comap f) y ≤ x}) Y_1) := by
  intro x1 x2 h
  simp
  apply homOfLE
  simp_all
  intro y h1
  intro a a_1
  simp_all only [SetLike.mem_coe, TopologicalSpace.Opens.coe_sSup, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  use y
  apply And.intro
  . rcases h with ⟨h2⟩
    apply PLift.down at h2
    apply le_trans h1 h2
  . exact a_1


def f_untenstern (f: C(X, Y)) : O X ⥤ O Y where
  obj x := sSup {y : O Y | comap f y ≤ x}
  map := f_untenstern_map f

def f_unit (f : C(X ,Y)) : PLift ((𝟭 (O Y)).obj x ≤ (f_obenstern f ⋙ f_untenstern f).obj x) := by
  simp
  refine { down := ?down }
  rw [f_untenstern, f_obenstern]
  simp [map, TopologicalSpace.Opens.comap, comap]
  intro a a_1
  simp_all only [SetLike.mem_coe, TopologicalSpace.Opens.coe_sSup, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  apply Exists.intro
  · apply And.intro
    intro a_2 a_3
    on_goal 2 => {exact a_1
    }
    simp_all only [TopologicalSpace.Opens.coe_mk, Set.mem_preimage, SetLike.mem_coe]

def f_counit (f: C(X, Y)) : PLift ((f_untenstern f ⋙ f_obenstern f).obj x ≤ (𝟭 (O X)).obj x) := by
  simp
  apply PLift.up
  simp [f_obenstern,f_untenstern, map, TopologicalSpace.Opens.comap, comap]
  intro a a_1
  simp_all only [TopologicalSpace.Opens.coe_mk, Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
  obtain ⟨w, h⟩ := a_1
  obtain ⟨left, right⟩ := h
  apply left
  simp_all only [TopologicalSpace.Opens.coe_mk, Set.mem_preimage, SetLike.mem_coe]


def f_adj (f : C(X, Y)) :  (f_obenstern f) ⊣ (f_untenstern f) where
  unit := {app := fun x => ⟨f_unit f⟩}
  counit := {app := fun x => ⟨f_counit f⟩}

def f_surjective_injective (f: C(X, Y)) : Function.Surjective (f_obenstern f).obj ↔ Function.Injective (f_obenstern f).obj := by
  sorry


def f_surjective_one (f: C(X, Y)) : Function.Surjective (f_obenstern f).obj ↔ (f_obenstern f) ⋙ (f_untenstern f) = 𝟭 (O Y) := by
  sorry
