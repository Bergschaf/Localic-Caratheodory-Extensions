
class Divisoid(X : Type)  where
  split : X → X → X → Prop
  ε : X
  split_sym : ∀ {x a b}, (split x a b) → (split x b a)
  split_ident₁ : ∀{x y}, split x ε y → x = y
  split_ident₂ : ∀ {x}, split x ε x
  split_split : ∀ {x a b a₁ a₂ b₁ b₂}, split x a b → split a a₁ a₂ → split b b₁ b₂
              → ∃ x₁ x₂, split x x₁ x₂ ∧ split x₁ a₁ b₁ ∧ split x₂ a₂ b₂
-- \leadsto and \oplus
notation x:arg "↝" a:arg "⊕" b:arg => Divisoid.split x a b

section
  variable {X : Type}[m : Divisoid X]
  variable (x : X)

  theorem Divisoid.split_genL:  x ↝ a ⊕ b → a ↝ a₁ ⊕ a₂ → ∃ q, x ↝ a₁ ⊕ q ∧ q ↝ a₂ ⊕ b := by
    intro h1 h2
    have h3 : b ↝ ε ⊕ b := by
        exact split_ident₂
    let s := split_split h1 h2 h3
    rcases s with ⟨x1, x2, s1, s2,s3⟩
    use x2
    apply And.intro
    . have h4 : x1 = a₁ := by
        let s2 := split_sym s2
        apply split_ident₁ s2
      rw [← h4]
      exact s1
    . exact s3



  theorem Divisoid.split_genR : x ↝ a ⊕ b → b ↝ c ⊕ d → ∃ q, x ↝ q ⊕ d ∧ q ↝ a ⊕ c := by
    intro h1 h2
    have h3 : a ↝ ε ⊕ a := by
        exact split_ident₂
    let h2 := split_sym h2
    let s := split_split h1 h3 h2
    rcases s with ⟨x1, x2, s1, s2,s3⟩
    use x2
    apply And.intro
    . have h4 : x1 = d := by
        apply split_ident₁ s2
      rw [← h4]
      apply split_sym
      exact s1
    . exact s3

end

def lifted {A : Type}(op : A → A → Option A)(x y : Option A) : Option A := match x , y with
  | none  , _ => none
  | _  , none => none
  | some x, some y => op x y

class PCM(X : Type) where
  op : X → X → Option X
  ε : X
  op_comm : ∀a b, op a b = op b a
  op_ident : ∀x, op ε x = some x
  op_assoc : ∀a b c, lifted op (op a b) (some c) = lifted op (some a) (op b c)

-- \cdot
infixl:70  "⬝" => PCM.op
infixl:70  "⬝'" => lifted PCM.op


section
  variable {X : Type}[m : PCM X]

  def pcm_divis: Divisoid X where
    split := (λx y z => some x = y ⬝ z)
    ε := PCM.ε
    split_sym := by
      simp only [PCM.op_comm]
      exact fun {x a b} a => a

    split_ident₁ := by
      intro x y h
      rw [PCM.op_ident] at h
      simp_all only [Option.some.injEq]

    split_ident₂ := by
      intro x
      rw [PCM.op_ident]
    split_split := by
      intro x a b a1 a2 b1 b2 h1 h2 h3
      simp
      use (a1 ⬝' a2)
      use (b1 ⬝' b2)



      apply And.intro
      . exact h1
      apply And.intro
      . match a1 ⬝ b1 with
        | none =>
        | some x => sorry
end
