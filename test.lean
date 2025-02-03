import Mathlib

variable {α : Type*}  [CompleteLattice α] [HeytingAlgebra α]

lemma test : ∀ (a : α) (s : Set α), a ⊓ sSup s ≤ ⨆ b ∈ s, a ⊓ b := by
  intro a s
  have h :∀ b,  a ⊓ sSup s ≤ b ↔ a ≤ sSup s ⇨ b := by
    intro b
    apply Iff.symm
    sorry
  rw [le_iSup_iff]
  simp only [iSup_le_iff]
  intro b h
  suffices (a ≤ sSup s ⇨ b) by (sorry) -- le_himp_iff

  have h1 : ∀ i ∈ s,( a ≤ i ⇨ b) := by
    intro i hi
    sorry
