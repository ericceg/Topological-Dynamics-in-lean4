import Mathlib


/-- Lemma: If we have AddAction M X and Y is a subset of X that is invariant under the action of M then the restriction of the action of M on Y is an AddAction M Y -/
instance AddAction_on_inv_subset
  {M X : Type*} [AddMonoid M] [AddAction M X] {Y : Set X}
  (h_Y_inv: ∀ c : M, ∀ x : X, x ∈ Y → c +ᵥ x ∈ Y) :
  AddAction M Y := {
    vadd := λ c y => ⟨c +ᵥ y.1, h_Y_inv c y.1 y.2⟩
    zero_vadd := λ x => Subtype.ext (zero_vadd M (x : X)),
    add_vadd := λ c₁ c₂ x => Subtype.ext (add_vadd c₁ c₂ (x : X))
    }
/-! EXPLANATION:
For the explanation, we restrict ourselves to the class VAdd
(the extension to the class AddAction should work similarly).
The definition of the class VAdd of M on X is given by a function vadd : M → X → X.
Hence to prove that the restriction of the action of M on Y is again of type VAdd, we need to define a function vadd : M → Y → Y.
To do this, we need to understand how lean handles subsets.
If Y : Set X, then the corresponding subtype Y has terms of the form ⟨y, h⟩, where y : X and h : x ∈ Y.
This means that a subset Y of X is represented by a term of type X and a proof h of the fact x ∈ Y.
(Credits to https://stackoverflow.com/questions/57154032/defining-a-function-to-a-subset-of-the-codomain)
Hence to construct a function M → Y → Y, when taking intputs c : M and y : Y we need to return a term of type Y,
i.e. something of the form ⟨y', h'⟩, where y' : X and h' : y' ∈ Y.
This explains the definition of vadd above.
 -/



open AddAction Set
open Pointwise -- necessary for `have : ∀ (E : Set Y), IsClosed E → (∀ (c : M), c +ᵥ E ⊆ E) → E = ∅ ∨ E = univ := sorry` to make sense

/-- Theorem 1.14: In a nonempty compact metric space X with an additive Action of M on X, there exists a closed,
nonempty subset Y such that Y is M-invariant and the restricted action of M on Y is minimal.
Todo: Think about additional assumptions about the action (e.g. continuity). Maybe even consider a continuous groupaction (induced by a homeomorphism on X).
 -/
theorem exists_minimal_invariant_subset
  {M X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [AddMonoid M] [AddAction M X] [ContinuousConstVAdd M X] :
   ∃ (Y : Set X) (hY_inv : ∀ c : M, ∀ x ∈ Y, c +ᵥ x ∈ Y),
   have : AddAction M Y := AddAction_on_inv_subset hY_inv
   IsClosed Y ∧
   Y.Nonempty ∧
   AddAction.IsMinimal M Y := by {
  let S := { Y : Set X | IsClosed Y ∧ Y.Nonempty ∧ ∀ c : M, ∀ x ∈ Y, c +ᵥ x ∈ Y }
  suffices ∃ Y ∈ S, ∀ Z ∈ S, Y ⊆ Z → Y = Z by {
    simp_all only [exists_and_left]
    obtain ⟨Y, hY, hY_maximal⟩ := this
    use Y
    aesop
    have AddAction_M_Y : AddAction M Y := AddAction_on_inv_subset hY.2.2
    have C_AddAction_M_Y : ContinuousConstVAdd M Y := sorry
    have RHS : ∀ (E : Set Y), IsClosed E → (∀ (c : M), c +ᵥ E ⊆ E) → E = ∅ ∨ E = univ := sorry
    have h1 := @isMinimal_iff_isClosed_vadd_invariant M Y inst_3 -- IMPORTANT: Here we need to use @ infront of isMinimal_iff_isClosed_vadd_invariant to allows us to explicitly provde the optional argument (topological space α in thise case).

  }
  apply zorn_subset at S
  unfold Maximal at S
  have hc := S (
    by
    intro c
    intro h
    intro h_is_chain
    sorry
  )

  obtain ⟨Y, hY, hY_maximal⟩ := hc
  use Y, hY
  intro Z hZ
  intro h_Y_subset_Z
  exact Set.Subset.antisymm h_Y_subset_Z (hY_maximal hZ h_Y_subset_Z)
  }
  -- let existence_minimal_element := S sorry



/-!
Run #min_imports at the end of the file to check necessary imports.
-/
