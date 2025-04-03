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

open AddAction Set
open Pointwise -- necessary for `have : ∀ (E : Set Y), IsClosed E → (∀ (c : M), c +ᵥ E ⊆ E) → E = ∅ ∨ E = univ := sorry` to make sense

/-- Theorem 1.14: In a nonempty compact metric space X with an additive Action of M on X, there exists a closed,
nonempty subset Y such that Y is M-invariant and the restricted action of M on Y is minimal.
Todo: Think about additional assumptions about the action (e.g. continuity). Maybe even consider a continuous groupaction (induced by a homeomorphism on X).
 -/
theorem exists_minimal_invariant_subset
  {M X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [AddMonoid M] [AddAction M X] [ContinuousConstVAdd M X] :
   ∃ (Y : Set X) (hY_inv : ∀ c : M, ∀ x ∈ Y, c +ᵥ x ∈ Y),
   have h_action_on_inv_subset : AddAction M Y := AddAction_on_inv_subset hY_inv
   IsClosed Y ∧
   Y.Nonempty ∧
   AddAction.IsMinimal M Y := by sorry

/-- For a point x₀ in a compact topological space X with an additive action M on X,
the set Y of limits of any function ϕ: ℕ → X where ϕ(0) = x₀ and ϕ(n + 1) = mₙ ϕ(n) for some element mₙ ∈ M. -/
def LimitSet {M X : Type*} [TopologicalSpace X] [CompactSpace X] [AddMonoid M] [AddAction M X]
  [ContinuousConstVAdd M X] (x : X) : Set X :=  {y | ∃ (m_n : ℕ → M), ∃ (ϕ : ℕ → X), (ϕ 0 = x) ∧ (∀ n, ϕ (n + 1) = m_n n +ᵥ ϕ n) ∧
    ∀(Y : Set X), ∃ N, ∀ n ≥ N, ϕ n ∈ Y ∧ IsOpen Y ∧ y ∈ Y }

/-- A recurrent point is a point that is contained in its LimitSet. -/
def isRecurrentPoint {M X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  [AddMonoid M] [AddAction M X] [ContinuousConstVAdd M X] (x : X) : Prop :=  x ∈ LimitSet x

/--Corollary 1.16: If X is a non-empty compact topological space with an additive action of M on X,
then there exists some recurrent x_0 ∈ X.-/
theorem exists_recurrent_point
  {M X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] [AddMonoid M] [AddAction M X] [ContinuousConstVAdd M X] :
  ∃ (x : X), isRecurrentPoint x := by sorry

/-!
Run #min_imports at the end of the file to check necessary imports.
-/
