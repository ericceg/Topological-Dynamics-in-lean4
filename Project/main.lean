import Mathlib


/-- Lemma: If we have AddAction M X and Y is a subset of X that is invariant under the action of M then the restriction of the action of M on Y is an AddAction M Y -/
instance AddAction_on_inv_subset
  {M X : Type*} [AddMonoid M] [AddAction M X] {Y : Set X}
  (h_Y_inv: ∀ c : M, ∀ x : X, x ∈ Y → c +ᵥ x ∈ Y) :
  AddAction M Y := by {
    sorry
  }



/-- Theorem 1.14: In a nonempty compact metric space X with an additive Action of M on X, there exists a closed,
nonempty subset Y such that Y is M-invariant and the restricted action of M on Y is minimal.
Todo: Think about additional assumptions about the action (e.g. continuity). Maybe even consider a continuous groupaction (induced by a homeomorphism on X).
 -/
theorem exists_minimal_invariant_subset
  {M X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X] [AddMonoid M] [AddAction M X] [ContinuousConstVAdd M X] :
   ∃ (Y : Set X) (hY_inv : ∀ c : M, ∀ x ∈ Y, c +ᵥ x ∈ Y),
   have : AddAction M Y := AddAction_on_inv_subset hY_inv
   IsClosed Y ∧
   Y.Nonempty ∧
   AddAction.IsMinimal M Y := by {
    sorry
   }
