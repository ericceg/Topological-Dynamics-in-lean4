import Mathlib


/-! A SubAddAction is a set which is closed under scalar multiplication.
structure SubAddAction (R : Type u) (M : Type v) [VAdd R M] : Type v where
  /-- The underlying set of a `SubAddAction`. -/
  carrier : Set M
  /-- The carrier set is closed under scalar multiplication. -/
  vadd_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c +ᵥ x ∈ carrier
-/

class MySubAddAction (M : Type*) (X : Type*) (Y : Set X) [AddMonoid M] [AddAction M X] where
  SubAction : AddAction M Y
  SubAction_eq_Action: ∀ (c : M) (x : Y), ↑(c +ᵥ x) = c +ᵥ ↑x

open scoped Pointwise

variable {M X : Type*} [h_X_top : TopologicalSpace X] [h_X_compact : CompactSpace X] [h_X_nonempty : Nonempty X]
  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X]


/-- Theorem 1.14: In a nonempty compact metric space X with an additive Action of M on X, there exists a closed,
nonempty subset Y such that Y is M-invariant and the restricted action of M on Y is minimal.
Todo: Think about additional assumptions about the action (e.g. continuity). Maybe even consider a continuous groupaction (induced by a homeomorphism on X).
 -/
theorem exists_minimal_invariant_subset :
   ∃ (Y : Set X) (h_SubAction : MySubAddAction M X Y),
   have SubAction : AddAction M Y := h_SubAction.SubAction
   Y.Nonempty ∧
   IsClosed Y ∧
   AddAction.IsMinimal M Y := by {
    let S := { Y : Set X | IsClosed Y ∧ Y.Nonempty ∧ ∀ c : M, ∀ x ∈ Y, c +ᵥ x ∈ Y }
    have minimal_set: ∃ Y ∈ S, ∀ Z ∈ S, Y ⊆ Z → Y = Z := by {
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
    obtain ⟨Y, h_Y⟩ :=  minimal_set
    use Y
   }
