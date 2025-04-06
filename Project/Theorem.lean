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

open Pointwise

open AddAction Set

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
    have h_Y_in_S := h_Y.1
    have h_Y_isClosed := h_Y_in_S.1
    have h_Y_nonempty := h_Y_in_S.2.1
    have h_Y_inv := h_Y_in_S.2.2
    have SubAddAction : MySubAddAction M X Y
    constructor
    have AddAction_on_Y : AddAction M Y := {
      vadd := λ c y => ⟨c +ᵥ y.1, h_Y_inv c y.1 y.2⟩
      zero_vadd := λ x => Subtype.ext (zero_vadd M (x : X)),
      add_vadd := λ c₁ c₂ x => Subtype.ext (add_vadd c₁ c₂ (x : X))
    }
    intro c x
    rfl
    have AddAction_on_Y : AddAction M Y := {
      vadd := λ c y => ⟨c +ᵥ y.1, h_Y_inv c y.1 y.2⟩
      zero_vadd := λ x => Subtype.ext (zero_vadd M (x : X)),
      add_vadd := λ c₁ c₂ x => Subtype.ext (add_vadd c₁ c₂ (x : X))
    }
    exact AddAction_on_Y
    use SubAddAction
    have AddAction_on_Y := SubAddAction.SubAction
    use h_Y_nonempty
    use h_Y_isClosed
    #check SubAddAction.SubAction.1
    have h_subaction_continuous : ContinuousConstVAdd M Y := by sorry
    have h1 := @isMinimal_iff_isClosed_vadd_invariant M Y h_M_monoid instTopologicalSpaceSubtype AddAction_on_Y h_subaction_continuous
    have h1 := h1.2
    have RHS : ∀ (E : Set Y), IsClosed E → (∀ (c : M), c +ᵥ E ⊆ E) → E = ∅ ∨ E = univ := sorry
    apply h1 at RHS
    convert RHS

   }
