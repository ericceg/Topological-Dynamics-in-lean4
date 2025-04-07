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
    have minimal_set: ∃ Y ∈ S, ∀ Z ∈ S, Z ⊆ Y → Y = Z := by {
      apply zorn_superset at S
      unfold Minimal at S
      have hc := S (
        by
        intro C
        intro h
        intro h_is_chain
        use (⋂₀ C)
        constructor
        · constructor
          · have h_all_sets_in_C_closed : ∀ c ∈ C, IsClosed c := by {
              intro c h_c_in_C
              have h_c_in_S := h h_c_in_C
              aesop
            }
            exact isClosed_sInter h_all_sets_in_C_closed
          · constructor
            · sorry
            · sorry
        · intro s h_s_in_C
          unfold sInter
          exact fun ⦃a⦄ a ↦ a s h_s_in_C -- obtained this using `hint`
      )
      obtain ⟨Y, hY, hY_minimal⟩ := hc
      use Y, hY
      intro Z hZ
      intro h_Y_subset_Z
      have h_new := hY_minimal hZ h_Y_subset_Z
      exact Subset.antisymm (hY_minimal hZ h_Y_subset_Z) h_Y_subset_Z -- obtained this using `hint`
      }
    obtain ⟨Y, h_Y⟩ :=  minimal_set
    use Y
    have h_Y_in_S := h_Y.1
    have h_Y_isClosed := h_Y_in_S.1
    have h_Y_nonempty := h_Y_in_S.2.1
    have h_Y_inv := h_Y_in_S.2.2
    have SubAddAction : MySubAddAction M X Y
    have AddAction_on_Y : AddAction M Y := {
      vadd := λ c y => ⟨c +ᵥ y.1, h_Y_inv c y.1 y.2⟩
      zero_vadd := λ x => Subtype.ext (zero_vadd M (x : X)),
      add_vadd := λ c₁ c₂ x => Subtype.ext (add_vadd c₁ c₂ (x : X))
    }
    constructor
    · intro c x
      rfl
    · exact AddAction_on_Y
    use SubAddAction
    use h_Y_nonempty
    use h_Y_isClosed
    #check SubAddAction.SubAction.1
    let h_subaction_VAdd := SubAddAction.SubAction.toVAdd
    have h_subaction_continuous_const_vadd : ∀ m : M, Continuous fun x : Y => m +ᵥ x := by {
      intro m
      have h_action_continuous_on_X := h_action_continuous.continuous_const_vadd m
      constructor
      intro S
      intro h_S
      sorry
    }
    have h_subaction_continuous : @ContinuousConstVAdd M Y instTopologicalSpaceSubtype SubAddAction.SubAction.toVAdd := by {
      constructor
      · exact h_subaction_continuous_const_vadd
    }
    have h1 := @isMinimal_iff_isClosed_vadd_invariant M Y h_M_monoid instTopologicalSpaceSubtype SubAddAction.SubAction h_subaction_continuous
    have h1 := h1.2
    apply h1
    intro E
    intro hE_isClosed
    intro hE_inv
    by_cases hE : E.Nonempty
    · right
      have h_Y_AddAction := SubAddAction.SubAction
      have h_E_in_S : ↑E ∈ S := by {
        constructor
        · exact IsClosed.trans hE_isClosed h_Y_isClosed
        · apply And.intro
          · exact Nonempty.image Subtype.val hE
          · intro c x
            intro h_x_in_E
            have h_E_inv_under_c := hE_inv c
            sorry
      }
      let E' := Subtype.val '' E
      have h_E'_in_S : E' ∈ S := by aesop
      have h_E'_sub_Y : E' ⊆ Y := by aesop
      have h2 := h_Y.2
      have h2 := h2 E'
      have h2 := h2 h_E'_in_S
      have h2 := h2 h_E'_sub_Y
      exact eq_univ_of_image_val_eq (id (Eq.symm h2))
    · left
      exact Set.not_nonempty_iff_eq_empty.mp hE
   }
