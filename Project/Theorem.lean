import Mathlib

open Pointwise AddAction Set


/--
Define `AddActionRestriction` class:
Given an additive action of an additive monoid M on a set X and a subset Y ⊆ X define the restriction of the action to Y subject to existence.
-/
class AddActionRestriction (M : Type*) (X : Type*) (Y : Set X)
  [AddMonoid M] [add_action_orig : AddAction M X] where
  SubAction : AddAction M Y
  SubAction_eq_Action : ∀ (c : M) (x : Y), ↑(c +ᵥ x) = add_action_orig.vadd c ↑x



/--
Lemma 13. Let M be an additive monoid acting on a set X and let Y ⊆ X be an M-
invariant subset, i.e. assume that MY ⊆ Y. Then the restricted action
M × Y → Y , (m, y) ↦ my
is a well-defined additive action of M on Y.
-/
def invariant_subset_restricted_action
  {M X : Type*} {Y : Set X}
  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X]
  (h_Y_invariant : ∀ c : M, ∀ y ∈ Y, c +ᵥ y ∈ Y) :
  AddActionRestriction M X Y := by {

  -- Define the restricted action on Y
  -- IMPORTANT: `let` is used (not `have`) to retain precise definition of `vadd`
  let AddAction_on_Y : AddAction M Y := {
    vadd := λ c y => ⟨c +ᵥ y.1, h_Y_invariant c y.1 y.2⟩,
    zero_vadd := λ x => Subtype.ext (zero_vadd M (x : X)),
    add_vadd := λ c₁ c₂ x => Subtype.ext (add_vadd c₁ c₂ (x : X))
  }

  constructor
  · intro c x
    change ↑(AddAction_on_Y.vadd c x) = h_M_X_action.vadd c ↑x
    exact rfl
}


/--
A version of `AddActionRestriction` where the restricted action is also continuous.
-/
class AddActionRestrictionContinuous (M X : Type*) (Y : Set X) [h_X_top : TopologicalSpace X]  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X] where
  (RestrictedAction : AddActionRestriction M X Y)
  (SubAction := RestrictedAction.SubAction)
  (SubActionContinuous : ContinuousConstVAdd M Y)


/--
Lemma 14. Let M be an additive monoid acting continuously on a compact topological
space X and let Y ⊆ X be an M-invariant subset. Then the restricted action of M on Y is
continuous.
-/
def restriction_of_continuous_action_is_continuous {M X : Type*} [h_X_top : TopologicalSpace X]  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X] (Y : Set X) (h_Y_invariant : ∀ c : M, ∀ y ∈ Y, c +ᵥ y ∈ Y) :
  AddActionRestrictionContinuous M X Y := by {
    have action_restricted := invariant_subset_restricted_action h_Y_invariant
    let SubAction := action_restricted.SubAction -- IMPORTANT: Here we need to use `let` instead of `have` to avoid the problem of "forgetting" the precise definition of the subaction
    constructor
    · exact action_restricted
    · have h_subaction_continuous_const_vadd : ∀ m : M, Continuous fun x : Y => m +ᵥ x := by {
        intro m
        let f := (fun x ↦ m +ᵥ x : X → X)
        have h_action_continuous_on_X := h_action_continuous.continuous_const_vadd m
        have h_action_continuous_on_Y : ContinuousOn f Y := by {
          exact Continuous.continuousOn h_action_continuous_on_X
        }
        have h_action_continuous_on_X : Continuous f := by exact h_action_continuous_on_X
        have ht : MapsTo f Y Y := by {
          unfold MapsTo
          intro x h_x_in_Y
          unfold f
          exact h_Y_invariant m x h_x_in_Y
        }
        have h_action_continuous_on_Y_restricted := @ContinuousOn.restrict_mapsTo X X h_X_top h_X_top f Y Y h_action_continuous_on_Y ht
        simp_all [f]
        have h_e : (MapsTo.restrict (fun x ↦ m +ᵥ x) Y Y ht) = (fun x : Y => m +ᵥ x) := by {
          ext x
          unfold MapsTo.restrict
          unfold Subtype.map
          simp
          have h_action_eq := action_restricted.SubAction_eq_Action m x
          simp_all [VAdd.vadd]
          exact rfl
        }
        have h_concl : Continuous fun x : Y => m +ᵥ x := h_e ▸ h_action_continuous_on_Y_restricted
        exact h_concl
      }
      exact { continuous_const_vadd := h_subaction_continuous_const_vadd }
  }





/--
Theorem 11. Let M be an additive monoid acting continuously on a non-empty compact
topological space X. If (M, X) is minimal then there exists a closed non-empty Y ⊆ X such
that MY ⊆ Y and the restricted action
M × Y → Y, (m, y) ↦ my
is minimal.
 -/
theorem exists_minimal_invariant_subset {M X : Type*}
  [h_X_top : TopologicalSpace X] [h_X_compact : CompactSpace X] [h_X_nonempty : Nonempty X]
  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X] :
   ∃ (Y : Set X) (h_SubAction : AddActionRestriction M X Y),
   have : AddAction M Y := h_SubAction.SubAction
   Y.Nonempty ∧
   IsClosed Y ∧
   AddAction.IsMinimal M Y := by {

    -- define the set S of closed non-empty subsets of X that are invariant under the action of M
    let S := { Y : Set X | IsClosed Y ∧ Y.Nonempty ∧ ∀ c : M, ∀ x ∈ Y, c +ᵥ x ∈ Y }
    have minimal_set: ∃ Y ∈ S, ∀ Z ∈ S, Z ⊆ Y → Y = Z := by {

      -- specialize Zorn's lemma to the set S
      have zorn_concl := zorn_superset S
      unfold Minimal at zorn_concl

      have h_existence_minimal_element := zorn_concl (
        by
        intro C
        intro h
        intro h_is_chain

        -- distinguish between the cases where C is empty and where C is non-empty
        by_cases h_C_nonempty : Nonempty ↑C -- needed to use `IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed`

        -- CASE 1: C is empty
        case neg := by
          have h_C_empty : C = ∅ := by {
            exact not_nonempty_iff_eq_empty'.mp h_C_nonempty
          }

          -- show that S is non-empty
          have : ∃ (x : Set X), x ∈ S := by {

            -- use X to witness the non-emptiness of S
            let X' := { x : X | True }
            use X'
            unfold S
            constructor
            · exact isClosed_const
            · constructor
              · apply Set.nonempty_def.2
                have h_exist_element_in_X : ∃ x : X, True := by {
                  exact (exists_const X).mpr trivial
                }
                obtain ⟨x, hx⟩ := h_exist_element_in_X
                use x
                exact hx
              · intro c x hx
                exact hx
          }
          obtain ⟨x, hx⟩ := this
          use x
          constructor
          · exact hx
          · simp_all only [le_eq_subset, empty_subset, IsChain.empty, nonempty_subtype, mem_empty_iff_false, exists_const, not_false_eq_true, IsEmpty.forall_iff, implies_true] -- obtained this using `hint`

        -- CASE 2: C is non-empty
        case pos := by

          -- use l := ⋂₀ C
          use (⋂₀ C)
          have h_all_sets_in_C_closed : ∀ c ∈ C, IsClosed c := by {
            intro c h_c_in_C
            have h_c_in_S := h h_c_in_C
            aesop
          }
          have h_all_sets_in_C_nonempty : ∀ c ∈ C, c.Nonempty := by {
            intro c h_c_in_C
            have h_c_in_S := h h_c_in_C
            have ⟨_, h_c_nonempty, _⟩ := h_c_in_S
            exact h_c_nonempty
          }
          have h_all_sets_in_C_compact : ∀ c ∈ C, IsCompact c := by {
            intro c h_c_in_C
            have h_c_in_S := h h_c_in_C
            exact IsClosed.isCompact (h_all_sets_in_C_closed c h_c_in_C) -- obtained this using `hint`
          }
          constructor

          -- show l ∈ S
          · constructor
            · exact isClosed_sInter h_all_sets_in_C_closed
            · constructor
              · have h_chain_reversed := IsChain.symm h_is_chain
                have : IsRefl (Set X) (flip fun x1 x2 ↦ x1 ⊆ x2) := by {
                  constructor
                  intro x
                  exact Subset.refl x
                }
                have h_C_DirectedOn := IsChain.directedOn h_chain_reversed
                have concl := @IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed X h_X_top C h_C_nonempty h_C_DirectedOn h_all_sets_in_C_nonempty h_all_sets_in_C_compact h_all_sets_in_C_closed
                exact concl
              · intro c x h_x_in_all_C
                have h_x_in_all_C : ∀ E ∈ C, c +ᵥ x ∈ E := by {
                  intro E h_E_in_C
                  have h_x_in_E : x ∈ E := by aesop
                  have h_E_in_S := h h_E_in_C
                  have ⟨_, _, h_E_inv⟩ := h_E_in_S
                  exact h_E_inv c x h_x_in_E
                }
                exact h_x_in_all_C

          -- show ∀ s ∈ C: l ⊆ s
          · intro s h_s_in_C
            unfold sInter
            exact fun ⦃a⦄ a ↦ a s h_s_in_C -- obtained this using `hint`
        )
      obtain ⟨Y, hY, hY_minimal⟩ := h_existence_minimal_element
      use Y, hY
      intro Z hZ
      intro h_Y_subset_Z
      have h_new := hY_minimal hZ h_Y_subset_Z
      exact Subset.antisymm (hY_minimal hZ h_Y_subset_Z) h_Y_subset_Z -- obtained this using `hint`
      }

    -- use the minimal set Y obtained from Zorn's lemma
    obtain ⟨Y, h_Y⟩ :=  minimal_set
    use Y
    have h_Y_in_S := h_Y.1
    have h_Y_isClosed := h_Y_in_S.1
    have h_Y_nonempty := h_Y_in_S.2.1
    have h_Y_inv := h_Y_in_S.2.2

    -- obtain restricted action (and use Lemma 14)
    let RestrictedActionContinuous := restriction_of_continuous_action_is_continuous Y h_Y_inv
    let h_subaction_continuous := RestrictedActionContinuous.SubActionContinuous
    let RestrictedAction := RestrictedActionContinuous.RestrictedAction
    let SubAction := RestrictedAction.SubAction

    use RestrictedAction
    use h_Y_nonempty
    use h_Y_isClosed

    -- apply Proposition 12
    have h1 := @isMinimal_iff_isClosed_vadd_invariant M Y h_M_monoid instTopologicalSpaceSubtype SubAction h_subaction_continuous
    have h1 := h1.2
    apply h1
    intro E
    intro hE_isClosed
    intro hE_inv
    by_cases hE : E.Nonempty
    · right
      let h_Y_AddAction := SubAction
      have h_E_in_S : ↑E ∈ S := by {
        constructor
        · exact IsClosed.trans hE_isClosed h_Y_isClosed
        · apply And.intro
          · exact Nonempty.image Subtype.val hE
          · intro c x
            intro h_x_in_E
            obtain ⟨y, hyE, rfl⟩ := h_x_in_E
            have h_E_inv_under_c := hE_inv c
            have h_cy_in_E : c +ᵥ y ∈ E := h_E_inv_under_c (Set.mem_image_of_mem _ hyE)
            have h_test := RestrictedAction.SubAction_eq_Action c y
            change h_M_X_action.vadd c y ∈ Subtype.val '' E
            rw [←h_test]
            exact mem_image_of_mem Subtype.val h_cy_in_E -- obtained this using `hint`
      }
      let E' := Subtype.val '' E
      have h_E'_in_S : E' ∈ S := by {
        gcongr
      }
      have h_E'_sub_Y : E' ⊆ Y := by {
        exact Subtype.coe_image_subset Y E
      }
      have h2 := h_Y.2
      have h2 := h2 E'
      have h2 := h2 h_E'_in_S
      have h2 := h2 h_E'_sub_Y
      exact eq_univ_of_image_val_eq (id (Eq.symm h2))
    · left
      exact Set.not_nonempty_iff_eq_empty.mp hE
   }
