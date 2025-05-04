import Mathlib

class MySubAddAction (M : Type*) (X : Type*) (Y : Set X) [AddMonoid M] [add_action_orig : AddAction M X] where
  SubAction : AddAction M Y
  SubAction_eq_Action : ∀ (c : M) (x : Y), ↑(c +ᵥ x) = add_action_orig.vadd c ↑x

open Pointwise AddAction Set

/-- Theorem 1.14: In a nonempty compact metric space X with an additive Action of M on X, there exists a closed,
nonempty subset Y such that Y is M-invariant and the restricted action of M on Y is minimal.--/
axiom exists_minimal_invariant_subset
  {M X : Type*} [h_X_top : TopologicalSpace X] [h_X_compact : CompactSpace X] [h_X_nonempty : Nonempty X]
  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X]:
   ∃ (Y : Set X) (h_SubAction : MySubAddAction M X Y),
   have : AddAction M Y := h_SubAction.SubAction
   Y.Nonempty ∧
   IsClosed Y ∧
   AddAction.IsMinimal M Y

open Set Filter
open Nat

lemma continuous_iterate {X : Type*} [TopologicalSpace X] {f : X → X} (n : ℕ) (hf : Continuous f) : Continuous (f^[n]) := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero]
    exact continuous_id
  | succ n ih =>
    simp only [Function.iterate_succ']
    exact hf.comp ih

variable {X : Type*} [h_X_top: TopologicalSpace X] [h_X_compact : CompactSpace X] [h_X_nonempty : Nonempty X]
variable (T : Homeomorph X X)

/-- Let ℕ act on X via iterates of T--/
def N_action (T: Homeomorph X X) (n : ℕ) (x : X) : X := (T^[n]) x

/-- Define the OmegaLimit of x under T--/
def MyOmegaLimit (x : X) : Set X := ⋂ (N : ℕ), closure ({ T^[n] x | n ≥ N } : Set X)

/-- Recurrent point: x ∈ closure of its forward orbit --/
noncomputable def isRecurrent (x : X) : Prop := x ∈ MyOmegaLimit T x

instance N_action_AddAction : AddAction ℕ X where
  vadd := N_action T
  zero_vadd := by
    intro x
    rfl
  add_vadd := by
    intros m n x
    exact congrFun (Function.iterate_add T.toFun m n) x

-- theorem isMinimal_iff_isClosed_vadd_invariant (M : Type u_1) {α : Type u_3} [AddMonoid M] [TopologicalSpace α] [AddAction M α] [ContinuousConstVAdd M α] :
-- AddAction.IsMinimal M α ↔ ∀ (s : Set α), IsClosed s → (∀ (c : M), c +ᵥ s ⊆ s) → s = ∅ ∨ s = Set.univ

/-- Corollary 1.16: If X is a non-empty compact topological space with a homeomorphism T:X → X (which can be though of as
inducing an action of ℕ onto X via n + x = T^n(x)) then there exists a recurrent point in the sense above.--/
theorem exists_recurrent_point (T : Homeomorph X X):
  ∃ x : X, isRecurrent T x := by {

  -- N acts on X by n + x=T^n(x) and this action is continuous
  let _ : AddAction ℕ X := N_action_AddAction T
  let _ : ContinuousConstVAdd ℕ X :=
  { continuous_const_vadd := fun n ↦ continuous_iterate n T.continuous }

  -- By the theorem (here axiom) above, there exists a non-empty, closed, T invariant minimal subset, call it Y
  obtain ⟨Y, hSubAction, hY_nonempty, hY_closed, hY_minimal⟩ :=
  exists_minimal_invariant_subset (M := ℕ) (X := X)

  let _ : AddAction ℕ Y := hSubAction.SubAction

  -- Y is not empty, so there exists some element, call it x
  obtain ⟨x, hx⟩ := hY_nonempty

  let Z := MyOmegaLimit T x

  -- the omega+ limit set of x is all of Y
  have orbit_dense : Z = Y := by {
    -- We consider x ∈ X into an element of Y (henceforth calling it x') using hx
    let x' : Y := ⟨x, hx⟩
    -- The orbit of x' is minimal in the sense that the orbit of x' is dense in Y
    have h_orbit := hY_minimal.dense_orbit x'
    -- Every point of Y is in the closure of the orbit of x'
    simp only [dense_iff_closure_eq, Set.ext_iff, Set.mem_univ, Subtype.forall] at h_orbit

    let contX : ContinuousConstVAdd ℕ X :=
    { continuous_const_vadd := fun n => continuous_iterate n T.continuous }

    let contY : ContinuousConstVAdd ℕ Y := sorry

    have : Z = Y := by {
      let Z_in_Y : Set Y := Subtype.val ⁻¹' Z

      have hZ_in_Y_closed : IsClosed Z_in_Y := by {
        have hZ_closed : IsClosed Z := by {
          apply isClosed_iInter
          intro N
          exact isClosed_closure
          }
        exact isClosed_induced_iff.mpr ⟨Z, hZ_closed, rfl⟩
        }

      have hZ_in_Y_invariant : ∀ (c : ℕ), c +ᵥ Z_in_Y ⊆ Z_in_Y := by {
        intro c y hy
        rcases hy with ⟨z, hzZinY, rfl⟩

        let contTc : Continuous (T^[c]) := continuous_iterate c T.continuous

        have h_main : ∀ N, T^[c] z ∈ closure ({ T^[n] x | n ≥ N } : Set X) := by {
          sorry
        }

        change Subtype.val (c +ᵥ z) ∈ Z
        rw [hSubAction.SubAction_eq_Action c z]
        exact Set.mem_iInter.2 h_main
      }

      have hZ_cases : Z_in_Y = ∅ ∨ Z_in_Y = univ := by {
        let h := @isMinimal_iff_isClosed_vadd_invariant ℕ Y _ _ hSubAction.SubAction
          contY
        apply h.mp hY_minimal Z_in_Y hZ_in_Y_closed
        apply hZ_in_Y_invariant
      }

      have Z_sub_Y : Z ⊆ Y := by {
        intros z hz
        have h_limit : ∀ N, z ∈ closure {T^[n] x | n ≥ N} := by {
          intro N
          exact Set.mem_iInter.mp hz N
        }
        have sequence_in_Y : ∀ n : ℕ, T^[n] x ∈ Y := by {
          intro n
          induction n with
          | zero =>
          exact hx
          | succ n ih =>
          have h1 : 1 +ᵥ T^[n] x ∈ Y := by {
            let y : {x // x ∈ Y} := ⟨T^[n] x, ih⟩
            have eq : ↑(1 +ᵥ y) = 1 +ᵥ (T^[n] x) := by
              exact (congr_arg (fun z => z) (hSubAction.SubAction_eq_Action 1 y))
            rw [← eq]
            exact (1 +ᵥ y).property
          }
          have h2 : (1 +ᵥ T^[n] x) = T^[n+1] x := by {
            simp [N_action, Function.iterate_succ']
            sorry
        }
          rw [← h2]
          exact h1
        }
        have : z ∈ Y := by {
          have h := h_limit 0
          have h_subset : {T^[n] x | n ≥ 0} ⊆ Y := by {
            rintro y ⟨n, hn, rfl⟩
            exact sequence_in_Y n
          }
          have h_closure : closure {T^[n] x | n ≥ 0} ⊆ Y := by {
            have h1 : closure Y = Y := hY_closed.closure_eq
            exact Subset.trans (closure_mono h_subset) (by rw [h1])
          }
          exact h_closure h
        }
        exact this
      }

      -- Z ≠ ∅
      have Z_in_Y_nonempty : Z_in_Y.Nonempty := by {
        have Z_nonempty : Z.Nonempty := by {
          have decreasing : ∀ i,
            closure {y | ∃ m ≥ i + 1, T^[m] x = y} ⊆ closure {y | ∃ m ≥ i, T^[m] x = y} := by {
            intro i
            apply closure_mono
            rintro y ⟨m, hm, rfl⟩
            exact ⟨m, Nat.le_trans (Nat.le_succ i) hm, rfl⟩
          }
          have all_closed : ∀ N, IsClosed (closure {y | ∃ n ≥ N, T^[n] x = y}) := by {
            intro N
            exact isClosed_closure
          }
          have all_nonempty : ∀ N, (closure {y | ∃ n ≥ N, T^[n] x = y}).Nonempty := by {
            intro N
            use T^[N] x
            apply subset_closure
            use N
          }

          have first_compact : IsCompact (closure { y | ∃ m ≥ 0, T^[m] x = y }) :=
            isClosed_closure.isCompact

          have Z_nonempty : Z.Nonempty :=
            IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
              (λ N => closure { y | ∃ m ≥ N, T^[m] x = y })
              decreasing
              all_nonempty
              first_compact
              all_closed

          exact Z_nonempty
        }
        have Z_in_Y_nonempty : Z_in_Y.Nonempty := by
          rcases Z_nonempty with ⟨z, hz⟩
          use ⟨z, Z_sub_Y hz⟩
          exact hz

        exact Z_in_Y_nonempty
      }

      -- As Z ≠ ∅ then Z_in_Y is all of univ
      have hZ_eq_univ : Z_in_Y = univ := (hZ_cases.resolve_left (by
      intro h
      exact Z_in_Y_nonempty.ne_empty h))

      -- We now need to show that Z is all of Y

      have Y_sub_Z : Y ⊆ Z := by {
        intros y hy
        have : ⟨y, hy⟩ ∈ Z_in_Y := by rw [hZ_eq_univ]; trivial
        exact this
      }

      exact subset_antisymm Z_sub_Y Y_sub_Z
    }
    exact this
  }

  -- as x ∈ Y then x is in the omega+ limit set of x
  have : x ∈ Z := by
    rw [orbit_dense]
    exact hx

  -- this is precisely the definition of x being recurrent
  exact ⟨x, this⟩
}
