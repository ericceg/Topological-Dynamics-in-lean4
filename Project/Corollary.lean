import Mathlib


class MySubAddAction (M : Type*) (X : Type*) (Y : Set X) [AddMonoid M] [add_action_orig : AddAction M X] where
  SubAction : AddAction M Y
  SubAction_eq_Action : ∀ (c : M) (x : Y), ↑(c +ᵥ x) = add_action_orig.vadd c ↑x

open Pointwise AddAction Set


/-- Theorem 1.14: In a nonempty compact metric space X with an additive Action of M on X, there exists a closed,
nonempty subset Y such that Y is M-invariant and the restricted action of M on Y is minimal.
Todo: Think about additional assumptions about the action (e.g. continuity). Maybe even consider a continuous groupaction (induced by a homeomorphism on X).
 -/
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

variable {X : Type*} [h_X_top: TopologicalSpace X] [h_X_compact : CompactSpace X] [h_X_nonempty : Nonempty X]

-- Define the homeomorphism T : X → X
variable (T : X → X)
variable (T : Homeomorph X X)

-- Let ℕ act on X via iterates of T
def N_action (n : ℕ) (x : X) : X := (T^[n]) x

-- Define the orbit closure of x under T
def orbitClosure (x : X) : Set X := closure { y | ∃ n : ℕ, y = N_action T n x }

-- Recurrent point: x ∈ closure of its forward orbit
noncomputable def isRecurrent (x : X) : Prop := x ∈ closure { y | ∃n : ℕ, y = (T^[n]) x }

instance N_action_AddAction : AddAction ℕ X where
  vadd := N_action T
  zero_vadd := by
    intro x
    rfl
  add_vadd := by
    intros m n x
    exact congrFun (Function.iterate_add T m n) x

theorem exists_recurrent_point (hT : Continuous T) (hT_inv : Continuous T.symm) :
  ∃ x : X, isRecurrent T x := by {

/-- Works until here --/

  obtain ⟨Y, h_sub, Y_nonempty, Y_closed, Y_minimal⟩ :=
    exists_minimal_invariant_subset (M := ℕ) (X := X)
  }
