import Mathlib
import Project.Theorem

--

/-!
## 1. If an action is minimal, every point is Recurrent
-/

variable {X : Type*} [TopologicalSpace X]
         {M : Type*} [AddMonoid M]
         [AddAction M X]

def StronglyRecurrent (x: X): Prop:=
  x ∈ ⋂ (m : M), closure (AddAction.orbit M (m +ᵥ x))

lemma Minimal_strongly_recurrent (x : X)
    [AddAction.IsMinimal M X] :
  StronglyRecurrent (M := M) x := by
    apply Set.mem_iInter.2
    intro m
    exact AddAction.IsMinimal.dense_orbit (M := M) (x :=  (m +ᵥ x)) x

/-!
## 2. If a point of a subaction is recurrent, it is recurrent upstairs as well
-/

/-- The sub-action packaged in AddActionRestriction as a type-class
instance, so that typeclass inference can find AddAction M Y. -/
instance AddActionRestriction.toAddAction
    {M X : Type*} {Y : Set X}
    [AddMonoid M] [AddAction M X] [h : AddActionRestriction M X Y] :
  AddAction M Y :=
  h.SubAction

/--  If a point is strongly recurrent for the sub-action on Y, then the same point (viewed in X) is strongly recurrent for the ambient action.  -/
lemma StronglyRecurrent.of_subaction
    {X : Type*} [TopologicalSpace X]
    {M : Type*} [AddMonoid M] [AddAction M X]
    {Y : Set X} [AddActionRestriction M X Y]
    {y : Y}
    (hy : StronglyRecurrent (M := M) (X := Y) y) :
  StronglyRecurrent (M := M) (X := X) (y : X) := by {

    apply Set.mem_iInter.2
    intro m
    -- 1. Strong recurrence inside `Y` (w rel topology)
    -- 2. Continuous inclusion sends it inside the closure in `X`
    have hX' : (y : X) ∈
      closure ((Subtype.val) '' (AddAction.orbit M (m +ᵥ y) : Set Y)) :=
        (closure_subtype).1 ((Set.mem_iInter.1 hy) m)
    -- 3. the image of the orbit in `Y` sits inside the ambient orbit in `X`
    have hsubset :
        (Subtype.val) '' (AddAction.orbit M (m +ᵥ y) : Set Y) ⊆
        (AddAction.orbit M (m +ᵥ (y : X)) : Set X) := by
      rintro z ⟨z', ⟨c, rfl⟩, rfl⟩
      -- Bring the action up in two steps

      --WRITE THIS HAVE ON THE BOARD: y ∈ Y ⊆ X: a+b+(y as element of Y)=a+b+(y though as an element of X) (where + are add action on M Y or on M X)
      have h1 : ↑(m +ᵥ y : Y) = m +ᵥ (y : X) :=
            AddActionRestriction.SubAction_eq_Action m y
      have h2 : ↑(c +ᵥ (m +ᵥ y) : Y) = c +ᵥ ((m +ᵥ y):X) :=
        AddActionRestriction.SubAction_eq_Action c (m +ᵥ y)
      rw [h1] at h2
      have hrewrite : ↑(c +ᵥ (m +ᵥ y) : Y) = c +ᵥ m +ᵥ (y : X) := h2
        -- the RHS is plainly in the ambient orbit
      have : (c +ᵥ (m +ᵥ (y : X)))
          ∈ (AddAction.orbit M (m +ᵥ (y : X)) : Set X) := ⟨c, rfl⟩
      simp [hrewrite]
    exact (closure_mono hsubset) hX'
}

lemma StronglyRecurrent.of_minimal_subaction
    {X : Type*} [TopologicalSpace X]
    {M : Type*} [AddMonoid M] [AddAction M X]
    {Y : Set X} [AddActionRestriction M X Y]
    (hmin: AddAction.IsMinimal M Y)
    {y : Y} :
  StronglyRecurrent (M := M) (X := X) (y : X) := by {

  haveI : AddAction.IsMinimal M Y := hmin

  have hy_in_Y : StronglyRecurrent (M := M) (X := Y) y :=
    Minimal_strongly_recurrent (M := M) (X := Y) y

  exact StronglyRecurrent.of_subaction hy_in_Y
}

/--!
## 3. If X is a non-empty compact space acted upon continuously by a monoid M, then X has a strongly recurrent point.
-/

theorem exists_strongly_recurrent
  {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
  {M : Type*} [AddMonoid M] [AddAction M X]
  [ContinuousConstVAdd M X] :
  ∃ x, StronglyRecurrent (M := M) (X := X) x := by {

  obtain ⟨Y, hSubAction, hY_nonempty, hY_closed, hY_minimal⟩ :=
  exists_minimal_invariant_subset (M := M) (X := X)

  obtain ⟨x0, hx0Y⟩ := hY_nonempty

  let y : Y := ⟨x0, hx0Y⟩

  haveI : AddAction.IsMinimal M Y := hY_minimal

  have hy_recurrent_in_Y :
    StronglyRecurrent (M := M) (X := Y) y :=
    Minimal_strongly_recurrent y

  have hx_recurrent_in_X :
    StronglyRecurrent (M := M) (X := X) (y : X) :=
      StronglyRecurrent.of_subaction hy_recurrent_in_Y

  use (y : X)
}
