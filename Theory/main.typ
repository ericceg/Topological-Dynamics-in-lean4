#import "preamble.typ": *


/* ----------------- LOAD PAPER TEMPLATE ----------------- */
#show: paper.with(
  title: [
    Topological Dynamics in `Lean`
  ],
  authors: (
    (
      name: "Eric Ceglie",
      affiliation: "ETH Zurich",
      email: "eceglie@ethz.ch",
    ),
    (
      name: "Leandro Zehnder",
      affiliation: "ETH Zurich",
      email: "lzehnde@ethz.ch",
    )
  ),
  abstract: [#lorem(50)],
  institution: [
    Federal Institute of Technology Zurich \
    Department of Mathematics
  ],
  toc: false,
  chapter-style-heading: false
)


#set enum(numbering: "(1)")
#set heading(numbering: none)

#let link_to_lean_implementation = link("https://github.com/ericceg/lean-theorem-minimal-subsystem")[`Lean` implementation (`github.com/ericceg/lean-theorem-minimal-subsystem`):]


= Topological Dynamics 


Let $X$ be a set and $T:X ->  X$ a map. This setting is called a _dynamical system_.

#definition()[
For any $x ∈ X$ define the _orbit_ of $x$ by $ 
cal(O)(x) := {T^n (x) | n ∈ NN_0}.  
$ 
]

From now on, assume that $X$ is a compact metric space and $T: X ->  X$ is continuous.
This is called a _topological dynamical system_. 

#definition()[
$T$ is called _transitive_ if there exists a point $x_0 ∈ X$ with dense orbit, i.e. 
if $overline(cal(O)(x_0)) = X$. 
]

#definition()[
$T$ is called _minimal_ if every orbit is dense. 
]

The following proposition provides an equivalent characterization of minimality.

#proposition()[
Let $T:X ->  X$ be continuous on a compact metric space.
Then $T$ is minimal if and only if for every closed $T$-invariant subset $E subset.eq X$ 
we have $E = emptyset$ or $E = X$.
]<prop-minimal-equivalence-1>

This proposition is already implemented in `mathlib4` and our goal will be to use this to prove the following theorem.


#theorem()[
Let $X$ be a non-empty compact metric space and $T:X ->  X$ continuous. 
Then there exists a closed non-empty $Y subset.eq X$ such that $T Y = Y$ 
and $T|_Y: Y ->  Y$ is minimal. 
]


= Reformulation using Actions 

As `mathlib4` tries to be as general as possible, we will reformulate the previous definitions and theorems using actions. On the one hand, this will make our final theorem more powerful and on the other hand, it will allow us to use the implementation of @prop-minimal-equivalence-1 more easily. 

#definition()[
A set $M$ equipped with a binary operation $+: M times M ->  M$ is called an _(additive) monoid_
the following hold:

1. For all $a, b, c ∈ M$ we have $(a+b)+c = a+(b+c)$.

2. There exists an element $0 ∈ M$ such that $a+0=0+a=a$ for all $a ∈ M$. 
]

#definition()[
  An _additive action_ of a monoid $M$ on a set $X$ is a map $ 
  M times X ->  X, space (m, x) |->  m x 
  $ 
  such that the following hold:

  1. For all $x ∈ X$ we have $0 + x = x$.

  2. For all $m, n ∈ M$ and $x ∈ X$ we have $(m + n) x = m (n x)$. 
]


Let $M$ be an additive monoid acting on a compact topological space $X$. 

#definition()[
For any $x ∈ X$ define the _orbit_ of $x$ by $ 
cal(O)(x) := {m x | m ∈ M}. 
$ 
]

#definition()[
  $(X, M)$ is called _minimal_ if every orbit is dense.
]

#block[
#link("https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics/Minimal.html#AddAction.IsMinimal")[`Lean` implementation (`mathlib4`):]

```lean
class AddAction.IsMinimal (M α : Type*) [AddMonoid M] [TopologicalSpace α] [AddAction M α] :
    Prop where
  dense_orbit : ∀ x : α, Dense (AddAction.orbit M x)
```
]

#definition()[
We say that the action of $M$ on $X$ is _continuous_ if for every $m ∈ M$ the map 
$X -> X, space x |->  m x$ is continuous. 
]

= Existence of Minimal Subsystems

The goal of this section is to prove the following theorem:

#theorem()[
Let $M$ be an additive monoid acting continuously on a non-empty compact topological space $X$.
If $(M, X)$ is minimal then there exists a closed non-empty $Y subset.eq X$ such that $M Y subset.eq Y$
and the restricted action $ 
M times Y ->  Y, space (m, y) |->  m y  
$ 
is minimal.
]<thm-existence-minimal-subsystem>

#link_to_lean_implementation
```lean
theorem exists_minimal_invariant_subset {M X : Type*} [h_X_top : TopologicalSpace X] [h_X_compact : CompactSpace X] [h_X_nonempty : Nonempty X] [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X] :
   ∃ (Y : Set X) (h_SubAction : AddActionRestriction M X Y),
   have : AddAction M Y := h_SubAction.SubAction
   Y.Nonempty ∧
   IsClosed Y ∧
   AddAction.IsMinimal M Y
```

We start with a reformulation of the notion of a minimal system.

#proposition()[
Let $M$ be an additive monoid acting continuously on a topological space $X$. The following are equivalent:

- $(X, M)$ is minimal. 

- For every closed $M$-invariant subset $E subset.eq X$ we have $E = emptyset$ or $E = X$.
]<prop-minimal-equivalence>

Conveniently, this reformulation is already implemented in `lean`.

#block(breakable: false)[
#link("https://leanprover-community.github.io/mathlib4_docs/Mathlib/Dynamics/Minimal.html#isMinimal_iff_isClosed_vadd_invariant")[`Lean` implementation (`mathlib4`):]

```lean
theorem isMinimal_iff_isClosed_vadd_invariant (M : Type u_1) {α : Type u_3} [AddMonoid M] [TopologicalSpace α] [AddAction M α] [ContinuousConstVAdd M α] :
AddAction.IsMinimal M α ↔ ∀ (s : Set α), IsClosed s → (∀ (c : M), c +ᵥ s ⊆ s) → s = ∅ ∨ s = Set.univ
```
]


For the proof of @thm-existence-minimal-subsystem we need two more lemmas that are not yet implemented in `lean`. 


#lemma[
  Let $M$ be an additive monoid acting on a set $X$ and let $Y subset.eq X$ be an $M$-invariant subset,
  i.e. assume that $M Y subset.eq Y$. Then the restricted action $ 
  M times Y ->  Y, space (m, y) |->  m y 
  $ 
  is a well-defined additive action of $M$ on $Y$.
]<lemma-restricted-action>

#link_to_lean_implementation
```lean
class AddActionRestriction (M : Type*) (X : Type*) (Y : Set X) [AddMonoid M] [add_action_orig : AddAction M X] where
  SubAction : AddAction M Y
  SubAction_eq_Action : ∀ (c : M) (x : Y), ↑(c +ᵥ x) = add_action_orig.vadd c ↑x

def invariant_subset_restricted_action {M X : Type*} {Y : Set X} [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] (h_Y_invariant : ∀ c : M, ∀ y ∈ Y, c +ᵥ y ∈ Y) : AddActionRestriction M X Y 
```


#lemma[
  Let $M$ be an additive monoid acting continuously on a compact topological space $X$ 
  and let $Y subset.eq X$ be an $M$-invariant subset.
  Then the restricted action of $M$ on $Y$ is continuous.
]<lemma-restricted-action-cont>

#link_to_lean_implementation
```lean
class AddActionRestrictionContinuous (M X : Type*) (Y : Set X) [h_X_top : TopologicalSpace X]  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X] where
  (RestrictedAction : AddActionRestriction M X Y)
  (SubAction := RestrictedAction.SubAction)
  (SubActionContinuous : ContinuousConstVAdd M Y)

def restriction_of_continuous_action_is_continuous {M X : Type*} [h_X_top : TopologicalSpace X]  [h_M_monoid : AddMonoid M] [h_M_X_action : AddAction M X] [h_action_continuous : ContinuousConstVAdd M X] (Y : Set X) (h_Y_invariant : ∀ c : M, ∀ y ∈ Y, c +ᵥ y ∈ Y) : AddActionRestrictionContinuous M X Y 
```

Besides @lemma-restricted-action and @lemma-restricted-action-cont, we state some more general results that will be needed and that are already implemented in `lean`. 


#theorem("Zorn's lemma")[
Let $S$ be a set of subsets of a set $α$. 
Assume that for every chain
$C subset.eq S$ there exists an element $l ∈ S$ such that $ 
∀ s ∈ C: space  l subset.eq s. 
$ 
Then there exists an element $m ∈ S$ such that $ 
∀ a ∈ S: space a subset.eq m ==> a = m. 
$ 
]<thm-zorn-lemma>

#block(breakable: false)[
#link("https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Zorn.html#zorn_superset")[`Lean` implementation (`mathlib4`):]
```lean
theorem zorn_superset 
    {α : Type u_1} (S : Set (Set α)) 
    (h : ∀ c ⊆ S, IsChain (fun (x1 x2 : Set α) => x1 ⊆ x2) c 
          → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
  ∃ (m : Set α), Minimal (fun (x : Set α) => x ∈ S) m
```
]



#theorem("Cantor's intersection theorem")[
The intersection of a non-empty directed family of nonempty compact closed sets is nonempty.
]<thm-cantor-intersection>

#block(breakable: false)[
#link("https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Compactness/Compact.html#IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed")[`Lean` implementation (`mathlib4`):]
```lean
theorem IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
    {S : Set (Set X)} [hS : Nonempty S] (hSd : DirectedOn (· ⊇ ·) S) 
    (hSn : ∀ U ∈ S, U.Nonempty) (hSc : ∀ U ∈ S, IsCompact U) 
    (hScl : ∀ U ∈ S, IsClosed U) : 
    (⋂₀ S).Nonempty 
```
]





We now turn to the proof of our main theorem on the existence of minimal subsystems. 


#proof([of @thm-existence-minimal-subsystem])[
Let $M$ be an additive monoid acting on a non-empty compact topological space $X$ and 
assume that $(X, M)$ is minimal. Define the family $ 
S := { Y subset.eq X bar Y != emptyset, space  Y "closed", space  M Y subset.eq Y}. 
$ 
We want to apply Zorn's lemma to find a minimal element in $S$. 
Let $C subset.eq S$ be any chain.
Observe that if $C = emptyset$ then we can take $l := X$ and we are done. Hence we may assume that $C != emptyset$,
which is important to be able to apply @thm-cantor-intersection.
Now define $ 
l := inter.big_(Y ∈ C) Y subset.eq X . 
$ 
We verify that $l ∈ S$. 

- Since for all $Y ∈ C$ we have $Y subset.eq X$ we obtain $l subset.eq X$. 

- Since $l$ is an intersection of closed sets it is closed. 

- First observe that for every $Y ∈ C$ we have $Y ∈ S$ and thus $Y subset.eq X$ and $Y$ is closed 
  by definition of $S$. Since $X$ is compact this implies that $Y$ is compact. 
  Moreover, every $Y ∈ C$ is non-empty by definition of $S$.
  Hence by @thm-cantor-intersection we obtain $l != emptyset$. 

- Let $y ∈ l$ and $m ∈ M$ be arbitrary. Then we have $ 
∀ Y ∈ C: space  m y ∈ Y
$
  since $C subset.eq S$. This implies $ 
  m y ∈ inter.big_(Y ∈ C) Y = l.  
  $ 
  Since $y ∈ l$ and $m ∈ M$ were arbitrary we obtain $M l subset.eq l$.

This proves $l ∈ S$. Moreover, by definition of $l$ we have $ 
∀ Y ∈ C: space  l subset.eq Y. 
$ 
Hence by @thm-zorn-lemma there exists an element $Y ∈ S$ such that $ 
∀ Z ∈ S: space  Z subset.eq Y ==> Z = Y. #<eq-1>
$ 
Observe that by definition of $S$ we have $M Y subset.eq Y$ and thus by @lemma-restricted-action
the restricted action $ 
M times Y ->  Y, space (m, y) |->  m y
$
is well-defined. Moreover, since $M$ acts continuously on $X$, by @lemma-restricted-action-cont 
we obtain that the restricted action of $M$ on $Y$ is again continuous. 

We now show that $(Y, M)$ is minimal using @prop-minimal-equivalence. 
Let $E subset.eq Y$ be any closed subset with $M E subset.eq E$ and assume that $E != emptyset$. 
Then we have $E ∈ S$ by definition of $S$. Hence using @eq-1 we obtain $E = Y$. 
This proves that $(Y, M)$ is minimal by @prop-minimal-equivalence. 
]


The full `lean` implementation of @thm-existence-minimal-subsystem, including its proof, can be found on #link("https://github.com/ericceg/lean-theorem-minimal-subsystem/blob/master/Project/Theorem.lean")[`github.com/ericceg/lean-theorem-minimal-subsystem`].


