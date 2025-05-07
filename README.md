# Lean Proof on Minimal Subsystem

Recall the following definition.

**Definition 1**
A homeomorphism $T:X \to X$ on a topological space is called *minimal* if every orbit is dense. 

We are trying to prove the following theorem in lean.

**Theorem 1** 
Let $X$ be a non-empty compact metric space and $T: X \to X$
a homeomorphism. Then there exists a closed non-empty $Y \subseteq X$ such that 
$T Y = Y$ and $T|_Y: Y \to Y$ is minimal.

**Definition 2**
Let $X$ be a topological space and $M$ be an additive monoid acting continuously on $X$ from the left. A point $x \in X$ is called strongly recurrent if:
$x \in \bigcap_{m \in M} \overline{\text{Orb}(m+x)}$. 

**Theorem 1.16.**
Let $X$ be a non-empty compact topological space acted on continuously by an additive monoid $M$ from the left. Then there exists a strongly recurrent point of $X$.
