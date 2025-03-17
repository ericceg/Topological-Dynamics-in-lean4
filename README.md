# Lean Proof on Minimal Subsystem

Recall the following definition.

**Definition 1.11.**
A homeomorphism $T:X \to X$ on a topological space is called *minimal* if every orbit is dense. 

We are trying to prove the following theorem in lean.

**Theorem 1.14.** 
Let $X$ be a non-empty compact metric space and $T: X \to X$
a homeomorphism. Then there exists a closed non-empty $Y \subseteq X$ such that 
$T Y = Y$ and $T|_Y: Y \to Y$ is minimal.