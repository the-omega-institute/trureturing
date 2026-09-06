# Odd-Prime Perfect One-Factorization

## Abstract

Kotzig's construction gives a perfect one-factorization of the complete graph on one point adjoining the residues modulo an odd prime.

**Definition 1.1 (Kotzig vertex type).**

$$\forall p \in \mathbb{N},\\{}\operatorname{Vertex}(p) := \operatorname{Option}(\operatorname{ZMod}(p)).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This repository formulation uses the classical Kotzig family as context. For a natural modulus p, the vertex type is exactly Option (ZMod p); the none vertex denotes the distinguished point at infinity.

**Definition 1.2 (Partner map in one factor).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p), x \in \operatorname{ZMod}(p),\\{}(\operatorname{partner}(a , none) = \operatorname{some}(a)) \land (\operatorname{partner}(a , \operatorname{some}(x)) = \operatorname{ite}(x = a , none , \operatorname{some}((2: \operatorname{ZMod}(p)) \cdot a - x))).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.partner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This repository definition formulates the partner map in the classical Kotzig family. The factor indexed by a pairs infinity with a. Every other finite vertex x is paired with 2a-x, while the finite vertex a is paired back with infinity. The displayed ite is the exact branch structure of the Lean definition.

**Definition 1.3 (Factor graph from the partner relation).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p),\\{}\operatorname{factor}(a) := \operatorname{SimpleGraph}.\operatorname{fromRel}((u, v: \operatorname{Vertex}(p) \mapsto v = \operatorname{partner}(a , u))).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.factor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This repository definition formulates the classical Kotzig factor graph as exactly SimpleGraph.fromRel applied to the relation v = partner(a,u). The orientation shown here matches the Lean defining expression; fromRel supplies symmetry and removes loops.

**Definition 1.4 (Union of two factors).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}\operatorname{pairGraph}(a , b) := \operatorname{sup}(\operatorname{factor}(a) , \operatorname{factor}(b)).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This repository definition uses the classical Kotzig family as context. The pair graph is the lattice supremum, equivalently the edge union, of the factors indexed by a and b.

**Definition 1.5 (Alternating-reflection translation step).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}\operatorname{translationStep}(a , b) := (2: \operatorname{ZMod}(p)) \cdot (b - a).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This repository definition records the translation used in its proof of the classical Kotzig family. Composing the two affine reflections gives displacement 2(b-a); in the partner graph that displacement is reached in one or two edges (the exceptional vertices are handled by a single edge).

**Theorem 1.6 (Owner of an edge incident to infinity).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}\forall a \in \operatorname{ZMod}(p), x \in \operatorname{ZMod}(p),\\{}(p \neq 2) \Rightarrow (\operatorname{Adj}(\operatorname{factor}(a) , none , \operatorname{some}(x)) \iff a = x).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.edge_owner_infinity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The edge from none to some x is in factor a exactly when a equals x.

**Theorem 1.7 (Owner of a finite edge).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}\forall a \in \operatorname{ZMod}(p), x \in \operatorname{ZMod}(p), y \in \operatorname{ZMod}(p),\\{}(p \neq 2 \land x \neq y) \Rightarrow (\operatorname{Adj}(\operatorname{factor}(a) , \operatorname{some}(x) , \operatorname{some}(y)) \iff a = \frac{(x + y)}{(2: \operatorname{ZMod}(p))}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.edge_owner_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct finite vertices x and y, the owner is their midpoint. The displayed fraction is field division in ZMod p, with denominator two coerced into that field; it is not natural-number division.

**Theorem 1.8 (Distinct factors have two neighbors at every vertex).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}\forall a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}(p \neq 2 \land a \neq b) \Rightarrow (\forall v \in \operatorname{Vertex}(p),\\{}\operatorname{ncard}(\operatorname{neighborSet}(\operatorname{pairGraph}(a , b) , v)) = 2).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph_two_regular` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This helper proof is repository work in the context of the classical Kotzig family. When a and b are distinct, the two partner vertices are distinct, so every neighbor set in pairGraph(a,b) has set cardinality two.

**Theorem 1.9 (The translation step has full additive order).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}\forall a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}(p \neq 2 \land a \neq b) \Rightarrow (\operatorname{addOrderOf}(\operatorname{translationStep}(a , b)) = p).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep_addOrderOf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This helper proof is repository work in the context of the classical Kotzig family. For distinct a and b and odd prime p, 2(b-a) is nonzero in ZMod p. Its additive order is therefore the prime p.

**Theorem 1.10 (Kotzig's odd-prime perfect one-factorization).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}(p \neq 2) \Rightarrow ((\forall a \in \operatorname{ZMod}(p), \operatorname{IsPerfectMatching}((\operatorname{Top}.\operatorname{top}: \operatorname{SimpleGraph}.\operatorname{Subgraph}(\operatorname{factor}(a))))) \land (\forall u \in \operatorname{Vertex}(p), v \in \operatorname{Vertex}(p),\\{}(u \neq v) \Rightarrow (\exists! a \in \operatorname{ZMod}(p), \operatorname{Adj}(\operatorname{factor}(a) , u , v))) \land (\forall a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}(a \neq b) \Rightarrow (\operatorname{IsHamiltonian}(\operatorname{pairGraph}(a , b))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.odd_prime_perfect_one_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The GK_{p+1} family is Kotzig's (1964); the explicit partner/ownership formulation and the proof for every odd prime, including p = 3, 5, 7, are repository work.

For every odd prime p, every factor is a perfect matching on Option (ZMod p), and every pair of distinct vertices belongs to exactly one indexed factor.

For distinct indices a and b, alternating the two partner reflections reaches x+2(b-a) from x in one or two edges. Since this nonzero translation generates additive ZMod p, the two-regular pair graph is connected; Mathlib's connected-cycle theorem then supplies a Hamiltonian cycle.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.Vertex`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.edge_owner_infinity`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.edge_owner_pair`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.factor`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.odd_prime_perfect_one_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph_two_regular`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.partner`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep_addOrderOf`
