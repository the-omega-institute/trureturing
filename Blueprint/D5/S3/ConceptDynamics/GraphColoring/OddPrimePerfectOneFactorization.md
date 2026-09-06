# Odd-Prime Perfect One-Factorization

## Abstract

Kotzig's construction gives a perfect one-factorization of the complete graph on one point adjoining the residues modulo an odd prime.

**Definition 1.1 (Kotzig vertex type).**

$$\forall p \in \mathbb{N},\\{}\operatorname{Vertex}(p) := \operatorname{Option}(\operatorname{ZMod}(p)).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.Vertex` (`✓ std3`).

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

For a natural modulus p, the vertex type is exactly Option (ZMod p); the none vertex denotes the distinguished point at infinity.

**Definition 1.2 (Partner map in one factor).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p), x \in \operatorname{ZMod}(p),\\{}(\operatorname{partner}(a , none) = \operatorname{some}(a)) \land (\operatorname{partner}(a , \operatorname{some}(x)) = \operatorname{ite}(x = a , none , \operatorname{some}((2: \operatorname{ZMod}(p)) \cdot a - x))).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.partner` (`✓ std3`).

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

The factor indexed by a pairs infinity with a. Every other finite vertex x is paired with 2a-x, while the finite vertex a is paired back with infinity. The displayed ite is the exact branch structure of the Lean definition.

**Definition 1.3 (Factor graph from the partner relation).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p),\\{}\operatorname{factor}(a) := \operatorname{SimpleGraph}.\operatorname{fromRel}((u, v: \operatorname{Vertex}(p) \mapsto v = \operatorname{partner}(a , u))).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.factor` (`✓ std3`).

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

The factor graph is exactly SimpleGraph.fromRel applied to the relation v = partner(a,u). The orientation shown here matches the Lean defining expression; fromRel supplies symmetry and removes loops.

**Definition 1.4 (Union of two factors).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}\operatorname{pairGraph}(a , b) := \operatorname{sup}(\operatorname{factor}(a) , \operatorname{factor}(b)).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph` (`✓ std3`).

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

The pair graph is the lattice supremum, equivalently the edge union, of the factors indexed by a and b.

**Definition 1.5 (Alternating-reflection translation step).**

$$\forall p \in \mathbb{N}, a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}\operatorname{translationStep}(a , b) := (2: \operatorname{ZMod}(p)) \cdot (b - a).$$

*Formalization.* `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep` (`✓ std3`).

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

Two alternating partner reflections translate a finite residue by exactly 2(b-a) in ZMod p.

**Theorem 1.6 (Distinct factors have two neighbors at every vertex).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}\forall a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}(p \neq 2 \land a \neq b) \Rightarrow (\forall v \in \operatorname{Vertex}(p),\\{}\operatorname{ncard}(\operatorname{neighborSet}(\operatorname{pairGraph}(a , b) , v)) = 2).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph_two_regular` (`✓ std3`). ∎

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

When a and b are distinct, the two partner vertices are distinct, so every neighbor set in pairGraph(a,b) has set cardinality two.

**Theorem 1.7 (The translation step has full additive order).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}\forall a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}(p \neq 2 \land a \neq b) \Rightarrow (\operatorname{addOrderOf}(\operatorname{translationStep}(a , b)) = p).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep_addOrderOf` (`✓ std3`). ∎

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

For distinct a and b and odd prime p, 2(b-a) is nonzero in ZMod p. Its additive order is therefore the prime p.

**Theorem 1.8 (Kotzig's odd-prime perfect one-factorization).**

$$\forall p \in \mathbb{N},\\{}[\operatorname{Fact}(\operatorname{Prime}(p))],\\{}(p \neq 2) \Rightarrow ((\forall a \in \operatorname{ZMod}(p), \operatorname{IsPerfectMatching}(\operatorname{topSubgraph}(\operatorname{factor}(a)))) \land (\forall u \in \operatorname{Vertex}(p), v \in \operatorname{Vertex}(p),\\{}(u \neq v) \Rightarrow (\exists! a \in \operatorname{ZMod}(p), \operatorname{Adj}(\operatorname{factor}(a) , u , v))) \land (\forall a \in \operatorname{ZMod}(p), b \in \operatorname{ZMod}(p),\\{}(a \neq b) \Rightarrow (\operatorname{IsHamiltonian}(\operatorname{pairGraph}(a , b))))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.odd_prime_perfect_one_factorization` (`✓ std3`). ∎

*Citation.* Jack Allsop and Ian M. Wanless (2025). *Perfect 1-factorisations of K_{11,11}*. DOI: [10.48550/arXiv.2506.02455](https://doi.org/10.48550/arXiv.2506.02455).

*Commentary.*

Kotzig (1964); literature attestation via Allsop–Wanless, arXiv:2506.02455.

For every odd prime p, every factor is a perfect matching on Option (ZMod p), and every pair of distinct vertices belongs to exactly one indexed factor.

For distinct indices a and b, alternating the two partner reflections reaches x+2(b-a) from x in one or two edges. Since this nonzero translation generates additive ZMod p, the two-regular pair graph is connected; Mathlib's connected-cycle theorem then supplies a Hamiltonian cycle.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.Vertex`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.factor`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.odd_prime_perfect_one_factorization`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.pairGraph_two_regular`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.partner`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep`
- Truth anchor: `D5/S3/ConceptDynamics/GraphColoring/OddPrimePerfectOneFactorization.translationStep_addOrderOf`
