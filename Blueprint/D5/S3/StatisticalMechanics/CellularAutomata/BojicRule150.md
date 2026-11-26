# The local semisimple-order LCM for Rule 150

## Abstract

For cyclic Rule 150 with admissible Mersenne odd part q, the LCM of the local semisimple orders on the nontrivial primary factors is q.

**Theorem 1.1 (The LCM is the Mersenne odd part).**

$$\forall k,m \in \mathbb{N}, \neg(3 \mid q) \implies \operatorname{lcm}_{f \in S_{q}} \operatorname{ord}(u_{k,m,f}) = q$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150.semisimpleOrder_lcm` (`✓ std3`). ∎

*Resolves.* `Problems/bojic-2026-rule-150-local-lcm` (proved) by `D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150.semisimpleOrder_lcm`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bojic-2026-rule-150-local-lcm","declaration_gid":"D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150.semisimpleOrder_lcm","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Ana Bojić (2026). *Semisimple–Unipotent Decomposition and the Exact Order of a Linear Cellular Automaton over F2*. DOI: [10.48550/arXiv.2611.33216](https://doi.org/10.48550/arXiv.2611.33216). URL: <https://arxiv.org/abs/2611.33216v1>.

*Commentary.*

For natural numbers k and m, set q = 2^k − 1 and assume that 3 does not divide q. This forces k to be positive, since 3 divides 0. Put n = 2^m q. For each distinct monic irreducible factor f of X^q − 1 over F₂ besides X + 1, take the class of G = 1 + X + X^(n − 1) in F₂[X]/(f^(2^m)). The formula uses S_q for this set of factors and u_(k,m,f) for the odd-order semisimple part of the class indexed by f. At k = 1, q = 1 and the index set is empty. Its LCM is 1.

Section 2.3 leaves this identity open. Theorem 8.8 describes the semisimple part, and Theorem 8.19 uses the local odd orders in the global period formula for q > 1. The formal construction takes the power G^((2^k)^m) in each primary quotient. It is the unique odd-order unit whose product with a cofactor 1 + ν gives the local multiplier, where ν is nilpotent and reduces to zero modulo f. Its order equals the order of G modulo f.

Frobenius gives q as a common exponent in the residue fields. If d is the LCM of the residue orders, then X^q − 1 divides (1 + X + X²)^d − X^d. The nonzero polynomial on the right has degree at most 2d. Thus q ≤ 2d, and q/d is an odd integer, so d = q.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CellularAutomata/BojicRule150.semisimpleOrder_lcm`
