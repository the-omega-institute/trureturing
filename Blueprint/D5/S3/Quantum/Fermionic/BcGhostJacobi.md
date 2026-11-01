# Finite Witt Jacobi cancellation

## Abstract

Actual finite triple-c Witt cancellation

The formulas are the classical bc ghost BRST construction, with vacuum cuts b at minus one and c at two. See Kato and Ogawa, Nuclear Physics B 212 (1983), 443–460, and Polchinski, String Theory, volume 1, chapter 4. No novelty of these formulas is claimed. The formal carrier is the original complex finitely supported occupation space.

**Theorem 1.1 (Qg R).**

$$\forall r \in Int,\; \operatorname{Qg} \cdot \operatorname{R}\left(r\right) - \operatorname{R}\left(r\right) \cdot \operatorname{Qg} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/BcGhostJacobi.Qg_R` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the actual quadratic Ward operator gives two jointly finite triple-c sums. Cyclic permutations of three actual c modes have positive sign, including repeated indices. A bijection on the two free integer indices identifies all cyclic sums. The polynomial (a-b)(a+b-c) plus its two cyclic permutations is zero, so the full operator sum vanishes.

This is an algebraic ghost-sector construction. It supplies a dependency for the broader Monster, vertex algebra, conformal field theory and string programme. It does not establish the matter-tensor BRST charge, its cohomology, a no-ghost theorem, string dynamics or AdS/CFT.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/BcGhostJacobi.Qg_R`
- Dependency: [D5/S3/Quantum/Fermionic/BcGhostBRST](BcGhostBRST.md)
