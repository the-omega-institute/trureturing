# Galois Weight

## Abstract

Galois Weight

Galois acts on Hodge–Tate images of degree h through a cyclotomic power.

**Theorem 1.1 (hodgeTateMap_galois_twist).**

Lean statement: `D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GaloisWeight.hodgeTateMap_galois_twist`

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GaloisWeight.hodgeTateMap_galois_twist` (`✓ std3`). ∎

*Citation.* Levent Alpöge with Claude (2026). *The Generalized Riemann Hypothesis for Dirichlet L-functions, in Lean 4 (compact edition)*. URL: <https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/README.md>.

*Commentary.*

Let g ∈ G_p fix E, let t ∈ k equal χ(g⁻¹), and let x be a Hodge class over E with λ_h(x_k) = restrictToPairs ξ. Then t^h ξ and the pull-back of ξ along the g-twist of tests have the same image under restrictToPairs.

## References

- Truth anchor: `D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GaloisWeight.hodgeTateMap_galois_twist`
- Dependency: [D5/S3/Zeros/GRH/Lib/PadicComparison/HodgeTate/GaloisTwist](GaloisTwist.md)
