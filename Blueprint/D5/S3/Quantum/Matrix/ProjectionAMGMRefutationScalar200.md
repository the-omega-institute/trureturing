# Scalar coordinate-descent projection AM-GM counterexample

## Abstract

An actual real unit-column basis at n=200 refutes the all-order scalar first-moment projection comparison.

**Definition 1.1 (Reuse the existing arithmetic mean).**

$$meanProj = \operatorname{ProjectionAMGMRefutation.meanProj}$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.meanProj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Acknowledgement.* D. Kim; J. Lee; C. Yun (2025). *Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent*. DOI: [10.48550/arXiv.2505.23152](https://doi.org/10.48550/arXiv.2505.23152). URL: <https://arxiv.org/abs/2505.23152v1>.

*Commentary.*

This abbreviation directly consumes ProjectionAMGMRefutation.meanProj; it introduces no different normalization or assertion.

**Definition 1.2 (Reuse the complete reversed-word average).**

$$symProd = \operatorname{ProjectionAMGMRefutation.symProd}$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.symProd` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Acknowledgement.* D. Kim; J. Lee; C. Yun (2025). *Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent*. DOI: [10.48550/arXiv.2505.23152](https://doi.org/10.48550/arXiv.2505.23152). URL: <https://arxiv.org/abs/2505.23152v1>.

*Commentary.*

This abbreviation directly consumes ProjectionAMGMRefutation.symProd: inverse n factorial times the sum over all labelled permutations, with the first entry rightmost.

**Definition 1.3 (Real unit independent coordinate columns).**

$$\forall (n:\mathbb{N}), \forall (a:Fin\left(n\right)\to Fin\left(n\right)\to \mathbb{R}), (IsCDFamily\left(a\right)) \Leftrightarrow ((\forall (i:Fin\left(n\right)), dotProduct\left(a(i), a(i)\right) = 1) \land (LinearIndependent\left(\mathbb{R}, a\right)))$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.IsCDFamily` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Acknowledgement.* D. Kim; J. Lee; C. Yun (2025). *Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent*. DOI: [10.48550/arXiv.2505.23152](https://doi.org/10.48550/arXiv.2505.23152). URL: <https://arxiv.org/abs/2505.23152v1>.

*Commentary.*

The columns are unit vectors and linearly independent in the full real n-dimensional space. At positive n this is an actual square basis; neither a dependent family nor mutual orthogonality is substituted.

**Definition 1.4 (Complement projection of a coordinate column).**

$$\forall (n:\mathbb{N}), \forall (a:Fin\left(n\right)\to Fin\left(n\right)\to \mathbb{R}), \forall (i:Fin\left(n\right)), cdProj\left(a, i\right) = 1 - \operatorname{Matrix.vecMulVec}\left(a(i), a(i)\right)$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.cdProj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Acknowledgement.* D. Kim; J. Lee; C. Yun (2025). *Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent*. DOI: [10.48550/arXiv.2505.23152](https://doi.org/10.48550/arXiv.2505.23152). URL: <https://arxiv.org/abs/2505.23152v1>.

*Commentary.*

The scalar block specialization d_i=1 of SLY Claim 4.1 uses I-a_i a_i^T. Unit length makes each complement a self-adjoint idempotent contraction. Claim 4.1 itself states identities and is not refuted.

**Definition 1.5 (The complete all-order scalar assertion).**

$$(claimScalar) \Leftrightarrow (\forall (n:\mathbb{N}), \forall (a:Fin\left(n\right)\to Fin\left(n\right)\to \mathbb{R}), (1 \le n) \Rightarrow ((IsCDFamily\left(a\right)) \Rightarrow (\operatorname{Matrix.PosSemidef}\left((meanProj\left(fun (i:Fin\left(n\right)) \mapsto cdProj\left(a, i\right)\right))^{n} - symProd\left(fun (i:Fin\left(n\right)) \mapsto cdProj\left(a, i\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.claimScalar` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Acknowledgement.* D. Kim; J. Lee; C. Yun (2025). *Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent*. DOI: [10.48550/arXiv.2505.23152](https://doi.org/10.48550/arXiv.2505.23152). URL: <https://arxiv.org/abs/2505.23152v1>.

*Commentary.*

For every positive n and every real unit independent family in R^n, the arithmetic mean raised to n minus the complete n! reversed-word average is positive semidefinite. This is the scalar specialization of SLY arXiv:1503.06387v3 Conjecture 3.1/(37) in its coordinate-descent application, and the structured first-moment comparison named original matrix AM-GM in KLY arXiv:2505.23152v1 Appendix E.2 under Assumption 2.2. No dimension cap, permutation sample, conditioning restriction or second-moment target is added.

**Theorem 1.6 (A finite basis gives a strict negative quadratic form).**

$$\neg claimScalar$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Sun; Z.-Q. Luo; Y. Ye (2020). *On the efficiency of random permutation for ADMM and coordinate descent*. DOI: [10.1287/moor.2019.0990](https://doi.org/10.1287/moor.2019.0990). URL: <https://arxiv.org/abs/1503.06387v3>.

*Acknowledgement.* D. Kim; J. Lee; C. Yun (2025). *Provable Benefit of Random Permutations over Uniform Sampling in Stochastic Coordinate Descent*. DOI: [10.48550/arXiv.2505.23152](https://doi.org/10.48550/arXiv.2505.23152). URL: <https://arxiv.org/abs/2505.23152v1>.

*Commentary.*

The supplied proof uses n=N=200, K=10^9, s=sqrt(K^2+1), a0=e1, ai=(K e1+e(i+1))/s for 1<=i<=198, a199=(e0-e1)/sqrt(2), and z=e0+200e1. It proves unit length and linear independence at this finite K, bounds the full difference against an auxiliary 199P+Q family, and proves z^T(M^200-G)z < -3/32+15840396/1000000000 < -1/16 < 0. The dependent family is only a comparison. This closed theorem has the literal type Not claimScalar.

Existing-owner integration: the sole OpenProblemResolutionClaim remains on ProjectionAMGMRefutation.result for sun-luo-ye-2020-projection-matrix-amgm, with this result as an additional member. This document creates no second claim. Admission basis is open-problem-resolution under the original all-n Tier 1 registration #17674 (2026-10-16T05:39:52Z). Its scoped status evidence is contextual namedness plus the preserved exact-claim literature screen, not the already-refuted unrestricted conjecture's former status.

The ended source review was quality approve, tests approve, architecture comment. The architecture concern about exact named-assertion status remains disclosed: no inspected passage independently labels this precise restriction a still-open conjecture. This author's existing-owner interpretation uses the named KLY first-moment display, SLY's explicit application and the original registration together; later independent complete admission review remains required. The historical proof-shape disagreement is not adjudicated here; declaration-level author accounting and actual consumers are recorded in the existing Problems dossier.

Only the scalar projection endpoint is formalized. Taking d_i=1 directly supplies ordinary SLY source specialization. The conventional symmetric positive square root gives an ordinary orthogonal-conjugacy correspondence with SPD unit-diagonal Hessians; no formal Hessian, full-block or update-transport endpoint is claimed. KLY does not separately specify its square-root choice in the inspected passages. Its later Appendix E.2 future work concerns second moments.

Evidence and literature limits: the proof source is reused verbatim, SHA-256 1067ac81d5cb1acca53faf795d906c6d832b55ab7c16c3890f44a6c143ca15ec. Historical private native evidence is not current acceptance. SLY journal text, numbering and arXiv equivalence and KLY conference equality remain unverified; Luenberger-Ye Chapter 14 full text remains unread. The inherited 37-retrieval and 41/33-row citation screens are incomplete, some records were metadata-only, and failed web access supplies no negative evidence. No global absence, priority, novelty, smallest dimension, optimal RP-CD rate, expected-inverse or second-moment settlement is claimed. Full current source-bound normal acceptance, independent review and final-head CI remain separate obligations.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.IsCDFamily`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.cdProj`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.claimScalar`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.meanProj`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.result`
- Truth anchor: `D5/S3/Quantum/Matrix/ProjectionAMGMRefutationScalar200.symProd`
- Dependency: [D5/S3/Quantum/Matrix/ProjectionAMGMRefutation](ProjectionAMGMRefutation.md)
