# Quantitative deficient cores with large prime factors

## Abstract

Deficient prime products attain each sufficiently large exponential threshold.

**Theorem 1.1 (Exponential threshold control at quadratic logarithmic cost).**

Lean statement: `D5/S3/Arith/Abundancy/ZelinskyDeficientCore.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Abundancy/ZelinskyDeficientCore.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Joshua Zelinsky (2026). *Must a Primitive Non-Deficient Number Always Have a Small Component?*. DOI: [10.48550/arXiv.2005.12115](https://doi.org/10.48550/arXiv.2005.12115). URL: <https://arxiv.org/abs/2005.12115v5>.

*Commentary.*

Fix any natural cutoff B. There are constants K>0 and T such that for every real t at least T there is a finite set S of primes exceeding B. Put h=product over p in S of (1+1/p) and a=h/(2-h). Then h<2, exp(t)<=a<=3*exp(t), every p in S is less than 2a, and the sum of log(p) over S is at most K*t^2. Distinctness of the prime factors makes their product squarefree, and its abundancy ratio is h.

Divergence of the reciprocal-prime sum supplies a finite prime product with h at least 2. A minimal crossing set, with its largest prime removed, gives a deficient starting core whose threshold parameter exceeds its prime factors.

For a large current parameter a, choose a prime p in (2a,3a]. Adjoining p keeps the core deficient and replaces a by a*(p+1)/(p-a), which lies between 3a/2 and 3a. All old and new prime factors remain below twice the new parameter. The first iteration to reach exp(t) therefore has parameter at most 3*exp(t). The number of iterations is linear in t, and each added prime has logarithm bounded linearly in that iteration's index, giving the quadratic total cost.

The construction supports the primitive non-deficient counting lower bound associated with Zelinsky's Conjectures 11, 13 and 15 in section 3 of arXiv:2005.12115v5 and https://github.com/the-omega-institute/trureturing/issues/31919.

## References

- Truth anchor: `D5/S3/Arith/Abundancy/ZelinskyDeficientCore.result`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/FixedLayerRigidity](../Robin/PriceRecord/FixedLayerRigidity.md)
