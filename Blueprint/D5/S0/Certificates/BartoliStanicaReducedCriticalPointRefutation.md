# Bartoli--Stănică Conjecture 2: reduced APN critical points

## Abstract

A fixed reduced polynomial over F32 refutes the reduced critical-point conjecture.

Bartoli and Stănică, Reduced polynomial lifts of APN permutations over Galois rings and effective non-APN bounds, arXiv:2608.30808v1 (31 August 2026), Conjecture 2 states: For every q = 2^m, the reduced representative f in F_(q)[x] of every APN permutation of F_(q) has a critical point in F_(q). The reduced representative means degree strictly less than q; the critical point is a finite rational a with the formal derivative f' evaluated at a equal to zero. This record keeps the universal quantifiers and does not use an unnormalized lift or an affine-invariance claim.

**Definition 1.1 (Directional differential fiber size).**

Lean statement: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.differentialFiberSize`

*Formalization.* `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.differentialFiberSize` (`✓ std3`).

*Citation.* Daniele Bartoli; Pantelimon Stănică (2026). *Reduced polynomial lifts of APN permutations over Galois rings and effective non-APN bounds*. URL: <https://arxiv.org/abs/2608.30808>.

*Commentary.*

For a finite field K and Polynomial f, this is the cardinality of the fiber of x ↦ f(x+a)+f(x) at target b.

**Definition 1.2 (Exact APN condition).**

Lean statement: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.exactAPN`

*Formalization.* `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.exactAPN` (`✓ std3`).

*Citation.* Daniele Bartoli; Pantelimon Stănică (2026). *Reduced polynomial lifts of APN permutations over Galois rings and effective non-APN bounds*. URL: <https://arxiv.org/abs/2608.30808>.

*Commentary.*

The predicate requires every nonzero direction and every target to have a differential fiber of size at most two, together with one nonzero-direction target attaining size two.

**Definition 1.3 (The reduced critical-point conjecture).**

Lean statement: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.claim`

*Formalization.* `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.claim` (`✓ std3`).

*Citation.* Daniele Bartoli; Pantelimon Stănică (2026). *Reduced polynomial lifts of APN permutations over Galois rings and effective non-APN bounds*. URL: <https://arxiv.org/abs/2608.30808>.

*Commentary.*

For every m > 0, every finite characteristic-two field K with cardinality 2^m, and every Polynomial f over K of degree less than 2^m whose evaluation is bijective and whose exact APN predicate holds, the same field contains a with f.derivative.eval a = 0. The Lean definition uses the same polynomial in all hypotheses and in the derivative conclusion.

**Theorem 1.4 (The F32 reduced polynomial has no critical point).**

Lean statement: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniele Bartoli; Pantelimon Stănică (2026). *Reduced polynomial lifts of APN permutations over Galois rings and effective non-APN bounds*. URL: <https://arxiv.org/abs/2608.30808>.

*Commentary.*

The theorem is a direct negation of the universal claim. Its live proof constructs the actual field with 32 elements and characteristic two from five-bit vectors reduced by t^5+t^2+1, then defines one degree-24 polynomial with the 16 supplied nonzero coefficients. Kernel computation checks all 32 evaluations, the evaluation bijection, all 31 × 32 nonzero-direction/target fibers, and the exact size-two fiber at direction label 1 and target label 16 with points 24 and 25.

The same polynomial has nowhere-zero formal derivative on all 32 field elements. The degree bound is the reduced representative condition. Labels are binary vectors in the field model, not natural-number casts or ZMod 32. The result uses only propext, Classical.choice and Quot.sound in its axiom closure. This is a fixed finite refutation and makes no global priority claim.

## References

- Truth anchor: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.claim`
- Truth anchor: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.differentialFiberSize`
- Truth anchor: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.exactAPN`
- Truth anchor: `D5/S0/Certificates/BartoliStanicaReducedCriticalPointRefutation.result`
