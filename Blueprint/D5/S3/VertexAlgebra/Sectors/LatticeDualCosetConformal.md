# Original Conformal Action on Dual-Coset Modules

## Abstract

Original Conformal Action on Dual-Coset Modules

D has any finite rank, including zero. Its Gram matrix is integral, symmetric and even on the diagonal. beta is integral. moduleL(H,m) is defined to be the normalized coefficient m+1 of the ACTUAL action of the ORIGINAL omega_D(H). It is not defined from a shifted diagonal formula. Borcherds supplies separate finite supports. Normal-product sums are evaluated on each vector before they are split; no globally finite endomorphism normal sum is asserted. Energy covariance uses both original inverse-Gram equations H G=1 and G H=1 and applies to every original input state and integer mode.

Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.

**Definition 1.1 (moduleL).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.moduleL`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.moduleL` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L_m is exactly action_D,beta(omega_D(H)) at normalized mode m+1 on the actual full carrier.

**Definition 1.2 (commutatorTerm).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.commutatorTerm`

*Formalization.* `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.commutatorTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The j term is binom(p,j) times the module mode p+q-j of the ORIGINAL state product a_j b.

**Theorem 1.3 (commutator terms finite).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.commutator_terms_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.commutator_terms_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original nonnegative state products have finite support before binomial weighting. Their module endomorphism terms therefore have finite support even for negative p.

**Theorem 1.4 (mode commutator).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.mode_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.mode_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary original a,b and all integer p,q, the commutator of their actual module modes equals the finite sum of binomially weighted original state-product modes.

**Theorem 1.5 (one mode commutator).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.one_mode_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.one_mode_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The mode-one commutator contains exactly the original products a_0 b and a_1 b, with output modes q+1 and q.

**Theorem 1.6 (minus one product field).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.minus_one_product_field`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.minus_one_product_field` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual field of the original minus-one product equals the normal product of the actual module fields. The two separately finite vectorwise halves ADD.

**Theorem 1.7 (action current).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.action_current`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.action_current` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer m, the actual module current is the original neutral current plus beta_i delta(m,0) times identity.

**Theorem 1.8 (moduleL normal).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.moduleL_normal`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.moduleL_normal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual original omega mode is one half of the H-weighted sum of normal products of the actual module currents.

**Theorem 1.9 (energy covariance).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.energy_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.energy_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original state a and integer q, [L_0,action(a)_q]=action(L_0_original a)_q-(q+1)action(a)_q. The original two-sided inverse identities are explicit.

**Theorem 1.10 (ward commutator).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.ward_commutator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.ward_commutator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer conformal mode m and original input mode q, the full Ward sum retains all original L_(j-1) a terms with binomial(m+1,j). Finite original state-product support precedes binomial weighting.

**Theorem 1.11 (translation covariance).**

Lean statement: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.translation_covariance`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.translation_covariance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ACTUAL original-omega mode L_-1 satisfies [L_-1,action(a)_q]=-q action(a)_(q-1) for every original state a.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.action_current`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.commutatorTerm`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.commutator_terms_finite`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.energy_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.minus_one_product_field`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.mode_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.moduleL`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.moduleL_normal`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.one_mode_commutator`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.translation_covariance`
- Truth anchor: `D5/S3/VertexAlgebra/Sectors/LatticeDualCosetConformal.ward_commutator`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualLZeroGrading](../LatticeActualLZeroGrading.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraVirasoro](../LatticeSugawaraVirasoro.md)
- Dependency: [D5/S3/VertexAlgebra/Sectors/LatticeDualCosetModule](LatticeDualCosetModule.md)
