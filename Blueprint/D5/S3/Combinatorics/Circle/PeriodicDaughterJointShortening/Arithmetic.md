# Arithmetic for the periodic daughter construction

## Abstract

Integer charge identities for the periodic daughter transport

This helper module gives the integer arithmetic used by the existing PeriodicDaughterJointShortening.Construction proof. The definitions name the old length, repeated seed, geometric scale factors and native digit phases; the theorems below are the exact source, centered-value and cross-modulus identities consumed by regular_block, top_block and daughter_order.

**Definition 1.1 (The shortened physical length).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.length`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.length` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

length d r is (d+1)*r-1, the old physical modulus length after one globally fresh daughter label is removed.

**Definition 1.2 (The repeated seed).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.seed`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.seed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

seed d w r is w multiplied by geom (d+1) r; Construction uses it as the old source and twice this value as the daughter source.

**Definition 1.3 (The daughter row base).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.q`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q d is the integer power 2^(d+1).

**Definition 1.4 (The old modulus parameter).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.n`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.n` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

n d is the integer 2^d-1, the old two-run modulus.

**Definition 1.5 (The lower geometric scale).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.H`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H d r is geom (d+1) (r-1), the scale of the complete lower old blocks.

**Definition 1.6 (The top geometric scale).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.R`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.R` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

R d r is q d raised to r-1, the scale of the shortened top block.

**Definition 1.7 (The daughter geometric scale).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.G`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G d r is geom (d+1) r, the scale of each complete daughter block.

**Definition 1.8 (The old actual modulus).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.N`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N d r is modulus (length d r), the actual integer modulus used by the old source.

**Definition 1.9 (The scalar arithmetic package).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.ScaleFacts`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.ScaleFacts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ScaleFacts d w r records the exact length, geometric, positivity, half-modulus, modulus, margin and daughter-capacity identities needed for the construction. Its fields include length_succ, q_eq, q_ge, H_ge, R_ge, G_ge, w_nonneg, w_bound, G_eq, modulus_eq, top_power, top_modulus, old_half, base_half, daughter_half, new_modulus, regular_margin, top_margin and daughter_margin.

**Theorem 1.10 (All scalar identities at the actual modulus).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.scale_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.scale_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 2≤d, w≤2^(d-1)-1 and 2≤r, scale_facts constructs ScaleFacts d w r. Construction uses this package in every regular, top and daughter block estimate.

**Definition 1.11 (The extended old phase).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.alpha`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.alpha` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

alpha d w i is the native actualSource d w digit at i when i<d and is w at the distinct final local-ear phase.

**Definition 1.12 (The extended native charge).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.e`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.e` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

e d w i is charge d w at old digits and w at the final local-ear phase.

**Definition 1.13 (The daughter phase).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.beta`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.beta` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

beta d w is actualSource (d+1) (2*w), the actual daughter phase function.

**Theorem 1.14 (Phase and charge identities).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_data`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For 2≤d, w≤2^(d-1)-1 and every i: e is nonnegative; alpha equals 2^i*w-n*e; beta equals 2*alpha-e; beta also equals 2^(i+1)*w-(q-1)*e; and beta lies between -n and n. Construction uses these bounds for all prefix and centered estimates.

**Theorem 1.15 (The fresh phase value).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_fresh`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_fresh` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the old dimension and width bounds, beta d w (Fin.last d)=w.

**Theorem 1.16 (The old phase cast).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every old digit i, beta d w i.castSucc = 2*actualSource d w i-charge d w i.

**Theorem 1.17 (The extended charge sum).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_charge_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_charge_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the old dimension and width bounds, the sum of e over Fin (d+1) is 2*w.

**Definition 1.18 (The nonnegative cross-modulus defect).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.defect`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.defect` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

defect d w j i is 2^(i+1)*w*geom (d+1) j+e d w i; it carries the integer discrepancy of a regular repeated block without division or parity choices.

**Definition 1.19 (The regular block value).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regularValue`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regularValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

regularValue d w r j i is 2^d*H*beta plus alpha plus 2^i*w*geom (d+1) j, with all factors at d,w,r.

**Definition 1.20 (The top block value).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.topValue`

*Formalization.* `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.topValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

topValue d w r i is R*actualSource d w i+H*beta d w i.castSucc.

**Theorem 1.21 (Defect positivity and total).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.defect_data`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.defect_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every phase i, defect is nonnegative, and its sum over Fin (d+1) is 2*w*q^j. Construction uses this exact total in regular_block.

**Theorem 1.22 (The regular doubled-value identity).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regular_double`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regular_double` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every regular block index j and phase i, 2*regularValue d w r j i = G*beta d w i+defect d w j i. Construction uses it to transfer the daughter prefix bounds to each old block.

**Theorem 1.23 (The actual regular source value).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regular_source`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regular_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j<r-1 and a valid physical label j*(d+1)+i.val below length d r, actualSource (length d r) (seed d w r) at that label equals regularValue d w r j i. Construction uses this live equality in regular_block.

**Theorem 1.24 (The actual top source value).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.top_source`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.top_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a valid top label (r-1)*(d+1)+i.val below length d r, actualSource at the repeated seed equals topValue d w r i. Construction uses this live equality in top_block.

**Theorem 1.25 (The actual periodic daughter source).**

Lean statement: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.daughter_source`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.daughter_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every daughter block j and phase i at a valid label below length d r+1, actualSource (length d r+1) (2*seed d w r) equals G*daughter phase beta d w i. Construction uses this live equality in daughter_order.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.G`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.H`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.N`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.R`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.ScaleFacts`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.alpha`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.beta`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.daughter_source`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.defect`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.defect_data`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.e`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.length`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.n`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_cast`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_charge_sum`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_data`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.phase_fresh`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.q`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regularValue`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regular_double`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.regular_source`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.scale_facts`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.seed`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.topValue`
- Truth anchor: `D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.top_source`
- Dependency: [D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic](../PeriodicShorteningArithmetic.md)
- Dependency: [D5/S3/Combinatorics/Circle/RunFirstEarTransport](../RunFirstEarTransport.md)
