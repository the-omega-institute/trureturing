# Literal indicator restriction

## Abstract

Literal indicator restriction

**Definition 1.1 (Literal indicator restriction).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.restrict`

*Formalization.* `D5/S3/Topology/Measures/L1Restriction.restrict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every measurable set s with proof hs and every f in L1, restrict(s,hs,f) is MemLp.toLp of the actual function s.indicator(f). It uses the canonical strongly measurable representative of f.

**Theorem 1.2 (Actual representative identity).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.coe_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.coe_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every measurable s and f in L1, the coerced representative of restrict(s,hs,f) equals s.indicator(f) almost everywhere. This is equality of L1 classes of literal restrictions.

**Theorem 1.3 (Real norm of the literal restriction).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.norm_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.norm_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every measurable s and f in L1, the norm of restrict(s,hs,f) equals the real integral over s of the pointwise norm of f.

**Theorem 1.4 (Extended norm of the literal restriction).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.enorm_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.enorm_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every measurable s and f in L1, the extended norm of restrict(s,hs,f) equals the nonnegative extended integral over s of the pointwise extended norm of f.

**Theorem 1.5 (Exact complementary decomposition).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.add_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.add_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every measurable s and every f in L1, restrict(s,hs,f) plus restrict(s complement,hs.compl,f) equals f exactly in L1.

**Theorem 1.6 (Exact norm additivity).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.norm_add_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.norm_add_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every measurable s and f in real L1, the sum of the norms of its literal restrictions to s and its complement equals the norm of f. Signed inputs are allowed.

**Theorem 1.7 (Restriction decreases the norm).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.norm_le`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.norm_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every measurable s and f in L1, the norm of restrict(s,hs,f) is at most the norm of f.

**Theorem 1.8 (Norm monotonicity in the carrier).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.norm_mono`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.norm_mono` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For all measurable s and t with s contained in t and every f in L1, the norm of the literal restriction to s is at most the norm of the restriction to t.

**Definition 1.9 (Actual measurable hard-tail carrier).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.tailSet`

*Formalization.* `D5/S3/Topology/Measures/L1Restriction.tailSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every natural k and f in L1, tailSet(k,f) is exactly the set of x with the real cast of k at most the pointwise norm of the canonical representative of f.

**Theorem 1.10 (Measurability in the original sigma algebra).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.measurable_tailSet`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.measurable_tailSet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every natural k and f in L1, tailSet(k,f) is measurable in the original sigma algebra. No completion is introduced.

**Definition 1.11 (Real hard-tail mass).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.tailNorm`

*Formalization.* `D5/S3/Topology/Measures/L1Restriction.tailNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every natural k and f in L1, tailNorm(k,f) is the norm of the literal restriction of f to tailSet(k,f).

**Theorem 1.12 (Hard-tail masses decrease).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.tailNorm_antitone`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.tailNorm_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every f in L1, the function from natural k to tailNorm(k,f) is antitone.

**Theorem 1.13 (Exact nested-tail subtraction).**

Lean statement: `D5/S3/Topology/Measures/L1Restriction.tailNorm_compl`

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Measures/L1Restriction.tailNorm_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Omega be an arbitrary type with an arbitrary measurable space, and let mu be an arbitrary measure. L1 means the real space Lp Real 1 mu. For every f in L1 and natural thresholds 0 < k <= K, the k-tail mass of the literal restriction of f to the complement of tailSet(K,f) equals tailNorm(k,f) minus tailNorm(K,f). The positivity of k excludes zero values from the test tail. All integrals are finite before real subtraction.

## References

- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.add_compl`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.coe_restrict`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.enorm_restrict`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.measurable_tailSet`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.norm_add_compl`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.norm_le`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.norm_mono`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.norm_restrict`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.restrict`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.tailNorm`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.tailNorm_antitone`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.tailNorm_compl`
- Truth anchor: `D5/S3/Topology/Measures/L1Restriction.tailSet`
