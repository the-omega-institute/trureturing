# Finite Residue Sums for Dedekind Reciprocity

## Abstract

Coprime multiplication permutes the nonzero residues and preserves their exact rational sum.

The module first rewrites the frozen rational sawtooth by a natural remainder. It then evaluates the linear and square sums on the interval from one to c minus one and proves the residue permutation with Finset.sum_bij.

**Theorem 1.1 (Coprime multiplication preserves the nonzero-residue sum).**

$$\forall d, c\in \mathbb{N},\ c>0 \land \gcd(d, c)=1 \Rightarrow \sum_{k=1}^{c-1}[(kd) \operatorname{mod} c]_{\mathbb{Q}} = \frac{c(c-1)}{2}.$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/Interference/DedekindReciprocityFiniteSums.sum_mul_mod` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The supporting named results are sawtooth_div_eq_mod, dedekindSum_eq_mod_sum, sum_Ico_cast, sum_Ico_cast_sq, sum_mul_mod_permutation, and sum_mul_mod_sq.

## References

- Truth anchor: `D5/S1/Phase/Interference/DedekindReciprocityFiniteSums.sum_mul_mod`
- Dependency: [D5/S1/Phase/Interference/DedekindBhkCertificates](DedekindBhkCertificates.md)
