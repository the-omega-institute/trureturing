# Hanna's second congruence modulo five

## Abstract

Hanna's second congruence modulo five.

The natural-number sequence a and the predicate InA033042 are those of HannaA365771. InA033042 includes zero and means that every base-five digit is at most one. Division and subtraction use natural arithmetic. OEIS entries have no page numbers; the source is A365771 revision 23, Comments, and A033042, Name.

**Definition 1.1 (Hanna's second conjecture).**

$$claim \Leftrightarrow (\forall m \in \mathbb{N},\; (0 < m) \Rightarrow ((\operatorname{InA033042}\left(m\right)) \Rightarrow ((\operatorname{a}\left(5 \cdot m + 1\right)) \bmod 5 = 2)))$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA365771Two.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A365771: Catalan-binomial residues modulo five*. URL: <https://oeis.org/A365771>.

*Commentary.*

(2) a(5*A033042(n) + 1) == 2 (mod 5) for n > 0,

**Theorem 1.2 (Hanna's second congruence).**

$$\forall m \in \mathbb{N},\; (0 < m) \Rightarrow ((\operatorname{InA033042}\left(m\right)) \Rightarrow ((\operatorname{a}\left(5 \cdot m + 1\right)) \bmod 5 = 2))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaA365771Two.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A365771: Catalan-binomial residues modulo five*. URL: <https://oeis.org/A365771>.

*Commentary.*

The digits of 5*m+1 are one followed by the digits of m. The digit step therefore preserves membership in A033042, and the positive-index residue classification gives residue two.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaA365771Two.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA365771Two.result`
- Dependency: [D5/S1/Recurrence/Residue/HannaA365771](HannaA365771.md)
