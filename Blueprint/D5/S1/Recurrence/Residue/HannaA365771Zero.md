# Hanna's third congruence modulo five

## Abstract

Hanna's third congruence modulo five.

The natural-number sequence a and the predicate InA033042 are those of HannaA365771. InA033042 includes zero and means that every base-five digit is at most one. Division and subtraction use natural arithmetic. OEIS entries have no page numbers; the source is A365771 revision 23, Comments, and A033042, Name.

**Definition 1.1 (Hanna's third conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((\neg (\exists m \in \mathbb{N},\; (\operatorname{InA033042}\left(m\right)) \land ((n = 5 \cdot m) \lor (n - 1 = 5 \cdot m)))) \Rightarrow ((\operatorname{a}\left(n\right)) \bmod 5 = 0)))$$

*Formalization.* `D5/S1/Recurrence/Residue/HannaA365771Zero.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2023). *OEIS A365771: Catalan-binomial residues modulo five*. URL: <https://oeis.org/A365771>.

*Commentary.*

(3) a(n) == 0 (mod 5) for n > 0 except when n or n-1 equals 5*A033042(k) for some k >= 0.

**Theorem 1.2 (Hanna's third congruence).**

$$\forall n \in \mathbb{N},\; (0 < n) \Rightarrow ((\neg (\exists m \in \mathbb{N},\; (\operatorname{InA033042}\left(m\right)) \land ((n = 5 \cdot m) \lor (n - 1 = 5 \cdot m)))) \Rightarrow ((\operatorname{a}\left(n\right)) \bmod 5 = 0))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/HannaA365771Zero.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2023). *OEIS A365771: Catalan-binomial residues modulo five*. URL: <https://oeis.org/A365771>.

*Commentary.*

If every base-five digit of a positive n is zero or one, division by five gives a quotient m in A033042 and remainder zero or one. Thus n=5*m or n-1=5*m. Outside these two forms, the positive-index residue classification gives residue zero.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/HannaA365771Zero.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/HannaA365771Zero.result`
- Dependency: [D5/S1/Recurrence/Residue/HannaA365771](HannaA365771.md)
