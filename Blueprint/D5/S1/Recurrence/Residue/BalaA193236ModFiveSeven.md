# OEIS A193236: congruences modulo five and seven

## Abstract

Bala's unbounded modulo-five and modulo-seven coefficient congruences.

All indices are natural numbers. Nat.div is natural-number division. The finite coefficient sum expresses the infinite triangular series: j*(j+1)/2=m implies j≤m. PowerSeries coefficients are rational unless stated otherwise.

**Definition 1.1 (The source series).**

$$F = \operatorname{PowerSeries}.\operatorname{mk}\left((\lambda (m: \mathbb{N}) \mapsto \sum_{j \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} \operatorname{if} \operatorname{Nat}.\operatorname{div}\left(j \cdot \left(j + 1\right), 2\right) = m \operatorname{then} ((-3: \mathbb{Q}))^{j} \cdot (2 \cdot j + 1: \mathbb{Q}) \operatorname{else} 0)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.F` (`✓ std3`).

*Citation.* Peter Bala; Paul D. Hanna (2021). *OEIS A193237 and A193236, congruences for triangular reciprocal cube roots*. URL: <https://oeis.org/A193237/internal>.

*Commentary.*

Expansion of g.f.: ( Sum_{n>=0} (-3)^n*(2*n+1)*x^(n*(n+1)/2) )^(-1/3). OEIS A193236, NAME line (unnumbered web entry; no page number). The coefficient at degree m sums exactly the terms of triangular degree m.

**Definition 1.2 (The normalized reciprocal cube root).**

$$\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsGF}\left(A\right) = \left((\operatorname{constantCoeff}\left(A\right) = 1) \land ((A)^{3} \cdot F = 1)\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.IsGF` (`✓ std3`).

*Citation.* Peter Bala; Paul D. Hanna (2021). *OEIS A193237 and A193236, congruences for triangular reciprocal cube roots*. URL: <https://oeis.org/A193237/internal>.

*Commentary.*

The source's constant-one expansion means constantCoeff(A)=1 and A^3*F=1.

**Definition 1.3 (Bala's two conjectures).**

$$claim = \left((\exists (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), \operatorname{IsGF}\left(A\right)) \land (\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{IsGF}\left(A\right)) \Rightarrow (\exists (a: \mathbb{N} \to \mathbb{Z}), (\forall (m: \mathbb{N}), \operatorname{coeff}\left(m, A\right) = (a\left(m\right): \mathbb{Q})) \land (\forall (n: \mathbb{N}), ((5: \mathbb{Z}) \mid a\left(5 \cdot n + 4\right)) \land ((7: \mathbb{Z}) \mid a\left(7 \cdot n + 5\right)))))\right)$$

*Formalization.* `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.claim` (`✓ std3`).

*Citation.* Peter Bala; Paul D. Hanna (2021). *OEIS A193237 and A193236, congruences for triangular reciprocal cube roots*. URL: <https://oeis.org/A193237/internal>.

*Commentary.*

Conjectures: a(5*n+4) == 0 (mod 5) and a(7*n+5) == 0 (mod 7) (both checked up to n = 200). - _Peter Bala_, Feb 26 2021 OEIS A193236, FORMULA line (unnumbered web entry; no page number). The statement asserts existence and covers every normalized rational solution, an integer coefficient sequence, both primes, and every natural index.

**Theorem 1.4 (Both unbounded congruences).**

$$(\exists (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), (\operatorname{constantCoeff}\left(A\right) = 1) \land ((A)^{3} \cdot F = 1)) \land (\forall (A: \operatorname{PowerSeries}\left(\mathbb{Q}\right)), ((\operatorname{constantCoeff}\left(A\right) = 1) \land ((A)^{3} \cdot F = 1)) \Rightarrow (\exists (a: \mathbb{N} \to \mathbb{Z}), (\forall (m: \mathbb{N}), \operatorname{coeff}\left(m, A\right) = (a\left(m\right): \mathbb{Q})) \land (\forall (n: \mathbb{N}), ((5: \mathbb{Z}) \mid a\left(5 \cdot n + 4\right)) \land ((7: \mathbb{Z}) \mid a\left(7 \cdot n + 5\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.result` (`✓ std3`). ∎

*Resolves.* `Problems/bala193236` (proved) by `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bala193236","declaration_gid":"D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Peter Bala; Paul D. Hanna (2021). *OEIS A193237 and A193236, congruences for triangular reciprocal cube roots*. URL: <https://oeis.org/A193237/internal>.

*Commentary.*

The positive-degree coefficients of F are multiples of nine. Coefficient contraction constructs an integral cube root of F, whose inverse is integral. Modulo five the triangular series is supported in residues 0 and 1, so its cube misses residue 4. Modulo seven it is supported in residues 0, 1 and 3, so its square misses residue 5. Frobenius transfers these missing residues to the reciprocal cube root. Uniqueness identifies every normalized rational solution.

## References

- Truth anchor: `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.F`
- Truth anchor: `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.IsGF`
- Truth anchor: `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.claim`
- Truth anchor: `D5/S1/Recurrence/Residue/BalaA193236ModFiveSeven.result`
- Dependency: [D5/S1/Recurrence/Residue/BalaA193237ModFiveSeven](BalaA193237ModFiveSeven.md)
