# Hanna's Cubed Sigma-Product Exponential

## Abstract

The cube has the characteristic-three coefficient pattern at every index.

**Definition 1.1 (The A382125 congruences).**

$$\operatorname{claim}\left(\right) \iff ((\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n, \operatorname{B}\left(\right)\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(n, \operatorname{A}\left(\right)\right) = (v: \mathbb{Q})) \land (u \equiv v \pmod{3}))) \land (\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n + 1, \operatorname{B}\left(\right)\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n + 2, \operatorname{B}\left(\right)\right) = (v: \mathbb{Q})) \land ((u \equiv 0 \pmod{3}) \land (v \equiv 0 \pmod{3})))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

Conjectures: a(3*n) == A382124(n) (mod 3) for n >= 0; a(3*n+1) == 0 (mod 3) and a(3*n+2) == 0 (mod 3) for n >= 0. OEIS A382125, COMMENT (unpaginated). A and B are the rational generating functions defined in HannaSigmaProductExpModThree; all coefficient witnesses are integers.

**Theorem 1.2 (All three coefficient classes).**

$$(\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n, \operatorname{B}\left(\right)\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(n, \operatorname{A}\left(\right)\right) = (v: \mathbb{Q})) \land (u \equiv v \pmod{3}))) \land (\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n + 1, \operatorname{B}\left(\right)\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n + 2, \operatorname{B}\left(\right)\right) = (v: \mathbb{Q})) \land ((u \equiv 0 \pmod{3}) \land (v \equiv 0 \pmod{3}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a382125-hanna-sigma-exponential-mod-three-cube` (proved) by `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a382125-hanna-sigma-exponential-mod-three-cube","declaration_gid":"D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382124 and A382125, sigma-product exponential series*. URL: <https://oeis.org/A382124>.

*Commentary.*

The first congruence is the symmetric A382124 congruence. The other two follow from the characteristic-three coefficient pattern of the integer lift cubed.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThreeCube.result`
- Dependency: [D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree](HannaSigmaProductExpModThree.md)
