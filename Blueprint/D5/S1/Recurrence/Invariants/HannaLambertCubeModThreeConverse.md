# Hanna's A382319 Congruence Modulo Three

## Abstract

The A382319 coefficient at n and the A382318 coefficient at 3n have the same residue modulo three.

PowerSeries.coeff extracts rational coefficients. Integer values are cast to the rationals in coefficient equalities. Int.ModEq(3,u,v) expresses equality of integer residues modulo three. The predicates IsA382318 and IsA382319 are those of HannaLambertCubeModThree.

**Definition 1.1 (The coefficient congruence).**

$$\operatorname{claim} = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \exists B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382318}\left(A\right)) \land (\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382319}\left(B\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382318}\left(A\right)) \implies ((\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382319}\left(B\right)) \implies (\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(n, B\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n, A\right) = (v: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, u, v\right)))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382319, g.f. A(x) satisfies A(x) = x/(1-x) + Sum_{n>=1} A(x^n)^3*. URL: <https://oeis.org/A382319>.

*Commentary.*

OEIS A382319, Comments (unpaginated): "Conjecture: a(n) == A382318(3*n) (mod 3) for n >= 0." Here A is the A382318 series and B is the A382319 series. Both solutions exist, and every such pair satisfies the displayed integer congruence for every natural n, including zero.

**Theorem 1.2 (The congruence holds).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \exists B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382318}\left(A\right)) \land (\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382319}\left(B\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382318}\left(A\right)) \implies ((\operatorname{HannaLambertCubeModThree}.\operatorname{IsA382319}\left(B\right)) \implies (\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(n, B\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n, A\right) = (v: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, u, v\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.result` (`✓ std3`). ∎

*Resolves.* `Problems/hanna-a382319-a382318-lambert-cube-mod-three` (proved) by `D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hanna-a382319-a382318-lambert-cube-mod-three","declaration_gid":"D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382319, g.f. A(x) satisfies A(x) = x/(1-x) + Sum_{n>=1} A(x^n)^3*. URL: <https://oeis.org/A382319>.

*Commentary.*

Apply the first coefficient congruence of HannaLambertCubeModThree.result and symmetry of Int.ModEq. The existence assertion is the same one.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLambertCubeModThreeConverse.result`
- Dependency: [D5/S1/Recurrence/Invariants/HannaLambertCubeModThree](HannaLambertCubeModThree.md)
