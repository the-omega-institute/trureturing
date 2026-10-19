# Hanna's Lambert-Cube Congruences Modulo Three

## Abstract

The Lambert transform connects Hanna's two cubic equations; cubic Frobenius gives their coefficient congruences modulo three.

The series have rational coefficients and constant coefficient zero. PowerSeries.coeff extracts a coefficient, X is the indeterminate, and Nat.div is Euclidean division on natural numbers. Integer coefficients are cast to the rationals in coefficient equalities. Int.ModEq(3,u,v) means that u and v have the same residue modulo three.

**Definition 1.1 (The coefficientwise Lambert sum).**

$$\forall F: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{lambertSum}\left(F\right) = \operatorname{mk}\left((m: \mathbb{N} \mapsto \sum_{n \in \operatorname{Finset}.\operatorname{Icc}\left(1, m\right)} \operatorname{ite}\left(n \mid m, \operatorname{coeff}\left(\operatorname{Nat}.\operatorname{div}\left(m, n\right), F\right), 0\right))\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.lambertSum` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382318, g.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3*. URL: <https://oeis.org/A382318>.

*Commentary.*

For a series F with constant coefficient zero, Sum_{n>=1} F(x^n) has at degree m the sum of coeff(m/n,F) over positive divisors n of m. The empty sum at m=0 is zero; each other coefficient is a finite sum.

**Definition 1.2 (The A382318 equation).**

$$\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsA382318}\left(A\right) = ((\operatorname{constantCoeff}\left(A\right) = 0) \land (A = X + \operatorname{lambertSum}\left(A\right)^{3}))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.IsA382318` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382318, g.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3*. URL: <https://oeis.org/A382318>.

*Commentary.*

OEIS A382318, Name (unpaginated): "G.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3." The series A has zero constant coefficient, as specified by the entry's offset one. The displayed cube is an ordinary ring power.

**Definition 1.3 (The A382319 equation).**

$$\forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \operatorname{IsA382319}\left(B\right) = ((\operatorname{constantCoeff}\left(B\right) = 0) \land (B = X \cdot (1 - X)^{-1} + \operatorname{lambertSum}\left(B^{3}\right)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.IsA382319` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382319, g.f. A(x) satisfies A(x) = x/(1-x) + Sum_{n>=1} A(x^n)^3*. URL: <https://oeis.org/A382319>.

*Commentary.*

OEIS A382319, Name (unpaginated): "G.f. A(x) satisfies A(x) = x/(1-x) + Sum_{n>=1} A(x^n)^3." Here B denotes that entry's series. The term x/(1-x) is X times the ring inverse of 1-X, and Sum_{n>=1} B(x^n)^3 is lambertSum(B^3). The constant coefficient is zero.

**Definition 1.4 (The two coefficient congruences).**

$$\operatorname{claim} = ((\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \exists B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsA382318}\left(A\right)) \land (\operatorname{IsA382319}\left(B\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsA382318}\left(A\right)) \implies ((\operatorname{IsA382319}\left(B\right)) \implies ((\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n, A\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(n, B\right) = (v: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, u, v\right)))) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n + 1, A\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n + 2, A\right) = (v: \mathbb{Q})) \land ((\operatorname{Int}.\operatorname{ModEq}\left(3, u, 0\right)) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, v, 0\right))))))))))$$

*Formalization.* `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.claim` (`✓ std3`).

*Citation.* Paul D. Hanna (2025). *OEIS A382318, g.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3*. URL: <https://oeis.org/A382318>.

*Commentary.*

OEIS A382318, Comments (unpaginated): "Conjectures: a(3*n) == A382319(n) (mod 3) for n >= 0; a(3*n+1) == 0 (mod 3) and a(3*n+2) == 0 (mod 3) for n >= 1." In the formula A is the A382318 series and B the A382319 series. Both exist, and every such pair has integer coefficients at the displayed indices with the stated residues. Indices include zero in the first congruence. The latter two start at n=1, leaving a(1)=1 unrestricted.

**Theorem 1.5 (Hanna's congruences hold).**

$$(\exists A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \exists B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsA382318}\left(A\right)) \land (\operatorname{IsA382319}\left(B\right))) \land (\forall A: \operatorname{PowerSeries}\left(\mathbb{Q}\right), \forall B: \operatorname{PowerSeries}\left(\mathbb{Q}\right), (\operatorname{IsA382318}\left(A\right)) \implies ((\operatorname{IsA382319}\left(B\right)) \implies ((\forall n: \mathbb{N}, \exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n, A\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(n, B\right) = (v: \mathbb{Q})) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, u, v\right)))) \land (\forall n: \mathbb{N}, (1 \le n) \implies (\exists u: \mathbb{Z}, \exists v: \mathbb{Z}, (\operatorname{coeff}\left(3 \cdot n + 1, A\right) = (u: \mathbb{Q})) \land ((\operatorname{coeff}\left(3 \cdot n + 2, A\right) = (v: \mathbb{Q})) \land ((\operatorname{Int}.\operatorname{ModEq}\left(3, u, 0\right)) \land (\operatorname{Int}.\operatorname{ModEq}\left(3, v, 0\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Paul D. Hanna (2025). *OEIS A382318, g.f. A(x) satisfies A(x) = x + ( Sum_{n>=1} A(x^n) )^3*. URL: <https://oeis.org/A382318>.

*Commentary.*

The transformation F maps to X plus the cube of its Lambert sum preserves zero constant coefficient and improves finite coefficient agreement by one degree. Iteration from zero therefore stabilizes coefficient by coefficient over every commutative ring, and the fixed point is unique. Mapping the integer fixed point into the rationals gives the rational solution. Linearity of the Lambert sum and lambertSum(X)=X*(1-X) inverse show that B=lambertSum(A) and A=X+B^3 for every pair of solutions. Reducing this identity modulo three and applying cubic Frobenius gives A=X+B(X^3). Extracting coefficients proves all three residue assertions.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.IsA382318`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.IsA382319`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.lambertSum`
- Truth anchor: `D5/S1/Recurrence/Invariants/HannaLambertCubeModThree.result`
- Dependency: [D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity](CubicFifteenSubstitutionParity.md)
- Dependency: [D5/S1/Recurrence/Invariants/CubicTernarySubstitutionParity](CubicTernarySubstitutionParity.md)
