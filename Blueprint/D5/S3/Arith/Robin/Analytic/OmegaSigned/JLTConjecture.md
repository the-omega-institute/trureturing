# Johnston-Leong-Tudzi Conjecture 5.1

## Abstract

The large-parameter limit of the signed Omega summatory limsup.

**Definition 1.1 (The signed summatory function).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.W`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.W` (`✓ std3`).

*Citation.* D. R. Johnston, N. Leong, S. Tudzi (2026). *New bounds and progress towards a conjecture on the summatory function of (−2)^{Ω(n)}*. DOI: [10.1080/10586458.2025.2483942](https://doi.org/10.1080/10586458.2025.2483942). URL: <https://arxiv.org/abs/2408.04143v3>.

*Commentary.*

For real a and x, W(a,x) is the sum of (-a)^Omega(n) over natural n in the closed interval from one to the natural floor of x. Omega is ArithmeticFunction.cardFactors: it counts prime factors with multiplicity.

**Definition 1.2 (The normalized limsup).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.s`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.s` (`✓ std3`).

*Citation.* D. R. Johnston, N. Leong, S. Tudzi (2026). *New bounds and progress towards a conjecture on the summatory function of (−2)^{Ω(n)}*. DOI: [10.1080/10586458.2025.2483942](https://doi.org/10.1080/10586458.2025.2483942). URL: <https://arxiv.org/abs/2408.04143v3>.

*Commentary.*

For real a, s(a) is the real filter limsup at positive infinity of |W(a,x)|/x^(logb(2,a)), with x real. The source uses a>2. The estimates here provide the boundedness needed for the real limsup when a>=64.

**Definition 1.3 (The error bound).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.B`

*Formalization.* `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.B` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. R. Johnston, N. Leong, S. Tudzi (2026). *New bounds and progress towards a conjecture on the summatory function of (−2)^{Ω(n)}*. DOI: [10.1080/10586458.2025.2483942](https://doi.org/10.1080/10586458.2025.2483942). URL: <https://arxiv.org/abs/2408.04143v3>.

*Commentary.*

For every real a, B(a) is (1/2)*3^(2-logb(2,a)/3). It tends to zero as a tends to positive infinity.

**Theorem 1.4 (Two-sided quantitative bounds).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.quantitative`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.quantitative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* D. R. Johnston, N. Leong, S. Tudzi (2026). *New bounds and progress towards a conjecture on the summatory function of (−2)^{Ω(n)}*. DOI: [10.1080/10586458.2025.2483942](https://doi.org/10.1080/10586458.2025.2483942). URL: <https://arxiv.org/abs/2408.04143v3>.

*Commentary.*

For every real a>=64, a/(a+1)-B(a)<=s(a) and s(a)<=1+B(a). Every positive integer has a unique representation 2^j*m with m odd. The geometric sum on each such fiber has absolute value at most a^J. The existing odd_part_lower theorem of PrimeExponentRecordLimitOne, via cardFactors_apply, gives 3^Omega(m)<=m for odd m. Consequently 2^(3*Omega(m))<=m^2. With v=logb(2,a)>=6, the normalized odd weight is at most m^(-v/3). Its tail from three is bounded by 3^(2-v/3) times the telescoping sum of 1/(m*(m-1)), hence by B(a). The odd part one supplies the main geometric sum. The upper estimate holds for every real x>=1, and the lower estimate follows along x=2^k. Eventual upper boundedness and lower coboundedness justify both limsup comparisons.

**Theorem 1.5 (The conjectured limit).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.result`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.result` (`✓ std3`). ∎

*Resolves.* `Problems/johnston-leong-tudzi-2026-conjecture-5-1` (proved) by `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"johnston-leong-tudzi-2026-conjecture-5-1","declaration_gid":"D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. R. Johnston, N. Leong, S. Tudzi (2026). *New bounds and progress towards a conjecture on the summatory function of (−2)^{Ω(n)}*. DOI: [10.1080/10586458.2025.2483942](https://doi.org/10.1080/10586458.2025.2483942). URL: <https://arxiv.org/abs/2408.04143v3>.

*Commentary.*

The function s tends to one as the real parameter a tends to positive infinity. The proof applies quantitative: its lower endpoint tends to one because a/(a+1) tends to one and B(a) tends to zero; its upper endpoint also tends to one. The squeeze theorem gives the claimed limit. This establishes precisely Conjecture 5.1, and gives no eventual strict bound from Conjecture 1.4, even for large fixed a, and no conclusion about Sun's conjecture at a=2.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.B`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.W`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.quantitative`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.result`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaSigned/JLTConjecture.s`
- Dependency: [D5/S3/Factorization/PrimeExponentRecordLimitOne](../../../../Factorization/PrimeExponentRecordLimitOne.md)
