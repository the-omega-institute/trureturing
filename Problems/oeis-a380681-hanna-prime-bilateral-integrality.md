---
slug: oeis-a380681-hanna-prime-bilateral-integrality
bibkey: hanna2025a380681
doi: null
url: https://oeis.org/A380681
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.result
---

# Hanna's prime bilateral integrality conjecture

## Problem

P. D. Hanna's [OEIS A380681](https://oeis.org/A380681), Comments section, states:

> Conjecture: if F(x) satisfies p*x = Sum_{n=-oo..+oo} (-1)^n * x^(p*n) * (F(x) + x^n)^(p*n) with F(0) = 1 for some fixed integer p, then F(x) is an integer series in x iff p is prime. The g.f. A(x) of this sequence is the case when p = 2; other cases include A380682 (p=3), A380683 (p=5), A380684 (p=7), A380685 (p=11), and A380686 (p=13).

Preregistration: [#18831](https://github.com/the-omega-institute/trureturing/issues/18831).
The [Library note](../Library/RecurrenceComposition/hanna2025a380681.md) records the source.
The formal parameter is $p\in\mathbb N$ with $p\ge2$, and $F\in\mathbb Q[[X]]$.
Integer powers are taken in $\mathbb Q((X))$. At degree $N$, the bilateral sum
means every symmetric window $[-K,K]$ with $K\ge N+1$.

### Statement echo

The Lean namespace is `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality`.

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $(-1)^n x^{pn}(F+x^n)^{pn}$, $n\in\mathbb Z$ | `term` | Literal integer Laurent powers, with $x=X$ and the embedded $F$. |
| $F(0)=1$ | First conjunct of `IsSolution` | The rational constant coefficient is one. |
| $px$ equals the bilateral sum | Remaining conjunct of `IsSolution` | Every coefficient in every sufficiently large symmetric window has the required value. |
| Integer series | Integer witness for every coefficient in `claim` | Every rational coefficient is the cast of an integer. |
| If and only if $p$ is prime | Equivalence in `claim` | Both directions hold for every normalized rational solution. |
| Fixed integer parameter | Natural $p\ge2$ in `claim` | The preregistered range; nonpositive parameters are outside the statement. |
| A solution exists | Existential conjunct of `claim` | Additional conclusion for every $p\ge2$, with no additional hypothesis. |

No source clause within the preregistered interpretation is dropped. Both the
`claim` and `result` Blueprint nodes display the complete proposition.

## Motivation

The equation relates an infinite bilateral Laurent sum to an integral
coefficient recursion. The settling GID is
`D5/S1/Recurrence/Bilateral/HannaPrimeBilateralIntegrality.result`.
It proves existence for every $p\ge2$ and characterizes integrality by primality.

## Gap

The source and literature screen in #18831 found no proof or refutation of the
common conjecture in A380681–A380686. The screen includes the entries and their
revisions, repository issues, LeanOpenProblems-results and formal-conjectures.
The research reading of revisions is seat-reported in that issue. Completeness
of the screen is `ASSUMED-UNVERIFIED`.

## Route

For $n=-m<0$, factor the summand as
$(-1)^m X^{pm(m-1)}(1+X^mF)^{-pm}$.
Together with the positive summands this makes each coefficient a finite sum.
At parameter one, the positive term indexed by $m$ with power $F^b$ pairs
with the negative term indexed by $r=m-b+1$, $j=b$; their exponents and
binomial coefficients agree and their signs are opposite. The remaining
negative constant cancels the zero-index summand.

For prime $p$, Frobenius transfers this cancellation to divisibility by $p$.
Removing the linear term gives a map that improves coefficient agreement by
one degree. Compatible iterates construct the rational solution and retain
integer coefficients. The proof applies the imported
`CubicFifteenSubstitutionParity.prime_power_subst` and
`PowerSeriesNormalizedContraction.exists_unique_fixed`.
The shared `BilateralProductModFour.window_split` separates the symmetric
window, and `BilateralProductModFour.ofSeries_inverse` identifies inverses
under the Laurent embedding.

Below degree $p$, the equation yields
$r!\,[X^r](1+XF)=\prod_{j<r}(1+jp)$ for $r<p$.
If $p$ is composite and $q$ is its least prime divisor, $q\mid q!$ but $q$
divides none of the numerator factors. An integer coefficient would
contradict this divisibility obstruction.

## Falsifier

A normalized rational solution at prime $p\ge2$ with a noninteger coefficient,
or one at composite $p\ge2$ with every coefficient integral, contradicts
`result`. A different convention for bilateral summation or nonpositive
parameters changes the statement.

## Evidence

`D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.result` proves the
full `claim`. Its admission basis is `open-problem-resolution (#18831; Proved)`.
The public theorem is classified `content`; the cancellation, construction
and coefficient obstruction are on its derivation path. The module has
`generality: G` and `utility: none`.

The four-slot escape audit is unfinished under
[issue #19820](https://github.com/the-omega-institute/trureturing/issues/19820)
for this `result` and the shared `BilateralProductModFour.window_split`.
The missing evidence is complete source reconstruction and lawful variation,
sensitivity and observational dependence for their quantified series and
group-valued function families. No `declared_validated` registration is claimed.

### Declaration judgement

| Declaration | proof_shape | escape_witness | Direct consumers |
| --- | --- | --- | --- |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.negative_factorization` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.term_normalization` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.ofSeries_inverse` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.term_normalization` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.term_normalization` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.isSolution_iff` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.normalized_outside` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.finite_window` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.finite_window` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.isSolution_iff`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_inverse_equation`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_divisibility_of_pairing`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_constant`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_difference_dvd`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_one_zero`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_zero_first` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.isSolution_iff` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_inverse_equation`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_fixed_iff` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.negative_binomial_coeff` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.negative_expansion` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.inverse_power_subst` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.negative_expansion` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.shifted_subst_coeff` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.negative_expansion` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.negative_expansion` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_one_zero` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.positive_expansion` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_one_zero` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.symmetric_sum` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_one_zero` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_one_zero` | content | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_one_zero` | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.result` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.contracting_series_fixedpoint` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.exists_solution` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.inverse_difference` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.exceptional_difference_dvd` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.inverse_difference_dvd` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.normalized_difference_dvd` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.shifted_difference_dvd` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.normalized_difference_dvd` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.normalized_difference_dvd` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_difference_dvd` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.exceptional_difference_dvd` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_difference_dvd` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_difference_dvd` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_first`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_contract` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_constant` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_fixed_iff` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_zero_first` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_first` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_first` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_constant` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_constant` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_fixed_iff` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_contract` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.exists_solution`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_solution_integral` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_fixed_iff` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.exists_solution`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_solution_integral` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.exists_solution` | content | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.exists_solution` | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.result` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.normalizedTerm_map` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_map` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_map` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_divisibility_of_pairing`, `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_preserves_integral` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.normalizedTerm_frobenius` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_divisibility_of_pairing` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_divisibility_of_pairing` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_preserves_integral` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.binomial_obstruction` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.integral_implies_prime` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.composite_minFac_lt` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.integral_implies_prime` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.normalized_tail_dvd` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_inverse_equation` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_inverse_equation` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_power_equation` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_power_equation` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_differential_equation` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.derivative_order` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_differential_equation` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_differential_equation` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_coefficient_recurrence` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.low_coefficient_recurrence` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.factorial_coefficient_identity` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.factorial_coefficient_identity` | content | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.factorial_coefficient_identity` | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.integral_implies_prime` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.integral_implies_prime` | content | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.integral_implies_prime` | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.result` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.step_preserves_integral` | bind-only | none | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_solution_integral` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_solution_integral` | content | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.prime_solution_integral` | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.result` |
| `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.result` | content | `D5.S1.Recurrence.Bilateral.HannaPrimeBilateralIntegrality.psi_one_zero` | settling result |

### Experiment

[Published checker and data](https://github.com/the-omega-institute/trureturing-experiments/tree/9dfe5bdc210cac281a148e7180239ddb21b0b34b/docs/reports/oeis-hanna-parity-family-research).
Command in that pinned directory: `python3 check.py`; exit 0, `RESULT PASS`.
The `check.py` SHA-256 is
`ec87bb1637d6a946d4e5fb43f078bc623ce327257ef53b9305c05c564ca154b5`.
For $p=2,3,4,5,6,7$, the computed solution includes coefficients through degree
11 and the equation through degree 12. For $p=8,9,10,11,13,15$, those degrees
are 8 and 9. The prime cases match A380681–A380686 and have integral coefficients.
For the tested composites the first noninteger coefficient is at $q-1$ and
equals $\prod_{j<q}(1+jp)/q!$. Three integer series selected with seed 7 satisfy
$\Psi_1(Y)=0$ and $\Psi_3(Y)\equiv0\pmod3$ through degree 12. These are finite
computations, separate from the uniform kernel-checked settlement.

## Triage

### What the settlement shows

| Item | Status | Evidence |
| --- | --- | --- |
| Normalized rational solutions are unique for every $p\ge2$ | Proved, kernel-checked transient application | A transient Lean application applies `contracting_series_fixedpoint`, `step_contract` and `step_fixed_iff` to arbitrary $p\ge2$; no additional public theorem. |
| There is no normalized rational solution for $p=1$ | Proved, kernel-checked transient application | A transient Lean application combines `isSolution_iff` with `psi_one_zero`; comparing the linear coefficients gives $0=1$. |
| Cancellation for arbitrary series over every commutative ring | Proved, kernel-checked | Private `psi_one_zero` has exactly this parameterized statement. |
| $r!\,[X^r](1+XF)=\prod_{j<r}(1+jp)$ for $p\ge2$, `IsSolution p F` and $r<p$ | Proved, kernel-checked | Private `factorial_coefficient_identity`. |
| The first noninteger coefficient is exactly at $q-1$ with reduced denominator exactly $q$ for every composite $p$ | Open as a uniform strengthening; computed for the six listed composites | `integral_implies_prime` needs nonintegrality only. The experiment determines first failure in its stated finite range; no uniform exact-denominator theorem is claimed. |
| Negative $p$ and $p=0$ | Open; outside the binding claim | The formal claim quantifies over natural $p\ge2$; no extension is asserted. |

The decisive mechanism is bilateral cancellation followed by Frobenius and a
coefficient contraction. The arbitrary-ring cancellation and low-degree
coefficient identity specify how far the argument extends. The stronger
first-failure assertion remains distinct from the proved integrality criterion.
No further source result relying on the conjecture is identified by the
literature screen; its completeness remains `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature-search completeness and the absence of an external settlement outside
the searched material are `ASSUMED-UNVERIFIED`. The uniform exact first-failure
and reduced-denominator assertion is not formalized. Nonpositive parameters are
outside the claim. The unfinished escape audit supplies no registration validation.
