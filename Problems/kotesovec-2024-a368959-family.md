---
slug: kotesovec-2024-a368959-family
bibkey: kotesovec2024a368959
doi: null
url: https://oeis.org/A368959
triage: theorem
motivation_gids:
  - D5/S3/Arith/CharacterSums/KotesovecConjectureTwo.result
---

# Kotěšovec's second A368959 conjecture

## Problem

Václav Kotěšovec, [OEIS A368959](https://oeis.org/A368959), COMMENTS; [preregistration #19242](https://github.com/the-omega-institute/trureturing/issues/19242).

> Conjecture 2: This sequence contains all the terms from A338325, plus 243, 972, 1944, 2401, ...

The NAME is “Numbers m such that Sum_{k=0..m-1} exp(2*Pi*i*k^s/m) <> 0 for all s>=2.” A001694 denotes powerful numbers. A338325 has NAME “Biquadratefree powerful numbers: numbers whose exponents in their prime factorization are either 2 or 3.” Membership uses positive natural numbers.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The complete sum over $0\le k<m$ | `KotesovecConjectureOne.monomialSum` | Literal summand and range; natural exponentiation precedes complex casting. |
| Every degree $s\ge2$ and positive $m$ | `KotesovecConjectureOne.InA368959` | Positivity, universal natural degree and nonvanishing are all explicit. |
| Prime exponents two or three | `KotesovecConjectureOne.InA338325` | Every prime factor of the positive natural number is covered. |
| Every A338325 term is included | First conjunct of `claimTwo` | Universal family inclusion. |
| 243, 972, 1944 and 2401 are included | Four remaining conjuncts of `claimTwo` | Every named modulus is retained. The ellipsis specifies no further list and is not read as exhaustiveness. |
| Entire second conjecture | `result : claimTwo` | No extra assumptions. |

## Motivation

Prime squares and cubes generate the biquadratefree powerful family through coprime products. The four named terms show that this family does not exhaust A368959. The [first conjecture](kotesovec-2024-a368959-monomial-sums.md) confines every member to the powerful numbers.

## Gap

The preregistrations record the source and literature screen: OEIS retained both conjectures without a solution reference; the bounded search covered Fried arXiv:2607.24832, Lam–Leung arXiv:math/9511209, Cochrane–Zheng's exponential-sum work and survey, Pigno's dissertation, MathOverflow 480590, formal-conjectures and the OEIS Open benchmark. No settlement was found in that searched scope. The final Pigno–Pinner journal version and Liu–Liu, *Truncated polynomials with restricted digits*, remain unread. Literature completeness is `ASSUMED-UNVERIFIED`; mathematical originality is not claimed.

## Route

For a prime power $q=p^{a+1}$ and an injective additive character, vanishing forces the power-map count polynomial to be divisible by the cyclotomic polynomial. Its degree is below $q$, so coefficients at $r$ and $r+p^a$ coincide for $r<p^a$. Unequal counts therefore force nonvanishing. A missing-preimage argument handles large degrees; odd quadratic sums and the exact small fibers handle the remaining cases. This proves nonvanishing for all prime squares and cubes and for $243$ and $2401$. CRT preserves it under coprime multiplication, giving the full family and $972=4\cdot243$, $1944=8\cdot243$.

## Falsifier

The source quantifies over every natural degree at least two. A numerical sample or a check only of the standard character cannot replace the universal proof. The four extra moduli are individual conjuncts; the ellipsis does not assert that the displayed family and four terms form the whole sequence.

## Evidence

The settling declaration is `D5.S3.Arith.CharacterSums.KotesovecConjectureTwo.result`. It imports the same-delivery `KotesovecConjectureOne`, whose `family_inclusion`, `good_prime_square`, `good_prime_cube`, `good_mul`, `good_to_membership`, `good_243` and `good_2401` lie on its proof path. The coefficient obstruction is private and consumed. The auxiliary predicate `Good` ranges over every injective additive character, and `good_to_membership` specializes to `ZMod.stdAddChar`.

Experiment: [published checker](https://github.com/the-omega-institute/trureturing-experiments/tree/69e451300aca2a3ed4ebf255d5b3adceaaca1c14/docs/reports/kotesovec-2024-a368959-monomial-sums). Command: `python3 check.py` from that directory, exit 0, `RESULT PASS`; script SHA-256 `d6dc43174ffdd445f069c7b355eeb596d3066c663e08819e20cff2d23e4064d9`. The implementation seat reran the identical pinned bytes. It reproduces the first twenty listed terms by searching $1\le m\le289$; checks the A338325 family through $m=3000$ and the four named moduli; checks the vanishing degree for every non-powerful $2\le m\le3000$; and checks the coefficient formulas for $p\in\{2,3,5,7,11,13\}$, $2\le a\le5$, $2\le s\le12$, restricted to $p^a\le200000$. Exponential-sum comparisons use absolute tolerance $10^{-6}$; fiber counts are exact integers. Its degree window is $2\le s\le e+\lambda(m)+1$, where $e$ is the largest prime exponent. These are computed comparisons, separate from the universal Lean proofs.

The escape audit is unfinished for the nine public theorems of these two modules, as listed in [#19384](https://github.com/the-omega-institute/trureturing/issues/19384). No Reg mirror is delivered. Missing evidence consists of faithful source reconstruction and equivalence bridges, enrolled readouts, actual realization, law variation, per-role sensitivity and observational dependence. The module comments and both dossiers link that issue; no `declared_validated` status is claimed.

## Triage

### What the settlement shows

- **Kernel-checked:** `KotesovecConjectureTwo.result` proves both the universal A338325 inclusion and membership of $243,972,1944,2401$.
- **Kernel-checked:** `KotesovecConjectureOne.good_prime_square`, `good_prime_cube` and `good_mul` show that nonvanishing holds for every injective additive character and is preserved under coprime products. `good_243` and `good_2401` give the additional prime-power factors, and `family_inclusion` gives the full family.
- **Kernel-checked:** the private `prime_power_coefficient_obstruction` forces equal coefficients in one class modulo $p^a$ when the sum modulo $p^{a+1}$ vanishes. It is assessed as bind-only and is not proposed as an escape witness.
- **Proved in prose:** the inclusion is not a classification. The member $243=3^5$ has an exponent outside $\{2,3\}$, and the powerful number $16$ is excluded by the cubic-sum calculation in the companion dossier.
- **Computed:** the pinned experiment checks the count formulas and family comparisons on the finite ranges in its entry. It does not certify a general exponent formula.
- **Open:** a closed description of all exponents giving membership for higher prime powers. Finite degree periodicity supplies a decision route for each fixed modulus, not such a closed description.

Both named conjectures are settled together. The source's other formulas and questions are outside these conclusions; the preregistration identifies no additional theorem conditional on the second conjecture.

### Target coverage

| Target item | Status and evidence |
| --- | --- |
| Both named conjectures | Proved: the two kernel-checked `result` declarations, each with its own resolution node and dossier. |
| Closed description of all prime-power exponents | Open; the family inclusion and named moduli give sufficient cases only. |
| Independent coefficient escape classification | The coefficient obstruction is bind-only and is not claimed as an escape witness. Four-slot audit evidence remains open in #19384. |
| Two named literature gaps | Open: the final Pigno–Pinner version and the Liu–Liu paper have not been verified. |
| Canonical admission and Scribe | The two module state records and the two `OpenProblemResolutionClaim` nodes record the two settlements. Reg evidence remains open in #19384. |
| Mathematical originality | Not claimed; applying established character and cyclotomic machinery does not establish priority. |
| Exhaustive prior-art clearance | `ASSUMED-UNVERIFIED`; bounded literature reading only. |
| Full repository gate | No local full gate; remote required CI is the admission authority. The claim here is the scoped kernel verification. |
| Canonical frozen status | The canonical deposit writers supply the two state records; no separate handwritten state is asserted. |

## ASSUMED-UNVERIFIED

Literature-screen completeness and independent priority are `ASSUMED-UNVERIFIED`. The two named literature gaps remain unresolved. The escape audit is unfinished under #19384, independently of the proofs and canonical state records. No complete classification of higher prime powers is claimed.
