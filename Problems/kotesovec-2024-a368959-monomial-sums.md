---
slug: kotesovec-2024-a368959-monomial-sums
bibkey: kotesovec2024a368959
doi: null
url: https://oeis.org/A368959
triage: theorem
motivation_gids:
  - D5/S3/Arith/CharacterSums/KotesovecConjectureOne.result
---

# Kotěšovec's first A368959 conjecture

## Problem

Václav Kotěšovec, [OEIS A368959](https://oeis.org/A368959), COMMENTS; [preregistration #19241](https://github.com/the-omega-institute/trureturing/issues/19241).

> Conjecture 1: This is a subset of A001694.

The NAME is “Numbers m such that Sum_{k=0..m-1} exp(2*Pi*i*k^s/m) <> 0 for all s>=2.” A001694 denotes powerful numbers. A338325 has NAME “Biquadratefree powerful numbers: numbers whose exponents in their prime factorization are either 2 or 3.” Membership uses positive natural numbers.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| The complete sum over $0\le k<m$ | `KotesovecConjectureOne.monomialSum` | Literal summand and range; natural exponentiation precedes complex casting. |
| Every degree $s\ge2$ and positive $m$ | `KotesovecConjectureOne.InA368959` | Positivity, universal natural degree and nonvanishing are all explicit. |
| Prime exponents two or three | `KotesovecConjectureOne.InA338325` | Every prime factor of the positive natural number is covered. |
| A368959 is a subset of A001694 | `claimOne`, proved by `result` | Universal implication to the frozen `PowerfulNumber.Powerful` predicate; no added hypotheses. |

## Motivation

A prime occurring exactly once in a modulus forces cancellation at that prime degree. This restricts all possible members at once. The companion [second conjecture](kotesovec-2024-a368959-family.md) gives an infinite included family and four further moduli.

## Gap

The preregistrations record the source and literature screen: OEIS retained both conjectures without a solution reference; the bounded search covered Fried arXiv:2607.24832, Lam–Leung arXiv:math/9511209, Cochrane–Zheng's exponential-sum work and survey, Pigno's dissertation, MathOverflow 480590, formal-conjectures and the OEIS Open benchmark. No settlement was found in that searched scope. The final Pigno–Pinner journal version and Liu–Liu, *Truncated polynomials with restricted digits*, remain unread. Literature completeness is `ASSUMED-UNVERIFIED`; mathematical originality is not claimed.

## Route

Chinese remaindering factors the complete additive-character power sum for coprime moduli. If $p\mid m$ but $p^2\nmid m$, write $m=pr$ with $p\nmid r$. At degree $s=p$, Fermat's identity turns the factor modulo $p$ into the sum of an injective additive character. This sum vanishes, and hence so does the original complete sum. The contrapositive proves that every prime divisor of a member has its square dividing the member.

## Falsifier

The conclusion applies to every positive modulus and every prime divisor; testing finitely many degrees or moduli alone cannot establish it. The public `result` proves exactly `claimOne`, without an extra factorization or coprimality hypothesis.

## Evidence

The settling declaration is `D5.S3.Arith.CharacterSums.KotesovecConjectureOne.result`. Its live proof uses the private `simple_prime_vanish`; CRT factorization is the private consumed `powerSum_crt`. `Powerful` is reused from `D5.S3.Arith.Powerful.PowerfulNumber.Powerful`. Both delivered modules have complete Scribe mirrors, and each settling result displays its full claim.

Experiment: [published checker](https://github.com/the-omega-institute/trureturing-experiments/tree/69e451300aca2a3ed4ebf255d5b3adceaaca1c14/docs/reports/kotesovec-2024-a368959-monomial-sums). Command: `python3 check.py` from that directory, exit 0, `RESULT PASS`; script SHA-256 `d6dc43174ffdd445f069c7b355eeb596d3066c663e08819e20cff2d23e4064d9`. The implementation seat reran the identical pinned bytes. It reproduces the first twenty listed terms by searching $1\le m\le289$; checks the A338325 family through $m=3000$ and the four named moduli; checks the vanishing degree for every non-powerful $2\le m\le3000$; and checks the coefficient formulas for $p\in\{2,3,5,7,11,13\}$, $2\le a\le5$, $2\le s\le12$, restricted to $p^a\le200000$. Exponential-sum comparisons use absolute tolerance $10^{-6}$; fiber counts are exact integers. Its degree window is $2\le s\le e+\lambda(m)+1$, where $e$ is the largest prime exponent. These are computed comparisons, separate from the universal Lean proofs.

The escape audit is unfinished for the nine public theorems of these two modules, as listed in [#19384](https://github.com/the-omega-institute/trureturing/issues/19384). No Reg mirror is delivered. Missing evidence consists of faithful source reconstruction and equivalence bridges, enrolled readouts, actual realization, law variation, per-role sensitivity and observational dependence. The module comments and both dossiers link that issue; no `declared_validated` status is claimed.

## Triage

### What the settlement shows

- **Kernel-checked:** `KotesovecConjectureOne.result` proves every A368959 member powerful. Its private `simple_prime_vanish` proves the sharper mechanism: a prime divisor occurring only once forces vanishing at degree $p$.
- **Kernel-checked:** `KotesovecConjectureTwo.result` proves the companion inclusion and all four named terms; the theorem states precisely those terms, not an exhaustive classification.
- **Proved in prose:** the converse fails at $16$. At degree three the eight odd residues are permuted by cubing, and their sixteenth-root sum is zero. Among the eight even residues, four cubes are $0$ and four are $8$ modulo $16$, whose character values cancel. Thus the full sum is zero although $16=2^4$ is powerful. This argument is not a separate Lean declaration.
- **Computed:** the experiment entry checks the finite modulus and degree ranges stated there. It is not a proof of the universal claim.
- **Open:** the exact subset of the powerful numbers, and a closed classification of prime-power exponents.

The source's two conjecture lines are settled by the two results. No further source theorem conditional on them is identified in the preregistration; other OEIS formulas and related entries are outside these claims.

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
