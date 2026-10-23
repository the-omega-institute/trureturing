---
slug: oeis-a382124-hanna-sigma-exponential-mod-three
bibkey: hanna2025a382124a382125
doi: null
url: https://oeis.org/A382124
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.result
---

# Hanna's A382124 congruence

## Problem

OEIS A382124 states: "Conjecture: a(n) == A382125(3*n) (mod 3) for n >= 0."

Write $A(x)=\exp(\sum_{n\ge1}\sigma(n)\sigma(2n)x^n/(3n))$ and $B(x)=\exp(\sum_{n\ge1}\sigma(n)\sigma(2n)x^n/n)$, with $\sigma(n)=\sum_{d\mid n}d$. The public rational-series definitions are exactly the preregistered expressions.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every index $n\ge0$ | `claim` quantifies over every natural index | Exact |
| A382124 generating function | `HannaSigmaProductExpModThree.A` | Exact rational exponential substitution |
| A382125 generating function | `HannaSigmaProductExpModThree.B` | Exact rational exponential substitution |
| $a(n)\equiv b(3n)\pmod3$ | `claim`: `coeff n A = u`, `coeff (3*n) B = v`, `u ≡ v [ZMOD 3]` | Exact |
| Integer coefficients | `∃ u v : ℤ` and the two rational coefficient equalities | Witnesses make congruence well typed; no extra hypothesis |

## Motivation

The named conjecture is preregistered in #18863. The exact rational formal series carry integer witnesses for the source's congruence statements. Its settling declaration is D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.result.

## Gap

The literature screen in #18863 and #18864 covers the OEIS entries and their links, the OEIS Open benchmark and four OEIS-proof papers, arXiv:2610.15849, arXiv:2410.07237, arXiv:2608.11941 and arXiv:2607.24832. No settlement was found in that searched scope. Completeness is `ASSUMED-UNVERIFIED`.

## Route

Put $c(n)=\sigma(n)\sigma(2n)/3$. The arithmetic argument proves that $c$ is integer valued and satisfies the Dold congruences. For the prime three, writing $m=3^a k$ with $3\nmid k$ gives $c(3^a k)=\sigma(3^a)^2c(k)$, and $\sigma(3^{a+1})-\sigma(3^a)=3^{a+1}$. This supplies the required power of three. The other primes use the Dold congruences of the divisor sum and their product and index-scaling closure.

The shared `DoldExponentialIntegrality.integral_exp_of_dold` theorem proves the sufficient Dold integrality criterion. `HannaSigmaProductExpModThree.AIntegral` applies it to $c$. The identity `integerCube_map` identifies the cube of the integral lift of $A$ with $B$. The theorem `cube_residues` applies characteristic-three Frobenius to that lift.

## Falsifier

A nonintegral coefficient of $A$, or an index violating a source congruence, contradicts the formal settlement under the displayed definitions. The finite experiment below is supporting evidence; the universal result is the Lean theorem.

## Evidence

The settling theorem is `D5/S1/Recurrence/Invariants/HannaSigmaProductExpModThree.result`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}. The full statement appears in its Blueprint theorem node.

The supporting source is adapted from AINTLIB at commit `1e63feb21e2dd9e54908d14c9c07058eff3ff1d4`, with attribution and Apache-2.0 license in `Library/RecurrenceComposition/aintlib2026dieudonnedwork.md`.

The escape audit is unfinished: [#19891](https://github.com/the-omega-institute/trureturing/issues/19891). The published owner declarations `D5.S3.Arith.Robin.PrimeFiberPropagation.sigma_prime_pow_succ`, `D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.Agree`, `D5.S1.Recurrence.LinearRows.LinearExponentDyadicSupport.pow_change` and `D5.S1.Recurrence.Residue.ParametricExponentialSquareCongruence.linear_ode_unique` are included in that unfinished audit. No delivered Reg registration is classified as `declared_validated`.

### Experiment

[Pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/7b61b379bca979d9231306df7e0b20924bcc3491/docs/reports/oeis-a382318-a382319-a382124-a382125-hanna-frobenius-mod3). Run `python3 check.py 300` in that directory; exit 0, `RESULT PASS`. The script SHA-256 is `319ee58b884641c875833eb3e830906af72d593ab73e1d6b0da6ff155cd352f3`.

Computed scope: $c(n)$ is integral for $1\le n\le900$; the Dold congruences hold for primes $p<40$ and $pm\le900$; $A$ is integral through degree 300 and $B$ through degree 900; their tested coefficients match the b-files; $B=A^3$ through degree 300; $a(n)\equiv b(3n)\pmod3$ for $0\le n\le300$; and $b(3n+1)\equiv b(3n+2)\equiv0\pmod3$ for $0\le n<300$.

### Declaration classification

Names in this table are relative to `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThree`. The shared live escape witness is `D5.S1.Recurrence.Algebraic.DoldExponentialIntegrality.IsRIntegralPS.dieudonneDwork_mpr`; content classification expands the same-delivery support.

| Declaration | proof_shape | escape_witness | Consumers |
| --- | --- | --- | --- |
| `A` | bind-only | none | `claim`, `AIntegral`, `B_eq_cube`, `integerSeries`, `integerSeries_map`, `integerCube_map`, `result`, `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.claim`, `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.result` |
| `B` | bind-only | none | `claim`, `B_eq_cube`, `integerCube_map`, `result`, `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.claim`, `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.result` |
| `claim` | bind-only | none | `result` |
| `Arithmetic.sigma_prime_step` | bind-only | none | `Arithmetic.c_three_prime_step`, `Arithmetic.sigma_dold` |
| `Arithmetic.sigma_two_succ` | bind-only | none | `Arithmetic.sigma_two_pair` |
| `Arithmetic.sigma_two_pair` | bind-only | none | `Arithmetic.sigma_product_three_dvd` |
| `Arithmetic.sigma_product_three_dvd` | bind-only | none | `Arithmetic.three_c` |
| `Arithmetic.c` | bind-only | none | `Arithmetic.three_c`, `Arithmetic.c_cast`, `Arithmetic.c_odd_prime_factor`, `Arithmetic.c_three_prime_step`, `Arithmetic.c_dold_away_three`, `Arithmetic.c_dold_three`, `Arithmetic.c_dold`, `AIntegral` |
| `Arithmetic.three_c` | bind-only | none | `Arithmetic.c_cast`, `Arithmetic.c_odd_prime_factor`, `Arithmetic.c_dold_away_three` |
| `Arithmetic.c_cast` | bind-only | none | `AIntegral` |
| `Arithmetic.c_odd_prime_factor` | bind-only | none | `Arithmetic.c_three_prime_step` |
| `Arithmetic.c_three_prime_step` | bind-only | none | `Arithmetic.c_dold_three` |
| `Arithmetic.padic_eq_of_split` | bind-only | none | `Arithmetic.sigma_dold`, `Arithmetic.c_dold_three` |
| `Arithmetic.sigma_dold` | bind-only | none | `Arithmetic.c_dold_away_three` |
| `Arithmetic.dold_mul` | bind-only | none | `Arithmetic.c_dold_away_three` |
| `Arithmetic.dold_scale` | bind-only | none | `Arithmetic.c_dold_away_three` |
| `Arithmetic.c_dold_away_three` | bind-only | none | `Arithmetic.c_dold` |
| `Arithmetic.c_dold_three` | bind-only | none | `Arithmetic.c_dold` |
| `Arithmetic.c_dold` | bind-only | none | `AIntegral` |
| `AIntegral` | content | shared witness | `integerSeries`, `integerSeries_map` |
| `B_eq_cube` | bind-only | none | `integerCube_map` |
| `integerSeries` | bind-only | none | `integerSeries_map`, `integerCube_map`, `cube_residues`, `result`, `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.result` |
| `integerSeries_map` | content | shared witness | `integerCube_map`, `result` |
| `integerCube_map` | content | shared witness | `result`, `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.result` |
| `cube_residues` | bind-only | none | `result`, `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.result` |
| `result` | content | shared witness | `D5.S1.Recurrence.Invariants.HannaSigmaProductExpModThreeCube.result` |

## Triage

### What the settlement shows

- **Proved in Lean — mechanism and integrality.** `DoldExponentialIntegrality.integral_exp_of_dold` proves integrality for every integer ghost sequence satisfying `Dold`. `HannaSigmaProductExpModThree.AIntegral` establishes the integrality of $A$; the arithmetic factorization at three closes the denominator-prime case.
- **Proved in Lean — exact scope.** `HannaSigmaProductExpModThree.result` and `HannaSigmaProductExpModThreeCube.result` prove the two complete preregistered claims at every natural index. They use no coefficient cutoff.
- **Proved in Lean — reusable structure.** The general sufficient Dold criterion has an arbitrary integer ghost sequence. `CubicFifteenSubstitutionParity.prime_power_subst` supplies Frobenius for arbitrary series over a prime residue field. No further named conjecture is claimed settled.
- **Computed — owner integration.** The source inventory publishes `LinearExponentDyadicSupport.pow_change` and `ParametricExponentialSquareCongruence.linear_ode_unique`, with complete Scribe nodes. `CubicFifteenSubstitutionParity.prime_power_subst` is already public on the protected base. These are reused through their owners.
- **Computed — shared support.** The delivered source inventory has one shared `DoldExponentialIntegrality` module, consumed by `HannaSigmaProductExpModThree.AIntegral`; no second copy is delivered. **Open:** integration of the independent fibpow lane is outside this delivery.
- **Computed — publication structure.** Each of the two named problems has its own dossier and one `OpenProblemResolutionClaim` on its settling `result`. **Open:** four-slot registration evidence is incomplete under #19891; required CI and the review triplet govern admission.
- **Computed — coefficient checks.** The experiment entry gives the command, script identity and exact finite ranges. Those ranges carry no uniform numerical conclusion.
- **Open.** The residues of $A$ itself modulo three are not determined here.

Inventory evidence: `git grep -n -E "^(private )?(noncomputable )?(def|theorem) (pow_change|linear_ode_unique|prime_power_subst|integral_exp_of_dold)|OpenProblemResolutionClaim" -- D5/S1/Recurrence Blueprint/D5/S1/Recurrence` (exit 0). The module and Scribe inventories establish the publication and sharing statements; they are not mathematical proofs.

### Generalization proved in prose

Let $q$ be prime and let $f:\mathbb N\to\mathbb Z$ satisfy the Dold congruences. Suppose $q\mid f(n)$ for every $n$ and $q^{v_q(m)+2}\mid f(qm)-f(m)$ for every positive $m$. Put $g(n)=f(n)/q$. At primes $p\ne q$, cancellation of the factor $q$ preserves the required $p$-power divisibility. At $p=q$, the extra power of $q$ gives $q^{v_q(m)+1}\mid g(qm)-g(m)$. Thus $g$ satisfies Dold, and the sufficient criterion makes $\exp(\sum_{n\ge1}g(n)x^n/n)$ integral. Reduction modulo $q$ and Frobenius identify its $q$-th power with substitution of $x^q$. This is a prose consequence of the general criterion, not a new Lean declaration or another named settlement.

The source's assertion that $B$ is the self-convolution cube of $A$ is represented by `integerCube_map` after rational mapping. The two stated residue conjectures follow. No other source result is asserted to depend on them.

## ASSUMED-UNVERIFIED

Literature completeness, priority, the source's identification with the formal generating functions and the fidelity of the prose-to-Lean correspondence are outside the kernel. The source and literature readings are attributed to the preregistration's orchestrator and literature seat. The experiment is finite. The escape-registration evidence remains incomplete under #19891.
