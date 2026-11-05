---
slug: oeis-a343825-kagey-power-sequences
bibkey: kagey2021a343825
doi: null
url: https://oeis.org/A343825
triage: theorem
motivation_gids:
  - D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences
---

# Kagey's eventual equality of power-sequence minima

## Problem

> Conjecture: T(p,k) = A071537(k) for fixed k and sufficiently large prime p.

The source is P. Kagey's OEIS A343825, COMMENT, revision 22. The defining NAME and the linked A071537 NAME are quoted in [the source note](../Library/Factorization/kagey2021a343825.md). The preregistration is [#18687](https://github.com/the-omega-institute/trureturing/issues/18687).

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| A nondecreasing sequence beginning at $k$ and ending at $m$ | `Valid n k m b`: option-valued first and last elements and pairwise natural order | Literal source convention |
| Every multiplicity is below $n$; the product is an integer $n$th power | The count bound and integer-power conjuncts of `Valid` | All conjuncts retained |
| $T(n,k)$ is the least such $m$ | `T` uses `Nat.find` | Zero extends the function outside the existence domain |
| Integer exponents on $[k,m]$, with nonzero first exponent and product one | `Relation k m` | Integer powers are interpreted in the rationals |
| A071537 is the least relation endpoint $m\ge k$ | `A071537` uses `Nat.find` | Zero extends the function outside the existence domain |
| Fixed $k$ and sufficiently large prime $p$ | `claim`: $\forall k\ge1,\ \exists N,\ \forall p,\ p\text{ prime}\land N\le p\Rightarrow T(p,k)=A071537(k)$ | $k\ge1$ is A071537's offset; the threshold depends only on $k$ |

## Motivation

This is a Tier 1 externally stated OEIS conjecture. The settlement is `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences.result`, with `admission_basis: open-problem-resolution (#18687; Proved)`, `generality: I`, and `utility: none`. There is no anchor atom. The theorem is uniform in $k$ and in all sufficiently large primes; finite tables alone cannot establish it.

## Gap

The preregistration's literature screen found no settlement in the searched OEIS entries, Epoch OEIS Open benchmark, AlphaProof Nexus and formal-conjectures repositories, S. Fried's OEIS-proof papers, or this repository. A071537's permutation theorem concerns the comparison sequence itself and does not settle the prime-power table. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Write $v(j)$ for the finite prime-factorization vector of $j$. Integer-exponent relations give rational linear relations among these vectors. Denominator clearing and rational linear separation provide, for each endpoint earlier than the least relation endpoint, an integer functional that vanishes on all later vectors but is nonzero on $v(k)$.

For the upper bound, reduce the exponents of a rational relation modulo a sufficiently large prime. The multiplicity at $k$ stays positive and every multiplicity is below the prime. Replicating and sorting produces a list ending no later than the relation endpoint. The product is a rational prime-power; integral closedness of the integers supplies an integer root.

For the lower bound, a putative admissible list ending early forces the prime to divide the product of its positive multiplicity at $k$ and the separating functional's nonzero value there. A prime larger than the absolute value of that value cannot divide it, and cannot divide a positive multiplicity smaller than itself. Taking a maximum of finitely many thresholds proves equality. This argument also includes $k=1$.

## Falsifier

The conjecture would be refuted by a fixed $k\ge1$ with unequal values at arbitrarily large primes. A single exceptional prime is compatible with the quantifiers. The exact Lean statement, its literal definitions, and the standard axiom closure specify the formal scope.

## Evidence

`D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.result` proves `claim`. Its public surface consists of the five source definitions and this one theorem. The private factorization-vector and replicated-list representations and the eighteen private helper theorems are consumed by the settlement.

### Judgement form

| module | declaration | declaration statement_id | proof_shape | escape_witness | consumers | direct frozen dependencies |
| --- | --- | --- | --- | --- | --- | --- |
| `D5/S3/Arith/Factorization/OeisA343825KageyPowerSequences` | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.result` | `sha256:b70767e06e5f4d2ceb5b7a4416d8da7a35156fe8425a4be1f4d417501d1fe661` | bind-only | none | none; settling result | `D5/S3/Factorization/Embeddings/RationalValuationRecovery` + `D5.S3.Factorization.Embeddings.RationalValuationRecovery.rational_finite_valuation_kernel` + `sha256:3961205c906d9af154530a8dc120be7f32d5f1f74bb6ea63fc3452c9fec4a93c` |

Module admission_basis: `open-problem-resolution (#18687; Proved)`.

| helper (full source name) | proof_shape | direct consumer(s) |
| --- | --- | --- |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.clear_den` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.separator` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.clear_den_on` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.relation_of_mem_span` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.rat_one_of_val` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.vec_relation` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.val_prod` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.vec_relation` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.vec_relation` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.relation_of_mem_span`, `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.relation_exists` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.relation_of_mem_span` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.separator` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.separator` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.lower_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.repList_count` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.repList_mem`, `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.repList_prod`, `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.repList_mem` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.repList_prod`, `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.repList_sorted` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.repList_prod` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.list_endpoints` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.residue_pow` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.int_root` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.upper_valid` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.result` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.valid_bounds` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.lower_valid`, `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.result` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.lower_valid` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.result` |
| `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.relation_exists` | bind-only | `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.result` |

The module's admission basis is the external open-problem resolution, rather than a new general-purpose escape witness. The four-slot escape audit for `result` is unfinished: [#19920](https://github.com/the-omega-institute/trureturing/issues/19920). The dependent threshold and universally quantified prime family require a source reconstruction and equivalence bridge, whole-family variation, slot sensitivity, and observational dependence. No validated registration is asserted.

### Experiment

[The comparison experiment](https://github.com/the-omega-institute/trureturing-experiments/tree/f3e1e2308481c84a0c7f7d21df488ddf8e172da3/docs/reports/oeis-a343825-kagey-power-sequences) is pinned to commit `f3e1e2308481c84a0c7f7d21df488ddf8e172da3`. Command: `python3 check.py 150`, exit 0. The SHA-256 of `check.py` is `6f03c345b4be85cfb0db53eb2a59723466002e1c82f28c358d8ea920823b74c5`.

Computed: A071537's listed values for $1\le k\le67$ agree, and the A343825 rows at $p\in\{2,3,5,7\}$ agree for $0\le k\le10$. For $1\le k\le150$, equality holds at $p\in\{31,41,43\}$; at $p=37$ the unequal indices are exactly $144,147,150$. Among primes at most $31$, the exceptions for $k=2$ are exactly $\{2\}$ and for $k=32$ exactly $\{2,3,5\}$. These are finite computations, not uniform proofs.

## Triage

| Target item | Status and evidence |
| --- | --- |
| Eventual equality for every fixed $k\ge1$ | Proved in Lean: `D5.S3.Arith.Factorization.OeisA343825KageyPowerSequences.result` |
| Remaining goals of this settlement | None; the theorem states the entire preregistered conjecture |
| Explicit threshold as a function of $k$ | Open; the proof selects finite witnesses and a maximum, without a numerical bound in $k$ |
| Characterization of exceptional primes | Open; the experiment gives only the tested finite instances |
| The separate prime-row permutation assertion | Open; eventual equality with $k$ fixed does not give a permutation for any fixed prime |
| The $p=37$ exception | Computed by the pinned experiment, exit 0: exactly $k=144,147,150$ within $1\le k\le150$; all three agree at $41$ and $43$ |
| Literature status | `ASSUMED-UNVERIFIED` completeness of the preregistration's screen |

### What the settlement shows

Proved in this module: the relation minimum over the rationals is exactly the prime-power sequence minimum once the prime is sufficiently large for each fixed starting index. The decisive mechanism is finite rational separation combined with reduction of integer exponents modulo a prime. The theorem imposes no upper bound on $k$ and applies to every prime above its existential threshold.

The three neighbouring questions in the table remain open. In particular, the theorem exchanges neither the fixed-index and fixed-prime roles nor the order of their quantifiers, so it does not settle the row permutation assertion. The source's comparison with A343881 and its other statements are not premises of `result` and receive no additional formal conclusion here.

## ASSUMED-UNVERIFIED

The literature screen is not exhaustive and no priority claim is made. The identification of the literal Lean definitions with the OEIS wording is a source-fidelity assessment. The experiment's modular elimination implements a mathematical comparison independently of the kernel proof; its finite output is computational evidence only. The escape audit remains unfinished under #19920.
