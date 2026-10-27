---
slug: hefg-egfcongruences
bibkey: hanna2013derivativesubstitutioncongruences
doi: null
url: https://oeis.org/A232694
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Residue/HannaA232694Congruences.result
---

# Hanna's A232694 congruences

## Problem

Paul D. Hanna's OEIS A232694 COMMENTS conjectures ask whether the factorial-normalized coefficients of the formal equation $A'(x)=A(x(A'(x))^4)$ with $A(0)=1$ satisfy $3\mid a_n$ for $n\ge3$ and $8\mid a_n-1$ for every $n\ge0$. The source note records the four nominated OEIS records and the literal source text. The settling declaration is `D5.S1.Recurrence.Residue.HannaA232694Congruences.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| $A'(x)=A(x(A'(x))^4)$ and $A(0)=1$ | `IsSolution` in `HannaA232694Congruences` | The formal derivative, substitution and constant coefficient are literal. |
| $a_n=n![x^n]A$ is integral | The existential `a : ℕ → ℤ` with `eCoeff A n = (a n : ℚ)` | Integrality is a conclusion at every index. |
| $3\mid a_n$ for $n\ge3$ | The first divisibility conjunct in `claim` | The threshold and modulus are literal. |
| $8\mid a_n-1$ for all $n\ge0$ | The second divisibility conjunct in `claim` | The all-index residue is literal. |

## Motivation

Preregistration [#21485](https://github.com/the-omega-institute/trureturing/issues/21485) supplies the source, conventions, proof outline, experiment and literature screen. The source is recorded in `Library/RecurrenceComposition/hanna2013derivativesubstitutioncongruences.md`. The settling uses `open-problem-resolution (#21485; Proved)`. The supporting machinery is `D5/S1/Recurrence/Residue/HannaEGFMachinery`; the existing parity owner supplies convolution and coefficient identities through its private declarations.

## Gap

The OEIS record labels the two residue assertions as conjectures. The proof requires an integral triangular recurrence for derivative-substitution equations, coefficientwise residual transfer, a finite polynomial residual modulo $3$, and the exponential residual modulo $8$. The literature screen found no settlement in its searched scope; completeness remains `ASSUMED-UNVERIFIED`.

## Route

The shared machinery constructs the unique integral coefficient recurrence, transports coefficient congruences from an integral approximate solution, and cancels integral unit powers. The A232694 module supplies the finite coefficient certificate for the polynomial $1+x+x^2/2$ modulo $3$ and the exponential approximate solution modulo $8$, then applies the transfer theorem to the literal claim.

## Falsifier

A counterexample would be a rational formal solution with constant coefficient one whose factorial-normalized coefficient fails either nominated divisibility condition. A failure of the integral recurrence, residual divisibility or unit-cancellation hypotheses would also block the proof. Passing finite coefficient checks does not establish the assertions at every index.

## Evidence

`D5.S1.Recurrence.Residue.HannaA232694Congruences.result` proves the complete `claim` with axiom closure contained in `{propext, Classical.choice, Quot.sound}`. Its Scribe result node carries one `OpenProblemResolutionClaim` with resolution `Proved` on this dossier. The finite exact experiment is external evidence and does not replace the kernel proof.

### Experiment

[Experiment directory at commit `e2566e824df32e3f308cd1b801ef82dd17fa64cf`](https://github.com/the-omega-institute/trureturing-experiments/tree/e2566e824df32e3f308cd1b801ef82dd17fa64cf/docs/reports/hanna-efg-congruences/), script `check.py`. The pinned script exists at that commit and has SHA-256 `14fa66db49524fd5b8ccbf45b2245d0a4813980bff076b1b0a855d869393f259`. Command `python3 ../trureturing-experiments/docs/reports/hanna-efg-congruences/check.py`; exit 0. It recomputes exact terms for indices $0$ through $300$ for all four records, checks the nominated congruences, and compares the literal rational-series iteration through degree 12. The output ends with `ALL_CHECKS_OK`.

The same pinned experiment prints the exact terms A232694 $a_2=1$, A232695 $a_3=11$, A232696 $a_3=-1$ and $a_9=1315706$, and A232686 $a_1=1$ and $a_3=14$. Each predecessor fails the respective divisibility cutoff lowered by one.

## Triage

### What the settlement shows

Lists of approximate-solution coefficients in the table are factorial-normalized coefficients.

| Item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Shared integer triangular recurrence, uniqueness and modular approximate-solution transfer for every natural $k,p$ and the normalized reciprocal branch; no analytic convergence claim | Proved; kernel-checked | `HannaEGFMachinery.residual_transfer`, `sequence_unique` and the supporting recurrence declarations. Formal power-series reasoning is coefficientwise. |
| All eight nominated congruences for indices $0$ through $300$, with independent rational-series agreement through degree 12 | Computed; external exact computation | `check.py` at the pinned experiment commit, command and exit 0 above. Scope is exactly four records, indices $0\ldots300$, and iteration degree 12. Uniform extension beyond that finite range is supplied by the kernel-checked results, not by this computation. |
| Cutoff predecessors A232694 $a_2=1$; A232695 $a_3=11$; A232696 $a_3=-1$ and $a_9=1315706$; A232686 $a_1=1$ and $a_3=14$ | Computed; external exact computation | `check.py` at the pinned experiment commit, command, exit code and SHA-256 above. These values refute lowering the respective nominated cutoffs by one. |
| Additional A232686 powers-of-two and even-index conjectures | Open; literature/source boundary | They are outside the four nominated propositions and have no declaration in this delivery. |
| Exponential residual sum is divisible by $m$ after subtracting $1$ whenever $m\mid k$, with the separate $k=4$ modulus-8 estimate | Proved; kernel-checked | `HannaEGFMachinery.expSum_mod`, `expSum_four_mod_eight` and `exp_residual`. The statement is coefficientwise for formal series. |
| A232694 uses the coefficient list $[1,1,1]$ modulo $3$ and the exponential residual modulo $8$; nonterminal binomial terms are divisible by $8$ | Proved; kernel-checked | The residual certificate and `HannaA232694Congruences.result` prove the two nominated tails. |
| A232695 uses $[1,1,1,11]$ modulo $2$ and the exponential residual modulo $5$; the general divisor-of-$k$ exponential transfer is available | Proved; kernel-checked | `HannaA232695Congruences.result` and the shared exponential residual declarations. The additional $2^k$ cutoff family is outside this module. |
| A232696 uses $[1,1,1,-1]$ modulo $2$ and $[1,1,1,-1,2,6,-264,5370,-93750,1315706]$ modulo $4$; integral-unit cancellation transfers residual divisibility | Proved; kernel-checked | `HannaA232696Congruences.result`, `clear_inverse_power` and the finite residual declarations. |
| A232686 uses $[1,1]$ modulo $2$ and $[1,1,2,14]$ modulo $4$ for the two unbounded tails | Proved; kernel-checked | `HannaA232686Congruences.result` and its finite residual declarations. The additional powers-of-two and even-index claims remain open. |

### Literature status

The source and revision histories for A232694, A232695, A232696 and A232686 were read. Searches of the exact identifiers in arXiv, Crossref, Math StackExchange, repository issues and the bounded author/sequence screen found no settlement in the inspected scope. The primary sources are OEIS records without DOI or arXiv identifiers. Literature completeness and absence of an unlocated prior solution are `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`. The experiment is finite exact evidence only. The escape audit for newly public declarations is unfinished under [#21758](https://github.com/the-omega-institute/trureturing/issues/21758); no Reg source is delivered and no target is claimed `declared_validated`.
