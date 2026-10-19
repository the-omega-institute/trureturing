---
slug: atashpendar-mestel-roscoe-ryan-2018-kappa-alternating-minimizer
bibkey: atashpendar2018deletionentropy
doi: null
url: https://arxiv.org/abs/1807.11609v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.result
---

# Alternating binary words need not minimize positional autocorrelation

## Problem

Atashpendar, Mestel, Roscoe and Ryan, *A Proof of Entropy Minimization for Outputs in Deletion Channels via Hidden Word Statistics*, arXiv:1807.11609v1, printed page 7, state Conjecture IV.4:

> The alternating subsequence of length m, i.e., x = 1010..., minimizes the autocorrelation coefficient κ².

Equation (11) on the same page defines

$$\kappa^2(x)=\sum_{1\le r,s\le m}\binom{r+s-2}{r-1}\binom{2m-r-s}{m-r}[[x_r=x_s]].$$

The universal minimization statement is false. At length $m=348$, the word $x=(011001)^{58}$ has strictly smaller coefficient than the alternating word $a=1010\ldots$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Binary word of length $m$ | `x : Fin m → Bool` in `claim` | `false` is 0 and `true` is 1; each position is counted once. |
| Every positive length | The natural binder $m$ and hypothesis $1\le m$ | No restriction on positive lengths. |
| Equation (11) | Both literal double sums in `claim` | Positions are shifted down by one; the binomials become $\binom{r+s}{r}\binom{2m-2-r-s}{m-1-r}$. |
| $1010\ldots$ | `decide (i.val % 2 = 0)` inside the left sum | Even zero-based positions carry 1. |
| Minimizes | The weak inequality against every word $x$ | All words of the same length are included. |
| Refutation | `result : ¬ claim` | The strict instance at length 348 contradicts the universal inequality. |

Natural subtraction in the binomial arguments is exact on these indices. The binders represent source lengths, positions and words; there is no additional mathematical premise. The claim keeps the source expression literal, while the proof uses the frozen `D5.S3.Entropy.DeletionChannelEntropyOrdering.kappa2`, whose body is that expression.

## Motivation

The settling GID is `D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.result`, preregistered in [#19163](https://github.com/the-omega-institute/trureturing/issues/19163). This is a tier-1 externally published named conjecture, frozen by `deposit-uncovered` with no digestion atom. The separate finite entropy-ordering question in Section V has a different statement and a different settlement.

## Gap

The source's Conjecture IV.4 is restated in Atashpendar's thesis, arXiv:2003.11663v1, Conjecture 6.3.3.1. The bounded literature screen recorded in #19163 covers the source, the thesis, citation and keyword searches for autocorrelation of hidden words and alternating minimization, and Bernstein polynomial norms. Singhvi–Sabary–Bar-Lev–Yaakobi, arXiv:2407.10026v2, treats single deletions; Güntürk–Li, arXiv:2112.09183, treats one-bit Bernstein approximation. Neither supplies this settlement. Exhaustive citation coverage and worldwide priority are `ASSUMED-UNVERIFIED`.

## Route

The private witness is the length-348 word with 1 at residues 1, 2 and 5 modulo 6. The proof reuses the existing positional coefficient and the frozen `CoefficientTree` lookup representation. `Nat.choose_eq_factorial_div_factorial` rewrites each binomial through a kernel-verified table of factorials from 0 through 694. The two words' 348 row sums are verified in 29 groups of 12 rows. Private `certified_defect` sums those rows and proves the exact natural difference

$$\kappa^2(a)-\kappa^2(x)=72205957507799609560655006349961851153741188979911147028434625522749530872921557830312745632696473970699075168094975823625414930530038291298408559098670303166362893884742404955920795949372113567213277960.$$

The positive right side contradicts the zero difference implied by `claim` at $m=348$, giving `result`. Every helper theorem is private and consumed. All eight theorem proofs have `proof_shape: bind-only`; no escape witness or general Bernstein identity is claimed. The admission basis is `open-problem-resolution (#19163; Refuted)` and the computational utility is a certified instance with `basis=refutes`.

## Falsifier

A mismatched source coefficient, the wrong alternating parity, or a nonpositive defect would invalidate this route. The displayed sums retain both ordered positions and both binomial factors. The finite certificate proves a strictly positive defect for the specified witness, and the mirror expands the entire proposition and its negation.

## Evidence

Canonical source: `D5/S3/Combinatorics/Hamming/AtashpendarKappaAlternatingRefutation.lean`; public definition `claim` and sole public theorem `result`. Its corresponding Blueprint displays the complete defining expression and the complete refuted proposition.

The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

### Experiment

The [pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/a5756b1099047a77f58f3ef90c9f7b2a0ad39e5b/docs/reports/atashpendar-mestel-roscoe-ryan-2018-kappa-alternating) contains `check.py`. At commit `a5756b1099047a77f58f3ef90c9f7b2a0ad39e5b`, its SHA-256 is `730e191b128e8992ea0337f8c1d52df780c57ae7e9a7af7be87cdf506f43381a`. Command: `python3 docs/reports/atashpendar-mestel-roscoe-ryan-2018-kappa-alternating/check.py`, exit 0, `RESULT PASS`.

The exact script bytes from that commit were rerun. The exhaustive scope is $2\le m\le14$, the family scope is $1\le k\le60$ for $(011001)^k$, the strict counterexample cross-check is $m=348$, and the Bernstein identity controls are 20 seeded random words with $2\le m\le9$. These computations are evidence only for those finite scopes.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Universal alternating minimization | Proved in Lean: `result` negates the source conjecture. |
| Finite failure mechanism | Proved in Lean: private `certified_defect` certifies a positive alternating-minus-period-six weighted-sum difference at $m=348$; `result` consumes it. |
| Bernstein mechanism | Open as a kernel formalization. The supplied research explanation relates the coefficient to an $L^2(0,1)$ norm of a one-bit Bernstein polynomial and sixth-root interference. It is not an additional theorem of this module. |
| Short words | Computed: the pinned experiment exhausts all binary words for $2\le m\le14$, finding exactly the two alternating minimizers. The broader preregistration claim through 16 is not certified by this checker; lengths 15 and 16 are outside this computation. |
| Period-six family boundary | Computed: among $1\le k\le60$, the first positive defect for $(011001)^k$ occurs at $k=58$; $k=57$ is not a counterexample. This does not establish the globally smallest counterexample length. |
| Exact comparison at length 348 | Proved in Lean: private `certified_defect` gives the displayed positive integer. Computed independently: the experiment's direct double sum agrees with its integer path recurrence. |
| Bernstein identity controls | Computed: exact rational checks on 20 seeded random words with $2\le m\le9$. No uniform identity follows from these tests. |
| Smallest counterexample among all words | Open. This settlement supplies an upper bound of 348, not global minimality. |
| True minimizers at general large lengths | Open. Neither the witness nor the finite searches classify them. |
| Uniform period-six asymptotic family | Open as a kernel formalization, together with the Bernstein identity underlying the supplied research argument. The finite search through $k=60$ does not prove eventual failure for every sufficiently large $k$. |
| Period-four runner-up claim | Open in this delivery: the pinned checker does not certify runner-up classification. |
| Literature status | Literature reading: the source, thesis restatement, citation and keyword screen, and the two related papers are described under Gap. Completeness is `ASSUMED-UNVERIFIED`. |
| Source consequence | Proved in prose: since `result` negates the universal premise, any assertion of alternating minimization using that premise is unavailable. No additional physical conclusion or finite-entropy-ordering theorem follows. Independent source results and the separate finite entropy-ordering settlement have their own hypotheses. |

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded screen is not an exhaustive citation export or a worldwide priority proof. The research explanation and asymptotic family are not kernel-checked here. No global minimal-length or large-length minimizer classification is claimed.
