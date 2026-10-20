---
slug: capitelli-somma-2024-all-odd-nonconvergence
bibkey: capitellisomma2024subtraction
doi: 10.48550/arXiv.2405.19593
url: https://arxiv.org/abs/2405.19593v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.result
---

# All-odd randomized subtraction games do not converge

## Problem

Nicolás Capitelli and Francisco Somma, “On sequences arising from randomizing subtraction games”, arXiv:2405.19593v1, Section 3, p. 7, state:

> However, we do not show that an all-odd subtraction set necesarily do not converge (although we conjeture it) nor we provide the exact limits of the even and odd subsequences for the (conjectured) non-convergent case.

The section assumes a finite nonempty subtraction set of positive integers with gcd one. A player selects uniformly among legal subtractions, and loses when none is available. Writing $A_n=\{s\in S:0<s\le n\}$, the next player's winning probability is $a_n=0$ if $A_n$ is empty and otherwise $a_n=1-|A_n|^{-1}\sum_{s\in A_n}a_{n-s}$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Finite subtraction set | `S : Finset ℕ` in `claim` | Finite sets, without an ordering or multiplicities. |
| Nonempty set | `S.Nonempty` | Preserved. |
| All subtractions odd and positive | `∀ s ∈ S, Odd s`; positivity follows for natural numbers | Preserved. |
| Section 3 assumes gcd one | `S.gcd id = 1` | Preserved in the public claim. |
| Uniform legal subtraction; no move loses | `legalMoves`, `winProb` | Literal preregistered recursion, including real division and truncated natural subtraction. |
| Does not converge | Absence of a real $L$ with `Tendsto (winProb S) atTop (𝓝 L)` | Preserved. |

The public `result` proves `claim`. No source clause is dropped. The private theorem `nonconvergence` proves the stronger statement without the gcd assumption.

## Motivation

The source proves convergence when the gcd-one subtraction set contains an even element. The all-odd result completes this qualitative dichotomy. It separates nonconvergence from the stronger questions of computing subsequence limits or determining characteristic-root multiplicities.

## Gap

Preregistration [#19195](https://github.com/the-omega-institute/trureturing/issues/19195) identifies the source's explicit conjecture and the bounded literature screen. That screen checked the arXiv record (only v1), the authors' publication lists, Capitelli–Privitelli arXiv:2012.06768 and classical renewal/take-away references. OpenAlex reported zero citations; the Semantic Scholar citation list returned HTTP 429. No settlement was found in that searched scope. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

Set $b_n=(-1)^n(1-2a_n)$ and $d_n=b_n+b_{n+1}$. Probability bounds give $-1\le b_n\le1$. Oddness turns the game recurrence into positive averaging for $b$.

If $n+1$ is not a new subtraction, the adjacent sums satisfy

$$
|A_n|d_n=\sum_{s\in A_n}d_{n-s}.
$$

If $n+1\in S$ and $A_n$ is nonempty, the changed denominator gives

$$
(|A_n|+1)d_n=\sum_{s\in A_n}d_{n-s}+b_n+1.
$$

The last term is nonnegative. Before the first legal move, $d_n$ is either zero or two; strong induction proves $d_n\ge0$ everywhere, and $d_{m-1}=2$ for $m=\min S$.

For $N\ge M=\max S$, use the forward-indexed finite window

$$
J_N=\sum_{s\in S}\sum_{0\le r<s}d_{N-s+r}.
$$

Telescoping and the full-move recurrence give $J_{N+1}=J_N$. The $s=M$ summand contains $d_{m-1}$ at $N=M$, so $J_M\ge2$. Hence $J_{M+n}=J_M\ge2$ for all natural $n$.

Convergence of $a_n$ would make adjacent differences tend to zero. The identity

$$
d_n=(-1)^n\,2(a_{n+1}-a_n)
$$

then gives $d_n\to0$ by bounded multiplication. Every term in the finite window tends to zero, contradicting its positive constant value. This argument needs no gcd condition and does not require showing that a hypothetical limit equals one half.

## Falsifier

A finite nonempty all-odd set with a convergent literal winning-probability sequence would falsify the claim. The proof must handle every change in the legal-move cardinality, preserve the startup term two, and use a common conserved window. The empty subtraction set has an identically zero sequence and is excluded. No theorem here classifies sets containing even moves without the source's gcd hypothesis.

## Evidence

The Lean module is `D5/S3/Combinatorics/Games/CapitelliSommaAllOddNonconvergence.lean`; its sole public theorem is `D5.S3.Combinatorics.Games.CapitelliSommaAllOddNonconvergence.result`. Its private helpers prove the stronger no-gcd theorem, the threshold identity, positivity, seed value, conservation and limiting contradiction. Its only direct import is `Mathlib.Topology.Instances.Real.Lemmas`; it imports no D5 owner.

The source note is [Capitelli–Somma](../Library/RecurrenceComposition/capitellisomma2024subtraction.md). The Scribe result displays the complete public claim and acknowledges that note.

### Experiment

The exact-rational checker is in [trureturing-experiments, commit 05c35921b138378509914de8d30660a98293945d](https://github.com/the-omega-institute/trureturing-experiments/tree/05c35921b138378509914de8d30660a98293945d/docs/reports/capitelli-somma-2024-all-odd-subtraction-nonconvergence). Command: `python3 docs/reports/capitelli-somma-2024-all-odd-subtraction-nonconvergence/check.py`, from that repository revision; exit 0. The `check.py` SHA-256 is `24aec8643260b64be3a352eadd67b96ad9ae0f9d905f886784fc72440b810738`.

The checker covers all 162 nonempty subsets of $\{1,3,\ldots,15\}$ with at most four members, computing $a_n$ for $0\le n<\max S+400$. It checks adjacent-sum nonnegativity, the seed value and the constant positive backward window. Its oscillation test is finite: the maximum adjacent difference in the last 49 pairs is at least $1/1000$; that finite observation alone is not a proof of nonconvergence.

For $S=\{1,3\},\{3,5\},\{1,3,5\},\{3,5,7\},\{5,7,9,11\}$, it computes 3000 terms and compares terms 2998 and 2999 with the predicted subsequence values to tolerance $10^{-9}$. Those comparisons use floating conversion of exact-rational errors. The corresponding coefficients are $-1/2,-1/8,-1/2,-2/15,-7/96$.

For coprime odd pairs with $k\in\{1,3,\ldots,15\}$ and $k<l<30$, the source's two-move coefficient expression agrees with the invariant-derived candidate on 14 pairs (all $k=1$) and disagrees on 57 pairs (all tested $k\ge3$). These finite comparisons do not prove a corrected coefficient formula or an erratum for untested pairs.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| Nonconvergence for every finite nonempty all-odd subtraction set, without gcd one | Proved; kernel-checked private `nonconvergence`, consumed by public `result` | All finite nonempty all-odd natural-number sets; `result` retains the source's gcd-one hypothesis. |
| Changing legal-move cardinality contributes $b_n+1$ and preserves nonnegativity | Proved; kernel-checked private `d_threshold` and `d_nonneg` | Every threshold with a previously nonempty legal-move set; `d_initial` handles startup. |
| First legal move gives $d_{m-1}=2$; full-move averaging conserves a positive finite window | Proved; kernel-checked private `d_seed`, `d_full`, `invariant_step`, `invariant_constant`, `invariant_positive` | $m=\min S$, and $J_{M+n}=J_M\ge2$ for $M=\max S$. |
| Exact-rational checker passes 162 all-odd sets | Computed; experiment entry above, exit 0 and stated script SHA-256 | The 162 sets and finite index ranges specified above. |
| Five coefficient examples; 57 disagreeing and 14 agreeing source-formula pairs | Computed; same experiment entry | Only the five listed sets and tested coprime pairs. Numerical agreement is not a limit theorem. |
| Question 3.4 coefficient formula and even/odd subsequence limits | Open in this formalization; not formalized | The proposed $\alpha_1=-I/(4\sum_{s\in S}s)$ and the corresponding limits have only the stated finite computational evidence here. |
| Source erratum beyond checker output | Open in this delivery; not formalized | No uniform correction or source theorem replacement is asserted. |
| Conjecture 3.3, simplicity of characteristic roots | Open; outside this settlement | Neither needed nor proved by the nonconvergence argument. |

The decisive mechanism is the positive seed that survives changes of averaging denominator and is retained by a conserved finite window. The proved extension removes the gcd assumption. The settlement supplies the qualitative all-odd half of the source's convergence discussion. It does not certify its quantitative two-move formulas or replace results relying on those formulas; the finite coefficient comparisons above delimit that separate issue.

The four-slot escape audit for the sole public theorem `result` is unfinished: [#19292](https://github.com/the-omega-institute/trureturing/issues/19292). No Reg mirror is delivered. The available enrolled equality/order/iff templates do not directly read its universal negated-convergence statement, and a dependent-family encoding lacks compiled reconstruction, bridge and variation/sensitivity evidence. This is no claim of `declared_validated` registration.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority remain `ASSUMED-UNVERIFIED`; the bounded source/literature screen is identified above. Coefficient and subsequence-limit formulas outside the exact tested scope are unproved here. The unfinished four-slot registration is tracked by #19292 and is distinct from the kernel proof of nonconvergence.
