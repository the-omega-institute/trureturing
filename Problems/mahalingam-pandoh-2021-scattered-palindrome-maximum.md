---
slug: mahalingam-pandoh-2021-scattered-palindrome-maximum
bibkey: mahalingampandoh2021scatteredpalindromes
doi: null
url: https://arxiv.org/abs/2108.02729v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.result
---

# Mahalingam–Pandoh maximum number of scattered palindromes

## Problem

K. Mahalingam and P. Pandoh, *Counting scattered palindromes in a finite word*, arXiv:2108.02729v1, §5, Conjecture 5.6, states:

> The maximum number of scattered palindromic subwords in a word of length $n$ is $3(2^{\lceil n/2\rceil-1})-2$ if $n$ is odd, $2^{n/2+1}-2$ if $n$ is even, and this bound is achieved only when $q=\lceil n/2\rceil$ if $n$ is odd, $\frac n2$ and $\frac n2+1$ if $n$ is even.

$SP(w)$ counts distinct nonempty palindromic scattered subwords, rather than their embeddings. A scattered subword is a subsequence; $q$ counts the distinct letters in $w$. Write $M(n)$ for the displayed maximum.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Scattered containment and palindromes (§2) | `spal` uses `List.sublists.toFinset` and excludes the empty word while requiring reversal equality. | Every word over a decidable alphabet; duplicate embeddings count once. |
| $SP(w)=|SPAL(w)|$ and $q=|Alph(w)|$ (§2) | `sp` and `alphabetSize`. | Cardinalities of the literal source objects. |
| The two parity cases of $M(n)$ | `maxSP`. | Natural division $(n+1)/2$ represents the ceiling; subtraction is truncated natural subtraction. |
| Maximum over all length-$n$ words | First conjunct of `claim`; `result`. | Universal bound over every decidable alphabet, including the empty word. |
| Attainment of the maximum | Second conjunct of `claim`; `attainment`; `result`. | Every $n\ge1$ and every permitted $q$; witnesses are natural-number words. |
| Only the specified alphabet sizes | `permittedQ`, third conjunct of `claim`; `result`. | Every extremal nonempty word; the even alternatives form a disjunction. |

The positive-length assumption applies to attainment and necessity. The universal bound includes $n=0$ as an additional proved boundary case. Decidable equality enables finite-set cardinalities; it does not restrict a finite word's letter pattern. Natural-number letters provide existence witnesses and impose no restriction on the universal clauses.

## Motivation

The exact maximum and its permitted alphabet sizes settle the three-clause assertion preregistered in [#15450](https://github.com/the-omega-institute/trureturing/issues/15450). The motivating frozen declaration is `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.result`. The supporting inequality concerns general monotone discretely convex functions and disjoint endpoint pairs.

## Gap

The source proves the fixed-alphabet formula for $q\ge n/2$ in Theorem 5.4, but states the unrestricted maximum as Conjecture 5.6. Its literature screen in #15450 records no prior settlement within the searched scope. A uniform estimate for all first-last endpoint matchings supplies the missing bound for unrestricted alphabets.

## Route

Partition the palindromes by their outer letter. Let $r$ count letters occurring at least twice, $s$ count letters occurring once, and $v_a$ be the factor between the first and last occurrences of a repeated letter $a$. The decomposition is

$$SP(w)=s+\sum_{a\text{ repeated}}(2+SP(v_a)).$$

The supporting `matching_bound` states that an increasing discretely convex natural-valued function has no greater aggregate gap cost on any disjoint endpoint matching than on the nested matching. Strong induction applies this to $f=M$. The exact recurrence, in its valid domain, is $M(n+2)=2M(n)+2$. Telescoping gives, with $k=|w|-2r$,

$$SP(w)+M(k)\le s+M(|w|),\qquad s\le k\le M(k).$$

For equality, the residue budget forces $s=k=M(k)$. Since $M(k)=k$ exactly for $k\le2$, parity gives $q=r+s=(|w|+k)/2$, precisely the permitted alphabet sizes. Fresh matching outer pairs around zero, one or two distinct central letters provide attainment.

## Falsifier

A word with $SP(w)>M(|w|)$, an extremal nonempty word with a forbidden alphabet size, or a permitted $(n,q)$ with no attaining word would falsify the corresponding conjunct of `claim`. `result` proves all three conjuncts without an additional mathematical hypothesis.

## Evidence

- Supporting module: `D5/S1/Words/Palindromes/ScatteredPalindromeMatching.lean`; public `matching_bound` and `nestSum_succ`.
- Settling module: `D5/S1/Words/Palindromes/ScatteredPalindromeMaximum.lean`; public `result : claim`. Private theorem names below refer to declarations in this module, whose proofs are checked with it.
- Canonical Scribes and their emitted Markdown mirror every public declaration. The settling node has one `OpenProblemResolutionClaim` with status Proved.
- Source note: `Library/Words/mahalingampandoh2021scatteredpalindromes.md`; arXiv:2108.02729v1, §2 and §5.
- The axiom closure of every public declaration is contained in {`propext`, `Classical.choice`, `Quot.sound`}.
- Escape audit unfinished: [#15593](https://github.com/the-omega-institute/trureturing/issues/15593). The targets are `ScatteredPalindromeMatching.nestSum_succ`, `ScatteredPalindromeMatching.matching_bound` and `ScatteredPalindromeMaximum.result`. The `DependentFamily.realize` registration lacks `ArenaRef`, original-statement `Implementation`, `Correspondence`, `VariationEvidence`, `Sensitivity` and `SourceSelection`, including telescope reconstruction, an equivalence bridge and actual observational dependence. The delivered-head DTR reading is `DTR-Unregistered` (Observe) for each of these three targets. No Reg source is delivered.

### Experiment

[Experiment directory at commit `925c63cebbbc422edb2f0d9ecb8e76aad0f26ee9`](https://github.com/the-omega-institute/trureturing-experiments/tree/925c63cebbbc422edb2f0d9ecb8e76aad0f26ee9/docs/reports/mahalingam-pandoh-2021-scattered-palindrome-maximum), containing `check.py`. Command: `python3 check.py`; exit 0; script SHA-256 `3ff6686dddc020b9051d6a624b090a331d5a35ea92c77f37c8944b1d3cd1571b`; final reading `bad= 0`.

The two counters agree on every relabelling-class representative of lengths 1–8. Exhaustive per-$q$ maxima for lengths 1–12 agree with the overall formula and permitted alphabets; lengths 1–10 agree with the source's Table 3. At lengths 11 and 12 the maxima are respectively 94 and 126, with attaining alphabet sizes respectively $\{6\}$ and $\{6,7\}$. The source's $q\ge n/2$ formula is checked through length 12. The outer-letter decomposition is checked on 3000 seeded random words of lengths 1–14 over at most five letters. The recurrence is checked for $2\le t<60$, and increments, convexity and the equality boundary for $0\le t<60$. The matching estimate for $f=M$ is checked exhaustively for $2\le n\le10$. The nested construction is checked for $0\le r\le6$ and $k\in\{0,1,2\}$, excluding the empty word. These are finite computations, not uniform proofs.

## Triage

`theorem`: Conjecture 5.6 is Proved by `result`, under the open-problem-resolution basis of #15450. Both modules have generality G and `utility: none`.

| Target item | Status and evidence kind | Evidence and boundary |
| --- | --- | --- |
| Outer-letter decomposition | Proved, kernel-checked. | Private `sp_decomposition` partitions the distinct nonempty palindromes. |
| Convex endpoint matching | Proved, kernel-checked. | Public `matching_bound`; its convex uncrossing and induction apply to arbitrary increasing discretely convex $f$. |
| Recurrence $M(n+2)=2M(n)+2$ | Proved, kernel-checked. | Private `maxSP_add_two`; no invalid subtraction recurrence at $n<2$. |
| Unrestricted bound and forced extremal alphabets | Proved, kernel-checked. | Private `sp_residue_bound`, `equality_permitted`, `bound_and_onlywhen`, and public `result`. Equality in the residue budget, which includes the matching estimate, forces the permitted $q$. |
| Experiment readings | Computed. | The pinned experiment entry above, with exactly its finite tested ranges, exit and SHA-256. |
| Extremal words determined by the construction | Proved, kernel-checked for the canonical natural-number family. | Private `construct_length`, `construct_alphabet`, `construct_sp` and `attainment` prove length $2r+k$, alphabet size $r+k$ and count $M(2r+k)$ for $k\le2$. |
| Sharp maximum at fixed $q<n/2$ | Open as a uniform question. | Table 3 and the experiment give finite values; neither is a general formula proved by `result`. |
| Characterization of all extremal words | Open. | `result` proves necessary alphabet sizes and the existence of extremizers, not a complete classification of their orderings. |

### What the settlement shows

The decisive mechanism is the outer-letter decomposition combined with the convex endpoint matching bound and telescoping recurrence. The kernel-checked estimate is uniform in length and the word's decidable alphabet. The supporting matching theorem also applies to every increasing discretely convex natural-valued function, beyond $M$.

The canonical attaining family starts with the distinct central letters $0,\ldots,k-1$, then adds fresh matching outer letters $k,k+1,\ldots,k+r-1$, for $k\in\{0,1,2\}$. The construction is nested, with length $2r+k$ and $r+k$ distinct letters. Injective relabelling preserves subsequences, reversal and distinctness, hence preserves $SP$ and the alphabet size; this relabelled-family statement is proved in prose by that bijection, not a separate Lean theorem. It does not exhaust all extremizers.

Equality also forces every repeated letter to occur exactly twice: in prose, the identity $|w|=\sum_a\operatorname{count}_w(a)$ and $s=|w|-2r$ leave no surplus occurrence beyond two for a repeated letter. This is a necessary condition, not a complete characterization. No separate Lean statement claiming this multiplicity classification is delivered.

The source's Theorem 5.4 remains a literature result for fixed $q\ge n/2$; the unrestricted maximum no longer needs Conjecture 5.6 as an assumption. This delivery does not formalize every fixed-alphabet value or a complete extremal-word classification. Both follow-up questions remain open here.

## ASSUMED-UNVERIFIED

The literature screen in #15450 did not obtain Holub–Saari (2009) in full. Its non-settlement is inferred from the source authors citing it while stating this conjecture; no exhaustive literature-completeness claim is made. Absence of a collision in an unpublished lane is unverified because the designated unpublished-lane inventory is absent. The escape audit remains unfinished under #15593; kernel verification does not complete that registration.
