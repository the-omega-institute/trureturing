---
slug: florian-dvorakova-2016-generalized-pseudostandard-periodicity
bibkey: floriandvorakova2016periodicity
doi: 10.37236/4771
url: https://arxiv.org/abs/1508.02020
triage: theorem
motivation_gids:
  - D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.result
---

# Periodicity of generalized pseudostandard words

## Problem

J. Florian and Ľ. Dvořáková, *On periodicity of generalized pseudostandard words*, Electronic Journal of Combinatorics 23(1), P1.2, Conjecture 29, asks whether a generalized pseudostandard word over any finite alphabet is periodic exactly when its normalized directive sequence satisfies the two tail conditions. The source and literal definitions are in [the Library note](../Library/Rewriting/floriandvorakova2016periodicity.md). The named assertion is proved by `D5.S1.Words.Palindromes.GeneralizedPseudostandardPeriodicity.result`. Preregistration: [#15626](https://github.com/the-omega-institute/trureturing/issues/15626).

For some common tail offset $k$, the conditions are:

1. $\vartheta_{k+i}(\delta_{k+i+1})=\vartheta_{k+j}(\delta_{k+j+1})$ for all $i,j\ge1$.
2. For all $i\ge1$, the image under $\vartheta_{k+i+1}$ of every $\vartheta_{k+i}$-palindrome is a $\vartheta_{k+i+2}$-palindrome.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Every finite alphabet and every involutory antimorphism | `claim` quantifies over `α : Type`, `Fintype α`, `DecidableEq α`; `InvAntimorphism` has the literal concatenation-reversal and involution laws | No alphabet-cardinality restriction |
| Successive shortest pseudopalindromic closures, starting with the empty word | `Generates`, with `IsClosure` expressing prefix, fixed word, and shortest length | Directive indices begin at one; the entries at zero are unused |
| Normalized directive generating the same infinite word | The first conjunct of `claim`; `Generates.normalization_exists` | Every prefix fixed by any involutory antimorphism occurs as a stage |
| The word is $d$-ary | `Function.Surjective u` | Every alphabet letter occurs |
| Periodicity | A positive natural period in `Function.Periodic` | Pure periodicity; the sufficiency proof constructs a pure period directly |
| A common finite directive prefix | One existential natural offset in `TailConditions` | Both directive sequences have the same offset |
| Condition 1, all tail indices | The first conjunct of `TailConditions`, with images of singleton words and both indices at least one | Literal letter-image equality |
| Condition 2, every fixed finite word | The second conjunct of `TailConditions` | Literal universal palindrome transport |
| Both directions | The second conjunct of `claim` is an equivalence; `result` proves `claim` | No source clause is dropped |

Palindromes use Mathlib's `Function.IsFixedPt` and infinite prefixes use the literal `List.ofFn` expression. Finite decidable equality supports the finite-alphabet formalization and does not restrict finite alphabets. The normalization conjunct makes the normalized sequence in the source assertion available for every generated word.

## Motivation

The source proves periodicity criteria for restricted alphabets and states the arbitrary finite-alphabet characterization as Conjecture 29. The two tail conditions constrain both the next letter and the interaction of successive antimorphisms.

## Gap

The changing-antimorphism criterion is not supplied by a fixed-antimorphism result. The bounded source and citation search recorded in #15626 finds no earlier arbitrary-alphabet settlement. That search is not an exhaustive novelty certificate; the unread ČVUT thesis remains a literature boundary.

## Route

Write each involutory antimorphism as reversal after its involutive letter permutation. The supporting module inserts the earliest missing fixed prefix between adjacent stages and enumerates all fixed-prefix lengths to obtain normalization. Its strong-induction `period_extend_left` argument supplies the overlap step used by `closure_prefix`, `earliest_insertion`, `Generates.adjacent_prefix_closure` and `Generates.normalization_exists`.

For sufficiency, palindrome transport is equivalent to conjugation of the letter permutations. Adjacent permutation products are constant on the tail. The closure suffix estimate makes positive stage-length gaps nonincreasing, so they stabilize to a positive $g$. Iterating the permutation product over its finite order supplies a positive pure period.

For necessity, extend a periodic word to integer indices. Long fixed prefixes give global reflections. Reflection centers form a coset of a subgroup of $\mathbb Z$; normalization and this coset force stabilization of positive gaps. Reflection conjugation gives condition 2, and the common reflected letter gives condition 1.

## Falsifier

A counterexample would consist of a finite alphabet, a generated word and normalized directive satisfying one side of the periodicity equivalence but not the other, or a generated word with no normalized directive. The kernel-checked `result` excludes these configurations within the stated definitions and axioms. The least-period formula is outside that assertion.

## Evidence

The two formal owners are [PseudopalindromicNormalization](../D5/S1/Words/Palindromes/PseudopalindromicNormalization.lean) and [GeneralizedPseudostandardPeriodicity](../D5/S1/Words/Palindromes/GeneralizedPseudostandardPeriodicity.lean), with corresponding Blueprint Scribes. The settling node has one `OpenProblemResolutionClaim` of kind `Proved`.

The finite experiment is [the pinned experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/4cb84370f8da7ba85f147f92e55b423c9feff76e/docs/reports/florian-dvorakova-2016-generalized-pseudostandard-periodicity). The measured command is `python3 /tmp/op-fdpw/stage-b-experiment-check.py`, using the byte-identical export of that pinned script; the reproducible command in the pinned directory is `python3 check.py`. Script SHA-256: `8372d38f2d12809dc76457fd2b6af9bdc4887ea608528e912f4c5732d5d84f28`. Exit 0. The screen checks 1,072 involution triples on alphabets of sizes 2–4, with all fixed words up to length 5; 400 random words for the shortest-closure comparison; and 1,500 random directives on alphabets of sizes 2–5 with prefix cap 1,500. It reports 173,073 adjacent-prefix closure steps and 720 d-ary cases: 336 with a small period, one with a longer observed period, and 383 failing the tail conditions with no observed period. It also reports 265 non-d-ary cases. The final reading is `bad= 0`. These are finite-prefix observations, not an unrestricted proof.

The four-slot escape audit is unfinished: [#15921](https://github.com/the-omega-institute/trureturing/issues/15921). Every public theorem, including the positive settling `result`, is an audit target. No `declared_validated` registration is asserted.

## Triage

### What the settlement shows

- **Kernel-checked:** normalization exists over every finite alphabet, by earliest insertion. Evidence: `PseudopalindromicNormalization.Generates.normalization_exists`; the consumed insertion chain is stated in Route.
- **Kernel-checked:** the tail conditions imply a positive pure period. Evidence: the sufficiency direction of `GeneralizedPseudostandardPeriodicity.result`, using private `gap_bound`, `TailConditions.stable_gap`, `TailConditions.adjacent_product`, `TailConditions.perm_periodic`, `tail_sufficient_period`. A constructed period is $g\operatorname{ord}(\rho)$, without a least-period assertion.
- **Kernel-checked:** a positive pure period implies the tail conditions for a normalized directive of a word using every letter. Evidence: the necessity direction of `result`, using private `periodic_center_coset`, `Generates.periodic_stable_gap`, `Generates.periodic_conjugation` and `Generates.tail_necessary`.
- **Proved in prose:** a strict lower bound for closure fails on a palindromic input. If $\vartheta(w)=w$, the input itself is a shortest fixed extension, so its closure has length $|w|$. **Kernel-checked:** the valid bound is $|w|\le|z|\le2|w|$ for `IsClosure θ w z`, by the prefix component of `PseudopalindromicNormalization.IsClosure` and private `PseudopalindromicNormalization.closure_bounds`, respectively. The strict growth of generated stages is a separate statement, `Generates.strict_growth`, since a letter is appended before closure.
- **Kernel-checked:** global reflection conjugation supplies the changing-antimorphism relation for every finite alphabet. Evidence: private `GeneralizedPseudostandardPeriodicity.reflection_conjugation` and `Generates.periodic_conjugation`, used by `result`; no ternary-specific identity is assumed.
- **Computed:** the pinned finite screen has exactly the scope and readings stated in Evidence. It supplies finite checks only, including the observed least-period equality; it establishes no uniform least-period formula.
- **ASSUMED-UNVERIFIED:** the ČVUT thesis was not readable through the recorded NyxID Firecrawl request, which returned HTTP 402. Evidence: the literature reading in #15626.
- **Open:** the least-period formula $p=g\operatorname{ord}(\rho)$ remains unproved here and is not part of `claim`.

Normalization does not require surjectivity; the periodicity equivalence in `claim` uses it to express the source's $d$-ary condition. The arbitrary finite alphabet replaces the source's ternary restriction for this conjecture. No additional source theorem or neighboring conjecture is claimed as a separate settlement. Bounds on closure and strict growth apply as stated above; a stronger strict closure lower bound is false. An exact least-period characterization is a neighboring question and remains open.

## ASSUMED-UNVERIFIED

The literature screen is bounded, and the ČVUT thesis is unread for the reason stated above. The finite screens do not establish the unrestricted theorem or the open least-period formula. Source and literature checks attributed to the orchestrator in #15626 are source-reported; the formal declarations are verified by Lean independently of those reports.
