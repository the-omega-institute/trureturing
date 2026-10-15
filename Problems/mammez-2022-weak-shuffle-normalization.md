---
slug: mammez-2022-weak-shuffle-normalization
bibkey: mammez2022weakshuffle
doi: 10.24330/ieja.1060709
url: https://arxiv.org/abs/2003.09142
triage: theorem
motivation_gids:
  - D5/S1/Words/WeakShuffleNormalization.result
---

# Normalization of weak shuffle products

## Problem

C. Mammez, *Weak stuffle algebras*, International Electronic Journal of Algebra 32 (2022), 1–45, DOI 10.24330/ieja.1060709, arXiv:2003.09142v3, Conjecture 3.10 (arXiv v3 Conjecture 14) states: “Proposition [3.9] is still true for any countable alphabet.” Proposition 3.9 asserts that a weak shuffle product over a characteristic-zero field is algebra-isomorphic to its normalized product; its proof covers alphabets with two or three letters.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| A field of characteristic 0 | `K`, `Field K`, `CharZero K` in `claim` | Literal algebraic hypotheses |
| Noncommutative polynomials on an alphabet | `KX X K`, finitely supported coefficients on `List X` | Every alphabet, including empty and uncountable ones |
| Empty word is the unit and the two-branch weak shuffle recursion | `wsWord`, with the first branch removing the left head and the second removing the right head | Literal recursion; the contraction coefficient is zero |
| Bilinear extension; associative and commutative product | `wsMul` and `IsWeakShuffle` | Both quantified identities occur in the predicate |
| Exceptional off-diagonal coefficient becomes one, its reverse becomes zero | `norm1` | Both ordered tests are explicit |
| Other off-diagonal coefficients are retained and diagonal coefficients are unchanged | `norm1`, `norm2` | The reverse exceptional test expresses the first bullet's forced reverse value |
| An algebra isomorphism between the two products | `claim`, `result` | A linear equivalence preserves the unit and intertwines multiplication |
| Any countable alphabet | `X : Type` in `claim` | Stronger: no countability hypothesis |

`DecidableEq X` is the implementation interface for finite-support words. Classical choice supplies it for every alphabet, so it does not restrict the mathematical scope. The implicit `Zero K` of `KX` and classical coefficient tests likewise do not change the definitions.

## Motivation

Preregistration [#15815](https://github.com/the-omega-institute/trureturing/issues/15815) supplies the verbatim source, the characteristic-zero hypotheses, the explicit normalization conventions and the bounded literature screen. The settling declaration is `D5.S1.Words.WeakShuffleNormalization.result`, with admission basis `open-problem-resolution (#15815; Proved)` and `utility: none`.

## Gap

The source leaves the extension beyond two or three letters conjectural. Its Remark 3.11 discusses interactions with further letters. The normalization theorem closes that extension without countability.

The escape audit for the sole public theorem `result` is unfinished. Issue [#16034](https://github.com/the-omega-institute/trureturing/issues/16034) records the unproved exact statement-to-law bridge, variation, sensitivity and observational dependence for a faithful dependent family of candidate linear equivalences, together with missing source-coordinate and enrolled-readout evidence. No Reg file or validated registration is delivered.

## Route

For an exceptional ordered pair $e=(a,b)$, put $P_e=\{x:f_1(x,b)\ne0\}$. Let $h_e(w)$ count the occurrences of $a$ in the maximal initial $P_e$-segment of $w$ when the next letter is $b$, and be zero otherwise. The proof establishes barrier laws from coefficient comparisons in commutativity and associativity. These laws imply a conservation identity for every nonzero recursion path. The word factor is

$$q(w)=\prod_{e=(a,b)\in E}f_1(a,b)^{-h_e(w)}.$$

Only pairs of letters occurring in $w$ contribute, so this product is finite even for an uncountable alphabet. The linear map $\Phi(w)=q(w)w$ has inverse given by reciprocal factors. The conserved path exponent proves the multiplicative intertwining identity after summing paths and extending bilinearly.

## Falsifier

A transcription error in the recursive product or normalization clauses, a counterexample to the barrier or path-exponent identities under the hypotheses, or an earlier publication settling Conjecture 3.10 would invalidate the claimed source correspondence or novelty. The kernel proof covers every characteristic-zero field and alphabet in `claim`; a finite numerical test is not its replacement.

## Evidence

The sole public theorem is `D5.S1.Words.WeakShuffleNormalization.result : claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. Its Scribe node records one `OpenProblemResolutionClaim` with `ResolutionKind.Proved`. The literature locator is `Library/Words/mammez2022weakshuffle.md`.

The experimental entry is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/de327b4c26fe4be8a1f1110ebd0a6e20e3116e34/docs/reports/mammez-2022-weak-shuffle-normalization), containing `check.py` with SHA-256 `06c1446836805820611383e917806782662510bc500149d7b5ff04b93f3a733e`. The command `python3 check.py` exited 0. In 150,000 sampled coefficient systems on alphabets of size 2–5, 9363 were commutative and associative for all words of length at most 2. Among these, 1073 had an exceptional pair: 832 on two letters, 198 on three and 43 on four; six had a case-(b) diagonal letter. For these exceptional systems the rescaling identity held for all pairs of words of length at most 3, and the normalized product was commutative and associative for all words of length at most 2. The final reading was `bad= 0`. No five-letter exceptional system occurred. These are finite readings, not a universal proof.

## Triage

### What the settlement shows

- **Proved, kernel-checked mechanism.** The private lemmas `barrier_outside`, `barrier_source` and `actual_barriers` derive from associativity in characteristic zero the barriers that prevent a head outside $P_e$ from being selected against a $P_e$-head, and prevent $a$ from being selected against any $P_e$-head. `APath.exponents` proves $t+h_e(u)+h_e(v)=h_e(w)$; `Run.toAPath` applies it to every nonzero recursive path. `Run.q_identity` then proves $q(w)c=q(u)q(v)c'$ path by path. `diagonal_wsWord`, `diagonal_wsMul` and `result` establish the algebra isomorphism. These helpers belong to the settling module and are used in its proof.
- **Proved, kernel-checked scope.** `result` quantifies over every alphabet, so includes uncountable alphabets. Its witness is the private `diagonalEquiv (q f1) (q_ne_zero f1)` construction; the finite product in `q` gives explicit finite-support exponents.
- **Computed.** The pinned experiment, command, SHA-256 and scope in Evidence give `bad= 0` for the 1073 sampled exceptional systems; they do not extend the sample to all coefficient systems or word lengths.
- **Open.** An analogous normalization of weak stuffle products with $f_3\not\equiv0$ is not established here. The source treats weak shuffle normalization with zero contraction and presents weak stuffle examples separately; the contraction term introduces a different recursion.
- **Open.** Classification of algebra isomorphism classes beyond normalization is not established here. The source's classification discussion after Lemma 18 leaves, among other pairs, $C_9$ versus $C_{13}$ and $C_{12}$ versus $C_{14}$ undecided; normalization does not decide those isomorphism questions.
- **Effect on source results, proved consequence.** Proposition 3.9's normalization conclusion extends to all alphabets. The other source results retain their hypotheses; this theorem does not classify weak stuffle products or decide their general isomorphism classes.

## ASSUMED-UNVERIFIED

Worldwide novelty and priority beyond the bounded literature screen in #15815 are not established. The numerical experiment covers only its stated finite sample and word lengths. The four-slot escape audit remains unfinished under #16034.
