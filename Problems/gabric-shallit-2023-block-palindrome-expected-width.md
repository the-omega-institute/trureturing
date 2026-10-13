---
slug: gabric-shallit-2023-block-palindrome-expected-width
bibkey: gabricshallit2023blockpalindromes
doi: 10.1007/978-3-031-33180-0_14
url: https://arxiv.org/abs/2302.13147
triage: theorem
motivation_gids:
  - D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.result
---

# Expected largest block-palindrome width

## Problem

D. Gabrić and J. Shallit, *Smallest and Largest Block Palindrome Factorizations*, arXiv:2302.13147v2, §3, p. 5, Conjecture 5; WORDS 2023, DOI 10.1007/978-3-031-33180-0_14:

> Let $k\geq2$. Then $E_k=1+\sum_{i=1}^{\infty}a_i k^{-i}$ where the sequence $(a_n/2)_{n\geq1}$ is A274199 in the On-Line Encyclopedia of Integer Sequences (OEIS).

A274199 has offset zero. The paper's displayed coefficients $2,4,6,10,16,\ldots$ fix $a_i=2\,\mathrm{A274199}(i)$ for $i\geq1$.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A word is over a $k$-letter alphabet | Lists over `Fin k`, enumerated by `DepthBudgetIidGreedyOptimality.words` | Uniform cardinality is $k^n$. |
| $w=w_m\cdots w_1w_0w_1\cdots w_m$, with nonempty outer blocks and possibly empty centre | `GreedyRenewal.IsBPFactorization` | `bs` lists the outer blocks from the centre outwards; the two flattenings have the source order. |
| Width $2m$ or $2m+1$ according to the centre | `GreedyRenewal.bpWidth` | The empty word has width zero, extending the source without affecting a limit at infinity. |
| Largest width over all valid factorizations | `GreedyRenewal.largestBPWidth` | The supremum is over valid widths; its boundedness is proved. |
| $E_{n,k}=k^{-n}\sum_{i=1}^n i\,\mathrm{LBP}_k(n,i)$ | `LargestFactorizationExpectedWidth.expectedWidth` | The definition is the uniform function-space average. The private `expectedWidth_weighted_count` identity gives the source's weighted width-count expression. |
| A274199 is the limiting reverse row of A274190 | `CompositionInversion.a274190_stable` and `a274190_diagonal_limit` | For $N\geq2d$, the diagonal equals $g(2d,d)$. The triangle includes $g(n,0)=1$ and the recurrence for every positive column. |
| Every integer $k\geq2$ and convergence to $1+2\sum_{i\geq1}\mathrm{A274199}(i)k^{-i}$ | `LargestFactorizationExpectedWidth.claim` and `result` | `claim` states existence of every reverse-row limit, summability of the positively indexed series, and convergence of the uniform average to one plus that series. `result` applies `coefficient_limit_results` to all three clauses. |

The auxiliary parameters in border and peeling statements range over arbitrary list alphabets. They strengthen the supporting statements and add no hypothesis to the settling result.

## Motivation

The source identifies the coefficient sequence empirically. The uniform limit and the connection with the stabilized A274190 diagonal require proofs beyond agreement of finitely many coefficients. The exact source, conventions, tier-1 literature screen and settlement criteria are preregistered in [#15445](https://github.com/the-omega-institute/trureturing/issues/15445).

## Gap

The source's Lemma 3 tail bound fails on its binary table entry at $n=11$, width $t=9$. Its original existence argument therefore does not supply the required domination. The proof here uses the exact renewal recursion and independently establishes that the empty-centre probability vanishes. A finite coefficient check alone does not prove the infinite generating-series identity.

## Route

A shortest proper border is unbordered and has length at most half the word. Conversely, a nonempty unbordered outer block of $uvu$ is its shortest border. An outer block that is itself bordered can be split to increase the factorization width. These statements yield `GreedyRenewal.largest_eq_peelWidth`.

Let $u_j(k)$ count unbordered words of length $j$, put $q_j=u_j(k)/k^{2j}$, and $q=\sum_{j\geq1}q_j$. The disjoint shortest-border partition gives `GreedyRenewal.renewal_tail_count`. Its probability recursion yields tails bounded by $q^r$ and converging to $q^r$, with $q<1$ for $k\geq2$.

If $R_n$ is the number of peeled pairs, the width is $2R_n+1-\mathbf1_{\{\text{empty centre}\}}$. The empty-centre probabilities at lengths $2m$ are the coefficients of $(1-Q(z))^{-1}$, where $Q(z)=\sum_jq_jz^j$. Their summability makes them tend to zero. Dominated convergence gives

$$E_k=1+2\sum_{r\geq1}q^r=\frac{2}{1-q}-1.$$

The A274190 recurrence is identified with the restricted first-part composition recurrence by `CompositionInversion.a274190_compCount`. `compCount_fib_bound` supplies the Fibonacci majorant. Pairing the complementary regions $j<2i$ and $2i\leq j$ in the absolutely convergent real double sums gives `unbordered_composition_series`: the full coefficient series equals $(1-q)^{-1}$. Stabilization identifies these coefficients with A274199, and `result` evaluates the expected-width limit.

The formal proof identifies the two count recurrences. A separate finite-set cardinality theorem for all restricted compositions is not asserted.

## Falsifier

A failure of shortest-border uniqueness, the disjoint renewal count, the composition-series pairing, or the source indexing would invalidate this route. For any $k\geq2$, failure of convergence to the stated stabilized coefficient series would falsify `claim`.

## Evidence

The Lean modules and their Scribes are `GreedyRenewal`, `CompositionInversion` and `LargestFactorizationExpectedWidth` under `D5/S1/Words/BlockPalindromes/` and `Blueprint/D5/S1/Words/BlockPalindromes/`. The settling declaration is `D5/S1/Words/BlockPalindromes/LargestFactorizationExpectedWidth.result`. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

Experiment: [expected-width check directory](https://github.com/the-omega-institute/trureturing-experiments/tree/717b7c72b6cadd0aea0aabe864e1bbb8f0a2a948/docs/reports/gabric-shallit-2023-block-palindrome-expected-width). Entry `check.py`; command `python3 check.py b274190.txt b274199.txt` from that directory with the OEIS b-files; exit 0; final reading `bad= 0`; script SHA-256 `aa1568275b45ad4b600cb7dad0c84a31c0842225ddd6b6b54cebe740b72ccdcb`. The executed script bytes equal that pinned file. The finite scopes and readings are stated below.

The escape audit is unfinished under [#15783](https://github.com/the-omega-institute/trureturing/issues/15783). All 36 public theorem targets, including `result`, have the DTR reading `DTR-Unregistered` (Observe): 25 in `GreedyRenewal`, 7 in `CompositionInversion`, and 4 in `LargestFactorizationExpectedWidth`. The missing evidence is source-bound dependent-family variation, sensitivity and observational dependence, together with a compiled enrolled four-slot registration. No successful four-slot registration is claimed.

## Triage

- **Mechanism — proved, kernel-checked.** `GreedyRenewal.shortest_border_le_half`, `maximal_outer_unbordered` and `largest_eq_peelWidth` give the greedy characterization. `shortest_partition` and `renewal_tail_count` give the disjoint counting recursion. In the settling module, private `renewal_tail_bound` and public `renewal_tail_limit` give geometric domination and the tail limit; `empty_centre_powerSeries` and private `empty_probability_limit` give the vanishing-centre step; `expectedWidth_limit` gives the uniform limiting expectation. `CompositionInversion.a274190_stable`, `a274190_compCount`, `compCount_fib_bound` and `unbordered_composition_series` identify and sum the coefficient recurrence. The conclusion is `LargestFactorizationExpectedWidth.result`.
- **Source Lemma 3 — computed false.** The pinned experiment gives $k=2$, $n=11$, $t=9$, $\mathrm{LBP}_2(11,9)=192$ and $192/2048=3/32>2^{-7/2}$. Its exact-arithmetic check compares $(3/32)^2$ with $2^{-7}$. The proof does not use Lemma 3.
- **Readings — computed.** The experiment entry in Evidence exits 0 with `bad= 0`. Greedy versus exhaustive maximum agrees for every word with $(k,n)=(2,0..14),(3,0..9),(4,0..7)$. Unbordered counts agree for $k=2$, lengths $1..14$, and $k=3$, lengths $1..9$. The renewal-tail formula agrees for $(k,n)=(2,12),(3,8)$ and $1\leq r\leq\lfloor n/2\rfloor$. Source Table 2 agrees for $n=10..14$, widths $1..10$. A274190 agrees with all 10001 supplied b-file terms (rows 0..139 and the first 131 entries of row 140); reverse-diagonal stabilization is checked for $0\leq d\leq74$, $2d\leq N<160$, with A274199 agreement on the 42 supplied indices $0..41$. Restricted-composition counts agree for $0\leq d\leq60$. The signed-chain evaluations agree for $k=2,3$, $1\leq j\leq24$; the formal-series inversion agrees through degree 60. The two length-400 truncated real-series evaluations agree within $10^{-30}$ for $k=2..8$. Source Table 3 agrees within $10^{-4}$ for $k=2..10,100$. The printed binary readings are $E_2\approx6.46862690628362287227$, $E_{15,2}=4.9755859375$, and $E_{16,2}=5.099700927734375$. These computations have finite scope; the uniform infinite limit is proved by Lean.

### What the settlement shows

**Proved, kernel-checked:** the decisive structures are the unique shortest-border partition and the complementary-region series pairing. `largest_eq_peelWidth` holds for arbitrary list alphabets; the expectation and coefficient-series conclusions hold for every integer $k\geq2$. The source's Theorem 4 existence conclusion is independently supplied by `expectedWidth_limit`, and Conjecture 5 is settled by `result`, without the false Lemma 3 bound.

**Computed:** the Lemma 3 defect concerns its proposed uniform tail estimate, not the limiting expectation. The exact counterexample and the binary numerical values have the scopes in Triage.

**Open:** nonuniform letter distributions, alternative factorization statistics and sharp quantitative rates of convergence are not settled by this result. No claim is made that the source's other arguments using Lemma 3 retain that bound. Repairing such statements requires their own hypotheses and estimates.

## ASSUMED-UNVERIFIED

The preregistration's literature screen found no settlement in the source versions, author later work, OpenAlex, Semantic Scholar, OEIS or MathDB. This is a bounded literature conclusion, not an exhaustive global absence theorem. The Reddit thread cited by the source could not be fetched. Four-slot escape registration remains unfinished under #15783.
