---
slug: glen-simpson-smyth-2017-lyndon-factors-open-problem-1
bibkey: glensimpsonsmyth2017lyndonfactors
doi: 10.37236/6915
url: https://arxiv.org/abs/1701.00928v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation
---

# Christoffel words need not attain the Lyndon-factor minimum

## Problem

Glen, Simpson and Smyth, *Counting Lyndon factors*, Section 6, p. 9,
Open Problem 1 (arXiv:1701.00928v1; DOI 10.37236/6915), ask:

> Is it true that the minimum number of distinct Lyndon factors over all
> Lyndon words of the same length is attained by at least one Christoffel
> word of that length?

The resolution is **Refuted**, under the literal finite-word conventions
of [#18581](https://github.com/the-omega-institute/trureturing/issues/18581).

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Lyndon words over an ordered alphabet | Frozen `LyndonOrder.IsLyndon`, applied to `List.ofFn w` | Nonempty and strictly least among nontrivial rotations; the imported suffix characterization is used in the proof. |
| A factor is a contiguous subword | `factor w i l` | Drops the first $i$ letters and takes at most $l$; valid nonempty occurrences satisfy $1\le l$ and $i+l\le n$. |
| Number of distinct Lyndon factors | `distinctLyndon w` | Cardinality after taking the image of valid occurrences; equal factor lists count once, including letters and the whole word. |
| At every common length | `claim`, quantified over $n\ge2$ | All lengths remain in the claim; $n=506$ refutes it. |
| At least one Christoffel word | A numerator $0<p<n$ with $\gcd(p,n)=1$ and `christoffel p n` | Lower mechanical word, letter $1$ exactly when $\lfloor(i+1)p/n\rfloor-\lfloor ip/n\rfloor=1$. |
| Minimum over all Lyndon competitors | Every $k$ and every $w:\operatorname{Fin}(n)\to\operatorname{Fin}(k)$ satisfying `IsLyndon` | Every finite ordered alphabet; the counterexample already has $k=2$. |
| Negative resolution | `result` proves the negation of `claim` | No restricted replacement of the affirmative claim. |

## Motivation

A length-$506$ binary Lyndon word has exactly $16$ distinct Lyndon factors,
whereas every Christoffel word of that length has at least $17$.
Thus optimizing within the Christoffel family does not solve the minimum
problem over all Lyndon words.

## Gap

The paper explicitly leaves the minimum-attainment assertion open.
Glen's 41ACCMCC talk, *On the Stern–Brocot tree, continued fractions, and
Lyndon words*, slide 19, announces an affirmative answer. The supplied
slides contain no proof, and the announcement conflicts with this instance.
The bounded literature screen in #18581 found no published proof or
counterexample. Its completeness is **ASSUMED-UNVERIFIED**.

## Route

Let $U=\mathtt{aabaabab}$, $V=\mathtt{aabab}$ and
$v=\mathtt{ababbababbabbababbabb}$. Replace each $a$ in $v$ by $UUV$
and each $b$ by $UUVV$, producing a binary word $w$ of length $506$.
The proof uses the literal word and certificates, without assuming general
morphism identities or the paper's continued-fraction count.

The private soundness lemmas `take_order_mono`, `rejection_take`,
`check_row_sound` and `check_rows_sound` justify compressed intervals of
rejected suffixes. They imply that all Lyndon factors of $w$ lie in a list
of $16$ candidates. Distinct occurrences give the matching lower bound.
For every eligible Christoffel numerator, $17$ distinct Lyndon-factor
occurrences give a lower bound.

## Falsifier

A length-$506$ Christoffel word with at most $16$ distinct Lyndon factors,
or a discrepancy between the source definitions and the literal claim,
would overturn the asserted separation. The formal result uses the actual
factor sets and the source's rotation predicate, with its imported suffix
characterization.

## Evidence

`D5/S1/Words/Complexity/LyndonFactorChristoffelMinimumRefutation.result`
proves $\neg\operatorname{claim}$. The private declarations `w_lyndon`,
`w_count` and `christoffel_lower` establish the witness's Lyndon property,
its exact count $16$, and the uniform Christoffel lower bound $17$ at $506$.
These are kernel-checked statements on the settling result's proof path.

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Supplementary experiment:
[the pinned verification directory](https://github.com/the-omega-institute/trureturing-experiments/tree/4c708c7738167c01f27b16ea993eaf92e66d766a/docs/reports/glen-simpson-smyth-2017-open-problem-1-christoffel-minimum).
Command: `python3 verify506.py` from that directory; exit $0$.
Script SHA-256: `9c9b9e90fd40e1a29042df31d674f5d637e4f444f738ed51c5342de4930600d4`.
The verification reports length $506$, letter counts $312/194$, and
exactly $16$ distinct Lyndon factors by two counting methods. It checks
all $220$ eligible Christoffel words, whose minimum count is $17$,
attained by $32$ numerators; the direct count agrees with the quotient-sum
formula on that finite set. Direct brute-force spot checks use numerators
$97,1,251$. The tested $A/B/h$ morphism identities have zero failures
among the script's $300$ random trials, restricted to trials containing
both letters. Those trials do not prove universal morphism identities.

## Triage

### What the settlement shows

| Item | Status and evidence |
| --- | --- |
| Minimum attainment by a Christoffel word fails already over a binary alphabet at length $506$. | **Proved, kernel-checked:** `result`, using `w_lyndon` and `w_count`. |
| Every length-$506$ Christoffel competitor has strictly more distinct Lyndon factors than the specified word. | **Proved, kernel-checked:** private `christoffel_lower` gives $17\le D(c)$ and private `w_count` gives $D(w)=16$, combined in `result`. |
| The unrestricted or binary global minimum at $506$ equals $16$. | **Open:** the witness proves an upper bound of $16$; no lower bound excluding $15$ is established here. |
| Length $506$ is the earliest counterexample. | **Open:** no all-smaller-length classification is proved or computed by the cited verification script. |
| Every arbitrary-alphabet minimizer reduces to a binary minimizer. | **Open:** the refutation uses a binary witness and supplies no alphabet-reduction theorem. |
| The $h$ morphism adds only four Lyndon factors while expanding lengths; general $A/B/h$ factor identities. | **Open as a universal statement:** suggested by the supplied research and tested in the finite random trials above; no such identity is formalized here. |

**Proved in prose:** any global or binary minimizer of length $506$, if
chosen, has count at most $16$ because $w$ is eligible. Each Christoffel
competitor has count at least $17$, so every such minimizer is
non-Christoffel. This consequence uses the proved separation, not an
assumption that the exhibited word attains the minimum.

The bound $15\le f(506)$ attributed to Saari's theorem in #18581 is
**unverified here**; applying that theorem with its equality case is a
separate obligation. The $h$-family and incidence-matrix searches, the
exhaustive binary/ternary/quaternary ranges, and their classifications in
#18581 are **open as independently reproduced claims in this delivery**;
the cited verification script does not execute those searches. The
alphabet-reduction and first-counterexample questions remain open.

The source's Theorem 8 is a count within the Christoffel family; it does
not assume the minimum-attainment assertion and is unaffected. No other
source theorem is refuted by this construction. The refuted general
minimum assertion cannot support a claim that Christoffel words always
supply global minimizers. General morphism factor identities remain a
separate possible formalization.

## ASSUMED-UNVERIFIED

Literature completeness, priority and the unavailable proof behind the
conflicting affirmative 2018 announcement are ASSUMED-UNVERIFIED.
Numerical trials establish only their stated finite scope. The exact
global minimum, earliest counterexample length and alphabet reduction
are not settled by this module.
