---
slug: kumar-peng-tran-2022-modular-integer-complexity-conjecture-4-4
bibkey: kumarpengtran2022complexity
doi: 10.48550/arXiv.2211.04379
url: https://arxiv.org/abs/2211.04379v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result
---

# Kumar–Peng–Tran Conjecture 4.4 fails at modulus 17

## Problem

A. Kumar, S. Peng and V. Tran, *Integer Complexity Generalizations in Various Rings*, arXiv:2211.04379v1, Section 4, Conjecture 4.4:

> E(m, 2) is the third most inefficient for odd m.

The source defines expressions from copies of $x$ using addition, multiplication and parentheses, evaluates them in $\mathbb{Z}/m\mathbb{Z}$ at a base $s$, and defines $E(m,s)$ as the maximum expression complexity over residues. The binding proposition reads “third” by individual unit bases: for every odd $m \ge 3$, at most two units $s$ satisfy $E(m,2)<E(m,s)$. Bases $3$ and $16$ tie in the witness, so dense ranking by distinct inefficiency values is outside this proposition.

### Statement echo

- The universal modulus binder is $m : \mathbb{N}$ with an anonymous $[\operatorname{NeZero}(m)]$ instance.
- The hypotheses are $3 \le m$ and $\operatorname{Odd}(m)$.
- The base is the residue $2 : \mathbb{Z}/m\mathbb{Z}$.
- The comparison domain is all units $s : (\mathbb{Z}/m\mathbb{Z})^\times$, coerced to $\mathbb{Z}/m\mathbb{Z}$.
- The conclusion is that the cardinality of the filtered units satisfying $E(m,2)<E(m,s)$ is at most $2$.
- The expression, leaf-count, evaluation, complexity and inefficiency clauses are represented by `Expr`, `Expr.leaves`, `Expr.eval`, `complexity` and `inefficiency` in the settling module.

## Motivation

The settlement supplies a counterexample to the individual-base reading of the source's third-place assertion. At $m=17$, base $2$ has inefficiency at most six while bases $1$, $3$ and $16$ each have inefficiency greater than six.

## Gap

Issue [#19529](https://github.com/the-omega-institute/trureturing/issues/19529) records the source text, the binding convention and the literature screen. The screen inspected arXiv v1 and the MathDB integer-complexity tag and found no settlement in that scope. A post-review revision mentioned on an author's CV was not read. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

The module defines $V(s,n)$ as the finite set of residues obtainable from expressions with at most $n$ leaves. Its recurrence includes the leaf $s$ and every sum or product formed from child budgets $i+1$ and $n-i$ for $0 \le i < n$. The theorem `mem_V_iff` proves the recurrence exactly characterizes expression values.

The finite certificates prove $V(2,6)$ is all of $\mathbb{Z}/17\mathbb{Z}$, while residues $10$, $0$ and $7$ are absent from $V(1,6)$, $V(3,6)$ and $V(16,6)$ and occur at budget seven. These bounds give $E(17,2)\le6$ and $E(17,1),E(17,3),E(17,16)>6$. The three distinct unit witnesses contradict the proposed cardinality bound.

## Falsifier

The formal settlement would address a different question if expressions omitted binary trees, if subtraction or constants were added, if nonunit bases were admitted, or if “third” counted distinct inefficiency values instead of individual unit bases. Exact inefficiencies and the least-counterexample assertion are outside the Lean theorem.

## Evidence

The canonical source is `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.lean`. The `basis=refutes` record designates `D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result`, which CLAUDE.md §3.9 exempts from four-slot registration; every other declaration is a definition or a private helper, so the module adds no other public theorem and no audit target remains.

The header line is:

```text
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Congruence/KumarPengTranModularComplexity.claim; result=D5/S3/Arith/Congruence/KumarPengTranModularComplexity.result; claim=D5/S3/Arith/Congruence/KumarPengTranModularComplexity.claim
```

The Scribe has one `OpenProblemResolutionClaim(Refuted)` on `result`.

The axiom closure of every public declaration is contained in `{propext, Classical.choice, Quot.sound}`. The frozen module state is `Golden/Frozen/state/D5/S3/Arith/Congruence/KumarPengTranModularComplexity.lean.json`, with module statement_id `sha256:0d6ab562269369c72069229d03650e0be797d56a8ab068f0ae0178d6ff8327d8`.

The independent computation is pinned to [the experiments repository at commit be6f3762ff2ffe845a13319026bcc5c562cf33a3](https://github.com/the-omega-institute/trureturing-experiments/tree/be6f3762ff2ffe845a13319026bcc5c562cf33a3/docs/reports/kumar-peng-tran-2022-modular-complexity-conjecture-4-4). The script path is `docs/reports/kumar-peng-tran-2022-modular-complexity-conjecture-4-4/check.py`; the commit contains that path and its SHA-256 is `0621236038fc47cc438d624b0268a360d1019ebb9ee77a4d1725bf70f071f909`. The command `python3 /tmp/op-kpt2211/check.py` (the pinned script extracted unchanged from that commit) exits 0 with `RESULT PASS`. It checks $E(17,2)=6$, $E(17,1)=9$, $E(17,3)=E(17,16)=7$, and the smallest failing odd modulus in the checked window $3\ldots101$ is $17$.

## Triage

Tier 1, published question from a 2022 paper, preregistered in issue #19529. Resolution: `Refuted`.

### What the settlement shows

- **Proved by `result`:** the binding cardinal-ranking claim is false. The witness is $m=17$ with three unit bases strictly above base $2$.
- **Proved by `mem_V_iff`, `complexity_le_iff`, `inefficiency_le_of_cover`, `inefficiency_gt_of_gap` and `separating_bounds`:** the recurrence covers all binary expression trees; $E(17,2)\le6$ and $E(17,1),E(17,3),E(17,16)>6$.
- **Proved in prose (cardinality argument):** the units represented by $1$, $3$ and $16$ are distinct because their residues modulo $17$ are distinct. The bounds in `separating_bounds` put each in the filtered unit set, so that set has cardinality at least $3$, contradicting the proposed bound $\le2$. This explains the proof of `result`; it is not a separate public Lean theorem.
- **Computed:** the pinned experiment gives the exact values above and tests every unit base for odd $m$ from $3$ through $101$. The failing moduli in that window are $17,35,51,55,57,61,69,75,81,87,93,99$; $17$ is the least within the window. Its scope does not formalize exact inefficiencies or establish a uniform theorem beyond that window.
- **Proved in prose (mechanism):** at base $2$, the two-leaf expressions $x+x$ and $x\cdot x$ agree because $2+2=2\cdot2=4$. The lower bound for base $3$ at modulus $17$ is kernel-checked by `gap_three` and `inefficiency_gt_of_gap`. A second mechanism is visible at modulus $51$: $35^2-1=1224=24\cdot51$, while $35\equiv-1\pmod3$ and $35\equiv1\pmod{17}$. These arithmetic identities explain the Chinese-remainder example; no classification of all such failures is asserted.
- **Open (neighbouring conjectures):** Conjecture 4.2 asserts that base $1$ is always maximal, and Conjecture 4.3 is an eventual ranking assertion for base $-1$. Neither is a theorem here. The experiment computes all unit inefficiencies in its stated window, but its pass condition concerns Conjecture 4.4; it does not certify a uniform extension of either neighbouring conjecture.
- **Open:** the source's Conjectures 4.2 and 4.3, global failure patterns, asymptotic behavior and every alternative tie convention remain outside this settlement.
- **Open:** literature completeness and the unread post-review revision remain `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

The bounded literature search does not establish exhaustive worldwide novelty or priority. The binding cardinal-ranking interpretation is explicit for this settlement; no claim is made about dense ranking by distinct inefficiency values. The experiment is evidence for the stated finite window, not a Lean theorem about all odd moduli.
