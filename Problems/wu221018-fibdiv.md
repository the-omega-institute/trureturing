---
slug: wu221018-fibdiv
bibkey: wu2026a221018
doi: null
url: https://oeis.org/A221018/internal
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.result
---

# Wu’s adjacent-index Fibonacci divisibility conjecture

## Problem

OEIS A221018, revision 35, NAME:

> Number k such that Fibonacci(k) is divisible by k, k + 1 and k - 1.

Its first FORMULA states:

> a(n) % 10 == 0, 2, or 8 (conjectured). - _Chai Wah Wu_, Aug 06 2026

The source generator starts at two. Write $F_k$ for the standard Fibonacci sequence, with $F_0=0$, $F_1=1$ and $F_{k+2}=F_k+F_{k+1}$. For every natural $k\ge2$, the three assumptions $(k-1)\mid F_k$, $k\mid F_k$ and $(k+1)\mid F_k$ imply $k\bmod10\in\{0,2,8\}$. No converse is asserted.

### Statement echo

| Source clause | Formal counterpart | Fidelity |
| --- | --- | --- |
| Generator starts at 2 | Natural index $k$ and $2\le k$ | Covers the source integers and makes natural subtraction ordinary subtraction. |
| Fibonacci(k) | Existing `Nat.fib k` | Standard initial values and recurrence; no replacement sequence. |
| Divisible by k, k+1 and k-1 | The three separate divisibility hypotheses of `claim` | Their implication chain is equivalent to the source conjunction. |
| Final digit 0, 2 or 8 | The three remainder alternatives in `claim` and `result` | Exact necessary condition; no added hypotheses or converse. |

## Motivation

The result settles the first FORMULA conjecture registered in [#21590](https://github.com/the-omega-institute/trureturing/issues/21590), through the settling declaration `D5.S3.Arith.Congruence.WuAdjacentFibonacciResidues.result`. The admission basis is `open-problem-resolution (#21590; Proved)`. The proof shape is bind-only: the settlement combines existing Fibonacci index divisibility with arithmetic normalization.

## Gap

The source explicitly labels the statement conjectured. The source and literature screen recorded in #21590 found no prior settlement in its searched scope. That screen covered the OEIS entry and history, exact identifiers, relevant Fibonacci divisibility literature and repository owners. Its completeness is ASSUMED-UNVERIFIED: unavailable citing-work lists and unread versions remain limitations. The arithmetic ingredients are classical; no new Fibonacci rank theorem is claimed.

## Route

The imported and used `D5.S1.Recurrence.GoldenFibDivisibility.fib_dvd_iff` at indices three, four and five gives $2\mid F_k\iff3\mid k$, $3\mid F_k\iff4\mid k$ and $5\mid F_k\iff5\mid k$. One of $k,k+1$ is even, so the original divisibilities force $2\mid F_k$, then $3\mid k$. Self-divisibility gives $3\mid F_k$, hence $4\mid k$ and therefore $12\mid k$. If $k\equiv1\pmod5$, its predecessor forces $5\mid F_k$ and $5\mid k$, a contradiction. The successor gives the same contradiction when $k\equiv4\pmod5$. Evenness and these two exclusions leave exactly the three asserted decimal alternatives.

## Falsifier

An index $k\ge2$ satisfying all three divisibility assumptions with $k\bmod10\notin\{0,2,8\}$ would refute the assertion. The theorem excludes such an index in the formal system. A source-domain or indexing mismatch would invalidate the stated correspondence; the literal claim and its source echo retain the original conventions.

## Evidence

The Lean module is `D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.lean`; its public theorem is `D5.S3.Arith.Congruence.WuAdjacentFibonacciResidues.result`. Its full proposition is mirrored in the corresponding Blueprint. The axiom closure of every public declaration is contained in {propext, Classical.choice, Quot.sound}.

The escape audit is unfinished: [#21705](https://github.com/the-omega-institute/trureturing/issues/21705). A faithful typed realization, enrolled readout and required sensitivity/dependence evidence for the guarded disjunction are not compiled; no declared_validated registration is claimed.

### Exact finite experiment

The experiment is [wu-a221018-fibdiv at commit 69cc788c26a9c571f2142e468269a27521199775](https://github.com/the-omega-institute/trureturing-experiments/tree/69cc788c26a9c571f2142e468269a27521199775/docs/reports/wu-a221018-fibdiv). The published `check.py` was extracted from that immutable revision and run as `python3 /Users/auric/.sshx/3f5d3f0b09dade04a65b9229/attempt-1/experiment-check.py`, exit 0. Its SHA-256 is `3c291c0c963c2b0f20cd3320587422a4bde0879a032107daf2dfbb7917130c80`; the supplied b-file SHA-256 is `6342506738bc79f3758594d8cf8b31b757e73e77be0062627f0059b2cf00549f`.

Every integer $2\le k\le500000$ was tested without a residue prefilter: 38 members, exactly the b-file prefix. A separate full-integer recurrence checks indices zero through 20000. All 10000 listed b-file terms pass; their final-digit histogram is 86 zeros, one two and 9913 eights. Fast doubling, matrix powering and 14930352 direct recurrence steps agree at $k=14930352$, where the Fibonacci pair is $(0,1)$ modulo $k(k-1)(k+1)$. These are finite checks, separate from the universal Lean theorem.

## Triage

| Item | Status | Evidence kind and scope |
| --- | --- | --- |
| $12\mid k$ under the three original assumptions | Proved | Proved in prose by the divisibility feedback in Route; also the proof-local `htwelve_index`, not a separate public theorem. |
| $k\bmod5$ is neither 1 nor 4 | Proved | Proved in prose in Route; the same contradictions occur as proof-local `hnot_one` and `hnot_four`. |
| Final digit belongs to $\{0,2,8\}$ | Proved | Kernel-checked `D5.S3.Arith.Congruence.WuAdjacentFibonacciResidues.result`. |
| Necessary residue conditions are insufficient at $k=12$ | Computed | $12\mid12$ and $12\bmod10=2$, but $F_{12}=144$ and $144\bmod\operatorname{lcm}(11,12,13)=144\ne0$; exact integer arithmetic. |
| Every allowed final digit occurs among checked members | Computed | Published experiment: $108$ ends in 8, $6480$ in 0 and $14930352$ in 2; each satisfies the three divisibilities. |
| Stronger A225219 restriction to 0 or 18 modulo 30 | Computed counterexample | Published experiment at $k=14930352$: membership holds and $k\bmod30=12$; the three independent computations agree. |
| Infinitude, density, frequencies and infinitely many members of each allowed final digit | Open | Neither the theorem nor the finite experiment settles these unbounded questions. |

### What the settlement shows

The decisive mechanism is feedback between index divisibility and Fibonacci zero indices, followed by a local obstruction at five. The route proves the stronger necessary index conditions $12\mid k$ and $k\bmod5\notin\{1,4\}$ in prose, while the public theorem states the original decimal conclusion. The counterexample $k=12$ shows these necessary conditions do not characterize membership. The three finite examples show that none of the permitted final digits can be deleted from the conclusion. Infinitude, density and frequencies remain open, as do infinitely many occurrences of each digit. No downstream theorem depending on the conjecture was identified in the screened sources; that is a literature-screen result with the completeness limits below, not an exhaustive dependency claim.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. OpenAlex and Semantic Scholar citing-work lists were unavailable, Jarden was only partly read, and the Cihan–Inam journal version was not read (its arXiv version was screened). Identifier searches cannot exclude a prior proof without the identifier. The escape audit remains unfinished in #21705. Finite examples establish no unbounded counting claim.
