---
slug: garg-2019-fibonacci-prefix-antipowers
bibkey: garg2021antipowers
doi: 10.46298/dmtcs.7134
url: https://arxiv.org/abs/1907.10816v4
triage: theorem
motivation_gids:
  - D5/S1/Words/Antipowers/GargFibonacciPrefixAntipower.result
---

# Garg's Fibonacci prefix antipower conjecture

## Problem

Swapnil Garg, *Antipowers in Uniform Morphic Words and the Fibonacci Word*,
arXiv:1907.10816v4, DMTCS 23(3), article 14, Conjecture 18, printed page 8:

> Let $F_n$ be an even Fibonacci number. Then, there is an $(F_n-1)$-antipower with block length $\frac{F_n}{2}+F_{n-1}$ that is a prefix of $\mathbf f$.

The Fibonacci word is the fixed point starting with $0$ of $0\mapsto01$,
$1\mapsto0$; $F_1=F_2=1$. A $k$-antipower consists of $k$ consecutive,
pairwise distinct blocks of equal length. [The source note](../Library/Words/garg2021antipowers.md)
quotes the definitions from §3 and the conjecture. [Issue #14479](https://github.com/the-omega-institute/trureturing/issues/14479)
fixes the universal statement GARG-1: every $n\ge1$ with $F_n$ even,
$K=F_n-1$, $L=F_n/2+F_{n-1}$, and the first $K$ blocks starting at $jL$.

## Motivation

`D5/S1/Words/Antipowers/GargFibonacciPrefixAntipower.result : claim` proves GARG-1.
The literal finite-prefix convention is $S_0=[0]$, $S_1=[0,1]$,
$S_{k+2}=S_{k+1}S_k$, with `fibW` their compatible diagonal limit.
The proved `fibW_bridge` identifies this limit with the existing golden word,
with Boolean `true` corresponding to letter $0$. Blocks are functions
`Fin (blockLength n) → Fin 2`; no extra hypothesis is imposed.

## Gap

The preregistration records the source and literature checks: arXiv v4;
MathDB's Fibonacci prefix antipower conjecture entry with no solutions;
Berger–Defant and Postic do not settle this exact prefix length.
This is `not-found-in-searched-scope`, not a proof of absence of other literature.
The source's longest-gap estimate does not establish the proposed length:
the sampled even-parity displacement is $\sqrt5\,\delta$, smaller than the
coarse longest-gap scale $\varphi^2\delta$.

## Route

The paper argument below gives the proof outline from the supplied proof,
with $\alpha=\varphi^{-1}$, $\varphi=(1+\sqrt5)/2$, $q=F_n$,
$p=F_{n-1}$, $\delta=\varphi^{-n}$, $s=(-1)^n$, $H=q/2$, and $L=H+p$.

1. **Cylinder coding.** Fact 14 gives
   $f(t)=1-(\lfloor(t+2)\alpha\rfloor-\lfloor(t+1)\alpha\rfloor)$.
   For a length-$m$ factor beginning at $a$, put $x=\{(a+1)\alpha\}$.
   Telescoping gives $k-\sum_{t<k}f(a+t)=\lfloor x+k\alpha\rfloor$.
   Successive differences recover the letters. Since $\alpha$ is irrational,
   $\lfloor x+k\alpha\rfloor=\lfloor k\alpha\rfloor+1_{x\ge\{-k\alpha\}}$.
   Thus factor equality is equality of the cells cut by $\{-k\alpha\}$,
   $1\le k\le m$, with cuts assigned to their right cell.
   The proof uses the frozen `golden_factor_eq_iff_cylinder_rank_eq`.
2. **Binet sampling.** The Lean helpers `residual`, `binet_residual`,
   `sampling_identity` and `sampling_phase` establish
   $q\alpha=p-s\delta$, $q\sqrt5\delta=1-s\delta^2$ and
   $L\alpha=M+1/2+s\sqrt5\delta/2$, where $M=F_{n-2}+(p-1)/2$ is an integer.
   The scaled sampled phase is congruent modulo $q$ to
   $X_j=p+jH+sj/2+e_j$, $e_j=-s\delta-j\delta^2/2$.
3. **Bounds.** For $n\ge9$, `large_bounds` proves
   $0<\delta<1/50$, $B=q\delta<9/20$,
   $A=\delta+q\delta^2/2<49/2000$; hence $A+B<1/2$.
   These follow from $\varphi>8/5$, $\sqrt5>223/100$ and Binet.
4. **Actual cuts.** Coprimality lets $k_r\in\{0,\ldots,q-1\}$ solve
   $-k_rp\equiv r\pmod q$. Set $C_r=r+sk_r\delta$.
   Then $C_{r+q}=C_r+q$, $C_0=0$, $C_q=q$, and the cuts strictly increase.
   `C_endpoint` proves $C_r/q\in$ `goldenCylinderEndpointSet (q-1)` for
   $0<r<q$. This is the new cut construction on the active proof path.
5. **Parity cells.** For $s=1$, the labels are
   $R_{2h}=p+h-1$, $R_{2h+1}=p+H+h$; for $s=-1$,
   $R_{2h}=p-h$, $R_{2h+1}=p+H-h-1$.
   `sample_in_lifted_cell` places each reduced phase strictly between
   $C_{R_j}$ and $C_{R_j+1}$. The bounds in step 3 separate both parity classes.
   `labels_injective_mod` proves that distinct $j<q-1$ have distinct labels
   modulo $q$. Together these give `golden_sample_grid_rank_injective`.
6. **Block distinction.** `large_distinct` supplies distinct length-$(q-1)$
   factors. Since $L\ge q-1$, equality of the full blocks would imply equality
   of these prefixes. For $n<9$, the even Fibonacci cases are $n=3,6$:
   one block at $n=3$; the seven length-$9$ blocks at $n=6$ are checked locally
   inside `result` by Lean. This covers every admissible $n$.

The seven length-$9$ blocks at $n=6$ are
$010010100$, $100101001$, $010010010$, $100100101$,
$001010010$, $010100101$, $001001010$.

## Falsifier

A collision between two distinct indices $i,j<F_n-1$ at the prescribed
length, with $n\ge1$ and $F_n$ even, would refute GARG-1. The Lean theorem
excludes such a collision under the literal word convention.
A failure of the stronger $F_n$-block statement is a sharpness observation,
not a counterexample to GARG-1.

## Evidence

The two modules provide the general sample-grid construction and the
universal settling theorem. The axiom closure of every public declaration
is contained in $\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The Scribe attaches `OpenProblemResolutionClaim` with resolution `Proved`
to the settling `result`. No digestion atom or coverage assertion is involved.
The finite computations below corroborate the proof in their stated scope;
they are not its universal proof.

## Triage

### What the settlement shows

| Target item | Status | Evidence and boundary |
| --- | --- | --- |
| Mechanism | proved in Lean | `C_endpoint`, `golden_sample_grid_rank_injective`, `sampling_identity`, `sampling_phase`, `large_distinct` and `result`: Binet sampling and disjoint parity cells, rather than a longest-gap estimate. |
| Consequence | proved by paper argument | The following subsequence argument proves $\liminf_k\gamma_0(k)/k\le\sqrt5/2$. It is not an additional Lean theorem. |
| Sharpness | computed through $n\le21$; uniform extension open | The script below finds $F_n$ blocks distinct at $n=3$, and the collision $(0,F_n-1)$ at $n=6,9,12,15,18,21$. |
| Generalisation | open for other Sturmian slopes | The supporting Lean theorem permits arbitrary coprime $p,q$, positive even $q$, and its explicit signed golden-slope residual bounds. It retains the golden slope; changing the slope requires a new coding and cut bridge. |

**Consequence, paper argument.** Write $\gamma_0(k)$ for the least block
length of a prefix $k$-antipower. For $n=3r$, Fibonacci parity gives even
$F_n$, and $K_r=F_{3r}-1\to\infty$.
The theorem gives $\gamma_0(K_r)\le L_r$.
Binet yields $F_{n-1}/F_n\to\varphi^{-1}$, so
$L_r/K_r\to1/2+\varphi^{-1}=\sqrt5/2$.
Taking the liminf along this unbounded subsequence proves the stated upper
bound. The source's Sturmian complexity argument gives the lower bound $1$.
The source's other propositions remain applicable under their original
hypotheses; the conditional prefix liminf remark following Conjecture 18
therefore has its premise discharged. The general all-start bounds are
not strengthened by this prefix-only settlement.

**Scope and sharpness.** For $n\ge9$, `large_distinct` proves the stronger
fact that the first $F_n-1$ letters already distinguish the sampled blocks.
The collision at the next block is a computation for the listed indices;
no uniform collision theorem is claimed. Other Sturmian slopes and optimal
prefix block lengths remain open follow-up questions.

### Prefix computation

The orchestrator's check is reproduced verbatim below. Command
`python3 /tmp/op-garg/check.py`, exit $0$, SHA-256
`7e48fc0d01b338691ccddb2633e42c85965acba18ed018879b052275bc363172`. A reader can save the block as `check.py` and run `python3 check.py`.
It tests exactly the even Fibonacci indices $n=3,6,9,12,15,18,21$;
all $F_n-1$ prescribed blocks are distinct. The $(F_n,K,L)$ values are
$(2,1,2)$, $(8,7,9)$, $(34,33,38)$, $(144,143,161)$,
$(610,609,682)$, $(2584,2583,2889)$, $(10946,10945,12238)$.

```python
import sys
# Fibonacci word f = phi^omega(0), phi(0)=01, phi(1)=0
a,b=b'0',b'01'
while len(b)<160_000_000: a,b=b,b+a
f=b
F=[0,1,1]
while len(F)<30: F.append(F[-1]+F[-2])
res={}
for n in range(3,22):
    if F[n]%2: continue
    K=F[n]-1; L=F[n]//2+F[n-1]
    assert K*L<=len(f)
    blocks=set(f[j*L:(j+1)*L] for j in range(K))
    res[n]=(F[n],K,L,len(blocks)==K)
    print(n,res[n],flush=True)
```

### Sharpness computation

Command `python3 /tmp/op-garg/stage-b/sharpness.py`, exit $0$, SHA-256
`ff7d35868595a80ecb17bc73383a977ef4a68787103063ea83891b46a9116a99`. Save the following source as `sharpness.py` to rerun with
`python3 sharpness.py`. It compares all $F_n$ prefix blocks in the same
index range and reports the first collision. The resulting scope and
status are exactly those in the Triage table.

```python
import json
from pathlib import Path
F=[0,1]
for n in range(2,22):F.append(F[-1]+F[-2])
need=max(F[n]*(F[n]//2+F[n-1]) for n in range(1,22) if F[n]%2==0)
a,b=b'0',b'01'
while len(b)<need:a,b=b,b+a
rows=[]
for n in range(1,22):
 if F[n]%2:continue
 q=F[n];L=q//2+F[n-1];seen={};collision=None
 for j in range(q):
  block=b[j*L:(j+1)*L]
  if block in seen:
   collision=[seen[block],j];break
  seen[block]=j
 row=dict(n=n,F=q,L=L,F_blocks_distinct=collision is None,first_collision=collision)
 rows.append(row);print(json.dumps(row),flush=True)
```

## ASSUMED-UNVERIFIED

The external literature gap is bounded by the searches recorded in #14479;
absence of a result outside that scope is unverified. The liminf consequence
has a paper argument here, with no separate kernel-checked limit theorem.
Uniform $F_n$-block sharpness and extensions to other Sturmian slopes are open.
