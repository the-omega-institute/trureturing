---
slug: kay-2010-transfer-rate-refutation
bibkey: kay2010perfectstatetransferreview
doi: 10.1142/S0219749910006514
url: https://arxiv.org/abs/0903.4274v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result
---

# Kay's transfer-rate conjecture for perfect state transfer chains

## Problem

A. Kay, *A Review of Perfect State Transfer and its Application as a
Constructive Tool*, arXiv:0903.4274v3 (Int. J. Quantum Inf. 8, 641 (2010)),
subsection "Transfer Rate". For the ordered eigenvalues
$\lambda_1 < \dots < \lambda_N$ of a mirror-symmetric chain the perfect state
transfer condition is

> $\lambda_n-\lambda_{n-1}=(2m_n+1)\pi/t_0$ where $t_0$ is the state transfer time, and $m_n$ is a positive integer (which can vary with $n$).

and $B'(\lambda_n)=\prod_{m=1\neq n}^N(\lambda_n-\lambda_m)$. The lemma of
that subsection (the sixth lemma of the source) reads:

> If a set of eigenvalues is chosen to fulfill the perfect state transfer condition of Eqn.~(\ref{eqn:st_cond}), then a necessary and sufficient condition to perfectly achieve the rate $M/2t_0$ for integer $M$ is that all the $R_k$ for $k=0\ldots M-1$ should be equal, where
> $R_k=\sum_{n=1}^N\frac{(-1)^n}{B'(\lambda_n)}$,
> and the sum is restricted to those terms satisfying the condition
> $\frac{t_0}{\pi}(\lambda_n-\lambda_1)\mod M=k.$

It is followed by the conjecture:

> We conjecture that it is impossible to fulfill the condition of Lemma \ref{lemma:rate} for any $M>2$, although we only have a proof for $M>N/2$.

Issue #14475 fixes the reading. A spectrum is a function `lam : Fin N → ℝ`;
the condition is `0 < t₀` together with positive integers `m` such that every
gap between consecutive levels is `(2 m + 1) π / t₀`; the level `n` lies in
the class `k` modulo `M` when the real number `(t₀/π)(λ_n − λ_1)` is an integer
congruent to `k`; the sign `(−1)^n` uses the source's index, which starts at
one. The conjecture is the statement that for every `N ≥ 1`, every such
spectrum and transfer time, and every integer `M > 2`, the sums `R_0, …,
R_{M−1}` are not all equal. The case `N = 0` is excluded because all sums of
the empty spectrum are empty and therefore equal.

## Motivation

The lemma turns the question of how fast a perfect state transfer chain can
be reused as a quantum channel into a condition on its spectrum: the standard
protocol has `M = 2`, and `M > 2` would mean that a new state can be placed on
the first site before the previous one has arrived. The conjecture says this
never happens. The declaration
`D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result` proves that the
conjecture is false.

## Gap

Issue #14475 preregisters the verbatim source, the reading above, the
expected settlement and the literature check before any formalization. Its
recorded readings: Kay, arXiv:1102.2338, derives the bound
$2l+D\leq M\leq N$ and concludes

> Ideally, we want the maximum transfer distance, which would be $N-1$ (a chain), imposing that $l=0$, as conjectured in \cite{akreview}.

so the later paper treats the conjecture as established. Bailey, Derevyagin
et al., arXiv:2411.06047, construct perfect state transfer Jacobi matrices
whose first-site amplitude vanishes before the transfer time (early state
exclusion): a $4\times4$ example with eigenvalues $\pm3/2,\pm5/2$ and a zero at
$\arccos(2/3)$, and, for every even order at least 4 and every $m$, a matrix
with $m$ such zeros; arXiv:2507.18767 and arXiv:2606.04353 continue that
study, the latter noting that the phenomenon "can happen multiple times".
Their $4\times4$ example already violates the bound of arXiv:1102.2338
($N=4$, $D=3$, $l=1$). For a perfect state transfer spectrum the condition of
the lemma with $M=4$ is equivalent to a zero of the first-site amplitude at
exactly $t_0/2$ (see Triage); none of the 24 perfect state transfer spectra
and three parametrised families extracted from these three papers fulfils the
condition of the lemma for any $3\le M\le N$ (second script in Evidence).
arXiv:2209.08160 makes no statement on the conjecture; a title and abstract
scan of the 285 works that INSPIRE lists as citing the review finds no
refutation. These readings are `not-found-in-searched-scope`; they do not
establish an exhaustive literature search or priority.

## Route

Take `N = 8`, `t₀ = π`, `M = 4` and the levels

`λ = (0, 31, 46, 65, 88, 107, 122, 153)`.

1. The gaps are `31, 15, 19, 23, 19, 15, 31`, that is `2m + 1` with
   `m = 15, 7, 9, 11, 9, 7, 15`, all positive.
2. `B'(λ_n)` is `−16291106900640, 760363989840, −273136152240, 203460697440,
   −203460697440, 273136152240, −760363989840, 16291106900640`.
3. Since `t₀ = π`, the number `(t₀/π)(λ_n − λ_1)` is `λ_n`, with residues
   `0, 3, 2, 1, 0, 3, 2, 1` modulo 4. The classes are `{0, 88}`, `{65, 153}`,
   `{46, 122}`, `{31, 107}` for `k = 0, 1, 2, 3`.
4. Every term `(−1)^n / B'(λ_n)` is positive, and
   `1/16291106900640 + 1/203460697440 = 1/760363989840 + 1/273136152240 =
   194/38984495395755`, so `R_0 = R_1 = R_2 = R_3 = 194/38984495395755`.

Here `M = 4 = N/2`, outside the range `M > N/2` for which the source has a
proof.

## Falsifier

The refutation would be undone by a reading of the lemma's condition under
which the four sums of this spectrum differ. The sums are nonzero, so every
class is nonempty; a sign convention with `(−1)^{n−1}` in place of `(−1)^n`
changes all four sums by the same sign; admitting `m_n = 0` enlarges the set
of spectra and leaves this one admissible. The source's proof for `M > N/2`
is not contradicted, because `M = N/2`.

## Evidence

The canonical source is
`D5/S3/Quantum/Dynamics/KayTransferRateRefutation.lean`. Its declarations are
`SpectrumCondition`, `derivativeAt`, `InClass`, `rateSum`, `RateCondition`,
`claim` and `result : ¬ claim`. `result` instantiates `claim` at the spectrum
above, proves the perfect state transfer condition with the multipliers
`15, 7, 9, 11, 9, 7, 15`, evaluates the eight values of `derivativeAt`,
decides the class of each level for each `k < 4`, and evaluates the four sums
by exact rational arithmetic. It uses the axioms `propext`,
`Classical.choice` and `Quot.sound`; no `sorry`, `native_decide` or new axiom.

The following script recomputes the values quoted in this dossier with exact
rational arithmetic (`python3 kay.py`, Python 3.9):

```python
from fractions import Fraction as F
from itertools import product

def levels(gaps):
    return [sum(gaps[:i]) for i in range(len(gaps) + 1)]

def derivative(lam, n):
    b = 1
    for j, y in enumerate(lam):
        if j != n: b *= lam[n] - y
    return b

def sums(gaps, M):
    lam = levels(gaps)
    r = [F(0)] * M
    for n, x in enumerate(lam):
        r[x % M] += F((-1) ** (n + 1), derivative(lam, n))
    return r

def hits(N, G, sym=False):
    odd = range(1, G + 1, 2)
    tuples = (t + t[-2::-1] for t in product(odd, repeat=N // 2)) if sym else product(odd, repeat=N - 1)
    return [(M, g) for g in tuples for M in range(3, N + 1) if len(set(sums(g, M))) == 1]

gaps = (31, 15, 19, 23, 19, 15, 31)
lam = levels(gaps)
print(lam, [derivative(lam, n) for n in range(8)], sums(gaps, 4))
w = [F(1, abs(derivative(lam, n))) for n in range(8)]
w = [x / sum(w) for x in w]
print(w[:4], [sum(w[n] for n in range(8) if lam[n] % 4 == k) for k in range(4)])
p0, p1, norm0, diag, coup = [F(0)] * 8, [F(1)] * 8, None, [], []
for k in range(8):
    norm = sum(w[i] * p1[i] ** 2 for i in range(8))
    a = sum(w[i] * lam[i] * p1[i] ** 2 for i in range(8)) / norm
    b = norm / norm0 if k else F(0)
    diag.append(a); coup.append(b)
    p0, p1, norm0 = p1, [(lam[i] - a) * p1[i] - b * p0[i] for i in range(8)], norm
print(diag, coup[1:])
print([hits(N, 31) for N in range(2, 7)], hits(7, 15), hits(8, 9), hits(8, 41, sym=True))
```

Its output: the levels, the eight values of `B'` and the four sums as in the
Route; the weights `2527/819456, 2461/37248, 6851/37248, 202337/819456` of the
first four levels and the class weights `1/4, 1/4, 1/4, 1/4`; the diagonal
`153/2` (eight times) and the squared couplings `834785/1164, 1197437/1455,
34047/20, 2500, 34047/20, 1197437/1455, 834785/1164`; and the search result
`[[], [], [], [], []] [] [] [(4, (31, 15, 19, 23, 19, 15, 31))]`.

The second script evaluates the condition of the lemma, for every
$3\le M\le N$, on perfect state transfer spectra taken from the examples and
theorems of arXiv:2411.06047, arXiv:2507.18767 and arXiv:2606.04353 (the
symmetric spectra are listed by their non-negative levels) and on three of
their parametrised families with parameter below 80. An output `[]` means that
no such $M$ fulfils the condition, `None` that the listed levels are not a
perfect state transfer spectrum; the last two lines are the spectrum of this
dossier, with the single hit $M=4$, and the families, with no hit
(`python3 lit_spectra.py`, Python 3.9):

```python
from fractions import Fraction as F
from math import gcd
from functools import reduce
def check(lam):
    lam = sorted(lam); N = len(lam)
    gaps = [lam[i+1] - lam[i] for i in range(N-1)]
    g = reduce(gcd, gaps)
    q = [(x - lam[0]) // g for x in lam]          # (t0/pi)(lam_n - lam_1) at the earliest candidate time pi/g
    if any(((b - a) % 2) == 0 for a, b in zip(q, q[1:])):
        return None                               # not a PST spectrum
    B = []
    for n in range(N):
        p = 1
        for j in range(N):
            if j != n: p *= q[n] - q[j]
        B.append(p)
    out = []
    for M in range(3, N + 1):
        R = [F(0)] * M
        for n in range(N):
            R[q[n] % M] += F((-1) ** (n + 1), B[n])
        if len(set(R)) == 1: out.append(M)
    return out
def sym(pos, zero=True):
    return sorted(([0] if zero else []) + list(pos) + [-x for x in pos])
named = {
 "0,1,2,3": sym([1,2,3]), "0,3,4,5": sym([3,4,5]), "0,1,4,7": sym([1,4,7]), "0,3,4,9": sym([3,4,9]),
 "0,3,6,11": sym([3,6,11]), "0,1,4": sym([1,4]), "0,3,12,13": sym([3,12,13]), "0,3,12": sym([3,12]),
 "0,3,8,9,12": sym([3,8,9,12]), "0,1,12..15": sym([1,12,13,14,15]), "0,1,12,13,14": sym([1,12,13,14]),
 "0,1,14..17": sym([1,14,15,16,17]), "0,1,14,15,16,19": sym([1,14,15,16,19]), "0,1,14,15,16": sym([1,14,15,16]),
 "0,1,2,13,14,15": sym([1,2,13,14,15]), "0,1,2,3,20,25": sym([1,2,3,20,25]), "0,1,2,3,4": sym([1,2,3,4]),
 "0,1,2,3,82..86": sym([1,2,3,82,83,84,85,86]), "0,1,2,81..86": sym([1,2,81,82,83,84,85,86]),
 "0,3,6,9": sym([3,6,9]), "0,3,8,9": sym([3,8,9]), "0,3,4": sym([3,4]), "0,1,2,81..85": sym([1,2,81,82,83,84,85]),
 "0,1,2,4,13,14,15": sym([1,2,4,13,14,15]), "0,1,2,3,13,14,15": sym([1,2,3,13,14,15]),
 "4x4 Bailey +-3/2,+-5/2 (x2)": [-5,-3,3,5],
 "delivery": [0, 31, 46, 65, 88, 107, 122, 153],
}
for k, v in named.items():
    print(k, check(v))
hits = []
for m in range(1, 80):
    for name, lam in [("0,1,2m,2m+1", sym([1, 2*m, 2*m+1])), ("0,2m+1,2m+2,2m+3", sym([2*m+1, 2*m+2, 2*m+3]))]:
        r = check(lam)
        if r: hits.append((name, m, r))
    for n in range(2, 9):                          # Bailey et al. family, doubled to integers
        up = [2*m + 2*k + 1 for k in range(n)]
        r = check(sym(up, zero=False))
        if r: hits.append(("bailey", n, m, r))
print("family hits", hits)
```

## Triage

Tier 1, an explicitly stated conjecture of a 2010 review; settlement Refuted.
`result` has `proof_shape: bind-only` (an exact finite evaluation of the
definitions at one explicit spectrum); `admission_basis:
open-problem-resolution` under the preregistration #14475; utility
`kind=certified-instance; basis=refutes` with the typed `claim` and `result`.
There is no atom and no digestion coverage edge.

### What the settlement shows

- **Proved by** `D5/S3/Quantum/Dynamics/KayTransferRateRefutation.result`:
  the condition of the lemma can be fulfilled with `M > 2`. The spectrum
  `0, 31, 46, 65, 88, 107, 122, 153` with `t₀ = π` fulfils the perfect state
  transfer condition and has `R_0 = R_1 = R_2 = R_3` for `M = 4`.
- **Computed (the script in Evidence), mechanism.** The weights of the
  eigenvectors on the first site are
  `w_n = (1/|B'(λ_n)|) / Σ_m (1/|B'(λ_m)|)`, the source's Eqn. `eqn:hoch`; all
  eight terms `(−1)^n/B'(λ_n)` have the same sign, so the sums `R_k` are the
  class weights up to a common factor. The four residue classes modulo 4,
  `{0, 88}`, `{65, 153}`, `{46, 122}`, `{31, 107}`, each carry weight exactly
  `1/4`. Hence the first-site amplitude
  `γ_1(t) = Σ_n w_n e^{−iλ_n t}` satisfies
  `γ_1(jπ/2) = (1/4) Σ_{k<4} (−i)^{jk}`, which is `0` for `j = 1, 2, 3` and `1`
  for `j = 4`: the amplitude vanishes at `t₀/2`, `t₀` and `3t₀/2` and returns
  at `2t₀`.
- **Computed, why one equation suffices.** The spectrum is mirror symmetric,
  `λ_n + λ_{9−n} = 153`, so `|B'(λ_n)| = |B'(λ_{9−n})|`; and `153 ≡ 1` modulo
  4, so the mirror exchanges the classes `0 ↔ 1` and `2 ↔ 3`. Thus
  `R_0 = R_1` and `R_2 = R_3` hold for every mirror-symmetric spectrum with
  these residues, and the only remaining condition is
  `1/|B'(λ_1)| + 1/|B'(λ_4)| = 1/|B'(λ_2)| + 1/|B'(λ_3)|`, which the four gaps
  `31, 15, 19, 23` solve. The source's displayed argument for large `M` uses a
  class with a single level; at `M = N/2` every class can have two levels and
  that argument has nothing to act on.
- **Computed, the chain.** The inverse eigenvalue problem for this spectrum
  gives the mirror-symmetric chain with constant diagonal `153/2` and squared
  couplings `834785/1164, 1197437/1455, 34047/20, 2500, 34047/20,
  1197437/1455, 834785/1164`; its first-site weights are the `w_n` above by
  construction. The chain is not in Lean.
- **What survives.** The source states a proof for `M > N/2`; it is not
  formalised or checked here. If it holds, `M = 4` needs `N ≥ 8`, so the
  spectrum above has the least possible number of levels for `M = 4`.
  **Computed (the script in Evidence, last line):** for `3 ≤ M ≤ N` there is no
  spectrum with `N ≤ 6` and odd gaps at most 31, none with `N = 7` and odd
  gaps at most 15, and none with `N = 8` and odd gaps at most 9; among the
  mirror-symmetric spectra with `N = 8` and odd gaps at most 41 the spectrum
  above is the only one, and only for `M = 4`. Gaps equal to 1 (`m_n = 0`) are
  included in these searches.
- **Open.** Whether an odd `M > 2` can occur; whether `M = 4` can occur with
  `N = 9, 10, 11` or with a spectrum that is not mirror symmetric; whether
  some `M ≥ 5` can occur; a proof that `N = 8` is least for `M = 4`. Issue
  #14475 reports an unformalised 2-adic argument and a computation excluding
  `4 | M` for `N ≤ 7` and `N = 9, 10, 11`; neither is reproduced here and
  neither is a proof in this repository.
- **Computed, the zeros.** For the spectrum above the first-site amplitude
  with the Hochstadt weights vanishes at `t₀/2`, `t₀` and `3t₀/2` and equals 1
  at `2t₀` (first script: the four class weights are `1/4`).
- **Proved on paper, not in Lean: `M = 4` is a zero at `t₀/2`.** For a perfect
  state transfer spectrum put `z_n = (t₀/π)(λ_n − λ_1)`; then
  `γ_1(t₀/2)` is proportional to `Σ_k R_k (−i)^k` over the classes modulo 4.
  The parity of `z_n` alternates with `n`, so `R_0 + R_2` and `R_1 + R_3` are
  the two parity sums, which are equal because `Σ_n 1/B'(λ_n) = 0`
  (equivalently, the amplitude vanishes at `t₀`); hence
  `γ_1(t₀/2) = 0` holds exactly when `R_0 = R_2` and `R_1 = R_3`, that is when
  all four `R_k` are equal. The zero at `3t₀/2` then follows from
  `|γ_1(t₀+s)| = |γ_1(t₀−s)|`.
- **Open, conditional on the source's lemma.** By the lemma of the source,
  which is not formalised here, the chain above achieves the rate
  `M/2t₀ = 2/t₀`, that is `t_r = t₀/2`; this would contradict the stronger
  conjecture stated before the lemma, "that there are no chains with
  $t_r<t_0$", and attain at `N = 8` the bound `1/t_r ≤ N/4t₀` that the source
  derives from the lemma.
- **Computed, the count for arXiv:1102.2338.** That paper's bound
  `2l + D ≤ M ≤ N`, with `D` the transfer distance, `M` the number of distinct
  eigenvalues and `l` the number of times before `t₀` at which the amplitude
  on the input site vanishes, gives `l = 0` for a chain (`D = N − 1`). The
  spectrum above has `N = 8`, `D = 7` and a zero at `t₀/2`, so `2l + D ≥ 9 > 8`.
  The published `4×4` example of arXiv:2411.06047 violates the same bound
  (`N = 4`, `D = 3`, `l = 1`), so this failure is not new here. **Open:** which
  step of the derivation of the bound fails.
- **Literature reading with a computed check: early state exclusion.**
  arXiv:2411.06047 constructs perfect state transfer Jacobi matrices whose
  first-site amplitude vanishes before `t₀`, with any prescribed number of
  such zeros, and proves that equally spaced spectra have none;
  arXiv:2507.18767 and arXiv:2606.04353 continue that study. By the
  equivalence above, the spectrum of this dossier is an example with a zero at
  exactly `t₀/2`. **Computed (second script):** none of the spectra extracted
  from those three papers fulfils the condition of the lemma for any
  `3 ≤ M ≤ N`.

## ASSUMED-UNVERIFIED

- The source's lemma (equal `R_k` if and only if the rate `M/2t₀` is achieved
  perfectly), its proof for `M > N/2` and its Eqn. `eqn:hoch` are used as
  stated; none is formalised here. The consequences listed for the rate, for
  `t_r` and for arXiv:1102.2338 depend on them.
- The journal text was not compared with arXiv v3; the statement formalised is
  that of the arXiv v3 source `review.tex`.
- The literature readings in Gap: the two quoted sentences of
  arXiv:1102.2338 and the theorems and the `4×4` example of arXiv:2411.06047
  were read in their sources; the spectra used by the second script were
  extracted from arXiv:2411.06047, arXiv:2507.18767 and arXiv:2606.04353 by a
  review seat and were not compared example by example with the papers;
  arXiv:2209.08160 and the INSPIRE scan are as recorded in #14475. No
  exhaustive novelty or priority is asserted.
- The 2-adic argument and the computation for `N = 9, 10, 11` reported in
  #14475 were not reproduced.
