---
slug: escobar-garcia-2025-seven-site-early-state-exclusion
bibkey: escobar2025earlystateexclusion
doi: 10.48550/arXiv.2507.18767
url: https://arxiv.org/abs/2507.18767v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion.result
---

# Early state exclusion in seven-site chains with symmetric spectrum

## Problem

M. G. Escobar, V. Garcia and A. Minenkova, *Early State Exclusion in 7-Qubit
Spin Chains*, arXiv:2507.18767v1, Section 4. A Jacobi matrix is a real
symmetric tridiagonal matrix with positive off-diagonal entries (Eq. (1.1):
"for $a_i \in \R$ and $b_i > 0$"). The source defines (quoted with its
displayed equations set inline and without `\emph` and `\label` markup):

> A Jacobi matrix $J$ realizes \textbf{perfect state transfer} (PST) between the end-vertices of the weighted path in Figure \ref{fig:nearestneighbor} at time $T > 0$ if $e^{-iJT}\e_0 = e^{i\phi}\e_N$ for some phase $\phi \in \R$.

> We consider a special case where $J$ has symmetric spectrum in section 3, meaning that for $\{\lambda_k\}_{k = 0}^N$, $\lambda_j = -\lambda_{N - j}$ for all $1 \leq j \leq N - 1$.

> Let $J$ be a Jacobi matrix realizing PST at earliest time $T > 0$. If there exists some $\tau \in (0, T)$ such that $\langle e^{-iJ\tau}\e_0, \e_0 \rangle = 0$, then we say that $J$ exhibits \textbf{early state exclusion} (ESE) at time $\tau$.

and conjectures:

> Let $J$ be a $7 \times 7$ Jacobi matrix with symmetric spectrum realizing PST. Then $J$ does not have ESE if and only if its positive eigenvalues are integer multiples of the smallest positive eigenvalue.

Issue #14487 fixes the reading. "Symmetric spectrum" is read as closure of the
spectrum under negation, the definition of arXiv:2606.04353 ("if
$-\lambda \in \sigma(J)$ whenever $\lambda  \in \sigma(J)$") and the sense in
which the source uses it for $\{0, \pm x, \pm y, \pm z\}$. The matrix is `pathHamiltonian r q` with
`r : Fin 6 → ℝ` positive and `q : Fin 7 → ℝ` arbitrary; perfect state transfer
at time `t` is `HasPST J t 0 (Fin.last 6)`, the modulus-one form of the
source's condition; the eigenvalues are Mathlib's
`(pathHamiltonian_isHermitian r q).eigenvalues`, and the spectrum is symmetric
when the negative of every eigenvalue is an eigenvalue; `T` is an earliest time
when `0 < T`, there is transfer at `T` and at no time in `(0, T)`; early state
exclusion is a `τ ∈ (0, T)` with `hamiltonianPropagator J τ 0 0 = 0`; the
divisibility condition asks for a positive eigenvalue that is the least
positive one and of which every positive eigenvalue is an integer multiple.
The statement is universally quantified over `r`, `q` and `T`.

## Motivation

Early state exclusion was introduced (arXiv:2411.06047) as a time before the
first perfect transfer at which the sender site is empty, so that a new state
could be injected early. For five sites the divisibility condition was known
to decide it; the source proves two one-parameter families for seven sites
(Theorems 3.2 and 3.4) and states that its techniques "cannot be replicated"
for the general seven-site statement. The declaration
`D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion.result` proves the
conjecture.

## Gap

Issue #14487 preregisters the verbatim source, the reading above, the expected
settlement and the literature check before any formalization. Its recorded
readings (2026-10-08): an arXiv full-text query for "early state exclusion"
returns three records, arXiv:2411.06047, the source, and arXiv:2606.04353
(Escobar, Garcia, Minenkova, June 2026). The last one says of the five- and
seven-site work

> Based on these examples, it was conjectured that this spectral property characterizes the presence or absence of ESE in systems with symmetric spectra. In this work, we demonstrate that this is not the case in general for larger chains.

and states

> It is known that a Jacobi matrix with a reduced symmetric spectrum $\{0, \pm \lambda_1, \pm \lambda_2\}$ has ESE if and only if $\lambda_1 \neq 1$~\cite{EM25}. This is not true in the general case

and illustrates the failure by appending $\pm 17$ to the nine-site spectrum
$\{0, \pm1, \pm14, \pm15, \pm16\}$. Its Section 3 gives, for every persymmetric
Jacobi matrix with symmetric spectrum of any order, the first-site amplitude
as a cosine sum with Hochstadt's weights (Proposition "Amplitude Formulas")
and the reduction to integer spectra of alternating parity with greatest
common divisor 1, first transfer at $\pi$ and time scaling by a common factor;
it also proves an upper bound on the number of early exclusion times and a
stability theorem under appending far eigenvalues. So Route steps 1 to 3 below
are known mathematics. The paper neither proves nor refutes the seven-site
conjecture. Semantic Scholar lists that paper as the only work citing the
source (read 2026-10-08). These readings are
`not-found-in-searched-scope`; they do not establish an exhaustive literature
search or priority.

## Route

1. **Spectrum.** Transfer at time `T` between the end sites makes the
   eigenvalues simple and fixes the first-site weights as
   $w_k = P / \prod_{l \ne k} |\lambda_k - \lambda_l|$, $P = \prod_j r_j$, with
   the phases $e^{iT\lambda_k}$ equal to a common unit times the sign of
   $\prod_{l \neq k} (\lambda_k - \lambda_l)$. For a symmetric seven-point
   spectrum $\{0, \pm x, \pm y, \pm z\}$ this gives $e^{iTx} = -1$,
   $e^{iTy} = 1$, $e^{iTz} = -1$, hence $x = \tfrac{\pi}{T} a$,
   $y = \tfrac{\pi}{T} b$, $z = \tfrac{\pi}{T} c$ with $a$ odd, $b$ even,
   $c$ odd, $0 < a < b < c$.
2. **Amplitude.** $(e^{-iJ\tau})_{0,0} = \sum_k w_k e^{-i\tau\lambda_k}
   = \kappa\, N(\pi\tau/T)$ with $\kappa > 0$ and
   $N(t) = (b^2-a^2)(c^2-a^2)(c^2-b^2) + b^2c^2(c^2-b^2)\cos at
   + a^2c^2(c^2-a^2)\cos bt + a^2b^2(b^2-a^2)\cos ct$.
3. **Earliest time.** If an integer $g$ divides $a$, $b$ and $c$ there is
   transfer at $T/g$; so an earliest $T$ forces $\gcd(a, b, c) = 1$, and the
   divisibility condition becomes $a = 1$.
4. **$a = 1$: no zero.** With $t = \pi - 2\theta$, $N = 2B$ and
   $B = b^2c^2\big[(\psi(\theta) - \psi(b\theta))((c\theta)^2 - \theta^2)
   - (\psi(\theta) - \psi(c\theta))((b\theta)^2 - \theta^2)\big]$,
   $\psi(u) = (\sin u/u)^2$. $B > 0$ because the chord slope
   $(\psi(\theta) - \psi(u))/(u^2 - \theta^2)$ is strictly decreasing in
   $u > \theta$ for $\theta \in (0, \pi/2]$: $\psi'(u)/u$ is strictly
   increasing on $(0, \pi]$, and beyond $\pi$ the tangent value stays below
   $4/\pi^2 \le \psi(\theta)$.
5. **$a \ge 3$: a zero.** $N(0) > 0$. If $a \nmid b$, averaging
   $\sin^2(\pi j b/a) - \sin^2(\pi j c/a)$ over the residues $j$ gives a time
   $|\pi - 2\pi j/a|$ with $N < 0$; if $a \mid b$, the time
   $|\pi - 2\pi l/c|$ with $a l \equiv \gcd(a, c) \pmod c$ has $N < 0$ by
   $\sin y > y - y^3/6$ and $\sin^2 x \le x^2$.

## Falsifier

A seven-site chain with symmetric spectrum and an earliest transfer time for
which the two sides of the equivalence disagree would refute the statement;
by the Route it would be a reduced triple $(a, b, c)$ with $a = 1$ and a zero
of $N$ in $(0, \pi)$, or with $a \ge 3$ and none. Reading "symmetric spectrum"
as symmetric about a point other than $0$ changes the amplitude only by a
phase (the source's Section 3.3); reading the transfer time as any transfer
time instead of the earliest one makes the statement false: the equidistant
spectrum $\{0, \pm 3, \pm 6, \pm 9\}$ (a figure of arXiv:2606.04353) satisfies
the divisibility condition and has transfer at $T = \pi$, but its amplitude
$\cos^6(3\tau/2)$ vanishes at $\tau = \pi/3$, which is its earliest transfer
time.

## Evidence

The public theorem `result : claim` is in
`D5/S3/Quantum/Dynamics/SevenSiteEarlyStateExclusion.lean`. It rests on
`D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude.symmetric_spectrum_reduction`
(Route steps 1 and 2 and the transfer at $T/g$ of step 3; the two conclusions
of step 3, $\gcd(a, b, c) = 1$ from the minimality of $T$ and the equivalence
of the divisibility condition with $a = 1$, are steps of `result`), on
`D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_zero_iff`
(steps 4–5) and on
`D5/S3/Quantum/Dynamics/SincSquareChordSlope.sincSq_chord_lt`. The axiom
closure of `result` is `propext`, `Classical.choice`, `Quot.sound`; no `sorry`,
`native_decide` or new axiom.

The following script counts, by Sturm sequences, the zeros in $(0, \pi)$ of the
Chebyshev form of the amplitude for reduced symmetric spectra
(`python3 ese.py`, Python 3 with sympy):

```python
import math
from fractions import Fraction
from itertools import combinations
import sympy as sp

x = sp.symbols('x')

def zeros(lams):
    l = [0] + list(lams)
    c = []
    for k in range(len(l)):
        p = 1
        for i in range(len(l)):
            if i != k: p *= abs(l[k] ** 2 - l[i] ** 2)
        c.append(Fraction(1, p))
    P = sum(sp.Rational(ck.numerator, ck.denominator) * sp.chebyshevt(lk, x) for lk, ck in zip(l, c))
    P = sp.Poly(sp.expand(P), x, domain='QQ')
    Q, R = sp.div(P, sp.Poly((x + 1) ** len(lams), x, domain='QQ'))
    assert R.is_zero and Q.eval(-1) != 0 and Q.eval(1) != 0
    return Q.count_roots(-1, 1)

def admissible(n, bound):
    for t in combinations(range(1, bound + 1), n):
        if all((t[i] - (t[i - 1] if i else 0)) % 2 == 1 for i in range(n)) and math.gcd(*t) == 1:
            yield t

for n, bound in ((2, 31), (3, 23), (4, 25)):
    stat = {}
    for t in admissible(n, bound):
        key = (t[0] == 1, zeros(t) > 0)
        stat[key] = stat.get(key, 0) + 1
    print(2 * n + 1, bound, dict(sorted(stat.items())))
print(zeros((1, 14, 15, 16)), zeros((1, 14, 15, 16, 17)), zeros((1, 14, 15, 16, 19)), zeros((1, 12, 13, 14, 15)))
print([zeros((2 * m + 1, 2 * m + 2, 2 * m + 3)) for m in range(1, 6)])
```

Its output: order 5, largest eigenvalue at most 31: 15 spectra with smallest
eigenvalue 1 and no zero, 80 with smallest eigenvalue above 1 and a zero;
order 7, at most 23: 66 and 208; order 9, at most 25: 286 and 699; no
exception in any of the three. The spectra $(1, 14, 15, 16)$,
$(1, 14, 15, 16, 17)$, $(1, 14, 15, 16, 19)$, $(1, 12, 13, 14, 15)$ have $0$,
$8$, $0$, $4$ zeros, and the triples $(2m+1, 2m+2, 2m+3)$, $m = 1, \dots, 5$,
have $2, 4, 6, 8, 10$. Longer runs of the same two functions: order 9 with
largest eigenvalue at most 37, 969 and 3800 with no exception; order 11 at
most 23, 710 spectra with smallest eigenvalue 1 and no zero, 5 with smallest
eigenvalue 1 and zeros (the spectra $(1, k, k+1, k+2, k+3)$,
$k = 12, 14, \dots, 20$), 1281 with smallest eigenvalue above 1, all with a
zero; order 13 at most 21, 764, 28 and 923 in the same three classes.

## Triage

Tier 1; the conjecture is **proved in this module**. Admission basis
`open-problem-resolution` (#14487; Proved). Information-escape registration is
paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved** (`D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.amplitudeNumerator_pos`):
  the cosine sum $N(1, b, c; t)$ is strictly positive on $[0, \pi)$.
  **Immediate consequence** (not a Lean statement): since the amplitude is
  $\kappa N(\pi\tau/T)$ with $\kappa > 0$, it is strictly positive on $[0, T)$
  when the positive eigenvalues are multiples of the smallest one, not merely
  nonzero.
- **Proved** (`D5/S3/Quantum/Dynamics/SincSquareChordSlope.sincSq_chord_lt`):
  the mechanism is a convexity property of $\operatorname{sinc}^2$ in the
  squared variable. With $f(X) = \sin^2(\theta\sqrt X)/X$ the quantity $B$ of
  Route step 4 is a positive multiple of the second divided difference
  $f[1, b^2, c^2]$, and the theorem says that the chord slope of $f$ from the
  node $1$ is increasing.
- **Proved** (`D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros.exists_amplitudeNumerator_neg`):
  when $a \ge 3$ the cosine sum takes a negative value at some point of
  $(0, \pi)$. The statement is existential; its proof uses the points
  $|\pi - 2\pi j/a|$ and $|\pi - 2\pi l/c|$ of Route step 5.
- **Proved** (`D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude.symmetric_spectrum_end_amplitude`):
  the amplitude formula for every seven-site chain with positive couplings,
  real potentials, symmetric spectrum and transfer at some time. The formula is
  known (the source's Eq. (2.1) for its explicit matrix; arXiv:2606.04353,
  Proposition "Amplitude Formulas", for every persymmetric Jacobi matrix with
  symmetric spectrum; Kay's criterion for persymmetry); the declaration is its
  Lean derivation from the hypothesis of transfer.
- **Proved** (`D5/S3/Quantum/Dynamics/SymmetricSpectrumEndAmplitude.symmetric_spectrum_reduction`):
  transfer at $T$ with symmetric spectrum forces the spectrum
  $\tfrac{\pi}{T}\{0, \pm a, \pm b, \pm c\}$ with $a$, $c$ odd and $b$ even,
  and a common divisor $g$ of $a, b, c$ gives transfer at $T/g$. This
  reduction is stated in Section 3 of arXiv:2606.04353; the declaration is its
  Lean proof for seven sites.
- **Computed** (by hand, not Lean statements): the hypotheses of `claim` are
  satisfiable on both sides of the equivalence, by the chains with spectra
  $\{0, \pm 1, \pm 2, \pm 3\}$ (amplitude $\cos^6(\tau/2)$, no zero before
  $\pi$) and $\{0, \pm 3, \pm 4, \pm 5\}$ (a figure of the source, with early
  state exclusion). A spectrum symmetric about a point $\mu \neq 0$ is covered
  after the shift of the potentials by $-\mu$, which multiplies the amplitude
  by a phase and changes neither the transfer times nor the zeros; `claim` is
  stated for $\mu = 0$, as the source's conjecture is.
- **Computed** (algebra, not a Lean statement): for five sites the same
  reduction gives $N_5(\pi - 2\theta) = 2\,(b^2 \sin^2 a\theta - a^2 \sin^2
  b\theta)$; for $a = 1$ this is positive by $|\sin b\theta| < b \sin\theta$,
  and for $a \ge 3$ it is negative at $\theta = \pi/a$. The five-site
  criterion is a first divided difference of $f$, the seven-site one a second.
- **Computed** (script above): for nine sites the criterion holds on all 4769
  reduced spectra with largest eigenvalue at most 37; for eleven sites it
  fails first at $\{0, \pm1, \pm12, \pm13, \pm14, \pm15\}$ (4 zeros), and at
  $\{0, \pm1, \pm14, \pm15, \pm16, \pm17\}$ (8 zeros), the example of
  arXiv:2606.04353.
- **Open:** the nine-site statement. In the divided-difference form it asks
  for a sign of $f[1, b^2, c^2, d^2]$; no proof is given here.
- **Open:** whether every chain of odd order with symmetric spectrum whose
  smallest positive eigenvalue does not divide the others has early state
  exclusion (no exception in the scans above, orders 5 to 13).
- **Open:** the number of zeros for $a \ge 3$. The source's Theorem 3.4 gives
  $2m$ for $(2m+1, 2m+2, 2m+3)$ (reproduced by the script for $m \le 5$);
  arXiv:2606.04353 bounds the number by $c - 3$ and shows it is even.
- **Effect on the source** (proved for the first two clauses, computed and
  literature for the last): the conjecture of Section 4 becomes a theorem;
  Theorem 3.2 and the existence part of Theorem 3.4 are special cases; the
  extension "for an arbitrary Jacobi matrix of odd order" mentioned after the
  conjecture fails at order 11 (the figure of arXiv:2606.04353 and the exact
  counts above), fails at order 13 in the scan above, and is undecided at
  order 9.

## ASSUMED-UNVERIFIED

Literature-search completeness outside the scope recorded in #14487 is
unverified. The five-site algebra and the nine- and eleven-site counts are
not Lean statements. The reference [EM25] of arXiv:2606.04353 for the
five-site criterion was not read.
