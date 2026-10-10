---
slug: dekking-keane-2022-two-block-thue-morse-frequency
bibkey: dekking2022twoblock
doi: 10.48550/arXiv.2202.13548
url: https://arxiv.org/abs/2202.13548v1
triage: theorem
motivation_gids:
  - D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.result
---

# The Thue–Morse two-block fixed point has frequency one half

## Problem

Dekking and Keane, *Two-block substitutions and morphic words*, arXiv:2202.13548v1,
Section 4, define
$\kappa_{\rm TM}(00)=001$, $\kappa_{\rm TM}(01)=010$,
$\kappa_{\rm TM}(10)=101$, and $\kappa_{\rm TM}(11)=110$.
Their fixed point $x^{(00)}$ starts with $00$ and satisfies
$x_{3n}=x_{2n}$, $x_{3n+1}=x_{2n+1}$, and $x_{3n+2}=1-x_{2n+1}$.

> **Conjecture 4.** The frequency of 1 in $x^{(00)}$ exists and equals $\frac12$.

The source is v1, Section 4, pp. 5–6. ArXiv v2 and the journal version change
the substitution; this conclusion concerns the displayed v1 table.

## Motivation

The assertion asks for the limit over every natural prefix length, rather
than a numerical approximation at selected lengths. The settling declaration
is `D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.result`.
Preregistration [#14986](https://github.com/the-omega-institute/trureturing/issues/14986)
fixes the literal table, the residue-first recursion, the counting ratio and
its real-valued `Filter.Tendsto` conclusion.

## Gap

The v1 paper states Conjecture 4 and OEIS A354896 records the density as an
unsolved problem. The source and literature checks in #14986 identify no
settlement of this v1 assertion. These bounded checks do not establish
worldwide priority. Frequency theorems for different substitutions do not
settle the displayed table.

## Route

For signs $a_n=1-2x_n$, a substitution step sends a pair $(u,v)$ to
$(u,v,-v)$. The coefficient functional $d_k$ of its $k$-fold iterate is
periodic modulo $2^k$ and satisfies
$d_{k+1}(2j)=d_k(3j)$ and
$d_{k+1}(2j+1)=d_k(3j+1)-d_k(3j+2)$.
Multiplication by $3$ permutes the residues modulo $2^k$.

Let $E_k=\sum_{r<2^k}d_k(r)^2$ and
$R_k=\sum_{r<2^k}d_k(r)d_k(r+1)$, with cyclic indices.
The four terms in $R_{k+1}$ cancel in pairs after cyclic shifts, so
$R_{k+1}=0$ and $E_{k+1}=3E_k-2R_k$.
The initial values $E_1=1$ and $R_1=0$ give $E_k=3^{k-1}$ for $k\ge1$.
Finite Cauchy–Schwarz bounds every aligned block of length $3^k$ by
$B_k=\sqrt{2^k3^{k-1}}$.

For $N=q3^k+r$ with $0\le r<3^k$, the signed prefix sum $S_N$ satisfies
$|S_N|\le qB_k+r$, hence
$|S_N|/N\le B_k/3^k+3^k/N$.
For fixed $k$, the second term tends to zero; the first tends to zero as
$k\to\infty$. Thus the signed mean tends to zero. The exact identity
$S_N=N-2\#\{n<N:x_n=1\}$ gives frequency $1/2$.

## Falsifier

A disagreement between `kappaTM`, `tmFixed` or `claim` and the quoted source
would invalidate the resolution claim. A fixed point of this table whose
true-letter counting ratio fails to tend to $1/2$ would contradict the
mathematical conclusion. The recurrence at residue zero reads only its first
input; evaluating that residue before recursion makes every recursive index
strictly smaller without changing the table equations.

## Evidence

The Lean module uses `Mathlib.Data.Nat.Periodic`,
`Mathlib.Analysis.SpecialFunctions.Sqrt` and the frozen block-sum declarations
`D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.sum_pairs` and
`D5.S1.Recurrence.Residue.ExponentialSquareWeightTernarySupport.sum_triples`,
both with coefficient type $\mathbb Z$. Its public theorem is
`result : claim`, with no extra hypotheses. The axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The Scribe has one `OpenProblemResolutionClaim` with resolution `Proved` on
this settling node. The Library note is
[dekking2022twoblock](../Library/Words/dekking2022twoblock.md).

The four-slot escape audit is unfinished:
[#15019](https://github.com/the-omega-institute/trureturing/issues/15019).
The public target is `D5.S1.Words.TwoBlockSubstitution.ThueMorseFrequency.result`.
A faithful registration still needs a source-bound convergence readout,
an equivalence bridge, whole-family variation and sensitivity, and actual
observational dependence. No validated registration is claimed.

Experiment entry:
[dekking-keane-2022-two-block-frequency](https://github.com/the-omega-institute/trureturing-experiments/tree/dc9fab204a29653ebe491c6bb8fafcb5795e884b/docs/reports/dekking-keane-2022-two-block-frequency),
in `the-omega-institute/trureturing-experiments`, commit
`dc9fab204a29653ebe491c6bb8fafcb5795e884b`.
Command: `python3 check.py 1594323`; exit code: **0**.
SHA-256: `c1fa93f145a2e886246578f6cde4ba41a8b7e4b200fad96e6a16faed9a3e1b26`.
The scope is the $00$ seed through $N=3^{13}=1594323$, the source recurrence
for every complete triple, and the cyclic identities at $k=1,\ldots,10$.
The prefix is `001110101101110010110001101110001`.
The measured frequency is $0.500266257213877$ and the maximum of
$|S_N|/N^\alpha$ over $1000\le N\le1594323$ is $0.1082$.
The energies for $k=1,\ldots,10$ are
$1,3,9,27,81,243,729,2187,6561,19683$; all corresponding correlations are zero.
These finite readings are not the evidence for the unbounded limit.

## Triage

### What the settlement shows

- **Mechanism — proved, kernel-checked.** The private declarations
  `coefficient_functional`, `correlation_succ`, `energy_recurrence` and
  `energy_succ` establish the coefficient formula, cancellation and energy
  on the derivation of `result`. The four correlation sums cancel after
  reindexing by the permutation induced by multiplication by $3$ modulo
  $2^k$. The claims $R_k=0$ and $E_k=3^{k-1}$ concern $k\ge1$;
  $R_0=E_0=1$.
- **Block bound and density — proved, kernel-checked.**
  `aligned_square_bound` applies `Finset.sum_mul_sq_le_sq_mul_sq` to the
  coefficient functional. `aligned_block_bound` gives $B_k$ for $k\ge1$.
  `signed_mean_tendsto` and `fixed_point_density` turn this into frequency
  $1/2$, and `result` applies it to the source's $00$ fixed point.
- **All four fixed points — proved.** `fixed_point_density` is kernel-checked
  for every Boolean word satisfying the source table equations, with no seed
  hypothesis. For each prefix $ab\in\{00,01,10,11\}$, prescribe $x_0=a$,
  $x_1=b$ and use the same residue-first recursion. All recursive indices
  are smaller, the residue-zero equation reads only its first input, and
  the three equations follow including $n=0$, where $x_2=1-b$.
  Each of these four fixed points therefore satisfies the hypothesis of
  `fixed_point_density` and has density $1/2$. Construction of the three
  additional words is proved here in prose, not added as Lean declarations.
- **Discrepancy rate — proved in prose, not formalized.** Write $N$ in base
  $3$ and partition its prefix from largest to smallest blocks. There are
  at most two aligned blocks of each length $3^k$, and their starting
  positions are multiples of $3^k$. Put $m=\lfloor\log_3N\rfloor$ and
  $r=\sqrt6$. Singletons have bound $1$, and $B_k=r^k/\sqrt3$ for $k\ge1$.
  Therefore
  $|S_N|\le2+(2/\sqrt3)\sum_{k=1}^m r^k
  \le[2+2r/(\sqrt3(r-1))]r^m
  \le[2+2r/(\sqrt3(r-1))]N^\alpha$,
  where $\alpha=\log\sqrt6/\log3\approx0.8154648768$.
  This uniform estimate applies to all four fixed points. It is an upper
  bound; optimality of this exponent is open.
- **Readings — computed.** The pinned experiment, command, exit code,
  SHA-256 and exact tested scope are given in Evidence. The computation
  checks the $00$ word and $k\le10$ identities; the uniform extensions use
  the proof, not the finite computation.
- **Related result — proved in cited literature.** Cassaigne, Espinoza, Rigo and Stipulanti,
  [arXiv:2602.21895](https://arxiv.org/abs/2602.21895), prove frequency $1/2$
  for different two-block substitutions by harmonic analysis on the
  $2$-adic integers. That paper concerns different substitutions; it is
  not on this module's dependency path. The argument here uses elementary
  finite energy and correlation identities.
- **Neighbouring questions — open.** Conjectures 1–3 of the v1 source
  concern mirror invariance, complexity at least $cn^2$, and uniform
  recurrence for the same word. Frequencies of longer factors remain
  open. The one-letter limit and its discrepancy bound do not establish
  any of those statements. This settlement supplies the asserted
  single-letter density wherever the source uses Conjecture 4; it adds no
  proof of those separate conjectures.

## ASSUMED-UNVERIFIED

Worldwide priority is not established by the bounded literature checks.
The escape registration evidence identified in #15019 is missing.
No sharpness claim is made for the discrepancy exponent.
