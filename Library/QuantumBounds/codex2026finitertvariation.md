---
bibkey: codex2026finitertvariation
authors: the-omega-institute/trureturing
title: "Finite-sector variational domination and finite-phase orientation trivialization"
year: 2026
doi: null
url: https://github.com/the-omega-institute/trureturing/tree/dev/D5/S3/Quantum/Entanglement
claim: "Existing-result applications giving simultaneous finite variational domination and a gluing-compatible trivialization of selected finite Boolean orientation models."
strata_touched: []
license: citation-only
triage: anchor
---

## Finite variational statement

Let $I$ be any nonempty finite index type, with no restriction on its universe,
and let $A:I\times I\to\mathbb R$ satisfy $A_{ij}\ge0$ for all $i,j$.
Neither symmetry nor positive semidefiniteness is assumed. Define

$$
\begin{aligned}
\Delta_I&=\{p:I\to\mathbb R:\ p_i\ge0,\ \sum_i p_i=1\},\\
Q_A(w)&=\sum_{i,j}A_{ij}w_iw_j,\\
R_A(p,x)&=\sum_{i,j}\sqrt{p_i}\sqrt{p_j}A_{ij}
                 \operatorname{Re}(\overline{x_i}x_j),\qquad x:I\to\mathbb C.
\end{aligned}
$$

There exists one $r\in\Delta_I$ such that simultaneously

$$
\begin{aligned}
&\forall w\in\Delta_I,\quad Q_A(w)\le Q_A(r),\\
&\forall p\in\Delta_I\ \forall x:I\to\mathbb C,\quad
  \sum_i|x_i|^2=1\ \Longrightarrow\ R_A(p,x)\le Q_A(r).
\end{aligned}
$$

The choice of $r$ precedes both universal quantifiers. It depends on $A$, not
on $w$, $p$, or $x$. This includes singleton index types, zero matrices,
zero coordinates of $p$, and nonsymmetric nonnegative matrices.

The simplex is nonempty and compact, and $Q_A$ is a continuous polynomial,
so choose a maximizer $r$. For arbitrary $p,x$ as above, put
$y_i=\sqrt{p_i}|x_i|$ and $m=\sum_i y_i$. Cauchy--Schwarz gives

$$
0\le m,\qquad
m^2\le\left(\sum_i(\sqrt{p_i})^2\right)
        \left(\sum_i|x_i|^2\right)=1,
\qquad m\le1.
$$

Fix any $i_0\in I$ and fill the missing mass:
$w_i=y_i+(1-m)\mathbf1_{i=i_0}$. Then $w_i\ge y_i\ge0$ and
$\sum_iw_i=m+(1-m)=1$, so $w\in\Delta_I$. For every pair of indices,

$$
\operatorname{Re}(\overline{x_i}x_j)
\le |\overline{x_i}x_j|=|x_i||x_j|.
$$

Multiplying by the nonnegative coefficient
$\sqrt{p_i}\sqrt{p_j}A_{ij}$, summing, and using $w\ge y\ge0$ yields

$$
R_A(p,x)\le Q_A(y)\le Q_A(w)\le Q_A(r).
$$

Thus the same simplex maximum bounds every normalized weighted complex
form. No Hermitian eigenvalue interpretation is needed for this statement.

The existing proof of `schur_upper` in
[FiniteSectorSchurUpper.lean](../../D5/S3/Quantum/Entanglement/FiniteSectorSchurUpper.lean)
contains this arbitrary-$A$ argument as its local `hRayleigh` proof inside
`hRayleighMax` and `hSchurPureUpper`. Its compactness and phase inequalities
supply the statement above. The public `schur_upper` has the more specific
residual-overlap model and kernel hypotheses; it is not a public theorem
for arbitrary $A$. Applying the local variational argument does not assert
the full channel optimization of theory §36.1 for arbitrary matrices.

## Actual selected residue phases

Use the recurrence in the existing
[Fibonacci certificate](../../docs/reports/fib-canonical-budget/certificate.py),
function `weight_orbit`. For each modulus $m>0$, define

$$
\begin{aligned}
T_m(u,v)&=((u+2v)\bmod m,\ (2u+3v)\bmod m),\\
a_m(0)&=(2\bmod m,3\bmod m),\qquad
 a_m(k+1)=T_m(a_m(k)).
\end{aligned}
$$

The selected orbit lengths are least positive return times of this initial
pair, not just orientation periods:

| Modulus $m$ | Least period $N_m$ | Initial pair | Last pair $a_m(N_m-1)$ |
| --- | ---: | --- | --- |
| $5040=16\cdot9\cdot5\cdot7$ | 80 | $(2,3)$ | $(0,1)$ |
| 7 | 16 | $(2,3)$ | $(0,1)$ |
| 16 | 8 | $(2,3)$ | $(0,1)$ |
| 9 | 8 | $(2,3)$ | $(0,1)$ |
| 5 | 20 | $(2,3)$ | $(0,1)$ |

For each listed modulus, the $N_m$ rows are within $[0,m)^2$ and pairwise
distinct; the recurrence holds at every row, including the closing step
$T_m(0,1)=(2,3)$. Therefore induction identifies the rows with the actual
iterates, and distinctness excludes any positive return before $N_m$.
For example, the entire modulus-7 orbit, in order, is

$$
\begin{aligned}
&(2,3),(1,6),(6,6),(4,2),(1,0),(1,2),(5,1),(0,6),\\
&(5,4),(6,1),(1,1),(3,5),(6,0),(6,5),(2,6),(0,1).
\end{aligned}
$$

Reduction of each common row modulo $m\in\{16,9,5,7\}$ gives
$a_m(k\bmod N_m)$. Reduction commutes with $T$, and the local periods divide
80; this specifies the common-to-local phase projection, including wrap.

## Equivariant Boolean cover and closing gluing

For any positive even $N$, write $C_N=\{0,\ldots,N-1\}$,
$s_N(i)=(i+1)\bmod N$, and $\epsilon(i)=i\bmod2\in\{0,1\}$.
The selected finite model has total set $C_N\times\{0,1\}$, projection
$\pi(i,b)=i$, and lifted successor
$F_N(i,b)=(s_N(i),b\mathbin\oplus1)$, where $\oplus$ is Boolean XOR.
The sheet-preserving successor is $H_N(i,b)=(s_N(i),b)$.
Define the gauge

$$
G_N(i,b)=(i,b\mathbin\oplus\epsilon(i)).
$$

It is its own inverse and preserves $\pi$. At every ordinary edge the
parity changes by one. At the closing edge, $N-1$ is odd and $s_N(N-1)=0$,
so parity changes there as well. Consequently

$$
G_N\circ F_N=H_N\circ G_N,
\qquad
G_N(0,b\mathbin\oplus1)
   =(0,b\mathbin\oplus1)
   =H_N(G_N(N-1,b)).
$$

This is an equivalence over the base that respects the actual successor
and the closing gluing. In the gauged coordinates the directed lifted
cycle is two separate sheet-preserving copies of $C_N$. Its monodromy is
identity after $N$ steps.

To place this construction over the actual residues rather than an
abstract index set, let $B_m=\{a_m(i):0\le i<N_m\}$. Distinctness gives the
bijection $O_m:C_{N_m}\to B_m$, $O_m(i)=a_m(i)$, and the recurrence gives
$T_mO_m=O_ms_{N_m}$. Transport the gauge by
$P_m(i,b)=(O_m(i),b)$:

$$
E_m=P_mG_{N_m}P_m^{-1},\qquad
F_m(q,b)=(T_mq,b\mathbin\oplus1),\qquad
H_m(q,b)=(T_mq,b).
$$

Then $E_m$ preserves the residue projection, is an involutive bijection,
and satisfies $E_mF_m=H_mE_m$. Its explicit closing equation is

$$
E_m(O_m(0),b\mathbin\oplus1)
  =(O_m(0),b\mathbin\oplus1)
  =H_m(E_m(O_m(N_m-1),b)).
$$

This applies in particular to the common 80-cycle and local 16-cycle,
and also to the even local 8-, 8-, and 20-cycles. The common-to-local
projection preserves $b$ and commutes with the flipped successors; since
each local period is even, it also commutes with these parity gauges.

## Readout of the full helix and scope

The existing
[GoldenScaleHelix.lean](../../D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.lean)
defines a state with level $\ell\in\mathbb N$, scale lift $t\in\mathbb R$,
and orientation $b\in\{0,1\}$. Its step is

$$
S(\ell,t,b)=(\ell+1,t+L,b\mathbin\oplus1),
\qquad L=2\log\varphi>0.
$$

For each selected modulus, the finite readout is

$$
f_m(\ell,t,b)=(a_m(\ell\bmod N_m),b).
$$

It is surjective: $(O_m(i),b)$ has preimage $(i,0,b)$. The recurrence,
including its closing row, proves $f_mS=F_mf_m$. Thus the selected finite
model is an actual equivariant readout of the full state, discarding the
scale lift and retaining only level modulo $N_m$ and orientation.

Induction gives $\operatorname{level}(S^n z)=\operatorname{level}(z)+n$.
For every state $z$ and every $n>0$, this level is strictly larger, so
$S^nz\ne z$. Finite phase closure never gives positive-period closure of
the full helix. The existing
[GoldenHelixParityReadout.lean](../../D5/S3/CompletionDynamics/GoldenMobius/GoldenHelixParityReadout.lean)
proves orientation return for all even step counts and orientation flip
for all odd counts; its even result supplies the 80- and 16-step instances.

Here a trivial cover means the explicit finite directed-cycle construction
above. No independently defined geometric Möbius or Klein cover, continuous
projection, or homeomorphism is supplied. An odd Boolean-flip cycle would
have nontrivial sheet monodromy, but it is not one of these selected even
orbits. These statements neither exclude other geometric realizations nor
establish a continuum or gravitational Ryu--Takayanagi identity.

## Sources

The mathematical suppliers are the three existing Lean files linked above
and the existing `weight_orbit` certificate. The variational argument uses
Mathlib's `isCompact_stdSimplex`, `exists_isMaxOn`,
`Finset.sum_mul_sq_le_sq_mul_sq`, and `Complex.re_le_norm`, under the
repository's pinned Mathlib dependency. Theory
[§§36.5--36.6](../../docs/develop/theory/ARITHMETIC_HOLOGRAPHIC_RT.md)
places these applications alongside the finite-sector discussion while
keeping its channel-optimization and physical assumptions explicit.
