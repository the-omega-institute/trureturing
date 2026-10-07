---
slug: barriga-2026-polygonal-fourier-couplings
bibkey: barriga2026dftbosonic
doi: null
url: https://arxiv.org/abs/2609.05644
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.result
---

# Positive polygonal couplings realize every discrete Fourier transform

## Problem

Barriga et al., *N-dimensional discrete Fourier transform via bosonic
Hamiltonian*, arXiv:2609.05644v1, §II.B, model an array of $N$ waveguides on a
regular polygon by a real circulant coupling matrix with zero diagonal and
$C_l=C_{N-l}$, evolve it by $U=e^{-i\mathcal C}$, and ask for diagonal phase
shifters with $\Phi^{\rm out}U\Phi^{\rm in}=F_N$, $F_N=(\omega^{jk})/\sqrt N$,
$\omega=e^{-2\pi i/N}$. They find analytic solutions for $N=4,5,6$ and numerical
ones up to $N=31$, and write:

> Whether the polygonal model can always yield solutions to obtain $F_N$ from
> Eq.~\eqref{eq:Coupling_polygon} or not is beyond our theoretical efforts.

The verbatim statements are in
[the literature note](../Library/QuantumChannels/barriga2026dftbosonic.md).
Issue [#13954](https://github.com/the-omega-institute/trureturing/issues/13954)
reads the question for every $N\ge1$, with exact equality (no column
relabelling) and, in addition, strictly positive couplings.

## Motivation

The polygonal model realizes $F_N$ in a single interaction region; an
affirmative answer for every $N$ removes the need for a numerical search over
couplings, which the paper reports up to $N=31$.

## Gap

Issue #13954 records the literature check before any Lean: one arXiv version;
arXiv, web and Zenodo searches found constructions of Fourier transforms by
adiabatic circulant Hamiltonians and results on uniform mixing of single rows,
but no construction of positive circulant couplings with
$\Phi^{\rm out}e^{-i\mathcal C}\Phi^{\rm in}=F_N$ for every $N$; the repository
had only the ten-mode edge refutation. `not-found-in-searched-scope`.

## Route

Put $f(r)=e^{i\pi r(r-N)/N}$; the circulant $B_{jl}=f(j-l)/\sqrt N$ satisfies
$DBD=F_N$ with $D=\mathrm{diag}(\overline{f(j)})$, so $B$ is unitary, and its
eigenvalues $\mu_k$ on the Fourier modes have modulus one and satisfy
$\mu_{-k}=\mu_k$. With $t_k=-\arg\mu_k\in[-\pi,\pi]$, mean $m$, and
$v_k=t_k-m-2\pi+2\pi N[k=0]$, the real symmetric circulant $\mathcal C$ with
spectrum $v$ has zero diagonal (its trace is $\sum_kv_k=0$), satisfies
$e^{-i\mathcal C}=e^{im}\,B$ (the shifts are multiples of $2\pi$), and has
off-diagonal entries $c_l=\kappa_l+2\pi$ with $|\kappa_l|\le\pi$, where $\kappa$
is the inverse transform of $t$; hence every coupling is at least $\pi$. The
phases are $\Phi^{\rm out}=D$ and $\Phi^{\rm in}=e^{-im}D$.

## Falsifier

The answer would not apply to a reading that fixes the couplings by a
prescribed distance law (for example exponential evanescent decay), which the
paper discusses separately for fabrication; the question as printed asks only
for circulant couplings.

## Evidence

The canonical source is `D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.lean`,
with public `fourier`, `IsUnimodularDiagonal`, `IsPolygonalCoupling`, `claim`
and `result : claim`. It imports the frozen
`D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow` (for `hamiltonianPropagator`,
$e^{-itH}$) and the frozen `D5/S3/Quantum/QuantumChannels/TomiyamaDiagonalKPositivity`
(for the Gram identity `fourierRows_gram` of the Fourier rows, made public at its
origin), and uses Mathlib's discrete Fourier transform `ZMod.dft` with its inverse
and `ZMod.dft_even_iff`. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide`, or
new axiom.
The module statement is `sha256:86195c1312f4468e797656b7564928ced7ecb53c5f01b7c277a0a9fe843b9677`,
the `result` statement `sha256:5a1df594bf419a7559be2a8c707b24fd243ec6bf36fd9403678ba6e637e0ec3c` and the
`claim` statement `sha256:9be0e0439bb0e37544677b1875f085b4a30c70179fa4ba06514143e3b090c8cf`. The Freeze
event is `sha256:778e6ec2571f17b0c7783975d355794f912dd7df39d175de2f5c261ad1544bb8`; its project-level
prerequisites are the frozen `ProjectionProbabilityFlow` and `TomiyamaDiagonalKPositivity` modules.

## Triage

Tier 1 question of a September 2026 paper, preregistered in issue #13954 before
any Lean. `theorem`; resolution `proved`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | bind-only | none | open-problem-resolution |

The private definitions and lemmas of the module (the chirp, the Fourier
transform on `ZMod N`, the circulant spectral kernel and its bounds) carry free
parameters and lie on the proof path of `result`. Utility is `none`. There is
no digestion atom.

### What the settlement shows

**Proved by `result`:** for every $N\ge1$ there are a real zero-diagonal
circulant coupling matrix with $c_l=c_{N-l}$ and strictly positive off-diagonal
entries and diagonal unimodular phases with
$\Phi^{\rm out}e^{-i\mathcal C}\Phi^{\rm in}=F_N$ exactly.

**Argued and checked numerically, not formalized.**

- *An explicit solution.* $\mathcal C_{jk}=\pi/(2N\sin^2(\pi(j-k)/N))$ has
  spectrum $a+\pi k(k-N)/N$, $a=\pi(N^2-1)/(6N)$, and gives
  $\Phi^{\rm out}e^{-i\mathcal C}\Phi^{\rm in}=F_N$ with $\Phi^{\rm out}=D$,
  $\Phi^{\rm in}=e^{ia}gD$, $g=N^{-1/2}\sum_rf(r)$ (residual $1.4\times10^{-14}$
  for $N\le40$, $64$, $97$ in #13954). At $N=4,5,6$ it gives the paper's
  analytic solutions; the main text's hexagon coupling $C_2=\pi/6$ is a
  misprint for the appendix value $\pi/9$.
- *Mechanism.* Positivity is free: the exponential only sees the spectrum
  modulo $2\pi$, and moving $2\pi$ between the zero mode and the others adds
  $2\pi$ to every coupling while keeping the diagonal zero. The proof applies
  this to the chirp circulant only. The same argument, applied to any circulant
  unitary whose spectrum is symmetric under $k\mapsto-k$ (principal arguments
  bounded by $\pi$, their mean subtracted, $2\pi$ removed from every mode and
  $2\pi N$ added to the zero mode), gives a zero-diagonal real symmetric
  circulant generator with off-diagonal entries at least $\pi$ that realizes the
  unitary up to a global phase; this extension is not formalized.
- *Fabrication.* The construction gives every pair of waveguides a coupling of
  at least $\pi$ in units of the interaction length. Whether such couplings are
  compatible with a prescribed distance law (the paper discusses exponential
  evanescent decay), a geometry and an interaction-length budget is outside the
  proved model.

**Open.** The minimal total coupling strength of a polygonal solution, and
which solutions are compatible with a prescribed distance law, are not settled
here.

**Effect on the paper.** The §II.B question has an affirmative answer for every
$N$; the numerical search of the polygonal model can be replaced by explicit
couplings.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof.
