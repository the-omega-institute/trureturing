---
slug: kumari-2017-cglmp-monogamy
bibkey: kumari2017sufficient
doi: 10.1103/PhysRevA.96.012128
url: https://arxiv.org/abs/1704.06516v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result
---

# Monogamy of the qutrit CGLMP inequality

## Problem

M. Kumari, S. Ghose and R. B. Mann, *Sufficient condition for nonexistence
of symmetric extension of qudits using Bell inequalities*, Phys. Rev. A 96,
012128 (2017), arXiv:1704.06516v2, Eq. (35):

> The CGLMP inequality for 2-qutrit states is monogamous, that is, if
> $\rho_{ABC}$ is any 3-qutrit state such that $\rho_{AB}$, $\rho_{BC}$ and
> $\rho_{AC}$ are its three 2-qutrit RDMs, at most one of these violates the
> CGLMP inequality.

Here $\mathcal B_{CGLMP}(\rho)$ is the maximum of the CGLMP expression
$\mathcal I_3$ (Eq. (CGLMP1)) over the angles of $A_k=U_{\text{FT}}U(\vec\phi_k)$
and $B_l=U^*_{\text{FT}}U(\vec\varphi_l)$, with
$U(\vec\phi)=\mathrm{diag}(e^{-i\phi(j)})$ and a computational-basis
measurement after each operator (Eq. (CGLMP2)). A state violates the
inequality when $\mathcal B_{CGLMP}>2$.

## Motivation

With the paper's Theorem 3, Eq. (35) was offered as a test for the absence of
symmetric extensions of two-qutrit states. The frozen declaration
`D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result` shows that Eq. (35)
is false.

## Gap

Issue #12528 classifies the conjecture as Tier 1 and records the checks made
before any Lean:

- arXiv:1704.06516 v2 is the latest version; the conjecture rests on
  numerical studies;
- the forward citations listed by Semantic Scholar (arXiv:2407.12933,
  arXiv:1904.02692) do not treat CGLMP monogamy; Lee–Son, Entropy 22, 1282
  (2020), arXiv:2010.09999, l. 581–582, still offer CGLMP monogamy as a
  possible explanation of non-violation;
- Augusiak et al., PRA 90, 052323 (2014), arXiv:1307.6390, Theorem 1, is a
  no-signalling relation with settings shared inside one tripartite
  distribution, so it does not decide Eq. (35), in which each reduced state is
  optimized separately;
- Cieśliński et al., arXiv:2312.04373, and Panda–Datta–Agrawal,
  arXiv:2601.02925, concern qubit and Dicke-state scenarios.

These are orchestrator-checked and seat-reported readings,
`not-found-in-searched-scope`; they do not establish exhaustive worldwide
novelty.

## Route

1. $v=|002\rangle+|011\rangle+2|020\rangle+|100\rangle+2|112\rangle-|121\rangle
   +2|210\rangle+2|222\rangle$, $\|v\|^2=20$, $\rho=vv^\dagger/20$.
2. For a reduced state of a pure state, each joint probability is
   $\frac1{20}\sum_c|((A\otimes B)v_{\cdot\cdot c})_{jk}|^2$. With angles in
   units of $\pi/6$, every amplitude is a sum of twelfth roots of unity
   divided by $3$.
3. On $\rho_{AB}$ take $\vec\phi_1=(0,2,7)$, $\vec\phi_2=(0,2,1)$,
   $\vec\varphi_1=(0,8,4)$, $\vec\varphi_2=(0,10,2)$; on $\rho_{AC}$ take
   $\vec\phi_1=(0,6,9)$, $\vec\phi_2=(0,6,3)$, $\vec\varphi_1=(0,10,2)$,
   $\vec\varphi_2=(0,0,6)$. In both cases the eight event probabilities, in
   the order of Eq. (CGLMP1), are $\frac{23}{60}+\frac{\sqrt3}5$,
   $\frac{23}{60}+\frac{\sqrt3}5$, $\frac12$, $\frac12$,
   $\frac{23}{60}-\frac{\sqrt3}5$, $\frac{23}{60}-\frac{\sqrt3}5$,
   $\frac14-\frac{\sqrt3}{15}$, $\frac14-\frac{\sqrt3}{15}$, so
   $\mathcal I_3=\frac12+\frac{14\sqrt3}{15}\approx2.1166$.

## Falsifier

The kernel-checked `result` is the negation of the following statement. For
every positive semidefinite $27\times27$ complex matrix $\rho$ of trace one,
indexed by $(a,b,c)$, and for all reals $b_{AB},b_{BC},b_{AC}$ that are the
maxima of $\mathcal I_3$ over the twelve angles on $\rho_{AB},\rho_{BC},
\rho_{AC}$ (`IsCglmpValue`, that is $\mathcal B_{CGLMP}$ of Eq. (CGLMP2)),
$b_{AB}>2$ implies $b_{BC}\le2$ and $b_{AC}\le2$. This is the displayed
implication of Eq. (35), which the conjecture contains.

The definitions are as follows:

- the reduced states are the frozen `partialTraceRight` and
  `partialTraceLeft` of `PartialTraceMutualInformation`, with the first-named
  party of each pair measured by $A_k$;
- $U_{\text{FT}}$ has entries $\omega^{jk}/\sqrt3$, with the frozen `omega`
  $=e^{2\pi i/3}$ of `FiniteLocalLatitudeGeometry`;
- outcome relations such as $B_1=A_2+1$ are read in `Fin 3`;
- `cglmpAt` is $\mathcal I_3$ at a given choice of the twelve angles, and
  `IsCglmpValue ρ b` says that $b$ is its greatest value over all angles.

Under the opposite sign convention for the Fourier transform, the probabilities
equal those at the negated angles, because $v$ is real. The refutation is
therefore convention independent. Since the paper's family is a subset of all
local projective measurements, the same values also refute the conjecture read
with unrestricted measurements.

## Evidence

Exact recomputation (SymPy, issue #12528): the eight event probabilities and
$\mathcal I_3$ for both reduced states. The literature seat recomputed them
independently. BFGS optimization over the paper's family gives
$\max\mathcal I_3(\rho_{AB})=\max\mathcal I_3(\rho_{AC})\approx2.1278$ and
$\max\mathcal I_3(\rho_{BC})\approx0$.

The canonical source is
`D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.lean`. It reuses the frozen `QutritThresholdSharing.normalization`
($(1/\sqrt3)^2=1/3$), made public for this purpose. Its public
declarations are `dft`, `phase`, `jointProb`, `eventProb`, `cglmpI3`,
`cglmpAt`, `IsCglmpValue`, `rhoAB`, `rhoBC`, `rhoAC`, `claim`, `stateVec`, `rho`, `ang` and
`result`.
The frozen module state has statement identity
`sha256:d702782b03881bd0fe04184abc5c12dd2f56c345b4e8b79d37b27c6366d172fd`. The
result declaration has statement identity
`sha256:9db90f908beb62a379f1fc501b8cd0b9b122407fc08b9390544e7b57547d5a96`. The Freeze event is
`sha256:712f68a6d1b05afac438770e5b0bfab63c5d138e8cc655c55cfa93d9aeeed287`; its
project-level frozen prerequisites are the Freeze events of the three reused
modules.
The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `native_decide`, or new axiom.

## Triage

Tier 1 conjecture of a 2017 journal article; resolution `Refuted` by
`D5/S3/Quantum/Entanglement/CglmpMonogamyRefutation.result`.
`proof_shape: bind-only` (the settlement of the named conjecture is the new
content; no escape witness); `admission_basis: open-problem-resolution`
(issue #12528). Utility kind `certified-instance`, basis `refutes` the
module's `claim`.

### What the settlement shows

- **Proved by `result`:** some three-qutrit state has
  $\mathcal B_{CGLMP}(\rho_{AB})>2$ and $\mathcal B_{CGLMP}(\rho_{AC})>2$, so
  the CGLMP inequality is not monogamous in the paper's sense.
- **Proved inside the proof of `result`:** for every two-qutrit matrix,
  $\mathcal I_3$ attains its maximum over the angles: it is continuous, it is
  unchanged when an angle moves by $2\pi$, and the box $[0,2\pi]^{24}$ is
  compact. For each reduced state of
  $vv^\dagger/20$, every joint probability is one twentieth of a sum of
  squared amplitudes. The two
  values $\mathcal I_3=\frac12+\frac{14\sqrt3}{15}$ hold at the stated
  angles, and $\rho$ is positive semidefinite with trace one.
- **Mechanism (orchestrator argument, not stated in Lean):**
  - Every basis state $|abc\rangle$ in the support of $v$ has
    $a-b-c\equiv1\pmod3$. For fixed $c$, the slice $v_{\cdot\cdot c}$ is
    supported on $b=a-c-1$, so for the events $B=A+s$ the squared amplitude
    does not depend on the outcome $j$ of $A$, and each event probability
    is a sum of three squared moduli of phase-twisted slices.
  - The two Bell tests use different settings on $A$. A no-signalling
    monogamy relation with shared settings (for example Augusiak et al.,
    Theorem 1) therefore does not apply.
- **Effect on the paper's other conclusions (checked by reading the v2
  source):**
  - The application to symmetric extensions (l. 407; abstract, l. 82;
    Discussion, l. 413) no longer follows from Eq. (35). It still holds: by Terhal–Doherty–Schwab,
    PRL 90, 157903 (2003), a state with a symmetric extension to two copies of
    $B$ admits a local model for every Bell test with two settings on $B$, so a
    CGLMP violation excludes such an extension. The paper cites that work
    (l. 96).
  - The statements that the numerical evidence supports monogamy of the
    2-qutrit CGLMP inequality (abstract, l. 82; introduction, l. 99;
    Discussion, l. 413) are contradicted.
  - The qubit results (Theorems 1 and 2) and the plotted families of
    Figs. 2–3, where only one reduced state violates, are unaffected.
- **Prior related examples (orchestrator-checked):**
  - Brunner–Vértesi, PRA 86, 042113 (2012), arXiv:1207.3986, l. 338–393,
    give three-qutrit states whose three marginals all violate CHSH with
    binary measurements on a qubit subspace.
  - Their state gives $\mathcal I_3=0$ for every angle in the paper's family
    (seat's computation). Optimizing $\mathcal I_3$ over arbitrary $3\times3$
    unitaries reaches only $2.0$ on each marginal (orchestrator's BFGS, 25
    restarts, $a=0.6469$; positive control $2.12779$ on this module's
    $\rho_{AB}$).
- **Open here:** whether all three reduced states of one three-qutrit state
  can violate the CGLMP inequality, and the largest pair
  $(\mathcal B_{CGLMP}(\rho_{AB}),\mathcal B_{CGLMP}(\rho_{AC}))$.

## ASSUMED-UNVERIFIED

The literature checks do not establish worldwide priority, and a complete
forward-citation graph was not obtained. The Lean kernel verifies the encoded
statement and its axiom closure. Its correspondence to the paper, including
the Fourier-transform convention and the reading of
$\mathcal B_{CGLMP}$ as the maximum over the angles, is checked by reading the source and the
definitions.
