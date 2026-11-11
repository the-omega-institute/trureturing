---
slug: mathex-2026-mo511715-cutoff-bound
bibkey: mathex2026mo511715
doi: null
url: https://mathoverflow.net/questions/511715/bound-of-series
triage: wall
motivation_gids:
  - D5/S3/Fourier/MO511715Source.result
---

# The complete MathOverflow 511715 cutoff-bound question

## Problem

[mathex](https://mathoverflow.net/users/138491/mathex), *Bound of series*,
MathOverflow 511715, revision 2, GUID
`A50CBAFD-9172-43CB-AD5D-4D59C3663AAC`, published 2026-05-26,
CC BY-SA 4.0. [Source note](../Library/Fourier/mathex2026mo511715.md).
The complete question follows; HTML presentation and display-math line breaks
are adapted. Quotation and adaptations retain
[CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).

> Consider $\phi_{\epsilon}: \mathbb{R}_+ \times \mathbb{Z}^5 \to \mathbb{R}_+,\epsilon>0$ defined by:
> $$
> \phi_{\epsilon}\left(q,n\right)=\sum_{\left(m_1,m_2\right) \in \left(\mathbb{Z}^5\right)^2} \mathcal{K}(q, n, m_1, m_2) \cdot \left|\zeta\left(\epsilon \left(m_1-m_2\right)\right)\right|^2\left|\zeta\left(\epsilon m_2\right)\right|^2
> $$
> where $\zeta$ is a compactly supported smooth function, $\zeta(0)=1,$ and
> $$
> \mathcal{K}(q, n, m_1, m_2) = |2\pi(n-m_1)|^2 \psi(n-m_1, m_1) \int_{0}^q \mathrm{e}^{-|2\pi(n-m_1)|^4(q-\alpha)} \left(\int_{\left[0,\alpha\right]^2} \mathrm{e}^{-\left|2\pi \left(m_1-m_2\right)\right|^4\left(q+\alpha-2v_1\right)-\left|2\pi m_2\right|^4 \left(q+\alpha-2v_2\right)}\,\mathrm{d}v_1\,\mathrm{d}v_2\right)  \mathrm{d}\alpha
> $$
>  The function $\psi:(\mathbb{Z}^5)^2\to [0,1]$ satisfies the support condition:
> $$
> \forall k_1,k_2 \in\mathbb{Z}^5,\psi(k_1, k_2) \neq 0 \implies \frac{9}{64} |k_1| \leq |k_2| \leq \frac{64}{9} |k_1|
> $$
>
> Let $\Delta_\epsilon(r, u) = \phi_{\epsilon}(r, u) - \phi_{\epsilon}(r, 0),r\geq 0,u \in\mathbb{Z}^5$.
>
>
> How to establish:
> $$
> \left| \Delta_{\epsilon_2}(r, u) - \Delta_{\epsilon_1}(r, u) \right| \leq C |\epsilon_2 - \epsilon_1|^\delta
> $$
> where $C$ and $\delta$ are independent of $r,u,\epsilon_1,\epsilon_2,\psi$

### Explicit conventional formalization

For each of $F=\mathbb R$ and $F=\mathbb C$, and every individually fixed
$\zeta\in C_c^\infty(\mathbb R^5;F)$ with $\zeta(0)=1$, ask whether there
exist finite real $C_\zeta\geq0$ and $\delta_\zeta>0$ such that for every
legal $\psi$, every real $r\geq0$, every $u\in\mathbb Z^5$, and every
$\epsilon_1,\epsilon_2>0$, the displayed estimate holds with exactly the
published $\phi,\mathcal K,\Delta$. Vector norms are Euclidean; scalar norms
are absolute value or complex modulus. Constants may depend on the fixed
cutoff, which is absent from the printed independence list. `claim` is the
conjunction of these two universal scalar assertions.

| Published feature | Retained interpretation |
| --- | --- |
| Five integer coordinates | `Lattice = Fin 5 → Int`, embedded in `EuclideanSpace Real (Fin 5)` |
| Every ordered pair | `phi` sums the full product lattice; no zero mode is removed |
| Frequency factors | `kernel` keeps the squared prefactor and all three separate fourth-power rates |
| Full inner square | `timeIntegral` uses product Lebesgue measure on the closed square; the proved Fubini bridge removes only null endpoints |
| Two cutoff squares | `cutoffWeight` keeps both scalar norm squares with the same cutoff and scale |
| One-way support implication | `LegalMask` has range $[0,1]$ and inclusive $9/64,64/9$ bounds, with no converse |
| Zero-output subtraction | `delta` uses the same cutoff and mask at both outputs |
| Uniformity | Constants precede mask, nonnegative time, every output and both positive scales; time zero and coincident scales remain included |

These conventions are interpretations, not recovered authorial intent. The
source does not define the vector norm, cutoff scalar typing, complete cutoff
prefix, types/signs of $C,\delta$, or $\mathbb R_+$. No cutoff symmetry,
radiality, monotonicity, common support radius, mask regularity, partition
identity, cancellation or extra cutoff/mask relation is imposed.

## Motivation

The question asks whether zero-output subtraction controls cutoff-scale
variation uniformly over an arbitrary mask satisfying only comparability.
Both scales must use the same joint realization. The retained construction
tests precisely that freedom; replacing it by a Littlewood–Paley partition
changes the question.

## Gap

The conventional assertion has the retained negation `result`. Independent
source review supports correspondence with the complete published question
under the disclosed Euclidean real/complex readings and documentary Tier-1
eligibility on the bounded literature record below. The source's omissions
remain explicit; the supported correspondence does not certify unspecified
authorial intent or a result for every possible norm. No unresolved material
source-semantic prerequisite is identified for this conventional question.

The Scribe attaches `OpenProblemResolutionClaim` with `ResolutionKind.Refuted`
and `ProblemSlugRef.Create("mathex-2026-mo511715-cutoff-bound")` to the existing
`D5/S3/Fourier/MO511715Source.result` Describe. It names this complete question,
with no additional resolution members. `proof_shape: bind-only` supplies no
escape witness; the host's `admission_basis: open-problem-resolution` uses
CLAUDE §3.2's external-question route. This prerequisite judgment and typed
annotation do not complete canonical admission. Selected canonical rendering,
first-freeze/current, utility admission, final independent review, required CI
and dev delivery remain outstanding, with the selected-consumer capability
gap owned by [#29078](https://github.com/the-omega-institute/trureturing/issues/29078).

### Preregistration and bounded literature status

The original [issue #29180](https://github.com/the-omega-institute/trureturing/issues/29180)
contains the complete source and a Tier-1 proposal: an author-posed 2026
analytic question with a proposed short route, rather than a finite-computation
frontier or documented core problem. The documented rationale and named
pre-probe checks support Tier-1 documentary eligibility under CLAUDE §3.6;
this is a bounded prerequisite judgment. Its
[pre-probe registration](https://github.com/the-omega-institute/trureturing/issues/29180#issuecomment-6790963738)
identifies the unchanged complete conventional event, SHA-256
`410a367b8a743883dfc12bdc9a4269e77d89dadd5646e3c22023747c16d44c8d`.
The original deadline `2026-11-12T18:00:00Z`, original 21600-host-second
account, predictions and prior settlements are unchanged. This dossier does
not register a narrower replacement event or settle that account.

The supplied primary-source snapshot checked 2026-11-11 has zero answers,
two revisions and one comment requesting motivation. This establishes
unanswered status at that snapshot, not absence of a settlement elsewhere.
The preregistration attributes bounded repository/public-private and pinned
Mathlib searches, a reading of atlas-lean
`0d5f68a243481fc67fd486d56a003c271b933ba1` in its different summability setting,
and Gubinelli–Imkeller–Perkowski, *Paracontrolled distributions and singular
PDEs*, arXiv:1210.2684v4, at its Bony/Littlewood–Paley definitions. None supplies
the exact source estimate or refutation in those recorded readings. That
framework's dyadic partition structure is absent from the source assumptions.

A bounded arXiv metadata check at 2026-11-11T18:53:45Z for `all:"511715"`
returned totalResults 0. A title query `ti:"Bound of series"` at
2026-11-11T18:54:19Z returned 12 total results, only the first five returned;
that query was not an exhaustive literature screen. Neither establishes
worldwide openness, priority, or absence of an equivalent settlement without
the source identifier. Documentary eligibility rests on the named bounded
record, not a claim of exhaustive absence. An applicable prior settlement
would defeat this route; none is identified in that record.

## Route

Let $e$ be the first lattice unit. Use the single mask that is one exactly
when $k+l=e$ and both published support comparisons hold, and zero otherwise.
At source arguments $k=n-m_1,l=m_1$, its sum is $n$. Every output except $e$
therefore vanishes, including the subtracted output zero.

Reindex $(m_1,m_2)=(a+b,b)$. For $N\geq1$, put all five coordinates of
$a,b$ in $[N,2N)\cap\mathbb Z$. This pair block has $N^{10}$ points. On it
the source mask is one and the exact kernel is at least $\kappa/N^{10}$,
$\kappa>0$. The genuine subregion is $\alpha\in[1-h,1]$ and
$v_1,v_2\in[\alpha-h,\alpha]$, with $h=\eta/N^4$,
$\eta=1/(20000(2\pi)^4)$ and decay budget $11/16$.

For each fixed normalized cutoff continuous at zero, choose $0<\rho\leq1$
so its modulus is at least $1/2$ on the closed $\rho$ ball. At
$\epsilon_J=\rho/(5\,2^J)$, both squared cutoff factors have product at least
$1/16$ simultaneously on all dyadic blocks $j\leq J$. Disjointness and
nonnegative omitted terms give $\phi_{\epsilon_J}(1,e)\geq c(J+1)$,
$c=\kappa/16>0$. Compact support makes each actual positive-scale sum finite;
no nonsummable `tsum` convention supplies the growth.

Keep reference scale $2$ and $M=\phi_2(1,e)$. For all finite real $C,\delta$,
the distinct positive scales satisfy $1\leq|2-\epsilon_J|\leq2$, hence
$C|2-\epsilon_J|^\delta\leq\max(C,0)\max(1,2^\delta)$.
Choose $J$ with $c(J+1)>M+\max(C,0)\max(1,2^\delta)$ to obtain strict failure
of the actual absolute delta estimate. The same cutoff and mask are used
throughout. The consumed `source_estimate_failure` establishes this stronger
obstruction for either scalar reading; `uniform_estimate_fails` consumes it,
and `result` uses a real smooth bump to negate the conjunction `claim`.

## Falsifier

A source-resolution claim is invalid if it silently selects a norm, scalar
type or extra mask relation as authorial intent, weakens registered quantifiers,
changes the kernel or square, or uses a cutoff sum without actual finite
support. A conventional uniform bound would contradict the retained strict
failure inequality. A bound for a more structured mask class would address a
successor question rather than reverse this arbitrary-mask obstruction.

## Evidence

The mathematical sources are `D5/S3/Fourier/MO511715Source.lean` and its
existing `Reg/D5/S3/Fourier/MO511715Source.lean` mirror. `claim : Prop` and
`result : Not claim` form the literal designated refutation interface. The
retained scoped compiled evidence supplied with this unit covers 41 modules,
1760 declarations, the standard three axioms and four `declared_validated`
Reg bindings. This content preparation preserves those source/evidence bytes;
it does not claim a new Lean/report run.

All 39 authored lemmas/theorems have `proof_shape: bind-only` under the
accepted full-inlining source/form judgment. Each nonterminal helper has a
live consumer in the result chain; `indexEquiv` is a consumed proof-bearing
definition. These consumers organize the proof and supply no escape witness.
The terminal `result` uses the external-open-problem basis with the supported
source/documentary prerequisites and its typed `Refuted` annotation; compiled
proofs and Reg bindings do not themselves grant canonical admission.

Canonical selected emission, FileMap and ledger/freeze consumption require
selection before discovery, the unresolved owner capability in
[#29078](https://github.com/the-omega-institute/trureturing/issues/29078).
No generated mirror, freeze, full rendered correspondence, final independent
review or required-CI admission is asserted here.

## Triage

1. **Established in the retained conventional proof:** each dyadic block
   contributes fixed positive mass. The arbitrary legal mask isolates a
   nonzero output and makes the zero-output subtraction vanish. The stated
   support ratios alone do not supply the hoped-for cancellation.
2. **Established in the retained stronger helper:** every fixed normalized
   compact cutoff continuous at zero, real or complex, fails at positive time
   and distinct positive scales for all finite real constants and all fixed
   real exponents. Smoothness is stronger than the hypotheses needed here.
   Both fixed-cutoff and all-cutoff-uniform constant readings are covered,
   with the disclosed Euclidean norm retained.
3. **Surviving scope:** finite support holds at every positive scale; the
   nonnegative kernel and exact subregion estimates remain valid. They do not
   supply the rejected estimate. The post identifies no motivating paper or
   downstream theorem, so no external theorem is declared invalidated.
4. **Open successor candidate:** for an explicitly specified Littlewood–Paley
   partition or other mask compatibility/cancellation condition, determine
   whether a cutoff-scale bound holds and with which uniformities. Neither
   sufficiency of that structure nor failure for every structured mask is
   proved here. This candidate needs its own hypotheses, literature check
   and preregistration.
5. **Supported prerequisites and unresolved admission boundary:** source
   correspondence for the conventional Euclidean real/complex question and
   bounded documentary eligibility are independently supported. The published
   norm/scalar/prefix/$\mathbb R_+$ omissions remain disclosed; unspecified
   intent and worldwide openness are not certified. Canonical admission,
   final review and publication remain outstanding.

## ASSUMED-UNVERIFIED

Original authorial intent and absence of a prior settlement beyond the bounded
readings are unverified and are not premises supplied by the prerequisite
approval. The typed `Refuted` annotation concerns the complete question under
its explicit conventional readings. The wall triage records outstanding
canonical/final admission, not an undecided source/documentary prerequisite
or a failure of the retained conventional proof. Rendered/current/freeze
checks and publication remain pending the compatible owner capability and
later review.
