---
slug: kania-kakol-2026-problem-8-2-ch-talagrand
bibkey: kania2026talagrand
doi: 10.48550/arXiv.2607.06808
url: https://arxiv.org/abs/2607.06808v2
triage: theorem
motivation_gids:
  - D5/S3/Topology/InverseLimit/TalagrandTopologicalConsequences.actual_CH_Talagrand_scheme_and_endpoints
---

# Kania–Kąkol Problem 8.2: the full Talagrand construction under CH

## Problem

Kania and Kąkol, *Talagrand compacta, 2DCP, and pointwise quotients*,
arXiv:2607.06808v2, revised 10 July 2026, PDF p.19, ask:

> Problem 8.2. Can the prediction principle in Theorem A be weakened from ♢(S) to CH?

### Exact statement correspondence

There is one mathematical input, `hCH : Cardinal.continuum = ℵ₁`, and one
literal carrier `K := (SignedOrdinalRealization.finalPrefix hCH).LimitSpace`.
The public theorem is
`TalagrandTopologicalConsequences.actual_CH_Talagrand_scheme_and_endpoints`.
All clauses below occur together in its statement and are consumed by its
proof.

| Original requirement | Lean statement and derivation |
| --- | --- |
| Actual closed nonempty coordinate compacta and onto restrictions | The first conjunction retains all `H.carrier`, `H.map` and `H.projection` readbacks and surjectivity. |
| Initial omega cube | Every carrier through omega is the whole cube; the final restriction onto the omega cube is onto. |
| Closed-cover successor split for omega ≤ alpha < omega-one | Closed Y,Z cover `H.Space a`; `H.carrier (nextStage a)` is literally the range of Boolean insertion from `splitCarrier Y Z`. |
| Proper limit and final thread equations | Each proper limit above omega is exactly its proper-slice limit carrier; the final carrier is exactly all compatible restrictions. |
| Countable-stage and final topology | Every proper stage is compact Hausdorff, zero-dimensional and metrizable. K is nonempty compact Hausdorff and zero-dimensional, with its actual limiting cone. |
| Whole original enumerations | U, B and nu are onto; B and V are the original whole births. Every signed measure has regular Jordan parts, variation mass one, support concentration and positive mass at least one half. |
| Original A–F and every signed selection | Every proper cutoff has the original `P.Laws D`, including every-choice signed F, with every original-label measure readback. No final-stage F is postulated. |
| G and cofinal bookkeeping | One eta gives the same support launches and signed source measures. The fixed G clopen is the new-coordinate-true cylinder. Its fixed increasing column sequence works for arbitrary complete signed norm-one lifts, with infinitely many evaluations at least one sixth and infinitely many exact zeros. Every row/label pair is treated cofinally above any base. |
| Theorem A closed-copy prohibition | For every closed A and continuous f : A → K with disjoint range, the range is finite. Every two disjoint homeomorphic subspaces, one closed, are consequently finite. This is stronger than excluding disjoint nonmetrizable closed copies. |
| No 2DCP | No sequence of nonempty compact T(n) has two disjoint copies of T(n+1) in T(n). No nesting or infinitude premise is added. |
| Grothendieck | Every sequence in the full real continuous dual converging pointwise to FInf converges under every continuous real bidual test. There is no input norm bound. |
| Entire signed dual unit ball | Every continuous map from all of `StoneCech ℕ` into `WeakDual ℝ C(K,ℝ)` bounded by one is noninjective, including principal and free points. |
| Point-space consequences | Every convergent sequence is eventually its actual limit; no continuous StoneCech injection exists; K is infinite, not first countable and not metrizable. |

## Motivation

Theorem A (p.2) assumes diamond on a stationary co-stationary subset of
omega-one. Its compactum realizes Talagrand's scheme and has no two disjoint
nonmetrizable closed homeomorphic subspaces; it consequently has no 2DCP.
Theorem B on the same page gives the Grothendieck property of C(T) and excludes
beta-omega from its entire weak-star dual unit ball. The same T has no
nontrivial convergent point sequence and no copy of beta-omega.

The combined target is preregistered as the external tier-2 problem
[#22300](https://github.com/the-omega-institute/trureturing/issues/22300),
before the first combined-theorem compilation. Earlier independently compiled
construction suppliers are reused; their earlier probes are not retroactively
preregistered by that issue.

## Gap

The target is the complete same-space Talagrand construction from CH alone, including all original signed A–G laws, literal successor/limit geometry, the arbitrary closed-copy prohibition and the entire signed dual-ball endpoints. Existing endpoint examples do not by themselves supply this conjunction or identify the original signed scheme.

## Route

The well-founded coherent ordinal history constructs all actual stages from
CH. Whole-birth transports preserve every label. The actual reindexing uses a
single eta for exhaustive support launches and signed G, retaining original
proper laws. The geometric readbacks identify the selected successor Result
with literal Boolean insertion and the proper limits with their actual
thread carriers.

The finite-image proof captures the whole Dirac sequence of a hypothetical
infinite disjoint image, obtains the same delayed event and its two permanent
pools, then reflects the final clopen preimage to a later proper stage.
Original every-choice F contradicts opposite indicator values on the two
infinite surviving pools. This yields the closed-copy and 2DCP conclusions.

The signed endpoint proof captures an arbitrary normalized regular signed
sequence in the original whole-birth enumeration. Actual G gives full
clopen oscillation on K. Original F and proper-stage factorization give the
signed ultrafilter collision on the same actual RawHistory. The analytic
reduction excludes the entire signed dual unit ball; the signed Grothendieck
criterion supplies arbitrary bidual convergence and eventual equality of
point sequences. Evaluation embeds K into that ball; its omega-cube quotient
ensures infinitude.

## Falsifier

The claimed correspondence fails if any required clause needs an assumption beyond CH, applies to a different compactum, restricts the original signed selections, or leaves a successor/limit identification unproved. A continuous injection of StoneCech Nat into the entire stated signed dual unit ball, or an infinite disjoint continuous image with closed domain in the constructed K, would contradict the respective proved endpoint.

## Evidence

The explicit successor/limit geometry has passed a targeted Lean 4.35 build.
The signed endpoint supplier has passed its real build and scoped report with
only `propext`, `Classical.choice` and `Quot.sound`. The complete combined theorem and both owning Reg source reconstructions
have also passed the targeted Lean 4.35 build. These checks alone are not
complete delivery acceptance.
The verified scoped report contains 66 modules and 2,138 declarations; every
axiom closure lies within the same standard three-axiom set. Canonical Scribe
emission passed. Three independent fixed-source reviews approved. Required CI and merge
evidence are tracked in [PR #22319](https://github.com/the-omega-institute/trureturing/pull/22319),
separately from the kernel evidence above. The oracle seat used its documented
Codex fallback after login expiry; no model-family diversity is claimed.

The source-faithful four-slot information registration is unfinished under
[#21750](https://github.com/the-omega-institute/trureturing/issues/21750).
The owning Reg mirrors reconstruct the full source telescopes; they do not
provide the enrolled whole-source readout, selection bridge and whole-family
variation/sensitivity evidence and do not claim `declared_validated`.

### Bounded literature comparison

The primary v2 paper retains the question. Fresh public arXiv retrievals on
26 October 2026 at 12:01 UTC found only v1 and v2 of this paper; the exact
Talagrand/2DCP search returned the original paper. The bounded 2DCP query in
math.GN/math.FA returned this paper and arXiv:2606.27568v1. No later solution
was identified in those results. The preregistration records these exact
queries and their HTTP-200 readings.

Known CH Talagrand analytic endpoints, CH Efimov/simple-extension examples,
diamond rigid Efimov examples and generic ZFC no2DCP compacta must be
distinguished from the full same-space signed-scheme target. The authors' later primary article arXiv:0811.0577v1, pp.3–4, distinguishes
ZFC weak-multiplier examples from the stronger CH weak-multiplication
examples and notes that the original disconnected example is not perfect.
Its p.10 invokes Koszmider 2004 Theorem 2.4 for Grothendieck; Proposition 4.5
concerns disjoint clopen pieces. These verified statements do not by
themselves establish the arbitrary closed-copy prohibition, entire signed
dual-ball exclusion and original Talagrand A–G identification together.
The 2004 full text remains unavailable, so no exhaustive exclusion of a
connection is asserted.

## Triage

`triage: theorem`. The final combination has `proof_shape: bind-only`: its construction and
analytic content lie in the consumed suppliers and geometry. Its admission
basis is `open-problem-resolution (#22300; Proved)`. The Scribe has one
`OpenProblemResolutionClaim(Proved)` for this dossier. No unrelated public
companion theorem is introduced.

## ASSUMED-UNVERIFIED

Literature completeness, absence of every differently worded or non-arXiv
prior solution, worldwide uniqueness and official acceptance remain
`ASSUMED-UNVERIFIED`. This dossier does not settle Problem 8.1, the full
metrizable quotient problem for Cp(K), or statements about every Talagrand
realization.
