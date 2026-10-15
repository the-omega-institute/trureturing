---
slug: hanaoka-konno-2021-riesz-walk-self-similarity
bibkey: hanaoka2021rieszwalk
doi: 10.26421/QIC21.5-6-5
url: https://arxiv.org/abs/2010.04518
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.result
---

# Hanaoka–Konno Conjecture 4.2: self-similarity of the Riesz walk

## Problem

R. Hanaoka and N. Konno, “Return probability and self-similarity of the Riesz
walk,” Quantum Information and Computation 21 (2021), 409–422,
arXiv:2010.04518v3, DOI 10.26421/QIC21.5-6-5, state Conjecture 4.2:

> Let Z_> = {1,2,3,...}. Put T_0(n)={0} and T_k(n)=((k-1)/n,k/n]
> for 1 <= k <= n. For the Riesz walk with initial state
> Psi_0=[1,0]^T delta_0, P(X_2t/(2t) in T_k(t)) =
> P(X_8t/(8t) in T_k(t)) for every t in Z_>.

Issue #15758 preregistered the exact natural-number reading. The delivered
declaration is D5/S3/Quantum/Walks/RieszWalkSelfSimilarity.result : claim,
and its module state has statement identity
sha256:4b9935aefe3ec7033ed45b54d5dec573a17d5471a67ae35f412951ac228f6269.

### Statement echo

The source's t >= 1 is the binder t : Nat with 1 <= t; its 0 <= k <= t
is k : Nat with k <= t. The source's normalized probability is
prob (2*t) (Tset t k) and prob (8*t) (Tset t k); Tset gives the singleton at
k=0 and the left-open, right-closed rational interval for 1 <= k <= t. The
conclusion is the equality in claim; result proves exactly that proposition.

## Motivation

The conjecture connects the return law of a quantum walk with the
fourth-power self-similarity of the Riesz measure. The settlement identifies
the stronger cumulative identity at both scales and supplies a kernel-checked
bridge from the CMV representation to the block probabilities.

## Gap

The paper reports numerical support but no proof for Conjecture 4.2. The
preregistered route was the CMV spectral representation, Geronimus
identification, and the Riesz decimation identity. The proof uses the five
supporting modules frozen in this delivery under escape-witness; the settling
module is admitted as open-problem-resolution (#15758; Proved).

The paper's division by z is represented using the pinned
RecursiveBoundaryRowSeries.tail owner because PowerSeries.X^{-1}=0. The
equations corresponding to the Schur definition and Schur step are proved by
schur0_spec and schurStep_spec; this is the convention repair recorded in
issue #15758.

Every newly authored public theorem, including the public Szego rho-square
owner `D5/S3/Weil/Szego/CanonicalTransfer.szego_rho_sq`
(declaration statement_id: `sha256:0c7e849be0a2d5c52755ddb652d3be5c71965267f3356f6b4e69cbbeb8141df6`), remains under the unfinished
escape audit [issue #15854](https://github.com/the-omega-institute/trureturing/issues/15854).
No declaration is reported as declared_validated.

## Route

The Riesz moments stabilize in finite products, giving a positive form on
Laurent polynomials. Gram–Schmidt produces the orthonormal Laurent basis and
the finite CMV projection representation. Geronimus identifies the Schur
parameters with the Verblunsky coefficients. The map z -> z^4 is an isometry
after the Riesz density change, and the parity-weighted projection identity
equates the two finite projection norms. The cumulative equality
F_(2t)(2x)=F_(8t)(8x) then yields the interval identities by subtraction, with
the singleton origin block handled separately.

## Falsifier

A natural t >= 1 and 0 <= k <= t violating the displayed probability equality
would contradict result. At the proof level, failure of the finite projection
identity, the Geronimus identification, or the fourth-power Riesz density
relation would break the route.

## Evidence

The kernel-checked result is
D5.S3.Quantum.Walks.RieszWalkSelfSimilarity.result; its proof uses only the
standard axiom closure propext, Classical.choice, and Quot.sound. The five
supporting modules and their Scribe projections are frozen in the module-state
ledger. The experiment entry
https://github.com/the-omega-institute/trureturing-experiments/tree/cc6202d7269efbf26843227e123f34f3652dc67c/docs/reports/hanaoka-konno-2021-riesz-walk-self-similarity
was run as python3 check.py, exit 0, and has SHA-256
54eca0560bd45517bdd5010d7540b01b5bf8360a23024434e7fff3b9406cb007.
It checks the literal Section 2 construction for t=1,...,32 (times up to 256),
with worst discrepancy $4.28 \times 10^{-61}$, and the factor-two control fails in 104
instances. These are finite computed readings.

## Triage

Tier-1 external conjecture, preregistered in #15758; resolution proved for
every natural t >= 1 and 0 <= k <= t. The admission basis is
open-problem-resolution (#15758; Proved); utility is none.

### What the settlement shows

- Kernel-checked: result proves the stated block equality. The decisive
  mechanism is CMV.Representation.SpectralReduction.cumulative_projection,
  CMV.Geronimus.schur_equals_gram, Riesz.Moments.Forms.tau_density,
  Riesz.Moments.Forms.riesz_residue_orthogonality,
  Riesz.Decimation.Parity.parity_weighted_projection, and
  RieszWalkSelfSimilarity.Scaling.cumulative_scale_four. These identify
  cumulative probabilities with Laurent-window projection norms, express
  fourth-power decimation with density $1 + \operatorname{Re} w$ and invariance
  under $z \mapsto iz$, and give $F_{2t}(2x) = F_{8t}(8x)$.
- Kernel-checked: the supporting content witnesses are
  Riesz.Moments.product_independent, CMV.SzegoRecurrence.OPUCRecurrence.monic_szego,
  CMV.Geronimus.schur_equals_gram, CMV.Representation.WalkCore.mu_outside, and
  Riesz.Decimation.Parity.parity_weighted_projection; their conclusions are
  consumed along result's proof path.
- Computed: the cited experiment checks 32 positive times and the factor-two
  control; it does not extend the kernel theorem or settle an asymptotic limit.
- Open: Conjectures 4.1 and 4.3, the limit theorem, and general m >= 3
  Riesz-type walks remain outside this result. The source's later questions
  relying on those statements are unchanged.

## ASSUMED-UNVERIFIED

The bounded literature screen recorded in #15758 did not find a later proof;
worldwide novelty, priority, and the absence of an independent proof outside
that screen remain unverified. The experiment is finite evidence and does not
replace the Lean proof.
