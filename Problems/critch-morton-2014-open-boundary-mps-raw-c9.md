---
slug: critch-morton-2014-open-boundary-mps-raw-c9
bibkey: critchmorton2014mps
doi: 10.3842/SIGMA.2014.095
url: https://arxiv.org/abs/1210.2812v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result
---

# Critch--Morton C9: raw actual-image settlement candidate

## Problem

A. Critch and J. Morton, *Algebraic geometry of matrix product states*, SIGMA 10 (2014), 095, arXiv:1210.2812v4, Conjecture 9:

> A generic N-qubit (D=d=2) translation invariant matrix product state Ψ with open boundary conditions is determined up to phase by a reduced density operator which traces out all but a chain of three adjacent states, but no fewer.

The displayed map is the raw partial trace
$Q_k(\psi)_{u,v}=\sum_b\psi_{ub}\overline{\psi_{vb}}$ on the actual affine image. Issue [#30422](https://github.com/the-omega-institute/trureturing/issues/30422) preregisters the exact raw $N\ge4$ prefix recovery and minimality target before proof probes. The formal result strengthens it to all $N=3+m\ge3$ and every adjacent placement. The paper does not specify the particular real-principal genericity convention used here, nor explicitly state $N\ge3$ in C9. These are explicit parts of the formal strengthening.

## Motivation

This is an identifiability limit for one finite local quantum observation in the literal translation-invariant binary bond-two open-boundary MPS model. It connects recovery from a three-site observation to hidden fibers of each smaller observation while retaining arbitrary actual competitors. Static identifiability supplies no dynamics, physical clock, energy or thermodynamic law.

## Gap

The bounded literature check as of 2026-11-15 found no accessible exact C9 proof, refutation or no-fewer settlement in its searched scope. This is `not-found-in-searched-scope`, not a global novelty, world-first or unique certificate. The preregistration records the original assertion, the full raw target, tier 1--2 assessment and bounded readout.

The repository suppliers establish prefix recovery, prefix-two ambiguity in every neighborhood, interior recovery and interior-two pointwise ambiguity. The result composes those exact suppliers with reversal, full-coordinate polynomial substitution and partial traces. Their original attributions, including the Ma--Zhang C8 source and CC BY 4.0 license, remain unchanged.

## Route

For each $m$, let $S_m=\mathrm{openBoundaryMPS}(3+m)$ be the ENTIRE literal actual image. Select the prefix recovery polynomial $O$, the prefix-two fiber polynomial $B$, the interior recovery polynomial $T$ when $m\ge2$ and $T=1$ otherwise, and the interior-two ambiguity polynomial $A$ when $m\ge1$ and $A=1$ otherwise. Their relative loci are open and dense.

Actual-state reversal $H\psi(w)=\psi(w\circ\mathrm{Fin.rev})$ is an involutive homeomorphism: transpose each original matrix by ordinary transpose and swap the original boundary vectors. The finite intersection
$L_O\cap L_B\cap L_T\cap L_A\cap H^{-1}L_O\cap H^{-1}L_B$
is open and dense and has a common actual witness. No irreducibility, Baire assumption or closure point substitutes for this witness.

Let `lift` substitute the complete real and imaginary raw-prefix $Q_3$ quadratic coordinate polynomials. With $L=OBTA$, $R=OB$ and $\tau$ reversing the real and imaginary amplitude indices, set
$P=\mathrm{lift}(L)\,\mathrm{rename}_{\tau}(\mathrm{lift}(R))$.
Evaluation at every amplitude identifies the full-state principal locus of $P$ with the intersection above. The common actual witness gives $P\ne0$. Public phase suppliers make its membership invariant under $U(1)$; no positive-scaling invariance is assumed.

Every target in this locus is explicitly nonzero. Boundary Q2 witnesses come from the original every-neighborhood clause applied to the open nonzero neighborhood of that target. Right-boundary witnesses reverse back; interior witnesses are supplied unchanged. Exact adjacent-pair partial traces preserve the SAME actual nonzero nonphase competitor at each requested site. Complete exterior sums and every length equality are retained.

At $m=0$ all required Q3/Q2 cases are boundary cases. At $m=1$ there is no strict interior triple and exactly one interior pair. Strict interior triple and pair hypotheses force $m\ge2$ and $m\ge1$, respectively, before supplier use.

## Falsifier

The candidate would fail source fidelity if it used a normalized observation, generic competitors, only a Zariski closure, a jointly known collection of windows, a missing exterior sum, or nonphase alone to infer nonzero. None is a premise of `result`. Each smaller window has its own possibly different actual nonzero nonphase competitor; no common competitor for every window is asserted.

A normalized-state theorem requires a separate slice-genericity or radial-invariance argument. Unit-phase saturation does not supply it. Normalized-density phase recovery on an entire nonzero affine cone cannot exclude positive rescaling.

## Evidence

The mathematical source is `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.lean`, with one public theorem `result`. Its telescope is the all-natural-$m$, full-amplitude polynomial, entire-actual-image, all-placement raw statement described above. The matching Scribe contains the exact candidate claim and applicability limits. The mirrored Reg source attempts the whole source family with an enrolled dependent-family readout; source-selection evidence is absent under #30422 and no `declared_validated` status is claimed.

## Triage

Candidate `admission_basis: open-problem-resolution` under CLAUDE 3.2; conservative `proof_shape: bind-only`. Each private auxiliary is used on the live proof path of `result`; no separate helper package is delivered. The same-unit `OpenProblemResolutionClaim(Proved)` refers only to this exact raw settlement candidate. Independent caller fidelity review, required checks, freezing, publication, literature priority and official acceptance remain separate. Global C9 status is OPEN and solved-open-problem KPI remains 0 until caller verification.
