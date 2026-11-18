---
slug: critch-morton-2014-open-boundary-mps-raw-c9
bibkey: critchmorton2014mps
doi: 10.3842/SIGMA.2014.095
url: https://arxiv.org/abs/1210.2812v4
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result
  - D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result
---

# Critch--Morton C9: raw and physical-mass-one settlement candidate

## Problem

A. Critch and J. Morton, *Algebraic geometry of matrix product states*, SIGMA 10 (2014), 095, arXiv:1210.2812v4, Conjecture 9:

> A generic N-qubit (D=d=2) translation invariant matrix product state Ψ with open boundary conditions is determined up to phase by a reduced density operator which traces out all but a chain of three adjacent states, but no fewer.

The displayed map is the raw partial trace
$Q_k(\psi)_{u,v}=\sum_b\psi_{ub}\overline{\psi_{vb}}$ on the actual affine image. Issue [#30422](https://github.com/the-omega-institute/trureturing/issues/30422) preregisters the exact raw $N\ge4$ prefix recovery and minimality target before proof probes. The formal result strengthens it to all $N=3+m\ge3$ and every adjacent placement. The paper does not specify the particular real-principal genericity convention used here, nor explicitly state $N\ge3$ in C9. These are explicit parts of the formal strengthening.

The same preregistration includes the physical reading with both states normalized. `OpenBoundaryMPSNormalizedC9.result` supplies that slice as an additional member of the single existing claim; it does not change the raw theorem's scope or remove the source's normalization and genericity ambiguities. These are two members addressing one external C9 problem, with no independent priority or second solved-problem credit.

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

For the physical member, for every natural $m$ including zero, put $N=3+m$, $M(\psi)=\sum_{w\in\{0,1\}^N}|\psi_w|^2$ and $\mathrm{MassOne}(N)=\{\psi\in S_m:M(\psi)=1\}$ with its induced topology. Let $P$ be the raw result's polynomial and $P_d$ its homogeneous components. The normalized result supplies nonzero literal real polynomials $P,H$, with
$$
H=\sum_{d=0}^{\deg P}P_d^2,\qquad
G=\{\psi\in\mathrm{MassOne}(N):H(\operatorname{Re}\psi,\operatorname{Im}\psi)\ne0\}.
$$
This single $G$ is nonempty, relatively open, dense and $U(1)$-saturated. For every $\psi\in G$, every $p,q\in\mathbb N$ with $p+q=m$, every exact equality $h:(p+3)+q=N$, and every actual mass-one competitor $\phi$, equality of `rawInterior p 3 q` after `castState h` is equivalent to $\phi=z\psi$ for some $|z|=1$. For every $p+q=m+1$ and every $h:(p+2)+q=N$, there is an actual mass-one nonphase competitor with the same individual two-site observation. Separately, for every $p+q=m+2$ and every $h:(p+1)+q=N$, such a competitor exists for the one-site observation. Each existential follows the window choice; no common competitor is asserted. All zero-length exteriors and all length casts remain in scope.

Finite homogeneous reconstruction gives $F_x(T)=\sum_d P_d(x)T^d=P(Tx)$. Coefficient extraction, the real sum-of-squares criterion and the univariate infinite-root theorem give $H(x)\ne0$ iff $P(tx)\ne0$ for some $t>0$, including zero polynomials, constants, empty variable carriers and $x=0$. Taking $t=1$ embeds the old dense locus in its positive-ray saturation. Positive-ray invariance and the continuous retraction $\psi\mapsto\psi/\sqrt{M(\psi)}$ from the open positive-mass actual subtype prove density on MassOne by pulling back nonempty open sets. Raw phase saturation and commuting scalar actions give $U(1)$ saturation. This supplies the slice-density argument missing from the raw result alone.

For every window, including boundaries, complete exterior sums give $\operatorname{tr}(Q_k(\psi))=M(\psi)$ and $Q_k(t\psi)=t^2Q_k(\psi)$ for real $t$. Length casts preserve mass and scalar action. Given $\psi\in G$, choose $t>0$ reaching the raw $P$ locus, apply the raw result at $t\psi$, and scale that same ambiguity witness back by $t^{-1}$. Trace equality ensures mass one and scalar cancellation preserves its observation and nonphase property. Recovery similarly scales each arbitrary mass-one competitor by $t$ and cancels it. The normalized Scribe and Library appendix give the full correspondence and proof exposition.

## Falsifier

The candidate would fail source fidelity if it used a normalized observation, generic competitors, only a Zariski closure, a jointly known collection of windows, a missing exterior sum, or nonphase alone to infer nonzero. None is a premise of `result`. Each smaller window has its own possibly different actual nonzero nonphase competitor; no common competitor for every window is asserted.

A normalized-state theorem requires a separate slice-genericity or radial-invariance argument. Unit-phase saturation does not supply it; the additional normalized member supplies it by the radial SOS and retraction argument above. Normalized-density phase recovery on an entire nonzero affine cone still cannot exclude positive rescaling; both states in the normalized theorem are explicitly mass one.

## Evidence

The mathematical source is `D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.lean`, with one public theorem `result`. Its telescope is the all-natural-$m$, full-amplitude polynomial, entire-actual-image, all-placement raw statement described above. The matching Scribe contains the exact candidate claim and applicability limits. The mirrored Reg source attempts the whole source family with an enrolled dependent-family readout; source-selection evidence is absent under #30422 and no `declared_validated` status is claimed.

`D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result` proves the all-natural-$m$ physical MassOne statement in Route. Its matching Scribe retains the full polynomial, slice topology, arbitrary recovery competitors, per-window ambiguity quantifiers and exclusions. It is the sole AdditionalMember of the existing claim hosted by `OpenBoundaryMPSAllWindowC9.result`, not a second claim. The normalized Reg attempt preserves the entire telescope but is `declared_unresolved`, IE-C050 ClosedTruthReadout, rule `source.selection_missing`; faithful source-selection evidence is absent. The newly public `OpenBoundaryMPSDensityGenericity.continuous_realCoordinates` separately lacks owner-mirror registration evidence. Both unfinished audits use the existing #30422 disclosure route; no new `declared_validated` status is asserted.

## Triage

Candidate `admission_basis: open-problem-resolution` under CLAUDE 3.2 and pre-probe #30422; conservative `proof_shape: bind-only` for the results and all 28 normalized private lemmas. Each private auxiliary is used on the live proof path of its `result`; no separate helper package or escape witness is claimed. The single `OpenProblemResolutionClaim(Proved)` retains the raw result as host and the normalized result as AdditionalMember, completing the same preregistered physical reading. Independent caller fidelity review, required checks, freezing, publication, literature priority and official acceptance remain separate. Global C9 status is OPEN and solved-open-problem KPI remains 0 until caller verification; there is no independent normalized priority or second problem credit.

### What the settlement shows

**Proved (`D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result`):** The decisive mechanism combines the existing boundary and interior suppliers on a common finite dense-open intersection in the actual image. Reversal reuses boundary recovery at the other end by ordinary matrix transpose with the original boundary vectors swapped. Substitution of the complete raw $Q_3$ coordinates, together with reversal of the full amplitude coordinates, represents that intersection by one polynomial; a common actual point proves that polynomial nonzero.

**Proved (`D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSAllWindowC9.result`):** For each natural $m$, $N=3+m$, one nonzero real polynomial in all real and imaginary amplitude coordinates defines a nonempty, relatively open and dense, $U(1)$-saturated locus in the ENTIRE actual open-boundary image. Every target there is nonzero, and each individual adjacent $Q_3$ window identifies it among arbitrary actual competitors exactly up to unit phase. Every individual adjacent $Q_2$ or $Q_1$ window instead admits an actual nonzero nonphase competitor, which may depend on the window. Partial traces retain the chosen pair witness when passing to a contained one-site window. Thus three versus one or two sites is sharp for a single adjacent raw observation in this finite binary bond-two translation-invariant model, including $N=3$ and every placement.

**Proved (`D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSNormalizedC9.result`):** The radial SOS polynomial, normalization retraction and trace-controlled witness transport supply the physical-mass-one slice and every individual-window statement in Route for all $N=3+m$, including $N=3$. The former raw-only slice gap is filled by this full normalized candidate, with both states normalized; it does not follow from $U(1)$ saturation alone. This is a member of the same C9 settlement candidate, not an additional external resolution.

**Open beyond this proved scope:** Reconstruction from jointly observed smaller windows, stability estimates, and dynamical or thermodynamic conclusions are not established here. The raw and normalized identifiability statements supply mathematical inputs envisaged by the paper's tomography discussion only within the stated model; an operational tomography protocol and its error bounds remain outside this settlement.

**Open for additional source consequences:** This result does not settle the periodic four-site question C10, and the bounded C9 literature check makes no claim about C10's global literature status. It does not alter the C8 coherent-sum result, its Ma--Zhang attribution or license, or the paper's other results. No extension to other bond or local dimensions or boundary models is proved here, and no new companion Lean theorem is asserted.

## ASSUMED-UNVERIFIED

The literature and priority assessment is bounded by the searched scope recorded in Gap: `not-found-in-searched-scope` is no global novelty, world-first or unique certificate. Global priority and a complete literature settlement remain unverified.

The four-slot source audit remains unfinished under issue [#30422](https://github.com/the-omega-institute/trureturing/issues/30422): `source.selection_missing` records absent source-selection evidence for the whole original result family. Existing Reg evidence is retained; neither this prose repair nor the mathematical proof establishes `declared_validated`.

For the normalized result the observed audit is `declared_unresolved`, IE-C050 ClosedTruthReadout, rule `source.selection_missing`. Separately, the newly public `OpenBoundaryMPSDensityGenericity.continuous_realCoordinates` has no owner-mirror registration evidence; no native verdict or validated status is invented for it. These exact targets are disclosed in [#30422, comment 6903181736](https://github.com/the-omega-institute/trureturing/issues/30422#issuecomment-6903181736), with exact caller readback; the disclosure supplies no missing audit evidence.

Required CI, caller fidelity acceptance, canonical freezing and publication of the combined candidate, and official acceptance remain pending. Local structural checks do not establish full Scribe validation, required CI or canonical admission. These lifecycle boundaries do not weaken the exact raw or normalized mathematical scopes stated above; global C9 remains OPEN and solved-open-problem KPI remains 0 pending caller full acceptance.
