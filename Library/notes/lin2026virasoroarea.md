---
bibkey: lin2026virasoroarea
authors: Jennifer Lin
year: 2026
title: Ryu-Takayanagi area from Virasoro modular data
doi: null
url: https://arxiv.org/html/2606.30723v1
claim: A conditional cross-channel entropy representation links leading area terms in holographic two-dimensional CFT examples to coarse-grained Virasoro sector multiplicities.
strata_touched: []
license: citation-only
triage: anchor
---

# Virasoro sector multiplicities and the RT interface

## Primary source and locator

Preprint arXiv:2606.30723v1, submitted 29 June 2026. The primary HTML introduction, section 2.5.2, section 3.1 and discussion specify the assumptions and the proposed interpretation.

## Use and boundary

The finite RT code has a structural sector-multiplicity interface, not an established CFT identification. Multi-interval and heavy-state claims retain conformal-block and saddle assumptions; quasi-probabilities require positivity checks. A prior source record's finite spectral counterexample to insufficient moment asymptotics remains separate from the current RT owner and does not evaluate the unknown Virasoro block. No claim that this preprint's open problem is solved, or that its coarse-graining is an independent two-party CPTP map, is made.

## Operational interface to the finite-multisector RG result

The primary introduction, equations (1.2) and (1.4), explicitly separate the center-label term, sector multiplicity and an intra-sector replica derivative. Footnotes 1 and 2 retain the large-central-charge conformal-block assumption, particularly for multiple intervals and heavy insertions. The canonical interpretation is conditional even when a leading entropy representation is available.

The original finite RG theorem in PR #8890 section 34 optimizes independent local CPTP maps with exact pure target outputs on each basis sector. It yields a simultaneous optimum for arbitrary finite sector count and a scale semigroup for integer power-rank towers. Applying that argument here requires a common finite regulator, positive density operators, actual integer source and target multiplicities, and a proof that the chosen Virasoro coarse graining obeys its local-channel and exact-sector hypotheses. None of those bridges is inferred from the entropy formula alone. The 2026-09-24 supplement below removes only the exact-output requirement, using a different lower-bound proof.

The original finite RG theorem and its conditional Virasoro interface are in sections 34-35 of the same RT theory owner. They neither evaluate the unknown conformal block nor establish the full gravitational RT formula. The quantum-channel theorem and the unproved physical bridge remain distinct.

## Conditional momentum-window bound

Equation (1.3) gives S(P)=4 sinh(2 pi b P) sinh(2 pi P/b), Q=b+1/b, and c=1+6Q^2. For positive P and b, the derivative of log S(P) is at least 2 pi Q. This derivative is evaluated directly from the displayed primary-source formula.

If actual integer loss ranks satisfy abs(log m_s-log S(P_s)-C0)<=eta with a common C0, a window of width DeltaP has discarded-area span at least max(0,2 pi Q DeltaP-2eta). Under the relevant finite RG hypotheses, the RG lower bound gives delta_*>=1-exp(-max(0,pi Q DeltaP-eta)). Requiring delta_*<=epsilon<1 therefore requires DeltaP<=[eta-log(1-epsilon)]/(pi Q).

The c^(-1/2) scale of this conditional necessary budget does not establish the rank-matching hypothesis, positivity of the proposed sector description, or physical locality of the CFT coarse-graining map. It is not attributed to Lin as a theorem already proved there. The source-supported derivative and the separately proved finite-channel result are distinguished from the unproved bridge between them. The paper's own conformal-block and saddle assumptions remain in force.

## 2026-09-24: what the unrestricted-output theorem changes

The full written supplement is https://github.com/the-omega-institute/trureturing/pull/8890#issuecomment-5816839471 . It is published in this existing PR, not yet incorporated as a new main-volume section. For the actual finite flat-rank model with positive integer ratios, the same optimal error 2T/(1+T) now holds over every independent local CPTP pair, including maps with erroneous basis-sector outputs. Consequently the necessary momentum-window bound above does not require exact basis-sector output by the candidate channel. This change is justified by a projected-environment weak-majorization argument and a reference-labelled joint test, not by simply applying the old proof outside its hypotheses.

All remaining physical assumptions survive: a common finite realization, the flat-target/source factor structure, actual integer ranks and matching budget, physical positive states, and independent local operations without communication or extra shared entanglement. The theorem does not construct the microscopic BCFT projectors in section 3.4, establish bin-probability positivity, or show that Lin's coarse graining preserves arbitrary inter-sector coherences.

The nonflat version additionally shows why matching scalar sector entropies is not a substitute for matching full discarded Schmidt spectra when a coherent finite-channel implementation is demanded. This is an operational consistency requirement for that stronger implementation problem, not a refutation of an entropy-only or algebra-restricted interpretation of the CFT formula. No global novelty claim, Lean proof, or physical RT closure is recorded.
