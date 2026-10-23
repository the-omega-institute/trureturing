---
bibkey: beyer2022jointmeasurability
authors: K. Beyer; R. Uola; K. Luoma; W. T. Strunz
year: 2022
title: Joint measurability in nonequilibrium quantum thermodynamics
doi: 10.1103/PhysRevE.106.L022101
url: https://arxiv.org/abs/2111.02854
claim: "The ansatz for the effects W^U_ab in Eq. (6) is a priori not the most general one [54]. However, numerical simulations suggest that our visibility bounds are tight and we conjecture that our construction is optimal to satisfy condition (ii) for the given model Eq. (5)"
strata_touched:
  - D5/S3/Quantum/Measurements/CalibratedJointMeasurabilityOptimality
license: citation-only
triage: anchor
---

# Joint measurability in nonequilibrium quantum thermodynamics

Phys. Rev. E 106, L022101; arXiv:2111.02854v2, pp. 3–4 and Supplemental Material.

## Verified locator

DOI: 10.1103/PhysRevE.106.L022101

Source: https://arxiv.org/abs/2111.02854

## Source statements

Page 3:

> (i) Average condition: The average operator of W^U agrees with the difference of the average operators of B^U and A for all choices of f and g

> (ii) Fluctuation condition: For states ρ_Δ diagonal in the initial energy eigenbasis the statistics given by W^U agrees with the sequentially measured GTPM statistics

Equation (5) fixes $A_a=\lambda\Pi_a+(1-\lambda)I/d$ and
$B_b=\gamma\Pi'_b+(1-\gamma)I/d$, with both visibilities in $(0,1)$.
The instrument is the Lüders instrument $\mathcal I^A_a(\rho)=\sqrt{A_a}\rho\sqrt{A_a}$.
Equations (8)–(9) give
$\gamma\le 2\kappa/(d+2\kappa-d\kappa)$, where
$\kappa=2\sqrt{\lambda+(1-\lambda)/d}\sqrt{(1-\lambda)/d}+(d-2)(1-\lambda)/d$.
The inverse Lüders construction proves sufficiency.

Page 4:

> The ansatz for the effects W^U_ab in Eq. (6) is a priori not the most general one [54]. However, numerical simulations suggest that our visibility bounds are tight and we conjecture that our construction is optimal to satisfy condition (ii) for the given model Eq. (5)

The Supplemental Material repeats:

> Therefore, we conjecture that the proposed form of the joint POVM is optimal for the given noise model if one wants to satisfy the fluctuation condition (ii).

The Lean necessity statement ranges over every dimension $d\ge2$, every intermediate
unitary, and all parent POVMs obeying both conditions, without restricting their form.
Standard matrix units represent each energy basis, and the arbitrary unitary represents
its relative orientation. Source sufficiency is cited, not formalized by the necessity theorem.
