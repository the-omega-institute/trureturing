---
bibkey: sakaiakimoto2026currentresponse
authors: Issei Sakai; Takuma Akimoto
year: 2026
title: "Symmetry breaking of current response in disordered exclusion processes"
doi: 10.1103/21vm-n8gp
url: https://arxiv.org/abs/2512.03316v2
claim: "For the asymmetric simple exclusion process on a ring with quenched site- or bond-dependent rates p_i(ε) = (1 + ε) w_{i,i+1}/2 and q_i(ε) = (1 − ε) w_{i,i−1}/2, a uniform bond-bias ratio p_i(ε)/q_{i+1}(ε) makes the bias-reversal and particle-hole symmetries equivalent, and either a uniform ratio (condition (i)) or the inversion-correspondence condition (ii) makes the stationary current odd in ε. The authors conjecture that an ε² contribution to the current appears whenever neither condition holds."
strata_touched:
  - D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation
license: citation-only
triage: anchor
---

# Sakai and Akimoto, symmetry breaking of the current response in disordered exclusion processes

I. Sakai and T. Akimoto, *Symmetry breaking of current response in disordered exclusion processes*, arXiv:2512.03316 [cond-mat.stat-mech] (v2 of 17 April 2026; v1 of 3 December 2025), Phys. Rev. E 113, 044123 (2026).

## Verified locator

DOI: https://doi.org/10.1103/21vm-n8gp

Source: https://arxiv.org/abs/2512.03316v2

The text was read from the PDF https://arxiv.org/pdf/2512.03316v2:
- pp. 1–2, §II (Eq. (1) on p. 1, Eq. (2) on p. 2);
- p. 2, §III.A (Eq. (5)), and p. 3, §III.D;
- p. 4, §III.F;
- p. 7, Appendix C.

## Source statements

§II (p. 1): "A particle at site i attempts to hop to site i − 1 with rate q_i(ε) and to site i + 1 with rate p_i(ε), where q_i(ε) = (1 − ε)/2 w_{i,i−1}, p_i(ε) = (1 + ε)/2 w_{i,i+1}. (1)" … "In the unbiased case (ε = 0), the rates satisfy ∏_{i=1}^{L} w_{i,i−1}/w_{i,i+1} = 1 ensuring that the stationary current vanishes in equilibrium (see Appendix A)."

§III.A (p. 2): "We define the bond-bias ratio r_i(ε) = p_i(ε)/q_{i+1}(ε), (5) which quantifies the local left-right bias across bond (i, i + 1)."

§III.D (p. 3): "(i) The bond-independent ratio condition requires that the bond-bias ratio r_i(ε) is independent of the bond index i. … (ii) The inversion-correspondence condition identifies cases in which the bias-reversal symmetry can still hold even when the bond-bias ratio is not uniform. … For disordered systems, the inversion-correspondence condition is a rare event, since it requires a finely tuned spatial symmetry of the random rates. We conjecture—and later confirm numerically— that an ε² contribution appears whenever neither condition (i) nor condition (ii) is satisfied."

§III.F (p. 4): "For a single-particle system, the bias-reversal symmetry holds for all ε."

Appendix C (p. 7): "In this condition, there exists k ∈ {1, . . . , L} such that for i ∈ {0, . . . , L − 1}, either p_{k+i}(ε) = q_{k−i}(−ε) or p_{k+i}(ε) = q_{k−i+1}(−ε) holds."

## Reading used by the repository

- The ε² contribution is the coefficient c₂ in J(ε) = c₁ε + c₂ε² + o(ε²), where J is the stationary current across one bond under the unique stationary law of the finite ring.
- Condition (ii) is read in its weakest per-site form, each alternative holding as an identity in ε.
- The conjecture is restricted to at least two particles and at least two holes, since §III.F already reports an exactly odd current for a single particle.
