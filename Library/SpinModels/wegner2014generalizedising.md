---
bibkey: wegner2014generalizedising
authors: Franz J. Wegner
year: 2014
title: "Duality in generalized Ising models"
doi: 10.48550/arXiv.1411.5815
url: https://arxiv.org/abs/1411.5815v1
claim: "For a generalized Ising model with mod-2 incidence matrix theta(b, r), Section 4.3 writes the partition function as the high-temperature expansion (24) over phi(b) in {0, 1}; by (25) the sum over spin configurations keeps exactly the phi_0 with sum_b theta(b, r) phi_0(b) = 0 mod 2 for all r, each contributing 2^Ns, which gives (27)."
strata_touched:
  - D5/S3/StatisticalMechanics/ZTwoHighTemperatureExpansion.sum_sgn_mul_prod_one_add_eq
license: citation-only
triage: anchor
---

# Duality in generalized Ising models

Lecture notes for the Les Houches summer school 2014, based on F. J. Wegner,
"Duality in Generalized Ising Models and Phase Transitions without Local Order
Parameters", J. Math. Phys. 12 (1971) 2259–2272, DOI 10.1063/1.1665530. The
bibliographic data of the 1971 paper (title, author, journal, volume 12, issue 10,
pages 2259–2272) were checked against its Crossref record; its full text was not read.

Section 4.1 (printed page 5) sets up the model: Ising spins S(r) on sites r, bonds b,
an incidence matrix θ(b, r) ∈ {0, 1} over the ring modulo 2, and bond variables
R(b) = ∏_r S(r)^θ(b,r), with βH = −∑_b K(b) R(b) (equation (14)).

Section 4.3, "Derivation of (22, 23)" (printed pages 6–7), expands

> Z{K} = ∏_b cosh K(b) ∑_{φ(b)} ∏_b tanh K(b)^φ(b) ∑_{S(r)} ∏_b R(b)^φ(b)   (24)

> with φ(b) ∈ {0, 1} independent for all b. Since
> ∏_b R(b)^φ(b) = ∏_r S(r)^(∑_b θ(b,r)φ(b))   (25)
> those φ(b) = φ0(b) contribute, which obey the set of homogeneous equations
> ∑_b θ(b, r) φ0(b) ≡ 0 mod 2   (26)
> for all r. [...] They contribute with the factor 2^Ns. Thus
> Z{K} = 2^Ns ∏_b cosh K(b) ∑_{φ0(b)} ∏_b tanh K(b)^φ0(b).   (27)

The quotations are transcribed from the PDF text layer of arXiv:1411.5815v1 with the
displayed formulas linearized. The passage treats the partition function, which is the case
without an inserted product of spins; the same expansion with an inserted product of
spins along a set of sites is not stated in this passage.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1411.5815
- URL: https://arxiv.org/abs/1411.5815v1
- PDF: https://arxiv.org/pdf/1411.5815v1, Section 4.1 (printed page 5) and Section 4.3, equations (24)–(27) (printed pages 6–7).
