---
bibkey: christodoulouruffini1971chargedblackhole
authors: Demetrios Christodoulou and Remo Ruffini
year: 1971
title: Reversible Transformations of a Charged Black Hole
doi: 10.1103/PhysRevD.4.3552
url: https://doi.org/10.1103/PhysRevD.4.3552
claim: The charged rotating black hole mass formula yields an irreducible mass which bounds reversible extraction.
strata_touched:
  - D5/S3/Geometry/Lorentz/BlackHoleThermodynamics4D
license: citation-only
triage: anchor
---

# Mass formula and horizon mechanics

## Verified locator

- Physical Review D 4 (1971), pp. 3552-3555.
- DOI https://doi.org/10.1103/PhysRevD.4.3552

## Related sources and mathematical correspondence

Reall, *Black Holes* (2024), Section 7.2, equations (7.1)-(7.2),
gives the Kerr-Newman metric and horizon polynomial. The model here
sets the magnetic charge to zero. Section 7.6, equations (7.44)-(7.46),
gives the irreducible mass and horizon area for Kerr and explains the
extraction bound. Section 9.4, equation (9.20), gives the first law and
describes the additional electric potential term for Einstein-Maxwell
theory. Equation (10.108) gives the Hawking temperature and the
following discussion describes the negative Schwarzschild heat capacity.

- https://www.damtp.cam.ac.uk/user/hsr1000/black_holes_lectures_2024.pdf
- [Related Schwarzschild geometry note](reall2024blackholes.md)
- Bardeen, Carter and Hawking, *The four laws of black hole mechanics*,
  Communications in Mathematical Physics 31 (1973), pp. 161-170,
  https://doi.org/10.1007/BF01645742.
- Hawking, *Particle creation by black holes*, Communications in Mathematical
  Physics 43 (1975), pp. 199-220, https://doi.org/10.1007/BF02345020.

The Lean module uses the horizon polynomial to prove the mass identity in
area, angular momentum and electric charge coordinates. Ordinary scalar
differentiation gives the first law on this family, including the coefficients
at extremality. Its extraction result applies to pairs of Kerr endpoints
with nondecreasing area. The sharp value is attained by an extremal Kerr
endpoint and an equal-area Schwarzschild endpoint. The temperature limit
concerns surface gravity at fixed positive mass.
