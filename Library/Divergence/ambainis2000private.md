---
bibkey: ambainis2000private
authors: Andris Ambainis; Michele Mosca; Alain Tapp; Ronald de Wolf
year: 2000
title: Private Quantum Channels
doi: 10.1109/SFCS.2000.892142
claim: Theorem 4.2 includes the balanced I and Y randomization of real-amplitude qubit states.
strata_touched:
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicDensity
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI
  - D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCommonSequence
license: citation-only
triage: anchor
---

# Private Quantum Channels

## Verified locator

FOCS 2000, pp. 547–553, Theorem 4.2.
[DOI 10.1109/SFCS.2000.892142](https://doi.org/10.1109/SFCS.2000.892142)

The one-qubit real-state case uses the average of the identity channel and
Pauli $Y$ conjugation. For a real unit vector $v$, the states from $v$ and $Yv$
are orthogonal, so their average is $I/2$. In the three-qubit construction,
the classical $B$ flag records this choice, and tracing out $B$ gives $AC=I/4$.
[Issue #32416](https://github.com/the-omega-institute/trureturing/issues/32416)
