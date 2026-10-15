# Native Exceptional Energy Support

## Abstract

The full native ghost support and oscillator frequency determine the exceptional zero-energy labels.

**Theorem 1.1 (Complete oscillator and ghost labels).**

$$\forall D, d, S, \operatorname{oscillatorEnergy}\left(d\right) + \operatorname{ghostEnergy}\left(S\right) = 0 \iff (d = 0 \land \operatorname{GroundZeroSites}\left(S\right)) \lor (\exists i \in \operatorname{Fin}\left(\operatorname{rank}\left(D\right)\right), d = \operatorname{single}\left(\operatorname{unitFrequency}\left(i\right), 1\right) \land \operatorname{NegativeOneSites}\left(S\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/OriginalZeroChargeEnergySector.zero_energy_labels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ghost states are finitely supported functions on all finite subsets of the natural-number site set. Even site 2k is the creator b at mode -k-2, with energy k+2; odd site 2k+1 is the creator c at mode 1-k, with energy k-1. In particular site 1 has energy -1, site 3 is the c zero mode, and site 5 has energy 1.

Removing site 1 leaves only nonnegative site weights. Therefore every ghost subset has energy at least -1. A site above 5 has weight at least 2, so no such site can occur at nonpositive ghost energy. The six possible nonpositive subsets follow from this proved support bound, not from an imposed occupation cutoff.

GroundZeroSites means that S is empty, {3}, {1,5}, or {1,3,5}; NegativeOneSites means that S is {1} or {1,3}. The unitFrequency index is (i,0), whose native oscillator weight is one.

Oscillator frequencies are positive integers. At zero total energy their sum is either zero or one. In the first case the complete oscillator exponent is zero. In the second case exactly one axis at frequency one has occupation one. This argument uses no positivity of the lattice Gram matrix and includes rank zero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/OriginalZeroChargeEnergySector.zero_energy_labels`
- Dependency: [D5/S3/VertexAlgebra/LatticePositiveEnergy](LatticePositiveEnergy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](LatticeSugawaraConformal.md)
