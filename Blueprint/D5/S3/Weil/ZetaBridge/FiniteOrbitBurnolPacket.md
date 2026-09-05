# Simultaneous Orbit Burnol Packet

Status: Candidate source and author projection.

For a valid `FiniteEvenWeilOrbitFrame`, the module first proves that the actual four-point zero orbits are pairwise disjoint. It then constructs one peak b, a finite exceptional spectral ball E, and tests k_i satisfying:

1. FT(b)=1 at both selected conjugate spectral nodes of every channel.
2. FT(k_i)(gamma_j)=delta_ij and FT(k_i)(conj gamma_j)=-delta_ij.
3. Every k_i vanishes at all exceptional zero indices outside the target union.
4. Outside E, both conjugate evaluations of b have norm at most 1/2.

Existence follows from finite compatible interpolation and the existing closed-strip decay estimate. The simultaneous exceptional set is essential: multiplying separately chosen single-orbit packets would not automatically preserve the other target values.

Main declarations: `frame_orbits_pairwise_disjoint`, `exists_common_exceptional_ball`, `exists_orbitBurnolPacket`.
