# Periodic Grid Holonomy

## Abstract

Binary plaquette flatness on a periodic rectangle has exactly two global seam bits.

**Definition 1.1 (Periodic edge labels).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.EdgeLabel`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.EdgeLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A label has horizontal and vertical ZMod 2 values indexed by Fin M and Fin N. For M,N at least three these index the two edge directions of the simple periodic rectangular grid.

**Definition 1.2 (Plaquette sum).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquette`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquette` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The plaquette at (i,j) is s(i,j)+u(i,j+1)+s(i+1,j)+u(i,j), with the additions in the two Fin indices taken cyclically.

**Definition 1.3 (Flat edge labels).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.Flat`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.Flat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Flatness means every plaquette sum vanishes.

**Definition 1.4 (Horizontal holonomy).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.rowHolonomy`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.rowHolonomy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The horizontal holonomy of a row is the sum of its horizontal labels.

**Definition 1.5 (Vertical holonomy).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.columnHolonomy`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.columnHolonomy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The vertical holonomy of a column is the sum of its vertical labels.

**Definition 1.6 (Vertex differential).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.gradient`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.gradient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The horizontal and vertical labels of a vertex potential are the binary sums of its endpoint values.

**Definition 1.7 (Two seam labels).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.seam`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.seam` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A horizontal seam value h occupies precisely the edges at the final column. A vertical seam value v occupies precisely the edges at the final row.

**Theorem 1.8 (Holonomy is constant across rows and columns).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_holonomy_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_holonomy_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a flat label, every row has the holonomy of row zero and every column has the holonomy of column zero. Summing one strip of plaquettes proves each equality.

**Theorem 1.9 (Gradient and seam decomposition).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_decomposition`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every flat binary edge label is the sum of a vertex differential and a seam whose values are its two holonomies. The vertex value at (0,0) is fixed to zero. The proof constructs the potential by cyclic integration and uses each plaquette to transfer horizontal differences between rows.

**Theorem 1.10 (Exact lift criterion).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_exact_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_exact_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A flat label is a single-valued periodic vertex differential exactly when both its horizontal and vertical holonomies vanish.

**Theorem 1.11 (Non-exact flat seam).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.horizontal_seam_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.horizontal_seam_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every M,N at least three, the seam with horizontal value one and vertical value zero is flat, has holonomy (1,0), and admits no periodic vertex lift. The argument uses no parity condition on M or N.

**Theorem 1.12 (Number of flat labels).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_label_card`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_label_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive M,N there are exactly 2^(MN+1) flat labels. The proof uses a bijection with anchored vertex assignments and two independent binary holonomies.

**Theorem 1.13 (Equal-size holonomy sectors).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.holonomy_sector_card`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.holonomy_sector_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every prescribed pair of binary holonomies, the corresponding flat sector contains exactly 2^(MN-1) labels. In particular all four sectors are nonempty.

**Theorem 1.14 (Unique plaquette relation).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquette_relation_rank_one`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquette_relation_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A binary linear combination of plaquette equations vanishes for every edge label exactly when all its coefficients are equal. Single-edge labels force adjacent coefficients to agree in both directions; the all-one relation follows by summing every plaquette.

**Theorem 1.15 (Number of all labels).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.edge_label_card`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.edge_label_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two edge directions contain 2MN binary positions, giving 2^(2MN) labels.

**Theorem 1.16 (Number of liftable labels).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.exact_label_card`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.exact_label_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exactly 2^(MN-1) labels are periodic vertex differentials. They are the zero-holonomy sector among the flat labels.

**Definition 1.17 (Binary edge-coordinate space).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.EdgeSpace`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.EdgeSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two arrays of periodic edge labels form a product vector space over ZMod 2.

**Definition 1.18 (Linear plaquette map).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquetteLinear`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquetteLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This linear map sends each edge assignment to its array of cyclic plaquette sums.

**Definition 1.19 (Flat kernel).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flatSubspace`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flatSubspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel of the plaquette map consists exactly of the flat edge labels.

**Theorem 1.20 (Plaquette rank, flat dimension, and uniform proportions).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.periodic_grid_linear_statistics`

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.periodic_grid_linear_statistics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The plaquette equations form an actual ZMod 2 linear map on the two edge-coordinate spaces. Its kernel is identified with flat labels, giving kernel dimension MN+1; rank-nullity gives plaquette rank MN-1. Both finite-uniform denominators are positive. Exact labels occupy 1/4 of flat labels, while flat and exact labels occupy respectively 1/2^(MN-1) and 1/2^(MN+1) of all edge labels.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.EdgeLabel`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.EdgeSpace`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.Flat`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.columnHolonomy`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.edge_label_card`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.exact_label_card`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flatSubspace`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_decomposition`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_exact_iff`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_holonomy_constant`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.flat_label_card`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.gradient`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.holonomy_sector_card`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.horizontal_seam_counterexample`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.periodic_grid_linear_statistics`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquette`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquetteLinear`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.plaquette_relation_rank_one`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.rowHolonomy`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.seam`
