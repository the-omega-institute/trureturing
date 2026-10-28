# Exact Distance to Periodic Grid Holonomy Sectors

## Abstract

Every flat rectangular periodic binary edge label has an exact Hamming distance to each prescribed holonomy sector.

**Definition 1.1 (Distance on labeled edges).**

Lean statement: `D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance.edgeDistance`

*Formalization.* `D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance.edgeDistance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For labels y and z on Fin M by Fin N, edgeDistance is the Hamming distance of their horizontal arrays, indexed by Fin M times Fin N, plus the Hamming distance of their vertical arrays on the same index set. Each of the 2MN labeled edge coordinates is counted once. Horizontal and vertical coordinates are distinct even at a seam intersection.

**Theorem 1.2 (Attained minimum over every flat holonomy sector).**

$$\forall M,N:\mathbb{N}, (0<M\land0<N)\Rightarrow\forall y:\operatorname{EdgeLabel}(M, N), \operatorname{Flat}(y)\Rightarrow\forall h,v:\operatorname{ZMod}(2), (\exists z:\operatorname{EdgeLabel}(M, N), \operatorname{Flat}(z)\land\operatorname{H}(z)=h\land\operatorname{V}(z)=v\land\operatorname{D}(y, z)=M[\operatorname{H}(y)\neq h]+N[\operatorname{V}(y)\neq v])\land(\forall z:\operatorname{EdgeLabel}(M, N), (\operatorname{Flat}(z)\land\operatorname{H}(z)=h\land\operatorname{V}(z)=v)\Rightarrow M[\operatorname{H}(y)\neq h]+N[\operatorname{V}(y)\neq v]\leq\operatorname{D}(y, z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance.flat_sector_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Eric Dennis, Alexei Kitaev, Andrew Landahl, John Preskill (2002). *Topological quantum memory*. DOI: [10.1063/1.1499754](https://doi.org/10.1063/1.1499754). URL: <https://arxiv.org/abs/quant-ph/0110143>.

*Commentary.*

Here H(y)=rowHolonomy(y,0), V(y)=columnHolonomy(y,0), D(y,z)=edgeDistance(y,z), and [P] is 1 when P holds and 0 otherwise. The dimensions M and N are arbitrary positive natural numbers. The input y is any flat label, and h and v are arbitrary elements of ZMod 2. There is a flat label z with holonomies (h,v) whose distance is exactly M[H(y) differs from h]+N[V(y) differs from v]. Every flat label with those holonomies has at least that distance.

If horizontal holonomies differ, flatness makes the row sums differ in every one of the M rows. Choose one disagreeing horizontal coordinate in each row. The row coordinate makes this choice injective, giving M distinct edits. Transposing the argument gives N distinct vertical edits when vertical holonomies differ. Adding the two support bounds is valid because the two edge orientations are counted separately.

For attainment, take the anchored potential supplied by flatLabelEquiv and use holonomySectorEquiv in the target sector with that same potential. The common gradient cancels in coordinate comparisons. Changing horizontal holonomy changes exactly the M horizontal seam entries; changing vertical holonomy changes exactly the N vertical seam entries. These changes occur simultaneously and preserve flatness.

The zero sector is precisely the image of periodic vertex gradients by PeriodicGridHolonomy.flat_exact_iff. Thus choosing h=v=0 gives the exact number of edge edits required to restore a periodic vertex realization from a flat input. The theorem is a minimum over a sector; it gives no uniqueness statement for an edge label or potential and specifies no decoder.

Positive dimensions one and two are included in the labeled periodic-cell model. Interpreting the coordinates as distinct simple-graph edges requires M,N at least three. The result extends the existing binary grid classification quantitatively within classical cohomology mathematics. Dennis, Kitaev, Landahl and Preskill give the shortest nontrivial cycle interpretation and square toric-code distance L. QECLean formalizes that square code-distance result with a different toolchain; its statement does not supply this rectangular all-sector minimum. No research originality or quantum implementation is asserted.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance.edgeDistance`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/PeriodicGridSectorDistance.flat_sector_distance`
- Dependency: [D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy](PeriodicGridHolonomy.md)
