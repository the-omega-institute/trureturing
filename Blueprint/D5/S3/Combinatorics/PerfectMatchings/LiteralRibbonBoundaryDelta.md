# Literal boundary change under signed ribbon deletion

## Abstract

On the full original flag carrier, deleting a marked ribbon counts its facial class exactly.

The input R contains a finite flag carrier, fixed-point-free involutions s and t for corners and bands, and the two flags a,b at one end of the mark. The four flags a,b,t(a),t(b) are distinct. The physical boundary components are the connected components under alternating corner and band steps. The cut fixes these four flags, and the deletion caps a with b and t(a) with t(b), leaving every other band step untouched. Thus Delta(R) counts the components after those literal same-end caps minus the original number.

**Theorem 1.1 (The original marked band and its boundary delta).**

$$\forall R \in MarkedRibbon,\; (\operatorname{Bad}\left(R\right) \Leftrightarrow \operatorname{Delta}\left(R\right) = 1) \land ((\operatorname{Good}\left(R\right) \Leftrightarrow \operatorname{Delta}\left(R\right) = 0) \land (\operatorname{Regular}\left(R\right) \Leftrightarrow \operatorname{Delta}\left(R\right) = -1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/LiteralRibbonBoundaryDelta.original_boundary_delta` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Bad, good, and regular denote the original directed-face tests BadAt, GoodAt, and RegularAt at the given end of R. The terminology follows Ghanbari and Šámal, Facial diagrams and cycle double cover, arXiv:2605.01410, Sections 1 and 3. The result counts actual original-flag components, not just the orbit classes visible at the four exposed labels.

The full directed-orbit quotient is the disjoint sum of untouched classes and actual exposed first-return classes. Untouched classes are canonically unchanged by seam replacement. After comparison of the three possible endpoint pairing forms, the directed deltas are +2, 0, and -2. Each undirected alternating component gives two opposite directed cycles, so the corresponding changes are +1, 0, and -1.

Neither connectedness nor orientability is assumed. Keeping the four attachment flags as dummy subdivisions also retains the boundary of a newly isolated endpoint. A surface realized by a separately constructed flag model, a general one-vertex chart, or a quantum measurement is not asserted here.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/LiteralRibbonBoundaryDelta.original_boundary_delta`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](FiniteBandSwitch.md)
