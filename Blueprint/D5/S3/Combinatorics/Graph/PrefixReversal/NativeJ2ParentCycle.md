# Unconditional Native Two-Label Parent Construction

## Abstract

The actual native F2 witnesses construct a special Hamilton path and all ordinary children, earning an unconditional Hamilton cycle on the full independent parent domain.

**Theorem 1.1 (The Native Special Child Has a Hamilton Path).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; 3 \le \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) \Rightarrow \left(\exists q \in \mathrm{SpecialWalk}\left(frame, \mathrm{Port}\left(0, 0\right), \mathrm{Port}\left(2, 1\right)\right),\; \mathrm{IsHamiltonian}\left(q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle.native_j2_special_hamilton_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five, every two-selected-label supply frame F and every base length at least three, the actual special child has a Hamilton path from R0 to L2. FrameDomain and SpecialDomain are proved equal on configurations. The false-half pieces of one native F2 Hamilton cycle are transported through that identity map, and their exact three cuts are identified with specialCuts. Their literal endpoint pairs R0/R2, L0/L1 and R1/L2 satisfy the E2 boundary law. The native c seam assembler then constructs the path from these particular pieces with full support and remaining-edge permutations. No special-path or target-partition certificate is assumed.

**Theorem 1.2 (The Full Parent Has an Unconditional Hamilton Cycle).**

$$\forall m \in \mathrm{Nat},\; 5 \le m \Rightarrow \left(\forall frame \in \mathrm{SupplyFrame}\left(m, 2\right),\; 3 \le \mathrm{Length}\left(\mathrm{Base}\left(frame\right)\right) \Rightarrow \left(\exists base \in \mathrm{ParentVertex}\left(frame\right),\; \exists cycle \in \mathrm{ParentClosedWalk}\left(frame, base\right),\; \mathrm{Value}\left(base\right) = \mathrm{rightPort}\left(frame, 0\right) \land \mathrm{IsHamiltonianCycle}\left(cycle\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle.native_j2_parent_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m at least five and every two-selected-label supply frame with base length at least three, there is a Hamilton cycle on ParentDomain based at R0. The special path is constructed by the preceding theorem. For each nonzero actual base gap, nativeChildFrame rotates only the base, and the native F2 theorem supplies a genuine Hamilton cycle with its earned remaining-b invariant. The invariant proves the literal ordinary supplier cut, so that same walk yields a SpecifiedOrdinaryCycle. Opening those cuts and connecting all actual child paths uses the independent complete child partition to exhaust ParentDomain. The theorem assumes no previous parent cycle, recursive hstep certificate or unproved endpoint state. Its saved boundary consumer maps the final m=5 parent through fullParentDomainIso to the six-label ambient Cayley graph.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle.native_j2_parent_hamiltonian_cycle`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle.native_j2_special_hamilton_path`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2HalfPaths](NativeActualJ2HalfPaths.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedFrameDomains](NativeMarkedFrameDomains.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances](NativeSpecialBoundaryInstances.md)
