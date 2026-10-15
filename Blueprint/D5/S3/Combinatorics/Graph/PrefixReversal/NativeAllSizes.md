# Native Hamilton Cycles at Every Size

## Abstract

The native state construction closes at the full permutation domain for every size.

**Theorem 1.1 (Three Native Prefix Reversals Admit a Hamilton Cycle).**

$$\forall m \in \mathrm{Nat},\; 3 \le m \Rightarrow \left(\exists base \in \mathrm{Configuration}\left(m\right),\; \exists walk \in \mathrm{NativeClosedWalk}\left(m, base\right),\; \mathrm{IsHamiltonianCycle}\left(walk\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeAllSizes.native_all_sizes_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural m at least three, the actual multiplication Cayley graph on Configuration m with the three generators a m, b m and c m has a Hamilton cycle. Configuration m is the permutation type on m plus one labels, so this covers every label count at least four. The four-label and five-label cases use the native base constructions; the six-label case uses the unconditional two-selected-label parent construction. For m at least six, the final frame selects m minus three labels and has a base of exactly three labels. The all-frame strong-state theorem supplies the special Hamilton path and the Hamilton cycles for each actual rotated ordinary child at this same order. Their remaining-b invariant earns the precise supplier edge opened in each child. The independent child partition and native seam assembly then produce a Hamilton cycle on the final parent domain. This final assembly only requires base length at least three; it does not call the state transition that consumes an additional base label. The three-label full-parent-domain isomorphism maps this cycle to the entire permutation Cayley graph. No recursive Hamiltonicity certificate or unproved endpoint state is an assumption of the result, and no literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeAllSizes.native_all_sizes_hamiltonian_cycle`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase](NativeFiveBase.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeFourBase](NativeFourBase.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentCycle](NativeJ2ParentCycle.md)
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeThreeLabelFullDomain](NativeThreeLabelFullDomain.md)
