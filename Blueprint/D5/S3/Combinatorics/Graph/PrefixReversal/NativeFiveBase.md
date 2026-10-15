# Actual Big-3 Hamilton Cycle at Size Five

## Abstract

The complete actual F2 construction at size five gives a Hamilton cycle on every permutation of five labels.

**Theorem 1.1 (Every Permutation Belongs to the Actual F2 Domain).**

$$\forall v \in \mathrm{Configuration}\left(4\right),\; \mathrm{F2Domain}\left(4, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase.native_five_domain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing native_f2_layer_iff identifies the independently defined F2 union with the layer obtained by erasing labels zero and four. The tuple of every permutation is a reordering of the identity tuple; filtering those two labels leaves a reordering of (1,2,3). Rotate the first label to the head. The remaining pair has two possible orders, giving exactly the reference circle or its reverse. Thus every actual permutation lies in the specified insertion layer and in F2Domain.

**Theorem 1.2 (Map the Actual F2 Cycle onto the Full Group).**

$$\exists base \in \mathrm{Configuration}\left(4\right),\; \exists w \in \mathrm{Walk}\left(\mathrm{mulCayley}\left(\mathrm{generatorTriple}\left(4\right)\right), base, base\right),\; \mathrm{IsHamiltonianCycle}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase.native_five_hamiltonian_cycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the existing native_f2_hamiltonian_cycle at m=4, whose cycle is constructed from actual contact grafts on the independently specified domain. The proved coverage makes its subtype inclusion bijective. The induced graph inclusion preserves every actual Cayley edge, so mapping this same cycle yields a Hamilton cycle for reversals of lengths five, four and three on all 5!=120 permutations.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase.native_five_domain`
- Truth anchor: `D5/S3/Combinatorics/Graph/PrefixReversal/NativeFiveBase.native_five_hamiltonian_cycle`
- Dependency: [D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2Coverage](NativeF2Coverage.md)
