# SupportMaskChecker

## Abstract

Exact tree evaluation and finite Fourier identities support the exclusion of uniform mixing on the cycle with twenty-one vertices.

**Theorem 1.1 (mask_sound).**

$$\forall (\alpha : \operatorname{Type}) (\operatorname{t} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \alpha) (\operatorname{j} : \operatorname{Nat}) , (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.indexValid} \operatorname{t} = \operatorname{true}) \to ((\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} \operatorname{t}) . \operatorname{testBit} \operatorname{j} = \operatorname{true} \iff \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.low} \operatorname{t} + \operatorname{j} \in \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.leaves} \operatorname{t})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.mask_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A valid support tree encodes membership exactly: bit j is set precisely when low(t) + j occurs among its leaves. The induction shifts each child mask to the common lower bound.

**Theorem 1.2 (checked_permutation).**

$$\forall (\alpha : \operatorname{Type}) (\operatorname{t} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.Tree} \alpha) (\operatorname{n} : \operatorname{Nat}) , (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.indexValid} \operatorname{t} = \operatorname{true}) \to ((\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.low} \operatorname{t} = 0) \to ((\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} \operatorname{t} = 2^{\operatorname{n}} - 1) \to ((\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.count} \operatorname{t} = \operatorname{n}) \to ((\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.leaves} \operatorname{t}) . \operatorname{Perm} (\operatorname{List.range} \operatorname{n})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked_permutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.3 (list_range_sum).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{F} : \operatorname{Nat} \to \operatorname{K}) (\operatorname{n} : \operatorname{Nat}) , ((\operatorname{List.range} \operatorname{n}) . \operatorname{map} \operatorname{F}) . \operatorname{sum} = \sum \operatorname{i} \in \operatorname{Finset.range} \operatorname{n} , \operatorname{F} \operatorname{i}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.list_range_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.4 (source_sum).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{F} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp} \to \operatorname{K}) , (\forall (\operatorname{v} \operatorname{w} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp}) , \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.plus} \operatorname{v} \operatorname{w}) = \operatorname{F} \operatorname{v} \cdot \operatorname{F} \operatorname{w}) \to ((\forall (\operatorname{g} : \operatorname{ZMod} 6 \times \operatorname{ZMod} 2) (\operatorname{v} \operatorname{w} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Exp}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.plus} \operatorname{v} \operatorname{w}) = \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.plus} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{v}) (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{w})) \to ((\sum \operatorname{i} \in \operatorname{Finset.range} 149736 , ((\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{i}) . 2 : \operatorname{K}) \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.norm} \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{i}) . 1) = (\sum \operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.h0} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.p0}) + (\sum \operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.h1} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.p1}) + (\sum \operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.h2} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.p2}) + (\sum \operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.h3} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.p3}) + (\sum \operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.h4} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.p4}) + (\sum \operatorname{g} : (\operatorname{ZMod} 6 \times \operatorname{ZMod} 2) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.h5} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.evalPoly} (\operatorname{fun} \operatorname{e} \mapsto \operatorname{F} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.act} \operatorname{g} \operatorname{e})) \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.p5})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.source_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.5 (rows1).**

$$\operatorname{rows1} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.rows1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.6 (expectedMask1).**

$$\operatorname{expectedMask1} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.expectedMask1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.7 (rowChecked1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{rows1} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.rowChecked1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.8 (targetChecked1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.targetCheck} \operatorname{rows1} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.targetChecked1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.9 (idsValid1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.indexValid} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{rows1}) = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.idsValid1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.10 (maskChecked1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{rows1}) = \operatorname{expectedMask1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.maskChecked1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.11 (countChecked1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.count} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{rows1}) = 49954$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.countChecked1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.12 (targetSum1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.targetSum} \operatorname{rows1} = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.targetSum1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.13 (g1).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g1} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.14 (g2).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g2} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(4 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.15 (g3).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g3} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(4 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(4 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.16 (g4).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g4} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3} \cdot \operatorname{x4})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(4 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x5}^{(2 : \mathbb{N})})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.17 (g5).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g5} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3} \cdot \operatorname{x4})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.18 (g6).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g6} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(4 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(3 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(3 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(4 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(5 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(6 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.19 (g7).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g7} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(3 : \mathbb{N})} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(4 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(4 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(3 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(4 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(3 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(4 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(5 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(6 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g7` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.20 (g8).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g8} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(4 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x3} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(3 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(3 : \mathbb{N})})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g8` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.21 (g9).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g9} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(3 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(4 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(3 : \mathbb{N})} \cdot \operatorname{x4} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3}^{(3 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(4 : \mathbb{N})} \cdot \operatorname{x4})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g9` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.22 (g12).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} : \operatorname{K}) , \operatorname{g12} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} : \operatorname{K}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed cleared certificate polynomial has the displayed type. Its coefficients and monomials are specified by the Lean definition.

**Definition 1.23 (g14).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} : \operatorname{K}) , \operatorname{g14} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} : \operatorname{K}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed cleared certificate polynomial has the displayed type. Its coefficients and monomials are specified by the Lean definition.

**Definition 1.24 (g19).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} : \operatorname{K}) , \operatorname{g19} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} : \operatorname{K}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g19` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed cleared certificate polynomial has the displayed type. Its coefficients and monomials are specified by the Lean definition.

**Definition 1.25 (g10).**

$$\forall (\operatorname{K} : \operatorname{Type}) [\operatorname{CommRing} \operatorname{K}] (\operatorname{x0} : \operatorname{K}) (\operatorname{x1} : \operatorname{K}) (\operatorname{x2} : \operatorname{K}) (\operatorname{x3} : \operatorname{K}) (\operatorname{x4} : \operatorname{K}) (\operatorname{x5} : \operatorname{K}) , \operatorname{g10} \operatorname{x0} \operatorname{x1} \operatorname{x2} \operatorname{x3} \operatorname{x4} \operatorname{x5} = ((((((1) : \operatorname{K}) \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}) + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x3} \cdot \operatorname{x4})))) + (((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(4 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})}) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(2 : \mathbb{N})} \cdot \operatorname{x1}^{(2 : \mathbb{N})} \cdot \operatorname{x2}^{(3 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4} \cdot \operatorname{x5}^{(2 : \mathbb{N})} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}))) + ((((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x2} \cdot \operatorname{x3} \cdot \operatorname{x4} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})})) + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5} + (((1) : \operatorname{K}) \cdot \operatorname{x0}^{(3 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4} \cdot \operatorname{x5} + ((1) : \operatorname{K}) \cdot \operatorname{x0}^{(4 : \mathbb{N})} \cdot \operatorname{x1} \cdot \operatorname{x2}^{(2 : \mathbb{N})} \cdot \operatorname{x3}^{(2 : \mathbb{N})} \cdot \operatorname{x4}^{(2 : \mathbb{N})} \cdot \operatorname{x5})))))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.26 (basisPhase).**

$$\forall (\operatorname{c} : \mathbb{C}) (\operatorname{r} : \operatorname{Fin} 6) , \operatorname{basisPhase} \operatorname{c} \operatorname{r} = \operatorname{if} \operatorname{r.val} = 0 \operatorname{then} \operatorname{Complex.exp} \operatorname{c} \operatorname{else} \operatorname{Complex.exp} (\operatorname{c} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier.eigenvalue} (\operatorname{r.val} : \operatorname{ZMod} 21))$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.basisPhase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Definition 1.27 (phase21).**

$$\forall (\operatorname{c} : \mathbb{C}) (\operatorname{j} : \operatorname{ZMod} 21) , \operatorname{phase21} \operatorname{c} \operatorname{j} = \operatorname{Complex.exp} (\operatorname{c} \cdot \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Fourier.eigenvalue} \operatorname{j})$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.phase21` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The displayed identity defines this operation.

**Theorem 1.28 (basisPhase_ne_zero).**

$$\forall (\operatorname{c} : \mathbb{C}) (\operatorname{r} : \operatorname{Fin} 6) , \operatorname{basisPhase} \operatorname{c} \operatorname{r} \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.basisPhase_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.29 (correlation_polynomial_1).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g1} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2) \cdot (\operatorname{basisPhase} \operatorname{c} 3) \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 1) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.30 (correlation_polynomial_2).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g2} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 3)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)^{(2 : \mathbb{N})}) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 2) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.31 (correlation_polynomial_3).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g3} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 3)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)^{(2 : \mathbb{N})}) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 3) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.32 (correlation_polynomial_4).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g4} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2) \cdot (\operatorname{basisPhase} \operatorname{c} 3) \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)^{(2 : \mathbb{N})}) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 4) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.33 (correlation_polynomial_5).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g5} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2) \cdot (\operatorname{basisPhase} \operatorname{c} 3) \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 5) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.34 (correlation_polynomial_6).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g6} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(3 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 3) \cdot (\operatorname{basisPhase} \operatorname{c} 4)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 5)^{(2 : \mathbb{N})}) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 6) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.35 (correlation_polynomial_7).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g7} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(3 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 2)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 3)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 4)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 5)^{(2 : \mathbb{N})}) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 7) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.36 (correlation_polynomial_8).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g8} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0) \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2) \cdot (\operatorname{basisPhase} \operatorname{c} 3)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)^{(2 : \mathbb{N})}) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 8) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.37 (correlation_polynomial_9).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g9} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 2) \cdot (\operatorname{basisPhase} \operatorname{c} 3)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 9) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.38 (correlation_polynomial_10).**

$$\forall (\operatorname{c} : \mathbb{C}) , \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.SupportMaskChecker.Ring.g10} (\operatorname{basisPhase} \operatorname{c} 0) (\operatorname{basisPhase} \operatorname{c} 1) (\operatorname{basisPhase} \operatorname{c} 2) (\operatorname{basisPhase} \operatorname{c} 3) (\operatorname{basisPhase} \operatorname{c} 4) (\operatorname{basisPhase} \operatorname{c} 5) = ((\operatorname{basisPhase} \operatorname{c} 0)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 1) \cdot (\operatorname{basisPhase} \operatorname{c} 2)^{(2 : \mathbb{N})} \cdot (\operatorname{basisPhase} \operatorname{c} 3) \cdot (\operatorname{basisPhase} \operatorname{c} 4) \cdot (\operatorname{basisPhase} \operatorname{c} 5)) \cdot \sum \operatorname{j} : \operatorname{ZMod} 21 , \operatorname{phase21} \operatorname{c} (\operatorname{j} + 10) / \operatorname{phase21} \operatorname{c} \operatorname{j}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.39 (group2_0).**

$$\operatorname{group2_{0}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.40 (group2_1).**

$$\operatorname{group2_{1}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.41 (group2_2).**

$$\operatorname{group2_{2}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.42 (group2_3).**

$$\operatorname{group2_{3}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.43 (group2_4).**

$$\operatorname{group2_{4}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.44 (group2_5).**

$$\operatorname{group2_{5}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.45 (group2_6).**

$$\operatorname{group2_{6}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.46 (group2_7).**

$$\operatorname{group2_{7}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_7` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.47 (group2_8).**

$$\operatorname{group2_{8}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_8` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.48 (group2_9).**

$$\operatorname{group2_{9}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_9` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.49 (group2_10).**

$$\operatorname{group2_{10}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.50 (group2_11).**

$$\operatorname{group2_{11}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.51 (group2_12).**

$$\operatorname{group2_{12}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.52 (group2_13).**

$$\operatorname{group2_{13}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.53 (group2_14).**

$$\operatorname{group2_{14}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.54 (group2_15).**

$$\operatorname{group2_{15}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_15` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.55 (group2_16).**

$$\operatorname{group2_{16}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.56 (group2_17).**

$$\operatorname{group2_{17}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_17` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.57 (group2_18).**

$$\operatorname{group2_{18}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_18` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.58 (group2_19).**

$$\operatorname{group2_{19}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_19` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Definition 1.59 (group2_20).**

$$\operatorname{group2_{20}} : \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Rows}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_20` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed balanced certificate tree has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.60 (checked2_0).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{0}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.61 (checked2_1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{1}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.62 (checked2_2).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{2}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.63 (checked2_3).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{3}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.64 (checked2_4).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{4}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.65 (checked2_5).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{5}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.66 (checked2_6).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{6}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.67 (checked2_7).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{7}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.68 (checked2_8).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{8}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.69 (checked2_9).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{9}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.70 (checked2_10).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{10}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.71 (checked2_11).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{11}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.72 (checked2_12).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{12}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.73 (checked2_13).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{13}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.74 (checked2_14).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{14}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_14` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.75 (checked2_15).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{15}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.76 (checked2_16).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{16}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.77 (checked2_17).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{17}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.78 (checked2_18).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{18}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_18` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.79 (checked2_19).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{19}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_19` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Theorem 1.80 (checked2_20).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.rowCheck} \operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Data.source} \operatorname{group2_{20}} = \operatorname{true}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_20` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.81 (groupMask2_0).**

$$\operatorname{groupMask2_{0}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.82 (groupMaskChecked2_0).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{0}}) = \operatorname{groupMask2_{0}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_0` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.83 (groupMask2_1).**

$$\operatorname{groupMask2_{1}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.84 (groupMaskChecked2_1).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{1}}) = \operatorname{groupMask2_{1}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_1` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.85 (groupMask2_2).**

$$\operatorname{groupMask2_{2}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.86 (groupMaskChecked2_2).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{2}}) = \operatorname{groupMask2_{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.87 (groupMask2_3).**

$$\operatorname{groupMask2_{3}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.88 (groupMaskChecked2_3).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{3}}) = \operatorname{groupMask2_{3}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.89 (groupMask2_4).**

$$\operatorname{groupMask2_{4}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_4` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.90 (groupMaskChecked2_4).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{4}}) = \operatorname{groupMask2_{4}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_4` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.91 (groupMask2_5).**

$$\operatorname{groupMask2_{5}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_5` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.92 (groupMaskChecked2_5).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{5}}) = \operatorname{groupMask2_{5}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_5` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.93 (groupMask2_6).**

$$\operatorname{groupMask2_{6}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_6` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.94 (groupMaskChecked2_6).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{6}}) = \operatorname{groupMask2_{6}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_6` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.95 (groupMask2_7).**

$$\operatorname{groupMask2_{7}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_7` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.96 (groupMaskChecked2_7).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{7}}) = \operatorname{groupMask2_{7}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_7` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.97 (groupMask2_8).**

$$\operatorname{groupMask2_{8}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_8` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.98 (groupMaskChecked2_8).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{8}}) = \operatorname{groupMask2_{8}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_8` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.99 (groupMask2_9).**

$$\operatorname{groupMask2_{9}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_9` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.100 (groupMaskChecked2_9).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{9}}) = \operatorname{groupMask2_{9}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_9` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.101 (groupMask2_10).**

$$\operatorname{groupMask2_{10}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_10` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.102 (groupMaskChecked2_10).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{10}}) = \operatorname{groupMask2_{10}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_10` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.103 (groupMask2_11).**

$$\operatorname{groupMask2_{11}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_11` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.104 (groupMaskChecked2_11).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{11}}) = \operatorname{groupMask2_{11}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_11` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.105 (groupMask2_12).**

$$\operatorname{groupMask2_{12}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_12` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.106 (groupMaskChecked2_12).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{12}}) = \operatorname{groupMask2_{12}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_12` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.107 (groupMask2_13).**

$$\operatorname{groupMask2_{13}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_13` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.108 (groupMaskChecked2_13).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{13}}) = \operatorname{groupMask2_{13}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_13` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.109 (groupMask2_14).**

$$\operatorname{groupMask2_{14}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_14` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.110 (groupMaskChecked2_14).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{14}}) = \operatorname{groupMask2_{14}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_14` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.111 (groupMask2_15).**

$$\operatorname{groupMask2_{15}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_15` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.112 (groupMaskChecked2_15).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{15}}) = \operatorname{groupMask2_{15}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_15` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.113 (groupMask2_16).**

$$\operatorname{groupMask2_{16}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_16` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.114 (groupMaskChecked2_16).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{16}}) = \operatorname{groupMask2_{16}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_16` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.115 (groupMask2_17).**

$$\operatorname{groupMask2_{17}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_17` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.116 (groupMaskChecked2_17).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{17}}) = \operatorname{groupMask2_{17}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_17` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.117 (groupMask2_18).**

$$\operatorname{groupMask2_{18}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_18` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.118 (groupMaskChecked2_18).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{18}}) = \operatorname{groupMask2_{18}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_18` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.119 (groupMask2_19).**

$$\operatorname{groupMask2_{19}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_19` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.120 (groupMaskChecked2_19).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{19}}) = \operatorname{groupMask2_{19}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_19` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

**Definition 1.121 (groupMask2_20).**

$$\operatorname{groupMask2_{20}} : \operatorname{Nat}$$

*Formalization.* `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_20` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fixed integer support mask has the displayed type. Its leaf sequence and node boundaries are the explicit values in this definition.

**Theorem 1.122 (groupMaskChecked2_20).**

$$\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.Index.mask} (\operatorname{D5.S3.Quantum.Dynamics.CycleUniformMixing.OrbitIndexedSums.ids} \operatorname{group2_{20}}) = \operatorname{groupMask2_{20}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_20` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed identity is used in the orbit-sum and spectral calculation.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.basisPhase`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.basisPhase_ne_zero`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_10`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_11`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_12`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_13`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_14`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_15`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_16`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_17`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_18`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_19`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_20`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_6`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_7`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_8`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked2_9`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.checked_permutation`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_10`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_6`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_7`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_8`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.correlation_polynomial_9`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.countChecked1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.expectedMask1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g10`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g12`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g14`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g19`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g6`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g7`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g8`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.g9`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_10`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_11`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_12`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_13`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_14`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_15`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_16`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_17`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_18`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_19`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_20`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_6`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_7`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_8`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.group2_9`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_10`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_11`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_12`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_13`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_14`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_15`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_16`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_17`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_18`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_19`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_20`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_6`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_7`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_8`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMask2_9`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_0`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_10`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_11`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_12`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_13`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_14`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_15`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_16`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_17`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_18`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_19`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_2`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_20`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_3`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_4`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_5`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_6`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_7`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_8`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.groupMaskChecked2_9`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.idsValid1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.list_range_sum`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.maskChecked1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.mask_sound`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.phase21`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.rowChecked1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.rows1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.source_sum`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.targetChecked1`
- Truth anchor: `D5/S3/Quantum/Dynamics/CycleUniformMixing/SupportMaskChecker.targetSum1`
- Dependency: [D5/S3/Quantum/Dynamics/CycleUniformMixing/OrbitIndexedSums](OrbitIndexedSums.md)
