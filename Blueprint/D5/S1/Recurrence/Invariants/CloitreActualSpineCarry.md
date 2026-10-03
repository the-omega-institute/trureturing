# Actual Cloitre Spine and Scalar Carry

## Abstract

The offset spine belongs to one finite actual Cloitre split tree and preserves its scalar carry total.

All conclusions use the original actual sequence C, selector g, orbit X and complete conditional Hyp21_1 bundle. No inhabitant of that bundle is established. G is the natural golden floor reading.

**Definition 1.1 (The complete actual ordered tree).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.actualTree`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.actualTree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zero gives the exterior empty tree. Labels one and two are terminal nodes. Every label n at least three has ordered children g(n) and n-g(n), each expanded by its own actual selector. Unconditional actual_foundations makes both children positive and strictly smaller, proving finiteness.

**Definition 1.2 (Root labels).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.rootLabel`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.rootLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty tree has exterior label zero.

**Definition 1.3 (Subtree occurrences).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.subtreeAt`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.subtreeAt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A list of Boolean sides identifies one complete subtree occurrence. False means left and true means right; a missing path returns none. Equal labels at different addresses remain distinct occurrences.

**Definition 1.4 (Structural scalar carry fold).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.totalCarry`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.totalCarry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A terminal label contributes zero. At each internal node, add the scalar Beatty deficit of its ordered child labels and both recursive child totals. This is an actual internal-node fold, not a definition by root defect. The Beatty deficit normalizes to G(a)+G(b)-G(a+b).

**Definition 1.5 (Width-dependent endpoint threshold).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.threshold`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.threshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

K(t)=12*t+7.

**Definition 1.6 (The ordered offset child).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.retainedBit`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.retainedBit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retain the left child at even F(j-1)+t-1 and the right child at odd parity.

**Definition 1.7 (Rank decrement).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.stepSize`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.stepSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The corresponding decrement is one or two.

**Definition 1.8 (The opposite anchor rank).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.anchorRank`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.anchorRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sibling anchor has rank j-2 in the even branch and j-1 in the odd branch.

**Definition 1.9 (Successive ranks).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.rank`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.rank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Iterate j to j-stepSize(t,j), keeping the numerical width t fixed.

**Definition 1.10 (Successive occurrence addresses).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.address`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.address` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Start at the empty root address and append the retained Boolean side.

**Definition 1.11 (Complete actual split facts).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.SplitFacts`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.SplitFacts` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ordered children have exactly the offset and anchor labels. Current and retained defects equal h(t)=t-G(t); the anchor defect and scalar split carry are zero. For t at least two, only the retained child has positive defect. At t=1 both defects vanish and the offset label selects it.

**Definition 1.12 (Six rank transitions).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.CongruenceControl`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.CongruenceControl` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For odd t and j modulo three equal to 0,1,2, the decrements are 2,1,2 and successor residues are 1,0,0. For even t they are 1,2,1 and 2,2,1. Reduce the full successor rank j-r modulo three, not truncated residues.

**Theorem 1.13 (One actual finite spine conserves scalar carry).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.full22_2`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.full22_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under every U satisfying the unchanged Hyp21_1, the structural fold on every positive actual tree equals its canonical root defect. For t at least one and k at least K(t), every active rank j >= K(t) has the complete ordered split facts and six congruence transitions. There is a positive finite first stopping index L, all earlier ranks are active, and J=rank(t,k,L) is K(t)-1 or K(t)-2.

For each natural 0 <= i <= L, address t k i identifies the complete actualTree (F (rank t k i) + t) inside the one root actualTree (F k + t). For each natural 0 <= i < L, the opposite address address t k i ++ [!(retainedBit t (rank t k i))] identifies its complete Fibonacci anchor tree actualTree (F (anchorRank t (rank t k i))); that anchor's totalCarry is zero, and totalCarry (actualTree (F (rank t k i) + t)) = totalCarry (actualTree (F (rank t k (i + 1)) + t)). Expanding the folds along these actual occurrences preserves the root total through the terminal tree, whose persistent defect and total are h(t). The separated digit supplier is used down to K(t)-2, without an endpoint hypothesis at that terminal rank.

Scalar zero does not assert zero unit-bit carry or zero at every internal node of an anchor subtree. The six control states retain the numerical width, do not bound it, do not classify the terminal tree and do not establish global selector regularity. Composition and unit-direction tree identities are outside this theorem.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.CongruenceControl`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.SplitFacts`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.actualTree`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.address`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.anchorRank`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.full22_2`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.rank`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.retainedBit`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.rootLabel`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.stepSize`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.subtreeAt`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.threshold`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualSpineCarry.totalCarry`
- Dependency: [D5/S0/Tower/GoldenGapZeckendorf](../../../S0/Tower/GoldenGapZeckendorf.md)
- Dependency: [D5/S1/Deficit/GoldenPhaseDeficit](../../Deficit/GoldenPhaseDeficit.md)
- Dependency: [D5/S1/Deficit/ZeckendorfDisplacementReading](../../Deficit/ZeckendorfDisplacementReading.md)
- Dependency: [D5/S1/Recurrence/Invariants/CloitreActualEndpointPhase](CloitreActualEndpointPhase.md)
- Dependency: [D5/S1/Recurrence/Invariants/CloitreActualRightProfile](CloitreActualRightProfile.md)
