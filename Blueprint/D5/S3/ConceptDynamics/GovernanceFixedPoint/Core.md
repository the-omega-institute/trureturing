# Governance Fixed-Point Core

## Abstract

Canonical carriers for governance gate equations with blind and self-reading status derivation, together with the two-status flip.

**Definition 1.1 (Gate agreement).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Gate`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Gate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A gate requires pointwise equality of the handwritten and derived status maps.

**Definition 1.2 (Blind derivation).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.BlindDeriver`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.BlindDeriver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A blind deriver reads a context and an entry without receiving the handwritten status map.

**Definition 1.3 (Self-reading derivation).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.SelfReadingDeriver`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.SelfReadingDeriver` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A self-reading deriver additionally receives the complete handwritten status map.

**Definition 1.4 (Blind lift).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.liftBlind`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.liftBlind` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical lift makes a blind deriver self-reading by ignoring its handwritten-map argument.

**Definition 1.5 (Status blindness).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.StatusBlind`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.StatusBlind` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Status blindness is exact factorization through the canonical blind lift.

**Definition 1.6 (Boolean flip).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.boolFlip`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.boolFlip` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean flip exchanges false and true.

**Definition 1.7 (Prefix extension).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.PrefixExtension`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.PrefixExtension` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A new byte list extends an old one when it is the old list followed by a suffix.

**Definition 1.8 (Tail bytes).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.TailBytes`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.TailBytes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tail bytes are the document bytes at and after a starting offset.

**Definition 1.9 (Content key).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ContentKey`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ContentKey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A content key is represented by the complete byte list.

**Definition 1.10 (Content-key constructor).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.contentKey`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.contentKey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The canonical content key retains all input bytes.

**Definition 1.11 (Verdict).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Verdict`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Verdict` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A settlement verdict is pending, admitted, or rejected.

**Definition 1.12 (Settlement view).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Settlement`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Settlement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The settlement view maps logical identifiers to current verdicts.

**Definition 1.13 (Ledger entry).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.LedgerEntry`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.LedgerEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ledger entry couples one logical identifier to its source bytes.

**Definition 1.14 (Active index view).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ActiveIndex`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ActiveIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The active-index view maps each logical identifier to its active content key.

**Definition 1.15 (Active source).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ActiveSource`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ActiveSource` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A content key is active for an identifier exactly when the index maps that identifier to the key.

**Definition 1.16 (Rekey result).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.RekeyResult`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.RekeyResult` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A rekey result records its predecessor, replacement entry, active index, and settlement view.

**Definition 1.17 (Legal tail rekey).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.LegalTailRekey`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.LegalTailRekey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A legal tail rekey preserves identity and settlement while extending the eligible source tail and updating only its active key.

**Definition 1.18 (Conservative rekey).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ConservativeRekey`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ConservativeRekey` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A conservative rekey preserves settlement and every unrelated active index while replacing exactly one logical source.

**Definition 1.19 (Jointly allowed repairs).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.JointAllowed`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.JointAllowed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The jointly allowed repairs are the intersection of two rule sets.

**Definition 1.20 (Reachable repair).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ReachableRepair`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ReachableRepair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A repair class is reachable when it contains a jointly allowed repair.

**Definition 1.21 (Deadlock).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Deadlocked`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Deadlocked` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A repair class is deadlocked when no repair in it is jointly allowed.

**Definition 1.22 (Channel-extended allowance).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.AllowedWithChannel`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.AllowedWithChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Adding a channel unions its repairs with the jointly allowed set.

**Definition 1.23 (Conservative channel).**

Lean statement: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ConservativeChannel`

*Formalization.* `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ConservativeChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A conservative channel retains every formerly allowed repair and adds exactly the designated repair class.

## References

- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ActiveIndex`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ActiveSource`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.AllowedWithChannel`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.BlindDeriver`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ConservativeChannel`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ConservativeRekey`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ContentKey`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Deadlocked`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Gate`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.JointAllowed`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.LedgerEntry`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.LegalTailRekey`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.PrefixExtension`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.ReachableRepair`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.RekeyResult`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.SelfReadingDeriver`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Settlement`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.StatusBlind`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.TailBytes`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.Verdict`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.boolFlip`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.contentKey`
- Truth anchor: `D5/S3/ConceptDynamics/GovernanceFixedPoint/Core.liftBlind`
