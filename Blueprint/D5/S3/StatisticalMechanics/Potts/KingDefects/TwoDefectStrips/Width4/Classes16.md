# Two-defect king transfers

## Abstract

The finite data support the literal width-4 king-grid recurrence.

The finite certificate establishes the domain successor multiset and its labelled-row multiplicities. These transition facts supply content for the later transfer proof.

**Theorem 1.1 (The successor multiset for source class 16).**

$$\forall (p: \operatorname{HardinA233164KingStrip}.\operatorname{Boundary}), (\forall (d: \operatorname{Fin}\left(3\right)), ((\operatorname{Data}.\operatorname{Valid}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right)) \Rightarrow ((\operatorname{Canonical}\left(p\right)) \Rightarrow ((\operatorname{Data}.\operatorname{cl}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right) = 16) \Rightarrow (\operatorname{Data}.\operatorname{successors}\left(p, \operatorname{Fin}.\operatorname{val}\left(d\right)\right) = \operatorname{Data}.\operatorname{classList}\left(16\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes16.class_successors` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; Colin Barker; OEIS Foundation Inc. (2013). *OEIS A229751: four-colour king arrays with exactly two mistakes*. URL: <https://oeis.org/A229751>.

*Commentary.*

For every canonical row and residual budget in this source class, sorting the admissible next-row classes gives the pinned successor list. Multiplicity records distinct labelled rows.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Classes16.class_successors`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/KingDefects/TwoDefectStrips/Width4/Data](Data.md)
