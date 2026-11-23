# Exact two-defect strip transfer

## Abstract

Exact two-defect strip transfer.

**Definition 1.1 (Admissible residual budgets).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff ((d \le 2) \land (\operatorname{\mathit{Finset}}.\operatorname{\mathit{card}}\left(\operatorname{\mathit{Finset}}.\operatorname{\mathit{filter}}\left(\lambda j: \operatorname{\mathit{Fin}}\left(5\right) \mapsto (p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{castSucc}}\left(j\right)\right) = p\left(\operatorname{\mathit{Fin}}.\operatorname{\mathit{succ}}\left(j\right)\right)), \operatorname{\mathit{Finset}}.\operatorname{\mathit{univ}}\right)\right) \le 2 - d))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The number of adjacent equalities in the six-cell boundary is at most the number of defects already used.

**Definition 1.2 (Classes at budget zero).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{exhaustedClass}} : (\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}) \to (\operatorname{\mathit{Fin}}\left(96\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhaustedClass` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The first 56 classes are the exhausted classes of A229585 in their original order. The next 40 classes use the equality patterns of boundaries with two adjacent equalities. Each pattern code lists colours in order of first occurrence and interprets them as base-three digits, starting with the least significant digit. Nat.mod selects the residue of the index in the pattern list modulo 40. The transition counts formula gives the outgoing multiplicities of each admissible boundary.

**Definition 1.3 (Class of a boundary and budget).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (d = 0) \operatorname{\mathit{then}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(72, \operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{exhaustedClass}}\left(p\right)\right) \operatorname{\mathit{else}} \operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(96, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A positive budget d uses the A229585 boundary class at budget d minus one.

**Definition 1.4 (Transfer matrix).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T} : \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(168\right), \operatorname{\mathit{Fin}}\left(168\right), \mathit{Int}\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The leading block is the A229585 transfer matrix. The lower left block is zero. The right blocks count rows that spend exactly the remaining budget. In the upper right block, 24 columns take their multiplicities from columns of the leading block. The remaining columns use 36 distinct multiplicity profiles. Within the lower right block, the original exhausted sources use the exhausted rows and columns of A229585, extended by zero columns. The transition counts formula gives the entries at each admissible source.

**Definition 1.5 (First-row weights).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{initial}} : (\operatorname{\mathit{Fin}}\left(168\right)) \to (\mathit{Int})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The first 72 entries are the A229585 initial weights. The remaining entries count labelled rows with exactly two horizontal defects, grouped by exhausted boundary class. The strip counting formula uses this vector on the left.

**Definition 1.6 (Acceptance weights).**

$$\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{terminal}} = \operatorname{\mathit{Fin}}.\operatorname{\mathit{append}}\left(0 : (\operatorname{\mathit{Fin}}\left(72\right)) \to (\mathit{Int}), 1 : (\operatorname{\mathit{Fin}}\left(96\right)) \to (\mathit{Int})\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

A completed strip is accepted when its remaining budget is zero.

**Theorem 1.7 (Multiplicity of a successor class).**

$$\forall p: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Boundary}}, (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \implies (\forall s: \operatorname{\mathit{Fin}}\left(168\right), (\sum_{r: \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{Row}}} ((\operatorname{\mathit{if}} ((\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right) \le d) \land (\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{boundary}}\left(r\right), d - \left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{cross}}\left(p, r\right) + \operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{bondDefects}}\left(\operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, r, r\right)\right)\right) = s)) \operatorname{\mathit{then}} (1: \mathit{Int}) \operatorname{\mathit{else}} (0: \mathit{Int}))) = \operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T}\left(\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{cl}}\left(p, d\right), s\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

Each admissible next row contributes one to the multiplicity of its class after spending its horizontal and antidiagonal defects.

Both bounds in the admissibility condition matter. With budget zero and a constant zero boundary, the two rows alternating colours one and two both contribute to class 85, whose matrix entry is one. With budget three and boundary (0, 1, 0, 1, 0, 1), the row (0, 2, 1, 2, 1, 2, 1) contributes to class zero, whose matrix entry is zero.

**Theorem 1.8 (The labelled strip count).**

$$\forall n: \mathit{Nat}, ((\operatorname{\mathit{DefectTransfer}}.\operatorname{\mathit{literalCount}}\left((q := 3), \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{horizontal}}, \operatorname{\mathit{HardinA229585StripData}}.\operatorname{\mathit{antidiagonal}}, 2, n + 1\right): \mathit{Int}) = \operatorname{\mathit{dotProduct}}\left(\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{initial}}, \operatorname{\mathit{Matrix}}.\operatorname{\mathit{mulVec}}\left((\operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{T})^{n}, \operatorname{\mathit{HardinA229693StripTransfer}}.\operatorname{\mathit{terminal}}\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.count_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229693: two-defect three-colour width-7 sheared strips*. URL: <https://oeis.org/A229693>.

*Commentary.*

The first row contributes the initial weight. Each later row multiplies by the transfer matrix, and terminal weights require exact exhaustion. The empty strip has zero colourings with exactly two defects, whereas the zero-power matrix coefficient counts the positive number of qualifying one-row strips.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.count_transfer`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.exhaustedClass`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.terminal`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.transition_counts`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177Canonical](../../../../Combinatorics/TraceAvoidingArrays/HardinA233177Canonical.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/DefectTransfer](../../StripDefects/DefectTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585Strip](../HardinA229585Strip.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripCertificate](../HardinA229585StripCertificate.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/HardinA229585StripData](../HardinA229585StripData.md)
