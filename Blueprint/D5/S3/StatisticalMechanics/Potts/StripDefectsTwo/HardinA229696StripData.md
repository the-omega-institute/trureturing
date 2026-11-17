# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Definition 1.1 (Valid).**

$$\forall p: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (d \le 2)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

Residual budgets are at most two.

**Definition 1.2 (cl).**

$$\forall p: \operatorname{\mathit{Fin}}\left(3\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(5, \operatorname{\mathit{HardinA229588Strip}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right): \operatorname{\mathit{Fin}}\left(15\right)) \operatorname{\mathit{else}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(10, \operatorname{\mathit{HardinA233258PairTransfer}}.\operatorname{\mathit{cls}}\left((p\left((0: \operatorname{\mathit{Fin}}\left(3\right))\right), p\left((1: \operatorname{\mathit{Fin}}\left(3\right))\right), p\left((2: \operatorname{\mathit{Fin}}\left(3\right))\right))\right)\right): \operatorname{\mathit{Fin}}\left(15\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

Positive budgets call the frozen one-defect classifier at d minus one. Zero budget selects the appended equality sector.

**Definition 1.3 (T).**

$$(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(15\right), \operatorname{\mathit{Fin}}\left(15\right), \mathit{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

The 15 by 15 integer matrix retains HardinA229588Strip.T in its leading 10 by 10 block. The added block records cost two and the inherited cost-one block; its diagonal is the frozen zero-temperature Q. The HardinA229696Strip.finite_certificate theorem pins every transition sum.

**Definition 1.4 (initial).**

$$(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(15\right) \to \mathit{Int})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

The 15 integer initial weights append 5 zero entries to the frozen initial vector; HardinA229696Strip.finite_certificate pins the initial class counts.

**Definition 1.5 (terminal).**

$$(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{\mathit{terminal}}: \operatorname{\mathit{Fin}}\left(15\right) \to \mathit{Int})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

The 15 integer acceptance weights are zero on the leading 10 states and one on the final 5 states; HardinA229696Strip.finite_certificate pins acceptance at residual zero.

**Definition 1.6 (W).**

$$(\operatorname{\mathit{HardinA229696StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(11\right) \to \left(\operatorname{\mathit{Fin}}\left(15\right) \to \mathit{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229696: two-defect canonical HA arrays*. URL: <https://oeis.org/A229696>.

*Commentary.*

The 11 by 15 integer table appends the new sector to the first 7 cached rows of HardinA229588Strip.W, then tabulates the remaining rows. HardinA229696StripForward.forward_certificate pins its initial row, every successor row, and its polynomial relation.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229696StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233258PairTransfer.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229588Strip](../StripDefects/HardinA229588Strip.md)
