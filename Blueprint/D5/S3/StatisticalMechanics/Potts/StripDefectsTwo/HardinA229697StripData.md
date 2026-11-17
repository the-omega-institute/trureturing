# Two-defect HA strips

## Abstract

Exact two-defect sheared square-lattice strip counts.

**Definition 1.1 (Valid).**

$$\forall p: \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \mathit{Nat}, ((\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{Valid}}\left(p, d\right)) \iff (d \le 2)))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.Valid` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

Residual budgets are at most two.

**Definition 1.2 (cl).**

$$\forall p: \operatorname{\mathit{Fin}}\left(4\right) \to \operatorname{\mathit{Fin}}\left(3\right), (\forall d: \mathit{Nat}, (\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{cl}}\left(p, d\right) = (\operatorname{\mathit{if}} (0 < d) \operatorname{\mathit{then}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{castAdd}}\left(14, \operatorname{\mathit{HardinA229589StripData}}.\operatorname{\mathit{cl}}\left(p, d - 1\right)\right): \operatorname{\mathit{Fin}}\left(42\right)) \operatorname{\mathit{else}} (\operatorname{\mathit{Fin}}.\operatorname{\mathit{natAdd}}\left(28, \operatorname{\mathit{HardinA233177PairTransfer}}.\operatorname{\mathit{cls}}\left((p\left((0: \operatorname{\mathit{Fin}}\left(4\right))\right), p\left((1: \operatorname{\mathit{Fin}}\left(4\right))\right), p\left((2: \operatorname{\mathit{Fin}}\left(4\right))\right), p\left((3: \operatorname{\mathit{Fin}}\left(4\right))\right))\right)\right): \operatorname{\mathit{Fin}}\left(42\right)))))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.cl` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

Positive budgets call the frozen one-defect classifier at d minus one. Zero budget selects the appended equality sector.

**Definition 1.3 (T).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{T}: \operatorname{\mathit{Matrix}}\left(\operatorname{\mathit{Fin}}\left(42\right), \operatorname{\mathit{Fin}}\left(42\right), \mathit{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.T` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 42 by 42 integer matrix retains HardinA229589StripData.T in its leading 28 by 28 block. The added block records cost two and the inherited cost-one block; its diagonal is the frozen zero-temperature Q. The HardinA229697Strip.finite_certificate theorem pins every transition sum.

**Definition 1.4 (initial).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{initial}}: \operatorname{\mathit{Fin}}\left(42\right) \to \mathit{Int})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.initial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 42 integer initial weights append 14 zero entries to the frozen initial vector; HardinA229697Strip.finite_certificate pins the initial class counts.

**Definition 1.5 (terminal).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{\mathit{terminal}}: \operatorname{\mathit{Fin}}\left(42\right) \to \mathit{Int})$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.terminal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 42 integer acceptance weights are zero on the leading 28 states and one on the final 14 states; HardinA229697Strip.finite_certificate pins acceptance at residual zero.

**Definition 1.6 (W).**

$$(\operatorname{\mathit{HardinA229697StripData}}.\operatorname{W}: \operatorname{\mathit{Fin}}\left(18\right) \to \left(\operatorname{\mathit{Fin}}\left(42\right) \to \mathit{Int}\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.W` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* R. H. Hardin; OEIS Foundation Inc. (2013). *OEIS A229697: two-defect canonical HA arrays*. URL: <https://oeis.org/A229697>.

*Commentary.*

The 18 by 42 integer table appends the new sector to the first 13 cached rows of HardinA229589StripData.W, then tabulates the remaining rows. HardinA229697StripForward.forward_certificate pins its initial row, every successor row, and its polynomial relation.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.T`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.Valid`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.W`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.cl`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.initial`
- Truth anchor: `D5/S3/StatisticalMechanics/Potts/StripDefectsTwo/HardinA229697StripData.terminal`
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer](../../../Combinatorics/TraceAvoidingArrays/HardinA233177PairTransfer.md)
- Dependency: [D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore](../../../Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferCore.md)
- Dependency: [D5/S3/StatisticalMechanics/Potts/StripDefects/HardinA229589StripData](../StripDefects/HardinA229589StripData.md)
