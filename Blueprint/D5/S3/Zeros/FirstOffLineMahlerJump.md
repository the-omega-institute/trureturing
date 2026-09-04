# First Off-Line Mahler Jump

## Abstract

A finite off-line root-pair filtration has a positive Mahler jump at its first height.

**Definition 1.1 (Mahler free energy).**

Lean statement: `D5/S3/Zeros/FirstOffLineMahlerJump.mahlerFreeEnergy`

*Formalization.* `D5/S3/Zeros/FirstOffLineMahlerJump.mahlerFreeEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each index represents one reflected off-line root pair, using its outer root. The free energy at cutoff T sums multiplicity times log radius over the representatives whose heights are at most T.

**Theorem 1.2 (The first Mahler jump).**

$$\begin{aligned}0 < T0, i0 \in R, h\left(i0\right) = T0,\\(\forall i \in R, T0 \leq h\left(i\right) \land 1 < r\left(i\right) \land 0 < m\left(i\right)) \Rightarrow\\(\forall T < T0, \operatorname{FreeEnergy}\left(R, h, r, m, T\right) = 0) \land 0 < \operatorname{FreeEnergy}\left(R, h, r, m, T0\right) \land\\((\forall i \in R, h\left(i\right) = T0 \Rightarrow i = i0) \Rightarrow\\\operatorname{FreeEnergy}\left(R, h, r, m, T0\right) = m\left(i0\right) \cdot \operatorname{log}\left(r\left(i0\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/FirstOffLineMahlerJump.first_off_line_mahler_jump` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite root-pair carrier makes every cutoff sum finite. A designated root at positive height T0 and the lower-bound hypothesis say that T0 is the first represented off-line height.

Every outer radius is strictly greater than one and every multiplicity is positive. Hence each active term is positive by Mathlib's log_pos lemma; these hypotheses explicitly exclude the totalized logarithm's nonpositive branch.

No term is active below T0, while the designated pair is active at T0. If it is the unique representative at that height, filtering gives a singleton and the jump is exactly its multiplicity times log radius. Counting one outer representative per reflected pair prevents an unintended factor of two.

## References

- Truth anchor: `D5/S3/Zeros/FirstOffLineMahlerJump.first_off_line_mahler_jump`
- Truth anchor: `D5/S3/Zeros/FirstOffLineMahlerJump.mahlerFreeEnergy`
