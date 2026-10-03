# Three-Row Common-Short-Hull Square-Root Lock

## Abstract

A common short hull and linked real cubic norms lock an odd integer quotient.

**Theorem 1.1 (Positive offsets and the next odd quotient).**

$$\forall S \in \mathbb{Z}, k \in \mathbb{Z}, h \in \mathbb{R}, l \in \mathbb{R}, b \in \mathbb{R}, c \in \mathbb{R}, d \in \mathbb{R}, Q \in \mathbb{R}, P \in \mathbb{R}, e \in \mathbb{R},\; \left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\left(\operatorname{Even}(S) \land 8 \le S\right) \land \operatorname{Odd}(k)\right) \land 0 \le h\right) \land h \le S - 2\right) \land l \le 0\right) \land 0 \le l + h\right) \land l \le b\right) \land b \le l + h\right) \land l \le c\right) \land c \le l + h\right) \land l \le d\right) \land d \le l + h\right) \land 1 \le \left|b\right|\right) \land 1 \le \left|c\right|\right) \land 1 \le \left|d\right|\right) \land 0 < Q\right) \land 0 < P\right) \land Q^{2} = \left(S^{2} + b\right) \cdot \left(S^{2} + c\right) \cdot \left(S^{2} + d\right)\right) \land P^{2} = b \cdot c \cdot d\right) \land \left(e = 1 \lor e = -1\right)\right) \land Q + e \cdot P = S^{2} \cdot k\right) \Rightarrow \left(\left(\left(0 < b \land 0 < c\right) \land 0 < d\right) \land k = S + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/ShortIntervals/ThreeRowSquareRootLock.three_row_square_root_lock` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scale S and quotient k are integers. The hull endpoints, offsets, positive roots and sign e are real; e denotes epsilon. Every occurrence of S and k in a real equation uses its integer-to-real embedding; N abbreviates S squared. All three offsets belong to the same interval containing zero. Neither positivity of the offsets nor the quotient conclusion is assumed.

Two negative offsets have maximum magnitude s and positive companion r, with s+r at most h. Comparing the norm squares puts both linked root combinations strictly between N(S-1) and N(S+1), forcing k=S and contradicting parity. For positive offsets the arithmetic-geometric comparison gives Q-P>NS. The identity (NS+13N/8)^2-(N+S)^3=S^3(16S^2-23S-64)/64 and P<3N/8 give Q+P<N(S+2). Both signs therefore force k=S+1.

This uniform conditional implication does not establish the dyadic scale, complete offset kernels, odd quotient or selected sign of an original Grimm configuration. Distinct actual integer offsets, all owners and factors, Hall conditions, saturation, compositeness, exterior cofactors, the unresolved two-unit equality branch and both nonzero-K orientations remain obligations of the whole problem. A repeated-offset real nonvacuity model is not an original arithmetic instance.

## References

- Truth anchor: `D5/S3/Arith/ShortIntervals/ThreeRowSquareRootLock.three_row_square_root_lock`
