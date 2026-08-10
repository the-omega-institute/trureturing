# Thue's Small-Representative Lemma

## Abstract

A nonzero residue modulo a prime has nonzero numerator and denominator representatives bounded by the square root.

**Theorem 1.1 (A nonzero residue has square-root-bounded numerator and denominator).**

$$\forall p\in\mathbb{N},\quad p\ \text{prime},\quad \forall x\in\mathbb{Z},\quad \neg(p \mid x) \Rightarrow \exists a,b\in\mathbb{Z},\quad a\neq0 \land b\neq0 \land \lvert a\rvert\leq\lfloor\sqrt{p}\rfloor \land \lvert b\rvert\leq\lfloor\sqrt{p}\rfloor \land a\equiv xb\ (\operatorname{mod}\ p)$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/Thue.thue_small_representatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t be the integer floor of the square root of the prime p. The (t+1)^2 pairs (u,v) with both coordinates between zero and t map to only p residues through u-xv. Two distinct pairs therefore collide. Their coordinate differences a and b satisfy a congruent to xb modulo p, and each absolute value is at most t.

Both differences are nonzero. If b were zero, the collision and the bounds below p would force a to be zero, contradicting that the two pairs differ. If a were zero, the premise that p does not divide x allows cancellation of x modulo p and forces b to be zero as well. This also records why the premise cannot be dropped: when p divides x, every bounded a congruent to xb is zero.

Library search used pinned Mathlib revision fabf563a7c95a166b8d7b6efca11c8b4dc9d911f. Exact hits were Fintype.exists_ne_map_eq_of_card_lt for the collision, Nat.lt_succ_sqrt for the square cardinality, Int.natAbs_coe_sub_coe_le_of_le for the two bounds, and ZMod.intCast_eq_intCast_iff for the final congruence. Searches of the repository and pinned Mathlib found no declaration already combining these into Thue's two-nonzero-representative statement.

The subsequent factorial application is kept as context rather than added to this theorem. There x is a factorial whose square is congruent to minus one modulo p, which in particular ensures that p does not divide x before this lemma is applied.

## References

- Truth anchor: `D5/S3/ArithUnits/Thue.thue_small_representatives`
