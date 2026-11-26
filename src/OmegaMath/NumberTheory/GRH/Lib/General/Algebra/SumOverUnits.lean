import OmegaMath.NumberTheory.GRH.Lib.General.NumberTheory.ClassNumberBound
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Sum over Z/N, N prime, splits as zero term plus sum over units. -/

lemma sum_eq_add_sum_units {N} [Fact N.Prime] {V} [AddCommMonoid V] (f : ZMod N → V) : ∑ c, f c =
  f 0 +
  ∑ c : _ˣ, f c.1 := by simp [Fintype.sum_eq_add_sum_subtype_ne f 0, ← unitsEquivNeZero.sum_comp]
