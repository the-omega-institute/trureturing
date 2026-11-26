import OmegaMath.NumberTheory.GRH.Lib.CM.Sigma.PadicSeriesDefs
import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.CuspKernel.BesselSchurBound
import OmegaMath.NumberTheory.GRH.Lib.Weil.Periods.DegreeOfT
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

This file: Index of a finite product of subgroups is the product of indices. -/

lemma index_pi_univ {I G} [Fintype I] [∀ i, Group (G i)] H :
    (@Subgroup.pi I G _ .univ H).index = ∏ i, (H i).index :=
  (Nat.card_congr (QuotientGroup.leftRel_pi H ▸ Setoid.piQuotientEquiv _) ▸ Nat.card_pi :)
