import OmegaMath.NumberTheory.GRH.Lib.Weil.DualPair.Lift
import OmegaMath.NumberTheory.GRH.Lib.Weil.DualPair.PairReal
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! A step of the proof of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth,
rapid decay.

This file: Predicate: all theta descents with data vacuum at given places vanish. -/

/-- All descents g ↦ ∫θ(ω_{a,1}(g,h)f)Y(h)dh of Y from U(V) to U(W) vanish, for data f that are
the vacuum at the places of S ∪ S̄. -/
def DescentsVanish {E n m} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] {s t} (W :
  Space E n s) (V : Space E m t) a S Y := ∀ f, Space.projOn _ S f = f →
  Space.lift (pairThetaKer W V a 1).swap f Y = 0
