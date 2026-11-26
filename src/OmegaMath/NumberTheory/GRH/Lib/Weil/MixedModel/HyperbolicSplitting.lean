import OmegaMath.NumberTheory.GRH.Lib.Weil.MixedModel.ZeroTermLaw
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Standard polarisation of the hyperbolic space as a splitting. -/

/-- The splitting of hyperbolic space of rank 2p over the zero space, with l the first p and k
the last p basis vectors. -/
noncomputable def hyperbolicSplitting E p [Field E] [CMType E] [WeilData E] [Fintype p] :
  (hypSpace E p).Splitting (stdSpace E Empty)
  p := by use .fromRows 0 1, .fromRows 1 0, 0 <;> first | (ext ⟨⟩; done) | simp +arith
