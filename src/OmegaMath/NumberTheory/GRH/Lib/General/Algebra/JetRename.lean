import OmegaMath.NumberTheory.GRH.Lib.General.Algebra.JetChainRule
import OmegaMath.NumberTheory.GRH.Lib.Weil.Fock.EntireTheta
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: The Fischer pairing is preserved by an injective renaming of the variables. -/

/-- The jet pairing P(∂)F(0) of a polynomial P with a power series F over a commutative ring is
unchanged when both are renamed along an injective map of variables. -/
lemma jet_rename {σ τ R} (e : σ ↪ τ) [CommRing R] {P Q} (h : .rename e P = Q) F :
    jet R Q (F.rename e) = jet R P F := h ▸ P.induction_on' (by
  simp [MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain, Finsupp.prod]) (by aesop)
