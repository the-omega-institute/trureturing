import GRH.New.Trace.GoodFormTransfer
import GRH.New.Rows.Separation
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: general results applied to the objects of this proof.

This file: Dimension of rows at most group order times degree times mass. -/

variable {P} (D : Data P)

lemma Data.decrPosition_paramW v i : decrPosition (D.paramW v) i = D.basisNumber i :=
  D.card_filter_basisNumber 0 _ (by simp [paramW_lt_iff]) (by simp)

/-- The complex dimension of the space of rows is at most |𝖦|·deg·mass_r, with 𝖦 = `Data.G`, deg the
product of the local degrees of the Bessel systems, and mass_r the mass of the genus of O_E^r. -/
lemma Data.finrank_rows_le_mass : D.rowDim ≤
  Nat.card D.G * D.filling.besselDegree * mass D.E D.r := by
  obtain ⟨⟨_, _, h⟩, A⟩ := exists_isHCParam_of_hasGap D.hasGap_signsY_paramW,
    D.classAut_eq_bot_of_le_chosenLevel (n := D.RowIndex) le_rfl D.nat_le_of_hasLogBound
  grw [D.finrank_rows_eq_finrank_goodForms ⟨_, D.nat_le_of_hasLogBound, le_rfl⟩,
    Submodule.finrank_le]
  erw [← (Space.algFormEquiv _ h _).finrank_eq, finrank_levelSpace_smoothFormRep A, Nat.cast_mul,
    card_classes_eq_classSum A, classSum_one_of_le levelOf_le_Kf, relIndex_levelOf,
    classSum_stdRatPoints_eq_mass, Module.finrank_pi, ← h.prod_formalDegree]
  simpa [Filling.besselDegree, (D.filling_fits.1 _).1, ↓card_rowIndex,
    Orbital.harish_chandra_degree_and_orbital, h.hasGap] using by linarith
