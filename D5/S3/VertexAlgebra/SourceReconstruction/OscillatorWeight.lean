/- GID: D5/S3/VertexAlgebra/SourceReconstruction/OscillatorWeight
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceReconstruction/OscillatorWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Algebraic weighted-degree bounds for the original source current modes. -/

import D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWords

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents OscillatorWords
open LatticeHalfFockFiniteCorrection LatticeHalfFockAllStateField MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

theorem polynomial_smul_weight_le (D : LatticeData) (scalar : ℂ)
    (polynomial : Oscillator D) :
    weightedTotalDegree (sourceWeight D) (scalar • polynomial) ≤
      weightedTotalDegree (sourceWeight D) polynomial := by
  classical
  apply Finset.sup_le
  intro exponent member
  exact le_weightedTotalDegree _ (support_smul member)

theorem polynomial_sum_weight_le (D : LatticeData) {Label : Type*}
    (labels : Finset Label) (polynomial : Label → Oscillator D) (bound : ℕ)
    (bounded : ∀ label ∈ labels, weightedTotalDegree (sourceWeight D) (polynomial label) ≤ bound) :
    weightedTotalDegree (sourceWeight D) (∑ label ∈ labels, polynomial label) ≤ bound := by
  classical
  apply Finset.sup_le
  intro exponent member
  obtain ⟨label, labelMember, exponentMember⟩ := Finset.mem_biUnion.mp (support_sum member)
  exact (le_weightedTotalDegree _ exponentMember).trans (bounded label labelMember)

theorem polynomial_X_weight_le (D : LatticeData) (index : Index D)
    (polynomial : Oscillator D) :
    weightedTotalDegree (sourceWeight D) (X index * polynomial) ≤
      weightedTotalDegree (sourceWeight D) polynomial + sourceWeight D index := by
  classical
  apply Finset.sup_le
  intro exponent member
  rw [support_X_mul] at member
  obtain ⟨previous, previousMember, rfl⟩ := Finset.mem_map.mp member
  change Finsupp.weight (sourceWeight D) (Finsupp.single index 1 + previous) ≤ _
  simp only [map_add, Finsupp.weight_single, one_smul]
  have bounded := le_weightedTotalDegree (sourceWeight D) previousMember
  omega

theorem polynomial_pderiv_weight_le (D : LatticeData) (index : Index D)
    (polynomial : Oscillator D) :
    weightedTotalDegree (sourceWeight D) (pderiv index polynomial) ≤
      weightedTotalDegree (sourceWeight D) polynomial := by
  classical
  apply Finset.sup_le
  intro exponent member
  have shifted : exponent + Finsupp.single index 1 ∈ polynomial.support := by
    rw [mem_support_iff]
    intro zero
    have nonzero := mem_support_iff.mp member
    exact nonzero (by simp [coeff_pderiv, zero])
  have bounded := le_weightedTotalDegree (sourceWeight D) shifted
  simp only [map_add, Finsupp.weight_single, one_smul] at bounded
  omega

theorem polynomial_current_nonnegative_weight_le (D : LatticeData)
    (colour : Fin D.rank) (charge : Charge D) (mode : ℤ) (nonnegative : 0 ≤ mode)
    (polynomial : Oscillator D) :
    weightedTotalDegree (sourceWeight D) (neutralPolynomialMode D colour charge mode polynomial) ≤
      weightedTotalDegree (sourceWeight D) polynomial := by
  classical
  unfold neutralPolynomialMode
  rw [if_neg (not_lt.mpr nonnegative)]
  split_ifs with zero
  · simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
      polynomial_smul_weight_le D (bilinear D (unitCharge D colour) charge : ℂ) polynomial
  · simp only [LinearMap.smul_apply, LinearMap.sum_apply, Derivation.coeFn_coe]
    apply (polynomial_smul_weight_le D _ _).trans
    apply polynomial_sum_weight_le
    intro other member
    exact (polynomial_smul_weight_le D _ _).trans
      (polynomial_pderiv_weight_le D _ polynomial)

theorem polynomial_correction_weight_lt (D : LatticeData) (colour : Fin D.rank)
    (charge : Charge D) (degree offset : ℕ) (polynomial : Oscillator D) :
    weightedTotalDegree (sourceWeight D)
        (neutralPolynomialMode D colour charge (-(degree : ℤ) + offset) polynomial) <
      weightedTotalDegree (sourceWeight D) polynomial + degree + 1 := by
  by_cases negative : -(degree : ℤ) + offset < 0
  · rw [neutralPolynomialMode, if_pos negative]
    change weightedTotalDegree (sourceWeight D)
      (X (colour, (-(-(degree : ℤ) + offset) - 1).toNat) * polynomial) < _
    have bounded := polynomial_X_weight_le D
      (colour, (-(-(degree : ℤ) + offset) - 1).toNat) polynomial
    have cast := Int.toNat_of_nonneg
      (show 0 ≤ -(-(degree : ℤ) + offset) - 1 by omega)
    change weightedTotalDegree (sourceWeight D)
      (X (colour, (-(-(degree : ℤ) + offset) - 1).toNat) * polynomial) ≤
      weightedTotalDegree (sourceWeight D) polynomial +
        ((-(-(degree : ℤ) + offset) - 1).toNat + 1) at bounded
    omega
  · have bounded := polynomial_current_nonnegative_weight_le D colour charge
      (-(degree : ℤ) + offset) (by omega) polynomial
    omega

theorem current_charge_component (D : LatticeData) (colour : Fin D.rank) (mode : ℤ)
    (state : Carrier D) (charge : Charge D) :
    (((unitCurrent D colour)[[mode]]) state) charge =
      neutralPolynomialMode D colour charge mode (state charge) := by
  classical
  rw [unitCurrent_mode, neutralMode, Finsupp.lsum_apply]
  simp only [Finsupp.sum, LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single charge]
  · simp
  · intro other member different
    simp [Finsupp.single_apply, different, Ne.symm different]
  · intro absent
    simp [Finsupp.notMem_support_iff.mp absent]

theorem correction_source_weight_lt (D : LatticeData) (colour : Fin D.rank)
    (degree offset : ℕ) (state : Carrier D) :
    sourceWeightBound D (((unitCurrent D colour)[[-(degree : ℤ) + offset]]) state) <
      sourceWeightBound D state + degree + 1 := by
  classical
  let output := (((unitCurrent D colour)[[-(degree : ℤ) + offset]]) state)
  have positive : 0 < sourceWeightBound D state + degree + 1 := by omega
  apply Finset.sup_lt_iff positive |>.mpr
  intro charge member
  change weightedTotalDegree (sourceWeight D) (output charge) < _
  have sourceMember : charge ∈ state.support := by
    rw [Finsupp.mem_support_iff] at member ⊢
    intro zero
    exact member (by simp [output, current_charge_component, zero])
  have bounded := Finset.le_sup
    (f := fun charge => weightedTotalDegree (sourceWeight D) (state charge)) sourceMember
  rw [show output charge = neutralPolynomialMode D colour charge
    (-(degree : ℤ) + offset) (state charge) by exact current_charge_component D colour _ state charge]
  exact (polynomial_correction_weight_lt D colour charge degree offset (state charge)).trans_le
    (Nat.add_le_add_right (Nat.add_le_add_right bounded degree) 1)

theorem single_source_weight (D : LatticeData) (charge : Charge D)
    (polynomial : Oscillator D) :
    sourceWeightBound D (Finsupp.single charge polynomial) =
      weightedTotalDegree (sourceWeight D) polynomial := by
  classical
  by_cases zero : polynomial = 0
  · simp [sourceWeightBound, zero, weightedTotalDegree_zero]
  · simp [sourceWeightBound, Finsupp.support_single_ne_zero charge zero]

theorem oscillatorWord_weight_le (D : LatticeData) (charge : Charge D)
    (word : List (Index D)) :
    sourceWeightBound D (oscillatorWord D charge word) ≤ wordWeight D word := by
  rw [oscillatorWord_eq, single_source_weight]
  induction word with
  | nil => simp [wordWeight, weightedTotalDegree, support_one]
  | cons index tail inductionHypothesis =>
    have bounded := polynomial_X_weight_le D index
      ((tail.map (fun index => (X index : Oscillator D))).prod)
    have total := bounded.trans (Nat.add_le_add_right inductionHypothesis (sourceWeight D index))
    simpa [wordWeight, Nat.add_comm] using total

theorem occurrence_weight_le (D : LatticeData) (state : Carrier D) (charge : Charge D)
    (chargeMember : charge ∈ state.support) (exponent : Index D →₀ ℕ)
    (exponentMember : exponent ∈ (state charge).support) :
    wordWeight D (LatticeAllStateField.occurrences D exponent) ≤ sourceWeightBound D state := by
  have identity : wordWeight D (LatticeAllStateField.occurrences D exponent) =
      Finsupp.weight (sourceWeight D) exponent := by
    run_tac
      let supplier := (Lean.Name.num
        `_private.D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection 0).append
        `D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection.wordWeight_occurrences
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact ($(Lean.mkIdent supplier)) _ _))
  rw [identity]
  exact (le_weightedTotalDegree _ exponentMember).trans
    (Finset.le_sup (f := fun charge =>
      weightedTotalDegree (sourceWeight D) (state charge)) chargeMember)

end
end D5.S3.VertexAlgebra.SourceReconstruction.OscillatorWeight
