/- GID: D5/S3/VertexAlgebra/SourceReconstruction/SourceEvaluator
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceReconstruction/SourceEvaluator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite original two-word mode evaluation from charged grounds and actual current recurrences. -/

import D5.S3.VertexAlgebra.SourceReconstruction.CurrentRecurrences

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace D5.S3.VertexAlgebra.SourceReconstruction.SourceEvaluator

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents
open LatticeAllStateField LatticeAllStateReconstruction
open LatticeHalfFockAllStateCurrentCommutator OscillatorWords CurrentRecurrences MvPolynomial
open scoped BigOperators VertexOperator

noncomputable section

def groundWord (D : LatticeData) (charge targetCharge : Charge D) :
    List (Index D) → ℤ → Carrier D
  | [], mode => ((actualField D charge)[[mode]]) (Finsupp.single targetCharge 1)
  | index :: tail, mode =>
    ((unitCurrent D index.1)[[-(index.2 : ℤ) - 1]]) (groundWord D charge targetCharge tail mode) -
      (bilinear D (unitCharge D index.1) charge : ℂ) •
        groundWord D charge targetCharge tail (mode - index.2 - 1)

theorem groundWord_agrees (D : LatticeData) (charge targetCharge : Charge D)
    (word : List (Index D)) (mode : ℤ) :
    groundWord D charge targetCharge word mode =
      mu D (Finsupp.single charge 1) mode (oscillatorWord D targetCharge word) := by
  induction word generalizing mode with
  | nil =>
    change ((actualField D charge)[[mode]]) (Finsupp.single targetCharge 1) =
      ((Y D (Finsupp.single charge 1))[[mode]]) (Finsupp.single targetCharge 1)
    rw [stateField_ground]
  | cons index tail inductionHypothesis =>
    rw [groundWord, oscillatorWord, source_charged_commutation,
      inductionHypothesis, inductionHypothesis]

def groundState (D : LatticeData) (charge : Charge D) (mode : ℤ) (target : Carrier D) : Carrier D :=
  ∑ targetCharge ∈ target.support,
    ∑ monomial ∈ ((basisMonomials (Index D) ℂ).repr (target targetCharge)).support,
      ((basisMonomials (Index D) ℂ).repr (target targetCharge) monomial) •
        groundWord D charge targetCharge (occurrences D monomial) mode

theorem groundState_agrees (D : LatticeData) (charge : Charge D)
    (mode : ℤ) (target : Carrier D) :
    groundState D charge mode target = mu D (Finsupp.single charge 1) mode target := by
  have expansion := congrArg ((Y D (Finsupp.single charge 1))[[mode]])
    (finite_source_expansion D target)
  simp only [map_sum, map_smul] at expansion
  unfold groundState
  simp only [groundWord_agrees]
  exact expansion.symm

def insertionCutoff (D : LatticeData) (source target : Carrier D) (mode : ℤ) : ℕ :=
  max ((-((HahnModule.of ℂ).symm (Y D source target)).order - mode).toNat + 1)
    (vectorFrequencyBound D target + 1)

theorem insertion_terms_vanish (D : LatticeData) (colour : Fin D.rank) (degree : ℕ)
    (mode : ℤ) (source target : Carrier D) (offset : ℕ)
    (outside : insertionCutoff D source target mode ≤ offset) :
    insertionFirst D colour degree mode source target offset = 0 ∧
      insertionSecond D colour degree mode source target offset = 0 := by
  unfold insertionCutoff at outside
  have first : mu D source (mode + offset) target = 0 := by
    apply VertexOperator.ncoeff_eq_zero_of_lt_order
    omega
  have second : ((unitCurrent D colour)[[(offset : ℤ)]]) target = 0 :=
    sourceCurrent_upper_truncation D (Pi.single colour 1) target _ (by omega)
  constructor
  · unfold insertionFirst
    rw [first, map_zero]
  · unfold insertionSecond
    rw [second]
    simp [mu]

theorem source_insertion_finite (D : LatticeData) (colour : Fin D.rank) (degree : ℕ)
    (mode : ℤ) (source target : Carrier D) :
    mu D (((unitCurrent D colour)[[-(degree : ℤ) - 1]]) source) mode target =
      ∑ offset ∈ Finset.range (insertionCutoff D source target mode),
        ((degree + offset).choose degree : ℂ) •
          (insertionFirst D colour degree mode source target offset +
            (-1 : ℂ) ^ degree • insertionSecond D colour degree mode source target offset) := by
  rw [source_insertion]
  apply finsum_eq_sum_of_support_subset
  intro offset nonzero
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra outside
  obtain ⟨first, second⟩ := insertion_terms_vanish D colour degree mode source target offset (by omega)
  exact nonzero (by simp [first, second])

def sourceWord (D : LatticeData) (charge : Charge D) :
    List (Index D) → ℤ → Carrier D → Carrier D
  | [], mode, target => groundState D charge mode target
  | index :: tail, mode, target =>
    ∑ offset ∈ Finset.range (insertionCutoff D (oscillatorWord D charge tail) target mode),
      ((index.2 + offset).choose index.2 : ℂ) •
        (((unitCurrent D index.1)[[-(index.2 : ℤ) - 1 - offset]])
          (sourceWord D charge tail (mode + offset) target) +
          (-1 : ℂ) ^ index.2 • sourceWord D charge tail (mode - index.2 - 1 - offset)
            (((unitCurrent D index.1)[[(offset : ℤ)]]) target))

theorem sourceWord_agrees (D : LatticeData) (charge : Charge D)
    (word : List (Index D)) (mode : ℤ) (target : Carrier D) :
    sourceWord D charge word mode target = mu D (oscillatorWord D charge word) mode target := by
  induction word generalizing mode target with
  | nil => exact groundState_agrees D charge mode target
  | cons index tail inductionHypothesis =>
    rw [oscillatorWord, source_insertion_finite]
    simp only [sourceWord, inductionHypothesis, insertionFirst, insertionSecond]

def evaluate (D : LatticeData) (source : Carrier D) (mode : ℤ) (target : Carrier D) : Carrier D :=
  ∑ charge ∈ source.support,
    ∑ monomial ∈ ((basisMonomials (Index D) ℂ).repr (source charge)).support,
      ((basisMonomials (Index D) ℂ).repr (source charge) monomial) •
        sourceWord D charge (occurrences D monomial) mode target

private def sourceEvaluation (D : LatticeData) (mode : ℤ) (target : Carrier D) :
    Carrier D →ₗ[ℂ] Carrier D where
  toFun source := mu D source mode target
  map_add' first second := by simp [mu]
  map_smul' scalar source := by simp [mu]

theorem evaluate_agrees (D : LatticeData) (source : Carrier D) (mode : ℤ) (target : Carrier D) :
    evaluate D source mode target = mu D source mode target := by
  have expansion := congrArg (sourceEvaluation D mode target) (finite_source_expansion D source)
  simp only [map_sum, map_smul] at expansion
  unfold evaluate
  simp only [sourceWord_agrees]
  exact expansion.symm

end
end D5.S3.VertexAlgebra.SourceReconstruction.SourceEvaluator
