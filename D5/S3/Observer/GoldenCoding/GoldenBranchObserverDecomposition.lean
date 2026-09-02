/- GID: D5/S3/Observer/GoldenCoding/GoldenBranchObserverDecomposition
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/GoldenBranchObserverDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden branch conjugation splits into trivial and sign channels. -/

import D5.S0.Conventions.InvolutionDecomposition
import D5.S3.PrimeForms.Splitting.GoldenLocalBranchClassification

/- Library-search audit trail (2026-09-01):
   * Exact repository hit `involution_even_odd_decomposition` supplies the generic
     half-sum/half-difference theorem and is applied below rather than reproved.
   * Exact repository definitions `bitFlip`, `evenBranchProjection`, and
     `oddBranchProjection` supply the concrete swap and both projectors.
   * Repository searches found no existing theorem identifying their complex ranges with
     the spans of `(1,1)` and `(1,-1)` and certifying those ranges as complements.
   * Pinned Mathlib and the other pinned Lean packages contain generic eigenspace,
     projection, span, and complement APIs, but no exact two-branch swap certificate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenCoding.GoldenBranchObserverDecomposition

open D5.S0.Conventions.InvolutionDecomposition
open D5.S3.PrimeForms.Splitting.GoldenLocalBranchClassification
open D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge

/-- The complex observation space with one coordinate for each real embedding. -/
abbrev BranchSpace := Fin 2 -> ℂ

/-- Basis vector for the expanding golden embedding. -/
def ePlus : BranchSpace := ![(1 : ℂ), 0]

/-- Basis vector for the conjugate golden embedding. -/
def eMinus : BranchSpace := ![(0 : ℂ), 1]

/-- Galois conjugation exchanges the two embedding coordinates. -/
def galoisConjugation : Module.End ℂ BranchSpace := bitFlip.mulVecLin

/-- The existing even matrix projector, regarded as a linear endomorphism. -/
def evenProjection : Module.End ℂ BranchSpace := evenBranchProjection.mulVecLin

/-- The existing odd matrix projector, regarded as a linear endomorphism. -/
def oddProjection : Module.End ℂ BranchSpace := oddBranchProjection.mulVecLin

/-- Generator of the trivial channel. -/
def evenVector : BranchSpace := ePlus + eMinus

/-- Generator of the sign channel. -/
def oddVector : BranchSpace := ePlus - eMinus

/-- The one-dimensional trivial channel. -/
def evenChannel : Submodule ℂ BranchSpace := Submodule.span ℂ {evenVector}

/-- The one-dimensional sign channel. -/
def oddChannel : Submodule ℂ BranchSpace := Submodule.span ℂ {oddVector}

/-- The coordinate hypothesis that an endomorphism exchanges the two golden branches. -/
def ExchangesBranches (J : Module.End ℂ BranchSpace) : Prop :=
  J ePlus = eMinus ∧ J eMinus = ePlus

private theorem galois_conjugation_apply (v : BranchSpace) :
    galoisConjugation v = ![v 1, v 0] := by
  ext i
  fin_cases i <;>
    simp [galoisConjugation, bitFlip, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem even_projection_apply (v : BranchSpace) :
    evenProjection v = ((v 0 + v 1) / 2) • evenVector := by
  ext i
  fin_cases i <;>
    simp [evenProjection, evenBranchProjection, evenVector, ePlus, eMinus, bitFlip,
      dotProduct, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring

private theorem odd_projection_apply (v : BranchSpace) :
    oddProjection v = ((v 0 - v 1) / 2) • oddVector := by
  ext i
  fin_cases i <;>
    simp [oddProjection, oddBranchProjection, oddVector, ePlus, eMinus, bitFlip,
      dotProduct, Fin.sum_univ_two,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring

private theorem even_projection_complex_half_sum (v : BranchSpace) :
    evenProjection v = (2 : ℂ)⁻¹ • (v + galoisConjugation v) := by
  rw [even_projection_apply, galois_conjugation_apply]
  ext i
  fin_cases i <;>
    simp [evenVector, ePlus, eMinus, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem odd_projection_complex_half_difference (v : BranchSpace) :
    oddProjection v = (2 : ℂ)⁻¹ • (v - galoisConjugation v) := by
  rw [odd_projection_apply, galois_conjugation_apply]
  ext i
  fin_cases i <;>
    simp [oddVector, ePlus, eMinus, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem even_projection_real_half_sum (v : BranchSpace) :
    evenProjection v = (2 : ℝ)⁻¹ • (v + galoisConjugation v) := by
  rw [even_projection_apply, galois_conjugation_apply]
  ext i
  fin_cases i <;>
    simp [evenVector, ePlus, eMinus, Matrix.vecHead, Matrix.vecTail] <;> ring

private theorem odd_projection_real_half_difference (v : BranchSpace) :
    oddProjection v = (2 : ℝ)⁻¹ • (v - galoisConjugation v) := by
  rw [odd_projection_apply, galois_conjugation_apply]
  ext i
  fin_cases i <;>
    simp [oddVector, ePlus, eMinus, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- The golden two-branch observation space is the direct sum of the trivial and sign
representations of Galois conjugation. The canonical even and odd projectors have exactly
the displayed one-dimensional ranges. -/
theorem golden_branch_observer_decomposition :
    galoisConjugation ePlus = eMinus ∧
      galoisConjugation eMinus = ePlus ∧
      evenProjection = (2 : ℂ)⁻¹ • (LinearMap.id + galoisConjugation) ∧
      oddProjection = (2 : ℂ)⁻¹ • (LinearMap.id - galoisConjugation) ∧
      (∀ v, v = evenProjection v + oddProjection v ∧
        galoisConjugation (evenProjection v) = evenProjection v ∧
        galoisConjugation (oddProjection v) = -oddProjection v) ∧
      LinearMap.range evenProjection = evenChannel ∧
      LinearMap.range oddProjection = oddChannel ∧
      IsCompl evenChannel oddChannel ∧
      (∀ v ∈ evenChannel, galoisConjugation v = v) ∧
      ∀ v ∈ oddChannel, galoisConjugation v = -v := by
  have hSwapPlus : galoisConjugation ePlus = eMinus := by
    rw [galois_conjugation_apply]
    ext i
    fin_cases i <;> norm_num [ePlus, eMinus]
  have hSwapMinus : galoisConjugation eMinus = ePlus := by
    rw [galois_conjugation_apply]
    ext i
    fin_cases i <;> norm_num [ePlus, eMinus]
  have hEvenMap :
      evenProjection = (2 : ℂ)⁻¹ • (LinearMap.id + galoisConjugation) := by
    apply LinearMap.ext
    intro v
    simpa using even_projection_complex_half_sum v
  have hOddMap :
      oddProjection = (2 : ℂ)⁻¹ • (LinearMap.id - galoisConjugation) := by
    apply LinearMap.ext
    intro v
    simpa using odd_projection_complex_half_difference v
  have hInvolutive :
      Function.Involutive (galoisConjugation.restrictScalars ℝ) := by
    intro v
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply,
      galois_conjugation_apply, galois_conjugation_apply]
    ext i
    fin_cases i <;> simp
  have hDecomposition :
      ∀ v, v = evenProjection v + oddProjection v ∧
        galoisConjugation (evenProjection v) = evenProjection v ∧
        galoisConjugation (oddProjection v) = -oddProjection v := by
    intro v
    have hGeneral := involution_even_odd_decomposition
      (galoisConjugation.restrictScalars ℝ) hInvolutive v
    dsimp only at hGeneral
    simp only [LinearMap.restrictScalars_apply] at hGeneral
    rw [← even_projection_real_half_sum v,
      ← odd_projection_real_half_difference v] at hGeneral
    exact hGeneral
  have hEvenRange : LinearMap.range evenProjection = evenChannel := by
    apply le_antisymm
    · rintro v ⟨x, rfl⟩
      rw [even_projection_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self evenVector)
    · refine Submodule.span_le.2 ?_
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      subst v
      refine ⟨evenVector, ?_⟩
      rw [even_projection_apply]
      ext i
      fin_cases i <;> norm_num [evenVector, ePlus, eMinus]
  have hOddRange : LinearMap.range oddProjection = oddChannel := by
    apply le_antisymm
    · rintro v ⟨x, rfl⟩
      rw [odd_projection_apply]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self oddVector)
    · refine Submodule.span_le.2 ?_
      intro v hv
      simp only [Set.mem_singleton_iff] at hv
      subst v
      refine ⟨oddVector, ?_⟩
      rw [odd_projection_apply]
      ext i
      fin_cases i <;> norm_num [oddVector, ePlus, eMinus]
  have hEvenEigen : ∀ v ∈ evenChannel, galoisConjugation v = v := by
    intro v hv
    rw [← hEvenRange] at hv
    rcases hv with ⟨x, rfl⟩
    exact (hDecomposition x).2.1
  have hOddEigen : ∀ v ∈ oddChannel, galoisConjugation v = -v := by
    intro v hv
    rw [← hOddRange] at hv
    rcases hv with ⟨x, rfl⟩
    exact (hDecomposition x).2.2
  have hComplement : IsCompl evenChannel oddChannel := by
    constructor
    · rw [Submodule.disjoint_def]
      intro v hEven hOdd
      have hFixed := hEvenEigen v hEven
      have hNegated := hOddEigen v hOdd
      apply funext
      intro i
      exact CharZero.eq_neg_self_iff.mp
        (congrFun (hFixed.symm.trans hNegated) i)
    · rw [Submodule.codisjoint_iff_exists_add_eq]
      intro v
      refine ⟨evenProjection v, oddProjection v, ?_, ?_, (hDecomposition v).1.symm⟩
      · rw [← hEvenRange]
        exact ⟨v, rfl⟩
      · rw [← hOddRange]
        exact ⟨v, rfl⟩
  exact ⟨hSwapPlus, hSwapMinus, hEvenMap, hOddMap, hDecomposition,
    hEvenRange, hOddRange, hComplement, hEvenEigen, hOddEigen⟩

-- Concrete positive probe: the canonical zero-one matrix exchanges both basis vectors.
example : ExchangesBranches galoisConjugation := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [ExchangesBranches, galoisConjugation, ePlus, eMinus, bitFlip,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- Concrete negative probe: the zero map neither exchanges the basis nor negates `(1,-1)`.
example :
    ¬ ExchangesBranches (0 : Module.End ℂ BranchSpace) ∧
      ¬ (0 : Module.End ℂ BranchSpace) oddVector = -oddVector := by
  constructor
  · intro h
    have hCoordinate := congrArg (fun v : BranchSpace => v 1) h.1
    norm_num [ExchangesBranches, ePlus, eMinus] at hCoordinate
  · intro h
    have hCoordinate := congrArg (fun v : BranchSpace => v 0) h
    norm_num [oddVector, ePlus, eMinus] at hCoordinate

#print axioms golden_branch_observer_decomposition

end D5.S3.Observer.GoldenCoding.GoldenBranchObserverDecomposition
