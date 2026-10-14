/- GID: D5/S3/VertexAlgebra/RelativePairing/NativePhysicalNoGhost
   generality: G
   mirror-B: none
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   proof_shape: imageForm_projection: bind-only; consumed by imageForm_noGhost
   proof_shape: imageForm_noGhost: content
   admission_basis: escape-witness
   escape_witness: Literal quotient extraction, finite transverse polynomial reconstruction,
   and ambient signature splitting are consumed together on every original physical class.
   Literature status: conditional algebraic no-ghost consequence; no novelty claim. -/

import D5.S3.VertexAlgebra.RelativePairing.NativePhysicalRealization
import D5.S3.VertexAlgebra.TransverseMetric.LorentzianSignature

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.RelativePairing.NativePhysicalNoGhost

open LatticeGeneratingFieldLocality LatticeSugawaraCurrents LatticeBcGhostBrstCharge
  OriginalQQuartetSource OriginalQPhysicalPairing OriginalQEnergyInclusionPairing
  NativePhysicalRealization NativeTransverseCoordinates
  TransverseMetric.NativePositivity LatticeOscillatorFockForm LatticeOscillatorFockMetric
open scoped TensorProduct

noncomputable section

private theorem transverseIndex_injective (D : LatticeData) (xAxis yAxis : Fin D.rank) :
    Function.Injective (transverseIndex D xAxis yAxis) := by
  rintro ⟨first, firstFrequency⟩ ⟨second, secondFrequency⟩ equality
  have components := Prod.mk.inj equality
  exact Prod.ext (Subtype.ext components.1) components.2

private def downPolynomial (D : LatticeData) (xAxis yAxis : Fin D.rank) (level : ℤ) :
    (TransverseDownIndex D xAxis yAxis level →₀ ℂ) →ₗ[ℂ]
      MvPolynomial (TransverseAxis D xAxis yAxis × ℕ) ℂ :=
  Finsupp.linearCombination ℂ (fun powers => MvPolynomial.monomial
    (powers.val.comapDomain (transverseIndex D xAxis yAxis)
      (transverseIndex_injective D xAxis yAxis).injOn) 1)

private theorem downPolynomial_reconstruction (D : LatticeData)
    (frame : Matrix (Fin D.rank) (Fin D.rank) ℂ) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ) :
    nativePolynomial D frame xAxis yAxis (downPolynomial D xAxis yAxis level coefficients) =
      transverseDownOscillator D frame xAxis yAxis level coefficients := by
  classical
  induction coefficients using Finsupp.induction_linear with
  | zero => simp [downPolynomial, transverseDownOscillator]
  | add first second firstProof secondProof =>
      simp only [map_add, firstProof, secondProof, transverseDownOscillator]
  | single powers scalar =>
      have supported : ↑powers.val.support ⊆ Set.range (transverseIndex D xAxis yAxis) := by
        rintro ⟨axis, frequency⟩ member
        have nonzero := Finsupp.mem_support_iff.mp member
        have unequalX : axis ≠ xAxis := by
          intro equality
          subst axis
          exact nonzero (powers.property.1 frequency)
        have unequalY : axis ≠ yAxis := by
          intro equality
          subst axis
          exact nonzero (powers.property.2.1 frequency)
        exact ⟨(⟨axis, unequalX, unequalY⟩, frequency), rfl⟩
      have reconstructed := Finsupp.mapDomain_comapDomain (transverseIndex D xAxis yAxis)
        (transverseIndex_injective D xAxis yAxis) powers.val supported
      simp only [downPolynomial, transverseDownOscillator, Finsupp.linearCombination_single,
        map_smul, nativePolynomial, AlgHom.comp_apply, MvPolynomial.rename_monomial,
        reconstructed]

private theorem transverseDownOscillator_nonzero (D : LatticeData)
    (frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
    (beta : Charge D) (xAxis yAxis : Fin D.rank) (level : ℤ)
    (coefficients : TransverseDownIndex D xAxis yAxis level →₀ ℂ)
    (nonzero : coefficients ≠ 0) :
    transverseDownOscillator D frame xAxis yAxis level coefficients ≠ 0 := by
  intro vanishing
  have stateZero : downState D frame beta xAxis yAxis level coefficients = 0 := by
    rw [downState_tensor, vanishing]
    simp
  have recovery := coordinates_downState D frame inverse leftFrame rightFrame
    beta xAxis yAxis level coefficients
  rw [stateZero, map_zero] at recovery
  exact nonzero recovery.symm

variable (D : LatticeData) (H frame inverse : Matrix (Fin D.rank) (Fin D.rank) ℂ)
  (leftGram : H * gramComplex D = 1) (rightGram : gramComplex D * H = 1)
  (leftFrame : inverse * frame = 1) (rightFrame : frame * inverse = 1)
  (beta : Charge D) (nullDirection : Fin D.rank → ℂ)
  (xAxis yAxis : Fin D.rank) (level : ℤ)
  (critical : D.rank = 26) (null : gramPair D nullDirection nullDirection = 0)
  (nonzero : chosenP D beta nullDirection ≠ 0) (distinct : xAxis ≠ yAxis)
  (xRow : frame xAxis = nullDirection)
  (yRow : frame yAxis = adaptedPartner D beta nullDirection)
  (xDual : ∀ row, gramPair D (frame yAxis) (frame row) = if row = xAxis then 1 else 0)
  (yDual : ∀ row, gramPair D (frame xAxis) (frame row) = if row = yAxis then 1 else 0)
  (shell : chosenH D beta + (level : ℂ) - 1 = 0)

local notation "extraction" => imageProjection D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
  xRow yRow xDual yDual shell
local notation "realization" => nativeImage D H frame inverse leftGram rightGram
  leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
  xRow yRow xDual yDual shell
local notation "literalForm" => imageForm D H beta level frame inverse leftGram rightGram
  leftFrame rightFrame nullDirection xAxis yAxis critical null nonzero distinct
  xRow yRow xDual yDual shell

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
private theorem imageProjection_nonzero (state : physicalImage D H beta level)
    (stateNonzero : state ≠ 0) : extraction state ≠ 0 := by
  intro vanishing
  let equivalence := nativePhysicalEquiv D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
    xRow yRow xDual yDual shell
  have recovered : equivalence (extraction state) = state :=
    nativeImage_imageProjection D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell state
  rw [vanishing, map_zero] at recovered
  exact stateNonzero recovered.symm

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem imageForm_projection (realRows : ∀ row column, star (frame row column) = frame row column)
    (first second : physicalImage D H beta level) :
    literalForm first second = -fockForm D
      (transverseDownOscillator D frame xAxis yAxis level (extraction first))
      (transverseDownOscillator D frame xAxis yAxis level (extraction second)) := by
  have firstRecovery := nativeImage_imageProjection D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
    xRow yRow xDual yDual shell first
  have secondRecovery := nativeImage_imageProjection D H frame inverse leftGram rightGram
    leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
    xRow yRow xDual yDual shell second
  calc
    literalForm first second = literalForm (realization (extraction first))
        (realization (extraction second)) := by rw [firstRecovery, secondRecovery]
    _ = _ := nativeImage_form D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell
      (realRows xAxis) (realRows yAxis) (extraction first) (extraction second)

include leftGram rightGram leftFrame rightFrame critical null nonzero distinct
  xRow yRow xDual yDual shell in
theorem imageForm_noGhost
    (realRows : ∀ row column, star (frame row column) = frame row column)
    (lorentzian : QuadraticForms.ActualSignature.signature (gramReal D).toQuadraticForm' =
      (D.rank : ℤ) - 2) :
    (∀ state : physicalImage D H beta level, state ≠ 0 →
      0 < (-literalForm state state).re ∧ (-literalForm state state).im = 0) ∧
    (∀ state : physicalImage D H beta level,
      (∀ other, literalForm state other = 0) ↔ state = 0) ∧
    (∀ state : physicalImage D H beta level,
      (∀ other, literalForm other state = 0) ↔ state = 0) := by
  have diagonal (state : physicalImage D H beta level) (stateNonzero : state ≠ 0) :
      0 < (-literalForm state state).re ∧ (-literalForm state state).im = 0 := by
    have coefficientNonzero := imageProjection_nonzero D H frame inverse leftGram rightGram
      leftFrame rightFrame beta nullDirection xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell state stateNonzero
    have oscillatorNonzero := transverseDownOscillator_nonzero D frame inverse leftFrame rightFrame
      beta xAxis yAxis level (extraction state) coefficientNonzero
    have reconstructed := downPolynomial_reconstruction D frame xAxis yAxis level
      (extraction state)
    have polynomialNonzero : downPolynomial D xAxis yAxis level (extraction state) ≠ 0 := by
      intro vanishing
      rw [vanishing, map_zero] at reconstructed
      exact oscillatorNonzero reconstructed.symm
    have positive := TransverseMetric.LorentzianSignature.transverseGram_posDef D frame inverse
      leftFrame rightFrame xAxis yAxis distinct realRows xDual yDual lorentzian
    have realTransverse := fun (axis : TransverseAxis D xAxis yAxis) column =>
      realRows axis.1 column
    have positiveNorm := nativePolynomial_positive D frame xAxis yAxis
      realTransverse positive
      (downPolynomial D xAxis yAxis level (extraction state)) polynomialNonzero
    have realNorm := nativePolynomial_norm_real D frame xAxis yAxis realTransverse positive
      (downPolynomial D xAxis yAxis level (extraction state))
    rw [reconstructed] at positiveNorm realNorm
    rw [imageForm_projection D H frame inverse leftGram rightGram leftFrame rightFrame
      beta nullDirection xAxis yAxis level critical null nonzero distinct
      xRow yRow xDual yDual shell
      realRows state state, neg_neg]
    exact ⟨positiveNorm, realNorm⟩
  have radicalDiagonal (state : physicalImage D H beta level) :
      literalForm state state = 0 → state = 0 := by
    intro vanishing
    by_contra stateNonzero
    have positivity := (diagonal state stateNonzero).1
    rw [vanishing] at positivity
    norm_num at positivity
  refine ⟨diagonal, ?_, ?_⟩
  · intro state
    constructor
    · intro radical
      exact radicalDiagonal state (radical state)
    · intro vanishing other
      rw [vanishing, map_zero, LinearMap.zero_apply]
  · intro state
    constructor
    · intro radical
      exact radicalDiagonal state (radical state)
    · intro vanishing other
      rw [vanishing, map_zero]

#print axioms imageForm_projection
#print axioms imageForm_noGhost

end
end D5.S3.VertexAlgebra.RelativePairing.NativePhysicalNoGhost
