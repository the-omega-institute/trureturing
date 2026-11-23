import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder

/-! Source-bound observation of the exact output displacement of the physical decoder. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder

open LeanInformationAudit Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FinitePreparationChannel (finite_preparation_quantum_channel)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open _root_.D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder
open UnitaryReconstruction.GibbsHiddenProcess (mix identity reset)

universe ur up uq um

local notation:max "raw" => CStarMatrix.ofMatrix.symm

private abbrev signature : Signature where
  Params := Σ _ : Type up, Type uq
  State dims := Matrix (dims.1 ⊕ dims.2) (dims.1 ⊕ dims.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ dims := Matrix (dims.1 ⊕ dims.2) (dims.1 ⊕ dims.2) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature.{up, uq} :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)

private def rejected : Realization signature.{up, uq} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law F := ∀ {R : Type ur} {P : Type up} {Q : Type uq} {M : Type um}
    [Fintype R] [DecidableEq R] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
    [Fintype M] [DecidableEq M],
    ∀ (E : QuantumChannel (P ⊕ Q) M) (D : QuantumChannel M (P ⊕ Q))
    (τ : DensityState (P ⊕ Q)) (_hτ : raw τ.1 = fromBlocks (raw τ.1).toBlocks₁₁ 0 0 0)
    (m : ℝ) (_hm : 0 < m) (_hfloor : m • (1 : Matrix P P ℂ) ≤ (raw τ.1).toBlocks₁₁)
    (_hfix : (D.comp E).mapState τ = τ)
    (K : Matrix (P ⊕ Q) (P ⊕ Q) ℂ) (_hK : K.IsHermitian) (_htr : K.trace = 0)
    (_hQQ : K.toBlocks₂₂ ≤ 0)
    (C : ℝ) (_hC : 1 + 2 * ‖K.toBlocks₁₂‖ ^ 2 / m ≤ C),
    let Z := fromBlocks (0 : Matrix P P ℂ) 0 0 (1 : Matrix Q Q ℂ) -
      (Fintype.card Q : ℝ) • raw τ.1
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (η : ℝ) (hη : 0 < η) (hη₁ : η ≤ 1), η ≤ δ →
        ∃ σ : DensityState (P ⊕ Q),
          raw σ.1 = raw τ.1 - η • K + (C * η ^ 2) • Z ∧
          let T := D.comp E
          let Dη := (mix η hη.le hη₁ (reset σ) identity).comp D
          let Tη := Dη.comp E
          F.readout () ⟨P, Q⟩ (raw τ.1 - act Tη (raw τ.1)) (η ^ 2 • K - (C * η ^ 3) • Z) ∧
          SingularJointErrorExpansion (R := R) T Tη τ σ K Z C η

private abbrev One := ULift Unit
private abbrev Zero := ULift Empty

private instance : Subsingleton (One.{up} ⊕ Zero.{uq}) where
  allEq a b := by
    rcases a with a | ⟨a⟩
    · rcases b with b | ⟨b⟩
      · exact congrArg Sum.inl (Subsingleton.elim a b)
      · exact b.elim
    · exact a.elim

private def singletonDensity : DensityState One.{um} :=
  ⟨CStarMatrix.ofMatrix 1, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv zero_le_one, by
    change (1 : Matrix One One ℂ).trace = 1
    simp [Matrix.trace]⟩

private def supportedDensity : DensityState (One.{up} ⊕ Zero.{uq}) :=
  ⟨CStarMatrix.ofMatrix 1, map_nonneg CStarMatrix.ofMatrixStarAlgEquiv zero_le_one, by
    change (1 : Matrix (One ⊕ Zero) (One ⊕ Zero) ℂ).trace = 1
    simp [Matrix.trace, Fintype.sum_sum_type]⟩

private theorem supported_density_unique (τ : DensityState (One.{up} ⊕ Zero.{uq})) :
    τ = supportedDensity := by
  apply Subtype.ext
  apply CStarMatrix.ext
  intro i j
  subst j
  have ht := τ.trace_eq_one
  letI : Unique (One.{up} ⊕ Zero.{uq}) := uniqueOfSubsingleton (Sum.inl default)
  change (∑ i : One ⊕ Zero, τ.1 i i) = 1 at ht
  have hi : i = default := Unique.eq_default i
  rw [hi]
  simpa [supportedDensity] using ht

private theorem rejected_law : ¬ arena.{ur, up, uq, um}.Law rejected := by
  intro h
  let τ : DensityState (One.{up} ⊕ Zero.{uq}) := supportedDensity
  have hs : raw τ.1 = fromBlocks (raw τ.1).toBlocks₁₁ 0 0 0 := by
    ext (i | i) (j | j)
    · rfl
    all_goals first | exact i.down.elim | exact j.down.elim
  have hf : (1 : ℝ) • (1 : Matrix One One ℂ) ≤ (raw τ.1).toBlocks₁₁ := by
    rw [one_smul]
    apply le_of_eq
    ext i j
    simp [τ, supportedDensity, Matrix.toBlocks₁₁]
  obtain ⟨E, _⟩ := finite_preparation_quantum_channel (fun _ : One.{up} ⊕ Zero.{uq} =>
    singletonDensity.{um})
  obtain ⟨D, _⟩ := finite_preparation_quantum_channel (fun _ : One.{um} => τ)
  obtain ⟨δ, hδ, hδ₁, hbound⟩ :=
    @h One.{ur} One.{up} Zero.{uq} One.{um} _ _ _ _ _ _ _ _ E D τ hs 1 zero_lt_one hf
      (supported_density_unique _) 0 Matrix.isHermitian_zero (by simp) (by rfl) 1
      (by simp [Matrix.toBlocks₁₂])
  obtain ⟨_, _, hf, _⟩ := hbound δ hδ hδ₁ le_rfl
  exact hf

private theorem dependence : ObservationalDependence signature.{up, uq} actual := by
  intro i
  refine ⟨⟨One.{up}, Zero.{uq}⟩, 0, 1, ?_⟩
  intro h
  have he : (0 : Matrix (One.{up} ⊕ Zero.{uq}) (One ⊕ Zero) ℂ) = 0 ↔ (1 : Matrix _ _ ℂ) = 0 :=
    Iff.of_eq (congrFun h 0)
  exact one_ne_zero (he.mp rfl)

def decoderShiftFamily : Registration arena.{ur, up, uq, um}
    (type_of% @singular_decoder_marginal_shift) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@singular_decoder_marginal_shift, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

set_option linter.style.longLine false in
def decoderShiftAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, _, 0, 0}
    (@singular_decoder_marginal_shift.{ur, up, uq, um}) (Realization signature.{up, uq}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder.singular_decoder_marginal_shift.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder.decoderShiftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{ur, up, uq, um}⟩
  objectArena := .source ⟨arena.{ur, up, uq, um}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{ur, up, uq, um} ⟨decoderShiftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.LocalCompression.SingularProductNoiseDecoder
