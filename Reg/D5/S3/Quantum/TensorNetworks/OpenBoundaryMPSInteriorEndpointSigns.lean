import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorRootRealization
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix Filter
open scoped Matrix ComplexOrder _root_.Topology Matrix.Norms.Elementwise
set_option autoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s → ∀ (p : ℕ), 1 ≤ p →
    ∀ (P : Bond), P.PosDef → ∀ (z₀ : ℂ), z₀ ≠ 0 →
    ∃ ε R : ℝ, 0 < ε ∧ ε < ‖z₀‖ ∧ ‖z₀‖ < R ∧
      ∀ (q : ℕ) (H : Bond) (z : ℂ), ‖z‖ = ε ∨ ‖z‖ = R →
        A.readout () () (residual s p q P H z) < 0

private def witnessSector : Sector := ⟨0, 1, 2⟩
private lemma witness_regular : Regular witnessSector := by
  norm_num [Regular, witnessSector, delta, alpha, beta, Complex.normSq_apply]

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ε, R, hε, _, _, hb⟩ := h witnessSector witness_regular 1 (by omega)
    1 (by simpa using (Matrix.PosDef.one (n := Fin 2) (R := ℂ))) 1 (by norm_num)
  have hz : ‖(ε : ℂ)‖ = ε := by simp [abs_of_pos hε]
  have hh := hb 0 0 (ε : ℂ) (Or.inl hz)
  exact lt_irrefl (0 : ℝ) hh

private lemma dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def source_registration : Registration arena (type_of% @annular_residual_negative) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@annular_residual_negative, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@annular_residual_negative) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.annular_residual_negative.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


private abbrev identitySignature (T : Type) : Signature where
  Params := Unit
  State _ := T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := T
  Anchor := Empty
  finiteAnchor := inferInstance

private def identityActual (T : Type) : Realization (identitySignature T) :=
  realize (identitySignature T) (fun _ _ x => x) (fun e => nomatch e)
private def identityRejected (T : Type) [Zero T] : Realization (identitySignature T) :=
  realize (identitySignature T) (fun _ _ _ => 0) (fun e => nomatch e)
private lemma identity_dependence (T : Type) [Nontrivial T] :
    ObservationalDependence (identitySignature T) (identityActual T) := by
  intro i
  obtain ⟨x, y, hxy⟩ := exists_pair_ne T
  exact ⟨(), x, y, hxy⟩

local instance : NormedAddCommGroup Bond := Matrix.normedAddCommGroup
local instance : NormedSpace ℂ Bond := Matrix.normedSpace
local instance : IsNormableSpace ℂ Bond :=
  inferInstanceAs (IsNormableSpace ℂ (Fin 2 → Fin 2 → ℂ))


namespace BundleEquality
abbrev signature := identitySignature Bond
abbrev actual := identityActual Bond
abbrev rejected := identityRejected Bond
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector) (z : ℂ) (X : Bond), inverseDualOperator s z X =
      A.readout () () (inverseDualTransfer s z X)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp [arena, rejected, identityRejected, realize] at h
  have hfalse := congrArg (fun M : Bond => M 0 0) (h witnessSector 1 1)
  change inverseDualOperator witnessSector 1 (1 : Bond) 0 0 = 0 at hfalse
  rw [inverse_dual_operator_apply] at hfalse
  norm_num [inverseDualTransfer, witnessSector, G, alpha, beta, delta,
    Matrix.inv_def, Ring.inverse_eq_inv, adjugate_fin_two, det_fin_two,
    diagonalStarInverse, mul_apply, Fin.sum_univ_two, map_ofNat] at hfalse

def source_registration : Registration arena (type_of% @inverse_dual_operator_apply) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverse_dual_operator_apply, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := identity_dependence Bond

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@inverse_dual_operator_apply) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_apply.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.BundleEquality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end BundleEquality

namespace ZeroOperator
abbrev signature := identitySignature (Bond →L[ℂ] Bond)
abbrev actual := identityActual (Bond →L[ℂ] Bond)
abbrev rejected := identityRejected (Bond →L[ℂ] Bond)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s →
    Tendsto (fun z : ℂ => ((‖z‖ ^ 2 : ℝ) : ℂ) • inverseDualOperator s z) (𝓝[≠] 0) (𝓝 (A.readout () () (zeroLimitOperator s)))

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp [arena, rejected, identityRejected, realize] at h
  have hs : Regular witnessSector := witness_regular
  have he := tendsto_nhds_unique (h witnessSector hs) (inverse_dual_operator_zero witnessSector hs)
  have hc := congrArg (fun L : Bond →L[ℂ] Bond => L (1 : Bond) 1 1) he
  change (0 : ℂ) = ((1 : Bond) 1 1 *
    (Complex.normSq (delta witnessSector) : ℂ)⁻¹) * Mzero witnessSector 1 1 at hc
  norm_num [Mzero, diagonalStarInverse, witnessSector, delta, alpha, beta,
    Complex.normSq_apply, Matrix.zero_apply] at hc

def source_registration : Registration arena (type_of% @inverse_dual_operator_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverse_dual_operator_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := identity_dependence (Bond →L[ℂ] Bond)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@inverse_dual_operator_zero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.ZeroOperator.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end ZeroOperator

namespace InfinityOperator
abbrev signature := identitySignature (Bond →L[ℂ] Bond)
abbrev actual := identityActual (Bond →L[ℂ] Bond)
abbrev rejected := identityRejected (Bond →L[ℂ] Bond)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s →
    Tendsto (inverseDualOperator s) (Bornology.cobounded ℂ) (𝓝 (A.readout () () (infinityLimitOperator s)))

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp [arena, rejected, identityRejected, realize] at h
  have hs : Regular witnessSector := witness_regular
  have he := tendsto_nhds_unique (h witnessSector hs) (inverse_dual_operator_infinity witnessSector hs)
  have hc := congrArg (fun L : Bond →L[ℂ] Bond => L (1 : Bond) 1 1) he
  change (0 : ℂ) = ((1 : Bond) 0 0 *
    (Complex.normSq (delta witnessSector) : ℂ)⁻¹) * Minf witnessSector 1 1 at hc
  norm_num [Minf, diagonalStarInverse, witnessSector, delta, alpha, beta,
    Complex.normSq_apply, Matrix.zero_apply] at hc

def source_registration : Registration arena (type_of% @inverse_dual_operator_infinity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@inverse_dual_operator_infinity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := identity_dependence (Bond →L[ℂ] Bond)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@inverse_dual_operator_infinity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.inverse_dual_operator_infinity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.InfinityOperator.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end InfinityOperator

namespace ZeroTrial
abbrev signature := identitySignature Bond
abbrev actual := identityActual Bond
abbrev rejected := identityRejected Bond
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s → ∀ (p : ℕ), 1 ≤ p → ∀ (P : Bond),
    Tendsto (fun z : ℂ => ((‖z‖ ^ (2 * p) : ℝ) : ℂ) • trialLeft s p P z) (𝓝[≠] 0) (𝓝 (A.readout () () ((P 1 1 * (Complex.normSq (delta s) : ℂ)⁻¹ ^ p *
        (((1 + Complex.normSq s.mu : ℝ) : ℂ)⁻¹) ^ (p - 1)) • Mzero s)))

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp [arena, rejected, identityRejected, realize] at h
  have hs : Regular witnessSector := witness_regular
  have he := tendsto_nhds_unique (h witnessSector hs 1 (by omega) 1)
    (trial_left_zero witnessSector hs 1 (by omega) 1)
  have hc := congrArg (fun M : Bond => M 1 1) he
  change (0 : ℂ) = _ at hc
  norm_num [Mzero, diagonalStarInverse, witnessSector, delta, alpha, beta,
    Complex.normSq_apply, Matrix.zero_apply] at hc

def source_registration : Registration arena (type_of% @trial_left_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trial_left_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := identity_dependence Bond

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trial_left_zero) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.trial_left_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.ZeroTrial.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end ZeroTrial

namespace InfinityTrial
abbrev signature := identitySignature Bond
abbrev actual := identityActual Bond
abbrev rejected := identityRejected Bond
abbrev arena : Arena where
  signature := signature
  Law A := ∀ (s : Sector), Regular s → ∀ (p : ℕ), 1 ≤ p → ∀ (P : Bond),
    Tendsto (trialLeft s p P) (Bornology.cobounded ℂ) (𝓝 (A.readout () () ((P 0 0 * (Complex.normSq (delta s) : ℂ)⁻¹ ^ p *
        ((Complex.normSq (beta s) : ℂ) / ((1 + Complex.normSq s.lambda : ℝ) : ℂ)) ^ (p - 1)) • Minf s)))

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  dsimp [arena, rejected, identityRejected, realize] at h
  have hs : Regular witnessSector := witness_regular
  have he := tendsto_nhds_unique (h witnessSector hs 1 (by omega) 1)
    (trial_left_infinity witnessSector hs 1 (by omega) 1)
  have hc := congrArg (fun M : Bond => M 1 1) he
  change (0 : ℂ) = _ at hc
  norm_num [Minf, diagonalStarInverse, witnessSector, delta, alpha, beta,
    Complex.normSq_apply, Matrix.zero_apply] at hc

def source_registration : Registration arena (type_of% @trial_left_infinity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@trial_left_infinity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := identity_dependence Bond

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@trial_left_infinity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.trial_left_infinity.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns.InfinityTrial.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
    definition := none
    coordinates := #[]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end InfinityTrial

#print axioms registration
end
end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorEndpointSigns
