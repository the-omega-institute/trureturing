import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Quantum.Recovery.BKMDiagonalStability

/-! Source-bound observations of diagonal BKM recovery. -/

open LeanInformationAudit Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_neg)
open _root_.D5.S3.Quantum.Recovery.BKMDiagonalStability
open _root_.D5.S3.Quantum.Recovery.BKMRelativeDensity (omega)

noncomputable section

namespace Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability

universe u

private theorem reference_trace_one :
    (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ).trace = 1 := by
  simp [Matrix.trace_one]

namespace CappedBound

open private traceNorm_eq_re_trace from D5.S3.Quantum.Recovery.BKMDiagonalStability

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Fintype n) (fun p => Matrix p.1 p.1 ℂ) (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p A => letI := p.2; traceNorm A) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 3) (fun e => nomatch e)

/-- Observe the trace norm of the reference error with the exact cap and spectral bound. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
      (a : Matrix n n ℂ) (ha : a.PosDef) (_ht : a.trace = 1),
    let X := normalizedReference a
    let T := spectralLogCondition (show X.PosDef from ha.smul (Nat.cast_pos.mpr Fintype.card_pos))
    let ε := diagonalRecoveryDefect a
    R.readout () ⟨n, inferInstance⟩ (a - (Fintype.card n : ℝ)⁻¹ • diagonalPart X) ≤
      min 2 (Real.sqrt ((12 + T ^ 2) * ε * (1 + ε)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  have hbad := h (1 : Matrix n n ℂ) Matrix.PosDef.one reference_trace_one
  dsimp [rejected, realize] at hbad
  have hle : (3 : ℝ) ≤ 2 := hbad.trans (min_le_left _ _)
  norm_num at hle

def family : Registration arena.{u} (type_of% @actual_maximal_abelian_bkm_stability.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_maximal_abelian_bkm_stability.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    let n := ULift.{u} Unit
    refine ⟨⟨n, inferInstance⟩, (0 : Matrix n n ℂ), 1, ?_⟩
    change traceNorm (0 : Matrix n n ℂ) ≠ traceNorm (1 : Matrix n n ℂ)
    rw [traceNorm_eq_re_trace Matrix.PosSemidef.zero, traceNorm_eq_re_trace Matrix.PosSemidef.one,
      Matrix.trace_zero, reference_trace_one, Complex.zero_re, Complex.one_re]
    exact zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_maximal_abelian_bkm_stability.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMDiagonalStability.actual_maximal_abelian_bkm_stability.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability.CappedBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p A => letI := p.2; traceNorm A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMDiagonalStability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CappedBound

namespace ComplexTrace

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Fintype n) (fun p => Matrix p.1 p.1 ℂ) (fun _ => ℂ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => letI := p.2; Matrix.trace M) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Observe the complex trace of the actual recovered matrix. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {a B : Matrix n n ℂ}
    (_ha : a.PosDef) (_hB : diagonalPart B = B),
    R.readout () ⟨n, inferInstance⟩ (diagonalRecovery a B) = B.trace

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  have hdiag : diagonalPart (1 : Matrix n n ℂ) = 1 := by
    simp [diagonalPart]
  have hb := h (B := (1 : Matrix n n ℂ)) Matrix.PosDef.one hdiag
  change (0 : ℂ) = (1 : Matrix n n ℂ).trace at hb
  rw [reference_trace_one] at hb
  exact zero_ne_one hb

def family : Registration arena.{u} (type_of% @diagonalRecovery_trace.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonalRecovery_trace.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    let n := ULift.{u} Unit
    refine ⟨⟨n, inferInstance⟩, (0 : Matrix n n ℂ), 1, ?_⟩
    change (0 : Matrix n n ℂ).trace ≠ (1 : Matrix n n ℂ).trace
    rw [Matrix.trace_zero, reference_trace_one]
    exact zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonalRecovery_trace.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Quantum.Recovery.BKMDiagonalStability.diagonalRecovery_trace.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability.ComplexTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p M => letI := p.2; Matrix.trace M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMDiagonalStability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ComplexTrace

namespace Positivity

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, DecidableEq n) (fun p => Matrix p.1 p.1 ℂ) (fun p => Matrix p.1 p.1 ℂ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p A => letI := p.2; diagonalPart A) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Observe the diagonal of the reference in the positivity characterization. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n] {a : Matrix n n ℂ}
      (_ha : a.PosDef) (_ht : a.trace = 1),
    (∀ B, DiagonalTest B → (diagonalRecovery a B).PosSemidef) ↔
      R.readout () ⟨n, inferInstance⟩ a = a

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  let a : Matrix n n ℂ := 1
  have ha : a.PosDef := Matrix.PosDef.one
  have ht : a.trace = 1 := reference_trace_one
  have hdiag : diagonalPart a = a := by simp [a, diagonalPart]
  exact zero_ne_one ((h ha ht).mp ((diagonalRecovery_positive_iff ha ht).mpr hdiag))

def family : Registration arena.{u} (type_of% @diagonalRecovery_positive_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonalRecovery_positive_iff.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    let n := ULift.{u} Unit
    refine ⟨⟨n, inferInstance⟩, (0 : Matrix n n ℂ), 1, ?_⟩
    change diagonalPart (0 : Matrix n n ℂ) ≠ diagonalPart 1
    simp [diagonalPart]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonalRecovery_positive_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMDiagonalStability.diagonalRecovery_positive_iff.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability.Positivity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p A => letI := p.2; diagonalPart A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMDiagonalStability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Positivity

namespace Attainment

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Fintype n) (fun p => Matrix p.1 p.1 ℂ) (fun _ => ℕ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p A => letI := p.2; A.rank) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Observe the rank of the maximizing coordinate projector. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] [Nonempty n]
      {a : Matrix n n ℂ} (_ha : a.PosDef),
    ∃ i, R.readout () ⟨n, inferInstance⟩ (coordinateProjector i) = 1 ∧
      IsGreatest {ε : ℝ | ∃ B : Matrix n n ℂ,
        DiagonalTest B ∧ negativeTrace (diagonalRecovery a B) = ε}
      (negativeTrace (diagonalRecovery a (coordinateProjector i)))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  obtain ⟨_, hr, _⟩ := h (a := (1 : Matrix n n ℂ)) Matrix.PosDef.one
  exact Nat.zero_ne_one hr

def family : Registration arena.{u} (type_of% @diagonalRecoveryDefect_isGreatest.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonalRecoveryDefect_isGreatest.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    let n := ULift.{u} Unit
    refine ⟨⟨n, inferInstance⟩, (0 : Matrix n n ℂ), 1, ?_⟩
    change (0 : Matrix n n ℂ).rank ≠ (1 : Matrix n n ℂ).rank
    simp

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonalRecoveryDefect_isGreatest.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMDiagonalStability.diagonalRecoveryDefect_isGreatest.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability.Attainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p A => letI := p.2; A.rank) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMDiagonalStability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Attainment

namespace DiagonalInverse

abbrev Parameters := Σ n : Type u, Σ _ : DecidableEq n, Matrix n n ℂ

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    Parameters.{u} (fun p => Matrix p.1 p.1 ℂ) (fun p => Matrix p.1 p.1 ℂ)

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p B => letI := p.2.1; diagonalOmegaInverse p.2.2 B)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Observe coordinate division in the inverse applied after diagonal omega. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {a B : Matrix n n ℂ}
      (_ha : a.PosDef) (_hB : diagonalPart B = B),
    omega (diagonalPart a) (diagonalOmegaInverse a B) = B ∧
      R.readout () ⟨n, inferInstance, a⟩ (omega (diagonalPart a) B) = B

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  let a : Matrix n n ℂ := 1
  have ha : a.PosDef := Matrix.PosDef.one
  have hdiag : diagonalPart a = a := by simp [a, diagonalPart]
  exact zero_ne_one (h ha hdiag).2

def family : Registration arena.{u} (type_of% @diagonalOmegaInverse_spec.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonalOmegaInverse_spec.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    let n := ULift.{u} Unit
    refine ⟨⟨n, inferInstance, 1⟩, (0 : Matrix n n ℂ), 1, ?_⟩
    change diagonalOmegaInverse (1 : Matrix n n ℂ) 0 ≠ diagonalOmegaInverse 1 1
    simp [diagonalOmegaInverse]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonalOmegaInverse_spec.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMDiagonalStability.diagonalOmegaInverse_spec.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability.DiagonalInverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p B => letI := p.2.1; diagonalOmegaInverse p.2.2 B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMDiagonalStability
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DiagonalInverse

namespace SpectralDefect

open private diagonalRecovery_isHermitian traceNorm_eq_re_trace from
  D5.S3.Quantum.Recovery.BKMDiagonalStability

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature
    (Σ n : Type u, Fintype n) (fun p => Matrix p.1 p.1 ℂ) (fun _ => ℝ)

def actual : Realization signature.{u} :=
  realize signature (fun _ p M => letI := p.2; negativeTrace M) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

/-- Observe the negative trace of the actual recovered matrix. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] {a B : Matrix n n ℂ}
      (ha : a.PosDef) (hB : DiagonalTest B),
    R.readout () ⟨n, inferInstance⟩ (diagonalRecovery a B) =
      spectralNegativeTrace (diagonalRecovery_isHermitian ha hB.2.1.isHermitian)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let n := ULift.{u} Unit
  let a : Matrix n n ℂ := 1
  have ha : a.PosDef := Matrix.PosDef.one
  have hB : DiagonalTest a :=
    ⟨by simp [a, diagonalPart], Matrix.PosSemidef.one, reference_trace_one⟩
  have hbad := h ha hB
  change (-1 : ℝ) = spectralNegativeTrace (diagonalRecovery_isHermitian ha hB.2.1.isHermitian)
    at hbad
  have hnonneg : 0 ≤ spectralNegativeTrace (diagonalRecovery_isHermitian ha hB.2.1.isHermitian) :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  linarith

def family : Registration arena.{u} (type_of% @diagonalRecovery_negativeTrace_eq_spectral.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonalRecovery_negativeTrace_eq_spectral.{u}, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro _
    let n := ULift.{u} Unit
    refine ⟨⟨n, inferInstance⟩, (0 : Matrix n n ℂ), -1, ?_⟩
    change negativeTrace (0 : Matrix n n ℂ) ≠ negativeTrace (-1)
    simp only [negativeTrace, traceNorm_neg,
      traceNorm_eq_re_trace Matrix.PosSemidef.zero, traceNorm_eq_re_trace Matrix.PosSemidef.one,
      Matrix.trace_zero, Matrix.trace_neg, reference_trace_one, Complex.zero_re,
      Complex.neg_re, Complex.one_re]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@diagonalRecovery_negativeTrace_eq_spectral.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Recovery.BKMDiagonalStability.diagonalRecovery_negativeTrace_eq_spectral.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability.SpectralDefect.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p M => letI := p.2; negativeTrace M) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.BKMDiagonalStability
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SpectralDefect

end Reg.D5.S3.Quantum.Recovery.BKMDiagonalStability
