import D5.S3.Quantum.Matrix.ReflectedSpectralWindow
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The finite spectral gap is a readout of the indexed frequency list. -/

noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.CentralSqrtTwoDefectGap (centralDefect)
open _root_.D5.S3.Quantum.Matrix.ReflectedSpectralWindow
open scoped Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Matrix.ReflectedSpectralWindow

private abbrev Index (n : ℕ) := Fin (2 * (n + 1) - 1 + 1)

private abbrev signature : Signature where
  Params := ℕ
  State n := Index n → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def readGap (n : ℕ) (freq : Index n → ℝ) : ℝ :=
  let : Nontrivial (Index n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  actualGap freq

private def actual : Realization signature :=
  realize signature (fun _ n freq => readGap n freq) (fun e => nomatch e)

private def zeroGap : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (freq : Index n → ℝ),
    Finset.univ.val.map freq = (centralDefect (n + 1) (by omega)).charpoly.roots →
    ∀ (τ ε : ℝ), 0 < ε →
    let δ := R.readout () n freq
    0 < δ ∧ (4 * (n + 1 : ℝ) / (ε * δ) ≤ τ →
      (1 - ε) / (2 * (n + 1 : ℝ)) <
        (∫ t in (0 : ℝ)..τ,
          ‖evolution (centralDefect (n + 1) (by omega)) t (Fin.last _) 0‖ ^ 2) / τ)

private theorem small_hermitian : (centralDefect 1 (by decide)).IsHermitian := by
  rw [_root_.Matrix.isHermitian_iff_isSymm]
  unfold centralDefect D5.S3.Quantum.Algebra.ZeitlinSixJ.Recurrence.jacobiMatrix
  simp [_root_.Matrix.IsSymm, _root_.Matrix.transpose_add, add_comm, add_left_comm]

private def sample : Index 0 → ℝ := small_hermitian.eigenvalues

private theorem sample_roots : Finset.univ.val.map sample =
    (centralDefect 1 (by decide)).charpoly.roots := by
  simpa [sample] using small_hermitian.roots_charpoly_eq_eigenvalues.symm

private theorem zeroGap_invalid : ¬ arena.Law zeroGap := by
  intro h
  have hz : (0 : ℝ) < 0 := (h 0 sample sample_roots 0 1 zero_lt_one).1
  exact (lt_irrefl 0) hz

private theorem constant_gap :
    readGap 0 (fun _ : Index 0 => (0 : ℝ)) = 0 := by
  let : Nontrivial (Index 0) := Fin.nontrivial_iff_two_le.mpr (by decide)
  unfold readGap actualGap
  have hm := (spectralDifferences (fun _ : Index 0 => (0 : ℝ))).min'_mem
    (by
      refine ⟨0, Finset.mem_image.mpr ⟨(0, 1), ?_, by simp⟩⟩
      simp)
  obtain ⟨⟨i, j⟩, _, he⟩ := Finset.mem_image.mp hm
  exact he.symm.trans (by simp)

def evidence : Registration arena (type_of% central_defect_endpoint_average) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨central_defect_endpoint_average, zeroGap, zeroGap_invalid⟩
  sensitivity := ⟨fun i => ⟨zeroGap, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, zeroGap_invalid⟩, fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨0, sample, (fun _ => 0), ?_⟩
    change readGap 0 sample ≠ readGap 0 (fun _ => 0)
    rw [constant_gap]
    exact (central_defect_endpoint_average 0 sample sample_roots 0 1 zero_lt_one).1.ne'

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      central_defect_endpoint_average (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.ReflectedSpectralWindow.central_defect_endpoint_average
  realizationName := `Reg.D5.S3.Quantum.Matrix.ReflectedSpectralWindow.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n freq => readGap n freq) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.ReflectedSpectralWindow
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Matrix.ReflectedSpectralWindow
