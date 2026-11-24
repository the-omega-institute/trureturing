import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the physical retained population. -/

noncomputable section
universe u
open Matrix
open Complex (normSq)
open scoped BigOperators Kronecker Matrix Matrix.Norms.L2Operator
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Divergence.LogDerivTrace (logDeriv)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.D5.S3.Quantum.Matrix.SpectralPower (mpow)
open _root_.D5.S3.Quantum.Recovery.BKMFlagRefinement (partialTracePetz)
open _root_.D5.S3.Quantum.Recovery.BKMRelativeDensity (omega)
open _root_.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM

open private logMean from D5.S3.Quantum.Recovery.BKMSpectralVariance
open private diagonalReal blocks raise from D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM

namespace Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM

local notation "Λ" => logMean

private abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

private def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} [Fintype ι] [DecidableEq ι]
    (V : Matrix.unitaryGroup (Fin 2) ℂ) {p q rmin : ℝ} {g : ι → ℝ} (H : Matrix ι ι ℂ)
    (_hp : 0 < p) (_hp' : p < 1) (_hq : 0 < q) (_hq' : q < 1)
    (_hr : 0 < rmin) (_hg : ∀ i, 0 < g i) (_hnorm : ∑ i, g i = 1)
    (_hband : ∀ i j, H i j ≠ 0 → rmin ≤ frequency q g i j)
    (_hsmall : q / ((1 - q) * rmin) < 1),
    let Q := diagonalReal (population q)
    let sigma0 := reference q g
    let τ := V.val * diagonalReal (population p) * V.valᴴ
    let D := retainedDensity V p g
    let X := pencilTangent q g H
    let L := logDeriv sigma0 X
    let C := logBlock q g H
    let w := rotationWeight V
    let P := p * (1 - w) + (1 - p) * w
    let E := (L * omega D L).trace.re / 2
    (∀ i j, H i j ≠ 0 → g i / g j ≤ q / ((1 - q) * rmin)) ∧
    ((∀ i, H i i = 0) ∧ (∀ i j, H i j = 0 ∨ H j i = 0)) ∧
    X = mpow sigma0 (1 / 2) * blocks raise H * mpow sigma0 (1 / 2) ∧
    L = blocks raise C ∧
    R.readout () () (τ 0 0) = P ∧
    (∀ s : ℝ,
      let σ := sigma0 + s • X
      let S := mpow σ (1 / 2)
      let R₀ := mpow sigma0 (-(1 / 2))
      partialTraceRight σ = Q ∧ partialTracePetz σ τ = S * (R₀ * D * R₀) * S) ∧
    E = (∑ i, ∑ j, normSq (C i j) *
      ((1 - w) ^ 2 * Λ ((1 - p) * g i) (p * g j) +
        w ^ 2 * Λ (p * g i) ((1 - p) * g j) +
        w * (1 - w) * Λ (g i) (g j))) ∧
    E ≤ ∑ i, ∑ j, normSq (C i j) * (((1 - P) * g i + P * g j) / 2)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let ι := ULift.{u} (Fin 2)
  let g : ι → ℝ := fun i => if i.down = 0 then 1 / 4 else 3 / 4
  let H : Matrix ι ι ℂ := Matrix.single (ULift.up 0) (ULift.up 1) Complex.I
  have hg (i : ι) : 0 < g i := by dsimp [g]; split_ifs <;> norm_num
  have hnorm : ∑ i, g i = 1 := by
    rw [← (Equiv.ulift : ι ≃ Fin 2).symm.sum_comp g]
    norm_num [g, Fin.sum_univ_two]
  have hband (i j : ι) (hij : H i j ≠ 0) : (1 : ℝ) ≤ frequency (1 / 4) g i j := by
    by_cases hi : i = ULift.up 0
    · by_cases hj : j = ULift.up 1
      · subst i j
        norm_num [frequency, g]
      · exact (hij (by simp [H, Matrix.single, hi, Ne.symm hj])).elim
    · exact (hij (by simp [H, Matrix.single, Ne.symm hi])).elim
  have result := @h ι inferInstance inferInstance 1 (1 / 3) (1 / 4) 1 g H
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hg hnorm hband (by norm_num)
  have hP := result.2.2.2.2.1
  norm_num [rejected, realize, rotationWeight] at hP

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro h
  change (0 : ℂ).re = (1 : ℂ).re at h
  norm_num at h

def family : Registration arena.{u} (type_of% @physical_pencil_rotated_bkm.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@physical_pencil_rotated_bkm.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_pencil_rotated_bkm.{u}) (Realization signature) Unit Unit where
  unitName := (``physical_pencil_rotated_bkm).str "__information_unit"
  realizationName := `Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "arg", "arg",
        "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Recovery.NoncommutingQubit.PetzRotatedBKM
