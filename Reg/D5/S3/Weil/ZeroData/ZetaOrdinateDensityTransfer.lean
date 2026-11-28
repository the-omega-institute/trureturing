import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer
import D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt
import Reg.Support.SingleDependentReadout

/-! Source-bound audit for the multiplicity-weighted ordinate sum. -/

namespace Reg.D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer

open Zeta23 Filter Finset
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer
open D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℂ)

private def ordinateSum (v T : ℝ) : ℂ :=
  ∑ ρ ∈ (zerosIn_finite 0 T).toFinset,
    (zeroMult ρ : ℂ) * Complex.exp (Complex.I * ((v * ρ.im : ℝ) : ℂ))

private def actual : Realization signature :=
  realize signature (fun _ v T => ordinateSum v T) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ T v A r : ℝ, 0 < r → |v| ≤ r / 4 →
    (∀ t > 0,
      (∑ ρ ∈ (zerosIn_finite 0 T).toFinset.filter (fun ρ => 1 / 2 + t ≤ ρ.re),
        (zeroMult ρ : ℝ)) ≤ A * Real.exp (-r * t)) →
    let s := (zerosIn_finite 0 T).toFinset
    ‖(∑ ρ ∈ s, (zeroMult ρ : ℂ) * Complex.exp ((v : ℂ) * (ρ - 1 / 2))) -
      R.readout () v T‖ ≤ 64 * A * (v / r) ^ 2

private theorem cutoff_zero : (zerosIn_finite 0 0).toFinset = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  have h := (Set.Finite.mem_toFinset _).mp hρ
  exact (not_lt_of_ge h.2.2) h.2.1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have htail (t : ℝ) (_ : 0 < t) :
      (∑ ρ ∈ (zerosIn_finite 0 0).toFinset.filter (fun ρ => 1 / 2 + t ≤ ρ.re),
        (zeroMult ρ : ℝ)) ≤ 0 * Real.exp (-(1 : ℝ) * t) := by
    simp [cutoff_zero]
  have hh := h 0 0 0 1 (by norm_num) (by norm_num) htail
  dsimp only at hh
  norm_num [cutoff_zero, rejected, realize] at hh

private theorem ordinateSum_zero_frequency (T : ℝ) :
    ordinateSum 0 T = (zetaZeroConfig.N 0 T : ℂ) := by
  rw [zetaZeroConfig_N, Ncount, finsum_mem_eq_finite_toFinset_sum _ (zerosIn_finite 0 T)]
  simp [ordinateSum]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  have hc : 0 < 1 / (2 * Real.pi) := by positivity
  obtain ⟨M, hM⟩ := eventually_atTop.mp (cumulative_count_asymptotic.eventually
    (eventually_gt_nhds hc))
  let T := max M 2
  have hcount := hM T (le_max_left _ _)
  have hn : zetaZeroConfig.N 0 T ≠ 0 := by
    intro he
    simp [he] at hcount
  refine ⟨0, 0, T, ?_⟩
  change ordinateSum 0 0 ≠ ordinateSum 0 T
  rw [show ordinateSum 0 0 = 0 by simp [ordinateSum, cutoff_zero], ordinateSum_zero_frequency]
  exact Ne.symm (Nat.cast_ne_zero.mpr hn)

def source_registration : Registration arena (type_of% @actual_reflection_bound_of_exponential_tail) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_reflection_bound_of_exponential_tail, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

#print axioms source_registration

private def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@actual_reflection_bound_of_exponential_tail) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer.unit
  realizationName := `Reg.D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ v T => ordinateSum v T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end

end Reg.D5.S3.Weil.ZeroData.ZetaOrdinateDensityTransfer
