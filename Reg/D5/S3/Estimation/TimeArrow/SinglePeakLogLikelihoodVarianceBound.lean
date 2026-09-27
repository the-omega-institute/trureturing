import D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
import Reg.Support.DependentFamily
import LeanInformationAudit.SealCommand

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakPathCurrent
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodCovariance
open _root_.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
open LeanInformationAudit
open Lean Elab Command
open Finset Set

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound

universe u

@[reducible] def varianceSignature : Signature where
  Params := Σ X : Type u, (X → ℝ) × X × ℝ × ℝ × ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization varianceSignature.{u} :=
  realize varianceSignature.{u} (fun _ _ x => psi x) (fun e => nomatch e)

def rejected : Realization varianceSignature.{u} :=
  realize varianceSignature.{u} (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := varianceSignature.{u}
  Law R := ∀ {X : Type u} [Fintype X]
    (chi : X → ℝ) (_hchi : ∀ x, chi x = 1 ∨ chi x = -1) (z : X) (_hz : chi z = 1)
    (r q : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (M : ℕ) (_hcard : Fintype.card X = 2 * M)
    (_hplus : (univ.filter fun x => chi x = 1).card = M) (_hM : 2 ≤ M)
    (_hq : q = r / ((M : ℝ) - 1)),
    let P := kernel chi z r q (Fintype.card X)
    let k := (M : ℝ) - 1
    let I := (phi r + k * phi q) / (Fintype.card X : ℝ)
    let J := (xi r - k * xi q) / (Fintype.card X : ℝ)
    let v := (psi r + k * psi q) / (Fintype.card X : ℝ) - I ^ 2
    (∀ x, |x| < 1 → R.readout () ⟨X, chi, z, r, q, M⟩ x ≤ 2 * phi x) ∧
    J ≤ 0 ∧
    v ≤ 2 * I ∧
    0 ≤ I ∧
    ∀ s, 1 ≤ s → pathVariance P s (logLikelihoodSum chi z r q s) ≤ 2 * s * I

run_cmd do
  let root := `Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
  let sourceName := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound ++
    `uniform_single_peak_log_likelihood_variance_bound
  let identity := "sha256:2cb7a44900c444ab9d10cd7a30da5c5f0cd94639ea02e236e3ee343483ae8206"
  let row : LeanInformationAudit.SnapshotOccurrence := {
    objectArenaName := root ++ `arena
    theoremName := sourceName
    statementIdentity := identity
    registrationModuleName := root }
  LeanInformationAudit.RootCatalogs.declare {
    rootId := root, expected := #[row], source := #[row], companionPrefix := some root }

def signFour (x : Fin 4) : ℝ := if x.1 < 2 then 1 else -1

theorem signFour_cases (x : Fin 4) : signFour x = 1 ∨ signFour x = -1 := by
  by_cases hx : x.1 < 2
  · left
    simp [signFour, hx]
  · right
    simp [signFour, hx]

theorem signFour_zero : signFour 0 = 1 := by norm_num [signFour]

theorem signFour_positive_card :
    (univ.filter fun x : Fin 4 => signFour x = 1).card = 2 := by
  have hset : (univ.filter fun x : Fin 4 => signFour x = 1) = {0, 1} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    fin_cases x <;> norm_num [signFour]
  rw [hset]
  decide

theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hplusLift :
      (univ.filter fun x : ULift.{u} (Fin 4) => signFour x.down = 1).card = 2 := by
    have hfilter :
        (univ.filter fun x : ULift.{u} (Fin 4) => signFour x.down = 1) =
          (univ.filter fun x : Fin 4 => signFour x = 1).map
            (Equiv.ulift.{u, 0}.symm : Fin 4 ≃ ULift.{u} (Fin 4)).toEmbedding := by
      ext x
      simp
    rw [hfilter, Finset.card_map, signFour_positive_card]
  have hall := h (X := ULift.{u} (Fin 4)) (fun x => signFour x.down)
    (fun x => signFour_cases x.down) (ULift.up 0) signFour_zero (1 / 2) (1 / 2)
    (by norm_num) (by norm_num) 2 (by simp [Fintype.card_ulift]) hplusLift
    (by norm_num) (by norm_num)
  have hzero := hall.1 0 (by norm_num : |(0 : ℝ)| < 1)
  change (1 : ℝ) ≤ 2 * phi 0 at hzero
  norm_num [phi] at hzero

theorem actual_law : arena.{u}.Law actual.{u} := by
  intro X _ chi hchi z hz r q hr0 hr1 M hcard hplus hM hq
  exact uniform_single_peak_log_likelihood_variance_bound
    chi hchi z hz r q hr0 hr1 M hcard hplus hM hq

theorem sensitivity_proof : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence varianceSignature.{u} actual.{u} := by
  intro i
  refine ⟨⟨ULift.{u} Unit, fun _ => 1, ⟨()⟩, 0, 0, 0⟩, 0, 1, ?_⟩
  cases i
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hsquare : Real.log 2 ^ 2 ≠ 0 := pow_ne_zero 2 hlog
  norm_num [actual, realize, varianceSignature, psi]
  exact hsquare.symm

def registration : Registration arena.{u} (arena.{u}.Law actual.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem uniform_single_peak_log_likelihood_variance_bound in arena
  readout via (realize varianceSignature.{u} (fun _ _ x => psi x) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
    coordinates := #[0, 2, 4, 6, 7, 10]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "body", "body", "fn", "arg"]
      stateBinder := 15 }] })
  escape continues (open)

#print axioms rejected_law
#print axioms actual_law
#print axioms sensitivity_proof
#print axioms dependence_proof

run_cmd LeanInformationAudit.validateRegistrySnapshot (← getEnv)

end Reg.D5.S3.Estimation.TimeArrow.SinglePeakLogLikelihoodVarianceBound
