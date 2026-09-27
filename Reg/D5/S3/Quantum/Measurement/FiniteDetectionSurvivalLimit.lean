import D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
open Filter LeanInformationAudit Matrix Topology
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

universe u

@[reducible] def survivalSignature : Signature where
  Params := Σ d : ℕ, Matrix (Fin d) (Fin d) ℂ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (Fin p.1) (Fin p.1) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization survivalSignature :=
  realize survivalSignature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e)

def rejected : Realization survivalSignature :=
  realize survivalSignature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := survivalSignature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1),
    Tendsto (fun N => R.readout () ⟨d, Q⟩ N) atTop
        (𝓝 (darkProjection Q L)) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        Tendsto (fun N => (ρ * ((Qᴴ) ^ N * Q ^ N)).trace) atTop
          (𝓝 (ρ * darkProjection Q L).trace)

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp
  exact finite_detection_survival_limit Q L hcomp

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
  let L : ULift.{u} Empty → Matrix (Fin 1) (Fin 1) ℂ := fun e => nomatch e.down
  have hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by
    simp [Q]
  have hbad := (h (ι := ULift.{u} Empty) Q L hcomp).1
  have hgood := (finite_detection_survival_limit Q L hcomp).1
  have hshift : Tendsto (fun N => (Qᴴ) ^ N * Q ^ N + 1) atTop
      (𝓝 (darkProjection Q L + 1)) := hgood.add tendsto_const_nhds
  have heq : darkProjection Q L = darkProjection Q L + 1 := by
    apply tendsto_nhds_unique hbad
    simpa only [rejected, realize, survivalSignature] using hshift
  have hentry := congrFun (congrFun heq 0) 0
  simp at hentry

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence survivalSignature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0⟩, 0, 1, ?_⟩
  intro h
  have hentry := congrFun (congrFun h 0) 0
  norm_num [actual, realize, survivalSignature, Matrix.mul_apply,
    dotProduct, Fin.sum_univ_one] at hentry

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem finite_detection_survival_limit in arena
  readout via (realize survivalSignature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn", "arg", "body"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

namespace DarkBlock

abbrev signature := survivalSignature

abbrev actual := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual

abbrev rejected := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) (_hd : d ≠ 0),
    ∃ (g : ℝ) (c : ℕ → ℝ),
      0 < g ∧ g ≤ 1 ∧
      (∀ N, 0 ≤ c N) ∧
      (∀ N, c N ≤ 1) ∧
      (∀ N, c (N + d) ≤ (1 - g) * c N) ∧
      (∀ N, darkProjection Q L ≤ R.readout () ⟨d, Q⟩ N) ∧
      (∀ N, R.readout () ⟨d, Q⟩ N - darkProjection Q L =
        (1 - darkProjection Q L) * R.readout () ⟨d, Q⟩ N *
          (1 - darkProjection Q L)) ∧
      0 ≤ 1 - darkProjection Q L ∧
      (∀ N, R.readout () ⟨d, Q⟩ N - darkProjection Q L ≤
        c N • (1 - darkProjection Q L)) ∧
      (∀ N, ‖R.readout () ⟨d, Q⟩ N - darkProjection Q L‖ ≤ c N) ∧
      1 - g = c d ∧
      R.readout () ⟨d, Q⟩ d - darkProjection Q L ≤
        (1 - g) • (1 - darkProjection Q L) ∧
      (∀ n k, c (n + k * d) ≤ (1 - g) ^ k) ∧
      (∀ N, c N ≤ (1 - g) ^ (N / d)) ∧
      (∀ n k, R.readout () ⟨d, Q⟩ (n + k * d) - darkProjection Q L ≤
        (1 - g) ^ k • (1 - darkProjection Q L)) ∧
      (∀ N, R.readout () ⟨d, Q⟩ N - darkProjection Q L ≤
        (1 - g) ^ (N / d) • (1 - darkProjection Q L))

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp hd
  exact dark_block_contraction Q L hcomp hd

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
  let L : ULift.{u} Empty → Matrix (Fin 1) (Fin 1) ℂ := fun e => nomatch e.down
  have hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by simp [Q]
  obtain ⟨_g, _c, _hg, _hg1, _hc0, _hc1, _hcstep, _hP, hfactor, _hPc,
    _hcontract, _hnorm, _hgap, _hblock, _hciter, _hcquotient, _hiterated, _hquotient⟩ :=
    h Q L hcomp one_ne_zero
  have hD : darkSpace Q L = ⊤ := by
    apply top_unique
    intro v _
    simp only [darkSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro _ x
    exact nomatch x.down
  have hP : darkProjection Q L = 1 := by
    simp only [darkProjection, hD, Submodule.starProjection_top', map_one]
  have hbad := hfactor 0
  simp only [rejected,
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected,
    realize, signature, Q, pow_zero, mul_one, hP] at hbad
  have hentry := congrFun (congrFun hbad 0) 0
  norm_num [Matrix.ofNat_apply, Matrix.one_apply] at hentry

theorem sensitivity_proof : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hji
    cases i
    cases j
    exact (hji rfl).elim
  · intro i
    exact nomatch i

theorem dependence_proof : ObservationalDependence signature actual :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.dependence_proof

def registration : Registration arena.{u} (arena.{u}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity_proof
  dependence := dependence_proof

register_information_theorem dark_block_contraction in arena
  readout via (realize signature
    (fun _ p N => (p.2ᴴ) ^ N * p.2 ^ N)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "arg", "arg", "arg", "arg", "fn", "arg", "body",
        "arg"]
      stateBinder := 17 }] })
  escape continues (open)

#print axioms actual_law
#print axioms rejected_law
#print axioms sensitivity_proof
#print axioms dependence_proof

end DarkBlock

end Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
