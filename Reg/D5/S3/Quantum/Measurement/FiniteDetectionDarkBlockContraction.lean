import D5.S3.Quantum.Measurement.FiniteDetectionDarkBlockContraction
import Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionDarkBlockContraction
open _root_.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkBlockContraction

universe u

abbrev signature :=
  Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.survivalSignature

abbrev actual := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.actual

abbrev rejected := Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ} {ι : Type u} [Fintype ι]
    (Q : Matrix (Fin d) (Fin d) ℂ)
    (L : ι → Matrix (Fin d) (Fin d) ℂ)
    (_hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1) (_hd : d ≠ 0),
    let D := ⨅ n : ℕ, ⨅ x : ι,
      LinearMap.ker (Matrix.toEuclideanLin (L x * Q ^ n))
    let P := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm D.starProjection
    let M := Matrix (Fin d) (Fin d) ℂ
    let S := R.readout () ⟨d, Q⟩
    let Pc := 1 - P
    let B : ℕ → Matrix (Fin d) (Fin d) ℂ := fun N => S N - P
    let leM : M → M → Prop := fun A C => A ≤ C
    let scale : ℝ → M := fun a => a • Pc
    ∃ (g : ℝ) (c : ℕ → ℝ),
      0 < g ∧ g ≤ 1 ∧
      (∀ N, 0 ≤ c N) ∧
      (∀ N, c N ≤ 1) ∧
      (∀ N, c (N + d) ≤ (1 - g) * c N) ∧
      (∀ N, leM P (S N)) ∧
      (∀ N, B N = Pc * S N * Pc) ∧
      leM 0 Pc ∧
      (∀ N, leM (B N) (scale (c N))) ∧
      (∀ N, ‖(B N : Matrix (Fin d) (Fin d) ℂ)‖ ≤ c N) ∧
      1 - g = c d ∧
      leM (B d) (scale (1 - g))

theorem actual_law : arena.{u}.Law actual := by
  intro d ι _ Q L hcomp hd
  exact dark_block_contraction Q L hcomp hd

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let Q : Matrix (Fin 1) (Fin 1) ℂ := 1
  let L : ULift.{u} Empty → Matrix (Fin 1) (Fin 1) ℂ := fun e => nomatch e.down
  have hcomp : Qᴴ * Q + ∑ x, (L x)ᴴ * L x = 1 := by simp [Q]
  obtain ⟨_g, _c, _hg, _hg1, _hc0, _hc1, _hcstep, _hP, hfactor, _hPc,
    _hcontract, _hnorm, _hgap, _hblock⟩ :=
    h Q L hcomp one_ne_zero
  have hD : darkSpace Q L = ⊤ := by
    apply top_unique
    intro v _
    simp only [darkSpace, Submodule.mem_iInf, LinearMap.mem_ker]
    intro _ x
    exact nomatch x.down
  have hP : darkProjection Q L = 1 := by
    simp only [darkProjection, hD, Submodule.starProjection_top', map_one]
  have hP_literal :
      (Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℂ)).symm
          (⨅ n : ℕ, ⨅ x : ULift.{u} Empty,
            LinearMap.ker (Matrix.toEuclideanLin (L x * Q ^ n))).starProjection = 1 := by
    change darkProjection Q L = 1
    exact hP
  have hbad := hfactor 0
  simp only [rejected,
    Reg.D5.S3.Quantum.Measurement.FiniteDetectionSurvivalLimit.rejected,
    realize, signature, Q, pow_zero, mul_one, hP_literal] at hbad
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
    owner := `D5.S3.Quantum.Measurement.FiniteDetectionDarkBlockContraction
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

end Reg.D5.S3.Quantum.Measurement.FiniteDetectionDarkBlockContraction
