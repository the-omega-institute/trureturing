import D5.S3.Quantum.Analysis.FirstDomainWeakCCR
import Reg.Support.DependentFamily
open MeasureTheory Filter Set
open scoped ENNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.FirstDomainWeakCCR
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR
abbrev H := Lp ℂ 2 (volume : Measure ℝ)
abbrev signature : Signature where
  Params := Unit
  State _ := H
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ _ u v => inner ℂ u v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (hbar : ℝ) (hhbar : 0 < hbar)
    (f g df dg : ℝ → ℂ)
    (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hdf : MemLp df 2 (volume : Measure ℝ)) (hdg : MemLp dg 2 (volume : Measure ℝ))
    (hxf : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 (volume : Measure ℝ))
    (hxg : MemLp (fun x : ℝ => (x : ℂ) * g x) 2 (volume : Measure ℝ))
    (hwf : ∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ →
      HasCompactSupport φ → (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * f x) =
      -∫ x : ℝ, (φ x : ℂ) * df x)
    (hwg : ∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ →
      HasCompactSupport φ → (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * g x) =
      -∫ x : ℝ, (φ x : ℂ) * dg x),
    R.readout (0 : Fin 3) () (hxf.toLp (fun x : ℝ => (x : ℂ) * f x))
        ((-Complex.I * (hbar : ℂ)) • hdg.toLp dg) -
      R.readout (1 : Fin 3) () ((-Complex.I * (hbar : ℂ)) • hdf.toLp df)
        (hxg.toLp (fun x : ℝ => (x : ℂ) * g x)) =
      Complex.I * (hbar : ℂ) * R.readout (2 : Fin 3) () (hf.toLp f) (hg.toLp g)

def nonzeroVector : H :=
  indicatorConstLp (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    2 measurableSet_Icc (by simp) (1 : ℂ)
theorem nonzeroVector_ne : nonzeroVector ≠ 0 := by
  have hn : ‖nonzeroVector‖ = 1 := by
    rw [nonzeroVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num [Measure.real, Real.volume_Icc]
  intro hz
  simpa [hz] using hn

def rejected (i : Fin 3) : Realization signature :=
  realize signature (fun j _ u v => inner ℂ u v + if j = i then 1 else 0) (fun e => nomatch e)
theorem actual_law : arena.Law actual := by
  intro hbar hhbar f g df dg hf hg hdf hdg hxf hxg hwf hwg
  exact first_domain_weak_ccr hbar hhbar f g df dg hf hg hdf hdg hxf hxg hwf hwg

theorem rejected_law (i : Fin 3) : ¬ arena.Law (rejected i) := by
  intro hb
  have hz : MemLp (fun _ : ℝ => (0 : ℂ)) 2 (volume : Measure ℝ) := MemLp.zero'
  have hx : MemLp (fun x : ℝ => (x : ℂ) * (0 : ℂ)) 2 (volume : Measure ℝ) := by
    simpa using hz
  have hx0 : hx.toLp (fun x : ℝ => (x : ℂ) * (0 : ℂ)) = 0 := by
    apply Lp.ext
    filter_upwards [hx.coeFn_toLp] with x h
    simpa using h
  have hbad := hb 1 (by norm_num) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) hz hz hz hz hx hx
    (by intro φ hc hs; simp) (by intro φ hc hs; simp)
  have hzero : hz.toLp (fun _ : ℝ => (0 : ℂ)) = 0 := hz.toLp_zero
  simp only [rejected, realize, hx0, hzero, smul_zero, inner_zero_left,
    inner_zero_right, Complex.ofReal_one, mul_one, zero_add, sub_zero] at hbad
  fin_cases i <;> norm_num [Fin.ext_iff, Complex.ext_iff] at hbad

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j hj
      funext p u v
      simp [rejected, actual, realize, hj]
    · intro i
      nomatch i
  dependence := by
    intro i
    refine ⟨(), (0 : H), nonzeroVector, ?_⟩
    intro he
    have hz : inner ℂ nonzeroVector nonzeroVector = 0 := by
      simpa [actual, realize] using (congrFun he nonzeroVector).symm
    exact nonzeroVector_ne (inner_self_eq_zero.mp hz)

def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S3.Quantum.Analysis.FirstDomainWeakCCR
  coordinates := #[]
  readouts := #[
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "fn"], functionOperand := true },
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn"], functionOperand := true },
    { path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "arg", "fn", "fn"], functionOperand := true }] }

register_information_theorem first_domain_weak_ccr in arena
  readout via (realize signature (fun _ _ u v => inner ℂ u v) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end Reg.D5.S3.Quantum.Analysis.FirstDomainWeakCCR
