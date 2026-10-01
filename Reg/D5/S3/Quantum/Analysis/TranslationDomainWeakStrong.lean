import D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
import Reg.Support.DependentFamily
open MeasureTheory Filter Set DomAddAct
open scoped ENNReal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
abbrev H := Lp ℂ 2 (volume : Measure ℝ)
abbrev signature : Signature where
  Params := ℝ
  State _ := H
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := H
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature :=
  realize signature (fun _ t u => DomAddAct.mk t +ᵥ u) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (f h : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ))
      (hh : MemLp h 2 (volume : Measure ℝ)),
    (∀ φ : ℝ → ℝ, ContDiff ℝ (WithTop.some (⊤ : ℕ∞)) φ → HasCompactSupport φ →
      (∫ x : ℝ, ((deriv φ x : ℝ) : ℂ) * f x) = -∫ x : ℝ, (φ x : ℂ) * h x) ↔
    HasDerivAt (fun t : ℝ => R.readout () t (hf.toLp f)) (hh.toLp h) 0
-- An actual whole-family intervention changes the translation readout at every input.
def nonzeroVector : H :=
  indicatorConstLp (μ := (volume : Measure ℝ)) (s := Set.Icc (0 : ℝ) 1)
    2 measurableSet_Icc (by simp) (1 : ℂ)
theorem nonzeroVector_ne : nonzeroVector ≠ 0 := by
  have hn : ‖nonzeroVector‖ = 1 := by
    rw [nonzeroVector, norm_indicatorConstLp (by norm_num) (by norm_num)]
    norm_num [Measure.real, Real.volume_Icc]
  intro hz
  simpa [hz] using hn
def rejected : Realization signature :=
  realize signature (fun _ t _ => t • nonzeroVector) (fun e => nomatch e)
theorem actual_law : arena.Law actual := by
  intro f h hf hh
  exact translation_domain_iff f h hf hh
theorem rejected_law : ¬ arena.Law rejected := by
  intro hb
  have hz : MemLp (fun _ : ℝ => (0 : ℂ)) 2 (volume : Measure ℝ) := MemLp.zero'
  have hd := (hb (fun _ => 0) (fun _ => 0) hz hz).mp (by intro φ hc hs; simp)
  have hd' : HasDerivAt (fun t : ℝ => t • nonzeroVector) nonzeroVector 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const nonzeroVector
  have he := hd'.unique hd
  have hzero : hz.toLp (fun _ : ℝ => (0 : ℂ)) = 0 := hz.toLp_zero
  exact nonzeroVector_ne (by simpa [rejected, realize, hzero] using he)
def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(0 : ℝ), (0 : H), nonzeroVector, ?_⟩
    intro he
    exact nonzeroVector_ne (by simpa [actual, realize] using he.symm)
def selection : LeanInformationAudit.SourceSelection := {
  owner := `D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
  coordinates := #[4]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg", "fn", "fn", "arg", "body"]
    stateOperand := some #["arg"] }] }

register_information_theorem translation_domain_iff in arena
  readout via (realize signature (fun _ t u => DomAddAct.mk t +ᵥ u) (fun e => nomatch e))
  realizes registration
  escape from source (selection)
  escape continues (open)

end Reg.D5.S3.Quantum.Analysis.TranslationDomainWeakStrong
