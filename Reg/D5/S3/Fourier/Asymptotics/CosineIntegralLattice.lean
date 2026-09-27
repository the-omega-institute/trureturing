import D5.S3.Fourier.Asymptotics.CosineIntegralGram
import Reg.Support.DependentFamily

open MeasureTheory Filter
open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice

abbrev signature : Signature where
  Params := ℝ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ z n => cosineIntegral (z * (n + 1)) ^ 2) (fun e => nomatch e)

/-- Every rejected fiber is summable. Its weighted mass is z², so no single
constant works at every positive spacing. -/
def rejected : Realization signature :=
  realize signature (fun _ z n => if n = 0 then z else 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
    Summable (fun n : ℕ => r.readout () z n) ∧
      z * (∑' n : ℕ, r.readout () z n) ≤ C

theorem rejected_summable (z : ℝ) : Summable (fun n : ℕ => rejected.readout () z n) := by
  exact (hasSum_ite_eq (0 : ℕ) z).summable

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨C, hC, h⟩
  have hb := (h (C + 1) (by linarith)).2
  simp [rejected, realize] at hb
  nlinarith [sq_nonneg C]

theorem dependence_proof : ObservationalDependence signature actual := by
  intro i
  by_contra h
  push Not at h
  obtain ⟨C, hC, hs⟩ := _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result
  have hzero (z : ℝ) (hz : 0 < z) : cosineIntegral z ^ 2 = 0 := by
    have he : (fun n : ℕ => cosineIntegral (z * (n + 1)) ^ 2) =
        fun _ : ℕ => cosineIntegral z ^ 2 := by
      funext n
      simpa [actual, realize] using h z n 0
    have ht := (hs z hz).1
    rw [he] at ht
    exact (summable_const_iff (cosineIntegral z ^ 2)).mp ht
  have he : (fun z : ℝ => cosineIntegral (1 * |z|) * cosineIntegral (1 * |z|)) =ᵐ[volume]
      fun _ => (0 : ℝ) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with z hz
    have hz0 : z ≠ 0 := by simpa using hz
    simpa [pow_two] using hzero |z| (abs_pos.mpr hz0)
  have hm := (_root_.D5.S3.Fourier.Asymptotics.CosineIntegralGram.result 1 1
    zero_lt_one zero_lt_one).2
  rw [integral_congr_ae he] at hm
  simp at hm
  exact Real.pi_ne_zero hm.symm

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := dependence_proof

register_information_theorem _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice.result in arena
  readout via (realize signature
    (fun _ z n => cosineIntegral (z * (n + 1)) ^ 2) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.CosineIntegralLattice
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "fn", "arg", "fn", "arg", "body"]
      stateBinder := 3 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CosineIntegralLattice
