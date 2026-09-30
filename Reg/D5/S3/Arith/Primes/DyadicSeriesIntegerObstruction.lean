import D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction

open _root_.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ → ℂ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s j => (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law a := ∀ (s : ℕ → ℂ) (r : ℕ) (_hr : 1 ≤ r) (x : ℤ) (_hx : 2 < x)
    (μ : ℂ) (_hs0 : s 0 = 1)
    (_hscaled : ∀ j : ℕ, 0 < j → ∃ z : ℤ, Odd z ∧ a.readout () s j = (z : ℂ))
    (_hsupper : ∀ j : ℕ, ‖s j‖ ≤ (Real.sqrt (2 : ℝ)) ^ r * (4 : ℝ) ^ j)
    (_hsum : HasSum (fun j : ℕ => s j * (((x : ℂ) ^ 2)⁻¹) ^ j) μ)
    (_hgap : 128 * (6 : ℝ) ^ r < (x : ℝ) ^ 2 - 4),
    ∀ M : ℤ, (x : ℂ) ^ r * μ ≠ (M : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let s : ℕ → ℂ := fun j => if j = 0 then 1 else 0
  have hs0 : s 0 = 1 := by simp [s]
  have hscale : ∀ j : ℕ, 0 < j → ∃ z : ℤ, Odd z ∧ rejected.readout () s j = (z : ℂ) := by
    intro j hj
    exact ⟨1, by norm_num, by simp [rejected, realize]⟩
  have hroot : 1 ≤ Real.sqrt (2 : ℝ) := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hpos := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hupper : ∀ j : ℕ, ‖s j‖ ≤ (Real.sqrt (2 : ℝ)) ^ 1 * (4 : ℝ) ^ j := by
    intro j
    by_cases hj : j = 0
    · subst j
      simpa [s] using hroot
    · simp only [s, if_neg hj, norm_zero, pow_one]
      positivity
  have hsum : HasSum (fun j : ℕ => s j * (((100 : ℤ) : ℂ) ^ 2)⁻¹ ^ j) (1 : ℂ) := by
    convert hasSum_ite_eq (0 : ℕ) (1 : ℂ) using 1
    ext j
    by_cases hj : j = 0 <;> simp [s, hj]
  have hbad := h s 1 (by norm_num) 100 (by norm_num) 1 hs0 hscale hupper hsum
    (by norm_num) 100
  norm_num at hbad

def registration : Registration arena
    (∀ (s : ℕ → ℂ) (r : ℕ) (_hr : 1 ≤ r) (x : ℤ) (_hx : 2 < x)
      (μ : ℂ) (_hs0 : s 0 = 1)
      (_hscaled : ∀ j : ℕ, 0 < j → ∃ z : ℤ, Odd z ∧
        (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j = (z : ℂ))
      (_hsupper : ∀ j : ℕ, ‖s j‖ ≤ (Real.sqrt (2 : ℝ)) ^ r * (4 : ℝ) ^ j)
      (_hsum : HasSum (fun j : ℕ => s j * (((x : ℂ) ^ 2)⁻¹) ^ j) μ)
      (_hgap : 128 * (6 : ℝ) ^ r < (x : ℝ) ^ 2 - 4),
      ∀ M : ℤ, (x : ℂ) ^ r * μ ≠ (M : ℂ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dyadic_series_integer_obstruction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(fun _ => (1 : ℂ)), 0, 1, ?_⟩
    change (2 : ℂ) ^ (0 + padicValNat 2 (0 : ℕ).factorial) * 1 ≠
      (2 : ℂ) ^ (1 + padicValNat 2 (1 : ℕ).factorial) * 1
    norm_num

register_information_theorem
  dyadic_series_integer_obstruction
  in arena
  readout via (realize signature
    (fun _ s j => (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j)
    (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 7 }] })
  escape continues (open)

end Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
