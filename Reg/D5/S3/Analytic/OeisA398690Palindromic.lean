import D5.S3.Analytic.OeisA398690Palindromic
import Reg.Support.DependentFamily

noncomputable section

namespace Reg.D5.S3.Analytic.OeisA398690Palindromic

open Polynomial
open _root_.D5.S3.Analytic.OeisA398690Palindromic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n q => simplifiedVerlinde (n + 3) q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, ∃ p : ℝ[X], p.natDegree = n ∧
    PowerSeries.mk (fun q => R.readout () n q) *
      (1 - PowerSeries.X) ^ (n + 1) = (p : PowerSeries ℝ) ∧
    ∀ j ≤ n, p.coeff j = p.coeff (n - j)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨p, hdeg, hseries, _⟩ := h 1
  have hzero : PowerSeries.mk (fun _ : ℕ => (0 : ℝ)) = 0 := by
    ext q
    simp
  have hpseries : (p : PowerSeries ℝ) = 0 := by
    change PowerSeries.mk (fun _ : ℕ => (0 : ℝ)) *
      (1 - PowerSeries.X) ^ 2 = (p : PowerSeries ℝ) at hseries
    rw [hzero, zero_mul] at hseries
    exact hseries.symm
  have hp : p = 0 := by
    exact (Polynomial.coe_injective ℝ) hpseries
  simp [hp] at hdeg

private theorem source_at_zero : simplifiedVerlinde 4 0 = 1 := by
  norm_num [simplifiedVerlinde, Finset.sum_range_succ, Real.sin_pi_div_two]

private theorem source_at_one : simplifiedVerlinde 4 1 = 3 := by
  have h3 : Real.sin (3 * Real.pi / 6) = 1 := by
    convert Real.sin_pi_div_two using 1 <;> ring
  have h5 : Real.sin (5 * Real.pi / 6) = 1 / 2 := by
    rw [show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_six]
  norm_num [simplifiedVerlinde, Finset.sum_range_succ,
    Real.sin_pi_div_six, h3, h5]

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (show j = i from @Subsingleton.elim Unit _ j i))
    · intro i
      exact nomatch i
  dependence := by
    intro i
    change ∃ p : ℕ, ∃ x y : ℕ,
      simplifiedVerlinde (p + 3) x ≠ simplifiedVerlinde (p + 3) y
    refine ⟨1, 0, 1, ?_⟩
    change simplifiedVerlinde 4 0 ≠ simplifiedVerlinde 4 1
    rw [source_at_zero, source_at_one]
    norm_num

register_information_theorem _root_.D5.S3.Analytic.OeisA398690Palindromic.result in arena
  readout via (realize signature
    (fun _ n q => simplifiedVerlinde (n + 3) q) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Analytic.OeisA398690Palindromic
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "body", "arg", "fn", "arg", "fn", "arg",
        "fn", "arg", "arg", "body"]
      stateBinder := 2 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Analytic.OeisA398690Palindromic
