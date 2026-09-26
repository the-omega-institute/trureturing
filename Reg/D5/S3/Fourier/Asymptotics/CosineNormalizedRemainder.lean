import D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
import Reg.Support.DependentFamily

open _root_.D5.S3.Fourier.Asymptotics.CosineIntegralLattice (cosineIntegral)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder

abbrev signature : Signature where
  Params := Σ _ : ℝ, ℕ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p k => Real.cos ((k : ℝ) * p.1) / (k : ℝ))
    (fun e => nomatch e)

/-- A perturbation of the literal summand with unbounded total error N².
A bounded perturbation alone would not contradict the uniform existential constant. -/
def rejected : Realization signature :=
  realize signature (fun _ p k => Real.cos ((k : ℝ) * p.1) / (k : ℝ) +
    if k = 1 then (p.2 : ℝ) ^ 2 else 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∃ C : ℝ, 0 < C ∧ ∀ θ : ℝ, 0 < θ → θ ≤ 1 → ∀ N : ℕ, 1 ≤ N →
    |(∑ k ∈ Finset.Icc 1 N, r.readout () ⟨θ, N⟩ k) -
      (-Real.log θ + cosineIntegral ((N : ℝ) * θ))| ≤
      C * (1 / (N : ℝ) + θ * (1 + max 0 (Real.log ((N : ℝ) * θ))))

theorem rejected_sum (θ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, rejected.readout () ⟨θ, N⟩ k) =
      (∑ k ∈ Finset.Icc 1 N, Real.cos ((k : ℝ) * θ) / (k : ℝ)) + (N : ℝ) ^ 2 := by
  simp [rejected, realize, Finset.sum_add_distrib, hN]

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨C, hC, h⟩
  obtain ⟨K, hK, hactual⟩ :=
    _root_.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (C + K) + 1)
  have hn1 : (1 : ℝ) < N := by linarith
  have hn : 1 ≤ N := by exact_mod_cast hn1.le
  have hn0 : (0 : ℝ) < N := by linarith
  have hbad := h 1 zero_lt_one le_rfl N hn
  have hgood := hactual 1 zero_lt_one le_rfl N hn
  rw [rejected_sum 1 N hn] at hbad
  simp only [Real.log_one, neg_zero, zero_add, mul_one, one_mul] at hbad hgood
  have he : (N : ℝ) ^ 2 ≤
      (C + K) * (1 / (N : ℝ) + (1 + max 0 (Real.log (N : ℝ)))) := by
    have hb := (abs_le.mp hbad).2
    have hg := (abs_le.mp hgood).1
    nlinarith
  have hinv : 1 / (N : ℝ) ≤ 1 := (div_le_one hn0).mpr hn1.le
  have hw : 1 / (N : ℝ) + (1 + max 0 (Real.log (N : ℝ))) ≤ 2 * N := by
    have hl : max 0 (Real.log (N : ℝ)) ≤ (N : ℝ) - 1 :=
      max_le (by linarith) (Real.log_le_sub_one_of_pos hn0)
    linarith
  have he' := he.trans (mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ C + K))
  nlinarith

def registration : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨1, 2⟩, (1 : ℕ), (2 : ℕ), ?_⟩
    norm_num only [actual, realize, Nat.cast_one, Nat.cast_ofNat, mul_one, div_one]
    intro h
    have hn : Real.cos 2 / 2 < 0 :=
      div_neg_of_neg_of_pos Real.cos_two_neg (by norm_num)
    exact (not_lt_of_ge Real.cos_one_pos.le) (h.symm ▸ hn)

register_information_theorem _root_.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder.result in arena
  readout via (realize signature
    (fun _ p k => Real.cos ((k : ℝ) * p.1) / (k : ℝ)) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
    coordinates := #[1, 4]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg", "body"]
      stateBinder := 6 }] })
  escape continues (open)

#print axioms registration

end Reg.D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
