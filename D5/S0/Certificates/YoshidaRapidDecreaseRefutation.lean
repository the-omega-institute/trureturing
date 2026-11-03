/- GID: D5/S0/Certificates/YoshidaRapidDecreaseRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/YoshidaRapidDecreaseRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/YoshidaRapidDecreaseRefutation.claim; result=D5/S0/Certificates/YoshidaRapidDecreaseRefutation.result; claim=D5/S0/Certificates/YoshidaRapidDecreaseRefutation.claim
   digest: A positive Gaussian coefficient sequence violates rapid-decrease closure at r=1. -/

/- Formalization classification:
   proof_shape: witness_pos: bind-only; consumer: witness_rapid.
   proof_shape: witness_succ: bind-only; consumer: witness_adjacent.
   proof_shape: witness_adjacent: bind-only; consumer: witness_rapid.
   proof_shape: witness_rapid: bind-only; consumer: result.
   proof_shape: output_not_rapid: bind-only; consumer: result.
   proof_shape: result: bind-only.
   escape_witness: none (all six proofs use upstream facts and normalization).
   admission_basis: open-problem-resolution (#23414; Refuted).
   Direct frozen dependencies: none (all declarations; pinned Mathlib only).
   The public result is the designated refutation result (`basis=refutes`) and is
   exempt from four-slot escape registration (CLAUDE.md §3.9).
   The coefficient expressions and claim are those of #23414 with the forwarding
   names IsSourceSeries and S expanded; the coefficient sequence represents f.
   Negative-index zero extension is inlined as its literal conditional expression:
   scalarSignedCoeff in D5.S3.VertexAlgebra.ChargedResidue.TwoChamber provides the
   same construction for complex power-series coefficients but cannot be imported
   at S0. No duplicate zero-extension declaration is introduced.
-/

import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S0.Certificates.YoshidaRapidDecreaseRefutation

/- Definition 29: a positive sequence is rapidly decreasing when one alpha
   above the source threshold works at every positive index. -/
def RapidlyDecreasing (a : ℕ → ℝ) : Prop :=
  (∀ k : ℕ, 0 < a k) ∧
    ∃ α : ℝ,
      max 2 ((Real.sqrt 2 / 2) * (1 + Real.sqrt (1 + a 1))) ≤ α ∧
        ∀ k : ℕ, 1 ≤ k →
          a k ^ 2 ≥ α ^ 2 *
            (fun j : ℤ => if j < 0 then 0 else a (Int.toNat j)) ((k : ℤ) - 1) *
            (fun j : ℤ => if j < 0 then 0 else a (Int.toNat j)) ((k : ℤ) + 1)

/- Section 6: S_r[f] has coefficient a_k^2 - a_{k-r}a_{k+r}. -/
def sCoeff (a : ℕ → ℝ) (r k : ℕ) : ℝ :=
  a k ^ 2 - (fun j : ℤ => if j < 0 then 0 else a (Int.toNat j)) ((k : ℤ) - (r : ℤ)) *
    (fun j : ℤ => if j < 0 then 0 else a (Int.toNat j)) ((k : ℤ) + (r : ℤ))

/- Open Problem 5, with existence of the implicitly specified source object. -/
def claim : Prop :=
  (∃ a : ℕ → ℝ, RapidlyDecreasing a) ∧
    ∀ a : ℕ → ℝ, RapidlyDecreasing a →
      ∀ r : ℕ, 1 ≤ r → RapidlyDecreasing (sCoeff a r)


private def witness (k : ℕ) : ℝ := (48 : ℝ)^k / (32 : ℝ)^(k.choose 2)

private theorem witness_pos (k : ℕ) : 0 < witness k := by
  exact div_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)

private theorem witness_succ (k : ℕ) :
    witness (k+1) = witness k * 48 / 32^k := by
  simp only [witness, Nat.choose_succ_succ, Nat.choose_one_right, pow_succ, pow_add]
  ring

private theorem witness_adjacent (k : ℕ) :
    witness (k+1)^2 = 32 * witness k * witness (k+2) := by
  have h32 : (32 : ℝ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [show k+2 = (k+1)+1 from rfl, witness_succ (k+1), witness_succ k, pow_succ]
  field_simp; ring

private theorem witness_rapid : RapidlyDecreasing witness := by
  refine ⟨witness_pos, 4 * Real.sqrt 2, ?_, ?_⟩
  · apply max_le
    · have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
      have hn := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    · have h49 : Real.sqrt 49 = 7 :=
        (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
      norm_num [witness, Nat.choose, h49] ; nlinarith
  · intro k hk
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      Int.toNat_natCast, mul_ite, mul_zero, ite_mul, zero_mul, ge_iff_le]
    have hs : (4 * Real.sqrt 2)^2 = (32 : ℝ) := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [hs]
    exact le_of_eq (witness_adjacent n).symm

private theorem output_not_rapid : ¬ RapidlyDecreasing (sCoeff witness 1) := by
  rintro ⟨_, α, hα, hineq⟩
  have hb0 : sCoeff witness 1 0 = 1 := by norm_num [sCoeff, witness, Nat.choose]
  have hb1 : sCoeff witness 1 1 = 2232 := by norm_num [sCoeff, witness, Nat.choose]
  have hb2 : sCoeff witness 1 2 = 5022 := by norm_num [sCoeff, witness, Nat.choose]
  have hloc := hineq 1 (by norm_num)
  norm_num [hb0, hb1, hb2] at hloc
  have ht := le_trans (le_max_right (2 : ℝ)
    ((Real.sqrt 2 / 2) * (1 + Real.sqrt (1 + sCoeff witness 1 1)))) hα
  rw [hb1] at ht
  norm_num at ht
  have hnon : 0 ≤ Real.sqrt 2 / 2 * (1 + Real.sqrt 2233) := by positivity
  have hsq := mul_self_le_mul_self hnon ht
  have hval : (Real.sqrt 2 / 2 * (1 + Real.sqrt 2233))^2 =
      1117 + Real.sqrt 2233 := by
    calc
      _ = (Real.sqrt 2)^2 / 4 *
        (1 + 2 * Real.sqrt 2233 + (Real.sqrt 2233)^2) := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2233)]
        ring
  nlinarith [Real.sqrt_nonneg (2233 : ℝ)]

theorem result : ¬ claim := by
  intro h
  exact output_not_rapid (h.2 witness witness_rapid 1 (by norm_num))

end D5.S0.Certificates.YoshidaRapidDecreaseRefutation
