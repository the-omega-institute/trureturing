/- GID: D5/S3/Arith/CharacterSums/PascadiSingularResultant
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiSingularResultant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common singular root modulo a square forces fourth-power resultant divisibility. -/

/- Provenance: integrated from the completed 2026-11-16 singular-cover research archive.
Original source SHA256: eb9f9c502221986f3b7f64263954614829ffd601da25470495669c1b2fcd2d54.
Canonical integration preserves the archived proofs; see the Pascadi Library note. -/

import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Taylor
import Lean.Elab.Tactic.Omega

/-! # Resultant divisibility at a common singular point -/

open Polynomial
open scoped BigOperators

namespace D5.S3.Arith.CharacterSums

noncomputable section

private theorem det_dvd_fourth_of_low_rows
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) (p : ℤ) (r₀ r₁ r₂ c₀ c₁ : ι)
    (h₀₁ : r₀ ≠ r₁) (h₀₂ : r₀ ≠ r₂) (h₁₂ : r₁ ≠ r₂)
    (h₀ : ∀ j, p ^ 2 ∣ M r₀ j)
    (h₀z : ∀ j, j ≠ c₀ → j ≠ c₁ → M r₀ j = 0)
    (h₁ : ∀ j, p ∣ M r₁ j)
    (h₁o : ∀ j, j ≠ c₀ → j ≠ c₁ → p ^ 2 ∣ M r₁ j)
    (h₂o : ∀ j, j ≠ c₀ → j ≠ c₁ → p ∣ M r₂ j) :
    p ^ 4 ∣ M.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.dvd_sum
  intro σ _
  apply dvd_mul_of_dvd_right
  change p ^ 4 ∣ ∏ i, M i (σ i)
  have hpart : p ^ 4 ∣ M r₀ (σ r₀) * M r₁ (σ r₁) * M r₂ (σ r₂) := by
    by_cases hs₀ : σ r₀ = c₀ ∨ σ r₀ = c₁
    · by_cases hs₁ : σ r₁ = c₀ ∨ σ r₁ = c₁
      · have hs₂₀ : σ r₂ ≠ c₀ := by
          rcases hs₀ with h | h <;> rcases hs₁ with h' | h' <;>
            intro h''
          · exact h₀₁ (σ.injective (h.trans h'.symm))
          · exact h₀₂ (σ.injective (h.trans h''.symm))
          · exact h₁₂ (σ.injective (h'.trans h''.symm))
          · exact h₀₁ (σ.injective (h.trans h'.symm))
        have hs₂₁ : σ r₂ ≠ c₁ := by
          rcases hs₀ with h | h <;> rcases hs₁ with h' | h' <;>
            intro h''
          · exact h₀₁ (σ.injective (h.trans h'.symm))
          · exact h₁₂ (σ.injective (h'.trans h''.symm))
          · exact h₀₂ (σ.injective (h.trans h''.symm))
          · exact h₀₁ (σ.injective (h.trans h'.symm))
        have := mul_dvd_mul (mul_dvd_mul (h₀ (σ r₀)) (h₁ (σ r₁)))
          (h₂o (σ r₂) hs₂₀ hs₂₁)
        simpa only [← pow_succ] using this
      · have := mul_dvd_mul (h₀ (σ r₀))
          (h₁o (σ r₁) (fun h => hs₁ (Or.inl h)) (fun h => hs₁ (Or.inr h)))
        have h₀₁div : p ^ 4 ∣ M r₀ (σ r₀) * M r₁ (σ r₁) := by
          simpa only [← pow_add] using this
        exact h₀₁div.mul_right _
    · rw [h₀z (σ r₀) (fun h => hs₀ (Or.inl h)) (fun h => hs₀ (Or.inr h)),
        zero_mul, zero_mul]
      exact dvd_zero _
  apply hpart.trans
  calc
    M r₀ (σ r₀) * M r₁ (σ r₁) * M r₂ (σ r₂) =
        ∏ i ∈ ({r₀, r₁, r₂} : Finset ι), M i (σ i) := by
      simp [h₀₁, h₀₂, h₁₂, mul_assoc]
    _ ∣ ∏ i, M i (σ i) :=
      Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ _)

private theorem shifted_coeff_dvd (q : ℤ[X]) (p : ℤ)
    (h₀ : p ^ 2 ∣ q.coeff 0) (h₁ : p ∣ q.coeff 1)
    (i k n a : ℕ) (ha : a + (i - k) ≤ 2) :
    p ^ a ∣ if i ∈ Set.Icc k (k + n) then q.coeff (i - k) else 0 := by
  split_ifs
  · by_cases hi₀ : i - k = 0
    · rw [hi₀]
      exact (pow_dvd_pow p (by omega)).trans h₀
    · by_cases hi₁ : i - k = 1
      · rw [hi₁]
        exact (pow_dvd_pow p (show a ≤ 1 by omega)).trans (by simpa using h₁)
      · have ha₀ : a = 0 := by omega
        simp [ha₀]
  · exact dvd_zero _

private theorem resultant_dvd_fourth_of_coeff
    (f g : ℤ[X]) (p : ℤ) (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hf₀ : p ^ 2 ∣ f.coeff 0) (hg₀ : p ^ 2 ∣ g.coeff 0)
    (hf₁ : p ∣ f.coeff 1) (hg₁ : p ∣ g.coeff 1) :
    p ^ 4 ∣ Polynomial.resultant f g m n := by
  let r₀ : Fin (m + n) := ⟨0, by omega⟩
  let r₁ : Fin (m + n) := ⟨1, by omega⟩
  let r₂ : Fin (m + n) := ⟨2, by omega⟩
  let c₀ : Fin (m + n) := Fin.castAdd n ⟨0, by omega⟩
  let c₁ : Fin (m + n) := Fin.natAdd m ⟨0, by omega⟩
  apply det_dvd_fourth_of_low_rows (f.sylvester g m n) p r₀ r₁ r₂ c₀ c₁
    (by simp [r₀, r₁, Fin.ext_iff]) (by simp [r₀, r₂, Fin.ext_iff])
    (by simp [r₁, r₂, Fin.ext_iff])
  · intro j
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        exact shifted_coeff_dvd g p hg₀ hg₁ 0 j n 2 (by omega)
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        exact shifted_coeff_dvd f p hf₀ hf₁ 0 j m 2 (by omega)
  · intro j hj₀ hj₁
    induction j using Fin.addCases with
    | left j =>
        have hj : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj₀
          apply Fin.ext
          simpa [c₀] using hz
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        exact ite_eq_right (by simp only [Set.mem_Icc]; change ¬ (j.1 ≤ 0 ∧ 0 ≤ j.1 + n); omega)
    | right j =>
        have hj : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj₁
          apply Fin.ext
          simp [c₁, hz]
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        exact ite_eq_right (by simp only [Set.mem_Icc]; change ¬ (j.1 ≤ 0 ∧ 0 ≤ j.1 + m); omega)
  · intro j
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        simpa only [pow_one] using shifted_coeff_dvd g p hg₀ hg₁ 1 j n 1 (by omega)
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        simpa only [pow_one] using shifted_coeff_dvd f p hf₀ hf₁ 1 j m 1 (by omega)
  · intro j hj₀ hj₁
    induction j using Fin.addCases with
    | left j =>
        have hj : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj₀
          apply Fin.ext
          simpa [c₀] using hz
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        exact shifted_coeff_dvd g p hg₀ hg₁ 1 j n 2 (by omega)
    | right j =>
        have hj : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj₁
          apply Fin.ext
          simp [c₁, hz]
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        exact shifted_coeff_dvd f p hf₀ hf₁ 1 j m 2 (by omega)
  · intro j hj₀ hj₁
    induction j using Fin.addCases with
    | left j =>
        have hj : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj₀
          apply Fin.ext
          simpa [c₀] using hz
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        simpa only [pow_one] using shifted_coeff_dvd g p hg₀ hg₁ 2 j n 1 (by omega)
    | right j =>
        have hj : (j : ℕ) ≠ 0 := by
          intro hz
          apply hj₁
          apply Fin.ext
          simp [c₁, hz]
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        simpa only [pow_one] using shifted_coeff_dvd f p hf₀ hf₁ 2 j m 1 (by omega)

/-- A common singular root modulo a square forces fourth-power divisibility of the
actual integer polynomial resultant. The divisor need not be prime, the degrees
may be any integers at least two, and leading coefficients need not be units. -/
theorem singular_resultant_dvd_fourth (f g : ℤ[X]) (b p : ℤ)
    (hf : 2 ≤ f.natDegree) (hg : 2 ≤ g.natDegree)
    (hf₀ : p ^ 2 ∣ f.eval b) (hg₀ : p ^ 2 ∣ g.eval b)
    (hf₁ : p ∣ f.derivative.eval b) (hg₁ : p ∣ g.derivative.eval b) :
    p ^ 4 ∣ Polynomial.resultant f g f.natDegree g.natDegree := by
  rw [← Polynomial.resultant_taylor f g b]
  apply resultant_dvd_fourth_of_coeff
    (f.taylor b) (g.taylor b) p _ _
    (by simpa using hf) (by simpa using hg)
  · simpa only [Polynomial.taylor_coeff_zero] using hf₀
  · simpa only [Polynomial.taylor_coeff_zero] using hg₀
  · simpa only [Polynomial.taylor_coeff_one] using hf₁
  · simpa only [Polynomial.taylor_coeff_one] using hg₁


end

end D5.S3.Arith.CharacterSums
