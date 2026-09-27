/- GID: D5/S3/ArithSums/ZhangCharacterSumDifferenceRefutation
   generality: I
   mirror-B: D5/B/S3/ArithSums/ZhangCharacterSumDifferenceRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.NumberTheory.LegendreSymbol.Basic, mathlib/module/Mathlib.Tactic.NormNum.Prime]
   utility: none
   digest: Zhang Question (D) is false: character sums have constant difference c = 1. -/

/- proof_shape: result: bind-only
   escape_witness: none
   admission_basis: open-problem-resolution (issue #8626)
   Direct frozen dependencies: none (pinned Mathlib only). -/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic.NormNum.Prime

open scoped BigOperators

namespace D5.S3.ArithSums.ZhangCharacterSumDifferenceRefutation

/-- `Sigma_{x=1}^{p-1} (f(x)/p)`: the Legendre character sum of `f` over
`1 <= x <= p-1` (identity (2) of arXiv:2506.17235v1). -/
def characterSum (p : ℕ) [Fact p.Prime] (f : Polynomial ℤ) : ℤ :=
  ∑ x ∈ Finset.Ico 1 p, legendreSym p (f.eval (x : ℤ))

/-- "Fundamentally different": `(f(x)/p) != (g(x)/p)` as functions on
`{1,...,p-1}` (the paper's own gloss). -/
def FundamentallyDifferent (p : ℕ) [Fact p.Prime] (f g : Polynomial ℤ) : Prop :=
  ∃ x ∈ Finset.Ico 1 p,
    legendreSym p (f.eval (x : ℤ)) ≠ legendreSym p (g.eval (x : ℤ))

/-- Question (D) of arXiv:2506.17235v1 read as the assertion "c can only be 0 or 2". -/
def claim : Prop := ∀ (f g : Polynomial ℤ) (c : ℤ),
  (∀ p : ℕ, ∀ hp : p.Prime, p ≠ 2 →
    haveI : Fact p.Prime := ⟨hp⟩
    FundamentallyDifferent p f g ∧ characterSum p f - characterSum p g = c) → c = 0 ∨ c = 2

/-- Question (D) is answered in the negative: `X^2` and `(X+1)^2` give `c = 1`. -/
theorem result : ¬ claim := by
  intro hclaim
  have hcounter := hclaim (Polynomial.X ^ 2) ((Polynomial.X + 1) ^ 2) 1
  have hforall : ∀ p : ℕ, ∀ hp : p.Prime, p ≠ 2 →
      haveI : Fact p.Prime := ⟨hp⟩
      FundamentallyDifferent p (Polynomial.X ^ 2) ((Polynomial.X + 1) ^ 2) ∧
        characterSum p (Polynomial.X ^ 2) -
            characterSum p ((Polynomial.X + 1) ^ 2) = 1 := by
    intro p hp hne
    letI : Fact p.Prime := ⟨hp⟩
    have hp3 : 3 ≤ p := by
      have hp2 : 2 ≤ p := hp.two_le
      omega
    have hnonzero : ∀ x : ℕ, x ∈ Finset.Ico 1 p → (x : ZMod p) ≠ 0 := by
      intro x hx hzero
      have hzero' : ((x : ℤ) : ZMod p) = 0 := by simpa using hzero
      have hdiv : (p : ℤ) ∣ (x : ℤ) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (x : ℤ) p).mp hzero'
      have hdivNat : p ∣ x := by exact_mod_cast hdiv
      have hxmem := Finset.mem_Ico.mp hx
      have hle : p ≤ x := Nat.le_of_dvd (by omega) hdivNat
      omega
    have hsum_x2 : characterSum p (Polynomial.X ^ 2) = (p : ℤ) - 1 := by
      unfold characterSum
      calc
        (∑ x ∈ Finset.Ico 1 p,
            legendreSym p ((Polynomial.X ^ 2).eval (x : ℤ))) =
            ∑ x ∈ Finset.Ico 1 p, (1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro x hx
              simp only [Polynomial.eval_pow, Polynomial.eval_X]
              apply legendreSym.sq_one' p
              simpa using hnonzero x hx
        _ = (p : ℤ) - 1 := by
          simp [Nat.card_Ico, hp.one_le]
    have hsum_shift : characterSum p ((Polynomial.X + 1) ^ 2) = (p : ℤ) - 2 := by
      unfold characterSum
      have hpminus : 1 ≤ p - 1 := by omega
      have hsplit :
          (∑ x ∈ Finset.Ico 1 p,
            legendreSym p (((Polynomial.X + 1) ^ 2).eval (x : ℤ))) =
            (∑ x ∈ Finset.Ico 1 (p - 1),
              legendreSym p (((Polynomial.X + 1) ^ 2).eval (x : ℤ))) +
              legendreSym p (((Polynomial.X + 1) ^ 2).eval ((p - 1 : ℕ) : ℤ)) := by
        calc
          (∑ x ∈ Finset.Ico 1 p,
              legendreSym p (((Polynomial.X + 1) ^ 2).eval (x : ℤ))) =
              ∑ x ∈ Finset.Ico 1 (p - 1 + 1),
                legendreSym p (((Polynomial.X + 1) ^ 2).eval (x : ℤ)) := by
                  congr 2
                  omega
          _ = _ := Finset.sum_Ico_succ_top hpminus _
      rw [hsplit]
      have hinner :
          (∑ x ∈ Finset.Ico 1 (p - 1),
            legendreSym p (((Polynomial.X + 1) ^ 2).eval (x : ℤ))) =
            ∑ x ∈ Finset.Ico 1 (p - 1), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxmem := Finset.mem_Ico.mp hx
        simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one]
        apply legendreSym.sq_one' p
        intro hzero
        have hzero' : (((x : ℤ) + 1 : ℤ) : ZMod p) = 0 := by simpa using hzero
        have hdiv : (p : ℤ) ∣ (x : ℤ) + 1 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd ((x : ℤ) + 1) p).mp hzero'
        have hdivNat : p ∣ x + 1 := by exact_mod_cast hdiv
        have hle : p ≤ x + 1 := Nat.le_of_dvd (by omega) hdivNat
        omega
      rw [hinner]
      have heval :
          ((Polynomial.X + 1) ^ 2).eval ((p - 1 : ℕ) : ℤ) = (p : ℤ) ^ 2 := by
        simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
          Polynomial.eval_one]
        congr 1
        omega
      rw [heval]
      have hzero : legendreSym p ((p : ℤ) ^ 2) = 0 := by
        rw [legendreSym.eq_zero_iff]
        simp
      rw [hzero]
      simp [Nat.card_Ico]
      omega
    constructor
    · refine ⟨p - 1, ?_, ?_⟩
      · simp only [Finset.mem_Ico]
        omega
      · have hlast : (p - 1 : ℕ) ∈ Finset.Ico 1 p := by
          simp only [Finset.mem_Ico]
          omega
        have hleft :
            legendreSym p ((Polynomial.X ^ 2).eval ((p - 1 : ℕ) : ℤ)) = 1 := by
          simp only [Polynomial.eval_pow, Polynomial.eval_X]
          apply legendreSym.sq_one' p
          simpa using hnonzero (p - 1) hlast
        have hright :
            legendreSym p (((Polynomial.X + 1) ^ 2).eval ((p - 1 : ℕ) : ℤ)) = 0 := by
          have heval :
              ((Polynomial.X + 1) ^ 2).eval ((p - 1 : ℕ) : ℤ) = (p : ℤ) ^ 2 := by
            simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
              Polynomial.eval_one]
            congr 1
            omega
          rw [heval, legendreSym.eq_zero_iff]
          simp
        rw [hleft, hright]
        norm_num
    · rw [hsum_x2, hsum_shift]
      omega
  have hbad := hcounter hforall
  omega

example : characterSum 3 (Polynomial.X ^ 2) = 2 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  unfold characterSum
  change (∑ x ∈ Finset.Ico 1 (2 + 1), _) = _
  rw [Finset.sum_Ico_succ_top (by norm_num)]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_Ico_succ_top (by norm_num)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have h2 : legendreSym 3 ((2 : ℤ) ^ 2) = 1 := legendreSym.sq_one' 3 (by
    intro hz
    have hd : (3 : ℤ) ∣ (2 : ℤ) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd 2 3).mp hz
    norm_num at hd)
  have h2' : legendreSym 3 4 = 1 := by convert h2 using 1 <;> norm_num
  norm_num
  rw [h2']
  norm_num

example : characterSum 3 ((Polynomial.X + 1) ^ 2) = 1 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  unfold characterSum
  change (∑ x ∈ Finset.Ico 1 (2 + 1), _) = _
  rw [Finset.sum_Ico_succ_top (by norm_num)]
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one]
  rw [Finset.sum_Ico_succ_top (by norm_num)]
  simp only [Finset.Ico_self, Finset.sum_empty, zero_add]
  have h1 : legendreSym 3 (((1 : ℤ) + 1) ^ 2) = 1 := legendreSym.sq_one' 3 (by
    intro hz
    have hd : (3 : ℤ) ∣ ((1 : ℤ) + 1) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd 2 3).mp (by simpa using hz)
    norm_num at hd)
  have h2 : legendreSym 3 (((2 : ℤ) + 1) ^ 2) = 0 := by
    rw [legendreSym.eq_zero_iff]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd 9 3).2 (by norm_num)
  have h1' : legendreSym 3 4 = 1 := by convert h1 using 1 <;> norm_num
  norm_num
  exact h1'

#print axioms result

end D5.S3.ArithSums.ZhangCharacterSumDifferenceRefutation
