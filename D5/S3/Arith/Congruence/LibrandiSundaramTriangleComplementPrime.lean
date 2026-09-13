/- GID: D5/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/LibrandiSundaramTriangleComplementPrime
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.Tactic.Linarith]
   utility: none
   digest: The complement of Librandi's triangle maps to primes through odd factorization. -/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

namespace D5.S3.Arith.Congruence.LibrandiSundaramTriangleComplementPrime

/- The natural-number subtraction and division in this definition are literal.  On the
   stated domain `m ≥ n ≥ 1`, the numerator is at least two, so neither operation truncates
   the intended integer expression. -/
def T (m n : ℕ) : ℕ := (2 * m * n + m + n - 2) / 2

def InTriangle (h : ℕ) : Prop := ∃ m n : ℕ, 1 ≤ n ∧ n ≤ m ∧ T m n = h

example : T 1 1 = 1 ∧ T 2 1 = 2 ∧ T 2 2 = 5 ∧
    T 3 1 = 4 ∧ T 3 2 = 7 ∧ T 3 3 = 11 := by
  decide

theorem librandi_a140869 : ∀ h : ℕ, ¬ InTriangle h → Nat.Prime (4 * h + 5) := by
  intro h hnot
  by_contra hprime
  let N : ℕ := 4 * h + 5
  have hN : 2 ≤ N := by
    dsimp [N]
    omega
  have hprimeN : ¬ Nat.Prime N := by
    simpa [N] using hprime
  obtain ⟨d, hdvd, hd2, hdN⟩ := Nat.exists_dvd_of_not_prime2 hN hprimeN
  set e : ℕ := N / d with he_def
  have hde : d * e = N := by
    rw [he_def]
    simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hdvd)
  have hoddN : Odd N := by
    dsimp [N]
    exact ⟨2 * h + 2, by omega⟩
  have hoddD : Odd d := by
    by_contra hnotodd
    have hEvenD : Even d := Nat.not_odd_iff_even.mp hnotodd
    have hTwoD : 2 ∣ d := even_iff_two_dvd.mp hEvenD
    have hTwoN : 2 ∣ N := hTwoD.trans hdvd
    exact (Nat.not_even_iff_odd.mpr hoddN) (even_iff_two_dvd.mpr hTwoN)
  have hoddE : Odd e := by
    by_contra hnotodd
    have hEvenE : Even e := Nat.not_odd_iff_even.mp hnotodd
    have hTwoE : 2 ∣ e := even_iff_two_dvd.mp hEvenE
    have hTwoN : 2 ∣ N := by
      rw [← hde]
      exact dvd_mul_of_dvd_right hTwoE d
    exact (Nat.not_even_iff_odd.mpr hoddN) (even_iff_two_dvd.mpr hTwoN)
  have he0 : e ≠ 0 := by
    intro he
    have hN0 : N = 0 := by simpa [he] using hde.symm
    rw [hN0] at hN
    omega
  have he1 : e ≠ 1 := by
    intro he
    have hdEq : d = N := by simpa [he] using hde
    rw [hdEq] at hdN
    omega
  have he2 : 2 ≤ e := (Nat.two_le_iff e).mpr ⟨he0, he1⟩
  obtain ⟨n, hdform⟩ := hoddD
  obtain ⟨m, heform⟩ := hoddE
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ m := by omega
  have hprod : (2 * n + 1) * (2 * m + 1) = 4 * h + 5 := by
    simpa [N, hdform, heform] using hde
  have hcoord : ∀ a b : ℕ, 1 ≤ b → b ≤ a →
      (2 * b + 1) * (2 * a + 1) = 4 * h + 5 → T a b = h := by
    intro a b hb1 hba hab
    have hlin : 4 * a * b + 2 * a + 2 * b = 4 * h + 4 := by
      nlinarith [hab]
    have habpos : 0 < a * b := Nat.mul_pos (by omega) (by omega)
    have hnum : 2 * a * b + a + b - 2 = 2 * h := by
      apply (Nat.sub_eq_iff_eq_add (by nlinarith [habpos])).2
      nlinarith [hlin]
    dsimp [T]
    omega
  rcases le_total n m with hnm | hmn
  · apply hnot
    exact ⟨m, n, hn1, hnm, hcoord m n hn1 hnm hprod⟩
  · apply hnot
    exact ⟨n, m, hm1, hmn, hcoord n m hm1 hmn (by simpa [Nat.mul_comm] using hprod)⟩

end D5.S3.Arith.Congruence.LibrandiSundaramTriangleComplementPrime

#print axioms D5.S3.Arith.Congruence.LibrandiSundaramTriangleComplementPrime.librandi_a140869
