/- GID: D5/S3/Arith/CharacterSums/PascadiQuadraticPrimitiveDirection
   generality: G
   mirror-B: D5/B/S3/Arith/CharacterSums/PascadiQuadraticPrimitiveDirection
   mirror-E: none(waiver:actual-quadratic-pencil-consumer)
   anchors: []
   utility: none
   digest: A collinear integer family has a primitive direction with weighted height control. -/

import Mathlib.Data.Int.GCD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! A primitive direction preserves the weights of the original leading data. -/

namespace D5.S3.Arith.CharacterSums.PrimeCube

private theorem integer_direction (m s : Fin 3 → ℤ)
    (hn : m 0 ≠ 0 ∨ s 0 ≠ 0)
    (hc : ∀ i, m 0 * s i - m i * s 0 = 0) :
    ∃ (d n : ℤ) (k : Fin 3 → ℤ),
      Int.gcd d n = 1 ∧ (∀ i, m i = d*k i) ∧ (∀ i, s i = n*k i) := by
  have hg : 0 < Int.gcd (m 0) (s 0) := by
    apply Nat.pos_of_ne_zero
    intro h
    have hz := Int.gcd_eq_zero_iff.mp h
    rcases hn with hn | hn <;> exact hn (by tauto)
  obtain ⟨d,n,hdn,hm,hs⟩ := Int.exists_gcd_one hg
  have hg0 : ((Int.gcd (m 0) (s 0) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hcross (i : Fin 3) : d*s i - n*m i = 0 := by
    have hz : (Int.gcd (m 0) (s 0) : ℤ)*(d*s i-n*m i) = 0 := by
      calc
        _ = (d*(Int.gcd (m 0) (s 0) : ℤ))*s i-
            m i*(n*(Int.gcd (m 0) (s 0) : ℤ)) := by ring
        _ = m 0*s i-m i*s 0 := by rw [← hm,← hs]
        _ = 0 := hc i
    exact (mul_eq_zero.mp hz).resolve_left hg0
  have hb : d*Int.gcdA d n+n*Int.gcdB d n = 1 := by
    simpa only [hdn, Nat.cast_one] using (Int.gcd_eq_gcd_ab d n).symm
  let k : Fin 3 → ℤ := fun i => Int.gcdA d n*m i+Int.gcdB d n*s i
  refine ⟨d,n,k,hdn,?_,?_⟩
  · intro i
    dsimp only [k]
    linear_combination -(m i)*hb-Int.gcdB d n*hcross i
  · intro i
    dsimp only [k]
    linear_combination -(s i)*hb+Int.gcdA d n*hcross i

/-- Collinear integer leading coefficients admit a primitive integral direction.
The same finite maximum controls the direction products at their original
weights; no division by an individual nonzero coefficient is used. -/
theorem quadratic_coefficient_primitive_direction (m s : Fin 3 → ℤ) (J : ℝ)
    (hJ : 1 ≤ J) (hn : m 0 ≠ 0 ∨ s 0 ≠ 0)
    (hc : ∀ i, m 0*s i-m i*s 0 = 0)
    (hm : ∀ i, |(m i : ℝ)| ≤ 3*J)
    (hs : ∀ i, |(s i : ℝ)| ≤ J^2) :
    ∃ (d n : ℤ) (k : Fin 3 → ℤ) (D : ℝ),
      Int.gcd d n = 1 ∧ (∀ i, m i=d*k i) ∧ (∀ i, s i=n*k i) ∧
      0 ≤ D ∧ (∀ i, |(k i : ℝ)| ≤ D) ∧
      |(d : ℝ)| * D ≤ 3*J ∧ |(n : ℝ)| * D ≤ J^2 ∧ D ≤ 3*J^2 := by
  obtain ⟨d,n,k,hdn,hmd,hns⟩ := integer_direction m s hn hc
  classical
  obtain ⟨i₀,hi₀,hmax⟩ := Finset.exists_mem_eq_sup
    (s := Finset.univ) (by simp : (Finset.univ : Finset (Fin 3)).Nonempty)
    (fun i => (k i).natAbs)
  let D : ℝ := (k i₀).natAbs
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hDi (i : Fin 3) : |(k i : ℝ)| ≤ D := by
    have h := Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)
    rw [hmax] at h
    have h' : ((k i).natAbs : ℝ) ≤ ((k i₀).natAbs : ℝ) := by exact_mod_cast h
    simpa [D] using h'
  have hDa : |(k i₀ : ℝ)| = D := by simp [D, Int.natCast_natAbs]
  have hdD : |(d : ℝ)| * D ≤ 3*J := by
    rw [← hDa, ← abs_mul, ← Int.cast_mul, ← hmd]
    exact hm i₀
  have hnD : |(n : ℝ)| * D ≤ J^2 := by
    rw [← hDa, ← abs_mul, ← Int.cast_mul, ← hns]
    exact hs i₀
  have hD : D ≤ 3*J^2 := by
    by_cases hd : d = 0
    · have hn0 : n ≠ 0 := by intro hz; simp [hd,hz] at hdn
      have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
      nlinarith only [hnD,hD0,hn1,sq_nonneg J]
    · have hd1 : (1 : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd
      nlinarith only [hdD,hD0,hd1,hJ,sq_nonneg (J-1)]
  exact ⟨d,n,k,D,hdn,hmd,hns,hD0,hDi,hdD,hnD,hD⟩

end D5.S3.Arith.CharacterSums.PrimeCube
