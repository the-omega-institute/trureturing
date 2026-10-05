import D5.S3.Arith.FibonacciAtomic.OptimalLawNearestStrictCeiling
import D5.S3.Arith.FibonacciAtomic.TriangularPathNormalization
import D5.S3.Arith.FibonacciAtomic.CarryGraphEmbedding
import Mathlib.Data.Fin.Tuple.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.OptimalLawEntersTriangle

open scoped BigOperators
open CarryGraphCriticalAttainment (alpha)
open DyadicSupportLines (cost residual)

example (m : ℕ) (hm : 2 ≤ m) (p : Fin m → ℝ)
    (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hopt : cost p = alpha m * sInf (Set.range p)) :
    ∀ i : Fin m, sInf (Set.range p) < p i → ∃ D : ℕ,
      0 < D ∧
      (∀ d < D, ⌊(2 : ℝ) ^ d * p i⌋ = ⌊(2 : ℝ) ^ d * sInf (Set.range p)⌋) ∧
      (∀ d, D ≤ d → Int.fract ((2 : ℝ) ^ d * p i) = 0) ∧
      ⌊(2 : ℝ) ^ D * p i⌋ = ⌊(2 : ℝ) ^ D * sInf (Set.range p)⌋ + 1 := by
  classical
  intro i hi
  let t := sInf (Set.range p)
  have tpos : 0 < t := by
    have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    obtain ⟨k, hk⟩ := (Set.range_nonempty p).csInf_mem (Set.finite_range p)
    change 0 < sInf (Set.range p)
    rw [← hk]
    exact hp k
  have term := OptimalLawLargerAtomsTerminate.result m hm p hp hs hopt i hi
  let D := Nat.find term
  obtain ⟨N, hN⟩ := Nat.find_spec term
  change p i = (N : ℝ) / (2 : ℝ) ^ D at hN
  have ceiling : p i = ((⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1) / (2 : ℝ) ^ D :=
    OptimalLawNearestStrictCeiling.result m hm p hp hs hopt i hi
  have grid (d : ℕ) (hd : D ≤ d) : ∃ A : ℕ, p i = (A : ℝ) / (2 : ℝ) ^ d := by
    refine ⟨N * 2 ^ (d - D), ?_⟩
    rw [hN, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [show (2 : ℝ) ^ d = (2 : ℝ) ^ D * (2 : ℝ) ^ (d - D) by
      rw [← pow_add, Nat.add_sub_of_le hd]]
    field_simp
  have shallow (d : ℕ) (hd : d < D) :
      ⌊(2 : ℝ) ^ d * p i⌋ = ⌊(2 : ℝ) ^ d * t⌋ := by
    let B := ⌊(2 : ℝ) ^ d * t⌋ + 1
    have Bpos : 0 ≤ B := by
      have H := Int.floor_nonneg.mpr
        (mul_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d) tpos.le)
      dsimp [B]
      omega
    let Q : ℝ := (B : ℝ) / (2 : ℝ) ^ d
    have Qt : t < Q := by
      apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)).mpr
      dsimp [B]
      push_cast
      simpa only [mul_comm] using Int.lt_floor_add_one ((2 : ℝ) ^ d * t)
    have Qgrid : (2 : ℝ) ^ D * Q = (B * 2 ^ (D - d) : ℤ) := by
      dsimp [Q]
      rw [show (2 : ℝ) ^ D = (2 : ℝ) ^ d * (2 : ℝ) ^ (D - d) by
        rw [← pow_add, Nat.add_sub_of_le hd.le]]
      push_cast
      field_simp
    have bound : p i ≤ Q := by
      rw [ceiling]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ D)).mpr
      have H := mul_lt_mul_of_pos_left Qt (by positivity : (0 : ℝ) < (2 : ℝ) ^ D)
      rw [Qgrid] at H
      have H' : ⌊(2 : ℝ) ^ D * t⌋ < B * 2 ^ (D - d) := Int.floor_lt.mpr H
      have H'' : ⌊(2 : ℝ) ^ D * t⌋ + 1 ≤ B * 2 ^ (D - d) := by omega
      have castH : (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1 ≤ (B * 2 ^ (D - d) : ℤ) := by
        exact_mod_cast H''
      rw [mul_comm Q, Qgrid]
      exact castH
    have lower : ⌊(2 : ℝ) ^ d * t⌋ ≤ ⌊(2 : ℝ) ^ d * p i⌋ :=
      Int.floor_mono (mul_le_mul_of_nonneg_left hi.le (by positivity))
    by_contra ne
    have bigger : B ≤ ⌊(2 : ℝ) ^ d * p i⌋ := by dsimp [B]; omega
    have above : Q ≤ p i := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ d)).mpr
      exact (by exact_mod_cast bigger : (B : ℝ) ≤ (⌊(2 : ℝ) ^ d * p i⌋ : ℝ)).trans
        (by simpa only [mul_comm] using Int.floor_le ((2 : ℝ) ^ d * p i))
    have eq : p i = Q := le_antisymm bound above
    apply Nat.find_min term hd
    refine ⟨B.toNat, ?_⟩
    rw [eq]
    dsimp [Q]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg Bpos).symm
  have Dpos : 0 < D := by
    by_contra H
    have Dzero : D = 0 := by omega
    have plt : p i < 1 := by
      letI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
      obtain ⟨j, hj⟩ := exists_ne i
      have Hsum := Finset.single_lt_sum (s := Finset.univ) (f := p)
        hj (Finset.mem_univ i) (Finset.mem_univ j) (hp j) (fun l _ _ => (hp l).le)
      rwa [hs] at Hsum
    rw [Dzero] at hN
    simp only [pow_zero, div_one] at hN
    have lo : (0 : ℝ) < N := hN ▸ hp i
    have hi' : (N : ℝ) < 1 := hN ▸ plt
    have lo' : 0 < N := by exact_mod_cast lo
    have hi'' : N < 1 := by exact_mod_cast hi'
    omega
  refine ⟨D, Dpos, shallow, ?_, ?_⟩
  · intro d hd
    obtain ⟨A, hA⟩ := grid d hd
    have eq : (2 : ℝ) ^ d * p i = A := by rw [hA]; field_simp
    rw [eq]
    exact Int.fract_natCast A
  · have eq : (2 : ℝ) ^ D * p i = (⌊(2 : ℝ) ^ D * t⌋ : ℝ) + 1 := by
      rw [ceiling]
      field_simp
    rw [eq, Int.floor_add_one, Int.floor_intCast]

end D5.S3.Arith.FibonacciAtomic.OptimalLawEntersTriangle
