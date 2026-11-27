/- GID: D5/S3/Arith/Divisors/ErdosNicolas/TentKernel
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/TentKernel
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: none
   digest: Finite nonnegative tent expansion of the Erdos Nicolas rational kernel. -/

import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- The rational tangent kernel, with its reciprocal tail. -/
def K (L r : ℕ) : ℚ :=
  if r ≤ L then 2 / L - r / (L : ℚ) ^ 2 else (r : ℚ)⁻¹

/-- The short-distance residual; natural subtraction implements the positive part. -/
def w (L g : ℕ) : ℚ := ((L - g : ℕ) : ℚ) ^ 2 / ((L : ℚ) ^ 2 * g)

@[simp] theorem K_zero (L : ℕ) : K L 0 = 2 / L := by simp [K]

theorem K_of_le {L r : ℕ} (h : r ≤ L) :
    K L r = 2 / L - r / (L : ℚ) ^ 2 := by simp [K, h]

private theorem K_of_ge {L r : ℕ} (hL : 0 < L) (h : L ≤ r) :
    K L r = (r : ℚ)⁻¹ := by
  by_cases he : r ≤ L
  · have hr : r = L := le_antisymm he h
    subst r
    rw [K_of_le le_rfl]
    have hn : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
    ring
  · simp [K, he]

private theorem K_nonneg (L r : ℕ) : 0 ≤ K L r := by
  by_cases hL0 : L = 0
  · subst L
    by_cases hr : r = 0
    · subst r
      norm_num [K]
    · simp [K, hr, inv_nonneg.mpr (show (0 : ℚ) ≤ r by positivity)]
  have hL : 0 < L := Nat.pos_of_ne_zero hL0
  by_cases hr : r ≤ L
  · rw [K_of_le hr]
    have hLq : (0 : ℚ) < L := by exact_mod_cast hL
    have hrq : (r : ℚ) ≤ L := by exact_mod_cast hr
    apply (sub_nonneg.mpr ?_)
    apply (div_le_iff₀ (sq_pos_of_pos hLq)).mpr
    field_simp
    nlinarith
  · simp only [K, if_neg hr]
    positivity

theorem w_nonneg (L g : ℕ) : 0 ≤ w L g := by unfold w; positivity

theorem inv_eq_K_add_w {L g : ℕ} (hg : 0 < g) :
    (g : ℚ)⁻¹ = K L g + w L g := by
  by_cases hL0 : L = 0
  · subst L
    simp [K, w, Nat.not_le.mpr hg]
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL0
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  by_cases h : g ≤ L
  · rw [K_of_le h, w, Nat.cast_sub h]
    field_simp
    ring
  · simp [K, h, w, Nat.sub_eq_zero_of_le (le_of_not_ge h)]

theorem K_le_inv {L g : ℕ} (hg : 0 < g) :
    K L g ≤ (g : ℚ)⁻¹ := by
  rw [inv_eq_K_add_w hg]
  exact le_add_of_nonneg_right (w_nonneg L g)

/-- Discrete second difference, with the unused zero coefficient set to zero. -/
def secondDifference (f : ℕ → ℚ) (s : ℕ) : ℚ :=
  if s = 0 then 0 else f (s - 1) - 2 * f s + f (s + 1)

/-- Finite discrete Green identity; no limiting operation is involved. -/
private theorem finite_tent_expansion (f : ℕ → ℚ) {M r : ℕ} (hr : r ≤ M) :
    f r = f M + (M - r : ℕ) * (f M - f (M + 1)) +
      ∑ s ∈ range (M + 1), (s - r : ℕ) * secondDifference f s := by
  induction M with
  | zero =>
      have : r = 0 := by omega
      subst r
      simp
  | succ M ih =>
      by_cases he : r = M + 1
      · subst r
        have hz : ∀ s ∈ range (M + 1 + 1), (s - (M + 1) : ℕ) = 0 := by
          intro s hs
          simp only [mem_range] at hs
          omega
        have hzsum : (∑ s ∈ range (M + 1 + 1),
            ((s - (M + 1) : ℕ) : ℚ) * secondDifference f s) = 0 := by
          apply sum_eq_zero
          intro s hs
          rw [hz s hs]
          simp
        rw [hzsum]
        simp
      · have hrM : r ≤ M := by omega
        have hc : ((M + 1 - r : ℕ) : ℚ) = (M - r : ℕ) + 1 := by
          rw [show M + 1 - r = (M - r) + 1 by omega]
          push_cast
          rfl
        have hd : secondDifference f (M + 1) =
            f M - 2 * f (M + 1) + f (M + 1 + 1) := by
          simp [secondDifference]
        rw [sum_range_succ, hd, hc]
        have hi := ih hrM
        linear_combination hi

private theorem K_decreasing {L : ℕ} (hL : 0 < L) (s : ℕ) :
    K L (s + 1) ≤ K L s := by
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  by_cases hs : s + 1 ≤ L
  · rw [K_of_le hs, K_of_le (by omega : s ≤ L)]
    push_cast
    have he : 2 / (L : ℚ) - ((s : ℚ) + 1) / (L : ℚ) ^ 2 =
        2 / (L : ℚ) - (s : ℚ) / (L : ℚ) ^ 2 - 1 / (L : ℚ) ^ 2 := by ring
    rw [he]
    exact sub_le_self _ (by positivity)
  · rw [K_of_ge hL (by omega : L ≤ s + 1), K_of_ge hL (by omega : L ≤ s)]
    apply inv_anti₀ (by exact_mod_cast (by omega : 0 < s))
    exact_mod_cast (Nat.le_succ s)

private theorem K_secondDifference_nonneg {L : ℕ} (hL : 0 < L) (s : ℕ) :
    0 ≤ secondDifference (K L) s := by
  by_cases hs0 : s = 0
  · simp [secondDifference, hs0]
  simp only [secondDifference, if_neg hs0]
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL
  have hs : 0 < s := by omega
  have hsq : (0 : ℚ) < s := by exact_mod_cast hs
  have hsq1 : (0 : ℚ) < s + 1 := by positivity
  have hcast : ((s - 1 : ℕ) : ℚ) = s - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s)]
    norm_num
  rcases lt_trichotomy s L with h | h | h
  · rw [K_of_le (by omega : s - 1 ≤ L), K_of_le h.le,
      K_of_le (by omega : s + 1 ≤ L), hcast]
    push_cast
    ring_nf
    exact le_rfl
  · subst s
    rw [K_of_le (by omega : L - 1 ≤ L), K_of_ge hL le_rfl,
      K_of_ge hL (by omega : L ≤ L + 1), hcast]
    push_cast
    have he : 2 / (L : ℚ) - ((L : ℚ) - 1) / (L : ℚ) ^ 2 -
        2 * (L : ℚ)⁻¹ + ((L : ℚ) + 1)⁻¹ =
        1 / ((L : ℚ) ^ 2 * (L + 1)) := by field_simp; ring
    rw [he]
    positivity
  · have hs1 : (0 : ℚ) < s - 1 := by
      have hsq2 : (1 : ℚ) < s := by exact_mod_cast (by omega : 1 < s)
      linarith
    rw [K_of_ge hL (by omega : L ≤ s - 1), K_of_ge hL h.le,
      K_of_ge hL (by omega : L ≤ s + 1), hcast]
    push_cast
    have he : ((s : ℚ) - 1)⁻¹ - 2 * (s : ℚ)⁻¹ + ((s : ℚ) + 1)⁻¹ =
        2 / (((s : ℚ) - 1) * s * (s + 1)) := by
      field_simp
      ring
    rw [he]
    positivity

private theorem overlap_card (s : ℕ) (x y : ℤ) :
    ((Ico x (x + s) ∩ Ico y (y + s)).card : ℚ) =
      ((s - (x - y).natAbs : ℕ) : ℚ) := by
  rw [Ico_inter_Ico, Int.card_Ico]
  congr 1
  have habs := Int.natCast_natAbs (x - y)
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_left (by omega : x + (s : ℤ) ≤ y + s)]
    rw [abs_of_nonpos (by omega : x - y ≤ 0)] at habs
    omega
  · rw [max_eq_left h, min_eq_right (by omega : y + (s : ℤ) ≤ x + s)]
    rw [abs_of_nonneg (by omega : 0 ≤ x - y)] at habs
    omega

/-- A tent is the Gram kernel of finite integer intervals. -/
private theorem tent_psd {ι : Type*} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ) (s : ℕ) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, c i * c j * ((s - (x i - x j).natAbs : ℕ) : ℚ) := by
  classical
  let I : ι → Finset ℤ := fun i => Ico (x i) (x i + s)
  let U := S.biUnion I
  let v : ι → ℤ → ℚ := fun i u => if u ∈ I i then c i else 0
  have he : ∀ i ∈ S, ∀ j ∈ S,
      c i * c j * ((s - (x i - x j).natAbs : ℕ) : ℚ) =
        ∑ u ∈ U, v i u * v j u := by
    intro i hi j hj
    have hf : U.filter (fun u => u ∈ I i ∧ u ∈ I j) = I i ∩ I j := by
      ext u
      simp only [mem_filter, mem_inter]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨mem_biUnion.mpr ⟨i, hi, h.1⟩, h⟩
    calc
      _ = ∑ u ∈ U.filter (fun u => u ∈ I i ∧ u ∈ I j), c i * c j := by
        rw [hf, sum_const]
        simp only [nsmul_eq_mul]
        rw [show ((I i ∩ I j).card : ℚ) =
          ((s - (x i - x j).natAbs : ℕ) : ℚ) from overlap_card s (x i) (x j)]
        ring
      _ = _ := by
        rw [sum_filter]
        apply sum_congr rfl
        intro u hu
        by_cases hiu : u ∈ I i <;> by_cases hju : u ∈ I j <;> simp [v, hiu, hju]
  have hgram : (∑ i ∈ S, ∑ j ∈ S,
      c i * c j * ((s - (x i - x j).natAbs : ℕ) : ℚ)) =
      ∑ u ∈ U, (∑ i ∈ S, v i u) ^ 2 := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, ∑ u ∈ U, v i u * v j u := by
        apply sum_congr rfl
        intro i hi
        apply sum_congr rfl
        intro j hj
        exact he i hi j hj
      _ = ∑ i ∈ S, ∑ u ∈ U, ∑ j ∈ S, v i u * v j u := by
        apply sum_congr rfl
        intro i hi
        rw [sum_comm]
      _ = ∑ u ∈ U, ∑ i ∈ S, ∑ j ∈ S, v i u * v j u := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro u hu
        simp_rw [← mul_sum]
        rw [← sum_mul, pow_two]
  rw [hgram]
  exact sum_nonneg (fun u hu => sq_nonneg _)

private def quadratic {ι : Type*} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ)
    (f : ℕ → ℚ) : ℚ :=
  ∑ i ∈ S, ∑ j ∈ S, c i * c j * f (x i - x j).natAbs

private theorem quadratic_add {ι : Type*} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ)
    (f g : ℕ → ℚ) :
    quadratic S x c (fun r => f r + g r) = quadratic S x c f + quadratic S x c g := by
  simp [quadratic, mul_add, sum_add_distrib]

private theorem quadratic_scale {ι : Type*} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ)
    (a : ℚ) (f : ℕ → ℚ) :
    quadratic S x c (fun r => a * f r) = a * quadratic S x c f := by
  unfold quadratic
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, a * (c i * c j * f (x i - x j).natAbs) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp_rw [← mul_sum]

private theorem quadratic_sum {ι κ : Type*} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ)
    (T : Finset κ) (f : κ → ℕ → ℚ) :
    quadratic S x c (fun r => ∑ k ∈ T, f k r) = ∑ k ∈ T, quadratic S x c (f k) := by
  unfold quadratic
  simp_rw [mul_sum]
  calc
    _ = ∑ i ∈ S, ∑ k ∈ T, ∑ j ∈ S,
        c i * c j * f k (x i - x j).natAbs := by
      apply sum_congr rfl
      intro i hi
      rw [sum_comm]
    _ = _ := sum_comm

private theorem quadratic_const {ι : Type*} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ)
    (a : ℚ) : quadratic S x c (fun _ => a) = a * (∑ i ∈ S, c i) ^ 2 := by
  have he : quadratic S x c (fun _ => a) = a * quadratic S x c (fun _ => 1) := by
    simpa using quadratic_scale S x c a (fun _ => 1)
  rw [he]
  unfold quadratic
  simp only [mul_one]
  simp_rw [← mul_sum, ← sum_mul]
  ring

/-- Positive semidefiniteness for arbitrary rational coefficients, including repeated points. -/
theorem kernel_psd {ι : Type*} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ)
    {L : ℕ} (hL : 0 < L) :
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, c i * c j * K L (x i - x j).natAbs := by
  classical
  let M := ∑ i ∈ S, ∑ j ∈ S, (x i - x j).natAbs
  have hbound : ∀ i ∈ S, ∀ j ∈ S, (x i - x j).natAbs ≤ M := by
    intro i hi j hj
    have h₁ : (x i - x j).natAbs ≤ ∑ k ∈ S, (x i - x k).natAbs :=
      single_le_sum (f := fun k => (x i - x k).natAbs)
        (fun _ _ => Nat.zero_le _) hj
    have h₂ : (∑ k ∈ S, (x i - x k).natAbs) ≤ M := by
      dsimp [M]
      exact single_le_sum (f := fun k => ∑ j ∈ S, (x k - x j).natAbs)
        (fun _ _ => Nat.zero_le _) hi
    exact h₁.trans h₂
  change 0 ≤ quadratic S x c (K L)
  have he : quadratic S x c (K L) = quadratic S x c (fun r =>
      K L M + ((M - r : ℕ) : ℚ) * (K L M - K L (M + 1)) +
        ∑ s ∈ range (M + 1), ((s - r : ℕ) : ℚ) * secondDifference (K L) s) := by
    unfold quadratic
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    exact congrArg (fun z : ℚ => c i * c j * z)
      (finite_tent_expansion (K L) (hbound i hi j hj))
  rw [he, quadratic_add, quadratic_add, quadratic_const, quadratic_sum]
  apply add_nonneg
  · apply add_nonneg
    · exact mul_nonneg (K_nonneg L M) (sq_nonneg _)
    · have heq : quadratic S x c (fun r =>
          ((M - r : ℕ) : ℚ) * (K L M - K L (M + 1))) =
          (K L M - K L (M + 1)) *
            quadratic S x c (fun r => ((M - r : ℕ) : ℚ)) := by
        simpa only [mul_comm] using
          quadratic_scale S x c (K L M - K L (M + 1))
            (fun r => ((M - r : ℕ) : ℚ))
      rw [heq]
      exact mul_nonneg (sub_nonneg.mpr (K_decreasing hL M)) (tent_psd S x c M)
  · apply sum_nonneg
    intro s hs
    have heq : quadratic S x c (fun r =>
        ((s - r : ℕ) : ℚ) * secondDifference (K L) s) =
        secondDifference (K L) s *
          quadratic S x c (fun r => ((s - r : ℕ) : ℚ)) := by
      simpa only [mul_comm] using quadratic_scale S x c
        (secondDifference (K L) s) (fun r => ((s - r : ℕ) : ℚ))
    rw [heq]
    exact mul_nonneg (K_secondDifference_nonneg hL s) (tent_psd S x c s)

/-- The bilinear energy of two finite sets of natural points. -/
def energy (L : ℕ) (A B : Finset ℕ) : ℚ :=
  ∑ x ∈ A, ∑ y ∈ B, K L (Nat.dist x y)

theorem energy_nonneg (L : ℕ) (A B : Finset ℕ) :
    0 ≤ energy L A B := by
  exact sum_nonneg (fun x hx => sum_nonneg (fun y hy => K_nonneg L _))

private theorem energy_symm (L : ℕ) (A B : Finset ℕ) : energy L A B = energy L B A := by
  unfold energy
  rw [sum_comm]
  apply sum_congr rfl
  intro y hy
  apply sum_congr rfl
  intro x hx
  rw [Nat.dist_comm]

theorem int_distance (x y : ℕ) : ((x : ℤ) - (y : ℤ)).natAbs = Nat.dist x y := by
  rcases le_total x y with h | h
  · rw [Int.natAbs_natCast_sub_natCast_of_le h, Nat.dist_eq_sub_of_le h]
  · rw [Int.natAbs_natCast_sub_natCast_of_ge h, Nat.dist_eq_sub_of_le_right h]

/-- Rational Cauchy Schwarz for the kernel; disjointness is unnecessary. -/
theorem energy_sq_le {L : ℕ} (hL : 0 < L) (A B : Finset ℕ) :
    energy L A B ^ 2 ≤ energy L A A * energy L B B := by
  classical
  have hquad : ∀ u : ℚ,
      0 ≤ energy L A A * (u * u) + 2 * energy L A B * u + energy L B B := by
    intro u
    have hp := kernel_psd (A.disjSum B)
      (Sum.elim (fun x : ℕ => (x : ℤ)) (fun x : ℕ => (x : ℤ)))
      (Sum.elim (fun _ : ℕ => u) (fun _ : ℕ => (1 : ℚ))) hL
    simp only [sum_disjSum, Sum.elim_inl, Sum.elim_inr, int_distance] at hp
    have heq : (∑ i ∈ A, ((∑ j ∈ A, u * u * K L (Nat.dist i j)) +
          ∑ j ∈ B, u * 1 * K L (Nat.dist i j))) +
        (∑ i ∈ B, ((∑ j ∈ A, 1 * u * K L (Nat.dist i j)) +
          ∑ j ∈ B, 1 * 1 * K L (Nat.dist i j))) =
        energy L A A * (u * u) + 2 * energy L A B * u + energy L B B := by
      simp only [sum_add_distrib, one_mul, mul_one]
      simp_rw [← mul_sum]
      change (u * u * energy L A A + u * energy L A B) +
        (u * energy L B A + energy L B B) = _
      rw [energy_symm L B A]
      ring
    rw [heq] at hp
    exact hp
  have hd := discrim_le_zero hquad
  dsimp [discrim] at hd
  nlinarith

#print axioms K_zero
#print axioms K_of_le
#print axioms K_of_ge
#print axioms K_nonneg
#print axioms w_nonneg
#print axioms inv_eq_K_add_w
#print axioms K_le_inv
#print axioms finite_tent_expansion
#print axioms tent_psd
#print axioms kernel_psd
#print axioms energy_nonneg
#print axioms energy_symm
#print axioms energy_sq_le

end D5.S3.Arith.ErdosNicolas
