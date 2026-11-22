/- GID: D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterJointTaylorReplay
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Horner evaluation of the joint Taylor polynomial and its mixed jet. -/

import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMomentPolynomial
import D5.S3.Quantum.Analysis.RefinedBMVPositiveCenterMixedJet

/-! # Horner evaluation of the positive-center joint Taylor jet -/

namespace RefinedBMV.PositiveCenter.SmallCorner

open scoped BigOperators

set_option autoImplicit false

/-- Horner evaluation of a consecutive block of coefficients. -/
def cornerJetHorner {R : Type*} [Add R] [Mul R] (x zero : MixedJet R)
    (c : ℕ → MixedJet R) (start : ℕ) : ℕ → MixedJet R
  | 0 => zero
  | n + 1 => ((cornerJetHorner x zero c (start + 1) n).mul x).add (c start)

/-- Evaluate a polynomial over the triangle `i + j < n`, one row at a time. -/
def cornerJointHorner {R : Type*} [Add R] [Mul R] (u v zero : MixedJet R)
    (c : ℕ → ℕ → MixedJet R) (n : ℕ) : MixedJet R :=
  cornerJetHorner u zero (fun i ↦ cornerJetHorner v zero (c i) 0 (n - i)) 0 n

private noncomputable def firstPower (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (n + 1) * x ^ n

private noncomputable def secondPower (x : ℝ) : ℕ → ℝ
  | 0 | 1 => 0
  | n + 2 => (n + 2) * (n + 1) * x ^ n

private theorem firstPower_succ (x : ℝ) (n : ℕ) :
    firstPower x (n + 1) = firstPower x n * x + x ^ n := by
  cases n with
  | zero => simp [firstPower]
  | succ n =>
    simp only [firstPower, pow_succ x n, Nat.cast_succ]
    ring

private theorem secondPower_succ (x : ℝ) (n : ℕ) :
    secondPower x (n + 1) = secondPower x n * x + 2 * firstPower x n := by
  cases n with
  | zero => simp [secondPower, firstPower]
  | succ n =>
    cases n with
    | zero => norm_num [secondPower, firstPower]
    | succ n =>
      simp only [secondPower, firstPower, pow_succ x n, Nat.cast_succ]
      ring

private noncomputable def affinePower (t a b : ℝ) (n : ℕ) : MixedJet ℝ :=
  ⟨t ^ n, a * firstPower t n, b * firstPower t n, a * b * secondPower t n⟩

private theorem affinePower_succ (t a b : ℝ) (n : ℕ) :
    (affinePower t a b n).mul ⟨t, a, b, 0⟩ = affinePower t a b (n + 1) := by
  simp only [affinePower, MixedJet.mul, firstPower_succ, secondPower_succ, pow_succ t n]
  congr 1 <;> ring

private noncomputable def jetSum (n : ℕ) (f : ℕ → MixedJet ℝ) : MixedJet ℝ :=
  ⟨∑ i ∈ Finset.range n, (f i).value, ∑ i ∈ Finset.range n, (f i).du,
    ∑ i ∈ Finset.range n, (f i).dv, ∑ i ∈ Finset.range n, (f i).duv⟩

private theorem jetSum_succ (n : ℕ) (f : ℕ → MixedJet ℝ) :
    jetSum (n + 1) f = (jetSum n fun i ↦ f (i + 1)).add (f 0) := by
  simp only [jetSum, MixedJet.add, Finset.sum_range_succ']

private theorem jetSum_mul (n : ℕ) (f : ℕ → MixedJet ℝ) (x : MixedJet ℝ) :
    (jetSum n f).mul x = jetSum n (fun i ↦ (f i).mul x) := by
  simp only [jetSum, MixedJet.mul, Finset.sum_add_distrib, Finset.sum_mul]

private theorem jet_mul_assoc (x y z : MixedJet ℝ) : (x.mul y).mul z = x.mul (y.mul z) := by
  simp only [MixedJet.mul]
  congr 1 <;> ring

private theorem jet_mul_unit (x : MixedJet ℝ) : x.mul ⟨1, 0, 0, 0⟩ = x := by
  cases x
  simp [MixedJet.mul]

private theorem cornerJetHorner_eq_jetSum (t a b : ℝ) (c : ℕ → MixedJet ℝ) (start n : ℕ) :
    cornerJetHorner ⟨t, a, b, 0⟩ ⟨0, 0, 0, 0⟩ c start n =
      jetSum n (fun i ↦ (c (start + i)).mul (affinePower t a b i)) := by
  induction n generalizing start with
  | zero => simp [cornerJetHorner, jetSum]
  | succ n ih =>
    rw [cornerJetHorner, ih, jetSum_succ, jetSum_mul]
    simp only [jet_mul_assoc, affinePower_succ, Nat.add_zero]
    have hzero : affinePower t a b 0 = ⟨1, 0, 0, 0⟩ := by
      simp [affinePower, firstPower, secondPower]
    simp only [hzero, jet_mul_unit, Nat.add_right_comm start 1, Nat.add_assoc]

private theorem sum_triangle {R : Type*} [AddCommMonoid R] (n : ℕ) (f : ℕ → ℕ → R) :
    (∑ m ∈ Finset.range n, ∑ i ∈ Finset.range (m+1), f i (m-i)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i), f i j := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ' (fun i ↦ ∑ j ∈ Finset.range (n+1-i), f i j),
      Finset.sum_range_succ' (fun m ↦ ∑ i ∈ Finset.range (m+1), f i (m-i))]
    simp only [Nat.sub_zero, Nat.add_sub_add_right]
    have hdiag (m : ℕ) :
        (∑ i ∈ Finset.range (m+1+1), f i (m+1-i)) =
          (∑ i ∈ Finset.range (m+1), f (i+1) (m-i)) + f 0 (m+1) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
    simp_rw [hdiag]
    rw [Finset.sum_add_distrib, ih (fun i j ↦ f (i + 1) j),
      Finset.sum_range_succ' (fun j ↦ f 0 j)]
    simp only [Nat.zero_sub]
    rw [show (∑ i ∈ Finset.range 1, f i 0) = f 0 0 from
      Finset.sum_range_one (fun i ↦ f i 0)]
    ac_rfl

private theorem sum_power_joint_fst (c : ℕ → ℕ → ℝ) (x y : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1-i),
        c i j * firstPower x i * y ^ j) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i),
        c (i+1) j * ((i : ℝ)+1) * x ^ i * y ^ j := by
  rw [Finset.sum_range_succ']
  simp only [firstPower, Nat.add_sub_add_right, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, mul_assoc]

private theorem sum_power_joint_snd (c : ℕ → ℕ → ℝ) (x y : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1-i),
        c i j * x ^ i * firstPower y j) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i),
        c i (j+1) * x ^ i * ((j : ℝ)+1) * y ^ j := by
  rw [Finset.sum_range_succ
    (fun i ↦ ∑ j ∈ Finset.range (n+1-i), c i j * x ^ i * firstPower y j) n]
  rw [show n + 1 - n = 1 by omega]
  simp only [Finset.sum_range_one, firstPower.eq_1, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [show n + 1 - i = n - i + 1 by have := Finset.mem_range.mp hi; omega,
    Finset.sum_range_succ']
  simp only [firstPower, mul_zero, add_zero, mul_assoc]

private theorem sum_power_joint_mixed (c : ℕ → ℕ → ℝ) (x y : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+2), ∑ j ∈ Finset.range (n+2-i),
        c i j * firstPower x i * firstPower y j) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i),
        c (i+1) (j+1) * ((i : ℝ)+1) * x ^ i * ((j : ℝ)+1) * y ^ j := by
  rw [Finset.sum_range_succ']
  simp only [firstPower.eq_1, firstPower.eq_2, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  simp_rw [show ∀ i, n + 2 - (i + 1) = n + 1 - i by intro i; omega]
  simpa only [mul_assoc] using
    (sum_power_joint_snd (fun i j ↦ c (i+1) j * ((i : ℝ)+1)) x y n)

private theorem joint_horner_eq_sums (c : ℕ → ℕ → ℝ) (u v : ℝ) (n : ℕ) :
    cornerJointHorner ⟨u, 1, 0, 0⟩ ⟨v, 0, 1, 0⟩ ⟨0, 0, 0, 0⟩
      (fun i j ↦ ⟨c i j, 0, 0, 0⟩) n =
      ⟨∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i), c i j * u ^ i * v ^ j,
       ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i), c i j * firstPower u i * v ^ j,
       ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i), c i j * u ^ i * firstPower v j,
       ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range (n-i),
         c i j * firstPower u i * firstPower v j⟩ := by
  simp only [cornerJointHorner, cornerJetHorner_eq_jetSum, jetSum, affinePower, MixedJet.mul,
    zero_mul, mul_zero, zero_add, add_zero, one_mul, Finset.sum_const_zero,
    Finset.sum_mul]
  congr 1 <;> exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ac_rfl))

private theorem jointTaylorPolynomial_rows {p : ℕ} (hp : 0 < p) (a b : ℕ) (u v : ℝ) :
    jointTaylorPolynomial p a b u v =
      ∑ i ∈ Finset.range (23-a-b), ∑ j ∈ Finset.range (23-a-b-i),
        momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs (a+i+2) (b+j)) *
          ((a+i).descFactorial a : ℝ) * ((b+j).descFactorial b : ℝ) * u^i * v^j := by
  rw [jointTaylorPolynomial_eq_normalized_moments hp]
  exact sum_triangle (23-a-b) (fun i j ↦
    momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs (a+i+2) (b+j)) *
      ((a+i).descFactorial a : ℝ) * ((b+j).descFactorial b : ℝ) * u^i * v^j)

/-- The triangular degree-22 Horner calculation has the four joint Taylor jet components. -/
theorem jointTaylorPolynomial_jet_eq_cornerJointHorner {p : ℕ} (hp : 0 < p) (u v : ℝ) :
    (⟨jointTaylorPolynomial p 0 0 u v, jointTaylorPolynomial p 1 0 u v,
      jointTaylorPolynomial p 0 1 u v, jointTaylorPolynomial p 1 1 u v⟩ : MixedJet ℝ) =
      cornerJointHorner ⟨u, 1, 0, 0⟩ ⟨v, 0, 1, 0⟩ ⟨0, 0, 0, 0⟩
        (fun i j ↦ ⟨momentHorner (3 / (p : ℝ)) (normalizedMomentCoeffs (i+2) j), 0, 0, 0⟩)
        23 := by
  rw [joint_horner_eq_sums, sum_power_joint_fst (n := 22), sum_power_joint_snd (n := 22),
    sum_power_joint_mixed (n := 21)]
  simp only [jointTaylorPolynomial_rows hp, Nat.descFactorial_zero, Nat.descFactorial_one,
    Nat.zero_add, Nat.add_comm 1, Nat.cast_add, Nat.cast_one, mul_one]
  congr 1 <;> exact Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl (fun j _ ↦ by ac_rfl))

#print axioms jointTaylorPolynomial_jet_eq_cornerJointHorner

end RefinedBMV.PositiveCenter.SmallCorner
