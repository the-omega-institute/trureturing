/- GID: D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation
   generality: I
   mirror-B: D5/B/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.claim; result=D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.result; claim=D5/S3/Geometry/BouafiaNegativeTypeDiversityDeletionRefutation.claim
   digest: A five-point scaled Hamming metric refutes irreversible diversity-weight deletion. -/

/-
admission_basis: open-problem-resolution (#25745; Refuted)
result: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none.
The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Every private theorem below is bind-only, with escape_witness: none and
Direct frozen dependencies: none. Consumers:
  bits_injective -> metric
  hamming_table -> negative_type, similarity_eq
  c_pos -> metric, embedding_dist, negative_type
  embedding_dist -> negative_type
  negative_type -> result
  similarity_eq -> result
  inverse0 -> weighting0, first_stop
  inverse1 -> weighting1, first_stop
  weighting0 -> active1, first_stop
  weighting1 -> first_stop, mass1, output1
  active1 -> first_stop, mass1, output1
  first_stop -> result
  mass1 -> output1
  output1 -> not_maximizing
  energy_gap -> not_maximizing
  not_maximizing -> result

Source: Philippe Bouafia, Magnitude and diversity of trees,
arXiv:2605.03681v1, pp. 4, 16–18; preregistration #25745.
Only the negative-type question on p. 18 is refuted. The stopping condition
is the nonnegative condition in Theorem 4's proof; the printed Algorithm 1
has the reversed test. Nonempty active sets, nonzero determinants, existence
of a first stop and a positive normalization are explicit in claim.
The principal matrices use Matrix.submatrix directly, and the quadratic
energy is written as the literal double sum, without forwarding definitions.
The metric and square-root embedding are the fixed five-point data;
no assertion about ordinary Euclidean distance or minimality is made.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

import Mathlib.InformationTheory.Hamming

noncomputable section

namespace D5.S3.Geometry.BouafiaNegativeTypeDiversityDeletionRefutation

open scoped BigOperators

/-- Literally, the square-root metric embeds isometrically into a Hilbert space.
For a finite space, a finite-dimensional real Hilbert space suffices. -/
def NegativeType {n : ℕ} [MetricSpace (Fin n)] : Prop :=
  ∃ m : ℕ, ∃ f : Fin n → EuclideanSpace ℝ (Fin m),
    Function.Injective f ∧
    ∀ i j : Fin n, dist (f i) (f j) = Real.sqrt (dist i j)

/-- The source's scale-one exponential similarity kernel. -/
def similarity {n : ℕ} [MetricSpace (Fin n)] : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => Real.exp (-dist i j)

/-- One solve, extended by zero outside A; FirstStop guards every inverse. -/
def weighting {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (A : Finset (Fin n)) :
    Fin n → ℝ :=
  fun i => if hi : i ∈ A then
    (((Z.submatrix (fun i : A => i.val) (fun j : A => j.val)))⁻¹).mulVec (fun _ => 1) ⟨i, hi⟩ else 0

/-- The active set before solve k, starting with every point at k = 0. -/
def active {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | k + 1 => (active Z k).filter (fun i => 0 < weighting Z (active Z k) i)

/-- The intended stopping condition, as specified in the proof of Theorem 4. -/
def stopped {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Prop :=
  ∀ i : Fin n, 0 ≤ weighting Z (active Z k) i

/-- Existence of a first stop includes nonempty active sets and genuine inverses. -/
def FirstStop {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Prop :=
  (∀ l : ℕ, l ≤ k → (active Z l).Nonempty ∧ ((Z.submatrix (fun i : (active Z l) => i.val) (fun j : (active Z l) => j.val))).det ≠ 0) ∧
  (∀ l : ℕ, l < k → ¬ stopped Z l) ∧ stopped Z k

/-- Total weight used for normalization. -/
def mass {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : ℝ :=
  ∑ i, weighting Z (active Z k) i

/-- The source's returned probability; the claim requires a positive denominator. -/
def output {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Fin n → ℝ :=
  fun i => weighting Z (active Z k) i / mass Z k

/-- Minimizes average similarity over exactly the probability simplex. -/
def DiversityMaximizing {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n → ℝ) : Prop :=
  (∃ μ : Convexity.StdSimplex ℝ (Fin n), ∀ i : Fin n, μ.weights i = p i) ∧
  ∀ ν : Convexity.StdSimplex ℝ (Fin n), (∑ i, ∑ j, Z i j * p j * p i) ≤ (∑ i, ∑ j, Z i j * ν.weights j * ν.weights i)

/-- Question (2) after Theorem 4: all nonempty finite metric spaces of negative type.
The existential conjunct asserts that the algorithm actually returns an output. -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → ∀ metric : MetricSpace (Fin n),
    letI := metric
    NegativeType (n := n) →
      (∃ k : ℕ, FirstStop (similarity (n := n)) k) ∧
      ∀ k : ℕ, FirstStop (similarity (n := n)) k →
        0 < mass (similarity (n := n)) k ∧
        DiversityMaximizing (similarity (n := n)) (output (similarity (n := n)) k)

end D5.S3.Geometry.BouafiaNegativeTypeDiversityDeletionRefutation

namespace D5.S3.Geometry.BouafiaNegativeTypeDiversityDeletionRefutation

set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

private def bits : Fin 5 → Fin 5 → Bool :=
  ![![false,false,false,false,false], ![true,true,false,false,true],
    ![false,false,true,false,true], ![false,true,false,true,true],
    ![false,false,true,true,true]]

private def H : Matrix (Fin 5) (Fin 5) ℕ :=
  !![0,3,2,3,3; 3,0,3,2,4; 2,3,0,3,1; 3,2,3,0,2; 3,4,1,2,0]

private theorem bits_injective : Function.Injective bits := by decide

private theorem hamming_table (i j : Fin 5) : hammingDist (bits i) (bits j) = H i j := by
  fin_cases i <;> fin_cases j <;> decide

private def c : ℝ := Real.log (20/19)

private theorem c_pos : 0 < c := Real.log_pos (by norm_num)

@[instance_reducible] private def metric : MetricSpace (Fin 5) where
  dist i j := c * hammingDist (bits i) (bits j)
  dist_self i := by simp only [hammingDist_self, Nat.cast_zero, mul_zero]
  dist_comm i j := by rw [hammingDist_comm]
  dist_triangle i j k := by
    rw [← mul_add, ← Nat.cast_add]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hammingDist_triangle (bits i) (bits j) (bits k)) c_pos.le
  eq_of_dist_eq_zero := by
    intro i j hij
    apply bits_injective
    apply eq_of_hammingDist_eq_zero
    exact_mod_cast (mul_eq_zero.mp hij).resolve_left c_pos.ne'

private def embedding (i : Fin 5) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (fun j => if bits i j then Real.sqrt c else 0)

private theorem embedding_dist (i j : Fin 5) :
    dist (embedding i) (embedding j) = Real.sqrt (c * H i j) := by
  rw [EuclideanSpace.dist_eq]
  congr 1
  fin_cases i <;> fin_cases j <;>
    norm_num [embedding, bits, H, Fin.sum_univ_succ, Real.dist_eq, sq_abs,
      Real.sq_sqrt c_pos.le] <;> ring

private theorem negative_type : @NegativeType 5 metric := by
  refine ⟨5, embedding, ?_, ?_⟩
  · intro i j hij
    apply metric.eq_of_dist_eq_zero
    change c * hammingDist (bits i) (bits j) = 0
    rw [hamming_table]
    have hzero : Real.sqrt (c * H i j) = 0 := by
      rw [← embedding_dist, hij, dist_self]
    exact (Real.sqrt_eq_zero (mul_nonneg c_pos.le (Nat.cast_nonneg _))).mp hzero
  · intro i j
    change dist (embedding i) (embedding j) = Real.sqrt (c * hammingDist (bits i) (bits j))
    rw [hamming_table, embedding_dist]

private def Z : Matrix (Fin 5) (Fin 5) ℝ := fun i j => (19/20) ^ H i j

private theorem similarity_eq : @similarity 5 metric = Z := by
  ext i j
  change Real.exp (-(c * (hammingDist (bits i) (bits j) : ℝ))) = (19/20) ^ H i j
  rw [hamming_table]
  have hc : Real.exp (-c) = (19/20 : ℝ) := by
    rw [c, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [← neg_mul, mul_comm (-c), Real.exp_nat_mul, hc]


private def R0 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![11371488911800/1674313857801, -20878796000/42931124559, -9564631391800/1674313857801, -4389760000000/1674313857801, 3961758400000/1674313857801;
    -20878796000/42931124559, 1640911280000/186034873089, -3975668452000/558104619267, -4320448000000/558104619267, 3899204320000/558104619267;
    -9564631391800/1674313857801, -3975668452000/558104619267, 36030445871800/1674313857801, 15074490712000/1674313857801, -29918555200000/1674313857801;
    -4389760000000/1674313857801, -4320448000000/558104619267, 15074490712000/1674313857801, 22702144000000/1674313857801, -20488684960000/1674313857801;
    3961758400000/1674313857801, 3899204320000/558104619267, -29918555200000/1674313857801, -20488684960000/1674313857801, 35663488000000/1674313857801]

private def R1 : Matrix (Fin 5) (Fin 5) ℝ :=
  !![58064200/11018319, -27436000/11018319, 0, 0, -27436000/11018319;
    -27436000/11018319, 11592560000/2794980253, 0, 0, -10425680000/8384940759;
    0, 0, 0, 0, 0;
    0, 0, 0, 0, 0;
    -27436000/11018319, -10425680000/8384940759, 0, 0, 11592560000/2794980253]

private def A : Finset (Fin 5) := {0,1,4}

private def w0 : Fin 5 → ℝ :=
  ![188194292000/558104619267, 254397360000/558104619267,
    -101751788000/558104619267, -21051416000/558104619267,
    305206400000/558104619267]

private def w1 : Fin 5 → ℝ :=
  ![3192200/11018319, 4564000/11018319, 0, 0, 4564000/11018319]

private def p : Fin 5 → ℝ := ![15961/61601,22820/61601,0,0,22820/61601]

private def better : Fin 5 → ℝ :=
  ![15945039/61601000,22797180/61601000,0,61601/61601000,22797180/61601000]

private theorem inverse0 : (Z.submatrix (fun i : (Finset.univ : Finset (Fin 5)) => i.val) (fun j : (Finset.univ : Finset (Fin 5)) => j.val)) * (R0.submatrix (fun i : (Finset.univ : Finset (Fin 5)) => i.val) (fun j : (Finset.univ : Finset (Fin 5)) => j.val)) = 1 := by
  ext ⟨i,hi⟩ ⟨j,hj⟩
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [Z,H,R0,Fin.sum_univ_succ,Matrix.one_apply]

private theorem inverse1 : (Z.submatrix (fun i : A => i.val) (fun j : A => j.val)) * (R1.submatrix (fun i : A => i.val) (fun j : A => j.val)) = 1 := by
  ext ⟨i,hi⟩ ⟨j,hj⟩
  change (∑ k : A, Z i k.val * R1 k.val j) =
    (1 : Matrix A A ℝ) ⟨i,hi⟩ ⟨j,hj⟩
  rw [Finset.sum_coe_sort A (fun k => Z i k * R1 k j)]
  simp only [A,Finset.mem_insert,Finset.mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    norm_num [Z,H,R1,A,Matrix.one_apply]

private theorem weighting0 : weighting Z Finset.univ = w0 := by
  unfold weighting
  rw [Matrix.inv_eq_right_inv inverse0]
  funext i
  simp only [Finset.mem_univ, dite_true, Matrix.submatrix_apply,
    Matrix.mulVec, dotProduct, mul_one, Finset.sum_coe_sort]
  fin_cases i <;> norm_num [R0,w0,Fin.sum_univ_succ]

private theorem weighting1 : weighting Z A = w1 := by
  unfold weighting
  rw [Matrix.inv_eq_right_inv inverse1]
  funext i
  by_cases hi : i ∈ A
  · rw [dite_eq_left hi]
    simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,mul_one,Finset.sum_coe_sort]
    fin_cases i <;> norm_num [A,R1,w1] at *
  · rw [dite_eq_right hi]
    fin_cases i <;> norm_num [A,w1] at *

private theorem active1 : active Z 1 = A := by
  rw [active,active,weighting0]
  ext i
  fin_cases i <;> norm_num [w0,A]

private theorem first_stop : FirstStop Z 1 := by
  constructor
  · intro l hl
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl with rfl | rfl
    · exact ⟨by simp [active], Matrix.det_ne_zero_of_right_inverse inverse0⟩
    · rw [active1]
      exact ⟨by simp [A], Matrix.det_ne_zero_of_right_inverse inverse1⟩
  constructor
  · intro l hl hs
    have hl0 : l = 0 := Nat.lt_one_iff.mp hl
    subst l
    have hn := hs (2 : Fin 5)
    change 0 ≤ weighting Z Finset.univ 2 at hn
    rw [weighting0] at hn
    norm_num [w0] at hn
  · intro i
    rw [active1,weighting1]
    fin_cases i <;> norm_num [w1]

private theorem mass1 : mass Z 1 = 12320200/11018319 := by
  unfold mass
  rw [active1,weighting1]
  norm_num [w1,Fin.sum_univ_succ]

private theorem output1 : output Z 1 = p := by
  funext i
  rw [output,mass1,active1,weighting1]
  fin_cases i <;> norm_num [w1,p]

private def competitor : Convexity.StdSimplex ℝ (Fin 5) where
  weights := Finsupp.equivFunOnFinite.symm better
  nonneg := by
    intro i
    change 0 ≤ better i
    fin_cases i <;> norm_num [better]
  total := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    change (∑ i, better i) = 1
    norm_num [better,Fin.sum_univ_succ]

private theorem energy_gap : (∑ i, ∑ j, Z i j * p j * p i) - (∑ i, ∑ j, Z i j * better j * better i) = 1707687919/246404000000000 := by
  norm_num [Z,H,p,better,Fin.sum_univ_succ]

private theorem not_maximizing : ¬ DiversityMaximizing Z (output Z 1) := by
  intro hm
  have h := hm.2 competitor
  rw [output1] at h
  change (∑ i, ∑ j, Z i j * p j * p i) ≤ (∑ i, ∑ j, Z i j * better j * better i) at h
  have hg := energy_gap
  linarith

theorem result : ¬ D5.S3.Geometry.BouafiaNegativeTypeDiversityDeletionRefutation.claim := by
  intro hc
  have h := (hc 5 (by norm_num) metric negative_type).2 1
  rw [similarity_eq] at h
  exact not_maximizing (h first_stop).2

end D5.S3.Geometry.BouafiaNegativeTypeDiversityDeletionRefutation
