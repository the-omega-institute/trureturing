/- GID: D5/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/SmallSignedEntryTranscriptCompensation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small signed entries compensate complete finite native transcripts. -/

import D5.S0.Naming.GreenClassMeasure
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! A weak first link separates return perturbations from off - root observability. -/

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

noncomputable section
namespace D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
open Matrix Polynomial Finset
open scoped BigOperators

/-- A finite tridiagonal matrix; the last edge coordinate is unused. -/
def band {R : Type*} [Zero R] (n : ℕ) (d : R)
    (up down : Fin (n + 2) → R) : Matrix (Fin (n + 2)) (Fin (n + 2)) R :=
  fun i j => if i = j then d else if i.val + 1 = j.val then up i
    else if j.val + 1 = i.val then down j else 0

/-- The polynomial path whose first upper link is one and first lower link is X. -/
def normalizedPath (n : ℕ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ[X] :=
  band n (C (1 / 2)) (fun i => if i = 0 then 1 else C (1 / 8))
    (fun i => if i = 0 then X else C (1 / 8))

/-- The symmetric rational path with a weak first link. -/
def weakPath (n : ℕ) (epsilon : ℚ) : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
  band n (1 / 2) (fun i => if i = 0 then epsilon else 1 / 8)
    (fun i => if i = 0 then epsilon else 1 / 8)

private theorem band_far {R : Type*} [Zero R] (n : ℕ) (d : R)
    (up down : Fin (n + 2) → R) (i j : Fin (n + 2))
    (h : i.val + 1 < j.val) : band n d up down i j = 0 := by
  have hij : i ≠ j := by intro he; subst j; omega
  simp [band, hij, show i.val + 1 ≠ j.val by omega,
    show j.val + 1 ≠ i.val by omega]

private theorem normalized_power_zero (n k : ℕ) (j : Fin (n + 2))
    (h : k < j.val) : (normalizedPath n ^ k) 0 j = 0 := by
  induction k generalizing j with
  | zero =>
    have hj : (0 : Fin (n + 2)) ≠ j := by intro he; subst j; simp at h
    simp [Matrix.one_apply, hj]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : k < i.val
    · rw [ih i hi, zero_mul]
    · rw [show normalizedPath n i j = 0 from band_far _ _ _ _ i j (by omega), mul_zero]

private theorem normalized_power_diagonal (n k : ℕ) (hk : k < n + 2) :
    (normalizedPath n ^ k) 0 ⟨k, hk⟩ =
      if k = 0 then 1 else C ((1 / 8 : ℚ) ^ (k - 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < n + 2 := by omega
    rw [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin (n + 2))]
    · rw [ih hk']
      have hne : (⟨k, hk'⟩ : Fin (n + 2)) ≠ ⟨k + 1, hk⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      simp only [normalizedPath, band, if_neg hne, Fin.val_mk, if_pos rfl]
      by_cases h : k = 0
      · subst k; simp
      · have hz : (⟨k, hk'⟩ : Fin (n + 2)) ≠ 0 := by simpa [Fin.ext_iff] using h
        simp only [if_neg h, if_neg hz, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          ↓reduceIte, Nat.add_sub_cancel]
        rw [← map_mul]
        congr 1
        have hkp : k - 1 + 1 = k := by omega
        rw [← pow_succ, hkp]
    · intro i _ hi
      by_cases hki : k < i.val
      · rw [normalized_power_zero n k i hki, zero_mul]
      · have hi' : i.val ≠ k := by intro hh; apply hi; exact Fin.ext hh
        rw [show normalizedPath n i ⟨k + 1, hk⟩ = 0 from
          band_far _ _ _ _ _ _ (by simp; omega), mul_zero]
    · simp

/-- The polynomial root return correction after factoring one X. -/
def returnCorrection (n : ℕ) : ℕ → ℚ[X]
  | 0 => 0
  | k + 1 => C (1 / 2) * returnCorrection n k +
      (normalizedPath n ^ k) 0 (1 : Fin (n + 2))

private theorem normalized_root_step (n k : ℕ) :
    (normalizedPath n ^ (k + 1)) 0 0 =
      C (1 / 2) * (normalizedPath n ^ k) 0 0 +
      X * (normalizedPath n ^ k) 0 (1 : Fin (n + 2)) := by
  rw [pow_succ, Matrix.mul_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 2)))]
  rw [Finset.sum_eq_single (1 : Fin (n + 2))]
  · simp [normalizedPath, band, mul_comm]
  · intro i hi hne
    have hi0 : i ≠ 0 := by simpa using hi
    have hi1 : i.val ≠ 1 := by intro h; apply hne; exact Fin.ext h
    simp [normalizedPath, band, hi0, show i.val ≠ 0 by intro h; apply hi0; exact Fin.ext h,
      show 0 + 1 ≠ i.val by omega, show i.val + 1 ≠ 0 by omega]
  · simp

private theorem normalized_return_difference (n k : ℕ) :
    (normalizedPath n ^ k) 0 0 = C ((1 / 2 : ℚ)^k) + X * returnCorrection n k := by
  induction k with
  | zero => simp [returnCorrection]
  | succ k ih =>
    rw [normalized_root_step, ih, returnCorrection, pow_succ, map_mul]
    ring

private theorem scaled_edge (n : ℕ) (epsilon : ℚ) (i j : Fin (n + 2)) :
    (if i = 0 then 1 else epsilon) * weakPath n epsilon i j =
      (if j = 0 then 1 else epsilon) *
        (normalizedPath n i j).eval (epsilon^2) := by
  by_cases hij : i = j
  · subst j; simp [weakPath, normalizedPath, band]
  · by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := Ne.symm hij
      have hjv : j.val ≠ 0 := by intro h; apply hj; exact Fin.ext h
      simp only [weakPath, normalizedPath, band, if_neg hij, if_neg hj,
        ite_true, Fin.val_zero]
      have hb : j.val + 1 ≠ 0 := by omega
      simp only [if_neg hb]
      split_ifs <;> simp
    · by_cases hj : j = 0
      · subst j
        have hiv : i.val ≠ 0 := by intro h; apply hi; exact Fin.ext h
        simp only [weakPath, normalizedPath, band, if_neg hij, if_neg hi,
          ite_true, Fin.val_zero]
        have hb : i.val + 1 ≠ 0 := by omega
        simp only [if_neg hb]
        split_ifs <;> simp [pow_two]
      · simp only [weakPath, normalizedPath, band, if_neg hij, if_neg hi, if_neg hj]
        split_ifs <;> simp

private theorem weak_power_normalized (n k : ℕ) (epsilon : ℚ) (j : Fin (n + 2)) :
    (weakPath n epsilon ^ k) 0 j =
      (if j = 0 then 1 else epsilon) *
        ((normalizedPath n ^ k) 0 j).eval (epsilon^2) := by
  induction k generalizing j with
  | zero => by_cases hj : (0 : Fin (n + 2)) = j <;> simp [Matrix.one_apply, hj, eq_comm]
  | succ k ih =>
    rw [pow_succ (weakPath n epsilon) k, pow_succ (normalizedPath n) k]
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih]
    have h := scaled_edge n epsilon i j
    calc
      _ = ((normalizedPath n ^ k) 0 i).eval (epsilon^2) *
          ((if i = 0 then 1 else epsilon) * weakPath n epsilon i j) := by ring
      _ = _ := by rw [h]; ring

/-- Rows one through n of the normalized root observation matrix. -/
def observationMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ[X] := fun i j =>
  (normalizedPath n ^ (i.val + 1)) 0 j.castSucc.succ

private theorem observation_diagonal (n : ℕ) (i : Fin n) :
    observationMatrix n i i = C ((1 / 8 : ℚ) ^ i.val) := by
  have h := normalized_power_diagonal n (i.val + 1) (by omega)
  have hi : (⟨i.val + 1, by omega⟩ : Fin (n + 2)) = i.castSucc.succ := Fin.ext rfl
  rw [hi] at h
  simpa [observationMatrix] using h

private theorem observation_unit (n : ℕ) : IsUnit (observationMatrix n) := by
  have ht : (observationMatrix n).IsLowerTriangular := by
    intro i j hij
    exact normalized_power_zero n (i.val + 1) j.castSucc.succ (by simpa using hij)
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_of_isLowerTriangular _ ht]
  apply IsUnit.prod_iff.mpr
  intro i _
  rw [observation_diagonal]
  exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num : (1 / 8 : ℚ) ≠ 0))).map C

/-- Constant triangular pivots solve an arbitrary polynomial compensation demand. -/
def compensators (n : ℕ) (d : Fin n → ℚ[X]) : Fin n → ℚ[X] :=
  (observationMatrix n)⁻¹ *ᵥ d

private theorem compensators_solve (n : ℕ) (d : Fin n → ℚ[X]) :
    observationMatrix n *ᵥ compensators n d = d := by
  rw [compensators, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (observation_unit n)),
    Matrix.one_mulVec]


/-- Every command has exactly its declared serial effect. -/
inductive Command where
  | read | tick | hold | add (input : ℚ)
  deriving DecidableEq

/-- Acknowledgements have no specimen dependent metadata. -/
inductive Reply where
  | scalar (value : ℚ) | ack
  deriving DecidableEq

/-- The actual number of returning matrix updates. -/
def tickCount : List Command → ℕ
  | [] => 0
  | .tick :: w => tickCount w + 1
  | _ :: w => tickCount w

/-- The bound root unit vector. -/
def rootVector (n : ℕ) : Fin (n + 1) → ℚ := Pi.single 0 1

/-- Native successor on the same matrix and field. -/
def advance {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) : Command → Fin (n + 1) → ℚ
  | .tick => a *ᵥ x
  | .add u => x + u • rootVector n
  | _ => x

/-- A Tick reports the root after its update. -/
def reply {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) : Command → Reply
  | .read => .scalar (x 0)
  | .tick => .scalar ((a *ᵥ x) 0)
  | _ => .ack

/-- Retain every scalar and acknowledgement in order. -/
def run {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) : List Command → List Reply
  | [] => []
  | c :: w => reply a x c :: run a (advance a x c) w

/-- The actual field at the advanced stopping cut. -/
def finalState {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) : List Command → Fin (n + 1) → ℚ
  | [] => x
  | c :: w => finalState a (advance a x c) w

/-- Root observations after hypothetical autonomous ticks. -/
def observe {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) (j : ℕ) : ℚ := (a ^ j *ᵥ x) 0

/-- The single cell reference matrix. -/
def reference : Matrix (Fin 1) (Fin 1) ℚ := fun _ _ => 1 / 2

/-- A command word demand includes all Add inputs at their actual tick ages. -/
def demand (n : ℕ) : List Command → ℕ → ℚ[X]
  | [], _ => 0
  | .add u :: w, j => -C u * returnCorrection n j + demand n w j
  | .tick :: w, j => if j = 0 then 0 else demand n w (j - 1)
  | _ :: w, j => demand n w j

private theorem demand_zero (n : ℕ) (w : List Command) : demand n w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons c w ih => cases c <;> simp [demand, returnCorrection, ih]

private theorem observe_zero {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) : observe a x 0 = x 0 := by simp [observe]

private theorem observe_tick {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) (j : ℕ) : observe a (a *ᵥ x) j = observe a x (j + 1) := by
  simp only [observe, Matrix.mulVec_mulVec, pow_succ]

private theorem observe_add {n : ℕ} (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) (u : ℚ) (j : ℕ) :
    observe a (x + u • rootVector n) j = observe a x j + u * (a^j) 0 0 := by
  simp [observe, Matrix.mulVec_add, Matrix.mulVec_smul, rootVector,
    Matrix.mulVec_single_one]

private theorem weak_moment (n j : ℕ) (epsilon : ℚ) :
    (weakPath n epsilon ^ j) 0 0 = (1 / 2 : ℚ)^j +
      epsilon^2 * (returnCorrection n j).eval (epsilon^2) := by
  rw [weak_power_normalized, normalized_return_difference]
  simp

private theorem compensation_replay (n : ℕ) (epsilon : ℚ) (w : List Command)
    (x : Fin (n + 2) → ℚ) (r : ℚ)
    (hx : ∀ j ≤ tickCount w, observe (weakPath n epsilon) x j =
      r * (1 / 2 : ℚ)^j + epsilon^2 * (demand n w j).eval (epsilon^2)) :
    run (weakPath n epsilon) x w = run reference (fun _ => r) w := by
  induction w generalizing x r with
  | nil => rfl
  | cons c w ih =>
    have hzero : x 0 = r := by
      have h := hx 0 (Nat.zero_le _)
      simpa only [observe_zero, pow_zero, mul_one, demand_zero,
        Polynomial.eval_zero, mul_zero, add_zero] using h
    cases c with
    | read =>
      simp only [run, reply, hzero]
      congr 1
      exact ih x r (by simpa only [tickCount, demand] using hx)
    | hold =>
      simp only [run, reply]
      congr 1
      exact ih x r (by simpa only [tickCount, demand] using hx)
    | add u =>
      simp only [run, reply]
      congr 1
      have href : advance reference (fun _ => r) (.add u) = fun _ => r + u := by
        ext i; fin_cases i; simp [advance, rootVector]
      rw [href]
      apply ih (advance _ x (.add u)) (r + u)
      intro j hj
      rw [advance, observe_add, hx j hj, weak_moment]
      simp only [demand, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_neg, Polynomial.eval_C] at *
      ring
    | tick =>
      have ht : (weakPath n epsilon *ᵥ x) 0 = r * (1 / 2) := by
        have h := hx 1 (by simp [tickCount])
        simpa [observe, demand, demand_zero] using h
      have hroot : (reference *ᵥ (fun _ => r)) 0 = r * (1 / 2) := by
        simp [reference, Matrix.mulVec, dotProduct, mul_comm]
      simp only [run, reply, ht, hroot]
      congr 1
      have href : advance reference (fun _ => r) .tick = fun _ => r * (1 / 2) := by
        ext i; fin_cases i; simp [advance, reference, Matrix.mulVec, dotProduct, mul_comm]
      rw [href]
      apply ih (advance _ x .tick) (r * (1 / 2))
      intro j hj
      rw [advance, observe_tick, hx (j + 1)
        (by simpa only [tickCount] using Nat.add_le_add_right hj 1)]
      simp only [demand, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
        Nat.add_sub_cancel, pow_succ]
      ring

/-- Embed the compensating interior coordinates, with both endpoints zero. -/
def entry (n : ℕ) (epsilon : ℚ) (w : Fin n → ℚ[X]) : Fin (n + 2) → ℚ :=
  Fin.cons 0 (Fin.snoc (fun i => epsilon * (w i).eval (epsilon^2)) 0)

private theorem entry_observation (n : ℕ) (epsilon : ℚ) (d : Fin n → ℚ[X])
    (i : Fin n) :
    observe (weakPath n epsilon) (entry n epsilon (compensators n d)) (i.val + 1) =
      epsilon^2 * (d i).eval (epsilon^2) := by
  have hs := congrFun (compensators_solve n d) i
  have he := congrArg (Polynomial.eval (epsilon^2)) hs
  simp only [Matrix.mulVec, dotProduct, Polynomial.eval_finsetSum, Polynomial.eval_mul] at he
  unfold observe Matrix.mulVec dotProduct entry
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, mul_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last,
    add_zero, zero_add]
  calc
    _ = epsilon^2 * ∑ j : Fin n,
        ((observationMatrix n i j).eval (epsilon^2) *
          (compensators n d j).eval (epsilon^2)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [weak_power_normalized]
      have hj : j.castSucc.succ ≠ (0 : Fin (n + 2)) := by simp
      simp only [if_neg hj, observationMatrix]
      ring
    _ = _ := by rw [he]

/-- Sum of absolute coefficients, a rational bound on the unit interval. -/
def coefficientBound (p : ℚ[X]) : ℚ := ∑ k ∈ p.support, |p.coeff k|

private theorem eval_bound (p : ℚ[X]) (x : ℚ) (hx : |x| ≤ 1) :
    |p.eval x| ≤ coefficientBound p := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hx)

private theorem small_entry (n : ℕ) (w : Fin n → ℚ[X]) (rho : ℚ) (hrho : 0 < rho) :
    ∃ epsilon : ℚ, 0 < epsilon ∧ epsilon ≤ 1 / 8 ∧
      (∑ i, |entry n epsilon w i|) < rho := by
  let bound : ℚ := 1 + ∑ i, coefficientBound (w i)
  have hb : 0 < bound := by
    dsimp [bound, coefficientBound]
    positivity
  let epsilon : ℚ := min (1 / 8) (rho / (2 * bound))
  have he : 0 < epsilon := lt_min (by norm_num) (div_pos hrho (mul_pos (by norm_num) hb))
  have hec : epsilon ≤ 1 / 8 := min_le_left _ _
  have her : epsilon ≤ rho / (2 * bound) := min_le_right _ _
  have hprod : epsilon * bound ≤ rho / 2 := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0:ℚ)<2) hb)).mp her
    linarith
  refine ⟨epsilon, he, hec, ?_⟩
  unfold entry
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [Fin.cons_zero, abs_zero, Fin.cons_succ, Fin.snoc_castSucc,
    Fin.snoc_last, add_zero, zero_add]
  calc
    _ ≤ ∑ i : Fin n, epsilon * coefficientBound (w i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_pos he]
      apply mul_le_mul_of_nonneg_left (eval_bound _ _ ?_) he.le
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith
    _ = epsilon * (bound - 1) := by rw [← Finset.mul_sum]; dsimp [bound]; ring
    _ < epsilon * bound := by nlinarith
    _ ≤ rho / 2 := hprod
    _ < rho := by linarith


/-- Real quadratic form of a rational matrix, without an inferred observation port. -/
def quadratic {m : ℕ} (a : Matrix (Fin m) (Fin m) ℚ) (v : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, v i * (a i j : ℝ) * v j

/-- The fixed spectral enclosure, interpreted on every real vector. -/
def Enclosed {m : ℕ} (a : Matrix (Fin m) (Fin m) ℚ) : Prop :=
  ∀ v : Fin m → ℝ,
    (1 / 4 : ℝ) * (∑ i, (v i)^2) ≤ quadratic a v ∧
    quadratic a v ≤ (3 / 4 : ℝ) * (∑ i, (v i)^2)

/-- Uncapped finite rational positive link Jacobi specimens. -/
structure NativeSource where
  dimension : ℕ
  matrix : Matrix (Fin (dimension + 1)) (Fin (dimension + 1)) ℚ
  symmetric : ∀ i j, matrix i j = matrix j i
  tridiagonal : ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → matrix i j = 0
  linksPositive : ∀ i : Fin dimension, 0 < matrix i.castSucc i.succ
  enclosed : Enclosed matrix

/-- The mathematical native order is positive and has no supplied common cap. -/
def NativeSource.order (s : NativeSource) : ℕ := s.dimension + 1

/-- A closed Euclidean entry ball at a nonnegative rational radius. -/
def InBall {m : ℕ} (rho : ℚ) (z : Fin m → ℚ) : Prop :=
  0 ≤ rho ∧ (∑ i, (z i : ℝ)^2) ≤ (rho : ℝ)^2

private theorem weak_symmetric (n : ℕ) (epsilon : ℚ) (i j : Fin (n + 2)) :
    weakPath n epsilon i j = weakPath n epsilon j i := by
  unfold weakPath band
  by_cases h : i = j
  · subst j; simp
  · have hs : j ≠ i := Ne.symm h
    by_cases hu : i.val + 1 = j.val
    · have hl : j.val + 1 ≠ i.val := by omega
      simp [h, hs, hu, hl]
    · by_cases hl : j.val + 1 = i.val <;> simp [h, hs, hu, hl]

private theorem unique_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Prop) [DecidablePred p]
    (hu : ∀ i j, p i → p j → i = j) (c : ℝ) (hc : 0 ≤ c) :
    (∑ i, if p i then c else 0) ≤ c := by
  by_cases he : ∃ i, p i
  · obtain ⟨i, hi⟩ := he
    rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hji
      have hj : ¬ p j := fun hj => hji (hu j i hj hi)
      simp [hj]
    · simp
  · have hp : ∀ i, ¬ p i := by simpa only [not_exists] using he
    simpa [hp] using hc

set_option backward.isDefEq.respectTransparency false in
private theorem quadratic_row_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : Matrix ι ι ℝ) (ha : ∀ i j, a i j = a j i) (q : ℝ)
    (hq : ∀ i, ∑ j, |a i j| ≤ q) (v : ι → ℝ) :
    |∑ i, ∑ j, v i * a i j * v j| ≤ q * ∑ i, (v i)^2 := by
  have hswap : (∑ i, ∑ j, |a i j| * (v j)^2) =
      ∑ i, ∑ j, |a i j| * (v i)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [ha i j]
  calc
    _ ≤ ∑ i, ∑ j, |v i * a i j * v j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, |a i j| * (((v i)^2 + (v j)^2) / 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hpair : |v i| * |v j| ≤ ((v i)^2 + (v j)^2) / 2 := by
        nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
      have h := mul_le_mul_of_nonneg_left hpair (abs_nonneg (a i j))
      simpa only [abs_mul, mul_comm, mul_left_comm, mul_assoc] using h
    _ = ((∑ i, ∑ j, |a i j| * (v i)^2) +
        (∑ i, ∑ j, |a i j| * (v j)^2)) / 2 := by
      simp only [← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]
    _ = ∑ i, (∑ j, |a i j|) * (v i)^2 := by
      rw [hswap]
      simp_rw [Finset.sum_mul]
      ring
    _ ≤ ∑ i, q * (v i)^2 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hq i) (sq_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

private theorem weak_enclosed (n : ℕ) (epsilon : ℚ) (he : 0 ≤ epsilon)
    (hec : epsilon ≤ 1 / 8) : Enclosed (weakPath n epsilon) := by
  let a : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ := fun i j =>
    if i = j then 0 else (weakPath n epsilon i j : ℝ)
  have hr : (0 : ℝ) ≤ epsilon := by exact_mod_cast he
  have h8 : epsilon * 8 ≤ 1 := by linarith
  have h8r : (epsilon : ℝ) * 8 ≤ 1 := by exact_mod_cast h8
  have hrc : (epsilon : ℝ) ≤ 1 / 8 := by linarith
  have ha : ∀ i j, a i j = a j i := by
    intro i j; dsimp [a]
    by_cases h : i=j
    · subst j; rfl
    · simp [h, Ne.symm h, weak_symmetric n epsilon i j]
  have hedge (i j : Fin (n + 2)) : |a i j| ≤
      (if i.val + 1=j.val then (1 / 8 : ℝ) else 0) +
      (if j.val + 1=i.val then (1 / 8 : ℝ) else 0) := by
    dsimp [a, weakPath, band]
    split_ifs <;> push_cast <;> (try simp only [abs_zero, abs_of_nonneg hr]) <;>
      (try norm_num at *) <;> (try linarith) <;> omega
  have hrow (i : Fin (n + 2)) : ∑ j, |a i j| ≤ (1 / 4 : ℝ) := by
    have hu := unique_sum_bound (fun j : Fin (n + 2) => i.val + 1=j.val)
      (fun j k hj hk => Fin.ext (by omega)) (1 / 8) (by norm_num)
    have hl := unique_sum_bound (fun j : Fin (n + 2) => j.val + 1=i.val)
      (fun j k hj hk => Fin.ext (by omega)) (1 / 8) (by norm_num)
    calc
      _ ≤ ∑ j, ((if i.val + 1=j.val then (1 / 8 : ℝ) else 0) +
          (if j.val + 1=i.val then (1 / 8 : ℝ) else 0)) :=
        Finset.sum_le_sum fun j _ => hedge i j
      _ ≤ 1 / 4 := by rw [Finset.sum_add_distrib]; linarith
  intro v
  have h := quadratic_row_bound a ha (1 / 4) hrow v
  have heq : quadratic (weakPath n epsilon) v =
      (1 / 2 : ℝ) * (∑ i, (v i)^2) + ∑ i, ∑ j, v i * a i j * v j := by
    have hcell (i j : Fin (n + 2)) :
        v i * (weakPath n epsilon i j : ℝ) * v j =
        (if i=j then (1 / 2 : ℝ) * (v i)^2 else 0) + v i * a i j * v j := by
      by_cases hij : i=j
      · subst j; simp [a, weakPath, band]; ring
      · simp [a, hij]
    unfold quadratic
    simp_rw [hcell, Finset.sum_add_distrib]
    simp [← Finset.mul_sum]
  rw [abs_le] at h
  rw [heq]
  constructor <;> linarith

/-- A positive weak link gives an admitted specimen, uniformly in its order. -/
def specimen (n : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hec : epsilon ≤ 1 / 8) : NativeSource where
  dimension := n + 1
  matrix := weakPath n epsilon
  symmetric := weak_symmetric n epsilon
  tridiagonal := by
    intro i j hij
    cases hij with
    | inl h => exact band_far _ _ _ _ _ _ h
    | inr h => rw [weak_symmetric]; exact band_far _ _ _ _ _ _ h
  linksPositive := by
    intro i
    have hne : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
    simp [weakPath, band, hne]
    split_ifs <;> first | exact he | norm_num
  enclosed := weak_enclosed n epsilon he.le hec

private theorem ball_of_l1_lt {m : ℕ} (rho : ℚ) (hrho : 0 < rho)
    (z : Fin m → ℚ) (hz : (∑ i, |z i|) < rho) : InBall rho z := by
  refine ⟨hrho.le, ?_⟩
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin m))) (f := fun i => |z i|)
    (fun _ _ => abs_nonneg _)
  simp only [sq_abs] at hsq
  have hnon : (0 : ℚ) ≤ ∑ i, |z i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h : (∑ i, (z i)^2) ≤ rho^2 := by nlinarith
  exact_mod_cast h


set_option backward.isDefEq.respectTransparency false in
/-- One fixed arbitrarily small signed entry reproduces a complete command word. -/
theorem small_entry_complete_transcript_compensation
    (rho : ℚ) (hrho : 0 < rho) (w : List Command) :
    ∃ (epsilon : ℚ) (s : NativeSource) (z : Fin s.order → ℚ),
      0 < epsilon ∧ epsilon ≤ 1 / 8 ∧
      s.order = tickCount w + 2 ∧ InBall rho z ∧
      (∑ i, |z i|) < rho ∧
      run s.matrix z w = run reference (fun _ => 0) w ∧
      (s.matrix ^ 2) 0 0 = (1 / 2 : ℚ)^2 + epsilon^2 := by
  let n := tickCount w
  let d : Fin n → ℚ[X] := fun i => demand n w (i.val + 1)
  let zpoly := compensators n d
  obtain ⟨epsilon, he, hec, hz⟩ := small_entry n zpoly rho hrho
  let s := specimen n epsilon he hec
  let z := entry n epsilon zpoly
  refine ⟨epsilon, s, z, he, hec, rfl, ball_of_l1_lt rho hrho z hz, hz, ?_, ?_⟩
  · apply compensation_replay n epsilon w z 0
    intro j hj
    simp only [zero_mul, zero_add]
    by_cases h0 : j = 0
    · subst j; simp [observe_zero, z, entry, demand_zero]
    · have hjn : j - 1 < n := by dsimp [n]; omega
      let i : Fin n := ⟨j - 1, hjn⟩
      have hi : i.val + 1 = j := by dsimp [i]; omega
      have h := entry_observation n epsilon d i
      simpa only [z, zpoly, d, hi] using h
  · change (weakPath n epsilon ^ 2) 0 0 = _
    rw [weak_moment]
    simp [returnCorrection, normalizedPath, band]


/-- The one cell reference belongs to the same fixed spectral class. -/
def referenceSource : NativeSource where
  dimension := 0
  matrix := reference
  symmetric := by intros; rfl
  tridiagonal := by intro i j h; fin_cases i; fin_cases j; simp at h
  linksPositive := by intro i; exact Fin.elim0 i
  enclosed := by
    intro v
    simp [quadratic, reference]
    constructor <;> nlinarith [sq_nonneg (v 0)]

/-- Arbitrary local computation, source calls, and successful export. -/
inductive Decision (L E : Type*) where
  | halt (value : E)
  | compute (next : L)
  | call (command : Command) (next : Reply → L)

/-- A controller has no native source argument or hidden source dependent advice. -/
abbrev Controller (L E : Type*) := L → Decision L E

/-- A finite successful actual execution, including all local computations. -/
inductive Successful {L E : Type*} (p : Controller L E) {n : ℕ}
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    L → (Fin (n + 1) → ℚ) → List Command → E → Prop where
  | halt {l x e} (decision : p l = .halt e) : Successful p a l x [] e
  | compute {l l' x w e} (decision : p l = .compute l')
      (rest : Successful p a l' x w e) : Successful p a l x w e
  | call {l x c next w e} (decision : p l = .call c next)
      (rest : Successful p a (next (reply a x c)) (advance a x c) w e) :
      Successful p a l x (c::w) e

private theorem successful_replay {L E : Type*} {p : Controller L E} {n : ℕ}
    {a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ} {l : L} {x : Fin (n + 1) → ℚ}
    {w : List Command} {e : E} (h : Successful p a l x w e) :
    ∀ {m : ℕ} (b : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (y : Fin (m + 1) → ℚ),
      run a x w = run b y w → Successful p b l y w e := by
  induction h with
  | halt hp => intro m b y _; exact .halt hp
  | compute hp h ih => intro m b y he; exact .compute hp (ih b y he)
  | @call l x c next w e hp h ih =>
    intro m b y he
    have heq := List.cons.inj he
    apply Successful.call hp
    rw [← heq.1]
    exact ih b (advance b y c) heq.2

/-- Necessary information in each of the three exact acquisition contracts. -/
inductive AcquisitionTarget (E : Type*) where
  | nativeOrder (decode : E → ℕ)
  | impulseLaw (decode : E → ℕ → ℚ)
  | predictor (decode : E → List Command → List Reply)

/-- A predictor is evaluated at the actual advanced native field. -/
def AcquisitionTarget.Correct {E : Type*} (target : AcquisitionTarget E)
    (s : NativeSource) (x : Fin s.order → ℚ) (e : E) : Prop :=
  match target with
  | .nativeOrder decode => decode e = s.order
  | .impulseLaw decode => ∀ j, decode e j = (s.matrix^j) 0 0
  | .predictor decode => ∀ w, decode e w = run s.matrix x w

/-- Successful finite termination and correctness of every successful export. -/
def AcquiresOnBall {L E : Type*} (rho : ℚ) (p : Controller L E)
    (initial : L) (target : AcquisitionTarget E) : Prop :=
  ∀ (s : NativeSource) (z : Fin s.order → ℚ), InBall rho z →
    (∃ w e, Successful p s.matrix initial z w e) ∧
    ∀ w e, Successful p s.matrix initial z w e →
      target.Correct s (finalState s.matrix z w) e

private theorem two_ticks_agreement {n m : ℕ}
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) (y : Fin (m + 1) → ℚ)
    (h : run a x [.tick, .tick] = run b y [.tick, .tick]) :
    observe a x 2 = observe b y 2 := by
  simp only [run, reply, advance, List.cons.injEq, Reply.scalar.injEq, and_true] at h
  simpa only [observe, pow_two, Matrix.mulVec_mulVec] using h.2

set_option backward.isDefEq.respectTransparency false in
private theorem actual_cut_separation {n m : ℕ}
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ)
    (x : Fin (n + 1) → ℚ) (y : Fin (m + 1) → ℚ)
    (h : (a^2) 0 0 ≠ (b^2) 0 0) :
    ∃ w : List Command, run a x w ≠ run b y w := by
  by_cases hbase : run a x [.tick, .tick] = run b y [.tick, .tick]
  · refine ⟨[.add 1, .tick, .tick], ?_⟩
    intro hplus
    have hplus' : run a (x + 1 • rootVector n) [.tick, .tick] =
        run b (y + 1 • rootVector m) [.tick, .tick] :=
      (List.cons.inj hplus).2
    have hu := two_ticks_agreement a b _ _ hplus'
    have hv := two_ticks_agreement a b x y hbase
    have ha := observe_add a x 1 2
    have hb := observe_add b y 1 2
    have hq := ha.symm.trans (hu.trans hb)
    simp only [one_mul] at hq
    apply h
    linarith only [hq, hv]
  · exact ⟨[.tick, .tick], hbase⟩

private theorem reference_moment_two : (reference^2) 0 0 = (1 / 2 : ℚ)^2 := by
  simp [pow_two, Matrix.mul_apply, reference]

set_option backward.isDefEq.respectTransparency false in
/-- No source blind deterministic controller acquires even the necessary exact data. -/
theorem no_deterministic_exact_acquisition
    (rho : ℚ) (hrho : 0 < rho) (L E : Type*) (p : Controller L E)
    (initial : L) (target : AcquisitionTarget E) :
    ¬ (∀ (s : NativeSource) (z : Fin s.order → ℚ),
      (0 ≤ rho ∧ (∑ i, (z i : ℝ) ^ 2) ≤ (rho : ℝ) ^ 2) →
      (∃ w e, Successful p s.matrix initial z w e) ∧
      ∀ w e, Successful p s.matrix initial z w e →
        target.Correct s (finalState s.matrix z w) e) := by
  change ¬ AcquiresOnBall rho p initial target
  intro hall
  have hball : InBall rho (fun _ : Fin referenceSource.order => (0 : ℚ)) := by
    simp [InBall, hrho.le]
  obtain ⟨⟨w, e, hrun⟩, hcorrect⟩ := hall referenceSource (fun _ => 0) hball
  obtain ⟨epsilon, s, z, he, _, horder, hball', _, htrace, hmoment⟩ :=
    small_entry_complete_transcript_compensation rho hrho w
  have hreplay : Successful p s.matrix initial z w e :=
    successful_replay hrun s.matrix z htrace.symm
  have hc0 := hcorrect w e hrun
  have hc1 := (hall s z hball').2 w e hreplay
  have hmne : (referenceSource.matrix^2) 0 0 ≠ (s.matrix^2) 0 0 := by
    change (reference^2) 0 0 ≠ _
    rw [reference_moment_two, hmoment]
    nlinarith [sq_pos_of_pos he]
  cases target with
  | nativeOrder decode =>
    change decode e = 1 at hc0
    change decode e = s.order at hc1
    omega
  | impulseLaw decode =>
    exact hmne ((hc0 2).symm.trans (hc1 2))
  | predictor decode =>
    obtain ⟨future, hfuture⟩ := actual_cut_separation referenceSource.matrix s.matrix
      (finalState referenceSource.matrix (fun _ => 0) w) (finalState s.matrix z w) hmne
    exact hfuture ((hc0 future).symm.trans (hc1 future))

/-- A fair bit controller can request a bit independently of source commands. -/
inductive BitDecision (L E : Type*) where
  | halt (value : E)
  | compute (next : L)
  | call (command : Command) (next : Reply → L)
  | bit (next : Bool → L)

/-- The only random resource is the next independent bit of the tape. -/
abbrev BitController (L E : Type*) := L → BitDecision L E

/-- Successful executions consume exactly a finite bit prefix and command word. -/
inductive BitSuccessful {L E : Type*} (p : BitController L E) {n : ℕ}
    (a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    L → (Fin (n + 1) → ℚ) → List Bool → List Command → E → Prop where
  | halt {l x e} (decision : p l = .halt e) : BitSuccessful p a l x [] [] e
  | compute {l l' x bits w e} (decision : p l = .compute l')
      (rest : BitSuccessful p a l' x bits w e) : BitSuccessful p a l x bits w e
  | call {l x c next bits w e} (decision : p l = .call c next)
      (rest : BitSuccessful p a (next (reply a x c)) (advance a x c) bits w e) :
      BitSuccessful p a l x bits (c :: w) e
  | bit {l x next b bits w e} (decision : p l = .bit next)
      (rest : BitSuccessful p a (next b) x bits w e) :
      BitSuccessful p a l x (b :: bits) w e

private theorem bit_successful_replay {L E : Type*} {p : BitController L E} {n : ℕ}
    {a : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ} {l : L} {x : Fin (n + 1) → ℚ}
    {bits : List Bool} {w : List Command} {e : E} (h : BitSuccessful p a l x bits w e) :
    ∀ {m : ℕ} (b : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) (y : Fin (m + 1) → ℚ),
      run a x w = run b y w → BitSuccessful p b l y bits w e := by
  induction h with
  | halt hp => intro m b y _; exact .halt hp
  | compute hp h ih => intro m b y he; exact .compute hp (ih b y he)
  | @call l x c next bits w e hp h ih =>
    intro m b y he
    have heq := List.cons.inj he
    apply BitSuccessful.call hp
    rw [← heq.1]
    exact ih b (advance b y c) heq.2
  | bit hp h ih => intro m b y he; exact .bit hp (ih b y he)

/-- The cylinder pins exactly the used prefix, including the empty prefix. -/
def prefixCylinder (bits : List Bool) : Set (ℕ → Bool) :=
  D5.S0.Naming.GreenClassMeasure.greenClass (Finset.range bits.length)
    (fun i => bits[i]?.getD false)

/-- Independent fair bits on an infinite tape, with the ordinary product measure. -/
def fairMeasure : MeasureTheory.Measure (ℕ → Bool) :=
  D5.S0.Naming.GreenClassMeasure.stringMeasure Bool

/-- The event of a successful finite execution on a fixed source and entry. -/
def finiteSuccess {L E : Type*} (p : BitController L E) (initial : L)
    (s : NativeSource) (z : Fin s.order → ℚ) : Set (ℕ → Bool) :=
  {tape | ∃ bits w e, tape ∈ prefixCylinder bits ∧
    BitSuccessful p s.matrix initial z bits w e}

/-- Error is an incorrect successful export at its actual stopping field. -/
def errorEvent {L E : Type*} (p : BitController L E) (initial : L)
    (target : AcquisitionTarget E) (s : NativeSource) (z : Fin s.order → ℚ) :
    Set (ℕ → Bool) :=
  {tape | ∃ bits w e, tape ∈ prefixCylinder bits ∧
    BitSuccessful p s.matrix initial z bits w e ∧
    ¬ target.Correct s (finalState s.matrix z w) e}

/-- Almost sure finite success and zero probability of incorrect success, for every fixed source. -/
def FairAcquiresOnBall {L E : Type*} (rho : ℚ) (p : BitController L E)
    (initial : L) (target : AcquisitionTarget E) : Prop :=
  ∀ (s : NativeSource) (z : Fin s.order → ℚ), InBall rho z →
    fairMeasure (finiteSuccess p initial s z)ᶜ = 0 ∧
    fairMeasure (errorEvent p initial target s z) = 0

private theorem fair_export_correct {L E : Type*} (p : BitController L E)
    (initial : L) (target : AcquisitionTarget E) (s : NativeSource)
    (z : Fin s.order → ℚ) (hzero : fairMeasure (errorEvent p initial target s z) = 0)
    (bits : List Bool) (w : List Command) (e : E)
    (hrun : BitSuccessful p s.matrix initial z bits w e) :
    target.Correct s (finalState s.matrix z w) e := by
  by_contra hbad
  have hsub : prefixCylinder bits ⊆ errorEvent p initial target s z := by
    intro tape ht
    exact ⟨bits, w, e, ht, hrun, hbad⟩
  have hpos : 0 < fairMeasure (prefixCylinder bits) :=
    D5.S0.Naming.GreenClassMeasure.greenClass_measure_pos _ _
  exact (ne_of_gt hpos) (le_antisymm ((MeasureTheory.measure_mono hsub).trans hzero.le)
    bot_le)

set_option backward.isDefEq.respectTransparency false in
/-- No zero error fair bit controller has almost sure successful finite exact acquisition. -/
theorem no_fair_zero_error_exact_acquisition
    (rho : ℚ) (hrho : 0 < rho) (L E : Type*) (p : BitController L E)
    (initial : L) (target : AcquisitionTarget E) :
    ¬ (∀ (s : NativeSource) (z : Fin s.order → ℚ),
      (0 ≤ rho ∧ (∑ i, (z i : ℝ) ^ 2) ≤ (rho : ℝ) ^ 2) →
      fairMeasure (finiteSuccess p initial s z)ᶜ = 0 ∧
      fairMeasure (errorEvent p initial target s z) = 0) := by
  change ¬ FairAcquiresOnBall rho p initial target
  intro hall
  have hball : InBall rho (fun _ : Fin referenceSource.order => (0 : ℚ)) := by
    simp [InBall, hrho.le]
  obtain ⟨hfinite, hzero⟩ := hall referenceSource (fun _ => 0) hball
  have hnonempty : (finiteSuccess p initial referenceSource (fun _ => 0)).Nonempty := by
    by_contra h
    have hempty : finiteSuccess p initial referenceSource (fun _ => 0) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp h
    have huniv : fairMeasure Set.univ = 1 := by
      unfold fairMeasure D5.S0.Naming.GreenClassMeasure.stringMeasure
      exact MeasureTheory.measure_univ
    simpa [hempty, huniv] using hfinite
  obtain ⟨tape, bits, w, e, htape, hrun⟩ := hnonempty
  have hc0 := fair_export_correct p initial target referenceSource (fun _ => 0)
    hzero bits w e hrun
  obtain ⟨epsilon, s, z, he, _, horder, hball', _, htrace, hmoment⟩ :=
    small_entry_complete_transcript_compensation rho hrho w
  have hreplay : BitSuccessful p s.matrix initial z bits w e :=
    bit_successful_replay hrun s.matrix z htrace.symm
  have hc1 := fair_export_correct p initial target s z (hall s z hball').2
    bits w e hreplay
  have hmne : (referenceSource.matrix ^ 2) 0 0 ≠ (s.matrix ^ 2) 0 0 := by
    change (reference ^ 2) 0 0 ≠ _
    rw [reference_moment_two, hmoment]
    nlinarith [sq_pos_of_pos he]
  cases target with
  | nativeOrder decode =>
    change decode e = 1 at hc0
    change decode e = s.order at hc1
    omega
  | impulseLaw decode => exact hmne ((hc0 2).symm.trans (hc1 2))
  | predictor decode =>
    obtain ⟨future, hfuture⟩ := actual_cut_separation referenceSource.matrix s.matrix
      (finalState referenceSource.matrix (fun _ => 0) w) (finalState s.matrix z w) hmne
    exact hfuture ((hc0 future).symm.trans (hc1 future))

#print axioms small_entry_complete_transcript_compensation
#print axioms no_deterministic_exact_acquisition
#print axioms no_fair_zero_error_exact_acquisition

end D5.S3.Observer.Linear.SmallSignedEntryTranscriptCompensation
