/- GID: D5/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Pressure/MarkovAdditivePaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite Markov path sums and corrected additive martingale moments. -/
import D5.S3.Combinatorics.Graph.Pressure.MarkovAdditiveCurvature
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! # Finite transition paths and corrected additive moments -/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators Matrix
open Matrix
namespace D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]

/-- `n` future states, following the separately supplied initial state. -/
def pathWeight (P : Matrix V V ℝ) : (n : ℕ) → V → (Fin n → V) → ℝ
  | 0, _, _ => 1
  | n+1, i, w => P i (w 0) * pathWeight P n (w 0) (Fin.tail w)

def pathExpectation (P : Matrix V V ℝ) (n : ℕ) (i : V) (f : (Fin n → V) → ℝ) : ℝ :=
  ∑ w, pathWeight P n i w * f w

private theorem pathExpectation_succ (P : Matrix V V ℝ) (n : ℕ) (i : V)
    (f : (Fin (n+1) → V) → ℝ) :
    pathExpectation P (n+1) i f =
      ∑ j, P i j * pathExpectation P n j (fun w => f (Fin.cons j w)) := by
  unfold pathExpectation
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => V))]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp [pathWeight, Fin.consEquiv, Finset.mul_sum, mul_assoc]

private theorem pathExpectation_zero (P : Matrix V V ℝ) (i : V)
    (f : (Fin 0 → V) → ℝ) : pathExpectation P 0 i f = f Fin.elim0 := by
  simpa only [pathExpectation, pathWeight, one_mul, Fintype.sum_unique] using
    congrArg f (Subsingleton.elim (default : Fin 0 → V) Fin.elim0)

private theorem pathExpectation_const (P : Matrix V V ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ V) (n : ℕ) (i : V) (c : ℝ) :
    pathExpectation P n i (fun _ => c) = c := by
  induction n generalizing i with
  | zero => simp [pathExpectation_zero]
  | succ n ih =>
    rw [pathExpectation_succ]
    simp_rw [ih]
    rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP, one_mul]

private theorem pathExpectation_add (P : Matrix V V ℝ) (n : ℕ) (i : V)
    (f k : (Fin n → V) → ℝ) :
    pathExpectation P n i (fun w => f w + k w) =
      pathExpectation P n i f + pathExpectation P n i k := by
  simp [pathExpectation, mul_add, Finset.sum_add_distrib]

private theorem pathExpectation_scale (P : Matrix V V ℝ) (n : ℕ) (i : V)
    (c : ℝ) (f : (Fin n → V) → ℝ) :
    pathExpectation P n i (fun w => c * f w) = c * pathExpectation P n i f := by
  simp [pathExpectation, Finset.mul_sum, mul_left_comm, mul_assoc]

/-- Sum of `n` transition rewards, not the sum of `n+1` state rewards. -/
def additiveSum (g : V → V → ℝ) : (n : ℕ) → V → (Fin n → V) → ℝ
  | 0, _, _ => 0
  | n+1, i, w => g i (w 0) + additiveSum g n (w 0) (Fin.tail w)

def endpoint : (n : ℕ) → V → (Fin n → V) → V
  | 0, i, _ => i
  | n+1, _, w => endpoint n (w 0) (Fin.tail w)

private theorem terminal_expectation (P : Matrix V V ℝ)
    (n : ℕ) (i : V) (f : V → ℝ) :
    pathExpectation P n i (fun w => f (endpoint n i w)) = (P^n *ᵥ f) i := by
  induction n generalizing i with
  | zero => simp [endpoint, pathExpectation_zero]
  | succ n ih =>
    rw [pathExpectation_succ, pow_succ', ← Matrix.mulVec_mulVec]
    change (∑ j, P i j * pathExpectation P n j (fun w => f (endpoint n j w))) = _
    simp_rw [ih]
    rfl

theorem pathWeight_nonneg (P : Matrix V V ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ V) (n : ℕ) (i : V) (w : Fin n → V) :
    0 ≤ pathWeight P n i w := by
  induction n generalizing i with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hP.1 _ _) (ih _ _)

private theorem pathWeight_hasDerivAt (P : Matrix V V ℝ) (K : ℝ → Matrix V V ℝ)
    (a : V → V → ℝ) (hK : K 0 = P)
    (hd : ∀ i j, HasDerivAt (fun t => K t i j) (P i j * a i j) 0)
    (n : ℕ) (i : V) (w : Fin n → V) :
    HasDerivAt (fun t => pathWeight (K t) n i w)
      (pathWeight P n i w * additiveSum a n i w) 0 := by
  induction n generalizing i with
  | zero => simpa [pathWeight, additiveSum] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | succ n ih =>
    have hh := (hd i (w 0)).mul (ih (w 0) (Fin.tail w))
    convert hh using 1
    · rfl
    · simp [hK, pathWeight, additiveSum]; ring

namespace Stationary
variable {P : Matrix V V ℝ} (π : Stationary P)

def stationaryExpectation (n : ℕ) (f : V → (Fin n → V) → ℝ) : ℝ :=
  ∑ i, π.prob i * pathExpectation P n i (f i)

/-- The actual probability mass on an initial state and `n` successive states. -/
def pathPMF (hP : P ∈ Matrix.rowStochastic ℝ V) (n : ℕ) : PMF (V × (Fin n → V)) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (π.prob x.1 * pathWeight P n x.1 x.2)) (by
    rw [← ENNReal.ofReal_one]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      have hn (i : V) : ∑ w, pathWeight P n i w = 1 := by
        simpa [pathExpectation] using pathExpectation_const P hP n i 1
      simp_rw [hn, mul_one]
      exact π.total
    · intro x _
      exact mul_nonneg (π.positive x.1).le (pathWeight_nonneg P hP n x.1 x.2))

/-- A parameter-dependent transition kernel with a parameter-independent initial row `π`. -/
def initialPathPMF (K : Matrix V V ℝ) (hK : K ∈ Matrix.rowStochastic ℝ V) (n : ℕ) :
    PMF (V × (Fin n → V)) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (π.prob x.1 * pathWeight K n x.1 x.2)) (by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sum_of_nonneg]
    · congr 1
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      have hn (i : V) : ∑ w, pathWeight K n i w = 1 := by
        simpa [pathExpectation] using pathExpectation_const K hK n i 1
      simp_rw [hn, mul_one]
      exact π.total
    · intro x _
      exact mul_nonneg (π.positive x.1).le (pathWeight_nonneg K hK n x.1 x.2))

private theorem centered_additive_mean
    (hP : P ∈ Matrix.rowStochastic ℝ V) (a : V → V → ℝ)
    (ha : ∀ i, ∑ j, P i j * a i j = 0) (n : ℕ) (i : V) :
    pathExpectation P n i (additiveSum a n i) = 0 := by
  induction n generalizing i with
  | zero => simp [additiveSum, pathExpectation_const P hP]
  | succ n ih =>
    rw [pathExpectation_succ]
    change (∑ j, P i j * pathExpectation P n j
      (fun w => a i j + additiveSum a n j w)) = 0
    simp_rw [pathExpectation_add, pathExpectation_const P hP, ih, add_zero]
    exact ha i

private theorem centered_additive_second_step
    (hP : P ∈ Matrix.rowStochastic ℝ V) (a : V → V → ℝ)
    (ha : ∀ i, ∑ j, P i j * a i j = 0) (n : ℕ) (i : V) :
    pathExpectation P (n+1) i (fun w => additiveSum a (n+1) i w ^ 2) =
      ∑ j, P i j * (a i j ^ 2 +
        pathExpectation P n j (fun w => additiveSum a n j w ^ 2)) := by
  rw [pathExpectation_succ]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he : (fun w => additiveSum a (n+1) i (Fin.cons j w)^2) =
      (fun w => a i j ^ 2 + 2 * a i j * additiveSum a n j w + additiveSum a n j w ^ 2) := by
    ext w; simp [additiveSum]; ring
  rw [he]
  simp_rw [pathExpectation_add, pathExpectation_const P hP, pathExpectation_scale,
    centered_additive_mean hP a ha, mul_zero, add_zero]

include π in
theorem centered_additive_second_moment
    (hP : P ∈ Matrix.rowStochastic ℝ V) (a : V → V → ℝ)
    (ha : ∀ i, ∑ j, P i j * a i j = 0) (n : ℕ) :
    π.stationaryExpectation n (fun i w => additiveSum a n i w ^ 2) =
      (n : ℝ) * ∑ i, ∑ j, π.prob i * P i j * a i j ^ 2 := by
  induction n with
  | zero => simp [stationaryExpectation, additiveSum, pathExpectation_const P hP]
  | succ n ih =>
    change (∑ i, π.prob i * pathExpectation P (n+1) i
      (fun w => additiveSum a (n+1) i w ^ 2)) = _
    conv_lhs => simp only [centered_additive_second_step hP a ha,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib, ← mul_assoc]
    have hs (f : V → ℝ) :
        (∑ i, ∑ j, π.prob i * P i j * f j) = ∑ j, π.prob j * f j := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      have hj := congrFun π.invariant j
      change (∑ i, π.prob i * P i j) = π.prob j at hj
      rw [hj]
    rw [hs]
    change _ + π.stationaryExpectation n (fun i w => additiveSum a n i w ^ 2) = _
    rw [ih, Nat.cast_add, Nat.cast_one]
    ring

/-- The corrected increment's exact finite-length square moment, under the stationary law. -/
theorem corrected_second_moment (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) :
    π.stationaryExpectation n
      (fun i w => additiveSum (π.score hP hI g) n i w ^ 2) =
      (n : ℝ) * π.varianceRate hP hI g :=
  π.centered_additive_second_moment hP (π.score hP hI g) (π.score_centered hP hI g) n

private theorem terminal_mixed_step (a : V → V → ℝ) (f : V → ℝ) (n : ℕ) :
    π.stationaryExpectation (n+1)
      (fun i w => additiveSum a (n+1) i w * f (endpoint (n+1) i w)) =
      π.edgeAverage (fun i j => a i j * (P^n *ᵥ f) j) +
        π.stationaryExpectation n (fun i w => additiveSum a n i w * f (endpoint n i w)) := by
  unfold stationaryExpectation
  simp_rw [pathExpectation_succ]
  change (∑ i, π.prob i * ∑ j, P i j * pathExpectation P n j
    (fun w => (a i j + additiveSum a n j w) * f (endpoint n j w))) = _
  simp only [add_mul, pathExpectation_add, pathExpectation_scale, terminal_expectation,
    mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · change (∑ i, ∑ j, π.prob i * (P i j * (a i j * (P^n *ᵥ f) j))) = _
    simp [edgeAverage, mul_assoc]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [← mul_assoc, ← Finset.sum_mul]
    have hj := congrFun π.invariant j
    change (∑ i, π.prob i * P i j) = π.prob j at hj
    rw [hj]

/-- Exact second-Poisson cancellation. No infinite covariance series is involved. -/
theorem second_poisson_endpoint_covariance
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    π.stationaryExpectation n (fun i w => additiveSum (π.score hP hI g) n i w *
      π.corrector hP hI g (endpoint n i w)) =
      π.edgeAverage (fun i j => π.score hP hI g i j *
        (π.secondCorrector hP hI g j - (P^n *ᵥ π.secondCorrector hP hI g) j)) := by
  let a := π.score hP hI g
  let h := π.corrector hP hI g
  let u := π.secondCorrector hP hI g
  have hpu : u - P *ᵥ u = h := (π.secondCorrector_spec hP hI g).1
  induction n with
  | zero => simp [stationaryExpectation, additiveSum, pathExpectation_const P hP, edgeAverage]
  | succ n ih =>
    rw [π.terminal_mixed_step, ih, ← map_add]
    apply congrArg π.edgeAverage
    ext i j
    have hp : P^n *ᵥ h = P^n *ᵥ u - P^(n+1) *ᵥ u := by
      rw [← hpu, Matrix.mulVec_sub, pow_succ, Matrix.mulVec_mulVec]
    change a i j * (P^n *ᵥ h) j + a i j * (u j - (P^n *ᵥ u) j) =
      a i j * (u j - (P^(n+1) *ᵥ u) j)
    rw [hp]
    simp only [Pi.sub_apply]
    ring

/-- The original reward and its martingale correction differ by exactly two endpoints. -/
theorem additive_decomposition (hP : P ∈ Matrix.rowStochastic ℝ V)
    (hI : P.IsIrreducible) (g : V → V → ℝ) (n : ℕ) (i : V) (w : Fin n → V) :
    additiveSum g n i w - (n : ℝ) * π.meanReward g =
      additiveSum (π.score hP hI g) n i w + π.corrector hP hI g i -
        π.corrector hP hI g (endpoint n i w) := by
  induction n generalizing i with
  | zero => simp [additiveSum, endpoint]
  | succ n ih =>
    simp only [additiveSum, endpoint, score, Nat.cast_add, Nat.cast_one]
    have hh := ih (w 0) (Fin.tail w)
    linarith

/-- The full finite-path score of the constructed Doob family, with initial `π` fixed. -/
theorem doob_path_score (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) (i : V) (w : Fin n → V)
    (hw : 0 < π.prob i * pathWeight P n i w) :
    HasDerivAt (fun t => Real.log (π.prob i * pathWeight (π.doob hP hI g t) n i w))
      (additiveSum (π.score hP hI g) n i w) 0 := by
  have hd := (pathWeight_hasDerivAt P (π.doob hP hI g) (π.score hP hI g)
    (π.doob_base hP hI g) (π.doob_hasDerivAt hP hI g) n i w).const_mul (π.prob i)
  have hl := hd.log (by simpa [π.doob_base hP hI g] using hw.ne')
  have hm : π.doob hP hI g 0 = P := π.doob_base hP hI g
  rw [hm] at hl
  have he : π.prob i * (pathWeight P n i w * additiveSum (π.score hP hI g) n i w) /
      (π.prob i * pathWeight P n i w) = additiveSum (π.score hP hI g) n i w := by
    rw [← mul_assoc, mul_div_cancel_left₀ _ hw.ne']
  rw [he] at hl
  exact hl

/-- Classical Fisher information of complete finite paths in the actual Doob family. -/
def pathFisher (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) : ℝ :=
  ∑ x : V × (Fin n → V), (π.pathPMF hP n x).toReal *
    (deriv (fun t => Real.log (π.prob x.1 * pathWeight (π.doob hP hI g t) n x.1 x.2)) 0)^2

theorem pathFisher_eq (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    π.pathFisher hP hI g n = (n : ℝ) * π.varianceRate hP hI g := by
  rw [← π.corrected_second_moment hP hI g n]
  unfold pathFisher stationaryExpectation pathExpectation
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hn : 0 ≤ π.prob i * pathWeight P n i w :=
    mul_nonneg (π.positive i).le (pathWeight_nonneg P hP n i w)
  change (ENNReal.ofReal (π.prob i * pathWeight P n i w)).toReal * _ = _
  rw [ENNReal.toReal_ofReal hn]
  by_cases hw : 0 < π.prob i * pathWeight P n i w
  · rw [(π.doob_path_score hP hI g n i w hw).deriv]
    ring
  · have hz : π.prob i * pathWeight P n i w = 0 := le_antisymm (le_of_not_gt hw) hn
    rw [hz, zero_mul, ← mul_assoc, hz, zero_mul]


/-- Maximum minus minimum on the actual finite state space. -/
def oscillation (f : V → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f +
    Finset.univ.sup' Finset.univ_nonempty (fun i => -f i)

private theorem oscillation_nonneg (f : V → ℝ) : 0 ≤ oscillation f := by
  let i : V := Classical.arbitrary V
  have h₁ := Finset.le_sup' (f := f) (Finset.mem_univ i)
  have h₂ := Finset.le_sup' (f := fun j => -f j) (Finset.mem_univ i)
  unfold oscillation
  linarith

private theorem abs_sub_le_oscillation (f : V → ℝ) (i j : V) :
    |f i - f j| ≤ oscillation f := by
  have hi := Finset.le_sup' (f := f) (Finset.mem_univ i)
  have hj := Finset.le_sup' (f := f) (Finset.mem_univ j)
  have hni := Finset.le_sup' (f := fun k => -f k) (Finset.mem_univ i)
  have hnj := Finset.le_sup' (f := fun k => -f k) (Finset.mem_univ j)
  rw [abs_le]
  unfold oscillation
  constructor <;> linarith

private theorem abs_sub_power_le_oscillation
    (hP : P ∈ Matrix.rowStochastic ℝ V) (f : V → ℝ) (n : ℕ) (i : V) :
    |f i - (P^n *ᵥ f) i| ≤ oscillation f := by
  have hn : P^n ∈ Matrix.rowStochastic ℝ V := pow_mem hP n
  have he : f i - (P^n *ᵥ f) i = ∑ j, (P^n) i j * (f i - f j) := by
    simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hn]
  rw [he]
  calc
    |∑ j, (P^n) i j * (f i - f j)| ≤ ∑ j, |(P^n) i j * (f i - f j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (P^n) i j * oscillation f := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hn.1 i j)]
      exact mul_le_mul_of_nonneg_left (abs_sub_le_oscillation f i j) (hn.1 i j)
    _ = oscillation f := by
      rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hn, one_mul]

private theorem edge_abs_score_bound
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    π.edgeAverage (fun i j => |π.score hP hI g i j|) ≤
      Real.sqrt (π.varianceRate hP hI g) := by
  let w : V × V → ℝ := fun x => π.prob x.1 * P x.1 x.2
  let a : V × V → ℝ := fun x => π.score hP hI g x.1 x.2
  have hw (x : V × V) : 0 ≤ w x := mul_nonneg (π.positive x.1).le (hP.1 _ _)
  have hs : ∑ x, w x = 1 := by
    simp [w, Fintype.sum_prod_type, ← Finset.mul_sum,
      Matrix.sum_row_of_mem_rowStochastic hP, π.total]
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun x => w x * |a x|) (f := w) (g := fun x => w x * a x ^ 2)
    (fun x _ => hw x) (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    (fun x _ => by rw [mul_pow, sq_abs]; nlinarith)
  rw [hs, one_mul] at hc
  have hh := Real.le_sqrt_of_sq_le hc
  simpa [edgeAverage, varianceRate, w, a, Fintype.sum_prod_type] using hh

/-- The second Poisson solution yields a uniform endpoint covariance bound, even periodically. -/
theorem second_poisson_covariance_bound
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    |π.stationaryExpectation n (fun i w => additiveSum (π.score hP hI g) n i w *
      π.corrector hP hI g (endpoint n i w))| ≤
      oscillation (π.secondCorrector hP hI g) * Real.sqrt (π.varianceRate hP hI g) := by
  rw [π.second_poisson_endpoint_covariance hP hI g]
  let U := oscillation (π.secondCorrector hP hI g)
  calc
    |π.edgeAverage (fun i j => π.score hP hI g i j *
      (π.secondCorrector hP hI g j - (P^n *ᵥ π.secondCorrector hP hI g) j))| ≤
      π.edgeAverage (fun i j => |π.score hP hI g i j| * U) := by
        unfold edgeAverage
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (mul_nonneg (π.positive i).le (hP.1 i j)), abs_mul]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (abs_sub_power_le_oscillation hP _ n j) (abs_nonneg _))
          (mul_nonneg (π.positive i).le (hP.1 i j))
    _ = U * π.edgeAverage (fun i j => |π.score hP hI g i j|) := by
      simp [edgeAverage, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ U * Real.sqrt (π.varianceRate hP hI g) :=
      mul_le_mul_of_nonneg_left (π.edge_abs_score_bound hP hI g)
        (oscillation_nonneg _)

private theorem terminal_stationary (n : ℕ) (f : V → ℝ) :
    π.stationaryExpectation n (fun i w => f (endpoint n i w)) = π.prob ⬝ᵥ f := by
  have hinv : π.prob ᵥ* P^n = π.prob := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, π.invariant]
  simp only [stationaryExpectation, terminal_expectation]
  change π.prob ⬝ᵥ (P^n *ᵥ f) = _
  rw [Matrix.dotProduct_mulVec, hinv]

private def expectationLinear (n : ℕ) : (V → (Fin n → V) → ℝ) →ₗ[ℝ] ℝ where
  toFun := π.stationaryExpectation n
  map_add' f k := by simp [stationaryExpectation, pathExpectation, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [stationaryExpectation, pathExpectation, smul_eq_mul,
    Finset.mul_sum, mul_left_comm, mul_assoc]

private theorem expectation_const (hP : P ∈ Matrix.rowStochastic ℝ V) (n : ℕ) (c : ℝ) :
    π.stationaryExpectation n (fun _ _ => c) = c := by
  simp [stationaryExpectation, pathExpectation_const P hP, ← Finset.sum_mul, π.total]

private theorem stationary_centered_mean
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    π.stationaryExpectation n (fun i w => additiveSum g n i w - (n : ℝ) * π.meanReward g) = 0 := by
  simp_rw [π.additive_decomposition hP hI g]
  change π.expectationLinear n ((fun i w => additiveSum (π.score hP hI g) n i w) +
    (fun i _ => π.corrector hP hI g i) - (fun i w => π.corrector hP hI g (endpoint n i w))) = 0
  rw [map_sub, map_add]
  have hm : π.expectationLinear n (fun i w => additiveSum (π.score hP hI g) n i w) = 0 := by
    simp [expectationLinear, stationaryExpectation,
      centered_additive_mean hP _ (π.score_centered hP hI g)]
  rw [hm, zero_add]
  change (∑ i, π.prob i * pathExpectation P n i (fun _ => π.corrector hP hI g i)) -
    π.stationaryExpectation n (fun i w => π.corrector hP hI g (endpoint n i w)) = 0
  simp_rw [pathExpectation_const P hP]
  rw [π.terminal_stationary]
  exact sub_self _

/-- Actual variance under the finite stationary path law. -/
def pathVariance (g : V → V → ℝ) (n : ℕ) : ℝ :=
  π.stationaryExpectation n (fun i w =>
    (additiveSum g n i w - π.stationaryExpectation n (additiveSum g n))^2)

private theorem stationary_additive_mean
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    π.stationaryExpectation n (additiveSum g n) = (n : ℝ) * π.meanReward g := by
  have hh := π.stationary_centered_mean hP hI g n
  change π.expectationLinear n ((fun i w => additiveSum g n i w) -
    (fun _ _ => (n : ℝ) * π.meanReward g)) = 0 at hh
  rw [map_sub] at hh
  change π.stationaryExpectation n (additiveSum g n) -
    π.stationaryExpectation n (fun _ _ => (n : ℝ) * π.meanReward g) = 0 at hh
  rw [π.expectation_const hP] at hh
  exact sub_eq_zero.mp hh

private theorem variance_endpoint_identity
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    π.pathVariance g n - (n : ℝ) * π.varianceRate hP hI g =
      π.stationaryExpectation n (fun i w =>
        (π.corrector hP hI g i - π.corrector hP hI g (endpoint n i w))^2) -
      2 * π.stationaryExpectation n (fun i w => additiveSum (π.score hP hI g) n i w *
        π.corrector hP hI g (endpoint n i w)) := by
  let h := π.corrector hP hI g
  let M := fun i w => additiveSum (π.score hP hI g) n i w
  have hi : π.stationaryExpectation n (fun i w => M i w * h i) = 0 := by
    unfold stationaryExpectation
    simp_rw [mul_comm (M _ _) (h _), pathExpectation_scale]
    simp [M, centered_additive_mean hP _ (π.score_centered hP hI g)]
  unfold pathVariance
  rw [π.stationary_additive_mean hP hI g n]
  simp_rw [π.additive_decomposition hP hI g]
  have he : (fun i w => (M i w + h i - h (endpoint n i w))^2) =
      (fun i w => M i w ^ 2) + (fun i w => (h i - h (endpoint n i w))^2) +
      (2 : ℝ) • (fun i w => M i w * h i) -
      (2 : ℝ) • (fun i w => M i w * h (endpoint n i w)) := by
    ext i w; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  change π.expectationLinear n (fun i w => (M i w + h i - h (endpoint n i w))^2) - _ = _
  rw [he, map_sub, map_add, map_add, map_smul, map_smul]
  change π.stationaryExpectation n (fun i w => M i w ^ 2) + _ +
    2 * π.stationaryExpectation n (fun i w => M i w * h i) - _ - _ = _
  rw [hi, show π.stationaryExpectation n (fun i w => M i w ^ 2) =
    (n : ℝ) * π.varianceRate hP hI g from π.corrected_second_moment hP hI g n]
  dsimp [expectationLinear, h, M]
  ring

private theorem endpoint_square_bound
    (hP : P ∈ Matrix.rowStochastic ℝ V) (f : V → ℝ) (n : ℕ) :
    0 ≤ π.stationaryExpectation n (fun i w => (f i - f (endpoint n i w))^2) ∧
    π.stationaryExpectation n (fun i w => (f i - f (endpoint n i w))^2) ≤ oscillation f ^ 2 := by
  have hn (i : V) (w : Fin n → V) : 0 ≤ π.prob i * pathWeight P n i w :=
    mul_nonneg (π.positive i).le (pathWeight_nonneg P hP n i w)
  constructor
  · apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (π.positive i).le
    exact Finset.sum_nonneg fun w _ => mul_nonneg (pathWeight_nonneg P hP n i w) (sq_nonneg _)
  · rw [← π.expectation_const hP n (oscillation f ^ 2)]
    unfold stationaryExpectation pathExpectation
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (π.positive i).le
    apply Finset.sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_left _ (pathWeight_nonneg P hP n i w)
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (oscillation_nonneg _)).mpr
      (abs_sub_le_oscillation f i (endpoint n i w))

/-- Uniform finite-length variance error with the periodic-safe constant from the second inverse. -/
theorem variance_uniform_bound
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) :
    |π.pathVariance g n - (n : ℝ) * π.varianceRate hP hI g| ≤
      oscillation (π.corrector hP hI g)^2 +
        2 * oscillation (π.secondCorrector hP hI g) * Real.sqrt (π.varianceRate hP hI g) := by
  rw [π.variance_endpoint_identity hP hI g]
  have hb := π.endpoint_square_bound hP (π.corrector hP hI g) n
  have hc := π.second_poisson_covariance_bound hP hI g n
  calc
    |_ - 2 * _| ≤ |π.stationaryExpectation n (fun i w =>
        (π.corrector hP hI g i - π.corrector hP hI g (endpoint n i w))^2)| +
        |2 * π.stationaryExpectation n (fun i w => additiveSum (π.score hP hI g) n i w *
          π.corrector hP hI g (endpoint n i w))| := abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg hb.1, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]; nlinarith [hb.2]


/-- Explicit O(1/n) normalized variance error for every positive transition length. -/
theorem normalized_variance_error
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible)
    (g : V → V → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |π.pathVariance g n / (n : ℝ) - π.varianceRate hP hI g| ≤
      (oscillation (π.corrector hP hI g)^2 +
        2 * oscillation (π.secondCorrector hP hI g) * Real.sqrt (π.varianceRate hP hI g)) / n := by
  have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have he : π.pathVariance g n / n - π.varianceRate hP hI g =
      (π.pathVariance g n - (n : ℝ) * π.varianceRate hP hI g) / n := by
    field_simp
  rw [he, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right (π.variance_uniform_bound hP hI g n) hp.le

/-- Normalized variance converges without an aperiodicity or mixing assumption. -/
theorem normalized_variance_tendsto
    (hP : P ∈ Matrix.rowStochastic ℝ V) (hI : P.IsIrreducible) (g : V → V → ℝ) :
    Filter.Tendsto (fun n : ℕ => π.pathVariance g n / (n : ℝ)) Filter.atTop
      (nhds (π.varianceRate hP hI g)) := by
  have hz : Filter.Tendsto (fun n : ℕ => π.pathVariance g n / (n : ℝ) - π.varianceRate hP hI g)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm' _
      (tendsto_const_div_atTop_nhds_zero_nat
        (oscillation (π.corrector hP hI g)^2 +
          2 * oscillation (π.secondCorrector hP hI g) * Real.sqrt (π.varianceRate hP hI g)))
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simpa only [Real.norm_eq_abs] using π.normalized_variance_error hP hI g n hn
  simpa only [sub_add_cancel, zero_add] using hz.add_const (π.varianceRate hP hI g)

end Stationary
end D5.S3.Combinatorics.Graph.Pressure.MarkovAdditive
