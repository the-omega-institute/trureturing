/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attainable stationary supports admit law-preserving restriction of the native observer. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRow
import D5.S3.Observer.ProductMeasures.FinitePmfLikelihood
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Combination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Classical Filter Topology
open scoped BigOperators Matrix Matrix.Norms.Elementwise

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowLimits
open MeasureTheory ProbabilityTheory
open FourthSegmentStoppedLaw NativeAcquiredPrefixState NativeAcquiredPrefixCylinder
open NativeConditionalControl.DepthLaw NativeConditionalControl.Prefix
open NativeObserverJointLaw NativePaidHistoryCommonRow
universe u
variable {Z : Type u} [Fintype Z]
local instance : DecidableEq Z := Classical.decEq Z
local instance : PartialOrder (Matrix Z Z ℝ) := inferInstanceAs (PartialOrder (Z → Z → ℝ))
local instance : CompactIccSpace (Matrix Z Z ℝ) :=
  inferInstanceAs (CompactIccSpace (Z → Z → ℝ))
local instance : FirstCountableTopology (Matrix Z Z ℝ) :=
  inferInstanceAs (FirstCountableTopology (Z → Z → ℝ))

/-- Matrix entries come only from the acquired operation kernel. -/
def acquiredMatrix (M : Observer Z) (op : Operation) : Matrix Z Z ℝ :=
  fun x y => (M.update op x y).toReal

/-- The ordered native operation product, independent of the source. -/
def historyMatrix (M : Observer Z) : List Operation → Matrix Z Z ℝ
  | [] => 1
  | op :: h => acquiredMatrix M op * historyMatrix M h

/-- An equal-pair rejection changes the private configuration twice. -/
def rejectionMatrix (M : Observer Z) (a : Letter) : Matrix Z Z ℝ :=
  acquiredMatrix M (.read a) * acquiredMatrix M (.read a)

/-- The actual seed/latch suffix is read in its original order. -/
def latchMatrix (M : Observer Z) : Matrix Z Z ℝ := historyMatrix M (reads [1,0,1,1,0,0])

def cesaro (P : Matrix Z Z ℝ) (w : ℕ) : Matrix Z Z ℝ :=
  (w:ℝ)⁻¹ • ∑ a ∈ Finset.range w, P^a

private theorem acquired_stochastic (M : Observer Z) (op : Operation) :
    acquiredMatrix M op ∈ Matrix.rowStochastic ℝ Z :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨fun _ _ => ENNReal.toReal_nonneg,
    fun x => by simpa only [acquiredMatrix, D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass] using
      D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass_sum (Output := fun _ : Nat => Z) (i := 0) (M.update op x)⟩

private theorem history_stochastic (M : Observer Z) (h : List Operation) :
    historyMatrix M h ∈ Matrix.rowStochastic ℝ Z := by
  induction h with
  | nil => exact (Matrix.rowStochastic ℝ Z).one_mem
  | cons op h ih => exact (Matrix.rowStochastic ℝ Z).mul_mem (acquired_stochastic M op) ih

private theorem cesaro_stochastic (P : Matrix Z Z ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) (w : ℕ) (hw : 0 < w) :
    cesaro P w ∈ Matrix.rowStochastic ℝ Z := by
  have hw' : (0:ℝ) < w := Nat.cast_pos.mpr hw
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro x y
    simp only [cesaro, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hw'.le) (Finset.sum_nonneg fun a _ =>
      Matrix.nonneg_of_mem_rowStochastic ((Matrix.rowStochastic ℝ Z).pow_mem hP a))
  · intro x
    simp only [cesaro, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul,
      ← Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [Matrix.sum_row_of_mem_rowStochastic ((Matrix.rowStochastic ℝ Z).pow_mem hP _),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hw'.ne']

private theorem stochastic_norm (P : Matrix Z Z ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) : ‖P‖ ≤ 1 := by
  apply (Matrix.norm_le_iff (by norm_num : (0:ℝ) ≤ 1)).mpr
  intro x y
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hP)]
    using (Matrix.le_one_of_mem_rowStochastic hP : P x y ≤ 1)

private theorem left_contraction (P Q : Matrix Z Z ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) : ‖P*Q‖ ≤ ‖Q‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg Q)).mpr
  intro x y
  simp only [Matrix.mul_apply, Real.norm_eq_abs]
  calc
    |∑ z, P x z*Q z y| ≤ ∑ z, |P x z*Q z y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, P x z*|Q z y| := by
      apply Finset.sum_congr rfl
      intro z _
      rw [abs_mul, abs_of_nonneg (Matrix.nonneg_of_mem_rowStochastic hP)]
    _ ≤ ∑ z, P x z*‖Q‖ := Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (Matrix.norm_entry_le_entrywise_sup_norm Q)
        (Matrix.nonneg_of_mem_rowStochastic hP)
    _ = ‖Q‖ := by rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP, one_mul]

private theorem cesaro_left_residual (P : Matrix Z Z ℝ) (w : ℕ) :
    P*cesaro P w-cesaro P w = (w:ℝ)⁻¹ • (P^w-1) := by
  unfold cesaro
  rw [Matrix.mul_smul, ← smul_sub, Matrix.mul_sum]
  congr 1
  have hs : (∑ a ∈ Finset.range w, P^(a+1)) + 1 =
      (∑ a ∈ Finset.range w, P^a) + P^w := by
    rw [← pow_zero P]
    exact (Finset.sum_range_succ' (fun a => P^a) w).symm.trans
      (Finset.sum_range_succ (fun a => P^a) w)
  simp_rw [← pow_succ']
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hs)

private theorem cesaro_right_residual (P : Matrix Z Z ℝ) (w : ℕ) :
    cesaro P w*P-cesaro P w = (w:ℝ)⁻¹ • (P^w-1) := by
  unfold cesaro
  rw [Matrix.smul_mul, ← smul_sub, Matrix.sum_mul]
  congr 1
  have hs : (∑ a ∈ Finset.range w, P^(a+1)) + 1 =
      (∑ a ∈ Finset.range w, P^a) + P^w := by
    rw [← pow_zero P]
    exact (Finset.sum_range_succ' (fun a => P^a) w).symm.trans
      (Finset.sum_range_succ (fun a => P^a) w)
  simp_rw [← pow_succ]
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using hs)

private theorem cesaro_residual_bound (P : Matrix Z Z ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) (w : ℕ) :
    ‖(w:ℝ)⁻¹ • (P^w-1)‖ ≤ 2/(w:ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg w))]
  have h := (norm_sub_le (P^w) 1).trans (add_le_add
    (stochastic_norm _ ((Matrix.rowStochastic ℝ Z).pow_mem hP w))
    (stochastic_norm _ (Matrix.rowStochastic ℝ Z).one_mem))
  calc
    _ ≤ (w:ℝ)⁻¹*2 := mul_le_mul_of_nonneg_left (show ‖P^w-1‖ ≤ (2:ℝ) from by norm_num at h ⊢; exact h) (inv_nonneg.mpr (Nat.cast_nonneg w))
    _ = 2/(w:ℝ) := by ring

private theorem stochastic_limit (P : ℕ → Matrix Z Z ℝ) (E : Matrix Z Z ℝ)
    (hP : ∀ n, P n ∈ Matrix.rowStochastic ℝ Z) (h : Tendsto P atTop (𝓝 E)) :
    E ∈ Matrix.rowStochastic ℝ Z := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  constructor
  · intro x y
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h x)) y)
      (Eventually.of_forall fun n => Matrix.nonneg_of_mem_rowStochastic (hP n))
  · intro x
    have ht : Tendsto (fun n => ∑ y, P n x y) atTop (𝓝 (∑ y, E x y)) :=
      tendsto_finsetSum _ fun y _ => (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp h x)) y
    have he : (fun n => ∑ y, P n x y) = fun _ => (1:ℝ) :=
      funext fun n => Matrix.sum_row_of_mem_rowStochastic (hP n) x
    rw [he] at ht
    exact tendsto_nhds_unique ht tendsto_const_nhds

private theorem pair_cluster (P Q : Matrix Z Z ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) (hQ : Q ∈ Matrix.rowStochastic ℝ Z) :
    ∃ E F : Matrix Z Z ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => cesaro P (φ n+1)) atTop (𝓝 E) ∧
      Tendsto (fun n => cesaro Q (φ n+1)) atTop (𝓝 F) := by
  let ones : Matrix Z Z ℝ := fun _ _ => 1
  have hc : IsCompact (Set.Icc ((0:Matrix Z Z ℝ),0) (ones,ones)) := isCompact_Icc
  have hx : ∀ n : ℕ, (cesaro P (n+1),cesaro Q (n+1)) ∈
      Set.Icc ((0:Matrix Z Z ℝ),0) (ones,ones) := by
    intro n
    refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
    · intro x y
      exact Matrix.nonneg_of_mem_rowStochastic (cesaro_stochastic P hP _ (by omega))
    · intro x y
      exact Matrix.nonneg_of_mem_rowStochastic (cesaro_stochastic Q hQ _ (by omega))
    · intro x y
      exact Matrix.le_one_of_mem_rowStochastic (cesaro_stochastic P hP _ (by omega))
    · intro x y
      exact Matrix.le_one_of_mem_rowStochastic (cesaro_stochastic Q hQ _ (by omega))
  obtain ⟨EF,_,φ,hφ,h⟩ := hc.tendsto_subseq hx
  exact ⟨EF.1,EF.2,φ,hφ,by exact ((continuous_fst.tendsto EF).comp h).congr (fun n => rfl),
    by exact ((continuous_snd.tendsto EF).comp h).congr (fun n => rfl)⟩

private theorem cesaro_fixed (P E : Matrix Z Z ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) (w : ℕ → ℕ)
    (hw : Tendsto w atTop atTop) (h : Tendsto (fun n => cesaro P (w n)) atTop (𝓝 E)) :
    P*E = E ∧ E*P = E := by
  have hR : Tendsto (fun n => (w n:ℝ)⁻¹ • (P^(w n)-1)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro x
    apply tendsto_pi_nhds.mpr
    intro y
    apply squeeze_zero_norm
      (fun n => (Matrix.norm_entry_le_entrywise_sup_norm ((w n:ℝ)⁻¹ • (P^(w n)-1))).trans
        (cesaro_residual_bound P hP (w n)))
    exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hw)
  constructor
  · have ht : Tendsto (fun n => P*cesaro P (w n)-cesaro P (w n)) atTop (𝓝 (P*E-E)) :=
      (tendsto_const_nhds.mul h).sub h
    have he := tendsto_nhds_unique ht (hR.congr fun n => (cesaro_left_residual P (w n)).symm)
    exact sub_eq_zero.mp he
  · have ht : Tendsto (fun n => cesaro P (w n)*P-cesaro P (w n)) atTop (𝓝 (E*P-E)) :=
      (h.mul tendsto_const_nhds).sub h
    have he := tendsto_nhds_unique ht (hR.congr fun n => (cesaro_right_residual P (w n)).symm)
    exact sub_eq_zero.mp he

private theorem arbitrary_shift (P E : Matrix Z Z ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) (hE : P*E = E)
    (w a : ℕ → ℕ) (h : Tendsto (fun n => cesaro P (w n)) atTop (𝓝 E)) :
    Tendsto (fun n => P^(a n)*cesaro P (w n)) atTop (𝓝 E) := by
  have hp (b : ℕ) : P^b*E = E := by
    induction b with
    | zero => simp
    | succ b ih => rw [pow_succ', mul_assoc, ih, hE]
  change Tendsto (fun n x y => cesaro P (w n) x y) atTop (𝓝 (fun x y => E x y)) at h
  change Tendsto (fun n x y => (P^(a n)*cesaro P (w n)) x y)
    atTop (𝓝 (fun x y => E x y))
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h
  change ‖P^(a n)*cesaro P (w n)-E‖ ≤ ‖cesaro P (w n)-E‖
  calc
    _ = ‖P^(a n)*(cesaro P (w n)-E)‖ := by rw [Matrix.mul_sub, hp]
    _ ≤ _ := left_contraction _ _ ((Matrix.rowStochastic ℝ Z).pow_mem hP _)

private theorem history_append (M : Observer Z) (h v : List Operation) :
    historyMatrix M (h++v) = historyMatrix M h*historyMatrix M v := by
  induction h with
  | nil => simp [historyMatrix]
  | cons op h ih => simp only [List.cons_append, historyMatrix, ih, mul_assoc]

private theorem retry_matrix (M : Observer Z) (a : Letter) (m : ℕ) :
    historyMatrix M (reads (retryWord (List.replicate m a))) = rejectionMatrix M a^m := by
  induction m with
  | zero => simp [retryWord, reads, historyMatrix]
  | succ m ih =>
    simp only [List.replicate_succ, retryWord, List.map_cons, List.flatten_cons,
      reads, List.map_append, List.map_cons, List.map_nil]
    change acquiredMatrix M (.read a)*(acquiredMatrix M (.read a)*
      historyMatrix M (reads (retryWord (List.replicate m a)))) = _
    rw [ih, ← mul_assoc, pow_succ', rejectionMatrix]

private theorem window_matrix (M : Observer Z) (m t : ℕ) :
    historyMatrix M (windowHistory m t 0 .p) =
      rejectionMatrix M 0^m*rejectionMatrix M 1^t*latchMatrix M := by
  unfold windowHistory windowWord
  simp only [loopWord, phaseWord, List.append_nil, retryWord, List.map_append,
    List.flatten_append, reads, List.map_append, List.replicate_zero, List.flatten_nil, List.map_nil]
  simp only [history_append, historyMatrix, mul_one]
  change historyMatrix M (reads (retryWord (List.replicate m 0)))*
    historyMatrix M (reads (retryWord (List.replicate t 1)))*latchMatrix M = _
  rw [retry_matrix, retry_matrix]

theorem bind_real (η : PMF Z) (U : Z → PMF Z) (y : Z) :
    (η.bind U y).toReal = ∑ x, (η x).toReal*(U x y).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum
    (fun x _ => ENNReal.mul_ne_top (η.apply_ne_top x) ((U x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul]

private theorem advance_real (M : Observer Z) (η : PMF Z) (h : List Operation) :
    (fun y => (advance M η h y).toReal) = (fun x => (η x).toReal) ᵥ* historyMatrix M h := by
  induction h generalizing η with
  | nil => simp [advance, historyMatrix]
  | cons op h ih =>
    rw [advance, ih, historyMatrix, ← Matrix.vecMul_vecMul]
    congr 1
    funext y
    exact bind_real η (M.update op) y

/-- Finite convex averages of actual rows; they are not posterior rows of a single history. -/
def windowAverage (M : Observer Z) (w : ℕ) (k : Depth) : Z → ℝ :=
  (w:ℝ)⁻¹ • ∑ u ∈ Finset.range w, (w:ℝ)⁻¹ • ∑ v ∈ Finset.range w,
    fun z => (row M (windowHistory (windowCount w (rate k) u)
      (windowCount w (1-(rate k:ℝ)) v) 0 .p) z).toReal

private theorem window_average_factor (M : Observer Z) (w : ℕ) (k : Depth) :
    windowAverage M w k = (fun z => (M.init z).toReal) ᵥ*
      ((rejectionMatrix M 0^⌊(w:ℝ)^3*(rate k:ℝ)⌋₊*cesaro (rejectionMatrix M 0) w)*
      (rejectionMatrix M 1^⌊(w:ℝ)^3*(1-(rate k:ℝ))⌋₊*cesaro (rejectionMatrix M 1) w)*
        latchMatrix M) := by
  unfold windowAverage
  simp_rw [row, advance_real, window_matrix, windowCount, pow_add]
  unfold cesaro
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.vecMul_smul, Matrix.vecMul_sum, smul_smul, Matrix.vecMul_vecMul,
    mul_assoc, Finset.smul_sum]
  rw [Finset.sum_comm]

/-- The same two stochastic matrix limits serve every native rate and every shift. -/
theorem native_common_window_limit (M : Observer Z) :
    ∃ E F : Matrix Z Z ℝ, ∃ φ : ℕ → ℕ, ∃ eta : Z → ℝ,
      StrictMono φ ∧ E ∈ Matrix.rowStochastic ℝ Z ∧ F ∈ Matrix.rowStochastic ℝ Z ∧
      rejectionMatrix M 0*E = E ∧ E*rejectionMatrix M 0 = E ∧
      rejectionMatrix M 1*F = F ∧ F*rejectionMatrix M 1 = F ∧
      eta = (fun z => (M.init z).toReal) ᵥ* (E*F*latchMatrix M) ∧
      (∀ z, 0 ≤ eta z) ∧ (∑ z, eta z) = 1 ∧
      (∀ k : Depth, Tendsto (fun n => windowAverage M (φ n+1) k) atTop (𝓝 eta)) ∧
      (∀ z, 0 < eta z → ∃ m t : ℕ, 0 < row M (windowHistory m t 0 .p) z) := by
  let P := rejectionMatrix M 0
  let Q := rejectionMatrix M 1
  have hP : P ∈ Matrix.rowStochastic ℝ Z :=
    (Matrix.rowStochastic ℝ Z).mul_mem (acquired_stochastic M _) (acquired_stochastic M _)
  have hQ : Q ∈ Matrix.rowStochastic ℝ Z :=
    (Matrix.rowStochastic ℝ Z).mul_mem (acquired_stochastic M _) (acquired_stochastic M _)
  obtain ⟨E,F,φ,hφ,hE,hF⟩ := pair_cluster P Q hP hQ
  have hw : Tendsto (fun n => φ n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop
  have hfE := cesaro_fixed P E hP _ hw hE
  have hfF := cesaro_fixed Q F hQ _ hw hF
  let eta := (fun z => (M.init z).toReal) ᵥ* (E*F*latchMatrix M)
  have heta (k : Depth) : Tendsto (fun n => windowAverage M (φ n+1) k) atTop (𝓝 eta) := by
    have he := arbitrary_shift P E hP hfE.1 _
      (fun n => ⌊(φ n+1:ℝ)^3*(rate k:ℝ)⌋₊) hE
    have hf := arbitrary_shift Q F hQ hfF.1 _
      (fun n => ⌊(φ n+1:ℝ)^3*(1-(rate k:ℝ))⌋₊) hF
    have hm := (he.mul hf).mul_const (latchMatrix M)
    have hc : Continuous (fun K : Matrix Z Z ℝ => (fun z => (M.init z).toReal) ᵥ* K) :=
      continuous_const.matrix_vecMul continuous_id
    have ht := (hc.tendsto (E*F*latchMatrix M)).comp hm
    apply ht.congr
    intro n
    simpa only [Function.comp_apply, P, Q, Nat.cast_add, Nat.cast_one] using
      (window_average_factor M (φ n+1) k).symm
  have hEs := stochastic_limit _ E (fun n => cesaro_stochastic P hP _ (by omega)) hE
  have hFs := stochastic_limit _ F (fun n => cesaro_stochastic Q hQ _ (by omega)) hF
  have hK : E*F*latchMatrix M ∈ Matrix.rowStochastic ℝ Z :=
    (Matrix.rowStochastic ℝ Z).mul_mem ((Matrix.rowStochastic ℝ Z).mul_mem hEs hFs)
      (history_stochastic M _)
  have hm : (∑ z, eta z) = 1 := by
    have h := Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hK
      (x := fun z => (M.init z).toReal) (by simpa [dotProduct, D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass] using
        D5.S3.Observer.ProductMeasures.FinitePmfLikelihood.pmfRealMass_sum (Output := fun _ : Nat => Z) (i := 0) M.init)
    simpa [dotProduct, eta] using h
  refine ⟨E,F,φ,eta,hφ,hEs,hFs,hfE.1,hfE.2,hfF.1,hfF.2,rfl,
    Matrix.nonneg_vecMul_of_mem_rowStochastic hK (fun _ => ENNReal.toReal_nonneg),hm,heta,?_⟩
  intro z hz
  by_contra hn
  push_neg at hn
  have hzero : ∀ m t, row M (windowHistory m t 0 .p) z = 0 := by
    intro m t
    exact le_antisymm (hn m t) zero_le
  have ha : ∀ n, windowAverage M (φ n+1) 1 z = 0 := by
    intro n
    simp [windowAverage, hzero]
  have ht := (tendsto_pi_nhds.mp (heta 1)) z
  simp only [ha] at ht
  have he : eta z = 0 := tendsto_nhds_unique ht tendsto_const_nhds
  linarith

#print axioms native_common_window_limit

/-- The original unweighted acquired return is beta followed by alpha. -/
def returnMatrix (M : Observer Z) : Matrix Z Z ℝ :=
  acquiredMatrix M (.read 1)*acquiredMatrix M (.read 0)

def phaseMatrix (M : Observer Z) : ActivePhase → Matrix Z Z ℝ
  | .p => 1
  | .beta => acquiredMatrix M (.read 1)

private theorem loop_matrix (M : Observer Z) (j : ℕ) :
    historyMatrix M (reads (loopWord j)) = returnMatrix M^j := by
  induction j with
  | zero => simp [loopWord, reads, historyMatrix]
  | succ j ih =>
    rw [loop_succ]
    change acquiredMatrix M (.read 1)*(acquiredMatrix M (.read 0)*
      historyMatrix M (reads (loopWord j))) = _
    rw [ih, ← mul_assoc, pow_succ', returnMatrix]

private theorem window_history_suffix (m t j : ℕ) (s : ActivePhase) :
    windowHistory m t j s = windowHistory m t 0 .p ++ reads (loopWord j) ++ reads (phaseWord s) := by
  simp [windowHistory, windowWord, loopWord, phaseWord, reads, List.map_append, List.append_assoc]

private theorem window_row_suffix (M : Observer Z) (m t j : ℕ) (s : ActivePhase) :
    (fun z => (row M (windowHistory m t j s) z).toReal) =
      (fun z => (row M (windowHistory m t 0 .p) z).toReal) ᵥ*
        (returnMatrix M^j*phaseMatrix M s) := by
  letI : MeasurableSpace Z := ⊤
  letI : MeasurableSingletonClass Z := ⟨fun _ => trivial⟩
  rw [window_history_suffix, row, advance_append, advance_append, advance_real, advance_real,
    Matrix.vecMul_vecMul, loop_matrix]
  cases s <;> simp [phaseWord, reads, historyMatrix, phaseMatrix, row]

/-- Append actual returns to every finite summand, without treating the average as a history. -/
def returnedAverage (M : Observer Z) (w : ℕ) (k : Depth) (j : ℕ) (s : ActivePhase) : Z → ℝ :=
  windowAverage M w k ᵥ* (returnMatrix M^j*phaseMatrix M s)

theorem returned_average_actual (M : Observer Z) (w : ℕ) (k : Depth)
    (j : ℕ) (s : ActivePhase) :
    returnedAverage M w k j s = (w:ℝ)⁻¹ • ∑ u ∈ Finset.range w,
      (w:ℝ)⁻¹ • ∑ v ∈ Finset.range w,
        fun z => (row M (windowHistory (windowCount w (rate k) u)
          (windowCount w (1-(rate k:ℝ)) v) j s) z).toReal := by
  unfold returnedAverage windowAverage
  simp only [Matrix.smul_vecMul, Matrix.sum_vecMul]
  simp_rw [← window_row_suffix]

private theorem returned_witness (M : Observer Z) (eta : Z → ℝ) (w : ℕ → ℕ)
    (h : Tendsto (fun n => windowAverage M (w n) 1) atTop (𝓝 eta))
    (j : ℕ) (s : ActivePhase) (z : Z)
    (hz : 0 < (eta ᵥ* (returnMatrix M^j*phaseMatrix M s)) z) :
    ∃ m t : ℕ, 0 < row M (windowHistory m t j s) z := by
  have hc : Continuous (fun v : Z → ℝ => v ᵥ* (returnMatrix M^j*phaseMatrix M s)) :=
    continuous_id.matrix_vecMul continuous_const
  have ht := (hc.tendsto eta).comp h
  by_contra hn
  push Not at hn
  have hz0 : ∀ m t, row M (windowHistory m t j s) z = 0 :=
    fun m t => le_antisymm (hn m t) zero_le
  have ha : ∀ n, returnedAverage M (w n) 1 j s z = 0 := by
    intro n
    rw [returned_average_actual]
    simp [hz0]
  have he : (eta ᵥ* (returnMatrix M^j*phaseMatrix M s)) z = 0 := by
    have hp := (tendsto_pi_nhds.mp ht) z
    change Tendsto (fun n => returnedAverage M (w n) 1 j s z) atTop (𝓝 _) at hp
    simp only [ha] at hp
    exact tendsto_nhds_unique hp tendsto_const_nhds
  linarith

private theorem positive_flow (P : Matrix Z Z ℝ) (v : Z → ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Z) (hv : ∀ x, 0 ≤ v x)
    (x y : Z) (hx : 0 < v x) (hxy : 0 < P x y) : 0 < (v ᵥ* P) y := by
  apply lt_of_lt_of_le (mul_pos hx hxy)
  change v x*P x y ≤ ∑ z, v z*P z y
  exact Finset.single_le_sum (f := fun z => v z*P z y) (fun z _ => mul_nonneg (hv z)
    (Matrix.nonneg_of_mem_rowStochastic hP)) (Finset.mem_univ x)

/-- One common attainable stationary pair for the two actual acquired updates.
All positive labels have finite paid-history witnesses and the two positive supports are closed.
No irreducibility, aperiodicity or positive-entry premise is imposed. -/
theorem native_common_stationary_rows (M : Observer Z) :
    ∃ pi tau eta : Z → ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀ k : Depth, Tendsto (fun n => windowAverage M (φ n+1) k) atTop (𝓝 eta)) ∧
      (∀ z, 0 ≤ pi z) ∧ (∑ z, pi z) = 1 ∧
      (∀ z, 0 ≤ tau z) ∧ (∑ z, tau z) = 1 ∧
      pi ᵥ* returnMatrix M = pi ∧
      pi ᵥ* acquiredMatrix M (.read 1) = tau ∧
      tau ᵥ* acquiredMatrix M (.read 0) = pi ∧
      (∀ z, 0 < pi z → ∃ m t j : ℕ, 0 < row M (windowHistory m t j .p) z) ∧
      (∀ z, 0 < tau z → ∃ m t j : ℕ, 0 < row M (windowHistory m t j .beta) z) ∧
      (∀ x y, 0 < pi x → 0 < acquiredMatrix M (.read 1) x y → 0 < tau y) ∧
      (∀ y x, 0 < tau y → 0 < acquiredMatrix M (.read 0) y x → 0 < pi x) ∧
      (∀ D : ActivePhase → Set (Z → ℝ), (∀ s, IsClosed (D s)) →
        (∀ s, Convex ℝ (D s)) →
        (∀ j s, eta ᵥ* (returnMatrix M^j*phaseMatrix M s) ∈ D s) →
        pi ∈ D .p ∧ tau ∈ D .beta) := by
  obtain ⟨E,F,φ,eta,hφ,hEs,hFs,hE1,hE2,hF1,hF2,heta,hη0,hη1,hlim,hreach⟩ :=
    native_common_window_limit M
  let C := returnMatrix M
  have hC : C ∈ Matrix.rowStochastic ℝ Z :=
    (Matrix.rowStochastic ℝ Z).mul_mem (acquired_stochastic M _) (acquired_stochastic M _)
  obtain ⟨G,_,ψ,hψ,hG,_⟩ := pair_cluster C C hC hC
  have hw : Tendsto (fun n => ψ n+1) atTop atTop := (tendsto_add_atTop_nat 1).comp hψ.tendsto_atTop
  have hGs := stochastic_limit _ G (fun n => cesaro_stochastic C hC _ (by omega)) hG
  have hf := (cesaro_fixed C G hC _ hw hG).2
  let pi := eta ᵥ* G
  let tau := pi ᵥ* acquiredMatrix M (.read 1)
  have hp0 : ∀ z, 0 ≤ pi z := Matrix.nonneg_vecMul_of_mem_rowStochastic hGs hη0
  have hp1 : (∑ z, pi z) = 1 := by
    have h := Matrix.vecMul_dotProduct_one_eq_one_rowStochastic hGs
      (x := eta) (by simpa [dotProduct] using hη1)
    simpa [dotProduct, pi] using h
  have ht0 : ∀ z, 0 ≤ tau z :=
    Matrix.nonneg_vecMul_of_mem_rowStochastic (acquired_stochastic M _) hp0
  have ht1 : (∑ z, tau z) = 1 := by
    have h := Matrix.vecMul_dotProduct_one_eq_one_rowStochastic (acquired_stochastic M (.read 1))
      (x := pi) (by simpa [dotProduct] using hp1)
    simpa [dotProduct, tau] using h
  have hstat : pi ᵥ* C = pi := by
    dsimp [pi]
    rw [Matrix.vecMul_vecMul, hf]
  have hback : tau ᵥ* acquiredMatrix M (.read 0) = pi := by
    change (pi ᵥ* acquiredMatrix M (.read 1)) ᵥ* acquiredMatrix M (.read 0) = pi
    rw [Matrix.vecMul_vecMul]
    exact hstat
  have hpc : Tendsto (fun n => eta ᵥ* cesaro C (ψ n+1)) atTop (𝓝 pi) := by
    have hc : Continuous (fun K : Matrix Z Z ℝ => eta ᵥ* K) :=
      continuous_const.matrix_vecMul continuous_id
    exact ((hc.tendsto G).comp hG).congr (fun n => rfl)
  have hphase (s : ActivePhase) :
      Tendsto (fun n => (eta ᵥ* cesaro C (ψ n+1)) ᵥ* phaseMatrix M s) atTop
        (𝓝 (pi ᵥ* phaseMatrix M s)) := by
    have hc : Continuous (fun v : Z → ℝ => v ᵥ* phaseMatrix M s) :=
      continuous_id.matrix_vecMul continuous_const
    exact ((hc.tendsto pi).comp hpc).congr (fun n => rfl)
  have hr (s : ActivePhase) (z : Z) (hz : 0 < (pi ᵥ* phaseMatrix M s) z) :
      ∃ m t j : ℕ, 0 < row M (windowHistory m t j s) z := by
    have hj : ∃ j : ℕ, 0 < (eta ᵥ* (C^j*phaseMatrix M s)) z := by
      by_contra hn
      push Not at hn
      have hzero : ∀ j, (eta ᵥ* (C^j*phaseMatrix M s)) z = 0 := by
        intro j
        apply le_antisymm (hn j)
        exact Matrix.nonneg_vecMul_of_mem_rowStochastic
          ((Matrix.rowStochastic ℝ Z).mul_mem ((Matrix.rowStochastic ℝ Z).pow_mem hC j)
            (by cases s <;> simp [phaseMatrix, acquired_stochastic])) hη0 z
      have he := (tendsto_pi_nhds.mp (hphase s)) z
      have hz0 : ∀ n, ((eta ᵥ* cesaro C (ψ n+1)) ᵥ* phaseMatrix M s) z = 0 := by
        intro n
        simp only [cesaro, Matrix.vecMul_smul, Matrix.vecMul_sum,
          Matrix.smul_vecMul, Matrix.sum_vecMul, Matrix.vecMul_vecMul]
        simp [hzero]
      simp only [hz0] at he
      have hEq : (pi ᵥ* phaseMatrix M s) z = 0 := tendsto_nhds_unique he tendsto_const_nhds
      linarith
    obtain ⟨j,hj⟩ := hj
    obtain ⟨m,t,ht⟩ := returned_witness M eta (fun n => φ n+1) (hlim 1) j s z hj
    exact ⟨m,t,j,ht⟩
  refine ⟨pi,tau,eta,φ,hφ,hlim,hp0,hp1,ht0,ht1,hstat,rfl,hback,?_,?_,?_,?_,?_⟩
  · intro z hz
    apply hr .p z
    simpa [phaseMatrix] using hz
  · intro z hz
    exact hr .beta z hz
  · exact fun x y hx hxy => positive_flow _ _ (acquired_stochastic M _) hp0 x y hx hxy
  · intro y x hy hyx
    rw [← hback]
    exact positive_flow _ _ (acquired_stochastic M _) ht0 y x hy hyx
  · intro D hclosed hconvex horbit
    have hmem (s : ActivePhase) : pi ᵥ* phaseMatrix M s ∈ D s := by
      apply (hclosed s).mem_of_tendsto (hphase s)
      apply Eventually.of_forall
      intro n
      simp only [cesaro, Matrix.vecMul_smul, Matrix.vecMul_sum,
        Matrix.smul_vecMul, Matrix.sum_vecMul, Matrix.vecMul_vecMul]
      rw [Finset.smul_sum]
      apply (hconvex s).sum_mem
      · intro j hj
        exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega))
      · intro j hj
        exact horbit j s
    exact ⟨by simpa [phaseMatrix] using hmem .p, hmem .beta⟩

#print axioms native_common_stationary_rows


section MeasurableSingletonLaws
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
open NativeInstalledFullLaw NativeFullResidual
open scoped ENNReal

/-- Original active held fields; endpoint fields retain their own writes and Stop blocks. -/
def heldFields (s : ActivePhase) : FiniteFields := ⟨.fourth (.active s),heldRegisters⟩

def terminal (M : Observer Z) (z : Z) : Prop :=
  (∃ b : Letter, (M.project z).control = .fourth (.pending b)) ∨
    (M.project z).control = .fourth .delivered

/-- Only zero stationary labels on the designated active fibre are removed. -/
def retained (M : Observer Z) (pi tau : PMF Z) (z : Z) : Prop :=
  (M.project z ≠ heldFields .p ∧ M.project z ≠ heldFields .beta) ∨
    z ∈ pi.support ∨ z ∈ tau.support

private def good (M : Observer Z) (pi tau : PMF Z) : Set Z :=
  {z | z ∈ pi.support ∨ z ∈ tau.support ∨ terminal M z}

/-- Clipping redirects only deleted columns to a retained label with identical finite fields. -/
def clippedObserver (M : Observer Z) (q : Z → Z) (hq : ∀ z, M.project (q z) = M.project z) :
    Observer Z where
  project := M.project
  init := M.init
  update op z := (M.update op z).map q
  init_refines := M.init_refines
  update_refines := by
    intro op z fields hf y hy
    obtain ⟨x,hx,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    exact (hq x).trans (M.update_refines op z fields hf x hx)

def clippedEmitter (M : Observer Z) (e : InstalledEmitter M)
    (q : Z → Z) (hq : ∀ z, M.project (q z) = M.project z) : InstalledEmitter (clippedObserver M q hq) where
  emit := e.emit
  lawful := e.lawful

private theorem pmf_map_fixed (η : PMF Z) (q : Z → Z)
    (hq : ∀ z ∈ η.support, q z = z) : η.map q = η := by
  classical
  conv_rhs => rw [← PMF.map_id η]
  ext y
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ η.support
  · rw [hq x hx]; rfl
  · have hz : η x = 0 := by simpa only [PMF.mem_support_iff, not_ne_iff] using hx
    simp only [hz, ite_self]

private theorem terminal_avoids (M : Observer Z) (z : Z) (hz : terminal M z) :
    M.project z ≠ heldFields .p ∧ M.project z ≠ heldFields .beta := by
  rcases hz with ⟨b,hb⟩ | hd
  · constructor <;> intro h <;> have hc := congrArg FiniteFields.control h
    all_goals simp only [heldFields, hb] at hc
    all_goals cases hc
  · constructor <;> intro h <;> have hc := congrArg FiniteFields.control h
    all_goals simp only [heldFields, hd] at hc
    all_goals cases hc

private theorem terminal_update (M : Observer Z) (z : Z) (hz : terminal M z)
    (op : Operation) (fields : FiniteFields) (hf : finiteStep (M.project z) op = some fields)
    (y : Z) (hy : y ∈ (M.update op z).support) : terminal M y := by
  have hp := M.update_refines op z fields hf y hy
  rcases hz with ⟨b,hb⟩ | hd
  · cases op with
    | read a => simp [finiteStep,finiteRead,hb] at hf
    | stop a =>
      simp only [finiteStep,finiteStop,hb] at hf
      split_ifs at hf with h
      · have he := Option.some.inj hf
        right
        rw [hp, ← he]
  · cases op <;> simp [finiteStep,finiteRead,finiteStop,hd] at hf

private theorem good_update (M : Observer Z) (pi tau : PMF Z)
    (hX : ∀ z ∈ pi.support, M.project z = heldFields .p)
    (hY : ∀ z ∈ tau.support, M.project z = heldFields .beta)
    (hB : ∀ x ∈ pi.support, ∀ y ∈ (M.update (.read 1) x).support, y ∈ tau.support)
    (hA : ∀ y ∈ tau.support, ∀ x ∈ (M.update (.read 0) y).support, x ∈ pi.support)
    (z : Z) (hz : z ∈ good M pi tau) (op : Operation) (fields : FiniteFields)
    (hf : finiteStep (M.project z) op = some fields) (y : Z)
    (hy : y ∈ (M.update op z).support) : y ∈ good M pi tau := by
  rcases hz with hx | hy' | ht
  · cases op with
    | stop b => simp [finiteStep,finiteStop,hX z hx,heldFields] at hf
    | read b =>
      fin_cases b
      · right; right; left
        refine ⟨0, ?_⟩
        have hp := M.update_refines (.read 0) z fields hf y hy
        simp [finiteStep,finiteRead,hX z hx,heldFields,payloadRead,completionControl] at hf
        rw [hp, ← hf]
      · exact Or.inr (Or.inl (hB z hx y hy))
  · cases op with
    | stop b => simp [finiteStep,finiteStop,hY z hy',heldFields] at hf
    | read b =>
      fin_cases b
      · exact Or.inl (hA z hy' y hy)
      · right; right; left
        refine ⟨1, ?_⟩
        have hp := M.update_refines (.read 1) z fields hf y hy
        simp [finiteStep,finiteRead,hY z hy',heldFields,payloadRead,completionControl] at hf
        rw [hp, ← hf]
  · exact Or.inr (Or.inr (terminal_update M z ht op fields hf y hy))

/-- The support-closed original return kernels admit zero-column deletion while copying
both complete generated laws. Equality is on the entire infinite trajectory space. -/
theorem native_support_clipping (M : Observer Z) (e : InstalledEmitter M) (pi tau : PMF Z)
    (hX : ∀ z ∈ pi.support, M.project z = heldFields .p)
    (hY : ∀ z ∈ tau.support, M.project z = heldFields .beta)
    (hB : ∀ x ∈ pi.support, ∀ y ∈ (M.update (.read 1) x).support, y ∈ tau.support)
    (hA : ∀ y ∈ tau.support, ∀ x ∈ (M.update (.read 0) y).support, x ∈ pi.support) :
    ∃ q : Z → Z, ∃ hq : ∀ z, M.project (q z) = M.project z,
      (∀ z, retained M pi tau (q z)) ∧
      (∀ z, retained M pi tau z → q z = z) ∧
      (∀ op z y, y ∈ ((clippedObserver M q hq).update op z).support → retained M pi tau y) ∧
      (∀ x ∈ pi.support, (clippedObserver M q hq).update (.read 1) x = M.update (.read 1) x) ∧
      (∀ y ∈ tau.support, (clippedObserver M q hq).update (.read 0) y = M.update (.read 0) y) ∧
      (∀ z, z ∈ pi.support ∨ z ∈ tau.support →
        markedLaw (clippedObserver M q hq) (clippedEmitter M e q hq) (z,none) = markedLaw M e (z,none) ∧
        fullLaw (clippedObserver M q hq) (clippedEmitter M e q hq) z = fullLaw M e z ∧
        ∀ s : ActivePhase, tailLaw (clippedObserver M q hq) (clippedEmitter M e q hq) s z = tailLaw M e s z) := by
  classical
  obtain ⟨x0,hx0⟩ := pi.support_nonempty
  obtain ⟨y0,hy0⟩ := tau.support_nonempty
  let q : Z → Z := fun z => if retained M pi tau z then z
    else if M.project z = heldFields .p then x0 else y0
  have hqi (z : Z) (hz : retained M pi tau z) : q z = z := by simp only [q, if_pos hz]
  have hqr (z : Z) : retained M pi tau (q z) := by
    by_cases hz : retained M pi tau z
    · rw [hqi z hz]; exact hz
    · dsimp only [q]; rw [if_neg hz]
      split_ifs
      · exact Or.inr (Or.inl hx0)
      · exact Or.inr (Or.inr hy0)
  have hqp (z : Z) : M.project (q z) = M.project z := by
    by_cases hz : retained M pi tau z
    · rw [hqi z hz]
    · have hfields : M.project z = heldFields .p ∨ M.project z = heldFields .beta := by
        by_contra hn
        push_neg at hn
        exact hz (Or.inl hn)
      dsimp only [q]; rw [if_neg hz]
      split_ifs with hp
      · exact (hX x0 hx0).trans hp.symm
      · exact (hY y0 hy0).trans ((hfields.resolve_left hp).symm)
  have hgi (z : Z) (hz : z ∈ good M pi tau) : q z = z := by
    apply hqi
    rcases hz with hx | hy | ht
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr hy)
    · exact Or.inl (terminal_avoids M z ht)
  have hgc := good_update M pi tau hX hY hB hA
  have hrow (z : Z) (hz : z ∈ good M pi tau) (a : Option Operation) :
      markedRow M e (z,a) = markedRow (clippedObserver M q hqp) (clippedEmitter M e q hqp) (z,a) := by
    ext v
    simp only [markedRow, clippedEmitter, PMF.bind_apply]
    apply tsum_congr
    intro op
    by_cases ho : op ∈ (e.emit z).support
    · cases op with
      | none => rfl
      | some op =>
        obtain ⟨fields,hf⟩ := Option.isSome_iff_exists.mp (e.lawful z (some op) ho)
        have hfix : (M.update op z).map q = M.update op z := pmf_map_fixed _ q
          (fun y hy => hgi y (hgc z hz op fields hf y hy))
        simp only [clippedObserver, hfix]
    · have he : e.emit z op = 0 := by simpa only [PMF.mem_support_iff, not_ne_iff] using ho
      simp only [he, zero_mul]
  have hclosed (z : Z) (hz : z ∈ good M pi tau) (a : Option Operation)
      (v : Marked Z) (hv : v ∈ (markedRow M e (z,a)).support) : v.1 ∈ good M pi tau := by
    obtain ⟨op,ho,hv⟩ := (PMF.mem_support_bind_iff _ _ _).mp hv
    cases op with
    | none =>
      have he := (PMF.mem_support_pure_iff _ _).mp hv
      subst v; exact hz
    | some op =>
      obtain ⟨y,hy,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
      obtain ⟨fields,hf⟩ := Option.isSome_iff_exists.mp (e.lawful z (some op) ho)
      exact hgc z hz op fields hf y hy
  refine ⟨q,hqp,hqr,hqi,?_,?_,?_,?_⟩
  · intro op z y hy
    obtain ⟨v,hv,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hy
    exact hqr v
  · intro x hx
    exact pmf_map_fixed _ q (fun y hy => hqi y (Or.inr (Or.inr (hB x hx y hy))))
  · intro y hy
    exact pmf_map_fixed _ q (fun x hx => hqi x (Or.inr (Or.inl (hA y hy x hx))))
  · intro z hz
    apply installed_law_invariant M (clippedObserver M q hqp) e (clippedEmitter M e q hqp)
      (good M pi tau) hrow hclosed rfl z
    exact hz.elim Or.inl (fun h => Or.inr (Or.inl h))

#print axioms native_support_clipping

end MeasurableSingletonLaws

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.NativePaidHistoryCommonRowLimits
