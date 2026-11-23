/- GID: D5/S3/Quantum/Measurement/OrderScores/QubitJensenShannon
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/OrderScores/QubitJensenShannon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The native qubit order score is an attained maximum on a closed Bloch disk. -/

/-
admission_basis: escape-witness
parameter_calibration: proof_shape: bind-only. Consumers: native_score_on_coordinates, maximizing_circle and quantitative_increase.
native_maximum: proof_shape: content. escape_witness: native_score_range identifies exactly the entire native range with the closed disk image.
series_weight_pos: proof_shape: bind-only. Consumers: bias_term_bound, summable_series_weight, disk_score_le_of_coeff_le and circle_score_increment.
coeff_zero: proof_shape: bind-only. Consumer: QubitJensenShannonMonotonicity.first_circle_coeff.
disk_series: proof_shape: content. escape_witness: bias_series extends the real-log expansion to both extreme biases by summable domination.
disk_score_le_of_coeff_le: proof_shape: content. escape_witness: disk_series supplies actual sums for both scores and their shared positive weights.
Direct frozen dependencies: MaxEntropy.shannonEntropy, QubitNormalFormState.qubitMatrix and qubitState,
ActualPureQubitGeometry.densityBridge, blochMatrix and its Bloch geometry, and FiniteStateChannel.DensityState.
-/

import D5.S3.Entropy.MaxEntropy
import D5.S3.Quantum.Information.QubitNormalFormState
import D5.S3.Quantum.Information.ActualPureQubitGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.OrderScores.QubitJensenShannon

open Matrix Finset Set
open D5.S3.Entropy.MaxEntropy (shannonEntropy)
open D5.S3.Quantum.Information.ActualPureQubitCostInfimum
open D5.S3.Quantum.Information.QubitNormalFormState (qubitMatrix qubitState)
open D5.S3.Quantum.Foundation.FiniteStateChannel
open scoped MatrixOrder ComplexOrder

def outcomeSign (outcome : Bool) : ℝ := if outcome then 1 else -1

/-- The signed Pauli projector for the axis with components (k, 0, m). -/
def projector (m k : ℝ) (outcome : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  qubitMatrix (outcomeSign outcome * k) (outcomeSign outcome * m)

set_option maxHeartbeats 1000000 in
private theorem trace_record_ab (m k : ℝ) (hunit : m ^ 2 + k ^ 2 = 1)
    (r : EuclideanSpace ℝ (Fin 3)) (a b : Bool) :
    (Matrix.trace (blochMatrix 1 r * (projector m k a * projector m (-k) b * projector m k a))).re =
      (1 + outcomeSign a * outcomeSign b * (m ^ 2 - k ^ 2)) / 4 *
        (1 + outcomeSign a * (m * r 2 + k * r 0)) := by
  cases a <;> cases b <;>
    simp [projector, qubitMatrix, outcomeSign, blochMatrix, Matrix.trace,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;>
    first
    | linear_combination ((1 + (m * r 2 - k * r 0)) / 8) * hunit
    | linear_combination ((1 - (m * r 2 - k * r 0)) / 8) * hunit

private theorem trace_record_ba (m k : ℝ) (hunit : m ^ 2 + k ^ 2 = 1)
    (r : EuclideanSpace ℝ (Fin 3)) (a b : Bool) :
    (Matrix.trace (blochMatrix 1 r * (projector m (-k) b * projector m k a * projector m (-k) b))).re =
      (1 + outcomeSign a * outcomeSign b * (m ^ 2 - k ^ 2)) / 4 *
        (1 + outcomeSign b * (m * r 2 - k * r 0)) := by
  have h := trace_record_ab m (-k) (by simpa using hunit) r b a
  rw [neg_neg, neg_sq] at h
  rw [h]
  ring

def nativeMatrix (rho : DensityState (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  CStarMatrix.ofMatrix.symm rho.val

private theorem native_matrix_psd (rho : DensityState (Fin 2)) :
    (nativeMatrix rho).PosSemidef :=
  (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm rho.nonnegative).posSemidef

private theorem native_coordinates (rho : DensityState (Fin 2)) :
    ∃ r : EuclideanSpace ℝ (Fin 3), ‖r‖ ≤ 1 ∧ nativeMatrix rho = blochMatrix 1 r := by
  have hpsd := native_matrix_psd rho
  have htrace : Matrix.trace (nativeMatrix rho) = 1 := rho.trace_eq_one
  have hnorm := norm_bloch_le_trace_of_posSemidef _ hpsd
  have hmatrix := (bloch_geometry_of_isHermitian _ hpsd.isHermitian).1
  rw [htrace, Complex.one_re] at hnorm hmatrix
  exact ⟨bloch (nativeMatrix rho), hnorm, hmatrix⟩

private theorem planar_domain (x z : ℝ) :
    (∃ (rho : DensityState (Fin 2)) (r : EuclideanSpace ℝ (Fin 3)),
      ‖r‖ ≤ 1 ∧ nativeMatrix rho = blochMatrix 1 r ∧ r 0 = x ∧ r 2 = z) ↔
      x ^ 2 + z ^ 2 ≤ 1 := by
  constructor
  · rintro ⟨rho, r, hnorm, _, h0, h2⟩
    have hs := EuclideanSpace.real_norm_sq_eq r
    rw [Fin.sum_univ_three, h0, h2] at hs
    nlinarith [sq_nonneg (r 1), norm_nonneg r]
  · intro h
    let r : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![x, 0, z]
    have hsq : ‖r‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      simpa [r] using h
    have hr : ‖r‖ ≤ 1 := by nlinarith [norm_nonneg r]
    refine ⟨qubitState x z h, r, hr, ?_, rfl, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nativeMatrix, qubitState, qubitMatrix, blochMatrix, r]

def sOfT (t : ℝ) : ℝ := (1 - Real.sqrt (1 - 4 * t ^ 2)) / 2

theorem parameter_calibration {t : ℝ} (ht : t ∈ Set.Icc 0 (1 / 2 : ℝ)) :
    sOfT t ∈ Set.Icc 0 (1 / 2 : ℝ) ∧ sOfT t * (1 - sOfT t) = t ^ 2 := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hrad : 0 ≤ 1 - 4 * t ^ 2 := by nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
  have hsq := Real.sq_sqrt hrad
  have hr := Real.sqrt_nonneg (1 - 4 * t ^ 2)
  have hle : Real.sqrt (1 - 4 * t ^ 2) ≤ 1 := by nlinarith [sq_nonneg t]
  unfold sOfT
  exact ⟨⟨by linarith, by linarith⟩, by nlinarith⟩

/-- The record puts the outcome of the first measurement in its first coordinate. -/
def jointRecord (A B : Bool → Matrix (Fin 2) (Fin 2) ℂ) (rho : DensityState (Fin 2))
    (o : Bool × Bool) : ℝ :=
  (Matrix.trace (nativeMatrix rho * (A o.1 * B o.2 * A o.1))).re

/-- Jensen–Shannon score in bits for two measurement-labelled Lüders records. -/
def orderScore (A B : Bool → Matrix (Fin 2) (Fin 2) ℂ) (rho : DensityState (Fin 2)) : ℝ :=
  let p := jointRecord A B rho
  let q := fun o : Bool × Bool => jointRecord B A rho o.swap
  (shannonEntropy (fun o => (p o + q o) / 2) - (shannonEntropy p + shannonEntropy q) / 2) / Real.log 2

/-- Wu's four-outcome Jensen–Shannon order score in bits for the canonical acute qubit pair. -/
def sourceScore (t : ℝ) (rho : DensityState (Fin 2)) : ℝ :=
  let s := sOfT t
  let m := Real.sqrt (1 - s)
  let k := Real.sqrt s
  orderScore (projector m k) (projector m (-k)) rho

/-- The optimized score. Its supremum is attained throughout the closed interval. -/
def psi (t : ℝ) : ℝ := sSup (Set.range (sourceScore t))

private def biasEntropy (y : ℝ) : ℝ := Real.binEntropy ((1 + y) / 2)
private def deficit (y : ℝ) : ℝ := Real.log 2 - biasEntropy y

private theorem bias_entropy_neg (y : ℝ) : biasEntropy (-y) = biasEntropy y := by
  unfold biasEntropy
  rw [show (1 + -y) / 2 = 1 - (1 + y) / 2 by ring, Real.binEntropy_one_sub]

private theorem pair_entropy (m y : ℝ) :
    Real.negMulLog (m * ((1 + y) / 2)) + Real.negMulLog (m * ((1 - y) / 2)) =
      Real.negMulLog m + m * biasEntropy y := by
  rw [Real.negMulLog_mul, Real.negMulLog_mul, biasEntropy,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1 - (1 + y) / 2 = (1 - y) / 2 by ring]
  ring

private def parityLaw (s y z : ℝ) (o : Bool × Bool) : ℝ :=
  if o.1 = o.2 then (1 - s) * ((1 + outcomeSign o.1 * y) / 2)
  else s * ((1 + outcomeSign o.1 * z) / 2)

private theorem parity_entropy (s y z : ℝ) :
    shannonEntropy (parityLaw s y z) =
      Real.negMulLog (1 - s) + (1 - s) * biasEntropy y +
      (Real.negMulLog s + s * biasEntropy z) := by
  simp only [shannonEntropy, Fintype.sum_prod_type, Fintype.sum_bool, parityLaw,
    Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, outcomeSign, one_mul,
    neg_one_mul, ← sub_eq_add_neg]
  rw [← pair_entropy (1 - s) y, ← pair_entropy s z]
  ring

private def reducedNats (s u v : ℝ) : ℝ :=
  (deficit (u + v) + deficit (u - v)) / 2 - (1 - s) * deficit u - s * deficit v

private theorem parity_js (s u v : ℝ) :
    shannonEntropy (fun o => (parityLaw s (u + v) (u + v) o +
      parityLaw s (u - v) (-(u - v)) o) / 2) -
    (shannonEntropy (parityLaw s (u + v) (u + v)) +
      shannonEntropy (parityLaw s (u - v) (-(u - v)))) / 2 =
      reducedNats s u v := by
  have hm : (fun o => (parityLaw s (u + v) (u + v) o +
      parityLaw s (u - v) (-(u - v)) o) / 2) = parityLaw s u v := by
    funext o
    unfold parityLaw
    split <;> ring
  rw [hm, parity_entropy, parity_entropy, parity_entropy, bias_entropy_neg]
  unfold reducedNats deficit
  ring

def disk : Set (ℝ × ℝ) := {d | d.1 ^ 2 + d.2 ^ 2 ≤ 1}

def diskScore (s : ℝ) (d : ℝ × ℝ) : ℝ :=
  reducedNats s (Real.sqrt (1 - s) * d.2) (Real.sqrt s * d.1) / Real.log 2

private theorem disk_compact : IsCompact disk := by
  have hc : IsCompact (Set.Icc ((-1 : ℝ), (-1 : ℝ)) (1, 1)) := isCompact_Icc
  refine hc.of_isClosed_subset (isClosed_le (by fun_prop) continuous_const) ?_
  rintro ⟨x,z⟩ hd
  change x ^ 2 + z ^ 2 ≤ 1 at hd
  exact ⟨⟨by nlinarith [sq_nonneg z], by nlinarith [sq_nonneg x]⟩,
    ⟨by nlinarith [sq_nonneg z], by nlinarith [sq_nonneg x]⟩⟩

private theorem disk_score_continuous (s : ℝ) : Continuous (diskScore s) := by
  unfold diskScore reducedNats deficit biasEntropy
  fun_prop

private theorem native_score_on_coordinates {t : ℝ} (ht : t ∈ Icc 0 (1 / 2 : ℝ))
    {rho : DensityState (Fin 2)} {r : EuclideanSpace ℝ (Fin 3)}
    (hr : nativeMatrix rho = blochMatrix 1 r) :
    sourceScore t rho = diskScore (sOfT t) (r 0, r 2) := by
  let s := sOfT t
  let m := Real.sqrt (1 - s)
  let k := Real.sqrt s
  let u := m * r 2
  let v := k * r 0
  have hs := (parameter_calibration ht).1
  have hm : m ^ 2 = 1 - s := Real.sq_sqrt (by have := hs.2; dsimp [s] at *; linarith)
  have hk : k ^ 2 = s := Real.sq_sqrt hs.1
  have hunit : m ^ 2 + k ^ 2 = 1 := by rw [hm, hk]; ring
  have hp (o : Bool × Bool) :
      (Matrix.trace (nativeMatrix rho * (projector m k o.1 * projector m (-k) o.2 *
        projector m k o.1))).re = parityLaw s (u + v) (u + v) o := by
    rw [hr, trace_record_ab m k hunit, hm, hk]
    rcases o with ⟨a,b⟩
    cases a <;> cases b <;> simp [parityLaw, outcomeSign, u, v] <;> ring
  have hq (o : Bool × Bool) :
      (Matrix.trace (nativeMatrix rho * (projector m (-k) o.2 * projector m k o.1 *
        projector m (-k) o.2))).re = parityLaw s (u - v) (-(u - v)) o := by
    rw [hr, trace_record_ba m k hunit, hm, hk]
    rcases o with ⟨a,b⟩
    cases a <;> cases b <;> simp [parityLaw, outcomeSign, u, v] <;> ring
  let p : Bool × Bool → ℝ := fun o =>
    (Matrix.trace (nativeMatrix rho *
      (projector m k o.1 * projector m (-k) o.2 * projector m k o.1))).re
  let q : Bool × Bool → ℝ := fun o =>
    (Matrix.trace (nativeMatrix rho *
      (projector m (-k) o.2 * projector m k o.1 * projector m (-k) o.2))).re
  have hp' : p = parityLaw s (u + v) (u + v) := funext hp
  have hq' : q = parityLaw s (u - v) (-(u - v)) := funext hq
  let js (p q : Bool × Bool → ℝ) :=
    (shannonEntropy (fun o => (p o + q o) / 2) - (shannonEntropy p + shannonEntropy q) / 2) / Real.log 2
  change js p q = reducedNats s u v / Real.log 2
  rw [hp', hq']
  exact congrArg (fun x : ℝ => x / Real.log 2) (parity_js s u v)

private theorem native_score_range {t : ℝ} (ht : t ∈ Icc 0 (1 / 2 : ℝ)) :
    Set.range (sourceScore t) = diskScore (sOfT t) '' disk := by
  ext score
  constructor
  · rintro ⟨rho, rfl⟩
    obtain ⟨r, hnorm, hr⟩ := native_coordinates rho
    exact ⟨(r 0, r 2), (planar_domain _ _).mp ⟨rho, r, hnorm, hr, rfl, rfl⟩,
      (native_score_on_coordinates ht hr).symm⟩
  · rintro ⟨⟨x,z⟩, hd, rfl⟩
    obtain ⟨rho, r, _, hr, h0, h2⟩ := (planar_domain x z).mpr hd
    exact ⟨rho, by rw [native_score_on_coordinates ht hr, h0, h2]⟩

theorem native_maximum {t : ℝ} (ht : t ∈ Icc 0 (1 / 2 : ℝ)) :
    ∃ d ∈ disk, ∃ rho : DensityState (Fin 2),
      sourceScore t rho = psi t ∧ diskScore (sOfT t) d = psi t ∧
      (∀ x ∈ disk, diskScore (sOfT t) x ≤ psi t) ∧
      (∀ rho' : DensityState (Fin 2), sourceScore t rho' ≤ psi t) := by
  obtain ⟨d, hd, hmax⟩ := disk_compact.exists_isMaxOn
    (show disk.Nonempty from ⟨(0,0), by norm_num [disk]⟩) (disk_score_continuous _).continuousOn
  have himage : IsGreatest (diskScore (sOfT t) '' disk) (diskScore (sOfT t) d) := by
    refine ⟨mem_image_of_mem _ hd, ?_⟩
    rintro _ ⟨d', hd', rfl⟩
    exact hmax hd'
  have hn : IsGreatest (Set.range (sourceScore t)) (diskScore (sOfT t) d) := by
    rwa [native_score_range ht]
  have he := hn.csSup_eq
  change psi t = _ at he
  obtain ⟨rho, hrho⟩ := hn.1
  exact ⟨d, hd, rho, hrho.trans he.symm, he.symm,
    fun d' hd' => (hmax hd').trans_eq he.symm,
    fun rho' => (hn.2 (mem_range_self rho')).trans_eq he.symm⟩

def circlePoint (w : ℝ) : ℝ × ℝ := (Real.sqrt w, Real.sqrt (1 - w))

/-! The entropy deficit has a uniformly convergent series on the closed bias interval. -/

def seriesWeight (n : ℕ) : ℝ := 1 / ((2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1))
private def biasTerm (n : ℕ) (x : ℝ) : ℝ := seriesWeight n * x ^ (2 * n + 2)

theorem series_weight_pos (n : ℕ) : 0 < seriesWeight n := by
  unfold seriesWeight
  positivity

private theorem summable_series_weight : Summable seriesWeight := by
  have h : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff 1).2
      (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ)))
  refine h.of_nonneg_of_le (fun n => (series_weight_pos n).le) (fun n => ?_)
  unfold seriesWeight
  apply one_div_le_one_div_of_le (by positivity)
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg (n : ℝ)]

private theorem bias_term_bound (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    ‖biasTerm n x‖ ≤ seriesWeight n := by
  rw [Real.norm_eq_abs, biasTerm, abs_mul, abs_of_pos (series_weight_pos n), ← pow_abs]
  exact mul_le_of_le_one_right (series_weight_pos n).le (pow_le_one₀ (abs_nonneg _) hx)

private theorem bias_series_open {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => biasTerm n x) (deficit x) := by
  have hsq : |x ^ 2| < 1 := by
    rw [← pow_abs]
    nlinarith [mul_pos (sub_pos.mpr hx) (show 0 < 1 + |x| by positivity)]
  have hplus : 1 + x ≠ 0 := by linarith [(abs_lt.mp hx).1]
  have hminus : 1 - x ≠ 0 := by linarith [(abs_lt.mp hx).2]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have ha := (Real.hasSum_log_sub_log_of_abs_lt_one hx).mul_left (x / 2)
  have hb := (Real.hasSum_pow_div_log_of_abs_lt_one hsq).mul_left (1 / 2 : ℝ)
  convert ha.sub hb using 1
  · funext n
    dsimp only [biasTerm, seriesWeight]
    rw [← pow_mul, show 2 * (n + 1) = 2 * n + 2 by omega, pow_succ x (2 * n + 1)]
    have h1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h3 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    ring
  · unfold deficit biasEntropy
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
      show 1 - (1 + x) / 2 = (1 - x) / 2 by ring,
      show 1 - x ^ 2 = (1 + x) * (1 - x) by ring,
      Real.log_mul hplus hminus, Real.negMulLog, Real.negMulLog,
      Real.log_div hplus htwo, Real.log_div hminus htwo]
    ring

private theorem bias_series {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n => biasTerm n x) (deficit x) := by
  let F (y : ℝ) := ∑' n, biasTerm n y
  have hcont : ContinuousOn F (Icc (-1 : ℝ) 1) :=
    continuousOn_tsum (fun n => by
      apply Continuous.continuousOn
      unfold biasTerm
      fun_prop) summable_series_weight
      (fun n _ hy => bias_term_bound n (abs_le.mpr hy))
  have hdef : Continuous deficit := by unfold deficit biasEntropy; fun_prop
  have hclosure : closure (Ioo (-1 : ℝ) 1) = Icc (-1 : ℝ) 1 :=
    closure_Ioo (by norm_num)
  have he : EqOn F deficit (Ioo (-1 : ℝ) 1) :=
    fun _ hy => (bias_series_open (abs_lt.mpr hy)).tsum_eq
  have hx' : x ∈ closure (Ioo (-1 : ℝ) 1) := hclosure ▸ hx
  have hc : IsClosed {y ∈ Icc (-1 : ℝ) 1 | F y = deficit y} :=
    isClosed_Icc.isClosed_eq hcont hdef.continuousOn
  have hclosed : closure (Ioo (-1 : ℝ) 1) ⊆ {y ∈ Icc (-1 : ℝ) 1 | F y = deficit y} :=
    closure_minimal (fun _ hy => ⟨Ioo_subset_Icc_self hy, he hy⟩) hc
  have hsum : Summable (fun n => biasTerm n x) :=
    .of_norm_bounded summable_series_weight (fun n => bias_term_bound n (abs_le.mpr hx))
  rw [← (hclosed hx').2]
  exact hsum.hasSum

def coeff (n : ℕ) (s u v : ℝ) : ℝ :=
  ((u + v) ^ (2 * n + 2) + (u - v) ^ (2 * n + 2)) / 2 -
    (1 - s) * u ^ (2 * n + 2) - s * v ^ (2 * n + 2)

private theorem reduced_series (s u v : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1)
    (hp : u + v ∈ Icc (-1 : ℝ) 1) (hm : u - v ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n => seriesWeight n * coeff n s u v) (reducedNats s u v) := by
  have h := (((bias_series hp).add (bias_series hm)).mul_right (1 / 2)).sub
    ((bias_series hu).mul_left (1 - s)) |>.sub ((bias_series hv).mul_left s)
  convert h using 1
  · funext n
    unfold biasTerm coeff
    ring
  · unfold reducedNats
    ring

theorem coeff_zero (s u v : ℝ) :
    coeff 0 s u v = s * u ^ 2 + (1 - s) * v ^ 2 := by
  norm_num [coeff]
  ring

private theorem unit_biases {s : ℝ} (hs : s ∈ Set.Icc 0 1) {x z : ℝ} (hd : x ^ 2 + z ^ 2 ≤ 1) :
    let u := Real.sqrt (1 - s) * z
    let v := Real.sqrt s * x
    u ∈ Set.Icc (-1 : ℝ) 1 ∧ v ∈ Set.Icc (-1 : ℝ) 1 ∧
      u + v ∈ Set.Icc (-1 : ℝ) 1 ∧ u - v ∈ Set.Icc (-1 : ℝ) 1 := by
  dsimp
  let m := Real.sqrt (1-s)
  let k := Real.sqrt s
  have hm : m ^ 2 = 1 - s := Real.sq_sqrt (sub_nonneg.mpr hs.2)
  have hk : k ^ 2 = s := Real.sq_sqrt hs.1
  have hu : (m*z) ^ 2 ≤ 1 := by
    rw [mul_pow, hm]
    nlinarith [mul_nonneg hs.1 (sq_nonneg z), sq_nonneg x]
  have hv : (k*x) ^ 2 ≤ 1 := by
    rw [mul_pow, hk]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sq_nonneg x), sq_nonneg z]
  have habs (y : ℝ) (hy : y ^ 2 ≤ 1) : y ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith
  have hp : (m*z+k*x)^2 ≤ 1 := by
    nlinarith only [hd, sq_nonneg (m*x-k*z), show (m*z+k*x)^2 + (m*x-k*z)^2 = x^2+z^2 by
      calc
        _ = (m^2+k^2)*(x^2+z^2) := by ring
        _ = _ := by rw [hm, hk]; ring]
  have hn : (m*z-k*x)^2 ≤ 1 := by
    nlinarith only [hd, sq_nonneg (m*x+k*z), show (m*z-k*x)^2 + (m*x+k*z)^2 = x^2+z^2 by
      calc
        _ = (m^2+k^2)*(x^2+z^2) := by ring
        _ = _ := by rw [hm, hk]; ring]
  exact ⟨habs _ hu, habs _ hv, habs _ hp, habs _ hn⟩

def diskCoeff (n : ℕ) (s : ℝ) (d : ℝ × ℝ) : ℝ :=
  coeff n s (Real.sqrt (1 - s) * d.2) (Real.sqrt s * d.1)

theorem disk_series {s : ℝ} (hs : s ∈ Set.Icc 0 1) {d : ℝ × ℝ} (hd : d ∈ disk) :
    HasSum (fun n => seriesWeight n * diskCoeff n s d) (diskScore s d * Real.log 2) := by
  obtain ⟨hu, hv, hp, hm⟩ := unit_biases hs hd
  rw [diskScore, div_mul_cancel₀ _ (Real.log_pos (by norm_num)).ne']
  exact reduced_series _ _ _ hu hv hp hm


theorem disk_score_le_of_coeff_le {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    {d e : ℝ × ℝ} (hd : d ∈ disk) (he : e ∈ disk)
    (hc : ∀ n, diskCoeff n s d ≤ diskCoeff n t e) :
    diskScore s d ≤ diskScore t e := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h₁ := disk_series hs hd
  have h₂ := disk_series ht he
  have h := h₁.summable.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_left (hc n) (series_weight_pos n).le) h₂.summable
  rw [h₁.tsum_eq, h₂.tsum_eq] at h
  exact le_of_mul_le_mul_right h hlog

end D5.S3.Quantum.Measurement.OrderScores.QubitJensenShannon
