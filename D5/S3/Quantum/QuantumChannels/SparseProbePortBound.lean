/- GID: D5/S3/Quantum/QuantumChannels/SparseProbePortBound
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/SparseProbePortBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sparse survival measurements bound every finite classical-quantum compression port. -/

import D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity
import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Foundation.FiniteDiamondDistance
import D5.S3.TotalVariation.Pinsker

noncomputable section
open Matrix Complex
open scoped ComplexConjugate BigOperators ComplexOrder MatrixOrder
namespace D5.S3.Quantum.QuantumChannels.SparseProbePortBound
open D5.S3.Quantum.QuantumChannels.SparseProbeCoercivity
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteDiamondDistance
open D5.S3.TotalVariation.Pinsker

variable {d q : ℕ} {F : Type*} [Fintype F]
  {a b : F → Type*} [∀ f, Fintype (a f)] [∀ f, Fintype (b f)]

/-- An actual finite classical-quantum port. The encoder produces a classical flag and
a q-dimensional quantum block; each fixed flag decoder is a whole-block channel.
There is no setting argument, quantum bypass, or restriction on flag probabilities. -/
structure Port (d q : ℕ) (F : Type*) [Fintype F]
    (a b : F → Type*) [∀ f, Fintype (a f)] [∀ f, Fintype (b f)] where
  encode : (f : F) → a f → Matrix (Fin q) (Fin d) ℂ
  decode : (f : F) → b f → Matrix (Fin d) (Fin q) ℂ
  encode_tp : (∑ f, ∑ i, (encode f i)ᴴ * encode f i) = 1
  decode_tp : ∀ f, (∑ j, (decode f j)ᴴ * decode f j) = 1

/-- All actual composite Kraus branches, including the classical flag. -/
def Port.kraus (P : Port d q F a b) (x : Σ f, a f × b f) :
    Matrix (Fin d) (Fin d) ℂ := P.decode x.1 x.2.2 * P.encode x.1 x.2.1

private theorem Port.complete (P : Port d q F a b) :
    (∑ x, (P.kraus x)ᴴ * P.kraus x) = 1 := by
  classical
  simp only [Port.kraus, Fintype.sum_sigma, Fintype.sum_prod_type, conjTranspose_mul]
  have h (f : F) (i : a f) :
      (∑ j, ((P.encode f i)ᴴ * (P.decode f j)ᴴ) *
        (P.decode f j * P.encode f i)) = (P.encode f i)ᴴ * P.encode f i := by
    calc
      _ = (P.encode f i)ᴴ * ((∑ j, (P.decode f j)ᴴ * P.decode f j) *
          P.encode f i) := by
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
      _ = _ := by rw [P.decode_tp, Matrix.one_mul]
  simp only [h]
  exact P.encode_tp

/-- The port composite in the existing all-amplification completely positive interface. -/
def Port.channel (P : Port d q F a b) : QuantumChannel (Fin d) (Fin d) :=
  Classical.choose (finite_kraus_quantum_channel P.kraus P.complete)

private theorem Port.action (P : Port d q F a b) (X : Matrix (Fin d) (Fin d) ℂ) :
    CStarMatrix.ofMatrix.symm
      (P.channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      ∑ x, P.kraus x * X * (P.kraus x)ᴴ :=
  Classical.choose_spec (finite_kraus_quantum_channel P.kraus P.complete) X

private theorem hs_trace (C : Matrix (Fin d) (Fin d) ℂ) :
    hsSq C = (trace (Cᴴ*C)).re := by
  simp only [hsSq, trace, diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

private theorem Port.hs_total (P : Port d q F a b) :
    (∑ x, hsSq (P.kraus x)) = d := by
  simp only [hs_trace]
  rw [← Complex.re_sum, ← trace_sum, P.complete]
  simp

private theorem Port.trace_total (P : Port d q F a b) :
    (∑ x, normSq (trace (P.kraus x))) ≤ q*d := by
  calc
    _ ≤ ∑ x, (q:ℝ) * hsSq (P.kraus x) := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [conjTranspose_conjTranspose, hsSq, Port.kraus] using
        D5.S3.Quantum.QuantumChannels.TomiyamaDiagonalKPositivity.trace_rank_bound
          q d (P.decode x.1 x.2.2)ᴴ (P.encode x.1 x.2.1)
    _ = _ := by rw [← Finset.mul_sum, P.hs_total]

private theorem Port.loss_lower (P : Port d q F a b)
    (v : Fin d → ℂ) (hd : 0 < d) (hv : ∑ i, normSq (v i) = 1)
    (μ : ℝ) (hμ : 0 < μ) (hfull : ∀ i, μ ≤ normSq (v i)) :
    μ/(2+μ) * (d-q) ≤ ∑ x, probeLoss (P.kraus x) v := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have ht : (∑ x, normSq (trace (P.kraus x))) / d ≤ q := by
    apply (div_le_iff₀ hd').mpr
    exact P.trace_total
  calc
    _ ≤ μ/(2+μ) * ((d:ℝ) - (∑ x, normSq (trace (P.kraus x)))/d) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      positivity
    _ = ∑ x, μ/(2+μ) * (hsSq (P.kraus x) - normSq (trace (P.kraus x))/d) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, P.hs_total]
    _ ≤ _ := Finset.sum_le_sum fun x _ =>
      sparse_probe_coercivity (P.kraus x) v hd hv μ hμ hfull

/-- Born probabilities of the complete projective readout after a fixed unitary. -/
def probabilities (U : Matrix (Fin d) (Fin d) ℂ) (ρ : DensityState (Fin d)) :
    Fin d → ℝ := fun i =>
  (U * CStarMatrix.ofMatrix.symm ρ.1 * Uᴴ) i i |>.re

/-- Worst density-input error for the coordinate setting and one fixed second setting. -/
def twoSettingError (U : Matrix (Fin d) (Fin d) ℂ)
    (T : QuantumChannel (Fin d) (Fin d)) : ℝ :=
  sSup (Set.range fun ρ : DensityState (Fin d) =>
    max (totalVariation (probabilities 1 ρ) (probabilities 1 (T.mapState ρ)))
      (totalVariation (probabilities U ρ) (probabilities U (T.mapState ρ))))

private theorem probabilities_nonneg (U : Matrix (Fin d) (Fin d) ℂ)
    (ρ : DensityState (Fin d)) (i : Fin d) : 0 ≤ probabilities U ρ i := by
  have hp : (CStarMatrix.ofMatrix.symm ρ.1).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (map_nonneg CStarMatrix.ofMatrixStarAlgEquiv.symm ρ.2.1)
  exact (Complex.nonneg_iff.mp ((hp.mul_mul_conjTranspose_same U).diag_nonneg)).1

private theorem probabilities_sum (U : Matrix (Fin d) (Fin d) ℂ)
    (hU : Uᴴ*U=1) (ρ : DensityState (Fin d)) : ∑ i, probabilities U ρ i = 1 := by
  change (∑ i, ((U * CStarMatrix.ofMatrix.symm ρ.1 * Uᴴ) i i).re) = 1
  rw [← Complex.re_sum]
  change (trace (U * CStarMatrix.ofMatrix.symm ρ.1 * Uᴴ)).re = 1
  rw [trace_mul_cycle, hU, Matrix.one_mul]
  exact congrArg Complex.re ρ.2.2

private theorem tv_bounds (p r : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hr : ∀ i, 0 ≤ r i) (hpsum : ∑ i, p i=1) (hrsum : ∑ i, r i=1) :
    0 ≤ totalVariation p r ∧ totalVariation p r ≤ 1 := by
  constructor
  · unfold totalVariation; positivity
  · have h : (∑ i, |p i-r i|) ≤ 2 := by
      calc
        _ ≤ ∑ i, (p i+r i) := Finset.sum_le_sum fun i _ =>
          (abs_sub (p i) (r i)).trans_eq (by rw [abs_of_nonneg (hp i), abs_of_nonneg (hr i)])
        _ = 2 := by rw [Finset.sum_add_distrib, hpsum, hrsum]; norm_num
    unfold totalVariation
    linarith

private theorem deterministic_event_le_tv (p r : Fin d → ℝ)
    (hpsum : ∑ i, p i=1) (hrsum : ∑ i, r i=1) (i : Fin d) (hi : p i=1) :
    1-r i ≤ totalVariation p r := by
  classical
  by_cases h : r i ≤ p i
  · rw [total_variation_eq_sum_positive p r (hpsum.trans hrsum.symm)]
    have hm : i ∈ Finset.univ.filter (fun j => r j ≤ p j) := by simp [h]
    have hs := Finset.single_le_sum (fun j hj =>
      sub_nonneg.mpr (Finset.mem_filter.mp hj).2) hm
    simpa only [hi] using hs
  · have hn : 0 ≤ totalVariation p r := by unfold totalVariation; positivity
    have : 1-r i ≤ 0 := by rw [hi] at h; linarith
    exact this.trans hn

private theorem error_dominates (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (T : QuantumChannel (Fin d) (Fin d)) (ρ : DensityState (Fin d)) :
    totalVariation (probabilities 1 ρ) (probabilities 1 (T.mapState ρ)) ≤
        twoSettingError U T ∧
    totalVariation (probabilities U ρ) (probabilities U (T.mapState ρ)) ≤
        twoSettingError U T := by
  have hb : BddAbove (Set.range fun ρ : DensityState (Fin d) =>
      max (totalVariation (probabilities 1 ρ) (probabilities 1 (T.mapState ρ)))
        (totalVariation (probabilities U ρ) (probabilities U (T.mapState ρ)))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨σ, rfl⟩
    apply max_le
    · exact (tv_bounds _ _ (probabilities_nonneg 1 σ) (probabilities_nonneg 1 _)
        (probabilities_sum 1 (by simp) σ) (probabilities_sum 1 (by simp) _)).2
    · exact (tv_bounds _ _ (probabilities_nonneg U σ) (probabilities_nonneg U _)
        (probabilities_sum U hU σ) (probabilities_sum U hU _)).2
  have hm := le_csSup hb (Set.mem_range_self ρ)
  exact ⟨(le_max_left _ _).trans hm, (le_max_right _ _).trans hm⟩

private def unitState (v : Fin d → ℂ) (hv : ∑ i, normSq (v i)=1) :
    DensityState (Fin d) := pureState v (by
  change (∑ i, conj (v i) * v i) = 1
  simp only [← normSq_eq_conj_mul_self, ← Complex.ofReal_sum, hv, Complex.ofReal_one])

private theorem pure_action (C : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    C * vecMulVec v (star v) * Cᴴ = vecMulVec (C.mulVec v) (star (C.mulVec v)) := by
  rw [mul_vecMulVec, vecMulVec_mul, vecMul_conjTranspose, star_star]

private theorem Port.vector_total (P : Port d q F a b) (v : Fin d → ℂ)
    (hv : ∑ i, normSq (v i)=1) :
    (∑ x, ∑ i, normSq ((P.kraus x).mulVec v i)) = 1 := by
  have he (C : Matrix (Fin d) (Fin d) ℂ) :
      ((star v ⬝ᵥ ((Cᴴ*C).mulVec v))).re = ∑ i, normSq (C.mulVec v i) := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star]
    simp only [dotProduct, Pi.star_apply, Complex.star_def, ← normSq_eq_conj_mul_self,
      Complex.re_sum, Complex.ofReal_re]
  rw [← Finset.sum_congr rfl (fun x _ => he (P.kraus x))]
  rw [← Complex.re_sum]
  have hs : (∑ x, star v ⬝ᵥ (((P.kraus x)ᴴ * P.kraus x).mulVec v)) =
      star v ⬝ᵥ ((∑ x, (P.kraus x)ᴴ * P.kraus x).mulVec v) := by
    simp only [Matrix.sum_mulVec, dotProduct_sum]
  rw [hs, P.complete, one_mulVec]
  simpa only [dotProduct, Pi.star_apply, Complex.star_def, ← normSq_eq_conj_mul_self,
    Complex.re_sum, Complex.ofReal_re] using hv

private theorem Port.pure_prob (P : Port d q F a b)
    (U : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ)
    (hv : ∑ i, normSq (v i)=1) (r : Fin d) :
    probabilities U (P.channel.mapState (unitState v hv)) r =
      ∑ x, normSq ((U * P.kraus x).mulVec v r) := by
  unfold probabilities
  change ((U * CStarMatrix.ofMatrix.symm
      (P.channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix (vecMulVec v (star v)))) * Uᴴ) r r).re = _
  rw [P.action, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x _
  have he : U * (P.kraus x * vecMulVec v (star v) * (P.kraus x)ᴴ) * Uᴴ =
      (U*P.kraus x) * vecMulVec v (star v) * (U*P.kraus x)ᴴ := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [he, pure_action]
  simp only [vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re]

private theorem pure_input_prob (U : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) (hv : ∑ i, normSq (v i)=1) (r : Fin d) :
    probabilities U (unitState v hv) r = normSq (U.mulVec v r) := by
  change ((U * CStarMatrix.ofMatrix.symm
    (CStarMatrix.ofMatrix (vecMulVec v (star v))) * Uᴴ) r r).re = _
  rw [CStarMatrix.ofMatrix.symm_apply_apply, pure_action]
  simp [vecMulVec_apply, Complex.mul_conj]

private theorem Port.loss_upper (P : Port d q F a b)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (v : Fin d → ℂ) (hv : ∑ i, normSq (v i)=1)
    (r : Fin d) (hrow : ∀ i, U r i = conj (v i)) :
    (∑ x, probeLoss (P.kraus x) v) ≤ (d+1:ℝ) * twoSettingError U P.channel := by
  classical
  let e := twoSettingError U P.channel
  have hb (i : Fin d) : 1-(∑ x, normSq (P.kraus x i i)) ≤ e := by
    let w : Fin d → ℂ := Pi.single i 1
    have hw : ∑ j, normSq (w j)=1 := by simp [w, Pi.single_apply]
    have ht := (error_dominates U hU P.channel (unitState w hw)).1
    have he := deterministic_event_le_tv
      (probabilities 1 (unitState w hw))
      (probabilities 1 (P.channel.mapState (unitState w hw)))
      (probabilities_sum 1 (by simp) _) (probabilities_sum 1 (by simp) _) i
      (by rw [pure_input_prob]; simp [w, Pi.single_apply])
    rw [P.pure_prob] at he
    simp only [one_mul, w, Matrix.mulVec_single_one, Matrix.col_apply] at he
    exact he.trans ht
  have hvdot : (∑ i, conj (v i)*v i) = 1 := by
    simp only [← normSq_eq_conj_mul_self, ← Complex.ofReal_sum, hv, Complex.ofReal_one]
  have hUv (C : Matrix (Fin d) (Fin d) ℂ) :
      (U*C).mulVec v r = ∑ i, conj (v i) * C.mulVec v i := by
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct, hrow]
  have hvtest : 1-(∑ x, normSq (∑ i, conj (v i)* (P.kraus x).mulVec v i)) ≤ e := by
    have ht := (error_dominates U hU P.channel (unitState v hv)).2
    have he := deterministic_event_le_tv
      (probabilities U (unitState v hv))
      (probabilities U (P.channel.mapState (unitState v hv)))
      (probabilities_sum U hU _) (probabilities_sum U hU _) r (by
        rw [pure_input_prob]
        have : U.mulVec v r=1 := by simp only [Matrix.mulVec, dotProduct, hrow, hvdot]
        rw [this, normSq_one])
    rw [P.pure_prob] at he
    simp only [hUv] at he
    exact he.trans ht
  have hoff : (∑ x, offSq (P.kraus x)) = ∑ i, (1-∑ x, normSq (P.kraus x i i)) := by
    have hx (x : Σ f, a f × b f) :
        offSq (P.kraus x) = hsSq (P.kraus x) - ∑ i, normSq (P.kraus x i i) := by
      have := SparseProbeCoercivity.hs_split (P.kraus x)
      linarith
    simp only [hx, Finset.sum_sub_distrib, P.hs_total]
    rw [Finset.sum_comm]
    simp
  have hsurv : (∑ x, survivalLoss (P.kraus x) v) =
      1-(∑ x, normSq (∑ i, conj (v i)* (P.kraus x).mulVec v i)) := by
    unfold survivalLoss
    rw [Finset.sum_sub_distrib, P.vector_total v hv]
  have hsum : (∑ i, (1-∑ x, normSq (P.kraus x i i))) ≤ d*e := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)
    simpa using this
  simp only [probeLoss, Finset.sum_add_distrib, hoff, hsurv]
  change _ ≤ (d+1:ℝ)*e
  linarith

/-- The set of attainable two-setting errors, allowing every finite flag and Kraus family. -/
def portErrors (d q : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {e | ∃ (F : Type) (_ : Fintype F) (a b : F → Type)
    (_ : ∀ f, Fintype (a f)) (_ : ∀ f, Fintype (b f)) (P : Port d q F a b),
      e = twoSettingError U P.channel}

/-- The quantitative chain for one actual port, with all flags already aggregated. -/
structure PortEstimate (P : Port d q F a b) (U : Matrix (Fin d) (Fin d) ℂ)
    (v : Fin d → ℂ) (μ : ℝ) : Prop where
  rankBound : ∀ x, Matrix.rank (P.kraus x) ≤ q
  hsTotal : (∑ x, hsSq (P.kraus x)) = d
  traceBound : (∑ x, normSq (trace (P.kraus x))) ≤ q*d
  lossLower : μ/(2+μ)*(d-q) ≤ ∑ x, probeLoss (P.kraus x) v
  lossUpper : (∑ x, probeLoss (P.kraus x) v) ≤ (d+1:ℝ)*twoSettingError U P.channel
  errorLower : μ*(d-q)/((2+μ)*(d+1)) ≤ twoSettingError U P.channel

private def classicalPort (d q : ℕ) (hq : 0 < q) :
    Port d q (Fin d) (fun _ => Unit) (fun _ => Fin q) where
  encode f _ := Matrix.single ⟨0, hq⟩ f 1
  decode f j := Matrix.single f j 1
  encode_tp := by
    classical
    simp only [Finset.univ_unique, Finset.sum_singleton, conjTranspose_single,
      star_one, single_mul_single_same, one_mul]
    exact Matrix.sum_single_one
  decode_tp f := by
    classical
    simp only [conjTranspose_single, star_one, single_mul_single_same, one_mul]
    exact Matrix.sum_single_one

private def identityPort (d : ℕ) : Port d d Unit (fun _ => Unit) (fun _ => Unit) where
  encode _ _ := 1
  decode _ _ := 1
  encode_tp := by simp
  decode_tp _ := by simp

private theorem identity_error (d : ℕ) (U : Matrix (Fin d) (Fin d) ℂ) (hd : 0 < d) :
    twoSettingError U (identityPort d).channel = 0 := by
  have hi (ρ : DensityState (Fin d)) : (identityPort d).channel.mapState ρ = ρ := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    change CStarMatrix.ofMatrix.symm
      ((identityPort d).channel.toCompletelyPositiveMap ρ.1) = _
    rw [← CStarMatrix.ofMatrix.apply_symm_apply ρ.1, Port.action]
    simp [identityPort, Port.kraus, Fintype.sum_sigma]
  have hn : Nonempty (DensityState (Fin d)) := by
    let i : Fin d := ⟨0, hd⟩
    exact ⟨unitState (Pi.single i 1) (by simp [Pi.single_apply])⟩
  unfold twoSettingError
  simp only [hi, totalVariation, sub_self, abs_zero, Finset.sum_const_zero, mul_zero,
    max_self]
  simp [Set.range_const]

private theorem Port.operational_lower (P : Port d q F a b)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (v : Fin d → ℂ) (hd : 0 < d) (hv : ∑ i, normSq (v i)=1)
    (r : Fin d) (hrow : ∀ i, U r i = conj (v i))
    (μ : ℝ) (hμ : 0 < μ) (hfull : ∀ i, μ ≤ normSq (v i)) :
    μ * (d-q) / ((2+μ)*(d+1)) ≤ twoSettingError U P.channel := by
  have hl := P.loss_lower v hd hv μ hμ hfull
  have hu := P.loss_upper U hU v hv r hrow
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have h : μ/(2+μ)*(d-q) ≤ (d+1:ℝ)*twoSettingError U P.channel := hl.trans hu
  apply (div_le_iff₀ (by positivity : 0 < (2+μ)*(d+1:ℝ))).mpr
  have := (div_le_iff₀ (by linarith : 0 < 2+μ)).mp
    (show μ*(d-q)/(2+μ) ≤ (d+1:ℝ)*twoSettingError U P.channel by
      simpa only [div_mul_eq_mul_div] using h)
  nlinarith

/-- Uniform operational obstruction for every finite complex classical-quantum port.
The infimum is non-strict, and a d-dimensional identity port attains zero error. -/
theorem sparse_probe_port_bound (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : Uᴴ*U=1)
    (v : Fin d → ℂ) (hv : ∑ i, normSq (v i)=1)
    (r : Fin d) (hrow : ∀ i, U r i = conj (v i))
    (μ : ℝ) (hμ : 0 < μ) (hfull : ∀ i, μ ≤ normSq (v i)) :
    (∀ (F : Type) [Fintype F] (a b : F → Type)
      [∀ f, Fintype (a f)] [∀ f, Fintype (b f)] (P : Port d q F a b),
      PortEstimate P U v μ) ∧
    μ*(d-q)/((2+μ)*(d+1)) ≤ sInf (portErrors d q U) ∧
    sInf (portErrors d d U) = 0 := by
  have hp (F : Type) [Fintype F] (a b : F → Type)
      [∀ f, Fintype (a f)] [∀ f, Fintype (b f)] (P : Port d q F a b) :
      PortEstimate P U v μ := {
    rankBound := fun x => by
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)
    hsTotal := P.hs_total
    traceBound := P.trace_total
    lossLower := P.loss_lower v hd hv μ hμ hfull
    lossUpper := P.loss_upper U hU v hv r hrow
    errorLower := P.operational_lower U hU v hd hv r hrow μ hμ hfull }
  have hb : ∀ e ∈ portErrors d q U, μ*(d-q)/((2+μ)*(d+1)) ≤ e := by
    rintro e ⟨F, hF, a, b, ha, hb, P, rfl⟩
    exact (hp F a b P).errorLower
  have hn : (portErrors d q U).Nonempty := by
    refine ⟨twoSettingError U (classicalPort d q hq).channel, ?_⟩
    exact ⟨Fin d, inferInstance, (fun _ => Unit), (fun _ => Fin q),
      inferInstance, inferInstance, classicalPort d q hq, rfl⟩
  have hz : ∀ e ∈ portErrors d d U, 0 ≤ e := by
    rintro e ⟨F, hF, a, b, ha, hb, P, rfl⟩
    simpa using P.operational_lower U hU v hd hv r hrow μ hμ hfull
  have hzero : 0 ∈ portErrors d d U := by
    refine ⟨Unit, inferInstance, (fun _ => Unit), (fun _ => Unit),
      inferInstance, inferInstance, identityPort d, ?_⟩
    exact (identity_error d U hd).symm
  exact ⟨hp, le_csInf hn hb,
    le_antisymm (csInf_le ⟨0, hz⟩ hzero) (le_csInf ⟨0, hzero⟩ hz)⟩

#print axioms sparse_probe_port_bound
end D5.S3.Quantum.QuantumChannels.SparseProbePortBound
