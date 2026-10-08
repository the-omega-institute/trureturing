/- GID: D5/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/CliffordJointMeasurability/ShiftedFourierOperatorCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A shifted Fourier reduction gives the sharp dual bound for path observables. -/
/-
proof_shape: path_dual_operator_certificate: content
escape_witness: path_dual_operator_certificate
admission_basis: escape-witness
Direct frozen dependencies: D5/S3/Quantum/Dynamics/PolygonalFourierCouplings.fourier
  statement_id: sha256:0706c337d65e033c10b3e874026fbc51bf5811becfd9777ca8892400ea826c21
Supporting lane modules are first-freeze dependencies.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: sine_weight_product: bind-only; consumer: sine_weights_full_sum
proof_shape: sine_weights_full_sum: bind-only; consumer: sine_weights_path_sum
proof_shape: sine_weights_path_sum: bind-only; consumer: pathDualWeight_sum
proof_shape: theta_pos: bind-only; consumer: fourier_edge_positive
proof_shape: theta_mul_L: bind-only; consumer: fourier_edge_positive
proof_shape: fourier_edge_positive: bind-only; consumer: positiveEdges_nonneg
proof_shape: fourier_cut_weight: bind-only; consumer: positiveEdges_nonneg
proof_shape: fourier_opposite_frequency: bind-only; consumer: negativeEdges_nonneg
proof_shape: positive_block_trace: bind-only; consumer: positiveT_trace
proof_shape: exponential_sum_orthogonality: bind-only; consumer: shiftedFourier_orthonormal
proof_shape: phase_star: bind-only; consumer: shiftedFourier_orthonormal
proof_shape: phase_mul: bind-only; consumer: shiftedFourier_orthonormal
proof_shape: phase_zero: bind-only; consumer: phase_neg
proof_shape: phase_cos: bind-only; consumer: weighted_phase_recurrence
proof_shape: shiftedFourier_orthonormal: bind-only; consumer: fourierGauge_unitary
proof_shape: phase_add: bind-only; consumer: phase_sub
proof_shape: phase_sub: bind-only; consumer: weighted_phase_recurrence
proof_shape: phase_neg: bind-only; consumer: weighted_phase_recurrence
proof_shape: weighted_phase_recurrence: bind-only; consumer: fourier_local_recurrence
proof_shape: fourierEntry_fin: bind-only; consumers: shiftedFourier_orthonormal, shiftedFourier_intertwines
proof_shape: fourier_local_recurrence: bind-only; consumer: shiftedFourier_intertwines
proof_shape: pathWeight_zero: bind-only; consumer: path_dual_operator_certificate
proof_shape: pathWeight_minus_one: bind-only; consumer: shiftedFourier_intertwines
proof_shape: pathWeight_last: bind-only; consumer: shiftedFourier_intertwines
proof_shape: fourierEdge_minus_one: bind-only; consumer: shiftedFourier_intertwines
proof_shape: fourierEdge_last: bind-only; consumer: shiftedFourier_intertwines
proof_shape: shiftedFourier_intertwines: bind-only; consumer: upperK_split
proof_shape: fourier_degree: bind-only; consumer: upperT_is_signed_laplacian
proof_shape: upperT_is_signed_laplacian: bind-only; consumer: upperT_positive_split
proof_shape: positiveEdges_nonneg: bind-only; consumer: negativeEdges_nonneg
proof_shape: negativeEdges_nonneg: bind-only; consumer: upperT_positive_split
proof_shape: weightedLap_sub: bind-only; consumer: upperT_positive_split
proof_shape: upperT_positive_split: bind-only; consumer: upperP_psd
proof_shape: positiveEdges_degree: bind-only; consumer: positiveT_diag
proof_shape: positiveT_diag: bind-only; consumer: positiveT_trace
proof_shape: positiveT_trace: bind-only; consumer: upperP_trace
proof_shape: gauge_unit: bind-only; consumer: gauge_next
proof_shape: gauge_next: bind-only; consumer: gauge_prev
proof_shape: gauge_prev: bind-only; consumer: gaugedJ_apply
proof_shape: gaugeD_unitary: bind-only; consumer: fourierGauge_unitary
proof_shape: gaugedJ_apply: bind-only; consumer: quadratic_upperK
proof_shape: fourierGauge_unitary: bind-only; consumer: upperP_trace
proof_shape: upperP_psd: bind-only; consumer: all_length_majorana_certificate
proof_shape: upperQ_psd: bind-only; consumer: all_length_majorana_certificate
proof_shape: upperP_trace: bind-only; consumer: all_length_majorana_certificate
proof_shape: upperK_split: bind-only; consumer: all_length_majorana_certificate
proof_shape: quadratic_upperK: bind-only; consumer: all_length_majorana_certificate
proof_shape: all_length_majorana_certificate: bind-only; consumer: all_sign_majorana_certificate
proof_shape: outcomeSign_square: bind-only; consumer: signChain_square
proof_shape: outcomeSign_star: bind-only; consumer: signChain_star
proof_shape: signChain_step: bind-only; consumer: signChain_square
proof_shape: signChain_square: bind-only; consumer: signedMajoranas_relations
proof_shape: signChain_star: bind-only; consumer: signedMajoranas_relations
proof_shape: signedMajoranas_relations: bind-only; consumer: all_sign_majorana_certificate
proof_shape: signedMajoranas_bond: bind-only; consumer: all_sign_majorana_certificate
proof_shape: all_sign_majorana_certificate: bind-only; consumer: path_dual_operator_certificate
proof_shape: padCompression_isometry: bind-only; consumer: path_dual_operator_certificate
proof_shape: padCompression_compress: bind-only; consumer: path_dual_operator_certificate
proof_shape: pathWeight_sine: bind-only; consumer: pathDualWeight_sum
proof_shape: theta_range: bind-only; consumer: theta_sin_cos_pos
proof_shape: theta_sin_cos_pos: bind-only; consumer: visibility_Icc
proof_shape: visibility_as_L: bind-only; consumer: visibility_Icc
proof_shape: visibility_Icc: bind-only; consumer: result
proof_shape: visibility_upper_of_weighted: bind-only; consumer: path_feasible_upper
-/
import D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
import D5.S3.Quantum.Dynamics.PolygonalFourierCouplings
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
namespace D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
open D5.S3.Quantum.Measurements.CliffordJointMeasurability.CliffordPathRealizations
private lemma sine_weight_product (j : ℕ) (θ : ℝ) :
    2 * (Real.sin ((j : ℝ) * θ) * Real.sin (((j : ℝ) + 1) * θ)) =
      Real.cos θ - Real.cos (2 * θ * (j : ℝ) + θ) := by
  calc
    2 * (Real.sin ((j : ℝ) * θ) * Real.sin (((j : ℝ) + 1) * θ)) =
        Real.cos ((j : ℝ) * θ - ((j : ℝ) + 1) * θ) -
          Real.cos ((j : ℝ) * θ + ((j : ℝ) + 1) * θ) := by
      nlinarith [Real.two_mul_sin_mul_sin ((j : ℝ) * θ) (((j : ℝ) + 1) * θ)]
    _ = Real.cos θ - Real.cos (2 * θ * (j : ℝ) + θ) := by
      rw [show (j : ℝ) * θ - ((j : ℝ) + 1) * θ = -θ by ring,
        show (j : ℝ) * θ + ((j : ℝ) + 1) * θ = 2 * θ * (j : ℝ) + θ by ring,
        Real.cos_neg]
private lemma sine_weights_full_sum (M : ℕ) (hM : 2 ≤ M) :
    let θ := Real.pi / (M : ℝ)
    (∑ j ∈ Finset.range M,
      Real.sin ((j : ℝ) * θ) * Real.sin (((j : ℝ) + 1) * θ)) =
        (M : ℝ) / 2 * Real.cos θ := by
  dsimp only
  let θ : ℝ := Real.pi / (M : ℝ)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMone : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
  have hθpos : 0 < θ := div_pos Real.pi_pos hMpos
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ hMpos).mpr
    nlinarith [Real.pi_pos]
  have hsin : Real.sin θ ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθpos hθlt)
  have hMθ : (M : ℝ) * θ = Real.pi := by
    dsimp [θ]
    field_simp
  have hmiddle : (M : ℝ) * (2 * θ) / 2 = Real.pi := by nlinarith [hMθ]
  have hlast : ((M : ℝ) - 1) * (2 * θ) / 2 + θ = Real.pi := by nlinarith [hMθ]
  have hsum : (∑ j ∈ Finset.range M, Real.cos (2 * θ * (j : ℝ) + θ)) = 0 := by
    have h := Real.sin_mul_sum_cos M (2 * θ) θ
    rw [show 2 * θ / 2 = θ by ring, hmiddle, hlast, Real.sin_pi, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hsin
  have htwo :
      2 * (∑ j ∈ Finset.range M,
        Real.sin ((j : ℝ) * θ) * Real.sin (((j : ℝ) + 1) * θ)) =
          (M : ℝ) * Real.cos θ := by
    rw [Finset.mul_sum]
    calc
      (∑ j ∈ Finset.range M,
        2 * (Real.sin ((j : ℝ) * θ) * Real.sin (((j : ℝ) + 1) * θ))) =
          ∑ j ∈ Finset.range M, (Real.cos θ - Real.cos (2 * θ * (j : ℝ) + θ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact sine_weight_product j θ
      _ = (M : ℝ) * Real.cos θ := by rw [Finset.sum_sub_distrib, hsum]; simp
  change (∑ j ∈ Finset.range M,
    Real.sin ((j : ℝ) * θ) * Real.sin (((j : ℝ) + 1) * θ)) =
      (M : ℝ) / 2 * Real.cos θ
  nlinarith [htwo]
lemma sine_weights_path_sum (K : ℕ) :
    let θ := Real.pi / ((K + 2 : ℕ) : ℝ)
    (∑ j ∈ Finset.range K,
      Real.sin (((j : ℝ) + 1) * θ) * Real.sin (((j : ℝ) + 2) * θ)) =
        ((K + 2 : ℕ) : ℝ) / 2 * Real.cos θ := by
  dsimp only
  let θ : ℝ := Real.pi / ((K + 2 : ℕ) : ℝ)
  let f : ℕ → ℝ := fun j =>
    Real.sin ((j : ℝ) * θ) * Real.sin (((j : ℝ) + 1) * θ)
  have hnum : ((K + 2 : ℕ) : ℝ) * θ = Real.pi := by
    dsimp [θ]
    field_simp
  have hzero : f 0 = 0 := by simp [f]
  have htail : f (K + 1) = 0 := by
    dsimp [f]
    rw [show ((K + 1 : ℕ) : ℝ) + 1 = ((K + 2 : ℕ) : ℝ) by push_cast; ring,
      hnum, Real.sin_pi, mul_zero]
  have hsplit : (∑ j ∈ Finset.range (K + 2), f j) =
      ∑ j ∈ Finset.range K, f (j + 1) := by
    rw [show K + 2 = (K + 1) + 1 by omega,
      Finset.sum_range_succ' f (K + 1),
      Finset.sum_range_succ (fun j => f (j + 1)) K, htail, hzero]
    simp
  calc
    (∑ j ∈ Finset.range K,
      Real.sin (((j : ℝ) + 1) * θ) * Real.sin (((j : ℝ) + 2) * θ)) =
        ∑ j ∈ Finset.range K, f (j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [f, Nat.cast_add, Nat.cast_one]
      congr 2 <;> ring
    _ = ∑ j ∈ Finset.range (K + 2), f j := hsplit.symm
    _ = ((K + 2 : ℕ) : ℝ) / 2 * Real.cos θ := by
      simpa [f, θ] using sine_weights_full_sum (K + 2) (by omega)
noncomputable section
def theta (L : ℕ) : ℝ := Real.pi / (2 * (L : ℝ))
private def frequencyReal (L : ℕ) (r : ℝ) : ℝ := (2*r-(L:ℝ)+1)*theta L
private def fourierEdge (L : ℕ) (r : ℝ) : ℝ := (1/2)*Real.cos (frequencyReal L r+theta L)
lemma theta_pos {L : ℕ} (hL : 0 < L) : 0 < theta L := by
  unfold theta
  exact div_pos Real.pi_pos (by positivity)
lemma theta_mul_L {L : ℕ} (hL : 0 < L) : (L : ℝ) * theta L = Real.pi / 2 := by
  unfold theta
  have hLR : (L : ℝ) ≠ 0 := by positivity
  field_simp
private lemma fourier_edge_positive {L r : ℕ} (hL : 2 ≤ L) (hr : r < L - 1) :
    0 < fourierEdge L r := by
  have hθ := theta_pos (show 0 < L by omega)
  have hLθ := theta_mul_L (show 0 < L by omega)
  have hrR : (r : ℝ) + 1 < L := by exact_mod_cast (by omega : r + 1 < L)
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hlow : -(Real.pi / 2) < frequencyReal L r + theta L := by
    unfold frequencyReal
    nlinarith [Real.pi_pos]
  have hhigh : frequencyReal L r + theta L < Real.pi / 2 := by
    unfold frequencyReal
    nlinarith
  unfold fourierEdge
  exact mul_pos (by norm_num) (Real.cos_pos_of_mem_Ioo ⟨hlow, hhigh⟩)
private lemma fourier_cut_weight {L : ℕ} (hL : 0 < L) : fourierEdge L ((L - 1 : ℕ) : ℝ) = 0 := by
  have hLθ := theta_mul_L hL
  have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ L)]
    norm_num
  unfold fourierEdge frequencyReal
  rw [hcast]
  have harg : (2 * ((L : ℝ) - 1) - (L : ℝ) + 1) * theta L + theta L = Real.pi / 2 := by
    nlinarith [hLθ]
  rw [harg, Real.cos_pi_div_two, mul_zero]
private lemma fourier_opposite_frequency (L r : ℕ) (hL : 0 < L) :
    frequencyReal L ((L + r : ℕ) : ℝ) = frequencyReal L r + Real.pi := by
  unfold frequencyReal
  push_cast
  nlinarith [theta_mul_L hL]
private lemma positive_block_trace {L : ℕ} (hL : 2 ≤ L) :
    (∑ r ∈ Finset.range L, Real.cos (theta L) * Real.cos (frequencyReal L r)) =
      Real.cos (theta L) / Real.sin (theta L) := by
  have hθ := theta_pos (show 0 < L by omega)
  have hLθ := theta_mul_L (show 0 < L by omega)
  have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
  have hθpi : theta L < Real.pi := by nlinarith [Real.pi_pos]
  have hs : Real.sin (theta L) ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ hθpi)
  have hsum := Real.sin_mul_sum_cos L (2 * theta L) ((1 - (L : ℝ)) * theta L)
  rw [show 2 * theta L / 2 = theta L by ring] at hsum
  have ha : (L : ℝ) * (2 * theta L) / 2 = Real.pi / 2 := by nlinarith [hLθ]
  have hb : ((L : ℝ) - 1) * (2 * theta L) / 2 + (1 - (L : ℝ)) * theta L = 0 := by ring
  rw [ha, hb, Real.sin_pi_div_two, Real.cos_zero, one_mul] at hsum
  have hsum' : (∑ r ∈ Finset.range L, Real.cos (frequencyReal L r)) = (Real.sin (theta L))⁻¹ := by
    rw [inv_eq_one_div]
    apply (eq_div_iff hs).mpr
    rw [mul_comm]
    convert hsum using 2
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    unfold frequencyReal
    ring
  rw [← Finset.mul_sum, hsum', div_eq_mul_inv]
end
noncomputable section
lemma exponential_sum_orthogonality (M : ℕ) (hM : 0 < M) (r s : Fin M) :
    (∑ j ∈ Finset.range M, Complex.exp
      (((2 * Real.pi * ((r : ℝ) - (s : ℝ)) / (M : ℝ)) * (j : ℝ) : ℝ) * Complex.I)) =
        if r = s then (M : ℂ) else 0 := by
  classical
  let : NeZero M := ⟨Nat.ne_of_gt hM⟩
  let e := ZMod.finEquiv M
  have hecast (j : Fin M) : e j = (j.val : ZMod M) := by
    have heval : (e j).val = j.val := by
      cases M with
      | zero => omega
      | succ M => rfl
    rw [← ZMod.natCast_zmod_val (e j), heval]
  have hentry (j : Fin M) :
      ZMod.stdAddChar (e j * (e r - e s)) = Complex.exp
        (((2 * Real.pi * ((r : ℝ) - (s : ℝ)) / (M : ℝ)) * (j : ℝ) : ℝ) * Complex.I) := by
    rw [hecast j, hecast r, hecast s]
    rw [show (j : ZMod M) * ((r : ZMod M) - (s : ZMod M)) =
      (((j : ℤ) * ((r : ℤ) - (s : ℤ)) : ℤ) : ZMod M) by push_cast; rfl,
      ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← hentry]
  rw [Fintype.sum_equiv e.toEquiv
    (fun j => ZMod.stdAddChar (e j * (e r - e s)))
    (fun x => ZMod.stdAddChar (x * (e r - e s))) (fun _ => rfl),
    AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar M)]
  simp only [sub_eq_zero, e.injective.eq_iff, ZMod.card, Nat.cast_ite, Nat.cast_zero]

end
noncomputable section
lemma phase_star (x : ℝ) : star ((fun x : ℝ => (Real.probChar x : ℂ)) x) = (fun x : ℝ => (Real.probChar x : ℂ)) (-x) := by
  exact Circle.star_addChar x
lemma phase_mul (x y : ℝ) : (fun x : ℝ => (Real.probChar x : ℂ)) x * (fun x : ℝ => (Real.probChar x : ℂ)) y = (fun x : ℝ => (Real.probChar x : ℂ)) (x + y) := by
  exact congrArg (fun z : Circle => (z : ℂ)) (Real.probChar.map_add_eq_mul x y).symm
private lemma phase_zero : (fun x : ℝ => (Real.probChar x : ℂ)) 0 = 1 := by simp [Real.probChar_apply]
lemma phase_cos (x : ℝ) : (Real.cos x : ℂ) = ((fun x : ℝ => (Real.probChar x : ℂ)) x + (fun x : ℝ => (Real.probChar x : ℂ)) (-x)) / 2 := by
  simp only [Real.probChar_apply, Complex.ofReal_neg, Complex.ofReal_cos]
  unfold Complex.cos
  rfl
private def fourierEntry (L : ℕ) (j r : ℝ) : ℂ :=
  (Real.sqrt ((2*L:ℕ):ℝ))⁻¹ * (fun x : ℝ => (Real.probChar x : ℂ)) (j*frequencyReal L r)
private def shiftedFourier (L : ℕ) : Matrix (Fin (2 * L)) (Fin (2 * L)) ℂ :=
  Matrix.diagonal (fun j : Fin (2 * L) => Complex.exp
    (((((j : ℝ) * ((1 - (L : ℝ)) * (Real.pi / (2 * (L : ℝ))))) : ℝ) : ℂ) * Complex.I)) *
    ((D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.fourier (2 * L)).map star)
private lemma fourierEntry_fin (L : ℕ) (j r : Fin (2*L)) :
    shiftedFourier L j r = fourierEntry L j r := by
  rw [shiftedFourier, Matrix.diagonal_mul]
  simp only [Matrix.map_apply, D5.S3.Quantum.Dynamics.PolygonalFourierCouplings.fourier,
    Complex.star_def, map_div₀, ← Complex.exp_conj, map_neg, map_mul,
    map_natCast, Complex.conj_ofReal, Complex.conj_I]
  simp only [fourierEntry, Real.probChar_apply, frequencyReal, theta,
    div_eq_mul_inv, Complex.ofReal_inv, ← mul_assoc]
  rw [← Complex.exp_add]
  conv_rhs => rw [mul_comm]
  congr 1
  congr 1
  push_cast
  ring
private lemma shiftedFourier_orthonormal {L : ℕ} (hL : 0 < L) :
    (shiftedFourier L).conjTranspose * shiftedFourier L = 1 := by
  classical
  have hM : 0 < 2 * L := by omega
  have hMR : (0 : ℝ) < 2 * L := by positivity
  have hsqrt : Real.sqrt ((2 * L : ℕ) : ℝ) ≠ 0 := by positivity
  let scale : ℂ := ((Real.sqrt ((2 * L : ℕ) : ℝ))⁻¹ : ℝ)
  have hscale : scale * scale = ((2 * L : ℕ) : ℂ)⁻¹ := by
    dsimp only [scale]
    rw [← Complex.ofReal_mul, ← mul_inv, ← sq, Real.sq_sqrt (by positivity)]
    simp
  ext r s
  simp only [Matrix.one_apply]
  simp_rw [Matrix.mul_apply, Matrix.conjTranspose_apply, fourierEntry_fin]
  change (∑ j : Fin (2 * L), star (scale * (fun x : ℝ => (Real.probChar x : ℂ)) ((j : ℝ) * frequencyReal L r)) *
    (scale * (fun x : ℝ => (Real.probChar x : ℂ)) ((j : ℝ) * frequencyReal L s))) = (if r = s then 1 else 0)
  have hterm : ∀ j : Fin (2 * L),
      star (scale * (fun x : ℝ => (Real.probChar x : ℂ)) ((j : ℝ) * frequencyReal L r)) *
        (scale * (fun x : ℝ => (Real.probChar x : ℂ)) ((j : ℝ) * frequencyReal L s)) =
          ((2 * L : ℕ) : ℂ)⁻¹ *
            (fun x : ℝ => (Real.probChar x : ℂ)) ((2 * Real.pi * ((s : ℝ) - (r : ℝ)) / ((2 * L : ℕ) : ℝ)) * (j : ℝ)) := by
    intro j
    have hstarscale : star scale = scale := by simp [scale]
    rw [star_mul, hstarscale, phase_star]
    calc
      ((fun x : ℝ => (Real.probChar x : ℂ)) (-((j : ℝ) * frequencyReal L r)) * scale) *
          (scale * (fun x : ℝ => (Real.probChar x : ℂ)) ((j : ℝ) * frequencyReal L s)) =
          (scale * scale) *
          ((fun x : ℝ => (Real.probChar x : ℂ)) (-((j : ℝ) * frequencyReal L r)) * (fun x : ℝ => (Real.probChar x : ℂ)) ((j : ℝ) * frequencyReal L s)) := by ring
      _ = _ := by
        rw [hscale, phase_mul]
        congr 2
        unfold frequencyReal theta
        push_cast
        field_simp
        ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  change ((2 * L : ℕ) : ℂ)⁻¹ * (∑ j : Fin (2 * L),
    (fun j : ℕ => (fun x : ℝ => (Real.probChar x : ℂ)) ((2 * Real.pi * ((s : ℝ) - (r : ℝ)) / ((2 * L : ℕ) : ℝ)) * (j : ℝ))) j) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (fun x : ℝ => (Real.probChar x : ℂ)) ((2 * Real.pi * ((s : ℝ) - (r : ℝ)) / ((2 * L : ℕ) : ℝ)) * (j : ℝ))) (2 * L)]
  have hsum := exponential_sum_orthogonality (2 * L) hM s r
  change (∑ j ∈ Finset.range (2 * L), (fun x : ℝ => (Real.probChar x : ℂ)) _) = _ at hsum
  rw [hsum]
  by_cases hrs : r = s
  · simp only [hrs, ↓reduceIte]
    exact inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hM)
  · simp [hrs, Ne.symm hrs, Matrix.one_apply]
end
noncomputable section
private lemma phase_add (a b : ℝ) : (fun x : ℝ => (Real.probChar x : ℂ)) (a+b) = (fun x : ℝ => (Real.probChar x : ℂ)) a * (fun x : ℝ => (Real.probChar x : ℂ)) b := (phase_mul a b).symm
private lemma phase_sub (a b : ℝ) : (fun x : ℝ => (Real.probChar x : ℂ)) (a-b) = (fun x : ℝ => (Real.probChar x : ℂ)) a * (fun x : ℝ => (Real.probChar x : ℂ)) (-b) := by
  rw [sub_eq_add_neg, phase_add]
private lemma phase_neg (a : ℝ) : (fun x : ℝ => (Real.probChar x : ℂ)) (-a) = ((fun x : ℝ => (Real.probChar x : ℂ)) a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [phase_mul, neg_add_cancel, phase_zero]
private lemma weighted_phase_recurrence (t x k θ : ℝ) :
    ((Real.cos θ - Real.cos (2*x+θ)) / 2 : ℝ) * (fun x : ℝ => (Real.probChar x : ℂ)) (t + k) +
      ((Real.cos θ - Real.cos (2*x-θ)) / 2 : ℝ) * (fun x : ℝ => (Real.probChar x : ℂ)) (t - k) =
      (Real.cos θ * Real.cos k : ℝ) * (fun x : ℝ => (Real.probChar x : ℂ)) t -
      ((Real.cos (k+θ)) / 2 : ℝ) * (fun x : ℝ => (Real.probChar x : ℂ)) (t + 2*x) -
      ((Real.cos (k-θ)) / 2 : ℝ) * (fun x : ℝ => (Real.probChar x : ℂ)) (t - 2*x) := by
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat,
    phase_cos, phase_sub, phase_add, neg_add_rev, neg_sub, phase_neg]
  have hnz : ∀ a, (fun x : ℝ => (Real.probChar x : ℂ)) a ≠ 0 := by intro a; exact Complex.exp_ne_zero _
  field_simp [hnz]
  ring
end
noncomputable section
def pathWeight (L : ℕ) (j : ℝ) : ℝ :=
  (Real.cos (theta L) - Real.cos ((2*j+1)*theta L))/2
private def fourierDiagonal (L : ℕ) (r : ℝ) : ℝ :=
  Real.cos (theta L)*Real.cos (frequencyReal L r)
private lemma fourier_local_recurrence (L : ℕ) (j r : ℝ) :
    (pathWeight L j:ℂ)*fourierEntry L (j+1) r +
      (pathWeight L (j-1):ℂ)*fourierEntry L (j-1) r =
    (fourierDiagonal L r:ℂ)*fourierEntry L j r -
      (fourierEdge L r:ℂ)*fourierEntry L j (r+1) -
      (fourierEdge L (r-1):ℂ)*fourierEntry L j (r-1) := by
  have h := weighted_phase_recurrence (j*frequencyReal L r) (j*theta L)
    (frequencyReal L r) (theta L)
  have hfplus : frequencyReal L (r+1) = frequencyReal L r+2*theta L := by
    unfold frequencyReal; ring
  have hfminus : frequencyReal L (r-1) = frequencyReal L r-2*theta L := by
    unfold frequencyReal; ring
  have hcos : frequencyReal L (r-1)+theta L=frequencyReal L r-theta L := by
    rw [hfminus]; ring
  have harg1 : (j+1)*frequencyReal L r=j*frequencyReal L r+frequencyReal L r := by ring
  have harg2 : (j-1)*frequencyReal L r=j*frequencyReal L r-frequencyReal L r := by ring
  have harg3 : j*frequencyReal L (r+1)=j*frequencyReal L r+2*(j*theta L) := by rw [hfplus]; ring
  have harg4 : j*frequencyReal L (r-1)=j*frequencyReal L r-2*(j*theta L) := by rw [hfminus]; ring
  have hw1 : (2*j+1)*theta L=2*(j*theta L)+theta L := by ring
  have hw2 : (2*(j-1)+1)*theta L=2*(j*theta L)-theta L := by ring
  unfold pathWeight fourierEntry fourierDiagonal fourierEdge
  rw [harg1, harg2, harg3, harg4, hw1, hw2, hcos]
  have hs := congrArg (fun z : ℂ => ((Real.sqrt ((2*L:ℕ):ℝ))⁻¹:ℂ)*z) h
  convert hs using 1 <;> push_cast <;> ring
private lemma pathWeight_zero (L : ℕ) : pathWeight L 0=0 := by simp [pathWeight]
private lemma pathWeight_minus_one (L : ℕ) : pathWeight L (-1)=0 := by
  norm_num [pathWeight, Real.cos_neg]
private lemma pathWeight_last {L : ℕ} (hL : 0<L) : pathWeight L (2*(L:ℝ)-1)=0 := by
  have hθ := theta_mul_L hL
  have ha : (2*(2*(L:ℝ)-1)+1)*theta L=2*Real.pi-theta L := by nlinarith
  unfold pathWeight
  rw [ha, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]
  ring
private lemma fourierEdge_minus_one {L : ℕ} (hL : 0<L) : fourierEdge L (-1)=0 := by
  have hθ := theta_mul_L hL
  have ha : frequencyReal L (-1)+theta L=-(Real.pi/2) := by
    unfold frequencyReal; nlinarith
  simp [fourierEdge, ha, Real.cos_neg]
private lemma fourierEdge_last {L : ℕ} (hL : 0<L) : fourierEdge L (2*(L:ℝ)-1)=0 := by
  have hθ := theta_mul_L hL
  have ha : frequencyReal L (2*(L:ℝ)-1)+theta L=Real.pi+Real.pi/2 := by
    unfold frequencyReal; nlinarith
  simp [fourierEdge, ha, Real.cos_add]
private def upperJ (L : ℕ) : Matrix (Fin (2*L)) (Fin (2*L)) ℂ :=
  tridiagonal (2*L) (fun _ => 0) (fun j => (pathWeight L j:ℂ))
private def upperT (L : ℕ) : Matrix (Fin (2*L)) (Fin (2*L)) ℂ :=
  tridiagonal (2*L) (fun r => (fourierDiagonal L r:ℂ)) (fun r => -(fourierEdge L r:ℂ))
private lemma shiftedFourier_intertwines {L : ℕ} (hL : 0 < L) :
    upperJ L * shiftedFourier L = shiftedFourier L * upperT L := by
  classical
  ext j r
  rw [upperJ, upperT, tridiagonal_mul_apply, mul_tridiagonal_apply]
  simp only [zero_mul, zero_add]
  have hjplus :
      (if h : j.val+1<2*L then (pathWeight L j:ℂ)*shiftedFourier L ⟨j.val+1,h⟩ r else 0) =
        (pathWeight L j:ℂ)*fourierEntry L ((j:ℝ)+1) r := by
    by_cases h : j.val+1 < 2*L
    · simp only [dif_pos h, fourierEntry_fin]
      congr 2
      simp
    · rw [dif_neg h]
      have hlast : (j:ℝ) = 2*(L:ℝ)-1 := by
        have hn : j.val+1=2*L := by have := j.isLt; omega
        have hr : (j:ℝ)+1=2*(L:ℝ) := by exact_mod_cast hn
        linarith
      rw [hlast, pathWeight_last hL]
      simp
  have hjminus :
      (if h : 0<j.val then (pathWeight L (⟨j.val-1,by omega⟩:Fin (2*L)):ℂ)*
        shiftedFourier L ⟨j.val-1,by omega⟩ r else 0) =
        (pathWeight L ((j:ℝ)-1):ℂ)*fourierEntry L ((j:ℝ)-1) r := by
    by_cases h : 0 < j.val
    · simp only [dif_pos h, fourierEntry_fin]
      have he : ((⟨j.val-1,by omega⟩:Fin (2*L)):ℝ)=(j:ℝ)-1 := by
        simp only [Fin.val_mk, Nat.cast_sub (by omega : 1≤j.val), Nat.cast_one]
      rw [he]
    · rw [dif_neg h]
      have hj : j.val=0 := by omega
      simp only [show (j:ℝ)=0 by exact_mod_cast hj, zero_sub]
      rw [pathWeight_minus_one]
      simp
  have hrplus :
      (if h : r.val+1<2*L then shiftedFourier L j ⟨r.val+1,h⟩ * -(fourierEdge L r:ℂ) else 0) =
        -(fourierEdge L r:ℂ)*fourierEntry L j ((r:ℝ)+1) := by
    by_cases h : r.val+1 < 2*L
    · simp only [dif_pos h, fourierEntry_fin]
      have he : ((⟨r.val+1,h⟩:Fin (2*L)):ℝ)=(r:ℝ)+1 := by simp
      rw [he, mul_comm]
    · rw [dif_neg h]
      have hlast : (r:ℝ) = 2*(L:ℝ)-1 := by
        have hn : r.val+1=2*L := by have := r.isLt; omega
        have hr : (r:ℝ)+1=2*(L:ℝ) := by exact_mod_cast hn
        linarith
      rw [hlast, fourierEdge_last hL]
      simp
  have hrminus :
      (if h : 0<r.val then shiftedFourier L j ⟨r.val-1,by omega⟩ *
        -(fourierEdge L (⟨r.val-1,by omega⟩:Fin (2*L)):ℂ) else 0) =
        -(fourierEdge L ((r:ℝ)-1):ℂ)*fourierEntry L j ((r:ℝ)-1) := by
    by_cases h : 0 < r.val
    · simp only [dif_pos h, fourierEntry_fin]
      have he : ((⟨r.val-1,by omega⟩:Fin (2*L)):ℝ)=(r:ℝ)-1 := by
        simp only [Fin.val_mk, Nat.cast_sub (by omega : 1≤r.val), Nat.cast_one]
      rw [he, mul_comm]
    · rw [dif_neg h]
      have hr : r.val=0 := by omega
      simp only [show (r:ℝ)=0 by exact_mod_cast hr, zero_sub]
      rw [fourierEdge_minus_one hL]
      simp
  rw [hjplus, hjminus, hrplus, hrminus, fourierEntry_fin]
  convert fourier_local_recurrence L (j:ℝ) (r:ℝ) using 1 <;> ring
end
open scoped ComplexOrder
noncomputable section
private lemma fourier_degree (L : ℕ) (r : ℝ) :
    fourierDiagonal L r=fourierEdge L (r-1)+fourierEdge L r := by
  unfold fourierDiagonal fourierEdge frequencyReal
  have hminus : (2*(r-1)-(L:ℝ)+1)*theta L+theta L=
      (2*r-(L:ℝ)+1)*theta L-theta L := by ring
  rw [hminus]
  nlinarith [Real.cos_add ((2*r-(L:ℝ)+1)*theta L) (theta L),
    Real.cos_sub ((2*r-(L:ℝ)+1)*theta L) (theta L)]
private lemma upperT_is_signed_laplacian {L : ℕ} (hL : 0 < L) :
    upperT L=weightedLap (2*L) (fun r => fourierEdge L r) := by
  classical
  ext j k
  rw [upperT, tridiagonal, weightedLap_apply]
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Matrix.transpose_apply, Matrix.of_apply]
  have hd : (fourierDiagonal L j:ℂ) = (fourierEdge L j:ℂ)+
      (if h : 0 < j.val then (fourierEdge L (⟨j.val-1,by omega⟩:Fin (2*L)):ℂ) else 0) := by
    rw [fourier_degree]
    by_cases h : 0 < j.val
    · rw [dif_pos h]
      have he : ((⟨j.val-1,by omega⟩:Fin (2*L)):ℝ)=(j:ℝ)-1 := by
        simp only [Nat.cast_sub (by omega : 1 ≤ j.val), Nat.cast_one]
      rw [he]
      push_cast
      ring
    · rw [dif_neg h]
      have he : (j:ℝ)=0 := by
        have hj : j.val=0 := by omega
        exact_mod_cast hj
      rw [he]
      simp [fourierEdge_minus_one hL]
  rw [hd]
  split_ifs <;> ring
private def positiveEdges (L : ℕ) (r : Fin (2*L)) : ℝ :=
  if r.val < L then fourierEdge L r else 0
private def negativeEdges (L : ℕ) (r : Fin (2*L)) : ℝ :=
  if r.val < L then 0 else -fourierEdge L r
private def positiveT (L : ℕ) := weightedLap (2*L) (positiveEdges L)
private def negativeT (L : ℕ) := weightedLap (2*L) (negativeEdges L)
private lemma positiveEdges_nonneg {L : ℕ} (hL : 2 ≤ L) (r : Fin (2*L)) :
    0 ≤ positiveEdges L r := by
  unfold positiveEdges
  by_cases h : r.val < L
  · rw [if_pos h]
    by_cases he : r.val=L-1
    · rw [he, fourier_cut_weight (by omega)]
    · exact le_of_lt (fourier_edge_positive hL (by omega))
  · simp [h]
private lemma negativeEdges_nonneg {L : ℕ} (hL : 2 ≤ L) (r : Fin (2*L)) :
    0 ≤ negativeEdges L r := by
  unfold negativeEdges
  by_cases h : r.val < L
  · simp [h]
  · rw [if_neg h]
    have hr : r.val=L+(r.val-L) := by omega
    have hed : fourierEdge L r=-fourierEdge L ((r.val-L:ℕ):ℝ) := by
      have hf := fourier_opposite_frequency L (r.val-L) (by omega)
      rw [← hr] at hf
      unfold fourierEdge
      rw [hf]
      rw [show frequencyReal L ((r.val-L : ℕ) : ℝ)+Real.pi+theta L=
        (frequencyReal L ((r.val-L : ℕ) : ℝ)+theta L)+Real.pi by ring, Real.cos_add_pi]
      ring
    rw [hed, neg_neg]
    have hnon := positiveEdges_nonneg hL (⟨r.val-L,by omega⟩:Fin (2*L))
    simpa [positiveEdges, show r.val-L < L by have := r.isLt; omega] using hnon
private lemma weightedLap_sub {M : ℕ} (b c : Fin M → ℝ) :
    weightedLap M (fun r => b r-c r)=weightedLap M b-weightedLap M c := by
  classical
  simp [weightedLap, Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
private lemma upperT_positive_split {L : ℕ} (hL : 2 ≤ L) :
    upperT L=positiveT L-negativeT L ∧
      (positiveT L).PosSemidef ∧ (negativeT L).PosSemidef := by
  refine ⟨?_, weightedLap_psd _ (positiveEdges_nonneg hL),
    weightedLap_psd _ (negativeEdges_nonneg hL)⟩
  rw [upperT_is_signed_laplacian (by omega), positiveT, negativeT, ← weightedLap_sub]
  congr 1
  funext r
  unfold positiveEdges negativeEdges
  split_ifs <;> ring
end
noncomputable section
private lemma positiveEdges_degree {L : ℕ} (hL : 0 < L) (r : Fin (2*L)) :
    positiveEdges L r+(if h : 0 < r.val then positiveEdges L ⟨r.val-1,by omega⟩ else 0) =
      if r.val < L then fourierDiagonal L r else 0 := by
  classical
  by_cases hr : r.val < L
  · rw [if_pos hr]
    unfold positiveEdges
    rw [if_pos hr]
    by_cases h0 : 0 < r.val
    · rw [dif_pos h0]
      simp only [Fin.val_mk, show r.val-1 < L by omega, ↓reduceIte]
      have he : ((⟨r.val-1,by omega⟩:Fin (2*L)):ℝ)=(r:ℝ)-1 := by
        simp only [Nat.cast_sub (by omega : 1 ≤ r.val), Nat.cast_one]
      rw [he, fourier_degree]
      ring
    · rw [dif_neg h0]
      have he : (r:ℝ)=0 := by
        have hr0 : r.val=0 := by omega
        exact_mod_cast hr0
      rw [he, fourier_degree]
      simp [fourierEdge_minus_one hL]
  · rw [if_neg hr]
    have h0 : 0 < r.val := by omega
    rw [dif_pos h0]
    unfold positiveEdges
    rw [if_neg hr]
    by_cases he : r.val=L
    · have hp : r.val-1=L-1 := by omega
      simp only [Fin.val_mk, hp, show L-1 < L by omega, ↓reduceIte, zero_add]
      change fourierEdge L ((L-1 : ℕ) : ℝ)=0
      exact fourier_cut_weight hL
    · simp [show ¬r.val-1 < L by omega]
private lemma positiveT_diag {L : ℕ} (hL : 0 < L) (r : Fin (2*L)) :
    positiveT L r r=if r.val < L then (fourierDiagonal L r:ℂ) else 0 := by
  rw [positiveT, weightedLap_apply]
  simp only [↓reduceIte, show ¬r.val+1=r.val by omega, sub_zero]
  have hd := congrArg (fun x : ℝ => (x:ℂ)) (positiveEdges_degree hL r)
  push_cast at hd
  split_ifs at * <;> simpa using hd
private lemma positiveT_trace {L : ℕ} (hL : 2 ≤ L) :
    (positiveT L).trace=(Real.cos (theta L)/Real.sin (theta L):ℂ) := by
  classical
  unfold Matrix.trace Matrix.diag
  simp_rw [positiveT_diag (show 0 < L by omega)]
  change (∑ r : Fin (2*L), (fun r : ℕ => if r < L then (fourierDiagonal L (r:ℝ):ℂ) else 0) r)=_
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => if r<L then (fourierDiagonal L (r:ℝ):ℂ) else 0) (2*L)]
  rw [show 2*L=L+L by omega, Finset.sum_range_add]
  have hfirst : (∑ r ∈ Finset.range L, if r < L then (fourierDiagonal L (r:ℝ):ℂ) else 0)=
      ∑ r ∈ Finset.range L, (fourierDiagonal L (r:ℝ):ℂ) := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [if_pos (Finset.mem_range.mp hr)]
  have hsecond : (∑ r ∈ Finset.range L, if L+r < L then (fourierDiagonal L ((L+r:ℕ):ℝ):ℂ) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro r hr
    rw [if_neg (by omega)]
  rw [hfirst, hsecond, add_zero]
  change (∑ r ∈ Finset.range L, ((Real.cos (theta L)*Real.cos (frequencyReal L r):ℝ):ℂ))=_
  rw [← Complex.ofReal_sum, positive_block_trace hL]
  norm_cast
end
noncomputable section
private def gauge (j : ℕ) : ℂ := (-Complex.I)^j
private def gaugeD (L : ℕ) : Matrix (Fin (2*L)) (Fin (2*L)) ℂ :=
  Matrix.diagonal (fun j => gauge j)
private lemma gauge_unit (j : ℕ) : gauge j*star (gauge j)=1 := by
  unfold gauge
  simp only [star_pow, star_neg, Complex.star_def, Complex.conj_I, neg_neg]
  rw [← mul_pow]
  norm_num [Complex.I_mul_I]
private lemma gauge_next (j : ℕ) : gauge j*star (gauge (j+1))=Complex.I := by
  have hs : gauge (j+1)=gauge j*(-Complex.I) := by unfold gauge; rw [pow_succ]
  have hi : star (-Complex.I)=Complex.I := by simp [Complex.star_def]
  rw [hs, star_mul, hi]
  calc
    _ = (gauge j*star (gauge j))*Complex.I := by ring
    _ = Complex.I := by rw [gauge_unit,one_mul]
private lemma gauge_prev (j : ℕ) : gauge (j+1)*star (gauge j)=-Complex.I := by
  have h := congrArg star (gauge_next j)
  simp only [star_mul, star_star] at h
  simpa [Complex.star_def] using h
private lemma gaugeD_unitary (L : ℕ) : (gaugeD L).conjTranspose*gaugeD L=1 := by
  classical
  ext j k
  simp only [gaugeD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply, Function.comp_apply, Pi.star_apply]
  by_cases h : j=k
  · subst k; simp only [↓reduceIte]; rw [mul_comm, gauge_unit]
  · simp [h]
private lemma gaugedJ_apply (L : ℕ) (j k : Fin (2*L)) :
    (gaugeD L*upperJ L*(gaugeD L).conjTranspose) j k =
      (if j.val+1=k.val then Complex.I*(pathWeight L j:ℂ) else 0) -
      (if k.val+1=j.val then Complex.I*(pathWeight L k:ℂ) else 0) := by
  classical
  simp only [gaugeD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul,
    Matrix.mul_diagonal, Function.comp_apply, Pi.star_apply, upperJ, tridiagonal, Matrix.add_apply, Matrix.diagonal_apply,
    Matrix.transpose_apply, Matrix.of_apply]
  have hz : (if j=k then (0:ℂ) else 0)=0 := by simp
  rw [hz, zero_add]
  by_cases h1 : j.val+1=k.val
  · have h2 : ¬k.val+1=j.val := by omega
    simp only [if_pos h1,if_neg h2,add_zero,sub_zero]
    have hg := gauge_next j.val
    rw [h1] at hg
    calc
      _ = (gauge j*star (gauge k))*(pathWeight L j:ℂ) := by ring
      _ = _ := by rw [hg]
  · by_cases h2 : k.val+1=j.val
    · simp only [if_neg h1,if_pos h2,zero_add,zero_sub]
      have hg := gauge_prev k.val
      rw [h2] at hg
      calc
        _ = (gauge j*star (gauge k))*(pathWeight L k:ℂ) := by ring
        _ = _ := by rw [hg]; ring
    · simp [h1,h2]
end
open scoped ComplexOrder
noncomputable section
private def fourierGauge (L : ℕ) := gaugeD L*shiftedFourier L
private def upperP (L : ℕ) := fourierGauge L*positiveT L*(fourierGauge L).conjTranspose
private def upperQ (L : ℕ) := fourierGauge L*negativeT L*(fourierGauge L).conjTranspose
private def upperK (L : ℕ) := gaugeD L*upperJ L*(gaugeD L).conjTranspose
private lemma fourierGauge_unitary {L : ℕ} (hL : 0 < L) :
    (fourierGauge L).conjTranspose*fourierGauge L=1 := by
  unfold fourierGauge
  rw [Matrix.conjTranspose_mul]
  calc
    _ = (shiftedFourier L).conjTranspose*((gaugeD L).conjTranspose*gaugeD L)*shiftedFourier L := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [gaugeD_unitary, Matrix.mul_one, shiftedFourier_orthonormal hL]
private lemma upperP_psd {L : ℕ} (hL : 2 ≤ L) : (upperP L).PosSemidef := by
  have h := (upperT_positive_split hL).2.1.conjTranspose_mul_mul_same (fourierGauge L).conjTranspose
  simpa [upperP] using h
private lemma upperQ_psd {L : ℕ} (hL : 2 ≤ L) : (upperQ L).PosSemidef := by
  have h := (upperT_positive_split hL).2.2.conjTranspose_mul_mul_same (fourierGauge L).conjTranspose
  simpa [upperQ] using h
private lemma upperP_trace {L : ℕ} (hL : 2 ≤ L) :
    (upperP L).trace=(Real.cos (theta L)/Real.sin (theta L):ℂ) := by
  rw [upperP, Matrix.trace_mul_cycle, fourierGauge_unitary (by omega), Matrix.one_mul,
    positiveT_trace hL]
private lemma upperK_split {L : ℕ} (hL : 2 ≤ L) : upperK L=upperP L-upperQ L := by
  have hFF : shiftedFourier L*(shiftedFourier L).conjTranspose=1 :=
    mul_eq_one_comm.mp (shiftedFourier_orthonormal (show 0 < L by omega))
  have hFT : shiftedFourier L*upperT L*(shiftedFourier L).conjTranspose=upperJ L := by
    rw [← shiftedFourier_intertwines (show 0 < L by omega), Matrix.mul_assoc, hFF, Matrix.mul_one]
  unfold upperP upperQ
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, ← (upperT_positive_split hL).1]
  unfold fourierGauge
  rw [Matrix.conjTranspose_mul]
  calc
    upperK L = gaugeD L*(shiftedFourier L*upperT L*(shiftedFourier L).conjTranspose)*(gaugeD L).conjTranspose := by
      rw [hFT]; rfl
    _ = _ := by simp only [Matrix.mul_assoc]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private def pathQuadratic {L : ℕ} (g : Fin (2*L) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ j : Fin (2*L), if h : j.val+1 < 2*L then
    (Complex.I*(pathWeight L j:ℂ)) • (g j*g ⟨j.val+1,h⟩) else 0
private lemma quadratic_upperK {L : ℕ} (g : Fin (2*L) → Matrix ι ι ℂ)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) :
    (1/2:ℂ) • Quadratic g (upperK L)=pathQuadratic g := by
  classical
  have hterm : ∀ j k : Fin (2*L),
      upperK L j k • (g j*g k) =
        (if j.val+1=k.val then (Complex.I*(pathWeight L j:ℂ)) • (g j*g k) else 0) +
        (if k.val+1=j.val then (Complex.I*(pathWeight L k:ℂ)) • (g k*g j) else 0) := by
    intro j k
    rw [upperK, gaugedJ_apply]
    by_cases h1 : j.val+1=k.val
    · have h2 : ¬k.val+1=j.val := by omega
      simp [h1,h2]
    · by_cases h2 : k.val+1=j.val
      · have hne : j ≠ k := by intro h; subst k; omega
        simp [h1,h2,hanti j k hne]
      · simp [h1,h2]
  have he : Quadratic g (upperK L)=pathQuadratic g+pathQuadratic g := by
    unfold Quadratic
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib]
    have hn : (∑ j : Fin (2*L), ∑ k : Fin (2*L), if j.val+1=k.val then
        (Complex.I*(pathWeight L j:ℂ)) • (g j*g k) else 0)=pathQuadratic g := by
      simp_rw [sum_fin_next]
      rfl
    rw [hn, Finset.sum_comm, hn]
  rw [he]
  module
private lemma all_length_majorana_certificate {L : ℕ} (hL : 2 ≤ L)
    (g : Fin (2*L) → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) :
    (((Real.cos (theta L)/Real.sin (theta L):ℂ)) • (1:Matrix ι ι ℂ)-pathQuadratic g).PosSemidef := by
  have h := quadratic_bound_of_positive_split g hsq hg hanti (upperP L) (upperQ L)
    (upperK L) (upperP_psd hL) (upperQ_psd hL) (upperK_split hL)
  rwa [upperP_trace hL, quadratic_upperK g hanti] at h
end
open scoped ComplexOrder
noncomputable section
private def signChain (a : ℕ → Bool) (k : ℕ) : ℂ :=
  ((List.range k).map (fun j => outcomeSign (a j))).prod
private lemma signChain_step (a : ℕ → Bool) (k : ℕ) :
    signChain a (k+1) = signChain a k * outcomeSign (a k) :=
  List.prod_range_succ _ _
private lemma outcomeSign_square (b : Bool) : outcomeSign b*outcomeSign b=1 := by cases b <;> norm_num [outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign]
private lemma outcomeSign_star (b : Bool) : star (outcomeSign b)=outcomeSign b := by cases b <;> simp [outcomeSign, D5.S3.QuantumBounds.MerminMeasurementDependence.boolSign]
private lemma signChain_square (a : ℕ → Bool) (k : ℕ) : signChain a k*signChain a k=1 := by
  induction k with
  | zero => simp [signChain]
  | succ k ih =>
    rw [signChain_step]
    calc
      _ = (signChain a k*signChain a k)*(outcomeSign (a k)*outcomeSign (a k)) := by ring
      _ = 1 := by rw [ih,outcomeSign_square,mul_one]
private lemma signChain_star (a : ℕ → Bool) (k : ℕ) : star (signChain a k)=signChain a k := by
  induction k with
  | zero => simp [signChain]
  | succ k ih => rw [signChain_step,star_mul,outcomeSign_star,ih,mul_comm]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
private def signedMajoranas {L : ℕ} (a : ℕ → Bool) (g : Fin (2*L) → Matrix ι ι ℂ) (j : Fin (2*L)) :=
  signChain a j • g j
private lemma signedMajoranas_relations {L : ℕ} (a : ℕ → Bool) (g : Fin (2*L) → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) :
    (∀ j, signedMajoranas a g j*signedMajoranas a g j=1) ∧
    (∀ j, star (signedMajoranas a g j)=signedMajoranas a g j) ∧
    (∀ j k, j ≠ k → signedMajoranas a g j*signedMajoranas a g k=-(signedMajoranas a g k*signedMajoranas a g j)) := by
  refine ⟨?_,?_,?_⟩
  · intro j; rw [signedMajoranas,smul_mul_smul,signChain_square,hsq,one_smul]
  · intro j; simp only [signedMajoranas,star_smul,signChain_star,hg]
  · intro j k hjk
    simp only [signedMajoranas,smul_mul_smul,hanti j k hjk,smul_neg]
    rw [mul_comm]
private lemma signedMajoranas_bond {L : ℕ} (a : ℕ → Bool) (g : Fin (2*L) → Matrix ι ι ℂ)
    (j : Fin (2*L)) (h : j.val+1 < 2*L) :
    signedMajoranas a g j*signedMajoranas a g ⟨j.val+1,h⟩=
      outcomeSign (a j) • (g j*g ⟨j.val+1,h⟩) := by
  rw [signedMajoranas,signedMajoranas,smul_mul_smul]
  change (signChain a j*signChain a (j.val+1)) • _=_
  rw [signChain_step]
  rw [← mul_assoc,signChain_square,one_mul]
private lemma all_sign_majorana_certificate {L : ℕ} (hL : 2 ≤ L) (a : ℕ → Bool)
    (g : Fin (2*L) → Matrix ι ι ℂ)
    (hsq : ∀ j, g j*g j=1) (hg : ∀ j, star (g j)=g j)
    (hanti : ∀ j k, j ≠ k → g j*g k=-(g k*g j)) :
    (((Real.cos (theta L)/Real.sin (theta L):ℂ)) • (1:Matrix ι ι ℂ)-
      ∑ j : Fin (2*L), if h : j.val+1 < 2*L then
        (outcomeSign (a j)*Complex.I*(pathWeight L j:ℂ)) • (g j*g ⟨j.val+1,h⟩) else 0).PosSemidef := by
  have hr := signedMajoranas_relations a g hsq hg hanti
  have hc := all_length_majorana_certificate hL (signedMajoranas a g) hr.1 hr.2.1 hr.2.2
  have he : pathQuadratic (signedMajoranas a g) =
      ∑ j : Fin (2*L), if h : j.val+1 < 2*L then
        (outcomeSign (a j)*Complex.I*(pathWeight L j:ℂ)) • (g j*g ⟨j.val+1,h⟩) else 0 := by
    unfold pathQuadratic
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with h
    · rw [signedMajoranas_bond a g j h,smul_smul]
      congr 1
      ring
    · rfl
  rwa [he] at hc
end
open  D5.S3.Quantum.FiniteDimensional
open scoped ComplexOrder Kronecker
noncomputable section
def pathDualWeight (n : ℕ) (k : Fin (2*n)) : ℝ := pathWeight (n+1) ((k:ℝ)+1)
def padCompression (d : ℕ) : Matrix ((Fin d × Fin 2) × Fin 2) (Fin d) ℂ :=
  (qubitV (ι:=Fin d × Fin 2) : Matrix ((Fin d × Fin 2) × Fin 2) (Fin d × Fin 2) ℂ) *
    ((qubitV (ι := Fin d)) : Matrix (Fin d × Fin 2) (Fin d) ℂ)
lemma padCompression_isometry (d : ℕ) :
    (padCompression d).conjTranspose*padCompression d=1 := by
  have h := congrArg (fun X : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ =>
    ((qubitV (ι := Fin d))).conjTranspose*X*(qubitV (ι := Fin d))) (qubitV_isometry (ι:=Fin d × Fin 2))
  simpa only [padCompression,Matrix.conjTranspose_mul,Matrix.mul_assoc,Matrix.mul_one,
    (qubitV_isometry (ι := Fin d))] using h
lemma padCompression_compress {d : ℕ} (B : (Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ)) :
    (padCompression d).conjTranspose*(B ⊗ₖ (1:Matrix (Fin 2) (Fin 2) ℂ))*padCompression d=
      ((qubitV (ι := Fin d))).conjTranspose*B*(qubitV (ι := Fin d)) := by
  have h := congrArg (fun X : (Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) => ((qubitV (ι := Fin d))).conjTranspose*X*(qubitV (ι := Fin d)))
    (qubitV_compress B (1:Matrix (Fin 2) (Fin 2) ℂ))
  simpa only [padCompression,Matrix.conjTranspose_mul,Matrix.mul_assoc,Matrix.one_apply,
    ↓reduceIte,one_smul] using h
lemma pathWeight_sine (L : ℕ) (j : ℝ) :
    pathWeight L j=Real.sin (j*theta L)*Real.sin ((j+1)*theta L) := by
  unfold pathWeight
  have h := Real.two_mul_sin_mul_sin (j*theta L) ((j+1)*theta L)
  rw [show j*theta L-(j+1)*theta L= -theta L by ring,Real.cos_neg] at h
  rw [show j*theta L+(j+1)*theta L=(2*j+1)*theta L by ring] at h
  linarith
lemma path_dual_operator_certificate {n d : ℕ} (hn : 1 ≤ n)
    (A : Fin (2*n) → (Matrix (Fin d) (Fin d) ℂ)) (hR : Realization (SimpleGraph.pathGraph (2*n)) A)
    (a : Fin (2*n) → Bool) :
    (((Real.cos (theta (n+1))/Real.sin (theta (n+1)):ℂ)) • (1:(Matrix (Fin d) (Fin d) ℂ))-
      weightedHamiltonian A (pathDualWeight n) a).PosSemidef := by
  classical
  let g := pathMajorana (liftPath (totalPath A)) (liftSeed d)
  have hg := realization_majoranas A hR
  have hanti : ∀ k l, k ≤ 2*n → l ≤ 2*n → k ≠ l → g k*g l=-(g l*g k) := by
    intro k l hk hl hkl
    by_cases hlt : k < l
    · exact hg.2.2.1 l hl k hlt
    · have h := hg.2.2.1 k hk l (by omega)
      simpa using congrArg Neg.neg h.symm
  let pg : Fin (2*n+2) → Matrix ((Fin d × Fin 2) × Fin 2) ((Fin d × Fin 2) × Fin 2) ℂ := paddedMajoranas g
  have hp := paddedMajoranas_relations g hg.1 hg.2.1 hanti
  let aa : ℕ → Bool := fun j => if hj : 0 < j ∧ j-1 < 2*n then a ⟨j-1,hj.2⟩ else false
  have hc := all_sign_majorana_certificate (L:=n+1) (by omega) aa pg hp.1 hp.2.1 hp.2.2
  let H := ∑ j : Fin (2*n+2), if h : j.val+1 < 2*(n+1) then
    (outcomeSign (aa j)*Complex.I*(pathWeight (n+1) j:ℂ)) • (pg j*pg ⟨j.val+1,by omega⟩) else 0
  have hH : (padCompression d).conjTranspose*H*padCompression d=weightedHamiltonian A (pathDualWeight n) a := by
    dsimp only [H]
    rw [Matrix.mul_sum,Matrix.sum_mul]
    rw [Fin.sum_univ_succ,Fin.sum_univ_castSucc]
    have hzero : (outcomeSign (aa 0)*Complex.I*(pathWeight (n+1) 0:ℂ))=0 := by rw [pathWeight_zero]; simp
    simp only [Fin.val_zero,Nat.cast_zero,Fin.val_succ,Fin.val_castSucc,hzero,zero_smul,Matrix.mul_zero,Matrix.zero_mul,
      Fin.val_last,show ¬(2*n+1)+1 < 2*(n+1) by omega,show 1 < 2*(n+1) by omega,↓reduceDIte,zero_add,add_zero]
    unfold weightedHamiltonian
    apply Finset.sum_congr rfl
    intro k hk
    have hkp : 0 < k.val+1 := by omega
    have hkn : k.val+1+1 < 2*(n+1) := by have := k.isLt; omega
    simp only [Fin.val_succ,Fin.val_castSucc,dif_pos hkn]
    rw [Matrix.mul_smul,Matrix.smul_mul]
    change (outcomeSign (aa (k.val+1))*Complex.I*(pathWeight (n+1) ((k.val+1:ℕ):ℝ):ℂ)) •
      ((padCompression d).conjTranspose*(pg (Fin.castSucc k).succ*pg ⟨k.val+1+1,by omega⟩)*padCompression d)=_
    have hbond := paddedMajoranas_bond (m:=2*n) g (Fin.castSucc k).succ hkp hkn
    have hgb := hg.2.2.2 k.val k.isLt
    have he : (padCompression d).conjTranspose*(Complex.I • (pg (Fin.castSucc k).succ*pg ⟨k.val+1+1,by omega⟩))*padCompression d=A k := by
      dsimp only [pg]
      have hidx : (k.val+1)-1=k.val := by omega
      simp only [Fin.val_succ,Fin.val_castSucc,hidx] at hbond
      rw [hbond,hgb,padCompression_compress]
      simp only [liftPath]
      split_ifs <;> rw [qubitV_compress] <;> simp [totalPath,k.isLt,qubitZ]
    have haa : aa (k.val+1)=a k := by simp [aa,show k.val+1-1=k.val by omega,k.isLt]
    rw [haa]
    have he' := congrArg (fun X : (Matrix (Fin d) (Fin d) ℂ) =>
      (outcomeSign (a k)*(pathWeight (n+1) ((k.val+1:ℕ):ℝ):ℂ)) • X) he
    simpa only [Matrix.mul_smul,Matrix.smul_mul,smul_smul,pathDualWeight,Nat.cast_add,Nat.cast_one,
      mul_assoc,mul_comm,mul_left_comm] using he'
  have hcomp := hc.conjTranspose_mul_mul_same (padCompression d)
  have heH : H=∑ j : Fin (2*(n+1)), if h : j.val+1 < 2*(n+1) then
      (outcomeSign (aa j)*Complex.I*(pathWeight (n+1) j:ℂ)) • (pg j*pg ⟨j.val+1,h⟩) else 0 := by rfl
  rw [← heH] at hcomp
  rwa [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,
    padCompression_isometry,hH] at hcomp
end
noncomputable section
private lemma theta_range {L : ℕ} (hL : 2 ≤ L) : 0 < theta L ∧ theta L ≤ Real.pi/4 := by
  have hp := theta_pos (show 0 < L by omega)
  have he := theta_mul_L (show 0 < L by omega)
  have hLR : (2:ℝ)≤ L := by exact_mod_cast hL
  constructor
  · exact hp
  · nlinarith
private lemma theta_sin_cos_pos {L : ℕ} (hL : 2 ≤ L) :
    0 < Real.sin (theta L) ∧ 0 < Real.cos (theta L) := by
  have hr := theta_range hL
  constructor
  · apply Real.sin_pos_of_pos_of_lt_pi hr.1
    linarith [Real.pi_pos]
  · apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
lemma visibility_as_L (n : ℕ) :
    visibility n=1/(((n+1:ℕ):ℝ)*Real.sin (theta (n+1))) := by
  unfold visibility theta
  push_cast
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
lemma visibility_Icc (n : ℕ) (hn : 1 ≤ n) : visibility n∈Set.Icc (0:ℝ) 1 := by
  have hp := theta_sin_cos_pos (L:=n+1) (by omega)
  have hr := theta_range (L:=n+1) (by omega)
  have hLθ := theta_mul_L (L:=n+1) (by omega)
  have hsin := Real.mul_le_sin hr.1.le (show theta (n+1)≤ Real.pi/2 by linarith [Real.pi_pos])
  have hprod : 1≤((n+1:ℕ):ℝ)*Real.sin (theta (n+1)) := by
    have hnR : (0:ℝ)<(n+1:ℕ) := by positivity
    have hh := mul_le_mul_of_nonneg_left hsin hnR.le
    have he : ((n+1:ℕ):ℝ)*(2/Real.pi*theta (n+1))=1 := by
      rw [mul_comm (2/Real.pi), ← mul_assoc, hLθ]
      field_simp
    rw [he] at hh
    exact hh
  rw [visibility_as_L]
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr hprod
lemma visibility_upper_of_weighted {n : ℕ} (hn : 1 ≤ n) (t : ℝ)
    (h : t*(((n+1:ℕ):ℝ)*Real.cos (theta (n+1)))≤
      Real.cos (theta (n+1))/Real.sin (theta (n+1))) : t ≤ visibility n := by
  have hp := theta_sin_cos_pos (L:=n+1) (by omega)
  have h' := mul_le_mul_of_nonneg_right h hp.1.le
  rw [div_mul_cancel₀ _ (ne_of_gt hp.1)] at h'
  have he : (t*((n+1:ℕ):ℝ)*Real.sin (theta (n+1)))*Real.cos (theta (n+1)) =
      (t*(((n+1:ℕ):ℝ)*Real.cos (theta (n+1))))*Real.sin (theta (n+1)) := by ring
  rw [← he] at h'
  have ht : t*((n+1:ℕ):ℝ)*Real.sin (theta (n+1))≤ 1 := by
    exact (mul_le_mul_iff_left₀ hp.2).mp (by simpa using h')
  rw [visibility_as_L]
  apply (le_div_iff₀ (mul_pos (by positivity) hp.1)).mpr
  nlinarith
end
end D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
