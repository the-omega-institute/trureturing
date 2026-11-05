/- GID: D5/S3/QuantumBounds/EnergyConstrainedDeterministicViolation
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/EnergyConstrainedDeterministicViolation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Deterministic entangled devices strictly violate the separable energy bound. -/

import D5.S3.Analytic.Adelic.ReflectedPairCurvatureRayleighIntertwiner
import D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes

/-! Qubit constructions for the energy-constrained prepare-and-measure scenario. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Analytic.Adelic.ReflectedPairCurvatureRayleighIntertwiner (evenChannelState)
open D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity pure_state_handshake)
open D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes (coordinateProjectorTwo)
open D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction
  (trace_projector_overlap)

namespace D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation

/-- Born probabilities for a local channel and a joint binary measurement. -/
def probability {dp ds dm : ℕ}
    (sigma : Matrix (Fin dp × Fin dm) (Fin dp × Fin dm) ℂ)
    (lam : Fin 2 → MatrixMap (Fin dp) (Fin ds) ℂ)
    (povm : Fin 2 → Matrix (Fin ds × Fin dm) (Fin ds × Fin dm) ℂ)
    (b x : Fin 2) : ℝ :=
  (D5.S3.Quantum.FiniteDimensional.bornProbability (povm b)
    (MatrixMap.kron (lam x) LinearMap.id sigma)).re

/-- Every positive energy budget below one half admits a deterministic-input violation. -/
def claim : Prop :=
  ∀ ω : ℝ, 0 < ω → ω < 1 / 2 →
    ∃ (dp ds dm : ℕ) (sigma : Matrix (Fin dp × Fin dm) (Fin dp × Fin dm) ℂ)
      (lam : Fin 2 → MatrixMap (Fin dp) (Fin ds) ℂ)
      (ham : Matrix (Fin ds) (Fin ds) ℂ) (g : Fin ds → ℂ)
      (povm : Fin 2 → Matrix (Fin ds × Fin dm) (Fin ds × Fin dm) ℂ),
      sigma.PosSemidef ∧ sigma.trace = 1 ∧
      (∀ x, (lam x).IsCompletelyPositive ∧ ∀ rho, (lam x rho).trace = rho.trace) ∧
      ham.IsHermitian ∧ star g ⬝ᵥ g = 1 ∧ ham *ᵥ g = 0 ∧
      (ham - (1 - Matrix.vecMulVec g (star g))).PosSemidef ∧
      (∀ b, (povm b).PosSemidef) ∧ povm 0 + povm 1 = 1 ∧
      (∀ x, (Matrix.trace (ham * lam x (partialTraceRight sigma))).re ≤ ω) ∧
      probability sigma lam povm 0 0 = 1 ∧
      probability sigma lam povm 0 1 - probability sigma lam povm 1 1 <
        2 * (1 - 2 * ω) ^ 2 - 1

private def psi (s r q : ℝ) (i : Fin 2 × Fin 2) : ℂ :=
  if i.1 = 0 then if i.2 = 0 then s else 0 else if i.2 = 0 then r else q

private def sigma (s r q : ℝ) := rankOneDensity (psi s r q)

private def kraus (s r q a h : ℝ) (x k : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if x = 0 then if k = 0 then 1 else 0 else
    if k = 0 then !![-(a : ℂ) / s, 0; (h : ℂ) ^ 2 / (s * q), (r : ℂ) / q]
    else !![-(h : ℂ) * r / (s * q), (h : ℂ) / q; 0, 0]

private def channel (s r q a h : ℝ) (x : Fin 2) :=
  MatrixMap.of_kraus (kraus s r q a h x) (kraus s r q a h x)

private def measurement (s r q : ℝ) (b : Fin 2) :=
  if b = 0 then sigma s r q else 1 - sigma s r q

private lemma parameters (ω : ℝ) (hω : 0 < ω) (hω' : ω < 1 / 2) :
    ∃ s r q a h : ℝ, 0 < s ∧ 0 < r ∧ 0 < q ∧ 0 < a ∧ 0 < h ∧
      s ^ 2 = 1 - ω ∧ r ^ 2 + q ^ 2 = ω ∧ q ^ 2 - r ^ 2 = h ^ 2 ∧
      a ^ 2 + h ^ 2 = s ^ 2 ∧ (s * a - 2 * r * q) ^ 2 < (1 - 2 * ω) ^ 2 := by
  let t : ℝ := (1 - 2 * ω) / 8
  have ht : 0 < t ∧ t < 1 / 8 := by dsimp [t]; constructor <;> linarith
  have hsarg : 0 < 1 - ω := by linarith
  have hrarg : 0 < ω * (1 / 2 - t) := mul_pos hω (by linarith)
  have hqarg : 0 < ω * (1 / 2 + t) := mul_pos hω (by linarith)
  have haarg : 0 < 1 - ω - 2 * ω * t := by nlinarith [mul_pos hω (by linarith : 0 < 1 / 2 - t)]
  have hharg : 0 < 2 * ω * t := mul_pos (by linarith) ht.1
  let s := Real.sqrt (1 - ω)
  let r := Real.sqrt (ω * (1 / 2 - t))
  let q := Real.sqrt (ω * (1 / 2 + t))
  let a := Real.sqrt (1 - ω - 2 * ω * t)
  let h := Real.sqrt (2 * ω * t)
  have hs : 0 < s := Real.sqrt_pos.2 hsarg
  have hr : 0 < r := Real.sqrt_pos.2 hrarg
  have hq : 0 < q := Real.sqrt_pos.2 hqarg
  have ha : 0 < a := Real.sqrt_pos.2 haarg
  have hh : 0 < h := Real.sqrt_pos.2 hharg
  have hs2 : s ^ 2 = 1 - ω := Real.sq_sqrt hsarg.le
  have hr2 : r ^ 2 = ω * (1 / 2 - t) := Real.sq_sqrt hrarg.le
  have hq2 : q ^ 2 = ω * (1 / 2 + t) := Real.sq_sqrt hqarg.le
  have ha2 : a ^ 2 = 1 - ω - 2 * ω * t := Real.sq_sqrt haarg.le
  have hh2 : h ^ 2 = 2 * ω * t := Real.sq_sqrt hharg.le
  refine ⟨s, r, q, a, h, hs, hr, hq, ha, hh, hs2, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith
  · let x := s * a
    let y := 2 * r * q
    have hx : 0 < x := mul_pos hs ha
    have hy : 0 < y := mul_pos (mul_pos (by norm_num) hr) hq
    have hx2 : x ^ 2 = (1 - ω) * (1 - ω - 2 * ω * t) := by
      dsimp [x]; rw [mul_pow, hs2, ha2]
    have hy2 : y ^ 2 = ω ^ 2 * (1 - 4 * t ^ 2) := by
      dsimp [y]; rw [mul_pow, mul_pow, hr2, hq2]; ring
    have hxb : 1 - ω - 2 * ω * t ≤ x := by
      have : (1 - ω - 2 * ω * t) ^ 2 ≤ x ^ 2 := by
        nlinarith only [hx2, mul_nonneg (mul_nonneg hω.le ht.1.le) haarg.le]
      exact (sq_le_sq₀ haarg.le hx.le).mp this
    have hyu : y ≤ ω := by
      apply (sq_le_sq₀ hy.le hω.le).mp
      nlinarith only [hy2, sq_nonneg (2 * ω * t)]
    have hxc : x < 1 - ω - ω * t := by
      have hc : 0 < 1 - ω - ω * t := by nlinarith only [haarg, mul_pos hω ht.1]
      apply (sq_lt_sq₀ hx.le hc.le).mp
      nlinarith only [hx2, sq_pos_of_pos (mul_pos hω ht.1)]
    have hyd : ω * (1 - 4 * t ^ 2) ≤ y := by
      have hd : 0 < 1 - 4 * t ^ 2 := by nlinarith only [ht.1, ht.2]
      apply (sq_le_sq₀ (mul_nonneg hω.le hd.le) hy.le).mp
      nlinarith only [hy2, mul_nonneg (sq_nonneg (2 * ω * t)) hd.le]
    have hxy : 0 < x - y := by
      have : 0 < (1 - 2 * ω) * (1 - ω / 4) := mul_pos (by linarith) (by linarith)
      dsimp [t] at hxb
      nlinarith only [hxb, hyu, this]
    have hxy' : x - y < 1 - 2 * ω := by
      have : 0 < ω * t * (1 - 4 * t) := mul_pos (mul_pos hω ht.1) (by linarith)
      nlinarith only [hxc, hyd, this]
    change (x - y) ^ 2 < (1 - 2 * ω) ^ 2
    exact (sq_lt_sq₀ hxy.le (by linarith)).2 hxy'

private lemma state_measurement (s r q : ℝ) (hs : s ^ 2 + r ^ 2 + q ^ 2 = 1) :
    (sigma s r q).PosSemidef ∧ (sigma s r q).trace = 1 ∧
      (∀ b, (measurement s r q b).PosSemidef) ∧
      measurement s r q 0 + measurement s r q 1 = 1 := by
  have hn : psi s r q ⬝ᵥ star (psi s r q) = 1 := by
    delta psi
    unfold dotProduct
    suffices (s : ℂ) * (s : ℂ) + ((r : ℂ) * (r : ℂ) + (q : ℂ) * (q : ℂ)) = 1 by
      simpa [Fintype.sum_prod_type, Fin.sum_univ_two] using this
    exact_mod_cast (by nlinarith [hs] : s * s + (r * r + q * q) = 1)
  have hp := Matrix.posSemidef_vecMulVec_self_star (psi s r q)
  have htrace : (sigma s r q).trace = 1 := by
    rw [sigma, rankOneDensity, Matrix.trace_vecMulVec, hn]
  have hsq : sigma s r q * sigma s r q = sigma s r q := by
    exact (pure_state_handshake (psi s r q) (by rwa [dotProduct_comm]) 1).1
  refine ⟨hp, htrace, ?_, ?_⟩
  · intro b
    delta measurement
    fin_cases b
    · exact hp
    · change (1 - sigma s r q).PosSemidef
      exact Matrix.nonneg_iff_posSemidef.mp
        (show IsStarProjection (sigma s r q) from
          ⟨hsq, hp.isHermitian.isSelfAdjoint⟩).one_sub_nonneg
  · delta measurement
    simp

private lemma kraus_complete (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hqr : q ^ 2 - r ^ 2 = h ^ 2) (ha : a ^ 2 + h ^ 2 = s ^ 2) (x : Fin 2) :
    (∑ k, (kraus s r q a h x k).conjTranspose * kraus s r q a h x k) = 1 := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqr' : (q : ℂ) ^ 2 - (r : ℂ) ^ 2 = (h : ℂ) ^ 2 := by exact_mod_cast hqr
  have ha' : (a : ℂ) ^ 2 + (h : ℂ) ^ 2 = (s : ℂ) ^ 2 := by exact_mod_cast ha
  delta kraus
  ext i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_two, -Matrix.cons_mul] <;>
    field_simp (disch := assumption) <;> ring_nf <;>
    first | linear_combination (q : ℂ) ^ 2 * ha' - (h : ℂ) ^ 2 * hqr'
          | linear_combination -hqr'
          | ring

private lemma channels (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hqr : q ^ 2 - r ^ 2 = h ^ 2) (ha : a ^ 2 + h ^ 2 = s ^ 2) (x : Fin 2) :
    (channel s r q a h x).IsCompletelyPositive ∧
      ∀ rho, (channel s r q a h x rho).trace = rho.trace := by
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive (kraus s r q a h x), ?_⟩
  obtain ⟨c, hc⟩ := finite_kraus_quantum_channel (kraus s r q a h x)
    (kraus_complete s r q a h hs hq hqr ha x)
  intro rho
  change (MatrixMap.of_kraus (kraus s r q a h x) (kraus s r q a h x) rho).trace = _
  unfold MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hc rho]
  exact c.trace_preserving (CStarMatrix.ofMatrix rho)

private lemma ground_energy : (coordinateProjectorTwo 1).IsHermitian ∧
    star evenChannelState ⬝ᵥ evenChannelState = 1 ∧
    (coordinateProjectorTwo 1) *ᵥ evenChannelState = 0 ∧
    ((coordinateProjectorTwo 1) -
      (1 - Matrix.vecMulVec evenChannelState (star evenChannelState))).PosSemidef := by
  have hh : (coordinateProjectorTwo 1).IsHermitian :=
    (D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes.coordinateContextTwo.rankOne 1).1
  have hz : (coordinateProjectorTwo 1) *ᵥ evenChannelState = 0 := by
    ext i
    change (∑ j, (coordinateProjectorTwo 1) i j * evenChannelState j) = 0
    delta coordinateProjectorTwo evenChannelState
    fin_cases i <;> norm_num [Fin.sum_univ_two]
  have hp : (coordinateProjectorTwo 1) -
      (1 - Matrix.vecMulVec evenChannelState (star evenChannelState)) = 0 := by
    ext i j
    change (coordinateProjectorTwo 1) i j - ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j -
      evenChannelState i * star (evenChannelState j)) = 0
    delta coordinateProjectorTwo evenChannelState
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.one_apply]
  refine ⟨hh, ?_, hz, ?_⟩
  · exact D5.S3.Quantum.Information.SeparableStateLocalUnitaryStabilizerObstruction.unit_e0
  · rw [hp]; exact Matrix.PosSemidef.zero

private lemma energies (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hqr : q ^ 2 - r ^ 2 = h ^ 2) (x : Fin 2) :
    (Matrix.trace ((coordinateProjectorTwo 1) * channel s r q a h x
      (partialTraceRight (sigma s r q)))).re = r ^ 2 + q ^ 2 := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqr' : (h : ℂ) ^ 2 = (q : ℂ) ^ 2 - (r : ℂ) ^ 2 := by exact_mod_cast hqr.symm
  have hc : Matrix.trace ((coordinateProjectorTwo 1) * channel s r q a h x
      (partialTraceRight (sigma s r q))) = ((r ^ 2 + q ^ 2 : ℝ) : ℂ) := by
    unfold channel MatrixMap.of_kraus
    simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    unfold Matrix.trace partialTraceRight
    simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.sum_apply,
      Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
    delta coordinateProjectorTwo kraus sigma rankOneDensity psi
    fin_cases x <;>
      simp [Matrix.vecMulVec_apply,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_two,
        -Matrix.cons_mul] <;>
      push_cast <;> (try simp only [hqr']) <;> field_simp (disch := assumption) <;> ring
  rw [hc]
  exact Complex.ofReal_re _

private lemma local_action {dp ds dm : ℕ}
    (lam : MatrixMap (Fin dp) (Fin ds) ℂ)
    (rho : Matrix (Fin dp × Fin dm) (Fin dp × Fin dm) ℂ)
    (i j : Fin ds) (k l : Fin dm) :
    MatrixMap.kron lam LinearMap.id rho (i, k) (j, l) =
      lam (fun u v => rho (u, k) (v, l)) i j := by
  exact D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence.kron_id_apply
    lam dm rho (i, k) (j, l)

private lemma joint_output (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hqr : q ^ 2 - r ^ 2 = h ^ 2) (x : Fin 2) :
    MatrixMap.kron (channel s r q a h x) LinearMap.id (sigma s r q) =
      if x = 0 then sigma s r q else
        sigma (-a) q r + Matrix.single (0, 1) (0, 1) ((h : ℂ) ^ 2) := by
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hh : (h : ℂ) ^ 2 = (q : ℂ) ^ 2 - (r : ℂ) ^ 2 := by exact_mod_cast hqr.symm
  ext ⟨i, k⟩ ⟨j, l⟩
  rw [local_action]
  unfold channel MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  delta kraus sigma rankOneDensity psi
  fin_cases x <;> fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.vecMulVec_apply, Matrix.single_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
      Fin.sum_univ_two, -Matrix.cons_mul] <;>
    (try simp only [hh]) <;> field_simp (disch := assumption) <;>
    first | assumption | (simp; done) | ring

private lemma probabilities (s r q a h : ℝ) (hs : s ≠ 0) (hq : q ≠ 0)
    (hn : s ^ 2 + r ^ 2 + q ^ 2 = 1) (hqr : q ^ 2 - r ^ 2 = h ^ 2) (ha : a ^ 2 + h ^ 2 = s ^ 2) :
    probability (sigma s r q) (channel s r q a h) (measurement s r q) 0 0 = 1 ∧
    probability (sigma s r q) (channel s r q a h) (measurement s r q) 0 1 =
      (s * a - 2 * r * q) ^ 2 ∧
    probability (sigma s r q) (channel s r q a h) (measurement s r q) 1 1 =
      1 - (s * a - 2 * r * q) ^ 2 := by
  have hn' : (s : ℂ) ^ 2 + (r : ℂ) ^ 2 + (q : ℂ) ^ 2 = 1 := by exact_mod_cast hn
  have ha' : (a : ℂ) ^ 2 + (h : ℂ) ^ 2 = (s : ℂ) ^ 2 := by exact_mod_cast ha
  have hp (b x : Fin 2) :
      Matrix.trace (measurement s r q b * MatrixMap.kron (channel s r q a h x)
        LinearMap.id (sigma s r q)) =
      if x = 0 then (if b = 0 then 1 else 0) else
        if b = 0 then ((s * a - 2 * r * q) ^ 2 : ℝ) else (1 - (s * a - 2 * r * q) ^ 2 : ℝ) := by
    rw [joint_output s r q a h hs hq hqr]
    delta measurement
    fin_cases b <;> fin_cases x <;>
      simp only [Fin.isValue, ↓reduceIte, one_ne_zero, Matrix.sub_mul, Matrix.mul_add,
        Matrix.one_mul, Matrix.trace_add, Matrix.trace_sub, sigma, trace_projector_overlap] <;>
      unfold rankOneDensity Matrix.trace <;>
      delta psi <;>
      simp [dotProduct, Complex.normSq_apply, Matrix.vecMulVec_apply, Matrix.single_apply,
        Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two] <;> push_cast <;>
      first | linear_combination ((s : ℂ) ^ 2 + (r : ℂ) ^ 2 + (q : ℂ) ^ 2 + 1) * hn'
            | linear_combination -((s : ℂ) ^ 2 + (r : ℂ) ^ 2 + (q : ℂ) ^ 2) * hn'
            | linear_combination hn' + ha'
            | linear_combination hn'
            | ring
  have hp00 := congrArg Complex.re (hp 0 0)
  have hp01 := congrArg Complex.re (hp 0 1)
  have hp11 := congrArg Complex.re (hp 1 1)
  delta probability D5.S3.Quantum.FiniteDimensional.bornProbability
  simpa only [↓reduceIte, one_ne_zero, Complex.one_re,
    Complex.ofReal_re] using And.intro hp00 (And.intro hp01 hp11)

/-- Qubit channels attain the strict violation for every energy budget in the open interval. -/
theorem result : claim := by
  intro ω hω hω'
  obtain ⟨s, r, q, a, h, hs, hr, hq, ha, hh, hs2, hrq, hqr, has, hv⟩ :=
    parameters ω hω hω'
  have hn : s ^ 2 + r ^ 2 + q ^ 2 = 1 := by linarith
  obtain ⟨hd, ht, hp, hm⟩ := state_measurement s r q hn
  obtain ⟨he, hg, hzero, hgap⟩ := ground_energy
  obtain ⟨hp0, hp1, hp2⟩ := probabilities s r q a h hs.ne' hq.ne' hn hqr has
  refine ⟨2, 2, 2, sigma s r q, channel s r q a h, (coordinateProjectorTwo 1), evenChannelState,
    measurement s r q, hd, ht, channels s r q a h hs.ne' hq.ne' hqr has,
    he, hg, hzero, hgap, hp, hm, ?_, hp0, ?_⟩
  · intro x
    rw [energies s r q a h hs.ne' hq.ne' hqr x, hrq]
  · rw [hp1, hp2]
    linarith

end D5.S3.QuantumBounds.EnergyConstrainedDeterministicViolation
