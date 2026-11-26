/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalPureScore
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalPureScore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic expansion and quantitative pure-mode bounds for the quarter-turn potential. -/

import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalGeometry

/-! The pure Fourier score and the norm estimates for its cubic expansion. -/

noncomputable section

open Real Quaternion
open scoped Quaternion InnerProductSpace

namespace RoundQuaternionLocalSharpness

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (inner_eq_components)

local notation "U" => unitary ℍ[ℝ]

def localT : ℝ := Real.sqrt 3 / 3
def localS : ℝ := Real.sqrt 2 * Real.sqrt 3 / 3
def localAlpha : ℝ := Real.sqrt 3 / 12
def localLinear : ℝ := Real.sqrt 2 * Real.sqrt 3 / 6
private def localInvS : ℝ := Real.sqrt 2 * Real.sqrt 3 / 4

private theorem local_constant_squares :
    localT ^ 2 = 1/3 ∧ localS ^ 2 = 2/3 ∧ localAlpha ^ 2 = 1/48 ∧
      localLinear ^ 2 = 1/6 ∧ localInvS ^ 2 = 3/8 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  norm_num [localT, localS, localAlpha, localLinear, localInvS, div_pow, mul_pow, h2, h3]

private theorem local_constant_values :
    localT = 1 / Real.sqrt 3 ∧ localS = Real.sqrt (2/3) ∧ localLinear = 1 / Real.sqrt 6 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · apply (eq_div_iff (by positivity : Real.sqrt 3 ≠ 0)).2
    unfold localT
    nlinarith
  · have hs : (Real.sqrt (2/3)) ^ 2 = 2/3 := Real.sq_sqrt (by norm_num)
    nlinarith [local_constant_squares.2.1, show 0 ≤ localS by unfold localS; positivity,
      Real.sqrt_nonneg (2/3)]
  · apply (eq_div_iff (by positivity : Real.sqrt 6 ≠ 0)).2
    have h := local_constant_squares.2.2.2.1
    have hsq : (localLinear * Real.sqrt 6)^2 = 1 := by rw [mul_pow, h, h6]; norm_num
    nlinarith [show 0 ≤ localLinear * Real.sqrt 6 by unfold localLinear; positivity]

private theorem local_constant_bounds :
    577/1000 < localT ∧ localT < 5774/10000 ∧ 815/1000 < localS ∧ localS < 817/1000 ∧
    0 < localAlpha ∧ localAlpha < 145/1000 ∧ 408/1000 < localLinear ∧
    localLinear < 409/1000 := by
  obtain ⟨hT, hS, hα, hL, _⟩ := local_constant_squares
  have ht : 0 < localT := by unfold localT; positivity
  have hs : 0 < localS := by unfold localS; positivity
  have ha : 0 < localAlpha := by unfold localAlpha; positivity
  have hl : 0 < localLinear := by unfold localLinear; positivity
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, ha,
    by nlinarith, by nlinarith, by nlinarith⟩


def localB (p : ℂ) (j : Fin 3) : ℝ :=
  localLinear * (p * rimPhase (rimPrev j)).re
private def localTau (p : ℂ) (j : Fin 3) : ℝ := Real.sqrt 3 * localB p j

private def localF (p : ℂ) (j : Fin 3) : ℝ :=
  let x := p.re
  let y := p.im
  ![Real.sqrt 3 * (x ^ 2 - y ^ 2) / 96 + x*y/16,
    Real.sqrt 3 * (x ^ 2 - y ^ 2) / 96 - x*y/16,
    -Real.sqrt 3 * (x ^ 2 - y ^ 2) / 48] j

private def localPsi (p : ℂ) (j : Fin 3) : ℝ := localF p j - localF p (rimPrev j)
private def localFibre (p : ℂ) (j : Fin 3) : ℝ := localS * (localTau p j + localPsi p j)
def localReal (p q : ℂ) : ℝ := localT + localLinear * ‖q‖ - localAlpha * ‖p‖^2
def localRadicand (p q : ℂ) (j : Fin 3) : ℝ :=
  1 - localReal p q ^ 2 - localB p j ^ 2 - localFibre p j ^ 2

def localRim (p q : ℂ) (j : Fin 3) : ℍ[ℝ] :=
  quatPair ⟨localReal p q, localB p j⟩
    (rimPhase j * ⟨Real.sqrt (localRadicand p q j), localFibre p j⟩)

private theorem local_rim_unit (p q : ℂ) (j : Fin 3) (h : 0 ≤ localRadicand p q j) :
    normSq (localRim p q j) = 1 := by
  simp only [localRim, local_normSq_pair, norm_mul, local_phase_norm, one_mul,
    local_sq_complex]
  rw [Real.sq_sqrt h, localRadicand]
  ring

def localUnitRim (p q : ℂ) (j : Fin 3) : U :=
  if h : 0 ≤ localRadicand p q j then asUnit (localRim p q j) (local_rim_unit p q j h)
  else 1

/-- The hub potential is \(1\). The rim potentials use the phased transverse coordinates. -/
def phasedPotential (p q : ℂ) : Fin 4 → U :=
  ![1, localUnitRim p q 0, localUnitRim p q 1, localUnitRim p q 2]

private theorem local_b_bound (p : ℂ) (j : Fin 3) : |localB p j| ≤ localLinear * ‖p‖ := by
  have h := Complex.abs_re_le_norm (p * rimPhase (rimPrev j))
  rw [norm_mul, local_phase_norm, mul_one] at h
  have hl : 0 ≤ localLinear := by unfold localLinear; positivity
  simpa only [localB, abs_mul, abs_of_nonneg hl] using mul_le_mul_of_nonneg_left h hl

private theorem local_psi_bound (p : ℂ) (j : Fin 3) : |localPsi p j| ≤ ‖p‖ ^ 2 / 16 := by
  let x := p.re
  let y := p.im
  let a := x ^ 2 - y ^ 2
  let b := 2*x*y
  have h : a ^ 2 + b ^ 2 = ‖p‖ ^ 4 := by
    rw [show ‖p‖ ^ 4 = (‖p‖ ^ 2) ^ 2 by ring, Complex.sq_norm, Complex.normSq_apply]
    dsimp [a, b, x, y]
    ring
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have bound (c d : ℝ) (hc : c ^ 2 + d ^ 2 = (1/16 : ℝ) ^ 2) :
      |c*a + d*b| ≤ ‖p‖^2/16 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
    rw [sq_abs]
    nlinarith [sq_nonneg (c*b-d*a), congrArg₂ (· * ·) hc h]
  fin_cases j
  · convert bound (Real.sqrt 3 / 32) (1/32) (by rw [div_pow, h3]; norm_num) using 1
    congr 1
    norm_num [localPsi, localF, rimPrev, a, b, x, y]
    ring
  · convert bound 0 (-1/16) (by norm_num) using 1
    congr 1
    norm_num [localPsi, localF, rimPrev, a, b, x, y]
    ring
  · convert bound (-Real.sqrt 3 / 32) (1/32) (by rw [div_pow, neg_pow, h3]; norm_num) using 1
    congr 1
    norm_num [localPsi, localF, rimPrev, a, b, x, y]
    ring


private theorem local_b_sq (p : ℂ) (j : Fin 3) : localB p j ^ 2 ≤ ‖p‖ ^ 2 / 6 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (by unfold localLinear; positivity)).2
    (local_b_bound p j)
  rw [sq_abs, mul_pow, local_constant_squares.2.2.2.1] at h
  nlinarith only [h]

private theorem local_psi_sq (p : ℂ) (j : Fin 3) : localPsi p j ^ 2 ≤ ‖p‖ ^ 4 / 256 := by
  have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (local_psi_bound p j)
  rw [sq_abs] at h
  calc
    _ ≤ (‖p‖ ^ 2 / 16) ^ 2 := h
    _ = _ := by ring

private theorem local_tau_bound (p : ℂ) (j : Fin 3) : |localTau p j| ≤ (71/100) * ‖p‖ := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
  rw [sq_abs, localTau, mul_pow, hs]
  calc
    _ ≤ 3 * (‖p‖^2/6) := by gcongr; exact local_b_sq p j
    _ ≤ _ := by nlinarith [sq_nonneg ‖p‖]

private theorem local_cross (p : ℂ) (j : Fin 3) :
    |2 * localS^2 * localTau p j * localPsi p j| ≤ (3/50) * ‖p‖^3 := by
  rw [local_constant_squares.2.1]
  calc
    _ = (4/3) * |localTau p j| * |localPsi p j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2 * (2/3))]
      ring
    _ ≤ (4/3) * ((71/100) * ‖p‖) * (‖p‖^2/16) := by
      gcongr
      · exact local_tau_bound p j
      · exact local_psi_bound p j
    _ ≤ _ := by nlinarith [show 0 ≤ ‖p‖^3 by positivity]

private theorem local_fibre_sq (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    localB p j ^ 2 + localFibre p j ^ 2 ≤ (51/100) * ‖p‖^2 := by
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : localB p j ^ 2 + localFibre p j ^ 2 = 3 * localB p j ^ 2 +
      2 * localS^2 * localTau p j * localPsi p j + (2/3) * localPsi p j ^ 2 := by
    have hτ : localTau p j ^ 2 = 3 * localB p j ^ 2 := by rw [localTau, mul_pow, h3]
    simp only [localFibre, mul_pow, local_constant_squares.2.1, add_sq, hτ]
    ring
  unfold localR at hp
  rw [he]
  have hp3 : ‖p‖^3 ≤ (3/50) * ‖p‖^2 := by
    rw [pow_succ, mul_comm (‖p‖ ^ 2)]
    gcongr
  have hp4 : ‖p‖^4 ≤ (3/50)^2 * ‖p‖^2 := by
    rw [show ‖p‖^4 = ‖p‖^2 * ‖p‖^2 by ring]
    gcongr
  have hcross := (abs_le.mp (local_cross p j)).2
  nlinarith only [local_b_sq p j, local_psi_sq p j, hcross, hp3, hp4, sq_nonneg ‖p‖]

private theorem local_real_bounds (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) :
    0 < localReal p q ∧ localReal p q < 603/1000 := by
  obtain ⟨htl, htu, _, _, hα, hαu, hll, hlu⟩ := local_constant_bounds
  have hprod : localLinear * ‖q‖ ≤ (409/1000) * localR := by gcongr
  have hprod' : localAlpha * ‖p‖^2 ≤ (145/1000) * localR^2 := by gcongr
  unfold localReal localR at *
  exact ⟨by linarith [mul_nonneg (by linarith : 0 ≤ localLinear) (norm_nonneg q)],
    by linarith [mul_nonneg hα.le (sq_nonneg ‖p‖)]⟩

private theorem local_radicand_bound (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR)
    (j : Fin 3) : (795/1000)^2 < localRadicand p q j := by
  obtain ⟨ha, ha'⟩ := local_real_bounds p q hp hq
  have hs := (sq_lt_sq₀ ha.le (by norm_num : 0 ≤ (603/1000:ℝ))).2 ha'
  have hp' := (sq_le_sq₀ (norm_nonneg p) (by unfold localR; positivity)).2 hp
  have hb := local_fibre_sq p hp j
  unfold localRadicand
  norm_num [localR] at hp'
  linarith

private theorem local_unit_rim_coe (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR)
    (j : Fin 3) : ((localUnitRim p q j : U) : ℍ[ℝ]) = localRim p q j := by
  rw [localUnitRim, dite_eq_left ((by norm_num : (0:ℝ) ≤ (795/1000)^2).trans
    (local_radicand_bound p q hp hq j).le)]
  rfl


/-- The first four terms of (3), graded by degree in \(p\). -/
def localRimTerm (p : ℂ) (j : Fin 3) (i : Fin 4) : ℍ[ℝ] :=
  ![quatPair ⟨localT, 0⟩ (rimPhase j * ⟨localS, 0⟩),
    quatPair ⟨0, localB p j⟩ (rimPhase j * ⟨0, localS * localTau p j⟩),
    quatPair ⟨-localAlpha * ‖p‖^2, 0⟩
      (rimPhase j * ⟨localInvS * (‖p‖^2/6 - 3*localB p j^2), localS * localPsi p j⟩),
    quatPair 0 (rimPhase j * ⟨-localS * localTau p j * localPsi p j, 0⟩)] i

def localAxis : ℍ[ℝ] := quatPair Complex.I 0
def localGainPure (p : ℂ) (j : Fin 3) : ℍ[ℝ] :=
  quatPair ⟨0, Real.sqrt (1-‖p‖^2)⟩ (p * star (rimPhase j))

private def localGainTerm (p : ℂ) (j : Fin 3) (i : Fin 4) : ℍ[ℝ] :=
  ![localAxis, quatPair 0 (p * star (rimPhase j)), quatPair ⟨0,-‖p‖^2/2⟩ 0, quatPair 0 0] i

private def localPureCubic (p : ℂ) (j : Fin 3) : ℝ :=
  let x := p.re
  let y := p.im
  ![(-3*Real.sqrt 2*x*‖p‖^2 + Real.sqrt 2*Real.sqrt 3*(23*x^2*y-9*y^3))/128,
    (3*Real.sqrt 2*x*‖p‖^2 + Real.sqrt 2*Real.sqrt 3*(23*x^2*y-9*y^3))/128,
    Real.sqrt 2*Real.sqrt 3*(13*x^2*y-3*y^3)/64] j

def localScore (x g y : ℍ[ℝ]) : ℝ := ⟪x*g, y⟫_ℝ

private theorem local_pair_score (z h g w z' h' : ℂ) :
    localScore (quatPair z h) (quatPair g w) (quatPair z' h') =
      ((z*g-h*star w)*star z' + (z*w+h*star g)*star h').re := by
  simp [localScore, quatPair, inner_eq_components, Quaternion.re_mul, Quaternion.imI_mul,
    Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im, Complex.star_def]
  ring

private theorem local_abs_score (x g y : ℍ[ℝ]) :
    |localScore x g y| ≤ ‖x‖*‖g‖*‖y‖ := by
  simpa only [localScore, norm_mul] using abs_real_inner_le_norm (x*g) y

private theorem local_root_powers (n : ℕ) (k : ℝ) (hk : 0 ≤ k) :
    Real.sqrt k ^ (2*n) = k ^ n := by rw [pow_mul, Real.sq_sqrt hk]

private theorem local_reduce_root_pow (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (_ : 2 ≤ n) :
    Real.sqrt k ^ n = k ^ (n / 2) * Real.sqrt k ^ (n % 2) := by
  calc
    _ = Real.sqrt k ^ (2 * (n / 2) + n % 2) := by congr 1; omega
    _ = _ := by rw [pow_add, local_root_powers _ _ hk]

private theorem local_pure_terms (p : ℂ) (j : Fin 3) :
    (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, if a.val+b.val+c.val < 4 then
      localScore (localRimTerm p j a) (localGainTerm p j b) (localRimTerm p (rimNext j) c)
       else 0) = localT - localAlpha*‖p‖^2 + localPureCubic p j := by
  fin_cases j <;>
    norm_num [Fin.sum_univ_succ, localRimTerm, localGainTerm, local_pair_score, localAxis,
      localPureCubic,
      localT, localS, localAlpha, localLinear, localInvS, localB, localTau, localPsi, localF,
      rimNext, rimPrev, rimPhase, zeta, Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.sq_norm, Complex.normSq_apply] <;>
    ring_nf <;>
    simp (disch := omega) [local_reduce_root_pow 2 (by norm_num),
      local_reduce_root_pow 3 (by norm_num)] <;> ring

private theorem local_cubic_monomial (p : ℂ) : |p.re ^ 2 * p.im| ≤ (2/5)*‖p‖^3 := by
  let x := p.re
  let y := p.im
  have hp : ‖p‖^2 = x^2+y^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [x,y]
    ring
  have h : 0 ≤ (x^2-2*y^2)^2 * (4*x^2+y^2) := by positivity
  have h' : ‖p‖^6 = (x^2+y^2)^3 := by rw [show ‖p‖^6 = (‖p‖^2)^3 by ring, hp]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).1
  rw [sq_abs]
  change (x^2*y)^2 ≤ _
  nlinarith only [h, h', show 0 ≤ ‖p‖^6 by positivity]

private theorem local_cubic_bound (p : ℂ) (j : Fin 3) :
    |localPureCubic p j| ≤ (2/5)*‖p‖^3 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have r2 : Real.sqrt 2 ≤ 1415/1000 := by nlinarith [Real.sqrt_nonneg 2]
  have r6 : Real.sqrt 2 * Real.sqrt 3 ≤ 49/20 := by
    have h : (Real.sqrt 2 * Real.sqrt 3)^2 = 6 := by rw [mul_pow, h2, h3]; norm_num
    nlinarith [show 0 ≤ Real.sqrt 2 * Real.sqrt 3 by positivity]
  have hx : |p.re*‖p‖^2| ≤ ‖p‖^3 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg ‖p‖), show ‖p‖^3 = ‖p‖*‖p‖^2 by ring]
    exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm p) (sq_nonneg _)
  have hy : |p.im^3| ≤ ‖p‖^3 := by
    rw [abs_pow]
    gcongr
    exact Complex.abs_im_le_norm p
  have hxy := local_cubic_monomial p
  have hxy' : |23*p.re^2*p.im-9*p.im^3| ≤ (23*(2/5)+9)*‖p‖^3 := by
    calc
      _ ≤ |23*p.re^2*p.im| + |9*p.im^3| := abs_sub _ _
      _ = 23*|p.re^2*p.im| + 9*|p.im^3| := by rw [mul_assoc 23]; norm_num [abs_mul]
      _ ≤ _ := by linarith
  have hxy'' : |13*p.re^2*p.im-3*p.im^3| ≤ (13*(2/5)+3)*‖p‖^3 := by
    calc
      _ ≤ |13*p.re^2*p.im| + |3*p.im^3| := abs_sub _ _
      _ = 13*|p.re^2*p.im| + 3*|p.im^3| := by rw [mul_assoc 13]; norm_num [abs_mul]
      _ ≤ _ := by linarith
  have hX : |3*Real.sqrt 2*(p.re*‖p‖^2)| ≤ (3*(1415/1000))*‖p‖^3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 3*Real.sqrt 2)]
    gcongr
  have hY : |(Real.sqrt 2*Real.sqrt 3)*(23*p.re^2*p.im-9*p.im^3)| ≤
      ((49/20)*(23*(2/5)+9))*‖p‖^3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2*Real.sqrt 3)]
    calc
      _ ≤ (49/20)*((23*(2/5)+9)*‖p‖^3) := by gcongr
      _ = _ := by ring
  have hZ : |(Real.sqrt 2*Real.sqrt 3)*(13*p.re^2*p.im-3*p.im^3)| ≤
      ((49/20)*(13*(2/5)+3))*‖p‖^3 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt 2*Real.sqrt 3)]
    calc
      _ ≤ (49/20)*((13*(2/5)+3)*‖p‖^3) := by gcongr
      _ = _ := by ring
  let X := 3*Real.sqrt 2*(p.re*‖p‖^2)
  let Y := (Real.sqrt 2*Real.sqrt 3)*(23*p.re^2*p.im-9*p.im^3)
  let Z := (Real.sqrt 2*Real.sqrt 3)*(13*p.re^2*p.im-3*p.im^3)
  fin_cases j
  · change |localPureCubic p 0| ≤ _
    rw [show localPureCubic p 0 = (-X+Y)/128 by simp [localPureCubic,X,Y]; ring]
    have h := abs_add_le (-X) Y
    rw [abs_neg] at h
    change |X| ≤ _ at hX
    change |Y| ≤ _ at hY
    norm_num [abs_div]
    linarith only [h, hX, hY, show 0 ≤ ‖p‖^3 by positivity]
  · change |localPureCubic p 1| ≤ _
    rw [show localPureCubic p 1 = (X+Y)/128 by simp [localPureCubic,X,Y]; ring]
    change |X| ≤ _ at hX
    change |Y| ≤ _ at hY
    norm_num [abs_div]
    linarith only [abs_add_le X Y, hX, hY, show 0 ≤ ‖p‖^3 by positivity]
  · change |Z/64| ≤ _
    change |Z| ≤ _ at hZ
    norm_num [abs_div]
    linarith only [hZ, show 0 ≤ ‖p‖^3 by positivity]


private theorem local_second_bound (p : ℂ) (j : Fin 3) :
    |‖p‖^2/6-3*localB p j^2| ≤ ‖p‖^2/3 := by
  rw [abs_le]
  constructor <;> nlinarith only [local_b_sq p j, sq_nonneg (localB p j), sq_nonneg ‖p‖]

private theorem local_higher_powers (P : ℝ) (hP : 0 ≤ P) (hp : P ≤ localR) :
    P^3 ≤ localR * P^2 ∧ P^4 ≤ localR ^ 2 * P^2 := by
  constructor
  · rw [pow_succ, mul_comm (P^2)]
    gcongr
  · rw [show P^4 = P^2*P^2 by ring]
    gcongr

private theorem local_pure_radical (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    let h := Real.sqrt (localRadicand p 0 j)
    let H₂ := ‖p‖^2/6-3*localB p j^2
    4/5 < h ∧ |h-localS| ≤ (213/1000)*‖p‖^2 ∧
      |h-(localS + localInvS*H₂ - localS*localTau p j*localPsi p j)| ≤
      (5/100)*‖p‖^4 := by
  dsimp only
  let P := ‖p‖
  let h := Real.sqrt (localRadicand p 0 j)
  let H₂ := P^2/6-3*localB p j^2
  let H₃ := -2*localS^2*localTau p j*localPsi p j
  let H₄ := -localAlpha^2 * P^4 - localS^2 * localPsi p j^2
  let H := H₂+H₃+H₄
  obtain ⟨htsq, hssq, hasq, _, hisq⟩ := local_constant_squares
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hτα : localTau p j ^ 2 = 3*localB p j ^ 2 := by rw [localTau, mul_pow, h3]
  have hα : 2*localT*localAlpha = 1/6 := by
    unfold localT localAlpha
    nlinarith only [h3]
  have hinv : 2*localS*localInvS = 1 := by
    unfold localS localInvS
    have h := local_constant_squares.2.1
    unfold localS at h
    nlinarith only [h]
  have hh : h^2 = localS^2 + H := by
    dsimp only [h, H, H₂, H₃, H₄, P]
    rw [Real.sq_sqrt (by linarith [local_radicand_bound p 0 hp (by norm_num [localR]) j])]
    simp only [localRadicand, localFibre, localReal, norm_zero, mul_zero, add_zero, mul_pow]
    rw [show (localTau p j + localPsi p j)^2 = 3*localB p j^2 +
      2*localTau p j*localPsi p j + localPsi p j^2 by rw [add_sq, hτα]]
    linear_combination -htsq - hssq + ‖p‖^2*hα - 3*localB p j^2*hssq
  have h₄ : |H₄| ≤ P^4/40 := by
    dsimp only [H₄]
    rw [hasq, hssq, abs_le]
    have hP : 0 ≤ P^4 := by positivity
    have hψ := sq_nonneg (localPsi p j)
    have hψ' : localPsi p j ^ 2 ≤ P^4/256 := local_psi_sq p j
    constructor <;> linarith only [hP, hψ, hψ']
  have h₂ := local_second_bound p j
  have h₃ : |H₃| ≤ (3/50)*P^3 := by
    dsimp only [H₃, P]
    rw [show -2 * localS^2 * localTau p j*localPsi p j =
      -(2 * localS^2 * localTau p j*localPsi p j) by ring, abs_neg]
    exact local_cross p j
  obtain ⟨hp3, hp4⟩ := local_higher_powers P (norm_nonneg p) hp
  have hH : |H| ≤ (34/100)*P^2 := by
    have hh' := (abs_add_le (H₂+H₃) H₄).trans (add_le_add_left (abs_add_le H₂ H₃) |H₄|)
    norm_num [localR] at hp3 hp4
    nlinarith only [hh', h₂, h₃, h₄, hp3, hp4, sq_nonneg P]
  have hs : (4/5:ℝ) < localS := lt_trans (by norm_num) local_constant_bounds.2.2.1
  have hh' : (4/5:ℝ) < h := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
    rw [hh, hssq]
    have hp' := (sq_le_sq₀ (norm_nonneg p) (by unfold localR; positivity)).2 hp
    norm_num [localR] at hp'
    linarith [(abs_le.mp hH).1]
  refine ⟨hh', ?_, ?_⟩
  · change |h-localS| ≤ _
    have ht : (h-localS)*(h+localS) = H := by nlinarith only [hh]
    rw [(eq_div_iff (by positivity : h+localS ≠ 0)).2 ht, abs_div,
      abs_of_nonneg (by positivity : 0 ≤ h+localS)]
    calc
      _ ≤ ((34/100)*P^2)/(8/5) := div_le_div₀ (by positivity) hH (by norm_num) (by linarith)
      _ ≤ _ := by nlinarith only [sq_nonneg P]
  have hden : 0 < 2*localS*(h+localS)^2 := by positivity
  have htaylor : h - (localS + localInvS*H₂ - localS*localTau p j*localPsi p j) =
      localInvS*H₄ - H^2/(2*localS*(h+localS)^2) := by
    have hsmall : (h-localS)*(h+localS) = H := by nlinarith only [hh]
    have hex : -localS*localTau p j*localPsi p j = localInvS*H₃ := by
      dsimp only [H₃]
      linear_combination localS*localTau p j*localPsi p j*hinv
    rw [show localS + localInvS*H₂ - localS*localTau p j*localPsi p j =
      localS + localInvS*H₂ + localInvS*H₃ by linarith only [hex]]
    have hp' : H^2 = ((h-localS)*(h+localS))^2 := congrArg (· ^ (2:ℕ)) hsmall.symm
    rw [hp', mul_pow, mul_div_mul_right _ _ (by positivity : (h+localS)^2 ≠ 0)]
    rw [show (h-localS)^2/(2*localS) = localInvS*(h-localS)^2 by
      apply (div_eq_iff (by positivity)).2
      linear_combination -(h-localS)^2*hinv]
    linear_combination localInvS*hsmall - (h-localS)*hinv
  change |h-_| ≤ _
  rw [htaylor]
  have hi : localInvS ≤ 5/8 := by nlinarith only [hisq, show 0 ≤ localInvS by unfold localInvS; positivity]
  have hab4 : |localInvS*H₄| ≤ (5/8)*(P^4/40) := by
    rw [abs_mul, abs_of_nonneg (by unfold localInvS; positivity)]
    gcongr
  have hsq : H^2 ≤ (34/100)^2 * P^4 := by
    have h' := (sq_le_sq₀ (abs_nonneg H) (by positivity)).2 hH
    rw [sq_abs, mul_pow] at h'
    nlinarith only [h']
  have hquot : H^2/(2*localS*(h+localS)^2) ≤ (34/100)^2*P^4/(8/5)^3 := by
    apply div_le_div₀ (by positivity) hsq (by norm_num)
    calc
      ((8/5) : ℝ)^3 = (2*(4/5)) * ((4/5)+(4/5))^2 := by norm_num
      _ ≤ 2*localS*(h+localS)^2 := by gcongr <;> linarith only [hs, hh']
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg (by positivity : 0 ≤ H^2/(2*localS*(h+localS)^2))]
  norm_num at hquot hab4 ⊢
  linarith only [hab4, hquot, show 0 ≤ P^4 by positivity]

private theorem local_axis_remainder (P : ℝ) (hP : 0 ≤ P) (hp : P ≤ localR) :
    |Real.sqrt (1-P^2) - (1-P^2/2)| ≤ (14/100)*P^4 := by
  let a := Real.sqrt (1-P^2)
  have p₂ : P^2 ≤ localR^2 := by gcongr
  norm_num [localR] at p₂
  have ha : a^2 = 1-P^2 := Real.sq_sqrt (by linarith)
  have ha' : (99/100:ℝ) < a := by nlinarith only [ha, p₂, Real.sqrt_nonneg (1-P^2)]
  have he : a - (1-P^2/2) = -P^4/(2*(a+1)^2) := by
    have hf : -(P^2) = (a-1)*(a+1) := by nlinarith only [ha]
    have hff : P^4 = ((a-1)*(a+1))^2 := by rw [← hf, neg_sq, ← pow_mul]
    rw [hff, mul_pow, ← neg_mul, mul_div_mul_right _ _ (by positivity : (a+1)^2 ≠ 0)]
    nlinarith only [ha]
  change |a - _| ≤ _
  rw [he, abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ P^4),
    abs_of_nonneg (by positivity : 0 ≤ 2*(a+1)^2)]
  calc
    _ ≤ P^4 / (2*(199/100)^2) := by gcongr; linarith only [ha']
    _ ≤ _ := by
      norm_num
      linarith only [show 0 ≤ P^4 by positivity]


private def localRimTerms (p : ℂ) (j : Fin 3) : Fin 5 → ℍ[ℝ] :=
  ![localRimTerm p j 0, localRimTerm p j 1, localRimTerm p j 2, localRimTerm p j 3,
    localRim p 0 j - ∑ i : Fin 4, localRimTerm p j i]

private def localGainTerms (p : ℂ) (j : Fin 3) : Fin 5 → ℍ[ℝ] :=
  ![localGainTerm p j 0, localGainTerm p j 1, localGainTerm p j 2, localGainTerm p j 3,
    localGainPure p j - ∑ i : Fin 4, localGainTerm p j i]

private def localRimMajorant : Fin 5 → ℝ := ![1, 71/100, 26/100, 37/1000, 5/100]
private def localGainMajorant : Fin 5 → ℝ := ![1, 1, 1/2, 0, 14/100]

private theorem local_rim_terms_bound (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    ∀ i : Fin 5, ‖localRimTerms p j i‖ ≤ localRimMajorant i * ‖p‖^i.val := by
  obtain ⟨ht, hs, ha, _, hi⟩ := local_constant_squares
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hτ : localTau p j ^ 2 = 3*localB p j ^ 2 := by rw [localTau, mul_pow, h3]
  have hb := local_b_sq p j
  have hψ := local_psi_sq p j
  have h₂ : (‖p‖^2/6 - 3*localB p j^2)^2 ≤ ‖p‖^4/9 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (local_second_bound p j)
    rw [sq_abs] at hh
    nlinarith only [hh]
  have h₃ : localTau p j^2*localPsi p j^2 ≤ ‖p‖^6/512 := by
    calc
      _ ≤ (‖p‖^2/2)*(‖p‖^4/256) := by gcongr; linarith only [hτ, hb]
      _ = _ := by ring
  have hExpand : localRimTerms p j 4 =
      quatPair 0 (rimPhase j * ⟨Real.sqrt (localRadicand p 0 j) -
        (localS+localInvS*(‖p‖^2/6 - 3*localB p j^2)-localS*localTau p j*localPsi p j), 0⟩) := by
    ext <;> simp [localRimTerms, localRimTerm, localRim, localReal, localFibre,
      Fin.sum_univ_succ, quatPair, Complex.mul_re, Complex.mul_im] <;> ring
  intro i
  fin_cases i
  all_goals apply (sq_le_sq₀ (norm_nonneg _) (by norm_num [localRimMajorant] <;> positivity)).1
  case «4» =>
    change ‖localRimTerms p j 4‖ ^ 2 ≤ _
    rw [hExpand]
    norm_num [localRimMajorant, local_norm_pair, norm_mul, local_phase_norm,
      local_sq_complex, mul_pow]
    have hr := (local_pure_radical p hp j).2.2
    have h := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hr
    rw [sq_abs] at h
    nlinarith only [h]
  all_goals norm_num [localRimTerms, localRimTerm, localRimMajorant, local_norm_pair, norm_mul,
    local_phase_norm, local_sq_complex, mul_pow, ht, hs, ha, hi, hτ]
  · nlinarith only [hb, sq_nonneg ‖p‖]
  · nlinarith only [h₂, hψ, show 0 ≤ ‖p‖^4 by positivity]
  · rw [hτ] at h₃
    nlinarith only [h₃, show 0 ≤ ‖p‖^6 by positivity]

private theorem local_gain_terms_bound (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    ∀ i : Fin 5, ‖localGainTerms p j i‖ ≤ localGainMajorant i * ‖p‖^i.val := by
  have hAxis : ‖localAxis‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1
    simp [localAxis, local_norm_pair]
  have hExpand : localGainTerms p j 4 =
      (Real.sqrt (1-‖p‖^2) - (1-‖p‖^2/2)) • localAxis := by
    ext <;> simp [localGainTerms, localGainTerm, localGainPure, localAxis, quatPair,
      Fin.sum_univ_succ] <;> ring
  intro i
  fin_cases i
  · simpa [localGainTerms, localGainTerm, localGainMajorant] using hAxis.le
  · have h : ‖quatPair 0 (p * star (rimPhase j))‖ ≤ ‖p‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg p)).1
      simp [local_norm_pair, local_phase_norm]
    simpa [localGainTerms, localGainTerm, localGainMajorant] using h
  · have h : ‖quatPair ⟨0,-‖p‖^2/2⟩ 0‖ ≤ (1/2)*‖p‖^2 := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
      simp [local_norm_pair, local_sq_complex] <;> ring_nf <;> exact le_rfl
    simpa [localGainTerms, localGainTerm, localGainMajorant] using h
  · have h : quatPair 0 0 = (0 : ℍ[ℝ]) := rfl
    simp [localGainTerms, localGainTerm, localGainMajorant, h]
  · change ‖localGainTerms p j 4‖ ≤ (14/100)*‖p‖^4
    rw [hExpand, norm_smul, hAxis, mul_one, Real.norm_eq_abs]
    exact local_axis_remainder ‖p‖ (norm_nonneg p) hp

private theorem local_score_sum (x g y : Fin 5 → ℍ[ℝ]) :
    localScore (∑ i, x i) (∑ j, g j) (∑ k, y k) =
      ∑ i, ∑ j, ∑ k, localScore (x i) (g j) (y k) := by
  simp only [localScore, Finset.sum_mul, Finset.mul_sum, sum_inner, inner_sum]
  calc
    _ = ∑ k, ∑ i, ∑ j, ⟪x i*g j, y k⟫_ℝ :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ j, ⟪x i*g j, y k⟫_ℝ := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private def localTailCoeff (a b c : Fin 5) : ℝ :=
  if 4 ≤ a.val+b.val+c.val then
    localRimMajorant a * localGainMajorant b * localRimMajorant c *
      localR^(a.val+b.val+c.val-4) else 0

private theorem local_tail_majorant : (∑ a, ∑ b, ∑ c, localTailCoeff a b c) ≤ 3 := by
  norm_num [Fin.sum_univ_succ, localTailCoeff, localRimMajorant, localGainMajorant, localR]

set_option maxHeartbeats 500000 in
private theorem local_pure_score (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    localT-localAlpha*‖p‖^2-(2/5)*‖p‖^3-3*‖p‖^4 ≤
      localScore (localRim p 0 j) (localGainPure p j) (localRim p 0 (rimNext j)) := by
  let P := ‖p‖
  let k := rimNext j
  let term := fun a b c : Fin 5 =>
    localScore (localRimTerms p j a) (localGainTerms p j b) (localRimTerms p k c)
  let tail := fun a b c : Fin 5 =>
    if 4 ≤ a.val+b.val+c.val then term a b c else 0
  let low := fun a b c : Fin 5 =>
    if a.val+b.val+c.val < 4 then term a b c else 0
  have hX (j : Fin 3) : (∑ i, localRimTerms p j i) = localRim p 0 j := by
    simp [localRimTerms, Fin.sum_univ_succ]
    abel
  have hG : (∑ i, localGainTerms p j i) = localGainPure p j := by
    simp [localGainTerms, Fin.sum_univ_succ]
    abel
  have hLow : (∑ a, ∑ b, ∑ c, low a b c) =
      localT - localAlpha*P^2 + localPureCubic p j := by
    simpa [low, term, P, k, Fin.sum_univ_succ, localRimTerms, localGainTerms] using
      local_pure_terms p j
  have hSplit : term = fun a b c => low a b c + tail a b c := by
    funext a b c
    by_cases h : a.val+b.val+c.val < 4
    · simp [low, tail, h, Nat.not_le.mpr h]
    · simp [low, tail, h, Nat.le_of_not_gt h]
  have hT a b c : |tail a b c| ≤ P^4 * localTailCoeff a b c := by
    by_cases h : 4 ≤ a.val+b.val+c.val
    · simp only [tail, localTailCoeff, ite_eq_left h]
      have ha : 0 ≤ localRimMajorant a := by fin_cases a <;> norm_num [localRimMajorant]
      have hb : 0 ≤ localGainMajorant b := by fin_cases b <;> norm_num [localGainMajorant]
      have hc : 0 ≤ localRimMajorant c := by fin_cases c <;> norm_num [localRimMajorant]
      have ha' := local_rim_terms_bound p hp j a
      have hb' := local_gain_terms_bound p hp j b
      have hc' := local_rim_terms_bound p hp k c
      calc
        _ ≤ (localRimMajorant a * P^a.val) * (localGainMajorant b * P^b.val) *
            (localRimMajorant c * P^c.val) := by
          refine (local_abs_score _ _ _).trans ?_
          gcongr
        _ = localRimMajorant a * localGainMajorant b * localRimMajorant c *
            (P^4 * P^(a.val+b.val+c.val-4)) := by
          rw [← pow_add, Nat.add_sub_of_le h, pow_add, pow_add]
          ring
        _ ≤ localRimMajorant a * localGainMajorant b * localRimMajorant c *
            (P^4 * localR^(a.val+b.val+c.val-4)) := by gcongr
        _ = _ := by ring
    · simp [tail, localTailCoeff, h]
  have hTail : |∑ a, ∑ b, ∑ c, tail a b c| ≤ 3*P^4 := by
    calc
      _ ≤ ∑ a, ∑ b, ∑ c, |tail a b c| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine Finset.sum_le_sum fun a _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        exact Finset.sum_le_sum fun b _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, ∑ b, ∑ c, P^4 * localTailCoeff a b c :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          Finset.sum_le_sum fun c _ => hT a b c
      _ = P^4 * (∑ a, ∑ b, ∑ c, localTailCoeff a b c) := by simp_rw [Finset.mul_sum]
      _ ≤ _ := (mul_le_mul_of_nonneg_left local_tail_majorant
        (show 0 ≤ P^4 by positivity)).trans_eq (mul_comm (P^4) 3)
  rw [← hX j, ← hX k, ← hG, local_score_sum]
  change _ ≤ ∑ a, ∑ b, ∑ c, term a b c
  rw [hSplit]
  simp only [Finset.sum_add_distrib, hLow]
  linarith only [(abs_le.mp (local_cubic_bound p j)).1, (abs_le.mp hTail).1]


private theorem local_real_fibre_norm (j : Fin 3) (a b : ℝ) :
    ‖quatPair ⟨a, 0⟩ (rimPhase j * ⟨b, 0⟩)‖ ^ 2 = a^2+b^2 := by
  simp [local_norm_pair, norm_mul, local_phase_norm, local_sq_complex]

def localQLinear (q : ℂ) (j : Fin 3) : ℍ[ℝ] :=
  quatPair ⟨localLinear*‖q‖, 0⟩
    (rimPhase j * ⟨-(Real.sqrt 2/2)*(localLinear*‖q‖), 0⟩)

private theorem local_pure_near (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    ‖localRim p 0 j-localRimTerm p j 0‖ ≤ (726/1000)*‖p‖ ∧
    ‖localRim p 0 j-(localRimTerm p j 0+localRimTerm p j 1)‖ ≤ (27/100)*‖p‖^2 := by
  have he : (∑ i, localRimTerms p j i) = localRim p 0 j := by
    simp [localRimTerms, Fin.sum_univ_succ]
    abel
  have h := local_rim_terms_bound p hp j
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have hX := norm_add_le (localRimTerms p j 2+localRimTerms p j 3) (localRimTerms p j 4)
  have hY := (norm_add_le (localRimTerms p j 2) (localRimTerms p j 3))
  have hZ := norm_add_le (localRimTerms p j 1)
    (localRimTerms p j 2+localRimTerms p j 3+localRimTerms p j 4)
  have hs : localRim p 0 j-localRimTerm p j 0 =
      localRimTerms p j 1 + (localRimTerms p j 2+localRimTerms p j 3+localRimTerms p j 4) := by
    rw [← he]
    simp [Fin.sum_univ_succ, localRimTerms]
    abel
  have hs' : localRim p 0 j-(localRimTerm p j 0+localRimTerm p j 1) =
      localRimTerms p j 2+localRimTerms p j 3+localRimTerms p j 4 := by
    rw [← he]
    simp [Fin.sum_univ_succ, localRimTerms]
    abel
  obtain ⟨hp3,hp4⟩ := local_higher_powers ‖p‖ (norm_nonneg p) hp
  have hp2 : ‖p‖^2 ≤ localR*‖p‖ := by rw [pow_two]; gcongr
  norm_num [localRimMajorant] at h1 h2 h3 h4
  norm_num [localR] at hp2 hp3 hp4
  constructor
  · rw [hs]; linarith only [h1,h2,h3,h4,hX,hY,hZ,hp2,hp3,hp4,norm_nonneg p]
  · rw [hs']; linarith only [h2,h3,h4,hX,hY,hp3,hp4,sq_nonneg ‖p‖]

private theorem local_pure_gain_near (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    ‖localGainPure p j-localAxis‖ ≤ (1031/1000)*‖p‖ := by
  have he : (∑ i, localGainTerms p j i) = localGainPure p j := by
    simp [localGainTerms, Fin.sum_univ_succ]
    abel
  have hs : localGainPure p j-localAxis =
      localGainTerms p j 1 + localGainTerms p j 2 + localGainTerms p j 4 := by
    rw [← he]
    have hz : quatPair 0 0 = (0 : ℍ[ℝ]) := rfl
    simp [Fin.sum_univ_succ, localGainTerms, localGainTerm, hz]
    abel
  have h := local_gain_terms_bound p hp j
  have h1 := h 1
  have h2 := h 2
  have h4 := h 4
  norm_num [localGainMajorant] at h1 h2 h4
  obtain ⟨_,hp4⟩ := local_higher_powers ‖p‖ (norm_nonneg p) hp
  have hp2 : ‖p‖^2 ≤ localR*‖p‖ := by rw [pow_two]; gcongr
  norm_num [localR] at hp2 hp4
  rw [hs]
  refine (norm_add_le _ _).trans ?_
  linarith only [norm_add_le (localGainTerms p j 1) (localGainTerms p j 2),
    h1,h2,h4,hp2,hp4,norm_nonneg p]

private theorem local_pure_gain_unit (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3) :
    ‖localGainPure p j‖ = 1 := by
  have hp₂ : ‖p‖^2 ≤ localR^2 := by gcongr
  have hn : 0 ≤ 1-‖p‖^2 := by norm_num [localR] at hp₂; linarith
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1
  simp [localGainPure, local_norm_pair, local_sq_complex, norm_mul, Complex.star_def,
    Complex.norm_conj, local_phase_norm, Real.sq_sqrt hn]

private theorem local_raw_unit (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (j : Fin 3) :
    ‖localRim p q j‖ = 1 := by
  rw [← local_unit_rim_coe p q hp hq j]
  exact unit_norm _

private theorem local_base_unit (p : ℂ) (j : Fin 3) : ‖localRimTerm p j 0‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1
  norm_num [localRimTerm, local_norm_pair, local_phase_norm, local_sq_complex,
    local_constant_squares.1, local_constant_squares.2.1]

private theorem local_b_diff (p : ℂ) (j : Fin 3) :
    |localB p (rimNext j) - localB p j| ≤ (71/100)*‖p‖ := by
  have h3 : Real.sqrt 3 ^2 = 3 := Real.sq_sqrt (by norm_num)
  have h : ‖rimPhase (rimPrev (rimNext j)) - rimPhase (rimPrev j)‖ = Real.sqrt 3 := by
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    fin_cases j <;> norm_num [rimPhase,rimNext,rimPrev,zeta,Complex.sq_norm,Complex.normSq_apply,
      Complex.star_def,h3] <;> nlinarith only [h3]
  have he : localB p (rimNext j) - localB p j =
      localLinear * (p*(rimPhase (rimPrev (rimNext j))-rimPhase (rimPrev j))).re := by
    simp [localB, mul_sub, Complex.sub_re] <;> ring
  have hc : localLinear * Real.sqrt 3 ≤ (71/100:ℝ) := by
    have h := local_constant_squares.2.2.2.1
    have hs : (localLinear*Real.sqrt 3)^2 = 1/2 := by rw [mul_pow,h,h3]; norm_num
    nlinarith only [hs, show 0 ≤ localLinear*Real.sqrt 3 by unfold localLinear; positivity]
  rw [he,abs_mul,abs_of_nonneg (by unfold localLinear; positivity)]
  refine (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by unfold localLinear; positivity)).trans ?_
  rw [norm_mul, h, mul_comm ‖p‖, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg p)

private theorem local_scalar_linear (p q : ℂ) (j : Fin 3) :
    let k := rimNext j
    let x := localRimTerm p j 0
    let y := localRimTerm p k 0
    let ξ := localRimTerm p j 1+localQLinear q j
    let υ := localRimTerm p k 1+localQLinear q k
    localScore x 1 y = 0 ∧
    localScore ξ 1 y+localScore x 1 υ =
      Real.sqrt 3*(localLinear*‖q‖)+localB p k-localB p j := by
  fin_cases j <;>
    norm_num [localRimTerm,localQLinear,localScore,localT,localS,localLinear,localB,localTau,
      rimNext,rimPrev,rimPhase,zeta,quatPair,inner_eq_components,Complex.mul_re,Complex.mul_im,
      Complex.star_def] <;>
    constructor <;> ring_nf <;>
    simp (disch := omega) [local_reduce_root_pow 2 (by norm_num),
      local_reduce_root_pow 3 (by norm_num)] <;> ring

private theorem local_q_base_identities (q : ℂ) (j : Fin 3)
    (hq : q * (zeta - 1) = ((Real.sqrt 3 * ‖q‖ : ℝ) : ℂ)) :
    let x := localRimTerm 0 j 0
    let y := localRimTerm 0 (rimNext j) 0
    localScore (localQLinear q j) localAxis y + localScore x localAxis (localQLinear q (rimNext j)) =
      -(localLinear*‖q‖) ∧
    localScore x (quatPair 0 (q*rimPhase j)) y = 2*localLinear*‖q‖ := by
  have hre := congrArg Complex.re hq
  have him := congrArg Complex.im hq
  fin_cases j <;>
    norm_num [localQLinear, localRimTerm, localScore, localAxis, localT, localS, localLinear,
      rimNext, rimPhase, zeta, quatPair, inner_eq_components, Complex.mul_re, Complex.mul_im,
      Complex.star_def, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul] at hre him ⊢ <;>
    constructor <;> ring_nf at * <;>
    simp (disch := omega) [local_reduce_root_pow 2 (by norm_num),
      local_reduce_root_pow 3 (by norm_num)] at * <;>
    try (solve | ring)
  all_goals linear_combination (Real.sqrt 2/3)*hre

private theorem local_linear_norm (q : ℂ) (j : Fin 3) :
    ‖localQLinear q j‖ = ‖q‖/2 := by
  have h2 : Real.sqrt 2^2 = 2 := Real.sq_sqrt (by norm_num)
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1
  simp [localQLinear,local_real_fibre_norm,mul_pow,div_pow,h2,
    local_constant_squares.2.2.2.1]
  ring

private theorem local_axis_unit : ‖localAxis‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1
  simp [localAxis,local_norm_pair]

private theorem local_axis_base (p : ℂ) (j : Fin 3) :
    localScore (localRimTerm p j 0) localAxis (localRimTerm p (rimNext j) 0) = localT := by
  have hs := local_constant_squares.2.1
  have h3 : Real.sqrt 3 ^2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases j <;>
    norm_num [localRimTerm,localAxis,localScore,rimNext,rimPhase,zeta,quatPair,
      inner_eq_components,Complex.mul_re,Complex.mul_im,Complex.star_def,Quaternion.re_mul,
      Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;>
    unfold localT <;> linear_combination (Real.sqrt 3/2)*hs


/-- Norm and score estimates for the cubic expansion and its linear terms. -/
structure PureScoreEstimates (rim : ℂ → ℂ → Fin 3 → ℍ[ℝ]) : Prop where
  constant_squares : localT ^ 2 = 1/3 ∧ localS ^ 2 = 2/3 ∧ localAlpha ^ 2 = 1/48 ∧
      localLinear ^ 2 = 1/6
  constant_values : localT = 1 / Real.sqrt 3 ∧ localS = Real.sqrt (2/3) ∧ localLinear = 1 / Real.sqrt 6
  constant_bounds : 577/1000 < localT ∧ localT < 5774/10000 ∧ 815/1000 < localS ∧ localS < 817/1000 ∧
    0 < localAlpha ∧ localAlpha < 145/1000 ∧ 408/1000 < localLinear ∧
    localLinear < 409/1000
  real_bounds : ∀ (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR),
    0 < localReal p q ∧ localReal p q < 603/1000
  radicand_bound : ∀ (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR)
    (j : Fin 3), (795/1000)^2 < localRadicand p q j
  rim_coe : ∀ (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR)
    (j : Fin 3), ((localUnitRim p q j : U) : ℍ[ℝ]) = rim p q j
  abs_score : ∀ (x g y : ℍ[ℝ]),
    |localScore x g y| ≤ ‖x‖*‖g‖*‖y‖
  pure_radical : ∀ (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3),
    let h := Real.sqrt (localRadicand p 0 j)
    4/5 < h ∧ |h-localS| ≤ (213/1000)*‖p‖^2
  pure_score : ∀ (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3),
    localT-localAlpha*‖p‖^2-(2/5)*‖p‖^3-3*‖p‖^4 ≤
      localScore (rim p 0 j) (localGainPure p j) (rim p 0 (rimNext j))
  real_fibre_norm : ∀ (j : Fin 3) (a b : ℝ),
    ‖quatPair ⟨a, 0⟩ (rimPhase j * ⟨b, 0⟩)‖ ^ 2 = a^2+b^2
  pure_near : ∀ (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3),
    ‖rim p 0 j-localRimTerm p j 0‖ ≤ (726/1000)*‖p‖ ∧
    ‖rim p 0 j-(localRimTerm p j 0+localRimTerm p j 1)‖ ≤ (27/100)*‖p‖^2
  pure_gain_near : ∀ (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3),
    ‖localGainPure p j-localAxis‖ ≤ (1031/1000)*‖p‖
  pure_gain_unit : ∀ (p : ℂ) (hp : ‖p‖ ≤ localR) (j : Fin 3),
    ‖localGainPure p j‖ = 1
  rim_unit : ∀ (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (j : Fin 3),
    ‖rim p q j‖ = 1
  base_unit : ∀ (p : ℂ) (j : Fin 3), ‖localRimTerm p j 0‖ = 1
  b_diff : ∀ (p : ℂ) (j : Fin 3),
    |localB p (rimNext j) - localB p j| ≤ (71/100)*‖p‖
  scalar_linear : ∀ (p q : ℂ) (j : Fin 3),
    let k := rimNext j
    let x := localRimTerm p j 0
    let y := localRimTerm p k 0
    let ξ := localRimTerm p j 1+localQLinear q j
    let υ := localRimTerm p k 1+localQLinear q k
    localScore x 1 y = 0 ∧
    localScore ξ 1 y+localScore x 1 υ =
      Real.sqrt 3*(localLinear*‖q‖)+localB p k-localB p j
  q_base_identities : ∀ (q : ℂ) (j : Fin 3)
    (hq : q * (zeta - 1) = ((Real.sqrt 3 * ‖q‖ : ℝ) : ℂ)),
    let x := localRimTerm 0 j 0
    let y := localRimTerm 0 (rimNext j) 0
    localScore (localQLinear q j) localAxis y + localScore x localAxis (localQLinear q (rimNext j)) =
      -(localLinear*‖q‖) ∧
    localScore x (quatPair 0 (q*rimPhase j)) y = 2*localLinear*‖q‖
  linear_norm : ∀ (q : ℂ) (j : Fin 3),
    ‖localQLinear q j‖ = ‖q‖/2
  axis_unit : ‖localAxis‖ = 1
  axis_base : ∀ (p : ℂ) (j : Fin 3),
    localScore (localRimTerm p j 0) localAxis (localRimTerm p (rimNext j) 0) = localT

/-- Quantitative estimates for the pure Fourier mode and its first variation. -/
theorem pure_score_estimates : PureScoreEstimates localRim where
  constant_squares := ⟨local_constant_squares.1, local_constant_squares.2.1,
    local_constant_squares.2.2.1, local_constant_squares.2.2.2.1⟩
  constant_values := local_constant_values
  constant_bounds := local_constant_bounds
  real_bounds := local_real_bounds
  radicand_bound := local_radicand_bound
  rim_coe := local_unit_rim_coe
  abs_score := local_abs_score
  pure_radical := fun p hp j =>
    ⟨(local_pure_radical p hp j).1, (local_pure_radical p hp j).2.1⟩
  pure_score := local_pure_score
  real_fibre_norm := local_real_fibre_norm
  pure_near := local_pure_near
  pure_gain_near := local_pure_gain_near
  pure_gain_unit := local_pure_gain_unit
  rim_unit := local_raw_unit
  base_unit := local_base_unit
  b_diff := local_b_diff
  scalar_linear := local_scalar_linear
  q_base_identities := local_q_base_identities
  linear_norm := local_linear_norm
  axis_unit := local_axis_unit
  axis_base := local_axis_base

end RoundQuaternionLocalSharpness
