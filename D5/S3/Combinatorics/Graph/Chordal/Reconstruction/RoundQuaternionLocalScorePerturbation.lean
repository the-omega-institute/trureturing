/- GID: D5/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalScorePerturbation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/Chordal/Reconstruction/RoundQuaternionLocalScorePerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extension of the pure Fourier rim estimate to both nonconstant modes and the scalar perturbation. -/

import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.RoundQuaternionLocalPureScore

/-! The axial, scalar and transverse perturbations of the pure Fourier rim score. -/

noncomputable section

open Real Quaternion
open scoped Quaternion InnerProductSpace

namespace RoundQuaternionLocalSharpness

open D5.S3.Quantum.AURICOmega.QuaternionComparisonModel (inner_eq_components)

local notation "U" => unitary ℍ[ℝ]

private theorem local_q_displacement (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR)
    (j : Fin 3) :
    ‖localRim p q j-localRim p 0 j‖ ≤ (515/1000)*‖q‖ ∧
    ‖localRim p q j-localRim p 0 j-localQLinear q j‖ ≤ (1/5)*localR*‖q‖ := by
  let d := localLinear*‖q‖
  let a := localReal p 0
  let h₀ := Real.sqrt (localRadicand p 0 j)
  let h₁ := Real.sqrt (localRadicand p q j)
  let R := (2*a+d)/(h₀+h₁)
  have h0 : ‖(0:ℂ)‖ ≤ localR := by norm_num [localR]
  have ha : 0 < a := (pure_score_estimates.real_bounds p 0 hp h0).1
  have hnon : 0 ≤ d := by unfold d localLinear; positivity
  have ha₀ : a = localT-localAlpha*‖p‖^2 := by simp [a, localReal]
  have ha₁ : localReal p q = a+d := by simp [a, d, localReal]; ring
  have h0lo : (4/5:ℝ) < h₀ := (pure_score_estimates.pure_radical p hp j).1
  have h1lo : (795/1000:ℝ) < h₁ := Real.lt_sqrt (by norm_num) |>.2
    (pure_score_estimates.radicand_bound p q hp hq j)
  have hden : 0 < h₀+h₁ := by linarith
  have hd : d ≤ (409/1000)*‖q‖ := by
    exact mul_le_mul_of_nonneg_right pure_score_estimates.constant_bounds.2.2.2.2.2.2.2.le (norm_nonneg q)
  have hr : 0 ≤ R ∧ R ≤ 3/4 := by
    refine ⟨div_nonneg (by linarith) hden.le, (div_le_iff₀ hden).2 ?_⟩
    obtain ⟨_, ht, _, _, hα, _, _, _⟩ := pure_score_estimates.constant_bounds
    have ha' : a ≤ localT := by rw [ha₀]; nlinarith only [mul_nonneg hα.le (sq_nonneg ‖p‖)]
    have hd' : d ≤ (409/1000)*localR := by linarith
    unfold localR at hd'
    linarith
  have hΔ : h₁-h₀ = -d*R := by
    obtain ⟨h₀', h₁'⟩ := (show h₀^2 = localRadicand p 0 j ∧ h₁^2 = localRadicand p q j by
      constructor <;> apply Real.sq_sqrt <;>
      linarith [pure_score_estimates.radicand_bound p 0 hp h0 j, pure_score_estimates.radicand_bound p q hp hq j])
    dsimp only [R]
    rw [← mul_div_assoc, eq_div_iff hden.ne']
    unfold localRadicand at h₀' h₁'
    rw [ha₁] at h₁'
    linear_combination h₁' - h₀'
  have heq : localRim p q j-localRim p 0 j = quatPair ⟨d, 0⟩ (rimPhase j*⟨-d*R, 0⟩) := by
    simp only [localRim, local_geometry.local_pair_sub, ← mul_sub]
    congr 1
    · apply Complex.ext
      · change localReal p q-a = d
        linarith only [ha₁]
      · simp
    · congr 1
      apply Complex.ext
      · exact hΔ
      · simp
  have heq' : localRim p q j-localRim p 0 j-localQLinear q j =
      quatPair 0 (rimPhase j*⟨-d*(R-Real.sqrt 2/2), 0⟩) := by
    rw [heq, localQLinear, local_geometry.local_pair_sub, ← mul_sub]
    congr 1
    · change (⟨d,0⟩:ℂ) - ⟨d,0⟩ = 0
      exact sub_self _
    · congr 1
      apply Complex.ext
      · change -d*R - (-(Real.sqrt 2/2)*d) = -d*(R-Real.sqrt 2/2)
        ring
      · simp
  constructor
  · rw [heq]
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    rw [pure_score_estimates.real_fibre_norm]
    have hRs := (sq_le_sq₀ hr.1 (by norm_num : 0 ≤ (3/4:ℝ))).2 hr.2
    have hd' : d^2 ≤ ((409/1000)*‖q‖)^2 := (sq_le_sq₀ hnon (by positivity)).2 hd
    nlinarith only [hd', mul_le_mul_of_nonneg_left hRs (sq_nonneg d), sq_nonneg ‖q‖]
  · rw [heq']
    have hSpos : 0 < localS := by unfold localS; positivity
    have h2 : Real.sqrt 2 ^2 = 2 := Real.sq_sqrt (by norm_num)
    have hcf : (Real.sqrt 2/2)*localS = localT := by
      unfold localS localT
      linear_combination (Real.sqrt 3/6)*h2
    have hsqrt : Real.sqrt 2/2 ≤ (71/100:ℝ) := by nlinarith only [h2, Real.sqrt_nonneg 2]
    have hDiff : |R-Real.sqrt 2/2| ≤ (12/25)*localR := by
      have hEq : R-Real.sqrt 2/2 =
          ((2*a+d-2*localT)-(Real.sqrt 2/2)*(h₀+h₁-2*localS))/(h₀+h₁) := by
        dsimp only [R]
        field_simp [hden.ne']
        linear_combination -4*hcf
      have hA : |2*a+d-2*localT| ≤ d + (29/100)*‖p‖^2 := by
        rw [ha₀, show 2*(localT-localAlpha*‖p‖^2)+d-2*localT =
          d - 2*localAlpha*‖p‖^2 by ring]
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg hnon, abs_of_nonneg (by unfold localAlpha; positivity)]
        have hc : 2*localAlpha ≤ (29/100:ℝ) := by
          linarith [pure_score_estimates.constant_bounds.2.2.2.2.2.1]
        exact add_le_add (le_refl d) (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖p‖))
      have hB : |h₀+h₁-2*localS| ≤ (426/1000)*‖p‖^2+(3/4)*d := by
        rw [show h₀+h₁-2*localS = (h₁-h₀) + 2*(h₀-localS) by ring, hΔ]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hnon, abs_of_nonneg hr.1]
        norm_num
        nlinarith only [(pure_score_estimates.pure_radical p hp j).2, mul_le_mul_of_nonneg_left hr.2 hnon]
      have hbnd : |(Real.sqrt 2/2)*(h₀+h₁-2*localS)| ≤
          (71/100)*((426/1000)*‖p‖^2+(3/4)*d) := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        gcongr
      have hp' : ‖p‖^2 ≤ localR^2 := by gcongr
      have hd' : d ≤ (409/1000)*localR := by linarith
      have hNum : |(2*a+d-2*localT)-(Real.sqrt 2/2)*(h₀+h₁-2*localS)| ≤
          (12/25)*localR*(h₀+h₁) := by
        refine (abs_sub _ _).trans ?_
        norm_num [localR] at *
        linarith only [hA, hbnd, hp', hd', h0lo, h1lo]
      rw [hEq, abs_div, abs_of_nonneg hden.le]
      exact (div_le_iff₀ hden).2 hNum
    have hprod := mul_le_mul hDiff hd hnon (by unfold localR; positivity :
      0 ≤ (12/25)*localR)
    apply (sq_le_sq₀ (norm_nonneg _) (by unfold localR; positivity)).1
    change ‖quatPair ⟨0, 0⟩ _‖^2 ≤ _
    rw [pure_score_estimates.real_fibre_norm]
    have hFinal : |-d*(R-Real.sqrt 2/2)| ≤ (1/5)*localR*‖q‖ := by
      rw [abs_mul, abs_neg, abs_of_nonneg hnon, mul_comm]
      nlinarith only [hprod, show 0 ≤ localR*‖q‖ by unfold localR; positivity]
    simpa only [zero_pow (by decide : 2 ≠ (0:ℕ)), zero_add, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (by unfold localR; positivity)).2 hFinal


private theorem local_score_change (x x' g g' y y' : ℍ[ℝ]) :
    |localScore x g y-localScore x' g' y'| ≤
      ‖x-x'‖*‖g‖*‖y‖ + ‖x'‖*‖g-g'‖*‖y‖ + ‖x'‖*‖g'‖*‖y-y'‖ := by
  have h : localScore x g y-localScore x' g' y' =
      localScore (x-x') g y + localScore x' (g-g') y + localScore x' g' (y-y') := by
    simp only [localScore, sub_mul, mul_sub, inner_sub_left, inner_sub_right]
    ring
  rw [h]
  exact (abs_add_le _ _).trans <| add_le_add ((abs_add_le _ _).trans <|
    add_le_add (pure_score_estimates.abs_score _ _ _) (pure_score_estimates.abs_score _ _ _)) (pure_score_estimates.abs_score _ _ _)

private theorem local_gain_q_diff (q : ℂ) (j : Fin 3) :
    ‖quatPair 0 (q * rimPhase j)‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  simp [local_geometry.local_norm_pair, norm_mul, local_geometry.local_phase_norm]

private theorem local_gain_axis_diff (p q : ℂ) (η : Fin 3 → ℝ)
    (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (he : etaMax η ≤ localR) (j : Fin 3) :
    |Real.sqrt (1-(η j)^2-‖transverse p q j‖^2)-Real.sqrt (1-‖p‖^2)| ≤
      (3*localR*‖q‖+localR*etaMax η)/(198/100) := by
  let P := ‖p‖
  let Q := ‖q‖
  let E := etaMax η
  let W := ‖transverse p q j‖
  let a := Real.sqrt (1-(η j)^2-W^2)
  let b := Real.sqrt (1-P^2)
  have hW : W ≤ P+Q := by
    simpa [W,P,Q,transverse,norm_mul,local_geometry.local_phase_norm,Complex.star_def,Complex.norm_conj] using
      norm_add_le (p*star (rimPhase j)) (q*rimPhase j)
  have hW' : |W-P| ≤ Q := by
    simpa [W,P,Q,transverse,norm_mul,local_geometry.local_phase_norm,Complex.star_def,Complex.norm_conj] using
      (abs_norm_sub_norm_le (p*star (rimPhase j)+q*rimPhase j) (p*star (rimPhase j)))
  have hη : (η j)^2 ≤ localR*E := by
    rw [← sq_abs, pow_two]
    exact mul_le_mul ((local_geometry.local_abs_eta η j).trans he) (local_geometry.local_abs_eta η j)
      (abs_nonneg _) (by norm_num [localR])
  have hWSq : W^2 ≤ (2*localR)^2 := by
    gcongr
    linarith
  have hEtaSq : (η j)^2 ≤ localR^2 := hη.trans (by
    rw [pow_two]; exact mul_le_mul_of_nonneg_left he (by norm_num [localR]))
  have hPSq : P^2 ≤ localR^2 := by gcongr
  have ha : a^2 = 1-(η j)^2-W^2 := Real.sq_sqrt (by norm_num [localR] at hEtaSq hWSq; linarith)
  have hb : b^2 = 1-P^2 := Real.sq_sqrt (by norm_num [localR] at hPSq; linarith)
  have ha' : (99/100:ℝ) < a := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
    norm_num [localR] at hEtaSq hWSq
    linarith
  have hb' : (99/100:ℝ) < b := by
    apply (sq_lt_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
    norm_num [localR] at hPSq
    linarith
  have hpos : 0 < a+b := by linarith
  have hdiff : (a-b)*(a+b) = -((η j)^2+(W-P)*(W+P)) := by nlinarith only [ha,hb]
  change |a-b| ≤ _
  rw [show a-b = -((η j)^2+(W-P)*(W+P))/(a+b) by
    exact (eq_div_iff hpos.ne').2 hdiff, abs_div, abs_neg, abs_of_nonneg hpos.le]
  have hEnonneg : 0 ≤ E := local_geometry.local_eta_nonneg η
  apply div_le_div₀ (by unfold localR; positivity) _ (by norm_num) (by linarith)
  refine (abs_add_le _ _).trans ?_
  have hWsum : 0 ≤ W+P := add_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_nonneg hWsum]
  have hwp : W+P ≤ 3*localR := by linarith
  linarith only [hη, mul_le_mul hW' hwp hWsum (show 0 ≤ Q from norm_nonneg q)]


private theorem local_scalar_bound (p q : ℂ) (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (j : Fin 3) :
    |localScore (localRim p q j) 1 (localRim p q (rimNext j))| ≤ (161/100)*localR := by
  let k := rimNext j
  let x := localRimTerm p j 0
  let y := localRimTerm p k 0
  let X := localRim p q j
  let Y := localRim p q k
  let ξ := localRimTerm p j 1+localQLinear q j
  let υ := localRimTerm p k 1+localQLinear q k
  have hnear (i : Fin 3) : ‖localRim p q i-localRimTerm p i 0‖ ≤ (1241/1000)*localR := by
    have he : localRim p q i-localRimTerm p i 0 =
        (localRim p q i-localRim p 0 i)+(localRim p 0 i-localRimTerm p i 0) := by abel
    rw [he]
    refine (norm_add_le _ _).trans ?_
    linarith [(pure_score_estimates.pure_near p hp i).1,(local_q_displacement p q hp hq i).1]
  have herr (i : Fin 3) :
      ‖(localRim p q i-localRimTerm p i 0)-(localRimTerm p i 1+localQLinear q i)‖ ≤
        (27/100)*‖p‖^2+(1/5)*localR*‖q‖ := by
    have he : (localRim p q i-localRimTerm p i 0)-(localRimTerm p i 1+localQLinear q i) =
        (localRim p 0 i-(localRimTerm p i 0+localRimTerm p i 1))+
          (localRim p q i-localRim p 0 i-localQLinear q i) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (pure_score_estimates.pure_near p hp i).2
      (local_q_displacement p q hp hq i).2)
  have hex : localScore X 1 Y =
      (Real.sqrt 3*(localLinear*‖q‖)+localB p k-localB p j) +
      (localScore (X-x-ξ) 1 y+localScore x 1 (Y-y-υ)+localScore (X-x) 1 (Y-y)) := by
    obtain ⟨h0,h1⟩ := pure_score_estimates.scalar_linear p q j
    change localScore x 1 y = 0 at h0
    change localScore ξ 1 y+localScore x 1 υ = _ at h1
    rw [← h1]
    simp only [localScore, sub_mul, inner_sub_left, inner_sub_right] at h0 ⊢
    linarith only [h0]
  have hx := pure_score_estimates.abs_score (X-x-ξ) (1:ℍ[ℝ]) y
  have hy := pure_score_estimates.abs_score x (1:ℍ[ℝ]) (Y-y-υ)
  have hxy := pure_score_estimates.abs_score (X-x) (1:ℍ[ℝ]) (Y-y)
  have hx' : |localScore (X-x-ξ) 1 y| ≤ (27/100)*‖p‖^2+(1/5)*localR*‖q‖ := by
    simp only [norm_one,pure_score_estimates.base_unit,x,y,mul_one,one_mul] at hx
    exact hx.trans (herr j)
  have hy' : |localScore x 1 (Y-y-υ)| ≤ (27/100)*‖p‖^2+(1/5)*localR*‖q‖ := by
    simp only [norm_one,pure_score_estimates.base_unit,x,y,mul_one,one_mul] at hy
    exact hy.trans (herr k)
  have hxy' : |localScore (X-x) 1 (Y-y)| ≤ ((1241/1000)*localR)^2 := by
    refine hxy.trans ?_
    rw [norm_one,mul_one,pow_two]
    exact mul_le_mul (hnear j) (hnear k) (norm_nonneg _) (by unfold localR; positivity)
  have hLin : |Real.sqrt 3*(localLinear*‖q‖)+localB p k-localB p j| ≤
      (71/100)*(‖p‖+‖q‖) := by
    have h3 : Real.sqrt 3 ^2 = 3 := Real.sq_sqrt (by norm_num)
    have hC : Real.sqrt 3*localLinear ≤ (71/100:ℝ) := by
      have hs : (Real.sqrt 3*localLinear)^2 = 1/2 := by
        rw [mul_pow,h3,pure_score_estimates.constant_squares.2.2.2]; norm_num
      nlinarith only [hs,show 0 ≤ Real.sqrt 3*localLinear by unfold localLinear; positivity]
    rw [show Real.sqrt 3*(localLinear*‖q‖)+localB p k-localB p j =
      (Real.sqrt 3*localLinear)*‖q‖+(localB p k-localB p j) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by unfold localLinear; positivity)]
    linarith [mul_le_mul_of_nonneg_right hC (norm_nonneg q),pure_score_estimates.b_diff p j]
  rw [hex]
  have hSum := (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add hx' hy')) hxy')
  refine ((abs_add_le _ _).trans (add_le_add hLin hSum)).trans ?_
  have hp₂ : ‖p‖^2 ≤ localR^2 := by gcongr
  have hq₂ : localR*‖q‖ ≤ localR^2 := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left hq (by norm_num [localR])
  norm_num [localR] at hp hq hp₂ hq₂ ⊢
  linarith only [hp,hq,hp₂,hq₂]


private theorem local_rim_score (A : Fin 3 → U) (p q : ℂ) (η γ : Fin 3 → ℝ)
    (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (he : etaMax η ≤ localR)
    (hγ : ∀ j, γ j = Real.sqrt (1-(η j)^2-‖transverse p q j‖^2))
    (hA : ∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j,γ j⟩ (transverse p q j))
    (hphase : q*(zeta-1) = ((Real.sqrt 3*‖q‖ : ℝ) : ℂ)) (j : Fin 3) :
    localT + localLinear*‖q‖ - localAlpha*‖p‖^2 - (2/5)*‖p‖^3 - 3*‖p‖^4 -
      (627/100)*localR*‖q‖ - 2*localR*etaMax η ≤
      localScore (localRim p q j) (A j : ℍ[ℝ]) (localRim p q (rimNext j)) := by
  let k := rimNext j
  let x := localRimTerm p j 0
  let y := localRimTerm p k 0
  let X₀ := localRim p 0 j
  let Y₀ := localRim p 0 k
  let X := localRim p q j
  let Y := localRim p q k
  let DX := X-X₀
  let DY := Y-Y₀
  let Ux := localQLinear q j
  let Uy := localQLinear q k
  let G := localGainPure p j
  let W := quatPair 0 (q*rimPhase j)
  let da := γ j - Real.sqrt (1-‖p‖^2)
  have hzero : ‖(0:ℂ)‖ ≤ localR := by norm_num [localR]
  have hRnonneg : 0 ≤ localR := by norm_num [localR]
  have nx : ‖x‖ = 1 := pure_score_estimates.base_unit p j
  have ny : ‖y‖ = 1 := pure_score_estimates.base_unit p k
  have nx₀ : ‖X₀‖ = 1 := pure_score_estimates.rim_unit p 0 hp hzero j
  have ny₀ : ‖Y₀‖ = 1 := pure_score_estimates.rim_unit p 0 hp hzero k
  have nX : ‖X‖ = 1 := pure_score_estimates.rim_unit p q hp hq j
  have nY : ‖Y‖ = 1 := pure_score_estimates.rim_unit p q hp hq k
  have nG : ‖G‖ = 1 := pure_score_estimates.pure_gain_unit p hp j
  have hG : ‖G-localAxis‖ ≤ (1031/1000)*localR := by
    linarith [pure_score_estimates.pure_gain_near p hp j]
  have hX₀ : ‖X₀-x‖ ≤ (726/1000)*localR := by linarith [(pure_score_estimates.pure_near p hp j).1]
  have hY₀ : ‖Y₀-y‖ ≤ (726/1000)*localR := by linarith [(pure_score_estimates.pure_near p hp k).1]
  have hX : ‖X-x‖ ≤ (1241/1000)*localR := by
    have h : X-x = DX+(X₀-x) := by dsimp only [DX]; abel
    rw [h]
    refine (norm_add_le _ _).trans ?_
    linarith [(local_q_displacement p q hp hq j).1]
  have hY : ‖Y-y‖ ≤ (1241/1000)*localR := by
    have h : Y-y = DY+(Y₀-y) := by dsimp only [DY]; abel
    rw [h]
    refine (norm_add_le _ _).trans ?_
    linarith [(local_q_displacement p q hp hq k).1]
  have hdx : ‖DX‖ ≤ (515/1000)*‖q‖ := (local_q_displacement p q hp hq j).1
  have hdy : ‖DY‖ ≤ (515/1000)*‖q‖ := (local_q_displacement p q hp hq k).1
  have hux : ‖DX-Ux‖ ≤ (1/5)*localR*‖q‖ := (local_q_displacement p q hp hq j).2
  have huy : ‖DY-Uy‖ ≤ (1/5)*localR*‖q‖ := (local_q_displacement p q hp hq k).2
  have h₁ : |localScore DX G Y₀-localScore Ux localAxis y| ≤
      ((1/5)+(1/2)*(1757/1000))*localR*‖q‖ := by
    refine (local_score_change _ _ _ _ _ _).trans ?_
    rw [ny₀,nG,pure_score_estimates.axis_unit,show ‖Ux‖ = ‖q‖/2 from pure_score_estimates.linear_norm q j]
    calc
      _ ≤ ((1/5)*localR*‖q‖)*1*1 + (‖q‖/2)*((1031/1000)*localR)*1 +
          (‖q‖/2)*1*((726/1000)*localR) := by gcongr
      _ = _ := by ring
  have h₂ : |localScore X₀ G DY-localScore x localAxis Uy| ≤
      ((1/5)+(515/1000)*(1757/1000))*localR*‖q‖ := by
    refine (local_score_change _ _ _ _ _ _).trans ?_
    rw [nx,nG,pure_score_estimates.axis_unit]
    calc
      _ ≤ ((726/1000)*localR)*1*((515/1000)*‖q‖) +
          1*((1031/1000)*localR)*((515/1000)*‖q‖) + 1*1*((1/5)*localR*‖q‖) := by
        gcongr <;> positivity
      _ = _ := by ring
  have h₃ : |localScore DX G DY| ≤ (515/1000)^2*localR*‖q‖ := by
    refine (pure_score_estimates.abs_score _ _ _).trans ?_
    rw [nG]
    have hdx' : ‖DX‖ ≤ (515/1000)*localR := hdx.trans (by gcongr)
    calc
      _ ≤ ((515/1000)*localR)*1*((515/1000)*‖q‖) := by gcongr <;> positivity
      _ = _ := by ring
  have h₄ : |localScore X W Y-localScore x W y| ≤ 2*(1241/1000)*localR*‖q‖ := by
    refine (local_score_change _ _ _ _ _ _).trans ?_
    rw [sub_self,norm_zero,nY,nx,show ‖W‖ = ‖q‖ from local_gain_q_diff q j]
    calc
      _ ≤ ((1241/1000)*localR)*‖q‖*1 + 1*0*1 + 1*‖q‖*((1241/1000)*localR) := by gcongr
      _ = _ := by ring
  have hA' : |localScore X localAxis Y| ≤ 73/100 := by
    have h := local_score_change X x localAxis localAxis Y y
    simp only [sub_self, norm_zero, pure_score_estimates.axis_unit, nY, nx, zero_mul, mul_zero,
      add_zero, mul_one, one_mul,
      show localScore x localAxis y = localT from pure_score_estimates.axis_base p j] at h
    calc
      _ ≤ |localScore X localAxis Y-localT|+|localT| := by
        simpa only [sub_add_cancel] using abs_add_le (localScore X localAxis Y-localT) localT
      _ ≤ _ := by
        have hTpos : 0 < localT := by unfold localT; positivity
        rw [abs_of_pos hTpos]
        norm_num [localR] at hX hY
        linarith only [h,hX,hY,pure_score_estimates.constant_bounds.2.1]
  have hax : |da * localScore X localAxis Y| ≤
      (73/100)*((3*localR*‖q‖+localR*etaMax η)/(198/100)) := by
    rw [abs_mul,mul_comm]
    gcongr
    simpa [da,hγ] using local_gain_axis_diff p q η hp hq he j
  have hsc : |η j * localScore X 1 Y| ≤ (161/100)*localR*etaMax η := by
    rw [abs_mul,mul_comm]
    exact mul_le_mul (local_scalar_bound p q hp hq j) (local_geometry.local_abs_eta η j)
      (abs_nonneg _) (by positivity)
  have hDecomp : (A j : ℍ[ℝ]) = G+W+da • localAxis-(η j) • (1:ℍ[ℝ]) := by
    rw [hA]
    ext <;> simp [G,W,da,localGainPure,localAxis,transverse,quatPair] <;> ring
  have hScore : localScore X (A j : ℍ[ℝ]) Y =
      localScore X₀ G Y₀ + localScore DX G Y₀ + localScore X₀ G DY + localScore DX G DY +
        localScore X W Y + da * localScore X localAxis Y - η j * localScore X 1 Y := by
    rw [hDecomp]
    simp only [DX,DY,localScore,sub_mul,mul_sub,add_mul,mul_add,inner_add_left,
      inner_add_right,inner_sub_left,inner_sub_right,mul_smul_comm,real_inner_smul_left]
    ring
  obtain ⟨h₀,hW⟩ := pure_score_estimates.q_base_identities q j hphase
  change localScore Ux localAxis y+localScore x localAxis Uy = _ at h₀
  change localScore x W y = _ at hW
  rw [hScore]
  have hQ₀ : 0 ≤ localR*‖q‖ := by unfold localR; positivity
  have hE₀ : 0 ≤ localR*etaMax η := mul_nonneg (by norm_num [localR]) (local_geometry.local_eta_nonneg η)
  linarith only [pure_score_estimates.pure_score p hp j, (abs_le.mp h₁).1, (abs_le.mp h₂).1,
    (abs_le.mp h₃).1, (abs_le.mp h₄).1, (abs_le.mp hax).1, (abs_le.mp hsc).2, h₀,hW,hQ₀,hE₀]


private theorem local_edge_pairing (a g b : U) :
    ⟪(g : ℍ[ℝ]), (↑(a⁻¹*b) : ℍ[ℝ])⟫_ℝ =
      localScore (a : ℍ[ℝ]) (g : ℍ[ℝ]) (b : ℍ[ℝ]) := by
  simp only [localScore, Quaternion.inner_def, Submonoid.coe_mul, ← Unitary.star_eq_inv,
    Unitary.coe_star, star_mul, star_star]
  rw [local_geometry.re_cyclic (a : ℍ[ℝ]) (g : ℍ[ℝ]) (star (b : ℍ[ℝ])), mul_assoc]

private theorem local_reverse_pairing (A : Fin 3 → U) (φ : Fin 4 → U) (i j : Fin 4) :
    ⟪(hubGaugedGains A j i : ℍ[ℝ]), (↑((φ j)⁻¹*φ i) : ℍ[ℝ])⟫_ℝ =
      ⟪(hubGaugedGains A i j : ℍ[ℝ]), (↑((φ i)⁻¹*φ j) : ℍ[ℝ])⟫_ℝ := by
  let a := hubGaugedGains A i j
  let b := (φ i)⁻¹*φ j
  have h : (φ j)⁻¹*φ i = b⁻¹ := by simp [b]
  rw [local_geometry.hub_reverse A i j, h]
  change ⟪(a⁻¹ : U).val, (b⁻¹ : U).val⟫_ℝ = ⟪a.val, b.val⟫_ℝ
  simp only [Quaternion.inner_def, ← Unitary.star_eq_inv, Unitary.coe_star, star_star]
  calc
    _ = ((b : ℍ[ℝ]) * star (a : ℍ[ℝ])).re := local_geometry.re_comm _ _
    _ = (star ((a : ℍ[ℝ]) * star (b : ℍ[ℝ]))).re := by rw [star_mul, star_star]
    _ = _ := Quaternion.re_star _

theorem local_minScore {A : Fin 3 → U} {p q : ℂ} {η γ : Fin 3 → ℝ}
    (hp : ‖p‖ ≤ localR) (hq : ‖q‖ ≤ localR) (he : etaMax η ≤ localR)
    (hγ : ∀ j, γ j = Real.sqrt (1-(η j)^2-‖transverse p q j‖^2))
    (hA : ∀ j, (A j : ℍ[ℝ]) = quatPair ⟨-η j,γ j⟩ (transverse p q j))
    (hphase : q*(zeta-1) = ((Real.sqrt 3*‖q‖ : ℝ) : ℂ))
    (i j : Fin 4) (hij : i ≠ j) :
    let φ := phasedPotential p q
    localT + localLinear*‖q‖ - localAlpha*‖p‖^2 - (2/5)*‖p‖^3 - 3*‖p‖^4 -
      (627/100)*localR*‖q‖ - 2*localR*etaMax η ≤
      ⟪(hubGaugedGains A i j : ℍ[ℝ]),
        (↑((φ i)⁻¹ * φ j) : ℍ[ℝ])⟫_ℝ := by
  dsimp only
  let φ := phasedPotential p q
  let B := localT + localLinear*‖q‖ - localAlpha*‖p‖^2 - (2/5)*‖p‖^3 - 3*‖p‖^4 -
    (627/100)*localR*‖q‖ - 2*localR*etaMax η
  have hSpoke (k : Fin 3) : B ≤ localScore 1 1 (localRim p q k) := by
    have h : localScore 1 1 (localRim p q k) = localReal p q := by
      simp [localScore,inner_eq_components,localRim,quatPair]
    rw [h,localReal]
    dsimp only [B]
    linarith only [show 0 ≤ ‖p‖^3 by positivity, show 0 ≤ ‖p‖^4 by positivity,
      show 0 ≤ localR*‖q‖ by unfold localR; positivity,
      mul_nonneg (by norm_num [localR] : 0 ≤ localR) (local_geometry.local_eta_nonneg η)]
  have hF₀ : B ≤ ⟪(hubGaugedGains A 0 1 : ℍ[ℝ]), (↑((φ 0)⁻¹*φ 1) : ℍ[ℝ])⟫_ℝ := by
    rw [local_edge_pairing]
    simpa [localScore,φ,phasedPotential,hubGaugedGains,pure_score_estimates.rim_coe p q hp hq]
      using hSpoke 0
  have hF₁ : B ≤ ⟪(hubGaugedGains A 0 2 : ℍ[ℝ]), (↑((φ 0)⁻¹*φ 2) : ℍ[ℝ])⟫_ℝ := by
    rw [local_edge_pairing]
    simpa [localScore,φ,phasedPotential,hubGaugedGains,pure_score_estimates.rim_coe p q hp hq]
      using hSpoke 1
  have hF₂ : B ≤ ⟪(hubGaugedGains A 0 3 : ℍ[ℝ]), (↑((φ 0)⁻¹*φ 3) : ℍ[ℝ])⟫_ℝ := by
    rw [local_edge_pairing]
    simpa [localScore,φ,phasedPotential,hubGaugedGains,pure_score_estimates.rim_coe p q hp hq]
      using hSpoke 2
  have hR₀ : B ≤ ⟪(hubGaugedGains A 1 2 : ℍ[ℝ]), (↑((φ 1)⁻¹*φ 2) : ℍ[ℝ])⟫_ℝ := by
    rw [local_edge_pairing]
    simpa [B,φ,phasedPotential,hubGaugedGains,pure_score_estimates.rim_coe p q hp hq,
      rimNext] using local_rim_score A p q η γ hp hq he hγ hA hphase 0
  have hR₁ : B ≤ ⟪(hubGaugedGains A 2 3 : ℍ[ℝ]), (↑((φ 2)⁻¹*φ 3) : ℍ[ℝ])⟫_ℝ := by
    rw [local_edge_pairing]
    simpa [B,φ,phasedPotential,hubGaugedGains,pure_score_estimates.rim_coe p q hp hq,
      rimNext] using local_rim_score A p q η γ hp hq he hγ hA hphase 1
  have hR₂ : B ≤ ⟪(hubGaugedGains A 3 1 : ℍ[ℝ]), (↑((φ 3)⁻¹*φ 1) : ℍ[ℝ])⟫_ℝ := by
    rw [local_edge_pairing]
    simpa [B,φ,phasedPotential,hubGaugedGains,pure_score_estimates.rim_coe p q hp hq,
      rimNext] using local_rim_score A p q η γ hp hq he hγ hA hphase 2
  change B ≤ ⟪(hubGaugedGains A i j : ℍ[ℝ]), (↑((φ i)⁻¹*φ j) : ℍ[ℝ])⟫_ℝ
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact hF₀ | exact hF₁ | exact hF₂ | exact hR₀ | exact hR₁ | exact hR₂
    | (rw [local_reverse_pairing A φ]
       first | exact hF₀ | exact hF₁ | exact hF₂ | exact hR₀ | exact hR₁ | exact hR₂)

end RoundQuaternionLocalSharpness
