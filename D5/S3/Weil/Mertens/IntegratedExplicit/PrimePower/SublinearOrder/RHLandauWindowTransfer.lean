/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLandauWindowTransfer
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLandauWindowTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Landau-type uniform ordinate sum bound transfers to harmonic score cancellation on logarithmic time windows. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment

open Finset

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLandauWindowTransfer

/-- Pointwise domination of weights preserves the lower bound on the score deficit. -/
private theorem weighted_deficit_mono {J : Type*} (s : Finset J) (z : J → ℂ) (a b : J → ℝ)
    (hab : ∀ j ∈ s, b j ≤ a j) (hz : ∀ j ∈ s, ‖z j‖ = 1) :
    (∑ j ∈ s, b j) - ‖∑ j ∈ s, (b j : ℂ) * z j‖ ≤
      (∑ j ∈ s, a j) - ‖∑ j ∈ s, (a j : ℂ) * z j‖ := by
  have hsplit : (∑ j ∈ s, (a j : ℂ) * z j) =
      (∑ j ∈ s, (b j : ℂ) * z j) + ∑ j ∈ s, ((a j - b j : ℝ) : ℂ) * z j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    push_cast
    ring
  have hrem : ‖∑ j ∈ s, ((a j - b j : ℝ) : ℂ) * z j‖ ≤ ∑ j ∈ s, (a j - b j) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j hj
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hab j hj)), hz j hj, mul_one]
  have htri := norm_add_le (∑ j ∈ s, (b j : ℂ) * z j)
      (∑ j ∈ s, ((a j - b j : ℝ) : ℂ) * z j)
  rw [← hsplit] at htri
  rw [Finset.sum_sub_distrib] at hrem
  linarith


theorem band_deficit {J : Type*} [DecidableEq J] (s B : Finset J)
    (z : J → ℂ) (a m : J → ℝ) {c : ℝ} (hc : 0 ≤ c) (hBs : B ⊆ s)
    (ha : ∀ j ∈ s, 0 ≤ a j) (hdom : ∀ j ∈ B, c * m j ≤ a j)
    (hz : ∀ j ∈ s, ‖z j‖ = 1) :
    c * ((∑ j ∈ B, m j) - ‖∑ j ∈ B, (m j : ℂ) * z j‖) ≤
      (∑ j ∈ s, a j) - ‖∑ j ∈ s, (a j : ℂ) * z j‖ := by
  let b (j : J) := if j ∈ B then c * m j else 0
  have hdom' : ∀ j ∈ s, b j ≤ a j := by
    intro j hj
    by_cases hb : j ∈ B
    · simpa [b, hb] using hdom j hb
    · simpa [b, hb] using ha j hj
  have h := weighted_deficit_mono s z a b hdom' hz
  have hsum : (∑ j ∈ s, b j) = c * ∑ j ∈ B, m j := by
    rw [← Finset.sum_subset hBs (fun j _ hj => by simp [b,hj])]
    simp only [b]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [hj]
  have hscore : (∑ j ∈ s, (b j : ℂ) * z j) =
      (c : ℂ) * ∑ j ∈ B, (m j : ℂ) * z j := by
    rw [← Finset.sum_subset hBs (fun j _ hj => by simp [b,hj])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [b,hj,mul_assoc]
  rw [hsum,hscore,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc] at h
  rwa [mul_sub]

open Filter
open scoped Topology
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase norm_phase)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (complexScore)

theorem harmonic_band_transfer (rh : RiemannHypothesis) :
    ∃ L : ℝ, 1 < L ∧ ∀ T : ℝ, L ≤ T → ∀ t : ℝ,
      let s := positiveCutoff rh T
      let B := s \ positiveCutoff rh (T * (3/4))
      let m (j : PositiveZetaZero) : ℝ := Zeta23.zeroMult j.val
      let g : ↥s → ℝ := fun j => ordinate j.1
      let w : ↥s → ℝ := fun j => harmonicWeight j.1 / harmonicMass rh T
      ‖∑ j ∈ B, (m j : ℂ) * phase (ordinate j) t‖ ≤ T*Real.log T/(32*Real.pi) →
      1/(32*Real.log T) ≤ 1-‖complexScore g w t‖ := by
  classical
  let S := zetaSpectrum rh
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0<c := by dsimp [c]; positivity
  have hN : CountAsymptotic S := zetaSpectrum_countAsymptotic rh
  have hscaled := count_scaled_limit S hN (u:=3/4) (by norm_num)
  have hdiff : Tendsto (fun T : ℝ => (S.N T-S.N (T*(3/4)) : ℝ)/(T*Real.log T)) atTop (𝓝 (c/4)) := by
    have h := hN.sub hscaled
    convert h using 1
    · ext T; ring
    · dsimp [c]; ring
  have hmass : Tendsto (fun T : ℝ => harmonicMass rh T/(Real.log T)^2) atTop (𝓝 (c/2)) := by
    convert harmonic_mass_limit rh using 2 <;> dsimp [c] <;> ring
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.1 (hdiff.eventually_const_lt (show c/8<c/4 by linarith))
  obtain ⟨M,hM⟩ := eventually_atTop.1 (hmass.eventually_lt_const (show c/2<c by linarith))
  let L := max (max L₀ M) 4
  refine ⟨L, (by dsimp [L]; have := le_max_right (max L₀ M) (4:ℝ); linarith), ?_⟩
  intro T hLT t s B m g w hcan
  have hT : 4≤T := (le_max_right _ _).trans hLT
  have hTpos : 0<T := by linarith
  have hlog : 0<Real.log T := Real.log_pos (by linarith)
  have hcut : positiveCutoff rh (T*(3/4)) ⊆ s := cutoff_mono rh (by linarith)
  have hBs : B⊆s := Finset.sdiff_subset
  have hdom (j : PositiveZetaZero) (hj : j∈B) : m j/(2*T) ≤ harmonicWeight j :=
    upper_weight rh (by linarith) hj
  have hcount : (c/8)*(T*Real.log T) ≤ (S.N T : ℝ)-(S.N (T*(3/4)) : ℝ) :=
    (lt_div_iff₀ (by positivity)).mp (hL₀ T (((le_max_left L₀ M).trans (le_max_left _ (4:ℝ))).trans hLT)) |>.le
  have hsumB : (∑ j ∈ B,m j) = (S.N T : ℝ)-(S.N (T*(3/4)) : ℝ) := by
    have he := Finset.sum_sdiff hcut (f := m)
    have e (U : ℝ) : (∑ j ∈ positiveCutoff rh U, m j) = (S.N U : ℝ) := by
      change (∑ j ∈ positiveCutoff rh U, (Zeta23.zeroMult j.val:ℝ)) =
        ((∑ j ∈ positiveCutoff rh U, Zeta23.zeroMult j.val : ℕ) : ℝ)
      rw [Nat.cast_sum]
    change (∑ j ∈ B,m j)+(∑ j ∈ positiveCutoff rh (T*(3/4)),m j) = (∑ j ∈ s,m j) at he
    rw [e (T*(3/4)),show (∑ j ∈ s,m j) = (S.N T : ℝ) from e T] at he
    linarith
  have hhalf : ‖∑ j ∈ B, (m j : ℂ)*phase (ordinate j) t‖ ≤ (∑ j ∈ B,m j)/2 := by
    apply hcan.trans
    rw [hsumB]
    have h : T*Real.log T/(32*Real.pi)=((c/8)*(T*Real.log T))/2 := by
      dsimp [c]
      ring
    rw [h]
    linarith
  let W := harmonicMass rh T
  let Zraw := ∑ j ∈ s, (harmonicWeight j:ℂ)*phase (ordinate j) t
  have hD := band_deficit s B (fun j => phase (ordinate j) t) harmonicWeight m
    (c:=1/(2*T)) (by positivity) hBs (fun j _=>weight_nonneg j)
    (fun j hj=>by simpa [div_eq_mul_inv,mul_comm] using hdom j hj)
    (fun j _=>norm_phase _ _)
  change (1/(2*T))*((∑ j∈B,m j)-‖∑ j∈B,(m j:ℂ)*phase (ordinate j) t‖) ≤ W-‖Zraw‖ at hD
  have hm : c*Real.log T/32 ≤ W-‖Zraw‖ := by
    calc
      _ = (1/(2*T))*(((c/8)*(T*Real.log T))/2) := by field_simp; ring
      _ ≤ (1/(2*T))*((∑ j∈B,m j)/2) := by
        rw [hsumB]
        exact mul_le_mul_of_nonneg_left (by linarith only [hcount]) (by positivity)
      _ ≤ (1/(2*T))*((∑ j∈B,m j)-‖∑ j∈B,(m j:ℂ)*phase (ordinate j) t‖) :=
        mul_le_mul_of_nonneg_left (by linarith only [hhalf]) (by positivity)
      _ ≤ _ := hD
  have hWpos : 0<W := by
    have : 0 < c*Real.log T/32 := by positivity
    linarith [norm_nonneg Zraw]
  have hWup : W≤c*(Real.log T)^2 :=
    (div_lt_iff₀ (sq_pos_of_pos hlog)).mp
      (hM T (((le_max_right L₀ M).trans (le_max_left _ (4:ℝ))).trans hLT)) |>.le
  have hZ : complexScore g w t=Zraw/(W:ℂ) := by
    unfold complexScore
    change (∑ j : ↥s, ((harmonicWeight j.1/W:ℝ):ℂ)*phase (ordinate j.1) t)=_
    rw [Finset.sum_coe_sort s (fun j => ((harmonicWeight j/W:ℝ):ℂ)*phase (ordinate j) t)]
    dsimp [Zraw]
    simp_rw [Complex.ofReal_div,div_mul_eq_mul_div]
    rw [Finset.sum_div]
  have hnorm : ‖Zraw‖=W*‖complexScore g w t‖ := by
    rw [hZ,Complex.norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hWpos]
    field_simp
  rw [hnorm] at hm
  have hD' : c*Real.log T/32 ≤ W*(1-‖complexScore g w t‖) := by linarith
  have hD0 : 0≤1-‖complexScore g w t‖ :=
    nonneg_of_mul_nonneg_right ((by positivity : 0≤c*Real.log T/32).trans hD') hWpos
  have hh := hD'.trans (mul_le_mul_of_nonneg_right hWup hD0)
  have hfinal : Real.log T/32≤(Real.log T)^2*(1-‖complexScore g w t‖) := by
    apply (mul_le_mul_iff_left₀ hc).mp
    nlinarith only [hh]
  apply (div_le_iff₀ (show 0<32*Real.log T by positivity)).mpr
  nlinarith only [hfinal, hlog, mul_nonneg hD0 hlog.le]


private theorem uniform_landau_envelope (b : ℝ) (hb : 0 < b) :
    ∃ L : ℝ, 4 ≤ L ∧ ∀ T V t : ℝ, L ≤ T → 1 < V → V ≤ T →
      b/Real.log T ≤ t → t ≤ Real.log T →
      V + Real.exp (t/2)*(1+t)^2 + Real.exp (t/2)*(1+Real.log V) +
          Real.log V/t ≤ (7+1/b)*T := by
  have he := (isLittleO_log_rpow_atTop (r := 1/4) (by norm_num)).bound
    (show (0:ℝ)<1 by norm_num)
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.1 he
  refine ⟨max L₀ 4, le_max_right _ _, ?_⟩
  intro T V t hLT hV hVT htlo hthi
  have hT : 4≤T := (le_max_right _ _).trans hLT
  have hT0 : 0<T := by linarith
  have hl : 0<Real.log T := Real.log_pos (by linarith)
  have ht : 0<t := (div_pos hb hl).trans_le htlo
  let q := T^(1/4:ℝ)
  have hq : 1≤q := by
    dsimp [q]; exact Real.one_le_rpow (by linarith) (by norm_num)
  have hlogq : Real.log T≤q := by
    have h := hL₀ T ((le_max_left _ _).trans hLT)
    rw [Real.norm_eq_abs,abs_of_pos hl,Real.norm_eq_abs,abs_of_nonneg (by positivity),one_mul] at h
    exact h
  have hq4 : q^4=T := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast hT0.le]
    norm_num
  have hexp : Real.exp (t/2) ≤ q^2 := by
    have h := Real.exp_le_exp.mpr (show t/2≤Real.log T/2 by linarith)
    dsimp [q]
    rw [← Real.rpow_mul_natCast hT0.le]
    norm_num
    rw [Real.rpow_def_of_pos hT0]
    convert h using 1 <;> ring
  have hvlog : 0<Real.log V := Real.log_pos hV
  have hlogV : Real.log V≤Real.log T := Real.log_le_log (by linarith) hVT
  have hq0 : 0≤q := by linarith
  have hq2 : q^2≤T := by nlinarith only [hq4, sq_nonneg q, mul_nonneg (sub_nonneg.mpr (one_le_pow₀ hq (n:=2))) (sq_nonneg q)]
  have hterm1 : Real.exp (t/2)*(1+t)^2 ≤ 4*T := by
    have h1 : (1+t) ≤ 2*q := by linarith
    have h2 := pow_le_pow_left₀ (by linarith : 0≤1+t) h1 2
    calc
      _ ≤ q^2*(2*q)^2 := mul_le_mul hexp h2 (by positivity) (by positivity)
      _ = 4*T := by nlinarith only [hq4]
  have hterm2 : Real.exp (t/2)*(1+Real.log V) ≤ 2*T := by
    have h1 : 1+Real.log V ≤ 2*q := by linarith
    have h2 : q≤q^2 := by nlinarith only [mul_nonneg hq0 (sub_nonneg.mpr hq)]
    calc
      _ ≤ q^2*(2*q) := mul_le_mul hexp h1 (by linarith) (by positivity)
      _ ≤ q^2*(2*q^2) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 2*T := by nlinarith only [hq4]
  have hterm3 : Real.log V/t ≤ T/b := by
    apply (div_le_div_iff₀ ht hb).mpr
    have ha : b ≤ t*Real.log T := (div_le_iff₀ hl).mp htlo
    have hh := mul_le_mul_of_nonneg_right ha hl.le
    have hsq : (Real.log T)^2≤T := (pow_le_pow_left₀ hl.le hlogq 2).trans hq2
    have h₁ := mul_le_mul_of_nonneg_right hlogV hb.le
    have h₂ := mul_le_mul_of_nonneg_left hsq ht.le
    nlinarith only [hh,h₁,h₂]
  calc
    _ ≤ T+4*T+2*T+T/b := by linarith
    _ = _ := by ring


theorem harmonic_landau_window_deficit (rh : RiemannHypothesis) (b C : ℝ)
    (hb : 0 < b) (hC : 0 < C)
    (hLandau : ∀ V t : ℝ, 1 < V → 0 < |t| →
      ‖∑ j ∈ positiveCutoff rh V, (Zeta23.zeroMult j.val : ℂ)*phase (ordinate j) t‖ ≤
        C*(V+Real.exp (|t|/2)*(1+|t|)^2+Real.exp (|t|/2)*(1+Real.log V)+Real.log V/|t|)) :
    ∃ L : ℝ, 1<L ∧ ∀ T t : ℝ, L≤T → b/Real.log T≤|t| → |t|≤Real.log T →
      let g : ↥(positiveCutoff rh T) → ℝ := fun j => ordinate j.1
      let w : ↥(positiveCutoff rh T) → ℝ := fun j => harmonicWeight j.1/harmonicMass rh T
      1/(32*Real.log T) ≤ 1-‖complexScore g w t‖ := by
  classical
  obtain ⟨L₀,hL₀,htransfer⟩ := harmonic_band_transfer rh
  obtain ⟨M,hM,henv⟩ := uniform_landau_envelope b hb
  let K := C*(7+1/b)
  have hK : 0<K := by dsimp [K]; positivity
  obtain ⟨A,hA⟩ := eventually_atTop.1
    (Real.tendsto_log_atTop.eventually_ge_atTop (64*Real.pi*K))
  let L := max (max L₀ M) A
  refine ⟨L,hL₀.trans_le ((le_max_left L₀ M).trans (le_max_left _ _)),?_⟩
  intro T t hLT htlo hthi g w
  have hLM : M≤T := ((le_max_right L₀ M).trans (le_max_left _ _)).trans hLT
  have hT : 4≤T := hM.trans hLM
  have ht : 0 < |t| := (div_pos hb (Real.log_pos (by linarith))).trans_le htlo
  let s := positiveCutoff rh T
  let B := s \ positiveCutoff rh (T*(3/4))
  let f (j : PositiveZetaZero) : ℂ := (Zeta23.zeroMult j.val:ℂ)*phase (ordinate j) t
  have hcut : positiveCutoff rh (T*(3/4))⊆s := cutoff_mono rh (by linarith)
  have hsum : (∑ j ∈ B,f j) =
      (∑ j ∈ s,f j)-(∑ j ∈ positiveCutoff rh (T*(3/4)),f j) := by
    have h := Finset.sum_sdiff hcut (f:=f)
    change (∑ j ∈ B,f j)+(∑ j ∈ positiveCutoff rh (T*(3/4)),f j)=(∑ j ∈ s,f j) at h
    exact eq_sub_of_add_eq h
  have hu (V : ℝ) (hv : 1<V) (hvT : V≤T) :
      ‖∑ j ∈ positiveCutoff rh V,f j‖ ≤ K*T := by
    calc
      _ ≤ C*(V+Real.exp (|t|/2)*(1+|t|)^2+
        Real.exp (|t|/2)*(1+Real.log V)+Real.log V/|t|) := hLandau V t hv ht
      _ ≤ C*((7+1/b)*T) :=
        mul_le_mul_of_nonneg_left (henv T V |t| hLM hv hvT htlo hthi) hC.le
      _ = _ := by dsimp [K]; ring
  have hband : ‖∑ j ∈ B,f j‖ ≤ T*Real.log T/(32*Real.pi) := by
    rw [hsum]
    have hlog := hA T ((le_max_right _ _).trans hLT)
    calc
      _ ≤ ‖∑ j ∈ s,f j‖+‖∑ j ∈ positiveCutoff rh (T*(3/4)),f j‖ := norm_sub_le _ _
      _ ≤ K*T+K*T := add_le_add (hu T (by linarith) le_rfl) (hu _ (by linarith) (by linarith))
      _ ≤ _ := by
        apply (le_div_iff₀ (by positivity : 0<32*Real.pi)).mpr
        nlinarith only [mul_le_mul_of_nonneg_left hlog (show 0≤T by linarith)]
  apply htransfer T (((le_max_left L₀ M).trans (le_max_left _ _)).trans hLT) t
  exact_mod_cast hband


end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHLandauWindowTransfer
