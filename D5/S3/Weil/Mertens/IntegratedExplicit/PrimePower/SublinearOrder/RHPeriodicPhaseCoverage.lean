/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHPeriodicPhaseCoverage
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHPeriodicPhaseCoverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual short-window zero counts control the weighted Fourier score on logarithmic time windows. -/

import D5.S3.Weil.ZeroData.CumulativeRvmError
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment

open Finset Filter
open scoped Topology
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder
open D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHHarmonicPairMoment
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness (PositiveZetaZero ordinate)
open D5.S3.Weil.ZeroData.PositiveOrdinateSpectrum
open D5.S3.Analytic.Oscillation.OrdinateCounting
open D5.S3.Weil.DirichletPolynomialMeanSquare (phase norm_phase)
open D5.S3.Fourier.Concentration.FiniteTailMomentMissingWindow (complexScore)

noncomputable section

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHPeriodicPhaseCoverage

private theorem two_arc_deficit {J : Type*} (s A B : Finset J)
    (z : J → ℂ) (w : J → ℝ) {m : ℝ}
    (hAs : A ⊆ s) (hBs : B ⊆ s)
    (hw : ∀ j ∈ s, 0 ≤ w j) (hz : ∀ j ∈ s, ‖z j‖=1)
    (hA : ∀ j ∈ A, ‖z j-1‖ ≤ 1/2) (hB : ∀ j ∈ B, ‖z j+1‖ ≤ 1/2)
    (hmA : m ≤ ∑ j ∈ A,w j) (hmB : m ≤ ∑ j ∈ B,w j) :
    m/2 ≤ (∑ j ∈ s,w j)-‖∑ j ∈ s,(w j:ℂ)*z j‖ := by
  classical
  let S := ∑ j ∈ s,(w j:ℂ)*z j
  obtain ⟨u,hu,hprojection⟩ : ∃ u : ℂ, ‖u‖=1 ∧ ((starRingEnd ℂ) u*S).re=‖S‖ := by
    by_cases hS : S=0
    · exact ⟨1,by simp,by simp [hS]⟩
    · let u := S/(‖S‖:ℂ)
      have hnorm : 0 < ‖S‖ := norm_pos_iff.mpr hS
      refine ⟨u,?_,?_⟩
      · dsimp [u]
        rw [Complex.norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hnorm,div_self hnorm.ne']
      · have he : (starRingEnd ℂ) u*S=(‖S‖:ℂ) := by
          dsimp [u]
          rw [map_div₀]
          simp only [Complex.conj_ofReal,div_mul_eq_mul_div,Complex.conj_mul']
          have hn : (‖S‖:ℂ) ≠ 0 := by exact_mod_cast hnorm.ne'
          field_simp
        rw [he,Complex.ofReal_re]
  let P (j : J) := ((starRingEnd ℂ) u*z j).re
  have hP (j : J) (hj : j∈s) : P j≤1 := by
    calc
      _ ≤ ‖(starRingEnd ℂ) u*z j‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul,Complex.norm_conj,hu,hz j hj,one_mul]
  have hsum : ‖S‖=∑ j ∈ s,w j*P j := by
    rw [← hprojection]
    dsimp [S,P]
    rw [mul_sum]
    simp only [Complex.re_sum]
    apply sum_congr rfl
    intro j hj
    rw [show (starRingEnd ℂ) u*((w j:ℂ)*z j) = (w j:ℂ)*((starRingEnd ℂ) u*z j) by ring]
    simp
  have hdef (U : Finset J) (hUs : U ⊆ s) (hU : ∀ j∈U,P j ≤ 1/2)
      (hm : m ≤ ∑ j∈U,w j) : m/2 ≤ (∑ j∈s,w j)-‖S‖ := by
    rw [hsum,← Finset.sum_sub_distrib]
    calc
      m/2 ≤ (∑ j∈U,w j)/2 := by linarith
      _ = ∑ j∈U,w j/2 := by rw [Finset.sum_div]
      _ ≤ ∑ j∈U,(w j-w j*P j) := by
        apply sum_le_sum
        intro j hj
        have h := mul_le_mul_of_nonneg_left (hU j hj) (hw j (hUs hj))
        linarith
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hUs (fun j hj _ => by
        have h := mul_le_mul_of_nonneg_left (hP j hj) (hw j hj)
        linarith)
  change m/2 ≤ (∑ j ∈ s,w j)-‖S‖
  by_cases hre : 0 ≤ u.re
  · apply hdef B hBs _ hmB
    intro j hj
    have h := Complex.re_le_norm ((starRingEnd ℂ) u*(z j+1))
    rw [norm_mul,Complex.norm_conj,hu,one_mul] at h
    have he : ((starRingEnd ℂ) u*(z j+1)).re=P j+u.re := by simp [P,mul_add]
    rw [he] at h
    linarith [hB j hj]
  · apply hdef A hAs _ hmA
    intro j hj
    have h := Complex.re_le_norm ((starRingEnd ℂ) u*(z j-1))
    rw [norm_mul,Complex.norm_conj,hu,one_mul] at h
    have he : ((starRingEnd ℂ) u*(z j-1)).re=P j-u.re := by simp [P,mul_sub]
    rw [he] at h
    linarith [hA j hj]

private theorem weight_lower {T : ℝ} {j : PositiveZetaZero}
    (hlo : 1/2 ≤ ordinate j) (hhi : ordinate j ≤ T) :
    (Zeta23.zeroMult j.val : ℝ)/(2*T) ≤ harmonicWeight j := by
  have hg : 0 < ordinate j := j.property.2
  have hT : 0 < T := hg.trans_le hhi
  have hratio : 1/(2*T) ≤ ordinate j/(1/4+(ordinate j)^2) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) hg.le,
      mul_nonneg (sub_nonneg.mpr hlo) (add_nonneg hg.le (by norm_num : (0:ℝ)≤1/2))]
  have h := mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg (Zeta23.zeroMult j.val))
  unfold harmonicWeight
  convert h using 1 <;> ring

private def arc (rh : RiemannHypothesis) (x y : ℝ) : Finset PositiveZetaZero :=
  positiveCutoff rh y \ positiveCutoff rh x

private theorem arc_mem (rh : RiemannHypothesis) (x y : ℝ) (j : PositiveZetaZero) :
    j ∈ arc rh x y ↔ x < ordinate j ∧ ordinate j ≤ y := by
  simp only [arc,Finset.mem_sdiff,cutoff_mem,not_le]
  tauto

private theorem arc_mass (rh : RiemannHypothesis) {x y T : ℝ}
    (hx : T/2 ≤ x) (hxy : x ≤ y) (hy : y ≤ T) (hT : 1 ≤ T) :
    (Zeta23.Ncount x y : ℝ)/(2*T) ≤ ∑ j ∈ arc rh x y,harmonicWeight j := by
  classical
  have hsub := cutoff_mono rh hxy
  have hcount (U : ℝ) :
      (∑ j ∈ positiveCutoff rh U, (Zeta23.zeroMult j.val : ℝ)) =
        (Zeta23.Ncount 0 U : ℝ) := by
    have h := zetaSpectrum_N rh U
    rw [Zeta23.zetaZeroConfig_N] at h
    rw [← h]
    change (∑ j ∈ positiveCutoff rh U,(Zeta23.zeroMult j.val : ℝ)) =
      ((∑ j ∈ positiveCutoff rh U,Zeta23.zeroMult j.val : ℕ):ℝ)
    rw [Nat.cast_sum]
  have hdiff : (∑ j ∈ arc rh x y,(Zeta23.zeroMult j.val:ℝ)) =
      (Zeta23.Ncount x y:ℝ) := by
    have hs := Finset.sum_sdiff hsub (f := fun j : PositiveZetaZero => (Zeta23.zeroMult j.val:ℝ))
    change (∑ j ∈ arc rh x y,(Zeta23.zeroMult j.val:ℝ)) +
      (∑ j ∈ positiveCutoff rh x,(Zeta23.zeroMult j.val:ℝ)) =
      (∑ j ∈ positiveCutoff rh y,(Zeta23.zeroMult j.val:ℝ)) at hs
    rw [hcount,hcount] at hs
    have hn := Zeta23.Ncount_add (show 0≤x by linarith) hxy
    exact_mod_cast (show (∑ j ∈ arc rh x y,(Zeta23.zeroMult j.val:ℝ)) =
      (Zeta23.Ncount x y:ℝ) by rw [hn,Nat.cast_add] at hs; linarith)
  rw [← hdiff,Finset.sum_div]
  apply sum_le_sum
  intro j hj
  have hmem := (arc_mem rh x y j).mp hj
  exact weight_lower (by linarith [hmem.1]) (hmem.2.trans hy)

/-- Each period's two short arcs lie close to the two opposite real directions. -/
private theorem period_phase {H t γ : ℝ} (_hH : 0<H) (ht : 0<t)
    (hHt : H*t=2*Real.pi) (k : ℕ) (b : Bool)
    (hlo : (k:ℝ)*H+(if b then H/2 else 0) ≤ γ)
    (hhi : γ ≤ (k:ℝ)*H+(if b then H/2 else 0)+H/16) :
    ‖phase γ t - (if b then (-1:ℂ) else 1)‖ ≤ 1/2 := by
  let x := (k:ℝ)*H+(if b then H/2 else 0)
  have hd0 : 0≤γ-x := by dsimp [x]; linarith
  have hd : γ-x≤H/16 := by dsimp [x]; linarith
  have hangle : (γ-x)*t ≤ Real.pi/8 := by
    have h := mul_le_mul_of_nonneg_right hd ht.le
    nlinarith only [h,hHt]
  have hp : phase x t = (if b then (-1:ℂ) else 1) := by
    cases b
    · have hx : x=(k:ℝ)*H := by simp [x]
      rw [hx]
      unfold phase
      have he : (((k:ℝ)*H:ℝ):ℂ)*Complex.I*(t:ℂ) =
          (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
        push_cast
        have hh : (H:ℂ)*(t:ℂ)=2*(Real.pi:ℂ) := by exact_mod_cast hHt
        calc
          _ = (k:ℂ)*((H:ℂ)*(t:ℂ))*Complex.I := by ring
          _ = _ := by rw [hh]; ring
      rw [he,Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow]
      rfl
    · have hx : x=(k:ℝ)*H+H/2 := by simp [x]
      rw [hx]
      unfold phase
      have he : ((((k:ℝ)*H+H/2:ℝ):ℂ))*Complex.I*(t:ℂ) =
          (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)+(Real.pi:ℂ)*Complex.I := by
        push_cast
        have hh : (H:ℂ)*(t:ℂ)=2*(Real.pi:ℂ) := by exact_mod_cast hHt
        calc
          _ = ((k:ℂ)+1/2)*((H:ℂ)*(t:ℂ))*Complex.I := by ring
          _ = _ := by rw [hh]; ring
      rw [he,Complex.exp_add,Complex.exp_nat_mul,Complex.exp_two_pi_mul_I,one_pow,one_mul,
        Complex.exp_pi_mul_I]
      rfl
  have hsplit : phase γ t=phase x t*Complex.exp (Complex.I*(((γ-x)*t:ℝ):ℂ)) := by
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hp,hsplit,← mul_sub_one,norm_mul,norm_phase,one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := (γ-x)*t)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hd0 ht.le)] at h
  exact h.trans (hangle.trans (by linarith [Real.pi_lt_four]))


private theorem periodic_arc_mass (rh : RiemannHypothesis) {T H t L K : ℝ}
    (hT : 4≤T) (hL : L≤T/2) (hK : 0<K)
    (hH : 0<H) (ht : 0<t) (hHt : H*t=2*Real.pi)
    (hsize : 8*H≤T) (hwidth : K*Real.log T≤H/16)
    (hcnt : ∀ x y : ℝ, L≤x → x+K*Real.log x≤y → y≤2*x →
      (y-x)*Real.log x/(8*Real.pi)≤(Zeta23.Ncount x y:ℝ))
    (b : Bool) :
    ∃ U : Finset PositiveZetaZero, U ⊆ positiveCutoff rh T ∧
      (∀ j ∈ U, ‖phase (ordinate j) t-(if b then (-1:ℂ) else 1)‖≤1/2) ∧
      Real.log T/(4096*Real.pi) ≤ ∑ j ∈ U,harmonicWeight j := by
  classical
  have hT0 : 0<T := by linarith
  have hlog : 0<Real.log T := Real.log_pos (by linarith)
  let n := ⌊T/(4*H)⌋₊
  let k0 := ⌈T/(2*H)⌉₊
  let shift : ℝ := if b then H/2 else 0
  have hs0 : 0 ≤ shift := by dsimp [shift]; split <;> positivity
  have hs1 : shift ≤ H/2 := by dsimp [shift]; split <;> linarith
  have hnup : (n:ℝ)≤T/(4*H) := Nat.floor_le (by positivity)
  have hnlo : T/(8*H)≤(n:ℝ) := by
    have hh : T/(4*H)<(n:ℝ)+1 := Nat.lt_floor_add_one _
    have htwo : 2≤T/(4*H) := by
      apply (le_div_iff₀ (by positivity : 0<4*H)).mpr
      nlinarith only [hsize]
    nlinarith only [hh,htwo,show T/(4*H)=2*(T/(8*H)) by ring]
  have hk0lo : T/(2*H)≤(k0:ℝ) := Nat.le_ceil _
  have hk0hi : (k0:ℝ)<T/(2*H)+1 := Nat.ceil_lt_add_one (by positivity)
  let x (k : ℕ) := ((k0+k:ℕ):ℝ)*H+shift
  let y (k : ℕ) := x k+H/16
  let C (k : ℕ) := arc rh (x k) (y k)
  let U := (range n).biUnion C
  have hklo (k : ℕ) : T/2≤x k := by
    have h := mul_le_mul_of_nonneg_right hk0lo hH.le
    have he : T/(2*H)*H=T/2 := by field_simp
    rw [he] at h
    dsimp [x]
    push_cast
    nlinarith only [h,hs0,mul_nonneg (Nat.cast_nonneg k) hH.le]
  have hkhi (k : ℕ) (hk : k∈range n) : y k≤T := by
    have hkn : (k:ℝ)+1≤n := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hk)
    have hk : (k:ℝ)+1≤T/(4*H) := hkn.trans hnup
    have hsum : (k0:ℝ)+(k:ℝ)+1 ≤T/(2*H)+1+T/(4*H) := by linarith
    have h := mul_le_mul_of_nonneg_right hsum hH.le
    have he : (T/(2*H)+1+T/(4*H))*H=3*T/4+H := by field_simp; ring
    rw [he] at h
    dsimp [y,x]
    push_cast
    nlinarith only [h,hs1,hsize,hH]
  have hloghalf : Real.log T/2 ≤ Real.log (T/2) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) hT
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    rw [Real.log_div hT0.ne' (by norm_num)]
    norm_num at hh
    linarith
  have hmass (k : ℕ) (hk : k∈range n) :
      H*Real.log T/(512*Real.pi*T) ≤ ∑ j ∈ C k,harmonicWeight j := by
    have hx := hklo k
    have hy := hkhi k hk
    have hxpos : 0<x k := by linarith
    have hxy : x k≤y k := by dsimp [y]; linarith
    have hlogxlo : Real.log T/2≤Real.log (x k) :=
      hloghalf.trans (Real.log_le_log (by positivity : 0<T/2) hx)
    have hwidth' : x k+K*Real.log (x k)≤y k := by
      have h := (mul_le_mul_of_nonneg_left (Real.log_le_log hxpos (hxy.trans hy)) hK.le).trans hwidth
      dsimp [y]
      linarith
    have hcount := hcnt (x k) (y k) (hL.trans hx) hwidth' (by linarith)
    have hlow : H*Real.log T/(256*Real.pi)≤(Zeta23.Ncount (x k) (y k):ℝ) := by
      calc
        _ = (H/16)*(Real.log T/2)/(8*Real.pi) := by ring
        _ ≤ (H/16)*Real.log (x k)/(8*Real.pi) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogxlo (by positivity)) (by positivity)
        _ = (y k-x k)*Real.log (x k)/(8*Real.pi) := by dsimp [y]; ring
        _ ≤ _ := hcount
    have h := div_le_div_of_nonneg_right hlow (show 0≤2*T by positivity)
    calc
      _ = (H*Real.log T/(256*Real.pi))/(2*T) := by ring
      _ ≤ (Zeta23.Ncount (x k) (y k):ℝ)/(2*T) := h
      _ ≤ _ := arc_mass rh hx hxy hy (by linarith)
  have hdisj : (↑(range n) : Set ℕ).PairwiseDisjoint C := by
    intro i hi j hj hij
    rw [Function.onFun,Finset.disjoint_left]
    intro r hri hrj
    have hi' := (arc_mem rh (x i) (y i) r).mp hri
    have hj' := (arc_mem rh (x j) (y j) r).mp hrj
    rcases lt_or_gt_of_ne hij with hlt|hlt
    · have hcast : ((k0+i:ℕ):ℝ)+1≤((k0+j:ℕ):ℝ) := by
        exact_mod_cast (show k0+i+1≤k0+j by omega)
      have hh := mul_le_mul_of_nonneg_right hcast hH.le
      dsimp [x,y] at hi' hj'
      linarith
    · have hcast : ((k0+j:ℕ):ℝ)+1≤((k0+i:ℕ):ℝ) := by
        exact_mod_cast (show k0+j+1≤k0+i by omega)
      have hh := mul_le_mul_of_nonneg_right hcast hH.le
      dsimp [x,y] at hi' hj'
      linarith
  have hUs : U⊆positiveCutoff rh T := by
    intro j hj
    obtain ⟨k,hk,hj⟩ := Finset.mem_biUnion.mp hj
    exact (cutoff_mem rh T j).mpr (((arc_mem rh (x k) (y k) j).mp hj).2.trans (hkhi k hk))
  have hphase (j : PositiveZetaZero) (hj : j∈U) :
      ‖phase (ordinate j) t-(if b then (-1:ℂ) else 1)‖≤1/2 := by
    obtain ⟨k,hk,hj⟩ := Finset.mem_biUnion.mp hj
    have hm := (arc_mem rh (x k) (y k) j).mp hj
    exact period_phase hH ht hHt (k0+k) b hm.1.le hm.2
  refine ⟨U,hUs,hphase,?_⟩
  rw [Finset.sum_biUnion hdisj]
  calc
    _ = (T/(8*H))*(H*Real.log T/(512*Real.pi*T)) := by field_simp; ring
    _ ≤ (n:ℝ)*(H*Real.log T/(512*Real.pi*T)) :=
      mul_le_mul_of_nonneg_right hnlo (by positivity)
    _ = ∑ k∈range n,H*Real.log T/(512*Real.pi*T) := by simp
    _ ≤ _ := sum_le_sum hmass


private theorem raw_score_even (s : Finset PositiveZetaZero) (t : ℝ) :
    ‖∑ j∈s,(harmonicWeight j:ℂ)*phase (ordinate j) (-t)‖ =
      ‖∑ j∈s,(harmonicWeight j:ℂ)*phase (ordinate j) t‖ := by
  have hphase (g : ℝ) : phase g (-t) = (starRingEnd ℂ) (phase g t) := by
    unfold phase
    rw [← Complex.exp_conj]
    push_cast
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    ring_nf
  have he : (∑ j∈s,(harmonicWeight j:ℂ)*phase (ordinate j) (-t)) =
      (starRingEnd ℂ) (∑ j∈s,(harmonicWeight j:ℂ)*phase (ordinate j) t) := by
    rw [map_sum]
    apply sum_congr rfl
    intro j hj
    rw [map_mul,Complex.conj_ofReal,hphase]
  rw [he,Complex.norm_conj]

/-- Short-window zero counts force a logarithmic-mass fraction into both
opposite phase arcs, uniformly up to reciprocal-logarithmic time. -/
theorem harmonic_periodic_phase_deficit (rh : RiemannHypothesis) :
    ∃ L b : ℝ, 1<L ∧ 0<b ∧ ∀ T t : ℝ, L≤T →
      16*Real.pi/T≤|t| → |t|≤b/Real.log T →
      let g : ↥(positiveCutoff rh T) → ℝ := fun j => ordinate j.1
      let w : ↥(positiveCutoff rh T) → ℝ := fun j => harmonicWeight j.1/harmonicMass rh T
      1/(4096*Real.log T) ≤ 1-‖complexScore g w t‖ := by
  classical
  obtain ⟨L₀,K,hL₀,hK,hcnt⟩ :=
    D5.S3.Weil.ZeroData.CumulativeRvmError.short_window_count_lower
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0<c := by dsimp [c]; positivity
  have hlim : Tendsto (fun T : ℝ => harmonicMass rh T/(Real.log T)^2) atTop (𝓝 (c/2)) := by
    convert harmonic_mass_limit rh using 2 <;> dsimp [c] <;> ring
  have hevent := hlim.eventually_lt_const (show c/2<c by linarith)
  obtain ⟨M,hM⟩ := eventually_atTop.1 hevent
  let L := max (max (2*L₀) 4) M
  let b := Real.pi/(8*K)
  have hL : 1<L := (by norm_num : (1:ℝ)<4).trans_le
    ((le_max_right (2*L₀) 4).trans (le_max_left _ _))
  have hb : 0<b := by dsimp [b]; positivity
  refine ⟨L,b,hL,hb,?_⟩
  intro T t hLT htlo hthi g w
  have hT : 4≤T := ((le_max_right (2*L₀) 4).trans (le_max_left _ _)).trans hLT
  have hLhalf : L₀≤T/2 := by
    have h := ((le_max_left (2*L₀) 4).trans (le_max_left (max (2*L₀) 4) M)).trans hLT
    linarith
  have hTpos : 0<T := by linarith
  have hlog : 0<Real.log T := Real.log_pos (by linarith)
  let τ := |t|
  have hτ : 0<τ := (by positivity : 0<16*Real.pi/T).trans_le htlo
  let H := 2*Real.pi/τ
  have hH : 0<H := by dsimp [H]; positivity
  have hHt : H*τ=2*Real.pi := by dsimp [H]; field_simp
  have hsize : 8*H≤T := by
    have h := (div_le_iff₀ hTpos).mp htlo
    change 16*Real.pi≤τ*T at h
    dsimp [H]
    rw [show 8*(2*Real.pi/τ)=16*Real.pi/τ by ring]
    exact (div_le_iff₀ hτ).mpr (by nlinarith only [h])
  have hwidth : K*Real.log T≤H/16 := by
    have h := (le_div_iff₀ hlog).mp hthi
    change τ*Real.log T≤Real.pi/(8*K) at h
    have h' := (le_div_iff₀ (by positivity : 0<8*K)).mp h
    have he : H/16=Real.pi/(8*τ) := by dsimp [H]; ring
    rw [he]
    apply (le_div_iff₀ (by positivity : 0<8*τ)).mpr
    nlinarith only [h']
  obtain ⟨A,hAs,hA,hmA⟩ :=
    periodic_arc_mass rh hT hLhalf hK hH hτ hHt hsize hwidth hcnt false
  obtain ⟨B,hBs,hB,hmB⟩ :=
    periodic_arc_mass rh hT hLhalf hK hH hτ hHt hsize hwidth hcnt true
  let s := positiveCutoff rh T
  let W := harmonicMass rh T
  let Zraw (v : ℝ) := ∑ j ∈ s,(harmonicWeight j:ℂ)*phase (ordinate j) v
  have hdef := two_arc_deficit s A B (fun j=>phase (ordinate j) τ) harmonicWeight
    hAs hBs (fun j _ => weight_nonneg j) (fun j _=>norm_phase _ _)
    (by simpa using hA) (by simpa [sub_neg_eq_add] using hB) hmA hmB
  change (Real.log T/(4096*Real.pi))/2 ≤ W-‖Zraw τ‖ at hdef
  have hWpos : 0<W := by
    have ha := sum_le_sum_of_subset_of_nonneg hAs
      (fun j _ _=>weight_nonneg j)
    change ∑ j ∈ A,harmonicWeight j ≤ W at ha
    exact (show 0<Real.log T/(4096*Real.pi) by positivity).trans_le (hmA.trans ha)
  have hWup : W≤c*(Real.log T)^2 :=
    (div_lt_iff₀ (sq_pos_of_pos hlog)).mp (by
      have h := hM T ((le_max_right (max (2*L₀) 4) M).trans hLT)
      exact h) |>.le
  have heven : ‖Zraw τ‖=‖Zraw t‖ := by
    by_cases ht0 : 0≤t
    · simp only [τ,abs_of_nonneg ht0]
    · have he : τ=-t := abs_of_neg (lt_of_not_ge ht0)
      rw [he]
      exact raw_score_even s t
  rw [heven] at hdef
  have hZ : complexScore g w t=Zraw t/(W:ℂ) := by
    unfold complexScore
    change (∑ j : ↥s, ((harmonicWeight j.1/W:ℝ):ℂ)*phase (ordinate j.1) t)=_
    rw [Finset.sum_coe_sort s (fun j => ((harmonicWeight j/W:ℝ):ℂ)*phase (ordinate j) t)]
    dsimp [Zraw]
    simp_rw [Complex.ofReal_div,div_mul_eq_mul_div]
    rw [Finset.sum_div]
  have hnorm : ‖Zraw t‖=W*‖complexScore g w t‖ := by
    rw [hZ,Complex.norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hWpos]
    field_simp
  rw [hnorm] at hdef
  have hd : (Real.log T/(4096*Real.pi))/2 ≤ W*(1-‖complexScore g w t‖) := by
    linarith
  have hd0 : 0≤1-‖complexScore g w t‖ :=
    nonneg_of_mul_nonneg_right ((by positivity : 0≤(Real.log T/(4096*Real.pi))/2).trans hd) hWpos
  have hh := hd.trans (mul_le_mul_of_nonneg_right hWup hd0)
  have hfinal : c*Real.log T/4096≤c*(Real.log T)^2*(1-‖complexScore g w t‖) := by
    convert hh using 1
    dsimp [c]
    ring
  have hh' : Real.log T/4096≤(Real.log T)^2*(1-‖complexScore g w t‖) := by
    apply (mul_le_mul_iff_left₀ hc).mp
    nlinarith only [hfinal]
  apply (div_le_iff₀ (by positivity : 0<4096*Real.log T)).mpr
  have hh'' : Real.log T≤4096*(Real.log T)^2*(1-‖complexScore g w t‖) := by
    nlinarith only [hh']
  exact (mul_le_mul_iff_left₀ hlog).mp (by nlinarith only [hh''])

#print axioms harmonic_periodic_phase_deficit


end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder.RHPeriodicPhaseCoverage
