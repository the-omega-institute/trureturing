/- GID: D5/S3/Weil/ZeroData/CumulativeRvmError
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/CumulativeRvmError
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact dyadic zero-count main term gives a logarithmic-square cumulative error and short-window lower counts. -/

import D5.S3.Weil.ZeroData.CumulativeRiemannVonMangoldt

/-! Retain the dyadic logarithmic residual through summation. -/

open Filter Set
open scoped Topology

noncomputable section

namespace D5.S3.Weil.ZeroData.CumulativeRvmError

private def mainTerm (x : ℝ) : ℝ :=
  (1/(2*Real.pi))*x*(Real.log (x/(2*Real.pi))-1)

private theorem dyadic_log_square (E : ℝ → ℝ) {U B K : ℝ}
    (hU : 1 < U) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbase : ∀ u ∈ Icc U (2*U), |E u| ≤ K)
    (hstep : ∀ x, U ≤ x → |E (2*x)-E x| ≤ B*Real.log x) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x, U ≤ x → |E x| ≤ D*(Real.log x)^2 := by
  have hUpos : 0 < U := by linarith
  have hlogU : 0 < Real.log U := Real.log_pos hU
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D := K/(Real.log U)^2+B/(2*Real.log 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDbase : K ≤ D*(Real.log U)^2 := by
    have h := le_add_of_nonneg_right
      (show 0 ≤ B/(2*Real.log 2) by positivity) (a := K/(Real.log U)^2)
    exact (div_le_iff₀ (sq_pos_of_pos hlogU)).mp h
  have hDstep : B ≤ 2*D*Real.log 2 := by
    have h := le_add_of_nonneg_left
      (show 0 ≤ K/(Real.log U)^2 by positivity) (a := B/(2*Real.log 2))
    have hh := (div_le_iff₀ (show 0 < 2*Real.log 2 by positivity)).mp h
    dsimp [D]
    linarith only [hh]
  have hiter (u : ℝ) (hu : u ∈ Icc U (2*U)) (n : ℕ) :
      |E ((2:ℝ)^n*u)| ≤ D*(Real.log ((2:ℝ)^n*u))^2 := by
    induction n with
    | zero =>
      simp only [pow_zero,one_mul]
      have hlog := Real.log_le_log hUpos hu.1
      exact (hbase u hu).trans (hDbase.trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlogU.le hlog 2) hD))
    | succ n ih =>
      let x := (2:ℝ)^n*u
      have hx : U ≤ x := hu.1.trans (by
        dsimp [x]
        simpa using mul_le_mul_of_nonneg_right
          (one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n := n)) (hUpos.le.trans hu.1))
      have hxpos : 0 < x := hUpos.trans_le hx
      have hlogx : 0 < Real.log x := Real.log_pos (hU.trans_le hx)
      have heq : (2:ℝ)^(n+1)*u=2*x := by dsimp [x]; rw [pow_succ]; ring
      rw [heq]
      calc
        |E (2*x)| ≤ |E (2*x)-E x|+|E x| := by
          simpa using abs_sub_le (E (2*x)) (E x) (0:ℝ)
        _ ≤ B*Real.log x+D*(Real.log x)^2 := add_le_add (hstep x hx) ih
        _ ≤ D*(Real.log (2*x))^2 := by
          rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hxpos.ne']
          nlinarith only [mul_le_mul_of_nonneg_right hDstep hlogx.le,
            mul_nonneg hD (sq_nonneg (Real.log 2))]
  refine ⟨D,hD,?_⟩
  intro Y hY
  have hYdiv : 1 ≤ Y/U := (le_div_iff₀ hUpos).mpr (by simpa using hY)
  obtain ⟨n,hnlo,hnhi⟩ := exists_nat_pow_near hYdiv (by norm_num : (1:ℝ)<2)
  let u := Y/(2:ℝ)^n
  have hpow : 0 < (2:ℝ)^n := by positivity
  have huU : U ≤ u := by
    apply (le_div_iff₀ hpow).mpr
    have h := (le_div_iff₀ hUpos).mp hnlo
    nlinarith
  have hu2U : u ≤ 2*U := by
    apply (div_le_iff₀ hpow).mpr
    have h := (div_lt_iff₀ hUpos).mp hnhi
    rw [pow_succ] at h
    nlinarith
  have hid : (2:ℝ)^n*u=Y := by dsimp [u]; field_simp
  simpa only [hid] using hiter u ⟨huU,hu2U⟩ n

/-- The existing exact dyadic Riemann–von Mangoldt count supplies a cumulative
logarithmic-square residual around the full first-order main term. -/
theorem cumulative_rvm_error :
    ∃ U D : ℝ, 1 < U ∧ 0 ≤ D ∧ ∀ Y, U ≤ Y →
      |(Zeta23.Ncount 0 Y : ℝ) -
        (1/(2*Real.pi))*Y*(Real.log (Y/(2*Real.pi))-1)| ≤ D*(Real.log Y)^2 := by
  let c : ℝ := 1/(2*Real.pi)
  let a := Real.log (2*Real.pi)+1
  let N := fun x : ℝ => (Zeta23.Ncount 0 x : ℝ)
  let E := fun x => N x-mainTerm x
  obtain ⟨C,T0,hmain⟩ :=
    D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaRiemannVonMangoldt.main
  let U := max T0 2
  have hU : 1 < U := (by norm_num : (1:ℝ)<2).trans_le (le_max_right T0 2)
  have hUpos : 0 < U := by linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hformula {x : ℝ} (hx : 0 < x) :
      mainTerm x=c*x*(Real.log x-a) := by
    unfold mainTerm
    rw [Real.log_div hx.ne' (by positivity : (2*Real.pi)≠0)]
    dsimp [c,a]
    ring
  let K := N (2*U)+c*(2*U)*(Real.log (2*U)+|a|)
  have hK : 0 ≤ K := by
    have hlog : 0 ≤ Real.log (2*U) := Real.log_nonneg (by linarith)
    have hN : 0 ≤ N (2*U) := Nat.cast_nonneg _
    dsimp [K]
    positivity
  have hbase (u : ℝ) (hu : u ∈ Icc U (2*U)) : |E u| ≤ K := by
    have hu0 : 0 < u := hUpos.trans_le hu.1
    have hN : 0 ≤ N u := Nat.cast_nonneg _
    have hNu : N u ≤ N (2*U) := by
      dsimp [N]
      exact_mod_cast Zeta23.Ncount_mono (a := 0) (c := 0) le_rfl hu.2
    have hlogu : 0 ≤ Real.log u := Real.log_nonneg (hU.le.trans hu.1)
    have hlog : Real.log u ≤ Real.log (2*U) := Real.log_le_log hu0 hu.2
    have hmainBound : |mainTerm u| ≤ c*(2*U)*(Real.log (2*U)+|a|) := by
      rw [hformula hu0,abs_mul,abs_mul,abs_of_nonneg hc,abs_of_pos hu0]
      have hsub : |Real.log u-a| ≤ Real.log (2*U)+|a| := by
        exact (abs_sub_le (Real.log u) 0 a).trans (by
          simpa [abs_of_nonneg hlogu] using add_le_add hlog (le_refl |a|))
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hu.2 hc) hsub (abs_nonneg _) (by positivity)
    have h : |N u-mainTerm u| ≤ N u+|mainTerm u| := by
      simpa only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hN] using
        abs_sub_le (N u) 0 (mainTerm u)
    exact h.trans (add_le_add hNu hmainBound)
  have hstep (x : ℝ) (hx : U ≤ x) : |E (2*x)-E x| ≤ |C| * Real.log x := by
    have hx0 : 0 < x := hUpos.trans_le hx
    have hlog : 0 ≤ Real.log x := Real.log_nonneg (hU.le.trans hx)
    have hn : N (2*x)=N x+(Zeta23.Ncount x (2*x):ℝ) := by
      dsimp [N]
      exact_mod_cast Zeta23.Ncount_add hx0.le (by linarith : x ≤ 2*x)
    have hm : mainTerm (2*x)-mainTerm x=x/(2*Real.pi)*Zeta23.ell1 x := by
      rw [hformula (by positivity : 0 < 2*x),hformula hx0,
        Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne']
      dsimp [Zeta23.ell1,Zeta23.l,c,a]
      rw [Real.log_div hx0.ne' (by positivity : (2*Real.pi)≠0)]
      ring
    have heq : E (2*x)-E x=(Zeta23.Ncount x (2*x):ℝ)-x/(2*Real.pi)*Zeta23.ell1 x := by
      dsimp [E]
      linarith only [hn,hm]
    rw [heq]
    have h := hmain x ((le_max_left T0 2).trans hx)
    simp only [Zeta23.zetaZeroConfig_N] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog)
  obtain ⟨D,hD,h⟩ := dyadic_log_square E hU (abs_nonneg C) hK hbase hstep
  exact ⟨U,D,hU,hD,h⟩

/-- The logarithmic-square residual gives a uniform positive count on
short ordinate windows of sufficiently large logarithmic width. -/
theorem short_window_count_lower :
    ∃ L K : ℝ, 1 < L ∧ 0 < K ∧ ∀ x y : ℝ,
      L ≤ x → x+K*Real.log x ≤ y → y ≤ 2*x →
      (y-x)*Real.log x/(8*Real.pi) ≤ (Zeta23.Ncount x y : ℝ) := by
  obtain ⟨U,D,hU,hD,herr⟩ := cumulative_rvm_error
  let c : ℝ := 1/(2*Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  let a := Real.log (2*Real.pi)+1
  let L := max (max U 2) (Real.exp (2*a))
  let K := 20*D/c+1
  have hL : 1 < L := hU.trans_le ((le_max_left U 2).trans (le_max_left _ _))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨L,K,hL,hK,?_⟩
  intro x y hx hwidth hy
  have hxU : U ≤ x := ((le_max_left U 2).trans (le_max_left _ _)).trans hx
  have hx2 : 2 ≤ x := (le_max_right U 2).trans ((le_max_left _ _).trans hx)
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (hL.trans_le hx)
  have hxy : x ≤ y := by
    have hp := mul_nonneg hK.le hlogx.le
    linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have ha : 2*a ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hx)
    simpa only [Real.log_exp] using h
  have hlogxy := Real.log_le_log hx0 hxy
  have hlogyup : Real.log y ≤ 2*Real.log x := by
    have h := Real.log_le_log hy0 hy
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hx0.ne'] at h
    linarith only [h,Real.log_le_log (by norm_num : (0:ℝ)<2) hx2]
  let M := mainTerm
  let N := fun u : ℝ => (Zeta23.Ncount 0 u : ℝ)
  have hMx : M x=c*x*(Real.log x-a) := by
    dsimp [M,mainTerm,c,a]
    rw [Real.log_div hx0.ne' (by positivity : (2*Real.pi)≠0)]
    ring
  have hMy : M y=c*y*(Real.log y-a) := by
    dsimp [M,mainTerm,c,a]
    rw [Real.log_div hy0.ne' (by positivity : (2*Real.pi)≠0)]
    ring
  have hgrowth : c*(y-x)*Real.log x/2 ≤ M y-M x := by
    rw [hMy,hMx]
    have h1 := mul_le_mul_of_nonneg_left (show Real.log x/2 ≤ Real.log x-a by linarith)
      (mul_nonneg hc.le (sub_nonneg.mpr hxy))
    have h2 := mul_nonneg (mul_nonneg hc.le hy0.le) (sub_nonneg.mpr hlogxy)
    nlinarith only [h1,h2]
  have hEx : |N x-M x| ≤ D*(Real.log x)^2 := herr x hxU
  have hEy : |N y-M y| ≤ D*(Real.log y)^2 := herr y (hxU.trans hxy)
  have hEy' : |N y-M y| ≤ 4*D*(Real.log x)^2 := by
    have h := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlogy hlogyup 2) hD
    exact hEy.trans (by nlinarith only [h])
  have herrDiff : 0 ≤ (N y-M y)-(N x-M x)+5*D*(Real.log x)^2 := by
    linarith only [(abs_le.mp hEx).2,(abs_le.mp hEy').1]
  have hwidthCost : 5*D*(Real.log x)^2 ≤ c*(y-x)*Real.log x/4 := by
    have hKbound : 20*D ≤ c*K := by
      dsimp [K]
      field_simp
      linarith
    have hwidth' : K*Real.log x ≤ y-x := by linarith
    have hh := mul_le_mul_of_nonneg_left hwidth' hc.le
    have hk := mul_le_mul_of_nonneg_right hKbound hlogx.le
    have htotal : 20*D*Real.log x ≤ c*(y-x) := by nlinarith only [hh,hk]
    have hfinal := mul_le_mul_of_nonneg_right htotal hlogx.le
    nlinarith only [hfinal]
  have hNadd : N y=N x+(Zeta23.Ncount x y:ℝ) := by
    dsimp [N]
    exact_mod_cast Zeta23.Ncount_add hx0.le hxy
  have hresult : c*(y-x)*Real.log x/4 ≤ (Zeta23.Ncount x y:ℝ) := by
    linarith only [hgrowth,herrDiff,hwidthCost,hNadd]
  convert hresult using 1
  dsimp [c]
  ring

#print axioms short_window_count_lower
#print axioms cumulative_rvm_error

end D5.S3.Weil.ZeroData.CumulativeRvmError
