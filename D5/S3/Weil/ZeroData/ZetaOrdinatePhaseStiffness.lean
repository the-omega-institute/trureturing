/- GID: D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unconditional counting controls the complete positive zeta ordinate phase. -/

import D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import D5.S3.Weil.ZetaRvm.NcountWindow
import Mathlib.Tactic

set_option autoImplicit false
open Filter Set
open scoped Topology

namespace D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness
open D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness

abbrev PositiveZetaZero := {rho : ℂ // Zeta23.IsNontrivialZero rho ∧ 0 < rho.im}
noncomputable def ordinate (rho : PositiveZetaZero) : ℝ := rho.val.im
noncomputable def multiplicity (rho : PositiveZetaZero) : ℝ := Zeta23.zeroMult rho.val
noncomputable def weight : PositiveZetaZero → ℝ := phaseWeight ordinate multiplicity
noncomputable def cost : ℝ → ℝ := phaseCost ordinate weight
noncomputable def slope : ℝ → ℝ := phaseSlope ordinate weight

set_option maxHeartbeats 1600000 in
-- The proof joins dyadic counting, strict cutoffs and finite low-frequency restoration.
/-- Coarse counting produces global C1 regularity and logarithmic square phase
bounds for the complete positive-ordinate zeta spectrum. -/
theorem actual_zeta_phase_stiffness :
    Summable weight ∧ Summable (fun rho => weight rho*ordinate rho) ∧
    (∀ t, HasDerivAt cost (slope t) t) ∧ Continuous slope ∧
    ∃ L B : ℝ, 2 ≤ L ∧ 0 ≤ B ∧ ∀ t, 0 < |t| → L*|t| ≤ 1 →
      |cost t-(1/(4*Real.pi))*t^2*(Real.log (|t|⁻¹))^2| ≤
        t^2*B*(Real.log (|t|⁻¹)+1) ∧
      |slope t-(1/(2*Real.pi))*t*(Real.log (|t|⁻¹))^2| ≤
        |t| *B*(Real.log (|t|⁻¹)+1) := by
  classical
  /- The dyadic estimate has the natural raw count increment as its premise.
     Cumulative asymptotics are produced by the argument, not assumed. -/
  have cumulative_count_from_dyadic (N : ℝ → ℝ) {U c B : ℝ}
      (hU : 1 < U) (hc : 0 ≤ c) (hN0 : ∀ u, 0 ≤ N u) (hmono : Monotone N)
      (hdyadic : ∀ T, U ≤ T → |N (2*T)-N T-c*T*Real.log T| ≤ B*T) :
      ∃ D : ℝ, 0 ≤ D ∧ ∀ Y, U ≤ Y → |N Y-c*Y*Real.log Y| ≤ D*Y := by
    have hU0 : 0 < U := zero_lt_one.trans hU
    have hB : 0 ≤ B := by
      have h := (abs_nonneg (N (2*U)-N U-c*U*Real.log U)).trans (hdyadic U le_rfl)
      nlinarith
    let E := fun T : ℝ => N T-c*T*Real.log T
    let K := B+2*c*Real.log 2
    let D0 := N (2*U)/U+2*c*Real.log (2*U)
    let D := max K D0
    have hK : 0 ≤ K := by
      have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
      dsimp only [K]
      positivity
    have hD : 0 ≤ D := hK.trans (le_max_left _ _)
    have hbase (u : ℝ) (hu : u ∈ Icc U (2*U)) : |E u| ≤ D*u := by
      have hu0 : 0 < u := hU0.trans_le hu.1
      have hlog0 : 0 ≤ Real.log u := (Real.log_pos (hU.trans_le hu.1)).le
      have hlogupper : Real.log u ≤ Real.log (2*U) := Real.log_le_log hu0 hu.2
      have hmain : c*u*Real.log u ≤ c*(2*U)*Real.log (2*U) := by
        calc
          c*u*Real.log u ≤ c*u*Real.log (2*U) :=
            mul_le_mul_of_nonneg_left hlogupper (mul_nonneg hc hu0.le)
          _ ≤ c*(2*U)*Real.log (2*U) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu.2 hc)
              (hlog0.trans hlogupper)
      have hlocal : |E u| ≤ N (2*U)+c*(2*U)*Real.log (2*U) := by
        dsimp only [E]
        apply abs_le.mpr
        constructor
        · linarith [hN0 u, hN0 (2*U)]
        · linarith [hmono hu.2, mul_nonneg (mul_nonneg hc hu0.le) hlog0]
      have heq : N (2*U)+c*(2*U)*Real.log (2*U) = D0*U := by
        dsimp only [D0]
        field_simp
      calc
        |E u| ≤ D0*U := hlocal.trans_eq heq
        _ ≤ D*U := mul_le_mul_of_nonneg_right (le_max_right _ _) hU0.le
        _ ≤ D*u := mul_le_mul_of_nonneg_left hu.1 hD
    have hstep (T : ℝ) (hT : U ≤ T) : |E (2*T)-E T| ≤ K*T := by
      have hT0 : 0 < T := hU0.trans_le hT
      have heq : E (2*T)-E T = (N (2*T)-N T-c*T*Real.log T)-2*c*T*Real.log 2 := by
        dsimp only [E]
        rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hT0.ne']
        ring
      rw [heq]
      have hrest : 0 ≤ 2*c*T*Real.log 2 := by
        have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
        positivity
      calc
        _ ≤ |N (2*T)-N T-c*T*Real.log T|+|2*c*T*Real.log 2| :=
          (abs_sub_le (N (2*T)-N T-c*T*Real.log T) 0 (2*c*T*Real.log 2)).trans_eq (by simp)
        _ ≤ B*T+2*c*T*Real.log 2 := add_le_add (hdyadic T hT) (by rw [abs_of_nonneg hrest])
        _ = K*T := by dsimp only [K]; ring
    have hiter (u : ℝ) (hu : u ∈ Icc U (2*U)) (n : ℕ) :
        |E ((2:ℝ)^n*u)| ≤ D*((2:ℝ)^n*u) := by
      induction n with
      | zero => simpa using hbase u hu
      | succ n ih =>
        have hpow : 1 ≤ (2:ℝ)^n := one_le_pow₀ (by norm_num)
        have hu0 : 0 ≤ u := hU0.le.trans hu.1
        have hT : U ≤ (2:ℝ)^n*u :=
          hu.1.trans (by simpa using mul_le_mul_of_nonneg_right hpow hu0)
        have heq : (2:ℝ)^(n+1)*u = 2*((2:ℝ)^n*u) := by rw [pow_succ]; ring
        rw [heq]
        calc
          |E (2*((2:ℝ)^n*u))| ≤ |E (2*((2:ℝ)^n*u))-E ((2:ℝ)^n*u)|+
              |E ((2:ℝ)^n*u)| := by
                simpa using abs_sub_le (E (2*((2:ℝ)^n*u))) (E ((2:ℝ)^n*u)) (0:ℝ)
          _ ≤ K*((2:ℝ)^n*u)+D*((2:ℝ)^n*u) := add_le_add (hstep _ hT) ih
          _ ≤ D*((2:ℝ)^n*u)+D*((2:ℝ)^n*u) :=
            add_le_add (mul_le_mul_of_nonneg_right (le_max_left K D0)
              (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) n) hu0)) le_rfl
          _ = D*(2*((2:ℝ)^n*u)) := by ring
    refine ⟨D, hD, ?_⟩
    intro Y hY
    have hYdiv : 1 ≤ Y/U := (le_div_iff₀ hU0).mpr (by simpa using hY)
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hYdiv (by norm_num : (1:ℝ)<2)
    let u := Y/(2:ℝ)^n
    have hpow0 : 0 < (2:ℝ)^n := by positivity
    have huU : U ≤ u := by
      apply (le_div_iff₀ hpow0).mpr
      have h := (le_div_iff₀ hU0).mp hnlo
      nlinarith
    have hu2U : u ≤ 2*U := by
      apply (div_le_iff₀ hpow0).mpr
      have h := (div_lt_iff₀ hU0).mp hnhi
      rw [pow_succ] at h
      nlinarith
    have hid : (2:ℝ)^n*u = Y := by dsimp only [u]; field_simp
    have h := hiter u ⟨huU,hu2U⟩ n
    simpa only [hid, E] using h
  /- The existing unconditional zeta RvM source is dyadic. This closes the coarse
     cumulative positive-ordinate count, retaining every zero's multiplicity. -/
  have zeta_cumulative_count_coarse :
      ∃ U D : ℝ, 1 < U ∧ 0 ≤ D ∧ ∀ Y, U ≤ Y →
        |(Zeta23.Ncount 0 Y : ℝ) - (1/(2*Real.pi))*Y*Real.log Y| ≤ D*Y := by
    let c : ℝ := 1/(2*Real.pi)
    let d : ℝ := 2*Real.log 2-1-Real.log (2*Real.pi)
    have hc : 0 ≤ c := by dsimp only [c]; positivity
    obtain ⟨C,T0,hmain⟩ :=
      D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData.zetaRiemannVonMangoldt.main
    let U := max T0 2
    have hU : 1 < U := lt_of_lt_of_le (by norm_num : (1:ℝ)<2) (le_max_right _ _)
    let N := fun T : ℝ => (Zeta23.Ncount 0 T : ℝ)
    have hN0 (T : ℝ) : 0 ≤ N T := Nat.cast_nonneg _
    have hmono : Monotone N := by
      intro u v huv
      dsimp only [N]
      exact_mod_cast Zeta23.Ncount_mono (a := 0) (c := 0) le_rfl huv
    have hdyadic (T : ℝ) (hT : U ≤ T) :
        |N (2*T)-N T-c*T*Real.log T| ≤ (|C|+c*|d|)*T := by
      have hT0 : 0 < T := (zero_lt_one.trans hU).trans_le hT
      have hlog0 : 0 ≤ Real.log T := (Real.log_pos (hU.trans_le hT)).le
      have hlogT : Real.log T ≤ T := by
        have h := Real.log_le_sub_one_of_pos hT0
        linarith
      have hm : |(Zeta23.Ncount T (2*T):ℝ)-T/(2*Real.pi)*Zeta23.ell1 T| ≤
          |C| *Real.log T := by
        have h := hmain T ((le_max_left T0 2).trans hT)
        simp only [Zeta23.zetaZeroConfig_N] at h
        exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hlog0)
      have hn : N (2*T) = N T+(Zeta23.Ncount T (2*T):ℝ) := by
        dsimp only [N]
        exact_mod_cast Zeta23.Ncount_add hT0.le (by linarith : T ≤ 2*T)
      have hell : T/(2*Real.pi)*Zeta23.ell1 T = c*T*(Real.log T+d) := by
        dsimp only [Zeta23.ell1,Zeta23.l,c,d]
        rw [Real.log_div hT0.ne' (by positivity : (2*Real.pi)≠0)]
        ring
      have heq : N (2*T)-N T-c*T*Real.log T =
          ((Zeta23.Ncount T (2*T):ℝ)-T/(2*Real.pi)*Zeta23.ell1 T)+c*T*d := by
        rw [hn,hell]
        ring
      have hrest : |c*T*d| = c*T*|d| := by
        rw [abs_mul,abs_mul,abs_of_nonneg hc,abs_of_pos hT0]
      rw [heq]
      calc
        _ ≤ |(Zeta23.Ncount T (2*T):ℝ)-T/(2*Real.pi)*Zeta23.ell1 T|+|c*T*d| :=
          abs_add_le _ _
        _ ≤ |C| *Real.log T+c*T*|d| := add_le_add hm (le_of_eq hrest)
        _ ≤ |C| *T+c*T*|d| :=
          add_le_add (mul_le_mul_of_nonneg_left hlogT (abs_nonneg C)) le_rfl
        _ = (|C|+c*|d|)*T := by ring
    obtain ⟨D,hD,hbound⟩ := cumulative_count_from_dyadic N hU hc hN0 hmono hdyadic
    exact ⟨U,D,hU,hD,hbound⟩
  /- Coarse endpoint control needs no separate local-window asymptotic. -/
  have strict_count_from_closed_sandwich (N S : ℝ → ℝ) {L c D : ℝ}
      (hL : 2 ≤ L) (hc : 0 ≤ c) (hD : 0 ≤ D)
      (hN0 : ∀ u, 0 ≤ N u) (hS0 : ∀ u, 0 ≤ S u)
      (hraw : ∀ u, L ≤ u → |N u-c*u*Real.log u| ≤ D*u)
      (hupper : ∀ u, L ≤ u → S u ≤ N u)
      (hlower : ∀ u, L+1 ≤ u → N (u-1)-N L ≤ S u) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u, L ≤ u → |S u-c*u*Real.log u| ≤ C*u := by
    have hL0 : 0 < L := by linarith
    let C := D+2*c+N L/L+c*Real.log (L+1)
    have hlogL : 0 ≤ Real.log (L+1) := Real.log_nonneg (by linarith)
    have hC : 0 ≤ C := by
      have hNL0 := hN0 L
      dsimp only [C]
      positivity
    refine ⟨C,hC,?_⟩
    intro u hu
    have hu0 : 0 < u := hL0.trans_le hu
    have hCu : D*u ≤ C*u := by
      apply mul_le_mul_of_nonneg_right _ hu0.le
      dsimp only [C]
      have hdiv : 0 ≤ N L/L := div_nonneg (hN0 L) hL0.le
      nlinarith
    apply abs_le.mpr
    constructor
    · by_cases hsmall : u < L+1
      · have hlogu : Real.log u ≤ Real.log (L+1) :=
          Real.log_le_log hu0 hsmall.le
        have hmain : c*u*Real.log u ≤ C*u := by
          calc
            c*u*Real.log u ≤ c*u*Real.log (L+1) :=
              mul_le_mul_of_nonneg_left hlogu (mul_nonneg hc hu0.le)
            _ ≤ C*u := by
              have hN := hN0 L
              have hdiv : 0 ≤ N L/L := div_nonneg hN hL0.le
              dsimp only [C]
              nlinarith
        linarith [hS0 u]
      · have hbig : L+1 ≤ u := le_of_not_gt hsmall
        have hv : L ≤ u-1 := by linarith
        have hv0 : 0 < u-1 := hL0.trans_le hv
        have hlog : Real.log u ≤ Real.log (u-1)+1 := by
          have hratio : u ≤ 2*(u-1) := by linarith
          have h := Real.log_le_log hu0 hratio
          rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hv0.ne'] at h
          have htwo : Real.log 2 ≤ 1 := by
            have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
            norm_num at this ⊢
            exact this
          linarith
        have hlogu : Real.log u ≤ u := by
          have := Real.log_le_sub_one_of_pos hu0
          linarith
        have hdiff : u*Real.log u-(u-1)*Real.log (u-1) ≤ 2*u := by
          nlinarith
        have herr := (abs_le.mp (hraw (u-1) hv)).1
        have hs := hlower u hbig
        have hNL : N L ≤ (N L/L)*u := by
          calc
            N L = (N L/L)*L := by field_simp
            _ ≤ (N L/L)*u := mul_le_mul_of_nonneg_left hu
              (div_nonneg (hN0 L) hL0.le)
        have hmul := mul_le_mul_of_nonneg_left hdiff hc
        dsimp only [C]
        have hbonus : 0 ≤ c*Real.log (L+1)*u := by positivity
        nlinarith
    · have h := (abs_le.mp (hraw u hu)).2
      exact (by linarith [hupper u hu])
  let strictZetaCutoff (L Y : ℝ) : Finset ℂ :=
    (Zeta23.zerosIn_finite L Y).toFinset.filter (fun rho => rho.im < Y)
  let strictZetaCount (L Y : ℝ) : ℝ :=
    ∑ rho ∈ strictZetaCutoff L Y, (Zeta23.zeroMult rho : ℝ)
  have strict_zeta_count_coarse :
      ∃ L C : ℝ, 2 ≤ L ∧ 0 ≤ C ∧ ∀ Y, L ≤ Y →
        |strictZetaCount L Y-(1/(2*Real.pi))*Y*Real.log Y| ≤ C*Y := by
    classical
    obtain ⟨U,D,hU,hD,hraw⟩ := zeta_cumulative_count_coarse
    let L := max U 2
    let N := fun Y : ℝ => (Zeta23.Ncount 0 Y : ℝ)
    have hL : 2 ≤ L := le_max_right _ _
    have hL0 : 0 < L := by linarith
    have hcast (a b : ℝ) : (Zeta23.Ncount a b : ℝ) =
        ∑ rho ∈ (Zeta23.zerosIn_finite a b).toFinset, (Zeta23.zeroMult rho : ℝ) := by
      rw [Zeta23.Ncount, finsum_mem_eq_finite_toFinset_sum _ (Zeta23.zerosIn_finite a b)]
      exact Nat.cast_sum _ _
    have hS0 (Y : ℝ) : 0 ≤ strictZetaCount L Y := by
      unfold strictZetaCount
      exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    have hupper (Y : ℝ) (_hY : L ≤ Y) : strictZetaCount L Y ≤ N Y := by
      dsimp only [N]
      rw [hcast]
      unfold strictZetaCount
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro rho hrho
        simp only [strictZetaCutoff,Finset.mem_filter,Set.Finite.mem_toFinset,
          Zeta23.zerosIn,Set.mem_ofPred_eq] at hrho ⊢
        exact ⟨hrho.1.1,hL0.trans hrho.1.2.1,hrho.1.2.2⟩
      · intro rho _ _
        exact Nat.cast_nonneg _
    have hlower (Y : ℝ) (hY : L+1 ≤ Y) : N (Y-1)-N L ≤ strictZetaCount L Y := by
      have hLY : L ≤ Y-1 := by linarith
      have hadd : N (Y-1) = N L+(Zeta23.Ncount L (Y-1) : ℝ) := by
        dsimp only [N]
        exact_mod_cast Zeta23.Ncount_add hL0.le hLY
      rw [hadd]
      ring_nf
      rw [hcast]
      unfold strictZetaCount
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro rho hrho
        simp only [strictZetaCutoff,Finset.mem_filter,Set.Finite.mem_toFinset,
          Zeta23.zerosIn,Set.mem_ofPred_eq] at hrho ⊢
        exact ⟨⟨hrho.1,hrho.2.1,by linarith [hrho.2.2]⟩,by linarith [hrho.2.2]⟩
      · intro rho _ _
        exact Nat.cast_nonneg _
    obtain ⟨C,hC,hbound⟩ := strict_count_from_closed_sandwich N (strictZetaCount L)
      hL (by positivity : (0:ℝ) ≤ 1/(2*Real.pi)) hD
      (fun _ => Nat.cast_nonneg _) hS0
      (fun Y hY => hraw Y ((le_max_left U 2).trans hY)) hupper hlower
    exact ⟨L,C,hL,hC,hbound⟩
  let HighZetaZero (L : ℝ) := {rho : ℂ // Zeta23.IsNontrivialZero rho ∧ L < rho.im}
  have high_zeta_locally_finite {L : ℝ} (hL : 0 < L) (Y : ℝ) :
      Set.Finite {rho : HighZetaZero L | rho.val.im < Y} := by
    have hpre := (Zeta23.zerosIn_finite 0 Y).preimage
      (show Set.InjOn (fun rho : HighZetaZero L => rho.val)
        ((fun rho : HighZetaZero L => rho.val) ⁻¹' Zeta23.zerosIn 0 Y) from
        fun _ _ _ _ h => Subtype.ext h)
    apply hpre.subset
    intro rho hrho
    exact ⟨rho.property.1,hL.trans rho.property.2,hrho.le⟩
  have high_zeta_strict_count_eq {L : ℝ} (hL : 0 < L) (Y : ℝ) :
      (∑ rho ∈ (high_zeta_locally_finite hL Y).toFinset,
        (Zeta23.zeroMult rho.val : ℝ)) = strictZetaCount L Y := by
    classical
    unfold strictZetaCount
    apply Finset.sum_bij (fun rho _ => rho.val)
    · intro rho hrho
      simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] at hrho
      simp only [strictZetaCutoff,Finset.mem_filter,Set.Finite.mem_toFinset,
        Zeta23.zerosIn,Set.mem_ofPred_eq]
      exact ⟨⟨rho.property.1,rho.property.2,hrho.le⟩,hrho⟩
    · intro rho _ sigma _ heq
      exact Subtype.ext heq
    · intro rho hrho
      simp only [strictZetaCutoff,Finset.mem_filter,Set.Finite.mem_toFinset,
        Zeta23.zerosIn,Set.mem_ofPred_eq] at hrho
      refine ⟨⟨rho,hrho.1.1,hrho.1.2.1⟩,?_,rfl⟩
      simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hrho.2
    · intro _ _
      rfl
  obtain ⟨L,C,hL,hC,hcount⟩ := strict_zeta_count_coarse
  have hL0 : 0 < L := by linarith
  let gamma := fun rho : HighZetaZero L => rho.val.im
  let mult := fun rho : HighZetaZero L => (Zeta23.zeroMult rho.val : ℝ)
  let hf := high_zeta_locally_finite hL0
  have hraw (Y : ℝ) (hY : L ≤ Y) :
      |strictCount gamma mult hf Y-(1/(2*Real.pi))*Y*Real.log Y| ≤ C*Y := by
    have heq : strictCount gamma mult hf Y = strictZetaCount L Y :=
      high_zeta_strict_count_eq hL0 Y
    rw [heq]
    exact hcount Y hY
  obtain ⟨hs,hs1,_hdhigh,_hchigh,hest⟩ := logarithmic_phase_stiffness gamma mult hf
    (by linarith : 1 < L) (fun rho => rho.property.2.le)
    (fun rho => Nat.cast_nonneg _) (by positivity : (0:ℝ) ≤ 1/(2*Real.pi)) hraw
  let low : Set PositiveZetaZero := {rho | ordinate rho ≤ L}
  have hlow : low.Finite := by
    have hpre := (Zeta23.zerosIn_finite 0 L).preimage
      (show Set.InjOn (fun rho : PositiveZetaZero => rho.val)
        ((fun rho : PositiveZetaZero => rho.val) ⁻¹' Zeta23.zerosIn 0 L) from
        fun _ _ _ _ h => Subtype.ext h)
    apply hpre.subset
    intro rho hrho
    exact ⟨rho.property.1,rho.property.2,hrho⟩
  let e : HighZetaZero L ≃ ↑lowᶜ := {
    toFun := fun rho => ⟨⟨rho.val,rho.property.1,hL0.trans rho.property.2⟩,
      not_le.mpr rho.property.2⟩
    invFun := fun rho => ⟨rho.val.val,rho.val.property.1,
      lt_of_not_ge rho.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hhi : Summable (fun rho : ↑lowᶜ => weight rho.val) := by
    apply e.summable_iff.mp
    exact hs
  have hhi1 : Summable (fun rho : ↑lowᶜ => weight rho.val*ordinate rho.val) := by
    apply e.summable_iff.mp
    exact hs1
  have hW : Summable weight := hlow.summable_compl_iff.mp hhi
  have hW1 : Summable (fun rho => weight rho*ordinate rho) :=
    hlow.summable_compl_iff.mp hhi1
  have ha (rho : PositiveZetaZero) : 0 ≤ weight rho := by
    unfold weight phaseWeight ordinate multiplicity
    exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg rho.property.2.le (by positivity))
  have hg (rho : PositiveZetaZero) : 0 ≤ ordinate rho := rho.property.2.le
  have hd (rho : PositiveZetaZero) (t : ℝ) :
      HasDerivAt (fun v => 2*weight rho*(1-Real.cos (ordinate rho*v)))
        (2*weight rho*ordinate rho*Real.sin (ordinate rho*t)) t := by
    convert! ((hasDerivAt_const t (1:ℝ)).sub
      ((Real.hasDerivAt_cos (ordinate rho*t)).comp t
        ((hasDerivAt_id t).const_mul (ordinate rho)))).const_mul (2*weight rho) using 1
    ring
  have hb (rho : PositiveZetaZero) (t : ℝ) :
      ‖2*weight rho*ordinate rho*Real.sin (ordinate rho*t)‖ ≤
        2*(weight rho*ordinate rho) := by
    have hai := ha rho
    have hgi := hg rho
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity :
      0 ≤ 2*weight rho*ordinate rho)]
    calc
      2*weight rho*ordinate rho*|Real.sin (ordinate rho*t)| ≤
          2*weight rho*ordinate rho*1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (by positivity)
      _ = _ := by ring
  have hzero : Summable (fun rho => 2*weight rho*(1-Real.cos (ordinate rho*(0:ℝ)))) :=
    by simp
  refine ⟨hW,hW1,fun t => hasDerivAt_tsum (hW1.mul_left 2) hd hb hzero t,
    continuous_tsum (fun rho => continuous_const.mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
      (hW1.mul_left 2) hb,?_⟩
  let : Fintype low := hlow.fintype
  let M := ∑ rho : low, weight rho.val*(ordinate rho.val)^2
  let mass := ∑' rho : HighZetaZero L, phaseWeight gamma mult rho
  let c : ℝ := 1/(2*Real.pi)
  let P := 10*c+2*C
  let Q := 8*c+10*C+c*(Real.log L)^2+mass/2+2*M
  let B := P+Q+1
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hmass : 0 ≤ mass := tsum_nonneg (fun rho => by
    have hgi : 0 < rho.val.im := hL0.trans rho.property.2
    dsimp only [phaseWeight,gamma,mult]
    positivity)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun rho _ =>
    mul_nonneg (ha rho.val) (sq_nonneg _))
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hquad (x : ℝ) : 0 ≤ 2*(1-Real.cos x) ∧ 2*(1-Real.cos x) ≤ x^2 := by
    have hcos := Real.cos_two_mul_eq_one_sub (x/2)
    have hsin := Real.sin_sq_le_sq (x := x/2)
    rw [show 2*(x/2)=x by ring] at hcos
    constructor
    · nlinarith [Real.cos_le_one x]
    · nlinarith
  let lowCost := fun t : ℝ => ∑ rho : low, 2*weight rho.val*(1-Real.cos (ordinate rho.val*t))
  let lowSlope := fun t : ℝ => ∑ rho : low,
    2*weight rho.val*ordinate rho.val*Real.sin (ordinate rho.val*t)
  have hlc (t : ℝ) : |lowCost t| ≤ t^2*M := by
    have hlo : 0 ≤ lowCost t := Finset.sum_nonneg (fun rho _ =>
      mul_nonneg (mul_nonneg (by norm_num) (ha rho.val))
        (sub_nonneg.mpr (Real.cos_le_one _)))
    rw [abs_of_nonneg hlo]
    dsimp only [lowCost,M]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro rho _
    have h := mul_le_mul_of_nonneg_left (hquad (ordinate rho.val*t)).2 (ha rho.val)
    nlinarith
  have hls (t : ℝ) : |lowSlope t| ≤ 2*|t| *M := by
    dsimp only [lowSlope,M]
    calc
      _ ≤ ∑ rho : low, |2*weight rho.val*ordinate rho.val*Real.sin (ordinate rho.val*t)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ rho : low, 2*|t| *(weight rho.val*(ordinate rho.val)^2) := by
        apply Finset.sum_le_sum
        intro rho _
        have hai := ha rho.val
        have hgi := hg rho.val
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*weight rho.val*ordinate rho.val)]
        have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := ordinate rho.val*t))
          (by positivity : 0 ≤ 2*weight rho.val*ordinate rho.val)
        rw [abs_mul,abs_of_nonneg hgi] at h
        nlinarith
      _ = _ := by rw [Finset.mul_sum]
  have hcostparts (t : ℝ) : cost t = lowCost t+phaseCost gamma (phaseWeight gamma mult) t := by
    have hbound (rho : PositiveZetaZero) :
        ‖2*weight rho*(1-Real.cos (ordinate rho*t))‖ ≤ 4*weight rho := by
      have hai := ha rho
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by positivity)
        (sub_nonneg.mpr (Real.cos_le_one _)))]
      nlinarith [Real.neg_one_le_cos (ordinate rho*t)]
    have hsum : Summable (fun rho => 2*weight rho*(1-Real.cos (ordinate rho*t))) :=
      (hW.mul_left 4).of_norm_bounded hbound
    have hparts := hsum.tsum_subtype_add_tsum_subtype_compl low
    have heq := e.tsum_eq (fun rho : ↑lowᶜ =>
      2*weight rho.val*(1-Real.cos (ordinate rho.val*t)))
    change phaseCost gamma (phaseWeight gamma mult) t = _ at heq
    rw [tsum_fintype,← heq] at hparts
    exact hparts.symm
  have hslopeparts (t : ℝ) : slope t = lowSlope t+phaseSlope gamma (phaseWeight gamma mult) t := by
    have hsum : Summable (fun rho =>
        2*weight rho*ordinate rho*Real.sin (ordinate rho*t)) :=
      (hW1.mul_left 2).of_norm_bounded (fun rho => hb rho t)
    have hparts := hsum.tsum_subtype_add_tsum_subtype_compl low
    have heq := e.tsum_eq (fun rho : ↑lowᶜ =>
      2*weight rho.val*ordinate rho.val*Real.sin (ordinate rho.val*t))
    change phaseSlope gamma (phaseWeight gamma mult) t = _ at heq
    rw [tsum_fintype,← heq] at hparts
    exact hparts.symm
  refine ⟨L,B,hL,hB,?_⟩
  intro t ht hsmall
  let Y := |t|⁻¹
  have hLY : L ≤ Y := by
    dsimp only [Y]
    rw [← one_div,le_div_iff₀ ht]
    exact hsmall
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg (by linarith)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  obtain ⟨_,_,hcos,hsin⟩ := hest t ht hsmall
  have hcosEq : (1/(4*Real.pi):ℝ) = c/2 := by dsimp only [c]; ring
  have hcosBound :
      |phaseCost gamma (phaseWeight gamma mult) t-c/2*t^2*(Real.log Y)^2| ≤
        t^2*(P*Real.log Y+Q-M) := by
    have hnon : 0 ≤ c/2*(Real.log L)^2+mass/4+M := by positivity
    have hneg : 0 ≤ C*Real.log L := mul_nonneg hC hlogL
    dsimp only [momentErrorBound] at hcos
    change _ ≤ t^2*(9*c*Real.log Y+8*c+9*C+
      (c*Real.log Y+C+c/2*(Real.log L)^2+C*(Real.log Y-Real.log L)+mass/4)) at hcos
    apply hcos.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg t)
    dsimp only [P,Q]
    nlinarith
  have hsinBound :
      |phaseSlope gamma (phaseWeight gamma mult) t-c*t*(Real.log Y)^2| ≤
        |t| *(P*Real.log Y+Q-2*M) := by
    have hneg : 0 ≤ C*Real.log L := mul_nonneg hC hlogL
    dsimp only [momentErrorBound] at hsin
    change _ ≤ |t| *(5*c*Real.log Y+4*c+5*C+
      2*(c*Real.log Y+C+c/2*(Real.log L)^2+C*(Real.log Y-Real.log L)+mass/4)) at hsin
    apply hsin.trans
    apply mul_le_mul_of_nonneg_left _ ht.le
    dsimp only [P,Q]
    nlinarith
  have hBQ : P*Real.log Y+Q ≤ B*(Real.log Y+1) := by
    dsimp only [B]
    nlinarith
  constructor
  · rw [hcosEq,hcostparts]
    change |lowCost t+phaseCost gamma (phaseWeight gamma mult) t-c/2*t^2*(Real.log Y)^2| ≤
      t^2*B*(Real.log Y+1)
    have htri := abs_add_le (lowCost t)
      (phaseCost gamma (phaseWeight gamma mult) t-c/2*t^2*(Real.log Y)^2)
    have h := htri.trans (add_le_add (hlc t) hcosBound)
    calc
      _ = |lowCost t+(phaseCost gamma (phaseWeight gamma mult) t-c/2*t^2*(Real.log Y)^2)| := by
        congr 1
        ring
      _ ≤ t^2*M+t^2*(P*Real.log Y+Q-M) := h
      _ = t^2*(P*Real.log Y+Q) := by ring
      _ ≤ t^2*(B*(Real.log Y+1)) := mul_le_mul_of_nonneg_left hBQ (sq_nonneg t)
      _ = _ := by ring
  · rw [hslopeparts]
    change |lowSlope t+phaseSlope gamma (phaseWeight gamma mult) t-c*t*(Real.log Y)^2| ≤
      |t| *B*(Real.log Y+1)
    have htri := abs_add_le (lowSlope t)
      (phaseSlope gamma (phaseWeight gamma mult) t-c*t*(Real.log Y)^2)
    have h := htri.trans (add_le_add (hls t) hsinBound)
    calc
      _ = |lowSlope t+(phaseSlope gamma (phaseWeight gamma mult) t-c*t*(Real.log Y)^2)| := by
        congr 1
        ring
      _ ≤ 2*|t| *M+|t| *(P*Real.log Y+Q-2*M) := h
      _ = |t| *(P*Real.log Y+Q) := by ring
      _ ≤ |t| *(B*(Real.log Y+1)) := mul_le_mul_of_nonneg_left hBQ ht.le
      _ = _ := by ring

#print axioms actual_zeta_phase_stiffness
end D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness
