/- GID: D5/S3/Observer/Linear/SpectralNoiseAsymptotics
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/SpectralNoiseAsymptotics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite power-controlled spectra determine all noise-exponent information growth and arbitrary positive-schedule recovery. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Linear.SpectralNoiseAsymptotics

open Filter
open scoped Topology BigOperators

/-- A finite family with two-sided power bounds has a uniformly bounded
logarithmic remainder at every noise exponent, a sharp recovery criterion for
arbitrary positive variance schedules, and the strict-threshold risk limit. -/
theorem spectral_noise_asymptotics (n:ℕ) (q:Fin (n+1) → ℕ) (hq:∀ i,q i≤q (Fin.last n))
  (lam:ℝ → Fin (n+1) → ℝ) (c C β:ℝ) (hc:0<c) (hC:0<C) (hβ:0<β)
  (hbounds:∀ᶠ T:ℝ in 𝓝[>] 0,∀ i,c*T^(q i)≤lam T i ∧ lam T i≤C*T^(q i)) :
  (∀ α:ℝ,
    (fun T:ℝ=>(1/2:ℝ)*(∑ i:Fin (n+1),Real.log (1+lam T i/(β*T^α)))-
      (1/2:ℝ)*(∑ i:Fin (n+1),max (α-(q i:ℝ)) 0)*Real.log (1/T))
      =O[𝓝[>] 0] (fun _:ℝ=>(1:ℝ))) ∧
  (∀ eps:ℝ → ℝ,(∀ T:ℝ,0<T → 0<eps T) →
    (Tendsto (fun T:ℝ=>(1/2:ℝ)*∑ i:Fin (n+1),eps T/(β*eps T+lam T i))
      (𝓝[>] 0) (𝓝 0) ↔ eps =o[𝓝[>] 0] (fun T:ℝ=>T^(q (Fin.last n))))) ∧
  (∀ α:ℝ,(∀ i,α≠(q i:ℝ)) →
    Tendsto (fun T:ℝ=>(1/2:ℝ)*∑ i:Fin (n+1),T^α/(β*T^α+lam T i))
      (𝓝[>] 0) (𝓝 ((1/2:ℝ)*∑ i:Fin (n+1),if α<(q i:ℝ) then β⁻¹ else 0))) := by
  classical
  have hlog (β c C:ℝ) (hβ:0<β) (hc:0<c) (hC:0<C)
      (q:ℕ) (α:ℝ) :
      let L:=min 1 (c/β)
      let U:=1+C/β
      ∀ T lam:ℝ,0<T → T≤1 → c*T^q≤lam → lam≤C*T^q →
        |Real.log (1+lam/(β*T^α))-max (α-(q:ℝ)) 0*Real.log (1/T)|≤
          |Real.log L|+|Real.log U| := by
      intro L U T lam hT hT1 hlo hhi
      have hpq:0<T^q:=pow_pos hT q
      have hratio:c≤lam/T^q ∧ lam/T^q≤C:=
        ⟨(le_div_iff₀ hpq).mpr hlo,(div_le_iff₀ hpq).mpr hhi⟩
      have hlam:0<lam:=lt_of_lt_of_le (mul_pos hc hpq) hlo
      have hl:0<L:=lt_min zero_lt_one (div_pos hc hβ)
      have hu:0<U:=by dsimp [U];positivity
      let h:=max (α-(q:ℝ)) 0
      let y:=T^h*(1+lam/(β*T^α))
      have hynorm:y=T^h+(lam/T^q)/β*T^(h+(q:ℝ)-α):=by
        dsimp only [y]
        rw [Real.rpow_sub hT,Real.rpow_add hT,Real.rpow_natCast]
        field_simp
        <;>ring
      have hyrange:L≤y ∧ y≤U:=by
        by_cases ha:α≤(q:ℝ)
        · have hh:h=0:=max_eq_right (sub_nonpos.mpr ha)
          rw [hynorm,hh,Real.rpow_zero]
          have he:0≤(q:ℝ)-α:=sub_nonneg.mpr ha
          have heq:(0:ℝ)+(q:ℝ)-α=(q:ℝ)-α:=by ring
          rw [heq]
          have hp:0≤T^((q:ℝ)-α):=(Real.rpow_pos_of_pos hT _).le
          have hp1:T^((q:ℝ)-α)≤1:=Real.rpow_le_one hT.le hT1 he
          have hrlo:0≤(lam/T^q)/β:=div_nonneg (le_trans hc.le hratio.1) hβ.le
          have hrhi:(lam/T^q)/β≤C/β:=(div_le_div_iff_of_pos_right hβ).mpr hratio.2
          constructor
          · exact (min_le_left _ _).trans (le_add_of_nonneg_right (mul_nonneg hrlo hp))
          · dsimp only [U]
            simpa only [add_comm] using add_le_add_left ((mul_le_mul_of_nonneg_left hp1 hrlo).trans (by simpa using hrhi)) 1
        · have ha':0<α-(q:ℝ):=sub_pos.mpr (lt_of_not_ge ha)
          have hh:h=α-(q:ℝ):=max_eq_left ha'.le
          have hexp:h+(q:ℝ)-α=0:=by rw [hh];ring
          rw [hynorm,hexp,Real.rpow_zero,mul_one]
          have hpow:T^h≤1:=Real.rpow_le_one hT.le hT1 (by rw [hh];exact ha'.le)
          have hpow0:0≤T^h:=(Real.rpow_pos_of_pos hT _).le
          have hrlo:c/β≤(lam/T^q)/β:=(div_le_div_iff_of_pos_right hβ).mpr hratio.1
          have hrhi:(lam/T^q)/β≤C/β:=(div_le_div_iff_of_pos_right hβ).mpr hratio.2
          exact ⟨(min_le_right _ _).trans (hrlo.trans (le_add_of_nonneg_left hpow0)),add_le_add hpow hrhi⟩
      have hypos:0<y:=lt_of_lt_of_le hl hyrange.1
      have heq:Real.log y=Real.log (1+lam/(β*T^α))-h*Real.log (1/T):=by
        dsimp only [y]
        rw [Real.log_mul (Real.rpow_pos_of_pos hT _).ne' (by positivity),Real.log_rpow hT,Real.log_div one_ne_zero hT.ne',Real.log_one]
        ring
      rw [←heq]
      have hloglo:Real.log L≤Real.log y:=Real.log_le_log hl hyrange.1
      have hloghi:Real.log y≤Real.log U:=Real.log_le_log hypos hyrange.2
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (Real.log L),abs_nonneg (Real.log U)]
      · linarith [le_abs_self (Real.log U),abs_nonneg (Real.log L)]
  
  have hreciprocal (β c C:ℝ) (hβ:0<β) (hc:0<c) (hC:0<C)
      (q:ℕ) (α:ℝ) (ha:α≠(q:ℝ)) (lam:ℝ → ℝ)
      (hb:∀ᶠ T:ℝ in 𝓝[>] 0,c*T^q≤lam T ∧ lam T≤C*T^q) :
      Tendsto (fun T:ℝ=>T^α/(β*T^α+lam T)) (𝓝[>] 0)
        (𝓝 (if α<(q:ℝ) then β⁻¹ else 0)) := by
      have hpos:∀ᶠ T:ℝ in 𝓝[>] 0,0<T:=self_mem_nhdsWithin
      have heq (T:ℝ) (hT:0<T):T^q/T^α=T^((q:ℝ)-α):=by
        rw [Real.rpow_sub hT,Real.rpow_natCast]
      by_cases hlt:α<(q:ℝ)
      · rw [if_pos hlt]
        have hp:0<(q:ℝ)-α:=sub_pos.mpr hlt
        have hrpow:Tendsto (fun T:ℝ=>T^((q:ℝ)-α)) (𝓝[>] 0) (𝓝 0):=by
          simpa only [Real.zero_rpow hp.ne'] using
            ((Real.continuous_rpow_const hp.le).continuousAt (x:=(0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        have hr:Tendsto (fun T:ℝ=>lam T/T^α) (𝓝[>] 0) (𝓝 0):=by
          apply squeeze_zero' _ _ (by simpa only [mul_zero] using hrpow.const_mul C)
          · filter_upwards [hpos,hb] with T hT hbound
            exact div_nonneg ((mul_pos hc (pow_pos hT _)).trans_le hbound.1).le (Real.rpow_pos_of_pos hT _).le
          · filter_upwards [hpos,hb] with T hT hbound
            rw [←heq T hT]
            simpa only [mul_div_assoc] using (div_le_div_iff_of_pos_right (Real.rpow_pos_of_pos hT α)).mpr hbound.2
        have hh: Tendsto (fun T:ℝ=>(β+lam T/T^α)⁻¹) (𝓝[>] 0) (𝓝 β⁻¹):=by
          simpa only [add_zero] using ((tendsto_const_nhds : Tendsto (fun _:ℝ=>β) (𝓝[>] 0) (𝓝 β)).add hr).inv₀ (by simpa only [add_zero] using hβ.ne')
        apply hh.congr'
        filter_upwards [hpos,hb] with T hT hbound
        have hden:0<β*T^α+lam T:=add_pos (mul_pos hβ (Real.rpow_pos_of_pos hT _)) ((mul_pos hc (pow_pos hT _)).trans_le hbound.1)
        field_simp [hden.ne',(Real.rpow_pos_of_pos hT α).ne']
      · rw [if_neg hlt]
        have hp:0<α-(q:ℝ):=sub_pos.mpr (lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm ha))
        have hrpow:Tendsto (fun T:ℝ=>T^(α-(q:ℝ))) (𝓝[>] 0) (𝓝 0):=by
          simpa only [Real.zero_rpow hp.ne'] using
            ((Real.continuous_rpow_const hp.le).continuousAt (x:=(0:ℝ))).tendsto.mono_left nhdsWithin_le_nhds
        apply squeeze_zero' _ _ (by simpa only [mul_zero] using hrpow.const_mul c⁻¹)
        · filter_upwards [hpos,hb] with T hT hbound
          exact div_nonneg (Real.rpow_pos_of_pos hT _).le (add_pos (mul_pos hβ (Real.rpow_pos_of_pos hT _)) ((mul_pos hc (pow_pos hT _)).trans_le hbound.1)).le
        · filter_upwards [hpos,hb] with T hT hbound
          have he:0<T^α:=Real.rpow_pos_of_pos hT _
          have hden:0<β*T^α+lam T:=add_pos (mul_pos hβ he) ((mul_pos hc (pow_pos hT _)).trans_le hbound.1)
          have hlo:c*T^q≤β*T^α+lam T:=hbound.1.trans (le_add_of_nonneg_left (mul_nonneg hβ.le he.le))
          calc
            T^α/(β*T^α+lam T)≤T^α/(c*T^q):=
              (div_le_div_iff₀ hden (mul_pos hc (pow_pos hT _))).mpr (by nlinarith only [hlo,he])
            _=c⁻¹*T^(α-(q:ℝ)):=by
              rw [Real.rpow_sub hT,Real.rpow_natCast]
              ring
  
  have hschedule (eps :ℝ → ℝ) (heps:∀ T:ℝ,0<T → 0<eps T) :
      let R:=fun T:ℝ=>(1/2:ℝ)*∑ i:Fin (n+1),eps T/(β*eps T+lam T i)
      Tendsto R (𝓝[>] 0) (𝓝 0) ↔ eps =o[𝓝[>] 0] (fun T:ℝ=>T^(q (Fin.last n))) := by
      classical
      intro R
      let δ:=fun T:ℝ=>eps T/T^(q (Fin.last n))
      let r:=fun T:ℝ=>fun i:Fin (n+1)=>eps T/(β*eps T+lam T i)
      let v:=fun T:ℝ=>δ T/(β*δ T+C)
      have hTpos:∀ᶠ T:ℝ in 𝓝[>] 0,0<T:=self_mem_nhdsWithin
      have hT1:∀ᶠ T:ℝ in 𝓝[>] 0,T≤1:=by
        have hh:∀ᶠ T:ℝ in 𝓝[>] 0,T<1:=
          (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds zero_lt_one)
        exact hh.mono fun T h=>h.le
      have hsmall:∀ᶠ T:ℝ in 𝓝[>] 0,
          0≤δ T ∧ (∀ i,0≤r T i ∧ r T i≤δ T/c) ∧ 0≤v T ∧ v T≤r T (Fin.last n) := by
        filter_upwards [hTpos,hT1,hbounds] with T hT hT1 hbound
        have hp:0<T^(q (Fin.last n)):=pow_pos hT _
        have he:=heps T hT
        have hd:0<δ T:=div_pos he hp
        have hr (i:Fin (n+1)):0≤r T i ∧ r T i≤δ T/c := by
          have hpow:T^(q (Fin.last n))≤T^(q i):=pow_le_pow_of_le_one hT.le hT1 (hq i)
          have hl:0<lam T i:=(mul_pos hc (pow_pos hT _)).trans_le (hbound i).1
          have hden:0<β*eps T+lam T i:=add_pos (mul_pos hβ he) hl
          refine ⟨div_nonneg he.le hden.le,?_⟩
          have hdenlo:c*T^(q (Fin.last n))≤β*eps T+lam T i := by
            exact (mul_le_mul_of_nonneg_left hpow hc.le).trans
              ((hbound i).1.trans (le_add_of_nonneg_left (mul_nonneg hβ.le he.le)))
          calc
            r T i ≤ eps T/(c*T^(q (Fin.last n))) :=
              (div_le_div_iff₀ hden (mul_pos hc hp)).mpr (by nlinarith only [hdenlo,he])
            _ = δ T/c := by dsimp only [δ]; field_simp <;> ring
        have hdenv:0<β*δ T+C:=add_pos (mul_pos hβ hd) hC
        have hvl: v T=eps T/(β*eps T+C*T^(q (Fin.last n))) := by
          dsimp only [v,δ]
          field_simp
          <;> ring
        have hlastlo:0<lam T (Fin.last n):=(mul_pos hc hp).trans_le (hbound (Fin.last n)).1
        have hdenr:0<β*eps T+lam T (Fin.last n):=add_pos (mul_pos hβ he) hlastlo
        refine ⟨hd.le,hr,div_nonneg hd.le hdenv.le,?_⟩
        rw [hvl]
        change eps T/(β*eps T+C*T^(q (Fin.last n)))≤eps T/(β*eps T+lam T (Fin.last n))
        apply (div_le_div_iff₀ (add_pos (mul_pos hβ he) (mul_pos hC hp)) hdenr).mpr
        nlinarith only [(hbound (Fin.last n)).2,he]
      have hlo:eps =o[𝓝[>] 0] (fun T:ℝ=>T^(q (Fin.last n))) ↔
          Tendsto δ (𝓝[>] 0) (𝓝 0) :=
        Asymptotics.isLittleO_iff_tendsto' (hTpos.mono fun T hT hz=>False.elim ((pow_pos hT _).ne' hz))
      rw [hlo]
      constructor
      · intro hR
        have hsum:Tendsto (fun T:ℝ=>∑ i:Fin (n+1),r T i) (𝓝[>] 0) (𝓝 0):=by
          convert hR.const_mul 2 using 1
          · ext T; dsimp only [R,r];ring
          · norm_num
        have hv:Tendsto v (𝓝[>] 0) (𝓝 0):=by
          apply squeeze_zero' (hsmall.mono fun T h=>h.2.2.1) _ hsum
          filter_upwards [hsmall] with T h
          exact h.2.2.2.trans (Finset.single_le_sum (fun i _ =>(h.2.1 i).1) (Finset.mem_univ (Fin.last n)))
        have hlim: Tendsto (fun T:ℝ=>C*v T/(1-β*v T)) (𝓝[>] 0) (𝓝 0):=by
          simpa only [Pi.div_def,mul_zero,sub_zero,zero_div] using (hv.const_mul C).div (tendsto_const_nhds.sub (hv.const_mul β)) (by norm_num : (1:ℝ)-β*0≠0)
        apply hlim.congr'
        filter_upwards [hTpos] with T hT
        have hd:0<δ T:=div_pos (heps T hT) (pow_pos hT _)
        have hp:0<β*δ T+C:=add_pos (mul_pos hβ hd) hC
        dsimp only [v]
        field_simp [hC.ne',hp.ne']
        <;> ring
      · intro hδ
        have hr:∀ i:Fin (n+1), Tendsto (fun T:ℝ=>r T i) (𝓝[>] 0) (𝓝 0):=by
          intro i
          apply squeeze_zero' (hsmall.mono fun T h=>(h.2.1 i).1)
            (hsmall.mono fun T h=>(h.2.1 i).2)
          simpa using hδ.div_const c
        have hh:=tendsto_finsetSum Finset.univ (fun i _=>hr i)
        simpa only [Finset.sum_const_zero,mul_zero] using hh.const_mul (1/2:ℝ)
  refine ⟨?_,hschedule,?_⟩
  · intro α
    let K:=|Real.log (min 1 (c/β))|+|Real.log (1+C/β)|
    apply Asymptotics.IsBigO.of_bound (((n+1:ℕ):ℝ)*K/2)
    have hT1:∀ᶠ T:ℝ in 𝓝[>] 0,T≤1:=by
      have hh:∀ᶠ T:ℝ in 𝓝[>] 0,T<1:=
        (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds zero_lt_one)
      exact hh.mono fun T h=>h.le
    filter_upwards [self_mem_nhdsWithin,hT1,hbounds] with T hT hT1 hb
    simp only [Real.norm_eq_abs,norm_one,mul_one]
    have hterm:∀ i:Fin (n+1),|Real.log (1+lam T i/(β*T^α))-max (α-(q i:ℝ)) 0*Real.log (1/T)|≤K:=by
      intro i
      exact hlog β c C hβ hc hC (q i) α T (lam T i) hT hT1 (hb i).1 (hb i).2
    have heq:(1/2:ℝ)*(∑ i:Fin (n+1),Real.log (1+lam T i/(β*T^α)))-
        (1/2:ℝ)*(∑ i:Fin (n+1),max (α-(q i:ℝ)) 0)*Real.log (1/T)=
        (1/2:ℝ)*∑ i:Fin (n+1),(Real.log (1+lam T i/(β*T^α))-max (α-(q i:ℝ)) 0*Real.log (1/T)):=by
      rw [Finset.sum_sub_distrib,←Finset.sum_mul]
      ring
    rw [heq,abs_mul,abs_of_pos (show 0<(1/2:ℝ) by norm_num)]
    have hsum:|∑ i:Fin (n+1),(Real.log (1+lam T i/(β*T^α))-max (α-(q i:ℝ)) 0*Real.log (1/T))|≤((n+1:ℕ):ℝ)*K:=by
      calc
        _≤∑ i:Fin (n+1),|Real.log (1+lam T i/(β*T^α))-max (α-(q i:ℝ)) 0*Real.log (1/T)|:=Finset.abs_sum_le_sum_abs _ _
        _≤∑ i:Fin (n+1),K:=Finset.sum_le_sum fun i _=>hterm i
        _=_:=by simp
    nlinarith only [hsum]
  · intro α hα
    apply Filter.Tendsto.const_mul
    apply tendsto_finsetSum Finset.univ
    intro i _
    exact hreciprocal β c C hβ hc hC (q i) α (hα i) (fun T=>lam T i)
      (hbounds.mono fun T h=>h i)

end D5.S3.Observer.Linear.SpectralNoiseAsymptotics
