/- GID: D5/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ZetaOrdinateCompleteOptimizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform all-minimizer logarithmic corrections for the complete positive zeta spectrum. -/

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness
import D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Ring.Basic
open Set
open scoped Topology
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness
open D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace D5.S3.Weil.ZeroData.ZetaOrdinateCompleteOptimizer
noncomputable def denominator (rho : PositiveZetaZero) : ℝ := 1/4+(ordinate rho)^2
noncomputable def drivingK : ℝ := ∑' rho, weight rho*(ordinate rho)^2/denominator rho
noncomputable def quadraticA : ℝ := ∑' rho, weight rho*(ordinate rho)^2/(denominator rho)^2
noncomputable def firstDriving (t : ℝ) : ℝ := ∑' rho, weight rho*
  ((1/denominator rho-2)*Real.cos (ordinate rho*t)-
    2*ordinate rho/denominator rho*Real.sin (ordinate rho*t))
noncomputable def secondDriving (t : ℝ) : ℝ := ∑' rho, weight rho*
  ((8*(ordinate rho)^2/(denominator rho)^2)*Real.cos (ordinate rho*t)-
    (-2/ordinate rho+8*ordinate rho/denominator rho-
      4*ordinate rho/(denominator rho)^2)*Real.sin (ordinate rho*t))
noncomputable def objective (ε t : ℝ) : ℝ := cost t+ε*firstDriving t+ε^2*secondDriving t
noncomputable def phaseOrbit (t : ℝ) : PositiveZetaZero → ℂ :=
  fun rho => Complex.exp ((ordinate rho*t : ℝ)*Complex.I)
noncomputable def quarterPhase : PositiveZetaZero → ℂ := fun _ => Complex.I
noncomputable def phaseHull : Set (PositiveZetaZero → ℂ) := closure (range phaseOrbit)
noncomputable def shiftedPhase (t : ℝ) : PositiveZetaZero → ℂ := quarterPhase*phaseOrbit t
noncomputable def phaseEnvelope (ε : ℝ) (z : PositiveZetaZero → ℂ) : ℝ :=
  2*(∑' rho, weight rho)-2*(∑' rho, weight rho*(z rho).im)+
  ε*(∑' rho, weight rho*((1/denominator rho-2)*(z rho).im+
    2*ordinate rho/denominator rho*(z rho).re))+
  ε^2*(∑' rho, weight rho*((8*(ordinate rho)^2/(denominator rho)^2)*(z rho).im+
    (-2/ordinate rho+8*ordinate rho/denominator rho-
      4*ordinate rho/(denominator rho)^2)*(z rho).re))
theorem actual_zeta_complete_optimizer :
    (quarterPhase ∈ phaseHull → ∀ t, shiftedPhase t ∈ phaseHull) ∧
    (∀ ε t, phaseEnvelope ε (shiftedPhase t) = objective ε t) ∧
    (RiemannHypothesis → Function.Injective ordinate ∧
      ∀ rho : PositiveZetaZero, denominator rho = Complex.normSq rho.val) ∧
    0 < drivingK ∧ ∃ a ε₀ Q : ℝ, 0 < a ∧
      0 < ε₀ ∧ ε₀ < Real.exp (-2) ∧ 1 ≤ Q ∧
      ∀ ε, 0 < ε → ε < ε₀ →
        (∃ t ∈ Set.Icc (-a) a, IsMinOn (objective ε) (Set.Icc (-a) a) t) ∧
        (∀ t ∈ Set.Icc (-a) a,
          IsMinOn (objective ε) (Set.Icc (-a) a) t →
          0 < t ∧ t < a ∧ HasDerivAt (objective ε) 0 t ∧
          let L := Real.log ε⁻¹
          let ell := Real.log t⁻¹
          let Cstar := 4*Real.pi*drivingK
          let Dstar := 4*Real.pi*drivingK^2
          |ell-(L+2*Real.log L-Real.log Cstar)| ≤ Q*Real.log L/L ∧
          |t*L^2/(Cstar*ε)-(1-4*Real.log L/L)| ≤ Q/L ∧
          |objective ε t-(ε*firstDriving 0+8*quadraticA*ε^2-
            Dstar*ε^2/L^2*(1-4*Real.log L/L))| ≤ Q*ε^2/L^3) := by
  -- Construct and localize all minimizers before refining their logarithmic scale.
  have functional_optimizer (δ v r r₁ g g₁ : ℝ → ℝ) {σ c d B : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) (hv0 : v 0 = 0) (hδ : ∀ t, HasDerivAt δ (v t) t) (hr : ∀ t, HasDerivAt r (r₁ t) t)
      (hg : ∀ t, HasDerivAt g (g₁ t) t) (hphase : ∀ t, 0 < |t| → |t| ≤ σ → |δ t - (c/2)*t^2*(Real.log (|t|⁻¹))^2| ≤ B*t^2*(Real.log (|t|⁻¹)+1)) (hslope : ∀ t, 0 < |t| → |t| ≤ σ → |v t - c*t*(Real.log (|t|⁻¹))^2| ≤
      B*|t| *(Real.log (|t|⁻¹)+1)) (hrate : ∀ t, |t| ≤ σ → |r₁ t+d| ≤ B*|t|) (hgbound : ∀ t, |t| ≤ σ → |g₁ t| ≤ B) :
      let J := fun ε t => (1+ε)*δ t+ε*r t+ε^2*g t; let Cstar := d/c; let Dstar := d^2/(2*c)
      ∃ a ε₀ Q : ℝ, 0 < a ∧ a ≤ σ ∧
        0 < ε₀ ∧ ε₀ < Real.exp (-2) ∧ 1 ≤ Q ∧
        ∀ ε, 0 < ε → ε < ε₀ →
          (∃ t ∈ Set.Icc (-a) a,
            IsMinOn (J ε) (Set.Icc (-a) a) t) ∧
          (∀ t ∈ Set.Icc (-a) a,
            IsMinOn (J ε) (Set.Icc (-a) a) t →
            0 < t ∧ t < a ∧
            ((1+ε)*v t+ε*r₁ t+ε^2*g₁ t = 0) ∧
            let L := Real.log ε⁻¹; let ell := Real.log t⁻¹
            |ell-(L+2*Real.log L-Real.log Cstar)| ≤
              Q*Real.log L/L ∧
            |t*L^2/(Cstar*ε)-(1-4*Real.log L/L)| ≤ Q/L ∧
            |J ε t-(ε*r 0+ε^2*g 0-
              Dstar*ε^2/L^2*(1-4*Real.log L/L))| ≤ Q*ε^2/L^3) := by
    have uniform_localization (δ v r r₁ g g₁ : ℝ → ℝ) {σ c d B : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) (hv0 : v 0 = 0) (hδ : ∀ t, HasDerivAt δ (v t) t) (hr : ∀ t, HasDerivAt r (r₁ t) t)
        (hg : ∀ t, HasDerivAt g (g₁ t) t) (hslope : ∀ t, 0 < |t| → |t| ≤ σ → |v t-c*t*(Real.log (|t|⁻¹))^2| ≤ B*|t| *(Real.log (|t|⁻¹)+1)) (hrate : ∀ t, |t| ≤ σ → |r₁ t+d| ≤ B*|t|) (hgbound : ∀ t, |t| ≤ σ → |g₁ t| ≤ B) :
        let J := fun ε t => (1+ε)*δ t+ε*r t+ε^2*g t
        ∃ a ε₀ : ℝ, 0 < a ∧ a ≤ σ ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-2) ∧
          ∀ ε, 0 < ε → ε < ε₀ →
            (∃ t ∈ Icc (-a) a, IsMinOn (J ε) (Icc (-a) a) t) ∧
            (∀ t ∈ Icc (-a) a, IsMinOn (J ε) (Icc (-a) a) t →
              0 < t ∧ t < a ∧ (1+ε)*v t+ε*r₁ t+ε^2*g₁ t = 0 ∧
              (d/(5*c))*ε ≤ t*(Real.log t⁻¹)^2 ∧
              t*(Real.log t⁻¹)^2 ≤ (2*d/c)*ε) := by
      have local_minimizers (f f' : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (hdf : ∀ t, HasDerivAt f (f' t) t) (hneg : ∀ t ∈ Icc (-a) 0, f' t < 0) (hpos : 0 < f' a) : (∃ t ∈ Icc (-a) a, IsMinOn f (Icc (-a) a) t) ∧
          (∀ t ∈ Icc (-a) a, IsMinOn f (Icc (-a) a) t → 0 < t ∧ t < a ∧ f' t = 0) := by
        have hab : -a ≤ a := by linarith
        constructor
        · exact isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
            (fun t _ => (hdf t).continuousAt.continuousWithinAt)
        · intro t ht hmin
          have htleft : -a < t := by
            rcases ht.1.eq_or_lt with (heq | hlt)
            · subst t
              have hcone : a - (-a) ∈ posTangentConeAt (Icc (-a) a) (-a) := sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab ▸ Subset.rfl)
              have hnonneg : 0 ≤ (a - (-a)) * f' (-a) := by
                simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hmin.localize.hasFDerivWithinAt_nonneg (hdf (-a)).hasDerivWithinAt hcone
              have hnegative : (a - (-a)) * f' (-a) < 0 := mul_neg_of_pos_of_neg (by linarith) (hneg (-a) ⟨le_rfl, by linarith⟩)
              exact (not_le_of_gt hnegative hnonneg).elim
            · exact hlt
          have htright : t < a := by
            rcases ht.2.eq_or_lt' with (heq | hlt)
            · subst t
              have hcone : -a - a ∈ posTangentConeAt (Icc (-a) a) a := sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab])
              have hnonneg : 0 ≤ (-a - a) * f' a := by
                simpa only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] using hmin.localize.hasFDerivWithinAt_nonneg (hdf a).hasDerivWithinAt hcone
              have hnegative : (-a - a) * f' a < 0 := mul_neg_of_neg_of_pos (by linarith) hpos; exact (not_le_of_gt hnegative hnonneg).elim
            · exact hlt
          have hnhds : Icc (-a) a ∈ 𝓝 t := by rw [← mem_interior_iff_mem_nhds, interior_Icc]; exact ⟨htleft, htright⟩
          have hstationary : f' t = 0 := (hmin.isLocalMin hnhds).hasDerivAt_eq_zero (hdf t)
          have htpos : 0 < t := by
            by_contra h
            have hbad := hneg t ⟨ht.1, le_of_not_gt h⟩; rw [hstationary] at hbad; exact (lt_irrefl 0 hbad)
          exact ⟨htpos, htright, hstationary⟩
      have stationary_squeeze {ε c d t ell v r g : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hd : 0 < d) (hslope : |v-c*t*ell^2| ≤ (c/4)*|t| *ell^2) (hforcing : d/2 ≤ -(r+ε*g) ∧ -(r+ε*g) ≤ 3*d/2)
          (hstationary : (1+ε)*v+ε*r+ε^2*g = 0) : 0 < t ∧ (d/(5*c))*ε ≤ t*ell^2 ∧ t*ell^2 ≤ (2*d/c)*ε := by
        have hcoef : 0 < 1+ε := by linarith
        have hforce : 0 < -(r+ε*g) := by linarith [hforcing.1]
        have heq : (1+ε)*v = ε*(-(r+ε*g)) := by nlinarith [hstationary]
        have hv : 0 < v := by
          apply (mul_pos_iff_of_pos_left hcoef).mp
          rw [heq]; exact mul_pos hε hforce
        have ht : 0 < t := by
          by_contra h
          have ht0 : t ≤ 0 := le_of_not_gt h; rw [abs_of_nonpos ht0] at hslope; have hupper := (abs_le.mp hslope).2
          have hnonpos : c*t*ell^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc.le ht0) (sq_nonneg ell); nlinarith
        rw [abs_of_pos ht] at hslope
        obtain ⟨hslow, hsup⟩ := abs_le.mp hslope
        have hvlow : d*ε/4 ≤ v := by
          have hprod := mul_le_mul_of_nonneg_left hforcing.1 hε.le; rw [← heq] at hprod
          have hcoefv : ε*v ≤ v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hε1 hv.le
          nlinarith
        have hvhigh : v ≤ 3*d*ε/2 := by
          have hprod := mul_le_mul_of_nonneg_left hforcing.2 hε.le; rw [← heq] at hprod; have hev : 0 ≤ ε*v := mul_nonneg hε.le hv.le; nlinarith
        refine ⟨ht, ?_, ?_⟩
        · have hbound : d*ε ≤ (5*c)*(t*ell^2) := by nlinarith
          calc
            (d/(5*c))*ε = (d*ε)/(5*c) := by ring
            _ ≤ t*ell^2 := (div_le_iff₀ (by positivity : 0 < 5*c)).mpr (by nlinarith [hbound])
        · have hbound : c*(t*ell^2) ≤ 2*d*ε := by nlinarith
          calc
            t*ell^2 ≤ (2*d*ε)/c := (le_div_iff₀ hc).mpr (by nlinarith [hbound])
            _ = (2*d/c)*ε := by ring
      let E := max 16 (8*B/c); let a := min σ (min (Real.exp (-E)) (d/(4*(B+1)))); have hE : 16 ≤ E := le_max_left _ _; have ha : 0 < a := lt_min hσ (lt_min (Real.exp_pos _) (by positivity))
      have haσ : a ≤ σ := min_le_left _ _; have haexp : a ≤ Real.exp (-E) := (min_le_right _ _).trans (min_le_left _ _); have had : a ≤ d/(4*(B+1)) := (min_le_right _ _).trans (min_le_right _ _)
      have hB1 : 0 < B+1 := by linarith
      have hsmall (t : ℝ) (ht0 : 0 < |t|) (hta : |t| ≤ a) : 16 ≤ Real.log (|t|⁻¹) ∧ |v t-c*t*(Real.log (|t|⁻¹))^2| ≤ (c/4)*|t| *(Real.log (|t|⁻¹))^2 := by
        let ell := Real.log (|t|⁻¹)
        have hell : E ≤ ell := by
          have h := Real.log_le_log ht0 (hta.trans haexp); rw [Real.log_exp] at h; dsimp only [ell]; rw [Real.log_inv]; linarith
        have hell16 : 16 ≤ ell := hE.trans hell
        have hell0 : 0 ≤ ell := by linarith
        have hcell : 8*B ≤ c*ell := by
          have h := (div_le_iff₀ hc).mp (show 8*B/c ≤ ell from (le_max_right _ _).trans hell); nlinarith
        have hlogbound : B*(ell+1) ≤ (c/4)*ell^2 := by
          have h := mul_le_mul_of_nonneg_right hcell hell0
          have h' := mul_le_mul_of_nonneg_left (show ell+1 ≤ 2*ell by linarith) hB
          nlinarith
        refine ⟨hell16, ?_⟩
        have h := hslope t ht0 (hta.trans haσ); have h' := mul_le_mul_of_nonneg_right hlogbound ht0.le; dsimp only [ell] at h'; nlinarith
      have hapos : 0 < v a := by
        have h := hsmall a (by rwa [abs_of_pos ha]) (by rw [abs_of_pos ha]); rw [abs_of_pos ha] at h
        have hell0 : 0 < Real.log a⁻¹ := by linarith [h.1]
        have hmain : 0 < c*a*(Real.log a⁻¹)^2 := by positivity
        linarith [(abs_le.mp h.2).1]
      let ε₀ := min (Real.exp (-2)/2) (min 1 (min (d/(4*(B+1))) (v a/(3*d)))); have hε₀ : 0 < ε₀ := lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
      have hε₀exp : ε₀ < Real.exp (-2) := (min_le_left _ _).trans_lt (by have h := Real.exp_pos (-2); linarith); dsimp only
      refine ⟨a, ε₀, ha, haσ, hε₀, hε₀exp, ?_⟩
      intro ε hε hεbound; have hε1 : ε ≤ 1 := hεbound.le.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hεd : ε ≤ d/(4*(B+1)) := hεbound.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      have hεva : ε ≤ v a/(3*d) := hεbound.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      have hforcing (t : ℝ) (hta : |t| ≤ a) : d/2 ≤ -(r₁ t+ε*g₁ t) ∧ -(r₁ t+ε*g₁ t) ≤ 3*d/2 := by
        have hr' := hrate t (hta.trans haσ); have hg' := hgbound t (hta.trans haσ); have hd1 := (le_div_iff₀ (by positivity : 0 < 4*(B+1))).mp had; have hd2 := (le_div_iff₀ (by positivity : 0 < 4*(B+1))).mp hεd
        have hBt : B*|t| ≤ d/4 := by
          have h := mul_le_mul_of_nonneg_left hta hB; nlinarith
        have hBε : ε*B ≤ d/4 := by nlinarith
        have hprod : |ε*g₁ t| ≤ ε*B := by rw [abs_mul,abs_of_pos hε]; exact mul_le_mul_of_nonneg_left hg' hε.le
        constructor <;> linarith [(abs_le.mp hr').1,(abs_le.mp hr').2,
          (abs_le.mp hprod).1,(abs_le.mp hprod).2]
      let j := fun t => (1+ε)*δ t+ε*r t+ε^2*g t; let j₁ := fun t => (1+ε)*v t+ε*r₁ t+ε^2*g₁ t
      have hj (t : ℝ) : HasDerivAt j (j₁ t) t := by
        exact (((hδ t).const_mul (1+ε)).add ((hr t).const_mul ε)).add ((hg t).const_mul (ε^2))
      have hjneg (t : ℝ) (ht : t ∈ Icc (-a) 0) : j₁ t < 0 := by
        have hta : |t| ≤ a := by rw [abs_of_nonpos ht.2]; linarith [ht.1]
        have hv : v t ≤ 0 := by
          by_cases ht0 : t = 0
          · simp only [ht0,hv0,le_refl]
          · have hsmall' := (hsmall t (abs_pos.mpr ht0) hta).2
            rw [abs_of_nonpos ht.2] at hsmall'; have hmain : c*t*(Real.log (|t|⁻¹))^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hc.le ht.2) (sq_nonneg _); rw [abs_of_nonpos ht.2] at hmain
            nlinarith [(abs_le.mp hsmall').2]
        have hf := hforcing t hta; dsimp only [j₁]
        have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 1+ε by linarith) hv
        have hdriv := mul_lt_mul_of_pos_left (show r₁ t+ε*g₁ t < 0 by linarith) hε
        nlinarith
      have hjpos : 0 < j₁ a := by
        have hf := hforcing a (by rw [abs_of_pos ha]); have hεav := (le_div_iff₀ (by positivity : 0 < 3*d)).mp hεva; have hprod := mul_le_mul_of_nonneg_left hf.2 hε.le; have hεv := mul_pos hε hapos; dsimp only [j₁]
        nlinarith
      obtain ⟨hexists,hall⟩ := local_minimizers j j₁ ha hj hjneg hjpos
      refine ⟨hexists, ?_⟩
      intro t ht hmin
      obtain ⟨htpos,htlt,hstat⟩ := hall t ht hmin
      have hta : |t| ≤ a := by rw [abs_of_pos htpos]; exact ht.2
      have hs := (hsmall t (by rwa [abs_of_pos htpos]) hta).2; rw [abs_of_pos htpos] at hs; have heq : (1+ε)*v t+ε*r₁ t+ε^2*g₁ t = 0 := hstat
      obtain ⟨_,hp,hq⟩ := stationary_squeeze (t := t) (ell := Real.log t⁻¹) hε hε1 hc hd (by simpa only [abs_of_pos htpos] using hs) (hforcing t hta) heq
      simpa only [abs_of_pos htpos] using And.intro htpos (And.intro htlt (And.intro heq (And.intro hp hq)))
    have mean_value_controls (r r₁ g g₁ : ℝ → ℝ) {σ B d t : ℝ} (hB : 0 ≤ B) (ht : 0 ≤ t) (htσ : t ≤ σ) (hr : ∀ u, HasDerivAt r (r₁ u) u) (hg : ∀ u, HasDerivAt g (g₁ u) u) (hrate : ∀ u, |u| ≤ σ → |r₁ u+d| ≤ B*|u|)
        (hgbound : ∀ u, |u| ≤ σ → |g₁ u| ≤ B) : |r t-r 0+d*t| ≤ B*t^2 ∧ |g t-g 0| ≤ B*t := by
      have huσ (u : ℝ) (hu : u ∈ Icc 0 t) : |u| ≤ σ := by rw [abs_of_nonneg hu.1]; exact hu.2.trans htσ
      have hd (u : ℝ) (_hu : u ∈ Icc 0 t) : HasDerivWithinAt (fun x => r x+d*x) (r₁ u+d) (Icc 0 t) u := by simpa using! ((hr u).add ((hasDerivAt_id u).const_mul d)).hasDerivWithinAt
      have hb (u : ℝ) (hu : u ∈ Icc 0 t) : ‖r₁ u+d‖ ≤ B*t := by
        rw [Real.norm_eq_abs]
        calc
          _ ≤ B*|u| := hrate u (huσ u hu)
          _ ≤ B*t := by rw [abs_of_nonneg hu.1]; exact mul_le_mul_of_nonneg_left hu.2 hB
      have hrv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc 0 t) (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl, ht⟩) (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
      have hgv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun u (_hu : u ∈ Icc 0 t) => (hg u).hasDerivWithinAt) (fun u (hu : u ∈ Icc 0 t) => show ‖g₁ u‖ ≤ B by
          rw [Real.norm_eq_abs]; exact hgbound u (huσ u hu))
        (convex_Icc 0 t)
        (show (0:ℝ) ∈ Icc 0 t from ⟨le_rfl, ht⟩)
        (show t ∈ Icc 0 t from ⟨ht, le_rfl⟩)
      constructor
      · convert hrv using 1 <;> simp only [Real.norm_eq_abs, mul_zero, add_zero, sub_zero,
          abs_of_nonneg ht]
        · congr 1; ring
        · ring
      · simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht] using hgv
    have logarithmic_bootstrap {p q ε t ell L : ℝ} (hp : 0 < p) (hq : 0 < q) (hε : 0 < ε) (ht : 0 < t) (hell : ell = Real.log t⁻¹) (hL : L = Real.log ε⁻¹) (hell16 : 16 ≤ ell) (hL16 : 16 ≤ L)
        (hLA : 2*max (|Real.log p|) (|Real.log q|) ≤ L) (hscale : p*ε ≤ t*ell^2 ∧ t*ell^2 ≤ q*ε) : L/2 ≤ ell ∧ ell ≤ 3*L ∧ |ell-L| ≤ (2+2*Real.log 3+max (|Real.log p|) (|Real.log q|))*Real.log L := by
      let A := max (|Real.log p|) (|Real.log q|); have hA : 0 ≤ A := (abs_nonneg _).trans (le_max_left _ _)
      have hell0 : 0 < ell := by linarith
      have hL0 : 0 < L := by linarith
      have hlog2lo : (1:ℝ)/2 ≤ Real.log 2 := by
        have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at h ⊢; exact h
      have hlog2hi : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); norm_num at h ⊢; exact h
      have hlog16 : Real.log 16 = 4*Real.log 2 := by
        have h := Real.log_pow (2:ℝ) 4; norm_num at h; exact h
      have hlogell0 : 0 ≤ Real.log ell := Real.log_nonneg (by linarith)
      have hlogL1 : 1 ≤ Real.log L := by
        have h := Real.log_le_log (by norm_num : (0:ℝ)<16) hL16; rw [hlog16] at h; linarith
      have hlogellhalf : 2*Real.log ell ≤ ell/2 := by
        have h := Real.log_le_sub_one_of_pos (div_pos hell0 (by norm_num : (0:ℝ)<16)); rw [Real.log_div hell0.ne' (by norm_num : (16:ℝ)≠0), hlog16] at h; linarith
      have hlogt : Real.log t = -ell := by rw [Real.log_inv] at hell; linarith
      have hlogε : Real.log ε = -L := by rw [Real.log_inv] at hL; linarith
      have hlow := Real.log_le_log (mul_pos hp hε) hscale.1; have hupp := Real.log_le_log (mul_pos ht (sq_pos_of_pos hell0)) hscale.2
      rw [Real.log_mul hp.ne' hε.ne', Real.log_mul ht.ne' (sq_pos_of_pos hell0).ne', Real.log_pow, hlogt, hlogε] at hlow
      rw [Real.log_mul ht.ne' (sq_pos_of_pos hell0).ne', Real.log_pow, Real.log_mul hq.ne' hε.ne', hlogt, hlogε] at hupp; norm_num at hlow hupp
      have hpA : -A ≤ Real.log p := by
        have h := neg_abs_le (Real.log p); have h' : |Real.log p| ≤ A := le_max_left _ _; linarith
      have hqA : Real.log q ≤ A := (le_abs_self _).trans (le_max_right _ _)
      have hres : |ell-L-2*Real.log ell| ≤ A := by
        apply abs_le.mpr
        constructor <;> linarith
      have hLA' : 2*A ≤ L := hLA
      have helllo : L/2 ≤ ell := by linarith [(abs_le.mp hres).1]
      have hellhi : ell ≤ 3*L := by linarith [(abs_le.mp hres).2]
      have hloghi : Real.log ell ≤ Real.log 3+Real.log L := by
        have h := Real.log_le_log hell0 hellhi; rw [Real.log_mul (by norm_num : (3:ℝ)≠0) hL0.ne'] at h; exact h
      have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have hcoarse : |ell-L| ≤ A+2*Real.log ell := by
        apply abs_le.mpr
        constructor <;> linarith [(abs_le.mp hres).1, (abs_le.mp hres).2]
      refine ⟨helllo, hellhi, ?_⟩
      calc
        |ell-L| ≤ A+2*Real.log ell := hcoarse
        _ ≤ A+2*Real.log 3+2*Real.log L := by linarith
        _ ≤ (2+2*Real.log 3+A)*Real.log L := by
          have h := mul_le_mul_of_nonneg_left hlogL1 (by positivity : 0 ≤ A+2*Real.log 3); nlinarith
    have refined_logarithm {ε t ell L C H B : ℝ} (hε : 0 < ε) (ht : 0 < t) (hC : 0 < C) (hH : 0 ≤ H) (hB : 0 ≤ B) (hL : 0 < L) (hell : ell = Real.log t⁻¹) (hLe : L = Real.log ε⁻¹)
        (helllo : L/2 ≤ ell) (hellhi : ell ≤ 3*L) (hellH : 2*H ≤ ell) (hlogL : 1 ≤ Real.log L) (hcoarse : |ell-L| ≤ B*Real.log L) (hrel : |t*ell^2/(C*ε)-1| ≤ H/ell) :
        |ell-(L+2*Real.log L-Real.log C)| ≤ 4*(B+H)*Real.log L/L := by
      have hell0 : 0 < ell := by linarith
      let X := t*ell^2/(C*ε); have hX0 : 0 < X := div_pos (mul_pos ht (sq_pos_of_pos hell0)) (mul_pos hC hε); have hhalf : H/ell ≤ 1/2 := (div_le_iff₀ hell0).mpr (by linarith)
      have hXhalf : 1/2 ≤ X := by
        have h := (abs_le.mp hrel).1; change -(H/ell) ≤ X-1 at h; linarith
      have hlogX : |Real.log X| ≤ 2*|X-1| := by
        apply abs_le.mpr
        constructor
        · have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hX0)
          rw [Real.log_inv] at h
          have hdiv : X⁻¹-1 ≤ 2*|X-1| := by
            have heq : X⁻¹-1 = (1-X)/X := by field_simp
            rw [heq]
            apply (div_le_iff₀ hX0).mpr
            have habs : 1-X ≤ |X-1| := by simpa only [abs_sub_comm] using le_abs_self (1-X)
            have hmul := mul_le_mul_of_nonneg_left hXhalf (abs_nonneg (X-1)); nlinarith
          linarith
        · have h := Real.log_le_sub_one_of_pos hX0
          linarith [le_abs_self (X-1), abs_nonneg (X-1)]
      have hlogXrate : |Real.log X| ≤ 4*H/L := by
        calc
          _ ≤ 2*(H/ell) := hlogX.trans (mul_le_mul_of_nonneg_left hrel (by norm_num))
          _ = (2*H)/ell := by ring
          _ ≤ 4*H/L := by
            apply (div_le_div_iff₀ hell0 hL).mpr
            have h := mul_le_mul_of_nonneg_left helllo hH; nlinarith
      have hlogdiff : |Real.log ell-Real.log L| ≤ (2/L)*|ell-L| := by
        have hLm : L ∈ Icc (L/2) (3*L) := by constructor <;> linarith
        have hem : ell ∈ Icc (L/2) (3*L) := ⟨helllo,hellhi⟩
        have hu0 (u : ℝ) (hu : u ∈ Icc (L/2) (3*L)) : 0 < u := by linarith [hu.1]
        have hd (u : ℝ) (hu : u ∈ Icc (L/2) (3*L)) : HasDerivWithinAt Real.log (1/u) (Icc (L/2) (3*L)) u := by
          simpa only [one_div] using (Real.hasDerivAt_log (hu0 u hu).ne').hasDerivWithinAt
        have hb (u : ℝ) (hu : u ∈ Icc (L/2) (3*L)) : ‖1/u‖ ≤ 2/L := by
          rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hu0 u hu))]
          apply (div_le_div_iff₀ (hu0 u hu) hL).mpr
          linarith [hu.1]
        simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Icc (L/2) (3*L)) hLm hem
      have hlogt : Real.log t = -ell := by rw [Real.log_inv] at hell; linarith
      have hloge : Real.log ε = -L := by rw [Real.log_inv] at hLe; linarith
      have hid : Real.log X = -ell+2*Real.log ell-Real.log C+L := by
        dsimp only [X]; rw [Real.log_div (mul_pos ht (sq_pos_of_pos hell0)).ne' (mul_pos hC hε).ne', Real.log_mul ht.ne' (sq_pos_of_pos hell0).ne', Real.log_pow, Real.log_mul hC.ne' hε.ne', hlogt, hloge]; ring
      have heq : ell-(L+2*Real.log L-Real.log C) = 2*(Real.log ell-Real.log L)-Real.log X := by rw [hid]; ring
      rw [heq]
      calc
        _ ≤ |2*(Real.log ell-Real.log L)|+|Real.log X| := abs_sub _ _
        _ = 2*|Real.log ell-Real.log L|+|Real.log X| := by rw [abs_mul]; norm_num
        _ ≤ 2*((2/L)*|ell-L|)+4*H/L := add_le_add (mul_le_mul_of_nonneg_left hlogdiff (by norm_num)) hlogXrate
        _ ≤ 2*((2/L)*(B*Real.log L))+4*H/L := by
          gcongr
        _ = (4*B*Real.log L+4*H)/L := by ring
        _ ≤ 4*(B+H)*Real.log L/L := by
          apply (div_le_div_iff₀ hL hL).mpr
          have h := mul_le_mul_of_nonneg_left hlogL hH; nlinarith
    have displacement_estimate {ell L X H B Q C : ℝ} (hL : 0 < L) (helllo : L/2 ≤ ell) (hellhi : ell ≤ 3*L) (hH : 0 ≤ H) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hlog0 : 0 ≤ Real.log L) (hlogsq : (Real.log L)^2 ≤ 4*L)
        (hcoarse : |ell-L| ≤ B*Real.log L) (hrefined : |ell-(L+2*Real.log L-Real.log C)| ≤ Q*Real.log L/L) (hrel : |X-1| ≤ H/ell) : |X*(L^2/ell^2)-(1-4*Real.log L/L)| ≤ (8*H+2*|Real.log C|+2*Q+112*B^2)/L := by
      have hell0 : 0 < ell := by linarith
      let u := (ell-L)/L; let Y := L^2/ell^2
      have hulow : -1/2 ≤ u := by
        apply (le_div_iff₀ hL).mpr
        linarith
      have huhi : u ≤ 2 := by
        apply (div_le_iff₀ hL).mpr
        linarith
      have hu0 : 0 < 1+u := by linarith
      have hY0 : 0 ≤ Y := by dsimp only [Y]; positivity
      have hY4 : Y ≤ 4 := by
        apply (div_le_iff₀ (sq_pos_of_pos hell0)).mpr
        have h := mul_self_le_mul_self (by positivity : 0 ≤ L/2) helllo; nlinarith
      have hYid : Y = 1/(1+u)^2 := by
        have hu_eq : 1+u = ell/L := by
          dsimp only [u]; field_simp
          <;> ring
        rw [hu_eq]; dsimp only [Y]; field_simp [hell0.ne', hL.ne']
      have hremid : Y-(1-2*u) = u^2*(3+2*u)/(1+u)^2 := by
        rw [hYid]; field_simp
        <;> ring
      have hrem0 : 0 ≤ Y-(1-2*u) := by rw [hremid]; exact div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (sq_nonneg _)
      have hrem : Y-(1-2*u) ≤ 28*u^2 := by
        rw [hremid]
        apply (div_le_iff₀ (sq_pos_of_pos hu0)).mpr
        have hn := mul_le_mul_of_nonneg_left (show 3+2*u ≤ 7 by linarith) (sq_nonneg u)
        have hden : 1/4 ≤ (1+u)^2 := by nlinarith
        have hd := mul_le_mul_of_nonneg_left hden (show 0 ≤ 28*u^2 by positivity)
        nlinarith
      have huabs : |u| ≤ B*Real.log L/L := by dsimp only [u]; rw [abs_div, abs_of_pos hL]; exact div_le_div_of_nonneg_right hcoarse hL.le
      have huabs0 : 0 ≤ B*Real.log L/L := by positivity
      have hu2 : u^2 ≤ (B*Real.log L/L)^2 := by
        have h := mul_self_le_mul_self (abs_nonneg u) huabs; simpa only [sq_abs, ← sq] using h
      have hremrate : |Y-(1-2*u)| ≤ 112*B^2/L := by
        rw [abs_of_nonneg hrem0]
        calc
          _ ≤ 28*u^2 := hrem
          _ ≤ 28*(B*Real.log L/L)^2 := mul_le_mul_of_nonneg_left hu2 (by norm_num)
          _ = (28*B^2*(Real.log L)^2)/L^2 := by ring
          _ ≤ (28*B^2*(4*L))/L^2 := by gcongr
          _ = 112*B^2/L := by field_simp; ring
      have hXY : |X*Y-Y| ≤ 8*H/L := by
        have heq : X*Y-Y = (X-1)*Y := by ring
        rw [heq, abs_mul, abs_of_nonneg hY0]
        calc
          _ ≤ (H/ell)*4 := mul_le_mul hrel hY4 hY0 (by positivity)
          _ = (4*H)/ell := by ring
          _ ≤ 8*H/L := by
            apply (div_le_div_iff₀ hell0 hL).mpr
            have h := mul_le_mul_of_nonneg_left helllo hH; nlinarith
      have hlogupper : Real.log L ≤ L := Real.log_le_self hL.le
      have hshape : |ell-L-2*Real.log L| ≤ |Real.log C|+Q := by
        have heq : ell-L-2*Real.log L = (ell-(L+2*Real.log L-Real.log C))-Real.log C := by ring
        rw [heq]
        calc
          _ ≤ |ell-(L+2*Real.log L-Real.log C)|+|Real.log C| := abs_sub _ _
          _ ≤ Q*Real.log L/L+|Real.log C| := add_le_add hrefined le_rfl
          _ ≤ |Real.log C|+Q := by
            have h := mul_le_mul_of_nonneg_left hlogupper hQ; have h' : Q*Real.log L/L ≤ Q := (div_le_iff₀ hL).mpr h; linarith
      have hlin : |(1-2*u)-(1-4*Real.log L/L)| ≤ (2*|Real.log C|+2*Q)/L := by
        have heq : (1-2*u)-(1-4*Real.log L/L) = (-2/L)*(ell-L-2*Real.log L) := by dsimp only [u]; ring
        rw [heq, abs_mul, abs_div, abs_of_pos hL]; norm_num
        calc
          _ ≤ (2/L)*(|Real.log C|+Q) := mul_le_mul_of_nonneg_left hshape (by positivity)
          _ = _ := by ring
      change |X*Y-(1-4*Real.log L/L)| ≤ _
      calc
        _ ≤ |X*Y-Y|+|Y-(1-2*u)|+|(1-2*u)-(1-4*Real.log L/L)| := by
          have h := abs_sub_le (X*Y) Y (1-4*Real.log L/L); have h' := abs_sub_le Y (1-2*u) (1-4*Real.log L/L); linarith
        _ ≤ 8*H/L+112*B^2/L+(2*|Real.log C|+2*Q)/L := add_le_add (add_le_add hXY hremrate) hlin
        _ = _ := by ring
    have relative_stationary_error {ε c d B t ell v r g : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c) (hd : 0 < d) (hB : 0 ≤ B) (ht : 0 < t) (hell : 1 ≤ ell) (hεell : ε*ell ≤ 3) (hslope : |v-c*t*ell^2| ≤ B*t*(ell+1))
        (hrate : |r+d| ≤ B*t) (hgbound : |g| ≤ B) (hstationary : (1+ε)*v+ε*r+ε^2*g = 0) (hscale : t*ell^2 ≤ (2*d/c)*ε) : |c*t*ell^2-d*ε| ≤ 2*B*t*ell+B*ε*t+(B+d)*ε^2 ∧ |t*ell^2/((d/c)*ε)-1| ≤ (6*B/c+3*B/d+3)/ell := by
      have hell0 : 0 < ell := by linarith
      have hcoef : 0 < 1+ε := by linarith
      have hidentity : (1+ε)*(v-d*ε) = -ε*(r+d)-ε^2*(g+d) := by nlinarith [hstationary]
      have hgd : |g+d| ≤ B+d := by
        calc
          _ ≤ |g|+|d| := abs_add_le _ _
          _ ≤ B+d := by rw [abs_of_pos hd]; exact add_le_add hgbound le_rfl
      have hv : |v-d*ε| ≤ B*ε*t+(B+d)*ε^2 := by
        have heq : |(1+ε)*(v-d*ε)| = (1+ε)*|v-d*ε| := by rw [abs_mul, abs_of_pos hcoef]
        have hab : |(1+ε)*(v-d*ε)| ≤ ε*|r+d|+ε^2*|g+d| := by
          rw [hidentity]
          calc
            _ ≤ |-ε*(r+d)|+|ε^2*(g+d)| := abs_sub _ _
            _ = _ := by rw [abs_mul, abs_mul, abs_neg, abs_of_pos hε, abs_of_nonneg (sq_nonneg ε)]
        have hbound : (1+ε)*|v-d*ε| ≤ B*ε*t+(B+d)*ε^2 := by
          rw [heq] at hab; have h1 := mul_le_mul_of_nonneg_left hrate hε.le; have h2 := mul_le_mul_of_nonneg_left hgd (sq_nonneg ε); nlinarith
        have hnonneg := mul_nonneg hε.le (abs_nonneg (v-d*ε)); nlinarith
      have hraw : |c*t*ell^2-d*ε| ≤ 2*B*t*ell+B*ε*t+(B+d)*ε^2 := by
        calc
          _ ≤ |c*t*ell^2-v|+|v-d*ε| := abs_sub_le _ _ _
          _ ≤ B*t*(ell+1)+(B*ε*t+(B+d)*ε^2) := add_le_add (by simpa only [abs_sub_comm] using hslope) hv
          _ ≤ _ := by
            have h := mul_le_mul_of_nonneg_left (show ell+1 ≤ 2*ell by linarith) (mul_nonneg hB ht.le)
            nlinarith
      have hscaled : |c*t*ell^2-d*ε| *ell ≤ (6*B/c+3*B/d+3)*(d*ε) := by
        have hεle : ε ≤ ell := hε1.trans hell
        have hsecond := mul_le_mul_of_nonneg_left hεle (show 0 ≤ B*t*ell by positivity)
        have hthird := mul_le_mul_of_nonneg_left hεell (show 0 ≤ (B+d)*ε by positivity)
        have hfirst := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 3*B by positivity)
        have hrawmul := mul_le_mul_of_nonneg_right hraw hell0.le
        have heq : (6*B/c+3*B/d+3)*(d*ε) = 3*B*((2*d/c)*ε)+3*(B+d)*ε := by
          field_simp
          <;> ring
        rw [heq]; nlinarith [hrawmul,hsecond,hthird,hfirst]
      refine ⟨hraw, ?_⟩
      have hnorm : t*ell^2/((d/c)*ε)-1 = (c*t*ell^2-d*ε)/(d*ε) := by
        field_simp
        <;> ring
      rw [hnorm, abs_div, abs_of_pos (mul_pos hd hε)]
      apply (div_le_div_iff₀ (mul_pos hd hε) hell0).mpr
      exact hscaled
    have objective_error {ε c d B t ell δ r r0 g g0 : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (hB : 0 ≤ B) (ht : 0 ≤ t) (hell : 1 ≤ ell) (hphase : |δ-(c/2)*t^2*ell^2| ≤ B*t^2*(ell+1)) (hr : |r-r0+d*t| ≤ B*t^2) (hg : |g-g0| ≤ B*t)
        (hstationary : |c*t*ell^2-d*ε| ≤ 2*B*t*ell+B*ε*t+(B+d)*ε^2) : |(1+ε)*δ+ε*r+ε^2*g-(ε*r0+ε^2*g0)+(d/2)*ε*t| ≤ 3*B*t^2*ell+((c+7*B)/2)*ε*t^2*ell^2+((3*B+d)/2)*ε^2*t := by
      have hell0 : 0 ≤ ell := by linarith
      have hphase2 : |δ-(c/2)*t^2*ell^2| ≤ 2*B*t^2*ell := by
        calc
          _ ≤ B*t^2*(ell+1) := hphase
          _ ≤ _ := by
            have h := mul_le_mul_of_nonneg_left (show ell+1 ≤ 2*ell by linarith) (show 0 ≤ B*t^2 by positivity)
            nlinarith
      have hδabs : |δ| ≤ (c/2+2*B)*t^2*ell^2 := by
        have h := abs_sub_le δ ((c/2)*t^2*ell^2) 0
        simp only [sub_zero,abs_of_nonneg (show 0 ≤ (c/2)*t^2*ell^2 by positivity)] at h
        have hsq : ell ≤ ell^2 := by nlinarith
        have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*B*t^2 by positivity)
        nlinarith
      have hmiddle : |(c/2)*t^2*ell^2-(d/2)*ε*t| ≤ B*t^2*ell+(B/2)*ε*t^2+((B+d)/2)*ε^2*t := by
        have heq : (c/2)*t^2*ell^2-(d/2)*ε*t = (t/2)*(c*t*ell^2-d*ε) := by ring
        rw [heq,abs_mul,abs_of_nonneg (show 0 ≤ t/2 by positivity)]
        have h := mul_le_mul_of_nonneg_left hstationary (show 0 ≤ t/2 by positivity)
        nlinarith
      have hεphase : |ε*δ| ≤ ε*((c/2+2*B)*t^2*ell^2) := by rw [abs_mul,abs_of_nonneg hε]; exact mul_le_mul_of_nonneg_left hδabs hε
      have hεr : |ε*(r-r0+d*t)| ≤ ε*(B*t^2) := by rw [abs_mul,abs_of_nonneg hε]; exact mul_le_mul_of_nonneg_left hr hε
      have hεg : |ε^2*(g-g0)| ≤ ε^2*(B*t) := by rw [abs_mul,abs_of_nonneg (sq_nonneg ε)]; exact mul_le_mul_of_nonneg_left hg (sq_nonneg ε)
      have heq : (1+ε)*δ+ε*r+ε^2*g-(ε*r0+ε^2*g0)+(d/2)*ε*t = (δ-(c/2)*t^2*ell^2)+((c/2)*t^2*ell^2-(d/2)*ε*t)+ ε*δ+ε*(r-r0+d*t)+ε^2*(g-g0) := by ring
      rw [heq]
      have hab : ∀ x y z v w : ℝ, |x+y+z+v+w| ≤ |x|+|y|+|z|+|v|+|w| := by
        intro x y z v w
        linarith [abs_add_le x y, abs_add_le (x+y) z,
          abs_add_le (x+y+z) v, abs_add_le (x+y+z+v) w]
      calc
        _ ≤ |δ-(c/2)*t^2*ell^2|+|(c/2)*t^2*ell^2-(d/2)*ε*t|+
            |ε*δ|+|ε*(r-r0+d*t)|+|ε^2*(g-g0)| := hab _ _ _ _ _
        _ ≤ 2*B*t^2*ell+(B*t^2*ell+(B/2)*ε*t^2+((B+d)/2)*ε^2*t)+ ε*((c/2+2*B)*t^2*ell^2)+ε*(B*t^2)+ε^2*(B*t) := add_le_add (add_le_add (add_le_add (add_le_add hphase2 hmiddle) hεphase) hεr) hεg
        _ ≤ _ := by
          have hsq : 1 ≤ ell^2 := by nlinarith
          have h := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (3*B/2)*ε*t^2 by positivity)
          nlinarith
    have log_square_bound {L : ℝ} (hL : 0 < L) (hlog : 0 ≤ Real.log L) : (Real.log L)^2 ≤ 4*L := by
      have h := Real.log_le_rpow_div hL.le (by norm_num : (0:ℝ)<1/2); rw [← Real.sqrt_eq_rpow] at h
      have hbound : Real.log L ≤ 2*Real.sqrt L := by linarith
      have hsq := mul_self_le_mul_self hlog hbound; nlinarith [Real.sq_sqrt hL.le]
    have value_scale_absorption {ε c d B q t ell L E : ℝ} (hε : 0 ≤ ε) (hc : 0 ≤ c) (hd : 0 ≤ d) (hB : 0 ≤ B) (hq : 0 ≤ q) (ht : 0 ≤ t) (hL : 0 < L) (helllo : L/2 ≤ ell) (hellhi : ell ≤ 3*L)
        (hεL : ε*L ≤ 1) (hscale : t*ell^2 ≤ q*ε) (herror : |E| ≤ 3*B*t^2*ell+((c+7*B)/2)*ε*t^2*ell^2+ ((3*B+d)/2)*ε^2*t) : |E| ≤ (144*B*q^2+72*(c+7*B)*q^2+2*(3*B+d)*q)*ε^2/L^3 := by
      have hell0 : 0 ≤ ell := by linarith
      have htbound : t ≤ 4*q*ε/L^2 := by
        have hs := mul_self_le_mul_self (show 0 ≤ L/2 by positivity) helllo
        have hprod := mul_le_mul_of_nonneg_left hs ht
        apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
        nlinarith
      have htbound0 : 0 ≤ 4*q*ε/L^2 := by positivity
      have ht2 : t^2 ≤ (4*q*ε/L^2)^2 := by
        have h := mul_self_le_mul_self ht htbound; simpa only [← sq] using h
      have hell2 : ell^2 ≤ (3*L)^2 := by
        have h := mul_self_le_mul_self hell0 hellhi; simpa only [← sq] using h
      have h1 : t^2*ell ≤ 48*q^2*ε^2/L^3 := by
        calc
          _ ≤ (4*q*ε/L^2)^2*(3*L) := mul_le_mul ht2 hellhi hell0 (sq_nonneg _)
          _ = _ := by field_simp; ring
      have h2 : ε*t^2*ell^2 ≤ 144*q^2*ε^3/L^2 := by
        calc
          _ = ε*(t^2*ell^2) := by ring
          _ ≤ ε*((4*q*ε/L^2)^2*(3*L)^2) := mul_le_mul_of_nonneg_left (mul_le_mul ht2 hell2 (sq_nonneg _) (sq_nonneg _)) hε
          _ = _ := by field_simp; ring
      have h3 : ε^2*t ≤ 4*q*ε^3/L^2 := by
        calc
          _ ≤ ε^2*(4*q*ε/L^2) := mul_le_mul_of_nonneg_left htbound (sq_nonneg ε)
          _ = _ := by ring
      have he : ε^3/L^2 ≤ ε^2/L^3 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hL) (pow_pos hL 3)).mpr
        have h := mul_le_mul_of_nonneg_left hεL (show 0 ≤ ε^2*L^2 by positivity)
        nlinarith
      have h2' : ε*t^2*ell^2 ≤ 144*q^2*ε^2/L^3 := by
        calc
          _ ≤ 144*q^2*ε^3/L^2 := h2
          _ = (144*q^2)*(ε^3/L^2) := by ring
          _ ≤ (144*q^2)*(ε^2/L^3) := mul_le_mul_of_nonneg_left he (by positivity)
          _ = _ := by ring
      have h3' : ε^2*t ≤ 4*q*ε^2/L^3 := by
        calc
          _ ≤ 4*q*ε^3/L^2 := h3
          _ = (4*q)*(ε^3/L^2) := by ring
          _ ≤ (4*q)*(ε^2/L^3) := mul_le_mul_of_nonneg_left he (by positivity)
          _ = _ := by ring
      calc
        |E| ≤ 3*B*t^2*ell+((c+7*B)/2)*ε*t^2*ell^2+((3*B+d)/2)*ε^2*t := herror
        _ = 3*B*(t^2*ell)+((c+7*B)/2)*(ε*t^2*ell^2)+((3*B+d)/2)*(ε^2*t) := by ring
        _ ≤ 3*B*(48*q^2*ε^2/L^3)+((c+7*B)/2)*(144*q^2*ε^2/L^3)+ ((3*B+d)/2)*(4*q*ε^2/L^3) := by gcongr
        _ = _ := by ring
    classical
    let σ' := min σ (Real.exp (-16)); have hσ' : 0 < σ' := lt_min hσ (Real.exp_pos _); have hσ'σ : σ' ≤ σ := min_le_left _ _
    obtain ⟨a, εbase, ha, haσ', hbase, hbaseexp, hmin⟩ := uniform_localization δ v r r₁ g g₁ hσ' hc hd hB hv0 hδ hr hg (fun t ht hts => hslope t ht (hts.trans hσ'σ)) (fun t hts => hrate t (hts.trans hσ'σ))
        (fun t hts => hgbound t (hts.trans hσ'σ))
    have haσ : a ≤ σ := haσ'.trans hσ'σ; have haexp : a ≤ Real.exp (-16) := haσ'.trans (min_le_right _ _); let p := d/(5*c); let q := 2*d/c; let C := d/c; let D := d^2/(2*c); let A0 := max (|Real.log p|) (|Real.log q|)
    let B1 := 2+2*Real.log 3+A0; let H := 6*B/c+3*B/d+3; let Qell := 4*(B1+H); let Qt := 8*H+2*|Real.log C|+2*Qell+112*B1^2; let Qv0 := 144*B*q^2+72*(c+7*B)*q^2+2*(3*B+d)*q; let Q := max 1 (max Qell (max Qt (Qv0+D*Qt)))
    let T := max 16 (max (2*A0) (4*H)); let ε₀ := min εbase (Real.exp (-T))
    have hp : 0 < p := by dsimp only [p]; positivity
    have hq : 0 < q := by dsimp only [q]; positivity
    have hC : 0 < C := by dsimp only [C]; positivity
    have hD : 0 ≤ D := by dsimp only [D]; positivity
    have hA0 : 0 ≤ A0 := (abs_nonneg _).trans (le_max_left _ _); have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hB1 : 0 ≤ B1 := by dsimp only [B1]; positivity
    have hH : 0 ≤ H := by dsimp only [H]; positivity
    have hQell : 0 ≤ Qell := by dsimp only [Qell]; positivity
    have hQt : 0 ≤ Qt := by dsimp only [Qt]; positivity
    have hQ1 : 1 ≤ Q := le_max_left _ _; have hQellQ : Qell ≤ Q := (le_max_left _ _).trans (le_max_right _ _); have hQtQ : Qt ≤ Q := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hQvQ : Qv0+D*Qt ≤ Q := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)); have hε₀ : 0 < ε₀ := lt_min hbase (Real.exp_pos _)
    have hε₀exp : ε₀ < Real.exp (-2) := (min_le_left _ _).trans_lt hbaseexp; dsimp only
    refine ⟨a, ε₀, Q, ha, haσ, hε₀, hε₀exp, hQ1, ?_⟩
    intro ε hε hεsmall; have hεbase : ε < εbase := hεsmall.trans_le (min_le_left _ _)
    obtain ⟨hexists,hall⟩ := hmin ε hε hεbase
    refine ⟨hexists, ?_⟩
    intro t ht hminimizer
    obtain ⟨htpos,htlt,hstationary,hpε,hqε⟩ := hall t ht hminimizer
    refine ⟨htpos,htlt,hstationary,?_⟩
    let L := Real.log ε⁻¹; let ell := Real.log t⁻¹
    have hLbound : T ≤ L := by
      have hεT : ε ≤ Real.exp (-T) := hεsmall.le.trans (min_le_right _ _); have h := Real.log_le_log hε hεT; rw [Real.log_exp] at h; dsimp only [L]; rw [Real.log_inv]; linarith
    have hL16 : 16 ≤ L := (le_max_left _ _).trans hLbound; have hLA : 2*A0 ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hLbound
    have hLH : 4*H ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hLbound
    have hL0 : 0 < L := by linarith
    have hell16 : 16 ≤ ell := by
      have h := Real.log_le_log htpos (ht.2.trans haexp); rw [Real.log_exp] at h; dsimp only [ell]; rw [Real.log_inv]; linarith
    have hell1 : 1 ≤ ell := by linarith
    have hell0 : 0 < ell := by linarith
    have hε1 : ε ≤ 1 := by
      have hexp : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num); exact (hεsmall.trans hε₀exp).le.trans hexp.le
    have hεL : ε*L ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hε); have hmul := mul_le_mul_of_nonneg_left h hε.le; change ε*L ≤ ε*(ε⁻¹-1) at hmul; rw [mul_sub, mul_inv_cancel₀ hε.ne', mul_one] at hmul; linarith
    have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2); norm_num at h ⊢; exact h
    have hlog16 : Real.log 16 = 4*Real.log 2 := by
      have h := Real.log_pow (2:ℝ) 4; norm_num at h; exact h
    have hlogL1 : 1 ≤ Real.log L := by
      have h := Real.log_le_log (by norm_num : (0:ℝ)<16) hL16; rw [hlog16] at h; linarith
    have hlogL0 : 0 ≤ Real.log L := by linarith
    have hscale : p*ε ≤ t*ell^2 ∧ t*ell^2 ≤ q*ε := ⟨hpε,hqε⟩
    obtain ⟨helllo,hellhi,hcoarse⟩ := logarithmic_bootstrap hp hq hε htpos rfl rfl hell16 hL16 hLA hscale
    have hεell : ε*ell ≤ 3 := by
      have h := mul_le_mul_of_nonneg_left hellhi hε.le; nlinarith
    have hellH : 2*H ≤ ell := by linarith
    have htσ : |t| ≤ σ := by rw [abs_of_pos htpos]; exact ht.2.trans haσ
    have hslope' : |v t-c*t*ell^2| ≤ B*t*(ell+1) := by simpa only [abs_of_pos htpos] using hslope t (by rwa [abs_of_pos htpos]) htσ
    have hrate' : |r₁ t+d| ≤ B*t := by simpa only [abs_of_pos htpos] using hrate t htσ
    obtain ⟨hraw,hrel⟩ := relative_stationary_error hε hε1 hc hd hB htpos hell1 hεell hslope' hrate' (hgbound t htσ) hstationary hqε
    have href := refined_logarithm hε htpos hC hH hB1 hL0 rfl rfl helllo hellhi hellH hlogL1 hcoarse hrel
    have hdisp := displacement_estimate hL0 helllo hellhi hH hB1 hQell hlogL0 (log_square_bound hL0 hlogL0) hcoarse href hrel
    have htL : t*L^2/(C*ε) = (t*ell^2/(C*ε))*(L^2/ell^2) := by field_simp [hell0.ne']
    have hdisp' : |t*L^2/(C*ε)-(1-4*Real.log L/L)| ≤ Qt/L := by rw [htL]; exact hdisp
    have hrates : |r t-r 0+d*t| ≤ B*t^2 ∧ |g t-g 0| ≤ B*t := mean_value_controls r r₁ g g₁ hB htpos.le (ht.2.trans haσ) hr hg hrate hgbound
    have hphase' : |δ t-(c/2)*t^2*ell^2| ≤ B*t^2*(ell+1) := by simpa only [abs_of_pos htpos] using hphase t (by rwa [abs_of_pos htpos]) htσ
    let E := (1+ε)*δ t+ε*r t+ε^2*g t-(ε*r 0+ε^2*g 0)+(d/2)*ε*t
    have hE : |E| ≤ Qv0*ε^2/L^3 := value_scale_absorption hε.le hc.le hd.le hB hq.le htpos.le hL0 helllo hellhi hεL hqε (objective_error hε.le hc.le hB htpos.le hell1 hphase' hrates.1 hrates.2 hraw)
    have hweight : 0 ≤ D*ε^2/L^2 := by positivity
    have hid : (d/2)*ε*t = (D*ε^2/L^2)*(t*L^2/(C*ε)) := by
      dsimp only [D,C]; field_simp
      <;> ring
    have hvalue : |(1+ε)*δ t+ε*r t+ε^2*g t-(ε*r 0+ε^2*g 0- D*ε^2/L^2*(1-4*Real.log L/L))| ≤ (Qv0+D*Qt)*ε^2/L^3 := by
      have heq : (1+ε)*δ t+ε*r t+ε^2*g t-(ε*r 0+ε^2*g 0- D*ε^2/L^2*(1-4*Real.log L/L)) = E-(D*ε^2/L^2)*(t*L^2/(C*ε)-(1-4*Real.log L/L)) := by
        dsimp only [E]; simp only [mul_sub]; rw [← hid]; ring
      rw [heq]
      calc
        _ ≤ |E|+|(D*ε^2/L^2)*(t*L^2/(C*ε)-(1-4*Real.log L/L))| := abs_sub _ _
        _ = |E|+(D*ε^2/L^2)*|t*L^2/(C*ε)-(1-4*Real.log L/L)| := by rw [abs_mul,abs_of_nonneg hweight]
        _ ≤ Qv0*ε^2/L^3+(D*ε^2/L^2)*(Qt/L) := add_le_add hE (mul_le_mul_of_nonneg_left hdisp' hweight)
        _ = _ := by ring
    refine ⟨href.trans ?_, hdisp'.trans ?_, hvalue.trans ?_⟩
    · have h := mul_le_mul_of_nonneg_right hQellQ
        (show 0 ≤ Real.log L/L by positivity)
      simpa only [Qell, L, mul_div_assoc] using h
    · exact div_le_div_of_nonneg_right hQtQ hL0.le
    · have h := mul_le_mul_of_nonneg_right hQvQ (show 0 ≤ ε^2/L^3 by positivity)
      simpa only [L, mul_div_assoc] using h
  -- The actual spectrum is nonempty and retains every positive-ordinate zero.
  have actual_driving_positive :
      let k := fun rho : PositiveZetaZero =>
        weight rho*(ordinate rho)^2/(1/4+(ordinate rho)^2)
      Summable k ∧ 0 < ∑' rho, k rho := by
    classical
    let k := fun rho : PositiveZetaZero =>
      weight rho*(ordinate rho)^2/(1/4+(ordinate rho)^2)
    change Summable k ∧ 0 < ∑' rho, k rho; have hγ (rho : PositiveZetaZero) : 0 < ordinate rho := rho.property.2
    have hm (rho : PositiveZetaZero) : 0 < multiplicity rho := by
      have h := Zeta23.ZetaSeam.one_le_mult_holds rho.val rho.property.1
      have hcast : (0:ℝ) < (Zeta23.zeroMult rho.val : ℝ) := by exact_mod_cast (by omega : 0 < Zeta23.zeroMult rho.val)
      exact hcast
    have ha (rho : PositiveZetaZero) : 0 < weight rho := by
      unfold weight phaseWeight
      exact div_pos (hm rho) (mul_pos (hγ rho) (by positivity))
    have hk0 (rho : PositiveZetaZero) : 0 ≤ k rho := by dsimp only [k]; exact div_nonneg (mul_nonneg (ha rho).le (sq_nonneg _)) (by positivity)
    have hkbound (rho : PositiveZetaZero) : k rho ≤ weight rho := by
      dsimp only [k]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<1/4+(ordinate rho)^2)).mpr
      nlinarith [ha rho]
    have hks : Summable k := Summable.of_nonneg_of_le hk0 hkbound actual_zeta_phase_stiffness.1
    have inhabitant : PositiveZetaZero := by
      let Z := zetaZeroData; have hz : Zeta23.IsNontrivialZero (Z.zero 0) := Z.zero_isNontrivial 0; have him : (Z.zero 0).im ≠ 0 := D5.S3.Weil.ZetaBridge.AlternatingZetaContinuation.ZeroData.im_ne_zero Z 0 hz
      by_cases hpositive : 0 < (Z.zero 0).im
      · exact ⟨Z.zero 0, hz, hpositive⟩
      · have hnegative : (Z.zero 0).im < 0 :=
          (lt_or_gt_of_ne him).resolve_right hpositive
        refine ⟨Z.zero (Z.conjugation 0), Z.zero_isNontrivial _, ?_⟩
        rw [Z.zero_conjugation, Complex.conj_im]; exact neg_pos.mpr hnegative
    have hkpositive : 0 < k inhabitant := by dsimp only [k]; exact div_pos (mul_pos (ha inhabitant) (sq_pos_of_pos (hγ inhabitant))) (by positivity)
    have hpart : k inhabitant ≤ ∑' rho, k rho := by simpa using hks.sum_le_tsum {inhabitant} (fun rho _ => hk0 rho)
    exact ⟨hks, hkpositive.trans_le hpart⟩
  have coefficient_bounds {γ : ℝ} (hγ : 0 < γ) :
      let D : ℝ := 1/4+γ^2; let g : ℝ := 8*γ^2/D^2; let h : ℝ := -2/γ+8*γ/D-4*γ/D^2
      0 < D ∧ 0 ≤ γ^2/D ∧ γ^2/D ≤ 1 ∧
        0 ≤ γ^2/D^2 ∧ γ^2/D^2 ≤ 1 ∧
        |g| ≤ 8 ∧ |γ*h| ≤ 14 := by
    dsimp only; let D : ℝ := 1/4+γ^2
    have hD : 0 < D := by dsimp only [D]; positivity
    have hDs : 0 < D^2 := sq_pos_of_pos hD; have hratio0 : 0 ≤ γ^2/D := div_nonneg (sq_nonneg γ) hD.le
    have hratio1 : γ^2/D ≤ 1 := by
      apply (div_le_iff₀ hD).mpr
      dsimp only [D]; nlinarith
    have hratio20 : 0 ≤ γ^2/D^2 := div_nonneg (sq_nonneg γ) hDs.le
    have hratio21 : γ^2/D^2 ≤ 1 := by
      apply (div_le_iff₀ hDs).mpr
      have hs := sq_nonneg (γ^2-1/4); dsimp only [D]; nlinarith
    have hg : |8*γ^2/D^2| ≤ 8 := by
      rw [abs_of_nonneg (by positivity : 0 ≤ 8*γ^2/D^2)]; have h := mul_le_mul_of_nonneg_left hratio21 (by norm_num : (0:ℝ) ≤ 8)
      calc
        8*γ^2/D^2 = 8*(γ^2/D^2) := by ring
        _ ≤ 8 := by simpa using h
    have heq : γ*(-2/γ+8*γ/D-4*γ/D^2) = -2+8*(γ^2/D)-4*(γ^2/D^2) := by
      field_simp
      <;> ring
    have hh : |γ*(-2/γ+8*γ/D-4*γ/D^2)| ≤ 14 := by
      rw [heq]
      apply abs_le.mpr
      constructor <;> nlinarith
    exact ⟨hD, hratio0, hratio1, hratio20, hratio21, hg, hh⟩
  have smooth_driving {ι : Type} (γ a g h : ι → ℝ) (hγ : ∀ i, 0 < γ i) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) (hsag : Summable (fun i => a i*γ i)) (hg : ∀ i, |g i| ≤ 8) (hh : ∀ i, |γ i*h i| ≤ 14) :
      let G := fun t => ∑' i, a i*(g i*Real.cos (γ i*t)-h i*Real.sin (γ i*t)); let G₁ := fun t => ∑' i, a i*(-g i*γ i*Real.sin (γ i*t)-h i*γ i*Real.cos (γ i*t))
      (∀ t, HasDerivAt G (G₁ t) t) ∧ Continuous G₁ ∧
      (∀ t, |G₁ t| ≤ 8*(∑' i, a i*γ i)+14*(∑' i, a i)) := by
    dsimp only; let b := fun i => 8*(a i*γ i)+14*a i; have hsb : Summable b := (hsag.mul_left 8).add (hsa.mul_left 14)
    have hd (i : ι) (t : ℝ) : HasDerivAt (fun x => a i*(g i*Real.cos (γ i*x)-h i*Real.sin (γ i*x))) (a i*(-g i*γ i*Real.sin (γ i*t)-h i*γ i*Real.cos (γ i*t))) t := by
      convert! ((((Real.hasDerivAt_cos (γ i*t)).comp t ((hasDerivAt_id t).const_mul (γ i))).const_mul (g i)).sub (((Real.hasDerivAt_sin (γ i*t)).comp t
          ((hasDerivAt_id t).const_mul (γ i))).const_mul (h i))).const_mul (a i) using 1
      ring
    have hb (i : ι) (t : ℝ) : ‖a i*(-g i*γ i*Real.sin (γ i*t)-h i*γ i*Real.cos (γ i*t))‖ ≤ b i := by
      have hgc : |a i*g i*γ i| ≤ 8*(a i*γ i) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (ha i), abs_of_pos (hγ i)]; have h := mul_le_mul_of_nonneg_left (hg i) (mul_nonneg (ha i) (hγ i).le); nlinarith
      have hhc : |a i*(γ i*h i)| ≤ 14*a i := by
        rw [abs_mul, abs_of_nonneg (ha i)]; have h := mul_le_mul_of_nonneg_left (hh i) (ha i); nlinarith
      have hs : |a i*g i*γ i*Real.sin (γ i*t)| ≤ 8*(a i*γ i) := by
        rw [abs_mul]
        calc
          _ ≤ |a i*g i*γ i| *1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
          _ ≤ _ := by simpa using hgc
      have hc : |a i*(γ i*h i)*Real.cos (γ i*t)| ≤ 14*a i := by
        rw [abs_mul]
        calc
          _ ≤ |a i*(γ i*h i)| *1 := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
          _ ≤ _ := by simpa using hhc
      rw [Real.norm_eq_abs]
      have heq : a i*(-g i*γ i*Real.sin (γ i*t)-h i*γ i*Real.cos (γ i*t)) = -(a i*g i*γ i*Real.sin (γ i*t))-a i*(γ i*h i)*Real.cos (γ i*t) := by ring
      rw [heq]
      calc
        _ ≤ |-(a i*g i*γ i*Real.sin (γ i*t))|+|a i*(γ i*h i)*Real.cos (γ i*t)| := abs_sub _ _
        _ ≤ b i := by rw [abs_neg]; exact add_le_add hs hc
    have hzero : Summable (fun i => a i*(g i*Real.cos (γ i*(0:ℝ))-h i*Real.sin (γ i*(0:ℝ)))) := by
      simp only [mul_zero, Real.cos_zero, mul_one, Real.sin_zero, sub_zero]
      apply Summable.of_norm_bounded (hsa.mul_left 8)
      intro i; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha i)]; have h := mul_le_mul_of_nonneg_left (hg i) (ha i); nlinarith
    refine ⟨fun t => hasDerivAt_tsum hsb hd hb hzero t, ?_, ?_⟩
    · exact continuous_tsum (fun i => continuous_const.mul
        ((continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).sub
          (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))))) hsb hb
    · intro t
      have hbound := tsum_of_norm_bounded hsb.hasSum (fun i => hb i t); rw [Real.norm_eq_abs] at hbound; dsimp only [b] at hbound; rw [(hsag.mul_left 8).tsum_add (hsa.mul_left 14), tsum_mul_left, tsum_mul_left] at hbound
      exact hbound
  have remainder_rate {ι : Type} (γ a : ι → ℝ) (hγ : ∀ i, 0 < γ i) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) (hsag : Summable (fun i => a i*γ i)) :
      let D := fun i => (1:ℝ)/4+(γ i)^2; let k := fun i => a i*(γ i)^2/D i; let R₁ := fun t => ∑' i, a i*(-γ i/D i*Real.sin (γ i*t)-
        2*(γ i)^2/D i*Real.cos (γ i*t))
      Summable k ∧ ∀ t,
        |R₁ t+2*(∑' i, k i)| ≤ |t| *((∑' i, k i)+2*(∑' i, a i*γ i)) := by
    dsimp only; let D := fun i => (1:ℝ)/4+(γ i)^2; let k := fun i => a i*(γ i)^2/D i
    have hD (i : ι) : 0 < D i := by dsimp only [D]; positivity
    have hk0 (i : ι) : 0 ≤ k i := div_nonneg (mul_nonneg (ha i) (sq_nonneg _)) (hD i).le
    have hkbound (i : ι) : k i ≤ a i := by
      apply (div_le_iff₀ (hD i)).mpr
      dsimp only [D]; nlinarith [ha i]
    have hks : Summable k := Summable.of_nonneg_of_le hk0 hkbound hsa
    refine ⟨hks, ?_⟩
    intro t; let z := fun i => a i*(-γ i/D i*Real.sin (γ i*t)-
        2*(γ i)^2/D i*Real.cos (γ i*t))+2*k i
    let b := fun i => |t| *(k i+2*(a i*γ i)); have hsb : Summable b := (hks.add (hsag.mul_left 2)).mul_left |t|
    have hb (i : ι) : ‖z i‖ ≤ b i := by
      have hγi := hγ i; have hai := ha i; have hDi := hD i; have hki := hk0 i
      have hfirst : |a i*γ i/D i*Real.sin (γ i*t)| ≤ |t| *k i := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ a i*γ i/D i)]
        calc
          _ ≤ (a i*γ i/D i)*|γ i*t| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by positivity)
          _ = |t| *k i := by rw [abs_mul, abs_of_pos (hγ i)]; dsimp only [k]; ring
      have hcos : |1-Real.cos (γ i*t)| ≤ |γ i*t| := by
        simpa only [Real.cos_zero, sub_zero, abs_sub_comm] using Real.abs_cos_sub_cos_le (γ i*t) 0
      have hsecond : |2*k i*(1-Real.cos (γ i*t))| ≤ |t| *(2*(a i*γ i)) := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2*k i)]
        calc
          _ ≤ 2*k i*|γ i*t| := mul_le_mul_of_nonneg_left hcos (by positivity)
          _ = |t| *(2*(k i*γ i)) := by rw [abs_mul, abs_of_pos (hγ i)]; ring
          _ ≤ |t| *(2*(a i*γ i)) := by
            gcongr
            exact hkbound i
      have hid : z i = -(a i*γ i/D i*Real.sin (γ i*t))+ 2*k i*(1-Real.cos (γ i*t)) := by dsimp only [z,k]; ring
      rw [Real.norm_eq_abs,hid]
      calc
        _ ≤ |-(a i*γ i/D i*Real.sin (γ i*t))|+
            |2*k i*(1-Real.cos (γ i*t))| := abs_add_le _ _
        _ ≤ |t| *k i+|t| *(2*(a i*γ i)) := by rw [abs_neg]; exact add_le_add hfirst hsecond
        _ = b i := by dsimp only [b]; ring
    have hsz : Summable z := Summable.of_norm_bounded hsb hb
    have hzsum : ∑' i, a i*(-γ i/D i*Real.sin (γ i*t)- 2*(γ i)^2/D i*Real.cos (γ i*t)) = (∑' i, z i)-2*(∑' i, k i) := by
      have heq : (fun i => a i*(-γ i/D i*Real.sin (γ i*t)- 2*(γ i)^2/D i*Real.cos (γ i*t))) = fun i => z i-2*k i := by
        funext i; dsimp only [z]; ring
      rw [heq, hsz.tsum_sub (hks.mul_left 2), tsum_mul_left]
    have hbound := tsum_of_norm_bounded hsb.hasSum hb; rw [Real.norm_eq_abs] at hbound; change |(∑' i, a i*(-γ i/D i*Real.sin (γ i*t)- 2*(γ i)^2/D i*Real.cos (γ i*t)))+2*(∑' i,k i)| ≤ _; rw [hzsum, sub_add_cancel]
    simpa only [b, tsum_mul_left, hks.tsum_add (hsag.mul_left 2)] using hbound
  have remainder_regularity {ι : Type} (γ a : ι → ℝ) (hγ : ∀ i, 0 < γ i) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) (hsag : Summable (fun i => a i*γ i)) :
      let D := fun i => (1:ℝ)/4+(γ i)^2; let R := fun t => ∑' i, a i*(Real.cos (γ i*t)/D i-
        2*γ i/D i*Real.sin (γ i*t))
      let R₁ := fun t => ∑' i, a i*(-γ i/D i*Real.sin (γ i*t)-
        2*(γ i)^2/D i*Real.cos (γ i*t))
      (∀ t, Summable (fun i => a i*(Real.cos (γ i*t)/D i-
        2*γ i/D i*Real.sin (γ i*t)))) ∧
      (∀ t, HasDerivAt R (R₁ t) t) ∧ Continuous R₁ := by
    dsimp only; let D := fun i => (1:ℝ)/4+(γ i)^2
    have hD (i : ι) : 0 < D i := by dsimp only [D]; positivity
    have hD4 (i : ι) : 1/D i ≤ 4 := by
      apply (div_le_iff₀ (hD i)).mpr
      dsimp only [D]; nlinarith [sq_nonneg (γ i)]
    have hk (i : ι) : (γ i)^2/D i ≤ 1 := by
      apply (div_le_iff₀ (hD i)).mpr
      dsimp only [D]; nlinarith
    let b := fun i => 4*(a i*γ i)+2*a i; let b₀ := fun i => 4*a i+8*(a i*γ i); have hsb : Summable b := (hsag.mul_left 4).add (hsa.mul_left 2); have hsb₀ : Summable b₀ := (hsa.mul_left 4).add (hsag.mul_left 8)
    have hcoeff (i : ι) : a i/D i ≤ 4*a i ∧ a i*γ i/D i ≤ 4*(a i*γ i) ∧ a i*(γ i)^2/D i ≤ a i := by
      have h₀ := mul_le_mul_of_nonneg_left (hD4 i) (ha i); have h₁ := mul_le_mul_of_nonneg_left (hD4 i) (mul_nonneg (ha i) (hγ i).le); have h₂ := mul_le_mul_of_nonneg_left (hk i) (ha i)
      constructor
      · simpa only [mul_one_div, mul_comm] using h₀
      constructor
      · simpa only [mul_one_div, mul_comm] using h₁
      · simpa only [mul_div_assoc, mul_one] using h₂
    have bound_trig {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (u : ℝ) : |x*Real.cos u-y*Real.sin u| ≤ x+y := by
      calc
        _ ≤ |x*Real.cos u|+|y*Real.sin u| := abs_sub _ _
        _ ≤ x+y := by
          rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hy]; simpa only [mul_one] using add_le_add (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hx) (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hy)
    have hs (t : ℝ) : Summable (fun i => a i*(Real.cos (γ i*t)/D i- 2*γ i/D i*Real.sin (γ i*t))) := by
      apply Summable.of_norm_bounded hsb₀
      intro i; have hai := ha i; have hγi := hγ i; have hDi := hD i; rw [Real.norm_eq_abs]
      have heq : a i*(Real.cos (γ i*t)/D i-2*γ i/D i*Real.sin (γ i*t)) = (a i/D i)*Real.cos (γ i*t)-(2*(a i*γ i/D i))*Real.sin (γ i*t) := by ring
      rw [heq]; have h := bound_trig (by positivity : 0 ≤ a i/D i) (by positivity : 0 ≤ 2*(a i*γ i/D i)) (γ i*t); dsimp only [b₀]; exact h.trans (by linarith [(hcoeff i).1, (hcoeff i).2.1])
    have hd (i : ι) (t : ℝ) : HasDerivAt (fun x => a i*(Real.cos (γ i*x)/D i-2*γ i/D i*Real.sin (γ i*x))) (a i*(-γ i/D i*Real.sin (γ i*t)-2*(γ i)^2/D i*Real.cos (γ i*t))) t := by
      convert! ((((Real.hasDerivAt_cos (γ i*t)).comp t ((hasDerivAt_id t).const_mul (γ i))).div_const (D i)).sub (((Real.hasDerivAt_sin (γ i*t)).comp t
          ((hasDerivAt_id t).const_mul (γ i))).const_mul (2*γ i/D i))).const_mul (a i) using 1
      ring
    have hb (i : ι) (t : ℝ) : ‖a i*(-γ i/D i*Real.sin (γ i*t)-2*(γ i)^2/D i*Real.cos (γ i*t))‖ ≤ b i := by
      have hai := ha i; have hγi := hγ i; have hDi := hD i; rw [Real.norm_eq_abs]
      have heq : a i*(-γ i/D i*Real.sin (γ i*t)-2*(γ i)^2/D i*Real.cos (γ i*t)) = -((a i*γ i/D i)*Real.sin (γ i*t)+(2*(a i*(γ i)^2/D i))*Real.cos (γ i*t)) := by ring
      rw [heq, abs_neg]
      have hx : 0 ≤ a i*γ i/D i := by positivity
      have hy : 0 ≤ 2*(a i*(γ i)^2/D i) := by positivity
      calc
        _ ≤ |(a i*γ i/D i)*Real.sin (γ i*t)|+
            |(2*(a i*(γ i)^2/D i))*Real.cos (γ i*t)| := abs_add_le _ _
        _ ≤ a i*γ i/D i+2*(a i*(γ i)^2/D i) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hx, abs_of_nonneg hy]; simpa only [mul_one] using add_le_add (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hx) (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hy)
        _ ≤ b i := by dsimp only [b]; linarith [(hcoeff i).2.1, (hcoeff i).2.2]
    exact ⟨hs, fun t => hasDerivAt_tsum hsb hd hb (hs 0) t, continuous_tsum (fun i => continuous_const.mul ((continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))).sub
          (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))))) hsb hb⟩
  have same_source_decomposition {ι : Type} (γ a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) (t : ℝ) (hsR : Summable (fun i => a i*(Real.cos (γ i*t)/(1/4+(γ i)^2)- 2*γ i/(1/4+(γ i)^2)*Real.sin (γ i*t)))) :
      let D := fun i => (1:ℝ)/4+(γ i)^2; let F := ∑' i, a i*((1/D i-2)*Real.cos (γ i*t)-
        2*γ i/D i*Real.sin (γ i*t))
      let R := ∑' i, a i*(Real.cos (γ i*t)/D i-
        2*γ i/D i*Real.sin (γ i*t))
      F = phaseCost γ a t+R-2*(∑' i, a i) := by
    dsimp only
    have hsCos : Summable (fun i => a i*Real.cos (γ i*t)) := by
      apply Summable.of_norm_bounded hsa
      intro i; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha i)]; simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (ha i)
    have hF : (fun i => a i*((1/(1/4+(γ i)^2)-2)*Real.cos (γ i*t)- 2*γ i/(1/4+(γ i)^2)*Real.sin (γ i*t))) = fun i => a i*(Real.cos (γ i*t)/(1/4+(γ i)^2)-
        2*γ i/(1/4+(γ i)^2)*Real.sin (γ i*t))-2*(a i*Real.cos (γ i*t)) := by
      funext i
      ring
    have hcost : phaseCost γ a t = 2*(∑' i, a i)-2*(∑' i, a i*Real.cos (γ i*t)) := by
      unfold phaseCost
      have hid : (fun i => 2*a i*(1-Real.cos (γ i*t))) = fun i => 2*(a i-a i*Real.cos (γ i*t)) := by funext i; ring
      rw [hid, tsum_mul_left, hsa.tsum_sub hsCos]; ring
    rw [hF, hsR.tsum_sub (hsCos.mul_left 2), tsum_mul_left, hcost]; ring
  -- Connect the same objective to the allowed phase orbit and the RH identification.
  have phase_in_hull (hquarter : quarterPhase ∈ phaseHull) (t : ℝ) : shiftedPhase t ∈ phaseHull := by
    let f := fun z : PositiveZetaZero → ℂ => z*phaseOrbit t; have hf : Continuous f := continuous_id.mul continuous_const
    have horbit (s : ℝ) : f (phaseOrbit s) = phaseOrbit (s+t) := by
      funext rho
      dsimp only [f, phaseOrbit, Pi.mul_apply]; rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hsubset : range phaseOrbit ⊆ f ⁻¹' phaseHull := by
      rintro z ⟨s, rfl⟩
      change f (phaseOrbit s) ∈ phaseHull; rw [horbit]; exact subset_closure ⟨s+t, rfl⟩
    exact (closure_minimal hsubset (isClosed_closure.preimage hf)) hquarter
  have phase_identification (ε t : ℝ) : phaseEnvelope ε (shiftedPhase t) = objective ε t := by
    have hcoords (rho : PositiveZetaZero) : (shiftedPhase t rho).re = -Real.sin (ordinate rho*t) ∧ (shiftedPhase t rho).im = Real.cos (ordinate rho*t) := by
      change (Complex.I*Complex.exp ((ordinate rho*t : ℝ)*Complex.I)).re = _ ∧ (Complex.I*Complex.exp ((ordinate rho*t : ℝ)*Complex.I)).im = _
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, and_self]
    have hsa := actual_zeta_phase_stiffness.1
    have ha (rho : PositiveZetaZero) : 0 ≤ weight rho := by
      have hγ := rho.property.2
      unfold weight phaseWeight ordinate D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness.multiplicity
      positivity
    have hsCos : Summable (fun rho => weight rho*Real.cos (ordinate rho*t)) := by
      apply Summable.of_norm_bounded hsa
      intro rho; rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha rho)]; simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (ha rho)
    have hcost : cost t = 2*(∑' rho, weight rho)- 2*(∑' rho, weight rho*(shiftedPhase t rho).im) := by
      have him : (fun rho => weight rho*(shiftedPhase t rho).im) = fun rho => weight rho*Real.cos (ordinate rho*t) := by
        funext rho; rw [(hcoords rho).2]
      rw [him]
      unfold cost phaseCost
      have hid : (fun rho => 2*weight rho*(1-Real.cos (ordinate rho*t))) = fun rho => 2*(weight rho-weight rho*Real.cos (ordinate rho*t)) := by
        funext rho; ring
      rw [hid, tsum_mul_left, hsa.tsum_sub hsCos]; ring
    have hF : (∑' rho, weight rho*((1/denominator rho-2)*(shiftedPhase t rho).im+ 2*ordinate rho/denominator rho*(shiftedPhase t rho).re)) = firstDriving t := by
      apply tsum_congr
      intro rho; rw [(hcoords rho).1, (hcoords rho).2]; ring
    have hG : (∑' rho, weight rho*((8*(ordinate rho)^2/(denominator rho)^2)*(shiftedPhase t rho).im+ (-2/ordinate rho+8*ordinate rho/denominator rho-
        4*ordinate rho/(denominator rho)^2)*(shiftedPhase t rho).re)) = secondDriving t := by
      apply tsum_congr
      intro rho; rw [(hcoords rho).1, (hcoords rho).2]; ring
    unfold phaseEnvelope objective
    rw [hF, hG, hcost]
  have rh_identification (hRH : RiemannHypothesis) : Function.Injective ordinate ∧ (∀ rho : PositiveZetaZero, denominator rho = Complex.normSq rho.val) := by
    have hline (rho : PositiveZetaZero) : rho.val.re = 1/2 := Zeta23.RH_implies_on_line hRH rho.property.1
    constructor
    · intro rho tau hsame
      apply Subtype.ext
      apply Complex.ext
      · exact (hline rho).trans (hline tau).symm
      · exact hsame
    · intro rho
      rw [Complex.normSq_apply, hline]
      unfold denominator ordinate
      ring
  classical
  refine ⟨phase_in_hull, phase_identification, rh_identification, ?_⟩
  obtain ⟨hsa, hsag, hcost, _, L₀, B₀, hL₀, hB₀, hphase⟩ := actual_zeta_phase_stiffness
  have hγ (rho : PositiveZetaZero) : 0 < ordinate rho := rho.property.2
  have ha (rho : PositiveZetaZero) : 0 ≤ weight rho := by
    have hγrho := hγ rho
    unfold weight phaseWeight D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness.multiplicity
    positivity
  obtain ⟨hsk, hK⟩ := actual_driving_positive
  change 0 < drivingK at hK; have hcoeff (rho : PositiveZetaZero) := coefficient_bounds (hγ rho); let D := denominator; let M₀ := ∑' rho, weight rho; let M₁ := ∑' rho, weight rho*ordinate rho
  let R := fun t => ∑' rho, weight rho*(Real.cos (ordinate rho*t)/D rho-
    2*ordinate rho/D rho*Real.sin (ordinate rho*t))
  let R₁ := fun t => ∑' rho, weight rho*(-ordinate rho/D rho*Real.sin (ordinate rho*t)-
    2*(ordinate rho)^2/D rho*Real.cos (ordinate rho*t))
  let r := fun t => R t-2*M₀; let gcoef := fun rho => 8*(ordinate rho)^2/(D rho)^2; let hcoef := fun rho => -2/ordinate rho+8*ordinate rho/D rho-
    4*ordinate rho/(D rho)^2
  let G₁ := fun t => ∑' rho, weight rho*(-gcoef rho*ordinate rho*Real.sin (ordinate rho*t)-
    hcoef rho*ordinate rho*Real.cos (ordinate rho*t))
  obtain ⟨hsR, hR, _⟩ := remainder_regularity ordinate weight hγ ha hsa hsag
  have hr : ∀ t, HasDerivAt r (R₁ t) t := fun t => (hR t).sub_const (2*M₀)
  have hdecomp (t : ℝ) : firstDriving t = cost t+r t := by
    have h := same_source_decomposition ordinate weight ha hsa t (hsR t); change firstDriving t = cost t+R t-2*M₀ at h; dsimp only [r]; linarith
  obtain ⟨hG, _, hGbound⟩ := smooth_driving ordinate weight gcoef hcoef hγ ha hsa hsag (fun rho => (hcoeff rho).2.2.2.2.2.1) (fun rho => (hcoeff rho).2.2.2.2.2.2)
  obtain ⟨_, hrate⟩ := remainder_rate ordinate weight hγ ha hsa hsag
  have hv0 : slope 0 = 0 := by simp [D5.S3.Weil.ZeroData.ZetaOrdinatePhaseStiffness.slope, phaseSlope]
  have hcost0 : cost 0 = 0 := by simp [cost, phaseCost]
  have hr0 : r 0 = firstDriving 0 := by simpa only [hcost0, zero_add] using (hdecomp 0).symm
  have hG0 : secondDriving 0 = 8*quadraticA := by
    unfold secondDriving quadraticA
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_one, sub_zero]
    have hid : (fun rho => weight rho*(8*(ordinate rho)^2/(denominator rho)^2)) = fun rho => 8*(weight rho*(ordinate rho)^2/(denominator rho)^2) := by
      funext rho
      ring
    rw [hid, tsum_mul_left]
  let c : ℝ := 1/(2*Real.pi); let d := 2*drivingK; let σ := 1/L₀; let B := max B₀ (max (drivingK+2*M₁) (8*M₁+14*M₀))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hd : 0 < d := by dsimp only [d]; positivity
  have hL₀0 : 0 < L₀ := by linarith
  have hσ : 0 < σ := by dsimp only [σ]; positivity
  have hB₀B : B₀ ≤ B := le_max_left _ _; have hB : 0 ≤ B := hB₀.trans hB₀B; have hRB : drivingK+2*M₁ ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hGB : 8*M₁+14*M₀ ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hcut (t : ℝ) (ht : |t| ≤ σ) : L₀*|t| ≤ 1 := by
    have h := (le_div_iff₀ hL₀0).mp ht; nlinarith
  have hphase' (t : ℝ) (ht : 0 < |t|) (htσ : |t| ≤ σ) : |cost t-(c/2)*t^2*(Real.log (|t|⁻¹))^2| ≤ B*t^2*(Real.log (|t|⁻¹)+1) := by
    have h := (hphase t ht (hcut t htσ)).1
    have heq : c/2 = 1/(4*Real.pi) := by dsimp only [c]; ring
    rw [heq]
    have hlog : 0 ≤ Real.log (|t|⁻¹)+1 := by
      have ht1 : |t| ≤ 1 := htσ.trans (by dsimp only [σ]; exact (div_le_one hL₀0).mpr (by linarith)); have hlog0 := Real.log_nonneg ((one_le_inv₀ ht).mpr ht1); linarith
    calc
      _ ≤ t^2*B₀*(Real.log (|t|⁻¹)+1) := h
      _ ≤ B*t^2*(Real.log (|t|⁻¹)+1) := by
        have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB₀B (sq_nonneg t)) hlog; nlinarith
  have hslope' (t : ℝ) (ht : 0 < |t|) (htσ : |t| ≤ σ) : |slope t-c*t*(Real.log (|t|⁻¹))^2| ≤ B*|t| *(Real.log (|t|⁻¹)+1) := by
    have h := (hphase t ht (hcut t htσ)).2; have ht1 : |t| ≤ 1 := htσ.trans (by dsimp only [σ]; exact (div_le_one hL₀0).mpr (by linarith)); have hlog0 := Real.log_nonneg ((one_le_inv₀ ht).mpr ht1)
    calc
      _ ≤ |t| *B₀*(Real.log (|t|⁻¹)+1) := h
      _ ≤ B*|t| *(Real.log (|t|⁻¹)+1) := by
        have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB₀B (abs_nonneg t)) (by linarith : 0 ≤ Real.log (|t|⁻¹)+1); nlinarith
  have hrbound (t : ℝ) (_ : |t| ≤ σ) : |R₁ t+d| ≤ B*|t| := by
    have h := hrate t; change |R₁ t+d| ≤ |t| *(drivingK+2*M₁) at h
    calc
      _ ≤ |t| *(drivingK+2*M₁) := h
      _ ≤ B*|t| := by nlinarith [mul_le_mul_of_nonneg_left hRB (abs_nonneg t)]
  have hgbound (t : ℝ) (_ : |t| ≤ σ) : |G₁ t| ≤ B := (hGbound t).trans hGB
  have hJ (ε : ℝ) : objective ε = fun t => (1+ε)*cost t+ε*r t+ε^2*secondDriving t := by
    funext t
    unfold objective
    rw [hdecomp]; ring
  have hC : d/c = 4*Real.pi*drivingK := by dsimp only [d,c]; field_simp; ring
  have hD : d^2/(2*c) = 4*Real.pi*drivingK^2 := by dsimp only [d,c]; field_simp; ring
  obtain ⟨a, ε₀, Q, ha', _, hε₀, hεexp, hQ, hall⟩ := functional_optimizer cost slope r R₁ secondDriving G₁ hσ hc hd hB hv0 hcost hr hG hphase' hslope' hrbound hgbound
  refine ⟨hK, a, ε₀, Q, ha', hε₀, hεexp, hQ, ?_⟩
  intro ε hε hεsmall
  obtain ⟨hexists, hmin⟩ := hall ε hε hεsmall
  simp only [hJ]
  refine ⟨hexists, ?_⟩
  intro t ht hminimum
  obtain ⟨htpos, htlt, hstation, hlog, hdisplacement, hvalue⟩ := hmin t ht hminimum
  have hderiv : HasDerivAt (objective ε) 0 t := by
    rw [hJ]; have h := (((hcost t).const_mul (1+ε)).add ((hr t).const_mul ε)).add ((hG t).const_mul (ε^2)); change HasDerivAt (fun y => (1+ε)*cost y+ε*r y+ε^2*secondDriving y) ((1+ε)*slope t+ε*R₁ t+ε^2*G₁ t) t at h
    rw [hstation] at h; exact h
  refine ⟨htpos, htlt, by simpa only [hJ] using hderiv, ?_⟩
  dsimp only at hlog hdisplacement hvalue ⊢; rw [hC] at hlog hdisplacement; rw [hD, hr0, hG0] at hvalue
  exact ⟨hlog, hdisplacement, by simpa only [mul_assoc, mul_comm, mul_left_comm] using hvalue⟩
end D5.S3.Weil.ZeroData.ZetaOrdinateCompleteOptimizer
