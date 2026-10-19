/- GID: D5/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/OriginalIncreasingFunctionJets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All finite monotone jets admit one smooth positive-derivative realization. -/

/- admission_basis: open-problem-resolution
   preregistration: issue12872; arXiv:2512.02151v1, Conjecture 1.2
   proof_shape: content
   utility: none; analytic existence and openness, with no bounded computation. -/

import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open Set Filter MeasureTheory Function Polynomial
open scoped Topology ContDiff BigOperators

namespace PnOriginal
def unitInterval : Set ℝ := Icc 0 1

def primitive (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ s in 0..x, g s

def repeatedIntegral (k : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := primitive^[k] g

def jet (j : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := iteratedDerivWithin j f unitInterval

def W (n : ℕ) : Set (Fin (n+1) → ℝ) := {b | ∃ f : ℝ → ℝ, ContDiffOn ℝ n f unitInterval ∧
    MonotoneOn (jet n f) unitInterval ∧
    (∃ x ∈ unitInterval, ∃ y ∈ unitInterval, jet n f x ≠ jet n f y) ∧
    ∀ j : Fin (n+1), jet j.val f 0 = 0 ∧ jet j.val f 1 = b j}

def P (n : ℕ) : Prop := IsOpen (W n) ∧ ∀ b ∈ W n, ∃ f : ℝ → ℝ, ContDiffOn ℝ ∞ f unitInterval ∧
    (∀ j : Fin (n+1), jet j.val f 0 = 0 ∧ jet j.val f 1 = b j) ∧
    (∀ x ∈ Ioo (0:ℝ) 1, 0 < jet (n+1) f x) ∧
    jet (n+1) f 0 = 1 ∧ jet (n+1) f 1 = 1 ∧
    (∀ j : ℕ, n+1 < j → jet j f 0 = 0 ∧ jet j f 1 = 0)

def clamp (x : ℝ) : ℝ := max 0 (min 1 x)

def extend (g : ℝ → ℝ) : ℝ → ℝ := g ∘ clamp

end PnOriginal

namespace PnActualMixtureConsumer
abbrev Vec (n : ℕ) := Fin (n + 1) → ℝ
abbrev Center := Icc (0 : ℝ) 1
abbrev Width := Ioi (0 : ℝ)
abbrev Param := Center × Width

def gamma (n : ℕ) (t : ℝ) : Vec n := fun k => (1 - t) ^ k.val
noncomputable def raw (xi sigma t : ℝ) : ℝ :=
  expNegInvGlue t * expNegInvGlue (1 - t) * Real.exp (-((t - xi)^2 / sigma^2))
noncomputable def z (xi sigma : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, raw xi sigma t
noncomputable def density (xi sigma t : ℝ) : ℝ := raw xi sigma t / z xi sigma
noncomputable def moment (n : ℕ) (xi sigma : ℝ) : Vec n :=
  ∫ t in Icc (0 : ℝ) 1, density xi sigma t • gamma n t
noncomputable def component (n : ℕ) (q : Param) : Vec n := moment n q.1 q.2
noncomputable def S (n : ℕ) : PointedCone ℝ (Vec n) :=
  PointedCone.hull ℝ (range (fun t : Center => gamma n t))
noncomputable def T (n : ℕ) : PointedCone ℝ (Vec n) := PointedCone.hull ℝ (range (component n))
noncomputable def mixture (c : Param →₀ {a : ℝ // 0 ≤ a}) (t : ℝ) : ℝ :=
  ∑ q ∈ c.support, (c q : ℝ) * density q.1 q.2 t

noncomputable def endpointCut (delta t : ℝ) : ℝ :=
  Real.smoothTransition (2 - 2*t/delta) + Real.smoothTransition (2 - 2*(1-t)/delta)
noncomputable def cutMoment (n : ℕ) (delta : ℝ) : Vec n :=
  ∫ t in Icc (0 : ℝ) 1, endpointCut delta t • gamma n t

noncomputable def rho (delta : ℝ) (c : Param →₀ {a : ℝ // 0 ≤ a}) (t : ℝ) : ℝ :=
  endpointCut delta t + mixture c t

end PnActualMixtureConsumer

open PnActualMixtureConsumer

namespace PnOriginal

theorem result (n : ℕ) : PnOriginal.P n := by
  classical
  -- Atomless Stieltjes moments encode the original weak monotone jets.
  have originalCoordinates (n : ℕ) (b : Fin (n+1) → ℝ) (hb : b ∈ W n) : ∃ G : StieltjesFunction ℝ,
        IsFiniteMeasure G.measure ∧ G.measure ≠ 0 ∧
        (∀ x : ℝ, G.measure {x} = 0) ∧ G.measure (Icc (0:ℝ) 1)ᶜ = 0 ∧
        (∀ k : Fin (n+1), (k.val.factorial : ℝ) * b ⟨n-k.val, by omega⟩ =
          ∫ t in Icc (0:ℝ) 1, (1-t)^k.val ∂G.measure) := by
    rcases hb with ⟨f,hf,hm,hn,hjets⟩
    let g := jet n f
    change MonotoneOn g unitInterval at hm
    have hud : UniqueDiffOn ℝ unitInterval := uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)
    have hcj (j : ℕ) (hj : j ≤ n) : ContinuousOn (jet j f) unitInterval :=
      hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hj) hud
    have hzj (j : ℕ) (hj : j ≤ n) : jet j f 0 = 0 := (hjets ⟨j, by omega⟩).1
    have hc : ContinuousOn g unitInterval := hcj n le_rfl
    have h0 : g 0 = 0 := hzj n le_rfl
    have hclamp : ∀ x, clamp x ∈ unitInterval := by
      intro x
      simp only [unitInterval, mem_Icc, clamp]
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    have hec : Continuous (extend g) := hc.comp_continuous (by unfold clamp; fun_prop) hclamp
    have hem : Monotone (extend g) := by
      intro x y hxy
      apply hm (hclamp x) (hclamp y)
      exact max_le_max le_rfl (min_le_min le_rfl hxy)
    let G : StieltjesFunction ℝ := ⟨extend g, hem, fun x => hec.continuousAt.continuousWithinAt⟩
    have heq (x : ℝ) (hx : x ∈ unitInterval) : G x = g x := by
      change g (clamp x) = g x
      simp only [unitInterval, mem_Icc] at hx
      simp [clamp, min_eq_right hx.2, max_eq_right hx.1]
    have hl (x : ℝ) (hx : x ≤ 0) : G x = 0 := by
      change g (clamp x) = 0
      rw [show clamp x = 0 by simp [clamp, min_eq_right (hx.trans (show (0:ℝ) ≤ 1 by norm_num)), max_eq_left hx]]
      exact h0
    have hu (x : ℝ) (hx : 1 ≤ x) : G x = g 1 := by
      change g (clamp x) = g 1
      simp [clamp, min_eq_left hx]
    have hatbot : Tendsto G atBot (𝓝 0) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
      exact (hl x hx).symm
    have hattop : Tendsto G atTop (𝓝 (g 1)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
      exact (hu x hx).symm
    have hcont : Continuous G := hec
    have hatom (x : ℝ) : G.measure {x} = 0 := by
      rw [G.measure_singleton, hcont.continuousAt.continuousWithinAt.leftLim_eq]
      simp
    have hmass : G.measure (Icc 0 1) = ENNReal.ofReal (g 1) := by
      rw [G.measure_Icc, hcont.continuousAt.continuousWithinAt.leftLim_eq,
        hu 1 le_rfl, hl 0 le_rfl, sub_zero]
    have hpos : 0 < g 1 := by
      have hb (x : ℝ) (hx : x ∈ unitInterval) : 0 ≤ g x ∧ g x ≤ g 1 := by
        constructor
        · simpa [h0] using hm (by norm_num [unitInterval]) hx hx.1
        · exact hm hx (by norm_num [unitInterval]) hx.2
      have hn0 : 0 ≤ g 1 := (hb 1 (by norm_num [unitInterval])).1
      by_contra hnpos
      have hz : g 1 = 0 := le_antisymm (le_of_not_gt hnpos) hn0
      rcases hn with ⟨x,hx,y,hy,hne⟩
      exact hne ((le_antisymm ((hb x hx).2.trans_eq hz) (hb x hx).1).trans
        (le_antisymm ((hb y hy).2.trans_eq hz) (hb y hy).1).symm)
    have htriangle (k : ℕ) (x : ℝ) (_hx : 0 ≤ x) :
        (∫ s in Icc (0:ℝ) x, ∫ t in Icc (0:ℝ) s, (s-t)^k ∂G.measure) =
          ∫ t in Icc (0:ℝ) x, (x-t)^(k+1)/(k+1) ∂G.measure := by
      let H : ℝ → ℝ → ℝ := fun s t => (Ici t).indicator (fun s => (s-t)^k) s
      have h_int : Integrable (uncurry H)
          ((volume.restrict (Icc (0:ℝ) x)).prod (G.measure.restrict (Icc (0:ℝ) x))) := by
        rw [Measure.prod_restrict]
        have hp : IntegrableOn (fun p : ℝ × ℝ => (p.1-p.2)^k)
            (Icc (0:ℝ) x ×ˢ Icc (0:ℝ) x) (volume.prod G.measure) :=
          (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1-p.2)^k)).continuousOn.integrableOn_compact
            (isCompact_Icc.prod isCompact_Icc)
        change Integrable ({p : ℝ × ℝ | p.2 ≤ p.1}.indicator (fun p => (p.1-p.2)^k)) _
        exact hp.indicator (measurableSet_le measurable_snd measurable_fst)
      have h_left (s : ℝ) (hs : s ∈ Icc (0:ℝ) x) : (∫ t in Icc (0:ℝ) x, H s t ∂G.measure) =
          ∫ t in Icc (0:ℝ) s, (s-t)^k ∂G.measure := by
        have hH : H s = (Iic s).indicator (fun t => (s-t)^k) := by
          funext t
          simp only [H, indicator, mem_Ici, mem_Iic]
        rw [hH, setIntegral_indicator measurableSet_Iic]
        have hi : Icc (0:ℝ) x ∩ Iic s = Icc 0 s := by
          rw [← Ici_inter_Iic, inter_assoc, Iic_inter_Iic, inf_eq_right.mpr hs.2]
          rfl
        rw [hi]
      have h_right (t : ℝ) (ht : t ∈ Icc (0:ℝ) x) :
          (∫ s in Icc (0:ℝ) x, H s t) = (x-t)^(k+1)/(k+1) := by
        rw [show (fun s => H s t) = (Ici t).indicator (fun s => (s-t)^k) by rfl,
          setIntegral_indicator measurableSet_Ici]
        have hi : Icc (0:ℝ) x ∩ Ici t = Icc t x := by
          rw [← Ici_inter_Iic, inter_right_comm, Ici_inter_Ici, sup_eq_right.mpr ht.1]
          rfl
        rw [hi, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.2]
        rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => u^k) t,
          integral_pow]
        simp
      calc
        _ = ∫ s in Icc (0:ℝ) x, ∫ t in Icc (0:ℝ) x, H s t ∂G.measure := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro s hs; exact (h_left s hs).symm
        _ = ∫ t in Icc (0:ℝ) x, (∫ s in Icc (0:ℝ) x, H s t) ∂G.measure := integral_integral_swap h_int
        _ = _ := by
          apply setIntegral_congr_fun measurableSet_Icc
          exact h_right
    have hformula (k : ℕ) : ∀ x ∈ unitInterval,
        repeatedIntegral k g x = (∫ t in Icc (0:ℝ) x, (x-t)^k ∂G.measure) / (k.factorial : ℝ) := by
      induction k with
      | zero =>
        intro x hx
        simp only [repeatedIntegral, Function.iterate_zero_apply, Nat.factorial_zero,
          Nat.cast_one, div_one, pow_zero, setIntegral_const, smul_eq_mul, mul_one]
        change g x = (G.measure (Icc 0 x)).toReal
        rw [G.measure_Icc, hcont.continuousAt.continuousWithinAt.leftLim_eq,
          heq x hx, hl 0 le_rfl, sub_zero, ENNReal.toReal_ofReal]
        simpa [h0] using hm (by norm_num [unitInterval]) hx hx.1
      | succ k ih =>
        intro x hx
        rw [repeatedIntegral, Function.iterate_succ_apply']
        change (∫ s in 0..x, repeatedIntegral k g s) = _
        have hcongr : (∫ s in 0..x, repeatedIntegral k g s) =
            ∫ s in 0..x, (∫ t in Icc (0:ℝ) s, (s-t)^k ∂G.measure) / (k.factorial : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          rw [uIcc_of_le hx.1] at hs
          exact ih s ⟨hs.1, hs.2.trans hx.2⟩
        rw [hcongr, intervalIntegral.integral_div,
          intervalIntegral.integral_of_le hx.1, ← integral_Icc_eq_integral_Ioc,
          htriangle k x hx.1, integral_div, Nat.factorial_succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_div]
    have hall (k : ℕ) : (k.factorial : ℝ) * repeatedIntegral k g 1 =
        ∫ t in Icc (0:ℝ) 1, (1-t)^k ∂G.measure := by
      rw [hformula k 1 (by norm_num [unitInterval])]
      have hfac : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      field_simp
    have hsupp : G.measure (Icc (0:ℝ) 1)ᶜ = 0 := by
      rw [measure_compl measurableSet_Icc (by rw [hmass]; exact ENNReal.ofReal_ne_top),
        G.measure_univ hatbot hattop, hmass, sub_zero, tsub_self]
    have hnonzero : G.measure ≠ 0 := by
      intro hz
      have he : G.measure (Icc (0:ℝ) 1) = 0 := by rw [hz]; simp
      rw [hmass, ENNReal.ofReal_eq_zero] at he
      exact hpos.not_ge he
    have hprimitive (j : ℕ) (hj : j < n) (x : ℝ) (hx : x ∈ unitInterval) :
        primitive (jet (j+1) f) x = jet j f x := by
      have hsub : Icc (0:ℝ) x ⊆ unitInterval := by
        intro s hs; exact ⟨hs.1, hs.2.trans hx.2⟩
      have hder (s : ℝ) (hs : s ∈ Ioo (0:ℝ) x) : HasDerivAt (jet j f) (jet (j+1) f s) s := by
        have hmem : s ∈ unitInterval := ⟨hs.1.le, hs.2.le.trans hx.2⟩
        have hd := hf.differentiableOn_iteratedDerivWithin
          (show (j : WithTop ℕ∞) < n by exact_mod_cast hj) hud s hmem
        simpa only [jet, iteratedDerivWithin_succ] using
          hd.hasDerivWithinAt.hasDerivAt (Icc_mem_nhds hs.1 (hs.2.trans_le hx.2))
      have hci : ContinuousOn (jet (j+1) f) (uIcc 0 x) := by
        rw [uIcc_of_le hx.1]
        exact (hcj (j+1) (by omega)).mono hsub
      change (∫ s in 0..x, jet (j+1) f s) = _
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
        ((hcj j hj.le).mono hsub) hder hci.intervalIntegrable, hzj j hj.le, sub_zero]
    have hrep (k : ℕ) (hk : k ≤ n) : ∀ x ∈ unitInterval,
        repeatedIntegral k (jet n f) x = jet (n-k) f x := by
      induction k with
      | zero => intro x hx; simp [repeatedIntegral]
      | succ k ih =>
        intro x hx
        have hkn : k ≤ n := by omega
        have he : n-k = (n-(k+1))+1 := by omega
        rw [repeatedIntegral, Function.iterate_succ_apply']
        change (∫ s in 0..x, repeatedIntegral k (jet n f) s) = _
        calc
          _ = ∫ s in 0..x, jet (n-k) f s := by
            apply intervalIntegral.integral_congr
            intro s hs
            rw [uIcc_of_le hx.1] at hs
            exact ih hkn s ⟨hs.1, hs.2.trans hx.2⟩
          _ = _ := by rw [he]; exact hprimitive (n-(k+1)) (by omega) x hx
    refine ⟨G,G.isFiniteMeasure hatbot hattop,hnonzero,hatom,hsupp,?_⟩
    intro k
    have hi := hrep k.val (by omega) 1 (by norm_num [unitInterval])
    rw [(hjets ⟨n-k.val, by omega⟩).2] at hi
    rw [← hi]
    exact hall k.val
  -- A nonzero supporting polynomial has only finitely many zeros.
  have originalCone (n : ℕ) (b : Fin (n+1) → ℝ) (hb : b ∈ PnOriginal.W n) :
      (fun k : Fin (n+1) => (k.val.factorial : ℝ) * b ⟨n-k.val, by omega⟩)
        ∈ interior (S n : Set (Vec n)) := by
    have hgamma : Continuous (gamma n) :=
      continuous_pi fun k => (continuous_const.sub continuous_id).pow k.val
    have hfinite (L : Vec n →ₗ[ℝ] ℝ) (hne : L ≠ 0) : Set.Finite {t : ℝ | L (gamma n t) = 0} := by
      let p : ℝ[X] := ∑ i : Fin (n+1), C (L (Pi.single i 1)) * X ^ i.val
      have hv (v : Vec n) : L v = ∑ i : Fin (n+1), L (Pi.single i 1) * v i := by
        have hsum : (∑ i : Fin (n+1), Pi.single i (v i)) = v := by ext; simp
        rw [← hsum, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [show Pi.single i (v i) = (v i) • Pi.single i 1 by
          ext j; by_cases h : j = i <;> simp [h]]
        simp [mul_comm]
      have heval (t : ℝ) : p.eval (1-t) = L (gamma n t) := by
        rw [hv (gamma n t)]
        simp [p, Polynomial.eval_finsetSum, gamma]
      have hcoeff (i : Fin (n+1)) : p.coeff i.val = L (Pi.single i 1) := by
        simp only [p, finsetSum_coeff, coeff_C_mul_X_pow]
        have hh : ∀ j : Fin (n+1), (i.val = j.val) ↔ (i = j) := fun j => Fin.ext_iff.symm
        simp only [hh]
        simp
      have hp : p ≠ 0 := by
        intro hp
        apply hne
        apply LinearMap.ext
        intro v
        change L v = 0
        have hz (i : Fin (n+1)) : L (Pi.single i 1) = 0 := by rw [← hcoeff i, hp]; simp
        rw [hv]
        simp only [hz, zero_mul, Finset.sum_const_zero]
      have hroot := (Polynomial.finite_setOfPred_isRoot hp).preimage
        (f := fun t : ℝ => 1-t) (by intro x _ y _ h; linarith)
      simpa only [Set.preimage_ofPred_eq, Polynomial.IsRoot, heval] using hroot
    have hspan : Submodule.span ℝ (S n : Set (Vec n)) = ⊤ := by
      by_contra h
      obtain ⟨L,hne,hker⟩ := (Submodule.span ℝ (S n : Set (Vec n))).exists_le_ker_of_lt_top
        (lt_top_iff_ne_top.mpr h)
      have hz : Icc (0:ℝ) 1 ⊆ {t : ℝ | L (gamma n t) = 0} := by
        intro t ht
        exact hker (Submodule.subset_span (PointedCone.subset_hull ⟨⟨t,ht⟩,rfl⟩))
      exact (Icc_infinite (by norm_num : (0:ℝ) < 1)) ((hfinite L hne).subset hz)
    have haff : affineSpan ℝ (S n : Set (Vec n)) = ⊤ := by
      apply SetLike.coe_injective
      rw [← Set.insert_eq_of_mem (S n).zero_mem, affineSpan_insert_zero, hspan]
      rfl
    have hint := (S n).convex.interior_nonempty_iff_affineSpan_eq_top.mpr haff
    rcases originalCoordinates n b hb with
      ⟨G,hGfinite,hGne,hGatom,hGsupp,hGcoords⟩
    let : IsFiniteMeasure G.measure := hGfinite
    let : NullSingletonClass G.measure := ⟨hGatom⟩
    let μ := G.measure.restrict (Icc (0:ℝ) 1)
    have hμeq : μ = G.measure :=
      Measure.restrict_eq_self_of_ae_mem (by simpa only [ae_iff, ← Set.compl_def] using hGsupp)
    have hμne : μ ≠ 0 := hμeq ▸ hGne
    let : NeZero μ := ⟨hμne⟩
    let m : Vec n := ∫ t, gamma n t ∂μ
    have hgi : Integrable (gamma n) μ := hgamma.continuousOn.integrableOn_compact isCompact_Icc
    have hmcoords : m = (fun k : Fin (n+1) =>
        (k.val.factorial : ℝ) * b ⟨n-k.val, by omega⟩) := by
      funext k
      rw [show m k = ∫ t, gamma n t k ∂μ by
        exact (eval_integral (fun j => hgi.eval j) k)]
      exact (hGcoords k).symm
    rw [← hmcoords]
    by_contra hm
    obtain ⟨L,hLne,hL⟩ := geometric_hahn_banach_of_nonempty_interior_point (S n).convex hm hint
    have hLnonpos (x : Vec n) (hx : x ∈ S n) : L x ≤ 0 := by
      by_contra! hpos
      have hbound := hL (((L m + 1) / L x) • x)
        ((S n).smul_mem (by
          have hmnonneg := hL 0 (S n).zero_mem
          simp only [map_zero] at hmnonneg
          exact div_nonneg (by linarith) hpos.le) hx)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at hbound
      linarith
    have hLmg : 0 ≤ L m := by simpa using hL 0 (S n).zero_mem
    have hnonneg : 0 ≤ᵐ[μ] fun t => -L (gamma n t) := by
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      exact ae_of_all _ fun t ht => neg_nonneg.mpr
        (hLnonpos _ (PointedCone.subset_hull ⟨⟨t,ht⟩,rfl⟩))
    have hli : Integrable (fun t => -L (gamma n t)) μ := (L.integrable_comp hgi).neg
    have hzeros : ∀ᵐ t ∂μ, L (gamma n t) ≠ 0 := by
      rw [hμeq]
      exact (hfinite L.toLinearMap (by
        intro hz; apply hLne; exact ContinuousLinearMap.coe_injective hz)).countable.ae_notMem G.measure
    have hpos : 0 < ∫ t, -L (gamma n t) ∂μ := by
      apply lt_of_le_of_ne (integral_nonneg_of_ae hnonneg)
      intro hz
      have hzero := (integral_eq_zero_iff_of_nonneg_ae hnonneg hli).mp hz.symm
      have : ∀ᵐ t ∂μ, False := by
        filter_upwards [hzero,hzeros] with t ht hne
        exact hne (neg_eq_zero.mp ht)
      exact this.exists.elim (fun t ht => ht)
    have he : (∫ t, -L (gamma n t) ∂μ) = -L m := by rw [integral_neg, L.integral_comp_comm hgi]
    rw [he] at hpos
    linarith
  -- Remove a small endpoint correction while keeping the residual in the interior.
  have compensatedDensity (n : ℕ) (m : Vec n) (hm : m ∈ interior (S n : Set (Vec n))) :
      ∃ (delta : ℝ) (c : Param →₀ {a : ℝ // 0 ≤ a}),
        ContDiff ℝ ∞ (rho delta c) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, 0 < rho delta c t) ∧
        (rho delta c 0 = 1 ∧ rho delta c 1 = 1) ∧
        (∀ j : ℕ, 0 < j → iteratedDerivWithin j (rho delta c) (Icc (0:ℝ) 1) 0 = 0 ∧
          iteratedDerivWithin j (rho delta c) (Icc (0:ℝ) 1) 1 = 0) ∧
        (∀ k : Fin (n+1), ∫ t in Icc (0 : ℝ) 1, (1-t)^k.val * rho delta c t = m k) := by
    let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
    have hμ : μ univ = 1 := by simp [μ, Real.volume_Icc]
    let : IsProbabilityMeasure μ := ⟨hμ⟩
    have hgamma : Continuous (gamma n) :=
      continuous_pi fun k => (continuous_const.sub continuous_id).pow k.val
    have hcutoff : ∃ delta : ℝ, ContDiff ℝ ∞ (endpointCut delta) ∧
        (∀ t : ℝ, 0 ≤ endpointCut delta t) ∧
        (∀ᶠ t in 𝓝 (0 : ℝ), endpointCut delta t = 1) ∧
        (∀ᶠ t in 𝓝 (1 : ℝ), endpointCut delta t = 1) ∧
        m - cutMoment n delta ∈ interior (S n : Set (Vec n)) := by
      have hcutdiff (delta : ℝ) : ContDiff ℝ ∞ (endpointCut delta) := by
        exact (Real.smoothTransition.contDiff.comp
          (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const delta))).add
          (Real.smoothTransition.contDiff.comp
            (contDiff_const.sub ((contDiff_const.mul (contDiff_const.sub contDiff_id)).div_const delta)))
      have hcutnonneg : ∀ delta t : ℝ, 0 ≤ endpointCut delta t :=
        fun delta t => add_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
      have hcutle (delta t : ℝ) : endpointCut delta t ≤ 2 := by
        have h₁ := Real.smoothTransition.le_one (2 - 2*t/delta)
        have h₂ := Real.smoothTransition.le_one (2 - 2*(1-t)/delta)
        calc
          endpointCut delta t ≤ (1:ℝ)+1 := add_le_add h₁ h₂
          _ = 2 := by norm_num
      have hvanish : ∀ t ∈ Ioo (0:ℝ) 1,
          ∀ᶠ delta in 𝓝[>] (0:ℝ), endpointCut delta t = 0 := by
        intro t ht
        filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds ht.1 : ∀ᶠ delta in 𝓝 (0:ℝ), delta < t).filter_mono nhdsWithin_le_nhds,
          (gt_mem_nhds (sub_pos.mpr ht.2) : ∀ᶠ delta in 𝓝 (0:ℝ), delta < 1-t).filter_mono nhdsWithin_le_nhds] with delta hd hdt hd1
        have harg₁ : 2 - 2*t/delta ≤ 0 := by
          have := (le_div_iff₀ hd).mpr (show 2*delta ≤ 2*t by linarith)
          linarith
        have harg₂ : 2 - 2*(1-t)/delta ≤ 0 := by
          have := (le_div_iff₀ hd).mpr (show 2*delta ≤ 2*(1-t) by linarith)
          linarith
        simp [endpointCut, Real.smoothTransition.zero_of_nonpos harg₁,
          Real.smoothTransition.zero_of_nonpos harg₂]
      have hvlimit : Tendsto (cutMoment n) (𝓝[>] (0:ℝ)) (𝓝 (0 : Vec n)) := by
        have hlim : ∀ᵐ t ∂μ, Tendsto (fun delta => endpointCut delta t • gamma n t)
            (𝓝[>] (0:ℝ)) (𝓝 (0 : Vec n)) := by
          change ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), _
          rw [← restrict_Ioo_eq_restrict_Icc]
          apply (ae_restrict_iff' measurableSet_Ioo).mpr
          exact ae_of_all _ fun t ht => tendsto_const_nhds.congr'
            ((hvanish t ht).mono fun delta h => by simp [h])
        have hgammale : ∀ t ∈ Icc (0:ℝ) 1, ‖gamma n t‖ ≤ 1 := by
          intro t ht
          apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
          intro k
          change ‖(1-t)^k.val‖ ≤ 1
          rw [Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _)]
          exact pow_le_one₀ (sub_nonneg.mpr ht.2) (by linarith [ht.1])
        have hbound (delta : ℝ) : ∀ᵐ t ∂μ, ‖endpointCut delta t • gamma n t‖ ≤ (2:ℝ) := by
          apply (ae_restrict_iff' measurableSet_Icc).mpr
          exact ae_of_all _ fun t ht => by
            rw [norm_smul, Real.norm_of_nonneg (hcutnonneg delta t)]
            exact (mul_le_mul (hcutle delta t) (hgammale t ht) (norm_nonneg _) (by norm_num)).trans_eq (mul_one 2)
        have hv := tendsto_integral_filter_of_dominated_convergence (μ := μ)
          (F := fun delta t => endpointCut delta t • gamma n t) (f := fun _ => (0 : Vec n)) (fun _ => (2:ℝ))
          (Eventually.of_forall fun delta =>
            ((hcutdiff delta).continuous.smul hgamma).aestronglyMeasurable)
          (Eventually.of_forall hbound) (integrable_const 2) hlim
        change Tendsto (fun delta => ∫ t, endpointCut delta t • gamma n t ∂μ) _ _
        simpa only [integral_zero] using hv
      have hrpoint : Tendsto (fun delta => m - cutMoment n delta)
          (𝓝[>] (0:ℝ)) (𝓝 m) := by
        simpa using tendsto_const_nhds.sub hvlimit
      have hrEventually := hrpoint.eventually (isOpen_interior.mem_nhds hm)
      have hpos : ∀ᶠ delta : ℝ in 𝓝[>] (0:ℝ), 0 < delta := self_mem_nhdsWithin
      have hsm : ∀ᶠ delta : ℝ in 𝓝[>] (0:ℝ), delta < 1/2 :=
        (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2)).filter_mono nhdsWithin_le_nhds
      obtain ⟨delta, hd, hsmall, hr⟩ := (hpos.and (hsm.and hrEventually)).exists
      have hl : ∀ t : ℝ, t < delta/2 → endpointCut delta t = 1 := by
        intro t ht
        have harg₁ : 1 ≤ 2 - 2*t/delta := by
          have hdiv : 2*t/delta ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
          linarith
        have harg₂ : 2 - 2*(1-t)/delta ≤ 0 := by
          have := (le_div_iff₀ hd).mpr (show 2*delta ≤ 2*(1-t) by linarith)
          linarith
        simp [endpointCut, Real.smoothTransition.one_of_one_le harg₁,
          Real.smoothTransition.zero_of_nonpos harg₂]
      have hreflect (t : ℝ) : endpointCut delta (1-t) = endpointCut delta t := by
        simp [endpointCut, sub_sub_cancel, add_comm]
      have hrgt (t : ℝ) (ht : 1-delta/2 < t) : endpointCut delta t = 1 := by
        rw [← hreflect]
        exact hl (1-t) (by linarith)
      have hleft : endpointCut delta =ᶠ[𝓝 (0:ℝ)] (fun _ => (1:ℝ)) :=
        (gt_mem_nhds (by linarith : (0:ℝ) < delta/2)).mono (hl ·)
      have hright : endpointCut delta =ᶠ[𝓝 (1:ℝ)] (fun _ => (1:ℝ)) :=
        (lt_mem_nhds (by linarith : 1-delta/2 < (1:ℝ))).mono (hrgt ·)
      exact ⟨delta, hcutdiff delta, hcutnonneg delta, hleft, hright, hr⟩
    have hactual : ∀ (r : Vec n) (hr : r ∈ interior (S n : Set (Vec n))),
      ∃ c : Param →₀ {a : ℝ // 0 ≤ a},
        ContDiff ℝ ∞ (mixture c) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, 0 < mixture c t) ∧
        (mixture c 0 = 0 ∧ mixture c 1 = 0) ∧
        (∀ j : ℕ, iteratedDeriv j (mixture c) 0 = 0 ∧ iteratedDeriv j (mixture c) 1 = 0) ∧
        (∀ k : Fin (n+1), ∫ t in Icc (0 : ℝ) 1,
          (1-t)^k.val * mixture c t = r k) := by
      have hrawdiff (xi sigma : ℝ) : ContDiff ℝ ∞ (raw xi sigma) := ((expNegInvGlue.contDiff.mul
          (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))).mul
          (Real.contDiff_exp.comp
            (((contDiff_id.sub contDiff_const).pow 2).div_const (sigma^2)).neg))
      have hraw (xi sigma : ℝ) : Continuous (raw xi sigma) := (hrawdiff xi sigma).continuous
      have hpdiff (xi sigma : ℝ) : ContDiff ℝ ∞ (density xi sigma) :=
        (hrawdiff xi sigma).div_const _
      have hrawnonneg (xi sigma t : ℝ) : 0 ≤ raw xi sigma t := by
        exact mul_nonneg (mul_nonneg (expNegInvGlue.nonneg t) (expNegInvGlue.nonneg (1-t)))
          (Real.exp_pos _).le
      have hrawpos : ∀ xi sigma t : ℝ, t ∈ Ioo (0 : ℝ) 1 → 0 < raw xi sigma t := by
        intro xi sigma t ht
        exact mul_pos (mul_pos (expNegInvGlue.pos_of_pos ht.1)
          (expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2))) (Real.exp_pos _)
      have hz (xi sigma : ℝ) : 0 < z xi sigma := by
        apply intervalIntegral.integral_pos (by norm_num) (hraw xi sigma).continuousOn
          (fun t _ => hrawnonneg xi sigma t)
        exact ⟨1/2, by constructor <;> norm_num, hrawpos xi sigma (1/2) (by constructor <;> norm_num)⟩
      have hpcontinuous (xi sigma : ℝ) : Continuous (density xi sigma) := by
        exact (hraw xi sigma).div_const _
      have hpnonneg (xi sigma t : ℝ) : 0 ≤ density xi sigma t := by
        exact div_nonneg (hrawnonneg xi sigma t) (hz xi sigma).le
      have hpone (xi sigma : ℝ) : ∫ t in Icc (0 : ℝ) 1, density xi sigma t = 1 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
        unfold density
        rw [intervalIntegral.integral_div]
        exact div_self (hz xi sigma).ne'
      have hlimit : ∀ xi : Center,
          Tendsto (fun sigma : ℝ => moment n xi sigma) (𝓝[>] (0 : ℝ)) (𝓝 (gamma n xi)) := by
        intro xi
        let w : ℝ → ℝ := fun t => expNegInvGlue t * expNegInvGlue (1-t)
        have hwcont : Continuous w := (expNegInvGlue.contDiff (n := ⊤)).continuous.mul
            ((expNegInvGlue.contDiff (n := ⊤)).continuous.comp (continuous_const.sub continuous_id))
        have hwnonneg : ∀ t, 0 ≤ w t := fun t =>
          mul_nonneg (expNegInvGlue.nonneg t) (expNegInvGlue.nonneg (1-t))
        have hwpos : ∀ t ∈ Ioo (0:ℝ) 1, 0 < w t := fun t ht =>
          mul_pos (expNegInvGlue.pos_of_pos ht.1)
            (expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2))
        have hwle : ∀ t, w t ≤ 1 := by
          have hE (t : ℝ) : expNegInvGlue t ≤ 1 := by
            by_cases ht : t ≤ 0
            · simp [expNegInvGlue.zero_of_nonpos ht]
            · rw [expNegInvGlue, if_neg ht]
              exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge ht)))
          intro t
          exact (mul_le_mul (hE t) (hE (1-t)) (expNegInvGlue.nonneg (1-t)) zero_le_one).trans_eq (one_mul 1)
        have hwint : IntegrableOn w (Icc (0:ℝ) 1) := hwcont.continuousOn.integrableOn_Icc
        have hzset : ∀ sigma, z xi sigma = ∫ t in Icc (0:ℝ) 1, raw xi sigma t := by
          intro sigma
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
          rfl
        have hpeak : ∀ u : Set ℝ, IsOpen u → (xi:ℝ) ∈ u →
            TendstoUniformlyOn (fun sigma t => density xi sigma t) 0 (𝓝[>] (0:ℝ)) (Icc (0:ℝ) 1 \ u) := by
          intro u hu hxi
          obtain ⟨d, hd, hdu⟩ := Metric.isOpen_iff.mp hu (xi:ℝ) hxi
          let v : Set ℝ := Metric.ball (xi:ℝ) (d/2) ∩ Ioo (0:ℝ) 1
          have hvopen : IsOpen v := Metric.isOpen_ball.inter isOpen_Ioo
          have hvsub : v ⊆ Icc (0:ℝ) 1 := fun t ht => ⟨ht.2.1.le, ht.2.2.le⟩
          have hxicl : (xi:ℝ) ∈ closure (Ioo (0:ℝ) 1) := by
            simpa only [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] using xi.property
          have hvne : v.Nonempty :=
            mem_closure_iff.mp hxicl (Metric.ball (xi:ℝ) (d/2)) Metric.isOpen_ball
              (Metric.mem_ball_self (by linarith))
          let A : ℝ := ∫ t in v, w t
          have hA : 0 < A := by
            apply (setIntegral_pos_iff_support_of_nonneg_ae
              (ae_of_all _ hwnonneg) (hwint.mono_set hvsub)).mpr
            exact (hvopen.measure_pos volume hvne).trans_le
              (measure_mono (fun t ht => ⟨(hwpos t ht.2).ne', ht⟩))
          have hlow : ∀ sigma : ℝ,
              Real.exp (-(d^2/4/sigma^2)) * A ≤ z xi sigma := by
            intro sigma
            have hrint : IntegrableOn (raw xi sigma) (Icc (0:ℝ) 1) :=
              (hraw xi sigma).continuousOn.integrableOn_Icc
            calc
              Real.exp (-(d^2/4/sigma^2)) * A = ∫ t in v, Real.exp (-(d^2/4/sigma^2)) * w t := by
                rw [integral_const_mul]
              _ ≤ ∫ t in v, raw xi sigma t := by
                apply setIntegral_mono_on ((hwint.mono_set hvsub).const_mul _)
                  (hrint.mono_set hvsub) hvopen.measurableSet
                intro t ht
                change _ ≤ w t * Real.exp (-((t-(xi:ℝ))^2 / sigma^2))
                rw [mul_comm]
                apply mul_le_mul_of_nonneg_left _ (hwnonneg t)
                apply Real.exp_le_exp.mpr
                apply neg_le_neg
                apply div_le_div_of_nonneg_right _ (sq_nonneg sigma)
                have hdist : |t-(xi:ℝ)| < d/2 := by
                  simpa only [Metric.mem_ball, Real.dist_eq] using ht.1
                have hs := (sq_le_sq).mpr (show |t-(xi:ℝ)| ≤ |d/2| by simpa [abs_of_pos (by linarith : 0 < d/2)] using hdist.le)
                nlinarith
              _ ≤ ∫ t in Icc (0:ℝ) 1, raw xi sigma t :=
                setIntegral_mono_set hrint (ae_of_all _ (hrawnonneg xi sigma)) (ae_of_all _ hvsub)
              _ = z xi sigma := (hzset sigma).symm
          have hbound : ∀ sigma t : ℝ, t ∈ Icc (0:ℝ) 1 \ u →
              density xi sigma t ≤ Real.exp (-(3*d^2/4)/sigma^2) / A := by
            intro sigma t ht
            have hdist : d ≤ |t-(xi:ℝ)| := by
              by_contra h
              exact ht.2 (hdu (by simpa only [Metric.mem_ball, Real.dist_eq] using lt_of_not_ge h))
            have hs : d^2 ≤ (t-(xi:ℝ))^2 := by
              have := (sq_le_sq).mpr (show |d| ≤ |t-(xi:ℝ)| by simpa [abs_of_pos hd] using hdist)
              exact this
            have hrupper : raw xi sigma t ≤ Real.exp (-(d^2/sigma^2)) := by
              change w t * _ ≤ _
              calc
                w t * Real.exp (-((t-(xi:ℝ))^2/sigma^2)) ≤
                    Real.exp (-((t-(xi:ℝ))^2/sigma^2)) :=
                  mul_le_of_le_one_left (Real.exp_pos _).le (hwle t)
                _ ≤ Real.exp (-(d^2/sigma^2)) :=
                  Real.exp_le_exp.mpr (neg_le_neg (div_le_div_of_nonneg_right hs (sq_nonneg sigma)))
            calc
              density xi sigma t ≤ Real.exp (-(d^2/sigma^2)) /
                  (Real.exp (-(d^2/4/sigma^2)) * A) := by
                exact div_le_div₀ (Real.exp_pos _).le hrupper
                  (mul_pos (Real.exp_pos _) hA) (hlow sigma)
              _ = Real.exp (-(3*d^2/4)/sigma^2) / A := by
                rw [div_mul_eq_div_div, ← Real.exp_sub]
                congr 2
                ring
          have hdecay : Tendsto (fun sigma : ℝ => Real.exp (-(3*d^2/4)/sigma^2) / A)
              (𝓝[>] (0:ℝ)) (𝓝 0) := by
            have hi : Tendsto (fun sigma : ℝ => (sigma^2)⁻¹) (𝓝[>] (0:ℝ)) atTop := by
              convert (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).comp
                (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)) using 1
              simp [Function.comp_def, inv_pow]
            have he : Tendsto (fun sigma : ℝ => Real.exp (-(3*d^2/4)/sigma^2))
                (𝓝[>] (0:ℝ)) (𝓝 0) := by
              apply Real.tendsto_exp_atBot.comp
              simpa only [div_eq_mul_inv] using
                (tendsto_const_mul_atBot_of_neg (by nlinarith : -(3*d^2/4) < 0)).mpr hi
            simpa only [zero_div] using he.div_const A
          apply Metric.tendstoUniformlyOn_iff.mpr
          intro eps heps
          filter_upwards [(tendsto_order.mp hdecay).2 eps heps] with sigma hsigma t ht
          simp only [Pi.zero_apply, dist_zero_left, Real.norm_of_nonneg (hpnonneg xi sigma t)]
          exact (hbound sigma t ht).trans_lt hsigma
        apply tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto measurableSet_Icc
          measurableSet_Icc (Subset.rfl) self_mem_nhdsWithin
          (by simp [Real.volume_Icc])
          (Eventually.of_forall (fun sigma t _ => hpnonneg xi sigma t)) hpeak
        · exact tendsto_const_nhds.congr (fun sigma => (hpone xi sigma).symm)
        · exact Eventually.of_forall (fun sigma => (hpcontinuous xi sigma).aestronglyMeasurable)
        · exact hgamma.continuousOn.integrableOn_Icc
        · exact hgamma.continuousAt.continuousWithinAt
      intro r hr
      have hmomentintegrable : ∀ q : Param,
          Integrable (fun t => density q.1 q.2 t • gamma n t) μ := by
        intro q
        exact ((hpcontinuous q.1 q.2).smul hgamma).continuousOn.integrableOn_Icc
      have heval (xi : Center) : gamma n xi ∈ (T n).topologicalClosure := by
        change gamma n xi ∈ closure (T n : Set (Vec n))
        apply mem_closure_of_tendsto (hlimit xi)
        filter_upwards [self_mem_nhdsWithin] with sigma hsigma
        exact PointedCone.subset_hull ⟨(xi, ⟨sigma, hsigma⟩), rfl⟩
      have hSleClosure : S n ≤ (T n).topologicalClosure := by
        apply Submodule.span_le.mpr
        rintro _ ⟨xi, rfl⟩
        exact heval xi
      -- The residual interior forces the mixture cone to have full affine span.
      have hSspanT : (S n : Set (Vec n)) ⊆ affineSpan ℝ (T n : Set (Vec n)) :=
        Subset.trans hSleClosure (closure_minimal (subset_affineSpan _ _)
          (affineSpan ℝ _).closed_of_finiteDimensional)
      have hspanT : affineSpan ℝ (T n : Set (Vec n)) = ⊤ := by
        apply top_unique
        rw [← isOpen_interior.affineSpan_eq_top ⟨r, hr⟩]
        exact affineSpan_le.mpr (Subset.trans interior_subset hSspanT)
      have hTint : (interior (T n : Set (Vec n))).Nonempty :=
        (T n).convex.interior_nonempty_iff_affineSpan_eq_top.mpr hspanT
      have hrT : r ∈ T n := by
        apply interior_subset
        rw [← (T n).convex.interior_closure_eq_interior_of_nonempty_interior hTint]
        exact interior_mono hSleClosure hr
      obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hrT
      have hSnonneg : ∀ x ∈ S n, 0 ≤ x (0 : Fin (n+1)) := by
        intro x hx
        apply Submodule.span_induction (p := fun x _ => 0 ≤ x (0 : Fin (n+1))) ?_ ?_ ?_ ?_ hx
        · rintro _ ⟨t, rfl⟩
          simp [gamma]
        · simp
        · intro x y _ _ hx hy
          exact add_nonneg hx hy
        · intro a x _ hx
          exact mul_nonneg a.property hx
      have hrmass : 0 < r (0 : Fin (n+1)) := by
        have hsub : (S n : Set (Vec n)) ⊆
            (fun v : Vec n => v (0 : Fin (n+1))) ⁻¹' Ici (0:ℝ) := hSnonneg
        have hi := interior_mono hsub hr
        have hi' := (isOpenMap_eval (X := fun _ : Fin (n+1) => ℝ) 0)
          |>.interior_preimage_subset_preimage_interior hi
        simpa only [interior_Ici, mem_preimage, mem_Ioi] using hi'
      have hrne : r ≠ 0 := by
        intro hz
        simpa [hz] using hrmass
      have hcne : c ≠ 0 := by
        intro hzero
        apply hrne
        simpa [hzero] using hc.symm
      obtain ⟨q₀, hq₀⟩ := Finsupp.support_nonempty_iff.mpr hcne
      have hcpos : 0 < (c q₀ : ℝ) := by
        have hne := Finsupp.mem_support_iff.mp hq₀
        apply lt_of_le_of_ne (c q₀).property
        intro hzero
        exact hne (Subtype.ext hzero.symm)
      have hmixint : (∫ t, mixture c t • gamma n t ∂μ) = r := by
        calc
          (∫ t, mixture c t • gamma n t ∂μ) =
              ∫ t, ∑ q ∈ c.support, (c q : ℝ) • (density q.1 q.2 t • gamma n t) ∂μ := by
            apply integral_congr_ae
            exact ae_of_all _ fun t => by simp [mixture, Finset.sum_smul, mul_smul]
          _ = ∑ q ∈ c.support, (c q : ℝ) • component n q := by
            rw [integral_finsetSum]
            · simp only [integral_smul]
              rfl
            · intro q _
              convert (hmomentintegrable q).smul (c q : ℝ) using 1
          _ = r := hc
      have hmixdiff : ContDiff ℝ ∞ (mixture c) :=
        ContDiff.sum fun q _ => contDiff_const.mul (hpdiff q.1 q.2)
      refine ⟨c, hmixdiff, ?_, ?_, ?_, ?_⟩
      · intro t ht
        unfold mixture
        apply Finset.sum_pos'
        · intro q _
          exact mul_nonneg (c q).property (hpnonneg q.1 q.2 t)
        · exact ⟨q₀, hq₀, mul_pos hcpos (div_pos (hrawpos q₀.1 q₀.2 t ht) (hz q₀.1 q₀.2))⟩
      · constructor <;> simp [mixture, density, raw, expNegInvGlue.zero]
      · intro j
        have hleft : EqOn (mixture c) (fun _ => (0 : ℝ)) (Iio (0 : ℝ)) := by
          intro t ht
          change t < 0 at ht
          simp [mixture, density, raw, expNegInvGlue.zero_of_nonpos (le_of_lt ht)]
        have hright : EqOn (mixture c) (fun _ => (0 : ℝ)) (Ioi (1 : ℝ)) := by
          intro t ht
          change 1 < t at ht
          simp [mixture, density, raw, expNegInvGlue.zero_of_nonpos (by linarith : 1-t ≤ 0)]
        have hcont := hmixdiff.continuous_iteratedDeriv j
          (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
        have hdl : EqOn (iteratedDeriv j (mixture c)) (fun _ => (0 : ℝ)) (Iio (0 : ℝ)) := by
          intro t ht
          simpa only [iteratedDeriv_fun_const_zero] using
            (hleft.iteratedDeriv_of_isOpen isOpen_Iio j) ht
        have hdr : EqOn (iteratedDeriv j (mixture c)) (fun _ => (0 : ℝ)) (Ioi (1 : ℝ)) := by
          intro t ht
          simpa only [iteratedDeriv_fun_const_zero] using
            (hright.iteratedDeriv_of_isOpen isOpen_Ioi j) ht
        constructor
        · exact hdl.closure hcont continuous_const (by simp)
        · exact hdr.closure hcont continuous_const (by simp)
      · intro k
        have hmi : Integrable (fun t => mixture c t • gamma n t) μ := by
          have hcont : Continuous (mixture c) := hmixdiff.continuous
          exact (hcont.smul hgamma).continuousOn.integrableOn_Icc
        have heval := congrFun hmixint k
        rw [eval_integral (fun j => hmi.eval j) k] at heval
        simpa [μ, gamma, mul_comm] using heval
    obtain ⟨delta, hcutdiff, hcutnonneg, hleft, hright, hr⟩ := hcutoff
    obtain ⟨c, hmixdiff, hmixpos, hmixends, hmixjets, hmixmom⟩ := hactual (m - cutMoment n delta) hr
    have hrhodiff : ContDiff ℝ ∞ (rho delta c) := hcutdiff.add hmixdiff
    have hcutint : Integrable (fun t => endpointCut delta t • gamma n t) μ :=
      (hcutdiff.continuous.smul hgamma).continuousOn.integrableOn_Icc
    have hcutcoord (k : Fin (n+1)) : cutMoment n delta k =
        ∫ t in Icc (0:ℝ) 1, (1-t)^k.val * endpointCut delta t := by
      have heval := eval_integral (fun j => hcutint.eval j) k
      simpa [cutMoment, μ, gamma, mul_comm] using heval
    have hrhojets : ∀ j : ℕ, 0 < j → iteratedDeriv j (rho delta c) 0 = 0 ∧
        iteratedDeriv j (rho delta c) 1 = 0 := by
      intro j hj
      have heql : rho delta c =ᶠ[𝓝 (0:ℝ)] (fun t => (1:ℝ) + mixture c t) :=
        hleft.mono fun t ht => by simp only [rho, ht]
      have heqr : rho delta c =ᶠ[𝓝 (1:ℝ)] (fun t => (1:ℝ) + mixture c t) :=
        hright.mono fun t ht => by simp only [rho, ht]
      constructor
      · rw [heql.iteratedDeriv_eq j, iteratedDeriv_const_add hj, (hmixjets j).1]
      · rw [heqr.iteratedDeriv_eq j, iteratedDeriv_const_add hj, (hmixjets j).2]
    refine ⟨delta, c, hrhodiff, ?_, ?_, ?_, ?_⟩
    · intro t ht
      exact add_pos_of_nonneg_of_pos (hcutnonneg t) (hmixpos t ht)
    · constructor
      · simp only [rho, (show endpointCut delta =ᶠ[𝓝 (0:ℝ)] (fun _ => (1:ℝ)) from hleft).eq_of_nhds, hmixends.1, add_zero]
      · simp only [rho, (show endpointCut delta =ᶠ[𝓝 (1:ℝ)] (fun _ => (1:ℝ)) from hright).eq_of_nhds, hmixends.2, add_zero]
    · intro j hj
      have hjdiff : ContDiff ℝ j (rho delta c) := hrhodiff.of_le
        (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))
      constructor
      · rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
          hjdiff.contDiffAt (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1), (hrhojets j hj).1]
      · rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one
          hjdiff.contDiffAt (by norm_num : (1:ℝ) ∈ Icc (0:ℝ) 1), (hrhojets j hj).2]
    · intro k
      have hci : IntegrableOn (fun t => (1-t)^k.val * endpointCut delta t) (Icc (0:ℝ) 1) :=
        (((continuous_const.sub continuous_id).pow k.val).mul hcutdiff.continuous).continuousOn.integrableOn_Icc
      have hmi : IntegrableOn (fun t => (1-t)^k.val * mixture c t) (Icc (0:ℝ) 1) :=
        (((continuous_const.sub continuous_id).pow k.val).mul hmixdiff.continuous).continuousOn.integrableOn_Icc
      calc
        (∫ t in Icc (0:ℝ) 1, (1-t)^k.val * rho delta c t) =
            (∫ t in Icc (0:ℝ) 1, (1-t)^k.val * endpointCut delta t) +
            (∫ t in Icc (0:ℝ) 1, (1-t)^k.val * mixture c t) := by
          simp only [rho, mul_add]
          exact integral_add hci hmi
        _ = cutMoment n delta k + (m - cutMoment n delta) k := by rw [← hcutcoord, hmixmom]
        _ = m k := by simp
  -- Repeated integration reconstructs one function with every endpoint jet.
  have reconstruct (n : ℕ) (b : Fin (n+1) → ℝ) (rho : ℝ → ℝ)
      (hsmooth : ContDiff ℝ ∞ rho)
      (hpositive : ∀ x ∈ Ioo (0:ℝ) 1, 0 < rho x)
      (hend : rho 0 = 1 ∧ rho 1 = 1)
      (hflat : ∀ r : ℕ, 0 < r → jet r rho 0 = 0 ∧ jet r rho 1 = 0)
      (hmoments : ∀ k : Fin (n+1),
        (∫ t in Icc (0:ℝ) 1, (1-t)^k.val * rho t) = (k.val.factorial : ℝ) * b ⟨n-k.val, by omega⟩) :
      let F := repeatedIntegral (n+1) rho
      ContDiffOn ℝ ∞ F unitInterval ∧
      (∀ j : Fin (n+1), jet j.val F 0 = 0 ∧ jet j.val F 1 = b j) ∧
      (∀ x ∈ Ioo (0:ℝ) 1, 0 < jet (n+1) F x) ∧
      jet (n+1) F 0 = 1 ∧ jet (n+1) F 1 = 1 ∧
      (∀ j : ℕ, n+1 < j → jet j F 0 = 0 ∧ jet j F 1 = 0) ∧
      b ∈ W n := by
    dsimp only
    have hud : UniqueDiffOn ℝ unitInterval := uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1)
    have h0 : (0:ℝ) ∈ unitInterval := by norm_num [unitInterval]
    have h1 : (1:ℝ) ∈ unitInterval := by norm_num [unitInterval]
    have hs (k : ℕ) : ContDiff ℝ ∞ (repeatedIntegral k rho) := by
      induction k with
      | zero => simpa [repeatedIntegral] using hsmooth
      | succ k ih =>
        rw [repeatedIntegral, Function.iterate_succ_apply']
        apply contDiff_infty_iff_deriv.mpr
        have hd : deriv (primitive (repeatedIntegral k rho)) = repeatedIntegral k rho := by
          funext x
          exact ih.continuous.deriv_integral _ 0 x
        refine ⟨fun x => (ih.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt, ?_⟩
        change ContDiff ℝ ∞ (deriv (primitive (repeatedIntegral k rho)))
        rw [hd]
        exact ih
    have hd (k : ℕ) : deriv (repeatedIntegral (k+1) rho) = repeatedIntegral k rho := by
      funext x
      rw [repeatedIntegral, Function.iterate_succ_apply']
      exact (hs k).continuous.deriv_integral _ 0 x
    have hlow (j k : ℕ) :
        iteratedDeriv j (repeatedIntegral (j+k) rho) = repeatedIntegral k rho := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [show j+1+k = (j+k)+1 by omega, iteratedDeriv_succ', hd]
        exact ih
    have hz (k : ℕ) : repeatedIntegral (k+1) rho 0 = 0 := by
      simp [repeatedIntegral, Function.iterate_succ_apply', primitive]
    have htop (k : ℕ) : iteratedDeriv (k+1) (repeatedIntegral (k+1) rho) = rho := by
      simpa [repeatedIntegral] using hlow (k+1) 0
    have hformula (k : ℕ) : repeatedIntegral (k+1) rho 1 =
        (k.factorial : ℝ)⁻¹ * (∫ t in Icc (0:ℝ) 1, (1-t)^k * rho t) := by
      have hzero (j : ℕ) (hj : j ∈ Finset.range (k+1)) :
          iteratedDeriv j (repeatedIntegral (k+1) rho) 0 = 0 := by
        have hjk : j ≤ k := by simpa using Finset.mem_range.mp hj
        rw [show k+1 = j + ((k-j)+1) by omega, hlow]
        exact hz (k-j)
      have ht := map_add_eq_sum_add_integral_iteratedFDeriv
        (f := repeatedIntegral (k+1) rho) (x := (0:ℝ)) (y := (1:ℝ)) (n := k)
        (fun t _ => (hs (k+1)).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((k+1) : ℕ∞) ≤ ⊤)))
      simp only [smul_eq_mul, mul_one, zero_add, ← iteratedDeriv_eq_iteratedFDeriv,
        htop] at ht
      rw [show (∑ j ∈ Finset.range (k+1), (j.factorial : ℝ)⁻¹ *
        iteratedDeriv j (repeatedIntegral (k+1) rho) 0) = 0 by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hzero j hj, mul_zero], zero_add] at ht
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
        ← integral_Icc_eq_integral_Ioc] at ht
      exact ht
    let F := repeatedIntegral (n+1) rho
    have hF : ContDiff ℝ ∞ F := hs (n+1)
    have hbridge (j : ℕ) (x : ℝ) (hx : x ∈ unitInterval) : jet j F x = iteratedDeriv j F x :=
      iteratedDerivWithin_eq_iteratedDeriv hud
        (hF.contDiffAt.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))) hx
    have hjetlow (j : ℕ) (hj : j ≤ n+1) (x : ℝ) (hx : x ∈ unitInterval) :
        jet j F x = repeatedIntegral (n+1-j) rho x := by
      rw [hbridge j x hx]
      change iteratedDeriv j (repeatedIntegral (n+1) rho) x = _
      have he := congrFun (hlow j (n+1-j)) x
      rw [show j+(n+1-j) = n+1 by omega] at he
      exact he
    have hends (j : Fin (n+1)) : jet j.val F 0 = 0 ∧ jet j.val F 1 = b j := by
      have hjn : j.val ≤ n := by omega
      have he : n+1-j.val = (n-j.val)+1 := by omega
      constructor
      · rw [hjetlow j.val (by omega) 0 h0, he]
        exact hz _
      · rw [hjetlow j.val (by omega) 1 h1, he, hformula]
        have hm := hmoments ⟨n-j.val, by omega⟩
        have hb : (⟨n-(n-j.val), by omega⟩ : Fin (n+1)) = j := by
          apply Fin.ext
          change n-(n-j.val) = j.val
          omega
        rw [hb] at hm
        rw [hm]
        have hfac : ((n-j.val).factorial : ℝ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (n-j.val)
        field_simp
    have hjetTop (x : ℝ) (hx : x ∈ unitInterval) : jet (n+1) F x = rho x := by
      simpa [repeatedIntegral] using hjetlow (n+1) le_rfl x hx
    have hhigher : ∀ j : ℕ, n+1 < j → jet j F 0 = 0 ∧ jet j F 1 = 0 := by
      intro j hj
      let r := j-(n+1)
      have hr : 0 < r := by dsimp [r]; omega
      have he : j = r+(n+1) := by dsimp [r]; omega
      have hid : iteratedDeriv j F = iteratedDeriv r rho := by
        rw [he, iteratedDeriv_eq_iterate, Function.iterate_add_apply]
        rw [← iteratedDeriv_eq_iterate (n := n+1)]
        rw [show iteratedDeriv (n+1) F = rho by exact htop n]
        exact (iteratedDeriv_eq_iterate).symm
      have hbr (x : ℝ) (hx : x ∈ unitInterval) : jet r rho x = iteratedDeriv r rho x :=
        iteratedDerivWithin_eq_iteratedDeriv hud (hsmooth.contDiffAt.of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))) hx
      constructor
      · rw [hbridge j 0 h0, hid, ← hbr 0 h0]
        exact (hflat r hr).1
      · rw [hbridge j 1 h1, hid, ← hbr 1 h1]
        exact (hflat r hr).2
    have hmono : StrictMonoOn (primitive rho) unitInterval := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      · exact (hs 1).continuous.continuousOn
      · intro x hx
        rw [interior_Icc] at hx
        change 0 < deriv (fun u => ∫ t in (0:ℝ)..u, rho t) x
        rw [hsmooth.continuous.deriv_integral]
        exact hpositive x hx
    have hjetn : EqOn (jet n F) (primitive rho) unitInterval := by
      intro x hx
      simpa [repeatedIntegral, primitive] using hjetlow n (by omega) x hx
    have hmonoJet : StrictMonoOn (jet n F) unitInterval := by
      intro x hx y hy hxy
      rw [hjetn hx, hjetn hy]
      exact hmono hx hy hxy
    refine ⟨hF.contDiffOn, hends, ?_, ?_, ?_, hhigher, ?_⟩
    · intro x hx
      rw [hjetTop x ⟨hx.1.le, hx.2.le⟩]
      exact hpositive x hx
    · rw [hjetTop 0 h0]
      exact hend.1
    · rw [hjetTop 1 h1]
      exact hend.2
    · exact ⟨F, hF.contDiffOn.of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)), hmonoJet.monotoneOn,
        ⟨0, h0, 1, h1, (hmonoJet h0 h1 (by norm_num)).ne⟩, hends⟩
  -- Reverse the jet coordinates before dividing by their factorial scales.
  let Phi : (Fin (n+1) → ℝ) → Vec n := fun b k => (k.val.factorial : ℝ) * b k.rev
  let Psi : Vec n → (Fin (n+1) → ℝ) := fun m j => m j.rev / (j.rev.val.factorial : ℝ)
  have hPsiPhi (b : Fin (n+1) → ℝ) : Psi (Phi b) = b := by
    funext j
    dsimp only [Psi, Phi]
    rw [Fin.rev_rev]
    have hfac : (j.rev.val.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j.rev.val
    field_simp
  have hPhiPsi (m : Vec n) : Phi (Psi m) = m := by
    funext k
    dsimp only [Phi, Psi]
    rw [Fin.rev_rev]
    have hfac : (k.val.factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero k.val
    field_simp
  have hrev (k : Fin (n+1)) : (⟨n-k.val, by omega⟩ : Fin (n+1)) = k.rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  have hforward (b : Fin (n+1) → ℝ) (hb : b ∈ W n) : Phi b ∈ interior (S n : Set (Vec n)) := by
    simpa only [Phi, hrev] using originalCone n b hb
  have hrealize (m : Vec n) (hm : m ∈ interior (S n : Set (Vec n))) :
      ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F unitInterval ∧
        (∀ j : Fin (n+1), jet j.val F 0 = 0 ∧ jet j.val F 1 = Psi m j) ∧
        (∀ x ∈ Ioo (0:ℝ) 1, 0 < jet (n+1) F x) ∧
        jet (n+1) F 0 = 1 ∧ jet (n+1) F 1 = 1 ∧
        (∀ j : ℕ, n+1 < j → jet j F 0 = 0 ∧ jet j F 1 = 0) ∧
        Psi m ∈ W n := by
    obtain ⟨delta, c, hsmooth, hpositive, hend, hwithin, hmoments⟩ := compensatedDensity n m hm
    have hflat : ∀ r : ℕ, 0 < r → jet r (rho delta c) 0 = 0 ∧ jet r (rho delta c) 1 = 0 := by
      simpa only [jet, unitInterval] using hwithin
    have hmoments' : ∀ k : Fin (n+1),
        (∫ t in Icc (0:ℝ) 1, (1-t)^k.val * rho delta c t) =
          (k.val.factorial : ℝ) * Psi m ⟨n-k.val, by omega⟩ := by
      intro k
      rw [hrev]
      have he := congrFun (hPhiPsi m) k
      change (k.val.factorial : ℝ) * Psi m k.rev = m k at he
      exact (hmoments k).trans he.symm
    exact ⟨repeatedIntegral (n+1) (rho delta c),
      reconstruct n (Psi m) (rho delta c) hsmooth hpositive hend hflat hmoments'⟩
  have heq : W n = Phi ⁻¹' interior (S n : Set (Vec n)) := by
    ext b
    constructor
    · exact hforward b
    · intro hm
      have hr := hrealize (Phi b) hm
      rw [hPsiPhi] at hr
      exact hr.choose_spec.2.2.2.2.2.2
  have hPhi : Continuous Phi := by
    apply continuous_pi
    intro k
    exact continuous_const.mul (continuous_apply k.rev)
  constructor
  · rw [heq]
    exact isOpen_interior.preimage hPhi
  · intro b hb
    have hr := hrealize (Phi b) (hforward b hb)
    rw [hPsiPhi] at hr
    obtain ⟨F, hs, hj, hp, h0, h1, hh, _⟩ := hr
    exact ⟨F, hs, hj, hp, h0, h1, hh⟩

end PnOriginal
