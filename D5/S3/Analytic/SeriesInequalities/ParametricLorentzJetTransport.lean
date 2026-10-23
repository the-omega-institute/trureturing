/- GID: D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parameter jets of the actual finite Lorentz center history. -/

import D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open Polynomial Finset Filter
open scoped Topology ContDiff

namespace D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport

open LorentzLowDegreeCoefficientRemainder LorentzLocalCoefficientKernel
open LorentzCoefficientRemainder LorentzWeightedHolderControl LorentzCommonGridStability
open OriginalRingEnvelopeScale ReferenceProfileMixedJets

private def jetMap (n r : ℕ) : (ℕ → ℕ → ℂ) →ₗ[ℂ] ℂ[X] where
  toFun := lorentzJet n r
  map_add' f g := by
    simp [lorentzJet,Pi.add_apply,map_add,add_mul,mul_add,sum_add_distrib]
  map_smul' c f := by
    simp [lorentzJet,Pi.smul_apply,smul_eq_C_mul,map_mul,mul_sum,← mul_assoc,
      mul_left_comm (C c)]
    apply sum_congr rfl
    intro ν _
    apply sum_congr rfl
    intro i _
    ring

private def operatorMap (n r : ℕ) : ℂ[X] →ₗ[ℂ] ℂ[X] where
  toFun := lorentzOperator n r
  map_add' P Q := by
    simp [lorentzOperator,lorentzJet,map_add,add_mul,mul_add,sum_add_distrib]
  map_smul' c P := by
    simp [lorentzOperator,lorentzJet,iterate_derivative_smul,eval_smul,smul_eq_C_mul,
      map_mul,mul_sum,← mul_assoc,mul_left_comm (C c)]
    apply sum_congr rfl
    intro ν _
    apply sum_congr rfl
    intro i _
    ring

private def stageMap (s n r : ℕ) : (ℕ → ℕ → ℕ → ℂ) →ₗ[ℂ] ℂ[X] :=
  (jetMap n r).comp (LinearMap.proj s)

private def historyMap (τ b r : ℕ) : ℕ → (ℕ → ℕ → ℕ → ℂ) →ₗ[ℂ] ℂ[X]
  | 0 => stageMap 0 τ r
  | k+1 => historyMap τ b r k + stageMap (k+1) (τ*b^(k+1)) r -
      (operatorMap (τ*b^(k+1)) r).comp (historyMap τ b r k)

private lemma history_congr (τ b r k : ℕ) (F G : ℕ → ℕ → ℕ → ℂ)
    (h : ∀ s ≤ k, ∀ ν ≤ r, ∀ i ≤ τ*b^s, F s ν i = G s ν i) :
    historyMap τ b r k F = historyMap τ b r k G := by
  have hj (s n : ℕ) (he : ∀ ν ≤ r, ∀ i ≤ n, F s ν i = G s ν i) :
      stageMap s n r F = stageMap s n r G := by
    change lorentzJet n r (F s) = lorentzJet n r (G s)
    unfold lorentzJet
    apply sum_congr rfl
    intro ν hν
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [he ν (by have := mem_range.mp hν; omega) i (by have := mem_range.mp hi; omega)]
  induction k with
  | zero => exact hj 0 τ (by simpa using h 0 (by omega))
  | succ k ih =>
    have hp := ih (fun s hs => h s (by omega))
    change historyMap τ b r k F + stageMap (k+1) (τ*b^(k+1)) r F -
      operatorMap (τ*b^(k+1)) r (historyMap τ b r k F) = _
    rw [hp,hj (k+1) (τ*b^(k+1)) (h (k+1) (by omega))]
    rfl

private def samples (τ b : ℕ) (f : ℝ → ℂ) (s ν i : ℕ) : ℂ :=
  iteratedDerivWithin ν f (Set.Icc 0 1) ((i : ℝ)/(τ*b^s))

private lemma history_eq_center {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
    (r k : ℕ) {f : ℝ → ℂ} (hf : ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1)) :
    historyMap τ b r k (samples τ b f) = center τ b r f k := by
  induction k with
  | zero =>
    change lorentzJet τ r (samples τ b f 0) = holderOperator τ r f
    unfold samples holderOperator
    simp only [pow_zero,mul_one,Nat.cast_one]
  | succ k ih =>
    change historyMap τ b r k (samples τ b f) +
      lorentzJet (τ*b^(k+1)) r (samples τ b f (k+1)) -
        lorentzOperator (τ*b^(k+1)) r (historyMap τ b r k (samples τ b f)) = _
    rw [ih,center,operator_residual (Nat.mul_pos hτ (pow_pos hb _)) hf]
    unfold samples holderOperator
    push_cast
    ring

private abbrev Sample (τ b r k : ℕ) :=
  (s : Fin (k+1)) × Fin (r+1) × Fin (τ*b^s.val+1)

private def extendSamples (τ b r k : ℕ) :
    (Sample τ b r k → ℂ) →ₗ[ℂ] (ℕ → ℕ → ℕ → ℂ) where
  toFun F s ν i := if hs : s ≤ k then if hν : ν ≤ r then if hi : i ≤ τ*b^s then
    F ⟨⟨s,by omega⟩,⟨ν,by omega⟩,⟨i,by dsimp; omega⟩⟩ else 0 else 0 else 0
  map_add' F G := by ext s ν i; dsimp; split_ifs <;> simp
  map_smul' c F := by ext s ν i; dsimp; split_ifs <;> simp

private def coefficientMap (D J : ℕ) : ℂ[X] →ₗ[ℂ] ℂ where
  toFun := bernsteinCoefficient D J
  map_add' P Q := by
    simp [bernsteinCoefficient,coeff_add,add_mul,add_div,sum_add_distrib]
  map_smul' c P := by
    simp [bernsteinCoefficient,coeff_smul,smul_eq_mul,mul_assoc,← Finset.mul_sum,mul_div_assoc]

private def coefficientFunctional (τ b r k D J : ℕ) :
    (Sample τ b r k → ℂ) →L[ℝ] ℂ :=
  (((coefficientMap D J).comp
    ((historyMap τ b r k).comp (extendSamples τ b r k))).restrictScalars ℝ).toContinuousLinearMap

private lemma functional_eq {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
    (r k D J : ℕ) {f : ℝ → ℂ} (hf : ContDiffOn ℝ r f (Set.Icc (0 : ℝ) 1)) :
    coefficientFunctional τ b r k D J
      (fun s => samples τ b f s.1.val s.2.1.val s.2.2.val) =
        bernsteinCoefficient D J (center τ b r f k) := by
  change bernsteinCoefficient D J
    (historyMap τ b r k (extendSamples τ b r k
      (fun s => samples τ b f s.1.val s.2.1.val s.2.2.val))) = _
  rw [history_congr τ b r k _ (samples τ b f) ?_,history_eq_center hτ hb r k hf]
  intro s hs ν hν i hi
  simp [extendSamples,hs,hν,hi]

lemma linear_iterated {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F)
    {f : ℝ → E} {x : ℝ} {m : ℕ} (hf : ContDiffAt ℝ m f x) :
    iteratedDeriv m (fun y => L (f y)) x = L (iteratedDeriv m f x) := by
  exact congrArg (fun p => p (fun _ : Fin m => (1 : ℝ)))
    (L.iteratedFDeriv_comp_left hf le_rfl)

private lemma coefficient_transport {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
    (r k D J m : ℕ) (F : ℝ → ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hf : ∀ y : ℝ, 0 < y → ContDiffOn ℝ r (F y) (Set.Icc (0 : ℝ) 1))
    (hs : ∀ s ≤ k, ∀ ν ≤ r, ∀ i ≤ τ*b^s,
      ContDiffAt ℝ m (fun y => samples τ b (F y) s ν i) x)
    (hm : ContDiffOn ℝ r (fun q => iteratedDeriv m (fun y => F y q) x) (Set.Icc (0 : ℝ) 1))
    (hcomm : ∀ ν ≤ r, ∀ q ∈ Set.Icc (0 : ℝ) 1,
      iteratedDeriv m (fun y => iteratedDerivWithin ν (F y) (Set.Icc 0 1) q) x =
        iteratedDerivWithin ν (fun q => iteratedDeriv m (fun y => F y q) x) (Set.Icc 0 1) q) :
    iteratedDeriv m (fun y => bernsteinCoefficient D J (center τ b r (F y) k)) x =
      bernsteinCoefficient D J
        (center τ b r (fun q => iteratedDeriv m (fun y => F y q) x) k) := by
  let L := coefficientFunctional τ b r k D J
  let V : ℝ → Sample τ b r k → ℂ := fun y s =>
    samples τ b (F y) s.1.val s.2.1.val s.2.2.val
  have hV : ContDiffAt ℝ m V x := by
    apply contDiffAt_pi.mpr
    intro s
    exact hs s.1.val (by omega) s.2.1.val (by omega) s.2.2.val (by omega)
  have he : (fun y => bernsteinCoefficient D J (center τ b r (F y) k)) =ᶠ[𝓝 x]
      (fun y => L (V y)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (functional_eq hτ hb r k D J (hf y hy)).symm
  rw [he.iteratedDeriv_eq m,linear_iterated L hV]
  have hjet : iteratedDeriv m V x = fun s : Sample τ b r k =>
      samples τ b (fun q => iteratedDeriv m (fun y => F y q) x) s.1.val s.2.1.val s.2.2.val := by
    funext s
    have hi := (linear_iterated (ContinuousLinearMap.proj s) hV).symm
    have hn : (0 : ℝ) < τ*b^s.1.val := by positivity
    have hq : (s.2.2.val : ℝ)/(τ*b^s.1.val) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one hn).mpr
        exact_mod_cast (show s.2.2.val ≤ τ*b^s.1.val by omega)
    exact hi.trans (hcomm s.2.1.val (by omega) _ hq)
  rw [hjet]
  exact functional_eq hτ hb r k D J hm

private lemma deriv_profile {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k m : ℕ) :
    deriv (profile φ k m) = profile (deriv φ) (k+1) m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext t
    have hs := profile_smooth hφ k m
    have hd := hs.differentiable (by simp)
    have hdd := ((contDiff_infty_iff_deriv.mp hs).2).differentiable (by simp)
    have h := ((hd t).hasDerivAt.const_mul (-((k+m : ℕ) : ℝ))).sub
      ((hasDerivAt_id t).mul ((hdd t).hasDerivAt))
    change deriv (fun t => -((k+m : ℕ) : ℝ)*profile φ k m t -
      t*deriv (profile φ k m) t) t = _
    have he := h.deriv
    change deriv (fun t => -((k+m : ℕ) : ℝ)*profile φ k m t -
      t*deriv (profile φ k m) t) t = _ at he
    rw [he,ih]
    simp only [profile,Nat.cast_add,Nat.cast_one,id_eq]
    ring

private lemma iterated_profile {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (k m ell : ℕ) :
    iteratedDeriv ell (profile φ k m) = profile (iteratedDeriv ell φ) (k+ell) m := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    rw [iteratedDeriv_succ,ih,deriv_profile (iterated_smooth hφ ell)]
    simp only [iteratedDeriv_succ,Nat.add_assoc]

private lemma mixed_commute {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    xqJet φ η a d m ell x q = qxJet φ η a d m ell x q := by
  rw [xq_formula hφ η a d m ell hx q,qx_formula hφ η a d m ell hx q,
    iterated_profile hφ 0 m ell,Nat.zero_add,Nat.add_comm ell m]

private lemma full_mixed_commute {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (m ell : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    iteratedDeriv m (fun y => iteratedDeriv ell (reference φ η a d y) q) x =
      fullQxJet φ η a d m ell x q := by
  have hc := mixed_commute hφ η a d m ell hx q
  cases m with
  | zero => rfl
  | succ m =>
    cases ell with
    | zero => rfl
    | succ ell =>
      simp only [xqJet,qxJet,fullQxJet] at hc ⊢
      unfold reference at hc ⊢
      simpa only [add_sub_cancel_left,
        iteratedDeriv_const_add (Nat.succ_pos ell),
        iteratedDeriv_const_add (Nat.succ_pos m)] using hc

private lemma qjet_formula {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (ν : ℕ) (x q : ℝ) :
    iteratedDeriv ν (reference φ η a d x) q =
      η*d^ν*x^(-(ν : ℤ))*iteratedDeriv ν φ ((a+d*q)/x) +
        if ν = 0 then 1/2 else 0 := by
  cases ν with
  | zero => simp [reference]; ring
  | succ ν =>
    unfold reference
    simp only [Nat.succ_eq_add_one,iteratedDeriv_const_add (Nat.succ_pos ν),
      iteratedDeriv_const_mul_field,affine_iterated hφ,Nat.succ_ne_zero,if_false,add_zero]
    ring

private lemma xjet_formula {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (m : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    iteratedDeriv m (fun y => reference φ η a d y q) x =
      η*x^(-(m : ℤ))*profile φ 0 m ((a+d*q)/x) + if m = 0 then 1/2 else 0 := by
  have h := fullQxJet_eq φ η a d m 0 x q
  rw [qx_formula hφ η a d m 0 hx q] at h
  simpa [fullQxJet] using h

private lemma reference_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d x : ℝ) : ContDiff ℝ ∞ (reference φ η a d x) := by
  exact contDiff_const.add (contDiff_const.mul
    (hφ.comp ((contDiff_const.add (contDiff_const.mul contDiff_id)).div_const x)))

private lemma qjet_scale_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (η a d : ℝ) (ν : ℕ) {x : ℝ} (hx : x ≠ 0) (q : ℝ) :
    ContDiffAt ℝ ∞ (fun y => iteratedDeriv ν (reference φ η a d y) q) x := by
  simp_rw [qjet_formula hφ]
  apply ContDiffAt.add _ contDiffAt_const
  apply ContDiffAt.mul
  · simp only [zpow_neg,zpow_natCast]
    exact contDiffAt_const.mul ((contDiffAt_id.pow ν).inv (pow_ne_zero ν hx))
  · exact (iterated_smooth hφ ν).contDiffAt.comp x
      (contDiffAt_const.div contDiffAt_id hx)

lemma reference_transport {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (η a d : ℝ) (r k D J m : ℕ)
    {x : ℝ} (hx : 0 < x) :
    iteratedDeriv m (fun y => bernsteinCoefficient D J
      (center τ b r (fun q : ℝ => (reference φ η a d y q : ℂ)) k)) x =
        bernsteinCoefficient D J (center τ b r
          (fun q : ℝ => ((iteratedDeriv m (fun y => reference φ η a d y q) x : ℝ) : ℂ)) k) := by
  have hinf (n : ℕ) : (n : ℕ∞ω) ≤ (↑(⊤ : ℕ∞) : ℕ∞ω) := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hxsmooth (q : ℝ) : ContDiffAt ℝ ∞ (fun y => reference φ η a d y q) x := by
    exact contDiffAt_const.add (contDiffAt_const.mul
      (hφ.contDiffAt.comp x (contDiffAt_const.div contDiffAt_id hx.ne')))
  have hcast (q : ℝ) : iteratedDeriv m (fun y => (reference φ η a d y q : ℂ)) x =
      ((iteratedDeriv m (fun y => reference φ η a d y q) x : ℝ) : ℂ) := by
    simpa only [Complex.ofRealCLM_apply] using
      linear_iterated Complex.ofRealCLM ((hxsmooth q).of_le (hinf m))
  have hqsmooth : ContDiff ℝ ∞ (fun q => iteratedDeriv m (fun y => reference φ η a d y q) x) := by
    simp_rw [xjet_formula hφ η a d m hx.ne']
    exact (contDiff_const.mul ((profile_smooth hφ 0 m).comp
      ((contDiff_const.add (contDiff_const.mul contDiff_id)).div_const x))).add contDiff_const
  have hsamples (y : ℝ) (ν : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin ν (fun q => (reference φ η a d y q : ℂ)) (Set.Icc 0 1) q =
        ((iteratedDeriv ν (reference φ η a d y) q : ℝ) : ℂ) :=
    complex_jet (reference_smooth hφ η a d y) ν hq
  have hc := coefficient_transport hτ hb r k D J m
    (fun y q => (reference φ η a d y q : ℂ)) hx
  have hf (y : ℝ) (_hy : 0 < y) : ContDiffOn ℝ r
      (fun q => (reference φ η a d y q : ℂ)) (Set.Icc 0 1) := by
    exact (Complex.ofRealCLM.contDiff.comp (reference_smooth hφ η a d y)).contDiffOn.of_le (hinf r)
  have hs (s : ℕ) (_hs : s ≤ k) (ν : ℕ) (_hν : ν ≤ r) (i : ℕ) (hi : i ≤ τ*b^s) :
      ContDiffAt ℝ m (fun y => samples τ b (fun q => (reference φ η a d y q : ℂ)) s ν i) x := by
    have hn : (0 : ℝ) < τ*b^s := by positivity
    have hq : (i : ℝ)/(τ*b^s) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity,(div_le_one hn).mpr (by exact_mod_cast hi)⟩
    simp only [samples]
    simp_rw [hsamples _ _ _ hq]
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (qjet_scale_smooth hφ η a d ν hx.ne' _)).of_le (hinf m)
  have hm : ContDiffOn ℝ r
      (fun q => iteratedDeriv m (fun y => (reference φ η a d y q : ℂ)) x) (Set.Icc 0 1) := by
    simp_rw [hcast]
    exact (Complex.ofRealCLM.contDiff.comp hqsmooth).contDiffOn.of_le (hinf r)
  have hcomm (ν : ℕ) (_hν : ν ≤ r) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDeriv m (fun y => iteratedDerivWithin ν
        (fun q => (reference φ η a d y q : ℂ)) (Set.Icc 0 1) q) x =
      iteratedDerivWithin ν (fun q => iteratedDeriv m
        (fun y => (reference φ η a d y q : ℂ)) x) (Set.Icc 0 1) q := by
    simp_rw [hsamples _ ν q hq,hcast]
    rw [complex_jet hqsmooth ν hq]
    have hi := linear_iterated Complex.ofRealCLM
      ((qjet_scale_smooth hφ η a d ν hx.ne' q).of_le (hinf m))
    simpa only [Complex.ofRealCLM_apply,full_mixed_commute hφ η a d m ν hx.ne' q,
      fullQxJet] using hi
  have h := hc hf hs hm hcomm
  simpa only [hcast] using h

/-- One already fixed initial grid works for every parameter derivative order.
The actual coefficient history has the coarse ring scale, while its actual
successive increments decay at the fine reference degree. The simultaneous
`q`-jet error retains the endpoint-sensitive local Bernstein scale. -/
theorem reference_center_mixed_scales {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Set.Ioi 0)
    (β η a d : ℝ) (r : ℕ) (ρ : ℝ) (hρ : (r : ℝ) < ρ) (hρ1 : ρ < (r : ℝ)+1) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar : ℝ, 0 < xstar → ∀ N : ℕ, r+1 ≤ N →
      ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ x : ℝ,
      0 < x → x ≤ 1 → ringScale xstar b j / Real.sqrt b ≤ x →
      let f := fun y q : ℝ => (reference (cutoff χ β) η a d y q : ℂ)
      let fm := fun q : ℝ => ((iteratedDeriv m
        (fun y => reference (cutoff χ β) η a d y q) x : ℝ) : ℂ)
      ∀ k : ℕ,
        (∀ t ≤ (N*b^j)*b^k+r,
          ‖iteratedDeriv m (fun y => bernsteinCoefficient ((N*b^j)*b^k+r) t
            (center (N*b^j) b r (f y) k)) x‖ ≤ C*(ringScale xstar b j)^(-(m : ℝ))) ∧
        (∀ t ≤ (N*b^j)*b^(k+1)+r,
          ‖iteratedDeriv m (fun y => bernsteinCoefficient ((N*b^j)*b^(k+1)+r) t
            (center (N*b^j) b r (f y) (k+1)-center (N*b^j) b r (f y) k)) x‖ ≤
              C*(ringScale xstar b j)^(-(m : ℝ)-ρ)*
                (((N*b^j)*b^(k+1) : ℕ) : ℝ)^(-ρ/2)) ∧
        (∀ ell ≤ r, ∀ q ∈ Set.Icc (0 : ℝ) 1,
          ‖iteratedDerivWithin ell fm (Set.Icc 0 1) q -
            (derivative^[ell] (center (N*b^j) b r fm k)).eval (q : ℂ)‖ ≤
              C*(ringScale xstar b j)^(-(m : ℝ)-ρ)*
                delta ((N*b^j)*b^k) q^(ρ-(ell : ℝ))) := by
  obtain ⟨Bc,hBc,hcb⟩ := center_coefficient_control r ρ hρ hρ1
  obtain ⟨Bs,hBs,U,V,E,hU,hV,hE,hst⟩ := common_grid_stability r ρ hρ hρ1
  obtain ⟨L,hL,hloc⟩ := residual_coefficient_control r ρ hρ
  refine ⟨max Bc Bs,le_trans hBc (le_max_left _ _),?_⟩
  intro b hb xstar hxstar N hN m
  have hbc : Bc ≤ b := (le_max_left _ _).trans hb
  have hbs : Bs ≤ b := (le_max_right _ _).trans hb
  have hb0 : 0 < b := by omega
  have hN0 : 0 < N := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb0
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbR
  have hφ := cutoff_smooth hχ hsχ β
  obtain ⟨K,hK,hcoeff⟩ := hcb b hbc
  have hp := cutoff_reference_mixed_scales hχ hcχ hsχ β η a d (Real.sqrt b) hsqrt
  choose A hA hAb using hp.1 m
  obtain ⟨H,hH,hHb⟩ := hp.2 m r (ρ-r) (by linarith) (by linarith)
  have hA0 := hA 0
  let Aall := 1+∑ ν ∈ Finset.Icc 1 r, A ν
  have hAA : 0 ≤ Aall := by
    have := sum_nonneg (s := Finset.Icc 1 r) (fun ν _ => (hA ν).le)
    dsimp [Aall]; linarith
  let R := (A 0+1)+K*Aall*(∑ ν ∈ Finset.Icc 1 r,
    (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ)))+K*H*(N : ℝ)^(-ρ/2)*xstar^(-ρ)
  let T := L*E*H*((b : ℝ)*((r : ℝ)+1))^ρ
  let C := 1+R+T+E*H
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hRC : R ≤ C := by dsimp [C]; nlinarith [mul_pos hE hH]
  have hTC : T ≤ C := by dsimp [C]; nlinarith [mul_pos hE hH]
  have hEC : E*H ≤ C := by dsimp [C]; nlinarith [mul_pos hE hH]
  refine ⟨C,hC,?_⟩
  intro j x hx hx1 hxs
  dsimp only
  let s := ringScale xstar b j
  let τ := N*b^j
  let g : ℝ → ℝ := fun q => iteratedDeriv m
    (fun y => reference (cutoff χ β) η a d y q) x
  have hs : 0 < s := by dsimp [s,ringScale]; positivity
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτr : r ≤ τ := (by omega : r ≤ N).trans
    (Nat.le_mul_of_pos_right N (pow_pos hb0 j))
  have hg : ContDiff ℝ ∞ g := by
    simp_rw [g,xjet_formula hφ η a d m hx.ne']
    exact (contDiff_const.mul ((profile_smooth hφ 0 m).comp
      ((contDiff_const.add (contDiff_const.mul contDiff_id)).div_const x))).add contDiff_const
  have hgc : ContDiffOn ℝ r (fun q => (g q : ℂ)) (Set.Icc 0 1) :=
    (Complex.ofRealCLM.contDiff.comp hg).contDiffOn.of_le
      (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))
  have hj (ell : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin ell (fun q => (g q : ℂ)) (Set.Icc 0 1) q =
        ((fullQxJet (cutoff χ β) η a d m ell x q : ℝ) : ℂ) := complex_jet hg ell hq
  have hjet (ell : ℕ) (q : ℝ) (he : m ≠ 0 ∨ ell ≠ 0) :
      |fullQxJet (cutoff χ β) η a d m ell x q| ≤ A ell*s^(-(m : ℝ))*s^(-(ell : ℝ)) := by
    have h := (hAb ell s x hs hx hxs q).2
    rw [fullQxJet_eq,if_neg (by tauto),add_zero]
    convert h using 1
    rw [mul_assoc,← Real.rpow_add hs]
    congr 2
    push_cast
    ring
  have hzero (q : ℝ) (_hq : q ∈ Set.Icc (0 : ℝ) 1) :
      ‖(g q : ℂ)-(0 : ℂ)‖ ≤ (A 0+1)*s^(-(m : ℝ)) := by
    rw [sub_zero,Complex.norm_real,Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst m
      have hh := (hAb 0 s x hs hx hxs q).2
      have he := fullQxJet_eq (cutoff χ β) η a d 0 0 x q
      simp only [fullQxJet,qxJet,iteratedDeriv_zero] at he hh
      simp only [g,iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one]
      simp only [Nat.cast_zero,Nat.zero_add,neg_zero,Real.rpow_zero,mul_one] at hh
      dsimp [reference] at hh ⊢
      rw [abs_le] at hh ⊢
      constructor <;> linarith [hh.1,hh.2]
    · have hh := hjet 0 q (Or.inl hm)
      have hh' : |g q| ≤ A 0*s^(-(m : ℝ)) := by
        simpa only [fullQxJet,iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one,g] using hh
      exact hh'.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hder (ν : ℕ) (hν : ν ∈ Finset.Icc 1 r) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin ν (fun q => (g q : ℂ)) (Set.Icc 0 1) q‖ ≤
        (Aall*s^(-(m : ℝ)))*s^(-(ν : ℝ)) := by
    rw [hj ν q hq,Complex.norm_real,Real.norm_eq_abs]
    have hν0 : ν ≠ 0 := by have := (Finset.mem_Icc.mp hν).1; omega
    apply (hjet ν q (Or.inr hν0)).trans
    have hAall : A ν ≤ Aall := by
      have := single_le_sum (s := Finset.Icc 1 r) (f := A) (fun i _ => (hA i).le) hν
      dsimp [Aall]; linarith
    gcongr
  have hholder (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (q' : ℝ) (hq' : q' ∈ Set.Icc (0 : ℝ) 1) :
      ‖iteratedDerivWithin r (fun q => (g q : ℂ)) (Set.Icc 0 1) q -
        iteratedDerivWithin r (fun q => (g q : ℂ)) (Set.Icc 0 1) q'‖ ≤
          (H*s^(-(m : ℝ)-ρ))*|q-q'|^(ρ-(r : ℝ)) := by
    rw [hj r q hq,hj r q' hq',← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    have hh := (hHb s x hs hx hx1 hxs).2 q q'
    convert hh using 1
    congr 2
    push_cast
    ring
  have hstable := hst b hbs τ hτ (fun q => (g q : ℂ)) hgc
    (H*s^(-(m : ℝ)-ρ)) (by positivity) hholder
  intro k
  constructor
  · intro t ht
    rw [reference_transport hτ hb0 hφ η a d r k _ t m hx]
    have hc := hcoeff τ hτ hτr (fun q => (g q : ℂ)) hgc 0
      ((A 0+1)*s^(-(m : ℝ))) (Aall*s^(-(m : ℝ))) (H*s^(-(m : ℝ)-ρ)) s
      (by positivity) (by positivity) (by positivity) hs hzero hder hholder k t ht
    rw [sub_zero] at hc
    have hsum : (∑ ν ∈ Finset.Icc 1 r, (τ : ℝ)^(-(ν : ℝ)/2)*s^(-(ν : ℝ))) =
        ∑ ν ∈ Finset.Icc 1 r, (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ)) := by
      apply sum_congr rfl
      intro ν _
      exact ring_scale_cancel hN0 hb0 hxstar j (ν : ℝ)
    rw [hsum] at hc
    have hcancel := ring_scale_cancel hN0 hb0 hxstar j ρ
    have he : K*(H*s^(-(m : ℝ)-ρ))*(τ : ℝ)^(-ρ/2) =
        (K*H*(N : ℝ)^(-ρ/2)*xstar^(-ρ))*s^(-(m : ℝ)) := by
      rw [Real.rpow_sub hs]
      have hr : s^(-ρ) = 1/s^ρ := by rw [Real.rpow_neg hs.le,one_div]
      change (τ : ℝ)^(-ρ/2)*s^(-ρ) = _ at hcancel
      rw [hr,← div_eq_mul_one_div] at hcancel
      calc
        _ = K*H*((τ : ℝ)^(-ρ/2)/s^ρ)*s^(-(m : ℝ)) := by ring
        _ = _ := by rw [hcancel]; ring
    rw [he] at hc
    have he' : (A 0+1)*s^(-(m : ℝ))+K*(Aall*s^(-(m : ℝ)))*
        (∑ ν ∈ Finset.Icc 1 r, (N : ℝ)^(-(ν : ℝ)/2)*xstar^(-(ν : ℝ)))+
        (K*H*(N : ℝ)^(-ρ/2)*xstar^(-ρ))*s^(-(m : ℝ)) = R*s^(-(m : ℝ)) := by
      dsimp [R]; ring
    rw [he'] at hc
    exact hc.trans (mul_le_mul_of_nonneg_right hRC (by positivity))
  constructor
  · intro t ht
    have hng : τ*b^k*b = τ*b^(k+1) := by rw [pow_succ]; ring
    have hτk : τ ≤ τ*b^k := Nat.le_mul_of_pos_right τ (pow_pos hb0 k)
    have hn : 0 < τ*b^k := by positivity
    have hn' : 0 < τ*b^(k+1) := by positivity
    have hloc := hloc (τ*b^k) b hn
      ((hτr.trans hτk).trans (Nat.le_mul_of_pos_right _ hb0)) (by omega)
      (fun q => (g q : ℂ)) hgc (center τ b r (fun q => (g q : ℂ)) k)
      (E*(H*s^(-(m : ℝ)-ρ))) (by positivity) (hstable k).2.2.2 t (by rwa [hng])
    rw [hng] at hloc
    have hp : (t : ℝ)/(τ*b^(k+1)+r) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity,(div_le_one (by positivity)).mpr (by exact_mod_cast ht)⟩
    have hd := Real.rpow_le_rpow (delta_pos hn' _).le
      (delta_upper hn' (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using hp))
      (show 0 ≤ ρ by have := Nat.cast_nonneg (α := ℝ) r; linarith)
    have hd' : delta (τ*b^(k+1)) ((t : ℝ)/(τ*b^(k+1)+r))^ρ ≤
        ((τ*b^(k+1) : ℕ) : ℝ)^(-ρ/2) := by
      rw [← Real.rpow_mul (by positivity),show -(1/2 : ℝ)*ρ = -ρ/2 by ring] at hd
      simpa only [Nat.cast_mul,Nat.cast_pow] using hd
    -- The two old/fine coefficient functionals use the same finite history.
    have hsmooth (K D t : ℕ) : ContDiffAt ℝ m
        (fun y => bernsteinCoefficient D t
          (center τ b r (fun q : ℝ => (reference (cutoff χ β) η a d y q : ℂ)) K)) x := by
      apply ContDiffAt.congr_of_eventuallyEq
        ((coefficientFunctional τ b r K D t).contDiff.contDiffAt.comp x ?_)
      · filter_upwards [Ioi_mem_nhds hx] with y hy
        exact (functional_eq hτ hb0 r K D t
          ((Complex.ofRealCLM.contDiff.comp (reference_smooth hφ η a d y)).contDiffOn.of_le
            (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤)))).symm
      · apply contDiffAt_pi.mpr
        intro z
        have hz : (z.2.2.val : ℝ)/(τ*b^z.1.val) ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨by positivity,(div_le_one (by positivity)).mpr (by exact_mod_cast (show z.2.2.val ≤ τ*b^z.1.val by omega))⟩
        change ContDiffAt ℝ m (fun y => iteratedDerivWithin z.2.1.val
          (fun q => (reference (cutoff χ β) η a d y q : ℂ)) (Set.Icc 0 1)
          ((z.2.2.val : ℝ)/(τ*b^z.1.val))) x
        simp_rw [complex_jet (reference_smooth hφ η a d _) _ hz]
        exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
          (qjet_scale_smooth hφ η a d _ hx.ne' _)).of_le
            (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
    simp_rw [coefficient_sub]
    rw [iteratedDeriv_fun_sub (hsmooth (k+1) _ t) (hsmooth k _ t)]
    rw [reference_transport hτ hb0 hφ η a d r (k+1) _ t m hx]
    rw [reference_transport hτ hb0 hφ η a d r k _ t m hx]
    rw [← coefficient_sub,center,add_sub_cancel_left]
    apply hloc.trans
    have hscale := mul_le_mul_of_nonneg_left hd'
      (show 0 ≤ L*(E*(H*s^(-(m : ℝ)-ρ)))*((b : ℝ)*((r : ℝ)+1))^ρ by positivity)
    calc
      _ ≤ T*s^(-(m : ℝ)-ρ)*((τ*b^(k+1) : ℕ) : ℝ)^(-ρ/2) := by
        convert hscale using 1 <;> (try simp only [T,Nat.cast_mul,Nat.cast_pow,pow_succ,mul_assoc]) <;> (try ring) <;> rfl
      _ ≤ _ := by gcongr
  · intro ell hell q hq
    apply ((hstable k).2.2.2 ell hell q hq).trans
    calc
      _ = (E*H)*s^(-(m : ℝ)-ρ)*delta (τ*b^k) q^(ρ-(ell : ℝ)) := by ring
      _ ≤ C*s^(-(m : ℝ)-ρ)*delta (τ*b^k) q^(ρ-(ell : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC (by positivity))
          (Real.rpow_nonneg (delta_pos (by positivity) q).le _)

/-- A compact smooth profile supported strictly inside `(-1,1)`. -/
def scaleBump (z : ℝ) : ℝ := expNegInvGlue (9/16-z^2)

private lemma bump_smooth : ContDiff ℝ ∞ scaleBump :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))

private lemma bump_nonneg (z : ℝ) : 0 ≤ scaleBump z := expNegInvGlue.nonneg _

private lemma bump_zero {z : ℝ} (h : z ≤ -1 ∨ 1 ≤ z) : scaleBump z = 0 := by
  apply expNegInvGlue.zero_of_nonpos
  rcases h with h | h <;> nlinarith [sq_nonneg (z+1),sq_nonneg (z-1)]

private lemma bump_pos {z : ℝ} (hl : -1/2 ≤ z) (hu : z ≤ 1/2) : 0 < scaleBump z := by
  apply expNegInvGlue.pos_of_pos
  nlinarith [mul_nonneg (by linarith : 0 ≤ z+1/2) (by linarith : 0 ≤ 1/2-z)]

/-- The natural translated denominator in the smooth proportional partition. -/
def scaleDenominator (z : ℝ) : ℝ := ∑' i : ℕ, scaleBump (z-i)

private lemma bump_tail {z : ℝ} {K i : ℕ} (hz : z+1 < K) (hi : K ≤ i) :
    scaleBump (z-i) = 0 := by
  apply bump_zero (Or.inl _)
  have : (K : ℝ) ≤ i := by exact_mod_cast hi
  linarith

private lemma denominator_finite {z : ℝ} {K : ℕ} (hz : z+1 < K) :
    scaleDenominator z = ∑ i ∈ range K, scaleBump (z-i) := by
  apply tsum_eq_sum
  intro i hi
  exact bump_tail hz (by simpa using hi)

private lemma denominator_smooth (z : ℝ) : ContDiffAt ℝ ∞ scaleDenominator z := by
  obtain ⟨K,hK⟩ := exists_nat_gt (z+2)
  have he : scaleDenominator =ᶠ[𝓝 z] fun y => ∑ i ∈ range K, scaleBump (y-i) := by
    filter_upwards [Iio_mem_nhds (by linarith : z < (K : ℝ)-1)] with y hy
    exact denominator_finite (by have hy' : y < (K : ℝ)-1 := hy; linarith)
  apply ContDiffAt.congr_of_eventuallyEq _ he
  exact (ContDiff.sum (fun i _ => bump_smooth.comp (contDiff_id.sub contDiff_const))).contDiffAt

private lemma denominator_positive {z : ℝ} (hz : 0 ≤ z) : 0 < scaleDenominator z := by
  obtain ⟨K,hK⟩ := exists_nat_gt (z+2)
  rw [denominator_finite (by linarith : z+1 < K)]
  let j := ⌊z+1/2⌋₊
  have hjl := Nat.floor_le (show 0 ≤ z+1/2 by linarith)
  have hju := Nat.lt_floor_add_one (z+1/2)
  have hj : j ∈ range K := by
    apply mem_range.mpr
    change ⌊z+1/2⌋₊ < K
    exact_mod_cast (show (⌊z+1/2⌋₊ : ℝ) < K by linarith)
  exact (bump_pos (by dsimp [j]; linarith) (by dsimp [j]; linarith)).trans_le
    (single_le_sum (fun i _ => bump_nonneg _) hj)

/-- Smooth logarithmic scale coordinate. -/
def scaleCoordinate (xstar : ℝ) (b : ℕ) (x : ℝ) : ℝ :=
  2*Real.log (xstar/x)/Real.log b

/-- The original normalized smooth weights, before finite stage truncation. -/
def scaleWeight (xstar : ℝ) (b j : ℕ) (x : ℝ) : ℝ :=
  scaleBump (scaleCoordinate xstar b x-j)/scaleDenominator (scaleCoordinate xstar b x)

private lemma coordinate_nonneg {xstar x : ℝ} {b : ℕ}
    (hx : 0 < x) (hxx : x ≤ xstar) (hb : 1 < b) :
    0 ≤ scaleCoordinate xstar b x := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  apply div_nonneg _ (Real.log_pos hbR).le
  exact mul_nonneg (by norm_num) (Real.log_nonneg ((le_div_iff₀ hx).mpr (by linarith)))

private lemma weight_smooth {xstar x : ℝ} {b : ℕ}
    (hxstar : 0 < xstar) (hx : 0 < x) (hxx : x ≤ xstar) (hb : 1 < b) (j : ℕ) :
    ContDiffAt ℝ ∞ (scaleWeight xstar b j) x := by
  have hz : ContDiffAt ℝ ∞ (scaleCoordinate xstar b) x := by
    exact (contDiffAt_const.mul ((contDiffAt_const.div contDiffAt_id hx.ne').log
      (div_ne_zero hxstar.ne' hx.ne'))).div_const _
  exact ((bump_smooth.contDiffAt.comp x (hz.sub contDiffAt_const)).div
    ((denominator_smooth _).comp x hz)
    (denominator_positive (coordinate_nonneg hx hxx hb)).ne')

private lemma weight_mass {xstar x : ℝ} {b : ℕ}
    (hx : 0 < x) (hxx : x ≤ xstar) (hb : 1 < b) (k : ℕ) :
    (∀ j, 0 ≤ scaleWeight xstar b j x) ∧
      ∑ j ∈ range (k+1), scaleWeight xstar b j x ≤ 1 := by
  have hz := coordinate_nonneg hx hxx hb
  have hp := denominator_positive hz
  constructor
  · intro j
    exact div_nonneg (bump_nonneg _) hp.le
  · obtain ⟨K,hK⟩ := exists_nat_gt (scaleCoordinate xstar b x+2)
    have hs : Summable (fun j : ℕ => scaleBump (scaleCoordinate xstar b x-j)) :=
      (hasSum_sum_of_ne_finset_zero (s := range K) (fun i hi =>
        bump_tail (by linarith) (by simpa using hi))).summable
    simp only [scaleWeight,← sum_div]
    exact (div_le_one hp).mpr (hs.sum_le_tsum _ (fun i _ => bump_nonneg _))

lemma active_ring {xstar x : ℝ} {b j : ℕ}
    (hxstar : 0 < xstar) (hx : 0 < x) (hb : 1 < b)
    (hw : scaleWeight xstar b j x ≠ 0) : ringScale xstar b j / Real.sqrt b ≤ x := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  have hb0 := lt_trans zero_lt_one hbR
  have hlog := Real.log_pos hbR
  have hz : scaleCoordinate xstar b x-j < 1 := by
    by_contra h
    exact hw (by simp [scaleWeight,bump_zero (Or.inr (le_of_not_gt h))])
  have hsqrt : Real.sqrt b = (b : ℝ)^(1/2 : ℝ) := Real.sqrt_eq_rpow _
  have hscale : ringScale xstar b j / Real.sqrt b =
      xstar*(b : ℝ)^(-((j : ℝ)+1)/2) := by
    rw [ringScale,hsqrt,mul_div_assoc,← Real.rpow_sub hb0]
    congr 2
    ring
  rw [hscale]
  have hxexp : xstar/x = Real.exp (Real.log (xstar/x)) := (Real.exp_log (div_pos hxstar hx)).symm
  have hexp : (b : ℝ)^(-((j : ℝ)+1)/2) ≤ x/xstar := by
    rw [Real.rpow_def_of_pos hb0,← Real.exp_log (div_pos hx hxstar)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hx.ne' hxstar.ne']
    dsimp [scaleCoordinate] at hz
    have hh := (div_lt_iff₀ hlog).mp (show 2*Real.log (xstar/x)/Real.log b < j+1 by linarith)
    rw [Real.log_div hxstar.ne' hx.ne'] at hh
    nlinarith
  calc
    xstar*(b : ℝ)^(-((j : ℝ)+1)/2) ≤ xstar*(x/xstar) := mul_le_mul_of_nonneg_left hexp hxstar.le
    _ = x := by field_simp

/-- The original finite lower array, with inactive rings represented by zero. -/
def publicLower (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    (b N : ℕ) (D xstar W β : ℝ) (k t : ℕ) (x : ℝ) : ℝ :=
  (1-W*x^β)/2+W*x^β*∑ j ∈ range (k+1), scaleWeight xstar b j x*
    ringLower (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ))
      (fun q => (reference φ η a d x q : ℂ)) (k-j) t

/-- The original finite upper array, including the unstarted tail mass. -/
def publicUpper (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    (b N : ℕ) (D xstar W β : ℝ) (k t : ℕ) (x : ℝ) : ℝ :=
  (1+W*x^β)/2-W*x^β*∑ j ∈ range (k+1), scaleWeight xstar b j x*
    (1-ringUpper (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ))
      (fun q => (reference φ η a d x q : ℂ)) (k-j) t)

private lemma eventual_width (φ : ℝ → ℝ) (η a d : ℝ) (r : ℕ) (ρ θ : ℝ)
    (b N : ℕ) (D xstar W β x : ℝ) (hb : 1 < b) (hN : 0 < N) (hNr : r ≤ N)
    (hD : 0 ≤ D) (hW : 0 ≤ W) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ)
    (hx : 0 < x) (hxx : x ≤ xstar) :
    ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, K ≤ k → ∀ t ≤ N*b^k+r,
      publicUpper φ η a d r ρ θ b N D xstar W β k t x-
        publicLower φ η a d r ρ θ b N D xstar W β k t x ≤ C*((N*b^k : ℕ) : ℝ)^(-ρ/2) := by
  have hxstar : 0 < xstar := hx.trans_le hxx
  obtain ⟨K,hK⟩ := exists_nat_gt (scaleCoordinate xstar b x+1)
  let v := fun j => scaleWeight xstar b j x
  let A := fun j => 2*D*(ringScale xstar b j)^(-ρ)*(θ+1)
  let S := ∑ j ∈ range K, v j*A j
  have hv := (weight_mass hx hxx hb 0).1
  have hA (j : ℕ) : 0 ≤ A j := by
    have hs : 0 ≤ ringScale xstar b j := by dsimp [ringScale]; positivity
    dsimp [A]; positivity
  have hS : 0 ≤ S := sum_nonneg (fun j _ => mul_nonneg (hv j) (hA j))
  have hw : 0 ≤ W*x^β := mul_nonneg hW (Real.rpow_nonneg hx.le _)
  refine ⟨K,1+W*x^β*S,by positivity,?_⟩
  intro k hk t ht
  have htail (j : ℕ) (hj : K ≤ j) : v j = 0 := by
    dsimp [v,scaleWeight]
    rw [bump_tail hK hj,zero_div]
  have hmass : ∑ j ∈ range (k+1), v j = 1 := by
    dsimp [v,scaleWeight]
    rw [← sum_div,← denominator_finite (by exact hK.trans_le (by exact_mod_cast (show K ≤ k+1 by omega)))]
    exact div_self (denominator_positive (coordinate_nonneg hx hxx hb)).ne'
  have hsum : (∑ j ∈ range (k+1), v j*A j) = S := by
    symm
    apply sum_subset (range_mono (by omega : K ≤ k+1))
    intro j hj hn
    rw [htail j (by simpa using hn),zero_mul]
  let low := fun j => ringLower (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ))
    (fun q => (reference φ η a d x q : ℂ)) (k-j) t
  let upp := fun j => ringUpper (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ))
    (fun q => (reference φ η a d x q : ℂ)) (k-j) t
  have hgap (j : ℕ) (hj : j ∈ range (k+1)) : upp j-low j ≤ A j*((N*b^k : ℕ) : ℝ)^(-ρ/2) := by
    have hjk : j ≤ k := by have := mem_range.mp hj; omega
    have he : (N*b^j)*b^(k-j) = N*b^k := by rw [mul_assoc,← pow_add,Nat.add_sub_of_le hjk]
    have hb0 : 0 < b := by omega
    have hn : 0 < N*b^k := by positivity
    have hrn : r ≤ N*b^k := hNr.trans (Nat.le_mul_of_pos_right N (pow_pos hb0 k))
    have hc := HNPCorrectionLiftAdvantage.correction_uniform_bound hn hrn ht hρ hθ
    have hDj : 0 ≤ D*(ringScale xstar b j)^(-ρ) := by
      have hs : 0 ≤ ringScale xstar b j := by dsimp [ringScale]; positivity
      positivity
    dsimp only [upp,low,ringUpper,ringLower]
    rw [he]
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hDj)]
  calc
    _ = W*x^β*∑ j ∈ range (k+1), v j*(upp j-low j) := by
      change (1+W*x^β)/2-W*x^β*(∑ j ∈ range (k+1), v j*(1-upp j))-
        ((1-W*x^β)/2+W*x^β*(∑ j ∈ range (k+1), v j*low j)) = _
      simp only [mul_sub,mul_one,sum_sub_distrib,hmass]
      ring
    _ ≤ W*x^β*∑ j ∈ range (k+1), v j*(A j*((N*b^k : ℕ) : ℝ)^(-ρ/2)) :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hgap j hj) (hv j))) hw
    _ = (W*x^β*S)*((N*b^k : ℕ) : ℝ)^(-ρ/2) := by
      simp_rw [← mul_assoc]
      rw [← sum_mul,hsum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)

lemma coefficient_smooth {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (η a d : ℝ) (r k D t : ℕ)
    {x : ℝ} (hx : 0 < x) : ContDiffAt ℝ ∞
      (fun y => bernsteinCoefficient D t
        (center τ b r (fun q => (reference φ η a d y q : ℂ)) k)) x := by
  let V : ℝ → Sample τ b r k → ℂ := fun y z => samples τ b
    (fun q => (reference φ η a d y q : ℂ)) z.1.val z.2.1.val z.2.2.val
  have hV : ContDiffAt ℝ ∞ V x := by
    apply contDiffAt_pi.mpr
    intro z
    have hz : (z.2.2.val : ℝ)/(τ*b^z.1.val) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity,(div_le_one (by positivity)).mpr (by exact_mod_cast (show z.2.2.val ≤ τ*b^z.1.val by omega))⟩
    change ContDiffAt ℝ ∞ (fun y => iteratedDerivWithin z.2.1.val
      (fun q => (reference φ η a d y q : ℂ)) (Set.Icc 0 1) ((z.2.2.val : ℝ)/(τ*b^z.1.val))) x
    simp_rw [complex_jet (reference_smooth hφ η a d _) _ hz]
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp x (qjet_scale_smooth hφ η a d _ hx.ne' _)
  apply ContDiffAt.congr_of_eventuallyEq
    ((coefficientFunctional τ b r k D t).contDiff.contDiffAt.comp x hV)
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact (functional_eq hτ hb r k D t
    ((Complex.ofRealCLM.contDiff.comp (reference_smooth hφ η a d y)).contDiffOn.of_le
      (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤)))).symm

private lemma lift_mixture {n d t : ℕ} (hd : d ≤ n) (ht : t ≤ n)
    (a w : ℝ) (s : Finset ℕ) (v : ℕ → ℝ) (f : ℕ → ℕ → ℝ) :
    HNPCorrectionLiftAdvantage.lift n d t (fun i => a+w*∑ j ∈ s, v j*f j i) =
      a+w*∑ j ∈ s, v j*HNPCorrectionLiftAdvantage.lift n d t (f j) := by
  have hw := HNPCorrectionLiftAdvantage.weight_sum hd ht
  unfold HNPCorrectionLiftAdvantage.lift
  simp only [mul_add,sum_add_distrib]
  rw [← sum_mul,hw,one_mul]
  congr 1
  simp only [mul_assoc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro i _
  ring

private lemma lift_complement {n d t : ℕ} (hd : d ≤ n) (ht : t ≤ n) (f : ℕ → ℝ) :
    HNPCorrectionLiftAdvantage.lift n d t (fun i => 1-f i) =
      1-HNPCorrectionLiftAdvantage.lift n d t f := by
  unfold HNPCorrectionLiftAdvantage.lift
  simp only [mul_sub,mul_one,sum_sub_distrib,HNPCorrectionLiftAdvantage.weight_sum hd ht]

/-- One initialization yields the original uninflated public arrays with smooth
positive-scale coefficients and a uniform probability margin. The common
weights are the normalized compact bumps, including their unstarted tail.
No differentiability at the zero scale is asserted. -/
theorem reference_public_array_regular {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) {T β : ℝ} (hT : 0 < T) (hβ : 0 ≤ β)
    (hsχ : tsupport χ ⊆ Set.Ioo 0 T) (hχrange : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (a d : ℝ) (r : ℕ) (ρ θ : ℝ) (hρ : (r : ℝ) < ρ)
    (hρ1 : ρ < (r : ℝ)+1) (hρ2 : 2 ≤ ρ) (hθ : 0 < θ) :
    ∃ B : ℕ, 16 ≤ B ∧ ∀ b : ℕ, B ≤ b →
      ∀ xstar : ℝ, 0 < xstar → xstar ≤ 1 → ∃ D : ℝ, 0 < D ∧
      ∃ N : ℕ, 3*r+2 ≤ N ∧ ∀ W : ℝ, 0 ≤ W → W*xstar^β ≤ 15/16 →
      let lower := publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β
      let upper := publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β
      (∀ k : ℕ, ∀ x : ℝ, 0 < x → x ≤ xstar →
        (∀ t ≤ N*b^k+r, ContDiffAt ℝ ∞ (lower k t) x ∧ ContDiffAt ℝ ∞ (upper k t) x ∧
          (1/32 : ℝ) ≤ lower k t x ∧ lower k t x ≤ upper k t x ∧ upper k t x ≤ 31/32 ∧
          |lower k t x-1/2| ≤ W*x^β/2 ∧ |upper k t x-1/2| ≤ W*x^β/2) ∧
        (∀ t ≤ N*b^(k+1)+r,
          HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun i => lower k i x) ≤ lower (k+1) t x ∧
          upper (k+1) t x ≤ HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun i => upper k i x))) ∧
      (0 < β → ∀ k t : ℕ, t ≤ N*b^k+r →
        ContinuousOn (lower k t) (Set.Icc 0 xstar) ∧
        ContinuousOn (upper k t) (Set.Icc 0 xstar)) ∧
      (∀ x : ℝ, 0 < x → x ≤ xstar → ∃ K : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ k : ℕ, K ≤ k → ∀ t ≤ N*b^k+r,
          (upper k t x-lower k t x ≤ C*((N*b^k : ℕ) : ℝ)^(-ρ/2))) ∧
      (∀ x : ℝ, 0 < x → x ≤ xstar → ∀ ε : ℝ, 0 < ε →
        ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ t ≤ N*b^k+r, upper k t x-lower k t x < ε) := by
  obtain ⟨B,hB,hb⟩ := reference_ring_envelopes hχ hcχ hT hβ hsχ hχrange
    a d r ρ θ hρ hρ1 hρ2 hθ
  refine ⟨B,hB,?_⟩
  intro b hBb xstar hxstar hxstar1
  obtain ⟨D,hD,N,hN,hr⟩ := hb b hBb xstar hxstar
  refine ⟨D,hD,N,hN,?_⟩
  intro W hW hW1
  let lower := publicLower (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β
  let upper := publicUpper (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β
  have hpos :
      ∀ k : ℕ, ∀ x : ℝ, 0 < x → x ≤ xstar →
        (∀ t ≤ N*b^k+r, ContDiffAt ℝ ∞ (lower k t) x ∧ ContDiffAt ℝ ∞ (upper k t) x ∧
          (1/32 : ℝ) ≤ lower k t x ∧ lower k t x ≤ upper k t x ∧ upper k t x ≤ 31/32 ∧
          |lower k t x-1/2| ≤ W*x^β/2 ∧ |upper k t x-1/2| ≤ W*x^β/2) ∧
        (∀ t ≤ N*b^(k+1)+r,
          HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun i => lower k i x) ≤ lower (k+1) t x ∧
          upper (k+1) t x ≤ HNPCorrectionLiftAdvantage.lift (N*b^(k+1)+r) (N*b^k+r) t (fun i => upper k i x)) := by
    intro k x hx hxx
    constructor
    · intro t ht
      have hb1 : 1 < b := by omega
      have hb0 : 0 < b := by omega
      have hN0 : 0 < N := by omega
      have hφ := cutoff_smooth hχ (fun y hy => (hsχ hy).1) β
      let η := 2/(5*T^β)
      let low (j : ℕ) (y : ℝ) := ringLower (N*b^j) b r ρ θ
        (D*(ringScale xstar b j)^(-ρ)) (fun q => (reference (cutoff χ β) η a d y q : ℂ)) (k-j) t
      let upp (j : ℕ) (y : ℝ) := ringUpper (N*b^j) b r ρ θ
        (D*(ringScale xstar b j)^(-ρ)) (fun q => (reference (cutoff χ β) η a d y q : ℂ)) (k-j) t
      have hsm (j : ℕ) : ContDiffAt ℝ ∞ (low j) x ∧ ContDiffAt ℝ ∞ (upp j) x := by
        have hc := Complex.reCLM.contDiff.contDiffAt.comp x
          (coefficient_smooth (by positivity : 0 < N*b^j) hb0 hφ η a d r (k-j) ((N*b^j)*b^(k-j)+r) t hx)
        exact ⟨hc.sub contDiffAt_const,hc.add contDiffAt_const⟩
      have hwsm : ContDiffAt ℝ ∞ (fun y : ℝ => W*y^β) x :=
        contDiffAt_const.mul (contDiffAt_id.rpow_const_of_ne hx.ne')
      refine ⟨?_,?_,?_⟩
      · exact ((contDiffAt_const.sub hwsm).div_const 2).add
          (hwsm.mul (ContDiffAt.sum (fun j _ => (weight_smooth hxstar hx hxx hb1 j).mul (hsm j).1)))
      · exact ((contDiffAt_const.add hwsm).div_const 2).sub
          (hwsm.mul (ContDiffAt.sum (fun j _ => (weight_smooth hxstar hx hxx hb1 j).mul
            (contDiffAt_const.sub (hsm j).2))))
      have hm := weight_mass hx hxx hb1 k
      have hpair (j : ℕ) (hj : j ∈ range (k+1)) :
          0 ≤ scaleWeight xstar b j x*low j x ∧
          0 ≤ scaleWeight xstar b j x*(1-upp j x) ∧
          scaleWeight xstar b j x*low j x+scaleWeight xstar b j x*(1-upp j x) ≤ scaleWeight xstar b j x := by
        by_cases hw : scaleWeight xstar b j x = 0
        · simp [hw]
        have hjk : j ≤ k := by have := mem_range.mp hj; omega
        have he : (N*b^j)*b^(k-j)+r = N*b^k+r := by
          rw [mul_assoc,← pow_add,Nat.add_sub_of_le hjk]
        have ht' : t ≤ (N*b^j)*b^(k-j)+r := by rwa [he]
        have hh := (hr j x hx (hxx.trans hxstar1) (active_ring hxstar hx hb1 hw) (k-j)).1 t ht'
        change (9/20 : ℝ) ≤ low j x ∧ low j x ≤ upp j x ∧ upp j x ≤ 19/20 at hh
        refine ⟨mul_nonneg (hm.1 j) (by linarith),mul_nonneg (hm.1 j) (by linarith),?_⟩
        nlinarith [mul_nonneg (hm.1 j) (sub_nonneg.mpr hh.2.1)]
      have hSL := sum_nonneg (fun j hj => (hpair j hj).1)
      have hSU := sum_nonneg (fun j hj => (hpair j hj).2.1)
      have hsum : (∑ j ∈ range (k+1), scaleWeight xstar b j x*low j x)+
          (∑ j ∈ range (k+1), scaleWeight xstar b j x*(1-upp j x)) ≤ 1 := by
        rw [← sum_add_distrib]
        exact (sum_le_sum (fun j hj => (hpair j hj).2.2)).trans hm.2
      have hw0 : 0 ≤ W*x^β := mul_nonneg hW (Real.rpow_nonneg hx.le _)
      have hw1 : W*x^β ≤ 15/16 := (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxx hβ) hW).trans hW1
      change (1/32 : ℝ) ≤ (1-W*x^β)/2+W*x^β*(∑ j ∈ range (k+1), scaleWeight xstar b j x*low j x) ∧
        (1-W*x^β)/2+W*x^β*(∑ j ∈ range (k+1), scaleWeight xstar b j x*low j x) ≤
          (1+W*x^β)/2-W*x^β*(∑ j ∈ range (k+1), scaleWeight xstar b j x*(1-upp j x)) ∧
        (1+W*x^β)/2-W*x^β*(∑ j ∈ range (k+1), scaleWeight xstar b j x*(1-upp j x)) ≤ 31/32 ∧
      |(1-W*x^β)/2+W*x^β*(∑ j ∈ range (k+1), scaleWeight xstar b j x*low j x)-1/2| ≤ W*x^β/2 ∧
      |(1+W*x^β)/2-W*x^β*(∑ j ∈ range (k+1), scaleWeight xstar b j x*(1-upp j x))-1/2| ≤ W*x^β/2
      constructor
      · nlinarith [mul_nonneg hw0 hSL]
      constructor
      · nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hsum)]
      constructor
      · nlinarith [mul_nonneg hw0 hSU]
      constructor <;> rw [abs_le] <;> constructor <;>
        nlinarith [mul_nonneg hw0 hSL,mul_nonneg hw0 hSU,mul_nonneg hw0 (sub_nonneg.mpr hsum)]
    · intro t ht
      have hb0 : 0 < b := by omega
      have hb1 : 1 < b := by omega
      have hd : N*b^k+r ≤ N*b^(k+1)+r := Nat.add_le_add_right
        (Nat.mul_le_mul_left N (Nat.pow_le_pow_right hb0 (by omega))) r
      let old := N*b^k+r
      let next := N*b^(k+1)+r
      let v := fun j => scaleWeight xstar b j x
      let f := fun q => (reference (cutoff χ β) (2/(5*T^β)) a d x q : ℂ)
      let lo (j l i : ℕ) := ringLower (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ)) f (l-j) i
      let up (j l i : ℕ) := ringUpper (N*b^j) b r ρ θ (D*(ringScale xstar b j)^(-ρ)) f (l-j) i
      have hm := weight_mass hx hxx hb1 k
      have hjoint (j : ℕ) (hj : j ∈ range (k+1)) :
          v j*HNPCorrectionLiftAdvantage.lift next old t (lo j k) ≤ v j*lo j (k+1) t ∧
          v j*HNPCorrectionLiftAdvantage.lift next old t (fun i => 1-up j k i) ≤ v j*(1-up j (k+1) t) := by
        by_cases hv : v j = 0
        · simp [hv]
        have hjk : j ≤ k := by have := mem_range.mp hj; omega
        have hko : (N*b^j)*b^(k-j)+r = old := by
          dsimp [old]; rw [mul_assoc,← pow_add,Nat.add_sub_of_le hjk]
        have hkn : (N*b^j)*b^(k-j+1)+r = next := by
          dsimp [next]; rw [mul_assoc,← pow_add,show j+(k-j+1)=k+1 by omega]
        have hh := (hr j x hx (hxx.trans hxstar1) (active_ring hxstar hx hb1 hv) (k-j)).2 t (by rwa [hkn])
        have hs : k-j+1=k+1-j := by omega
        rw [hko,hkn,hs] at hh
        change HNPCorrectionLiftAdvantage.lift next old t (lo j k) ≤ lo j (k+1) t ∧
          up j (k+1) t ≤ HNPCorrectionLiftAdvantage.lift next old t (up j k) at hh
        refine ⟨mul_le_mul_of_nonneg_left hh.1 (hm.1 j),?_⟩
        rw [lift_complement hd ht]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_left hh.2 1) (hm.1 j)
      have hnew : 0 ≤ v (k+1)*lo (k+1) (k+1) t ∧ 0 ≤ v (k+1)*(1-up (k+1) (k+1) t) := by
        by_cases hv : v (k+1) = 0
        · simp [hv]
        have hh := (hr (k+1) x hx (hxx.trans hxstar1) (active_ring hxstar hx hb1 hv) 0).1 t (by simpa using ht)
        have hh' : (9/20 : ℝ) ≤ lo (k+1) (k+1) t ∧ lo (k+1) (k+1) t ≤ up (k+1) (k+1) t ∧ up (k+1) (k+1) t ≤ 19/20 := by
          simpa only [lo,up,Nat.sub_self,f] using hh
        rcases hh' with ⟨ha,hab,hb⟩
        exact ⟨mul_nonneg (hm.1 _) (by linarith),mul_nonneg (hm.1 _) (by linarith)⟩
      have hLS : (∑ j ∈ range (k+1), v j*HNPCorrectionLiftAdvantage.lift next old t (lo j k)) ≤
          ∑ j ∈ range (k+1+1), v j*lo j (k+1) t := by
        rw [sum_range_succ (n := k+1)]
        exact (sum_le_sum (fun j hj => (hjoint j hj).1)).trans (le_add_of_nonneg_right hnew.1)
      have hUS : (∑ j ∈ range (k+1), v j*HNPCorrectionLiftAdvantage.lift next old t (fun i => 1-up j k i)) ≤
          ∑ j ∈ range (k+1+1), v j*(1-up j (k+1) t) := by
        rw [sum_range_succ (n := k+1)]
        exact (sum_le_sum (fun j hj => (hjoint j hj).2)).trans (le_add_of_nonneg_right hnew.2)
      have hw : 0 ≤ W*x^β := mul_nonneg hW (Real.rpow_nonneg hx.le _)
      constructor
      · change HNPCorrectionLiftAdvantage.lift next old t
          (fun i => (1-W*x^β)/2+W*x^β*∑ j ∈ range (k+1), v j*lo j k i) ≤ _
        rw [lift_mixture hd ht]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hLS hw)
      · change _ ≤ HNPCorrectionLiftAdvantage.lift next old t
          (fun i => (1+W*x^β)/2-W*x^β*∑ j ∈ range (k+1), v j*(1-up j k i))
        simp_rw [sub_eq_add_neg,← neg_mul]
        rw [lift_mixture hd ht]
        simpa only [upper,publicUpper,sub_eq_add_neg,neg_mul,up,v,f,old,next] using
        add_le_add (le_refl ((1+W*x^β)/2)) (mul_le_mul_of_nonpos_left hUS (neg_nonpos.mpr hw))
  refine ⟨hpos,?_,?_,?_⟩
  · intro hβ0 k t ht
    have hzL : lower k t 0 = 1/2 := by simp [lower,publicLower,Real.zero_rpow hβ0.ne']
    have hzU : upper k t 0 = 1/2 := by simp [upper,publicUpper,Real.zero_rpow hβ0.ne']
    have hc0 (A : ℝ → ℝ) (hA0 : A 0 = 1/2)
        (hA : ∀ x : ℝ, 0 < x → x ≤ xstar → |A x-1/2| ≤ W*x^β/2) :
        ContinuousWithinAt A (Set.Icc 0 xstar) 0 := by
      rw [ContinuousWithinAt,hA0,tendsto_iff_norm_sub_tendsto_zero]
      have hbnd : Tendsto (fun x : ℝ => W*x^β/2) (𝓝[Set.Icc 0 xstar] 0) (𝓝 0) := by
        have hc : ContinuousAt (fun x : ℝ => W*x^β/2) 0 :=
          (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inr hβ0.le))).div_const 2
        simpa [Real.zero_rpow hβ0.ne'] using hc.tendsto.mono_left nhdsWithin_le_nhds
      apply squeeze_zero' (Eventually.of_forall (fun x => norm_nonneg _)) _ hbnd
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [Real.norm_eq_abs]
      rcases eq_or_lt_of_le hx.1 with he | he
      · subst x
        simp [hA0,Real.zero_rpow hβ0.ne']
      · exact hA x he hx.2
    have hLc := hc0 _ hzL (fun x hx hxx => ((hpos k x hx hxx).1 t ht).2.2.2.2.2.1)
    have hUc := hc0 _ hzU (fun x hx hxx => ((hpos k x hx hxx).1 t ht).2.2.2.2.2.2)
    constructor <;> intro x hx
    · rcases eq_or_lt_of_le hx.1 with he | he
      · simpa [← he] using hLc
      · exact (((hpos k x he hx.2).1 t ht).1).continuousAt.continuousWithinAt
    · rcases eq_or_lt_of_le hx.1 with he | he
      · simpa [← he] using hUc
      · exact (((hpos k x he hx.2).1 t ht).2.1).continuousAt.continuousWithinAt
  · intro x hx hxx
    exact eventual_width (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β x
      (by omega) (by omega) (by omega)
      hD.le hW (by linarith) hθ.le hx hxx
  · intro x hx hxx ε hε
    obtain ⟨K,C,hC,hbound⟩ := eventual_width (cutoff χ β) (2/(5*T^β)) a d r ρ θ b N D xstar W β x
      (by omega) (by omega) (by omega) hD.le hW (by linarith) hθ.le hx hxx
    have hn : Tendsto (fun k : ℕ => ((N*b^k : ℕ) : ℝ)) atTop atTop := by
      simp only [Nat.cast_mul,Nat.cast_pow]
      exact (tendsto_const_mul_atTop_of_pos (by exact_mod_cast (show 0 < N by omega))).mpr
        (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (show 1 < b by omega)))
    have hlim : Tendsto (fun k : ℕ => C*((N*b^k : ℕ) : ℝ)^(-ρ/2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,neg_div,mul_zero] using
        ((tendsto_rpow_neg_atTop (by linarith : 0 < ρ/2)).comp hn).const_mul C
    obtain ⟨K',hK'⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
    exact ⟨max K K',fun k hk t ht => (hbound k ((le_max_left _ _).trans hk) t ht).trans_lt
      (hK' k ((le_max_right _ _).trans hk))⟩
end D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
