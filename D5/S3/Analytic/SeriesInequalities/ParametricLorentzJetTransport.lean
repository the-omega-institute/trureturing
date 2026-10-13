/- GID: D5/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport
   generality: G
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/ParametricLorentzJetTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Parameter jets of the actual finite Lorentz center history. -/

import D5.S3.Analytic.SeriesInequalities.HNPCorrectionLiftAdvantage
import Mathlib.Analysis.Normed.Module.FiniteDimension

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



private lemma linear_iterated {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

private lemma reference_transport {τ b : ℕ} (hτ : 0 < τ) (hb : 0 < b)
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

end D5.S3.Analytic.SeriesInequalities.ParametricLorentzJetTransport
