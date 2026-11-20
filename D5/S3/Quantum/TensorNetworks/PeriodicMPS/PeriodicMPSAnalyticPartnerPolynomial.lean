/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticPartnerPolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSAnalyticPartnerPolynomial
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.FDeriv.Analytic]
   utility: none
   digest: Dividing odd and even polynomial rows by their leading powers gives an even analytic system with a local solution at a certified simple zero. -/
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Polynomial.Eval.Degree

/-! Polynomial rescaling and analytic inversion at a simple reduced root. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSAnalyticPartnerPolynomial

open Filter Polynomial Asymptotics
open scoped Topology

noncomputable section

abbrev Imaginary := Fin 3 → ℝ
abbrev RealRegular := Fin 4 → ℝ
/-- The parameters are `(β, γ, δ)`, `(a₂, b₂, c₂, d₂)`, and `t`. -/
abbrev Parameters := Imaginary × RealRegular × ℝ
/-- The residuals are the three imaginary rows, four real regular rows, and `h`. -/
abbrev Rows := Fin 3 ⊕ (Fin 4 ⊕ Unit)

/-- A polynomial in ε with coefficient functions of the eight chart parameters. -/
abbrev Family := Polynomial (Parameters → ℝ)

def evaluate (p : Family) (ε : ℝ) (w : Parameters) : ℝ :=
  p.eval₂ (Pi.evalRingHom _ w) ε

def order : Rows → ℕ
  | .inl _ => 1
  | .inr _ => 2

def shift (k : ℕ) (p : Family) : Family := k.iterate Polynomial.divX p

def scaled (p : Rows → Family) (q : ℝ × Parameters) : Parameters :=
  (fun i => evaluate (shift 1 (p (.inl i))) q.1 q.2,
   fun i => evaluate (shift 2 (p (.inr (.inl i)))) q.1 q.2,
   evaluate (shift 2 (p (.inr (.inr ())))) q.1 q.2)

@[simp] theorem evaluate_zero (p : Family) (w : Parameters) :
    evaluate p 0 w = p.coeff 0 w := by simp [evaluate]

@[simp] theorem scaled_zero (p : Rows → Family) (w : Parameters) :
    scaled p (0, w) =
      (fun i => (p (.inl i)).coeff 1 w,
       fun i => (p (.inr (.inl i))).coeff 2 w,
       (p (.inr (.inr ()))).coeff 2 w) := by
  simp [scaled, shift, Function.iterate_succ_apply', coeff_divX]

theorem analyticAt_evaluate (p : Family) (q : ℝ × Parameters)
    (ha : ∀ k, AnalyticAt ℝ (p.coeff k) q.2) :
    AnalyticAt ℝ (fun q : ℝ × Parameters => evaluate p q.1 q.2) q := by
  simp only [evaluate, eval₂_eq_sum_range, Pi.evalRingHom_apply]
  apply Finset.analyticAt_fun_sum
  intro i _
  exact ((ha i).comp ((ContinuousLinearMap.snd ℝ ℝ Parameters).analyticAt q)).mul
    (((ContinuousLinearMap.fst ℝ ℝ Parameters).analyticAt q).pow i)

theorem analyticAt_scaled (p : Rows → Family) (q : ℝ × Parameters)
    (ha : ∀ i k, AnalyticAt ℝ ((p i).coeff k) q.2) :
    AnalyticAt ℝ (scaled p) q := by
  have h (i : Rows) : AnalyticAt ℝ
      (fun a : ℝ × Parameters => evaluate (shift (order i) (p i)) a.1 a.2) q := by
    apply analyticAt_evaluate
    intro k
    rcases i with i | i
    · simpa [order, shift, Function.iterate_succ_apply', coeff_divX] using ha (.inl i) (k + 1)
    · simpa [order, shift, Function.iterate_succ_apply', coeff_divX] using ha (.inr i) (k + 1 + 1)
  exact (AnalyticAt.pi fun i => h (.inl i)).prod
    ((AnalyticAt.pi fun i => h (.inr (.inl i))).prod (h (.inr (.inr ()))))

private theorem coeff_one_of_even (p : Family) (w : Parameters)
    (h : ∀ ε, evaluate p (-ε) w = evaluate p ε w) : p.coeff 1 w = 0 := by
  let q := p.map (Pi.evalRingHom (fun _ : Parameters => ℝ) w)
  have hd : HasDerivAt (fun ε => evaluate p ε w) (p.coeff 1 w) 0 := by
    simpa [q, evaluate, eval_map, ← coeff_zero_eq_eval_zero, coeff_derivative] using q.hasDerivAt 0
  have hd₀ : HasDerivAt (fun ε => evaluate p ε w) (p.coeff 1 w) (-id (0 : ℝ)) := by simpa using hd
  have hd' := hd₀.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg)
  have he : HasDerivAt (fun ε => evaluate p ε w) (-p.coeff 1 w) 0 := by
    simpa [Function.comp_def, h] using hd'
  linarith [hd.unique he]

/-- Exact rescaling follows from the vanishing constant terms and evenness of the real rows. -/
theorem evaluate_eq_pow_mul (p : Rows → Family)
    (hz : ∀ i w, evaluate (p i) 0 w = 0)
    (he : ∀ i w ε, evaluate (p (.inr i)) (-ε) w = evaluate (p (.inr i)) ε w)
    (i : Rows) (w : Parameters) (ε : ℝ) :
    evaluate (p i) ε w = ε ^ order i * evaluate (shift (order i) (p i)) ε w := by
  have step (r : Family) (hr : r.coeff 0 w = 0) :
      evaluate r ε w = ε * evaluate r.divX ε w := by
    have H := congrArg (fun q : Family => evaluate q ε w) (X_mul_divX_add r)
    simpa only [evaluate, eval₂_add, eval₂_mul, eval₂_X, eval₂_C, Pi.evalRingHom_apply,
      hr, add_zero] using H.symm
  cases i with
  | inl i => simpa [order, shift] using step (p (.inl i)) (by simpa using hz (.inl i) w)
  | inr i =>
    have h₁ : (p (.inr i)).divX.coeff 0 w = 0 := by
      simpa [coeff_divX] using coeff_one_of_even (p (.inr i)) w (he i w)
    rw [step (p (.inr i)) (by simpa using hz (.inr i) w), step _ h₁]
    simp [order, shift, Function.iterate_succ_apply', pow_two, mul_assoc]

/-- The scaled system is even, including at ε = 0. -/
theorem scaled_neg (p : Rows → Family)
    (hz : ∀ i w, evaluate (p i) 0 w = 0)
    (ho : ∀ i w ε, evaluate (p (.inl i)) (-ε) w = -evaluate (p (.inl i)) ε w)
    (he : ∀ i w ε, evaluate (p (.inr i)) (-ε) w = evaluate (p (.inr i)) ε w)
    (ε : ℝ) (w : Parameters) : scaled p (-ε, w) = scaled p (ε, w) := by
  by_cases h : ε = 0
  · simp [h]
  have hi (i : Fin 3) :
      evaluate (shift 1 (p (.inl i))) (-ε) w = evaluate (shift 1 (p (.inl i))) ε w := by
    have H := ho i w ε
    rw [evaluate_eq_pow_mul p hz he (.inl i) w (-ε),
      evaluate_eq_pow_mul p hz he (.inl i) w ε] at H
    simp only [order, pow_one, neg_mul, neg_inj] at H
    exact mul_left_cancel₀ h H
  have hr (i : Fin 4 ⊕ Unit) :
      evaluate (shift 2 (p (.inr i))) (-ε) w = evaluate (shift 2 (p (.inr i))) ε w := by
    have H := he i w ε
    rw [evaluate_eq_pow_mul p hz he (.inr i) w (-ε),
      evaluate_eq_pow_mul p hz he (.inr i) w ε] at H
    simp only [order, neg_sq] at H
    exact mul_left_cancel₀ (pow_ne_zero _ h) H
  exact Prod.ext (funext hi) (Prod.ext (funext fun i => hr (.inl i)) (hr (.inr ())))

/-- A certificate for the two regular blocks and the eliminated coherence equation.
`eliminate t` gives the seven regular parameters after eliminating at fixed `t`.
The scalar `scale` absorbs the nonzero normalization factors in the leading system. -/
structure LeadingCertificate (g : Parameters → Parameters) (w : Parameters) where
  imagBlock : Imaginary →L[ℝ] Imaginary
  realBlock : RealRegular →L[ℝ] RealRegular
  imag_inj : Function.Injective imagBlock
  real_inj : Function.Injective realBlock
  imag_deriv : HasFDerivAt (fun u : Imaginary × RealRegular => (g (u.1, u.2, w.2.2)).1)
    (imagBlock.comp (ContinuousLinearMap.fst ℝ Imaginary RealRegular)) (w.1, w.2.1)
  real_deriv : HasFDerivAt (fun v : RealRegular => (g (w.1, v, w.2.2)).2.1)
    realBlock w.2.1
  eliminate : ℝ → Imaginary × RealRegular
  tangent : Imaginary × RealRegular
  eliminate_deriv : HasDerivAt eliminate tangent w.2.2
  eliminate_at : eliminate w.2.2 = (w.1, w.2.1)
  scale : ℝ
  A : ℝ
  B : ℝ
  scale_ne : scale ≠ 0
  A_ne : A ≠ 0
  root : w.2.2 = -B / A
  other_root : w.2.2 ≠ 1
  reduced : ∀ᶠ t in 𝓝 w.2.2, g ((eliminate t).1, (eliminate t).2, t) =
    (0, 0, scale * ((t - 1) * (A * t + B)))

private theorem LeadingCertificate.root_eq {g : Parameters → Parameters} {w : Parameters}
    (c : LeadingCertificate g w) : c.A * w.2.2 + c.B = 0 := by
  rw [c.root]
  field_simp [c.A_ne]
  ring

/-- Block elimination proves bijectivity. The tangent to the eliminated curve
tests the Schur complement on a vector with last coordinate one. -/
theorem LeadingCertificate.invertible {g : Parameters → Parameters} {w : Parameters}
    (c : LeadingCertificate g w) (hg : AnalyticAt ℝ g w) :
    g w = 0 ∧ ∃ L : Parameters ≃L[ℝ] Parameters,
      HasFDerivAt g (L : Parameters →L[ℝ] Parameters) w := by
  have hz := c.reduced.self_of_nhds
  rw [c.eliminate_at, c.root_eq] at hz
  have hzero : g w = 0 := by
    change g w = (0, 0, 0)
    simpa using hz
  let D := fderiv ℝ g w
  have hD : HasFDerivAt g D w := hg.differentiableAt.hasFDerivAt
  have hi (u : Imaginary) (v : RealRegular) : (D (u, v, 0)).1 = c.imagBlock u := by
    let J : (Imaginary × RealRegular) →L[ℝ] Parameters :=
      (ContinuousLinearMap.fst ℝ Imaginary RealRegular).prod
        ((ContinuousLinearMap.snd ℝ Imaginary RealRegular).prod 0)
    have hJ : HasFDerivAt (fun a : Imaginary × RealRegular => (a.1, a.2, w.2.2))
        J (w.1, w.2.1) := by
      simpa [J] using (ContinuousLinearMap.fst ℝ Imaginary RealRegular).hasFDerivAt.prodMk
        ((ContinuousLinearMap.snd ℝ Imaginary RealRegular).hasFDerivAt.prodMk
          (hasFDerivAt_const (w.1, w.2.1) (c := w.2.2)))
    have H := (hD.comp (w.1, w.2.1) hJ).fst
    exact congrArg (fun L : (Imaginary × RealRegular) →L[ℝ] Imaginary => L (u, v))
      (H.fderiv.symm.trans c.imag_deriv.fderiv)
  have hr (v : RealRegular) : (D (0, v, 0)).2.1 = c.realBlock v := by
    let J : RealRegular →L[ℝ] Parameters := (0 : RealRegular →L[ℝ] Imaginary).prod
      ((ContinuousLinearMap.id ℝ RealRegular).prod 0)
    have hJ : HasFDerivAt (fun v : RealRegular => (w.1, v, w.2.2)) J w.2.1 := by
      simpa [J] using (hasFDerivAt_const w.2.1 (c := w.1)).prodMk
        ((hasFDerivAt_id w.2.1).prodMk (hasFDerivAt_const w.2.1 (c := w.2.2)))
    have H := (hD.comp w.2.1 hJ).snd.fst
    exact congrArg (fun L : RealRegular →L[ℝ] RealRegular => L v)
      (H.fderiv.symm.trans c.real_deriv.fderiv)
  let T : Parameters := (c.tangent.1, c.tangent.2, 1)
  let d := c.scale * ((w.2.2 - 1) * c.A)
  have hd : d ≠ 0 := mul_ne_zero c.scale_ne (mul_ne_zero (sub_ne_zero.mpr c.other_root) c.A_ne)
  have hT : D T = (0, 0, d) := by
    have hEl : HasDerivAt (fun t => ((c.eliminate t).1, (c.eliminate t).2, t)) T w.2.2 :=
      c.eliminate_deriv.fst.prodMk (c.eliminate_deriv.snd.prodMk (hasDerivAt_id _))
    have hAt : ((c.eliminate w.2.2).1, (c.eliminate w.2.2).2, w.2.2) = w := by
      simp [c.eliminate_at]
    have he : (fun t => g ((c.eliminate t).1, (c.eliminate t).2, t)) =ᶠ[𝓝 w.2.2]
        (fun t => (0, 0, c.scale * ((t - 1) * (c.A * t + c.B)))) := c.reduced
    have H := (hD.comp_hasDerivAt_of_eq w.2.2 hEl hAt.symm).congr_of_eventuallyEq he.symm
    have hq : HasDerivAt (fun t => c.scale * ((t - 1) * (c.A * t + c.B))) d w.2.2 := by
      simpa [d, c.root_eq] using (((hasDerivAt_id w.2.2).sub_const 1).mul
        (((hasDerivAt_id w.2.2).const_mul c.A).add_const c.B)).const_mul c.scale
    have hVec : HasDerivAt (fun t => (0, 0, c.scale * ((t - 1) * (c.A * t + c.B))))
        ((0, 0, d) : Parameters) w.2.2 :=
      (hasDerivAt_const _ (0 : Imaginary)).prodMk
        ((hasDerivAt_const _ (0 : RealRegular)).prodMk hq)
    exact H.unique hVec
  have hker : ∀ x : Parameters, D x = 0 → x = 0 := by
    rintro ⟨u, v, t⟩ hx
    let y : Parameters := (u, v, t) - t • T
    have hy : y.2.2 = 0 := by simp [y, T]
    have hDy : D y = -(t • (0, 0, d) : Parameters) := by
      simp [y, hx, hT]
    have hy' : y = (y.1, y.2.1, 0) := Prod.ext rfl (Prod.ext rfl hy)
    have hu : y.1 = 0 := by
      apply c.imag_inj
      rw [← hi y.1 y.2.1, ← hy', hDy]
      simp
    have hy'' : y = (0, y.2.1, 0) := Prod.ext hu (Prod.ext rfl hy)
    have hv : y.2.1 = 0 := by
      apply c.real_inj
      rw [← hr y.2.1, ← hy'', hDy]
      simp
    have hY : y = 0 := Prod.ext hu (Prod.ext hv hy)
    have ht : t = 0 := by
      have H := congrArg (fun x : Parameters => x.2.2) hDy
      simp [hY, smul_eq_mul] at H
      exact H.resolve_right hd
    simpa [y, ht] using hY
  have hinj : Function.Injective D := by
    intro x y h
    apply sub_eq_zero.mp
    exact hker _ (by rw [map_sub, h, sub_self])
  have hsurj : Function.Surjective D := LinearMap.injective_iff_surjective.mp hinj
  let L := (LinearEquiv.ofBijective D.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨hzero, L, hD⟩

/-- Ordinary analytic inversion gives the unique solution germ. Reflection of
the parameter preserves the equations, so the solution germ is even. -/
theorem exists_even_solution {S : ℝ × Parameters → Parameters} {w₀ : Parameters}
    (ha : AnalyticAt ℝ S (0, w₀)) (hz : S (0, w₀) = 0)
    (he : ∀ ε w, S (-ε, w) = S (ε, w))
    (L : Parameters ≃L[ℝ] Parameters)
    (hL : HasFDerivAt (fun w => S (0, w)) (L : Parameters →L[ℝ] Parameters) w₀) :
    ∃ w : ℝ → Parameters, w 0 = w₀ ∧ AnalyticAt ℝ w 0 ∧
      (∀ᶠ ε in 𝓝 0, S (ε, w ε) = 0) ∧
      ((fun ε => w (-ε)) =ᶠ[𝓝 0] w) ∧
      ∀ v : ℝ → Parameters, v 0 = w₀ → ContinuousAt v 0 →
        (∀ᶠ ε in 𝓝 0, S (ε, v ε) = 0) → v =ᶠ[𝓝 0] w := by
  let F : ℝ × Parameters → ℝ × Parameters := fun a => (a.1, S a)
  let J : Parameters →L[ℝ] ℝ × Parameters := (0 : Parameters →L[ℝ] ℝ).prod (.id ℝ Parameters)
  let D := (ContinuousLinearMap.fst ℝ ℝ Parameters).prod (fderiv ℝ S (0, w₀))
  have hD : HasFDerivAt F D (0, w₀) :=
    (ContinuousLinearMap.fst ℝ ℝ Parameters).hasFDerivAt.prodMk ha.differentiableAt.hasFDerivAt
  have hS : ∀ v, fderiv ℝ S (0, w₀) (0, v) = L v := by
    intro v
    have H := ha.differentiableAt.hasFDerivAt.comp w₀ (J.hasFDerivAt (x := w₀))
    exact congrArg (fun K : Parameters →L[ℝ] Parameters => K v) (H.fderiv.symm.trans hL.fderiv)
  have hker : ∀ a, D a = 0 → a = 0 := by
    rintro ⟨ε, v⟩ h
    have hε : ε = 0 := congrArg Prod.fst h
    subst ε
    have hv : L v = 0 := (hS v).symm.trans (congrArg Prod.snd h)
    exact Prod.ext rfl (L.injective (hv.trans L.map_zero.symm))
  have hj : Function.Injective D := by
    intro a b h
    exact sub_eq_zero.mp (hker _ (by rw [map_sub, h, sub_self]))
  let K := (LinearEquiv.ofBijective D.toLinearMap
    ⟨hj, LinearMap.injective_iff_surjective.mp hj⟩).toContinuousLinearEquiv
  have hK : HasFDerivAt F (K : (ℝ × Parameters) →L[ℝ] _) (0, w₀) := hD
  have hF : AnalyticAt ℝ F (0, w₀) :=
    ((ContinuousLinearMap.fst ℝ ℝ Parameters).analyticAt _).prod ha
  have hD' := hF.hasStrictFDerivAt
  rw [hK.fderiv] at hD'
  let e := hD'.toOpenPartialHomeomorph F
  have hx : (0, w₀) ∈ e.source := hD'.mem_toOpenPartialHomeomorph_source
  have ht : F (0, w₀) ∈ e.target := hD'.image_mem_toOpenPartialHomeomorph_target
  have hval : F (0, w₀) = (0, 0) := Prod.ext rfl hz
  have hi : AnalyticAt ℝ e.symm (F (0, w₀)) :=
    e.analyticAt_symm' hx hF (i := K) hK.fderiv
  let f : ℝ → ℝ × Parameters := fun ε => e.symm (ε, 0)
  let w : ℝ → Parameters := fun ε => (f ε).2
  have hf : AnalyticAt ℝ f 0 := hi.comp_of_eq (analyticAt_id.prod analyticAt_const) hval.symm
  have hw : AnalyticAt ℝ w 0 := ((ContinuousLinearMap.snd ℝ ℝ Parameters).analyticAt _).comp hf
  have hw₀ : w 0 = w₀ := by
    change (e.symm (0, 0)).2 = w₀
    rw [← hval]
    exact congrArg Prod.snd (e.left_inv hx)
  have ht' : ∀ᶠ ε : ℝ in 𝓝 0, (ε, (0 : Parameters)) ∈ e.target :=
    (continuous_id.prodMk continuous_const).continuousAt
      (e.open_target.mem_nhds (hval ▸ ht))
  have hs : ∀ᶠ ε in 𝓝 0, S (ε, w ε) = 0 := by
    filter_upwards [ht'] with ε hε
    have H : F (f ε) = (ε, 0) := e.right_inv hε
    have hfst : (f ε).1 = ε := congrArg Prod.fst H
    have heq : (ε, w ε) = f ε := Prod.ext hfst.symm rfl
    rw [heq]
    exact congrArg Prod.snd H
  have hu (v : ℝ → Parameters) (hv₀ : v 0 = w₀) (hv : ContinuousAt v 0)
      (h : ∀ᶠ ε in 𝓝 0, S (ε, v ε) = 0) : v =ᶠ[𝓝 0] w := by
    have hvx : ((0 : ℝ), v 0) ∈ e.source := by rwa [hv₀]
    have hmem : ∀ᶠ ε : ℝ in 𝓝 0, (ε, v ε) ∈ e.source :=
      (continuousAt_id.prodMk hv) (e.open_source.mem_nhds hvx)
    filter_upwards [h, hmem] with ε hε hmem
    have H : e (ε, v ε) = (ε, 0) := Prod.ext rfl hε
    exact congrArg Prod.snd (H ▸ e.left_inv hmem).symm
  have hn : Tendsto (fun ε : ℝ => -ε) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.continuousAt (x := (0 : ℝ))).tendsto
  have hneg : ContinuousAt (fun ε : ℝ => w (-ε)) 0 := by
    change Tendsto _ _ (𝓝 (w (-0)))
    rw [neg_zero]
    exact hw.continuousAt.tendsto.comp hn
  refine ⟨w, hw₀, hw, hs, hu (fun ε => w (-ε)) (by simpa using hw₀) hneg ?_, hu⟩
  filter_upwards [hn.eventually hs] with ε hε
  exact (he ε (w (-ε))).symm.trans hε

/-- Polynomial rescaling and the reduced root certificate give an exact even
parameter germ for the original eight equations. -/
theorem exists_polynomial_partner (p : Rows → Family) (w₀ : Parameters)
    (ha : ∀ i k, AnalyticAt ℝ ((p i).coeff k) w₀)
    (hz : ∀ i w, evaluate (p i) 0 w = 0)
    (ho : ∀ i w ε, evaluate (p (.inl i)) (-ε) w = -evaluate (p (.inl i)) ε w)
    (he : ∀ i w ε, evaluate (p (.inr i)) (-ε) w = evaluate (p (.inr i)) ε w)
    (cert : LeadingCertificate (fun w => scaled p (0, w)) w₀) :
    ∃ w : ℝ → Parameters, w 0 = w₀ ∧ AnalyticAt ℝ w 0 ∧
      ((fun ε => w (-ε)) =ᶠ[𝓝 0] w) ∧
      ∀ᶠ ε in 𝓝 0, ∀ i, evaluate (p i) ε (w ε) = 0 := by
  have hs := analyticAt_scaled p (0, w₀) ha
  have hslice : AnalyticAt ℝ (fun w => scaled p (0, w)) w₀ :=
    hs.comp (analyticAt_const.prod analyticAt_id)
  obtain ⟨hzero, L, hL⟩ := cert.invertible hslice
  obtain ⟨w, hw₀, hw, hwS, heven, _⟩ := exists_even_solution hs hzero (scaled_neg p hz ho he) L hL
  refine ⟨w, hw₀, hw, heven, ?_⟩
  filter_upwards [hwS] with ε hε i
  have hx : evaluate (shift (order i) (p i)) ε (w ε) = 0 := by
    rcases i with i | i
    · exact congrFun (congrArg Prod.fst hε) i
    rcases i with i | ⟨⟩
    · exact congrFun (congrArg (fun a : Parameters => a.2.1) hε) i
    · exact congrArg (fun a : Parameters => a.2.2) hε
  rw [evaluate_eq_pow_mul p hz he, hx, mul_zero]

/-- The coefficient of ε² in the convergent series is the only parameter
correction needed to lift the chart through degree four. -/
theorem even_taylor_two {w : ℝ → Parameters} (hw : AnalyticAt ℝ w 0)
    (he : (fun ε => w (-ε)) =ᶠ[𝓝 0] w) :
    ∃ w₂ : Parameters, (fun ε : ℝ => w ε - (w 0 + ε ^ 2 • w₂)) =O[𝓝 0]
      (fun ε => ‖ε‖ ^ 4) := by
  obtain ⟨p, hp⟩ := hw
  let N := -(ContinuousLinearMap.id ℝ ℝ)
  have hn : HasFPowerSeriesAt w p (N 0) := by simpa [N] using hp
  have hNeg : HasFPowerSeriesAt (fun ε => w (-ε)) (p.compContinuousLinearMap N) 0 :=
    hn.compContinuousLinearMap
  have hP := hNeg.eq_formalMultilinearSeries_of_eventually hp he
  have hsign (j : ℕ) : (-1 : ℝ) ^ j • p.coeff j = p.coeff j := by
    have H := congrArg (fun q : FormalMultilinearSeries ℝ ℝ Parameters => q.coeff j) hP
    change (p.compContinuousLinearMap N) j 1 = p.coeff j at H
    rw [FormalMultilinearSeries.compContinuousLinearMap_apply] at H
    have harg : (fun i : Fin j => N ((1 : Fin j → ℝ) i)) = fun _ => (-1 : ℝ) := by
      funext i
      simp [N]
    change p j (fun i => N ((1 : Fin j → ℝ) i)) = p.coeff j at H
    calc
      (-1 : ℝ) ^ j • p.coeff j = p j (fun _ => (-1 : ℝ)) :=
        FormalMultilinearSeries.apply_eq_pow_smul_coeff.symm
      _ = p.coeff j := harg ▸ H
  have vanish (j : ℕ) (hj : (-1 : ℝ) ^ j = -1) : p.coeff j = 0 := by
    have H : -(p.coeff j) = p.coeff j := by simpa [hj] using hsign j
    have h : (2 : ℝ) • p.coeff j = 0 := by
      rw [two_smul]
      exact calc
        p.coeff j + p.coeff j = -(p.coeff j) + p.coeff j := congrArg (· + p.coeff j) H.symm
        _ = 0 := neg_add_cancel _
    exact (smul_eq_zero.mp h).resolve_left (by norm_num)
  have h1 := vanish 1 (by norm_num)
  have h3 := vanish 3 (by norm_num)
  have h0 : p.coeff 0 = w 0 := hp.coeff_zero _
  refine ⟨p.coeff 2, ?_⟩
  simpa [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    FormalMultilinearSeries.apply_eq_pow_smul_coeff, h0, h1, h3] using hp.isBigO_sub_partialSum_pow 4

#print axioms LeadingCertificate.invertible
#print axioms exists_polynomial_partner
#print axioms even_taylor_two

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSAnalyticPartnerPolynomial
