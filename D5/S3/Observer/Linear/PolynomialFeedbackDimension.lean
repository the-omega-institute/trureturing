/- GID: D5/S3/Observer/Linear/PolynomialFeedbackDimension
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/PolynomialFeedbackDimension
   mirror-E: none(waiver:unrestricted-deterministic-history-dimension)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.ImplicitContDiff, mathlib/module/Mathlib.Analysis.Calculus.MeanValue]
   utility: none
   digest: Scalar polynomial-gain acquisition cannot recover its full target below the parameter dimension. -/

import D5.S3.Observer.Linear.GainRayHistory
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Topology Matrix ContDiff
open Set Filter Module

namespace D5.S3.Observer.Linear.PolynomialFeedbackDimension

abbrev Parameters (k d : ℕ) :=
  ℝ × ℝ × ℝ × (Fin k → ℝ) × (Fin (d + 1) → ℝ)

def Legal {k d : ℕ} (x : Parameters k d) : Prop :=
  0 < x.1 ∧ 0 < x.2.1 ∧ 0 < x.2.2.1

abbrev World (k d : ℕ) := {x : Parameters k d // Legal x}

def source {k d : ℕ} (x : Parameters k d) : GainRay.Mat :=
  !![x.1, x.2.1; x.2.2.1, x.2.1 * x.2.2.1 / x.1]

def gain {k d : ℕ} (x : Parameters k d) : Polynomial ℝ :=
  Polynomial.ofFn (k + 1) (Fin.cons 1 x.2.2.2.1)

def drift {k d : ℕ} (x : Parameters k d) : Polynomial ℝ :=
  Polynomial.ofFn (d + 1) x.2.2.2.2

abbrev Answer := GainRay.Mat × Polynomial ℝ × Polynomial ℝ

def target {k d : ℕ} (x : Parameters k d) : Answer :=
  ((Matrix.trace (source x))⁻¹ • source x,
    Matrix.trace (source x) • gain x, drift x)

def readAt {k d : ℕ} (x : Parameters k d) (w : List Bool) (i : ℕ) : ℝ :=
  (gain x).eval (i : ℝ) *
    Matrix.trace (GainRay.acquisition (w.take i) * source x) +
    (drift x).eval (i : ℝ)

def readings {k d : ℕ} (x : Parameters k d) (w : List Bool) : GainRay.History w :=
  fun i => readAt x w i.val

/-- A total decision on the complete chronological action and scalar history. -/
abbrev Protocol := (w : List Bool) → GainRay.History w → Bool ⊕ Answer

/-- The fuel counts reads, including the read at the current word. -/
def run {k d : ℕ} (P : Protocol) (x : Parameters k d) : ℕ → List Bool → Option Answer
  | 0, _ => none
  | n + 1, w => match P w (readings x w) with
    | .inr a => some a
    | .inl e => run P x n (w ++ [e])

def UniformlyStops {k d : ℕ} (P : Protocol) (m : ℕ) : Prop :=
  ∀ x : World k d, ∃ a, run P x.val m [] = some a

private theorem trace_pos {k d : ℕ} (x : Parameters k d) (hx : Legal x) :
    0 < Matrix.trace (source x) := by
  simp only [source, Matrix.trace, Fin.sum_univ_two]
  exact add_pos hx.1 (div_pos (mul_pos hx.2.1 hx.2.2) hx.1)

private theorem target_injective {k d : ℕ} : InjOn (@target k d) {x | Legal x} := by
  intro x hx y hy h
  have ha : Matrix.trace (source x) = Matrix.trace (source y) := by
    have hc := congrArg (fun a : Answer => a.2.1.coeff 0) h
    simpa [target, gain] using hc
  have hn : Matrix.trace (source x) ≠ 0 := (trace_pos x hx).ne'
  have hS : source x = source y := by
    have hs := congrArg (fun a : Answer => Matrix.trace (source x) • a.1) h
    simpa [target, ← ha, smul_smul, hn] using hs
  have hG : gain x = gain y := by
    have hg := congrArg (fun a : Answer => (Matrix.trace (source x))⁻¹ • a.2.1) h
    simpa [target, ← ha, smul_smul, hn] using hg
  have hp : x.1 = y.1 := by simpa [source] using congrArg (fun S => S 0 0) hS
  have hq : x.2.1 = y.2.1 := by simpa [source] using congrArg (fun S => S 0 1) hS
  have hr : x.2.2.1 = y.2.2.1 := by simpa [source] using congrArg (fun S => S 1 0) hS
  have hγ : x.2.2.2.1 = y.2.2.2.1 := by
    have hc := Polynomial.injective_ofFn (k + 1) hG
    funext i
    simpa using congrFun hc i.succ
  have hD : x.2.2.2.2 = y.2.2.2.2 :=
    Polynomial.injective_ofFn (d + 1) (congrArg (fun a : Answer => a.2.2) h)
  exact Prod.ext hp (Prod.ext hq (Prod.ext hr (Prod.ext hγ hD)))

private theorem read_contDiffOn {k d : ℕ}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : IsOpen U) (φ : E → Parameters k d)
    (hφ : ContDiffOn ℝ 1 φ U) (hlegal : ∀ x ∈ U, Legal (φ x))
    (w : List Bool) (i : ℕ) :
    ContDiffOn ℝ 1 (fun x => readAt (φ x) w i) U := by
  intro x hx
  have hs : ContDiffAt ℝ 1 φ x := (hφ x hx).contDiffAt (hU.mem_nhds hx)
  have hp : (φ x).1 ≠ 0 := (hlegal x hx).1.ne'
  apply ContDiffAt.contDiffWithinAt
  simp only [readAt, gain, drift, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, source,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  apply ContDiffAt.add
  · apply ContDiffAt.mul
    · apply ContDiffAt.sum
      intro j hj
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero]; fun_prop
      · simp only [Fin.cons_succ]; fun_prop
    · fun_prop (disch := assumption)
  · apply ContDiffAt.sum
    intro j hj
    fun_prop

private theorem regular_slice
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (U : Set E) (hU : IsOpen U)
    (f : E → ℝ) (a : E) (ha : a ∈ U) (hf : ContDiffAt ℝ 1 f a)
    (hne : fderiv ℝ f a ≠ 0) :
    ∃ (l : E →L[ℝ] ℝ) (V : Set l.ker) (ψ : l.ker → E),
      IsOpen V ∧ V.Nonempty ∧ Convex ℝ V ∧ MapsTo ψ V U ∧ InjOn ψ V ∧
      ContDiffOn ℝ 1 ψ V ∧ (∀ y ∈ V, f (ψ y) = f a) ∧
      finrank ℝ l.ker + 1 = finrank ℝ E := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let l := fderiv ℝ f a
  have hl : l.toLinearMap ≠ 0 := by
    intro h
    apply hne
    exact ContinuousLinearMap.coe_injective h
  have hs : Function.Surjective l :=
    surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (by simp) hl
  have hr : l.range = ⊤ := LinearMap.range_eq_top.mpr hs
  let hc := l.ker_closedComplemented_of_finiteDimensional_range
  let hd := hf.hasStrictFDerivAt (by norm_num)
  let φ := hd.implicitFunctionDataOfComplemented f l hr hc
  let ψ := hd.implicitFunctionOfComplemented f l hr hc (f a)
  let e := hd.implicitToOpenPartialHomeomorphOfComplemented f l hr hc
  have hψ0 : ψ 0 = a := hd.implicitFunctionOfComplemented_apply_image hr hc
  have hφ : ContDiffAt ℝ 1 φ.implicitFunction.uncurry (f a, (0 : l.ker)) := by
    have h := φ.contDiffAt_implicitFunction hf (by
      dsimp [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
      fun_prop) (by norm_num)
    simpa [φ, ImplicitFunctionData.prodFun,
      HasStrictFDerivAt.implicitFunctionDataOfComplemented] using h
  have hψ : ContDiffAt ℝ 1 ψ 0 :=
    hφ.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have htarget : ∀ᶠ y : l.ker in 𝓝 0, (f a, y) ∈ e.target :=
    (continuousAt_const.prodMk continuousAt_id).eventually
      (e.open_target.mem_nhds
        (hd.mem_implicitToOpenPartialHomeomorphOfComplemented_target hr hc))
  have hinside : ∀ᶠ y in 𝓝 (0 : l.ker), ψ y ∈ U := by
    apply hψ.continuousAt.eventually
    rw [hψ0]
    exact hU.mem_nhds ha
  have hlevel : ∀ᶠ y : l.ker in 𝓝 0, f (ψ y) = f a :=
    (continuousAt_const.prodMk continuousAt_id).tendsto.eventually
      (hd.map_implicitFunctionOfComplemented_eq hr hc)
  have hcont : ∀ᶠ y in 𝓝 (0 : l.ker), ContDiffAt ℝ 1 ψ y :=
    hψ.eventually (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (htarget.and (hinside.and (hlevel.and hcont)))
  refine ⟨l, Metric.ball 0 ε, ψ, Metric.isOpen_ball,
    ⟨0, Metric.mem_ball_self hε⟩, convex_ball _ _, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact (hball hy).2.1
  · intro y hy z hz heq
    have hy' := e.right_inv (hball hy).1
    have hz' := e.right_inv (hball hz).1
    exact congrArg Prod.snd (hy'.symm.trans ((congrArg e heq).trans hz'))
  · intro y hy
    exact (hball hy).2.2.2.contDiffWithinAt
  · intro y hy
    exact (hball hy).2.2.1
  · have h := l.toLinearMap.finrank_range_add_finrank_ker
    rw [hr, finrank_top, finrank_self] at h
    omega

private theorem chart_obstruction {k d : ℕ} (P : Protocol) (b : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
      (U : Set E), IsOpen U → U.Nonempty → Convex ℝ U →
      ∀ (φ : E → Parameters k d), ContDiffOn ℝ 1 φ U → InjOn φ U →
      (∀ x ∈ U, Legal (φ x)) →
      ∀ (w : List Bool),
      (∀ x ∈ U, ∀ y ∈ U, ∀ i < w.length, readAt (φ x) w i = readAt (φ y) w i) →
      b < finrank ℝ E →
      ¬ (∀ x ∈ U, run P (φ x) b w = some (target (φ x))) := by
  classical
  induction b with
  | zero =>
    intro E _ _ _ U hU hne hc φ hφ hi hl w hp hb hs
    obtain ⟨x, hx⟩ := hne
    have h := hs x hx
    simp [run] at h
  | succ b ih =>
    intro E _ _ _ U hU hne hc φ hφ hi hl w hp hb hs
    let f : E → ℝ := fun x => readAt (φ x) w w.length
    have hf : ContDiffOn ℝ 1 f U := read_contDiffOn U hU φ hφ hl w w.length
    have step :
        ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
          (V : Set F), IsOpen V → V.Nonempty → Convex ℝ V →
          ∀ (ψ : F → E), ContDiffOn ℝ 1 ψ V → InjOn ψ V → MapsTo ψ V U →
          (∃ c, ∀ y ∈ V, f (ψ y) = c) → b < finrank ℝ F → False := by
      intro F _ _ _ V hV hv hvc ψ hψ hψi hψm hlevel hdim
      obtain ⟨c, hlevel⟩ := hlevel
      obtain ⟨y₀, hy₀⟩ := hv
      let χ := φ ∘ ψ
      have hhist (y : F) (hy : y ∈ V) : readings (χ y) w = readings (χ y₀) w := by
        ext i
        by_cases ht : i.val < w.length
        · exact hp _ (hψm hy) _ (hψm hy₀) _ ht
        · have he : i.val = w.length := by have := i.isLt; omega
          change readAt (φ (ψ y)) w i.val = readAt (φ (ψ y₀)) w i.val
          rw [he]
          exact (hlevel y hy).trans (hlevel y₀ hy₀).symm
      cases hd : P w (readings (χ y₀) w) with
      | inr answer =>
        have ht (y : F) (hy : y ∈ V) : target (χ y) = answer := by
          have h := hs (ψ y) (hψm hy)
          change run P (χ y) (b + 1) w = _ at h
          rw [run, hhist y hy, hd] at h
          exact (Option.some.inj h).symm
        let : Nontrivial F := Module.nontrivial_of_finrank_pos (R := ℝ) (M := F) (by omega)
        have hinf : V.Infinite := infinite_of_mem_nhds y₀ (hV.mem_nhds hy₀)
        obtain ⟨y₁, hy₁, hne⟩ := hinf.exists_notMem_finite (finite_singleton y₀)
        apply hne
        apply mem_singleton_iff.mpr
        apply hψi hy₁ hy₀
        apply hi (hψm hy₁) (hψm hy₀)
        apply target_injective (hl _ (hψm hy₁)) (hl _ (hψm hy₀))
        exact (ht y₁ hy₁).trans (ht y₀ hy₀).symm
      | inl atom =>
        refine ih F V hV ⟨y₀, hy₀⟩ hvc χ (hφ.comp hψ hψm) (hi.comp hψi hψm)
          (fun y hy => hl _ (hψm hy)) (w ++ [atom]) ?_ hdim ?_
        · intro y hy z hz i hi'
          have hle : i ≤ w.length := by simp only [List.length_append, List.length_singleton] at hi'; omega
          change readAt (φ (ψ y)) (w ++ [atom]) i = readAt (φ (ψ z)) (w ++ [atom]) i
          simp only [readAt, List.take_append_of_le_length hle]
          exact congrFun ((hhist y hy).trans (hhist z hz).symm) ⟨i, by omega⟩
        · intro y hy
          have h := hs (ψ y) (hψm hy)
          change run P (χ y) (b + 1) w = _ at h
          rw [run, hhist y hy, hd] at h
          exact h
    by_cases hz : ∀ x ∈ U, fderiv ℝ f x = 0
    · apply step E U hU hne hc id contDiffOn_id (injOn_id U) (fun _ h => h) ?_ (by omega)
      exact hU.exists_is_const_of_fderiv_eq_zero hc.isPreconnected
        (hf.differentiableOn (by norm_num)) hz
    · push Not at hz
      obtain ⟨a, ha, hna⟩ := hz
      obtain ⟨l, V, ψ, hV, hv, hvc, hψm, hψi, hψ, hlevel, hdim⟩ :=
        regular_slice U hU f a ha ((hf a ha).contDiffAt (hU.mem_nhds ha)) hna
      exact step l.ker V hV hv hvc ψ hψ hψi hψm ⟨f a, hlevel⟩ (by omega)

/-- No uniform exact deterministic recovery is possible below the full parameter dimension. -/
theorem unrestricted_polynomial_feedback_lower_bound (k d m : ℕ) (P : Protocol)
    (hm : m < k + d + 4) (hstop : UniformlyStops (k := k) (d := d) P m) :
    ∃ x : World k d, ∃ a, run P x.val m [] = some a ∧ a ≠ target x.val := by
  classical
  by_contra h
  push Not at h
  have hs (x : World k d) : run P x.val m [] = some (target x.val) := by
    obtain ⟨a, ha⟩ := hstop x
    rw [← h x a ha]
    exact ha
  let x₀ : Parameters k d := (1, 1, 1, 0, 0)
  have hlegal : Legal x₀ := by norm_num [Legal, x₀]
  have hopen : IsOpen {x : Parameters k d | Legal x} := by
    change IsOpen ({x : Parameters k d | 0 < x.1} ∩
      ({x : Parameters k d | 0 < x.2.1} ∩ {x : Parameters k d | 0 < x.2.2.1}))
    exact (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
        (isOpen_lt continuous_const (continuous_fst.comp (continuous_snd.comp continuous_snd))))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hlegal)
  refine chart_obstruction P m (Parameters k d) (Metric.ball x₀ ε)
    Metric.isOpen_ball ⟨x₀, Metric.mem_ball_self hε⟩ (convex_ball _ _) id
    contDiffOn_id (injOn_id _) (fun _ hx => hball hx) [] (by simp) ?_
    (fun x hx => hs ⟨x, hball hx⟩)
  simpa only [Parameters, finrank_prod, finrank_self, finrank_fin_fun] using
    (show m < 1 + (1 + (1 + (k + (d + 1)))) by omega)

#print axioms unrestricted_polynomial_feedback_lower_bound

end D5.S3.Observer.Linear.PolynomialFeedbackDimension
