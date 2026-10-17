/- GID: D5/S3/Quantum/Analysis/DiagonalEnergy
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/DiagonalEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The same diagonal closure has true resolvents, heat traces and extended state energy. -/
/-
Trace-class products and unconditional trace evaluation use the attributed
PhysLean suppliers GeneralProduct and GeneralIdeal, without a commutation
hypothesis. The strong heat and closure come from DiagonalHeat; their selected
PhysLean and Scott Armstrong source attributions remain authoritative.
The bounded resolvent approximation is standard operator theory.
-/
import D5.S3.Quantum.Analysis.DiagonalHeat

open Filter
open scoped Topology ENNReal NNReal InnerProductSpace ComplexConjugate lp ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace D5.S3.Quantum.Analysis.DiagonalEnergy
open D5.S3.Quantum.Analysis.DiagonalHeat
variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem range_basis (e : HilbertBasis ι ℂ H) :
    ∃ (q : ι ≃ Set.range e) (b : HilbertBasis (Set.range e) ℂ H), ∀ i, b (q i) = e i := by
  classical
  let q : ι ≃ Set.range e := Equiv.ofInjective e e.orthonormal.linearIndependent.injective
  have hr : Set.range (e ∘ q.symm) = Set.range e := by
    ext x
    constructor
    · rintro ⟨j,rfl⟩; exact ⟨q.symm j,rfl⟩
    · rintro ⟨i,rfl⟩; exact ⟨q i,by simp⟩
  let b := HilbertBasis.mk (e.orthonormal.comp q.symm q.symm.injective) (by rw [hr,e.dense_span])
  refine ⟨q,b,fun i => ?_⟩
  change HilbertBasis.mk _ _ (q i) = _
  rw [HilbertBasis.coe_mk]
  simp

private theorem actual_trace_hasSum (e : HilbertBasis ι ℂ H) {A : H →L[ℂ] H}
    (hA : IsTraceClass A) : HasSum (fun i => ⟪e i,A (e i)⟫_ℂ) (trace A hA) := by
  obtain ⟨q,b,hb⟩ := range_basis e
  have hs := (summable_trace_diagonal_of_isTraceClass hA b).hasSum
  rw [← trace_eq_of_hilbertBasis hA b] at hs
  have ht := q.hasSum_iff.mpr hs
  simpa only [Function.comp_def,hb] using ht

private theorem traceClass_of_positive_diagonal (e : HilbertBasis ι ℂ H)
    {A : H →L[ℂ] H} (hA : A.IsPositive) (a : ι → ℝ)
    (ha : Summable a) (he : ∀ i, A (e i) = a i • e i) : IsTraceClass A := by
  classical
  obtain ⟨q,b,hb⟩ := range_basis e
  refine ⟨Set.range e,b,?_⟩
  rw [CFC.abs_of_nonneg A ((ContinuousLinearMap.nonneg_iff_isPositive (f := A)).mpr hA)]
  apply q.summable_iff.mp
  convert ha using 1
  ext i
  simp only [Function.comp_def,hb,he,inner_smul_right_eq_smul]
  simp [inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]

/-- At each strictly positive time, the actual positive heat is trace class and
both its real and complex coefficient series have the literal operator trace. -/
theorem heat_trace (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hs : ∀ β : ℝ, 0 < β → Summable (fun i => Real.exp (-β*h i)))
    (β : ℝ≥0) (hβ : 0 < β) :
    ∃ ht : IsTraceClass (heat e h hh β),
      HasSum (fun i => (Real.exp (-(β : ℝ)*h i) : ℂ)) (trace (heat e h hh β) ht) ∧
      HasSum (fun i => Real.exp (-(β : ℝ)*h i)) (trace (heat e h hh β) ht).re := by
  classical
  have hd := diagonal_heat e h hh
  have he (i) : heat e h hh β (e i) = Real.exp (-(β : ℝ)*h i) • e i :=
    multiplier_basis e _ _ _ i
  have ht := traceClass_of_positive_diagonal e (hd.2.2.2.2.2.1 β) _
    (hs β hβ) he
  refine ⟨ht,?_,?_⟩
  · convert actual_trace_hasSum e ht using 1
    ext i
    simp only [he,inner_smul_right_eq_smul]
    simp [inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
  · have hc : HasSum (fun i => (Real.exp (-(β : ℝ)*h i) : ℂ))
        (trace (heat e h hh β) ht) := by
      convert actual_trace_hasSum e ht using 1
      ext i
      simp only [he,inner_smul_right_eq_smul]
      simp [inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
    simpa only [Complex.reCLM_apply,Complex.ofReal_re] using Complex.reCLM.hasSum hc

private theorem inverse_bound (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (i : ι) : |(m+h i)⁻¹| ≤ (⟨m⁻¹,(inv_pos.mpr hm).le⟩ : ℝ≥0) := by
  rw [abs_of_pos (inv_pos.mpr (add_pos_of_pos_of_nonneg hm (hh i)))]
  exact inv_anti₀ hm (le_add_of_nonneg_right (hh i))

/-- The actual bounded full-basis resolvent of the same Hamiltonian. -/
def resolvent (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) : H →L[ℂ] H :=
  multiplier e (fun i => (m+h i)⁻¹) ⟨m⁻¹,(inv_pos.mpr hm).le⟩ (inverse_bound h hh m hm)

private theorem resolvent_coeff (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (x : H) (i : ι) :
    e.repr (resolvent e h hh m hm x) i = ((m+h i)⁻¹ : ℂ)*e.repr x i :=
  by simpa only [resolvent,Complex.ofReal_inv,Complex.ofReal_add] using
    multiplier_coeff e (fun i => (m+h i)⁻¹) _ (inverse_bound h hh m hm) x i

private theorem resolvent_graph (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (x : H) :
    (resolvent e h hh m hm x, x-m • resolvent e h hh m hm x) ∈ (hamiltonian e h).graph := by
  apply ((diagonal_heat e h hh).2.2.1 _ _).mpr
  intro i
  have hn : (m+h i : ℂ) ≠ 0 := by exact_mod_cast (add_pos_of_pos_of_nonneg hm (hh i)).ne'
  simp only [map_sub,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,
    lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,resolvent_coeff,
    Complex.ofReal_inv,Complex.ofReal_add]
  have alg (M R z : ℂ) (hne : M+R ≠ 0) :
      z-M*((M+R)⁻¹*z) = R*((M+R)⁻¹*z) := by
    field_simp [hne]
    <;> ring
  exact alg m (h i) (e.repr x i) hn

/-- The resolvent value as an element of the actual operator domain. -/
def resolventVector (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (x : H) : (hamiltonian e h).domain :=
  ⟨resolvent e h hh m hm x, LinearPMap.mem_domain_of_mem_graph (resolvent_graph e h hh m hm x)⟩

/-- Both inverse identities and uniqueness hold on the full actual domain. -/
theorem resolvent_inverse (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) :
    (∀ x, (hamiltonian e h) (resolventVector e h hh m hm x) +
      m • resolvent e h hh m hm x = x) ∧
    (∀ y : (hamiltonian e h).domain,
      resolvent e h hh m hm ((hamiltonian e h) y + m • (y : H)) = y) ∧
    (∀ A : H →L[ℂ] H,
      (∀ x, (A x,x-m • A x) ∈ (hamiltonian e h).graph) → A = resolvent e h hh m hm) := by
  have hg := (diagonal_heat e h hh).2.2.1
  have hleft (x : H) : (hamiltonian e h) (resolventVector e h hh m hm x) +
      m • resolvent e h hh m hm x = x := by
    have hy := ((LinearPMap.image_iff (resolventVector e h hh m hm x).2).mpr
      (resolvent_graph e h hh m hm x)).symm
    change (hamiltonian e h) (resolventVector e h hh m hm x) = _ at hy
    rw [hy]; abel
  have hright (y : (hamiltonian e h).domain) :
      resolvent e h hh m hm ((hamiltonian e h) y + m • (y : H)) = y := by
    have hy := (hg _ _).mp ((hamiltonian e h).mem_graph y)
    apply e.repr.injective
    ext i
    have hn : (m+h i : ℂ) ≠ 0 := by exact_mod_cast (add_pos_of_pos_of_nonneg hm (hh i)).ne'
    simp only [resolvent_coeff,map_add,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,
      lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,hy,
      Complex.ofReal_inv,Complex.ofReal_add]
    have alg (M R z : ℂ) (hne : M+R ≠ 0) :
        (M+R)⁻¹*(R*z)+M*((M+R)⁻¹*z) = z := by
      field_simp [hne]
      <;> ring
    exact alg m (h i) (e.repr (y : H) i) hn
  refine ⟨hleft,hright,?_⟩
  intro A hA
  apply ContinuousLinearMap.ext
  intro x
  have hx := hA x
  let y : (hamiltonian e h).domain := ⟨A x,LinearPMap.mem_domain_of_mem_graph hx⟩
  have hy : (hamiltonian e h) y = x-m • A x := ((LinearPMap.image_iff y.2).mpr hx).symm
  have ht := hright y
  rw [hy,sub_add_cancel] at ht
  exact ht.symm

/-- Bounded Yosida energy coefficient. -/
def capCoeff (m r : ℝ) : ℝ := m*r/(m+r)

private theorem cap_bounds {m r : ℝ} (hm : 0 < m) (hr : 0 ≤ r) :
    0 ≤ capCoeff m r ∧ capCoeff m r ≤ m ∧ capCoeff m r ≤ r := by
  have hd := add_pos_of_pos_of_nonneg hm hr
  dsimp [capCoeff]
  refine ⟨div_nonneg (mul_nonneg hm.le hr) hd.le,?_,?_⟩
  · apply (div_le_iff₀ hd).mpr; nlinarith [sq_nonneg m]
  · apply (div_le_iff₀ hd).mpr; nlinarith [sq_nonneg r]

/-- The bounded energy cap is defined by the true resolvent, without K times rho. -/
def cap (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) : H →L[ℂ] H :=
  m • ContinuousLinearMap.id ℂ H - (m^2) • resolvent e h hh m hm

private theorem cap_coeff (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (x : H) (i : ι) :
    e.repr (cap e h hh m hm x) i = (capCoeff m (h i) : ℂ)*e.repr x i := by
  have hn : (m+h i : ℂ) ≠ 0 := by exact_mod_cast (add_pos_of_pos_of_nonneg hm (hh i)).ne'
  simp only [cap,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,map_sub,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,
    lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,resolvent_coeff,
    capCoeff,Complex.ofReal_inv,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_add,
    Complex.ofReal_pow]
  have alg (M R z : ℂ) (hne : M+R ≠ 0) :
      M*z-M^2*((M+R)⁻¹*z) = (M*R/(M+R))*z := by
    field_simp [hne]
    <;> ring
  convert alg (m : ℂ) (h i : ℂ) (e.repr x i) hn using 1 <;> norm_cast

private theorem cap_eq_multiplier (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) :
    cap e h hh m hm = multiplier e (fun i => capCoeff m (h i)) ⟨m,hm.le⟩
      (fun i => by rw [abs_of_nonneg (cap_bounds hm (hh i)).1]; exact (cap_bounds hm (hh i)).2.1) := by
  ext x
  apply e.repr.injective
  ext i
  erw [cap_coeff,multiplier_coeff]

private theorem cap_positive (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) : (cap e h hh m hm).IsPositive := by
  rw [cap_eq_multiplier]
  exact multiplier_positive e _ _ _ (fun i => (cap_bounds hm (hh i)).1)

private theorem cap_basis (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (i : ι) : cap e h hh m hm (e i) = capCoeff m (h i) • e i := by
  rw [cap_eq_multiplier]
  exact multiplier_basis e _ _ _ i

private theorem cap_product_traceClass (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) :
    IsTraceClass (cap e h hh m hm * ρ) := by
  simpa only [mul_one] using (isTraceClass_mul_mul (A := cap e h hh m hm) (B := 1) hρ)

private theorem cap_trace_hasSum (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) :
    HasSum (fun i => capCoeff m (h i)*(⟪e i,ρ (e i)⟫_ℂ).re)
      (trace (cap e h hh m hm * ρ) (cap_product_traceClass e h hh m hm ρ hρ)).re := by
  have hs := actual_trace_hasSum e (cap_product_traceClass e h hh m hm ρ hρ)
  have he (i) : ⟪e i,(cap e h hh m hm * ρ) (e i)⟫_ℂ =
      (capCoeff m (h i) : ℂ)*⟪e i,ρ (e i)⟫_ℂ := by
    rw [ContinuousLinearMap.mul_apply,← (cap_positive e h hh m hm).inner_left_eq_inner_right,
      cap_basis,inner_smul_left_eq_star_smul]
    rfl
  have ht := Complex.reCLM.hasSum hs
  simpa only [Complex.reCLM_apply,he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using ht

/-- Extended state energy from actual bounded traces of canonical resolvent caps. -/
def stateEnergy (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (trace (cap e h hh (n+1) (by positivity) * ρ)
    (cap_product_traceClass e h hh (n+1) (by positivity) ρ hρ)).re

private theorem cap_order (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) :
    IsSelfAdjoint (cap e h hh m hm) ∧ 0 ≤ cap e h hh m hm ∧
      cap e h hh m hm ≤ m • ContinuousLinearMap.id ℂ H := by
  have hp := cap_positive e h hh m hm
  refine ⟨hp.isSelfAdjoint,(ContinuousLinearMap.nonneg_iff_isPositive (f := cap e h hh m hm)).mpr hp,?_⟩
  rw [ContinuousLinearMap.le_def]
  have heq : m • ContinuousLinearMap.id ℂ H - cap e h hh m hm =
      multiplier e (fun i => m-capCoeff m (h i)) ⟨m,hm.le⟩ (fun i => by
        rw [abs_of_nonneg (sub_nonneg.mpr (cap_bounds hm (hh i)).2.1)]
        exact sub_le_self m (cap_bounds hm (hh i)).1) := by
    apply ContinuousLinearMap.ext
    intro x
    apply e.repr.injective
    ext i
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,map_sub,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,
      lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
      cap_coeff,multiplier_coeff,Complex.ofReal_sub]
    exact (sub_mul (m : ℂ) (capCoeff m (h i) : ℂ) (e.repr x i)).symm
  rw [heq]
  exact multiplier_positive e _ _ _ (fun i => sub_nonneg.mpr (cap_bounds hm (hh i)).2.1)

private theorem cap_monotone {r : ℝ} (hr : 0 ≤ r) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : capCoeff a r ≤ capCoeff b r := by
  have hb := ha.trans_le hab
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg ha hr)
    (add_pos_of_pos_of_nonneg hb hr)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg r)]

private theorem cap_order_monotone (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) :
    cap e h hh a ha ≤ cap e h hh b hb := by
  rw [ContinuousLinearMap.le_def]
  let d : ι → ℝ := fun i => capCoeff b (h i)-capCoeff a (h i)
  have hd (i) : 0 ≤ d i := sub_nonneg.mpr (cap_monotone (hh i) ha hab)
  have hbd (i) : |d i| ≤ (⟨b,hb.le⟩ : ℝ≥0) := by
    rw [abs_of_nonneg (hd i)]
    exact (sub_le_self _ (cap_bounds ha (hh i)).1).trans (cap_bounds hb (hh i)).2.1
  have heq : cap e h hh b hb-cap e h hh a ha = multiplier e d ⟨b,hb.le⟩ hbd := by
    apply ContinuousLinearMap.ext
    intro x
    apply e.repr.injective
    ext i
    simp only [ContinuousLinearMap.sub_apply,map_sub,lp.coeFn_sub,Pi.sub_apply]
    erw [cap_coeff,cap_coeff,multiplier_coeff]
    simp only [d,Complex.ofReal_sub]
    exact (sub_mul _ _ _).symm
  rw [heq]
  exact multiplier_positive e d ⟨b,hb.le⟩ hbd hd

private theorem cap_limit (r : ℝ) :
    Tendsto (fun n : ℕ => capCoeff (n+1) r) atTop (𝓝 r) := by
  have ht := ((tendsto_natCast_div_add_atTop r).comp (tendsto_add_atTop_nat 1)).mul_const r
  convert ht using 1
  · funext n
    simp only [capCoeff,Function.comp_def,Nat.cast_add,Nat.cast_one]
    ring
  · simp

private theorem cap_trace_complex (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (m : ℝ) (hm : 0 < m) (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) :
    HasSum (fun i => (capCoeff m (h i) : ℂ)*⟪e i,ρ (e i)⟫_ℂ)
      (trace (cap e h hh m hm * ρ) (cap_product_traceClass e h hh m hm ρ hρ)) := by
  have hs := actual_trace_hasSum e (cap_product_traceClass e h hh m hm ρ hρ)
  convert hs using 1
  ext i
  rw [ContinuousLinearMap.mul_apply,← (cap_positive e h hh m hm).inner_left_eq_inner_right,
    cap_basis,inner_smul_left_eq_star_smul]
  rfl

private theorem energy_identity (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) (hp : ρ.IsPositive) :
    Monotone (fun n : ℕ => ENNReal.ofReal (trace (cap e h hh (n+1) (by positivity) * ρ)
      (cap_product_traceClass e h hh (n+1) (by positivity) ρ hρ)).re) ∧
    stateEnergy e h hh ρ hρ = ∑' i, ENNReal.ofReal (h i * (⟪e i,ρ (e i)⟫_ℂ).re) := by
  classical
  let p : ι → ℝ := fun i => (⟪e i,ρ (e i)⟫_ℂ).re
  have hp0 (i) : 0 ≤ p i := hp.re_inner_nonneg_right _
  let a : ℕ → ι → ℝ≥0∞ := fun n i => ENNReal.ofReal (capCoeff (n+1) (h i)*p i)
  have hat (n : ℕ) : ENNReal.ofReal (trace (cap e h hh (n+1) (by positivity) * ρ)
      (cap_product_traceClass e h hh (n+1) (by positivity) ρ hρ)).re = ∑' i, a n i := by
    rw [← (cap_trace_hasSum e h hh (n+1) (by positivity) ρ hρ).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg
      (fun i => mul_nonneg (cap_bounds (by positivity) (hh i)).1 (hp0 i))
      (cap_trace_hasSum e h hh (n+1) (by positivity) ρ hρ).summable
  have ham (i : ι) : Monotone (fun n => a n i) := by
    intro n k hnk
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right _ (hp0 i)
    exact cap_monotone (hh i) (by positivity) (by exact_mod_cast Nat.add_le_add_right hnk 1)
  refine ⟨?_,?_⟩
  · intro n k hnk
    simp only [hat]
    exact ENNReal.tsum_le_tsum (fun i => ham i hnk)
  · change (⨆ n : ℕ, ENNReal.ofReal _) = _
    simp only [hat]
    apply le_antisymm
    · apply iSup_le
      intro n
      apply ENNReal.tsum_le_tsum
      intro i
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (cap_bounds (by positivity) (hh i)).2.2 (hp0 i))
    · rw [ENNReal.tsum_eq_iSup_sum]
      apply iSup_le
      intro F
      have hlim : Tendsto (fun n : ℕ => ∑ i ∈ F, a n i) atTop
          (𝓝 (∑ i ∈ F, ENNReal.ofReal (h i*p i))) :=
        tendsto_finsetSum F (fun i _ => ENNReal.tendsto_ofReal ((cap_limit (h i)).mul_const (p i)))
      apply le_of_tendsto hlim
      exact Eventually.of_forall fun n => (ENNReal.sum_le_tsum F).trans (le_iSup (fun n => ∑' i, a n i) n)

private theorem lower_bound (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (h1 : ∀ i, 1 ≤ h i) (x : (hamiltonian e h).domain) :
    ‖(x : H)‖^2 ≤ (⟪(x : H),(hamiltonian e h) x⟫_ℂ).re := by
  classical
  have hgraph := ((diagonal_heat e h hh).2.2.1 _ _).mp ((hamiltonian e h).mem_graph x)
  have hcore := D5.S3.Quantum.Analysis.EigenbasisGraphCore.eigenbasis_graph_coefficients
    e (finiteOperator e h) h rfl (finite_basis e h) (x : H) ((hamiltonian e h) x)
  obtain ⟨u,hu,hi,hux,huK⟩ := hcore.2.1 (by
    simpa only [HilbertBasis.repr_apply_apply] using hgraph)
  have hf (F : Finset ι) : ‖(u F : H)‖^2 ≤ (⟪(u F : H),(finiteOperator e h) (u F)⟫_ℂ).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ),hu,hi,
      e.orthonormal.inner_sum, e.orthonormal.inner_sum]
    change Complex.reAddGroupHom (∑ i ∈ F, _) ≤ Complex.reAddGroupHom (∑ i ∈ F, _)
    simp only [map_sum]
    apply Finset.sum_le_sum
    intro i _
    have alg (z : ℂ) (r : ℝ) (hr : 1 ≤ r) :
        (conj z*z).re ≤ (conj z*((r : ℂ)*z)).re := by
      have heq : conj z*((r : ℂ)*z) = (r : ℂ)*(conj z*z) := by ring
      rw [heq,← Complex.normSq_eq_conj_mul_self]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      nlinarith [Complex.normSq_nonneg z]
    exact alg ⟪e i,(x : H)⟫_ℂ (h i) (h1 i)
  exact le_of_tendsto_of_tendsto ((hux.norm).pow 2)
    (Complex.continuous_re.tendsto _ |>.comp (hux.inner (𝕜 := ℂ) huK)) (Eventually.of_forall hf)

/-- One actual whole-space Hamiltonian supplies all-temperature heat traces,
true resolvents and the monotone extended state energy, including infinity. -/
theorem diagonal_resolvent_energy (e : HilbertBasis ι ℂ H) (h : ι → ℝ) (hh : ∀ i, 0 ≤ h i)
    (hs : ∀ β : ℝ, 0 < β → Summable (fun i => Real.exp (-β*h i)))
    (ρ : H →L[ℂ] H) (hρ : IsTraceClass ρ) (hp : ρ.IsPositive) :
    (∀ β : ℝ≥0, 0 < β → ∃ ht : IsTraceClass (heat e h hh β),
      HasSum (fun i => (Real.exp (-(β : ℝ)*h i) : ℂ)) (trace (heat e h hh β) ht) ∧
      HasSum (fun i => Real.exp (-(β : ℝ)*h i)) (trace (heat e h hh β) ht).re) ∧
    (∀ (m : ℝ) (hm : 0 < m),
      (∀ x, (hamiltonian e h) (resolventVector e h hh m hm x) + m • resolvent e h hh m hm x = x) ∧
      (∀ y : (hamiltonian e h).domain,
        resolvent e h hh m hm ((hamiltonian e h) y + m • (y : H)) = y) ∧
      IsSelfAdjoint (cap e h hh m hm) ∧ 0 ≤ cap e h hh m hm ∧
      cap e h hh m hm ≤ m • ContinuousLinearMap.id ℂ H ∧
      (∀ (b : ℝ) (hb : 0 < b), m ≤ b → cap e h hh m hm ≤ cap e h hh b hb) ∧
      (∀ (x : H) (i : ι), e.repr (cap e h hh m hm x) i =
        (capCoeff m (h i) : ℂ)*e.repr x i) ∧
      ∃ ht : IsTraceClass (cap e h hh m hm * ρ),
        HasSum (fun i => (capCoeff m (h i) : ℂ)*⟪e i,ρ (e i)⟫_ℂ)
          (trace (cap e h hh m hm * ρ) ht) ∧
        HasSum (fun i => capCoeff m (h i)*(⟪e i,ρ (e i)⟫_ℂ).re)
          (trace (cap e h hh m hm * ρ) ht).re) ∧
    Monotone (fun n : ℕ => ENNReal.ofReal (trace (cap e h hh (n+1) (by positivity) * ρ)
      (cap_product_traceClass e h hh (n+1) (by positivity) ρ hρ)).re) ∧
    stateEnergy e h hh ρ hρ = ∑' i, ENNReal.ofReal (h i*(⟪e i,ρ (e i)⟫_ℂ).re) ∧
    ((∀ i, 1 ≤ h i) → ∀ x : (hamiltonian e h).domain,
      ‖(x : H)‖^2 ≤ (⟪(x : H),(hamiltonian e h) x⟫_ℂ).re) := by
  refine ⟨fun β hβ => heat_trace e h hh hs β hβ,?_,(energy_identity e h hh ρ hρ hp).1,
    (energy_identity e h hh ρ hρ hp).2,fun h1 x => lower_bound e h hh h1 x⟩
  intro m hm
  have hi := resolvent_inverse e h hh m hm
  have ho := cap_order e h hh m hm
  exact ⟨hi.1,hi.2.1,ho.1,ho.2.1,ho.2.2,
    (fun b hb hab => cap_order_monotone e h hh m b hm hb hab),cap_coeff e h hh m hm,
    cap_product_traceClass e h hh m hm ρ hρ,
    cap_trace_complex e h hh m hm ρ hρ,cap_trace_hasSum e h hh m hm ρ hρ⟩

#print axioms heat_trace
#print axioms resolvent_inverse
#print axioms diagonal_resolvent_energy

end D5.S3.Quantum.Analysis.DiagonalEnergy
