import CFMPOriginalEndpointCaps460Transient
import CFMPOriginalStrictInverse310Transient

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology Matrix
open D5.S3.Geometry.Hyperideal.TwoLengthAngleSum (rawCos)
open CFMPOriginalForward390 (angle angleD)

namespace CFMPOriginalCapSharpness520Transient

def profile (σ ε : ℝ) : Fin 6 → ℝ := ![σ-2*ε,ε,ε,ε,ε,ε]

def quotient (σ ε : ℝ) : ℝ :=
  ((Real.sin (σ-2*ε))^2 * Real.cos ε + 2*(Real.cos ε)^2 +
    2*Real.cos (σ-2*ε)*(Real.cos ε)^2) /
  angleD (Real.cos (σ-2*ε)) (Real.cos ε) (Real.cos ε)

def capValues (σ : ℝ) : Set ℝ := {X | ∃ x : Fin 6 → ℝ,
  (∀ q, 1 < x q) ∧ (∀ q, -1 < rawCos x q ∧ rawCos x q < 1) ∧
    angle x 0+angle x 1+angle x 2 ≤ σ ∧
    angle x 0+angle x 4+angle x 5 ≤ σ ∧ x 0=X}

theorem quotient_limit (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ ≤ Real.pi/2) :
    Tendsto (quotient σ) (𝓝 0) (𝓝 ((3-Real.cos σ)/(1+Real.cos σ))) := by
  have hc : 0 ≤ Real.cos σ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],hσ⟩
  have hden : 0 < angleD (Real.cos σ) 1 1 := by
    dsimp only [angleD]
    nlinarith only [hc,sq_nonneg (Real.cos σ)]
  have hn : Continuous (fun ε : ℝ =>
      (Real.sin (σ-2*ε))^2 * Real.cos ε + 2*(Real.cos ε)^2 +
        2*Real.cos (σ-2*ε)*(Real.cos ε)^2) := by fun_prop
  have hd : Continuous (fun ε : ℝ =>
      angleD (Real.cos (σ-2*ε)) (Real.cos ε) (Real.cos ε)) := by
    unfold angleD
    fun_prop
  have hz : angleD (Real.cos (σ-2*0)) (Real.cos 0) (Real.cos 0) ≠ 0 := by
    simpa only [mul_zero,sub_zero,Real.cos_zero] using hden.ne'
  have hcont : ContinuousAt (quotient σ) 0 := hn.continuousAt.div hd.continuousAt hz
  have he : quotient σ 0 = (3-Real.cos σ)/(1+Real.cos σ) := by
    have hp : 1+Real.cos σ ≠ 0 := by linarith only [hc]
    have hsq := Real.sin_sq_add_cos_sq σ
    have hnum : (Real.sin σ)^2+2+2*Real.cos σ =
        (3-Real.cos σ)*(1+Real.cos σ) := by nlinarith only [hsq]
    have hd0 : angleD (Real.cos σ) 1 1 = (1+Real.cos σ)^2 := by
      unfold angleD
      ring
    simp only [quotient,mul_zero,sub_zero,Real.cos_zero,one_pow,mul_one]
    rw [hnum,hd0]
    field_simp [hp] <;> ring
  simpa only [he] using hcont.tendsto

theorem profile_realized (σ ε : ℝ) (hσ0 : 0 < σ) (hσ : σ ≤ Real.pi/2)
    (hε : 0 < ε) (hεσ : ε < σ/2) (hεπ : ε < Real.pi/3) :
    ∃ x : Fin 6 → ℝ, (∀ q, 1 < x q) ∧
      (∀ q, -1 < rawCos x q ∧ rawCos x q < 1) ∧
      angle x 0+angle x 1+angle x 2 ≤ σ ∧
      angle x 0+angle x 4+angle x 5 ≤ σ ∧ x 0=quotient σ ε := by
  have hα (q : Fin 6) : 0 < profile σ ε q := by
    fin_cases q <;> simp only [profile,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] <;> linarith
  have hv0 : profile σ ε 0+profile σ ε 1+profile σ ε 2 < Real.pi := by
    norm_num [profile]
    linarith [Real.pi_pos]
  have hv1 : profile σ ε 0+profile σ ε 5+profile σ ε 4 < Real.pi := by
    norm_num [profile]
    linarith [Real.pi_pos]
  have hv2 : profile σ ε 1+profile σ ε 5+profile σ ε 3 < Real.pi := by
    norm_num [profile]
    linarith
  have hv3 : profile σ ε 2+profile σ ε 4+profile σ ε 3 < Real.pi := by
    norm_num [profile]
    linarith
  obtain ⟨l,hg,ha⟩ := CFMPOriginalStrictInverse310Transient.original_strict_angle_inverse
    (profile σ ε) hα hv0 hv1 hv2 hv3
  let x : Fin 6 → ℝ := fun q => Real.cosh (l q)
  have hx (q : Fin 6) : 1 < x q := Real.one_lt_cosh.mpr (hg.1 q).ne'
  have hc (q : Fin 6) : -1 < rawCos x q ∧ rawCos x q < 1 := hg.2 q
  have har (q : Fin 6) : angle x q = profile σ ε q := ha q
  have hcap1 : angle x 0+angle x 1+angle x 2 ≤ σ := by
    simp only [har,profile,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue]
    linarith
  have hcap2 : angle x 0+angle x 4+angle x 5 ≤ σ := by
    simp only [har,profile,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue]
    linarith
  obtain ⟨_,_,_,_,hD,_,hf⟩ := CFMPOriginalForward390.forward x hx hc
  simp only [har,profile,Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] at hD hf
  have hroot : Real.sqrt
      (angleD (Real.cos (σ-2*ε)) (Real.cos ε) (Real.cos ε) *
        angleD (Real.cos (σ-2*ε)) (Real.cos ε) (Real.cos ε)) =
      angleD (Real.cos (σ-2*ε)) (Real.cos ε) (Real.cos ε) := by
    simpa only [pow_two] using Real.sqrt_sq hD.le
  rw [hroot] at hf
  refine ⟨x,hx,hc,hcap1,hcap2,hf.trans ?_⟩
  unfold quotient
  congr 1
  ring

theorem original_equal_cap_sharp (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ ≤ Real.pi/2) :
    IsLUB (capValues σ) ((3-Real.cos σ)/(1+Real.cos σ)) := by
  have upper : ∀ X ∈ capValues σ, X < (3-Real.cos σ)/(1+Real.cos σ) := by
    intro X hX
    obtain ⟨x,hx,hc,hcap1,hcap2,he⟩ := hX
    have h := (CFMPOriginalEndpointCaps444Transient.original_equal_endpoint_caps
      x hx hc σ hcap1 hcap2 hσ).2
    simpa only [he] using h
  refine ⟨fun X hX => (upper X hX).le,?_⟩
  intro a ha
  by_contra h
  have hlt : a < (3-Real.cos σ)/(1+Real.cos σ) := lt_of_not_ge h
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), a < quotient σ ε :=
    (quotient_limit σ hσ0 hσ).eventually (Ioi_mem_nhds hlt)
  obtain ⟨δ,hδ,hclose⟩ := Metric.eventually_nhds_iff.mp hnear
  have hm : 0 < min δ (min (σ/2) (Real.pi/3)) :=
    lt_min hδ (lt_min (by linarith only [hσ0]) (by linarith [Real.pi_pos]))
  obtain ⟨ε,hε,hεm⟩ := exists_between hm
  have hεδ : ε < δ := hεm.trans_le (min_le_left _ _)
  have hεσ : ε < σ/2 := hεm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεπ : ε < Real.pi/3 := hεm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨x,hx,hc,hcap1,hcap2,he⟩ := profile_realized σ ε hσ0 hσ hε hεσ hεπ
  have hmemb : x 0 ∈ capValues σ := ⟨x,hx,hc,hcap1,hcap2,rfl⟩
  have hlow : a < x 0 := by
    rw [he]
    apply hclose
    simpa only [Real.dist_eq,sub_zero,abs_of_pos hε] using hεδ
  exact (not_lt_of_ge (ha hmemb)) hlow

end CFMPOriginalCapSharpness520Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  let name := ``CFMPOriginalCapSharpness520Transient.original_equal_cap_sharp
  unless (env.checked.get.find? name).isSome do
    Lean.throwError "CFMP520 checked target missing"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP520 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP520 CHECKED {name} axioms={axioms}"
