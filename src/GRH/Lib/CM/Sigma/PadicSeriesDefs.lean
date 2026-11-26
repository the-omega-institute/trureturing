import GRH.Lib.CM.Sigma.CurveTheta
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Supporting lemmas (textbook or folklore).

Part of: Sigma and theta functions of a lattice, addition and doubling formulas, uniformisation
(known result; see Lib.CM.Sigma.CurveTheta).

This file: Sections of degree m on the curve: division and spanning monomials. Taylor series at 0 of
analytic functions: ring laws and injectivity. Ring of integers of C_p and inclusion of integral
power series. -/

open Complex Nat AnalyticAt ComplexConjugate Finset Function IsAppellHumbert PowerSeries Submodule

variable {d} (C : CMLattice d) (x : ℕ × ℕ × ℕ) {f g : ℂ → ℂ} {p : ℕ} [Fact p.Prime] {σ : Type}

/-- The degree a + 2b + 3c of a triple (a, b, c): the degree of the monomial θ^a·σ^{2b}·G^c
(`CMLattice.monomialSection`) as a section. -/
@[simp] abbrev CMLattice.monomialDeg := x.1 + x.2.1 * 2 + x.2.2 * 3

/-- For a triple (a, b, c) of natural numbers, the function θ^a·σ^{2b}·G^c on ℂ, with σ the
sigma function and G = `CMLattice.phiThetaCube` the entire function φθ³. -/
@[local simp] noncomputable def CMLattice.monomialSection :=
  C.θ ^ x.1 * ((C.σ ^ 2) ^ x.2.1 * C.phiThetaCube ^ x.2.2)

@[fun_prop] lemma CMLattice.differentiable_monomialSection :
  Differentiable ℂ (C.monomialSection x) := by fun_prop [monomialSection, phiThetaCube]

/-- For x = (a, b, c) in ℕ³ and z + t ∉ Λ, the monomial θ^a·σ^{2b}·G^c (G the entire extension of
φθ³) has value θ(z)^{a+2b+3c}·ξ(z)^b·φ(z)^c at z. -/
lemma CMLattice.monomialSection_eq z (hz : z + C.t ∉ C.Λ) :
    C.monomialSection x z = C.θ z ^ monomialDeg x *
  (C.translatedWp z ^ x.2.1 * C.translatedWpDeriv z ^ x.2.2) := by simp [phiThetaCube_spec, *]; ring

/-- For a CM datum C and x = (a, b, c) in ℕ³, the monomial θ^a·σ^{2b}·G^c, with G the entire
extension of φθ³, is a section of degree a + 2b + 3c. -/
lemma CMLattice.monomialSection_mem : C.monomialSection x ∈ C.sections (monomialDeg x) :=
  ⟨by fun_prop, Subtype.forall'.2 fun l ↦
  C.eq_of_eq_off_lattice C.t (by simp_all [↓monomialSection_eq, translatedWpDeriv, translatedWp,
  add_right_comm _ l.1, C.θ_mem.2, ← exp_nsmul, add_mem_cancel_right, mul_pow]; grind)⟩

/-- Every section of degree 0 of the CM datum C, that is, every entire Λ-periodic function, is
constant. -/
lemma CMLattice.sections_zero_le_const : C.sections 0 ≤ 1 := fun f k ↦
  ⟨_, .symm (funext (by simpa using apply_smul_of_nonpos k 1))⟩

/-- Let g(z) = (U_yθ_D)(az), a ≠ 0, D any CM datum, be a section of degree m of C. A section f of
degree m + k that vanishes at the zeros of g is cg with c in any subspace S containing the sections
of degree k. -/
lemma CMLattice.section_division {e} D y {m k S f g a} (s : C.sections k ≤ S) (hg :
  g ∈ C.sections m) (hf : f ∈ C.sections (m + k)) (a0 : a ≠ 0) (E : g =
  (@twistedTranslate e D 1 y D.θ <| a * ·)) (h : ∀ z, g z = 0 → f z = 0) : ∃ c ∈ S, c * g = f := by
  replace E z : g z = 0 → deriv g z ≠ 0 := E ▸ by simp (disch := fun_prop) [↓deriv_comp_mul_left, θ,
    funext (thetaShift_apply _ _ _), add_assoc, deriv_comp_add_const]; grind [thetaSpace_two_eq_span
    sigma_mem_thetaSpace D.σ_ne_zero sigma_apply_zero, CMLattice, exp_ne_zero]
  obtain ⟨⟨u⟩, ⟨v⟩⟩ := hf, hg; let T z h : ℂ → ℂ := ite (g z = 0) (dslope h z) h
  have A {z h} := ((by simp [T, apply_ite, ← differentiableOn_univ, differentiableOn_dslope] :
    Differentiable ℂ h → Differentiable ℂ (T z h)) · z)
  use fun z ↦ (T z f / T z g) z, s ⟨fun z ↦ ((A u).div (A v) ?n).congr_of_eventuallyEq
    (((A v).continuousAt.eventually_ne ?n).mono ?_), ?_⟩, funext ?_ <;> simp +contextual (disch :=
    first | fun_prop | trivial) [T, dslope, update, slope, *, ite_apply, ← deriv_comp_add_const,
    exp_add, add_div] <;> grind [C.isAppellHumbert_multiplier.ne_zero, exp_ne_zero, pow_ne_zero]

/-- Every section of degree m is a complex linear combination of the functions θ^a σ^{2b} G^c
(that is, θ^m ξ^b φ^c) with c ≤ 1 and a + 2b + 3c = m. -/
lemma CMLattice.sections_le_span_monomialSection m : C.sections m ≤ span ℂ (C.monomialSection ''
  {x | x.2.2 ≤ 1 ∧ monomialDeg x = m}) := m.twoStepInduction (C.sections_zero_le_const.trans
  (by aesop)) ((eq_span_singleton_of_mem_of_finrank_eq_one finrank_thetaSpace_nsmul C.θ_mem
  (ne_iff.2 ⟨0, by simp⟩)).trans_le (span_mono (by simp; use 1, 0; simp))) fun m _ ih f k ↦ by
  let x := (0, m / 2 + 1 - m % 2, m % 2)
  have F := sub_mem k (smul_mem _ ((f / C.monomialSection x) (-C.t))
    (by convert C.monomialSection_mem x using 2; lia))
  refine (sub_mem_iff_left _ (smul_mem _ _ (subset_span (by grind)))).1 ((map_span_le (.mulRight ..)
    ..).2 ?_ (C.section_division C 0 ih C.θ_mem (add_comm 1 _ ▸ F) one_ne_zero (by simp) ?_))
  use fun _ ⟨x, _⟩ ↦ subset_span ⟨x + (1, 0), by simp_all; grind⟩
  simpa [x, t_notMem, by simpa [C.θ_eq_zero_iff.2]
    using congr(($(C.phiThetaCube_sq_add (-C.t))) = 0)] using fun z ↦ (F.2 (z + C.t) · (-C.t))

/-- If 0 ≠ δ ∈ ℤ[ω], δδ̄ = N and δy ∈ Λ, then z ↦ (U_yθ)(δ̄z) is a section of degree N. -/
lemma CMLattice.twistedTranslate_comp_mem [PrimeSevenModEight d] {δ y N} (h : C.IsIsogeny C.1
  (conj δ) N) (h0 : δ ≠ 0) (hy : δ * y ∈ C.Λ) : (C.twistedTranslate 1 y C.θ <| conj δ * ·) ∈
  C.sections N := by convert (thetaShift_mem_of_dual (a := y / conj δ) (mem_dualLattice_nsmul.2
  (C.isAppellHumbert_multiplier.le_dualLattice (Eq.subst ?_ hy))) (C.comp_mul_mem_sections h
  C.θ_mem)) using 2 <;> simp [thetaShift_apply, ← by simpa [ne_of_gt] using h.2] <;> field [h0]

attribute [fun_prop] Differentiable.analyticAt

@[simp] lemma coeff_taylorAtZero n : coeff n (taylorAtZero f) = iteratedDeriv n f 0 / n ! :=
  coeff_mk ..

@[simp] lemma constantCoeff_taylorAtZero : constantCoeff (taylorAtZero f) =
  f 0 := by simp [taylorAtZero]

@[simp] lemma taylorAtZero_const c :
    (taylorAtZero fun _ ↦ c) = PowerSeries.C c := by ext ⟨⟩ <;> simp [iteratedDeriv_const]

@[simp] lemma taylorAtZero_comp_mul a f : taylorAtZero (f <| a * ·) = rescale a (taylorAtZero f) :=
  PowerSeries.ext fun n ↦ by induction n generalizing f <;> simp_all [iteratedDeriv_succ',
  funext (deriv_comp_mul_left _ f), field, pow_add]

lemma eq_of_taylorAtZero_eq : Differentiable ℂ f → Differentiable ℂ g → taylorAtZero f =
  taylorAtZero g → f = g := by
  simp_all [funext_iff, ← taylorSeries_eq_of_entire' 0, inv_mul_eq_div, ← coeff_taylorAtZero]

@[simp] lemma taylorAtZero_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
  taylorAtZero (fun z ↦ f z + g z) = taylorAtZero f + taylorAtZero g :=
  PowerSeries.ext (by simp [*, field, iteratedDeriv_fun_add, contDiffAt])

@[simp] lemma taylorAtZero_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorAtZero (fun z ↦ f z * g z) = taylorAtZero f * taylorAtZero g := PowerSeries.ext (by
  simp [*, coeff_mul, iteratedDeriv_fun_mul, contDiffAt, sum_div, Nat.antidiagonal_eq_image]
  grind [sum_congr, cast_choose, cast_ne_zero])

@[simp] lemma taylorAtZero_eval (hf : AnalyticAt ℂ f 0) P : taylorAtZero (P.eval <| f ·) =
  Polynomial.aeval (taylorAtZero f)
  P := by apply @P.recOnHorner <;> simp +contextual (disch := fun_prop)

@[simp] lemma taylorAtZero_pow (hf : AnalyticAt ℂ f 0) n :
    taylorAtZero (f · ^ n) = taylorAtZero f ^ n := by simpa using taylorAtZero_eval hf (.X ^ n)

/-- The valuation ring 𝔬 of ℂ_p. -/
noncomputable abbrev valRingCp (p : ℕ) [Fact p.Prime] := NormedField.valuation (K := ℂ_[p]).integer

/-- The ring homomorphism from power series over the valuation ring 𝔬 to power series over ℂ_p
induced by the inclusion of coefficients. -/
noncomputable abbrev seriesToCp := MvPowerSeries.map (σ := σ) (valRingCp p).subtype

@[simp] lemma seriesToCp_smul (k : valRingCp p) f : @seriesToCp p _ σ (k • f) =
  k.1 • seriesToCp f := rfl
