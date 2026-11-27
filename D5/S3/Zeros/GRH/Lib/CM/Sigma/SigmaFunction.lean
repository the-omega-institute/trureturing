/- GID: D5/S3/Zeros/GRH/Lib/CM/Sigma/SigmaFunction
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/CM/Sigma/SigmaFunction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.CM.Sigma.SigmaFunction. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/CM/Sigma/SigmaFunction.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Shimura.ComplexTheta.ThetaDimension
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.HuaIntegral
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Sigma and theta functions of a lattice, addition and doubling formulas, uniformisation
(known result; see Lib.CM.Sigma.CurveTheta).

This file: From degree two on, theta functions have no common zero. Sigma function as odd canonical
theta function; zeros, dimension, addition formula. -/

open AddSubgroup Complex ComplexConjugate IsAppellHumbert Module PeriodPair Set thetaSpace

variable {V : Type} [FinComplexSpace V] (L : PeriodPair) {f g : ℂ → ℂ}

/-- If f, g are entire functions on a finite-dimensional complex space with fg = 0 and f ≠ 0,
then g = 0. -/
lemma eq_zero_of_entire_mul_eq_zero {f g : V → ℂ} (a : Differentiable ℂ f) (b :
  Differentiable ℂ g) (h : f * g = 0)
  (n : f ≠ 0) : g = 0 := (Function.ne_iff.1 n).rec fun z e ↦ AnalyticOnNhd.eq_of_eventuallyEq
  (fun _ _ ↦ analyticAt_of_eventually_differentiable (.of_forall b)) analyticOnNhd_const
  (((a z).continuousAt.eventually_ne e).mono (by simp_all [funext_iff]; grind))

/-- For Appell–Humbert data (B, χ) with positive Riemann form and n ≥ 2, the theta functions of
type (nB, χⁿ) have no common zero. -/
lemma IsAppellHumbert.exists_apply_ne_zero {L : Submodule ℤ V} [IsFullRankLattice L] {B :
  LatticeForm L} {χ : V → ℂ} (hB : IsAppellHumbert B χ)
  [IsPosRiemann B] z : ∀ n > 1, ∃ f ∈ (n • B).thetaSpace (χ ^ n), f z ≠ 0
  | n + 2, _ => hB.exists_theta_ne_zero.rec fun _ ⟨k@⟨_, _⟩, hs⟩ ↦ not_subset.1 fun h ↦ hs (((
add_left_surjective z).comp ((MulAction.surjective₀ (by norm_cast : -(n + 1 : ℝ) ≠ 0)).comp
(add_left_surjective (-z)))).injective_comp_right (eq_zero_of_entire_mul_eq_zero k.1 (by fun_prop)
    (funext fun a ↦ by simpa [thetaShift_apply] using
    (h ((mul (thetaShift_mem (pow k n.succ) (-z + a)) (thetaShift_mem k _)).imp_right (by
    simp [exp_neg, field, succ_nsmul, mul_add, add_mul, exp_add, pow_succ]))).symm) hs))

lemma PeriodPair.eq_of_eq_off_lattice t (h : ∀ z, z + t ∉ L.lattice → f z = g z) (k : Differentiable
  ℂ fun z ↦ (f z, g z) := by fun_prop) : ∀ z, f z = g z := ((countable_range (L.lattice.subtype · -
  t)).dense_compl ℝ).induction (by aesop) (isClosed_diagonal.preimage k.continuous)

/-- The area |Im(ω̄₁ω₂)| of the fundamental parallelogram spanned by the periods ω₁, ω₂ of the
period pair L. -/
def PeriodPair.area := |(conj L.ω₁ * L.ω₂).im|

/-- The hermitian form (l, z) ↦ (π/A)·l̄·z on ℂ, A the area of the lattice of L, as a map
real-linear in l and complex-linear in z. -/
noncomputable def PeriodPair.hermitianForm :
    LatticeForm L.lattice := (.pi / L.area) • .restrictScalars ℝ (.mul ℂ ℂ) ∘L conjCLE

/-- Multiplication by a maps the lattice of L into that of M, and aā·area(L) = N·area(M); for a
≠ 0, an isogeny of degree N. -/
@[simp] def PeriodPair.IsIsogeny M a (N : ℕ) := (∀ x ∈ L.lattice, a * x ∈ lattice M) ∧ a * conj a *
    L.area = N * M.area

@[simp] lemma area_pos : 0 < L.area := by        simpa [area, Basis.det, Basis.toMatrix,
  det_succ_column_zero'] using basisOneI.isUnit_det L.basis

/-- For a period lattice Λ and complex number w, the complex number 1 if w/2 lies in Λ and −1
otherwise. -/
noncomputable def sigmaSign w := ite (w / 2 ∈ L.lattice) (1 : ℂ) (-1)

@[simp] lemma hermitianForm_apply l z : L.hermitianForm l z =
  Real.pi / L.area * (z * conj l) := by simp [hermitianForm, field]

/-- The Riemann form of the hermitian form (l, z) ↦ (π/A)·l̄·z of a period pair L is E(u, v) =
Im(ū·v)/A, where A is the area of the lattice. -/
lemma riemannForm_hermitianForm u v : L.hermitianForm.riemannForm u v =
  (conj u * v).im / L.area := by simp [riemannForm]; field

lemma exists_riemannForm_periods_eq_sign : ∃ k ∈ [1, -1], L.hermitianForm.riemannForm L.ω₁ L.ω₂ =
  (k : ℤ) := by simp; grind [riemannForm_hermitianForm, area, area_pos]

lemma half_mem_lattice_iff_even (m n : ℤ) : (m * L.ω₁ + n * L.ω₂) / 2 ∈ L.lattice ↔ Even m ∧
  Even n := by
  simp [even_iff_two_dvd, ← Rat.den_div_intCast_eq_one_iff, ← L.mul_ω₁_add_mul_ω₂_mem_lattice]
  ring_nf

attribute [local simp] thetaShift_apply Subtype.ext_iff funext_iff mul_pow riemannForm_hermitianForm
  sigmaSign

variable {L : PeriodPair} {m : ℕ} {χ f : ℂ → ℂ}

instance isAppellHumbert_hermitianForm : IsAppellHumbert L.hermitianForm (sigmaSign L) :=
  ⟨by simp [field], by aesop, (exists_riemannForm_periods_eq_sign L).rec (by
  simp_rw [mem_lattice]; rintro k _ _ ⟨a, b, ⟨⟩⟩ _ ⟨c, d, ⟨⟩⟩
  erw [show riemannForm _ _ _ = ↑((c * b - d * a) * k) by simp_all; grind, mul_comm (_ * I),
    exp_int_mul]
  simp [neg_one_zpow_eq_ite, parity_simps,
    half_mem_lattice_iff_even]; grind [half_mem_lattice_iff_even L (a + c) (b + d)])⟩

/-- If multiplication by the complex number a maps the lattice of L into the lattice of M, then
a·ā·area(L) = N·area(M) for some natural number N. -/
lemma exists_isIsogeny_of_mul_mem_lattice {M a} (ha : ∀ x ∈ L.lattice, a * x ∈ lattice M) : ∃ N,
  L.IsIsogeny M a N := (isAppellHumbert_hermitianForm.le_dualLattice (ha _ L.ω₁_mem_lattice) _
  (ha _ L.ω₂_mem_lattice)).imp' Int.natAbs fun _ ↦ (⟨ha, mod_cast have := area_pos M
  by simp_all [← ·, mul_mul_mul_comm, conj_mul', mul_conj', sq, abs_div, area]⟩)

instance : IsPosRiemann L.hermitianForm := ⟨by simp [← normSq_apply]⟩

lemma IsAppellHumbert.finrank_thetaSpace_nsmul [h : IsAppellHumbert L.hermitianForm χ] [NeZero m] :
  finrank ℂ ((m • L.hermitianForm).thetaSpace (χ ^ m)) = m := by
  simpa [ZLattice.rank ℝ] using (h.nsmul m).finrank_sq_eq_relIndex.2.1.trans
    ((congrArg index (le_antisymm (fun ⟨a, _⟩ l ↦ by use ⟨a / m,
    mem_dualLattice_nsmul.2 (h.le_dualLattice ?_)⟩ <;> simp [↓nsmul_eq_mul']; exact l) (by
  rintro _ ⟨⟨x, c⟩, ⟨⟩⟩
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨k⟩⟩ := c _ L.ω₁_mem_lattice, c _ L.ω₂_mem_lattice,
    exists_riemannForm_periods_eq_sign L
  use mem_lattice.2 ⟨k * b, -k * a, by
    simp_all [Complex.ext_iff]; casesm* _ ∧ _, _ ∨ _ <;> simp_all <;> grind⟩))).trans
    (index_range_nsmul (RealComplexForm.dualLattice _) m))

/-- For Appell–Humbert data (H, χ) on L, a nonzero theta function f with f(0) = 0 has simple
zeros exactly at the lattice points, and ℘f² (extended by f′² on the lattice) and f² span
the theta functions of type (2H, χ²). -/
lemma IsAppellHumbert.thetaSpace_two_eq_span [h : IsAppellHumbert L.hermitianForm χ] (hf :
  f ∈ L.hermitianForm.thetaSpace χ) (hf0 : f ≠ 0) (h0 : f 0 = 0)
  : let Q z := if z ∈ L.lattice then deriv f z ^ 2 else ℘[L] z * f z ^ 2
  (∀ z, f z = 0 ↔ z ∈ L.lattice) ∧ (∀ z ∈ L.lattice, deriv f z ≠ 0) ∧
    (2 • L.hermitianForm).thetaSpace (χ ^ 2) = Submodule.span ℂ {Q, f ^ 2} := by
  intro Q; have := (hf.2 · · 0)
  have : Differentiable ℂ Q := fun z ↦ .congr_of_eventuallyEq (f := ite (z ∈ L.lattice) (dslope f z
    ^ 2 - (z⁻¹ • f) ^ 2) 0 + ℘[L - z] * f ^ 2) (by split <;> rcases hf.1, (hf.1.analyticAt z
    ).choose_spec.has_fpower_series_dslope_fslope.analyticAt <;> fun_prop) (.mono
    (L.compl_lattice_sdiff_singleton_mem_nhds z) (by split <;> simp [*, dslope,
    weierstrassPExcept_of_notMem] <;> grind [slope_def_field, weierstrassPExcept_add L ⟨z, _⟩]))
  have := congr($(((LinearIndependent.pair_iff' (by simp [*])).2 fun c e ↦ hf0
    (hf.1.contDiff.analyticOnNhd.eq_of_frequently_eq analyticOnNhd_const
    (((tendsto_cobounded_of_meromorphicOrderAt_neg ((L.order_weierstrassP 0 (by simp)).trans_lt (by
    decide))).eventually_ne_cobounded c).frequently.mono (by simp_all; grind)))
    ).span_eq_top_of_card_eq_finrank (b := ![⟨_, pow hf 2⟩, ⟨Q, this, Subtype.forall'.2 fun l
    ↦ L.eq_of_eq_off_lattice 0 (by simp [Q, add_mem_cancel_right, hf.2, ← exp_nsmul]; grind)⟩])
    (by simp [finrank_thetaSpace_nsmul])).map (thetaSpace ..).subtype)
  simp_all [Submodule.map_span, image_pair, SetLike.ext_iff, Submodule.mem_span_pair, ← forall_and]
  intro; grind [h.exists_apply_ne_zero ‹_› 2 (by lia)]

/-- For every period lattice Λ there is an odd theta function f with f′(0) = 1 for the hermitian
form (π/A)·l̄·z, A the area, and the multiplier equal to 1 on 2Λ and −1 elsewhere.

Known result: Sigma and theta functions of a lattice, addition and doubling formulas,
uniformisation. -/
lemma exists_sigma : ∃ f ∈ L.hermitianForm.thetaSpace (sigmaSign L), f.Odd ∧ deriv f 0 = 1 := by
  let ⟨f, hf, hf0⟩ := (@isAppellHumbert_hermitianForm L).exists_theta_ne_zero
  have hg := sub_mem hf (hf.imp (·.comp differentiable_neg) (by simp_all [neg_div, ↓neg_add]))
  have e m := hf.2 _ (mem_lattice.2 ⟨m, 1, rfl⟩) ((m * L.1 + L.2) / -2)
  refine ⟨_, Submodule.smul_mem _ _ hg, ?_, (deriv_const_mul_field _).trans (inv_mul_cancel₀
    ((thetaSpace_two_eq_span hg (fun E ↦ L.ω₁_div_two_notMem_lattice (((thetaSpace_two_eq_span
    (thetaShift_mem hf (L.ω₂ / 2)) (by simpa using
    (add_right_surjective _).injective_comp_right.ne hf0) ?_).1 _).1 ?_)) ?_).2.1 0 ?_))⟩ <;>
    simp_all [-sub_eq_zero, ↓half_mem_lattice_iff_even, Function.Odd] <;> grind [e 0, e 1, exp_zero]

/-- The sigma function of L: a chosen odd theta function for the lattice, the form H and the
multiplier `sigmaSign`, with derivative 1 at 0. -/
noncomputable def PeriodPair.σ L := (@exists_sigma L).choose

/-- The sigma function of L is entire, and σ(z + l) = ±exp(π(l̄z + |l|²/2)/A)·σ(z) for l in the
lattice Λ of area A, with sign + if l/2 ∈ Λ and − otherwise. -/
lemma sigma_mem_thetaSpace : L.σ ∈ L.hermitianForm.thetaSpace (sigmaSign L) := by grind [σ]

@[fun_prop] lemma differentiable_sigma : Differentiable ℂ L.σ := sigma_mem_thetaSpace.1

/-- The sigma function of a period pair L is odd: σ(−z) = −σ(z) for all complex z. -/
@[simp] lemma sigma_neg z : L.σ (-z) = -L.σ z := exists_sigma.choose_spec.2.1 z

@[simp] lemma sigma_apply_zero : L.σ 0 = 0 := by grind [@sigma_neg L 0]

/-- The sigma function of a period pair L has derivative 1 at 0. -/
@[simp] lemma deriv_sigma_zero : deriv L.σ 0 = 1 := by grind [σ]

/-- The sigma function is not identically zero. -/
lemma PeriodPair.σ_ne_zero : L.σ ≠ 0 := (by simpa [·] using @deriv_sigma_zero L)

@[simp] lemma sigma_eq_zero_iff {z} : L.σ z = 0 ↔ z ∈ L.lattice :=
  (thetaSpace_two_eq_span sigma_mem_thetaSpace σ_ne_zero sigma_apply_zero).1 z

/-- Addition formula for the sigma function of L: for u and v outside the lattice, σ(u + v)·σ(u
− v) = (℘(v) − ℘(u))·σ(u)²·σ(v)².

Known result: Sigma and theta functions of a lattice, addition and doubling formulas,
uniformisation. -/
lemma sigma_add_mul_sigma_sub {u v} : u ∉ L.lattice → v ∉ L.lattice → L.σ (u + v) * L.σ (u - v) =
    (℘[L] v - ℘[L] u) * (L.σ u ^ 2 * L.σ v ^ 2) := by
  have ⟨_, _, e⟩ := Submodule.mem_span_pair.1 ((thetaSpace_two_eq_span sigma_mem_thetaSpace
    L.σ_ne_zero sigma_apply_zero).2.2.le (x := fun z ↦ L.σ (z + v) * L.σ (z - v))
    ⟨by fun_prop, by simp_all [add_right_comm, sigma_mem_thetaSpace.2, exp_add,
    add_sub_right_comm, exp_sub, two_mul, -hermitianForm_apply, ← exp_nsmul, field]⟩)
  grind [sigma_eq_zero_iff, by simpa using congr(($e 0, $e v, $e u))]
