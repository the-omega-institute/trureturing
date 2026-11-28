/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/TypeFrobenius
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/LocalGlobal/TypeFrobenius
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.LocalGlobal.TypeFrobenius. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/LocalGlobal/TypeFrobenius.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.LocalGlobal.EigencharCompatibility
import D5.S3.Zeros.GRH.Lib.Adelic.CuspForms.BaseLevel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Local-global compatibility at tame level, away from and at l (known result; see
Lib.GaloisRep.LocalGlobal.LabelCompatibility).

This file: With one ramified character, U equals Frobenius where tame inertia acts non-trivially. -/

open Nat Pi Algebra Finset Fintype Matrix NumberField Polynomial Valued Finset.Nat Finset.Pi

attribute [local simp] algebraMap_eq_smul_one prod_eq_zero_iff mulSingle_apply eval_prod

variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E n} [Field E] [CMType E]
  [Algebra E Ω] [Fintype n] [Nonempty n] {V : Space E n 1} {κ} [V.IsStd] [WeilData E] {w :
  FinPlace E} {hw : star w ≠ w} {A : ClosurePlace} (hA : IsPlaceOver A w) {ϖ u} {s τ :
  decompGroup Gal(Ω/E) A} (hϖ : v ϖ.1 = .exp (-1)) (eϖ : localArtin Gal(Ω/E) A w ϖ = s) (hφ :
  IsFrob A w.q s.1⁻¹) (hu : v u.1 = 1) (e : localArtin Gal(Ω/E) A w u = τ) (hτ :
  ↑τ ∈ inertiaGroup Gal(Ω/E) A) (hℓ : ↑ℓ ∉ w.1) {x : Isotypic V κ} {y} (hy : y ∈ x.1)

include hA hϖ eϖ hφ hu e hτ hℓ hy

/-- At split w ∤ ℓ let s (geometric Frobenius), τ (inertial) lift Art(ϖ), Art(u); 0 ≠ y ∈ x ∩
`parahoricEigenspace` f c; d_i = c(diag, u at i), equal only within blocks of f. In x's Galois
representation s, τ commute, polynomials vanishing at all ιd_i kill τ, and ∏(X −
ι(θ_i(ϖ)d_i^b)) kills sτ^b (b ≥ 0) for an exponent θ nonzero on y. -/
lemma galRep_of_parahoric_type (h0 : y ≠ 0) f {c} : let ρ := localFormRep V κ hw; y ∈
    parahoricEigenspace ρ f c → let F := (x.galRep s).1; let T := (x.galRep
        τ).1; let d i := c (diagGL (mulSingle i u)); (∀ i k, d i = d k → f i = f k) → (∀ p, (∀ i,
          p.IsRoot (ιℓ (d i))) → aeval T p = 0) ∧ Commute F T ∧ ∃ θ, (∃ l, IsExponent ρ (torusChar
          θ) l ∧ l y ≠ 0) ∧ ∀ b, aeval (F * T ^ b) (∏ i, (X - C (ιℓ (θ i ϖ * d i ^ b)))) = 0 := by
  intro ρ ⟨hx, m⟩ F T d hf
  obtain ⟨⟨⟩, hl, θ, h, hθ, σ, hs, z, z', hz⟩ := ‹V.IsStd›.eq_stdSpace,
    hA.valuation_natCast_eq_one_iff.2 hℓ, exists_sorted_of_type (v_uniformizer _) hx (fun _ ↦
    (m _ ⟨·, by aesop (add simp diagonal)⟩)) (fun σ
    h ↦ ⟨_, m _ ⟨permGL_mem_intGL σ, fun _ j c ↦ by simp [σ.symm_apply_eq,
    Fin.ext_iff, ne_of_apply_ne f (hf _ _ (h j u hu) ▸ c).ne']⟩⟩) isUnitary_localFormRep h0
  have hP := (x.attached_galRep hy h0).local_global_of_eigencharacter hz
    ((x.isEigenform hy h0).of_mem_cyclicSpan z' hz.1) hs hA
  have K s x i e a := (hP s x 0 (inv_mem i) e a).elim (·.aeval_eq_zero_of_roots hl i ·.2)
  use fun p H ↦ K _ _ hτ e hu p (by clear * - hu hθ H; aesop), by simpa [div_eq_iff_eq_mul,
    Units.ext_iff] using! (K (_ * _ / _ / _) 1 (div_mem (s.2 ▸ hτ.conj _) hτ) (by simp) (by simp) (X
    - 1) (by simp) :), θ, h, fun b ↦ ?_
  rw [← Equiv.prod_comp σ]
  simpa [*] using (hP (_ * _ ^ b) (_ * u ^ b) 1 (by simpa using (zpow_mem hτ (-b)).mul_iff.2 hφ)
    (by simp [*]) (by simp [*])).2.2.1 hl

/-- Let y in x be pro-p-Iwahori fixed at w ∤ ℓ, the line stabiliser acting by χ of the top left
entry, χ(u) ≠ 0, χ(u)^(n!) ≠ 1. Then tr((τ − 1)M)·G(U)y = tr(G(s)(τ − 1)M)·y via ι, in the Galois
representation of x, for G in ℂ[X], any matrix M, U the Hecke operator of diag(ϖ,1,…,1). -/
lemma hecke_eq_frob_on_parahoricEigenspace χ (o : χ u.1 ≠ (0 : ℂ)) (hζ : χ u ^ (card n)! ≠ 1)
  (G : ℂ[X]) {M} : let ρ := localFormRep V κ hw; let U := heckeCoset ρ.ρ proIwahori (diagGL
      (mulSingle 0 ϖ)); let F := (x.galRep s).1; let T := (x.galRep τ).1 - 1; y ∈
          parahoricEigenspace ρ (min 1) (χ ∘ (· 0 0)) → ιℓ.symm (T * M).trace • aeval U G y
        = ιℓ.symm (aeval F (G.map ιℓ.toRingHom) * T * M).trace • y := by
  intro ρ U F T m
  -- induction on the polynomial; degree one is left
  induction G using recOnHorner generalizing y <;> have k : U y ∈ _ ∧ U y ∈ parahoricEigenspace
    .. := ⟨x.map_mem (heckeFun_mem_localGroupAlgebra hw _) hy, heckeCoset_mem_parahoricEigenspace ρ
    hϖ m⟩ <;> simp [add_mul, add_smul, smul_smul, @mul_comm ℂ, *]
  by_contra
  obtain ⟨⟨d, _⟩, h0, a, b⟩ := heckeCoset_mulSingle_zero_eq hϖ m.1, sub_ne_zero.2 this,
    sub_mem ((x.1 ⊓ _).smul_mem _ k) ((x.1 ⊓ _).smul_mem _ ⟨hy, m⟩)
  have h1 : χ 1 = 1 := (smul_left_injective ℂ h0 (by simpa using b.2 1)).symm
  obtain ⟨K, hc, θ, ⟨l, h : IsExponent ρ .., l0⟩, hF⟩ := galRep_of_parahoric_type hA hϖ eϖ hφ hu e
    hτ hℓ a h0 _ b (by clear * - h1 hζ; simp [apply_ite]; grind [one_pow])
  -- the roots of `T + 1` are `χ u, 1, …, 1`, so `F` is a scalar on the image of `T` (Vandermonde).
  let q := ∏ i ∈ univ.erase 0, (X - C (ιℓ (θ i ϖ)))
  have M : F * T = ιℓ (θ 0 ϖ) • T := by
    ext r c; simpa [q, sub_mul, coeff_zero_prod] using congrFun
      (@eq_zero_of_forall_index_sum_pow_mul_eq_zero _ _ (card n) _ (ιℓ (χ u) ^ ·.1) (fun i ↦
      (q.coeff i • F ^ i.1 * (F - ιℓ (θ 0 ϖ) • 1) * T) r c) (.of_lt_imp_ne fun i j l e ↦ hζ <|
      (dvd_factorial (zero_lt_sub_of_lt l) (sub_lt_of_lt j.2).le).elim (by simp_all [← map_pow,
      pow_mul, pow_sub₀, l.le])) fun b ↦ by
      simpa [prod_ite, filter_eq, filter_ne, mul_comm _ q, q, *, apply_ite, aeval_eq_sum_range' (by
        simp [NeZero.pos] : q.natDegree < card n), sum_range, _root_.smul_pow, sum_mul,
        Matrix.sum_apply, ← smul_sub, mul_left_comm (q.coeff _)] using
        congr($((hF b ▸ (aeval_semiconj (SemiconjBy.mul_right (hc.symm.sub_left (by simp)) ((by
        simpa [SemiconjBy, mul_sub] using (K ((X - 1) * (X - C (ιℓ (χ u))))
          (by simp [*, apply_ite]) :) :
        SemiconjBy T _ (ιℓ (χ u) • 1)).pow_right b)) _).symm :)) r c)) 0
  simp [U, mul_assoc, h.apply_compactMean, compactMean_eq_self y m.1 ▸ h d y,
    coe_normAbsChar_locField, norm_locField_eq_q_zpow, field, *] at l0
