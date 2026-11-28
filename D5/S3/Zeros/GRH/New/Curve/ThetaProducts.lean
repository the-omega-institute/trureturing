/- GID: D5/S3/Zeros/GRH/New/Curve/ThetaProducts
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Curve/ThetaProducts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Curve.ThetaProducts. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Curve/ThetaProducts.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Curve.FormalParameter
import D5.S3.Zeros.GRH.New.Curve.PeriodDefs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Normal form of theta series at non-split primes (see New.Curve.FormalParameter).

This file: Theta products along tight frames: integral up to one exponential coupling partner
places. -/

open MvPowerSeries Finset ComplexConjugate LinearTopology NumberField IsLocalRing CharP


attribute [local simp] subst_comp_subst_apply subst_mul subst_smul constantCoeff_subst_eq_zero
  sum_pow_char_pow smul_sum pderiv_X sum_pow_char smul_pow Real.rpow_neg norm_p_eq_inv
variable {p Q J} [fp : Fact p.Prime] [CommRing Q] [CharP Q p] [Fintype J] (P : Parameters) (s)

/-- In characteristic p, let e = 2, or e = 1 and ρ hold; let t_i − t_i^{p^e} = L_i and t_i^{p^n}
= 0 for n ≥ B. If ∑L_i^{p^j+1} = 0 for odd j (all j if ρ), then ∑t_i^{p+1} = 0 and
∑t_i^{p+p^e} = 0. -/
lemma sum_pow_eq_zero_of_null {B e ρ} {t L : J → Q} (he : e = 1 ∧ ρ ∨ e = 2) (ht : ∀ i,
  t i - t i ^ p ^ e = L i) (t0 : ∀ i, ∀ n ≥ B, t i ^ p ^ n = 0) (hq : ∀ j, Odd j ∨ ρ → ∑ i, L i ^
  p ^ j * L i = 0) : ∑ i, t i ^ (p + 1) = 0 ∧ ∑ i, t i ^ (p + p ^ e) = 0 := by simp (disch := grind)
  [(eq_sum_pow_of_sub_pow_eq (ht _) B).trans ∘ add_eq_left.2, sum_mul_sum, ← pow_mul,
  @sum_comm _ _ J, ← pow_add p, ← pow_succ, ↓pow_add (t _), fun a b (h : Odd (a + b) ∨ ρ) ↦ (by
  induction a, b using Nat.recDiagAux <;> simp (disch := grind [fp.1.pos]) [*, pow_succ, pow_mul,
    ← mul_pow, ← sum_pow_char, mul_comm (L _)] : ∑ i, L i ^ p ^ a * L i ^ p ^ b = 0)]

/-- Over a commutative ring of prime characteristic p, let power series t_i have t_i(0) = 0, t_i
− t_i^{p²} = ∑_v r_{v,i}X_{v,c}. Then ∑_i r_{x,i}t_i^p has nonzero coefficients exactly at
the X_{y,c}^{p^j} with j odd and ∑_i r_{y,i}^{p^j}r_{x,i} ≠ 0. -/
lemma coeff_sum_frob_ne_zero_iff {Φ I} [Fintype Φ] {r : Φ → J → Q} {t : J → MvPowerSeries (Φ × I) Q}
    (t0 : ∀ i, constantCoeff (t i) = 0) x {c} (ht : ∀ i, t i - t i ^ p ^ 2 = ∑ v, C (r v i) * X
    (v, c)) d : coeff d (∑ i, t i ^ p * C (r x i)) ≠ 0 ↔ ∃ n y,
    ∑ i, r y i ^ p ^ (2 * n + 1) * r x i ≠ 0 ∧ d = .single (y, c) (p ^ (2 * n + 1)) := by
  rcases fp.1.one_lt, charP_of_injective_ringHom (@C_injective (Φ × I) Q _)
  simp (disch := grind [Nat.lt_pow_self]) [congrArg (· ^ p) (eq_sum_pow_of_sub_pow_eq (ht _)
    d.degree), add_pow_char, ← pow_mul, ← pow_succ, ← smul_eq_C_mul, sum_mul, @sum_comm _ _ J,
    coeff_X_pow, coeff_eq_zero_of_constantCoeff_nilpotent (m := 1), ← sum_product']
  use (by grind [exists_ne_zero_of_sum_ne_zero ·]), fun ⟨n, y, _⟩ ↦ by rw [sum_eq_single (n, y)] <;>
    grind [Nat.lt_pow_self, Nat.pow_right_inj, Finsupp.degree_single, Finsupp.single_eq_single_iff]

namespace Parameters

variable [PadicPlace p]

/-- The set of series ∏ι(U_{y_{j,k}}θ)(ι(b w_j†)z_k) over ℂ_p, over j and k ∈ c, with (w_j) a
tight frame of length M, |ιb| = r, nδy_{j,k} ∈ Λ, p prime to Mn;
U_y = `CMLattice.twistedTranslate` 1 y, and θ, Λ are those of `Parameters.cmCurve`. -/
def thetaProducts (δ : 𝓞 P.K) r c [Fintype c] := {Θ | ∃ J, ∃ (_ : Fintype J) (w : J → P.E s), ∃ M n
  b, ∃ y : J × c → ℂ, IsTightFrame w 1 M ∧ Θ = ∏ i, (taylorVia ιₚ (P.cmCurve.twistedTranslate 1 (y
  i) P.cmCurve.θ)).subst (linearSeries fun (τ, k) ↦ ite (k = i.2) (ιₚ (b * conj (Φ τ (w i.1)))) 0) ∧
  (p.Coprime M ∧ p.Coprime n) ∧ ‖ιₚ b‖ = r ∧ ∀ i, n * δ * y i ∈ P.cmCurve.Λ}

/-- Let (p/d) ≠ 1, (w_i) a tight frame of length M, β ∈ 𝔬. Then z_{v,i} = βι(w̄_{i,v}) ∈ 𝔬, and in
characteristic p, modulo elements of valuation ≥ (1 − (p/d))/2,
∑_i z_{v,i}^{p^j} z_{v′,i} is β^{p^j+1}M if
v′ = −p^j v, else 0 (j odd or p = d). -/
lemma exists_frame_rows_frob (hp : chiK P.d p ≠ 1) {w : J → _} {M} (hw : IsTightFrame w 1 M) β :
  ∃ z : _ → _ → valRingCp p, (∀ v i, z v i = β.1 * ιₚ (conj (Φ v (w i)))) ∧ ∀ (Q : Type)
  [CommRing Q] [CharP Q p] (g : _ →+* Q), (∀ x, ‖x.1‖ ≤ p ^ ((chiK P.d p - 1) / 2 : ℝ) → g x = 0) →
  ∀ j, Odd j ∨ p = P.d → ∀ v v', ∑ i, g (z v i) ^ p ^ j * g (z v' i) =
  ite (P.placeOfInt s (-p ^ j) * v = v') (g β ^ p ^ j * g β * M) 0 := by
  let N := P.N₁ s
  let x i := IsIntegralClosure.mk' (𝓞 (P.E s)) (N * w i) (algebraMap_mem_Ô.1 (by
    simpa [N, mul_assoc, finiteImage, WeilData.α] using mul_mem N₁_mul_α_mem (hw.1 i)))
  have hd := hp ∘ @chiK_eq_one_of_dvd P p s fp.1; obtain ⟨α, ⟨⟩⟩ : ↑N ∣ β := IsUnit.dvd (by
    simpa [← residue_ne_zero_iff_isUnit, cast_eq_zero_iff])
  let f v := ((ιₚ.comp (Φ v)).comp (algebraMap _ (P.E s))).codRestrict (valRingCp p)
    (id (norm_ringOfIntegers_le (ιₚ.comp _)))
  use fun v i ↦ f v (star (x i)) * α, by simp [f, x, field], fun Q _ _ g h j _ v v' ↦ ?_
  simpa [by simpa using (frob_ext hd (g.comp (f v)) j (.inr ⟨rfl, rfl⟩)).2 ⟨rfl, by
    obtain ⟨⟨⟨⟩, _⟩ | _⟩ := chiK_cases P.d p, h (f v (P.sqrtNegDInE s)), congr(√‖(f v (algebraMap _
      _ $(QuadField.sqrtNegDInt_sq P.d))).1‖) <;> simp_all [sqrtNegDInE, Real.sqrt_eq_rpow P.d,
      neg_div]⟩, apply_ite, sum_mul, ← iterateFrobenius_def, mul_mul_mul_comm _ (iterateFrobenius Q
    p j _), mul_right_comm _ (M : Q)] using congrArg (g · * (g α ^ p ^ j * g α)) (show
    ∑ i, f v (galOfPlaceInt (P.placeOfInt s (-p ^ j)) (x i)) * f v' (star (x i)) = ite (_ = v') (N *
    N * M) 0 by ext; simpa [f, x, ← phi_mul, mul_comm v, mul_mul_mul_comm _, mul_sum, apply_ite]
    using congr(N * N * ιₚ $(hw.2 ..)))

/-- For (p/d) ≠ 1, some ϖ, π with |ϖ| = p^{−ρ_p} (ρ_p = `nonsplitWeight`),
|π| = p^{((p/d)−1)/2} serve all r ≤ 1 and Θ in
`Parameters.thetaProducts` (δ = 1): `IsIntegralOnNullCone` holds for each B, with couplings
j ≤ log_p B, j odd or p = d. If (p/d) = −1 and r = 1, Θ(ϖz) = exp(κΨ)V with |κ| = p^{1−1/(p−1)}, Ψ,
V integral, Ψ(0) = 0, and ∂_xΨ has unit coefficients exactly at the z_y^{p^j}, j odd, −p^j y = x.

Normal form of theta series at non-split primes. -/
lemma thetaProducts_normal_form (hp : chiK P.d p ≠ 1) : ∃ ϖ π, ‖ϖ‖ = p ^ (-nonsplitWeight P.d
  p) ∧ ‖π.1‖ = p ^ ((chiK P.d p - 1) / 2 : ℝ) ∧ ∀ {I} [Fintype I], ∀ r ≤ 1, ∀ Θ ∈ P.thetaProducts
  s 1 r I, (∀ B, IsIntegralOnNullCone (fun j v ↦ P.placeOfInt s (-p ^ j) * v) {j ≤ p.log B | Odd j ∨
  p = P.d} ϖ π B Θ) ∧ (chiK P.d p = -1 → r = 1 → ∃ (κ : ℂ_[p]) (Ψ V : MvPowerSeries _
  (valRingCp p)), ‖κ‖ = p ^ (1 - 1 / (p - 1) : ℝ) ∧ constantCoeff Ψ = 0 ∧ Θ.rescale (fun _ ↦ ϖ) =
  expSubst (κ • seriesToCp Ψ) * seriesToCp V ∧ ∀ x d, (pderiv x (Ψ.map (residue _))).coeff d ≠ 0 ↔
  ∃ j y, Odd j ∧ (P.placeOfInt s (-p ^ j) * y.1, y.2) = x ∧ d = .single y (p ^ j)) := by
  obtain ⟨⟨e, ϖ, π, S, E, ⟨-, hϖ, hπ, π1, S0, ε, _⟩, H⟩, hP⟩ := P.cmCurve.exists_formal_parameter,
    fp.1
  obtain ⟨_, _, _, R, _, hπ', he, ⟨⟩, ψ0, hV⟩ := H hp (P.thirteen_le_of_chiK_ne_one hP hp)
  set ψ := _ + π • R; use ϖ, π, hϖ, hπ'; rintro I _ _ ha Θ ⟨J, _, w, M, n, b, y, hw, _, hM, ⟨⟩, hy⟩
  choose N κ hκ v ev using hV n hM.2
  obtain ⟨z, hz, hF⟩ := hπ' ▸ P.exists_frame_rows_frob s hp hw ⟨_, mul_mem hκ.1.le ha⟩
  simp [hP.coprime_iff_not_dvd] at hM S0 ψ0 hy
  let c (i : J × I) := @PowerSeries.substAlgHom (valRingCp p) _ _ (valRingCp p) _ _
    (∑ v, z v i.1 • X (v, i.2)) (by simp); let Ψ := ∑ i, c i ψ
  have cX i : c i .X = _ := substAlgHom_X ..
  refine Exists.elim ?_ fun V (⟨Ψ0, eV, cS⟩ : _ ∧ _ ∧ ∀ i, constantCoeff (c i S) = 0) ↦
    ⟨fun B τ Z Z0 hq m hm ↦ ?_, fun h _ ↦ ⟨κ, Ψ, V, by simp [*], Ψ0, eV, fun x d ↦ ?_⟩⟩
  use ∏ i, c i (v (y i) (hy _ _))
  simp (disch := simp [*]) [c, Ψ, map_subst, expSubst_sum, *, PowerSeries.substAlgHom, -map_mul]
  simp [linearSeries, *, PowerSeries.subst, Fintype.sum_prod_type, mul_smul]
  let σ := substAlgHom (R := valRingCp p) (hasSubst_of_constantCoeff_zero Z0)
  have ⟨Q, φ, K⟩ : ∃ Q : CommRingCat, ∃ φ : _ →+* Q, RingHom.ker φ = (basis τ (valRingCp p)
    ((Valuation.leIdeal _ ‖π.1‖₊).toTwoSided, m)).asIdeal := ⟨.of _, _, Ideal.mk_ker⟩
  simp [Ideal.ext_iff, basis, ← NNReal.coe_le_coe] at K
  have hT := (K (σ Ψ)).1 (by
    nontriviality
    have K0 x := by simpa [coeff_C, apply_ite, ite_apply, @forall_comm (_ ≤ m)] using (K (C x)).2
    have := of_eq_zero hP (by simpa [hπ] using K0 p)
    have t0 f e n hn := (K (f ^ p ^ n)).2 fun d h ↦ by
      rw [coeff_eq_zero_of_constantCoeff_nilpotent e (Nat.one_add_le_iff.2 (((d.degree_mono
        h).trans hm).trans_lt (p.lt_pow_of_log_lt hP.one_lt hn)))]; simp
    obtain ⟨E, hq⟩ := (congr(φ <| σ <| c · $ε)), hq φ
    simp [cX, K0, @smul_eq_C_mul τ, -Prod.forall, Fintype.sum_prod_type_right] at E t0 hq
    obtain ⟨hq⟩ := (iff_self_and.2 (sum_pow_eq_zero_of_null (he.imp_right (·.1)) E fun _ ↦ t0 _ (by
      simp [σ, cS, Z0]))).1 fun j h ↦ by
      simp [σ, ↓substAlgHom_X, mul_pow, sum_mul_sum, by simpa using hF _ (φ.comp C) K0 j h,
        mul_mul_mul_comm _ (φ _ ^ _), @sum_comm _ _ J, ← sum_mul, ← mul_sum, Fintype.sum_prod_type]
      by_cases! j ≤ p.log B <;> simp [*]
    simp [ψ, Ψ, *, ← mul_sum, @smul_eq_C_mul τ, sq]
    cases he <;> simp [by simpa using hq 0, *])
  apply_fun subst (seriesToCp <| Z ·) at eV
  simp [σ, ← map_subst, Ψ0, Z0, rescale_eq_subst, PowerSeries.subst] at eV hT
  refine eV ▸ sum_mem fun d h ↦ mul_mem ((PowerSeries.coeff_subst (by simp [*]) ..).symm.subst
    (finsum_induction _ (by simp) @(valRingCp p).add_mem fun k ↦ ?_)) (by simp)
  simp [coeff_pow, mul_sum]; refine sum_mem fun l e ↦ (?_ : ‖_‖ ≤ 1)
  simp at h e ⊢; grw [← rpow_le_norm_factorial, hT] <;> (try simp [*, hP.pos, ← Real.rpow_add,
            ← Real.rpow_mul_natCast, Real.rpow_pos_of_pos]); ring_nf; simp
  grw [← h, ← e.1, ← single_le_sum _ ‹_›] <;> simp
  obtain ⟨⟨⟩⟩ := he.resolve_left (by simp [·, chiK] at h)
  have K (x : valRingCp p) h := (residue_eq_zero_iff x).2 (π1.not_ge <|
    isUnit_integer_iff_norm_eq_one.1 · ▸ h)
  have E i := congr((fun f ↦ (f, pderiv x f)) (map (residue _) (c i $ε)))
  simp [cX, @smul_eq_C_mul (_ × I), K, ← map_natCast C, cast_eq_zero] at E
  simpa [ψ, cast_eq_zero, Ψ, *, ← mul_sum, @smul_eq_C_mul (_ × I), ← map_natCast C, Odd, ite_and,
    Fintype.sum_prod_type, Prod.ext_iff, cast_eq_zero_iff, hF _ _ K] using
    coeff_sum_frob_ne_zero_iff (by simp [cS]) x.1 (E · x.2 |>.1) d
