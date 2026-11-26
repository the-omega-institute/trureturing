/- GID: D5/S3/Zeros/GRH/New/Selmer/HeckeString
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/HeckeString
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.HeckeString. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/HeckeString.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.HeckeStableSubspaces
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Strings of roots of Hecke polynomials, from the eigenvalue 1 of a Galois representation.

Part of: Ties hold on forms and weak lifts do not move (see New.Patching.OnePrimeTie).

This file: Weak lifts: Hecke polynomial is the string times a factor integral after normalising. -/


open Matrix Polynomial Fintype ComplexOrder IsUltrametricDist NormedField
variable {ℓ} [ThePrime ℓ] {P} {D : Data P} {r n} [Fintype n]

/-- Let B be monic, C integral, AB ≡ C ≡ A'B coefficientwise modulo the maximal ideal of the
integers of ℚ̄_ℓ, and ‖A'(1)‖ ≥ 1. Then A divides an integral polynomial e with e(1) = 1. -/
lemma exists_integral_multiple_eval_one {A A' B C : (PadicAlgCl ℓ)[X]} (m : B.Monic) (z :
  ∀ i, ‖C.coeff i‖ ≤ 1) (a : ∀ i, ‖(A * B - C).coeff i‖ < 1) (h : ∀ i, ‖C.coeff i - (A' * B).coeff
  i‖ < 1) (u : 1 ≤ ‖eval 1 A'‖) : ∃ e, A ∣ .map (intQpBar ℓ).subtype e ∧ e.eval 1 = 1 :=
  have v : 1 ≤ ‖A.eval 1‖ := by
    grw [← sub_add_cancel A' A, eval_add, norm_add_le_max, eval_eq_sum_range,
      (exists_norm_finsetSum_le ..).choose_spec.2, norm_mul, norm_coeff_le_of_mul_monic m
      (le_supNorm _), (exists_eq_supNorm _).choose_spec, sub_mul, ← sub_add_sub_cancel _ C,
      coeff_add, norm_add_le_max] at u; simp_all [norm_sub_rev (C.coeff _), not_le_of_gt]
  ((A * .C (A.eval 1)⁻¹).lifts_iff_coeff_lifts.2 (by simp [← NNReal.coe_le_coe,
    field, norm_coeff_le_of_mul_monic
    m (by grw [← sub_add_cancel (A * B), coeff_add _ _ ·, norm_add_le_max, a, z, max_self,
    v])])).imp fun e he ↦ ⟨⟨_, he⟩, by simpa [norm_pos_iff.1 (by bound)] using congr(eval 1 $he)⟩

/-- Let T be a continuous function from the Galois group to n × n matrices, T(δ_i) = y^i A, and
y^j − 1 a unit for 1 ≤ j ≤ 4n + 2. For some i, ‖det(1 − T(φ))‖ ≥ 1 for all φ near δ_i. -/
lemma exists_eventually_no_eigenvalue_one {T : AbsGal D → Matrix n n (PadicAlgCl ℓ)} (c : Continuous
  T) (δ : ℕ → _) {y : PadicAlgCl ℓ} {A} (h : ∀ i, T (δ i) = y ^ i • A) (hy : ∀ j ∈ Set.Icc 1
  (4 * card n + 2), ‖y ^ j - 1‖ = 1) : ∃ i, ∀ᶠ φ in nhds (δ i), 1 ≤ ‖(T φ).charpoly.eval 1‖ := by
  by_contra! a
  simp_rw [eval_charpoly, ← mem_ball_zero_iff] at a
  have (i : Fin (card n + 1)) H := a i ((isClosed_ball ..).preimage_of_continuous.compl_mem_nhds
    (by simpa [h] using! ((congrArg valuation (det_aeval_neg_eq_prod_roots (-A)
    (1 - y ^ i.1 • .X))).trans (map_multiset_prod ..)).trans_ge (Multiset.one_le_prod H)))
  choose z μ m H using by simpa using this
  refine z 0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ (.of_lt_imp_ne fun i j a e ↦
    (valuation.map_sub_lt (H j) (H i)).ne ?_) m (by simp))
  simpa [e, mul_assoc, ← sub_one_mul, NNReal.eq_iff, hy (j - i) (by grind), ← pow_sub_mul_pow
    y a.le] using valuation.map_one_sub_of_lt (H i)

variable [PadicIso ℓ] [Fintype r] [Nonempty n] {O : AuxPair D.E r n} {x : Isotypic (stdSpace _
  n) (O.κ, O.detExp)} {f} (hf : f ∈ x.1) (h₀ : f ≠ 0) (h : ∀ g,
  (normalisedRep O x.galRep g).1.charpoly.IsRoot 1)
include hf h₀ h

/-- Let every g have eigenvalue 1 on the normalised representation of the eigenform f. At a
split w ∤ ℓ of prime norm q where f has Hecke polynomial S, the numbers ν q^i, i < n − r,
are roots of S, ν = `AutChar.frobValue` of `AuxPair.a`. -/
lemma isRoot_hecke_string {w hw S i} (hℓ : ↑ℓ ∉ w.1) (hS : HasHeckePolyAt f.1 w hw S) :
  i < O.rankDiff → S.IsRoot (O.a.frobValue r w * w.q ^ i) := by
  obtain ⟨⟨s, b⟩, y, _, e, a⟩ := w.isPlaceOver_placeOver.exists_isFrob (AbsGal D),
    hasHeckePolyAt_iff_localFormRep.1 hS
  exact isRoot_string_of_norm isUnitary_localFormRep y h₀ e a (.of_map (by
    simpa [↓chiOneInv_spec w.isPlaceOver_placeOver hℓ 1, b] using
      isRoot_of_isRoot_charpoly (P := comp _ ((chiOneInv O s⁻¹).1⁻¹ • .X)) (by
    simpa [aeval_comp, Units.smul_def] using (((sphericalCompat_std w f.2 (x.isEigenform hf h₀)).2
    (x.attached_galRep hf h₀) hS.1 _ w.isPlaceOver_placeOver).2.2 _ _ hS s⁻¹ b).1
      (w.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2 hℓ)) (h s⁻¹))
    ιℓ.toRingHom.injective) (by simp [AutChar.frobValue, sq, ← mul_pow, ← pow_add, O.rank_lt.le])

/-- Let the normalised representation u of an eigenform have integral characteristic polynomials,
all with root 1. At generic geometric Frobenii σ (`mostFrobenii`): if char
u(σ) ≡ S·∏_{i<n−r}(X − cyc(σ)^{−i}) with ‖S(1)‖ ≥ 1, the rescaled Hecke polynomial is
∏_{i<n−r}(X − q^i)·T, and ιT divides an integral e with e(1) = 1. -/
lemma eventually_heckePoly_eq_string_mul (z : ∀ g i, ‖(normalisedRep O x.galRep g).1.charpoly.coeff
  i‖ ≤ 1) : ∀ᶠ y in mostFrobenii _, ∀ S, 1 ≤ ‖eval 1 S‖ → (∀ i, ‖(normalisedRep O x.galRep
  y.frob).1.charpoly.coeff i - coeff (S * ∏ i ∈ .range O.rankDiff, (X
  - C (cycInv ℓ _ _ y.frob ^ i))) i‖ < 1) → ∃ e, HasRootString (x.heckePolyAt y.w) (.map (algebraMap
  EllAdicIntegers _) e) y.w.q (ιℓ.symm (chiOneInv O y.frob).1)⁻¹ O.rankDiff ∧ e.eval 1 = 1 := by
  filter_upwards [(x.attached_galRep hf h₀).2.2.2 _ one_half_pos, eventually_mostFrobenii
    ((x.isEigenform hf h₀).2.and (eventually_notMem_star_notMem ℓ ∅))] with w a ⟨k, _, _, l⟩ _ b e
  refine (Finset.prod_dvd_of_coprime ((pairwise_coprime_X_sub_C (pow_right_strictMono₀ (by
    simp)).injective).set_pairwise _)
    (by simpa [chiOneInv_spec w.isPlaceOver l 1, w.isFrob, ↓dvd_iff_isRoot] using (fun
    _ ↦ isRoot_hecke_string hf h₀ h l (k w.prime_q).2))).elim fun T y ↦
    (exists_integral_multiple_eval_one (A := chiOneInv O w.frob ^ card n • 1 * T.map ιℓ)
    (monic_prod_X_sub_C ..) (z _) (fun i ↦ ?_) e b).imp fun _ : (intQpBar ℓ)[X] ↦ .imp_left (⟨T,
    y, by simpa [Polynomial.map_map] using! map_dvd (mapEquiv ιℓ.symm) <| dvd_of_mul_left_dvd ·⟩)
  generalize x.heckePolyAt _ = H at *
  by_cases! i ≤ card n <;> simpa [‹_›, cycInv_eq_of_isFrob w l, pow_sub₀, Units.smul_def, ← mul_sub,
    ← by simpa [Polynomial.map_prod, mul_comm _ T] using congr(mapEquiv ιℓ $y), norm_sub_rev,
    charpoly_smul_coeff, coeff_eq_zero_of_natDegree_lt, mul_assoc, mul_comm (ιℓ _),
    norm_eq_one_of_continuous, AlgHeckeChar.continuous_avatar] using
    (a _ rfl i).trans_lt one_half_lt_one
