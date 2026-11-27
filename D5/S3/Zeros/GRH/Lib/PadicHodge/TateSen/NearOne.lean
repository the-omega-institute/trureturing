/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/TateSen/NearOne
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/TateSen/NearOne
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.TateSen.NearOne. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/TateSen/NearOne.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.CyclotomicRamification
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.Defs
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Ax–Sen–Tate theorem and Tate's vanishing of the invariants of C_p(i). Ax's theorem
is given for any subgroup, without the constant, and Tate's for H⁰ only, on any open subgroup, from
the boundedness of the normalised trace to Q_p. As a consequence, invariants of B_dR modulo a
submodule come from the base field. Source: J. Ax, Zeros of polynomials over local fields: the
Galois action, J. Algebra 15 (1970); J. Tate, p-divisible groups (1967), §3; see also
Fontaine–Ouyang 3.3-3.5 and Brinon–Conrad §14.

Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius (known
result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Tate: normalised trace bounded on cyclotomic tower; H^0 of C_p(i) vanishes. Filter near
1, fixed field, embeddings of Q̄_p into C_p are Galois elements. -/

section

open Algebra Finset Polynomial IntermediateField Submodule Units NeZero Set
  IsUltrametricDist InfiniteGalois AdjoinSimple NonarchimedeanGroup PadicComplex Subgroup

/-- Tate: there is a constant C, depending only on p, such that every z in Q̄_p fixed by the
kernel of the cyclotomic character, that is z in Q_p(μ_{p^∞}), has normalised trace to Q_p
of absolute value at most C·|z|. -/
lemma exists_norm_normalizedTrace_le p [ThePrime p] : ∃ C, ∀ z ∈ fixedField cyclotomicGp.ker,
    ‖normalizedTrace ℚ_[p] _ z‖ ≤ C * ‖z‖ := let T := normalizedTrace ℚ_[p] (PadicAlgCl p)
  ((nthRoots p 1).map T).finite_toSet.isBounded.exists_pos_norm_le.imp' (· * p) fun C ⟨c,
    d⟩ z _ ↦ by
  choose n ζ h k using by simpa using
    (exists_cyclotomicGp_eq_of_isClosed 1 (isClosed_setOf_smul z (· ≠ z))).mt (by aesop)
  have H η (h : η ^ p ^ n.succ = 1) : ‖T η‖ ≤
    C := by if e : η ^ p = 1 then simp_all [pos] else simp [c.le, by
    simpa [← pow_mul, mul_sum, fun a ha ↦ ((exists_inertia_cyclotomicGp_eq a ha).rec fun g k ↦
    by erw [← cycCharMod_eq_iff (g := g).1 (by simp [cycCharMod_prime_pow_eq, k]) η h,
      normalizedTrace_map _ _ g.toAlgHom]
    : T (η ^ a) = T η), ← pow_succ', ne, h] using congr(T (η * $(geom_sum_eq e (p ^ n))))]
  obtain ⟨e, l, a, rfl⟩ := norm_zeta_sub_one_pow h ▸ norm_p_eq_inv,
    lt_imp_lt_of_le_imp_le (one_le_pow₀ ·) (norm_zeta_sub_one_pow h ▸
    norm_p_lt_one), by simpa [natDegree_cyclotomic, -coe_range,
    mem_span_image_finset_iff_exists_fun', ↓← taylor_apply] using ((span_range_natDegree_eq_adjoin
    ((cyclotomic.monic ..).comp_X_add_C 1) (by simpa [↓aeval_comp, ← eval_map_algebraMap] using
    (isRoot_cyclotomic_iff.2 h))).ge ((adjoin_toSubalgebra {ζ - 1}).le ((fixedField_fixingSubgroup
    _).le ((k _).mtr <| by simpa using ·.2 (gen ..)))))
  grw [← sum_filter_ne_zero, map_sum, norm_sum_le_of_forall_le_of_nonneg]; bound
  intros; grw [norm_sum_eq_sup'_of_pairwise_ne ⟨_, ‹_›⟩, ← le_sup' _ ‹_›]
  simp [norm_smul]; grw [← pow_le_pow_of_le_one, e, sub_eq_add_neg, Commute.add_pow', map_sum,
    norm_sum_le_of_forall_le_of_nonneg c.le] <;> simp_all [T, field, le_of_lt, neg_one_pow_eq_ite,
    -nsmul_eq_mul, ← pow_mul, h.pow_eq_one_iff_dvd, apply_ite, (norm_nsmul_le _ _).trans]
  simp_all [Set.Pairwise, norm_smul, ← inv_eq_iff_eq_inv.2 e, ← zpow_natCast, ← zpow_mul,
    Padic.norm_eq_zpow_neg_valuation, ← zpow_add₀, l.ne, Int.emod_eq_of_lt,
    h.sub_one_ne_zero (by simp [Fact.out]), ne_of_apply_ne (· % ((p ^ n.succ).totient : ℤ))]

/-- Tate's theorem: if x ∈ C_p, u ≠ v are integers and χ(g)^u·g(x) = χ(g)^v·x for all g near 1
in G_p, χ the cyclotomic character, then x = 0.

Known result: Ax–Sen–Tate theorem and Tate's vanishing of the invariants of C_p(i). -/
lemma tate_eq_zero_of_chi_twist {p} [ThePrime p] {x : ℂ_[p]} {u v : ℤ} (hu : u ≠ v) (h : ∀ᶠ g in
  nhds 1, (cyclotomicGp g ^ u).1 • g • x = (cyclotomicGp g ^ v).1 • x) : x = 0 := (is_nonarchimedean
  _ h).rec fun U _ ↦ mem_span.1 (mem_span_fixed (.id _) (smulMonoidHom.comp ((cyclotomicGp ^ (-u +
  v))⁻¹.prod (actionRep ℤ_[p] _ (.id _)))) (by simp [smul_def', ← coe_eq, mul_smul_comm]) (by simpa
  [inv_smul_eq_iff, zpow_add, mul_smul]) (fixingSubgroup_fixedFieldOf _).le) ⊥ fun y h ↦ by
  simp_all [inv_smul_eq_iff]; choose C H using exists_norm_normalizedTrace_le p
  have A x hx (f : C(_, ℂ_[p])) h : 1 ≤ C * ‖f x‖ := (mapsTo_image_iff.2 h).closure_left
    (f.2.norm.const_mul _) isClosed_Ici (ax_exists_near_fixed cyclotomicGp.ker hx)
  apply Function.mtr (by aesop) (A y⁻¹ (by aesop) (1 - y • .id _) fun w hw ↦ ?_)
  let ⟨γ, k, c⟩ : ∃ γ, γ w = w ∧ (cyclotomicGp γ ^ (-u + v)).1.1 ≠ 1 :=
    (exists_inertia_cyclotomicGp_eq p.succ (by
   simp)).rec fun γ c ↦ (exists_pow_mem_of_index_ne_zero (quotient_finite_of_isOpen _
    (isLocalGalois_padic.1.6 w)).card_pos.ne' γ).rec fun N k ↦ ⟨_, k.2.2, (val_eq_one.2
    ∘ pow_natAbs_eq_one.2 ∘ ext ∘ PadicInt.ext).mt (by simp [c]; norm_cast; simp [ne]; lia)⟩
  convert A ((mk0 _ (sub_ne_zero.2 c))⁻¹ • y * w) ?_ (1 - (γ • .id _ - .id _)) fun z hz ↦ ?_ <;>
    simp +contextual [*, by simpa using hw, smul_comm _ _⁻¹, Units.smul_def]
  congr! 3; match_scalars <;> simp [field]
  norm_cast; simpa [map_sub, normalizedTrace_minpoly, ← C_1, -map_one] using
    H _ (sub_mem (one_mem _) (sub_mem (smul_mem_fixedPoints_of_normal γ hz) hz))

end

open UniformSpace.Completion Submodule Units Module Filter Topology nonZeroDivisors AlgHom

/-- Elimination in a free module. Suppose that for each nonzero v in W proportional to all y in W
supported within its support, some u in W∩W' supported there has a coordinate equal to 1. Then
W ⊂ W'. -/
lemma le_of_echelon {A V ι} [CommRing A] [AddCommGroup V] [Module A V] (b :
    V ≃ₗ[A] ι →₀ A) {W W' : Submodule A _} (hP : ∀ v ∈ W, v ≠ 0 → (∀ y ∈ W, (∀ i, b v i = 0 →
    b y i = 0) → ∀ k, b v k • y = b y k • v) → ∃ u ∈ W ⊓ W', (∃ k, b u k = 1) ∧ ∀ i, b v i = 0 →
    b u i = 0) : W ≤ W' := ((InvImage.wf (b · |>.1) wellFounded_lt).fix (C := (· ∈ _ → _ ∧ _))
  (fun w ih hw ↦ by refine have h := (by_cases id fun _ ↦ hP w hw · fun y _ _ k ↦ ?_); ⟨by_cases
  (by bound) (h · |>.rec fun y ⟨_, ⟨k, _⟩, _⟩ ↦ ?_), h⟩ <;> (
  have := by simpa [mul_comm, LT.lt, LE.le, InvImage] using ih (b y k • w - b w k • y)
  grind [sub_mem_iff_left, smul_mem, one_smul, mem_inf, smul_eq_zero_of_left])) · · |>.1)

/-- F a filter of neighbourhoods of 1 in G_p, ι finite; each a ∈ W ⊂ C_p^ι has (χ(g)^u_i·g a_i)
∈ W for F-almost all g. Then W ⊂ W' once W' contains each integral a ∈ W over Q̄_p, F-almost
fixed, with some a_k = 1, a_i = 0 if u_i ≠ u_k. -/
lemma le_of_hodgeTate_stable {p} [ThePrime p] {ι} [_root_.Finite ι] {F} (hF : nhds 1 ≤ F) (u :
  ι → ℤ) (W W' : Submodule ℂ_[p] (ι → ℂ_[p])) (hW : ∀ a ∈ W, ∀ᶠ g in F, (fun i ↦
  (cyclotomicGp g ^ u i).1 • g • a i) ∈ W)
  (H : ∀ a k, (↑) ∘ a ∈ W → (∀ i, ‖a i‖ ≤ 1) → (∀ i, u i = u k ∨ a i = 0) → a k = 1 → (∀ i, ∀ᶠ g in
  F, g (a i) = a i) → (↑) ∘ a ∈ W') : W ≤ W' := le_of_echelon (Pi.basisFun ..).1 fun v hv n h ↦ by
  obtain ⟨k, z, _⟩ := by simpa [n] using v.support.toFinite.exists_maximalFor (‖v ·‖)
  have M := W.smul_mem (v k)⁻¹ hv
  have e i := by simpa [*, -smul_mul'] using (hW _ M).mono fun _ ↦
    (congr((v k)⁻¹ * $(h _ · (by simp +contextual) k) i))
  have h₂ i := (tate_eq_zero_of_chi_twist · (hF (e i)))
  have f i := (e i).mono fun g h ↦ by_cases (isSMulRegular _ _ <| · ▸ h) (h₂ i · ▸ smul_zero g)
  choose a ha using (exists_algebraic_of_fixed_near_one <| hF <| f ·)
  simp [*, Pi.smul_def] at M h₂ f
  refine ⟨_, ⟨M, H a k M ?_ ?_ (coe_inj.1 ?_) f⟩, ?_⟩ <;>
    simp [← norm_coe (a _), ← ha, field, coe_one] <;> grind [norm_zero]

variable {p} [ThePrime p] {Γ} [Group Γ] [𝒥 : OverGp Γ p]

instance flat_padicInt_of_algebra_padic {B} [CommRing B] [Algebra ℤ_[p] B] [Algebra ℚ_[p] B]
    [IsScalarTower ℤ_[p] ℚ_[p] B] : Flat ℤ_[p] B := .trans _ ℚ_[p] _

lemma nearOne_eq_nhds_one [TopologicalSpace Γ] (hj : IsOpenEmbedding 𝒥.toGp) : nearOne Γ = 𝓝 1 := by
  simp [nearOne, hj.nhds_eq_comap]

variable (Γ) in
/-- The local field cut out by `toGp`. -/ noncomputable abbrev localFieldOf := fixedFieldOf 𝒥.toGp.range

lemma mem_localFieldOf {x} : x ∈ localFieldOf Γ ↔ ∀ g, 𝒥.toGp g x = x := by simp

lemma exists_gp_eq_algHom (γ : _ →ₐ[ℤ_[p]] ℂ_[p]) : ∃ s : Gp p, ∀ x, γ x = s x := ⟨restrictNormal'
  (γ.extendScalarsOfIsLocalization _ _⁰) _, by simp [restrictNormal', PadicComplex.coe_eq]⟩

variable (Γ) in lemma nhds_one_le_map_nearOne : 𝓝 1 ≤ Filter.map toGp (nearOne Γ) :=
  (map_comap_of_mem (𝒥.2.1.mem_nhds (one_mem _))).ge
