/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLevel
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeLevel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.BaseChange.BaseChangeLevel. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/BaseChange/BaseChangeLevel.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.BaseChangeWeight
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Tame levels; matching of unit functions at principal congruence level, keeping unramified
places maximal. -/

open NumberField Matrix Set Valued Module Ideal Subtype


variable {E E' n : Type} [Field E] [CMType E] [Field E'] [NumberField E'] [CMType E'] [Algebra E E']
  [Fintype n] {σ : Gal(E'/E)} (hσ : σ ≠ 1) {μ} [hμ : IsStep (E := E) E' μ] {f : E →+* E}
attribute [local simp] ite_mem adeleMap_idem_placesAbove adeleMap_gal_pow
  Algebra.algebraMap_ofSubring idem_mul_self

variable (E' μ) in
/-- At every place u of E' above w, some element of Gal(E'/E) lies outside the inertia group of
u, and μ∘Nm is trivial on the local units at u. -/
def IsStepUnramifiedAt w := ∀ u : FinPlace E', u.below E = w → (∃ σ, σ ∉ u.1.inertia Gal(E'/E)) ∧
  ∀ x, v x.1 = 1 → μ (locIdele _ (localNorm E u x)) = 1

/-- The ring homomorphism between the integral finite adeles of E and of E' induced by an
embedding f: E → E'. -/
noncomputable def intAdeleMap (f : E →+* E') := (adeleMap f).restrict _ _ fun _ ↦
  (adeleMap_mem_Ohat f).2

@[simp] lemma intAdeleMap_iterate i : ∀ x, (intAdeleMap f)^[i] x =
  (adeleMap f ^ i) x := by induction i <;> tauto

omit [CMType E] [NumberField E'] [CMType E'] in
lemma notMem_inertia_of_comap_ne {u : FinPlace E'} (h : u.comap σ ≠ u) : σ ∉ u.1.inertia _ :=
  fun a ↦ h (by ext x; simpa using! u.1.add_mem_iff_right (b := x) (a x))

include hσ hμ

lemma exists_isTameAtLevel_intAdeleMap : ∃ C ≠ 0, ∀ m : Ô E', intAdeleMap σ m = m →
  (∀ u, C.cast ∈ u.1 → (∀ g, g ∈ u.1.inertia Gal(E'/E)) → reduceAt u m = 0) →
  IsTameAtLevel (intAdeleMap σ) (finrank E E') m := by
  obtain ⟨⟨e, _⟩, b, x, _⟩ := hμ.exists_trace_eq_one, bijective_pow_gal hσ,
    not_forall.1 (hσ ∘ IsGaloisGroup.faithful (𝓞 E) (B := 𝓞 E').1)
  refine ⟨(span {σ • x - x}).absNorm, by simpa, fun m a h ↦ ⟨a, ⟨algebraMap _ _ e, 0, val_injective
    (by simp [b.sum_comp (· e), *, Finset.sum_range, ← map_sum, ← trace_eq_sum_automorphisms,
    -AlgEquiv.coe_pow])⟩, by ext; simp [↓adeleMap_pow_finrank_eq_one], finrank_pos,
    fun i l P _ hP ↦ ?_⟩⟩
  have H : ∀ g, g ∈ (P.under (𝓞 E')).inertia _ := (bijective_pow_gal ((@b.1 ⟨i, l.2⟩ 0).mt (by
    grind))).2.forall.2 (pow_mem (fun _ ↦ by simp; convert hP _; simp [← coe_inj, algebraMap.smul'])
      ·)
  exact map_le_of_le_comap (fun _ ↦ algebraMap_ResField_eq_zero.1) ((map_under_Ô (by simpa) (I :=
    RingHom.ker (reduceAt ⟨_, inferInstance, by simpa ∘ (·.le (H ..))⟩))
    (algebraMap_ResField_eq_zero.2
    (H ..))).ge (h _ ((span_singleton_le_iff_mem _).2 (H ..) (absNorm_mem _)) H))

/-- For a step, σ ≠ 1 and H open: there are levels K_u ≤ GL_n(O_u) over E', maximal above
`IsStepUnramifiedAt` places w with K_w ≤ H, pulling back into H; each level L above S is open,
σ-stable, satisfies `CocyclesSplit`, and its indicators form a `IsMatchingPairAbove`. -/
lemma exists_baseChange_level {H} (hH : H.IsOpen) : ∃ K, (∀ u, K u ≤ Kw n u) ∧
  (∀ S L, L = localLevel n (placesAbove _ S) K → L.IsOpen ∧ (∀ k, galoisGf σ k ∈ L ↔ k ∈ L) ∧
  CocyclesSplit (finrank E E') (idem (placesAbove _ S)) L (galoisGf σ) ∧ IsMatchingPairAbove σ μ S L
  (indicator L 1 ∘ baseChangeGf (E' := E')) (indicator L 1)) ∧ (localLevel n univ
  K).comap baseChangeGf ≤ H ∧ ∀ w, IsStepUnramifiedAt E' μ w → maxCompactAt n w ≤ H →
  ∀ u ∈ placesAbove _ {w}, K u = Kw n u := by
  obtain ⟨⟨C, C₀, t⟩, S₀, hS, hS'⟩ := exists_isTameAtLevel_intAdeleMap hσ,
    exists_inf_trivialOn_le hH
  let A := placesAbove E' {w | IsStepUnramifiedAt E' μ w ∧ w ∉ conjClosure S₀}
  have un {u} (h : u ∈ A) := h.elim (·.1 u rfl) (·.1 _ (below_star u) |>.imp (by
    simpa using fun σ x b ↦ ⟨σ, _, by convert b; ext; apply map_star_CM σ.toRingHom⟩) fun b y _ ↦ by
    simpa [↓star_mul, ↓← units_map_adeleNorm_star, adeleNorm_locIdele, star_locIdele, *] using
      (hμ.apply_norm_eq_one_iff _).2 ⟨1, locIdele u y, rfl⟩)
  let F x := x + idem A * (1 - x)
  obtain ⟨N, N₀, U⟩ := mem_nhds_zero_finAdele_iff.1 (((isCompact_Ô.prod
    (isCompact_idelesUnitOff_empty.diff hμ.isClopen_normKer.2)).eventually_forall_mem (fun x p ↦
    p.2.1 - F x * p.1) {1}ᶜ fun z ⟨_, a, b⟩ ↦ isOpen_ne.mem_nhds fun e ↦
    b (mem_of_locIdele_mem hμ.isClopen_normKer.1 fun u ↦ congr(μ $(adeleNorm_locIdele
    ..)).trans (by_cases (un · |>.2 _ (mem_idelesUnitOff.1 a u id)) fun c ↦ by simp [(Units.ext (by
    simpa [F, c, ideleAt] using congr($e u)) : ideleAt u _ = 1)]))).and ((isCompact_Ô.matrix.prod
    (isCompact_Kf.diff hH)).eventually_forall_mem (fun x p ↦
    p.2.1.1.map (finAdeleIncl _ E') - F x • p.1) {1}ᶜ fun z ⟨_, a, b⟩ ↦ isOpen_ne.mem_nhds fun e ↦
    b (hS' ⟨a, Gf.mem_trivialOn.2 ((FinPlace.comap_surjective
    _).forall.2 fun u c ↦ Units.ext (ext fun i j ↦ RingHom.injective _ (congr($(eq_add_of_sub_eq e)
    i j u).trans (by simp +contextual [F, A, apply_ite, placesAbove, mod_cast c]))))⟩)))
  specialize U C (by simp); let m : Ô _ := N * C + ⟨_, idem_mem_Ô A⟩ * (1 - N * C)
  let k := F ((N * C)⁻¹ : E')
  have hk : m * k = 1 := by dsimp [m]; grind [idem_mul_self, map_natCast,
    congr(($(@mul_inv_cancel₀ E' _ (N * C) (by positivity)) : 𝔸f E'))]
  have hK {u g} : g ∈ congruenceGL ((v.leSubmodule 1).comap (.mulLeft _ (k u))) id ↔ g ∈ Kw n u ∧
    ∀ i j, _ * _ ∈ LocInt u := .rfl
  refine ⟨_, fun _ _ ↦ (hK.1 · |>.1), fun S L hL ↦ ?_, fun g h ↦ by
    simp [localLevel, atPlace_sub_one_apply, forall_and, *, -Matrix.sub_apply, ← mem_Kf_iff,
      baseChangeGf_mem_Kf] at h
    exact by_contra (U.2 (k • _, g) ⟨fun _ _ ↦ mem_Ô.2 (h.2 · ..), h.1, ·⟩
      (by erw [smul_smul, hk, one_smul, sub_sub_self]; rfl)), fun w b c u hu ↦ by
    ext; simp +contextual [↓hK, k, F, mem_intGL, sub_mem, show u ∈ A by grind [placesAbove]]⟩
  have hL' g : g ∈ L ↔ ∀ a b, idem (placesAbove _ S) * k * (g.1.1 - 1) a b ∈ Ô _ := by
    simp only [*, mem_localLevel, mul_assoc, idem_mul_mem_Ô, finAdele_mul_apply,
      ← atPlace_sub_one_apply, forall_and, mem_intGL]; rw [and_iff_right_of_imp fun H ↦ ?_]; tauto
    have a := (mul_mem (mem_Ô.1 m.2 _) <| H · · · ·)
    simp [← mul_assoc, ← finAdele_mul_apply, hk, sub_eq_add_neg, add_mem_cancel_right] at a
    exact ⟨a, fun w h i j ↦ (v_locMap_le_one ..).1 (g.atPlace_star rfl ▸ a _ (by simpa) ..)⟩
  refine have a g := ?_; ⟨(ext hL').symm.subst isOpen_Ô.matrix.preimage_of_continuous, a,
      isMatchingPair_congruence_level ⟨_, idem_mem_Ô _⟩ isProfiniteRing_intAdeles (t 0 ?_ ?_) ?_
      (((map_sub ..).trans (congrArg _ ?_)).subst (exists_isUnit_sub_star_Ohat.choose_spec.map
      (intAdeleMap (algebraMap E _)))) ?_ (t (_ * m) ?_ fun u c b ↦ by
    simp [m, by simpa using algebraMap_ResField_eq_zero.2 c, un.mt, b]) ?_
    ⟨(star_mul' ·.1)⟩ (Subring.isIntegrallyClosedIn_iff.2 fun _ h ↦ mem_Ô.2 fun u ↦
    ((Valuation.integer.integers (v.comap (evalAt u))).mem_of_integral (h.map_of_comp_eq
    (Subring.inclusion (iInf_le ..)) 1 rfl) :)) _ rfl ?_ ?_ ((mul_mul_mul_comm ..).trans (by
    simp [*])) ?_ (hL' · |>.trans ⟨fun h ↦ ⟨(⟨_, h · ·⟩), rfl⟩, (congrFun₂ ·.choose_spec · ·
    |>.subst (prop _))⟩) fun y z _ ↦ by_contra (U.1 (_, _) ⟨y.2, by simp [coe_idelesUnitOff_empty,
      mul_mem, add_mem, Submonoid.mem_units_iff], ·⟩ (add_sub_cancel_right ..))⟩
  simp +zetaDelta [hL', ↓← adeleMap_mem_Ohat σ.toRingHom (x := _ * (g.1.1 - 1) _ _)]; rfl
  all_goals simp +zetaDelta [a, intAdeleMap, ← coe_inj, star_idem, preimage,
    adeleMap_star, mem_range_finAdeleIncl_iff.1, ← mul_assoc]
