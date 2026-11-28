/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeWeight
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/BaseChange/BaseChangeWeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.BaseChange.BaseChangeWeight. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/BaseChange/BaseChangeWeight.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.TwistedTraceSum
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Cyclic base change of prime degree for definite unitary groups (weak lift, local
matching) (known result; see Lib.GaloisRep.BaseChange.BaseChangeEigenchar).

This file: Matching of spherical Hecke functions at places splitting completely in the extension.
Twisted character of base-changed weight equals character at the norm. -/

open Set Matrix RingHom Polynomial Gf Module
variable {E E' n W} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n] {σ :
  Gal(E'/E)} [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (Gf E' n) W} {u : FinPlace E'}

attribute [local simp] map_aeval_matrix map_smul' adeleMap_apply star_idem Matrix.map_add
  atPlace_baseChangeGf twistedNorm_map_eq_prod adeleMap_gal_pow indicator_subgroup_mul_left
  idem_apply Polynomial.map_prod cutGL Set.ext_iff below_star atPlace_atSplit_of_ne
  placesAbove mul_mem_cancel_left mul_mem_cancel_right leftTranslation funext_iff

attribute [-simp] evalAt_apply in
omit [CMType E'] in
/-- Let μ be trivial at T, T contain no place with its conjugate, B be the places above T and their
conjugates. If z = 1 off T and P ∣ Nm z − X above T, z is a root on B, and z(γ)/z(γ)* is z(γ) above
T. -/
lemma IsStep.isNormRoot_of_one_side {μ} (hμ : IsStep E' μ) {B T} (e : B = placesAbove E' T) (hD :
  ∀ w ∈ T, ∀ x, μ (locIdele w x) = 1) (s : ∀ w ∈ T, star w ∉ T) {p P z} [NeZero p] (hz : ∀ u,
  .below E u ∉ T → z.map (evalAt u) = 1) (N : ∀ u, .below E u ∈ T →
  P.map (evalAt u) ∣ (twistedNorm (.map (adeleMap σ)) p z).map (evalAt u) - X) :
  IsNormRoot n (adeleMap σ) p (idem B) (normKer _ μ) P z ∧ ∀ γ a : Gf E' n, IsRootQuotient γ
  (idem B • z) a → ∀ u, .below E u ∈ T → a.atPlace u = aeval (γ.atPlace u).1 (z.map (evalAt u)) :=
  have I (u : FinPlace E') S := (evalAt_apply ..).trans (idem_apply S u)
  ⟨⟨by ext : 2; simp_all [← evalAt_apply, ← coeff_map]; grind, by
  rintro g rfl
  have N : (twistedNorm (.map (adeleMap σ)) p z).aeval g.1.1 = cutGL (idem_mul_self (.below E ⁻¹'
    T)) g.1 := matrix_ext_evalAt fun u ↦ if a : _ then (N u a).elim (by simp_all [sub_eq_iff_eq_add,
    aeval_self_charpoly, ← charpoly_map]) else by simp [*, (map_map (adeleMap _) (evalAt u) z).trans
    (map_map (evalAt _) (locMap _ rfl) _).symm]
  choose _ _ h using (twistedNorm_map_eq_prod p z ▸ isUnit_aeval_iff_isCoprime.1 ⟨_,
    N.symm⟩).of_prod_right 0 (by grind [NeZero])
  use fun k M _ ↦ (isUnit_det_of_left_inverse (by simpa [*, one_def] using congr(aeval M $h))).imp
    fun d c ↦ ⟨mem_of_locIdele_mem hμ.isClopen_normKer.1 fun u ↦ if a :
    u.below E ∈ T then by simp [adeleNorm_locIdele,
    *] else by simp [show ideleAt u d = 1 by ext; simp_all [ideleAt, map_det]], c⟩,
    matrix_ext_evalAt fun u ↦ by simp_all [← U.inv_val_eq_conjTranspose, Matrix.map_sub]; aesop⟩,
    fun _ _ a u _ ↦ by simpa [*, fun M ↦ (id rfl : Mᴴ.map (evalAt u) =
    (M.map (evalAt _))ᵀ.map (conjLoc (star_star u)))] using! congr(map $a (evalAt u))⟩

lemma heckeSplit_comp_baseChangeGf hu hw (s : (⇑(locMap _ (.refl (u.below E)))).Surjective) {j x}
  (hx : x ∈ sphericalAt π u) (h : ∀ k ∈ supportedOn n (.below E ⁻¹' {u.below E} \ {u}), π k x = x) :
  heckeSplit (π.comp baseChangeGf) (w :=
  u.below E) hw j x = heckeSplit π (w := u) hu j x := heckeFun_comp _ (by simp)
  ((mem_sphericalAt_iff _).1 hx) (by simp) (GL_map_surjective _ s) (by apply locMap_mem_Kw) (fun _ ↦
  by erw [← π.inv_apply_eq_iff, ← End.mul_apply, ← map_mul, h _ (mem_supportedOn.2 fun v _ _ ↦ ?_)]
     by_cases star v = u <;> [rw [← atPlace_star_eq_one_iff]; by_cases v = u] <;> aesop)
  (by simp [basicDoubleCoset, indicator_apply, ← map_inv, -coe_units_inv, ← map_det,
  ← mapMatrix_apply, v_locMap_eq_of_isUnit_log _ rfl ((s (uniformizer u)).imp (by simp_all))])

attribute [local grind =] star_star below_star below_comap atPlace_star_mem_iff InjOn

/-- For a step E'/E, σ ≠ 1 and a set S of split matched places (`IsMatched`), some set of
matching pairs (`IsMatchingPairAbove`) contains the pair of level indicators and, for each w ∈ S, is
stable under all (T_{w,j}, T_{u,j}) for some place u above w. -/
lemma exists_hecke_stable_matching {μ} (hσ : σ ≠ 1) [hμ : IsStep E' μ] {S} (h : ∀ w ∈ S, w.IsSplit ∧
  IsMatched E' μ w) : let B := localLevel n (placesAbove _ S); ∃ St : Set _, (indicator B 1 ∘
    baseChangeGf (E' := E'), indicator B 1) ∈ St ∧ (∀ x ∈ St, IsMatchingPairAbove σ μ S B x.1 x.2) ∧
    ∀ w : S, ∃ u, .below E u = w.1 ∧ ∀ x ∈ St, ∀ hw hu j, (heckeSplit
  leftTranslation (w := w) hw j x.1, heckeSplit leftTranslation (w := u) hu j x.2) ∈ St := by
  intro B
  obtain ⟨V, hV, -, b, c⟩ := exists_subset_bijOn (.below E ⁻¹' S) fun u : FinPlace E' ↦
    s(u.below E, (star u).below E)
  let A := FinPlace.below E ⁻¹' .below E '' V \ V
  have s : placesAbove E' S =
    placesAbove _ (.below E '' V) := by simp [SurjOn] at c ⊢; grind [=_ below_star]
  have l {g} : g ∈ B ↔ g ∈ localLevel n V ∧
    g ∈ localLevel n A := by grind [mem_localLevel, placesAbove, =_ atPlace_star_mem_iff]
  use {(F ∘ baseChangeGf, indicator (localLevel n A) 1 * F) | (F) (_ : ∀ k ∈ localLevel n V,
    leftTranslation k F = F ∧ ∀ g, F (g * k)
    = F g)}, ⟨indicator (localLevel n V) 1, by simp +contextual [indicator], by
    ext <;> simp [indicator, l, ite_and, mem_localLevel,
      A]; congr! with H; erw [ite_eq_left fun _ _ a e _ ↦
    (locMap_mem_Kw (w := .below E _) _).2 (e ▸ (locMap_mem_Kw _).1 (H _ a))]⟩, ?_, fun ⟨w, m⟩ ↦ ?_
  rintro _ ⟨F, hF, rfl⟩; have ⟨β, η⟩ := bijective_pow_gal hσ
  have key {u : FinPlace E'} {g d : Gal(E'/E)} (a : u.comap g ∈ V) : u.comap d ∈ V ↔ d = g :=
    (mul_left_surjective g d).rec fun d e ↦ e ▸ ⟨(mul_eq_left.2 <| (((h _ (hV a)).2.2 _ rfl).2
    _).mtr <| b · a (by grind)), by grind⟩
  have t i {u} : ∀ ⦃k⦄, atPlace (.comap ↑(σ ^ i) u) k ∈ Kw n _ → ((galoisGf σ)^[i] k).atPlace u ∈
    Kw .. := i.rec (by tauto) fun _ a _ ↦ @a _ ∘ (locMap_mem_Kw _).2
  use fun k hk ↦ ?_, fun P _ _ ↦ ⟨1 + idem V • (X - 1),
    (hμ.isNormRoot_of_one_side s (forall_mem_image.2 fun _
    a ↦ (h _ (hV a)).2.1) (by grind) (by simp; tauto) fun u ⟨v, a, e⟩ ↦ ?_).imp_right fun H γ a _ d
    ↦ ?_⟩; simp_all [indicator, (@l (galoisGf σ k)).1 fun u a ↦ t 1 (hk _ (by simpa))]
  obtain ⟨i, rfl⟩ := η.exists.1 (FinPlace.exists_gal_comap_eq e.symm)
  simp [Finset.prod_range, add_ite, key a, β.eq_iff]
  have ⟨_, a₂⟩ : a ∈ localLevel n A ∧ γ⁻¹ * a ∈ localLevel n V :=
    .imp (trivialOn_le_localLevel ·) (trivialOn_le_localLevel ·) (by
    simp +contextual [↓mem_trivialOn, Units.ext_iff, H _ _ d, ↓mem_image_of_mem, A])
  rw [← Nat.succ_pred_prime hμ.out] at *
  simp +contextual [← (hF _ a₂).2 γ, *]
  rintro δ _ rfl h _; simpa [twistedNorm, mul_div_assoc] using div_mem (inv_mem a₂) (list_prod_mem
    (List.forall_mem_map.2 fun i m u a ↦ t _ (h _ ⟨⟨u, by simpa⟩, β.ne
    (Fin.succ_ne_zero ⟨i, List.mem_range.1 m⟩) ∘ (@key u 1 _ a).1⟩)))
  obtain ⟨u, rfl, e⟩ : ∃ u, .below E u = w ∧ u ∈ V.conjClosure := by
    simp at s; grind [w.comap_surjective (algebraMap E E')]
  use u, rfl; rintro _ ⟨F, hF, rfl⟩ hw hu j
  have o a : atSplit hu a ∈ localLevel n A :=
    trivialOn_le_localLevel (supportedOn_le_trivialOn (by grind) (atSplit_mem_supportedOn hu a))
  use heckeSplit leftTranslation hu j F, fun k hk ↦ ⟨(heckeSplit_comm_of_atPlace_mem hu j ?_ (by
    grind [mem_localLevel])).symm.trans (congrArg _ ?_), ?_⟩, Prod.ext (heckeSplit_comp_baseChangeGf
    hu hw (fun y ↦ ⟨_, congr(evalAt u $(finAdeleIncl_adeleNorm E _ (1 + singleAdele u
    (y - 1)))).trans (by erw [map_prod, Fintype.prod_eq_single 1, adeleMap_id] <;> simp +contextual
    [(h _ m).2.2])⟩) ?_ (fun k a ↦
    (hF _ (trivialOn_le_localLevel (supportedOn_le_trivialOn (by grind) a))).1) ▸ map_heckeSplit _ _
    (LinearMap.funLeft ℂ ℂ baseChangeGf) ?_) ?_ <;> simp +contextual [heckeSplit, *, by simpa using
    hF, heckeGL, heckeFun_sum, ← mul_assoc, mem_localLevel, mem_Kf_iff, Finset.mul_sum]

open NumberField ComplexEmbedding ComplexConjugate Finset Fin Equiv Function

attribute [local implicit_reducible] stdSpace

variable {E E' n : _} [Field E] [Field E'] [Algebra E E'] [IsGalois E E'] [Fintype n] {σ :
  Gal(E'/E)}

/-- Base change of a weight κ from E to E': its column numbers and determinant exponent at an
infinite place are those of κ at the place of E below. -/
noncomputable def Weight.baseChange (κ : Weight E) : Weight E' :=
  ((κ.1 <| ·.comap (algebraMap ..)), (κ.2 <| ·.comap (algebraMap ..)))

/-- For E'/E Galois of prime degree p, σ ≠ 1, compatible CM types and ρ the pulled-back weight
representation, some s has sρ(δ) = ρ(σδ)s, and tr(ρ(δ)s) is the character of weight κ at γ
whenever δσ(δ)⋯σ^{p−1}(δ) = γ. -/
lemma exists_twisted_weightRep_trace (hσ : σ ≠ 1) [hp : Fact (finrank E E').Prime] [CMType E] [c :
  CMOver E E'] (κ : Weight E) : let j := U.map (J := 1) (algebraMap E E') (map_star_CM _)
  let ω := U.mapEnd (map_star_CM σ)
  let ρ := (stdSpace _ n).weightRep κ.baseChange.1 κ.baseChange.2
  ∃ s, (∀ δ, s * ρ δ = ρ (ω δ) * s) ∧ ∀ δ γ, twistedNorm ω (finrank E E') δ = j γ →
    (s * ρ δ).trace ℂ _ =
  ((stdSpace ..).weightRep κ.1 κ.2 γ).trace ℂ _ := (Nat.exists_eq_add_one.2 hp.1.pos).elim (by
  intro k hE j ω ρ
  choose i hi using fun u ↦ (AlgEquiv.symm_bijective.comp (hE ▸ bijective_pow_gal hσ)).2.exists.1
    (exists_comp_symm_eq_of_comp_eq (lift _ ((Φ (u.comap (algebraMap E _))).comp conj)) ((Φ u).comp
    conj) (RingHom.ext (by simp [@starRingEnd_apply E, @starRingEnd_apply E', by
    simpa [RingHom.ext_iff] using c.2 (Φ u)])))
  let e := ofBijective _ ((Nat.bijective_iff_injective_and_card fun u ↦ (⟨i u, u.comap (algebraMap E
    _)⟩ : Σ _, _)).2 ⟨fun _ ↦ by grind [mk_Φ, cancel_right, surjective], by simp [mul_comm, *, (⟨by
    simp [InfinitePlace.IsUnramified]⟩ : IsUnramifiedAtInfinitePlaces E E').card_infinitePlace]⟩)
  let A : WeylIndex n κ.baseChange.1 ≃ (_ → WeylIndex ..) :=
    .trans (.symm (e.symm.piCongrLeft' _)) (piCurry _)
  let G l := (weylRep κ.1 κ.2).comp (.pi fun v ↦ GeneralLinearGroup.map (n := n)
    ((lift _ ((Φ v).comp conj)).comp (σ ^ l).toRingHom))
  use (submatrix 1 (A.trans ((finRotate _).piCongrLeft' _)) A).toLin'
  simp_rw [fun δ ↦ ((LinearMap.ext (stdSpace_weightRep_apply δ)).trans (congrArg _ (Matrix.ext
    (by simp [reindex_equiv A.symm, ← hi, G, weylRep, @schur_apply_eq_prod (InfinitePlace _),
    prod_smul, ← Fintype.prod_sigma', reindex_equiv e]; tauto))) : ρ δ = (of fun a b ↦ ∏ l, G l.1 δ
    (A a l) (A b l)).toLin'), End.mul_eq_comp, ← toLin'_mul, mul_submatrix_one, one_submatrix_mul]
  use fun δ ↦ congrArg _ (Matrix.ext fun i _ ↦ .trans (.symm (Equiv.prod_comp (finRotate _) _)) (by
    simp [G, val_add, ← hE, ← IsGalois.card_aut_eq_finrank]; rfl)), fun δ γ h ↦ .symm ?_
  simp [trace, reindex_equiv A.symm, prod_univ_succ, ← cycleRange_last]
  trans (G 0 (j γ)).trace
  simp [LinearMap.ext (g := toLin' _) (stdSpace_weightRep_apply γ), G, j, U.map, weylRep,
    Units.smul_def, comp_def]
  simp [*, twistedNorm, ← h]
  refine k.rec ?_ ?_ δ (G 0 δ) <;> intros <;> simp [reindex_equiv (consEquiv _), ← mul_assoc,
    mul_apply, sum_mul, Fintype.sum_prod_type_right, prod_univ_succ, *, univ_eq_empty] <;> rfl)
