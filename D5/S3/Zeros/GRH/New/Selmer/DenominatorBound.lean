/- GID: D5/S3/Zeros/GRH/New/Selmer/DenominatorBound
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/DenominatorBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.DenominatorBound. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/DenominatorBound.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Selmer.TrianglePrimes
import D5.S3.Zeros.GRH.New.Patching.OnePrimeTie
import D5.S3.Zeros.GRH.New.Selmer.HeckeString
import D5.S3.Zeros.GRH.New.Selmer.RibetElement
import D5.S3.Zeros.GRH.New.Selmer.BaseLevelOfLabel
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Denominator of projection to lifts, without the even part. For a twist with short Selmer groups,
the ℓ-adic denominator of the projection to theta lifts, read by pairing integral forms with ones
orthogonal to non-lifts resembling lifts, is bounded by local losses, class number, level and odd
classes, while the even classes, where Vandiver's conjecture lives, cost nothing. Ribet-type bounds,
Taylor–Wiles primes in the residually reducible case and the mass formula case are known. Related
work: Dasgupta–Kakde–Silliman–Wang, The residually indistinguishable case of Ribet's method for GL2,
2023; Dotto–Thorne, Modularity of residually reducible representations of rank 2, 2026;
Martin–Wakatsuki, Mass formulas and Eisenstein congruences in higher rank, 2024.

This file: Denominator of projection to theta lifts bounded without the even classes. -/


open Polynomial Fintype Module Filter Isotypic Real LinearMap LevelPlaces.LevelForm Submodule IsApt
  NeZero PadicInt Units
attribute [-simp] map_eq_zero nsmul_eq_mul Pi.smul_apply

/-- There are h ≤ v_ℓ(`Data.chosenGroupOrder`), with h = 0 unless ℓ ≤ h₂², and γ in the Galois group
of E such that
cyc(γ)^a − 1 divides ℓ^h in ℤ_ℓ for all 0 < a < t. -/
lemma exists_cycChar_pow_sub_one_dvd {P} (D : Data P) ℓ [ThePrime ℓ] : ∃ h ≤ padicValNat ℓ
  D.chosenGroupOrder, (ℓ ≤ D.h₂ ^ 2 ∨ h = 0) ∧ ∃ γ : AbsGal D, ∀ a ∈ Set.Ioo 0 D.t, (cycChar Ω ℓ γ ^
  a).1 - 1 ∣ ℓ ^ h := if l : D.h₂ ^ 2 < ℓ then IsCyclic.exists_ofOrder_eq_natCard.elim fun b hb ↦
  (exists_inertia_cycChar_eq (valuation_comap_intQpBar_lt_one
  (IsAlgClosed.lift (R := ℚ)).1) (ZMod.val_coe_unit_coprime b).symm).elim fun γ i ↦ ⟨0, bot_le,
  .inr rfl, {γ with commutes' x := D.algebraMap_mem_cycloField x ⟨γ, cycCharMod_of_mem_inertiaGroup
  i.1 ((Nat.coprime_of_lt_prime out (D.nat_le_of_hasLogBound.trans_lt l) Fact.out).valuation_eq_one
  (valuation_comap_intQpBar_lt_one _))⟩}, fun a h ↦ (IsUnit.of_map toZMod _ (by
    erw [val_pow_eq_pow_val, i.2]
    simpa using pow_ne_one_of_lt_orderOf h.1.ne' (by grind [orderOf_units, Nat.card_units,
      Nat.card_zmod, Nat.le_self_pow]))).dvd⟩ else (exists_chosen_notMem_placesDividing D ℓ).elim
  fun v ⟨i, _, hw, hi⟩ ↦ ⟨_, le_rfl, by lia, (v.isPlaceOver_placeOver.exists_isFrob _).imp
  fun φ hφ a ha ↦ by simpa [hφ.cycChar_eq ℓ (v.isPlaceOver_placeOver.valuation_natCast_eq_one_iff.2
  hw.2), hi, pos, valuation] using (g_pow_sub_one_dvd_chosenGroupOrder D ⟨ha.1,
  ha.2.le.trans D.nat_le_of_hasLogBound⟩).natCast.trans (unitCoeff_spec (p := ℓ) out).dvd⟩

/-- Let Q be auxiliary, the avatar ψ of ϑ⁻¹ anticyclotomic, Σ_Q v(ψ(γ) − 1) ≤ cr for tame generators
γ, β = `rowBudget`. A cut spanned by lifts whose rows T have Sel_M(Tψ) of length ≤ (10fr + 1)cr,
M = ⌊D.r·β⌋ + 1, has denominator ≤ rβ log ℓ.

Denominator of projection to lifts, without the even part. -/
theorem denominatorLe_rowBudget {P} {D : Data P} {ℓ} [ThePrime ℓ] (ι : PadicIso ℓ) (ϑ :
  D.Twist) (hq : IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (crudeUnit ℓ D)) {r n} [Fintype r]
  [Fintype n] {O : AuxPair _ r n} {E Z} (hw : Z ≤ span ℂ {y ∈ Z | (∃ c, y ∈ (tupleProj O c).range ∧
  IsApt O c ϑ ∧ (tupleProj O c).range ≤ range (O.groupAlgAction E)) ∧ ∃ z, O.Lifts y z ∧ ∃ R, ∃ V :
  AuxPair _ r n, HasRow V z R ∧ O.μ = V.μ * ϑ.toAutChar ∧ ∃ γ s, SelmerLengthLe ϑ.invAvatar R ϑ.Q
  (⌊D.r * rowBudget D ℓ⌋₊ + 1) γ s}) : DenominatorLe ιℓ O E Z (rowBudget D ℓ * log ℓ) := by
  refine let A := _; have hZ : span ℂ A = Z := span_eq_of_le _ inf_le_left hw; fun _ e ↦ e ▸ fun
    Ξ Ξ' hl hΞ ↦ norm_gram_det_le_of_operators hZ toSmoothForm (innerₛₗ ℂ ∘ Ξ) (by simp)
        (D.chosenGroupOrder ^ 3) fun _ m₀ o ↦ ?_
  have T {S} (k : S ⊆ A) w h s X : span ℂ S ∈ (O.heckePolyOnForms h s X).invtSubmodule :=
    span_le.2 fun y m ↦ (O.heckePolyOnForms_eq_smul h s ((k m).2.2.choose_spec.1 w h s)
    X).symm.subst (smul_mem _ _ (subset_span m))
  have hT := hZ ▸ T le_rfl
  let N (x : Isotypic (stdSpace _ n) (O.κ, O.detExp)) := normalisedRep O x.galRep
  let 𝓧 (x : Isotypic ..) := ∃ v ∈ A, v.toSmoothForm ∈ x.1 ∧ v.toSmoothForm ≠ 0
  choose c m₁ hc le using m₀.2.1
  -- a lift has another label, or it has the label `c` and lies in an isotypic space
  have z {v} (m : v ∈ A) : tupleProj O c v = 0 ∨ v ∈ (tupleProj O c).range ∧ ∃ x : Isotypic ..,
    v.toSmoothForm ∈ x.1 ∧ _ := or_iff_not_imp_left.2 fun h ↦ ⟨m.2.1.elim fun b k ↦
    (by_contra (h <| tupleProj_eq_self_of_mem_range k.1 ▸ by simp [← End.mul_apply, ← map_mul,
    tupleIdem_orthogonal.ortho ·]) : c = b) ▸ k.1, by_contra fun H ↦ h <| mem_ker.1 <|
    le_of_isotypic_mem (T (by simpa)) (by simpa [mem_span_singleton] using fun x _ m a b ↦
    (H ⟨x, (smul_mem_iff _ a).1 m, b⟩).elim) (mem_span_singleton_self v)⟩
  choose x₀ m₂ using ((z m₀).resolve_left ((tupleProj_eq_self_of_mem_range m₁).trans_ne o)).2
  have h𝓧 : 𝓧 x₀ := ⟨_, m₀, m₂⟩
  have := card_pos_iff.1 O.rank_lt.pos
  choose! _ R hR hL γ₀ y₀ hS₀ using fun {x} (m : 𝓧 x) ↦ (m.elim fun _ k ↦ k.1.2.2.elim fun _ L ↦
    L.2.elim fun R V ↦ V.elim fun _ e ↦ e.1.1.imp fun _ r ↦ ⟨R, r, e.1.2 e.2.1 L.1 (k.2.elim
    isEigenform) (k.2.elim attached_galRep), e.2.2⟩ : ∃ τ R, IsRow D O.rankDiff τ R ∧ _ ∧ _)
  choose γ hγ y h₀ hy using (hR h𝓧).exists_scalar_inertia
  choose _ B sp j co using exists_baseLevel hc hq.1
  have cp (x : B.Eigensystem ![]) g i : ‖(N x g).1.charpoly.coeff
    i‖ ≤ 1 := by simp [(eventually_exists_isLatticeIn (r :=
    N x) (co _ _ (by simp) _ x.2).1.continuous).exists.choose_spec.choose_spec.charpoly_eq_map]
  choose h hh hℓ g₁ hC using exists_cycChar_pow_sub_one_dvd D ℓ
  -- a generic normaliser is regular on the finitely many `N x` that have a regular `N x g - 1`
  let s := {x : B.Eigensystem ![] | ∀ g, (N x g).1.charpoly.IsRoot 1}
  have W (j : ℕ) (t : Set ↥sᶜ) : ∃ θ, ∀ x ∈ t, ((ribetNormaliser (@γ₀ x₀) g₁⁻¹ (@y₀ x₀) (ℓ ^ j)
      θ).linearCombination (intQpBar ℓ) fun g ↦ (N x g).1 - 1).det ≠ 0 := t.toFinite.induction_on _
    (by simp) @fun a _ _ f ⟨θ, h⟩ ↦ (not_forall.1 a.2).elim fun g k ↦ ((f.insert _).eventually_all.2
    fun z m ↦ ((mul_right_injective₀ (neg_ne_zero.2 (ne (ℓ ^ j : PadicAlgCl ℓ)))).comp
    Nat.cast_injective).tendsto_cofinite.eventually (eventually_cofinite_not_isRoot (mt ext_iff.1
    fun e ↦ m.elim (k <| ((Matrix.eval_charpoly ..).trans (coeff_det_X_add_C_card ..).symm).trans <|
    · ▸ e _) (h z · (coeff_det_X_add_C_zero (_ - (N z g).1) _ ▸ e 0))))).exists.imp' (θ + .single g
    ·) (by simp_rw [IsRoot.def, eval_det]; intro; convert id
           simp [ribetNormaliser, X_mul,
             ← Matrix.smul_eq_mul_diagonal, -Finsupp.smul_single]; module)
  choose θ z' hθ hz' using (W _ .univ).imp fun θ h ↦ ((IsFractionRing.isAlgebraic_iff (intQpBar ℓ)
    (PadicAlgCl ℓ) _).2 (.of_finite ..)).exists_nonzero_coeff_and_aeval_eq_zero
    (Pi.isUnit_iff.2 (h · ⟨⟩ |>.isUnit)).mem_nonZeroDivisors
  rw [aeval_pi_apply, funext_iff] at hz'
  choose J _ _ ty hP using exists_isPrimeTriangle O.rankDiff D.algebraMap_mem_cycloField
    (by grw [hc.rank_le.2]; exact D.nat_lt_of_hasLogBound) (by grw [hc.rank_le.2]; exact hC) hℓ
    D.nat_le_of_hasLogBound fun ν g ↦ (exists_eventually_no_eigenvalue_one
    (hq.2.1.isLocallyConstant.continuous.smul (continuous_val.comp (hR h𝓧).continuous)) _ (by
    intro; simp [hq.2.1.eq_one_of_mem_inertiaAbove γ (hγ.imp (by clear * - hq; grind [IsAuxTwist])),
      h₀, _root_.smul_pow, smul_comm (ϑ.invAvatar g), pow_right_comm y]; rfl) (hy ν)).elim fun i
    hσ ↦ ⟨γ ^ i, by simp [cycChar_eq_one_of_mem_inertiaAbove (hγ.imp fun _ ↦ .imp_left (·.2))],
    inter_mem_inf ((eventually_mostFrobenii ((eventually_notMem_star_notMem ℓ (badPlaces D ℓ)).and
    (B.eventually_isOffLevel (L := ![])))).and <| .all fun x : {x : B.Eigensystem _ // (∀ g k, ‖((N
    x g).1.charpoly.coeff - (N x₀ g).1.charpoly.coeff) k‖ < 1) ∧ x ∈ s} ↦ x.1.2.elim fun f m ↦
    eventually_heckePoly_eq_string_mul (x := x.1.1) m.1.1 m.2 x.2.2 (cp _)) (preimage_mem_comap hσ)⟩
  -- `ν` beats the constant that `exists_diagOp_mem_ellIntegralForms` names below
  choose! ν hν using @ENNReal.exists_nat_gt _
  have w (a : EllAdicIntegers) : a.1 = algebraMap _ _ a := rfl
  choose Q tri q s₅ using hP _ ν.succ_pos
  let a := ((coeHom _).comp (chiOneInv O)).codRestrict (intQpBar ℓ) (norm_eq_one_of_continuous (by
    fun_prop) · |>.le)
  choose e s he using fun k x ↦
    (q k).2 x _ (s₅ k) (congr(‖_ - coeff $(charpoly_eq_mul_of_trace_pow_add _ _ _ (by
    simpa [N, _root_.smul_pow, pow_right_comm] using hL h𝓧 <| _ ^ ·)) _‖).ge.trans_lt <| x.2.1 _ ·)
  let ξ {J L x v} m (a : _ ∧ _) : B.Eigensystem (J := J) L := ⟨x, _,
    ⟨a.1, B.formsOfLevel_base_le _ (sp v m)⟩, a.2⟩
  refine (B.exists_diagOp_mem_ellIntegralForms Q (q · |>.1.2) (a := a) (N := N) (fun _ _ ↦
    rfl) (fun k ↦ Subtype.ext ((chiOneInv_spec (Q.frobData k).isPlaceOver (tri.isNewPlaces k).1 0
    (inv_mem (Q.frobData k).isPlaceOver.tameGenerator.2)).trans (pow_zero _))) _ z' (𝓧 ·)
    ⟨ξ m₁ m₂, h𝓧⟩ _ hc.odd.2.pos.ne' (fun k x m h₀ h₁ ↦ (s k ⟨⟨x, m⟩, fun g k ↦ h₁ ⟨_, sub_mem
    (algebraMap_mem _ (⟨_, cp ..⟩ : EllAdicIntegers)) (B.charpoly_mem_heckeAlgebra (a := a) (fun _
    _ ↦ rfl) g k)⟩ (sub_self _), by_contra (h₀ <| hz' ⟨_, ·⟩)⟩).imp fun _ ↦ .imp_right (·.trans
    (Polynomial.map_dvd _ (Finset.univ.dvd_prod_of_mem _ (Finset.mem_univ _)))))
    (dvd_iff_ellVal_le.2 <|
    (hν (by simp [ellVal, ne, w, map_ofNat]; exact (hθ <| Subtype.ext ·))).le.trans <| by simp [w])
    fun S _ hS ↦ ribet_columns hc hq hh tri S (co _ _ (q · |>.1.1.1) _ ·.2) .refl (fun x ↦
    ⟨hR x.2, hS₀ x.2⟩) (hL ·.2) hS (fun j ↦ (eval_prod ..).trans
    (Finset.prod_eq_one fun i _ ↦ he j i) : ∀ j,
    eval (1 : EllAdicIntegers) _ = 1) _ θ).elim fun s h ↦ ?_
  let' E s := B.diagOp (L := Q.w) s ∘ₗ toSmoothForm
  have key s {y v} m a : (E s ∘ₗ tupleProj O c) v = _ := congr(E
    s $(IsApt.tupleProj_eq_self_of_mem_range m)).trans (B.diagOp_apply s (@ξ _ _ y v m a) a.1)
  refine ⟨_, fun v m ↦ (z m).elim (⟨0, by simp [·]⟩) fun k ↦ ⟨_, key _ k.1 k.2.choose_spec⟩,
    fun l e ↦ smul_left_injective ℂ m₂.2 (key s m₁ m₂ ▸ e) ▸ ?_, fun a b w m e ↦ ?_⟩
  convert ellVal_le_iff.1 h.1 using 1 <;> simp [rpow_def_of_pos, pos] <;> ring
  have : _ • _ • w.toSmoothForm ∈ BaseLevel.ellIntegralForms := e ▸ h.2 _ (sp _ ⟨_, rfl⟩) _ (j _
    fun _ h ↦ by simpa using! (weylGauge_le_one_iff (ι := _) _ h).1 ((hΞ b).1 _)) _ (sp _ ⟨_, rfl⟩)
    (fun s k ↦ (hw.trans (sInf_le fun v m ↦ (z m).elim (by simp [·]) fun r ↦ r.2.elim fun _ a ↦ by
    simpa [k (ξ r.1 a) ⟨v, m, a⟩] using key s r.1 a) : _ ≤ (E s ∘ₗ _).ker) (by simp))
    fun s k ↦ (E s ∘ₗ _).sub_mem_ker_iff.1 (show tupleProj O c (Ξ' b - _) ∈ (E s).ker by
    -- a weak lift that is orthogonal to the cut and to the impostors at `w` is an impostor
    choose w ok hv hS using ((B.eventually_isOffLevel (L := ![])).and_frequently
      (frequently_isSplit_notMem_places O)).exists
    refine le_of_isotypic_mem (Z :=
      (tupleProj O c).range ⊓ Zᗮ ⊓ (_ ⊓ (O.heckePolyOnForms hv hS (O.testValue w)).ker)ᗮ) (by
      iterate 2 intros; apply_rules only [Sublattice.inf_mem, orthogonal_mem_invtSubmodule_hecke,
        IsApt.range_tupleProj_mem_invtSubmodule, hT]
      intro; simp +contextual [O.heckePolyOnForms_comm hv]) (fun x v r a ↦ by_contra fun H ↦
      inner_self_ne_zero.2 (ne_zero_of_map a.2) (r.2 v ⟨r.1, ?_⟩)) ⟨⟨⟨_, rfl⟩,
      isSymmetric_tupleProj.orthogonalComplement_mem_invtSubmodule (hw.trans (sInf_le fun v m ↦
      (z m).elim (by simp [·]) (by simp [tupleProj_eq_self_of_mem_range ·.1, m.1]))) (by simp)⟩,
      fun _ a ↦ by rw [← isSymmetric_tupleProj, tupleProj_eq_self_of_mem_range a.1.1,
      sub_mem ((hΞ b).2 _ _ _) (orthogonal_le inf_le_right (by simp)) _ ⟨⟨le a.1.1, a.2⟩, a.1.2⟩]⟩
    let y {J L} := @ξ J L x v r.1.1 a
    choose z t e u using hasHeckePolyAt_of_mem_eigenformsAt (ok.2.2.2 _ y.2 ⟨a.1, sp _ r.1.1⟩) hv
    simpa [O.heckePolyOnForms_eq_smul _ _ (isSphericalWith_of_heckeSplit z u), ne_zero_of_map a.2,
      e, eval_heckePoly, AuxPair.testValue, AutChar.frobValue, HeckeChar.atUnif] using
      isRoot_hecke_string a.1 a.2 (by_contra fun h ↦ H <| by simp [E, B.diagOp_apply s y a.1,
      k y (hz' ⟨y, h⟩)]) ok.2.2.1 ⟨z, t, e, u⟩ (by simp [O.rank_lt]))
  simpa [nsmul_eq_mul, ← PadicComplex.norm_extends ℓ D.chosenGroupOrder, inner_smul_right_eq_smul,
    field] using (Ξ a).norm_inner_le_one (D.chosenGroupOrder • D.chosenGroupOrder • w) ⟨(algebraMap
    ..).comp ιℓ.toRingHom⟩ (D.card_classAut_dvd_chosenGroupOrder hc.card_le levelOf_le_Kf) (hl a _)
    (weylGauge_le_one_of_integralAbove (ι := _) _ (by simpa using! this · ·))
