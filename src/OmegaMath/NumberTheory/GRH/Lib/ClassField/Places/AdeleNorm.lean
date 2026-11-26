import OmegaMath.NumberTheory.GRH.Lib.General.Groups.ArtinDefs
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.IdeleHilbert90
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Adeles.RationalPoints
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic number theory (textbook or folklore).

Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes (known
result; see Lib.ClassField.Places.LocalFrobenius).

Part of: Adeles of a number field: base change, discreteness and compact quotient, modulus (known
result; see Lib.Adelic.Adeles.IdeleHilbert90).

This file: Ideles to ideals and class group; large S; open subgroups that contain the principal
ideles of totally positive elements have finite index.
Dirichlet–Chevalley–Hasse S-unit theorem: finite generation and rank. Norm map on finite adeles of
an extension and its basic properties. -/

open Algebra FractionalIdeal Function Module NumberField Subgroup Valued WithZero
  IsDedekindDomain.FiniteAdeleRing IsDedekindDomain.HeightOneSpectrum NumberField.Units

variable {K} [Field K] [NumberField K] {R S : Set (FinPlace K)} (K' L) [Field K'] [NumberField K']
  [Field L] [NumberField L] [Algebra K' L] [Algebra K L] (w : FinPlace L)

attribute [-simp] WithZero.inv_exp
attribute [local simp] WithZero.exp_neg

@[ext] lemma fractionalIdeal_count_ext {I J : _ˣ} (h : ∀ v : FinPlace K, count K v I.1 = count K v
  J) : I = J := Units.ext ((· K I.ne_zero ▸ by aesop) finprod_heightOneSpectrum_factorization')

lemma exists_idele_divisor_hom : ∃ d : _ →* _ˣ, (∀ a w, v (a.1 w) ≤ 1 ↔ 0 ≤ count K w (d a)) ∧
  d.ker = idelesUnitOff ∅ ∧ (∀ v, d (locIdele v (uniformizer v)) = mk0 K ⟨v.1, by simp [ne_bot]⟩) ∧
  ∀ x, d (principalIdele x) = toPrincipalIdeal _ K x := by
  choose d hd using fun a : (𝔸f K)ˣ ↦ (⟨.mk0 _ (by simp [finprod_ne_zero, zpow_ne_zero, ne_bot]),
    (count_finprod K · _ (.mono (finite_idele_val_ne_one a) (by aesop)))⟩ :
    ∃ I, ∀ w, count K w (Units.val I) = -log (v (a.1 w)))
  refine ⟨.mk' d ?_, ?_, Subgroup.ext ?_, .symm ⟨?_, ?_⟩⟩ <;> simp_all [count_mul, count_one,
    mul_comm, isUnit_iff.1, count_maximal, fractionalIdeal_count_ext_iff, ← @exp_inj ℤ,
    ← @exp_le_exp ℤ]
  rintro ⟨x⟩ _; obtain ⟨a, b, hb, ⟨⟩⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have ha : a ≠ 0 := by aesop
  rw [count_well_defined K (a := b) (J := .span {a})]
  · simp_all [valuation_of_algebraMap, intValuation_def, inv_mul_eq_div, nonZeroDivisors.ne_zero hb]
  · exact spanSingleton_ne_zero_iff.2 (by simp_all [nonZeroDivisors.ne_zero hb])
  · rw [coeIdeal_span_singleton, ← map_mul, inv_mul_eq_div]
  · aesop (add simp [ne_comm])

lemma exists_idele_classGroup_hom : ∃ c : (𝔸f K)ˣ →* ClassGroup (𝓞 K), c.ker = principalIdele.range
  ⊔ idelesUnitOff ∅ := exists_idele_divisor_hom.imp' (ClassGroup.mk K).comp fun d h ↦
  h.2.1 ▸ Subgroup.ext (by simp [← (ClassGroup.equiv K).map_eq_one_iff, ↓← comap_map_eq, h])

/-- For every finite idele a of K, the power a^h, with h the class number of K, is a principal
idele times an idele that is a unit at every prime. -/
lemma pow_classNumber_mem_principal_sup a : a ^ classNumber K ∈ (@principalIdele K ..).range ⊔
  idelesUnitOff ∅ := exists_idele_classGroup_hom.choose_spec.le (by simp [classNumber])

lemma exists_valuation_eq_of_mem_sup {a} : a ∈ principalIdele.range ⊔ idelesUnitOff S → ∃ x,
  ∀ w ∉ S, w.valuation K (Units.val x) = v (a.1 w) := by aesop (add simp mem_sup)

/-- For finite sets R, R' of finite places there is a finite S ⊃ R, meeting R' only inside R,
such that every finite idele is a principal idele times a unit outside S. -/
lemma exists_sup_idelesUnitOff_eq_top (hR : R.Finite) (R' : _ := ∅) (h : Set.Finite R' := by simp) :
  ∃ S, S.Finite ∧ R ⊆ S ∧ (∀ v ∈ R', v ∈ S → v ∈ R) ∧ principalIdele.range ⊔ idelesUnitOff S = ⊤ :=
  exists_idele_classGroup_hom.rec fun c e ↦ by
  choose x _ _ using fun y ↦ denseRange_algebraMap_finAdele.mem_nhds ((eventually_ne_nhds (invFun c
    y).ne_zero).and (h.eventually_all.2 fun v _ ↦ (continuous_evalAt v).continuousAt (locally_const
    (by simp [isUnit_iff.1]))))
  refine ⟨_, hR.union (Set.finite_iUnion fun y ↦ finite_idele_val_ne_one (principalIdele (.mk0 (x
    y)⁻¹ ?_) * invFun c y)), ?_, ?_, top_unique fun a _ ↦ (comap_map_eq_self (e.trans_le ?_)).le ⟨_,
    mem_sup.2 ⟨_, ⟨.mk0 (x (c a)) ?_, rfl⟩, _, ?_, mul_eq_of_eq_inv_mul rfl⟩, apply_invFun_apply⟩⟩
  repeat simp_all [isUnit_iff.1, idelesUnitOff_mono, ↓sup_le_sup]

/-- An open subgroup H of the finite ideles of a number field K that contains the principal
ideles of all totally positive elements of K^× has finite index. -/
lemma finiteIndex_idele_subgroup_of_isOpen H (h : H.IsOpen) (h' : ∀ x : Kˣ, IsTotallyPositive x.1 →
  principalIdele x ∈ H) : FiniteIndex H := ⟨by
  rw [← relIndex_mul_index (le_sup_left (b := principalIdele.range)),
    ← relIndex_mul_index le_sup_left]
  simpa [← index_comap] using ⟨((Units.map (.pi fun φ ↦ signHom.toMonoidHom.comp
    _)).ker.finiteIndex_of_le (h' · ∘ (sign_eq_one_iff.1 congr($(·).1 ·)))).1,
    isCompact_idelesUnitOff_empty.relIndex_ne_zero (isOpen_mono le_sup_left h),
    (finiteIndex_of_le (exists_idele_classGroup_hom.choose_spec.trans_le (by order))).1⟩⟩

instance : NonarchimedeanGroup (𝔸f K)ˣ := have : TotallyDisconnectedSpace (𝔸f K)ˣ := ⟨fun s _ h ↦
    s.subsingleton_of_image (by aesop_cat) (h.image (·.1 ·) (by fun_prop)).subsingleton⟩
  have := (@isCompact_idelesUnitOff_empty K _ _).compactSpace
  .nonarchimedean_of_emb (idelesUnitOff ∅).subtype
    (isOpen_idelesUnitOff _).isOpenEmbedding_subtypeVal

/-- For a finite set S of primes of K there is an integer h ≥ 1 such that, for every d : S → ℤ,
some S-unit has valuation exp(h·d(v)) at each v in S. -/
lemma exists_valuation_eq_exp_mul (hS : S.Finite) : ∃ h ≠ (0 : ℕ), ∀ d : S → ℤ, ∃ x :
    S.unit K, ∀ v, v.1.valuation K x.1.1 = exp (h * d v) := ⟨_, classNumber_ne_zero K, fun d ↦
    (exists_idele_eq_uniformizer_zpow (Subtype.val.extend d 0)
  (hS.subset (by_contra (by aesop)))).elim fun a _ ↦ Subtype.exists.2
  ((exists_valuation_eq_of_mem_sup (pow_classNumber_mem_principal_sup a)).imp (by aesop_cat))⟩

/-- Dirichlet's S-unit theorem: for a finite set S of finite places of K, the S-unit group is
finitely generated of rank #S + (number of infinite places) − 1. -/
lemma SUnit.dirichlet_unit_theorem (hS : S.Finite) : Module.Finite ℤ (Additive (S.unit K)) ∧
  finrank ℤ (Additive (S.unit K)) + 1 = S.ncard + Fintype.card (InfinitePlace K) := by
  obtain ⟨_, c, _, k⟩ := hS.fintype, exists_valuation_eq_exp_mul hS
  let g := (AddMonoidHom.mk' (fun (x : Additive (S.unit K)) (v : S) ↦
    (v.1.valuation K x.toMul.1).log) (by aesop)).toIntLinearMap
  have e : g.ker ≃ₗ[ℤ] _ := ((MulEquiv.subgroupCongr (H := g.ker.toAddSubgroup.toSubgroup') (by
    ext x; simp [funext_iff, g, ← @exp_inj ℤ]
    peel with v; grind [x.2 v])).trans ((subgroupOfEquivOfLe (by tauto)).trans
    ((IsDedekindDomain.integer_empty (𝓞 K) K ▸ Set.unitEquivUnitsInteger ..).trans (Units.mapEquiv
    (botEquivOfInjective Subtype.val_injective).toMulEquiv)))).toAdditive.toIntLinearEquiv
  have := (isNoetherian_of_range_eq_ker (g.ker.subtype ∘ₗ e.symm.1) g (by simp)).finite
  simp_all [← g.ker.finrank_quotient_add_finrank, g.quotKerEquivRange.finrank_eq,
    e.finrank_eq, finrank_eq, rank, add_assoc, NeZero.one_le, g.range.finrank_le.eq_of_not_lt
    (mt g.range.exists_of_finrank_lt fun ⟨z, h⟩ ↦ h c (by lia) ((k z).imp' .ofMul (by aesop)))]

instance : Free (𝔸f K') (𝔸f L) := .of_basis (adeleBasis (finBasis ..))

instance : Module.Finite (𝔸f K') (𝔸f L) := .of_basis (adeleBasis (finBasis ..))

/-- For an extension L/K of number fields, the algebra norm from the finite adeles of L to the
finite adeles of K, as a multiplicative map. -/
noncomputable abbrev adeleNorm := norm (S := 𝔸f L) (𝔸f K')

@[fun_prop] lemma continuous_adeleNorm : Continuous (adeleNorm K' L) := by
  simp [(isHomeomorph_adeleCombination (finBasis K' L)).isQuotientMap.continuous_iff, comp_def,
    norm_eq_matrix_det (Free.chooseBasis ..), Fintype.linearCombination]; fun_prop

@[simp] lemma adeleNorm_algebraMap (x : L) : adeleNorm K' L x = norm K' x := by
  simp [norm_eq_matrix_det (adeleBasis (finBasis ..)), norm_eq_matrix_det (finBasis ..), ← map_mul,
    Matrix.det_apply, leftMulMatrix_eq_repr_mul,
    adeleBasis]; simp [← adeleCombination_repr (finBasis K' _)]

lemma adeleNorm_finAdeleIncl : ∀ a, adeleNorm K' L (finAdeleIncl K' L a) = a ^ finrank K' L :=
  denseRange_algebraMap_finAdele.eq

lemma finAdeleIncl_adeleNorm [IsGalois K' L] : ∀ y, finAdeleIncl K' L (adeleNorm K' L y) = ∏ σ :
    Gal(L/K'), adeleMap σ y :=
  denseRange_algebraMap_finAdele.eq (by simp [norm_eq_prod_automorphisms])

variable {L}

/-- For an extension L/K and a finite place w of L above v, the local norm L_w^× → K_v^×: the
v-component of the adelic norm of the idele supported at w. -/
noncomputable def localNorm :=
  ((ideleAt (w.below K')).comp (Units.map (adeleNorm ..))).comp (locIdele w)

lemma adeleNorm_mem_Ohat {y} (h : y ∈ Ô L) : adeleNorm K L y ∈ Ô K :=
  Set.MapsTo.closure_left (by simpa using
  (isIntegral_norm K ·.2)) (by fun_prop) isCompact_Ô.isClosed (Subtype.dense_iff.1 dense_Ô h)

/-- For number fields L/K, a finite place w of L and y in L_w^×, the norm to K of the finite
idele that is y at w and 1 elsewhere is 1 at every place except the one below w. -/
lemma adeleNorm_locIdele y : (locIdele w y).map (adeleNorm K L) = locIdele _ (localNorm K w y) := by
  ext v : 2; by_cases v = w.below K; aesop
  simpa [adeleNorm_finAdeleIncl, *] using congr(adeleNorm K
    L $(show SemiconjBy (finAdeleIncl K L (idem {v})) _ 1 by
    simp_all [SemiconjBy, DFunLike.ext_iff, ← and_forall_ne w, adeleMap_apply, eq_comm]) v)

lemma v_adeleNorm_eq_one {y} (h : y ∈ idelesUnitOff ∅) v : Valued.v (adeleNorm K L y.1 v) = 1 :=
  mem_idelesUnitOff (a := y.map _).1 (coe_idelesUnitOff_empty.ge
  ((coe_idelesUnitOff_empty.le h).imp adeleNorm_mem_Ohat adeleNorm_mem_Ohat)) v id

variable [IsCMField K] [IsCMField L]

@[simp] lemma adeleNorm_star w : adeleNorm K L (star w) = star (adeleNorm K L w) := .trans
    (norm_eq_of_equiv_equiv starRingAut starRingAut (RingHom.ext (adeleMap_star _)) _) (by aesop)

lemma units_map_adeleNorm_star w : Units.map (adeleNorm K L) (star w) =
  star (w.map (adeleNorm ..)) := by aesop
