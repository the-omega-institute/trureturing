/- GID: D5/S3/Zeros/GRH/New/Exchange/GridFirstColumns
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/GridFirstColumns
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.GridFirstColumns. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/GridFirstColumns.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.RowLadder
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Crude rows: integral twisted lifts and bounded conjugates (see New.Exchange.CrudeRows).

This file: Twist-free restriction projected to level g; periods under translation; index ratios. -/
seal Finset.univ Finset.sum Finset.prod

open Finset Equiv Fintype Function Ideal MatMul Matrix MulAction LevelPlaces Pointwise Space
  Ideal.Quotient

variable {P} (D : Data P) (ϑ : D.MFoldTwist)

namespace Data

instance : IsLocalHom (reduceToTriangle ϑ false) :=
  ⟨Quot.ind fun _ h ↦ ((isUnit_mk_pow_iff_isUnit_mk _ (NeZero.ne D.b₁)).2 h).map
  (factor (by simp [levelModulus, mul_pow, mul_mono, pow_le_self NeZero.out, Bool.cond_false,
    -Bool.cond_eq_ite]))⟩

/-- At node (0, j) of the grid V, the order `Data.triangleOrder` of GL modulo `Data.triangleModulus`
is C times the index `Data.levelIndex` of the level, with C independent of ϑ. -/
lemma triangleOrder_eq_mul_levelIndex j : ∃ C, ∀ ϑ, D.triangleOrder false ϑ j =
  C * levelIndex ϑ false 0 j := ⟨(card (D.triangleModulus false 1).ResRing / card
  (D.gridModulus 1).ResRing) ^ card (D.Y j) ^ 2, fun ϑ ↦ by
  simpa [finMean, nodeLevel, levelIndex, card_congr of.symm, card_𝔪, mul_pow, div_pow, field, sq,
    pow_mul, prod_eq_zero_iff, (card_congr (.ofInjective _ Units.val_injective)).trans (card_subtype
    IsUnit), isUnit_iff_isUnit_det, ← RingHom.map_det, -RingHom.mapMatrix_apply] using!
    (finMean_comp_surjective
    ((reduceToTriangle ϑ false).mapMatrix (m := D.Y j)).toAddMonoidHom (factor_surjective _ :
    Surjective (reduceToTriangle ..)).comp_left.comp_left (if IsUnit · then 1 else 0)).symm⟩

/-- For j ≤ m, the period `Data.diagonalPeriodForm` of forms y on V_{j,j} and φ on Z_{j,j} = V_{j,j}
⊕ ⟨(−1)^j⟩, at a real point g, is unchanged when y is translated by a finite point u and φ by
u ⊕ 1. -/
lemma diagonalPeriodForm_formRep {j h g} u y φ : diagonalPeriodForm ϑ h g (formRep _ _ u y)
  (formRep _ _ (U.block (D.gridDiagEquiv j) (u, 1)) φ) = diagonalPeriodForm ϑ h g y φ := by
  refine (congrArg _ (funext fun x ↦ ?_)).trans ((gridSpace ..).integral_comp_mul_right u
    (fun a b x ↦ ?_) (y.2.1.rec (φ.2.1.rec (by fun_prop)))).1
  simp [Prod.mul_def]; erw [← (U.block _).map_mul]; aesop
  simp; rw [y.2.rat_mul _ b, ← one_mul (1, _), ← Prod.mk_mul_mk, map_mul, map_mul,
    mul_assoc, φ.2.rat_mul] <;> simp_all [gridSpace_diag h, mem_Γ_iff_range, Space.reindex,
    sum, ← map_inv, reindex_equiv (D.gridDiagEquiv j), -coe_units_inv, -RingHom.mem_range]

/-- For g real, some linear r from `Data.gridLevelForms` 0 (forms on Y₀ ⊕ ⟨1⟩) to forms of level
K(g₀g₁) = `Data.chosenLevel` on Y₀ has ⟨y, rφ⟩ = ∫ ȳ(x) φ((x ⊕ 1)g) dx for all φ, ϑ and y of
principal level `Data.levelPlaces` ϑ. -/
lemma exists_restrict_bordered g : ∃ r : D.gridLevelForms 0 →ₗ[ℂ] levelSpace ((gridSpace ..).formRep
  (D.gridKernel false 0 0 false)) chosenLevel, ∀ φ (ϑ : D.MFoldTwist), ∀ y ∈ levelSpace (formRep ..)
  (levelOf (D.levelPlaces ϑ).placeAt ⊥), (gridSpace ..).petersson y (r φ) = diagonalPeriodForm ϑ
  zero_le g (conjForm (isConjKernelPair_gridKernel (by simp) false).2 y) φ := by
  have he := @isConjKernelPair_gridKernel _ D false 0 0 (by simp) false
  rcases (⟨(·.2.exists_level.elim fun K h ↦ .mono K.mem_nhds_one (Subtype.ext ∘ funext ∘ h ·))⟩ :
    IsSmoothRep ((gridSpace ..).formRep (D.gridKernel false 0 0 false))),
    (gridSpace ..).finite_levelSpace he.1 ⟨D.chosenLevel, isOpen_levelOf⟩
  refine let A :=
      (diagonalPeriodForm 1 zero_le g ∘ₛₗ conjForm he.2).flip.compr₂ₛₗ (starLinearEquiv ℂ).1
    let r := .applyₗ 1 ∘ₗ .adjoint.1 ∘ₛₗ A.domRestrict₁₂ ..
    ⟨r, fun φ ϑ y m ↦ star_injective ((map_compactMean_of_const (innerₛₗ _ (r φ).1) fun u c ↦
    ?_).symm.trans
      ((((A φ).domRestrict _).adjoint_inner_left ⟨_, compactMean_mem_levelSpace y⟩ _).trans ?_))⟩
  simpa [(r φ).2 ⟨u, c⟩] using! inner_formRep u (r φ) y
  simp [-diagonalPeriodForm]; apply map_compactMean_of_const; rintro _ ⟨u, c, rfl⟩
  have ⟨v, b, e⟩ := exists_reductionK₀_eq ((gridModulus 1).reductionK₀ u)⁻¹
  have w := (Modulus.mem_principalLevel_iff gridModulus_one_ideal (u * v)).2 (by simp [e])
  rw [← D.diagonalPeriodForm_formRep ϑ (u * v), φ.2 ⟨_, _⟩]
  simp [A, periodPairing, ← mem_levelSpace_formRep_iff.1 m v (D.chosenLevel_inf_trivialOn_le ϑ
    ⟨(D.chosenLevel.mul_mem_cancel_left ⟨u, c, rfl⟩).1 (principalLevel_le_chosenLevel
    piGBar_dvd_gridLevelGen w), by simp_all [places_modulus_eq_union, IsChosen,
    Gf.mem_supportedOn.1 b, twist_one_spec, levelNorm_mem_and_notMem_of_mem_Q _ ϑ.1.1]⟩) (_ * u.1)]
  simp_all [principalLevel, mem_Kf, reindex_equiv (D.gridDiagEquiv 0)]; exact ⟨0, by simp⟩

variable {D ϑ} {g : ∀ p, GL (D.NodeIndex p) (gridModulus ϑ).ResRing} (h : ∀ z,
  g (z, 0, D.m) = 1) (D' : Data P)

include h in
/-- Let g be 1 at both nodes (0, m), and k in K_0 reduce to g(0, b), with k = 1 if b = m. Then k
translates the descent `Data.legDescents` for the moved tuple g·S to that for S, times
`Data.edgeCharProd` over its edges. -/
lemma formRep_legDescents_tupleAction {z b} S F k (e : g (z, 0, b) = (gridModulus ϑ).reductionK₀ k)
  (n : b = D.m → k = 1 := by simp [m_eq_two_mul_varrho_add_two]) : formRep _ _ k.1 (legDescents
  (tupleAction g S) z b F) = edgeCharProd g (D.legEdges z b) • legDescents S z b F := by
  fun_induction legDescents S z b <;> rw [legDescents]
  rename_i b l i
  let u := ite (b + 1 = D.m) 1 (liftMod (g (z, 0, b + 1)))
  have U : g _ = Modulus.reductionK₀ _ u := by grind [reductionK₀_liftMod]
  simp [tupleAction, *]
  refine ((isEdgeFamily_grid id false rfl zero_le l).isArrow_modDatum.2.formRep_formLift_of_eq_smul
    (pairWeil_modDatum_single k u) _).trans (congr(_ • descentMove _
      $(i u U (ite_eq_left ·))).trans ?_)
  simp [gridChar_det, smul_smul, edgeCharProd, legEdges, prod_eq_prod_Ico_succ_bot,
    edgeChar, *]; ring
  by_cases ‹ℕ› = D.m <;> simp_all [legEdges, edgeCharProd, not_lt.2]

/-- Let g be 1 at both nodes (0, m), and its value at (0, 0) in Z be that in V extended by 1.
Moving S by g multiplies the period over U(Y₀) of the descents of Ξ, φ by `Data.edgeCharProd`
over their edges. -/
lemma diagonalPeriodForm_tupleAction (h : ∀ z, g (z, 0, D.m) = 1) (k : g (true, 0, 0) =
  blockInlGL (D.gridDiagEquiv 0) (g (_, 0, 0))) r Ξ φ S : diagonalPeriodForm ϑ zero_le r
  (legDescents (tupleAction g S) _ 0 Ξ) (legDescents (tupleAction g S) _ 0 φ) = edgeCharProd g
  (D.path 0) * diagonalPeriodForm ϑ zero_le r (legDescents S _ 0 Ξ) (legDescents S _ 0 φ) := by
  have ⟨w, W⟩ :=
    map_block_eq_blockGL (gridModulus ϑ).reduction (D.gridDiagEquiv 0) (liftMod (g (_, 0, 0))) 1
  erw [← diagonalPeriodForm_formRep,
    formRep_legDescents_tupleAction h S Ξ _ (reductionK₀_liftMod _).symm,
    formRep_legDescents_tupleAction h S φ ⟨_, w⟩ (by erw [k, W, reductionK₀_liftMod]; simp)]
  simp [edgeCharProd, legEdges, gridPath, prod_union, disjoint_left, field]

/-- At the last stage j = m, for each real point g there is β with period `Data.gridPeriod` equal
to β·`Data.endPeriod`(Λ(ϑ), Ξ, φ) for all (ϑ, Ξ, φ). -/
lemma gridPeriod_eq_endPeriod Λ g : ∃ β, ∀ x, D'.gridPeriod Λ x le_rfl g =
  β * endPeriod (Λ x.1) (·.rec x.2.1 x.2.2) := by
  -- the lifts along a last column are chains of theta kernels
  have C z {j} (hj : j ≤ D'.m) : ∃ c, ∀ ϑ (S : EdgeTuple ϑ) F, (gridPathMap S z j _ F).1 =
      ofAlgForm (-D'.gridParam z 0 j _) _
    ((c * levelIndex ϑ z j D'.m / levelIndex ϑ z 0 D'.m) • endChain S z j F) := by
    induction' j with j ih <;> obtain ⟨U, W⟩ := (D'.endWeightData z).2.2
    · exact ⟨1, by simp [gridPathMap,
        legDescents]; intros; erw [ofAlgForm_toAlgForm (W 0 hj)]⟩
    obtain ⟨⟨c, ih⟩, H, e⟩ := ih (by omega), U j
    refine (exists_lift_ofAlgForm_eq_smul (W j (by omega)) (W _ hj) H (c := 1 * P.jetScale D'.s)
      (by simp)).imp' (· * c / P.vacuumScale D'.s ^ Fintype.card
      (D'.EndIndex z j.succ × D'.EndIndex z j) / D'.levelIndex 1 z j.succ D'.m)
      fun _ u _ _ _ ↦ ((isEdgeFamily_grid id true rfl).isArrow_modDatum.1.coe_formLift _).trans ?_
    rw [ih, gridHarmonic, e]; repeat refine isStd_gridSpace.std_induction ?_
    erw [u _ _ (endKernel.eq_1 ..).symm (vacuumDatum ..)]; simp [compUpTo, chain, endChain,
      levelIndex_eq_untwisted, endLevel, Modulus.stdLevelIndex_levelOfSubgroup, endDatum,
      funext_iff, field]
  choose c hc using (C · le_rfl)
  choose β H using D'.endBranching.2.2 g
  use β * (∏ z, c z) * D'.levelIndex 1 true D'.m D'.m / D'.levelIndex 1 true 0 D'.m,
    fun _ ↦ congr(Λ _ fun S ↦ $(by
    simp [periodPairing]; erw [hc, hc, H _ _ _ _ (endLevel ..)]
    simp [endLevel, Modulus.stdLevelIndex_levelOfSubgroup, levelIndex_eq_untwisted, field,
      endBlockPoint])).trans ((Λ _).map_smul ..)

/-- If `S` holds at the start, the kernels preserve it and pairings of `S`-vectors satisfy
‖σ(M·a)‖ ≤ R, then `endPeriod` is a sum of N·∏ card `StdClasses` such a, N ≤ `tupleBound ϑ ^ n`. -/
lemma endPeriod_mem {n} {Λ : GridDatum ϑ} (hΛ : IsTidy n (D.path D.m) Λ) {y} (hy :
  FixedByEndLevels ϑ y) (S : ∀ _ _, _ → _ → Prop) {F M R} [NormedField F] (σ : ℂ →+* F) (hs : ∀ x z,
  ∀ j < D.m, ∀ g h v, S z j g v → S z _ h ((endKernel ϑ z j).jetMatrix ((endKernel ϑ z j).ω (g,
  h) (@endDatum _ D ϑ x z j)) v)) (hB : ∀ z g, S z 0 g ((D.endToAlgForm z (y z)).1 g)) (hA :
  ∀ {g v' v}, S _ _ g v' → S _ _ (endBlockPoint ϑ g) v → ‖σ
  (M * D.endPairing v' v)‖ ≤ R) : ∃ N ≤ tupleBound ϑ ^ n, endPeriod Λ y ∈ (N * ∏ z,
  ∏ j ∈ range (D.m + (!z).toNat), .card (StdClasses (endLevel ϑ z j))) • {a | ‖σ (M * a)‖ ≤ R} := by
  -- invariance of the integrand, by the definition of tidy data
  have J (a : ∀ z j, endLevel ϑ z j) (e : (a ..).1 = U.block (D.gridDiagEquiv _) ((a ..).1, 1))
    (β β' : _ →ₗ[ℂ] _) : let F Φ := Λ fun x ↦ D.endPairing (β
      (TensorChain.pure (Φ x false) D.m)) (β' (TensorChain.pure (Φ x true) D.m))
    F (fun x z j ↦ (endKernel ϑ z j).ω (a z j, (a z _).1) (endDatum x z j)) = F endDatum := by
    choose u k f using (a · · |>.2)
    simp_rw [← f] at *
    let g (p : Node) := Pi.mulSingle (M := fun b ↦ GL (D.GridIndex p.1 p.2.1 b) _) _
      ((gridModulus ϑ).reductionK₀ (u ..)) p.2.2
    exact mul_left_cancel₀ (by simp [edgeCharProd, prod_eq_zero_iff, MulChar.apply_eq_zero_iff])
      (((hΛ.equivariant g ⟨by simpa [g] using (k · 0), fun j ↦ by
      obtain rfl | h := em (D.m = j) <;> simp [g, *]
      convert! (e ▸ map_block_eq_blockGL _ _ _ 1).2; simp⟩) _).symm.trans (by
      simpa [-prod_mul_distrib, fun z S ↦ TensorChain.pure_smul (g := fun j ↦ (endKernel ϑ z j).ω (u
        z j, (u z _).1) (endDatum (tupleAction g S) z j)) (endDatum S z) _ D.m fun _ _ ↦ Subtype.ext
        ((map_smul ..).trans (.trans (congrArg _ (by
        simp [vacuumDatum, ← modDatum_vacVector]; apply pairWeil_modDatum_single
        simp [tupleAction, g])) (smul_comm ..))),
        ← Pi.smul_def, -smul_eq_mul, edgeCharProd, legEdges, gridPath, g, prod_union, disjoint_left,
        mul_assoc, gridChar_det, edgeChar, division_def] using! mul_left_comm ..))
  choose X W c s hW hc e using hΛ.isShortSum
  have T z j h := D.classAut_eq_bot_of_le_chosenLevel ((endLevel_le_principalLevel ϑ z j).trans
    (D.principalLevel_le_chosenLevel piGBar_dvd_gridLevelGen)) (boxes_endWeightData_le z h).1
  choose B b using fun z ↦ exists_linear_chain_eq_pure (endKernel ϑ z) _ (D.endToAlgForm z (y z))
  erw [endPeriod, e, ← classIntegral_sum _ (.mulLeft <| c ·) 1 ?_ (by tauto)]
  simp [prod_range_succ, mul_nsmul, -Nat.card_eq_fintype_card]
  exact ⟨_, hW, classIntegral_mem_nsmul (T _ _ .refl) (by
    rintro _ ⟨u, k, rfl⟩ g
    cases map_block_eq_blockGL (gridModulus ϑ).reduction (gridDiagEquiv ..) u 1
    convert J (Bool.rec (Pi.mulSingle _ ⟨u, by tauto⟩) (Pi.mulSingle _ ⟨_, ⟨_, ‹_›⟩, by simp_all
      [Modulus.reductionK₀, nodeLevel, m_eq_two_mul_varrho_add_two, Units.ext_iff, ← submatrix_map],
      rfl⟩)) _ (B _ g) (B _ (endBlockPoint ϑ g)) <;> simp [e, ← b, chain_equivariant, hy _,
      endBlockPoint, ← map_mul]) fun g ↦ IsJointlyInvariant.sum_chain_mem_nsmul (endKernel ϑ _)
    (L := (c · • D.endPairing.flip _)) (fun a _ ↦ by simpa [*] using
    (J (Bool.rec a 1) (by simp [*]) · _)) (T _ · ·.le) (hy _) _ (by tauto) (hB _) fun β h ↦
    IsJointlyInvariant.sum_chain_mem_nsmul (endKernel ϑ _) (L := (c · • D.endPairing _))
    (fun a _ ↦ by simpa [e] using J (Bool.rec 1 a) (by simp [*]) β) (T _ · ·.le) (hy _) _ (by tauto)
    (hB _) fun β' h' ↦ (sum_const {a | _}).le (Set.finsetSum_mem_finsetSum _ _ _ fun x a ↦ by
      simpa [mul_left_comm ‖σ M‖] using (mul_le_of_le_one_left (by bound) (by_cases (by
        simp [·]) (hc x · |>.1 |> σ.isOfFinOrder |>.norm_eq_one.le))).trans (hA (h x a) (h' x a)))⟩
  intro x; have η z := (endChain (s x) z D.m (y z)).2
  refine ⟨?_, (_ ⊓ Subgroup.comap ((U.block (gridDiagEquiv ..)).comp (.inl ..)) _).isOpen_mono
    (fun a x g ↦ ?_) (.and (η _).1 (.preimage_of_continuous (f :=
    (G.blockEmb (s := 1) Sum.elim_one_one.symm ⟨⟨1, ·⟩, 1⟩ |>.2)) (η _).1))⟩
  rintro _ ⟨γ, rfl⟩ _
  simpa [endBlockPoint, ← map_mul, ← block_embFin] using! congr($(((η _).2 ..).trans
    (stdSpace_weightRep_apply ..)) ⬝ᵥ _ *ᵥ $(((η _).2 (U.block _ (γ, 1)) (endBlockPoint ..)).trans
    (stdSpace_weightRep_apply ..))).trans (D.endBranching.2.1.choose_spec.1 ..)
  simpa [endBlockPoint, ← map_mul] using congr(D.endPairing $(x.1 g) $(x.2 (endBlockPoint ..)))

/-- For b ≤ m some Φ satisfies `Data.IsLevelTidy` of order 2(m − b) on the edges (0, i) → (0, i+1),
b ≤ i < m, of both grids, and B(ιΞ, ιφ) = N·Φ(S ↦ B(d_SΞ, d_Sφ)) for bilinear B; ι =
`Data.iotaPlus` (untwisted on φ), d = `Data.legDescents`, N the product of `Data.triangleOrder` over
these i and both grids. -/
lemma exists_isLevelTidy_iotaPlus_eq {b} (hb : b ≤ D.m) : ∃ Φ :
    GridDatum ϑ, IsLevelTidy (2 * (D.m - b)) (D.legEdges false b ∪ D.legEdges true b) Φ ∧
  ∀ (B : _ →ₗ[ℂ] _ →ₗ[ℂ] ℂ) Ξ φ, B (iotaPlus ϑ false b Ξ) (D.iotaPlus 1 true b φ) =
  (∏ i ∈ Ico b D.m, triangleOrder false ϑ i * triangleOrder true ϑ i) * Φ fun S ↦ B
  (legDescents S _ b Ξ) (legDescents S _ b φ) := Nat.decreasingInduction (fun b h ⟨Φ, q, e⟩ ↦ by
  let u z := verticalEdge z 0 b
  let Ψ z (y : Matrix (NodeIndex (u z).2) (D.NodeIndex (u z).1) _) :=
    inclusionDatum _ (y.map (reduceToTriangle ϑ z))
  have s z {n w Λ} (v : u z ∉ w) : IsLevelTidy n w Λ →
    IsLevelTidy (n + 1) (insert (u z) w) (Λ.bind (fun _ ↦ Ψ z)
    (update · _)) := .imp (.bind (by simp [card_matrix_le_tupleBound, u, h, h.le]) fun S y e ↦ by
      cases z; have : HasLeftInv y := ⟨_ * (inclMatrix _ .inl)ᵀ, (Matrix.mul_assoc ..).trans
        (isUnit_of_mapMatrix (reduceToTriangle ..) (by simp; erw [Pi.support_single_subset e,
        transpose_map, map_inclMatrix, inclMatrix_transpose_mul_self .inl]; simp)).val_inv_mul⟩
      all_goals grind [IsOfFinOrder.one]) fun C g G f ↦ by
    have a i k (h : k ∈ nodeLevel ϑ (z, 0, i)) : k.map (reduceToTriangle ϑ z) = 1 ∧
      edgeChar ϑ (u z) k.1.det = 1 := by
      cases z <;> simp [nodeLevel] at h; simp [h]
      obtain ⟨k, rfl⟩ := reductionK₀_surjective k
      erw [← gridChar_det _ _ Unit 1, gridChar_det (ϑ := 1) false b Unit 1,
        (Units.ext Modulus.factor_reductionK₀).symm.trans h]; simp [h]
    erw [edgeCharProd, prod_insert v, mul_assoc, ← C g G]
    simp [h.le, u, *]
    congr with S; simp
    convert (injective_gl_inv_mul_mul (g (u z).2) (g (u z).1)).bijective_of_finite.sum_comp _
    simp [Ψ, u, h.le, *, -coe_units_inv, ← GeneralLinearGroup.val_map_apply]
    left; congr; set_option synthInstance.maxHeartbeats 200000 in
      grind [tupleAction, Matrix.mul_assoc]
  refine ⟨_, by convert s false ?_ (s true ?_ q) <;> first | lia | simp [legEdges,
    ← insert_Ico_add_one_left_eq_Ico h, u, insert_comm], fun B Ξ φ ↦ ?_⟩
  unfold legDescents iotaPlus
  simp_rw [h, ite_true, prod_eq_prod_Ico_succ_bot h]
  erw [e (B.compl₁₂ (pointDescent ..) (pointDescent ϑ ..))]
  simp [fun z ↦ (by erw [pointDescent, modDescent, ← modDatum_factor, modDatum_eq_sum]; simp; rfl :
    pointDescent ϑ z b = (triangleOrder z ϑ b : ℂ) • ∑ y, Ψ z y • descentMove y), fun z c S y ↦
    @legDescents_congr _ D ϑ (update S (u c) y) S z (b + 1) (by grind [legEdges]),
    u, LinearMap.pi, ← sum_fn, ← Pi.smul_def, -smul_eq_mul]
  simp [mul_sum]; ac_rfl) ⟨.proj 0, ⟨⟨_, {0}, 1, 0, by simp [legEdges]⟩, by
    delta tupleAction edgeCharProd legEdges; aesop⟩, by simp [iotaPlus, legDescents]⟩ hb

/-- For some C, every ϑ has a datum Λ, tidy of order 4m on `Data.path` 0, such that
`Data.triangleOrder` at node (0, m) of V times the period `Data.diagonalPeriodForm` over U(Y₀) of
the descents `Data.iotaPlus` of Ξ, φ equals C times `Data.gridPeriod` for Λ. -/
lemma exists_isTidy_diagonalPeriodForm_eq : ∃ C Λ, ∀ ϑ, IsTidy (4 * D.m) (D.path 0) (Λ ϑ) ∧ ∀ r Ξ φ,
  triangleOrder false ϑ D.m * diagonalPeriodForm ϑ zero_le r
  (iotaPlus ϑ _ 0 Ξ) (D.iotaPlus 1 _ 0 φ) = C * gridPeriod Λ (ϑ, Ξ, φ) zero_le r := by
  choose κ K using D.triangleOrder_eq_mul_levelIndex
  choose Φ q e using (@exists_isLevelTidy_iotaPlus_eq _ D · 0 zero_le)
  let t' {ϑ} (x : ∀ p : _ × Fin D.m, _ ⧸ D.nodeLevel ϑ (p.1, 0, p.2)) : ∀ p, GL _ _
    | (z, 0, i) => if h : _ then (x (z, ⟨i, h⟩)).out else 1 | _ => 1
  let t {ϑ} x := update (@t' ϑ x) (_, 0, 0) (blockInlGL (gridDiagEquiv ..) (t' x (_, 0, 0)))
  refine ⟨κ D.m * (range D.m).prod κ, (Φ · |>.bind (fun _ x ↦ edgeCharProd (t x) (D.path 0)) fun S
    x ↦ tupleAction (t x)⁻¹ S), fun ϑ ↦ ⟨⟨fun g ⟨G, G'⟩ f ↦ ?_, add_mul 2 2 _ ▸ (q ϑ).1.bind (by
    simp; grw [prod_le_pow_card _ _ (tupleBound ϑ)]; simp; exact fun p _ ↦ (card_le_of_embedding ⟨_,
    Units.val_injective.comp Quotient.out_injective⟩).trans (by simp [card_matrix_le_tupleBound]))
    fun S x _ n ↦ ⟨(CommMonoid.torsion ℂ).prod_mem fun _ _ ↦ (edgeChar ..).isOfFinOrder
    (Units.isUnit _).isOfFinOrder, fun e a b ↦ (n e a b).imp' ((t x e.1).1 * · * (t x e.2)⁻¹.1)
    fun L h ↦ by simp [tupleAction, ← L.mul_assoc, h]⟩⟩, fun r Ξ φ ↦ ?_⟩⟩
  · simp [LinearMap.pi, ← sum_fn, ← Pi.smul_def, -smul_eq_mul]
    rw [mul_sum, ← (piCongrRight fun p ↦ toPerm (g (p.1, 0, p.2))).sum_comp, eq_comm]
    congr with x
    set y := piCongrRight _ x
    have E z i (h : i ≤ D.m) : (t' y _)⁻¹ * (g _ * t' x _) ∈ nodeLevel ϑ (z, 0, i) := by
      obtain rfl | h := h.eq_or_lt <;> simp [t', ← QuotientGroup.eq, y, ← Quotient.mk_smul_out, *]
    erw [← mul_assoc, ← edgeCharProd_mul, ← mul_inv_cancel_left (t y) (g * _), edgeCharProd_mul,
      mul_assoc, ← (q ϑ).2]
    delta tupleAction; simp
    rintro ⟨⟩ ⟨⟩ _ <;> simp [t, *, ← map_inv, ← map_mul, Subgroup.mem_bot.1 (E false ..)]
  simp +unfoldPartialApp [-diagonalPeriodForm, LinearMap.pi, gridPathMap, ← fun x ↦
    @diagonalPeriodForm_tupleAction _ D ϑ (t x) (by simp [t, t', m_eq_two_mul_varrho_add_two])
    (by simp [t]), tupleAction, mul_left_comm _ (levelIndex ..)]
  erw [e, (Φ ϑ).map_smul, (Φ ϑ).map_smul]
  simp [prod_prod_type, prod_range, K]
  simp [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, levelIndex_eq_untwisted]; ac_rfl
