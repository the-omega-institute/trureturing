/- GID: D5/S3/Zeros/GRH/New/Exchange/CrudeRows
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/CrudeRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.CrudeRows. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/CrudeRows.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Exchange.RowsReached
import D5.S3.Zeros.GRH.New.Exchange.GridFirstColumns
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Crude rows, with integral twisted lifts and bounded conjugates. Forms of level g on the
indefinite U(Y_0) are spanned by forms whose untwisted chain of
lifts has all conjugates explicitly bounded, and whose twisted chains are integral at primes prime
to the conductor after one scalar per twist that costs little height at the chosen twists.
Rationality or integrality of theta lifts via seesaw identities and periods along U(n+1)⊃U(n) is
known. Related work: Harris, Cohomological automorphic forms on unitary groups I, 1999; Prasanna,
Integrality of a ratio of Petersson norms, 2006; Grobner–Harris–Lin, Factorization of periods, 2025.

This file: The main result `Data.crude_rows`. Pairings of twisted chains of all rows are multiples
of the end period. -/

open Fintype Function Matrix MeasureTheory Real Space Submodule

variable {P : Parameters} (D : Data P)

/-- There are tidy data Φ ϑ of order 4m on `Data.path` 0, and g, α, a surjection r:
`Data.gridLevelForms` m → `Data.principalForms` Y₀ free of ϑ, with i·∫Ξ·lift(rφ) =
α·`Data.gridPeriod` Φ (ϑ, Ξ, φ) g; i = [K₀ : `Data.levelY` ϑ m], lift composes the m maps
`Data.liftY` ϑ. -/
lemma Data.exists_isTidy_integral_eq_gridPeriod : ∃ Φ, (∀ ϑ, IsTidy (4 * D.m) (D.path 0) (Φ ϑ)) ∧
  ∃ g α, ∃ r : D.gridLevelForms D.m →ₗ[ℂ] _, r.range = ⊤ ∧ ∀ (ϑ : D.MFoldTwist) Ξ φ,
  stdLevelIndex (D.levelY ϑ D.m) * ∫ x, Ξ x * D.liftChainY ϑ _ (r φ)
  x ∂(spaceY ..).quotMeasure = α * gridPeriod Φ (ϑ, Ξ, φ) zero_le g := by
  obtain ⟨⟨g, S⟩, ι⟩ := D.eq_zero_of_orthogonal_gridLevelForms, D.gridLevelForms_eq_map_iotaPlus
  choose C Λ q K using D.exists_isTidy_diagonalPeriodForm_eq
  choose r H using D.exists_restrict_bordered g
  use Λ, q, g, C, r ∘ₗ (iotaPlus ..).restrict (ι.ge ⟨·, ·, rfl⟩), orthogonal_eq_bot_iff.1
    (bot_unique fun y hy ↦ Subtype.ext (Subtype.ext (S _ y.2 (ι ▸ Set.forall_mem_image.2 fun φ
    m ↦ by simpa [periodPairing] using! (H _ 1 _ (levelSpace_anti (levelY_le_chosenLevel ..)
    y.2)).symm.trans (inner_eq_zero_symm.1 (hy _ ⟨⟨φ, m⟩, rfl⟩)))))), fun ϑ Ξ φ ↦ K .. ▸ ?_
  obtain ⟨Z, Y⟩ := (H · ϑ (conjForm (isConjKernelPair_gridKernel (by simp) true).2 (iotaPlus ϑ _ 0
    Ξ)) (mem_levelSpace_formRep_iff.2 fun k a g ↦ congr(star ($(((D.iotaPlus_adjoint_weightedChain
    false ϑ D.nat_le_of_hasLogBound 0).1 one_ne_zero).1 _ _ ((LevelPlaces.ker_reductionK₀_eq _).ge
    (mem_levelOf.1 a).2)) g)))), (D.iotaPlus_adjoint_weightedChain _ ϑ .refl · |>.2 Ξ)
  simp +unfoldPartialApp [liftY, liftChainY, petersson, periodPairing, iotaPlus.eq_1 _ _ D.m,
    ← LevelPlaces.card_GL_levelModulus, -Subtype.forall] at *
  erw [Y, Z]; rfl

/-- For some d(ϑ) costing k squares, tidy data of order n on path i yield tidy data of order n +
k on path j; if the new periods are constant multiples of T, the old are of T/d. -/
def Data.HasRoute {i j} (h : i ≤ D.m) (h' : j ≤ D.m) k := ∃ d : _ → ℂˣ, D.CostsSquares k (d ·) ∧ ∀ n
  Λ, (∀ ϑ, IsTidy n (D.path i) (Λ ϑ)) → ∃ Φ, (∀ ϑ, IsTidy (n + k) (D.path j) (Φ ϑ)) ∧ ∀ T : _ → ℂ,
  (∀ g, ∃ β, ∀ x, gridPeriod Φ x h' g = β * T x) → ∀ g, ∃ β, ∀ x, gridPeriod Λ x h g =
  β * (T x / d x.1)

/-- For j < m there is a `Data.HasRoute` of cost 4j + 2 from path j to path j + 1: tidy data of
order n give tidy data of order n + 4j + 2, and if the new periods are multiples of T, the
old are multiples of T/d. -/
lemma Data.hasRoute_succ {j} (h : j < D.m) : D.HasRoute (j := j + 1) h.le h (4 * j + 2) := by
  obtain ⟨⟨t, o⟩, ⟨ι, ν, s⟩, H, κ₀, σ, c₃, g₃, Q⟩ := D.t_odd, gridSpace_subdiag j,
    exists_modKernel_flip_line (gridSpace ..) (-(-1) ^ j), exists_squareLaw_grid false h h
  rw [neg_neg, ← mul_neg_one (_ ^ j), ← pow_succ] at H
  generalize flipPoly (E := D.E) _ _ = τ at H
  choose κ₁ c₁ g₁ H₁ using (descent_past_gridPathMap h · .refl); let N := D.GridIndex false j.succ j
  choose ψ c hc H using fun ϑ ↦
    H (gridModulus ϑ) (gridChar ϑ false j N) (gridChar ϑ true j N) (Modulus.flipScalar _ ^ j)
  use c₁ false * c₁ true * c₃ * c⁻¹,
    (((g₁ _).mul (g₁ _) .refl).mul g₃ .refl).mul (.of_norm_sq_eq_mul_card_zpow _ 1
    (card N) (by simpa [field, eq_comm] using hc)) (by omega), fun n Λ hΛ ↦ ?_
  choose Φ₁ q₁ e₁ using (H₁ _ · _ _ _ (by simp [gridPath, legEdges]) (hΛ _))
  choose Φ₂ q₂ e₂ using (H₁ _ · _ _ _ (by simp [gridPath, legEdges]) (q₁ _))
  simp [↓Finset.insert_union] at q₂
  let u := D.gridDiagEquiv
  choose Φ₀ q₀ e₀ using (q₂ · |>.exists_square_move (_, _, _) ι.symm (u _) (u _) (ψ _) (Q _) (R :=
    (_, _, _)) (by simp [IsAdmissibleFamily, update, h.ne']; clear * -; bound)
    (by simp [gridPath, legEdges]; clear * - h; grind))
  use Φ₀, by simpa +arith [path, gridPath, Finset.range_add_one] using q₀, fun T X g ↦ ?_
  choose _ _ _ _ _ _ E using @IsTidy.isShortSum _ D; let e := (G.reindex (E := D.E) _ ν).symm
  have : Continuous e := G.continuous_reindex _ (by simp [← ν, comp_def])
  have t x := by simpa [e, ← s] using (gridSpace ..).height_reindex _ ν (e x)
  refine (seesaw_periods _ (c := fun x ↦ T x / (c₃ / c) x.1) (T := gridSpace ..) (E <|
    q₂ ·.1) (isEdgeFamily_grid (·.1) true rfl) (isEdgeFamily_grid _ false rfl) fun P _ ↦ mul_le.2 ?_
    (mem_rename_range_mul (.map id (.map ι.symm (u _ ∘ .inl))) (.map id (.map ι.symm (u _ ∘ .inr)))
    (by simp [reindex_equiv (u _)]) P)).imp' (κ₁ false * κ₁ true * ·) fun β b x ↦
    ((e₁ _ _ (fun S ↦ diagonalPeriodForm _ _ g _) ?_).trans congr(_ * $((e₂ _ _ (fun S ↦
    (diagonalPeriodForm _ h.le g).flip _) ?_).trans congr(_ * $(b x))))).trans (by simp [field])
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  let K 𝔪 a z Ψ : ModerateWeight (gridSpace ..) (gridSpace ..) := ⟨⟨fun x ↦
    z * modKernel (gridSpace ..) (signedSpace _ fun _ ↦ (-1) ^ j.succ) a WeilData.upsilonU1 𝔪 Ψ
    (τ B) (e x) (1, 𝔪.flipScalar ^ j * 𝔪.flipScalar), by fun_prop [modKernel]⟩, ⟨e, ‹_›⟩, ⟨_, _, (by
    simp; grw [modKernel, pairTheta, ((pairThetaKer ..).isModerate ..).choose_spec.choose_spec, t ·,
      mul_assoc])⟩, 1, by simp [t, e]⟩
  have Z 𝔪 a z ψ x r G (F y : GridForm ..) : periodPairing G (K 𝔪 a z (matrixFourier ψ (Pi.single
    x 1))) r F y = z * ∑ k, ψ (k * x).trace * periodPairing G (K 𝔪 a 1 (Pi.single k 1)) r F y := by
    simp [periodPairing, ← integral_const_mul, ← integral_finsetSum,
      (integrable_moderate_mul_forms G ..).const_mul]
    simp [K, modKernel, pairTheta, modDatum_eq_sum _ _ (matrixFourier _ _), matrixFourier,
      Finset.sum_mul, Finset.mul_sum]; ac_rfl
  refine' subset_span ⟨A, _, _, fun r ↦ (seesaw_periods _ (E <| q₀ ·.1) (isEdgeFamily_grid _ true
    rfl) (isEdgeFamily_grid _ false rfl) fun _ _ ↦ subset_span ⟨_, _, _, X, fun _ _ _ _ ↦ _⟩).imp'
    (κ₀ * ·) fun β b o ↦ (congrArg _ (funext fun S ↦ Z ..)).trans ((map_smul _ (c o.1).1 _).trans
    (congr(_ * $((e₀ _ (fun S k ↦ (gridPathMap S _ j _ (levelIndex .. • o.2.1),
    periodPairing _ (K _ (gridChar o.1 true j N) 1 (Pi.single k 1)) r (gridPathMap S _ j
    _ o.2.2))) _).trans congr(_ * $(b o)))).trans (by simp [field]))), fun _ _ _ _ ↦ _⟩
  on_goal 4 => simp [K]; erw [← H, eq_comm, mul_comm, ← modKernel_sum_left,
    ← modKernel_reindex (u _) (D.gridDiagEquiv_spec h.le) _ ν, ← gridSpace_diag h.le, ← s]; congr 1
  on_goal 2 => simp [K]; erw [mul_comm, ← modKernel_sum_right, ← modKernel_reindex _ ν
    (u _) (D.gridDiagEquiv_spec h), ← gridSpace_diag h, ← s]; congr! -closePost 1
  any_goals exact (by simp +contextual [gridPathMap_congr · ·])
  all_goals clear * - o e u; simp [gridChar, card_gridIndex, mul_assoc, ← pow_succ, *, e,
    funext_iff, ← ext_iff, reindex_equiv ι.symm, reindex_equiv (u _), Prod.map_comp_map] <;> grind

/-- For j ≤ m there is a `Data.HasRoute` of cost 2j² from path 0 to path j: tidy data of order
n give tidy data of order n + 2j², and if the new periods are multiples of T, the old are
multiples of T/d. -/
lemma Data.gridPeriod_climb {j} (h : j ≤ D.m) : D.HasRoute zero_le h (2 * j * j) := by
  induction' j with j i
  · use 1, .one, fun _ ↦ (⟨·, ·, by simp⟩)
  obtain ⟨⟨c, g, X⟩, d, g', H⟩ := i (by lia), D.hasRoute_succ h
  use d * c, g'.mul g (by lia), (X · · · |>.elim fun Φ ⟨q, X⟩ ↦ (H _ Φ q).imp fun _ ↦
    .imp (by grind) (by simpa [div_div] using X _ <| · · ·))

seal HCParam.dsKernel

/-- Some integer 0 < N ≤ exp(x⁹⁹b²) makes N·`endPeriod Λ y` integral at every p prime to N(Q), for
tidy Λ on `Data.path` m and p-integral forms y as in `Data.FixedByEndLevels`. -/
lemma Data.exists_mul_endPeriod_mem_embValRing : ∃ N ≠ (0 : ℕ), N ≤ exp (D.x ^ 99 * D.b ^ 2) ∧
  ∀ {ϑ n} {Λ : GridDatum ϑ} {y p} [Fact p.Prime] [PadicPlace p], IsTidy n (D.path D.m) Λ →
  FixedByEndLevels ϑ y → p.Coprime ϑ.levelNorm → (∀ z g, weylGauge _
  (endDetExp z 0) g ((D.endToAlgForm z (y z)).1 g) ≤ 1) → N * endPeriod Λ y ∈ embValRing :=
  D.endBranching.2.1.elim fun L ⟨B, C, _⟩ ↦ by
  choose a b c using boxes_endWeightData_le
  use (∏ τ, (D.gProd ^ D.b₁ * D.N₁) ^ (D.m * (L τ).natAbs)) * (?ν ^ D.m) ^ 2, ?_, le_exp_of_log_le
    ?_, fun h hy q k ↦ (embValRing.toAddSubgroup.comap (.mulLeft _)).nsmul_subset .rfl
    (endPeriod_mem h hy (fun z j g v ↦ weylGauge _ (D.endDetExp z j) g (((?ν : ℂ) • ·)^[j] v) ≤ 1)
    ιₚ (fun _ _ _ j g h v ↦ .trans (by
    simpa [endKernel] using P.mem_raises_of_dvd (endDatum ..)
      (P.smul_vacuumDatum_mem_standardData norm_mul_gProd_pow_mem_modulus (by
    simp [ite_mem]) q) embValRing.one_mem (by grw [card_prod, b, a, a]; use 1; exacts
              [j.le, j, j]) g h ((_ : ℂ) • v))) k fun {g _ _} a b ↦ ?_).choose_spec.2
  iterate 2 simp [log_prod, log_mul, NeZero.ne, Finset.prod_eq_zero_iff, -Nat.cast_natAbs]
  grw [C, b, c] <;> simp; simpa using D.le_of_hasLogBound
  erw [Nat.cast_mul, mul_assoc, Nat.cast_pow, sq, ← smul_eq_mul (_ * _), mul_smul, ← map_smul,
    ← D.endPairing.map_smul₂, map_mul, ιₚ.map_dotProduct, Nat.cast_pow]
  simp only [map_natCast, comp_def, ιₚ.map_mulVec, smul_iterate, mulVecLin_apply, weylGauge,
    ← map_inv, Matrix.map_map, map_intCast, endBlockPoint,
    pi_norm_le_iff_of_nonneg one_pos.le] at a b ⊢
  rw [← (Units.inv_mul_eq_iff_eq_mul _).2 (B _ _ _ g⁻¹ ..), ← mul_assoc, Nat.cast_prod,
    ← Finset.prod_inv_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine NormedField.valuation.integer.mul_mem (prod_mem fun τ _ ↦ ?_) (sum_mem fun _ _ ↦
    mul_mem (a _) (sum_mem fun _ _ ↦ mul_mem (by simp) (b _)))
  obtain ⟨u, n, e | e⟩ := mul_mem (((gridModulus ‹_›).generator_spec.2.2 _).1
    ((Modulus.reduction_eq_zero_iff _).2 (Ideal.mem_map_of_mem _ norm_mul_gProd_pow_mem_modulus)))
    (mul_mem (star_mem_Ô (mul_mem (Modulus.generator_spec _).1
    P.N₁_mul_α_mem)) P.inv_α_mem), (L τ).eq_nat_or_neg <;> [skip; apply star_mem_Ô at u] <;>
    use (norm_adeleExtension_le_one ((ιₚ.comp _).comp _) (pow_mem u (D.m * n))).trans_eq'
    (by simp [Modulus.flipScalar, e, scalarFin, coe_divStar, WeilData.α, ← inv_pow,
    adeleExtension_star, q.norm_natCast_eq_one, -Nat.cast_prod]; ring)

/-- For the trivial twist, let Λ be tidy of order 4m + 2m² on `Data.path` m, y a pair of
forms as in `Data.FixedByEndLevels`, σ an automorphism of ℂ. If the σ-conjugate values have squared
norms at most B, B′, then |σ(`Data.endPeriod`(Λ, y))| ≤ exp(x²⁰⁰b²)√B√B′. -/
lemma Data.endPeriod_le {Λ : GridDatum 1} {y} (h :
  IsTidy (4 * D.m + 2 * D.m * D.m) (D.path D.m) Λ) (hy : FixedByEndLevels 1 y)
  (σ : ℂ ≃+* ℂ) {B : _ → ℝ} (k : ∀ z g, weylNormSq (σ ∘ (D.endToAlgForm z (y z)).1 g) ≤ B z) :
  ‖σ (endPeriod Λ y)‖ ≤ exp (D.x ^ 200 * D.b ^ 2) * √(B false) * √(B true) := by
  choose a b _ using boxes_endWeightData_le
  let G := (D.x ^ 99 * D.b ^ 2).exp
  have hn z j h : _ ≤ G := (D.card_stdClasses_le_exp_mul_log (K := endLevel 1 z j) (1 * _) (a z h)
    (by with_unfolding_all exact
    Modulus.principalLevel_le_levelOfSubgroup norm_mul_gProd_pow_mem_modulus)).trans
    (by simpa [G] using D.le_of_hasLogBound)
  choose _ q r using endPeriod_mem h hy (fun z j _ v ↦ √(weylNormSq (σ ∘ v)) ≤ G ^ j * √(B z))
    σ.toRingHom (M := 1) (fun x z j o g h v u ↦ have k := ((D.endWeightData z).2.2.1 j).1
    ((P.norm_jet_le_of_isAdmissibleComb
      (P.isAdmissibleComb_vacuumDatum 1 (by simp [apply_ite, ite_le_one])) ..).2 1 k v).trans (by
    rcases D.hasLogUpper_of_le (a z o), D.hasLogUpper_of_le (a z o.le)
    simp_rw [Finset.sum_range, ← sum_prod_type']
    grw [pow_succ' G, mul_assoc G, le_abs_self (log (_ / _)), le_exp_log (_ * 1), ← exp_add,
      (Finset.single_le_sum (by simp) (by simp)).trans
      (k.1.sum_diagramWeight_eq_boxes.trans_le (b z o))]
    gcongr; simpa [G, card_𝔪, prod_q_chosenPlace, twist_one_spec] using D.le_of_hasLogBound))
    (by simp [sqrt_le_sqrt, k]) fun u v ↦ ((D.endBranching.2.1.choose_spec.2.2 _
    (b _ le_rfl) ..).trans (by grw [u, v])).trans_eq' (by simp [entrywise])
  let ⟨v, u, s⟩ := Set.mem_nsmul_iff_sum.1 r
  grw [← s, map_sum, norm_sum_le_of_le _ (by simpa [-univ_bool] using u), Fin.sum_const]
  simp [-Nat.card_eq_fintype_card, ← mul_assoc, mul_right_comm _ √(B false)]
  grw [hn, hn, q, ← le_exp_of_log_le]
  simpa [log_mul, G, NeZero.ne, card_𝔪, prod_q_chosenPlace, twist_one_spec] using
    D.le_of_hasLogBound
  repeat grind

/-- Some nowhere zero c(ϑ) costs 2m² squares (`Data.CostsSquares`), and the forms of level K(g) on
Y₀ are spanned by the y with c(ϑ)/c(1)·ι_ϑ y integral above every l prime to the norms in Q(ϑ) and
all conjugates of values of ι₁y of squared norm ≤ exp(x₁²b²).

Crude rows: integral twisted lifts and bounded conjugates. -/
lemma Data.crude_rows : ∃ c : _ → ℂˣ, D.CostsSquares (2 * D.m * D.m) (c ·) ∧ span ℂ {y |
    (∀ ϑ l [Fact l.Prime] ι, l.Coprime ϑ.levelNorm →
  (c ϑ / c 1 : ℂ) • D.iotaAtLevel ϑ y ∈ LevelPlaces.LevelForm.integralForms (l := l) ι) ∧
  ∀ (σ : ℂ ≃+* ℂ) g, weylNormSq (σ ∘ (D.ι .one y).1 g) ≤ exp (D.x₁ ^ 2 * D.b ^ 2)} = ⊤ := by
  choose Λ q g α r R J using D.exists_isTidy_integral_eq_gridPeriod; choose N n C B using
    D.exists_mul_endPeriod_mem_embValRing
  choose c hc H using D.gridPeriod_climb le_rfl; choose Φ hΦ H using H _ Λ q
  choose A L l m o using
    exists_dual_pairing_of_isHCParam D.isHCParam_Y ((D.endWeightData _).2.2.2 0 bot_le)
  choose β H using H _ (D.gridPeriod_eq_endPeriod Φ) g; use c, hc, eq_top_mono ?_ R
  simp_rw [H] at J; set β := α * β
  choose t f using show Associated β (β / β) by by_cases β = 0 <;> simp [*]
  choose a b _ using boxes_endWeightData_le
  let e := (D.gridSpace 0 ..).algFormEquiv ((D.endWeightData true).2.2.2 0 bot_le)
    (principalLevel _ D.gridLevelGen)
  let ξ ϑ x v : levelSpace (algFormRep (D.endWeightData false).1 (endDetExp false 0))
    (levelY ϑ D.m) := deltaForm _ _ 1 x v
  let Ξ ϑ x v := (D.endToAlgForm false).symm (ξ ϑ x v).1
  have h' ϑ x v : D.endToAlgForm _ (Ξ ϑ x v) = _ := (endToAlgForm ..).4 _
  erw [r.range_eq_map, ← e.range, e.range_eq_map, ← span_isShort_eq_top (B :=
    (D.x ^ 99 * D.b ^ 2).exp) (classAut_eq_bot_of_le_chosenLevel (principalLevel_le_chosenLevel
    piGBar_dvd_gridLevelGen) (a _ zero_le)) P.cycloConductor_mem_different (by grw [b, a] <;> simp)
    (by grw [shortBasisConst, a _ zero_le]; exact le_exp_of_log_le D.le_of_hasLogBound), map_span,
    e.image_eq_preimage_symm, map_span_le]
  have E ϑ x v (φ : D.gridLevelForms _) : FixedByEndLevels ϑ (·.rec (Ξ ϑ x v) φ.1) := Bool.rec
    (h' .. ▸ levelSpace_anti (Subgroup.map_mono fun k b ↦ funext fun i ↦ by simpa using! (congrArg
    (·.1.map (modulusResidue _ (places_levelModulus.ge ⟨i, rfl⟩))) b)) (ξ ..).2)
    (levelSpace_anti (endLevel_le_principalLevel ..) (e.symm φ).2)
  have δ (η : ℤ) ϑ x v φ : v ⬝ᵥ A.map (↑) *ᵥ (((c ϑ).1 / c 1) • D.ι ϑ ((t.1 * c 1 * η * N / card
    (WeylIndex (D.Y D.m) D.columnsY)) • r φ)).1 x =
    η * (β / β * (N * endPeriod (Φ ϑ) (·.rec (Ξ ϑ x v) φ.1))) := by
    obtain ⟨p, q⟩ := J ϑ (Ξ ϑ x v) φ, ((D.iotaAtLevel ϑ (r φ)).algFormRep_eq_self_of_mem (k := ·))
    erw [← ofAlgForm_toAlgForm D.isHCParam_Y (liftChainY _ _ _),
      integral_mul_eq_classIntegral D.isHCParam_Y (D.levelY ϑ _) (isAutomorphic_algFormCoeff _) _
      (l _ _), classIntegral_eq_classSum, classSum_deltaForm fun _ ↦ .mk' (· ⬝ᵥ _) (by simp)] at p
    simpa [← f, n, field, -card_pi, mul_comm (c ϑ).1, mul_assoc] using! congr(η * N * $p)
    intros; rw [levelSpace_smoothFormRep_apply (χ := 1) (by simpa)]; simpa using! L ..
    intro _ h g; simpa using! congr($((ξ ..).2 ⟨_, h⟩).1 g ⬝ᵥ _ *ᵥ $(q _ h).1 g)
  refine fun φ k ↦ (smul_mem_iff _ ?_).1 (subset_span ⟨fun ϑ p _ _ q ↦
    weylGauge_le_one_of_integralAbove _ fun x _ i ↦ congr($(mul_left_cancel₀ (by simp)
    (congr($(m.choose_spec _) i).symm.trans (δ ..))) ∈ embValRing).mpr (mul_mem
    (by simp [div_self_le_one]) (B (hΦ ϑ) (E ϑ x _ φ) q (Bool.rec (fun y ↦ h'
    .. ▸ (weylGauge_deltaForm_le (by simp)).trans <| by simp [IsUltrametricDist.norm_intCast_le_one,
    weylGauge_le_one_iff, *]) (by simpa using! k.1 p ·)))), fun σ x ↦ (o _).elim fun w ⟨u, v⟩ ↦
    u ▸ ?_⟩)
  simp [n, -card_pi]
  have s := D.endPeriod_le (hΦ 1) (E 1 x (σ.symm ∘ w) φ) σ (B := (ite · (D.x ^ 99 * D.b ^ 2).exp
    (weylNormSq w))) (Bool.rec (fun _ ↦ h' .. ▸ (weylNormSq_deltaForm_le (by simp) ..).trans
    (by simp [D.classAut_eq_bot_of_le_chosenLevel (levelY_le_chosenLevel ..) (a false zero_le),
    comp_def])) (k.2 σ))
  have e := congr(‖$((PolyRep.coe_weylNormSq w).trans ((v w).symm.trans (.trans
    (by simp [dotProduct, mulVec]; rfl) congr(σ $(δ _ 1 _ (σ.symm ∘ w) _)))))‖).le
  simp [abs_of_nonneg, ← mul_assoc, le_of_lt] at e s
  nth_grw 1 [hookNumber_le (by exact b false zero_le), div_self_le_one, s, C, ← mul_assoc,
    ← mul_assoc, mul_right_comm] at e
  exact (sqrt_le_iff.1 (div_sqrt ▸ div_le_of_le_mul₀ (by simp) (by positivity) e)).2.trans
    (le_exp_of_log_le (by simpa [log_mul, ← exp_half, NeZero.ne] using D.le_of_hasLogBound))
