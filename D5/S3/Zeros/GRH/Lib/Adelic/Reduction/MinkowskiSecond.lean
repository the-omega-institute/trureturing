/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Reduction/MinkowskiSecond
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Reduction/MinkowskiSecond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Reduction.MinkowskiSecond. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Reduction/MinkowskiSecond.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.BaseChange.OrbitClassSum
import D5.S3.Zeros.GRH.Lib.Adelic.Witt.SpaceOperations
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: adelic points of unitary groups, levels and Haar measures. Here a hermitian space
comes with an adelic frame to a fixed diagonal form that is the identity at all finite places. Hence
all spaces of one signature share one adelic group. Source: V. Platonov, A. Rapinchuk, Algebraic
Groups and Number Theory, 1994, ch. 5.

Part of: Reduction theory: Mahler-Godement compactness, finite covolume, adelic Minkowski theorems
(known result; see Lib.Adelic.Reduction.Defs).

This file: A nonzero algebraic integer has a conjugate of modulus at least one. Adelic Blichfeldt
count and Minkowski's first theorem with multiplicity. First minimum, height, moderate growth, rapid
decay, dilations along an isotropic subspace. Adelic unitary group closed in matrices; definite
rational points discrete in finite part. Adelic Minkowski second theorem with crude constant;
counting field points in dilated boxes. -/

lemma eq_zero_of_norm_Φ {E} [Field E] [NumberField E] [PlaceEmbedding E] {x : E} (h : IsIntegral ℤ
  x) : (∀ v, ‖Φ v x‖ < 1) → x = 0 := Not.imp_symm (NumberField.one_le_house_of_isIntegral h) ∘ by
  simp_all [NumberField.house, pi_norm_lt_iff, ← NumberField.InfinitePlace.apply]

open Set ENNReal Fintype Matrix MeasureTheory Metric NumberField Measure Classical
variable {E : Type _} [Field E] [CMType E] {n : Type _} [Fintype n] (y : GL n (𝔸 E))

/-- For E CM, y ∈ GL_n(𝔸) and measurable S ⊂ 𝔸^n, |det y|·vol(S) is the integral over x in
𝔸^n/E^n, for the quotient measure, of #{ξ ∈ E^n : y⁻¹(ξ + x) ∈ S}. -/
lemma lintegral_encard_rat_points {S} (hS : MeasurableSet S) : .ofReal (ideleAbs y.det) * volume S =
    ∫⁻ x, {ξ | y⁻¹.1 *ᵥ (toAdele ∘ ξ + x) ∈ S}.encard ∂(ratVectors E n).qms := .trans (by simp)
  (((MeasurePreserving.comp ⟨by fun_prop, volume_map_mulVec_adele _⟩
  measurePreserving_addOrbitMeasure).measure_preimage (by aesop)).symm.trans (.trans (prod_apply (by
  measurability)) (lintegral_congr fun _ ↦ (count_apply .of_discrete).trans (mod_cast encard_congr
  (Equiv.ofInjective _ (@toAdele E ..).injective.comp_left).subtypeEquivOfSubtype.symm))))

/-- Minkowski's first theorem with multiplicity: for y in GL_n(𝔸), |det y| is at most (2
rd)^{fn} times the number of ξ in E^n with y⁻¹ξ integral at finite places and all entries of
absolute value below 1 at the f infinite places. -/
lemma minkowski_first : ENNReal.ofReal (ideleAbs y.det) ≤ .ofReal (((2 * rootDiscr E) ^ numInfPlaces
  E) ^ card n) * {ξ | ∀ i, (y⁻¹.1 *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E}.encard := by
  have := rootDiscr_pos E
  grw [← (lintegral_encard_rat_points y (.univ_pi fun _ ↦ ((@isOpen_ball _ _ 0 2⁻¹).prod
    isOpen_Ô).measurableSet)).trans_le (lintegral_le_const (.of_forall fun x ↦ ENat.toENNReal_mono
    (encard_le_encard_of_injOn (fun b h ↦ by simpa [mulVec_sub, ← two_mul] using (fun i
    ↦ sub_mem_sub (h i ⟨⟩) (epsilon_spec_aux ⟨0⟩ _ ⟨b, h⟩ i ⟨⟩))) sub_left_injective.injOn))),
    mul_left_comm, ofReal_le_of_le_toReal]
  simp (disch := bound) [volÔ_eq, volume_pi, volume_eq_prod, pi_ball, ← inv_pow, ← mul_pow]
  grind [Real.two_le_pi, one_le_pow₀]

lemma exists_ne_zero_inv_mulVec_mem (h :
  ((2 * rootDiscr E) ^ numInfPlaces E) ^ card n < ideleAbs y.det) :
  ∃ ξ, (∀ i, (y⁻¹.1 *ᵥ toAdele ∘ ξ) i ∈ ball 0 1 ×ˢ Ô E) ∧ ξ ≠ 0 := exists_ne_of_one_lt_encard
  (mod_cast one_lt_of_lt_mul_right (α := ℝ≥0∞) ((minkowski_first y).trans_lt' (by simpa))) 0

variable {n : Type _} [Fintype n] {E : Type _} [Field E] [CMType E]
  {s : n → ℤˣ} (V : Space E n s) (F : _ → ℂ)

/-- The group of pairs (g, c) in U(J) × Rˣ with gA = cA and wᴴJgv = wᴴJv for all square matrices
v, w with AᴴJv = AᴴJw = 0. -/
noncomputable def dilationGroup {R : Type*} [CommRing R] [StarRing R] {m : Type*} (A : Matrix n m R)
  {J} := Subgroup.ofDiv {g : U J × Rˣ | g.1.1.1 * A = g.2 • A ∧ ∀ v w : Matrix n n R, Aᴴ * (J *
  v) = 0 → Aᴴ * (J * w) = 0 → wᴴ * (J * (g.1.1.1 * v)) = wᴴ * (J * v)} ⟨1, by simp⟩ fun _ g k h ↦ by
    constructor <;> intros <;> [rw [← smul_left_cancel_iff k.2, ← Matrix.mul_smul, ← h.1];
      erw [mul_assoc, g.2, ← h.2]] <;> simp_all [↓← Matrix.mul_assoc, smul_smul,
      ← U.gram_invariant k.1 _ _⁻¹]

/-- For a space (J, x), the additive map sending y ∈ E^n to the archimedean components of x⁻¹y
in Euclidean space ℂ^{fn}; its norm is the length of y. -/
noncomputable def Space.archCoords := AddMonoidHom.mk' (G := EuclideanSpace ℂ (_ × n))
    (.toLp 2 fun p ↦ V.vecAtPoint · p.2 |>.1 p.1) (by aesop)

/-- The set of vectors y of the lattice of V (`Space.baseLattice`) whose length (`Space.archCoords`)
is at most r. -/
abbrev Space.latticeBall r := {y ∈ V.baseLattice | ‖V.archCoords y‖ ≤ r}

/-- The first minimum of the lattice of V, cut off at 1: the infimum of 1 and the lengths
(`Space.archCoords`) of the nonzero lattice vectors. -/
noncomputable def Space.firstMinimum :=
  sInf (insert 1 ((‖V.archCoords ·‖) '' {y ∈ V.baseLattice | y ≠ 0}))

/-- The height ht(g) = 1/λ(g), with λ(g) the first minimum of V moved by g, cut off at 1
(`Space.firstMinimum`). -/
noncomputable def Space.height g := (V.move g).firstMinimum⁻¹

/-- F on G has moderate growth: |F(g)| ≤ C·ht(g)^B for all g, for some real C and natural number
B. -/
def Space.IsModerate := ∃ C B, ∀ g, ‖F g‖ ≤ C * V.height g ^ B

/-- F on G has rapid decay: |F(g)|·ht(g)^B is bounded on G for every natural number B. -/
def Space.IsRapid := ∀ B, ∃ C, ∀ g, ‖F g‖ * V.height g ^ B ≤ C

variable {E : Type _} [Field E] [NumberField E] [NumberField.IsCMField E] {n : Type _} [Fintype n]
  {s : n → _}

/-- The map sending an element of the adelic unitary group G to its matrix over the adeles is a
closed embedding. -/
lemma G.isClosedEmbedding_mat : Topology.IsClosedEmbedding (mat : G E s → _) :=
  have e := U.isClosedEmbedding_mat (by simp)
  e.comp
    (toUnitary.1.3.isClosedEmbedding (.prodMk (continuous_pi (U.continuous_map <| continuous_apply
    · |>.fst')) (U.continuous_map continuous_snd)) (e.continuous_iff.2 continuous_mat))

lemma G.ext_mat {g g' : G E s} : g.mat = g'.mat → g = g' := (isClosedEmbedding_mat.1.2 ·)

lemma G.continuous_iff {X} [TopologicalSpace X] {f : X → G E s} :
    Continuous f ↔ Continuous (f · |>.mat) := isClosedEmbedding_mat.continuous_iff

instance {E : Type _} [Field E] [CMType E] (W : Space E n 1) : DiscreteTopology W.Γf :=
    continuous_subtype_val.discrete_of_tendsto_cofinite_cocompact (.mono_left (by
  simpa [← Filter.coprod_cocompact] using!
    W.ratEmbed.tendsto_coe_cofinite_of_isDiscrete W.ratEmbed_injective
    ⟨W.discreteTopology_Gamma⟩) Set.rangeFactorization_surjective.le_map_cofinite)

open Complex Int _root_.Matrix Finset Function
variable {E : Type _} [Field E] [CMType E] {n : Type _} [Fintype n] (x : n → ℤ)

variable {E : Type _} [Field E] [NumberField E] in
variable (E) in
/-- The idele of E that is 2 at all infinite places and 1 at the finite places. -/
noncomputable def twoAtInfinity : (𝔸 E)ˣ :=
  .map ⟨⟨(fun _ ↦ ·, 1), rfl⟩, by aesop⟩ (.mk0 2 (by simp))

attribute [local simp low] diagonal_apply mulVec_apply Prod.fst_prod Prod.fst_sum Prod.snd_prod
  Prod.snd_sum Units.smul_def dotProduct mul_assoc twoAtInfinity zpow_nonneg

attribute [local simp ←] map_inv map_zpow

lemma sum_norm_sq_mulVec_of_isometry {m} [Fintype m] {Q : Matrix m n ℂ} (h : Qᴴ * Q = 1) v :
    ∑ i, ‖(Q *ᵥ v) i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  simpa [← ofReal_inj, ← conj_mul', star_mulVec, h] using Q.dotProduct_mulVec (star (Q *ᵥ v)) v

lemma ideleAbs_det_mkAdelicGL a (b : GL n (𝔸f E)) : ideleAbs (mkAdelicGL (a, b)).det =
  (∏ w, ‖(a w).1.det‖ ^ 2) * finIdeleAbs b.det := by simp [finIdeleAbs, ideleAbs, det_apply]

/-- For an integer vector x, the diagonal adelic matrix whose i-th entry is 2^{x_i} at the
infinite places and 1 at the finite places. -/
noncomputable def dyadicDiag {E : Type _} [Field E] [NumberField E] {n : Type _} [Fintype n]
    (x : n → ℤ) := diagGL (twoAtInfinity E ^ x ·)

/-- The set of Y in GL_n(E) with y⁻¹ Y D⁻¹ in M, where D is diagonal with entries 2^{x_i} at
infinity and 1 at finite places. -/
def profileBases (M : Set _) x y := {Y : GL n E | y⁻¹ * Y.map toAdele * (dyadicDiag x)⁻¹ ∈ M}

lemma isCompact_closedBall_prod_integral (r := 1) :
    @IsCompact (𝔸 E) _ (closedBall 0 r ×ˢ Ô E) := (isCompact_closedBall ..).prod isCompact_Ô

lemma ideleAbs_det_dyadicDiag : @ideleAbs E _ _ (dyadicDiag x).det = (2 ^ (2 * numInfPlaces E)) ^
  ∑ i, x i := by simp [dyadicDiag, ideleAbs, ← zpow_sum_of_ne_zero]; group

lemma ideleAbs_det_dyadicDiag_natCast (x : n → ℕ) : @ideleAbs E _ _ (dyadicDiag (x ·)).det =
  ((2 ^ numInfPlaces E) ^ ∑ i, x i) ^ 2 := (ideleAbs_det_dyadicDiag _).trans (mod_cast by ring)

lemma dyadicDiag_inv_mem (x : n → ℕ) : (dyadicDiag (x ·))⁻¹.1 ∈ Set.matrix
  (closedBall 0 1 ×ˢ Ô E) := by simp [dyadicDiag, diagonal_mem_matrix_iff, Pi.pow_def]; bound

@[simp↓] lemma ideleAbs_det_map_toAdele (Y : GL n E) : ideleAbs (Y.map toAdele).det = 1 :=
  Y.map_det toAdele ▸ ideleAbs_toAdele _

/-- A form of Minkowski's second theorem: for y in GL_n(𝔸) there are a basis Y_j of E^n and
integers x_j with y⁻¹Y_j integral at finite places, of Euclidean length ≤ 2^{x_j} over all f
infinite places together, and |det y|_𝔸 · 4^{f∑x_j} ≤ (8fn·rd)^{fn}, rd the root
discriminant. -/
lemma minkowski_second (y : GL n _) : ∃ᵉ (Y) (x : n → ℤ), (det Y ≠ 0 ∧ ∀ j,
  let v := y⁻¹.1 *ᵥ toAdele ∘ Y j
  (∀ i, (v i).2 ∈ Ô E) ∧ ‖WithLp.toLp 2 fun p : _ × _ ↦ (v p.2).1 p.1‖ ≤ 2 ^ x j) ∧ ideleAbs y.det *
  (2 ^ (2 * numInfPlaces E)) ^ ∑ i, x i ≤
  (8 * (numInfPlaces E * card n) * NumberField.rootDiscr E) ^ (numInfPlaces E * card n) := by
  cases isEmpty_or_nonempty n; simp [univ_eq_empty, ideleAbs]; by_contra! H
  choose N o h using exists_forall_mul_mem_Ô (Prod.snd ∘ y.2.uncurry)
  obtain ⟨_, ⟨Y, x, hY, ⟨⟩⟩, hm⟩ :=
    @exists_least_of_bdd (∃ Y x, _ ∧ Finset.univ.sum x = ·) ⟨_, fun _ ⟨Y, x, h, e⟩ ↦
    e ▸ (le_zpow_iff_clog_le (by simp) (by simp [rootDiscr_pos, zero_lt_iff])).1 (@cast_pow .. ▸
    (div_le_iff₀' ideleAbs_pos).2 (H Y x h).le)⟩ ⟨_, Matrix.diagonal N, _, ⟨by simpa, fun j ↦
    ⟨by simpa [apply_ite, mul_comm] using! (h ⟨·, j⟩), self_le_zpow_clog _root_.one_lt_two _⟩⟩, rfl⟩
  let g := .map toAdele (.mk'' Yᵀ (by simp [*]))⁻¹ * y
  let A w := g.map (evalInf w); let B := g.map (.snd ..)
  choose b t u using fun w ↦
    exists_orthonormal_mul x ⟨_, (Units.mk0 (2 * √(numInfPlaces E * card n)) (by simp) • (A w)⁻¹).4⟩
  choose c hc _ using exists_ne_zero_inv_mulVec_mem (mkAdelicGL (b, B) * dyadicDiag x) (by
    contrapose! H; use Y, x, hY
    have e w := by simpa [field, (A _).det_ne_zero] using congr(‖$(u w).det‖).symm
    have : ideleAbs g.det = _ := ideleAbs_det_mkAdelicGL A B
    simp_all [g, ideleAbs_det_dyadicDiag, ideleAbs_det_mkAdelicGL]
    grw [H]; ring; norm_num [pow_mul', mul_comm])
  choose j hj hj' using c.support.exists_max_image x Subtype.finite (by simpa)
  refine (hm _ ⟨_, x - Pi.single j 1, ⟨(Y.det_updateRow_sum j c).trans_ne (by simp_all),
    (and_forall_ne j).1 ⟨?_, fun i k ↦ by simpa [k] using hY.2 i⟩⟩, rfl⟩).not_gt (by simp)
  simp [← mulVec_mulVec, dyadicDiag, -coe_units_inv, field, forall_and, pi_norm_lt_iff] at hc
  simpa [← vecMul_eq_sum, comp_def, RingHom.map_vecMul, mulVec_vecMul, zpow_sub₀, sum_prod_type,
    PiLp.norm_eq_of_L2, mul_pow, @mul_comm ℝ, field, ← mul_sum, -coe_units_inv, Real.sqrt_le_iff]
    using! (hc.symm.imp_right fun h ↦ sum_mono fun w ↦ (sum_norm_sq_mulVec_of_isometry (u w)
    ((b w).2 *ᵥ _)).trans_le (sum_le_card_nsmul _ _ ((2 ^ x j) ^ 2) fun l _ ↦ by
      gcongr; by_contra! k; have := by simpa using k.trans (h ..)
      simp +contextual [Finset.sum_eq_zero, or_iff_not_imp_right, not_lt.2,
        blockTriangular_inv_of_blockTriangular (t w) (this.trans_le' (hj' ..))] at k) :)

/-- For f : α → [0, ∞] and a finite index set n, the sum over all tuples x ∈ α^n of ∏_i f(x_i)
is at most (∑_a f(a))^|n|. -/
lemma tsum_prod_le_prod_tsum {α} (f : α → ℝ≥0∞) : ∑' x : n → α, ∏ i, f (x i) ≤ ∏ _ : n, tsum f :=
    tsum_le_of_sum_le' bot_le fun s ↦ by grw [(by grind : s ⊆ piFinset (s.image ∘ eval)),
    ← prod_univ_sum, ENNReal.sum_le_tsum]

lemma encard_le_of_dyadic_box {α B} (hB : IsCompact B) : ∃ C ≠ ∞, ∀ (x : n → ℤ) {S} (f : α → n → E),
  Set.InjOn f S → (∀ a ∈ S, (fun i ↦ (twoAtInfinity E ^ (-x i)).1 * f a i) ∈ B) → S.encard ≤
  C * .ofReal (((2 ^ numInfPlaces E) ^ ∑ i, (x i).toNat) ^ 2) := by
  choose _ hF _ a s using IsCovolOneLattice.exists_compact_cover (ratVectors E n)
  have hS := isCompact_univ_pi (fun _ ↦ isCompact_closedBall_prod_integral) |> fun p ↦
    (p.mul hB).add (p.mul hF)
  exists volume _, hS.measure_ne_top; introv u k
  grw [← ideleAbs_det_dyadicDiag_natCast, mul_comm, lintegral_encard_rat_points _ hS.measurableSet,
    ← iInf_le_lintegral]
  use le_iInf fun v ↦ mod_cast Set.encard_le_encard_of_injOn (fun ξ h ↦ ⟨_, ⟨(twoAtInfinity E ^
    (-x⁺ + x) · |>.1), ?_, _, k ξ h, rfl⟩, _, ⟨_, ?_, _, (a v).choose_spec ▸ s v, rfl⟩, by
    ext1; simp [dyadicDiag, -map_zpow, _root_.zpow_add]; ring!⟩)
    ((add_left_injective _).comp_injOn u) <;> simp [field, posPart]
