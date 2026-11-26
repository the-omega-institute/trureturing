import OmegaMath.NumberTheory.GRH.New.RealPlace.Size
import OmegaMath.NumberTheory.GRH.Lib.DiscreteSeries.Bruhat.BigCell
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Set-up for this proof: general results applied to the objects of this proof.

Part of: Tower method: pairings of kernels bounded floor by floor (see New.RealPlace.LocalTheorem).

This file: Invariant measure as a tower of big cells; definitions of level, gauge, weights,
pairing kernels.

Letters: H_l is `Shape.Form.GT`, Q_l is `Shape.Form.unitriGroup`, 𝒩_{<l} is
`Shape.Form.unipotentBelow`, η_l is `Place.heisenbergMeasure`, w_p is `weylElem`, f is the frame
(e₁, …, e_ϱ, z); the module md, the character ψ and the Plancherel constant c are fields of
`Place`. -/

noncomputable section


open Matrix MeasureTheory Measure FI ENNReal Fintype Place TraceOne Function Filter
variable {A} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A] (ι)
  [Fintype ι] {𝔰 : Shape} (T : 𝔰.Form A) (m) [IsHermUnit T.splitGram] {l i j}

/-- A level: a basis of V_ϱ, measures θ on H_ϱ and μH on H_{ϱ+1}, a hermitian unit g, an open
ball 𝔅 in V, a compact box Bx, measurable positions Cm. -/
structure Level extends HyperbolicBasis ι T m where
  (θ measureH : Measure T.G) (g : Aˣ) (𝔅 : Set (𝔰.BesselIndex → A))
  (boxSet positions : Set T.G) [sFinite_theta : SFinite θ] [sFinite_measureH :
    SFinite measureH] [neZero_measureH : NeZero measureH]
  theta_spec : (∀ᵐ x ∂θ, x ∈ GT 𝔰.ϱ) ∧ θ.map (orbitPoint 𝔰.top) =
    toHyperbolicBasis.floorQuadric 𝔰.top
  measureH_spec : (∀ᵐ x ∂measureH, x ∈ besselH) ∧ (∀ s ∈ besselH, measureH ∗ₘ dirac s = measureH) ∧
    ∀ g, measureH {h | ∃ u ∈ besselU, u * (h * g) ∈ boxSet} ≤ 1
  star_g : star g.1 = g
  ball_spec : IsOpen 𝔅 ∧ 0 ∈ 𝔅 ∧ IsCompact (closure 𝔅)
  box_spec : IsCompact boxSet ∧ MeasurableSet positions

variable {ι T m} {ν ρ} [SFinite ν] [SFinite ρ] {s : T.G} {S : Subgroup T.G} {f Φ : T.G → ℝ≥0∞}
  (F : Level ι T m) (b : Fin 𝔰.n)

namespace Level

attribute [instance] sFinite_theta sFinite_measureH neZero_measureH

/-- The measure θ_l of floor l: the law of w_l(c)⁻¹ν under `Place.weylLaw` and η_l for l < ϱ; θ,
μH for l = ϱ, ϱ+1; the unit mass at 1 beyond. -/
def floorMeasure l := if l < 𝔰.ϱ then weylLaw l ∗ₘ heisenbergMeasure l else if l =
  𝔰.ϱ then F.θ else if l = 𝔰.n then F.measureH else dirac 1

instance : SFinite (F.floorMeasure l) := by fun_cases floorMeasure <;> infer_instance

/-- The convolution (η_{l+i−1}∗θ_{l+i−1}) ∗ ⋯ ∗ (η_l∗θ_l) of i factors; for l = 0 it is the
measure 𝗆_i. -/
abbrev stackMeasure := descConv fun a ↦ heisenbergMeasure a ∗ₘ F.floorMeasure a

/-- The measure 𝖬 = (η_{ϱ+1}∗θ_{ϱ+1}) ∗ ⋯ ∗ (η₀∗θ₀) on the unitary group, the product over all
floors. -/
abbrev groupMeasure := F.stackMeasure 0 (𝔰.ϱ + 2)

/-- The convolution θ_{[l,ϱ+1]} = θ_{ϱ+1} ∗ ⋯ ∗ θ_l of the measures of the floors from l
upwards; the unit mass at 1 if l > ϱ + 1. -/
@[simp] abbrev upperMeasure l := descConv F.floorMeasure l (𝔰.ϱ + 2 - l)

/-- The point g is near at j: the coset Q_j g meets the box Bx of the level. -/
def IsNear j g := ∃ ξ ∈ unitriGroup j, ξ * g ∈ F.boxSet

/-- The matrix whose columns are the vectors of the orthonormal part of the basis of V_ϱ, read
as vectors of V. -/
abbrev orthonormalPart : Matrix 𝔰.BesselIndex ι A :=
  fromRows 0 (F.basisMatrix.toCols₂.toCols₂.toCols₁.fromRows 0)

/-- The set of pairs (u, u') of vectors of V such that u and (u − u')/g lie in the ball 𝔅. -/
abbrev closePairs := {u : _ × _ | u.1 ∈ F.𝔅 ∧ F.g⁻¹.1 • (u.1 - u.2) ∈ F.𝔅}

/-- The set 𝔤_a(x, xy) of values h(e_a, w), for w orthogonal to the e_b, b < a, with (x⁻¹w,
(xy)⁻¹w) in `Level.closePairs`. -/
def floorValues a (x y : T.G) := (· (eStar a)) ''
  {w | (x⁻¹.1.1 *ᵥ w, (x * y)⁻¹.1 *ᵥ w) ∈ F.closePairs ∧ ∀ b < a, w (eStar b) = 0}

/-- The exponent s = |ι| − (3(ϱ+1) + 1 + m), truncated at zero, of the volumes in the weight
`Level.floorWeight`. -/
abbrev volumeExponent (_ : Level ι T m) := card ι - (3 * 𝔰.n + 1 + m)

/-- The weight ℘_j(x, xy): the product, over the first j hyperbolic pairs a, of vol(𝔤_a(x,
xy))^s, with 𝔤_a = `Level.floorValues` and s = `Level.volumeExponent`. -/
def floorWeight j x y := ∏ a with a.1 < j, volume (F.floorValues a x y) ^ F.volumeExponent

/-- For a unit g, by default that of the level, the number md(g)^{d+1/2}, where d = |κ| − 1 +
2(ϱ − l) if l < ϱ and d = |κ| + 1 otherwise. -/
def floorModulus l (g := F.g) := P.md g ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (l + 1))) * P.md g ^ (2⁻¹ : ℝ)

variable {F}

/-- For b ≤ ϱ, the map σ ↦ σ⁻¹f_{b+1} is measurable and carries the floor measure θ_b to the
quadric measure δ^(b) on V_b. -/
lemma measurePreserving_orbitPoint : MeasurePreserving (orbitPoint b) (F.floorMeasure b)
  (F.floorQuadric b) := ⟨by fun_prop, b.lastCases
  (by simp [floorMeasure, theta_spec]) fun a ↦ ext_of_lintegral _ fun Φ _ ↦ by
  rw [← ((isDisintegration_quadricMeasure (IsHermitian.submatrix ‹IsHermUnit _›.1 (·.1))).map _
    ((gram_inclMatrix (![.inl a, eStar a] ⊕ᵥ @Subtype.val _ (a + 1 ≤ floorOf ·)) 1).trans _)).unique
    (F.isDisintegration_floorVolume _ (map_inclMatrix_eq_floorVolume _ _ _))]
  any_goals simp [gram_inclMatrix, ← ext_iff]; grind
  simp (disch := with_unfolding_all fun_prop) [floorMeasure, heisenbergMeasure, lintegral_map,
    mconv, lintegral_prod, lintegral_withDensity_eq_lintegral_mul, volume_eq_prod]
  rw [lintegral_congr_of_ae_imp ae_isUnit]; rintro _ ⟨t, rfl⟩
  rw [← lintegral_neg_eq_self, eq_comm, lintegral_eq_mul_lintegral_map (map_mulVec_volume _
    (t.1 • 1) _), lintegral_map] <;> first | fun_prop | simp [↓card_succ_le_floorOf, orbitPoint,
    heisenbergElem_inv, ← mulVec_mulVec, -mulVec_single]
  congr! 3; rw [lintegral_sub_left_eq_self (Φ <| heisenbergElem a ⟨_, ·⟩ |>.1.1 *ᵥ _)]
  congr!; simp [↓heisenbergElem_mulVec, flatChart, inclMatrix_val_mulVec, -inverse_star_unit,
    floorWeyl, weylOn, level, ← Pi.single_apply, col_apply', ↓splitGram_col, ← gram_inclMatrix]
  simp [funext_iff, inclMatrix, mulVec_apply_eq_sum, ← mulVec_smul, star_mulVec_dotProduct]
  grind [invOf_mul_self, Matrix.mul_assoc]⟩

/-- For b ≤ ϱ and s in H_b, the map σ ↦ sσ⁻¹f_{b+1} is measurable and carries the floor measure
θ_b to the quadric measure δ^(b). -/
lemma measurePreserving_mulVec_orbitPoint (hs : s ∈ GT b) : MeasurePreserving (s *ᵥ orbitPoint b ·)
  (F.floorMeasure b) (F.floorQuadric b) := .comp ⟨by fun_prop,
  ((F.isDisintegration_floorVolume b rfl).map s.2 s.1.4).unique (F.isDisintegration_floorVolume b
  ((measurePreserving_floor_block_mulVec hs).of_semiconj (hfm := ⟨by fun_prop, rfl⟩)
  (inclMatrix_mulVec_floor_block b.is_le hs) (by fun_prop)).2)⟩ (measurePreserving_orbitPoint b)

lemma ae_floorMeasure_mem : ∀ᵐ x ∂F.floorMeasure l, x ∈ GT l := by
  fun_cases floorMeasure <;> simp [theta_spec, measureH_spec,
    ae_mem_mconv _ (eventually_and.1 ae_mem_floorUnipotent).1 measurableSet_floorGroup,
    ae_map_iff measurable_floorWeyl.fun_inv.aemeasurable, measurableSet_floorGroup, *]

@[congr] lemma lintegral_floorMeasure_congr {μ} (e : F.floorMeasure l = μ) (h : ∀ σ ∈ GT l, f σ =
  Φ σ) : lintegral (F.floorMeasure l) f = lintegral μ Φ :=
  e ▸ lintegral_congr_of_ae_imp ae_floorMeasure_mem h

@[simp] lemma floorMeasure_top : F.floorMeasure 𝔰.n = F.measureH := by simp [floorMeasure]

lemma upperMeasure_eq_succ_mconv : F.upperMeasure l = F.upperMeasure (l + 1) ∗ₘ F.floorMeasure
  l := by grind [descConv.eq_def, floorMeasure, mconv_dirac_one]

lemma descConv_floorMeasure_succ (h : l < 𝔰.ϱ) : descConv F.floorMeasure l (i + 1) = (weylLaw l ∗ₘ
  descConv F.floorMeasure (l + 1) i) ∗ₘ heisenbergMeasure l := by rw [descConv, floorMeasure,
  ite_eq_left h, ← mconv_assoc, mconv_comm_of_ae ((ae_descConv_mem ae_floorMeasure_mem).mono fun s k
  ↦ by simp (disch := first | fun_prop | lia) [dirac_mconv, mconv_dirac, Measure.map_map,
  comp_def, floorWeyl, (commute_weylOn _ k).inv_left.eq])]

/-- For j ≤ ϱ and measurable Φ ≥ 0, ∫ Φ(w_q⁻¹w_p x) dθ(x) = ∏_{a=1}^{j}
md(p_a/q_a)^{|κ|+2(ϱ−a+1)} ∫ Φ dθ, where θ = θ_{ϱ+1} ∗ ⋯ ∗ θ₀ and w_p, w_q have length j. -/
lemma lintegral_weylRatio_mul {p q} : j ≤ 𝔰.ϱ → Measurable Φ → ∫⁻ x, Φ (weylRatio j p q *
  x) ∂F.upperMeasure 0 = (∏ a ∈ .range j, md (p a / q a).1 ^ (𝔰.k + 2 * (𝔰.ϱ - a))) * ∫⁻ x,
  Φ x ∂F.upperMeasure 0 := j.rec (by simp [weylRatio]) fun j ih hj _ ↦ by
  rw [Finset.prod_range_succ_comm, mul_assoc, ← ih, upperMeasure, (by lia : _ - 0 =
    j + (𝔰.ϱ - j + 2)), descConv_add, descConv_floorMeasure_succ, mconv_assoc, mconv_assoc]
  repeat rw [lintegral_mconv, lintegral_map, lintegral_withDensity_eq_lintegral_mul]
  rw [lintegral_eq_mul_lintegral_map (map_mul_volume (p j / q j)), lintegral_map,
    ← lintegral_const_mul, ← lintegral_const_mul, lintegral_congr_of_ae_imp ae_isUnit]
  all_goals first | fun_prop | lia | simp [mul_pow, ← mul_assoc]
  congr! 5; grind [=_ pow_succ']; ext
  simp [coe_weylRatio, floorWeyl, weylOn, division_def, Ring.mul_inverse_rev]
  grind [Units.inv_mul, =_ star_mul, oppositeIndex_spec]

/-- Let the subgroup S contain H_l, and let f ≥ 0 be measurable and left invariant under Q_{l+1}
∩ S. Then ∫ f(xs) dθ_l(x) = ∫ f dθ_l for every s in Q_l ∩ S. -/
lemma lintegral_floorMeasure_mul_right (hS : GT l ≤ S) (hi : (unitriGroup (l + 1) ⊓ S).FixesLeft f)
  (hs : s ∈ unitriGroup l ⊓ S) (hf : Measurable f := by fun_prop) : ∫⁻ x,
  f (x * s) ∂F.floorMeasure l = ∫⁻ x, f x ∂F.floorMeasure l := by
  obtain ⟨γ, a, ν, n, rfl⟩ := exists_floorGroup_mul_unipotentBelow hs.1
  rw [lintegral_floorMeasure_congr rfl fun x k ↦
    .trans (by group) (hi _ ⟨unipotentBelow_le_unitriGroup (conj_mem_unipotentBelow (mul_mem k a)
    n), by simp_all [mul_assoc x γ, mul_mem, hS k, hS a]⟩ (x * γ))]
  obtain h | _ | _ := lt_or_ge l 𝔰.n
  have ⟨A, m, e⟩ := exists_factor_orbitPoint ⟨l, h⟩ hf (hi · ∘ by gcongr)
  simpa +contextual [mul_mem, orbitPoint, *, -mulVec_single,
    ← (measurePreserving_orbitPoint ..).lintegral_comp] using
    (measurePreserving_mulVec_orbitPoint ⟨l, h⟩ (inv_mem a)).lintegral_comp m
  repeat simp_all [← lintegral_mconv_dirac, measureH_spec, floorGroup_eq_bot]

lemma ae_stackMeasure_mem : ∀ᵐ x ∂F.stackMeasure l i, x ∈ GT l :=
  ae_descConv_mem (ae_mem_mconv (eventually_and.1 ae_mem_floorUnipotent).1 ae_floorMeasure_mem)

/-- If l + i = ϱ + 2, the convolution (η_{ϱ+1}∗θ_{ϱ+1}) ∗ ⋯ ∗ (η_l∗θ_l) of i factors is
invariant under right translation by every s in H_l. -/
lemma stackMeasure_mconv_dirac (h : l + i = 𝔰.ϱ + 2) (hs : s ∈ GT l) :
  F.stackMeasure l i ∗ₘ dirac s = F.stackMeasure l i := by
  induction i generalizing l s; simp_all [floorGroup_eq_bot]; apply ext_of_lintegral; intros
  rw [eq_comm, stackMeasure, descConv, ← mconv_assoc, lintegral_mconv_symm,
    ← lintegral_floorMeasure_mul_right le_rfl _ ⟨mem_unitriGroup_of_mem_floorGroup hs, hs⟩,
    mconv_assoc, lintegral_mconv_symm, lintegral_mconv_dirac] <;> try fun_prop
  simp_rw [← lintegral_mconv_dirac]
  grind [_=_ mconv_assoc, dirac_mconv_heisenbergMeasure_comm, heisenbergMeasure_mconv_dirac,
    exists_floorGroup_mul_floorUnipotent, =_ dirac_mconv_dirac]

instance isMulRightInvariant_groupMeasure : F.groupMeasure.IsMulRightInvariant :=
  ⟨by simp [← mconv_dirac, stackMeasure_mconv_dirac]⟩

/-- The measure 𝗆_j = (η_{j−1}∗θ_{j−1}) ∗ ⋯ ∗ (η₀∗θ₀) equals η_{<j} ∗ θ_{[0,j−1]}, where
θ_{[0,j−1]} = θ_{j−1} ∗ ⋯ ∗ θ₀. -/
lemma stackMeasure_zero_eq : F.stackMeasure 0 j =
  ascConv heisenbergMeasure j ∗ₘ descConv F.floorMeasure 0 j := j.rec (by simp! [descConv])
  (by grind [descConv_succ, ascConv_heisenbergMeasure_succ, _=_ mconv_assoc,
  mconv_comm_of_ae (F.ae_floorMeasure_mem.mono ascConv_heisenbergMeasure_dirac_comm)])

/-- For all l and i, the convolution (η_{l+i−1}∗θ_{l+i−1}) ∗ ⋯ ∗ (η_l∗θ_l) is not the zero
measure. -/
lemma stackMeasure_ne_zero : F.stackMeasure l i ≠ 0 := measure_univ_pos.1 (by
  induction i generalizing l <;> simp [descConv, mconv_apply_eq_lintegral, *]
  grind [floorMeasure, mconv_zero, heisenbergMeasure, dirac_ne_zero, F.neZero_measureH.1,
    fun e ↦ by simpa (disch := fun_prop) [NeZero.ne]
    using congr($((F.measurePreserving_orbitPoint ⟨l, e⟩).2) = 0)])

variable [F.groupMeasure.IsHaarMeasure]

/-- Let 𝖬 = ρ ∗ ν be a Haar measure, with ρ carried by the subgroup S, right S-invariant and
commuting with the unit mass at s. Then ∫ Φ(sg) dν(g) = ∫ Φ dν for measurable left
S-invariant Φ ≥ 0. -/
lemma lintegral_mul_left_eq_of_factor (e : F.groupMeasure = ρ ∗ₘ ν) (a : ∀ᵐ y ∂ρ, y ∈ S) (r :
  ∀ s ∈ S, ρ ∗ₘ dirac s = ρ) (c : dirac s ∗ₘ ρ = ρ ∗ₘ dirac s) (m : Measurable Φ) (i :
  S.FixesLeft Φ) : ∫⁻ g, Φ (s * g) ∂ν = lintegral ν Φ := by
  have ⟨f, f0, _, f1⟩ := exists_pos_lintegral_lt_of_sigmaFinite F.groupMeasure top_ne_zero
  have E ν [SFinite ν] (e : F.groupMeasure = ρ ∗ₘ ν) : ∫⁻ x,
    Φ x / (∫⁻ y, f (y * x) ∂ρ) * f x ∂F.groupMeasure = lintegral ν Φ := by
    rw [e, lintegral_mconv_symm] at f1 ⊢
    rw [lintegral_congr_of_ae_imp (ae_lt_top _ f1.ne)]; intro g k
    rw [lintegral_congr_of_ae_imp a, lintegral_const_mul,
      ENNReal.div_mul_cancel (stackMeasure_ne_zero ∘ e.trans ∘ by
      simp +contextual (disch := fun_prop) [EventuallyEq, (f0 _).ne']) k.ne]
    repeat first | fun_prop | simp_all [← mul_assoc, i _, ← lintegral_mconv_dirac (f <| · * g)]
  rw [← lintegral_dirac_mconv]
  grind [_=_ mconv_assoc, dirac_mconv, map_mul_left_eq_self F.groupMeasure]

/-- Let 𝖬 be a Haar measure, j ≤ ϱ+2, and w_p the Weyl element of length j. For measurable left
H_j-invariant Φ ≥ 0, ∫ Φ(w_p⁻¹g) d𝗆_j(g) = ∫ Φ(g) d𝗆_j(g). -/
lemma lintegral_stackMeasure_mul_left p (hΦ : Measurable Φ) (hi : (GT j).FixesLeft Φ) (hj : j ≤
  𝔰.ϱ + 2 := by lia) : ∫⁻ g, Φ ((weylElem j p)⁻¹ * g) ∂F.stackMeasure 0 j = ∫⁻ g,
  Φ g ∂F.stackMeasure 0 j := by apply (lintegral_mul_left_eq_of_factor (Nat.add_sub_of_le hj ▸
  descConv_add ..) ae_stackMeasure_mem _ (mconv_comm_of_ae (ae_stackMeasure_mem.mono
  _)).symm) <;> simp_all [stackMeasure_mconv_dirac, commute_weylElem, Commute.eq]

variable (F) (j : ℕ) (k : T.G → T.G → ℂ) (w x g y : T.G) (K : ℝ≥0∞)

/-- For every g, the integral of c(σg) against θ_j, over the σ with σg near at j+1, is at most
K. -/
def FloorMassLe (c : _ → _) := ∀ g, ∫⁻ σ in {σ | F.IsNear (j + 1) (σ * g)},
  c (σ * g) ∂F.floorMeasure j ≤ K

/-- The averaged kernel k_j(g, y) = ∫ k(σg, σy) dθ_{[j,ϱ+1]}(σ), where θ_{[j,ϱ+1]} = θ_{ϱ+1} ∗ ⋯
∗ θ_j. -/
def upperPairing := ∫ x, k (x * g) (x * y) ∂F.upperMeasure j

/-- A measurable kernel k twisted by w commuting with H_j: its averages k_l (`Level.upperPairing`)
converge boundedly, satisfy k_{l+1}(nx, n'y) = ψ((fw(wn'w⁻¹) − fw(n))/g) k_{l+1}(x, y) on
𝒩_{<l}, fw being `simpleRootSum`, and vanish unless x is near at l. -/
structure IsPairingKernel where
  measurable : Measurable ↿k
  law {l n n'} : n ∈ unipotentBelow l → n' ∈ unipotentBelow l → ∀ g y,
    F.upperPairing (l + 1) k (n * g) (n' * y) =
    ψ (F.g⁻¹.1 * (simpleRootSum (w * n' * w⁻¹) - simpleRootSum n)) * F.upperPairing (l + 1) k g y
  conj_eq_self : ∀ s ∈ GT j, w * s * w⁻¹ = s
  exists_lintegral_le l : ∃ c < ∞, ∀ g y, ∫⁻ x, ‖k (x * g) (x * y)‖ₑ ∂F.upperMeasure l ≤ c
  isNear_of_upperPairing_ne_zero : ∀ {l g y}, F.upperPairing l k g y ≠ 0 → F.IsNear l g

/-- The function z ↦ 1/℘_j(z, zx), the inverse weight (`Level.floorWeight`) of the pair (z, zx), on
the points z near at j, and 0 elsewhere. -/
def invWeight := {z | F.IsNear j z}.indicator fun z ↦ (F.floorWeight j z x)⁻¹

/-- The integral ∫ |k_{j+1}(σg, σy)| dθ_j(σ), with k_{j+1} the averaged kernel
`Level.upperPairing`. -/
def pivotModulus := ∫⁻ σ, ‖F.upperPairing (j + 1) k (σ * g) (σ * y)‖ₑ ∂F.floorMeasure j

/-- The weighted square 𝖠_j(g) = ℘_j(g, gx)·|k_{j+1}(g, gx)|², with the weight `Level.floorWeight`
of the pair (g, gx) and the averaged kernel `Level.upperPairing`. -/
abbrev weightedSquare := F.floorWeight j g x * ‖F.upperPairing (j + 1) k g (g * x)‖ₑ ^ 2

/-- The function 𝖻_j(g) = ∫ (𝖠_j + 𝖻_{j+1})(σg) dθ_j(σ) for j ≤ ϱ, and 0 for j > ϱ, where 𝖠_j is
`Level.weightedSquare` at the position x. -/
def weightedSquareSum x j g := if j < 𝔰.n then ∫⁻ σ,
  F.weightedSquare j k x (σ * g) + weightedSquareSum x (j + 1) (σ * g) ∂F.floorMeasure j else 0

/-- The integral 𝖹_j(x) = ∫ 𝖻_j dθ_{[0,j−1]} of `Level.weightedSquareSum` at the position x, where
θ_{[0,j−1]} = θ_{j−1} ∗ ⋯ ∗ θ₀. -/
def selfNorm := ∫⁻ g, F.weightedSquareSum k x j g ∂descConv F.floorMeasure 0 j

end Level

/-- A gauge of exponent s: a size with compact B_j giving the level's data size 1, and a finite
Λ ≥ 2 whose powers bound moduli, volumes, cone masses and integrals of φ^s, where s =
`Level.volumeExponent` and φ is the majorant of inverse volumes in the field `com`. -/
structure Gauge extends Size T where
  Λ : ℝ≥0∞
  isCompact_ofSize j : IsCompact (ofSize j)
  two_le_and_pairs_le : 2 ≤ Λ ∧ m ≤ 9 * 𝔰.n
  one_le_c_and_ne_top : 1 ≤ c A ∧ Λ ≠ ∞
  data_mem_ofSize : ↑F.g ∈ ofSize 1 ∧ toSize.HasMatSize 1 F.basisMatrix ∧
    τ * skewUnit⁻¹.1 ∈ ofSize 1
  hasMatSize_box ⦃x⦄ : x ∈ F.boxSet → toSize.HasMatSize 1 x.1.1
  hasVecSize_ball : F.𝔅 ⊆ Size.vecsOfSize 1
  md_le j (u : Aˣ) : ↑u ∈ ofSize j → P.md u ≤ Λ ^ j
  volume_le j : volume (ofSize j) ≤ Λ ^ (j + 1)
  fib σ [Fintype σ] j : m ≤ card σ → card σ ≤ m + 𝔰.ϱ → quadricMeasure
    (hyperbolicGram σ (0 : Matrix _ Empty A)) 0 (Size.vecsOfSize j) ≤ Λ ^ (99 * 𝔰.n * (j + 1))
  com : ∀ x ∈ F.boxSet, ∀ y ∈ F.positions, ∀ v : Matrix (Fin 𝔰.ϱ) _ A, let W := {w | v *ᵥ w = 0 ∧
               (x⁻¹.1.1 *ᵥ F.orthonormalPart *ᵥ w, (x * y)⁻¹.1.1 *ᵥ F.orthonormalPart *ᵥ w) ∈
      F.closePairs}; ∃ φ, Measurable φ ∧ (∀ u, (volume ((star u ⬝ᵥ ·) '' W))⁻¹ ≤ φ u ∧
      volume {c : A | ∀ w ∈ W, ∃ z ∈ F.closePairs, ∃ z' ∈ F.closePairs, star (c • u) ⬝ᵥ w =
      F.g⁻¹ * (star z.1 ⬝ᵥ T.splitGram *ᵥ z'.1 - star z.2 ⬝ᵥ T.splitGram *ᵥ z'.2)} ≤
      φ u) ∧ ∀ j, ∫⁻ u in toSize.vecsOfSize j, φ u ^ F.volumeExponent ≤ Λ ^ (99 * 𝔰.n * (j + 1))

@[simp] lemma Gauge.one_le_Lambda (Γ : Gauge F) : 1 ≤ Γ.Λ :=
  one_le_two.trans Γ.two_le_and_pairs_le.1

/-- The set of positions x in Cm such that (x − 1)/g has size 1, g the unit of the level. -/
def Gauge.positionsOfSize (Γ : Gauge F) :=
  {x ∈ F.positions | Γ.HasMatSize 1 (F.g⁻¹.1 • (x.1.1 - 1))}
