/- GID: D5/S3/Zeros/GRH/New/RealPlace/LocalTheorem
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/LocalTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.LocalTheorem. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/LocalTheorem.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.RealPlace.WeightPlancherel
import D5.S3.Zeros.GRH.New.Filling.BesselSystem
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Tower method, with pairings of kernels bounded floor by floor. In a tower of subgroups with
measures, at a complex place or a product of finite places, a pairing of two equivariant kernels on
one floor is an integral of pairings on the next, weighted Cauchy–Schwarz and Plancherel bound it by
L² norms, and one proof gives the frequency bounds at both kinds of place. Kloosterman integrals by
induction on rank, low-rank orbital bounds, Parseval and Schur weights are known. Related work:
Jacquet, Smooth transfer of Kloosterman integrals, 2003; Michel–Ramakrishnan–Yang, Bessel periods on
U(2,1)×U(1,1), 2023; Miao, Bessel functions and Kloosterman integrals on GL(n), 2024.

This file: Local theorem: weighted bounds for pairings of cut Bessel kernels, descent between
floors.

Letters as in New.RealPlace.LevelGauge; fl_l is `Level.floorModulus`, 𝖬 is `Level.groupMeasure`,
𝗆_j is `Level.stackMeasure` 0 j, Z is `Shape.Form.frameGram`, Λ is `Gauge.Λ`, a head is
`Size.IsHead`, a position is a point of `Level.positions`. -/

noncomputable section


open Matrix MeasureTheory Measure ENNReal Fintype ComplexConjugate InnerProductSpace Level Finset
  Function RCLike Place
attribute [-simp] Subtype.forall Subtype.exists inv_mul_cancel₀
variable {A} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A] {ι}
  [Fintype ι] {m} {𝔰 : Shape} (j : ℕ) {T : 𝔰.Form A} [IsHermUnit T.splitGram] {F :
  Level ι T m} (p q : ℕ → Aˣ)
  {ξ : Aˣ} {I : Type} [Fintype I] (W W' : T.G → EuclideanSpace ℂ I) (x : T.G) (Γ Γ' : Gauge F)

/-- For families of units p, q, the number κ_j = ∏_{a<j} md(p_a q_a)^{d_a/2} (a counted from 0),
where d_a = |κ| − 1 + 2(ϱ − a) for a < ϱ. -/
def Level.headDensity (_ : Level ι T m) :=
  ∏ a ∈ .range j, (P.md (p a * q a) ^ (2⁻¹ : ℝ)) ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)))

/-- The kernel (x, y) ↦ ⟨W(x), W'(dy)⟩ pairing W with the left translate of W' by d. -/
@[simp] abbrev translatePairing d x y := ⟪W x, W' (d * y)⟫_ℂ

/-- W is a Bessel function of frequency η: bounded, measurable, with W(ux) = ψ(η σ(u))W(x) for u
in 𝖴, σ the superdiagonal sum of the frame block. -/
structure Place.IsBessel (η : Aˣ) : Prop extends IsBoundedMeasurable W where
  law : ∀ u ∈ T.besselU, ∀ x, W (u * x) = ψ (η * simpleRootSum u) • W x

/-- W is a cut Bessel function for the level: Bessel of frequency 1/g, and zero at x unless ux
lies in the box for some u in 𝖴. -/
structure Level.IsCut : Prop extends P.IsBessel W F.g⁻¹ where
  exists_mul_mem_box : ∀ {x}, W x ≠ 0 → ∃ u ∈ T.besselU, u * x ∈ F.boxSet

/-- The number 𝖭(W, W') = ∬ |⟨W(x), W'(y)⟩|², both variables integrated against θ_{ϱ+1} ∗ ⋯ ∗
θ₀. -/
def Level.pairingNorm := ∫⁻ x, ∫⁻ y, ‖⟪W x, W' y⟫_ℂ‖ₑ ^ 2 ∂F.upperMeasure 0 ∂F.upperMeasure 0

/-- At g, the product k_j(g, gx)·conj(k'_j(w⁻¹g, w⁻¹gx)) of averaged kernels. -/
def Level.formIntegrandOne d w g := F.upperPairing j (translatePairing W W 1) g (g * x) * conj
  (F.upperPairing j (translatePairing W W d) (w⁻¹ * g) (w⁻¹ * g * x))

/-- The double integral ∬ ω(στ⁻¹) k_{j+1}(σg, σgx) conj(k'_{j+1}(τw_p⁻¹g, τw_p⁻¹gx)) dθ_j(τ)
dθ_j(σ), with k_{j+1}, k'_{j+1} the averages (`Level.upperPairing`) of ⟨Wy, Wy'⟩ and ⟨Wy,
W(w_q⁻¹w_p y')⟩. -/
def Level.formIntegrand (ω : _ → ℂ) g := ∫ σ, ∫ τ, ω (σ * τ⁻¹) * F.formIntegrandOne (j + 1) W x
  (weylRatio j p q) (σ * weylElem j p * τ⁻¹) (σ * g) ∂F.floorMeasure j ∂F.floorMeasure j

/-- The form 𝓘_j(p, q; ω): κ_j times the integral against 𝖬 × 𝗆_j of the double integral
`Level.formIntegrand` for the kernels ⟨Wy, Wy'⟩, ⟨Wy, W(w_q⁻¹w_p y')⟩ and w_p. -/
def Level.floorForm ω := (F.headDensity j p q).toReal * ∫ z,
  F.formIntegrand j p q W z.1 ω z.2 ∂F.groupMeasure.prod (F.stackMeasure 0 j)

/-- The number 𝖥_j(x; ω): at the position x, the integral against 𝗆_j of the modulus of the
double integral `Level.formIntegrand` that defines the form 𝓘_j(p, q; ω). -/
def Level.formModulus ω := ∫⁻ g, ‖F.formIntegrand j p q W x ω g‖ₑ ∂F.stackMeasure 0 j

/-- The majorant 𝓘_j⁺(x): the integral against 𝗆_j of the double integral with moduli inside, a
product of two `Level.pivotModulus` terms, for the kernels ⟨Wy, Wy'⟩, ⟨Wy, W'(w_q⁻¹w_p y')⟩ and
w_p. -/
def Level.formMajorant := ∫⁻ g, F.pivotModulus j (translatePairing W W 1) g (g * x) *
  F.pivotModulus j (translatePairing W W' (weylRatio j p q)) ((weylElem j p)⁻¹ * g)
  ((weylElem j p)⁻¹ * g * x) ∂F.stackMeasure 0 j

/-- The number 𝖣_j(x) = Λ^{3·10⁶(ϱ+1)³} ∏_{a<j} fl_a(p_{a+1}⁻¹)² 𝖹₀(x) 𝖹'_j(x), the 𝖹 being
`Level.selfNorm` for the kernels ⟨Wy, Wy'⟩ and ⟨Wy, W'(w_q⁻¹w_p y')⟩. -/
def Gauge.selfNormProduct := (∏ a ∈ .range j, F.floorModulus a (p a)⁻¹) ^ 2 * Γ.globalConst ^ 3 *
  F.selfNorm 0 (translatePairing W W 1) x * F.selfNorm j (translatePairing W W' (weylRatio j p q)) x

attribute [local simp] mul_assoc div_eq_mul_inv formIntegrand formIntegrandOne
  Fin.prod_univ_castSucc floorModulus floorForm lintegral_prod lintegral_mconv_symm
  ENNReal.inv_mul_cancel_left ENNReal.mul_inv_cancel prod_range coe_weylRatio weylRatio_inv
variable {j p q W W' x} (hk : F.IsCut W) (hk' : IsBessel W' F.g⁻¹) (hj : j ≤ 𝔰.ϱ) (hp :
  Γ.IsHead j p) (hx : x ∈ F.positions)

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermUnit T.splitGram] in
/-- For b ≤ ϱ, the diagonal entry h(f_{b+1}, x f_{b+1}) of Z(x) is unchanged when x is
multiplied on the left or on the right by an element t of Q_{b+1} ∩ H_b. -/
lemma frameGram_diag_mul {b : Fin 𝔰.n} (h : x ∈ unitriGroup (b + 1) ⊓ GT b) y :
    T.frameGram (x * y).1.1 b b = T.frameGram y b b ∧ T.frameGram (y * x).1.1 b b =
  T.frameGram y b b := have e := orbitPoint_eq_iff.1 ((mem_unitriGroup_succ_iff h.2).1
    h.1); by simpa [↓mulVec_mulVec] using! (And.intro (e ▸ U.form_mulVec_mulVec x _
    (y.1.1 *ᵥ Pi.single _ 1) :) congr((T.splitGram *ᵥ y *ᵥ $e) (𝔰.besselFrame b)))

/-- Let k satisfy `Level.IsPairingKernel`, x be a position. If every σ in H_l with k(σg, σgx) ≠ 0
has vol 𝔤_a(σg, σgx) ≤ ε for some l < a ≤ ϱ, then (∫|k_{l+1}(σg, σgx)| dθ_l)² ≤ ε^s
Λ^{10⁴(ϱ+1)(ϱ−l)} 𝖻_l(g)/℘_l(g, gx). -/
lemma Gauge.pivotModulus_sq_le_of_capped {k d ε l g} (hK : F.IsPairingKernel j k d) (hx :
  x ∈ F.positions) (hc : ∀ σ ∈ GT l, k (σ * g) (σ * (g * x)) ≠ 0 → ∃ a : Fin _, l ≤ a ∧ volume
  (F.floorValues a (σ * g) x) ≤ ε) : F.pivotModulus l k g (g * x) ^ 2 ≤ ε ^ F.volumeExponent *
  (Γ.Λ ^ (10 ^ 4 * 𝔰.n)) ^ (𝔰.ϱ - l) * (F.weightedSquareSum k x l g / F.floorWeight l g x) := by
  induction' e : _ - l with i ih generalizing l g
  rw [of_not_not (mt exists_ne_zero_of_pivotModulus (by grind))]; simp
  rw [weightedSquareSum, ite_eq_left (by lia), div_eq_mul_inv, ← lintegral_mul_const,
    pow_succ' (_ ^ _), mul_left_comm, mul_assoc, ← lintegral_const_mul] <;> try fun_prop
  lift l to Fin 𝔰.ϱ using
    (by lia); refine hK.pivotModulus_sq_le (Γ.floorMassLe_floorWeight_div l hx) fun σ s ↦ ?_
  by_cases e : volume (F.floorValues l (σ * g) x) ≤
    ε <;> [grw [← e, ← Γ.one_le_Lambda, ← le_self_add (a := F.weightedSquare ..)]; grw
    [hK.enorm_upperPairing_le, ← mul_assoc, ih (fun τ a n ↦ by grind [mul_mem (by grind : τ ∈ _) s,
    floorValues_mul (mem_unitriGroup_of_mem_floorGroup a)]) (by lia)]] <;>
    simp [floorWeight_succ, s, ENNReal.mul_inv, ENNReal.mul_inv_cancel_left] <;> ring_nf <;> simp

/-- Let 𝖬 be Haar and k satisfy `Level.IsPairingKernel` at j ≤ ϱ. The 𝖬-integral of 𝖹_j(x) over the
positions x with (x−1)/g of size 1 is at most (ϱ+1) ∏_{l<ϱ}(fl_l c^{|ι|} Λ^{4600(ϱ+1)})
∬|k|², for θ_{ϱ+1} ∗ ⋯ ∗ θ₀ in both variables. -/
lemma Gauge.lintegral_selfNorm_le [F.groupMeasure.IsHaarMeasure] {k d c} (hK :
  F.IsPairingKernel j k d) (hj : j ≤ 𝔰.ϱ) (e : (∏ l ∈
  .range 𝔰.ϱ, Γ.floorConst l) * ∫⁻ g, ∫⁻ y, ‖k g y‖ₑ ^ 2 ∂F.upperMeasure 0 ∂F.upperMeasure 0 =
  c) : ∫⁻ x in Γ.positionsOfSize, F.selfNorm j k x ∂F.groupMeasure ≤ 𝔰.n * c := by
  obtain ⟨hB, I⟩ := Γ.measurableSet_positionsOfSize, fun {l n} ↦ by simpa using @hK.law l 1 n
  let W l g y := ∫⁻ ν, Γ.positionsOfSize.indicator 1 (g⁻¹ * (ν * y)) ∂ascConv heisenbergMeasure l
  let Φ l g y := ∞ * W l g y ⊓ ‖F.upperPairing (l + 1) k g y‖ₑ ^ 2
  have V {l g y σ t} h : W l g y = W l (σ * g) (t * y) :=
    (lintegral_eq_of_dirac_mconv_eq (s := σ) (t := t) h).trans (by simp [W])
  apply le_add_self.trans (Nat.decreasingInduction' (P := fun l ↦ ∃ ρ, SFinite ρ ∧ l * c + ∫⁻ x in
    Γ.positionsOfSize, F.selfNorm l k x ∂F.groupMeasure ≤ 𝔰.n * c ∧ F.groupMeasure = ascConv
    heisenbergMeasure l ∗ₘ ρ ∧ (∏ a ∈ range l, if a < 𝔰.ϱ then Γ.floorConst a else 1) * ∫⁻ g, ∫⁻ y,
    Φ l g y ∂ρ ∂descConv F.floorMeasure 0 (l + 1) ≤ c) (fun l h _ ⟨ρ, _, z, e, i⟩ ↦ (fun a ↦ ⟨_,
    inferInstance, .trans ?_ z, a⟩) ⟨e ▸ mconv_assoc .., .trans ?_ i⟩) hj.step ⟨F.upperMeasure 0,
    inferInstance, by simp [selfNorm, weightedSquareSum], by simp [stackMeasure_zero_eq, ascConv],
    e ▸ by gcongr ?_ * ∫⁻ g, ∫⁻ y, ?_ ∂_ ∂_ <;> simp [Φ, upperPairing, descConv]⟩).choose_spec.2.1
  · simp [hK.selfNorm_eq_add_succ h.le_pred, weightedSquare, add_one_mul, add_assoc]
    grw [lintegral_add_left, ← add_le_add_left a.2, lintegral_lintegral_swap, ← lintegral_const_mul]
    gcongr with g
    grw [← lintegral_indicator hB, ← lintegral_mul_left_eq_self _ g⁻¹, a.1, lintegral_mconv_symm,
      ← lintegral_const_mul]
    any_goals fun_prop
    exact lintegral_mono fun y ↦ not_lt.1 fun n ↦ n.not_ge ((lintegral_le_of_ae_imp
      ae_ascConv_mem_unipotentBelow fun ν h ↦ by simp [I h, Set.indicator, ← ofReal_norm]).trans
      ((lintegral_mul_const _ (by fun_prop)).trans_le (mul_le_mul' ((Γ.lintegral_floorWeight_le
      (by lia) g y ((exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow n.ne_bot).elim
      (by simp; grind [→ IsPairingKernel.isNear_of_upperPairing_ne_zero, IsNear]))).trans
      (by gcongr; grind)) (le_min ((top_mul fun z ↦ (exists_ne_zero_of_ae ((lintegral_eq_zero_iff
      (by fun_prop)).1 z) n.ne_bot).elim (by simp_all)).ge.trans' le_top) le_rfl))))
  grw [prod_range_succ, mul_assoc, descConv_succ (l + 1), lintegral_mconv_symm,
    ← lintegral_const_mul (ite ..)]
  gcongr with g
  grw [← lintegral_floorMeasure_congr rfl fun σ a ↦ lintegral_mul_left_eq_of_factor e
    ae_ascConv_mem_unipotentBelow (by grind [ascConv_heisenbergMeasure_invariant])
    (ascConv_heisenbergMeasure_dirac_comm _ a) _ fun s o y ↦ by simp [Φ,
    @V (l + 1) _ y 1 s (by simp [ascConv_heisenbergMeasure_invariant o]), I o, ← ofReal_norm],
    lintegral_lintegral_swap, ← lintegral_const_mul, lintegral_mconv_symm, lintegral_mono fun y ↦
    if z : W (l + 1) g y = 0 then ((lintegral_mono fun n ↦ inf_le_left).trans_eq (by simpa (disch :=
    with_unfolding_all fun_prop) [W, ascConv] using z)).trans zero_le else ?_]
  any_goals fun_prop
  simp +contextual only [Φ, ← V (ascConv_heisenbergMeasure_dirac_comm _ _), top_mul z]; split
  grw [Γ.parseval_heisenbergMeasure_of_box ⟨l, ‹_›⟩ F.g⁻¹ F.g 0 1 (hK.mono (by lia)) g y
    (fun s c ↦ by simp [hK.3 _ (floorGroup_anti ‹_› c.1), simpleRootSum_eq_zero_of_mem_besselH])
    (fun n a H ↦ ⟨And.intro a (by simp at H; simpa using And.imp (exists_ne_zero_of_ae
    ae_ascConv_mem_unipotentBelow) hK.isNear_of_upperPairing_ne_zero H), by simp⟩) (by
    rintro _ ⟨u, ⟨_, h₁, e₀⟩, _, o, k⟩
    obtain ⟨t, ht, ν, hν, rfl⟩ :=
      exists_floorGroup_mul_unipotentBelow (unitriGroup_anti l.le_succ o)
    exact ⟨t, ⟨(mul_mem_cancel_right (unipotentBelow_le_unitriGroup hν)).1 o, ht⟩, _, by grind,
      Γ.hasMatSize_box k, fun n ⟨hn, ⟨μ, hμ, e⟩, _⟩ ↦ ⟨_, conj_mem_unipotentBelow ht
      (mul_mem (mul_mem hν h₁) (conj_mem_unipotentBelow (mul_mem u (inv_mem
      hn)).1 (inv_mem (mul_mem hν hμ)))), (conj_mul_inv_close_to_one k e₀ e (by group) · _)⟩⟩)]
  simp; ring_nf; rfl
  grw [heisenbergMeasure_eq_dirac_one (by lia), ← hK.pivotModulus_sq_le (u := 1)
    (by simp [FloorMassLe, IsNear, measureH_spec, (by lia : l = 𝔰.ϱ)]),
    ← hK.enorm_upperPairing_le]; simp

/-- The form is bounded by its modulus version: |𝓘_j(p, q; ω)| ≤ κ_j ∫ 𝖥_j(x; ω) d𝖬(x). -/
lemma Level.enorm_floorForm_le ω : ‖F.floorForm j p q W ω‖ₑ ≤ F.headDensity j p q * ∫⁻ x,
  F.formModulus j p q W x ω ∂F.groupMeasure := by
  grw [floorForm, enorm_mul, enorm_integral_le_lintegral_enorm, lintegral_prod_le, ← ofReal_norm]
  simp [formModulus]; grw [ofReal_toReal_le]

lemma Level.stackMeasure_top : F.stackMeasure 𝔰.ϱ 2 =
  F.measureH ∗ₘ F.floorMeasure 𝔰.ϱ := by simp [descConv]

lemma Gauge.isCompact_hasMatSize : IsCompact {y : T.G | Γ.HasMatSize j y.1.1} :=
  isClosedEmbedding_unitary_coe.isCompact_preimage (Γ.isCompact_ofSize _).matrix

include hk

lemma Level.IsCut.isNear_of_ne_zero (h : W x ≠ 0) : F.IsNear j x := (hk.2 h).imp fun _ ↦
  .imp_left mem_unitriGroup_of_mem_besselU

/-- For a cut Bessel function W and a weight ω of modulus at most 1, at every x the quantity
𝖥_j(x; ω) (`Level.formModulus`) is at most the majorant 𝓘_j⁺(x) (`Level.formMajorant`) taken with W'
= W. -/
lemma Level.IsCut.formModulus_le_formMajorant {ω} (h : ∀ x, ‖ω x‖ ≤ 1) : F.formModulus j p q W x ω ≤
  F.formMajorant j p q W W x := lintegral_mono fun _ ↦ by
  delta formIntegrand pivotModulus
  repeat grw [enorm_integral_le_lintegral_enorm]
  grw [(ofReal_norm _).ge, norm_mul_le, h,
    ← lintegral_mul_const _ (hk.1.1.rec (by fun_prop [upperPairing]))]
  simp [lintegral_const_mul']

include Γ

/-- Let W be a cut Bessel function, p a head of length ϱ for the gauge, and x in H_ϱ. If W(y) ≠
0 and W((w_p x)⁻¹y) ≠ 0, then the entries of y have size 60(ϱ+1)². -/
lemma Gauge.hasMatSize_of_ne_zero {y} (hp : Γ.IsHead 𝔰.ϱ p) (t : x ∈ GT 𝔰.ϱ) (h : W y ≠ 0) (n :
  W ((weylElem 𝔰.ϱ p * x)⁻¹ * y) ≠ 0) : Γ.HasMatSize (60 * 𝔰.n ^ 2) y.1.1 :=
  (hk.2 h).elim fun u ⟨hu, v⟩ ↦ (Size.hasMatSize_of_isHead Γ.hasMatSize_box .refl
  (IsNear.of_floorGroup_mul (by simpa using hk.isNear_of_ne_zero n) (inv_mem t))
  ⟨mem_unitriGroup_of_mem_besselU hu, v⟩ hp ((unipotentBelow_eq_besselU .refl).ge hu)).1

/-- For a Haar measure μ, a continuous cut Bessel function W, heads p, q of length ϱ and x in
H_ϱ, ⟨J_W(w_p x), J_W(w_q x)⟩ is the μ×μ-integral of ⟨Wy, Wy'⟩ times the conjugate of
⟨W((w_p x)⁻¹y), W((w_q x)⁻¹y')⟩. -/
lemma Gauge.inner_besselCorrelation {μ} [IsHaarMeasure μ] (hW : Continuous W) (hp : Γ.IsHead 𝔰.ϱ p)
  (hq : Γ.IsHead 𝔰.ϱ q) (t : x ∈ GT 𝔰.ϱ) : ⟪besselCorrelation μ W (weylElem 𝔰.ϱ p * x),
  besselCorrelation μ W (weylElem 𝔰.ϱ q * x)⟫_ℂ = ∫ z, ⟪W z.1, W z.2⟫_ℂ * conj ⟪W
  ((weylElem 𝔰.ϱ p * x)⁻¹ * z.1), W ((weylElem 𝔰.ϱ q * x)⁻¹ * z.2)⟫_ℂ ∂μ.prod μ := by
  simp_rw [PiLp.inner_apply, besselCorrelation, inner_apply', ← integral_conj, ← integral_prod_mul]
  rw [← integral_finsetSum _ fun i _ ↦ HasCompactSupport.integrable
    (.intro (Γ.isCompact_hasMatSize.prod Γ.isCompact_hasMatSize) fun y ↦ not_imp_comm.1 fun z ↦ by
    use Γ.hasMatSize_of_ne_zero hk hp t ?_ ?_,
      Γ.hasMatSize_of_ne_zero hk hq t ?_ ?_ <;> exact (z <| · ▸ by simp))]
  simp [sum_prod_type, Finset.sum_mul_sum, mul_left_comm]

/-- For W cut, W' Bessel of frequency 1/g and 𝗍 = w_q⁻¹w_p, the kernel (y, y') ↦ ⟨Wy, W'(𝗍y')⟩
satisfies `Level.IsPairingKernel` at floor j, with twisting element 𝗍. -/
lemma Gauge.isPairingKernel_translatePairing (hk' : P.IsBessel W' F.g⁻¹) j p q :
  F.IsPairingKernel j (translatePairing W W' (weylRatio j p q)) (weylRatio j p q) := by
  obtain ⟨⟨_, C, b⟩, _, _, b'⟩ := hk.1.1, hk'.1
  refine ⟨by fun_prop, @fun l u v a b g y ↦ .trans (integral_congr_ae
    ((ae_descConv_mem ae_floorMeasure_mem).mono fun σ c ↦ ?_)) (integral_const_mul ..),
    fun s a ↦ by simp [weylRatio, weylElem_mul_left_comm a], fun l ↦ ⟨_, ?_, fun g y ↦ by
    grw [← setLIntegral_eq_of_support_subset, (ofReal_norm _).ge, norm_inner_le_norm, b,
      le_abs_self C, b', setLIntegral_const,
      upperMeasure_isNear_le (Γ.floorMassLe_one · Γ.hasFibreBound_floorQuadric) l g, Γ.volume_le]
    exact fun _ _ ↦ hk.isNear_of_ne_zero (by aesop)⟩, Not.imp_symm fun n ↦ integral_eq_zero_of_ae
    ((ae_descConv_mem ae_floorMeasure_mem).mono fun _ a ↦ by simp [by_contra (n <|
    hk.isNear_of_ne_zero · |>.of_floorGroup_mul a)])⟩
  dsimp
  rw [(congrArg W (by simp)).trans (hk.law _ (unipotentBelow_le_besselU (conj_mem_unipotentBelow c
    (by grind : u ∈ _))) (σ * g)), (congrArg W' (by simp [weylRatio])).trans (hk'.law ((weylRatio j
    q p)⁻¹ * (σ * v * σ⁻¹) * _) (conj_mem_unitriangular (by simp) (unipotentBelow_le_besselU
    (conj_mem_unipotentBelow c (by grind)))) (weylRatio j p q * (σ * y)))]
  simp [mul_sub, ψ.map_sub_eq_div, ← inv_eq_conj, simpleRootSum,
    ← superdiag_conj_eq _ c, *, -besselFrame_castSucc, -mul_assoc]
  ring
  finiteness [Γ.one_le_c_and_ne_top.2]

/-- For a level F with a gauge and a cut Bessel function W, the function (x, y) ↦ ⟨W(x), W(y)⟩
is a kernel in the sense of `Level.IsPairingKernel` at floor j, with twisting element w = 1. -/
lemma Gauge.isPairingKernel_self j : F.IsPairingKernel j (translatePairing W
  W 1) 1 := by simpa [weylRatio] using Γ.isPairingKernel_translatePairing hk hk.1 j 1 1

/-- For a level with a gauge and W cut, k_j(g, gx)·conj(k'_j(w_p⁻¹g, w_p⁻¹gx)) equals, for every
g, the double integral `Level.formIntegrand` with weight 1; k_j, k'_j are the averages of ⟨Wy,
Wy'⟩ and ⟨Wy, W(w_q⁻¹w_p y')⟩. -/
lemma Level.formIntegrandOne_eq : F.formIntegrandOne j W x (weylRatio j p q) (weylElem j p) =
  F.formIntegrand j p q W x 1 := funext (by simp [← (Γ.isPairingKernel_self
  hk j).upperPairing_eq_integral_succ.2,
  ← (Γ.isPairingKernel_translatePairing hk hk.1 ..).upperPairing_eq_integral_succ.2, integral_conj])

/-- Descent, for a gauge, W cut, b ≤ ϱ, ∫𝓘_b⁺ d𝖬 finite, θ_b the law of v(c)⁻¹n under ρ(c)dc ×
ζ, ζ carried by Q_{b+1} ∩ H_b. If a.e. Ψ(c) = tκ_bρ(c) ψ(ηZ_{b+1,b+1}(v(c)))
∫`Level.formIntegrandOne` d(𝖬 × (ζ∗θ_b∗𝗆_b)) (floor b+1, w = w_p v(c)), then Ψ is integrable with
integral t·`Level.floorForm` at weight ψ(ηZ_{b+1,b+1}). -/
lemma Level.integral_succ_floor_eq (b : Fin 𝔰.n) {ζ} [SFinite ζ] {v : A → _} {ρ Ψ t} (η :
  A) (hm : ∫⁻ x, F.formMajorant b p q W W x ∂F.groupMeasure ≠ ∞) (z : ∀ᵐ n ∂ζ,
  n ∈ unitriGroup (b + 1) ⊓ GT b) (hρ : ∀ᵐ c, ρ c < ∞) (hc : F.floorMeasure b =
  (volume.withDensity ρ).map (fun c ↦ (v c)⁻¹) ∗ₘ ζ) (hΨ : ∀ᵐ c, Ψ c = t * (F.headDensity b p q * ρ
  c).toReal • (ψ (η * T.frameGram (v c).1.1 b b) * ∫ z, F.formIntegrandOne (b + 1) W z.1
  (weylRatio b p q) (weylElem b p * v c) z.2 ∂F.groupMeasure.prod ((ζ ∗ₘ F.floorMeasure b) ∗ₘ
  F.stackMeasure 0 b))) (mv : Measurable v := by fun_prop) (mρ : Measurable ρ := by fun_prop) :
  Integrable Ψ ∧ ∫ c, Ψ c = t * F.floorForm b p q W fun x ↦ P.ψ (η * T.frameGram x b b) := by
  let ψ (x : T.G) := P.ψ (η * T.frameGram x b b)
  obtain ⟨k, k', _⟩ := Γ.isPairingKernel_self hk b,
    Γ.isPairingKernel_translatePairing hk hk.1 b p q, (by fun_prop [frameGram] : Measurable ψ)
  have E : ProbabilityTheory.IdentDistrib (fun (z, c) ↦ ψ (v c) * F.formIntegrandOne (b + 1) W z.1
    (weylRatio b p q) (weylElem b p * v c) z.2) (fun (((x, g), σ), τ) ↦
    ψ (σ * τ⁻¹) * F.formIntegrandOne (b + 1) W x (weylRatio b p q) (σ * weylElem b p *
    τ⁻¹) (σ * g)) ((F.groupMeasure.prod ((ζ ∗ₘ F.floorMeasure b) ∗ₘ F.stackMeasure 0 b)).prod
    (volume.withDensity ρ)) (((F.groupMeasure.prod
    (F.stackMeasure 0 b)).prod (F.floorMeasure b)).prod (F.floorMeasure b)) :=
    ⟨by fun_prop [formIntegrandOne], by fun_prop [formIntegrandOne], ext_of_lintegral _ fun φ _ ↦ by
    simp (disch := with_unfolding_all fun_prop) [lintegral_map]
    congr! 5 with _ _ σ hσ
    rw [← lintegral_floorMeasure_mul_right le_rfl
      (fun s _ ↦ by simp [-mul_assoc, mul_assoc s, k'.upperPairing_invariant, ← mul_assoc σ, ψ,
      ↓frameGram_diag_mul, *]) ⟨mem_unitriGroup_of_mem_floorGroup hσ, hσ⟩, hc, lintegral_mconv_symm,
      lintegral_congr_of_ae_imp z fun _ ↦ ?_] <;> try rw [lintegral_map]
    any_goals fun_prop
    simp_all [weylElem_mul_left_comm, k.upperPairing_invariant, ψ, ↓frameGram_diag_mul]⟩
  have K : Integrable _ _ := ⟨E.2.aestronglyMeasurable, hm.lt_top.trans_le' (by
    grw [(enorm_mul ..).le, (ofReal_norm _).ge, (P.norm_psi _).le]
    simp (disch := with_unfolding_all fun_prop) [formMajorant, pivotModulus, lintegral_mul_const])⟩
  have J := E.integrable_iff.2 K
  simpa [↓integral_prod_symm _ J, ↓integral_prod, ↓K, integrable_congr hΨ, ↓K.integral_prod_left,
    integral_congr_ae hΨ, ψ, integral_withDensity_eq_integral_toReal_smul, *] using And.intro
    ((((integrable_withDensity_iff_integrable_smul' mρ hρ).1 J.integral_prod_right).const_mul
    _).const_mul t) (Or.inl (Or.inl E.integral_eq))

/-- Descent. For a level with a gauge, W cut, a < ϱ, η in A, t complex and ∫𝓘_a⁺ d𝖬 finite,
c ↦ ψ(ηc)·t·𝓘_{a+1}((p, c), (q, c); 1) is integrable, with integral t·𝓘_a(p, q; ψ(ηZ_{a+1,a+1}));
here 𝓘 is `Level.floorForm`.

Tower method: pairings of kernels bounded floor by floor. -/
lemma Gauge.integral_floorForm_succ (a : Fin _) t η (hm : ∫⁻ x,
  F.formMajorant a p q W W x ∂F.groupMeasure ≠ ∞) : let f c := ψ (η * c) *
    (t * F.floorForm (a + 1) (update p a (unitOrOne c)) (update q a (unitOrOne c)) W 1)
  Integrable f ∧ ∫ c, f c = t * F.floorForm a p q W (ψ <| η * T.frameGram ·.1.1 a.castSucc
    a.castSucc) := integral_succ_floor_eq Γ hk a.castSucc η hm (ae_mem_floorUnipotent.mono fun _ h ↦
  ⟨unipotentBelow_le_unitriGroup h.2, h.1⟩) (ae_isUnit.mono fun
    | _, ⟨c, rfl⟩ => by simp [Ne.lt_top]) (ite_eq_left a.2) (ae_isUnit.mono fun _ ⟨c,
  h⟩ ↦ by simp [← h, ↓← formIntegrandOne_eq Γ hk, weylRatio, weylElem_succ, (commute_weylElem _).eq,
  descConv_succ, frameGram_floorWeyl, headDensity, ← sq, LT.lt.ne, ← rpow_two, -rpow_ofNat, field])

variable [F.groupMeasure.IsHaarMeasure]
include hk' hj

/-- Let 𝖬 be Haar, W cut, W' Bessel, q a head of length j ≤ ϱ for Γ, 𝖭(W,W)𝖭(W,W') ≤ Θ², and
f² ≤ e²𝖣_j on a set S of positions with (x−1)/g of Γ'-size 1. Then κ_j∫_S f d𝖬 ≤ eΘ c^{|ι|ϱ}
∏_{l<ϱ}fl_l · Λ^{1.5·10⁶(ϱ+1)³+1} Λ'^{50000(ϱ+1)²}. -/
lemma Gauge.lintegral_positions_le (hq : Γ.IsHead j q) {Θ S e} {f : _ → _} (hΘ :
  F.pairingNorm W W * F.pairingNorm W W' ≤ Θ ^ 2)
  (hS : S ⊆ Γ'.positionsOfSize) (h : ∀ x ∈ S, f x ^ 2 ≤ e ^ 2 * selfNormProduct j p q W W' x Γ) :
  F.headDensity j p q * ∫⁻ x in S, f x ∂F.groupMeasure ≤ (e * ∏ l ∈ range 𝔰.ϱ, F.floorModulus l) *
  P.c ^ (card ι * 𝔰.ϱ) * Γ.Λ ^ (1500000 * 𝔰.n ^ 3) * Γ'.Λ ^ (50000 * 𝔰.n ^ 2) * Θ * Γ.Λ := by
  obtain ⟨k, k', _, _⟩ := Γ.isPairingKernel_self hk _, Γ.isPairingKernel_translatePairing hk hk' ..,
    hk.stronglyMeasurable, hk'.stronglyMeasurable
  grw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, mul_pow, mul_pow, ← hΘ, ← Γ.md_le 2 _
    (Γ.mem_ofSize_mono (hq j .refl)), setLIntegral_mono _ fun x m ↦ (le_rpow_inv_iff two_pos).2
    (mod_cast h x m), lintegral_mono_set hS, sq_lintegral_le _ _ fun x ↦ by exact
    ((rpow_inv_natCast_pow two_ne_zero _).trans_le (mul_assoc ..).ge), lintegral_const_mul,
    lintegral_const_mul, Γ'.lintegral_selfNorm_le k zero_le rfl, Γ'.lintegral_selfNorm_le k'
    hj congr(_ * ∫⁻ g, $(lintegral_weylRatio_mul (Φ := (‖⟪W g, W' ·⟫_ℂ‖ₑ ^ 2)) hj ?_) ∂_),
    lintegral_const_mul, 𝔰.n.lt_two_pow_self] <;> try fun_prop [selfNormProduct, selfNorm]
  simp [Level.pairingNorm, -md_inv]; grw [Γ'.two_le_and_pairs_le.1, ← ge_iff_le]; ring_nf
  simp_rw [mul_assoc]; gcongr <;> simp [headDensity, ← map_mul, ← prod_pow, ← prod_mul_distrib,
    ← map_pow, pow_right_comm _ _ 2, ← Finset.prod_inv_distrib, ← rpow_two, -md_inv, -rpow_ofNat]
  convert le_rfl; norm_cast; apply Additive.ofMul.injective; simp; match_scalars <;> grind

include hp hx

/-- Let 𝖬 be Haar, W cut, W' Bessel, p a head of length j ≤ ϱ, x a position. If f(g)² ≤
KΛ^{10⁶(ϱ+1)³}(𝖻_j/℘_j)(g)(𝖻'_j/℘_j)(w_p⁻¹g) for all g, then (∫ f d𝗆_j)² ≤ K 𝖣_j(x). -/
lemma Gauge.sq_lintegral_le_selfNormProduct {f : _ → _} {K} (hf : ∀ g, f g ≠ 0 → f g ^ 2 ≤
  K * Γ.globalConst * (F.weightedSquareSum (translatePairing W W 1) x j g /
  F.floorWeight j g x) * (F.weightedSquareSum (translatePairing W W' (weylRatio j p q)) x j
  ((weylElem j p)⁻¹ * g) / F.floorWeight j ((weylElem j p)⁻¹ * g) x)) :
  (∫⁻ g, f g ∂F.stackMeasure 0 j) ^ 2 ≤ K * Γ.selfNormProduct j p q W W' x := by
  obtain ⟨k, k'⟩ := Γ.isPairingKernel_self hk _, Γ.isPairingKernel_translatePairing hk hk' ..
  obtain ⟨b, c⟩ := k.weightedSquareSum_invariant_support x, k'.weightedSquareSum_invariant_support x
  nth_grw 1 [selfNormProduct, ← k.selfNorm_le_selfNorm_zero hj.step, sq_lintegral_le,
    lintegral_stackMeasure_mul_left p, stackMeasure_zero_eq,
    Γ.lintegral_mul_invWeight_le hj hp hx .refl c, lintegral_const_mul (K * Γ.globalConst),
    stackMeasure_zero_eq, Γ.lintegral_mul_invWeight_le hj hp.star_head hx .refl b] <;> try fun_prop
  simp [selfNorm]; ring_nf; rfl
  simp +contextual [weylElem_mul_left_comm, c.1]
  intro g; by_cases e : f g = 0; simp [e]
  grw [hf g e]; simp [invWeight, Set.indicator]; split_ifs; ring_nf; repeat simp [*]

/-- Let 𝖬 be Haar, W cut, W' Bessel and zero off points near at j ≤ ϱ, p a head, x a position,
floor j of mass ≤ V, V ≥ 1. Then 𝓘_j⁺(x)² ≤ σ^s V² 𝖣_j(x), provided σ ≥ 1 or ⟨Wy, W(yx)⟩ ≠ 0
with w_p⁻¹y, w_q⁻¹yx near at j forces vol 𝔤_a(y, yx) ≤ σ for some j < a ≤ ϱ. -/
lemma Gauge.formMajorant_sq_le {σ V} (v : F.FloorMassLe j V 1) (u : 1 ≤ V) (n : ∀ {y}, W' y ≠ 0 →
  F.IsNear j y) (c : σ < 1 → ∀ y, ⟪W y, W (y * x)⟫_ℂ ≠ 0 → F.IsNear j ((weylElem j p)⁻¹ * y) →
  F.IsNear j ((weylElem j q)⁻¹ * (y * x)) → ∃ a : Fin _, j ≤ a ∧ volume (F.floorValues a y x) ≤ σ) :
  F.formMajorant j p q W W' x ^ 2 ≤ σ ^ F.volumeExponent * V ^ 2 * Γ.selfNormProduct j p q W W' x :=
  Γ.sq_lintegral_le_selfNormProduct hk hk' hj hp hx fun y e ↦ by
  obtain ⟨⟨τ, b, _⟩, k, k'⟩ := exists_ne_zero_of_pivotModulus (right_ne_zero_of_mul e),
    Γ.isPairingKernel_self hk j, Γ.isPairingKernel_translatePairing hk hk' ..
  grw [mul_pow, k'.pivotModulus_sq_le v, lintegral_upperPairing_sq_le hj]; by_cases! l : 1 ≤ σ <;>
    [grw [k.pivotModulus_sq_le v, lintegral_upperPairing_sq_le hj, globalConst, ← Γ.one_le_Lambda, ←
    l]; grw [Γ.pivotModulus_sq_le_of_capped k hx fun ρ a e ↦
    c l _ ?_ (.of_floorGroup_mul (hk.isNear_of_ne_zero ?_) (div_mem b a)) (.of_floorGroup_mul (n
    ?_) (div_mem b a)), (by lia : _ - j ≤ 100 * 𝔰.n ^ 2), ← le_self_pow u two_ne_zero]] <;>
    first | ring_nf; rfl | intro; simp_all [weylRatio, ← (weylElem_mul_left_comm _).2] | bound

omit hk'

/-- Let 𝖬 be Haar, W cut, p a head of length j ≤ ϱ, x a position, ξ a unit, ψ(η·) = ψ(ξ·) on
elements of size 200(ϱ+1)². Then `Level.formModulus` at x with weight ψ(ηZ_{j+1,j+1}) has square at
most (c/md ξ)^|ι| times `Gauge.selfNormProduct` (W' = W).

Tower method: pairings of kernels bounded floor by floor. -/
lemma Gauge.formModulus_sq_le_of_char {η} (hφ : ∀ z ∈ Γ.ofSize (200 * 𝔰.n ^ 2), ψ (η * z) =
  ψ (ξ * z)) : F.formModulus j p q W x (fun x ↦ ψ (η * (T.frameGram x).diag ⟨j, by lia⟩)) ^ 2 ≤
  (P.c / P.md ξ) ^ card ι * Γ.selfNormProduct j p q W W x :=
  Γ.sq_lintegral_le_selfNormProduct hk hk.1 hj hp hx fun g H ↦ by
  lift j to Fin 𝔰.n using (by lia); repeat grw [← lintegral_upperPairing_sq_le hj]
  simp [Matrix.diag, ↓frameGram_eq_form_orbitPoint] at H ⊢
  obtain ⟨hf, K, σ, a, τ, b, -, h⟩ := Γ.isPairingKernel_self hk _,
    Γ.isPairingKernel_translatePairing hk hk.1 .., by
    simpa using H ∘ integral_eq_zero_of_ae ∘ ae_floorMeasure_mem.mono ∘ forall₂_imp fun _ _ ↦
      integral_eq_zero_of_ae ∘ ae_floorMeasure_mem.mono
  obtain ⟨t, ht, k, k'⟩ := exists_hasMatSize_of_isNear hj hp ((hf.isNear_of_upperPairing_ne_zero
    h.1).of_floorGroup_mul a) ((K.isNear_of_upperPairing_ne_zero h.2).of_floorGroup_mul b)
  obtain ⟨⟨e, -⟩, v, l⟩ := Γ.amplitude_support_and_plancherel ht k hf (g * x),
    Γ.amplitude_support_and_plancherel ht k' K ((weylElem j p)⁻¹ * (g * x))
  grw [integral_congr_ae (e.mono fun σ s ↦ (integral_congr_ae (v.mono fun τ s' ↦ ?_)).trans
    ((integral_const_mul ..).trans (congrArg _ integral_conj))),
    ← setIntegral_eq_integral_of_ae_compl_eq_zero (e.mono fun _ h ↦ not_imp_comm.1
    (h ∘ left_ne_zero_of_mul)), enorm_integral_le_lintegral_enorm, sq_lintegral_le _
    (Measurable.aemeasurable _) fun _ ↦ by rw [enorm_mul, mul_pow, enorm_conj]]
  refine (mul_le_mul' (setLIntegral_le_lintegral ..)
    (((measurePreserving_mulVec_orbitPoint j ht).setLIntegral_comp_preimage measurableSet_vecsOfSize
    (by fun_prop)).trans_le (l (-ξ) 0 hasFibreBound_floorQuadric))).trans ?_
  simp; ring_nf; gcongr <;> simp
  repeat fun_prop
  simp [ψ.map_neg_eq_inv, inv_eq_conj, mul_left_comm _ (ψ _), -mulVec_mulVec, U.form_mulVec_mulVec]
  exact or_iff_not_imp_right.2 fun n ↦ hφ _ (U.form_mulVec_mulVec t .. ▸ Γ.mem_ofSize_mono
    (Γ.dotProduct_mem_ofSize (fun a _ ↦ Γ.neg_star_mem_ofSize.2.2
    (s (n ∘ .inl) a)) (Size.HasMatSize.mulVec Γ.gram_mem_ofSize.1 (s' (n ∘ .inr)))))

/-- Local theorem, unequal heads. Let 𝖬 be Haar, W cut, p a head of length j, 1 ≤ j ≤ ϱ, x a
position. If the unit ξ equals (1/p_j − 1/q_j)/g for the last entries, then 𝖥_j(x; 1)² ≤
(c/md ξ)^{|ι|} 𝖣_j(x). -/
lemma Gauge.formModulus_sq_le_of_heads {i} (hi : j = i + 1) (h : ξ =
  F.g⁻¹ * ((p i)⁻¹.1 - (q i)⁻¹.1)) :
  F.formModulus j p q W x 1 ^ 2 ≤ (P.c / P.md ξ) ^ card ι * Γ.selfNormProduct j p q W W x := by
  let r g := F.floorWeight j g x * F.invWeight i x (weylElem i p * g)
  let u g := ∞ * F.invWeight j x (weylElem j p * g) ⊓ r g * ‖F.upperPairing j
    (translatePairing W W (weylRatio j p q)) g (g * x)‖ₑ ^ 2
  subst hi; obtain ⟨k, k'⟩ := Γ.isPairingKernel_self hk _,
    Γ.isPairingKernel_translatePairing hk hk.1 (i + 1) p q
  grw [formModulus, ← formIntegrandOne_eq Γ hk, selfNormProduct, ← k.selfNorm_le_selfNorm_zero
    (by lia : i ≤ _), ← le_self_add.trans (k.selfNorm_eq_add_succ (by lia)).ge, sq_lintegral_le _ _
    fun g ↦ not_lt.1 fun z : u ((weylElem _ p)⁻¹ * g) * (F.weightedSquare i _ x g * _) < _ ↦
    z.not_ge ?_, lintegral_stackMeasure_mul_left p _ fun s a g ↦ by simp [r, u,
    weylElem_mul_left_comm, k'.upperPairing_invariant, a,
    (by grind : s ∈ GT i)], stackMeasure_zero_eq, Γ.lintegral_mul_invWeight_le hj hp.star_head hx
    .refl k.weightedSquare_invariant_support, ascConv_heisenbergMeasure_succ, mconv_assoc,
    lintegral_mconv_symm, lintegral_mono fun g ↦ by grw [Γ.parseval_heisenbergMeasure_of_box ⟨i,
    hj⟩ (-ξ * p i) (p i)⁻¹ 1 (r g) k' g (g * x) (fun s c ↦ by
    simp_rw [simpleRootSum, ← sum_sub_distrib, mul_sum]; congr with b
    simp [-besselFrame_castSucc]; grind [floorUnipotent_superdiag_eq_zero b c, Units.mul_inv])
    (fun n a e ↦ ⟨by
    simp [invWeight, u] at e; have N {w} :=
      inv_mul_cancel_left w (n * g) ▸ k'.isNear_of_upperPairing_ne_zero e.2.2
    exact And.intro (Γ.exists_hasMatSize_of_isNear hj hp e.1 N) (And.intro a
      (Size.head_entries_mem_ofSize (a := ⟨i, hj⟩) Γ.hasMatSize_box hj N e.1.choose_spec hp
      .refl).1), by simp [u, r, weylElem_mul_left_comm a.1, unipotentBelow_le_unitriGroup a.2]⟩) (by
    exact fun _ ⟨⟨τ, t, _, h⟩, a, L⟩ ↦ ⟨τ, by simp; grind, _, a.2, by simpa using h,
      fun _ ⟨⟨_, s, _, e⟩, _⟩ ↦ ⟨1, one_mem _, fun c ↦ Γ.mul_mem_ofSize L (by
      rw [← inv_mem_iff, mem_floorGroup] at s t; simp at s t
      simpa [mul_apply, s, t] using (h.mul e.inv).sub .one c (eStar ⟨i, hj⟩))⟩⟩),
    lintegral_upperPairing_sq_le hj, mul_left_comm, mul_right_comm (F.floorWeight ..),
    ENNReal.mul_div_cancel] <;> simp, lintegral_const_mul, Γ.lintegral_mul_invWeight_le (by lia)
    (hp · ·.step) hx i.le_succ (k'.weightedSquareSum_invariant_support x)] <;> try fun_prop
  simp [selfNorm]; ring_nf; gcongr <;> simp
  cases And.imp k.isNear_of_upperPairing_ne_zero k'.isNear_of_upperPairing_ne_zero (by simpa using
    z.ne_zero)
  simp_all [u, r, invWeight, ↓weylElem_star, weylElem_succ, mem_unitriGroup_of_mem_floorGroup
    floorWeyl_mem_floorGroup, inf_of_le_right, IsNear.of_floorGroup_mul (x := 1) _ _
    i.le_succ]; ring_nf; simp
