import OmegaMath.NumberTheory.GRH.Lib.General.Measure.SubgroupIntegral
import OmegaMath.NumberTheory.GRH.Lib.Adelic.Poincare.BesselSubgroup
import OmegaMath.NumberTheory.GRH.Lib.General.Measure.Place
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of measure and integration (textbook or folklore).

Part of: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar measure
(known result; see Lib.DiscreteSeries.Bruhat.ComplexPlace).

This file: Product integrals, measurability, and L² bounds of integral operators multiply over
products. The unipotent character written as a trace against a matrix. Heisenberg floors, their
measures, quadric charts and convolution towers over an abstract place. Open Bruhat cell of a
unitary group: existence from nonzero minors, and uniqueness. -/

noncomputable section

open MeasureTheory Measure Fin Classical Fintype
variable {V Y X I A} [MeasurableSpace Y] {μ : Measure Y} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace X] [Monoid A] (c : Aˣ)

/-- Tonelli's theorem for finite products: for σ-finite measures μ_i on nonempty spaces and
measurable [0, ∞]-valued functions f_i, the integral of x ↦ ∏ f_i(x_i) against the product
measure is the product of the integrals of the f_i. -/
lemma lintegral_pi_prod {ι} [Fintype ι] {X : ι → _} [∀ i, MeasurableSpace (X i)] [∀ i, Nonempty
    (X i)] μ [∀ i, SigmaFinite (μ i)] {f : ∀ i, X i → _} (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂.pi μ = ∏ i, ∫⁻ x, f i x ∂μ i := (lintegral_eq_lmarginal_univ
  ofNonempty).trans (Finset.univ.induction (by simp) (by simp +contextual (disch := first
  | fun_prop | grind) [↓lmarginal_insert', lmarginal, lintegral_mul_const]))

lemma enorm_toReal_smul_le x (v : V) : ‖x.toReal • v‖ₑ ≤ x * ‖v‖ₑ := by
  cases x <;> simp [enorm_smul]

lemma integrable_toReal_smul {φ} {F : _ → V} : Measurable φ → AEStronglyMeasurable F μ →
    ∫⁻ y, φ y * ‖F y‖ₑ ∂μ < ⊤ → Integrable (fun y ↦ (φ y).toReal • F y) μ := (⟨·.ennreal_toReal
  |>.aestronglyMeasurable.smul ·, by grw [HasFiniteIntegral, enorm_toReal_smul_le, ·]⟩)

@[fun_prop] lemma measurable_integral [SFinite μ] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V] {f : X → Y → V} : Measurable ↿f → Measurable (∫ y, f · y ∂μ) :=
    (·.stronglyMeasurable.integral_prod_right.measurable)

/-- The L² bound ∫ ∑ᵢ |∫ φ(y) kᵢ(x, y) dμ(y)|² dm(x) ≤ ∫ |φ|² dn holds for every bounded
measurable φ : Y → ℂ. -/
def IsL2Contraction [Fintype I] m (μ n : Measure Y) (k : I → X → Y → ℂ) := ∀ φ C, Measurable φ →
  (∀ y, ‖φ y‖ ≤ C) → ∫⁻ x, ∑ i, ‖∫ y, φ y * k i x y ∂μ‖ₑ ^ 2 ∂m ≤ ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂n

/-- L² bounds of integral operators multiply: if finitely many measurable kernels k_v,
integrable in y, satisfy `IsL2Contraction` for σ-finite measures, so do the product kernels ∏_v
k_v(x_v, y_v) for the product measures. -/
lemma IsL2Contraction.pi {ι : Type} [Fintype ι] {I : ι → _} [∀ v, Fintype (I v)] {m μ n} [∀ v,
  SigmaFinite (m v)] [∀ v, SigmaFinite (μ v)] [∀ v, SigmaFinite (n v)] {k : ∀ _ _, X → Y → _} (hk :
  ∀ v i, Measurable ↿(k v i)) (hi : ∀ v i x, Integrable (k v i x) (μ v)) (h : ∀ v,
  IsL2Contraction (m v) (μ v) (n v) (k v)) :
  IsL2Contraction (.pi m) (.pi μ) (.pi n) fun (i : ∀ v, I v) x y ↦ ∏ v, k v (i v) (x v) (y v) := by
  have ⟨e⟩ := Finite.of_fintype ι
  induction' ‹ℕ› with _ ih generalizing ι <;> repeat intro
  have := e.isEmpty; simp [pi_of_empty _, prod_empty]
  simp_rw [← pi_map_piCongrLeft e.symm, ← (measurePreserving_piFinSuccAbove _ 0).symm.2,
    lintegral_map_equiv, integral_map_equiv]
  refine' (fun φ C _ hC ↦ _ : IsL2Contraction ..) _ ‹_› ..
  simp (disch := exact (((hi ..).mul_prod (.fintype_prod (by tauto))).bdd_mul (by fun_prop)
    (.of_forall hC))) [← ((consEquiv _).trans (e.symm.piCongrLeft I)).sum_comp, ← e.symm.prod_comp,
    integral_prod_symm, prod_univ_succ, sum_prod_type, MeasurableEquiv.piCongrLeft]
  grw [lintegral_prod_le, lintegral_prod_symm, ← h _ _ C, (lintegral_finsetSum ..).le,
    lintegral_lintegral_swap (Measurable.aemeasurable _), ← (lintegral_finsetSum ..).ge,
    ← ih _ _ (by tauto) 1 _ _ _ fun _ ↦ norm_integral_le_of_norm_le
    ((hi ..).norm.const_mul _) (.of_forall (by grw [norm_mul, hC ⟨·, _⟩]))]
  repeat first | fun_prop | grind [integral_mul_const]

/-- The sequence indexed by ℕ that is the tuple c at indices below n, t at index n, and 1 at
indices above n. -/
def padTuple {C n} [One C] (c : Fin n → C) t a := dite _ (c ⟨a, ·⟩) fun _ ↦ ite (a = n) t 1

/-- The element c as a unit if it is invertible, and the unit 1 otherwise. -/
def unitOrOne (c : A) := if h : IsUnit c then h.unit else 1

@[simp] lemma unitOrOne_val : unitOrOne ↑c = c := by simp [unitOrOne]

lemma continuousAt_unitOrOne [TopologicalSpace A] [h : IsOpenUnits A] :
  ContinuousAt unitOrOne c.1 := h.1.continuousAt_iff.1 (by convert continuousAt_id; aesop)

namespace Filling

open Matrix Finset
variable {A : _} {𝔰 : Shape} [CommRing A] (T : 𝔰.Form A)

/-- The chain matrix C of T: the matrix for which tr(Cu) = σ(u) + conj σ(u⁻¹) on isometries u,
where σ(u) = ∑ u_{j,j+1} on the frame. -/
def besselCharMatrix := of fun y x ↦ ∑ a, (ite (.inl a = x) (ite (𝔰.besselFrame a.succ = y) 1 0) 0 +
  ite (eStar a = y) (T.splitGram (𝔰.besselFrame a.succ) x) 0)

variable {T} [StarRing A] (u : T.G)

lemma trace_besselCharMatrix_mul : (besselCharMatrix T * u.1.1).trace =
  simpleRootSum u + star (simpleRootSum u⁻¹) := by
  have := congrFun₂ (U.form_mul_inv_eq u⁻¹)
  simp_all [mul_apply, sum_mul, add_mul, simpleRootSum, @Finset.sum_comm (Fin _), -Sum.forall,
    besselCharMatrix, trace]

lemma simpleRootSum_inv : u ∈ besselS → simpleRootSum u⁻¹ = -simpleRootSum u := by simp_all
  [eq_neg_iff_add_eq_zero, ← simpleRootSum_mul, simpleRootSum_eq_zero_of_mem_besselH]

end Filling

seal CStarMatrix

open Matrix Sum Function ENNReal Filter TraceOne Place U Subgroup
variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {l}

attribute [local simp ↓] star_form mconv_dirac dirac_mconv lintegral_prod lintegral_map comp_def

section

variable [TraceOne A] {T : 𝔰.Form A} (a : Fin 𝔰.ϱ) {g s : T.G} [H : IsHermUnit T.splitGram]
  (p q : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A)

attribute [local simp] ext_iff_mulVec mulVec_neg IsHermUnit.conjTranspose_eq inclMatrix_val_mulVec
  eichlerMap vecMulVec FI.level

attribute [local simp ←] mulVec_mulVec

/-- The isometry ν(v, β) of floor a: the Eichler transformation with e*_{a+1} ↦ e*_{a+1} + v +
(β − τh(v,v))e_{a+1}, for β skew and v projected to V_{a+1}. -/
def TraceOne.heisenbergElem := let v := inclMatrix A (↑) *ᵥ p.1; U.of H.2
    (eichlerMap T.splitGram (Pi.single (inl a) 1) (-v) (τ * star v ⬝ᵥ T.splitGram *ᵥ v - p.2))
    (by apply (exists_unitary_eq_eichlerMap ..).elim fun e ↦ (· ▸ e.2) <;> simp [v]; grind)

@[local simp ↓] lemma heisenbergElem_mulVec w : let v := inclMatrix A (↑) *ᵥ p.1; heisenbergElem
    (T := T) a p *ᵥ w = w + w (eStar a) • v + ((p.2 - τ * star v ⬝ᵥ T.splitGram *ᵥ v) * w
    (eStar a) - star v ⬝ᵥ T.splitGram *ᵥ w) • Pi.single (inl
    a) 1 := by simp [heisenbergElem, eichlerMap_mulVec, -eichlerMap]; module

/-- Every Heisenberg element ν(v, β) of floor a < ϱ lies in the group 𝒩_a = H_a ∩ 𝒩_{<a+1}. -/
lemma heisenbergElem_mem_floorUnipotent : heisenbergElem (T := T) a p ∈ floorUnipotent a := by
  constructor <;> simp [mem_floorGroup, mem_unipotentBelow, heisenbergElem] <;> grind [star_zero]

variable {a p q}

lemma mul_heisenbergElem (h : s ∈ GT (a + 1)) : s * heisenbergElem a p =
  heisenbergElem a (s.1.1.toSquareBlockProp _ *ᵥ p.1, p.2) * s := by
  obtain _ := (mem_unitriGroup_succ_iff (b := a.castSucc) (by grind)).1
    (mem_unitriGroup_of_mem_floorGroup h), form_mulVec_mulVec s (Pi.single (inl a) 1)
  ext : 2; simp_all [inclMatrix_mulVec_floor_block, form_mulVec_mulVec, orbitPoint_eq_iff]

lemma heisenbergElem_mul : (heisenbergElem a p * heisenbergElem a q : T.G) =
  heisenbergElem a (p.1 + q.1, p.2 + q.2 + skewPart (τ * star (inclMatrix A (↑) *ᵥ q.1) ⬝ᵥ
  T.splitGram *ᵥ inclMatrix A (↑) *ᵥ p.1)) := by ext : 2; simp [funext_iff]; grind

/-- Let g lie in H_a and x be e_{a+1} or e*_{a+1}. If c·gx has coordinate 1 at e*_{a+1}, then
c·gx = ν(v, β)e*_{a+1} for some Heisenberg element ν(v, β) of floor a. -/
lemma exists_col_eq_heisenbergElem i c (h : g ∈ GT a) (k : floorOf i = a) (e : g.1 (eStar a) i * c =
  1) : ∃ p, g *ᵥ Pi.single i c = (heisenbergElem (T := T) a p).1.1 *ᵥ Pi.single (eStar a) 1 := by
  obtain _ := (floorGroup_apply h · i),
    form_mulVec_mulVec g (Pi.single i c) (Pi.single i c); set w := g.1.1 *ᵥ _
  let ⟨v, d, f⟩ : ∃ v d, w =
    Pi.single (eStar a) 1 + inclMatrix A (@Subtype.val _ (a + 1 ≤ floorOf ·)) *ᵥ v +
    d • Pi.single (inl a) 1 := ⟨(w ·), w (inl a), by simp_all [w, funext_iff]; grind [floorOf]⟩
  use ⟨v, skewPart (star τ * d)⟩; simp_all; grind [oppositeIndex_spec]

/-- For a < ϱ and g in Q_{a+1} ∩ H_a, there is a Heisenberg element ν(v, β) of floor a such that
g⁻¹ν(v, β) lies in H_{a+1}. -/
lemma exists_heisenbergElem_mem_floorGroup (h : g ∈ unitriGroup (a + 1) ⊓ GT a) : ∃ p,
  g⁻¹ * heisenbergElem a p ∈ GT (a + 1) := (exists_col_eq_heisenbergElem (eStar a) 1 h.2 rfl
  (by grind [unitriGroup_dual_row h.1, one_apply_eq])).imp fun p f ↦ mem_floorGroup.2 fun i j _ ↦ by
  have := mul_mem (inv_mem h) ⟨unipotentBelow_le_unitriGroup
    (heisenbergElem_mem_floorUnipotent a p).2, (heisenbergElem_mem_floorUnipotent ..).1⟩
  by_cases j = eStar a; simpa [↓mulVec_mulVec, *] using congr((g⁻¹ *ᵥ $f) i).symm
  grind [level_le_or_exists_dual, mem_inf, Fin.ext_iff]

lemma exists_floorGroup_mul_floorUnipotent (h : s ∈ unitriGroup (l + 1) ⊓ GT l) : ∃ g ∈ GT (l + 1),
  ∃ ν ∈ floorUnipotent l, s = g * ν := if k : _ then ⟨_, (exists_heisenbergElem_mem_floorGroup (a :=
  ⟨l, k⟩) (inv_mem h)).choose_spec, by simp [← inv_mul_eq_iff_eq_mul,
  heisenbergElem_mem_floorUnipotent ⟨l, k⟩]⟩ else ⟨s, by simp_all; grind⟩

lemma exists_floorGroup_mul_unipotentBelow {j} : s ∈ unitriGroup j → ∃ γ ∈ GT j,
  ∃ ν ∈ unipotentBelow j, s = γ * ν :=
  j.rec (fun _ ↦ ⟨s, by simp⟩) fun j i h ↦ have ⟨γ, a, ν, b, e⟩ := i (by grind)
  (exists_floorGroup_mul_floorUnipotent ⟨by simp_all [mul_mem_cancel_right,
    unipotentBelow_le_unitriGroup b], a⟩).imp fun g
  ⟨c, n, k, d⟩ ↦ ⟨c, n * ν, mul_mem k.2 (by grind), by grind⟩

/-- 𝖲 = 𝖴𝖧: when the Gram matrix of the whole space is hermitian and invertible, s lies in the
Bessel subgroup 𝖲 if and only if s = uh with u in 𝖴 and h in 𝖧, the subgroup fixing all e_j,
e*_j and z. -/
lemma mem_besselS : s ∈ besselS ↔ ∃ u ∈ besselU, ∃ h ∈ besselH, s = u * h :=
  ⟨(exists_floorGroup_mul_unipotentBelow · |>.elim
  fun h ⟨a, _, b, e⟩ ↦ ⟨_, unipotentBelow_le_besselU (conj_mem_unipotentBelow a b),
  h, by simp [*]⟩), by grind [mul_mem, mem_unitriGroup_of_mem_besselU]⟩

/-- If the Gram matrix of the whole space is hermitian and invertible, the Bessel subgroup 𝖲 of
the unitary group normalises the subgroup 𝖴⁰ of elements of 𝖴 fixing the frame. -/
lemma besselS_le_normalizer_besselU0 : T.besselS ≤ .normalizer T.besselU0 :=
  le_normalizer_iff.2 fun s a u h ↦ by
  obtain ⟨⟨_, _, ⟨⟩⟩⟩ := mem_besselS.1 (inv_mem a), mul_inv_cancel s ▸ one_mem T.besselU0,
    besselS_le_normalizer_besselU a u
  simp_all [mem_besselU0_iff, ← mul_assoc, frameMatrix_mul_besselH, frameMatrix_mul]

/-- Induction on the groups 𝒩_{<j}, for a hermitian invertible Gram matrix: if C 0 1 holds, and
C j ν implies C (j+1) (γν) for all γ in 𝒩_j, then C j s holds for every s in 𝒩_{<j}. -/
lemma unipotentBelow_induction {C : ℕ → T.G → Prop} (o : C 0 1) (h : ∀ j, ∀ γ ∈ floorUnipotent j,
  ∀ ν, C j ν → C (j + 1) (γ * ν)) j : ∀ s ∈ unipotentBelow j, C j s :=
  j.rec (fun _ k ↦ by simpa [eq_one_of_mem_floorGroup_inf ⟨floorGroup_zero.ge ⟨⟩, k⟩]) fun j i _ k ↦
  (exists_floorGroup_mul_unipotentBelow (unipotentBelow_le_unitriGroup k)).elim fun _ ⟨a, _, b, e⟩ ↦
  e ▸ h j _ ⟨a, (mul_mem_cancel_right (by grind : _ ∈ unipotentBelow _)).1 (e ▸ k)⟩ _ (i _ b)

/-- For a < ϱ, every element of 𝒩_a is a Heisenberg element ν(v, β) of floor a. -/
lemma exists_eq_heisenbergElem_of_mem (h : g ∈ floorUnipotent a) : ∃ p, g = heisenbergElem a p :=
  (exists_heisenbergElem_mem_floorGroup ⟨unipotentBelow_le_unitriGroup h.2, h.1⟩).imp fun p e
  ↦ inv_mul_eq_one.1 (eq_one_of_mem_floorGroup_inf ⟨e,
  (mul_mem (inv_mem h) (heisenbergElem_mem_floorUnipotent ..)).2⟩ (by simp))

lemma heisenbergElem_inv : (heisenbergElem (T := T) a p)⁻¹ = heisenbergElem a (-p.1,
  skewPart (τ * star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ inclMatrix A (↑) *ᵥ p.1) - p.2) :=
  inv_eq_of_mul_eq_one_right (by ext; simp [↓heisenbergElem_mul, heisenbergElem])

/-- For s in H_{a+1} and v in V_{a+1}, the sum of the entries just above the diagonal of the
frame block of sν(v, β)s⁻¹ equals −h(v, s⁻¹f_{a+2}). -/
lemma simpleRootSum_conj_heisenbergElem (k : s ∈ GT (a + 1)) : simpleRootSum (s * heisenbergElem a
  p * s⁻¹) = -(star (inclMatrix A (↑) *ᵥ p.1) ⬝ᵥ T.splitGram *ᵥ orbitPoint a.succ s) := by
  rw [← form_mulVec_mulVec s, mul_heisenbergElem k, mul_inv_cancel_right,
    ← inclMatrix_mulVec_floor_block a.2 k, orbitPoint_eq_iff.1 rfl, simpleRootSum, sum_eq_single a
    (floorUnipotent_superdiag_eq_zero · (heisenbergElem_mem_floorUnipotent ..) ∘ by lia)]
  simp [heisenbergElem, ↓dotProduct_mulVec, neg_vecMul]; grind [floorOf, floorOf_besselFrame]

end

variable [TopologicalSpace A] [MeasureSpace A] [P : Place A] (ι : Type) [Fintype ι] (T : 𝔰.Form A)
  (m : ℕ) {n k Z : Type} [Fintype n] [Fintype k]

/-- The Haar measure of V_l, as a measure on V: the image of the volume on the coordinates of
floor at least l under the inclusion. -/
abbrev floorVolume (l : ℕ) : Measure (𝔰.BesselIndex → A) :=
  map (inclMatrix A (@Subtype.val _ (l ≤ floorOf ·)) *ᵥ ·) volume

/-- A volume-preserving basis of V_ϱ = X₀ ⊕ Az made of m+1 hyperbolic pairs and an orthonormal
part indexed by ι. -/
structure HyperbolicBasis where
  basisMatrix : Matrix 𝔰.MiddleIndex (_ ⊕ SplitIndex m ι) A
  gram_eq : basisMatrixᴴ * T * basisMatrix = planeSumGram (hyperbolicGram _ 1)
  card_eq : 𝔰.k + 1 = card ι + 2 * m + 2
  md_det : P.md T.det = 1

attribute [local simp ←] Matrix.ext_iff

variable {ι T m} (F : HyperbolicBasis ι T m) (b : Fin 𝔰.n) [MeasurableSpace Z] {ζ : Measure Z}

/-- The law of w_l(c)⁻¹, w_l(c) the Weyl element of floor l, when c in A has the measure
md(c)^{d_l} dc, d_l = |κ| + 1 + 2(ϱ − l − 1). -/
abbrev Place.weylLaw (l : ℕ) : Measure T.G :=
  (volume.withDensity (md · ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (l + 1))))).map fun c ↦ (floorWeyl l c)⁻¹

lemma measurePreserving_inclMatrix (g : n ≃ k) : MeasurePreserving (inclMatrix A g *ᵥ ·) := by
  simpa [inclMatrix, submatrix_mulVec_equiv] using! (measurePreserving_piCongrLeft _ g.symm).symm

omit [TopologicalSpace A] [MeasureSpace A] [Place A] in
lemma gram_inclMatrix {n} (g : n → k) (J : Matrix k k A) : (inclMatrix A g)ᴴ * J * inclMatrix A g =
  J.submatrix g g := by simp [inclMatrix, mul_apply]

lemma map_inclMatrix_eq_floorVolume (f : n → 𝔰.BesselIndex) (hf : Injective f := by intro; simp)
  (h : ∀ i, i ∈ Set.range f ↔ l ≤ floorOf i := by simp) : volume.map (inclMatrix A f *ᵥ ·) =
  floorVolume l := by simp (disch := fun_prop) [floorVolume, ← (measurePreserving_inclMatrix
  (.trans (.ofInjective f hf) (.subtypeEquivRight h))).2, Measure.map_map, mul_inclMatrix]; rfl

/-- The index set of the hyperbolic pairs of the chart of V_b other than the first: the m
further pairs of V_ϱ and the pairs (e_a, e*_a), a > b. -/
abbrev FloorPairs m := Fin m ⊕ {i : Fin 𝔰.ϱ // b.1 ≤ i}

/-- The matrix whose columns are the basis of V_b formed by the given basis of V_ϱ and the pairs
e_a, e*_a with a > b. -/
def HyperbolicBasis.floorBasis :
  Matrix 𝔰.BesselIndex (Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m) A := inclMatrix A (inr ∘ inl ⊕ᵥ
  .map (↑) (inr ∘ (↑))) * F.basisMatrix.fromBlocks 0 0 (diagonal 1) * inclMatrix A (inl ∘ inl ⊕ᵥ
  (.map (inr ∘ inl) inl ⊕ᵥ (inl ∘ inr ∘ inr ∘ inl ⊕ᵥ .map (inr ∘ inr ∘ inr) inr)))

lemma HyperbolicBasis.gram_floorBasis : (F.floorBasis b)ᴴ * T.splitGram * F.floorBasis b =
  planeSumGram (hyperbolicGram _ 1) := by rw [floorBasis, gram_mul, gram_inclMatrix, gram_mul,
  gram_inclMatrix, (?_ : submatrix _ _ _ = T.fromBlocks
  0 0 (fromBlocks 0 1 1 0))] <;> simp [F.gram_eq, splitGram]

/-- The linear map v ↦ Ev given by the matrix E of a basis `HyperbolicBasis` of V_ϱ preserves
volume. -/
lemma HyperbolicBasis.measurePreserving_mulVec : MeasurePreserving (F.basisMatrix *ᵥ ·) :=
  let e := equivOfCardEq (α := 𝔰.MiddleIndex) (by simp +arith [F.card_eq])
  have d := congr($(gram_mul F.basisMatrix T (inclMatrix A e)) ^ 2).trans (c := 1) (by simp [sq,
    gram_inclMatrix, F.gram_eq, ↓reindex_equiv e.symm])
  ⟨by fun_prop, by simp (disch := fun_prop) [← (measurePreserving_inclMatrix e).2, Measure.map_map,
    P.map_mulVec_volume _ _ (isUnit_det_of_left_inverse ((mul_assoc ..).trans
    d)), by simpa [F.md_det, ← sq,
    toNNReal_eq_one_iff, -conjTranspose_mul] using congr((P.md ($d).det).toNNReal)]⟩

lemma HyperbolicBasis.map_floorBasis_volume : volume.map (F.floorBasis b *ᵥ ·) = floorVolume b := by
  simp [floorBasis, ← mulVec_mulVec, fromBlocks_mulVec]
  apply (MeasurePreserving.comp ⟨by fun_prop, map_inclMatrix_eq_floorVolume _ _ _⟩
    (measurePreserving_sumElim.comp ((F.measurePreserving_mulVec.prod (.id _)).comp
    ((measurePreserving_sumPiEquivProdPi _).comp (measurePreserving_inclMatrix
    (.ofBijective ..)))))).2 <;> simp [Bijective, Injective, Surjective, b.is_le]

variable {μ ν : Measure T.G} [SFinite μ] [SFinite ν] (σ : ℕ →
  Measure T.G) [∀ l, SFinite (σ l)] {i j} {s : T.G} {S : Subgroup T.G} {f : T.G → ℝ≥0∞}

/-- The measure η_l on the unitary group: for l < ϱ the image of dv dβ on V_{l+1} × A⁻ under (v,
β) ↦ ν(v, β), otherwise the unit mass at 1. -/
def Place.heisenbergMeasure [H : IsHermUnit T.splitGram] l := if h :
  l < 𝔰.ϱ then (volume.prod P.skewMeasure).map (heisenbergElem (T := T) ⟨l, h⟩) else dirac 1

lemma measurableSet_floorGroup : MeasurableSet (T.GT l : Set T.G) :=
  (isClosed_of_entries_eq_one mem_floorGroup).measurableSet

@[simp] lemma heisenbergMeasure_eq_dirac_one [H : IsHermUnit T.splitGram]
    (h : 𝔰.ϱ ≤ l) : heisenbergMeasure l = dirac (1 :
  T.G) := dite_eq_right h.not_gt

@[fun_prop] lemma continuous_orbitPoint : Continuous (orbitPoint b : T.G →
  _) := by fun_prop [orbitPoint]

variable [H : IsHermUnit T.splitGram] in
instance :
  SFinite (heisenbergMeasure l : Measure T.G) := by fun_cases heisenbergMeasure <;> infer_instance

lemma isClosedEmbedding_unitary_coe [H : IsHermUnit T.splitGram] :
    Topology.IsClosedEmbedding (·.1.1 : T.G → _) :=
  isClosedEmbedding_mat H.2

lemma measurable_unitary_of_coe [H : IsHermUnit T.splitGram]
    {f : Z → T.G} : Measurable (f · |>.1.1) → Measurable f :=
  isClosedEmbedding_unitary_coe.measurableEmbedding.measurable_comp_iff.1

@[fun_prop] lemma continuous_weylElem [H : IsHermUnit T.splitGram] :
    Continuous (weylElem 𝔰.ϱ : _ → T.G) :=
  isClosedEmbedding_unitary_coe.continuous_iff.2
  (continuous_matrix fun _ _ ↦ by simp [weylElem, weylOn]; split_ifs <;> fun_prop)

/-- For a place A and any l, the map from A to the unitary group sending c to the Weyl element
w_l(c) (`floorWeyl`) is measurable. -/
@[fun_prop] lemma measurable_floorWeyl [H : IsHermUnit T.splitGram] :
    Measurable (floorWeyl l : A → T.G) :=
  measurable_unitary_of_coe (by
  have : Measurable (@IsUnit A _) := measurableEmbedding_units_val.measurableSet_range.mem
  repeat apply measurable_pi_lambda <;> intro
  simp [floorWeyl, weylOn, eq_ite_iff]; apply_rules [Measurable.ite] <;> measurability)

@[fun_prop] lemma continuous_heisenbergElem [H : IsHermUnit T.splitGram]
    {a} : Continuous (heisenbergElem (T := T) a) :=
  isClosedEmbedding_unitary_coe.continuous_iff.2 (by simp [heisenbergElem, eichlerMap]; fun_prop)

lemma measurePreserving_floor_block_mulVec [H : IsHermUnit T.splitGram] (h : s ∈ GT l) :
  MeasurePreserving (s.1.1.toSquareBlockProp (l ≤ floorOf ·) *ᵥ ·) := measurePreserving_mulVec _
  (by simpa [U.det, twoBlockTriangular_det' s.1.1 (l ≤ floorOf ·) (by grind [one_apply_ne]), show
  toSquareBlockProp s.1.1 (¬l ≤ floorOf ·) = toBlock 1 _ _ by ext; apply h; grind]
  using (det (H.2.map detMonoidHom) s).2.1)

lemma ae_mem_floorUnipotent [H : IsHermUnit T.splitGram] : ∀ᵐ x : T.G ∂heisenbergMeasure l,
  x ∈ floorUnipotent l := by fun_cases heisenbergMeasure; exacts [(ae_map_iff (by fun_prop)
  (measurableSet_floorGroup.inter (isClosed_of_entries_eq_one
  mem_unipotentBelow).measurableSet)).2 (.of_forall (heisenbergElem_mem_floorUnipotent _)), by simp]

lemma heisenbergMeasure_mconv_dirac [H : IsHermUnit T.splitGram]
    (h : s ∈ floorUnipotent l) : heisenbergMeasure l ∗ₘ dirac s =
  heisenbergMeasure l ∧ dirac s ∗ₘ heisenbergMeasure l = heisenbergMeasure l := by
  fun_cases heisenbergMeasure; obtain ⟨⟨v, t⟩, rfl⟩ := exists_eq_heisenbergElem_of_mem (a :=
    ⟨_, ‹_›⟩) h; constructor <;> apply ext_of_lintegral <;> intro Φ _ <;> simp (disch := fun_prop)
    [heisenbergElem_mul, add_assoc, add_comm
    t, fun w ↦ lintegral_add_right_eq_self (μ := skewMeasure) (Φ <| heisenbergElem _ ⟨w, ·⟩)] <;> rw
    [← lintegral_add_right_eq_self _ (-v)] <;> simp
  simp_all [eq_one_of_mem_floorGroup_inf h]

lemma dirac_mconv_heisenbergMeasure_comm [H : IsHermUnit T.splitGram]
    (h : s ∈ GT (l + 1)) : dirac s ∗ₘ heisenbergMeasure l =
  heisenbergMeasure l ∗ₘ dirac s := by fun_cases heisenbergMeasure; nth_rw 2
  [← ((measurePreserving_floor_block_mulVec h).prod (.id _)).2]; repeat simp (disch :=
  fun_prop) [↓Measure.map_map, mul_heisenbergElem (a := ⟨l, _⟩) h, Prod.map_def]

/-- For measures σ_l on a group, the convolution σ_{a+i−1} ∗ ⋯ ∗ σ_a in descending order of i
consecutive terms; the Dirac measure at 1 if i = 0. -/
def descConv | _, 0 => dirac 1 | a, i + 1 => descConv (a + 1) i ∗ₘ σ a

/-- For measures σ_l on a group, the convolution σ_0 ∗ ⋯ ∗ σ_{j−1} in ascending order; the Dirac
measure at 1 if j = 0. -/
def ascConv | 0 => dirac 1 | j + 1 => ascConv j ∗ₘ σ j

instance (a i) : SFinite (descConv σ a i) := by fun_induction descConv <;> infer_instance

instance : SFinite (ascConv σ j) := by fun_induction ascConv <;> infer_instance

variable {σ}

lemma lintegral_mconv_dirac f : lintegral (μ ∗ₘ dirac s) f = ∫⁻ x, f (x * s) ∂μ :=
  by simpa using lintegral_map_equiv f (.mulRight s)

lemma lintegral_dirac_mconv f s : lintegral (dirac s ∗ₘ μ) f = ∫⁻ x, f (s * x) ∂μ :=
  by simpa using lintegral_map_equiv f (.mulLeft s)

lemma lintegral_eq_of_dirac_mconv_eq {t} (h : dirac s ∗ₘ μ = μ ∗ₘ dirac t) : lintegral μ f = ∫⁻ x,
  f (s⁻¹ * x * t) ∂μ := by simpa [↓lintegral_dirac_mconv, ↓lintegral_mconv_dirac,
  mul_assoc] using congr(∫⁻ x, f (s⁻¹ * x) ∂$h)

lemma lintegral_mconv_symm (hf : Measurable f) : lintegral (μ ∗ₘ ν) f = ∫⁻ y, ∫⁻ x,
  f (x * y) ∂μ ∂ν := (lintegral_mconv hf).trans (lintegral_lintegral_swap (by fun_prop))

lemma mconv_apply_eq_lintegral {Y} (o : MeasurableSet Y) : (μ ∗ₘ ν) Y = ∫⁻ y,
  μ {x | x * y ∈ Y} ∂ν := map_apply measurable_mul o ▸ prod_apply_symm (measurable_mul o)

omit [SFinite μ] in
lemma ae_mem_mconv (h : ∀ᵐ x ∂μ, x ∈ S) (k : ∀ᵐ x ∂ν, x ∈ S) (m : MeasurableSet S.carrier := by
    exact measurableSet_floorGroup) : ∀ᵐ x ∂μ ∗ₘ ν, x ∈ S := (ae_map_iff (by fun_prop) m).2
  (.mono (measure_prod_compl_eq_zero h k) fun _ ↦ And.elim S.mul_mem)

lemma mconv_comm_of_ae (h : ∀ᵐ s ∂μ, dirac s ∗ₘ ν = ν ∗ₘ dirac s) : μ ∗ₘ ν = ν ∗ₘ μ :=
  ext_of_lintegral _
  fun f a ↦ by rw [lintegral_mconv a, lintegral_mconv_symm a, lintegral_congr_of_ae_imp h]
               simp +contextual [← lintegral_dirac_mconv, ← lintegral_mconv_dirac]

lemma descConv_add i j a : descConv σ a (i + j) = descConv σ (a + i) j ∗ₘ descConv σ a i := by
  fun_induction descConv <;> simp_all +arith [descConv, mconv_assoc]

lemma descConv_succ i : descConv σ 0 (i + 1) =
  σ i ∗ₘ descConv σ 0 i := by simp [↓descConv_add, descConv]

omit [TopologicalSpace A] [Place A] [SFinite μ] in
lemma exists_ne_zero_of_ae {p : _ → _} (h : ∀ᵐ x ∂μ, p x) (k : lintegral μ f ≠ 0) : ∃ x, p x ∧
  f x ≠ 0 := by contrapose! k; simp [lintegral_congr_of_ae_imp h k]

/-- The measure δ^(b) on the quadric h(v, v) = h(f_{b+1}, f_{b+1}) in V_b: the flat chart
measure `Place.quadricMeasure` carried over by the basis of V_b. -/
abbrev HyperbolicBasis.floorQuadric [H : IsHermUnit T.splitGram]
    (β := skewUnitMul (T.splitGram (𝔰.besselFrame b)
  (𝔰.besselFrame b))) := (quadricMeasure (hyperbolicGram _ 1) β).map (F.floorBasis b *ᵥ ·)

lemma HyperbolicBasis.isDisintegration_floorVolume [H : IsHermUnit T.splitGram]
    {μ} (v : μ = floorVolume b) :
  IsDisintegration μ T.splitGram (F.floorQuadric b ·) := have k := F.gram_floorBasis b; v ▸
    F.map_floorBasis_volume b ▸ (isDisintegration_quadricMeasure (by simp)).map k
  ((Matrix.mul_assoc ..).trans (congr($k * $k).trans (by simp)))

lemma exists_factor_orbitPoint [StandardBorelSpace Z] [Nonempty Z] {Φ : T.G → Z} (hF : Measurable Φ)
    (hi : (unitriGroup (b + 1) ⊓ GT b).FixesLeft Φ) : ∃ A, Measurable A ∧ ∀ σ ∈ GT b, Φ σ =
  A (orbitPoint b σ) := have := (measurableSet_floorGroup (l := b)).standardBorel
  ((factorsThrough_iff (Φ ∘ (·.1) : GT b → _)).1 fun σ τ h ↦ by simpa using
    (hi _ (inv_mul_mem_of_orbitPoint_eq σ⁻¹.2
    τ⁻¹.2 h) τ)).elim fun _ f ↦ ((Measurable.measurable_comp_iff_restrict (by fun_prop)).1 (f ▸
    hF.comp (by fun_prop))).exists_eq_measurable_comp.imp (by aesop (add simp funext_iff))

lemma ae_descConv_mem (h : ∀ {l}, ∀ᵐ x ∂σ l, x ∈ GT l) : ∀ᵐ x ∂descConv σ l i, x ∈ GT l := by
  fun_induction descConv; simp; exact ae_mem_mconv (.mono ‹_› (by grind)) h

variable [H : IsHermUnit T.splitGram]

lemma ascConv_heisenbergMeasure_dirac_comm : ∀ s ∈ T.GT j, dirac s ∗ₘ ascConv heisenbergMeasure j =
  ascConv heisenbergMeasure j ∗ₘ dirac s := j.rec (by simp [ascConv]) (by grind [ascConv,
  _=_ mconv_assoc, dirac_mconv_heisenbergMeasure_comm])

lemma ascConv_heisenbergMeasure_succ : (ascConv heisenbergMeasure (j + 1) : Measure T.G) =
  heisenbergMeasure j ∗ₘ ascConv heisenbergMeasure j :=
  (mconv_comm_of_ae (ae_mem_floorUnipotent.mono (ascConv_heisenbergMeasure_dirac_comm · ·.1))).symm

lemma ascConv_heisenbergMeasure_invariant : s ∈ unipotentBelow
  j → let α := ascConv heisenbergMeasure j; α ∗ₘ dirac s = α ∧ dirac s ∗ₘ α = α := by
  apply unipotentBelow_induction; simp; grind [ascConv, ascConv_heisenbergMeasure_succ,
    _=_ mconv_assoc, =_ dirac_mconv_dirac, → heisenbergMeasure_mconv_dirac]

lemma ae_ascConv_mem_unipotentBelow : ∀ᵐ x ∂ascConv heisenbergMeasure j, x ∈ T.unipotentBelow j :=
  j.rec (by simp [ascConv]) fun _ h ↦ ae_mem_mconv (h.mono (by grind)) (ae_mem_floorUnipotent.mono
  fun _ ↦ (·.2)) (isClosed_of_entries_eq_one mem_unipotentBelow).measurableSet

/-- Plancherel's inequality at a place: for a unit η and f measurable and integrable on A^ι, ∫
|∫ ψ(η v*w) f(w) dw|² dv ≤ (c/md η)^{|ι|} ∫ |f|². -/
lemma Place.plancherel_inequality (η : Aˣ) {f : (ι → A) → ℂ} (hf : Integrable f) (k :
  Measurable f) : ∫⁻ v, ‖∫ w, P.ψ
  (η * star v ⬝ᵥ w) * f w‖ₑ ^ 2 ≤ (P.c / P.md η) ^ card ι * ∫⁻ w, ‖f w‖ₑ ^ 2 := by
  obtain ⟨G, m, i, p, o, b⟩ := P.exists_plancherel_kernel
  grw [lintegral_mono fun v ↦ ((by fun_prop : Continuous fun x ↦ ‖(‖∫ w, P.ψ (η * star v ⬝ᵥ w) *
    f w‖ ^ 2 * ∏ i, G (star x * v i) : ℂ)‖ₑ).tendsto' 0 _ (by simp [enorm, o])).liminf_eq.ge,
    lintegral_liminf_le, liminf_le_of_frequently_le' ((mem_closure_iff_frequently.1
    (dense_of_ae ae_isUnit 0)).mono _)]; rintro _ ⟨u, rfl⟩; let g v (x : _ × _) :=
         (∏ i, G (v i)) * ψ (η * u⁻¹ * star v ⬝ᵥ (x.2 - x.1)) * (star (f x.1) * f x.2)
  have J : Integrable g.uncurry := .mono (.smul_prod (.fintype_prod fun _ ↦ i) (hf.mul_prod
    hf)) (Measurable.aestronglyMeasurable (by fun_prop)) (by simp [g, uncurry])
  have e v : ‖∫ w, P.ψ (η * u⁻¹ * star v ⬝ᵥ w) * f w‖ ^ 2 * ∏ i, ↑(G (v i)) = ∫ x, g v x := by
    simp [← Complex.conj_mul', ← integral_conj, ← integral_prod_mul, mul_assoc,
      g, mul_sub, ψ.map_sub_eq_div, division_def, Complex.inv_eq_conj]; ac_rfl
  grw [lintegral_eq_mul_lintegral_map (map_mulVec_volume _ (star u⁻¹.1 • 1) _), lintegral_map, ← b,
    lintegral_eq_mul_lintegral_map (map_mul_volume (η * u⁻¹)) (md_ne_zero_and_ne_top
    _), lintegral_map] <;> try simp [← mul_assoc, mul_pow,
    ENNReal.mul_div_right_comm, ENNReal.div_self, ← star_mul, e, IsUnit.pow]
  grw [← ofReal_integral_norm_eq_lintegral_enorm (by exact J.integral_prod_left), mul_assoc, card,
    Real.ofReal_le_enorm, show ‖_‖ₑ = ‖∫ (v) (x), g v x‖ₑ by
    simp [← e, abs_of_nonneg (p _), enorm]; norm_cast,
    integral_integral_swap J, enorm_integral_le_lintegral_enorm, volume_eq_prod,
    ← (measurePreserving_prod_add_swap ..).lintegral_comp, lintegral_prod_le,
    ← Finset.prod_const (lintegral ..), ← lintegral_pi_prod, ← lintegral_mul_const]
  gcongr _ * ∫⁻ z, ?_; any_goals fun_prop
  simpa [g, lintegral_add_right_eq_self (‖f ·‖ₑ ^ 2), lintegral_const_mul',
    ← sq, ← rpow_mul_natCast] using mul_le_mul' (by simp [enorm, ← ofNNReal_finsetProd, dotProduct,
    ← nnnorm_prod, ← integral_fintype_prod_volume_eq_prod, -AddChar.toMonoidHom_apply, mul_assoc,
    Finset.mul_sum, mul_left_comm, show ⇑ψ = ψ.toMonoidHom ∘ .ofAdd from
    rfl]) (lintegral_mul_le_Lp_mul_Lq _ .two_two hf.1.enorm (hf.comp_add_right z).1.enorm)

/-- For ζ s-finite, the regrouping (((t, x), w), (y, z)) ↦ ((t, (x, w, y)), z), with t in A, x, y in
A^n, w in A^ι, preserves the products of volumes and ζ. -/
lemma measurePreserving_shuffle_coords [SFinite ζ] : MeasurePreserving (fun (((t, x), w), y, z) ↦
  (((t, x ⊕ᵥ (w ⊕ᵥ y)) : A × (n ⊕ ι ⊕ n → A)), z)) ((volume.prod volume).prod (volume.prod ζ))
  (volume.prod ζ) := ⟨by fun_prop, ext_of_lintegral _ fun f _ ↦ by simp (disch :=
  with_unfolding_all fun_prop) [volume_eq_prod, ← measurePreserving_sumElim.lintegral_comp]⟩

namespace Filling

variable {A : _} [Field A] [StarRing A] {𝔰 : Shape} {T : 𝔰.Form A} {γ σ :
  T.G} {p q : ℕ → Aˣ} (hσ : σ ∈ GT 𝔰.ϱ)

attribute [local simp] entrywise weylOn FI.level frameGram diagonal toBlocks₂₂ toBlocks₁₁ mul_assoc

/-- Bruhat's big cell: over a field with involution and an element of trace 1, if all leading
minors of Z(γ) are nonzero, then γ = u⁻¹w_pσu' with u, u' in 𝖴, w_p a Weyl element of length
ϱ and σ in U(X₀ ⊕ Az).

Known result: Isotropic flags in unitary groups: Heisenberg radicals, big Bruhat cell, Haar
measure. -/
lemma exists_big_cell_decomp [IsHermUnit T.splitGram]
    [TraceOne A] (h : ∀ l, leadingMinor (T.frameGram γ) l ≠ 0) (j :
  Fin 𝔰.n := ⟨_, .refl⟩) : ∃ᵉ (u ∈ besselU) (u' ∈ besselU) (p) (σ ∈ GT j), γ =
  u⁻¹ * (weylElem j p * σ) * u' := j.induction ⟨1, by simp, 1, by simp⟩ (by
  rintro j ⟨u, a, u', a', p, σ, s, rfl⟩
  let x := Units.mk0 (σ.1 (eStar j) (inl j)) fun z ↦ h ⟨_, by lia⟩
    ((leadingMinor_frameGram_besselU_mul a a' _).trans (det_eq_zero_of_column_eq_zero ⊤ ((show ∀ c ≤
    j, T.frameGram _ c.castSucc j.castSucc = 0 by simp_all [le_iff_eq_or_lt, ↓(commute_weylElem
    s).eq, weylElem, floorGroup_apply s]) ⟨_, by lia⟩ ·.is_le)))
  have ⟨v, e⟩ := exists_col_eq_heisenbergElem _ _ s rfl x.3
  have ⟨q, k⟩ := exists_heisenbergElem_mem_floorGroup (inv_mul_mem_of_orbitPoint_eq s
    (mul_mem (heisenbergElem_mem_floorUnipotent j v).1 (floorWeyl_mem_floorGroup (c := ↑x)))
    (by simp_all [orbitPoint, floorWeyl, funext_iff, field]) :)
  exact ⟨_, mul_mem (inv_mem (unipotentBelow_le_besselU (heisenbergElem_mem_floorUnipotent j v).2))
    a, _, mul_mem (inv_mem (unipotentBelow_le_besselU (heisenbergElem_mem_floorUnipotent j
    q).2)) a', update p j x, _, k, by simp [weylElem_succ, weylElem_mul_left_comm,
    Subgroup.mem_inf.1 (heisenbergElem_mem_floorUnipotent ..)]⟩)

include hσ

lemma coe_weylElem_mul : (weylElem 𝔰.ϱ p * σ).1.1 =
  fromBlocks 0 (fromCols 0 (diagonal fun a ↦ (star (p a.1).1)⁻¹)) (fromRows 0 (diagonal (p ·.1)))
  (σ.1.1.toBlocks₂₂.toBlocks₁₁.fromBlocks 0 0 0) := by simp [weylElem, floorGroup_apply hσ]; lia

lemma frameGram_weylElem_mul : T.frameGram (weylElem 𝔰.ϱ p * σ).1 = diagonal (n :=
  Fin (𝔰.ϱ + 1)) (snoc (p · |>.1)
  (T.frameGram σ 𝔰.top 𝔰.top)) := by simp [↓coe_weylElem_mul hσ, ↓forall_fin_succ', eq_comm]

lemma big_cell_unique {v w : besselU × besselU} (e : v.1.1 * (weylElem 𝔰.ϱ p * σ) * v.2.1⁻¹ =
    w.1.1 * (weylElem 𝔰.ϱ q * σ) * w.2.1⁻¹) : (∀ a : Fin 𝔰.ϱ, p a = q a) ∧ v = w := by
  obtain ⟨⟨⟨u, hu⟩, u', hu'⟩, rfl⟩ := mul_left_surjective v w
  simp [↓eq_mul_inv_iff_mul_eq] at e
  have k b : (∀ i, u.1 i (eStar b) = ite (i = eStar b) 1 0) ∧ p b = q b := by
    replace e i := congr($e.1 i (inl b))
    simp [weylElem, Units.ext_iff, floorGroup_apply hσ, mem_besselU] at *
    simp [*] at e; grind [Units.ne_zero]
  cases eq_one_of_mem_besselU_of_fix hu (B := fromRows 0 (fromRows 0 1)) (by simp [k]) rfl
  simp_all [show weylElem 𝔰.ϱ q * σ = weylElem 𝔰.ϱ p * σ by ext; simp [weylElem, *]]
