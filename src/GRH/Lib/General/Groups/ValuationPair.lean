import GRH.Lib.General.LinearAlgebra.Base
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of group theory (textbook or folklore).

This file: Unitary group of a form over a star ring; integral, congruence subgroups; topology
instances. Abstract Heisenberg bicharacter, representation, vacuum function and group action with
cocycle. Twisted norm and its basic laws, tame cyclic actions, profinite rings. Ring pairs behaving
as valuation rings after patching along idempotents. -/

noncomputable section

attribute [-simp] Unitary.mul_star_self_of_mem

attribute [fun_prop] Continuous.mul_const

open Function Matrix MeasureTheory MulOpposite Set Notation Topology Units

attribute [simp] Matrix.one_apply conjTranspose_fromCols_eq_fromRows_conjTranspose
  conjTranspose_fromRows_eq_fromCols_conjTranspose fromCols_mul_fromRows fromCols_mul_fromBlocks
  fromBlocks_mul_fromRows fromCols_map fromRows_map fromBlocks_multiply fromBlocks_conjTranspose
  fromBlocks_map

/-- Strong induction along an integer weight w on a finite type: if P a follows from P b for all
b with w b < w a, then P holds everywhere. -/
lemma Finite.int_weight_induction {ι : Type*} [Finite ι] (w : ι → ℤ) {P : ι → Prop} :
  (∀ a, (∀ b, w b < w a → P b) → P a) → ∀ a, P a := (wellFounded_of_trans_of_irrefl _).fix

/-- Change of index along a bijection e: α → β. A universal or existential statement over β, and
a finite sum or product over β, may be rewritten over α by substituting e(x). -/
lemma reindex_equiv {F α β} [EquivLike F α β] (e : F) : (∀ {p : β → _}, (∀ y, p y) ↔ ∀ x, p (e x)) ∧
    (∀ {p : β → _}, (∃ y, p y) ↔ ∃ x, p (e x)) ∧ ∀ [Fintype α] [Fintype β] {M : Type} (f : β → M),
    (∀ [AddCommMonoid M], ∑ i, f i = ∑ i, f (e i)) ∧ ∀ [CommMonoid M], ∏ i, f i = ∏ i, f (e i) :=
  have b := EquivLike.bijective e
  ⟨b.2.forall, b.2.exists, fun _ ↦ by simp [b.sum_comp, b.prod_comp]⟩

/-- Matrices entry by entry: equations, products, products with vectors. -/
lemma entrywise.{u} {R} {m : Type u} : (∀ {n : Type u} {A B : Matrix m n R}, A = B ↔
    ∀ i j, A i j = B i j) ∧ ∀ [Fintype m] [Semiring R], (∀ v w : m → R, v ⬝ᵥ w = ∑ i, v i * w i) ∧
    ∀ {l : Type u} (A : Matrix l m R) i, (∀ v, (A *ᵥ v) i = ∑ j, A i j * v j) ∧
    ∀ {n : Type u} (B : Matrix m n R) k, (A * B) i k = ∑ j, A i j * B j k := by bound

variable {X Y} [TopologicalSpace X] [TopologicalSpace Y] {s K : Set X} {f : Y → X}

/-- If K is compact and s is closed in a topological space, then s ∩ K is compact as a subset of
the subspace s. -/
lemma IsCompact.preimage_val (k : IsCompact K) (h : IsClosed s := by infer_instance) :
    IsCompact (s ↓∩ K) := h.isProperMap_subtypeVal.isCompact_preimage k

/-- The image of a compact set under a continuous map is compact; continuity is found by
automation unless supplied. -/
lemma IsCompact.image_auto (h : IsCompact s) f (c : Continuous f := by fun_prop) :
    IsCompact (f '' s : Set Y) := h.image c

/-- The preimage of an open set under a continuous map is open; continuity is found by
automation unless supplied. -/
lemma IsOpen.preimage_of_continuous (h : IsOpen s) (c : Continuous f := by fun_prop) :
  IsOpen (f ⁻¹' s) := c.1 _ h

/-- The preimage of a closed set under a continuous map is closed; continuity is found by
automation unless supplied. -/
lemma IsClosed.preimage_of_continuous (h : IsClosed s) (c : Continuous f := by fun_prop) :
  IsClosed (f ⁻¹' s) := h.preimage c

variable {E} [NormedAddCommGroup E] [MeasurableSpace X] [OpensMeasurableSpace X] {ν : Measure X}
  [IsFiniteMeasureOnCompacts ν] {f : X → E}

/-- A continuous function f from a Hausdorff space to a normed group is integrable on a compact
set K, for a measure ν finite on compact sets. Continuity is proved automatically by
default. -/
lemma IsCompact.integrableOn [T2Space X] (k : IsCompact K) (f : X → E)
    (c : Continuous f := by fun_prop) : IntegrableOn f K ν := c.continuousOn.integrableOn_compact k

/-- A continuous function f of compact support with values in a normed group is integrable, for
a measure ν finite on compact sets. Continuity is proved automatically by default. -/
lemma HasCompactSupport.integrable (k : HasCompactSupport f) (c : Continuous f := by fun_prop) :
    Integrable f ν := c.integrable_of_hasCompactSupport k

/-- A continuous function from a compact space X to a normed group is integrable for every finite
Borel measure ν on X. -/
lemma integrable_of_compactSpace [CompactSpace X] (c : Continuous f := by
  fun_prop (disch := simp)) : Integrable f ν := HasCompactSupport.integrable (.of_compactSpace _) c

scoped[MatMul] attribute [simp] Matrix.mul_assoc Matrix.mul_add Matrix.add_mul Matrix.sub_mul
  Matrix.mul_sub

variable {m n R S : Type*}

section

variable [Countable m] [Countable n] [Monoid R] [TopologicalSpace R] [ContinuousMul R]
  [MeasurableSpace R] [BorelSpace R]

instance : MeasurableSpace (Matrix m n R) := .pi

variable [SecondCountableTopology R] [Finite m] [Finite n] [Countable R] [LocallyCompactSpace R] in
deriving instance Countable, LocallyCompactSpace, BorelSpace for Matrix m n R

variable [PolishSpace R]

instance : PolishSpace Rˣ := have : PolishSpace Rᵐᵒᵖ := opEquiv.symm.polishSpace_induced
  isClosedEmbedding_embedProduct.polishSpace

deriving instance PolishSpace for Matrix m n R

instance : BorelSpace Rˣ := by
  borelize Rˣ; use (continuous_val.measurableEmbedding val_injective).comap_eq

end

instance [Fintype m] [Fintype n] [MeasureSpace R] : MeasureSpace (Matrix m n R) := .pi

/-- For a map u: m → n of index sets, the n×m matrix whose j-th column is the standard basis
vector e_{u(j)}. -/
def inclMatrix R [Zero R] [One R] (u : m → n) := (1 : Matrix n n R).submatrix id u

/-- The complex diagonal matrix whose diagonal entries are the signs s_i = ±1. -/
def signMatrix (s : n → ℤˣ) := diagonal (s · : n → ℂ)

@[simp] lemma signMatrix_one : @signMatrix n 1 = 1 := by simp [signMatrix]

variable [Fintype n] [CommRing R] [CommRing S] {O : Subring R} (ε : n → ℤˣ)

lemma mul_inclMatrix {l} (M : Matrix l n R) (u : m → n) : M * inclMatrix R u = M.submatrix id u :=
  mul_submatrix_one 1 ..

lemma signMatrix_mul_self : signMatrix ε * signMatrix ε = 1 := by simp [signMatrix, ← Int.cast_mul]

/-- The homomorphism sending a family of units of R to the diagonal matrix in GL_n(R) with these
entries. -/
def diagGL : (n → Rˣ) →* GL n R :=
  (Units.map (diagonalRingHom n R).1).comp MulEquiv.piUnits.symm.toMonoidHom

@[simp] lemma coe_diagGL (t : n → Rˣ) : (diagGL t).1 = diagonal fun i ↦ ↑(t i) := rfl

/-- The transpose of g, as an element of GL_n(R). -/
@[simps] def transposeGL (g : GL n R) : GL n R := by use gᵀ, g⁻¹.1ᵀ <;> simp [← transpose_mul]

/-- For distinct indices i, j and a in R, the element 1 + aE_{ij} of GL_n(R), with inverse 1 −
aE_{ij}. -/
@[simps] def transvectionGL {i j : n} (h : i ≠ j) (a : R) : GL n R := by
  use transvection i j a, transvection i j (-a) <;> simp [transvection_mul_transvection_same, h]

/-- For a subring O of R, the subgroup GL_n(O) of GL_n(R): matrices with entries in O whose
inverse has entries in O. -/
def intGL n [Fintype n] (O : Subring R) := (GeneralLinearGroup.map (n := n) O.subtype).range

lemma mem_intGL {g} : g ∈ intGL n O ↔ (∀ i j, g i j ∈ O) ∧ ∀ i j, g⁻¹ i j ∈ O := ⟨(·.choose_spec
  ▸ by simp [← map_inv]), fun ⟨a, b⟩ ↦ ⟨.mkOfMulEqOne (⟨_, a · ·⟩) (⟨_, b · ·⟩)
  (map_injective O.subtype_injective (Matrix.map_mul.trans (g.3.trans (by simp)))), rfl⟩⟩

/-- For a ring homomorphism f: O → S, the homomorphism GL_n(O) → GL_n(S) applying f to each
entry. -/
def intGL.map (f : O →+* S) : intGL n O →* GL n S := (GeneralLinearGroup.map f).comp (.toHomUnits
  (by use! fun k ↦ of (⟨_, (mem_intGL.1 k.2).1 · ·⟩) <;> aesop (add simp mul_apply)))

variable {f : O →+* S} {k : intGL n O}

@[simp] lemma intGL.map_apply i j : map f k i j = f ⟨_, (mem_intGL.1 k.2).1 i j⟩ := rfl

lemma intGL.map_eq_one : map f k = 1 ↔ ∀ i j, f (⟨_, (mem_intGL.1 k.2).1 i j⟩ - ⟨_, (mem_intGL.1
  (one_mem _)).1 i j⟩) = 0 := by simp [GeneralLinearGroup.ext_iff, ← (map f).map_one, -map_one]

@[simp] lemma mem_span_singleton_iff_exists_mul {a x} : x ∈ O ∙ a ↔ ∃ y ∈ O, x = a * y := by
  simp [Submodule.mem_span_singleton, O.smul_def, mul_comm, eq_comm]

/-- The group of matrices in GL_n(O) whose rows e(i) are congruent to those of 1 modulo M; for e
the identity, the principal congruence subgroup of level M. -/
def congruenceGL (M : Submodule O R) (e : m → n) := Subgroup.ofDiv
  {g ∈ intGL n O | ∀ i j, (g.1 - 1) (e i) j ∈ M} ⟨1, by simp⟩ fun g ⟨a, b⟩ k ⟨c, d⟩ ↦ ⟨div_mem a c,
  fun i j ↦ (congrFun₂ (by simp [sub_mul] : (k.2ᵀ * (_ - _)ᵀ)ᵀ = _) ..).subst
  (M.sum_smul_mem (⟨_, (mem_intGL.1 c).2 · j⟩) fun l _ ↦ sub_mem (b ..) (d ..))⟩

variable [StarRing R] [StarRing S] (J : Matrix n n R) (f : R →+* S)

lemma map_conjTranspose_mul_mul (hf : ∀ x, f (star x) = star (f x)) (z B : Matrix n n R) :
    (zᴴ * B * z).map f = (z.map f)ᴴ * B.map f * z.map f := by simp [conjTranspose_map _ hf]

lemma gram_mul {c} [Fintype m] (X : Matrix n m R) (J : Matrix n n R) (Y : Matrix m c R) :
    (X * Y)ᴴ * J * (X * Y) = Yᴴ * (Xᴴ * J * X) * Y := by simp [Matrix.mul_assoc]

lemma gram_mul_of_gram_eq {J J' J''} {x y : GL n R} (h : x.1ᴴ * J * x = J') (k : y.1ᴴ * J' * y =
  J'') : (x * y).1ᴴ * J * (x * y).1 = J'' := k ▸ h ▸ gram_mul ..

lemma gram_inv_of_gram_eq {J J'} {x : GL n R} (h : x.1ᴴ * J * x = J') : x⁻¹.1ᴴ * J' * x⁻¹ = J :=
  by simp [← h, ← gram_mul]

/-- The unitary group U(J) of a matrix J over a commutative ring with involution: the g in
GL_n(R) with gᴴJg = J. -/
def U : Subgroup (GL n R) :=
  ⟨⟨⟨{g | _ᴴ * J * g.1 = J}, gram_mul_of_gram_eq⟩, by simp⟩, gram_inv_of_gram_eq⟩

/-- For a vector of signs ε, the unitary group U(J) of the diagonal matrix J=diag(ε). -/
abbrev USign := U (signMatrix ε)

variable {J} (g : U J) (hf : ∀ x, f (star x) = star (f x) := by simp)

lemma mem_U {g} : g ∈ U J ↔ g.1ᴴ * J * g = J := .rfl

instance : CoeOut (U J) (Matrix n n R) := ⟨(·.1)⟩

namespace U

lemma form_mul_inv_eq : J * g⁻¹ = g.1.1ᴴ * J := (mul_inv_eq_iff_eq_mul _).2 g.2.symm

lemma coe_inv (hJ : J * J = 1) (g : U J) : g⁻¹ = J * g.1.1ᴴ * J := by grind [form_mul_inv_eq]

/-- For g in the unitary group of the identity matrix over a commutative ring R with involution,
the matrix of g⁻¹ is the conjugate transpose gᴴ. -/
lemma inv_val_eq_conjTranspose (g : U (1 : Matrix n n R)) : g⁻¹.1.1 =
  gᴴ := by grind [form_mul_inv_eq]

lemma gram_invariant {a b} (A : Matrix n a R) (B : Matrix n b R) : (g.1.1 * A)ᴴ * J * (g.1.1 * B) =
  Aᴴ * J * B := by simp [Matrix.mul_assoc, ← form_mul_inv_eq]

lemma form_mulVec_mulVec x y : star (g *ᵥ x) ⬝ᵥ J *ᵥ g *ᵥ y = star x ⬝ᵥ J *ᵥ y := by
  simp [star_mulVec, ↓dotProduct_mulVec, mem_U.1]

/-- For invertible J and a matrix M with MᴴJM = J, the element of U(J) with matrix M. -/
@[simps! coe_val] def of (hJ : IsUnit J) M (h : Mᴴ * J * M = J) : U J :=
  ⟨(isUnit_of_mul_isUnit_right (h ▸ hJ)).unit, h⟩

/-- For a ring homomorphism f commuting with the involutions and carrying J to J', the
homomorphism U(J) → U(J') applying f to each entry. -/
def map {J J'} (h : Matrix.map J f = J' := by simp) : U (n := n) J →* U J' := .codRestrict
  ((GeneralLinearGroup.map f).comp (U J).subtype) _ fun g ↦
  h ▸ by erw [mem_U, ← map_conjTranspose_mul_mul f hf, g.2]

variable {f}

lemma mem_range_map (inj : Injective f) (hJ : IsUnit J) {J'} (h : J.map f = J') {g M}
  (e : M.map f = ↑g) : ∃ k, k.1.1 = M ∧ map f hf h k = g := ⟨of hJ _
  (map_injective inj (by grind [map_conjTranspose_mul_mul, mem_U])), rfl, Subtype.ext (ext e)⟩

/-- For x in GL_n(R) with xᴴJx = J', the isomorphism U(J') ≅ U(J), g ↦ x g x⁻¹. -/
@[simps! apply_coe symm_apply_coe] def conj (x : GL n R) {J J'} (h : x.1ᴴ * J * x = J') :
  U J' ≃* U J := by use! fun g ↦ ⟨_, gram_mul_of_gram_eq (gram_mul_of_gram_eq h g.2)
  (gram_inv_of_gram_eq h)⟩, fun g ↦ ⟨_, gram_mul_of_gram_eq
  (gram_mul_of_gram_eq (gram_inv_of_gram_eq h) g.2) h⟩ <;> intro <;> simp [mul_assoc]

/-- For J with unit determinant, the determinant as a homomorphism from U(J) to the group of
elements u of R with uū = 1. -/
def det (hJ : IsUnit J.det) : U J →* unitary R := .mk' (fun g ↦ ⟨_, by
  simpa [unitary, mul_comm, mul_assoc, hJ.mul_eq_left] using congr($(g.2).det)⟩) (by simp)

lemma continuous_map [TopologicalSpace R] [TopologicalSpace S] (hf : Continuous f := by fun_prop)
    {h J' h'} : Continuous (map f h h' : U J → U J') := .subtype_mk (by simp; fun_prop) _

end U

variable [TopologicalSpace R] [IsTopologicalRing R] [ContinuousStar R] (J : Matrix n n R)

lemma isClosed_U [T2Space R] : IsClosed (SetLike.coe (U J)) := by apply isClosed_eq <;> fun_prop

instance [T2Space R] [LocallyCompactSpace R] : LocallyCompactSpace (U J) :=
  (isClosed_U J).locallyCompactSpace

instance [PolishSpace R] : PolishSpace (U J) := (isClosed_U J).polishSpace

variable {J} [T2Space R]

omit [IsTopologicalRing R] [ContinuousStar R] in
lemma isClosed_of_entries_eq_one {S : Subgroup (U J)} {p : _ → _ → Prop} (h : ∀ {g}, g ∈ S ↔ ∀ i j,
  p i j → g.1.1 i j = (1 : Matrix ..) i j) : @IsClosed (U J) _ S := isClosed_of_closure_subset
  fun _ ↦ (h.2 fun _ _ e ↦ EqOn.closure (fun _ ↦ (h.1 · _ _ e)) (by fun_prop) (by fun_prop) ·)

/-- For invertible J over a Hausdorff topological commutative ring with continuous involution,
the map sending an element of U(J) to its matrix is a closed embedding. -/
lemma U.isClosedEmbedding_mat (hJ : IsUnit J) : IsClosedEmbedding (·.1.1 : U J → _) :=
  .of_comp (isEmbedding_graph (f := (op <| J⁻¹ * ·ᴴ * J)) (by fun_prop)) (by
    simpa [← isUnit_iff_isUnit_det, *, ↓comp_def, ← form_mul_inv_eq, mul_assoc] using
      isClosedEmbedding_embedProduct.comp (isClosed_U _).isClosedEmbedding_subtypeVal)

lemma U_one_mem_unitaryGroup (h : U 1) :
  h.1.1 ∈ unitaryGroup n ℂ := by simp [unitary, star, ← U.inv_val_eq_conjTranspose]

instance : CompactSpace (U (1 : Matrix n n ℂ)) := ⟨(eq_univ_of_forall (by simp [mem_matrix,
  entry_norm_bound_of_unitary, U_one_mem_unitaryGroup])).subst
  ((U.isClosedEmbedding_mat isUnit_one).isCompact_preimage (isCompact_closedBall 0 1).matrix)⟩

instance : CompactSpace (U (@signMatrix n 1)) := signMatrix_one.substr inferInstance

instance U.borelSpace {J : Matrix n n ℂ} : BorelSpace (U J) := inferInstance

variable {A} [Fintype m] [AddGroup A] [TopologicalSpace A] [MeasureSpace A]
  [(@volume A _).IsAddHaarMeasure] [SigmaFinite (@volume A _)] [MeasurableAdd A]

instance : SigmaFinite (@volume (Matrix m n A) _) := Measure.pi.sigmaFinite _

instance isAddHaarMeasure_pi : (@volume (n → A) _).IsAddHaarMeasure where

instance : (@volume (Matrix m n A) _).IsAddHaarMeasure := isAddHaarMeasure_pi

scoped[Sgn] attribute [simp] Int.units_ne_iff_eq_neg

open ComplexConjugate
variable (W) [AddCommGroup W] [TopologicalSpace W]

/-- A continuous function β on W × W, W a topological abelian group, with values of modulus one,
multiplicative in each variable, and β(x,x) = 1. -/
structure Heisenberg where
  β : W → W → ℂ
  add_left x x' y : β (x + x') y = β x y * β x' y
  add_right x y y' : β x (y + y') = β x y * β x y'
  self_eq_one x : β x x = 1
  norm_eq_one x y : ‖β x y‖ = 1
  cont : Continuous fun p : W × W ↦ β p.1 p.2

namespace Heisenberg

variable {W} [MeasurableSpace W] (H) (μ : outParam (Measure W)) (e : outParam (W → ℂ))

/-- A family of linear isometries ρ(x), x in W, of a complex normed space, strongly continuous,
with ρ(0) = 1 and ρ(x)ρ(y) = β(x,y)ρ(x+y). -/
structure Rep X [NormedAddCommGroup X] [NormedSpace ℂ X] where
  ρ : W → X →L[ℂ] X
  mul x y v : ρ x (ρ y v) = β H x y • ρ (x + y) v
  norm_map x v : ‖ρ x v‖ = ‖v‖
  cont : Continuous fun p : W × X ↦ ρ p.1 p.2

/-- The function e: W → ℂ is a vacuum for β and μ: continuous, integrable, even, real-valued,
e(0) = 1, and ∫ e(z)e(x−y−z)β(z,y)β(z+y,x) dμ(z) = e(y)e(x). -/
class IsVacuum where
  cont : Continuous e
  apply_zero : e 0 = 1
  apply_neg x : e (-x) = e x
  conj_apply x : conj (e x) = e x
  twisted_conv y x : ∫ z, e z * (β H z y * (β H (z + y) x * e (x - (z + y)))) ∂μ = e y * e x
  integrable : Integrable e μ

/-- The action of G on W preserves β and μ, and a continuous multiplier Δ: G → ℂ has Δ(1) = 1,
Δ(g⁻¹) = conj Δ(g), Δ(g)Δ(h)Δ((gh)⁻¹) ∬ e(hx)e(ghy)β(x,y)e(x+y) = c(g,h). -/
structure MultiplierAction G [Group G] [TopologicalSpace G] [DistribMulAction G W] (c : G →
  G → ℂ := 1) where
  beta_smul (g : G) (x y : W) : β H (g • x) (g • y) = β H x y
  measurePreserving (g : G) : MeasurePreserving (g • ·) μ μ
  Δ : G → ℂ
  continuous_delta : Continuous Δ
  Δ_one : Δ 1 = 1
  Δ_inv g : Δ g⁻¹ = conj (Δ g)
  cocycle g h : Δ g * Δ h * Δ (g * h)⁻¹ *
    ∫ x, ∫ y, e (h • x) * e ((g * h) • y) * β H x y * e (x + y) ∂μ ∂μ = c g h

end Heisenberg

variable {M} [Monoid M] {R n : _} [CommRing R] [Fintype n] [StarRing R] {G} [Group G] {K : Subgroup
  G}

/-- The twisted norm δ · τ(δ) ⋯ τ^{p−1}(δ) of δ in the monoid M, for a map τ : M → M. -/
@[local simp] def twistedNorm (τ : M → M) p δ := ((List.range p).map (τ^[·] δ)).prod

/-- σ^p = 1, p > 0, σ(m) = m, some e has ∑_{i<p} σ^i(e) ≡ 1 mod m, and for 0 < i < p every prime
ideal modulo which σ^i is the identity contains m. -/
def IsTameAtLevel (σ : R →+* R) p m := σ m = m ∧ (∃ e, m ∣ ∑ i ∈ .range p, (σ ^ i) e - 1)
    ∧ σ ^ p = 1 ∧ 0 < p ∧ ∀ i ∈ Set.Ioo 0 p, ∀ P [Ideal.IsPrime P], (∀ x, (σ ^ i) x - x ∈ P) → m ∈ P

/-- Every sequence in R has a unique limit along the hyperfilter on ℕ, for the topology given by
the ideals MR, M a nonzero natural number. -/
def IsProfiniteRing R [CommRing R] := ∀ x : ℕ → R, ∃! L, ∀ M ≠ 0, ∀ᶠ N in .hyperfilter ℕ,
  M.cast ∣ x N - L

/-- The endomorphism of the unitary group {g : gᴴg = 1} over R given by applying entrywise a
ring endomorphism σ commuting with the involution. -/
abbrev U.mapEnd {σ} hσ := (map σ hσ : Monoid.End (U (1 : Matrix n n R)))

lemma twistedNorm_conj (τ : G →* G) p {y} (h : τ^[p] y = y) δ : twistedNorm τ p (y⁻¹ * δ * τ y) =
  y⁻¹ * twistedNorm τ p δ *
  y := congr(_ * $h) ▸ p.rec (by simp) (by simp_all [List.range_add, mul_assoc])

lemma twistedNorm_mem τ p (h : ∀ k ∈ K, τ k ∈ K) : ∀ {δ}, δ ∈ K →
  twistedNorm τ p δ ∈ K := by induction p with aesop

lemma map_twistedNorm {M Γ} [Monoid M] [Monoid Γ] {σ τ} (e : Γ →* M) (h : ∀ δ, e (τ δ) =
  σ (e δ)) p : ∀ δ, e (twistedNorm τ p δ) = twistedNorm σ p (e δ) := by induction p with simp_all

lemma twistedNorm_succ' (τ : M →* M) p δ : twistedNorm τ (p + 1) δ =
  δ * τ (twistedNorm τ p δ) := by simp [↓map_twistedNorm τ]

variable {A : _} [CommRing A] (R : Subring A) {n : _} [Fintype n] {e : A} (he : IsIdempotentElem e)

/-- For all a, b in A there is an idempotent e of the subring R such that ea lies in Rb and (1 −
e)b lies in Ra. -/
abbrev IsValuationPair := ∀ a b : A, ∃ e : R, e.1 * e = e ∧ R ∙ a ⊔ R ∙ b ≤ R ∙ (a - e * (a - b))

lemma isValuationPair_valuationSubring {F} [Field F] (O : ValuationSubring F) :
  IsValuationPair O.1 := (by simp; grind [O.mem_or_inv_mem <| · / ·, O.zero_mem, O.one_mem])

lemma IsValuationPair.top : IsValuationPair R →
  @IsValuationPair R _ ⊤ := by simp_all [Subtype.ext_iff, IsValuationPair]

attribute [local simp] add_mul mul_add smul_smul mul_sub sub_mul

/-- For an idempotent e of the commutative ring A, the endomorphism g ↦ e·g + (1−e)·1 of GL_n(A). -/
def cutGL : GL n A →* GL n A := Units.map ⟨⟨(e • · + (1 - e) • 1), by simp⟩, by simp [he.eq]⟩

/-- For a self-adjoint idempotent e of A, the endomorphism g ↦ e·g + (1−e)·1 of the unitary group of
the identity form, the g in GL_n(A) with gᴴg = 1. -/
def U.cutAt [StarRing A] (hs : star e = e) := ((cutGL (n := n) he).comp (U 1).subtype).codRestrict
  (U 1) (by simp_all [mem_U, cutGL, he.eq])
