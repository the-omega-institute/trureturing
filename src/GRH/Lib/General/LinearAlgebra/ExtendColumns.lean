import GRH.Lib.General.Groups.ValuationPair
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Poincaré series along a Bessel subgroup, unfolding; unipotent strong approximation (known
result; see Lib.Adelic.Poincare.BesselSubgroup).

This file: Kronecker products, parabolic, unitriangular, Levi, parahoric subgroups; Bessel subgroups
and frame of the space. Independent columns extend to an invertible matrix; standard inclusion is
injective. -/

noncomputable section

open Fin Finset LinearEquiv Matrix

/-- The shape of a hermitian space with ϱ hyperbolic planes, a summand X₀ and a vector z: the
number ϱ, a finite index set κ for X₀, and one index k₀ in κ. -/
structure Shape where (ϱ : ℕ) (κ : Type) [fintypeIndex : Fintype κ] (k₀ : κ)

attribute [instance] Shape.fintypeIndex

variable {R : Type*} [CommRing R] (𝔰 : Shape) {S} [Fintype S] {a b c : S → Type}
  (A : ∀ s, Matrix (a s) (b s) R) {R'} [CommRing R'] (φ : R →+* R') {μ}

/-- The Kronecker product of a finite family of matrices A s: the entry at (β, α) is the product
over s of the entries of A s at (β s, α s). -/
def kroneckerPi := of fun β α : ∀ _, _ ↦ ∏ s, A s (β s) (α s)

lemma kroneckerPi_mul [∀ s, Fintype (b s)] (B : ∀ s, Matrix (b s) (c s) R) : kroneckerPi (fun s ↦
  A s * B s) = kroneckerPi A * kroneckerPi B := (by simp [kroneckerPi, entrywise, prod_univ_sum])

@[simp] lemma kroneckerPi_one : @kroneckerPi R _ S _ a a (fun _ ↦ 1) = 1 :=
  Matrix.ext (by simp [kroneckerPi, prod_boole, funext_iff])

lemma kroneckerPi_map : kroneckerPi (A · |>.map φ) = (kroneckerPi A).map φ :=
  Matrix.ext (by simp [kroneckerPi])

/-- The additive character c ↦ exp(c − c̄) of ℂ, as a function. -/
def wave c := (c - starRingEnd ℂ c).exp

@[simp] lemma norm_wave c : ‖wave c‖ = 1 := by simp [wave]

/-- The index set made of ϱ indices, a middle set μ, and ϱ further indices, as a disjoint union. -/
abbrev SplitIndex ϱ (μ : Type) := Fin ϱ ⊕ μ ⊕ Fin ϱ

/-- The basis index set of V_ϱ = X₀ ⊕ ⟨z⟩: the indices κ of X₀ and one more for z. -/
abbrev Shape.MiddleIndex := 𝔰.κ ⊕ Unit

/-- The index set of the basis of the whole space: ϱ indices for the e_j, the basis indices of
V_ϱ, and ϱ indices for the e*_j. -/
abbrev Shape.BesselIndex := SplitIndex 𝔰.ϱ 𝔰.MiddleIndex

/-- The number n = ϱ + 1 of vectors in the frame (e_1, …, e_ϱ, z). -/
abbrev Shape.n := 𝔰.ϱ + 1

/-- The index, in the basis of the whole space, of the basis vector j of X₀. -/
abbrev Shape.indexX₀ (j : 𝔰.κ) : 𝔰.BesselIndex := .inr (.inl (.inl j))

/-- The index of z in the basis of the whole space. -/
abbrev Shape.z : 𝔰.BesselIndex := .inr (.inl (.inr ()))

/-- The last position in the frame (e_1, …, e_ϱ, z), that of z. -/
abbrev Shape.top := last 𝔰.ϱ

/-- The square matrices over R indexed by the basis of V_ϱ, serving as Gram matrices on V_ϱ. -/
abbrev Shape.Form R := Matrix 𝔰.MiddleIndex 𝔰.MiddleIndex R

/-- The rank k of X₀: the number of elements of κ. -/
abbrev Shape.k := Fintype.card 𝔰.κ

/-- The rank r of the whole space: the number of elements of the basis index set
`Shape.BesselIndex`. -/
abbrev Shape.r := Fintype.card 𝔰.BesselIndex

/-- The natural-number level of a basis index: i for index i of the first block, ϱ on the middle
block, 2ϱ−i for index i of the last block. -/
def FI.level {ϱ μ} : SplitIndex ϱ μ → ℕ := (↑) ⊕ᵥ ((fun _ ↦ ϱ) ⊕ᵥ (2 * ϱ - ·))

/-- The index of the basis vector e*_a, in the last of the three blocks. -/
@[match_pattern] abbrev eStar {ϱ} (a : Fin ϱ) : SplitIndex ϱ μ := .inr (.inr a)

/-- The Gram matrix of hyperbolic planes indexed by σ plus the form T: identity blocks pair the
two copies of σ, and T is the middle block. -/
abbrev hyperbolicGram σ (T : Matrix μ μ R) : Matrix (σ ⊕ μ ⊕ σ) (σ ⊕ μ ⊕ σ) R :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 1) (T.fromBlocks 0 0 0)

/-- The indices of the frame (f_1, …, f_n) = (e_1, …, e_ϱ, z) in the basis of the whole space. -/
def Shape.besselFrame : Fin (𝔰.ϱ + 1) → 𝔰.BesselIndex := snoc .inl 𝔰.z

variable {n : Type*} [Fintype n] {α : Type*} [LinearOrder α] (lev : n → α) {r : n → n → Prop}

/-- For N in R, the block diagonal Gram matrix on V_ϱ that is the identity on X₀ and −N at z. -/
def Shape.middleGram (N : R) : 𝔰.Form R := fromBlocks 1 0 0 (of fun _ _ ↦ -N)

/-- The Gram matrix of the whole space: ϱ hyperbolic planes, pairing e_j with e*_j by identity
blocks, together with T as the middle block on V_ϱ. -/
def Shape.Form.splitGram {𝔰 : Shape} (T : 𝔰.Form R) : Matrix 𝔰.BesselIndex 𝔰.BesselIndex R :=
  hyperbolicGram _ T

/-- The subgroup of GL_n(R) of matrices that are block upper triangular for the level function
lev. -/
def parabolic : Subgroup (GL n R) := ⟨⟨⟨{g | g.1.BlockTriangular lev}, .mul⟩,
  blockTriangular_one⟩, by simp_all [blockTriangular_inv_of_blockTriangular]⟩

/-- The homomorphism sending a block upper triangular invertible matrix to its diagonal block of
level a. -/
def blockHom a : parabolic (R := R) lev →* GL {i // lev i = a} R := .toHomUnits
    ⟨⟨(·.1.1.toSquareBlock _ a), (toBlock_one_self _).trans one_classical⟩, fun g h ↦ Matrix.ext
    fun i j ↦ sum_congr_set {x | _} _ _ (by tauto) (by grind [@g.2 i, @h.2 ·, not_lt])⟩

variable {lev : n → α} {𝔰 : Shape} {Z : Matrix n n R} (T : 𝔰.Form R) {T' : 𝔰.Form R'} [StarRing R']
  {k} (W : Type) [CommRing W] [IsLocalRing W] (τ : Fin k → ℕ) (ι : S ↪ n)

/-- For a relation r on indices with r i j implying r i k or r k j, the group of u in GL_n(R)
with u_ij = δ_ij whenever r i j. -/
def agreeWithOneOn (r : n → n → Prop) R [CommRing R] (h : ∀ i k j, r i j → r i k ∨ r k j := by
  grind) := Subgroup.ofDiv {u : GL n R | ∀ i j, r i j → u i j = (1 : Matrix ..) i j} ⟨1, by simp⟩
  fun x a y b i j e ↦ have := (parabolic (if r i · then 0 else 1)).2 (x := y) fun _ ↦ (by grind
    [one_apply_ne]); (sum_congr rfl fun k _ ↦ by grind [@this k j]).trans congr($y.mul_inv i j)

/-- The group of block upper triangular matrices all of whose diagonal blocks are the identity. -/
abbrev unitriangular (lev : n → α) R [CommRing R] := agreeWithOneOn (lev · ≥ lev ·) R

lemma mem_agreeWithOneOn {h x} : x ∈ agreeWithOneOn r R h ↔ ∀ a b : n, r a b → x a b =
  (1 : Matrix ..) a b := .rfl

attribute [simp] Subgroup.copy mem_agreeWithOneOn

/-- If d in GL_n(R), R a commutative ring, is block upper triangular for the levels lev and u is
block upper triangular with identity diagonal blocks, then d⁻¹ud also has identity diagonal
blocks and is block upper triangular. -/
lemma conj_mem_unitriangular {u d} (t : d.1.BlockTriangular lev) (a : u ∈ unitriangular lev R) :
    d⁻¹ * u * d ∈ unitriangular lev R := fun i j e ↦ by
  simp_rw [← d.inv_mul, ← congr($(d⁻¹.1.mul_one) * d.1), Units.val_mul, Matrix.mul_apply, sum_mul]
  congr! 2 with l _ k; grind [(parabolic _).2 t (j := k), @t l, a k, not_le]

lemma det_eq_one_of_unitriangular (h : ∀ a b, lev b ≤ lev a → Z a b = (1 : Matrix ..) a b) :
  Z.det = 1 := by simp [show Z.BlockTriangular lev by grind [BlockTriangular, one_apply_ne].det,
  show Z.toSquareBlock lev = 1 by aesop (add simp toSquareBlock_def)]

/-- The leading principal minor D_l of Z: the determinant of its upper-left l × l submatrix. -/
def leadingMinor {i} Z l := ((submatrix Z (castLE (@is_le i l)) (castLE l.is_le)).det : R)

/-- The diagonal matrix over R with entry p at the index k₀ and 1 at every other index. -/
abbrev Filling.scaleAt (p : R) (k₀ : μ) := diagonal (if · = k₀ then p else 1)

/-- The columns of γ at the frame indices, that is the image γf of the frame f = (e₁,…,e_ϱ,z). -/
abbrev frameImage (γ : Matrix 𝔰.BesselIndex _ R) := γ.submatrix id 𝔰.besselFrame

/-- For a square matrix γ on the whole space with Gram matrix J, the submatrix of Jγ on the
frame indices: Z(γ) = (h(f_j, γf_l)). -/
def Shape.Form.frameGram (γ : Matrix 𝔰.BesselIndex _ R) :=
  (T.splitGram * γ).submatrix 𝔰.besselFrame 𝔰.besselFrame

/-- The unitary group of the whole space. -/
abbrev Shape.Form.G [StarRing R] := U T.splitGram

/-- The square submatrix of γ on the rows and columns of the frame (e₁, …, e_ϱ, z). -/
def frameMatrix (γ : T'.G) := γ.1.1.submatrix 𝔰.besselFrame 𝔰.besselFrame

/-- The unipotent group 𝖴: the elements of the unitary group of the whole space that are block
upper triangular for the levels `FI.level`, with identity diagonal blocks. -/
def Shape.Form.besselU := (unitriangular FI.level R').subgroupOf T'.G

/-- The subgroup 𝖴⁰ of the elements of 𝖴 that fix every vector of the frame (e_1, …, e_ϱ, z). -/
def Shape.Form.besselU0 :=
  T'.besselU ⊓ (agreeWithOneOn (fun _ j ↦ j ∈ Set.range 𝔰.besselFrame) R').subgroupOf _

export Shape (besselFrame middleGram)

export Shape.Form (splitGram frameGram besselU besselU0)

/-- The Levi subgroup of a labelling τ of the indices: matrices in GL_k(W) whose (i,j) entry
vanishes whenever τ(i) ≠ τ(j). -/
def levi :=
  (agreeWithOneOn (τ · ≠ τ ·) W).copy {g | ∀ i j, τ i ≠ τ j → g i j = 0} (by ext; simp; grind)

/-- The parahoric subgroup of a labelling τ: matrices in GL_k(W), W local, whose (i,j) entry
lies in the maximal ideal whenever τ(i) < τ(j). -/
def parahoric :=
  (parabolic (OrderDual.toDual ∘ τ)).comap (GeneralLinearGroup.map (IsLocalRing.residue W))

lemma inclMatrix_mulVecLin_injective k [Field k] : (⇑(inclMatrix k ι).mulVecLin).Injective :=
  mulVec_injective_iff.2 ((linearIndependent_cols_of_isUnit isUnit_one).comp ι ι.2)

/-- A matrix b over a field with linearly independent columns extends to an invertible matrix u:
column ι(j) of u is column j of b. -/
lemma exists_GL_mul_inclMatrix {k} [Field k] {b} (h : (⇑b.mulVecLin).Injective) : ∃ u : GL n k,
  u.1 * inclMatrix k ι = b := (Submodule.exists_linearEquiv_restrict_eq
  ((ofInjective _ (inclMatrix_mulVecLin_injective ι k)).symm ≪≫ₗ
  ofInjective _ h)).imp' (.mk'' ·.toMatrix' (by simp [← coe_det])) (by simp_all [ext_iff_mulVec,
  ← mulVec_mulVec, ↓reindex_equiv (ofInjective ..), inclMatrix_mulVecLin_injective])
