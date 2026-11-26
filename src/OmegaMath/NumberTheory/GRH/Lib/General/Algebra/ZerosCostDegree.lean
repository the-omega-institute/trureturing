import OmegaMath.NumberTheory.GRH.Lib.General.LinearAlgebra.ColumnLattices
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Known result: Combinatorial Nullstellensatz with multiplicity. Over any field, the grid is
replaced by a set of at least ∏κ(u) points at which each u^κ(u) agrees with a polynomial of lower
weighted degree, where u has weight 1/κ(u). A nonzero polynomial vanishing to order d at all the
points then has a monomial of weighted degree at least d. Source: Alon, Combinatorial
Nullstellensatz (1999); Ball–Serra, Punctured combinatorial Nullstellensätze (2009).

Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character (known
result; see Lib.GLn.SchurModule.MinorBasis).

This file: Schur modules, Weyl lattices, Fischer product, kernel, Gram form, symmetric powers:
definitions. High-order vanishing at all points of a complete intersection forces large weighted
degree. -/

noncomputable section

open Classical MvPolynomial Module Finset Matrix Nat Sigma Finsupp Fintype Function Submodule Ideal
variable {σ Φ m R : Type} [CommRing R] [Fintype Φ] (n n' : Φ → Type) [∀ τ, Fintype
  (n τ)] [∀ τ, Fintype (n' τ)] (c : m → Φ) (N e : Φ → ℕ) (κ : Φ → ℕ → ℕ) (τ) (z : ∀ _, Matrix _ _ R)

/-- For row colouring c, arrays b and y, the array yb with (a,j) entry Σ_{i≤j} y(a,i)
b(c(a),i,j), using the upper triangular part of b for a's colour. -/
def borelMul (b y : _ → R) (x : m × ℕ) := ∑ i ∈ range (x.2 + 1), y (x.1, i) * b (c x.1, i, x.2)

/-- For bounds N and column multiplicities κ, the finitely supported weight whose value at
(τ,i), columns numbered from 0, is the sum of κ_τ(h) over i<h<N_τ. -/
def diagramWeight := ∑ τ, ∑ h ∈ range (N τ), κ τ h • ∑ i ∈ range h, single (τ, i) 1

variable (m R)

/-- The polynomial ring over R in variables y_{a,i} indexed by a row a in m and a column i in ℕ. -/
abbrev MatrixPoly := MvPolynomial (m × ℕ) R

/-- The type of fillings assigning, for each height h<N, to each of k(h) columns an h-tuple of
elements of m, with no ordering condition. -/
abbrev Tableau N (k : ℕ → ℕ) := ∀ h : Fin N, Fin (k h) → Fin h → m

variable {m} {h N : ℕ} {k}

/-- The bilinear pairing of a polynomial P with a formal power series F giving P(∂)F(0), the sum
over exponents d of d! times both d-th coefficients. -/
def jet : MvPolynomial σ R →ₗ[R] MvPowerSeries σ R →ₗ[R] R :=
  (basisMonomials ..).constr ℕ fun d ↦ (d.prod fun _ ↦ (·!)) • MvPowerSeries.coeff d

/-- The bilinear form on polynomials ⟨P,Q⟩ = P(∂)Q(0), for which monomials are orthogonal and
⟨x^d,x^d⟩ = d!. -/
@[local simp] def fockPairing : LinearMap.BilinForm R (MvPolynomial σ R) :=
  (jet R).compl₂ (coeToMvPowerSeries.algHom R).toLinearMap

/-- For an h-tuple I of rows, the polynomial determinant of the h×h matrix of variables in rows
I and the first h columns. -/
def minor (I : Fin h → m) : MatrixPoly m R := det (of (X ⟨I ·, ·⟩))

/-- For a row colouring c and weight l, the module of Borel semi-invariants: polynomials f with
f(yβ) = ∏β_{τ,ii}^{l(τ,i)} f(y) for generic upper triangular matrices β_τ, one per colour. -/
def nabla (l : Φ × ℕ →₀ ℕ) : Submodule R (MatrixPoly m R) := (aeval (borelMul c (C ∘ @X R _ _)
  X)).toLinearMap.eqLocus ((l.prod fun p ↦ (@X R _ _ (p.1, p.2, p.2) ^ ·)) • (aeval X).toLinearMap)

/-- For a filling T and a row map e, the product over columns of T of the minors `minor`
whose rows are the e-images of the column's entries. -/
def tableauPoly e (T : Tableau σ N k) := ∏ h, ∏ j, @minor m R _ _ (e ∘ T h j)

/-- For x in ℂ^N and l : ℕ → ℕ, the alternant det(x_i^{l(N−1−j)+j}), 0 ≤ i, j < N, if l(N) = 0,
and zero otherwise. -/
def PolyRep.alternant (x : Fin N → ℂ) (l : ℕ → ℕ) :=
  ite (l N = 0) (det (of fun i j ↦ x i ^ (l j.rev + j))) 0

/-- The minor products of s form a basis of the span of all minor products over every commutative
ring, and Σ_{T∈s} x^T times a_0(x) equals a_l(x), l(j) = Σ_{j<h<N} k(h), a the alternant
`PolyRep.alternant`. -/
def IsStdTableauSet (s : Finset (Tableau m N k)) :=
  (∀ R [CommRing R], let v (T : Tableau m N k) := tableauPoly R id T
  LinearIndepOn R v s ∧ ∀ T, v T ∈ Submodule.span R (v '' s)) ∧ ∀ M (e : Fin M ≃ m) x, (∑ T ∈ s,
  ∏ h, ∏ j, ∏ a, x (T h j a)) * PolyRep.alternant (x ∘ e) 0 =
  PolyRep.alternant (x ∘ e) (∑ h ∈ Ioo · N, k h)

/-- The finite type of fillings belonging to the chosen standard set for rows m and column data
N,k. -/
def StdTableau m N k := {T // T ∈ epsilon (@IsStdTableauSet m N k)} deriving Fintype

/-- A type is read as the constant family of types. -/
instance : Coe Type (Φ → Type) := ⟨fun n _ ↦ n⟩

/-- The number of elements of the finite row type n_τ at the place τ. -/
abbrev rankAt := card (n τ)

/-- The fixed numbering of the rows at the place τ: a chosen bijection from n_τ to {0, …, |n_τ|
− 1}. -/
abbrev PolyRep.rowPos := equivFin (n τ)

/-- The type of families choosing, for each place τ, a filling in the chosen standard set with
rows n_τ, heights below |n_τ| and multiplicities κ_τ. -/
abbrev WeylIndexFam := ∀ τ, StdTableau (n τ) (rankAt n τ) (κ τ)

/-- The type of families of chosen standard fillings over the places, in the case where the row
type is the same finite type n at every place. -/
abbrev WeylIndex n [Fintype n] κ := @WeylIndexFam Φ n _ κ

/-- The module of Borel semi-invariant polynomials in rows (τ,a), coloured by τ, whose weight is
the partition tuple built from κ using heights below |n_τ|. -/
abbrev nablaFam := nabla R (@Sigma.fst _ n) (diagramWeight (rankAt n) κ)

/-- For a family i of chosen standard fillings, the polynomial that is the product over places τ
of the minor product of i_τ in the rows of block τ. -/
def nablaBasis (i : WeylIndexFam n κ) := ∏ τ, tableauPoly (m := Σ τ, n τ) R (Sigma.mk τ) (i τ).1

/-- The polynomial product over places τ and h<N_τ of the leading principal h×h minor of the
variables in block τ raised to κ_τ(h). -/
def highestPoly (N : Φ → ℕ) := ∏ τ,
  tableauPoly R (Sigma.mk τ) (fun h _ ↦ Fin.castLE h.is_le' : Tableau _ (N τ) (κ τ))

/-- The product over places τ of the determinant of the variables in all rows of block τ (fixed
enumeration) and first |n_τ| columns, raised to e_τ. -/
def detPow := ∏ τ, minor (m := Σ τ, n τ) R (⟨τ, (equivFin (n τ)).symm ·⟩) ^ e τ

/-- The generic n_τ × n_τ matrix at the place τ: its (a, b) entry is the variable X_{τ,a,b} of
the polynomial ring over R in the entries at all places. -/
def PolyRep.genericMatrixAt := of (@X R (Σ τ, n τ × n τ) _ ⟨τ, ·, ·⟩)

/-- The hook number: the integer ⟨f,f⟩ = f(∂)f(0), where f is the product of the leading
principal h×h minors raised to κ_τ(h), h<N_τ. -/
def hookNumber N := fockPairing ℤ (highestPoly ℤ κ N) (highestPoly ℤ κ N)

/-- The natural number κ_τ(|n_τ|) if |n_τ| < |n'_τ|, and 0 otherwise, as a function of the place
τ. -/
def schurDetExp := ite (rankAt n τ < rankAt n' τ) (κ τ (rankAt n τ)) 0

/-- The condition, at every place τ, that |n_τ| ≤ |n'_τ| and κ_τ(h) = 0 for |n_τ| < h < |n'_τ|. -/
@[grind] def FitsRanks := ∀ τ, rankAt n τ ≤ rankAt n' τ ∧ ∀ h ∈ Ioo (rankAt n τ) (rankAt n' τ),
  κ τ h = 0

variable {R n n'} (y : (Σ τ, n τ) × ℕ → R) (α a) (f g : MvPolynomial σ R) (i F)

/-- For matrices z_τ of size n'_τ×n_τ, the algebra homomorphism f ↦ f(zy) sending variable
y_{(τ,b),i} to Σ_a z_τ(b,a) y_{(τ,a),i}. -/
def rowSubst : MatrixPoly (Σ τ, n' τ) R →ₐ[R] MatrixPoly (Σ τ, n τ) R := aeval fun x ↦ ∑ a,
  z _ x.1.2 a • X (⟨_, a⟩, x.2)

/-- For maps e_τ from rows to natural numbers, the array over R whose entry at row (τ,a), column
i is 1 if e_τ(a)=i and 0 otherwise. -/
def permArray (e : ∀ τ, n τ → ℕ) (x : (Σ τ, n τ) × ℕ) := @ite R (e _ x.1.2 = x.2) _ 1 0

/-- A numbering of the rows is read as a map to `ℕ`. -/
instance : CoeOut (∀ τ, n τ ≃ Fin (rankAt n τ)) (∀ τ, n τ → ℕ) := ⟨(· · ·)⟩

/-- The R-linear map sending a coordinate vector ξ to the polynomial Σ_i ξ_i b_i, where the b_i
are the basis products of minors `nablaBasis`. -/
abbrev PolyRep.nablaCombination := Fintype.linearCombination R (nablaBasis R n κ)

/-- The ring homomorphism from polynomials in variables (τ,a,b) to R evaluating each variable at the
matrix entry z_τ(a,b). -/
abbrev PolyRep.evalMat := eval (R := R) fun x : Σ τ, n τ × n τ ↦ z _ x.2.1 x.2.2

omit [Fintype Φ] [∀ τ, Fintype (n τ)] in
@[simp] lemma PolyRep.genericMatrixAt_map_evalMat τ : (genericMatrixAt R n τ).map (evalMat z) =
  z τ := by ext; simp [genericMatrixAt]

@[local simp↓ low] lemma jet_eq_sum : jet R f F = ∑ m ∈ f.support, f.coeff m * (m.prod
    fun _ ↦ (↑·!)) * F.coeff m := by simp [jet, Basis.constr_apply]; ac_rfl

lemma jet_monomial : jet R (monomial α a) F = a * (α.prod fun _ : σ ↦ (↑·!)) * F.coeff α := by aesop

@[local simp↓] lemma jet_mul_X : jet R (f * X i) F = jet R f (F.pderiv i) := by
  simp +singlePass [← mul_prod_erase' _ i, F.coeff_pderiv]; simp!; grind

/-- The Fock pairing of the monomial a·y^α with a polynomial g over R equals α! · a ·
(coefficient of y^α in g), where α! is the product of the factorials of the exponents. -/
lemma fockPairing_monomial : fockPairing R (monomial α a) g =
  α.prod (fun _ ↦ (·!)) * (a * g.coeff α) := by simp; grind

lemma fockPairing_C : fockPairing R (C a) g = a * constantCoeff g := by aesop

lemma fockPairing_mul_X : fockPairing R (f * X i) g =
  fockPairing R f (pderiv i g) := by simp [MvPowerSeries.pderiv_coe]

/-- The Schur matrix S_κ(z) of matrices z_τ of size n'_τ×n_τ: row i holds chosen coordinates of
b'_i(zy) in the family b_j(y)·∏_τ det(y_τ)^{d_τ}, d given by `schurDetExp`. -/
def schur := of (invFun (Fintype.linearCombination R
  (nablaBasis R n κ · * detPow R n (schurDetExp n n' κ))) ∘ rowSubst z ∘ nablaBasis R n' κ)

/-- For a family i of fillings, a place τ and a row a, the number of entries of the filling i_τ
equal to a. -/
def tableauWeight {κ} (i : WeylIndexFam n κ) τ a := ∑ h, ∑ j, #{s | (i τ).1 h j s = a}

variable (n) [Fintype m] (z : Matrix m σ R) {R'} [CommRing R'] [Fintype σ]

/-- For an array y over R, the polynomial x ↦ f(yᵀx), taken blockwise with the first |n_τ|
columns of y, f the product of leading minors `highestPoly`. -/
def weylKernel := rowSubst (fun τ ↦ of fun i ↦ (y ⟨⟨τ, ·⟩, i.1⟩)) (highestPoly R κ (rankAt n))

/-- The Gram matrix: the integer matrix G of coefficients of the kernel f(yᵀx) in the
minor-product basis, so that the kernel is Σ G_ij b_i(x) b_j(y). -/
def weylGram := of (invFun (PolyRep.nablaCombination (R := ℤ) κ) ∘ invFun
  (PolyRep.nablaCombination κ) (weylKernel n κ X))

/-- The linear map from coordinate vectors ξ to polynomials sending ξ to Σ_i (Gξ)_i b_i, with G
the Gram matrix and b_i the basis minor products. -/
def toPoly := PolyRep.nablaCombination κ ∘ₗ ((weylGram n κ).map (@Int.cast R _)).mulVecLin

/-- For an array y over R, the vector whose i-th entry is the value b_i(y) of the basis minor
product at y. -/
def weylEval := (nablaBasis R n κ i).eval y

/-- For an m×σ matrix z over R, the R-algebra map from polynomials in variables indexed by σ to
those indexed by m sending X_b to ∑_t z_{tb} X_t. -/
def linSubst : MvPolynomial σ R →ₐ[R] MvPolynomial m R := aeval (∑ t, z t · • X t)

lemma fockPairing_linSubst f : ∀ g, fockPairing R f (linSubst z g) = fockPairing R (linSubst zᵀ f)
  g := by have ⦃f i⦄ : (linSubst z f).pderiv i = ∑ a, z i a • linSubst z (f.pderiv a) <;> apply
  f.induction_on <;> simp_all [linSubst, fockPairing_C, fockPairing_mul_X,
  @Finset.mul_sum σ, -fockPairing, hom_bind₁, apply_ite]

variable {n} (a : ℕ) (ψ : R →+* R') (A B : Matrix σ σ R)

/-- The integer Gram matrix `weylGram` of Weyl's lattice for the ranks n and column counts κ,
with its entries mapped to the ring R. -/
abbrev weylGramOver {κ} := (weylGram n κ).map (@Int.cast R _)

variable (σ) in abbrev Monomials := ↥((@univ σ _).finsuppAntidiag a)

lemma linSubst_eq_bind₁ : linSubst A =
  bind₁ Aᵀ.toMvPolynomial := by simp [linSubst, X, smul_monomial]; rfl

attribute [local simp ←] ext_iff toMvPolynomial_mul C_mul' degree_eq_sum

@[simp] lemma linSubst_one : linSubst 1 f = f := by simp [linSubst_eq_bind₁]

lemma linSubst_mul : linSubst (A * B) f =
  linSubst A (linSubst B f) := by simp [linSubst_eq_bind₁, bind₁_bind₁]

lemma map_linSubst : MvPolynomial.map ψ (linSubst A f) =
  linSubst (A.map ψ) (MvPolynomial.map ψ f) := by simp [linSubst, map_bind₁]

variable {a f} {S} [Fintype S] (α : Monomials σ a)

lemma Monomials.degree_eq : α.1.degree = a := by aesop

lemma Monomials.isHomogeneous_linSubst : (linSubst A (monomial α 1)).IsHomogeneous a := by
  simpa [linSubst_eq_bind₁] using!
    (isHomogeneous_monomial 1 α.degree_eq).aeval _ Aᵀ.toMvPolynomial_isHomogeneous

lemma sum_monomials_eq_of_isHomogeneous (hf : f.IsHomogeneous a) : ∑ β : Monomials σ a,
  f.coeff β • monomial β 1 = f := by
  ext; simpa [coeff_sum, eq_comm, sum_attach _ fun β ↦ ite _ (f.coeff β) 0] using hf.coeff_eq_zero

/-- The a-th symmetric power: the homomorphism sending a square matrix A to the matrix, in the
monomial basis, of `linSubst` A on forms of degree a. -/
def symPowMatrix a := MonoidHom.mk ⟨fun A ↦ @of _ _ R fun β α : Monomials σ a ↦
  (linSubst A (monomial α.1 1)).coeff β.1, by simp [eq_comm, one_apply]⟩ fun A
  B ↦ by ext; simpa [linSubst_mul, @mul_comm R, coeff_sum, Matrix.mul_apply] using congr((linSubst
  A $(sum_monomials_eq_of_isHomogeneous (Monomials.isHomogeneous_linSubst ..))).coeff _).symm

/-- For a family β of degree-a exponent vectors indexed by s, the single exponent vector on
variables (b,s) taking the value β_s(b). -/
def exponentOf : (S → Monomials σ a) ↪ σ × S →₀ ℕ :=
  ⟨fun β ↦ equivFunOnFinite.symm fun x ↦ (β x.2).1 x.1, id fun _ _ h ↦ by ext; congrm $h (_, _)⟩

/-- For a coefficient function F on families β of degree-a exponents, the polynomial ∑_β F(β)
x^β in the variables (b,s). -/
def polyOfCoeffs := ∑ β : S → Monomials σ a, monomial (R := R) (exponentOf β) ∘ₗ .proj β

lemma symPowMatrix_map : symPowMatrix a (A.map ψ) = (symPowMatrix a A).map ψ := by
  simp [symPowMatrix, ← coeff_map, map_linSubst]

/-- Give the variable u the cost 1/κ_u. Take at least ∏κ_u distinct points at which each u^{κ_u}
agrees with a polynomial whose monomials cost less than 1. Then every f ≠ 0 vanishing to
order d at these points has a monomial of cost at least d.

Known result: Combinatorial Nullstellensatz with multiplicity. -/
lemma exists_le_cost_of_vanishing {K ι S : Type} [Field K] [Fintype ι] [Fintype S] (κ : ι → ℕ)
    (κ0 : ∀ u, 0 < κ u) (z : S → _) (inj : z.Injective) (card : ∏ u, κ u ≤ Fintype.card S)
    (hz : ∀ u, ∃ g : MvPolynomial ι K, (∀ α ∈ g.support, weight (κ · : ι → ℝ)⁻¹ α < 1) ∧
      ∀ t, MvPolynomial.eval (z t) g = z t u ^ κ u) (d : ℕ) f (f0 : f ≠ 0) (hf : ∀ t,
    f ∈ vanishingIdeal K {z t} ^ d) : ∃ α ∈ f.support, d ≤ weight (κ · : ι → ℝ)⁻¹ α := by
  choose g hg h0 using hz
  have ⟨Γ, hΓ⟩ := (@finite_of_degree_lt ι _ d).exists_finset_coe
  -- the jets of order below `d` at the points
  let T (w : ι → K) := bind₁ (X + C ∘ w)
  let J := LinearMap.pi fun y : S × Γ ↦ lcoeff K y.2 ∘ₗ (T (z y.1)).toLinearMap
  have hJ {p} y h : J p y = 0 := (mem_pow_idealOfVars_iff' ..).1 (le_comap_pow (T _) d
    (pow_right_mono (fun p ↦ by simpa [T, degree_eq_zero_iff, hom_bind₁, ← constantCoeff_eq] using
    (mem_pow_idealOfVars_iff' 1 (T _ p)).2) (I := vanishingIdeal K {z y.1}) d h)) _ (hΓ.le y.2.2)
  -- the products `b α γ` = x^α ∏_u (x_u^κ_u − g_u)^γ_u
  let b α γ := monomial α 1 * bind₁ (fun u ↦ X u ^ κ u - g u) (monomial γ 1)
  let v (x : univ.finsupp (range ∘ κ) × Γ) := b x.1 x.2
  have lin {N p} h : p ∈ N := span_le.2 (Set.forall_mem_image.2 h)
    ((basisMonomials ι K).mem_span_image.2 (le_refl ↑p.support))
  -- those with `α < κ` span, triangularly for the cost; they vanish to order `|γ|`
  have div M : ∀ α γ, (d ≤ γ.degree + weight (κ · : ι → ℝ)⁻¹ α → J.ker ≤ M) → b α γ ∈ span K (.range
      v) ⊔ M := (wellQuasiOrdered_le.of_surjective (s := weight (κ · : ι → ℝ)⁻¹ ⁻¹'o LE.le) ⟨id, fun
      e ↦ by simp [weight_eq_sum]; grw [e _]⟩ (⟨·, rfl⟩)).wellFounded.fix fun α ih γ hγ ↦ by
    by_cases! e : ∀ u, α u < κ u
    exact (lt_or_ge _ d).elim (mem_sup_left <| subset_span ⟨⟨⟨_, by simpa [mem_finsupp_iff]⟩,
      γ, hΓ.ge ·⟩, rfl⟩) fun o ↦ mem_sup_right (hγ (by grw [o, weight_eq_sum]; simp; positivity)
      (funext (hJ · (mul_mem_left _ _ (le_comap_pow _ d (pow_right_mono (by simp [Ideal.span_le,
      h0]) d ((mem_pow_idealOfVars_iff ..).2 (by simpa))))))))
    obtain ⟨u, β, rfl⟩ := e.imp fun _ ↦ exists_add_of_le ∘ single_le_iff.2
    simp [weight, κ0, ne_of_gt] at *
    convert add_mem (ih β ?_ ?_ (Finsupp.single u 1 + γ) ?_)
      (@lin (.comap (.mulRight K (b β γ)) (_ ⊔ M))
      (g u) fun δ e ↦ by simp [b]; apply ih <;> grind) <;> simp [b, monomial_single_add] <;> grind
  -- those with `|γ| < d` are as many as the jets, so they are independent modulo the kernel
  refine f0.imp_symm fun H ↦ (range_ker_disjoint (v := v)
    (linearIndependent_of_top_le_span_of_card_le_finrank (fun y _ ↦ ?_) (by simp; bound))).le_bot
    ⟨lin fun α e ↦ by simpa [b, mt (⟨α, e, ·⟩) H] using div ⊥ α 0, funext (hJ · (hf _))⟩
  -- Chinese remainders: the jets at the points are arbitrary
  have ⟨p, h⟩ := exists_forall_sub_mem_ideal (I := (vanishingIdeal K {z ·} ^ d)) (fun t t' ↦
    .pow ∘ isCoprime_of_isMaximal ∘ mt fun h ↦ inj (by ext u; simpa using h.ge (by simp :
    X u - C (z t' u) ∈ _))) fun t ↦ T (-z t) (∑ γ, monomial γ.1 (y (t, γ)))
  rw [Set.range_comp, span_image, ← show J p = y by
    ext x; simpa [J, T, bind₁_bind₁, coeff_sum] using hJ x (h _)]
  exact (comap_map_eq ..).ge (lin fun α _ ↦ by simpa [b] using div J.ker α 0)
