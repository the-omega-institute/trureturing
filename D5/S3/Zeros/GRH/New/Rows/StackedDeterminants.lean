/- GID: D5/S3/Zeros/GRH/New/Rows/StackedDeterminants
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/StackedDeterminants
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.StackedDeterminants. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/StackedDeterminants.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Rows.SemiInvariantNorm
import D5.S3.Zeros.GRH.New.Rows.PartnerCut
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeCharacter.LevelModulus
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Records of the data and parameters used below, and names for their objects.

Dictionaries between two encodings of the same objects.

Set-up for this proof: Exchange of theta kernels with explicit determinant polynomials. A fixed
multiple of a theta kernel summed over a definite unitary group equals a kernel integrated over a
unitary group of no larger rank, with explicit determinant polynomials on both sides, times a
non-zero factor sized by Hecke L-values and the conductor. A block form moves the twist onto a
square block. Known: the first term identity between theta integrals of complementary
spaces, and determinant harmonics. See Gan–Qiu–Takeda, The regularized Siegel–Weil
formula, 2014 (after Kudla–Rallis, 1994; Ichino, 2004); Kashiwara–Vergne, On the Segal–Shale–Weil
representations and harmonic polynomials, 1978; Böcherer–Schulze-Pillot, Siegel modular forms and
theta series attached to quaternion algebras, 1991.

This file: Record of auxiliary dual pair: levels, characters, data, theta descent, Hecke test
polynomial. Record of the splitting of V, residue rings modulo squared level, generator idele.
Bordered determinant, trivial modulus, the carrier lift and the summing form. Products of bordered
determinants, their substitution law, and coordinates in a Schur basis. -/

noncomputable section

open Matrix NumberField ComplexConjugate Fintype Subgroup Space WeilData Sum MatMul
section

variable {E r n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [Fintype n] (S :
  LevelPlaces E) (u : r ↪ n)

/-- The finite group given by the product over the M-places w of GL_r of the residue field at w. -/
abbrev LevelPlaces.ChosenGL (r : Type) [Fintype r] := ∀ i, GL r (ResField (S.chosenPlace i))

-- Two spellings of one place are compared without unfolding its ring of integers.
attribute [local irreducible] IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers

/-- The homomorphism sending (g_w) in ∏_M GL_r(k_w) to the family equal to diag(g_w, 1) at the
places of M and 1 at those of Q. -/
def firstBlockHom : S.ChosenGL r →* ∀ i, GL n (ResField (S.placeAt i)) :=
  .pi (rec ((extendGL u).comp <| Pi.evalMonoidHom _ ·) fun _ ↦ 1)

/-- The group of families in ∏ GL_n(k_w) that at places of M fix the basis vectors indexed by u,
and at places of Q preserve the span of the other basis vectors. -/
def auxLevel : Subgroup (∀ i, GL n (ResField (S.placeAt i))) := pi .univ (rec
  (fun i ↦ MulAction.stabilizer _ (inclMatrix (ResField (S.placeAt (inl i))) u).col) fun _ ↦
  rangeParabolic u)

end

variable (E r n : Type) [Field E] [CMType E] [Fintype r] [Fintype n] (S : LevelPlaces E) (u : r ↪ n)
  [WeilData E]

/-- An auxiliary pair: places M and Q, a space W of rank r with numbered basis vectors, an
embedding of indices into n > r, weights k⁺, k⁻ given by the numbers `colsPlus`, `colsMinus` of
columns of each height, and a character μ whose tame part is
trivial off these places. -/
structure AuxPair extends LevelPlaces E where
  signs : r → _
  W : Space E r signs
  incl : r ↪ n
  ord : r → ℕ
  (colsPlus colsMinus : InfinitePlace E → ℕ → ℕ) μ : AutChar E
  (weight ψ) hasWeight : μ.HasWeight weight ψ
  tame_eq_one : ∀ w ∉ toLevelPlaces.places, ψ w = 1
  rank_lt : card r < card n

namespace AuxPair

attribute [instance] hasWeight

variable {E r n} (O : AuxPair E r n)

/-- The subgroup of K₀ of elements fixing the basis vectors indexed by `O.incl` modulo places of M
and preserving the span of the others modulo places of Q. -/
abbrev levelGroup := levelOf _ (auxLevel O.1 O.incl)

/-- The function on families X of n×r residue matrices: ∏_{w∈Q} ψ_w(det of the `O.incl`-rows of X_w)
if X_w is the inclusion matrix of `O.incl` at every w in M, else 0. -/
def resDetDatum (X : ∀ i, Matrix n r (ResField (O.placeAt i))) := if ∀ i, X (inl i) =
  inclMatrix _ O.incl then ∏ i, O.ψ _ ((X (inr i)).submatrix O.incl id).det else 0

/-- The weight datum (τ, i) ↦ k⁺(τ, i) + k⁻(τ, n − i) of forms on V = I_n, with n the rank of V. -/
abbrev κ := mixedWeight n O.colsPlus O.colsMinus

/-- For an infinite place τ, the integer minus the sum of k⁻(τ, i) over 1 ≤ i < n, completing
the weight of forms on V. -/
abbrev detExp τ := -((∑ i ∈ .Ico 1 (card n), O.colsMinus τ i :) : ℤ)

/-- The character g ↦ ∏_{w∈Q} ψ_w⁻¹(det g_{w,00}) of `auxLevel`, with ψ the tame part of μ and
g_{w,00} the block of g_w with rows and columns indexed by `O.incl`. -/
def auxLevelChar : auxLevel O.1 O.incl →* ℂ :=
  ⟨⟨fun g ↦ ∏ i, O.ψ⁻¹ _ ((g.1 (inr i)).1.submatrix O.incl O.incl).det,
  by bound⟩, fun g ↦ by simp [submatrix_mul_of_mem_rangeParabolic _ (g.2 (.inr _) ⟨⟩), -elim_inr]⟩

/-- The character of the level subgroup of the auxiliary pair O obtained by reducing modulo the
places of M and Q and applying `AuxPair.auxLevelChar`. -/
abbrev levelChar := O.auxLevelChar.comp (levelOf.reduction ..)

/-- Algebraic forms on V = I_n of weight (κ, e), with level fixing the `O.incl`-basis vectors mod M
and the span of the others mod Q, and character `AuxPair.auxLevelChar`. -/
abbrev FormV := O.LevelForm _ O.auxLevelChar O.κ O.detExp

/-- The representation of ∏_{w∈M} GL_r(k_w) on the vectors of π of level `O.levelGroup` and
character `O.levelChar`: g acts by ∏ ψ_w(det g_w) times π of a lift of diag(g, 1). -/
def chosenGLRep {W} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ _ W) :
  Representation ℂ (O.ChosenGL r) (levelSpace π _ O.levelChar) :=
  ⟨⟨fun g ↦ (∏ i, O.ψ _ (g i).1.det) • levelRep π _ (firstBlockHom _ O.incl) (by
  delta auxLevelChar firstBlockHom auxLevel LevelPlaces.placeAt Sum.elim
  simp [mem_pi, ↓mem_stabilizer_col_iff, inv_mul_eq_iff_eq_mul_of_invertible]
  simp_all [← Matrix.mul_assoc]) g, by simp⟩, by simp [← smul_mul_smul]⟩

/-- The representation of ∏_M GL_r(k_w) on the forms on V in which s acts by ∏ψ_w(det s_w) times
translation by diag(s,1). -/
def formAction : Representation ℂ (O.ChosenGL r) O.FormV := chosenGLRep ..

/-- The linear map from V_{k⁺} ⊗ V_{k⁻} (functions on pairs of indices) to polynomials sending a
⊗ b to the product of their Fock polynomials in the positive, resp. negative, variables. -/
def tensorPoly := Fintype.linearCombination ℂ fun p : WeylIndex n _ × WeylIndex n _ ↦
  letterPoly O.signs O.ord 1 O.colsPlus (Pi.single p.1 1) * letterPoly O.signs O.ord (-1)
  O.colsMinus (Pi.single p.2 1)

omit [WeilData E] in
@[simp] lemma tensorPoly_vecMulVec a b : O.tensorPoly (vecMulVec b a).vec =
  letterPoly O.signs O.ord 1 _ a * letterPoly O.signs O.ord (-1) _ b
  := by rw [pi_eq_sum_univ' a, pi_eq_sum_univ' b]; simp [tensorPoly, linearCombination_apply,
  sum_prod_type, sum_mul_sum, vecMulVec_apply, mul_smul]

/-- The linear map ξ ↦ P_ξ: apply the matrix `mixedCartan`, read the result as a polynomial
(`toPoly`), and substitute the Fock variables by `fockLetters`. -/
def harmonicPoly := O.tensorPoly ∘ₗ ((mixedCartan ..).1.map (↑)).mulVecLin

/-- The adelic character υ raised to the number r₋ of basis vectors of W with sign −1. -/
abbrev a : AutChar E := upsilonU1 ^ negCount O.signs

/-- The adelic character μ·υ^{⌊n/2⌋}, for μ the character of the auxiliary pair and n the rank
of V. -/
abbrev b := rankTwist O.μ n

/-- The theta kernel `pairThetaKer` of the pair (W, I_n) of the auxiliary pair O, with the
characters `AuxPair.a` and `AuxPair.b`. -/
abbrev pairThetaKernel := pairThetaKer O.W (stdSpace E n) O.a O.b

/-- The finite datum on Hom(W, I_n): the vector named from the vacuum by the function
`AuxPair.resDetDatum` of reductions at the places of M and Q. -/
def auxDatum := delta% vacuumDatum O.W (stdSpace ..) (O.levelModulus 2)
  (O.resDetDatum fun i ↦ ·.map (levelResidueAt i))

/-- The datum v_{P_ξ} ⊗ Υ in 𝒮(Hom(W, V)): the Fock vector of the polynomial P_ξ =
`AuxPair.harmonicPoly` ξ tensored with the finite datum `AuxPair.auxDatum`. -/
@[simp] abbrev fockDatum ξ := integrated _ (O.harmonicPoly ξ) O.auxDatum.1

/-- For g in U(W)(𝔸) and finite h in U(V), the linear form ξ ↦ conj θ(ω_{a,b}(g, h)(v_{P_ξ̄} ⊗
Υ)), with ξ̄ the complex conjugate of ξ. -/
def conjKernel g h := IsLinearMap.mk' (R := ℂ) (fun ξ ↦ conj
  (pairTheta _ _ O.a O.b (O.fockDatum (star ξ)) (g, 1, h))) (by constructor <;> simp [pairTheta])

/-- The linear map from forms Ξ on V to functions on U(W)(𝔸): θΞ(g) is the class sum, at the
level of O, of h ↦ `AuxPair.conjKernel` g h (Ξ(h)). -/
def θ : O.FormV →ₗ[ℂ] G E O.signs → ℂ := by use ⟨fun Ξ g ↦ stdClassSum O.levelGroup fun h ↦
  O.conjKernel g h (Ξ h), ?_⟩ <;> simp [apply_eq_evalForm, classSum, Finset.mul_sum, funext_iff]

variable {w : FinPlace E} (hw : _ ≠ w) (hS : w ∉ O.places.conjClosure)

/-- The operator H_w(X) = ∑_{i≤n} (−X)^i q^{i(i−1)/2} T_{w,i} on the forms on V, with q the norm
of w. -/
def heckePolyOnForms (X : ℂ) : Module.End ℂ O.FormV :=
  (heckePolyOp (algFormRep ..) hw X).restrict fun _ h ↦ have := (heckeSplit_mem_levelSpace
    hw · (LevelPlaces.LevelForm.mem_sphericalAt ⟨_, h⟩ hS) levelOf_le_Kf h)
  by simp [heckePolyOp, heckePolyEval, sum_mem, Submodule.smul_mem, *]

omit [WeilData E] in
lemma heckePolyOnForms_eq_smul {y p} (h : IsSphericalWith (rightRegular ..) hw p y.1.1) X :
  O.heckePolyOnForms hw hS X y = p X • y := Subtype.ext
  (Subtype.ext ((map_heckePolyOp (Submodule.subtype _) _).trans (h.2 X)))

/-- The difference of ranks t = n − r = dim V − dim W (truncated at zero) of the auxiliary pair. -/
abbrev rankDiff (_ : AuxPair E r n) := card n - card r

/-- The complex number q^{1−n+r/2} υ(ϖ_w)^{r−2r₋}, with q the norm of w, ϖ_w the chosen
uniformiser, r₋ the number of minus signs of W. -/
def testValue w := (O.a.frobValue r w * w.q ^ (O.rankDiff - 1))⁻¹

/-- At each split w with w, w̄ off the places, y is spherical with Hecke polynomial ∏_{l<n−r}(1
− q^l νT) · H_{z(w)}(q^{n−r} νT/ν'), ν, ν' the `AutChar.frobValue` of a, b in ranks r, n. -/
def Lifts (y : O.FormV) (z : _ → _) := ∀ w (hw : _ ≠ w), w ∉ O.places.conjClosure →
  IsSphericalWith (rightRegular ..) hw (fun T ↦ trivialHecke w.q O.rankDiff (O.a.frobValue r w *
  T) * heckePolyEval r w (z w) (w.q ^ O.rankDiff * O.a.frobValue r w / O.b.frobValue n w * T)) y.1.1

end AuxPair

open Ideal Modulus Set Gf LevelPlaces Quotient MvPolynomial Finset
section

variable {E r n N m a : Type} [Field E] [NumberField E] [IsCMField E] [Fintype r] [Fintype n]
  [Fintype N] [Fintype m] {S : LevelPlaces E}

/-- The modulus M², where M is the product of the primes of the family M of S. -/
abbrev LevelPlaces.chosenModulusSq (S : LevelPlaces E) := S.levelModulus 2 false

lemma map_block_eq_blockGL {R} [CommRing R] f ε (k : Kf E N) (l : Kf E m) : ∃ h, Kf.map (S := R) n f
  ⟨U.block ε (k, l), h⟩ = reindexGL ε (blockGL (Kf.map N f k, Kf.map m f l)) := by simp [mem_Kf,
  mem_Kf.1, Units.ext_iff, ← ext_iff, reindex_equiv ε, ← ZeroMemClass.zero_def]

lemma levelModulus_ideal_le : (S.levelModulus 2).ideal ≤ S.chosenModulusSq.ideal :=
  mul_mono_right (by simp)

lemma places_levelModulus_false {c} [NeZero c] : (S.levelModulus c false).places =
  Set.range S.chosenPlace := Set.ext (by simp [Modulus.places, levelModulus,
  IsPrime.pow_le_iff NeZero.out, _root_.prod_places_le_iff])

/-- The reduction homomorphism from the ring R₁ modulo M²Q to the ring R₀ modulo M². -/
abbrev reduceToR₀ : (S.levelModulus 2).ResRing →+* S.chosenModulusSq.ResRing :=
  factor levelModulus_ideal_le

lemma liftMod_mem_supportedOn (B : GL n S.chosenModulusSq.ResRing) : ↑(liftMod B) ∈ supportedOn n
  (Set.range S.chosenPlace) := by grind [places_levelModulus_false, liftMod]

end

variable {E r n : Type} (N m a : Type) [Field E] [CMType E] [Fintype r] [Fintype n] [Fintype N]
  [Fintype m] {S : LevelPlaces E} (O : AuxPair E r n)

lemma atPlace_twistPlace_eq_one {k} (h : k ∈ supportedOn n (Set.range S.chosenPlace)) i :
  k.atPlace (S.twistPlace i) = 1 := S.7.rec (by simp_all [eq_comm])

/-- A splitting N ⊕ m ≃ n carrying z to `O.incl`, embeddings of r and of a in N, and
`HasColumnsBelow` for k⁺ on N and k⁻ on m. -/
structure DividedSplitting (z : r ↪ m) extends ε : N ⊕ m ≃ n where
  ε_ι i : ε (inr (z i)) = O.incl i
  (fixedEmb : r ↪ N) (dividedEmb : a ↪ N) low : HasColumnsBelow n N O.colsPlus ∧
    HasColumnsBelow n m O.colsMinus

/-- The chosen integral idele generating the product M of the places `O.chosenPlace`, equal to 1 at
the places not dividing M. -/
def AuxPair.genIdele := (O.levelModulus 1 false).generator

/-- For an auxiliary pair O, the idele `AuxPair.genIdele` generating the modulus M, regarded as an
element of the ring Ô of integral finite adeles of E. -/
abbrev AuxPair.genIntAdele : Ô E := ⟨O.genIdele, (generator_spec _).1⟩

variable {N} {m} {a} {O} {z : r ↪ m} (V : DividedSplitting N m a O z)

lemma genIdele_apply_of_notMem {w} : w ∉ Set.range O.chosenPlace →
  O.genIdele.1 w = 1 := by simp_all [generator_spec, AuxPair.genIdele, places_levelModulus_false]

lemma reduction_levelModulus_eq_zero_iff {c x} : (O.levelModulus c false).reduction x = 0 ↔
  O.genIdele⁻¹.1 ^ c * x ∈ Ô E := by have := (O.levelModulus 1).2; simp_all [↓generator_spec, mem_Ô,
  v_inv, AuxPair.genIdele, valued_generator, levelModulus,
  FiniteMultiplicity.multiplicity_pow, FiniteMultiplicity.of_prime_left, (_ : FinPlace E).prime]

namespace DividedSplitting

/-- The image in the residue ring R₀ = O_E/M² of the idele `AuxPair.genIdele` generating M; it
depends on O only, not on V. -/
abbrev genResidue (_ : DividedSplitting N m a O z) := O.chosenModulusSq.reduction O.genIntAdele

lemma genResidue_smul_eq_iff {k c} (S : Matrix k c (O.levelModulus 2).ResRing) u :
    V.genResidue • S.map reduceToR₀ = V.genResidue • inclMatrix _ u ↔ ∀ i,
  S.map (levelResidueAt (inl i)) = inclMatrix _ u := by
  choose X e using fun a b ↦
    (add_left_surjective (inclMatrix _ u a b)).comp (reduction_surjective _) (S a b)
  simpa [inclMatrix, apply_ite (_ : _ →+* _), ← ext_iff, ← e, ← map_mul,
    reduction_levelModulus_eq_zero_iff, sq, mul_add, mul_assoc,
    -elim_inl] using! matrix_ext_modulusResidue O.isConjApart_chosenPlace.1 (x :=
    (of X).map (O.levelModulus 1 false).reduction) (y := 0)

end DividedSplitting

section

variable {Φ l n n' : Type} [Fintype l] [Fintype n'] (τ : Φ) (η : Matrix l n ℂ) (j : l ⊕ n' → n)
  (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]

/-- The determinant of the columns j of the complex matrix η stacked over the n′×n variable
matrix at τ. -/
def stackedDet := (((η.map C).fromRows (of fun a b ↦ X (τ, a, b))).submatrix id j).det

/-- The modulus of E whose ideal is the whole ring of integers. -/
abbrev unitModulus : Modulus E := ⟨⊤, top_ne_bot, (by simp [·.2.1])⟩

end

variable {Φ l n n' : Type} [Fintype l] [Fintype n'] (τ : Φ) (j : l ⊕ n' → n) (E : Type) [Field E]
  [CMType E] [WeilData E] (m : ℕ)

/-- The carrier: the theta lift of the constant 1 from U(I_m⁻) to the unitary group of signature
(2m, m), characters υ^m and 1, modulus 1, polynomial ∏_τ det(y⁻_τ)^{2m}. -/
def carrierForm := Space.lift (pairThetaKer (stdSpace ..).neg (signedSpace E (1 ⊕ᵥ -1 :
  Fin (2 * m) ⊕ Fin m → _)) (upsilonU1 ^ m) 1)
  (modDatum _ _ (unitModulus E) 1 (polyVector _ (∏ τ, letterMinor τ .inr id ^ (2 * m)))) fun _ ↦ 1

variable {E}

/-- The function Ξ°(h) on U(I_{n′})(𝔸_f): the class sum over U(I_m), level K₀, of the theta
kernel with characters c, 1, constant datum and polynomial 1. -/
def carrierXi c h :=
  stdClassSum (Kf E (Fin m)) (modKernelI (n' := n') (stdSpace ..) c 1 (unitModulus E) 1 1 ⟨1, ·⟩ h)

variable {Φ a L N : Type} [Fintype a] [Fintype N] [Fintype L] (e : a ⊕ N ≃ L) {p : ℕ} [Fintype Φ]
  {ι : Φ → Type} [∀ τ, Fintype (ι τ)] (M : ∀ τ, ι τ → _) (c : Φ → Matrix N N ℂ)
  (g : Φ → Matrix L L ℂ)

lemma exists_det_fromCols (e : L ≃ a ⊕ N) Z : ∃ (Y : Matrix a L ℂ) (γ : ℂ), (∀ X, ((fromCols X
  Z).submatrix id e).det = γ * (Y * X)ᵀ.det) ∧ ‖γ‖ ^ 2 * ‖(Y * Yᴴ).det‖ ≤ ‖(Zᴴ * Z).det‖ :=
  (isValuationPair_top.exists_mul_clear_cols Zᴴ (.trans .inr e.symm.toEmbedding)).elim fun V _ ↦ by
  let U := V.1.submatrix id e.symm
  have G W X := ((U.toCols₁.fromCols W).submatrix id e)ᴴ.det_mul ((fromCols X Z).submatrix id e)
  simp [↓det_conjTranspose, ← submatrix_mul, ↓det_transpose, mul_comm,
    (conjTranspose_injective (by aesop) : U.toCols₁ᴴ * Z = 0)] at *
  have H X := by simpa [← eq_div_iff, U, mul_div_right_comm] using (G U.toCols₂ X).symm
  exact ⟨_, _, H, by cases (by simpa [H, ← mul_assoc, U] using congr(‖$(G Z U.toCols₁)‖)) <;>
    simp [*, field]⟩

/-- The substitution x_τ ↦ c_τᵀ x_τ g_τᵀ on complex polynomials in the entries of N×L matrices
x_τ. -/
abbrev twoSidedSubst := aeval (R := ℂ) fun (τ, a, b) ↦ ∑ i, ∑ j,
  (c τ i a * g τ b j) • @X ℂ _ _ (τ, i, j)

/-- Rewrites a polynomial in matrix entries x_{τ,i,c} as a polynomial in the first p columns,
with coefficients polynomials in the entries of the columns indexed by L. -/
def inFirstCols := aeval (R := ℂ) fun (τ, a, b) ↦ (Sum.elim (X ⟨⟨τ, a⟩, @Fin.val p ·⟩)
  (C <| @X ℂ (Φ × N × L) _ ⟨τ, a, ·⟩) b : MatrixPoly (Σ _, N) _)

/-- The product over τ and k of the determinants of M_{τk} stacked over the variable matrix x_τ
(`stackedDet`), columns ordered by e. -/
def stackedDetProd := ∏ τ, ∏ k, stackedDet τ (M τ k) e

/-- The substitution x_τ ↦ c_τᵀ x_τ g_τᵀ sends the product over τ, k of the determinants of
M_{τk} g_τᵀ stacked over x_τ to ∏_τ (det c_τ · det g_τ)^{#ι(τ)} times the same product for
the matrices M_{τk}. -/
lemma twoSidedSubst_stackedDetProd : twoSidedSubst c g (stackedDetProd e fun τ k ↦ M τ k * (g τ)ᵀ) =
    (∏ τ, ((c τ).det * (g τ).det) ^ card (ι τ)) • stackedDetProd e M := funext (by
  simp [-prod_mul_distrib, stackedDetProd, stackedDet, ← prod_smul, ← card_univ, smul_prod,
    hom_bind₁, ↓RingHom.map_det]; congr!
  rw [show ∀ M, _ * det M = det (fromBlocks 1 0 0 _ᵀ * (M * _ᵀ.submatrix e e)) by simp [field]]
  congr 1 with ⟨⟩ <;> simp [mul_apply, mul_sum, ← submatrix_map]; ac_nf)

/-- The l-th coordinate of F in the first p columns: the Fock pairing of inFirstCols F with the
basis polynomial l of weight κ, divided by the hook number; a polynomial in the remaining
variables. -/
def firstColsCoord κ F l :=
  (hookNumber κ (rankAt N) : ℂ)⁻¹ • fockPairing _ (@inFirstCols Φ L N p F) (nablaBasis _ _ κ l)

lemma twoSidedSubst_firstColsCoord {F F'} {s : ℂ} (H : twoSidedSubst c (fromBlocks 1 0 0 <|
  g ·) F' = s • F) κ l : twoSidedSubst c g (∑ l', schur κ c l l' • firstColsCoord κ F' l') =
  s • firstColsCoord (p := p) κ F l := by
  obtain ⟨_, H⟩ :=
    map_fockPairing (twoSidedSubst c g).1 (inFirstCols F'), congr(firstColsCoord κ $H l)
  rw [firstColsCoord, comp_aeval_apply, (MvPolynomial.algHom_ext (by simp [inFirstCols, rowSubst,
    ← C_mul']) : aeval _ = ((rowSubst fun τ ↦ ((c τ).map C)ᵀ).restrictScalars ℂ).comp
    ((mapAlgHom (twoSidedSubst c g)).comp inFirstCols))] at H
  simp_all [fockPairing_rowSubst, schur_map, C_mul', firstColsCoord, smul_comm _ _⁻¹, smul_sum]
