/- GID: D5/S3/Zeros/GRH/Lib/Adelic/Witt/SpaceOperations
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Adelic/Witt/SpaceOperations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Adelic.Witt.SpaceOperations. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Adelic/Witt/SpaceOperations.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Hilbert90.UnitaryHilbert90
import D5.S3.Zeros.GRH.Lib.DiscreteSeries.Bruhat.EichlerMaps
import D5.S3.Zeros.GRH.Lib.Adelic.Adeles.AdelicModulus
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa
decomposition (known result; see Lib.SiegelWeil.SingularForms.AdaptedHom).

Part of: Adelic points of unitary groups, levels and Haar measures (known result; see
Lib.Adelic.Reduction.MinkowskiSecond).

This file: Witt's extension theorem for primitive frames over integral finite adeles, unramified CM
case. Unimodular hermitian forms over integral adeles have orthonormal bases; real units are norms.
Orthogonal sums, negatives, reindexing, moving of framed hermitian spaces and their adelic
groups. -/

noncomputable section

section

open Matrix NumberField MatMul InnerProductSpace
variable {E n k : Type*} [Field E] [NumberField E] [IsCMField E] [Fintype n]
  {R : Type _} [CommRing R] {O : Subring R} {X : Matrix n k R}

lemma IsPrimitiveMatrix.exists_map_subtype_eq : IsPrimitiveMatrix O X → ∃ Y, HasLeftInv Y ∧
  .map Y O.subtype = X | ⟨a, _, b, e⟩ => ⟨(⟨_, a · ·⟩),
  ⟨(⟨_, b · ·⟩), map_injective O.subtype_injective (Matrix.map_mul.trans (by simpa))⟩, rfl⟩

lemma isPrimitiveMatrix_iff {g} : IsPrimitiveMatrix O g ↔ ∃ x ∈ intGL n O, x.1 = g :=
  ⟨fun ⟨a, _, b, e⟩ ↦ ⟨(.mkOfMulEqOne _ _
  e)⁻¹, mem_intGL.2 ⟨a, b⟩, rfl⟩, fun ⟨x, h, e⟩ ↦ e ▸ (mem_intGL.1 h).imp_right (⟨_, ·, x.4⟩)⟩

variable [Fintype k] [StablyUnram E] {X Y : Matrix n k (𝔸f E)}

lemma exists_isUnit_sub_star_Ohat : ∃ z : Ô E, IsUnit (z - star z) := ‹StablyUnram
  E›.exists_isUnit_sub_star.imp' (algebraMap ..) fun _ ↦ Eq.subst (by aesop) ∘ .map (algebraMap ..)

/-- Witt's theorem over Ô, for stably unramified CM E: two n × k matrices X, Y over Ô with left
inverses over Ô and XᴴX = YᴴY satisfy g X = Y for some g in GL_n(Ô) with gᴴg = 1.

Known result: Witt's extension theorem for hermitian forms; unimodular lattices; Iwasawa
decomposition. -/
lemma witt_Ô (hX : IsPrimitiveMatrix (Ô E) X) (hY : IsPrimitiveMatrix (Ô E) Y) (h : Xᴴ * X =
  Yᴴ * Y) : ∃ g ∈ Kf E n, g.1.1 * X = Y := by
  have A a x y : ∃ c : Matrix n n (Ô E), IsUnit (a + (1 - a * x) * c * (1 - y * a)) := by
    obtain ⟨p, _, q, _, d, rfl⟩ := isValuationPair_Ohat.top.smith_normal_form a
    let e := diagonal (Subtype.mk _ <| idem_mem_Ô {w | (reduceAt w ∘ d) · = 0})
    refine ⟨p * e * q, isUnit_of_mul_isUnit_left (y := q⁻¹ * (1 + e * q * y * p * diagonal d))
      (isUnit_of_mul_isUnit_right (x := (1 + diagonal d * q * x * p * e) * p⁻¹) ?_)⟩
    simp [isUnit_iff_isUnit_det, eq_iff_le_not_lt, mem_Ô.1, ← reduceAt_eq_zero,
      mul_assoc, add_assoc, sub_eq_add_neg, RingHom.map_det, ↓map_add, ↓map_neg, e, ← mul_assoc
      (diagonal _) (diagonal _), Finset.prod_eq_zero_iff, ite_eq_right_iff.2, idem_mul_self]
    grind
  obtain ⟨⟨X, ⟨L, l⟩, ⟨⟩⟩, Y, ⟨M, m⟩, ⟨⟩⟩ := hX.exists_map_subtype_eq, hY.exists_map_subtype_eq
  have : Xᴴ * X = Yᴴ * Y := by ext; simp_all [← ext_iff, mul_apply]
  have ⟨c, a, e⟩ := A (Y * L + Mᴴ * Xᴴ * (1 - X * L)) (Lᴴ * Yᴴ) (X * M)
  refine (exists_fixed_orthonormal_frame isProfiniteRing_intAdeles isTameAtLevel_one rfl
    exists_isUnit_sub_star_Ohat.choose_spec ?_ (star a * a).isUnit (by
    simp [star]) rfl).elim fun T ⟨_, _, _, t⟩ ↦ ⟨U.map _ ?_ ?_ (U.of isUnit_one (a.1 * T) (by simpa
    [star] using t)), ⟨_, rfl⟩, Matrix.map_mul.symm.trans ?_⟩ <;> simp [*, star, -Matrix.mul_sub]

lemma witt_Ohat_of_orthonormal (h : Xᴴ * (1 : Matrix n n (𝔸f E)) * X = 1) (h' : Yᴴ * (1 :
  Matrix n n (𝔸f E)) * Y = 1) (hX : IsIntMatrix (Ô E) X) (hY : IsIntMatrix (Ô E) Y) : ∃ g ∈ Kf E n,
  g.1.1 * X = Y := by apply witt_Ô ⟨_, _, _, h⟩ ⟨_, _, _, h'⟩ <;> simp_all [star_mem_Ô, IsIntMatrix]

/-- Gram–Schmidt: for a complex n × k matrix X with a left inverse there is an invertible b,
block upper triangular for wt, such that X b has orthonormal columns. -/
lemma exists_orthonormal_mul {n k α} [Fintype n] [Fintype k] [LinearOrder α]
    (wt : k → α) {X : Matrix n k ℂ} : HasLeftInv X → ∃ b : GL k ℂ, b.1.BlockTriangular wt ∧
      (X * b.1)ᴴ * (X * b.1) = 1 | ⟨L, _⟩ => let B := PiLp.basisFun 2 ℂ k
  let := LinearOrder.lift' (toLex ∘ Function.prod wt embeddingToCardinal) (by aesop_cat)
  let := (monoEquivOfFin k rfl).symm.locallyFiniteOrderBot
  let := NormedAddCommGroup.induced _ _ X.toEuclideanLin (.of_comp (f := (L *ᵥ ·.1)) (by aesop_cat))
  let := induced X.toEuclideanLin
  have := (transpose_mul ..).symm.trans (gram_eq_one_iff_orthonormal.2
    (gramSchmidtNormed_orthonormal B.linearIndependent))
  ⟨(.mkOfMulEqOne _ _ ((Matrix.mul_assoc ..).trans this))⁻¹, fun _ _ _ ↦
    mul_eq_zero_of_right _ (gramSchmidt_triangular (by tauto) B), this⟩

variable {E n : Type _} [Field E] [NumberField E] [Fintype n] [IsCMField E] [StablyUnram E]

/-- For stably unramified CM E, a hermitian square matrix b with entries in Ô and a left inverse
over Ô satisfies kᴴ b k = 1 for some k in GL_n(Ô). -/
lemma exists_orthonormal_Ô {b} : IsUnimodular (Ô E) b → ∃ k ∈ intGL n (Ô E), k.1ᴴ * b * k.1 = 1
  | ⟨h, _, ⟨x, rfl⟩, c⟩ => c ▸ (exists_fixed_orthonormal_frame isProfiniteRing_intAdeles
    isTameAtLevel_one rfl exists_isUnit_sub_star_Ohat.choose_spec (by
    simp) x.isUnit (by ext; simp_all [← ext_iff]) rfl).elim fun _ ⟨_, _, _, e⟩ ↦ ⟨_, ⟨
    (.mkOfMulEqOne _ _ e)⁻¹, rfl⟩, by erw [← map_conjTranspose_mul_mul, e] <;> simp⟩

/-- For stably unramified CM E, every conjugation-invariant finite adele u that is a local unit
at every finite place is the norm x̄ x of a unit x of Ô. -/
lemma exists_norm_eq_Ô {u} (hu : star u = u) (h : ∀ w, Valued.v (u w) = 1) : ∃ x : (Ô E)ˣ,
  star x.1.1 * x = u := by simpa [Finset.range, Subtype.ext_iff] using! ((IsTameAtLevel.of_skew
  (by bound) exists_isUnit_sub_star_Ohat.choose_spec (starRingEnd _).map_one).exists_norm
  (.inr isProfiniteRing_intAdeles) (isUnit_Ô (x := ⟨u, by grind [mem_Ô]⟩).2 h) (Subtype.ext hu))

end

open Matrix Sgn

attribute [local simp] Prod.ext_iff Space.gram_point funext_iff mem_U signMatrix stdForm

section

variable {m n R : Type*} [Fintype m] [Fintype n] [CommRing R] [StarRing R] {l : Type _} [Fintype l]
  (e : m ⊕ l ≃ n) (s : n → ℤˣ) {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]
  {t : m → ℤˣ}

/-- The homomorphism GL_m(R) × GL_n(R) → GL_{m+n}(R) sending (g, h) to the block diagonal matrix
diag(g, h). -/
@[simps! apply_val] def blockGL : GL m R × GL n R →* GL (m ⊕ n) R := by use! fun g ↦
  ⟨fromBlocks g.1 0 0 g.2, fromBlocks ↑g.1⁻¹ 0 0 ↑g.2⁻¹, ?_, ?_⟩ <;> aesop

omit [Fintype m] [Fintype n] in
lemma signMatrix_sum s t : fromBlocks (signMatrix s) 0 0 (signMatrix t) =
  signMatrix (n := m ⊕ n) (s ⊕ᵥ t) := by simp

omit [Fintype n] in
@[simp] lemma signMatrix_neg : signMatrix (-s) = -signMatrix s := by simp

/-- For a bijection e of index sets, the isomorphism GL_m(R) ≅ GL_n(R) relabelling rows and
columns along e. -/
@[simps! apply_val] def reindexGL (e : m ≃ n) :
    GL m R ≃* GL n R := Units.mapEquiv (reindexRingEquiv R e).toMulEquiv

/-- For matrices J, J' with block diagonal sum J'', the homomorphism U(J) × U(J') → U(J'')
sending (g,h) to the block diagonal matrix diag(g,h). -/
def U.sum {J : Matrix m m R} {J' J''} (h : fromBlocks J 0 0 J' = J'') : U J × U (n := n) J' →* U
    J'' := (blockGL.comp ((U J).subtype.prodMap (U J').subtype)).codRestrict _ (by aesop)

/-- The block diagonal homomorphism U_m(R) × U_n(R) → U_{m+n}(R), (g, h) ↦ diag(g, h), between
the unitary groups of identity matrices. -/
abbrev U.blockSumOne := sum (@fromBlocks_one' m n R _ _)

/-- For a bijection e of index sets carrying the matrix J to J', the group isomorphism U(J) ≅
U(J') relabelling rows and columns along e. -/
def U.reindex (e : m ≃ n) {J : Matrix m m R} {J'} (h : J.submatrix e.symm e.symm = J' := by simp) :
    U J ≃* U J' := ⟨(reindexGL e).subtypeEquiv (h ▸ by simp [← ext_iff, reindex_equiv e]), by simp⟩

/-- The block diagonal embedding U(1_m) × U(1_l) → U(1_n) of unitary groups of identity
matrices, along a bijection of the disjoint union of m and l with n. -/
def U.block := (reindex (J' := 1) e).toMonoidHom.comp (blockSumOne (R := R))

@[simp] lemma U.block_val h :
    (block (R := R) e h).1.1 = (fromBlocks h.1 0 0 h.2).submatrix e.symm e.symm := rfl

variable {m n : Type*} [Fintype m] [Fintype n] {s : n → _} {t : m → ℤˣ} (e : n ≃ m)
  (h : s ∘ e.symm = t) (g : G E s)

/-- The block diagonal embedding of the product of the adelic unitary groups for signs s and t
into the one for the concatenated signs. -/
def G.sum : G E s × G E t →* G E (s ⊕ᵥ t) :=
  .prod (.mk' (fun g w ↦ U.sum (signMatrix_sum ..) (g.1.1 w, g.2.1 w))
  (by simp [← map_mul, -signMatrix])) ((U.sum (by simp)).comp (.prodMap (.snd ..) (.snd ..)))

@[simp] lemma G.mat_sum g : (sum g : G E (s ⊕ᵥ t)).mat = g.1.mat.fromBlocks 0 0 g.2.mat := by bound

/-- The isomorphism between the adelic unitary groups for signs s and −s that is the identity on
matrices, since U(J) = U(−J) at each infinite place. -/
def G.neg : G E s ≃* G E (-s) := .prodCongr
    (.piCongrRight fun _ ↦ .subgroupCongr (by simp [U, -signMatrix])) (.refl _)

omit [NumberField.IsCMField E] [Fintype m] [Fintype n] in
lemma stdForm_sum : fromBlocks (stdForm E s) 0 0 (stdForm E t) = stdForm E (s ⊕ᵥ t) := by simp

lemma gram_mkAdelicGL {E : Type*} [Field E] [CMType E]
    {J a b} (ha : ∀ w, (a w).1ᴴ * map J (Φ w) * (a w).1 = signMatrix s)
    (hb : b.1ᴴ * J.map (↑) * b.1 = 1) : (mkAdelicGL (a, b)).1ᴴ * J.map toAdele * (mkAdelicGL (a,
  b)).1 = stdForm E s := by apply matrix_ext_𝔸 <;> simpa [↓Matrix.map_mul]

@[simp] lemma G.mat_neg : (neg g).mat = g.mat := by ext <;> rfl

/-- For a bijection of index sets carrying signs s to signs t, the isomorphism of the
corresponding adelic unitary groups relabelling rows and columns in every component. -/
def G.reindex : G E s ≃* G E t := toUnitary.trans ((U.reindex e (h ▸ by simp)).trans toUnitary.symm)

@[simp] lemma G.mat_reindex : (reindex e h g).mat = g.mat.submatrix e.symm e.symm := rfl

/-- The chosen element of norm −1 of Ô, the finite part of `normNegOneIdele`, as a unit with inverse
minus its conjugate. -/
def Weil.normNegOne [StablyUnram E] :
  (Ô E)ˣ := have e := exists_norm_eq_Ô (u := -1) (by simp) (by simp)
  .mkOfMulEqOne e.choose (-star e.choose.1) (by ext1; simp; grind)

/-- For stably unramified E, the chosen unit ε = `Weil.normNegOne` of Ô satisfies ε̄ε = −1 in the
finite adeles of E. -/
@[simp] lemma star_normNegOne_mul_self [StablyUnram E] :
    star Weil.normNegOne.1.1 * Weil.normNegOne.1.1 = (-1 : 𝔸f E) := by simp [Weil.normNegOne]; grind

variable (E) [StablyUnram E]

/-- For stably unramified E, a chosen idele that is 1 at the infinite places and whose finite
part is an integral ε with ε̄ε = −1. -/
def normNegOneIdele : (𝔸 E)ˣ := Weil.normNegOne.map (.prod 1 (Ô E).subtype.1)

end

variable (E : Type*) [Field E] [CMType E] {m n : Type*} [Fintype m] [Fintype n] {s : n → _}
  {t : m → ℤˣ} (e : n ≃ m) (h : s ∘ e.symm = t) (g : G E s) (V : Space E n s)
  (e : n ≃ m) (h : s ∘ e.symm = t) [StablyUnram E] (W : Space E m t)

/-- For stably unramified E, the space I_{p,q} with matrix diag(s); its point is diagonal, with
entry 1 where s_i = 1 and `normNegOneIdele` where s_i = −1. -/
def signedSpace s : Space E n s := ⟨diagonal (s ·), diagGL fun i ↦
  ite (s i = 1) 1 (normNegOneIdele E), by simp_all [apply_ite, ite_apply, normNegOneIdele]⟩

namespace Space

variable {E}

/-- For spaces V, W with signs s, t, the space with concatenated signs whose matrix and point
are the block diagonal sums of those of V and W. -/
def sum : Space E _ (s ⊕ᵥ t) := ⟨V.J.fromBlocks 0 0 W.J, blockGL (V.x, W.x), by simp⟩

/-- For a space V with signs s and an index bijection carrying s to t, the space with signs t
obtained by relabelling its matrix and point. -/
def reindex : Space E m t := ⟨V.J.reindex e e, reindexGL e V.x, h ▸ by simp [← submatrix_map]⟩

/-- For stably unramified E and a space (J, x) with signs s, the space with signs −s, matrix −J
and point x multiplied by the scalar `normNegOneIdele`. -/
def neg : Space E n (-s) := ⟨-V.J, normNegOneIdele E • V.x, by
  simp [Matrix.map_neg, normNegOneIdele, Units.smul_def,
    ← diagonal_smul]; grind [star_normNegOne_mul_self]⟩

/-- For a space (J, x) and g in G, the space (J, xg): the same matrix with the point moved by g. -/
def move (g : G E s) : Space E n s := ⟨_, _, gram_mul_of_gram_eq V.3 g.toUnitary.2⟩

attribute [simps J] signedSpace sum reindex neg move
