import GRH.Lib.Weil.Unramified.SphericalHecke
import GRH.Lib.Weil.Construction.PairDefs
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Set-up used by: Schrödinger and mixed models of the Weil representation; action of parabolic
subgroups.

This file: Two-block matrices: inclusion matrices, block embedding of GL_r, block-triangular
criteria. -/

open MatMul Matrix Set

attribute [local simp] BlockTriangular Matrix.mul_apply invTransposeGL inclMatrix lt_iff_le_not_ge
  parabolic

variable {r n n' R ι : Type*} [CommRing R] {E} [Field E] [NumberField E] {T : Matrix n n' R}
  [Fintype r] [Fintype n] (u : r ↪ n) (g : GL r R) {x : GL n R} {f : ι → n'} {r' : Type*}

lemma map_inclMatrix [CommRing ι] (f : R →+* ι) (u : r' → n') : (inclMatrix R u).map f =
  inclMatrix ι u := by aesop

omit [Fintype r] in
lemma inclMatrix_transpose_mul : (inclMatrix R u)ᵀ * T = T.submatrix u id := by aesop

omit [Fintype r] in
@[simp] lemma inclMatrix_transpose_mul_self : (inclMatrix R u)ᵀ * inclMatrix R u = 1 := by aesop

/-- The function on adelic matrices x equal to f of the family of reductions modulo the places w
i if x is integral at all of them, and 0 otherwise. -/
noncomputable def residueDatum (w : ι → FinPlace E) (f : _ → ℂ) x := ite (∀ i p,
  x p (w i) ∈ LocInt _) (f fun i ↦ (@vecToMat n n' _ x).map (residueOrZero ∘ evalAt (w i))) 0

/-- For an embedding u of index sets, the homomorphism GL_r(R) → GL_n(R), g ↦ diag(g, 1), with g
acting on the indices in the image of u. -/
@[local simp] noncomputable def extendGL : GL r R →* GL n R := Units.map ⟨⟨fun g ↦ 1 + inclMatrix R
  u * (g - 1) * (inclMatrix R u)ᵀ, by simp⟩, by simp [-inclMatrix, add_assoc, ← _ᵀ.mul_assoc]⟩

@[simp] lemma extendGL_mul_inclMatrix : (extendGL u g).1 * inclMatrix R u =
  inclMatrix R u * g.1 := by aesop

lemma extendGL_spec : (extendGL u g).1.submatrix u u = g ∧ ∀ i ∉ range u, ∀ j, extendGL u g i j =
    (1 : Matrix ..) i j := by simp [eq_comm]; aesop

lemma mem_stabilizer_col_iff : x ∈ MulAction.stabilizer _ T.col ↔ x.1 * T = T := transpose_inj

omit [Fintype n] in
lemma eq_inclMatrix_mul_iff : T = inclMatrix R u * T.submatrix u id ↔ ∀ i ∉ range u, ∀ j,
  T i j = 0 := ext_iff.symm.trans (forall_congr' (by by_cases ∃ x, · = u x <;> aesop))

attribute [local instance] Prop.linearOrder

/-- The parabolic subgroup of GL_n(R) of matrices whose rows with index in the image of u vanish
in the columns with index outside that image. -/
noncomputable def rangeParabolic : Subgroup (GL n R) :=
  (parabolic (· ∉ range u)).map invTransposeGL.toMonoidHom

omit [Fintype r] in
lemma mem_rangeParabolic_iff : x ∈ rangeParabolic u ↔ ∀ i, ∀ j ∉ range u, x (u i) j = 0 := by
  erw [← inv_mem_iff, mem_image_equiv]; aesop

lemma submatrix_mul_of_mem_rangeParabolic (h : x ∈ rangeParabolic u) : (x.1 * T).submatrix u f =
  x.1.submatrix u u * T.submatrix u f :=
  ext (by simp; grind [Fintype.sum_of_injective u u.2, mem_rangeParabolic_iff])

omit [Fintype r] in
lemma index_rangeParabolic : (rangeParabolic (R := R) u).index =
  (parabolic (R := R) (· ∉ range u)).index := by simp [rangeParabolic]
