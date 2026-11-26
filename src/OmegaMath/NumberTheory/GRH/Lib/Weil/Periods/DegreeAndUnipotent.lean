import OmegaMath.NumberTheory.GRH.Lib.Adelic.Unitary.SpaceBasic
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Transfer of Bessel and Fourier–Jacobi periods under a theta lift (one unfolding step)
(known result; see Lib.Weil.Periods.UnfoldingStep).

This file: Graded hermitian spaces: definite part plus string, unipotent and Bessel subgroups.
Degree of graded matrices, adjoints, basic facts on the Bessel subgroup. -/

noncomputable section

open Matrix
variable {R X X' ι ι' : Type _} {s : ℕ} {s' : ℕ} (a) [CommRing R] {E : Type*} [Field E] [CMType E]
  [Fintype ι] [Fintype X] (e' : X' ⊕ Fin s' ≃ ι') (e : X ⊕ Fin s ≃ ι) {ε : ι → ℤˣ} {N : E}
  (V : Space E ι ε)

/-- The block diagonal matrix with block A from X to X' and block B from string to string,
reindexed along e and e'. -/
abbrev gradedBlocks A B := (fromBlocks (α := R) A 0 0 B).submatrix e'.symm e.symm

/-- The Gram matrix of X plus a string of length s: identity on X; string vectors a, b with a +
b = s − 1 pair to 1, or to −N if a = b. -/
def gradedGram (N : R) := gradedBlocks e e 1 (of fun a b ↦ ite (a = b.rev) (ite (a = b) (-N) 1) 0)

attribute [simp] stdForm_one

/-- For a space (J, x) and g in G, the adelic matrix x g x⁻¹ of g in rational coordinates, an
element of U(J)(𝔸). -/
def Space.ratCoordMatrix : G E ε →* Matrix ι ι (𝔸 E) := by use! (V.toRatCoords ·) <;> simp

/-- A presentation of V as X plus a string of length s: an indexing of its basis with Gram
matrix `gradedGram`, N = N̄ ≠ 0, and a constant c = c̄ ≠ 0 in E. -/
structure Grading N X s where
  indexEquiv : X ⊕ Fin s ≃ ι
  gram_eq : V.J = gradedGram indexEquiv N
  N_spec : N ≠ 0 ∧ star N = N
  c : {c : E // c ≠ 0 ∧ star c = c}

namespace Grading

variable {V} (Y : Grading V N X s)

/-- The grade of a basis index of V: 0 on the indices of X, and s − 1 − 2i on the i-th vector of
the string (0 ≤ i < s). -/
@[local simp] def gradeOf i := ((Y.indexEquiv.symm i).elim 0 (s - 1 - 2 * ·.1) : ℤ)

omit [Fintype X] in
@[simp] lemma gradeOf_inl a (Y : Grading V N X s) :
    Y.gradeOf (Y.indexEquiv (.inl a)) = 0 := by simp

omit [Fintype X] in
@[simp] lemma gradeOf_inr a (Y : Grading V N X s) :
    Y.gradeOf (Y.indexEquiv (.inr a)) = s - 1 - 2 * a := by simp

/-- The unipotent subgroup of the g in G whose matrix in rational coordinates, minus 1, strictly
raises grades. -/
def unipotent := (unitriangular (-Y.gradeOf ·) _).comap V.ratCoordMatrix.toHomUnits

/-- The homomorphism from the adelic unitary group of the standard definite space on X to that
of V, acting on X and fixing the string vectors. -/
def inclX := ((U.reindex Y.indexEquiv (by erw [Y.2, ← submatrix_map]; aesop)).trans
  V.toRatCoords.symm).toMonoidHom.comp ((U.sum rfl).comp (G.toUnitary (s := 1).toMonoidHom.prod 1))

lemma ratCoordMatrix_inclX h : V.ratCoordMatrix (Y.inclX h) =
  gradedBlocks Y.indexEquiv Y.indexEquiv h.mat 1 := by simp [Space.ratCoordMatrix, inclX]; rfl

/-- The subgroup of the g in G whose matrix in rational coordinates fixes each string vector of
grade ≥ 0 up to string vectors of higher grade. -/
def besselGroup := (agreeWithOneOn (fun i k ↦ ite (Y.indexEquiv.symm k).isRight 0 1 ≤ Y.gradeOf k ∧
  Y.gradeOf i ≤ Y.gradeOf k) _).comap V.ratCoordMatrix.toHomUnits

/-- The rational points of U(V) that lie in the Bessel (Fourier–Jacobi) subgroup
`Grading.besselGroup` of the grading Y, as a subgroup of the adelic group G. -/
abbrev ratBessel := V.Γ ⊓ Y.besselGroup

end Grading

variable {E : Type*} [Field E] [CMType E] {ι X : Type _} [Fintype ι] [Fintype X] {s : ℕ}
  {ε : ι → ℤˣ} {N : E} {V : Space E ι ε} (Y : Grading V N X s) {g : G E ε} {ι' : Type _}
  [Fintype ι']

/-- The matrix x raises weights by at least d: x_{ba} = 0 whenever w'(b) < w(a) + d. -/
def HasDegreeGe {R ι ι'} [Zero R] (w' w : _ → ℤ) d (x : Matrix ι' ι R) := ∀ b a, w' b < w a + d →
  x b a = 0

lemma HasDegreeGe.mul {R ι κ} [CommRing R] {w'' w' w d d' y x} (h : @HasDegreeGe R ι' κ _ w'' w' d
  x) (h' : @HasDegreeGe R ι ι' _ w' w d' y) {e} (he : e ≤ d + d' := by omega) :
  HasDegreeGe w'' w e (x * y) := by grind [HasDegreeGe, Matrix.mul_apply, Finset.sum_eq_zero]

@[fun_prop] lemma Space.isEmbedding_ratCoordMatrix : Topology.IsEmbedding V.ratCoordMatrix :=
    (isHomeomorph_smul (ConjAct.toConjAct V.x)).isEmbedding.comp G.isClosedEmbedding_mat.1

lemma Space.mem_Gamma_iff_ratCoordMatrix : g ∈ V.Γ ↔ ∀ i k,
  V.ratCoordMatrix g i k ∈ toAdele.range := mem_Γ_iff_range _

@[simp] lemma ratCoordMatrix_stdSpace g : (stdSpace E X).ratCoordMatrix g = g.mat :=
  (mul_one _).trans (one_mul _)

namespace Grading

attribute [local simp] HasDegreeGe ratCoordMatrix_inclX Space.mem_Gamma_iff_ratCoordMatrix

omit [Fintype X] in
/-- g lies in the unipotent group `Grading.unipotent` if and only if its matrix in rational
coordinates, minus 1, has degree at least 1: the entry (i, k) vanishes whenever grade(i) ≤
grade(k). -/
@[simp] lemma mem_unipotent : g ∈ Y.unipotent ↔
  HasDegreeGe Y.gradeOf Y.gradeOf 1 (V.ratCoordMatrix g - 1) := forall₂_congr (by simp)

omit [Fintype X] in
lemma hasDegreeGe_two_of_odd : Odd s → g ∈ Y.unipotent → HasDegreeGe Y.gradeOf Y.gradeOf 2
  (V.ratCoordMatrix g - 1) := by simp [reindex_equiv Y.indexEquiv]; grind

omit [Fintype X] in
/-- g lies in `Grading.besselGroup` if and only if it fixes each string vector of grade ≥ 0 up to
higher grades: for such an index k, the entry (i, k) of its matrix minus 1 vanishes whenever
grade(i) ≤ grade(k). -/
@[local simp] lemma mem_besselGroup_iff_sub_one : g ∈ Y.besselGroup ↔ ∀ i k,
  ite (Y.indexEquiv.symm k).isRight 0 1 ≤ Y.gradeOf k → Y.gradeOf i ≤
  Y.gradeOf k → (V.ratCoordMatrix g - 1) i k = 0 := forall₂_congr (by simp)

lemma inclX_mem_besselGroup a : Y.inclX a ∈ Y.besselGroup := by simp [reindex_equiv Y.indexEquiv]

omit [Fintype X] in
lemma unipotent_le_besselGroup : Y.unipotent ≤ Y.besselGroup := by aesop_cat

instance instIsClosedGCoeSubgroupRg : IsClosed (SetLike.coe Y.besselGroup) :=
  isClosed_of_closure_subset fun _ h i k e ↦ closure_singleton.le
  (map_mem_closure (f := (V.ratCoordMatrix · i k)) (by fun_prop) h fun _ ↦ (· i k e))

@[fun_prop] lemma continuous_inclX : Continuous Y.inclX :=
  V.isEmbedding_ratCoordMatrix.continuous_iff.2 (by simp [Function.comp_def]; fun_prop)

lemma inclX_mem_ratBessel {a} : a ∈ (stdSpace ..).Γ →
  Y.inclX a ∈ Y.ratBessel := by aesop (add simp (reindex_equiv Y.indexEquiv))
