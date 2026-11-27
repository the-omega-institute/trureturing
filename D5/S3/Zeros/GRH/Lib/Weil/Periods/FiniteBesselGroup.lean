/- GID: D5/S3/Zeros/GRH/Lib/Weil/Periods/FiniteBesselGroup
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/Weil/Periods/FiniteBesselGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.Weil.Periods.FiniteBesselGroup. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/Weil/Periods/FiniteBesselGroup.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.NumberTheory.UpsilonValues
import D5.S3.Zeros.GRH.Lib.Weil.Periods.DegreeAndUnipotent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Transfer of Bessel and Fourier–Jacobi periods under a theta lift (one unfolding step)
(known result; see Lib.Weil.Periods.UnfoldingStep).

This file: Base point of the surviving orbit, shift character, generic Bessel/Fourier-Jacobi
functions. Graded hermitian matrices, adjoints; Bessel subgroup is unipotent radical times definite
unitary group. Rational coordinates of finite adelic points; finite parts of the Bessel subgroup. -/
seal Finset.univ Finset.sum Finset.prod

open Fintype Matrix

variable {E ι ι' X X' : Type} [Field E] [CMType E] [Fintype ι] [Fintype ι'] {s s' ε ε' N} {V :
  Space E ι ε} {V' : Space E ι' ε'} (Y : Grading V N X s) (Y' : Grading V' N X' s') (d : ι' → ℤ)

/-- The involution of the basis indices of V that fixes the indices of X and exchanges the
string vectors i and s − 1 − i. -/
def Grading.stringReversal i := Y.indexEquiv ((Y.indexEquiv.symm i).map id .rev)

/-- The rational matrix 𝖳: V → V' killing X, with e_a ↦ t_a e'_a on strings; for grade > 0, 0, <
0, t_a = 1, −Nc, c (s odd) or c, none, 1 (s even). -/
noncomputable def Grading.stringMap := (gradedBlocks Y'.indexEquiv Y.indexEquiv 0 (.of fun b a ↦
  ite (b.1 = a) (ite (Odd s ↔ 2 * a + 1 < s) 1 ↑Y.c * ite (2 * a + 1 = s) (-N) 1) 0)).map toAdele

/-- The condition that the matrix w agrees with 𝖳 (`Grading.stringMap`) at all entries (b, a) where
a has positive grade and b has grade below that of a. -/
abbrev Grading.AgreesWithT (w : Matrix ..) := ∀ b a, 0 < Y.gradeOf a → Y'.gradeOf b < Y.gradeOf a →
  w b a = Y.stringMap Y' b a

/-- For weights d on the target basis and an index pair (b,a), the integer d(b) minus the grade
of a in Y. -/
abbrev Grading.mapDegree (r : _ × _) := d r.1 - Y.gradeOf r.2

/-- For a grading d of the target indices, the additive group of rational matrices whose entry
(b, a) vanishes whenever d(b) is less than the grade of a. -/
def Grading.nonnegMaps : AddSubgroup
  (ratMatrices E ι' ι) := by use! {w | HasDegreeGe d Y.gradeOf 0 w.1} <;> simp_all [HasDegreeGe]

/-- The rational matrix killing X and sending string vector b to c times string vector b + 1,
with a further factor −N at grade 0 and −Nc at grade 1. -/
noncomputable def Grading.shift := (gradedBlocks Y.indexEquiv Y.indexEquiv 0 (.of fun a b ↦
  ite (a.1 = b + 1) (Y.c * ite (2 * b + 1 = s) (-N) (ite (2 * a = s) (-N * Y.c) 1)) 0)).map toAdele

/-- The conditions on P : G → ℂ: continuous, left invariant under rational points of
`Grading.besselGroup`, and P(ng) = χ(n)P(g) for unipotent n with n − 1 raising grades by at least
2. -/
structure Grading.IsGeneric [WeilData E] (P : G E ε → ℂ) where
  continuous : Continuous P
  rat_mul : Y.ratBessel.FixesLeft P
  unipotent_mul g : ∀ n ∈ Y.unipotent, HasDegreeGe Y.gradeOf Y.gradeOf 2 (V.ratCoordMatrix n - 1) →
    P (n * g) = stdAddChar E ((WeilData.j / 2 : E) * (Y.shift * V.ratCoordMatrix n).trace) * P g

section

open MatMul

variable [Fintype X] [Fintype X'] (V₁ : Space E ι ε) (V'' : Space E ι' ε') (Y₁ :
  Grading V N X s) {g}

/-- The adjoint J⁻¹ yᴴ J' of an adelic matrix y: V → V' in rational coordinates, J and J' the
Gram matrices of V and V'. -/
noncomputable def Space.formAdjoint (y : Matrix ι' ι (𝔸 E)) :=
  V₁.J⁻¹.map toAdele * yᴴ * V''.J.map toAdele

attribute [local simp] HasDegreeGe Grading.stringReversal Space.formAdjoint
  Space.map_J_inv_mul_map_J mul_sub sub_mul

lemma Space.formAdjoint_formAdjoint x : V''.formAdjoint V₁ (V₁.formAdjoint V'' x) =
  x := by simp [conjTranspose_nonsing_inv, conjTranspose_J, ← Matrix.mul_assoc, x.mul_assoc]

lemma Space.formAdjoint_ratCoordMatrix_mul g y : V''.formAdjoint V₁ (V₁.ratCoordMatrix g * y) =
  V''.formAdjoint V₁ y * V₁.ratCoordMatrix g⁻¹ := by simp [ratCoordMatrix, ← U.form_mul_inv_eq]

omit [Fintype X] in
@[simp] lemma Grading.gradeOf_stringReversal : ∀ i,
  Y₁.gradeOf (Y₁.stringReversal i) = -Y₁.gradeOf i := by simp +arith [reindex_equiv Y₁.indexEquiv]

lemma Grading.map_gradedGram_mul_apply {R κ : Type} {M} [CommRing R] (f : E →+* R) (A :
  Matrix ι' κ R) : ∀ i p, ((gradedGram Y'.indexEquiv M).map f * A) i p =
  f (gradedGram Y'.indexEquiv M i (Y'.stringReversal i)) * A (Y'.stringReversal i) p := by
  simp [gradedGram, mul_apply, reindex_equiv Y'.indexEquiv, apply_ite f, ← Fin.rev_eq_iff]

lemma Grading.vecMul_J_apply y : ∀ a, (y ᵥ* V.J.map toAdele) a =
  y (Y.stringReversal a) * gradedGram Y.indexEquiv N (Y.stringReversal a) a := by
  simp [Y.2, gradedGram, vecMul_apply_eq_sum, reindex_equiv Y.indexEquiv, apply_ite toAdele]

@[simp] lemma Grading.J_inv_eq_gradedGram : V.J⁻¹ = gradedGram Y.indexEquiv N⁻¹ := inv_eq_left_inv
  (by simp [Y.2, gradedGram, entrywise, reindex_equiv Y.indexEquiv]; grind [Grading])

lemma Grading.formAdjoint_apply y a b : V.formAdjoint V' y a b = gradedGram Y.indexEquiv N⁻¹ a
  (Y.stringReversal a) * star (y (Y'.stringReversal b) (Y.stringReversal a))
  * gradedGram Y'.indexEquiv N (Y'.stringReversal b) b :=
  (Y'.vecMul_J_apply ..).trans (by simp [Y.J_inv_eq_gradedGram, map_gradedGram_mul_apply])

lemma Grading.mem_besselGroup_iff : g ∈ Y₁.besselGroup ↔ ∀ i k, Y₁.gradeOf i ≤ Y₁.gradeOf k →
  (Y₁.indexEquiv.symm i).isRight ∨ (Y₁.indexEquiv.symm
  k).isRight → V.ratCoordMatrix g i k = (1 : Matrix ..) i k := ⟨(by grind [inv_mem ·, congrFun₂ (by
  simpa using V.formAdjoint_ratCoordMatrix_mul V g⁻¹ 1 : V.formAdjoint V (_ - 1) = _ - 1) · ·,
  stringReversal, formAdjoint_apply, star_zero,
  gradeOf_stringReversal, Matrix.sub_apply, ← Y₁.mem_besselGroup_iff_sub_one.1]), by simp_all
  [mem_besselGroup_iff_sub_one, reindex_equiv Y₁.indexEquiv]⟩

lemma Grading.hasDegreeGe_zero_of_mem_besselGroup : g ∈ Y₁.besselGroup →
  HasDegreeGe Y₁.gradeOf Y₁.gradeOf 0
  (V.ratCoordMatrix g) := by simp [mem_besselGroup_iff, reindex_equiv Y₁.indexEquiv]; grind

lemma Grading.exists_besselGroup_proj : ∃ p : Y.besselGroup →* _, Continuous p ∧
  (∀ r, r * (Y.inclX (p r))⁻¹ ∈ Y.unipotent) ∧ (∀ a, p ⟨_, Y.inclX_mem_besselGroup a⟩ = a) ∧
  (∀ r, ↑r ∈ Y.unipotent ↔ p r = 1) ∧ ∀ r, r.1 ∈ Y.ratBessel → p r ∈ (stdSpace ..).Γ := by
  refine ⟨.mk' (fun r ↦ G.toUnitary.symm
    (U.of ?_ (toBlocks₁₁ ((V.ratCoordMatrix r).onFun Y.indexEquiv)) (flip .trans (congr(toBlocks₁₁
    ($((V.toRatCoords r).2).onFun Y.indexEquiv)).trans ?_) (r.rec ?_)))) ?_, G.continuous_iff.2 ?_,
    .symm ⟨?h, fun _ ↦ ((?h.2.1 _).2 ((MonoidHom.div_mem_ker_iff _).2 (?h.1 _).symm) :)⟩⟩ <;>
    simp +contextual [G.mat, gradedGram, entrywise, Space.mem_Gamma_iff_ratCoordMatrix,
    reindex_equiv Y.indexEquiv, ← (stdSpace ..).isEmbedding_ratCoordMatrix.2.eq_iff,
    mem_besselGroup_iff, Y.2, ratCoordMatrix_inclX, toBlocks₁₁] <;>
    first | fun_prop | simp [Space.ratCoordMatrix]; grind -funext [star_zero, sum_eq_zero]

/-- Every g in `Grading.besselGroup` is a product n·a with n in the grade-raising unipotent group
`Grading.unipotent` and a in the image of the adelic group U(X). -/
lemma Grading.exists_unipotent_mul_inclX : g ∈ Y.besselGroup → ∃ n ∈ Y.unipotent, ∃ a, g =
  n * Y.inclX a := (⟨_, Y.exists_besselGroup_proj.choose_spec.2.1 ⟨g, ·⟩, _, eq_mul_of_div_eq rfl⟩)

end

/-- For g in G_f, the matrix x_f g x_f⁻¹ of g in rational coordinates. -/
noncomputable def Space.ratCoordMatrixFin (g : Gf E ι) := V.xFin.1 * g * V.xFin⁻¹

lemma Space.ratCoordMatrix_eq g : V.ratCoordMatrix g = V.x * g.mat * V.x⁻¹ := rfl

lemma Space.ratCoordMatrixFin_snd g : V.ratCoordMatrixFin g.2 =
  (V.ratCoordMatrix g).map (RingHom.snd ..) := by simp_rw [ratCoordMatrix_eq, Matrix.map_mul]; rfl

lemma Space.ratCoordMatrix_inr g a b : V.ratCoordMatrix (1, g) a b = ((1 : Matrix ..) a b,
  V.ratCoordMatrixFin g a b) := by simpa [ratCoordMatrix_eq, mul_apply, Prod.fst_sum, funext_iff,
  apply_ite, Prod.ext_iff, ratCoordMatrixFin_snd (1, g)] using congr(($V.x.mul_inv a b).1)

/-- For a hermitian space (J, x), the finite part x_f of x satisfies x_fᴴ J x_f = 1 over the
finite adeles. -/
lemma Space.gram_xFin : V.xFin.1ᴴ * V.J.map (↑) * V.xFin.1 = 1 := by
  simpa [stdForm, -RingHom.coe_snd] using! congr(map $V.gram_point (RingHom.snd ..))

variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] {ε : ι → ℤˣ} {s : ℕ} {N : E}
  {V : Space E ι ε} (Y : Grading V N X s) (Y₁ : Grading V N ι' s) (h)

namespace Grading

/-- The subgroup of the g in G_f such that (1, g) lies in the group `Grading.besselGroup` generated
by the unipotent group and U(X). -/
noncomputable def besselFin := Y.besselGroup.comap (.inr ..)

variable [Fintype X] {ε : ι → ℤˣ} {s : ℕ} {N : E} {V : Space E ι ε} (Y : Grading V N X s) in
/-- The homomorphism from the finite adelic points of U(X) to those of U(V): embed (1,a) by
U(X) → U(V) and take the finite component. -/
noncomputable def inclXFin := (MonoidHom.snd ..).comp (Y.inclX.comp (.inr ..))

attribute [local simp] besselFin inclXFin ratCoordMatrix_inclX mem_besselGroup_iff
  Space.ratCoordMatrix_inr Space.ratCoordMatrixFin_snd

lemma ratCoordMatrixFin_inclXFin : V.ratCoordMatrixFin (Y₁.inclXFin h) = gradedBlocks Y₁.indexEquiv
  Y₁.indexEquiv h 1 := ext (by simp [reindex_equiv Y₁.indexEquiv, apply_ite])

lemma inclX_inr : Y₁.inclX (1, h) = (1, Y₁.inclXFin h) :=
  V.isEmbedding_ratCoordMatrix.2 (ext (by simp [reindex_equiv Y₁.indexEquiv]; aesop))

open MatMul

lemma snd_mem_besselFin {g} : g ∈ Y₁.besselGroup → g.2 ∈ Y₁.besselFin := by aesop

instance : IsClosed (SetLike.coe Y.besselFin) :=
  Y.instIsClosedGCoeSubgroupRg.preimage_of_continuous (f := (1, ·))
