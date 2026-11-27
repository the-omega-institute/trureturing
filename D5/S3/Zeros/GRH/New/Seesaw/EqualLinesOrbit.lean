/- GID: D5/S3/Zeros/GRH/New/Seesaw/EqualLinesOrbit
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Seesaw/EqualLinesOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Seesaw.EqualLinesOrbit. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Seesaw/EqualLinesOrbit.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.LatticeAndTorsionDefs
import D5.S3.Zeros.GRH.Lib.Weil.Periods.DegreeOfT
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Seesaw identity for a chain of theta lifts (see New.Seesaw.SeesawTheorem).

Part of: Unfolded periods as finite sums with controlled denominators (see
New.Seesaw.SeesawTheorem).

This file: Lattice bases adapted to the flag, their diagonal lines, nearness and glue conditions.
Lattices with equal adapted lines lie in one double coset, by integral Witt. -/

open Fintype Matrix Valued Space WithZero MatMul
variable {E X ι : Type} [Field E] [CMType E] [Fintype ι] {ε s N} {V : Space E ι ε}
  (e : X ⊕ Fin s ≃ ι) (Y : Grading V N X s) (y : Gf E ι)

/-- The numbering of the basis indices used for triangularity: 4i + 1 on the i-th string vector
(0 ≤ i < s) and 2s on the indices of X. -/
def flagOrder i := (e.symm i).elim (fun _ ↦ 2 * s) (4 * ·.1 + 1)

attribute [local simp] blockTriangular_inv_of_blockTriangular ideleLogVal mul_assoc v_inv

/-- For matrices A, B block triangular for the order `flagOrder` e and a string index i = e(a),
the (i,i) entry of AB is the product of the (i,i) entries of A and B. -/
lemma mul_apply_string_of_blockTriangular {e : X ⊕ Fin s ≃ ι} {R} [CommRing R] {A B} (h :
  BlockTriangular (R := R) A (flagOrder
  e)) (h' : BlockTriangular B (flagOrder e)) a : letI i := e (.inr a); (A * B) i i =
    A i i * B i i := sum_eq_single _ ((reindex_equiv e).1.2 (by grind [flagOrder, BlockTriangular]))

/-- The conditions that b is block triangular for `flagOrder`, spans the same Ô-lattice as x, and
has diagonal entry β_i at the i-th string vector. -/
structure Grading.IsAdaptedBasis (x b : GL ι (𝔸f E)) (β : _ → (𝔸f E)ˣ) where
  triangular : b.1.BlockTriangular (flagOrder Y.indexEquiv)
  integral : b⁻¹ * x ∈ intGL ι (Ô E)
  diag_eq i : b (Y.indexEquiv (.inr i)) (Y.indexEquiv (.inr i)) = β i

/-- For y in G_f: b is an adapted basis (`Grading.IsAdaptedBasis`), with string diagonal β, of the
lattice spanned by the columns of x_f·y, x_f the finite frame of V. -/
abbrev Grading.IsAdaptedAt := Y.IsAdaptedBasis (V.xFin * y)

/-- The lattice of x has an adapted basis whose i-th string entry has the valuations of (a/ā)^n
c_i, exactly off Q ∪ Q̄ and within k on it; c_i = 1 (s odd), else a⁻¹ (2i < s) or ā. -/
def Grading.HasNearLines a (Q : Finset _) (n k : ℕ) x := ∃ b β, Y.IsAdaptedAt x b β ∧ ∀ i w,
  |ideleLogVal (β i) w - ideleLogVal ((a /
  star a) ^ n * ite (Odd s) 1 (ite (2 * i < s) a⁻¹ (star a))) w| ≤ ite (w ∈ Q ∨ star w ∈ Q) ↑k 0

lemma Grading.exists_isAdaptedAt : ∃ b β, Y.IsAdaptedAt y b β :=
  (isValuationPair_Ohat.exists_isPrimitiveMatrix_mul ⟨_, (V.xFin * y).mul_inv⟩ _).imp fun b H ↦
  ⟨(.mkOfMulEqOne _ _ <| by rw [← mul_apply_string_of_blockTriangular H.1 _ ·, b.3] <;> aesop), H.1,
  inv_mem_iff.1 (exists_eq_right.1 (mod_cast isPrimitiveMatrix_iff.1 H.2)), by simp⟩

variable {w} {Y : Grading V N X s} {y : Gf E ι} {b β g g' b' β'} (h : Y.IsAdaptedBasis g b β) (h' :
  Y.IsAdaptedBasis g' b' β')

lemma Grading.IsAdaptedAt.gram_string_entry [Fintype X] (h : Y.IsAdaptedAt y b β) i j (hj : j ≤
  i.rev) : letI k := (b⁻¹ * (V.xFin * y))⁻¹.1
  letI f := Y.indexEquiv ∘ .inr; (kᴴ * k) (f i) (f j) = V.J (f i) (f j) • (star (β i) * β j).1 := by
  erw [← mul_one _ᴴ, gram_mul_of_gram_eq (gram_inv_of_gram_eq (gram_mul_of_gram_eq V.gram_xFin y.2))
    (mul_assoc ..), Y.2, mul_apply, sum_eq_single (Y.indexEquiv (.inr i))] <;>
    simp [↓map_gradedGram_mul_apply, gradedGram, stringReversal, reindex_equiv Y.indexEquiv]
    <;> grind [IsAdaptedBasis, flagOrder, BlockTriangular, star_zero, Algebra.smul_def]

lemma Grading.IsAdaptedBasis.inv (h : Y.IsAdaptedBasis g b β) : Y.IsAdaptedBasis b⁻¹ b⁻¹ β⁻¹ :=
  ⟨by simp [h.1], by simp, (Units.eq_inv_of_mul_eq_one_right <| by simp [← h.3 ·,
  ← mul_apply_string_of_blockTriangular, h.1])⟩

include h h'

lemma Grading.IsAdaptedBasis.ideleLogVal_le (e : IsIntMatrix v.integer
  ((g⁻¹ * g').map (evalAt w)).1) i : ideleLogVal (β' i) w ≤ ideleLogVal (β i) w := by
  simpa [mul_apply_string_of_blockTriangular h.inv.1 h'.1, h.inv.3, h'.3, field,
    zero_lt_iff, -coe_units_inv] using (v.valuationSubring.1.comap (evalAt w)).matrix.mul_mem
    (mul_mem (mem_intGL_Ô.1 h.2 w).isIntMatrix e) (mem_intGL_Ô.1 h'.2 w).isIntMatrix_inv
    (Y.indexEquiv (.inr i)) (Y.indexEquiv (.inr i))

lemma Grading.IsAdaptedBasis.ideleLogVal_eq (e : g.map (evalAt w) = g'.map (evalAt w)) i :
  ideleLogVal (β' i) w = ideleLogVal (β i) w := by
  apply_rules [le_antisymm, ideleLogVal_le] <;> simp [e, IsIntMatrix.one]

omit h h'

/-- For E stably unramified (`StablyUnram`): if x, x′ have adapted bases whose string diagonal
entries β_i, β′_i have equal valuations at all finite places whenever 2i < s, then x′kx⁻¹
lies in `Grading.besselFin` for some k in K_0. -/
lemma Grading.IsAdaptedAt.exists_mem_besselFin {E X ι} [Field E] [CMType E] [Fintype ι] [Fintype X]
  {ε s N} {V : Space E ι ε} [StablyUnram E] {Y : Grading V N X s} {x x' b b' β β'} (h :
  Y.IsAdaptedAt x b β) (h' : Y.IsAdaptedAt x' b' β') (l : ∀ i w, i ≤ i.rev → ideleLogVal (β' i) w =
  ideleLogVal (β i) w) : ∃ k ∈ Kf E ι, x' * k * x⁻¹ ∈ Y.besselFin := by
  let γ a := ite (a ≤ a.rev) β β' a
  have ⟨b', h'⟩ : ∃ b', Y.IsAdaptedAt x' b' γ :=
    ⟨b' * diagGL ((1 ⊕ᵥ β'⁻¹ * γ) ∘ Y.indexEquiv.symm), by constructor <;> simp_all [h'.1 _,
    BlockTriangular, ← map_inv, diagonal_apply, h'.3, mul_assoc, mul_mem, h'.2, γ, mem_intGL,
    reindex_equiv Y.indexEquiv, mem_Ô, ← log_le_log, v_inv, ideleLogVal, apply_ite, ite_apply]⟩
  let f (a : {a // a ≤ a.rev}) := Y.indexEquiv (.inr a.1)
  let P {g} (h : g ∈ intGL ι (Ô E)) : IsPrimitiveMatrix (Ô E) (submatrix (Units.inv g) id f) :=
    (mem_intGL.1 h).symm.imp (by tauto) fun H ↦ ⟨g.1.submatrix f id, fun i ↦ H (f i),
      (g.3 ▸ submatrix_one f (by aesop_cat) : (g.1 * g.inv).submatrix f f = 1)⟩
  peel witt_Ô (P h.2) (P h'.2) (by ext; erw [h.gram_string_entry,
    h'.gram_string_entry] <;> grind) with g n e
  refine Y.mem_besselGroup_iff_sub_one.2 (Y.indexEquiv.surjective.forall₂.2 fun _ _ _ _ ↦ ?_)
  have q {i} c : (V.ratCoordMatrixFin (x' * g * x⁻¹) * b) i (f c) = b' i (f c) := by
    simpa [submatrix_mul (e₂ := id), ratCoordMatrixFin] using! congr(((V.xFin * x').1 * $e) i _)
  erw [sub_eq_zero, ratCoordMatrix_inr, ← b.mul_inv_cancel_right (V.ratCoordMatrixFin _), mul_apply,
    Finset.sum_congr rfl ((reindex_equiv Y.indexEquiv).1.2 _), ← mul_apply, b.mul_inv]
  apply apply_ite₂
  grind (splits := 20) [q ⟨_, _⟩, h.inv, gradeOf_inl, flagOrder, gradeOf_inr, BlockTriangular,
    IsAdaptedBasis]
