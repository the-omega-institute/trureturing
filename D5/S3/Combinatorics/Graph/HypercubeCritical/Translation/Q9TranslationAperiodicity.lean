/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/Translation/Q9TranslationAperiodicity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Two components of a subcubic 258-point support have trivial XOR stabilizers. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
import D5.S3.Combinatorics.Graph.PerronFrobenius.InvolutionGramObstruction
import D5.S3.Combinatorics.Graph.PerronFrobenius.IrrationalQuadraticBipartition
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Weighted Huang saturation constrains XOR translations on actual cubic components. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9InternalGramConnected

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open BalancedCubeGirth (adjacent_exists_flip)
open BalancedCubeComponentBoundary (flip_injective)
open Q9BoundaryGram (Interior)
open Q9IsotropicHuang (parity)
open Q9WeightedSaturation (Rows biadjacency)
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private unsigned unsigned_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram

private theorem unsigned_pos_iff_adj (w : Fin 9 → ℝ) (hw : ∀ a, 0 < w a) (x y : Q 9) :
    0 < unsigned w x y ↔ (hypercube 9).Adj x y := by
  constructor
  · intro hpos
    by_contra hxy
    exact (ne_of_gt hpos) (unsigned_zero w hxy)
  · intro hxy
    obtain ⟨a, rfl⟩ := adjacent_exists_flip hxy
    simpa only [unsigned, (flip_injective x).eq_iff, Fintype.sum_ite_eq'] using hw a

private theorem row_parity {C : Finset (Q 9)} {b : Bool} (x : Rows C b) :
    parity x.1.1 = b :=
  (Finset.mem_filter.mp x.property).2

private def parityEquiv (C : Finset (Q 9)) (b : Bool) :
    Rows C b ⊕ Interior C b ≃ (C : Set (Q 9)) where
  toFun
    | .inl x => x.1
    | .inr y => ⟨y.1.1, y.property⟩
  invFun x :=
    if h : parity x.1 = b then
      .inl ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    else
      .inr ⟨⟨x.1, h⟩, x.property⟩
  left_inv := by
    rintro (x | y) <;> dsimp only
    · rw [dite_eq_left (row_parity x)]
    · rw [dite_eq_right y.1.property]
  right_inv x := by
    dsimp only
    split_ifs <;> rfl

private def positiveBiadjacencyGraphIso (w : Fin 9 → ℝ) (hw : ∀ a, 0 < w a)
    (C : Finset (Q 9)) (b : Bool) :
    Matrix.positiveBiadjacencyGraph (biadjacency w C b) ≃g
      (hypercube 9).induce (C : Set (Q 9)) where
  toEquiv := parityEquiv C b
  map_rel_iff' := by
    rintro (x | x) (y | y)
    · change (hypercube 9).Adj x.1.1 y.1.1 ↔ False
      exact iff_false_intro fun h =>
        cubeParity_ne_of_adj h ((row_parity x).trans (row_parity y).symm)
    · change (hypercube 9).Adj x.1.1 y.1.1 ↔ 0 < unsigned w x.1.1 y.1.1
      exact (unsigned_pos_iff_adj w hw _ _).symm
    · change (hypercube 9).Adj x.1.1 y.1.1 ↔ 0 < unsigned w y.1.1 x.1.1
      exact ⟨fun h => (unsigned_pos_iff_adj w hw _ _).mpr h.symm,
        fun h => ((unsigned_pos_iff_adj w hw _ _).mp h).symm⟩
    · change (hypercube 9).Adj x.1.1 y.1.1 ↔ False
      have hx : parity x.1.1 = !b := Bool.eq_not_of_ne x.1.property
      have hy : parity y.1.1 = !b := Bool.eq_not_of_ne y.1.property
      exact iff_false_intro fun h => cubeParity_ne_of_adj h (hx.trans hy.symm)

open Classical in
/-- Positive weights give the induced cube's connected graph on the two parity indices. -/
theorem positiveBiadjacencyGraph_connected (w : Fin 9 → ℝ) (hw : ∀ a, 0 < w a)
    (C : Finset (Q 9)) (b : Bool)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected) :
    (Matrix.positiveBiadjacencyGraph (biadjacency w C b)).Connected :=
  (SimpleGraph.Iso.connected_iff (positiveBiadjacencyGraphIso w hw C b)).mpr hc

open Classical in
/-- Cubicity gives a positive internal entry in every retained row. -/
theorem exists_positive_biadjacency (w : Fin 9 → ℝ) (hw : ∀ a, 0 < w a)
    (C : Finset (Q 9)) (b : Bool)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (x : Rows C b) : ∃ y : Interior C b, 0 < biadjacency w C b x y := by
  let G := (hypercube 9).induce (C : Set (Q 9))
  have hdegree : 0 < G.degree x.1 := by
    change 0 < ((hypercube 9).induce (C : Set (Q 9))).degree x.1
    rw [hr.degree_eq x.1]
    exact Nat.succ_pos 2
  obtain ⟨y, hxy⟩ := (G.degree_pos_iff_exists_adj x.1).mp hdegree
  have hxy' : (hypercube 9).Adj x.1.1 y.1 := hxy
  have hy : parity y.1 ≠ b := fun h =>
    cubeParity_ne_of_adj hxy' ((row_parity x).trans h.symm)
  exact ⟨⟨⟨y.1, hy⟩, y.property⟩, (unsigned_pos_iff_adj w hw _ _).mpr hxy'⟩

open Classical in
/-- The internal weighted Gram matrix of a connected cubic support is irreducible. -/
theorem isIrreducible_internal_gram (w : Fin 9 → ℝ) (hw : ∀ a, 0 < w a)
    (C : Finset (Q 9)) (b : Bool)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected) :
    let M := biadjacency w C b
    (M * Mᵀ).IsIrreducible := by
  refine Matrix.isIrreducible_mul_transpose_of_connected (biadjacency w C b) ?_
    (positiveBiadjacencyGraph_connected w hw C b hc)
    (exists_positive_biadjacency w hw C b hr)
  intro x y
  change 0 ≤ unsigned w x.1.1 y.1.1
  unfold unsigned
  exact Finset.sum_nonneg fun a _ => ite_nonneg (hw a).le le_rfl

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9InternalGramConnected

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

open scoped BigOperators Matrix
open BalancedCriticalSpectrum (Q)
open Q9BoundaryGram (Interior)
open Q9IsotropicHuang (parity)
open private translate_flip translate_translate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
open private unsigned from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram

/-- Translate a cube vertex by coordinatewise XOR. -/
abbrev xorTranslate (t x : Q 9) : Q 9 := fun i => Bool.xor (t i) (x i)

private theorem parity_xorTranslate (t x : Q 9) :
    parity (xorTranslate t x) = parity t + parity x := by
  change (∑ i : Fin 9, (t i + x i)) = (∑ i : Fin 9, t i) + (∑ i : Fin 9, x i)
  exact Finset.sum_add_distrib

private theorem parity_xorTranslate_of_even {t : Q 9} (ht : parity t = false) (x : Q 9) :
    parity (xorTranslate t x) = parity x := by
  rw [parity_xorTranslate, show parity t = (0 : Bool) from ht, zero_add]

variable {C : Finset (Q 9)} {b : Bool} {t : Q 9}
variable (hC : ∀ x ∈ C, xorTranslate t x ∈ C) (ht : parity t = false)

/-- An even XOR period acts by an involution on the retained rows. -/
def rowTranslation : Equiv.Perm (Rows C b) := by
  let f (x : Rows C b) : Rows C b :=
    ⟨⟨xorTranslate t x.val.val, hC _ x.val.property⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (parity_xorTranslate_of_even ht _).trans (Finset.mem_filter.mp x.property).2⟩⟩
  have hf : Function.Involutive f := by
    intro x
    exact Subtype.ext (Subtype.ext (translate_translate t x.val.val))
  exact ⟨f, f, hf, hf⟩

/-- The same period acts on the actual interior columns. -/
def interiorTranslation : Equiv.Perm (Interior C b) := by
  let f (x : Interior C b) : Interior C b :=
    ⟨⟨xorTranslate t x.val.val, fun h =>
      x.val.property ((parity_xorTranslate_of_even ht _).symm.trans h)⟩,
      hC _ x.property⟩
  have hf : Function.Involutive f := by
    intro x
    exact Subtype.ext (Subtype.ext (translate_translate t x.val.val))
  exact ⟨f, f, hf, hf⟩

theorem rowTranslation_involutive :
    Function.Involutive (rowTranslation (b := b) hC ht) :=
  (rowTranslation hC ht).left_inv

variable {R : Type*} [CommRing R]

/-- The permutation matrix of the retained row action. -/
def rowPermutation : Matrix (Rows C b) (Rows C b) R :=
  (rowTranslation hC ht).permMatrix R

theorem rowPermutation_mulVec (v : Rows C b → R) :
    rowPermutation hC ht *ᵥ v = v ∘ rowTranslation hC ht :=
  Matrix.permMatrix_mulVec _

theorem rowPermutation_sq :
    rowPermutation (R := R) (b := b) hC ht * rowPermutation hC ht = 1 := by
  let e := rowTranslation (b := b) hC ht
  have he : e * e = 1 := Equiv.ext (rowTranslation_involutive hC ht)
  change e.permMatrix R * e.permMatrix R = 1
  rw [← Matrix.permMatrix_mul, he, Matrix.permMatrix_one]

private theorem rowPermutation_mul_apply {κ : Type*} (A : Matrix (Rows C b) κ R)
    (x : Rows C b) (y : κ) :
    (rowPermutation (R := R) (b := b) hC ht * A) x y = A (rowTranslation hC ht x) y := by
  have h : rowPermutation hC ht * A = A.submatrix (rowTranslation hC ht) id :=
    PEquiv.toMatrix_toPEquiv_mul _ A
  exact congrArg (fun M : Matrix (Rows C b) κ R => M x y) h

private theorem mul_rowPermutation_apply {κ : Type*} (A : Matrix κ (Rows C b) R)
    (x : κ) (y : Rows C b) :
    (A * rowPermutation (R := R) (b := b) hC ht) x y = A x (rowTranslation hC ht y) := by
  have h : A * rowPermutation hC ht = A.submatrix id (rowTranslation hC ht).symm :=
    PEquiv.mul_toMatrix_toPEquiv A _
  exact congrArg (fun M : Matrix κ (Rows C b) R => M x y) h

private theorem unsigned_xorTranslate (w : Fin 9 → R) (t x y : Q 9) :
    unsigned w (xorTranslate t x) (xorTranslate t y) = unsigned w x y := by
  unfold unsigned
  apply Finset.sum_congr rfl
  intro k _
  have hflip : xorTranslate t (BalancedCriticalSpectrum.flip x k) =
      BalancedCriticalSpectrum.flip (xorTranslate t x) k := translate_flip t x k
  have hinj : Function.Injective (xorTranslate t) :=
    (show Function.Involutive (xorTranslate t) from translate_translate t).injective
  simp only [← hflip, hinj.eq_iff]

/-- Translating both indices preserves the weighted biadjacency. -/
theorem biadjacency_reindex_xorTranslate (w : Fin 9 → R) :
    Matrix.reindex (rowTranslation (b := b) hC ht) (interiorTranslation (b := b) hC ht)
      (biadjacency w C b) = biadjacency w C b := by
  ext x y
  change unsigned w (xorTranslate t x.val.val) (xorTranslate t y.val.val) =
    unsigned w x.val.val y.val.val
  exact unsigned_xorTranslate w t _ _

/-- The row Gram of the full interior weighted biadjacency. -/
abbrev interiorGram (w : Fin 9 → R) (C : Finset (Q 9)) (b : Bool) :
    Matrix (Rows C b) (Rows C b) R :=
  biadjacency w C b * (biadjacency w C b)ᵀ

/-- Column reindexing cancels in the finite sum defining the Gram. -/
theorem gram_reindex_xorTranslate (w : Fin 9 → R) :
    Matrix.reindex (rowTranslation (b := b) hC ht) (rowTranslation (b := b) hC ht)
      (interiorGram w C b) = interiorGram w C b := by
  let e := rowTranslation (b := b) hC ht
  let f := interiorTranslation (b := b) hC ht
  let M := biadjacency w C b
  change (M * Mᵀ).submatrix e.symm e.symm = M * Mᵀ
  rw [← Matrix.submatrix_mul_equiv M Mᵀ e.symm f.symm e.symm, ← Matrix.transpose_submatrix]
  change Matrix.reindex e f M * (Matrix.reindex e f M)ᵀ = M * Mᵀ
  rw [show Matrix.reindex e f M = M from biadjacency_reindex_xorTranslate hC ht w]

/-- The row permutation commutes with the Gram for all coordinate weightings. -/
theorem rowPermutation_mul_gram (w : Fin 9 → R) :
    rowPermutation hC ht * interiorGram w C b = interiorGram w C b * rowPermutation hC ht := by
  let e := rowTranslation (b := b) hC ht
  let G := interiorGram w C b
  have hG (x y : Rows C b) : G (e x) (e y) = G x y :=
    congrArg (fun A : Matrix (Rows C b) (Rows C b) R => A x y)
      (gram_reindex_xorTranslate hC ht w)
  ext x y
  rw [rowPermutation_mul_apply, mul_rowPermutation_apply]
  change G (e x) y = G x (e y)
  have he : e (e y) = y := rowTranslation_involutive hC ht y
  simpa only [he] using hG x (e y)

/-- The same commutation identity for the weighted saturation defect. -/
theorem rowPermutation_mul_defect (w : Fin 9 → R) :
    rowPermutation hC ht * defect w (biadjacency w C b) =
      defect w (biadjacency w C b) * rowPermutation hC ht := by
  unfold defect
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, show rowPermutation hC ht * interiorGram w C b =
      interiorGram w C b * rowPermutation hC ht from rowPermutation_mul_gram hC ht w]

/-- The sign of a vertex at the designated coordinate. -/
def coordinateSign (i : Fin 9) (x : Q 9) : R :=
  if x i = true then -1 else 1

/-- The coordinate sign involution on the retained rows. -/
def rowCoordinateSign (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :
    Matrix (Rows C b) (Rows C b) R :=
  Matrix.diagonal fun x => coordinateSign i x.val.val

private theorem coordinateSign_sq (i : Fin 9) (x : Q 9) :
    coordinateSign (R := R) i x * coordinateSign i x = 1 := by
  cases hx : x i <;> simp [coordinateSign, hx]

theorem rowCoordinateSign_sq (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :
    rowCoordinateSign (R := R) C b i * rowCoordinateSign C b i = 1 := by
  rw [rowCoordinateSign, Matrix.diagonal_mul_diagonal']
  simp only [coordinateSign_sq, Matrix.diagonal_one]

/-- The coordinate sign anticommutes with translation when the period flips that bit. -/
theorem rowCoordinateSign_mul_rowPermutation (i : Fin 9) (hi : t i = true) :
    rowCoordinateSign (R := R) C b i * rowPermutation hC ht =
      -(rowPermutation hC ht * rowCoordinateSign C b i) := by
  let e := rowTranslation (b := b) hC ht
  let s (x : Rows C b) : R := coordinateSign i x.val.val
  have hs (x : Rows C b) : s (e x) = -s x := by
    change coordinateSign i (xorTranslate t x.val.val) = -coordinateSign i x.val.val
    cases hx : x.val.val i <;> simp [coordinateSign, xorTranslate, hi, hx]
  ext x y
  rw [Matrix.neg_apply, rowPermutation_mul_apply]
  change (Matrix.diagonal s * e.permMatrix R) x y = -Matrix.diagonal s (e x) y
  rw [Matrix.diagonal_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply]
  by_cases h : e x = y
  · subst y
    simp [hs]
  · rw [Matrix.diagonal_apply_ne _ h]
    simp [Ne.symm h]

/-- Replace a single coordinate weight by its additive inverse. -/
def negateWeight (i : Fin 9) (w : Fin 9 → R) (k : Fin 9) : R :=
  if k = i then -w k else w k

private theorem negateWeight_apply_flip (w : Fin 9 → R) (i k : Fin 9) (x : Q 9) :
    negateWeight i w k =
      coordinateSign i x * w k * coordinateSign i (BalancedCriticalSpectrum.flip x k) := by
  by_cases hk : k = i
  · subst k
    cases hx : x i <;> simp [negateWeight, coordinateSign, BalancedCriticalSpectrum.flip, hx]
  · have hflip : BalancedCriticalSpectrum.flip x k i = x i :=
      Function.update_of_ne (Ne.symm hk) _ _
    cases hx : x i <;> simp [negateWeight, hk, coordinateSign, hflip, hx]

private theorem unsigned_negateWeight (w : Fin 9 → R) (i : Fin 9) (x y : Q 9) :
    unsigned (negateWeight i w) x y = coordinateSign i x * unsigned w x y * coordinateSign i y := by
  simp only [unsigned, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : BalancedCriticalSpectrum.flip x k = y
  · subst y
    simpa only [ite_true] using negateWeight_apply_flip w i k x
  · simp [hk]

/-- Negating one weight multiplies the biadjacency by the endpoint signs. -/
theorem biadjacency_negateWeight (w : Fin 9 → R) (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :
    biadjacency (negateWeight i w) C b =
      rowCoordinateSign C b i * biadjacency w C b *
        Matrix.diagonal (fun y : Interior C b => coordinateSign i y.val.val) := by
  ext x y
  rw [rowCoordinateSign, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact unsigned_negateWeight w i x.val.val y.val.val

/-- Negating one weight conjugates the Gram by the retained row signs. -/
theorem gram_negateWeight (w : Fin 9 → R) (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :
    interiorGram (negateWeight i w) C b =
      rowCoordinateSign C b i * interiorGram w C b * rowCoordinateSign C b i := by
  let M := biadjacency w C b
  let J := rowCoordinateSign (R := R) C b i
  let K := Matrix.diagonal (fun y : Interior C b => coordinateSign (R := R) i y.val.val)
  have hK : K * K = 1 := by
    change Matrix.diagonal _ * Matrix.diagonal _ = _
    rw [Matrix.diagonal_mul_diagonal']
    simp only [coordinateSign_sq, Matrix.diagonal_one]
  have hJt : Jᵀ = J := Matrix.diagonal_transpose _
  have hKt : Kᵀ = K := Matrix.diagonal_transpose _
  change biadjacency (negateWeight i w) C b *
    (biadjacency (negateWeight i w) C b)ᵀ = J * (M * Mᵀ) * J
  rw [show biadjacency (negateWeight i w) C b = J * M * K from biadjacency_negateWeight w C b i,
    Matrix.transpose_mul, Matrix.transpose_mul, hJt, hKt]
  calc
    _ = J * M * (K * K) * Mᵀ * J := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hK, Matrix.mul_one, Matrix.mul_assoc J M Mᵀ]

/-- Negating one weight conjugates the defect by the same row signs. -/
theorem defect_negateWeight (w : Fin 9 → R) (C : Finset (Q 9)) (b : Bool) (i : Fin 9) :
    defect (negateWeight i w) (biadjacency (negateWeight i w) C b) =
      rowCoordinateSign C b i * defect w (biadjacency w C b) * rowCoordinateSign C b i := by
  have hq : (∑ k, negateWeight i w k ^ 2) = ∑ k, w k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k = i <;> simp [negateWeight, hk]
  unfold defect
  change (∑ k, negateWeight i w k ^ 2) • 1 - interiorGram (negateWeight i w) C b =
    rowCoordinateSign C b i * ((∑ k, w k ^ 2) • 1 - interiorGram w C b) * rowCoordinateSign C b i
  rw [hq, gram_negateWeight]
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    rowCoordinateSign_sq]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

open scoped Matrix Polynomial
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9IsotropicHuang (parity)
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private unsigned from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram

private def axisWeight {R : Type*} [One R] (i : Fin 9) (s : R) (k : Fin 9) : R :=
  if k = i then s else 1

open Classical in
private theorem eval_axis_defect (C : Finset (Q 9)) (b : Bool) (i : Fin 9) (s : ℝ) :
    let W := axisWeight i (Polynomial.X : ℝ[X])
    let w := axisWeight i s
    (Polynomial.evalRingHom s).mapMatrix (defect W (biadjacency W C b)) =
      defect w (biadjacency w C b) := by
  dsimp only
  let W := axisWeight i (Polynomial.X : ℝ[X])
  let w := axisWeight i s
  let e := Polynomial.evalRingHom s
  have hw (k : Fin 9) : e (W k) = w k := by
    by_cases hk : k = i <;> simp [e, W, w, axisWeight, hk]
  have hM : (biadjacency W C b).map e = biadjacency w C b := by
    ext x y
    change e (unsigned W x.val.val y.val.val) = unsigned w x.val.val y.val.val
    unfold unsigned
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp [hw]
  change (defect W (biadjacency W C b)).map e = defect w (biadjacency w C b)
  unfold defect
  rw [Matrix.map_sub e (map_sub e), Matrix.map_smul' e _ _ (map_mul e),
    Matrix.map_one e (map_zero e) (map_one e), Matrix.map_mul, Matrix.transpose_map, hM]
  simp only [map_sum, map_pow, hw]

open Classical in
/-- A connected cubic support that attains the weighted Gram bound at all
positive weights has no nonzero even XOR period. -/
theorem no_nonzero_even_period_of_universal_gram
    (C : Finset (Q 9))
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hSat : ∀ (w : Fin 9 → ℝ), (∀ i, 0 < w i) →
      ∃ u : Rows C false → ℝ, (∀ x, 0 < u x) ∧
        interiorGram w C false *ᵥ u = (∑ i, w i ^ 2) • u)
    (t : Q 9) (ht : parity t = false) (hperiod : ∀ x ∈ C, xorTranslate t x ∈ C) :
    ∀ i, t i = false := by
  classical
  intro i
  by_contra hi
  have hit : t i = true := Bool.eq_true_of_not_eq_false hi
  let b := false
  let W := axisWeight i (Polynomial.X : ℝ[X])
  let F := defect W (biadjacency W C b)
  let A (s : ℝ) := interiorGram (axisWeight i s) C b
  let q (s : ℝ) := ∑ a, axisWeight i s a ^ 2
  let e := rowTranslation (b := b) hperiod ht
  let P : Matrix (Rows C b) (Rows C b) ℝ := rowPermutation hperiod ht
  let J : Matrix (Rows C b) (Rows C b) ℝ := rowCoordinateSign C b i
  have hF (s : ℝ) : (Polynomial.evalRingHom s).mapMatrix F =
      q s • (1 : Matrix (Rows C b) (Rows C b) ℝ) - A s :=
    eval_axis_defect C b i s
  have hpos (s : ℝ) (hs : 0 < s) (k : Fin 9) : 0 < axisWeight i s k := by
    unfold axisWeight
    split <;> positivity
  have hA (s : ℝ) (hs : 0 < s) : (A s).IsIrreducible :=
    Q9InternalGramConnected.isIrreducible_internal_gram _ (hpos s hs) C b hrC hcC
  have hE (s : ℝ) (x y : Rows C b) : A s (e x) (e y) = A s x y :=
    congrArg (fun M : Matrix (Rows C b) (Rows C b) ℝ => M x y)
      (gram_reindex_xorTranslate hperiod ht (axisWeight i s))
  have hu (s : ℝ) (hs : 0 < s) :
      ∃ u : Rows C b → ℝ, (∀ x, 0 < u x) ∧ A s *ᵥ u = q s • u := by
    exact hSat (axisWeight i s) (hpos s hs)
  have hrows : Nonempty (Rows C b) := by
    obtain ⟨x⟩ := hcC.nonempty
    let G := (hypercube 9).induce (C : Set (Q 9))
    have hdeg : 0 < G.degree x := by rw [hrC.degree_eq]; decide
    obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj x).mp hdeg
    have hxy := cubeParity_ne_of_adj hy
    by_cases hx : parity x.val = b
    · exact ⟨⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩⟩
    · have hyb : parity y.val = b := by
        cases h : parity x.val <;> cases h' : parity y.val <;> simp_all [b]
      exact ⟨⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyb⟩⟩⟩
  have hP : P * P = 1 := rowPermutation_sq hperiod ht
  have hJ : J * J = 1 := rowCoordinateSign_sq C b i
  have hanti : P * J = -(J * P) := by
    have h : J * P = -(P * J) := rowCoordinateSign_mul_rowPermutation hperiod ht i hit
    rw [h, neg_neg]
  have hcomm : P * (Polynomial.evalRingHom (-1 : ℝ)).mapMatrix F =
      (Polynomial.evalRingHom (-1 : ℝ)).mapMatrix F * P := by
    rw [hF]
    exact rowPermutation_mul_defect hperiod ht (axisWeight i (-1 : ℝ))
  have hchange : (Polynomial.evalRingHom (1 : ℝ)).mapMatrix F * J =
      J * (Polynomial.evalRingHom (-1 : ℝ)).mapMatrix F := by
    have hw : negateWeight i (axisWeight i (1 : ℝ)) = axisWeight i (-1 : ℝ) := by
      funext k
      by_cases hk : k = i <;> simp [negateWeight, axisWeight, hk]
    have h : (Polynomial.evalRingHom (-1 : ℝ)).mapMatrix F =
        J * (Polynomial.evalRingHom (1 : ℝ)).mapMatrix F * J := by
      rw [eval_axis_defect C b i (-1), eval_axis_defect C b i 1, ← hw]
      exact defect_negateWeight (axisWeight i (1 : ℝ)) C b i
    rw [h]
    symm
    calc
      _ = (J * J) * ((Polynomial.evalRingHom (1 : ℝ)).mapMatrix F * J) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.one_mul]
  have hfixed : ∀ v : Rows C b → ℝ,
      (Polynomial.evalRingHom (1 : ℝ)).mapMatrix F *ᵥ v = 0 → P *ᵥ v = v := by
    intro v hv
    rw [hF, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
    obtain ⟨u, hupos, heig⟩ := hu 1 (by norm_num)
    rw [show P *ᵥ v = v ∘ e from rowPermutation_mulVec hperiod ht v]
    exact funext (Matrix.eigenvector_fixed_by_perm_of_pos_eigenvector (hA 1 (by norm_num))
      e (hE 1) hupos heig hv.symm)
  apply Matrix.not_forall_pos_fixed_kernel_of_anticommute F P J hP hJ hanti hcomm hchange hfixed
  intro s hs
  obtain ⟨u, hupos, heig⟩ := hu s hs
  refine ⟨u, Pi.ne_zero_of_pos hupos, ?_, ?_⟩
  · rw [show P *ᵥ u = u ∘ e from rowPermutation_mulVec hperiod ht u]
    exact funext (Matrix.eigenvector_fixed_by_perm_of_pos_eigenvector (hA s hs)
      e (hE s) hupos heig heig)
  · rw [hF, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig, sub_self]


end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9BoundaryGram (Interior)
open Q9IsotropicHuang (parity)
open D5.S3.Combinatorics.Graph.PerronFrobenius.IrrationalQuadraticBipartition
  (preserves_bipartition_of_sq_rat)
open private cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private translate_translate from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.HuangTranslationObstruction
open private unsigned unsigned_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram
open Q9InternalGramConnected (parityEquiv unsigned_pos_iff_adj)

open BalancedCriticalSpectrum (flip)

private theorem unsigned_symm {R : Type*} [CommRing R] (w : Fin 9 → R) (x y : Q 9) :
    unsigned w x y = unsigned w y x := by
  unfold unsigned
  apply Finset.sum_congr rfl
  intro i _
  have hflip : flip x i = y ↔ flip y i = x := by
    constructor <;> intro h <;> rw [← h, BalancedCriticalSpectrum.flip_flip]
  simp only [hflip]

private def oddPeriodWeight (i : Fin 9) : ℚ :=
  if i = 0 then 2 else 1

unseal Nat.sqrt.iter in
private theorem irrational_sqrt_twelve : Irrational (Real.sqrt 12) := by decide

open Classical in
/-- A connected cubic support that attains the weighted Gram bound at all
positive weights has no odd XOR period. -/
theorem no_odd_period_of_universal_gram
    (C : Finset (Q 9))
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hSat : ∀ (w : Fin 9 → ℝ), (∀ i, 0 < w i) →
      ∃ u : Rows C false → ℝ, (∀ x, 0 < u x) ∧
        interiorGram w C false *ᵥ u = (∑ i, w i ^ 2) • u)
    (t : Q 9) (ht : parity t = true) (hperiod : ∀ x ∈ C, xorTranslate t x ∈ C) :
    False := by
  classical
  let I := Rows C false ⊕ Interior C false
  let e : I ≃ (C : Set (Q 9)) := parityEquiv C false
  let X (a : I) : Q 9 := (e a).val
  let w (i : Fin 9) : ℝ := (oddPeriodWeight i : ℝ)
  have hw (i : Fin 9) : 0 < w i := by
    by_cases hi : i = 0 <;> norm_num [w, oddPeriodWeight, hi]
  have hw_sq : (∑ i, w i ^ 2) = 12 := by
    have hterm (i : Fin 9) : w i ^ 2 = 1 + if i = 0 then (3 : ℝ) else 0 := by
      by_cases hi : i = 0 <;> norm_num [w, oddPeriodWeight, hi]
    simp only [hterm, Finset.sum_add_distrib, Fintype.sum_ite_eq', Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  let A : Matrix I I ℚ := fun a b => unsigned oddPeriodWeight (X a) (X b)
  let R := A.map (algebraMap ℚ ℝ)
  have hR (a b : I) : R a b = unsigned w (X a) (X b) := by
    change (algebraMap ℚ ℝ) (unsigned oddPeriodWeight (X a) (X b)) = _
    simp only [unsigned, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp [w]
  have hSymm : R.IsSymm := by
    ext a b
    simp only [Matrix.transpose_apply, hR]
    exact unsigned_symm w (X b) (X a)
  have hpos (a b : I) : 0 < R a b ↔ (hypercube 9).Adj (X a) (X b) := by
    rw [hR]
    exact unsigned_pos_iff_adj w hw _ _
  let M := biadjacency w C false
  have hrow (x : Rows C false) : parity (X (.inl x)) = false :=
    (Finset.mem_filter.mp x.property).2
  have hcol (y : Interior C false) : parity (X (.inr y)) = true :=
    Bool.eq_true_of_not_eq_false y.val.property
  have hblock : R = Matrix.fromBlocks 0 M Mᵀ 0 := by
    ext (a | a) (b | b)
    · rw [hR, Matrix.fromBlocks_apply₁₁]
      exact unsigned_zero w (fun h => cubeParity_ne_of_adj h ((hrow a).trans (hrow b).symm))
    · exact hR _ _
    · rw [hR, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply]
      exact unsigned_symm w (X (.inr a)) (X (.inl b))
    · rw [hR, Matrix.fromBlocks_apply₂₂]
      exact unsigned_zero w (fun h => cubeParity_ne_of_adj h ((hcol a).trans (hcol b).symm))
  have hgraph (a b : I) : (Matrix.positiveBiadjacencyGraph M).Adj a b ↔ 0 < R a b := by
    rw [hblock]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.positiveBiadjacencyGraph]
  have hneighbor (a : I) : ∃ b : I, 0 < R a b := by
    let G := (hypercube 9).induce (C : Set (Q 9))
    have hdegree : 0 < G.degree (e a) := by
      rw [hrC.degree_eq]
      decide
    obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj (e a)).mp hdegree
    refine ⟨e.symm y, (hpos _ _).mpr ?_⟩
    change (hypercube 9).Adj (e a).val (e (e.symm y)).val
    rw [e.apply_symm_apply]
    exact hy
  let : Quiver I := R.toQuiver
  have hconn : Quiver.IsStronglyConnected I := by
    intro a b
    have hG := Q9InternalGramConnected.positiveBiadjacencyGraph_connected w hw C false hcC
    have hab := (SimpleGraph.reachable_iff_reflTransGen
      (G := Matrix.positiveBiadjacencyGraph M) a b).mp (hG.preconnected a b)
    induction hab with
    | refl => exact ⟨Quiver.Path.nil⟩
    | tail _ hadj ih => exact ⟨ih.some.cons ⟨(hgraph _ _).mp hadj⟩⟩
  obtain ⟨x⟩ := hcC.nonempty
  obtain ⟨y, hy⟩ := hneighbor (e.symm x)
  have hEdge : e.symm x ⟶ y := ⟨hy⟩
  have hIrred : R.IsIrreducible := by
    refine ⟨?_, hconn.isSStronglyConnected_of_hom hEdge⟩
    intro a b
    rw [hR]
    unfold unsigned
    exact Finset.sum_nonneg fun i _ => ite_nonneg (hw i).le le_rfl
  let ρ : ℝ := Real.sqrt 12
  have hρpos : 0 < ρ := Real.sqrt_pos.2 (by norm_num)
  have hρsq : ρ ^ 2 = (12 : ℝ) := Real.sq_sqrt (by norm_num)
  have hρirr : Irrational ρ := irrational_sqrt_twelve
  obtain ⟨u, hu, hGram⟩ := hSat w hw
  change (M * Mᵀ) *ᵥ u = (∑ i, w i ^ 2) • u at hGram
  rw [hw_sq, ← hρsq] at hGram
  -- Cubicity supplies a positive summand for each column of the lifted vector.
  let v : Interior C false → ℝ := ρ⁻¹ • (Mᵀ *ᵥ u)
  have hMnonneg (a : Rows C false) (b : Interior C false) : 0 ≤ M a b := by
    change 0 ≤ unsigned w (X (.inl a)) (X (.inr b))
    rw [← hR]
    exact hIrred.nonneg _ _
  have hv (b : Interior C false) : 0 < v b := by
    obtain ⟨a | c, ha⟩ := hneighbor (.inr b)
    · have hMpos : 0 < M a b := by
        simpa only [hblock, Matrix.fromBlocks_apply₂₁, Matrix.transpose_apply] using ha
      change 0 < ρ⁻¹ * (∑ a, M a b * u a)
      exact mul_pos (inv_pos.mpr hρpos)
        (Finset.sum_pos' (fun j _ => mul_nonneg (hMnonneg j b) (hu j).le)
          ⟨a, Finset.mem_univ _, mul_pos hMpos (hu a)⟩)
    · simp [hblock] at ha
  have hv_row : M *ᵥ v = ρ • u := by
    simp only [v, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGram, smul_smul]
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hρpos.ne', one_mul]
  have hu_col : Mᵀ *ᵥ u = ρ • v := by
    simp only [v, smul_smul, mul_inv_cancel₀ hρpos.ne', one_smul]
  let f : I → ℝ := Sum.elim u v
  have hfpos (a : I) : 0 < f a := by
    rcases a with a | a
    · exact hu a
    · exact hv a
  have hf : R *ᵥ f = ρ • f := by
    rw [hblock, Matrix.fromBlocks_mulVec]
    change Sum.elim (0 *ᵥ u + M *ᵥ v) (Mᵀ *ᵥ u + 0 *ᵥ v) = _
    rw [Matrix.zero_mulVec, Matrix.zero_mulVec, zero_add, add_zero, hv_row, hu_col]
    funext a
    cases a <;> rfl
  let shift (a : (C : Set (Q 9))) : (C : Set (Q 9)) :=
    ⟨xorTranslate t a.val, hperiod _ a.property⟩
  have hshift : Function.Involutive shift := fun a =>
    Subtype.ext (translate_translate t a.val)
  let p : Equiv.Perm I := (e.trans hshift.toPerm).trans e.symm
  have hpX (a : I) : X (p a) = xorTranslate t (X a) := by
    change (e (e.symm (shift (e a)))).val = _
    rw [e.apply_symm_apply]
  have hp (a b : I) : A (p a) (p b) = A a b := by
    change unsigned oddPeriodWeight (X (p a)) (X (p b)) = _
    rw [hpX, hpX]
    exact unsigned_xorTranslate oddPeriodWeight t (X a) (X b)
  have hcolor {a b : I} (hab : 0 < R a b) : parity (X b) = !parity (X a) :=
    Bool.eq_not_of_ne (cubeParity_ne_of_adj ((hpos a b).mp hab)).symm
  have hsq_rat : ρ ^ 2 = ((12 : ℚ) : ℝ) := by simpa using hρsq
  have hpColor := preserves_bipartition_of_sq_rat A hIrred hSymm p hp
    hρirr hsq_rat hfpos hf (fun a => parity (X a)) hcolor (e.symm x)
  rw [hpX, parity_xorTranslate, ht] at hpColor
  have odd_add_ne (b : Bool) : (true : Bool) + b ≠ b := by
    cases b <;> decide
  exact odd_add_ne _ hpColor


end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open Q9IsotropicHuang (parity)
open Q9BoundaryGram (Interior Exterior)
open Q9WeightedBoundaryGram (signed switched gram_split)
open private balanced_switch from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedBoundaryGram

/-- The signed retained-to-interior block, before any balance switch. -/
abbrev signedBiadjacency (w : Fin 9 → ℝ) (C : Finset (Q 9)) (b : Bool) :
    Matrix (Rows C b) (Interior C b) ℝ :=
  (signed w).submatrix (fun x => x.val.val) (fun y => y.val.val)

open Classical in
/-- A connected balanced cubic support with a singular signed Gram defect
admits a positive internal Gram eigenvector. -/
theorem exists_positive_gram_of_signed_defect_singular
    (C : Finset (Q 9)) (b : Bool)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hb : IsBalanced C) (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i)
    (hdet : (defect w (signedBiadjacency w C b)).det = 0) :
    ∃ u : Rows C b → ℝ, (∀ x, 0 < u x) ∧
      interiorGram w C b *ᵥ u = (∑ i, w i ^ 2) • u := by
  classical
  let r : Rows C b ↪ Q 9 := ⟨fun x => x.val.val, fun _ _ h => Subtype.ext (Subtype.ext h)⟩
  have hrp (x : Rows C b) : parity (r x) = b := (Finset.mem_filter.mp x.property).2
  obtain ⟨s, hs, hswitch⟩ := balanced_switch (R := ℝ) C hb
  let M := signedBiadjacency w C b
  let B := biadjacency w C b
  let S : Matrix (Rows C b) (Rows C b) ℝ := Matrix.diagonal (fun x => (s (r x) : ℝ))
  let T : Matrix (Interior C b) (Interior C b) ℝ :=
    Matrix.diagonal (fun y => (s y.val.val : ℝ))
  have hsq (x : Q 9) : (s x : ℝ) * (s x : ℝ) = 1 := by exact_mod_cast hs x
  have hS : S * S = 1 := by
    simp [S, hsq, Matrix.diagonal_one]
  have hT : T * T = 1 := by
    simp [T, hsq, Matrix.diagonal_one]
  have hSt : Sᵀ = S := Matrix.diagonal_transpose _
  have hTt : Tᵀ = T := Matrix.diagonal_transpose _
  have hB : B = S * M * T := by
    ext x y
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    exact (hswitch w (r x) x.val.property y.val.val y.property).symm
  have hGram : B * Bᵀ = S * (M * Mᵀ) * S := by
    rw [hB, Matrix.transpose_mul, Matrix.transpose_mul, hSt, hTt]
    calc
      _ = S * M * (T * T) * Mᵀ * S := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hT, Matrix.mul_one, Matrix.mul_assoc S M Mᵀ]
  have hD : defect w B = S * defect w M * S := by
    unfold defect
    rw [hGram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hS]
  have hdetB : (defect w B).det = 0 := by
    rw [hD, Matrix.det_mul, Matrix.det_mul, show (defect w M).det = 0 from hdet,
      mul_zero, zero_mul]
  let K := (switched w s).submatrix r (fun y : Exterior C b => y.val.val)
  have hGramSplit : K * Kᵀ = defect w B := by
    have hM : (switched w s).submatrix r (fun y : Interior C b => y.val.val) = B := by
      ext x y
      exact hswitch w (r x) x.val.property y.val.val y.property
    have h := gram_split w s hs C b r hrp
    dsimp only at h
    rwa [hM] at h
  obtain ⟨u, hu, _, heig⟩ := Matrix.exists_positive_gram_kernel_of_det_eq_zero
    (Q9InternalGramConnected.isIrreducible_internal_gram w hw C b hr hc) hGramSplit.symm hdetB
  exact ⟨u, hu, heig⟩

open Classical in
/-- A connected balanced cubic support whose signed Gram defect is always
singular has trivial XOR translation stabilizer. -/
theorem no_nonzero_period_of_signed_gram_saturation
    (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hb : IsBalanced C)
    (hSat : ∀ w : Fin 9 → ℝ, (∀ i, 0 < w i) → (defect w (signedBiadjacency w C false)).det = 0)
    (t : Q 9) (hperiod : ∀ x ∈ C, xorTranslate t x ∈ C) :
    t = fun _ => false := by
  have heig (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i) :=
    exists_positive_gram_of_signed_defect_singular C false hr hc hb w hw (hSat w hw)
  funext i
  cases hpar : parity t
  · exact no_nonzero_even_period_of_universal_gram C hr hc heig t hpar hperiod i
  · exact (no_odd_period_of_universal_gram C hr hc heig t hpar hperiod).elim


end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ActualAperiodicity

open scoped Matrix
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open ComponentBoundary
open Q9ComponentSaturation (componentDefect componentDefect_det_eq componentParityFinset
  exists_two_weighted_singular_components)
open Q9IsotropicHuang (parity)
open Q9WeightedBoundaryGram (signed)
open Q9WeightedSaturation (Rows defect signedBiadjacency xorTranslate
  no_nonzero_period_of_signed_gram_saturation)
open TwoBalancedComponents (componentFinset mem_componentFinset zero_iff_of_reachable)
open private label rowEmbedding row_parity signedDefect signed_defect_restrict
  unit_kernel_extension from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ComponentSaturation
open private componentFinset_regular_and_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents

private abbrev Comp (U : Finset (Q 9)) :=
  ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent

private theorem component_connected (U : Finset (Q 9)) (K : Comp U) :
    ((hypercube 9).induce (componentFinset U K : Set (Q 9))).Connected := by
  classical
  let f (x : (componentFinset U K : Set (Q 9))) : K :=
    let hx := (mem_componentFinset U K x.val).mp x.property
    ⟨⟨x.val, hx.choose⟩, hx.choose_spec⟩
  let e := Equiv.ofBijective f ⟨fun _ _ h =>
    Subtype.ext (congrArg (fun y : K => y.val.val) h), fun y => by
      refine ⟨⟨y.val.val, (mem_componentFinset U K _).mpr ⟨y.val.property, y.property⟩⟩, ?_⟩
      exact Subtype.ext (Subtype.ext rfl)⟩
  let iso : ((hypercube 9).induce (componentFinset U K : Set (Q 9))) ≃g K.toSimpleGraph :=
    { toEquiv := e
      map_rel_iff' := Iff.rfl }
  exact iso.connected_iff.mpr K.connected_toSimpleGraph

open Classical in
private theorem regular_and_balanced_of_component_singular (U : Finset (Q 9)) (K : Comp U)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3)
    (hdet : (componentDefect (fun _ => (1 : ℝ)) U false K).det = 0) :
    ((hypercube 9).induce (componentFinset U K : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced (componentFinset U K) := by
  classical
  let J := {i : Rows U false // label i = K}
  let e : J ↪ Rows U false := ⟨Subtype.val, Subtype.val_injective⟩
  let r := e.trans (rowEmbedding U false)
  obtain ⟨u, hu, hk⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  change ((signedDefect (fun _ => (1 : ℝ)) U false (rowEmbedding U false)).submatrix e e) *ᵥ u =
    0 at hk
  rw [signed_defect_restrict] at hk
  obtain ⟨z, hOut, hEig, hRow⟩ := unit_kernel_extension U false r
    (fun i => row_parity i.val) (fun i => i.val.val.property) u hk
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra! h
    exact hu (funext h)
  have hzi : z (r i) ≠ 0 := by
    rw [hRow (r i) (row_parity i.val), r.injective.extend_apply]
    exact hi
  have he := (Q9SignedContactCells.unit_weight z).symm.trans hEig
  apply componentFinset_regular_and_balanced U z hdeg hOut he K
  intro y hy
  obtain ⟨hyU, hyK⟩ := (mem_componentFinset U K y).mp hy
  have hRi : i.val.val ∈ K.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mpr i.property
  exact fun hz => hzi ((zero_iff_of_reachable U z hdeg hOut he
    (K.reachable_of_mem_supp hRi hyK)).mpr hz)

open Classical in
/-- The component defect determinant is intrinsic to its selected support. -/
theorem signed_defect_det_eq_component (w : Fin 9 → ℝ) (U : Finset (Q 9))
    (b : Bool) (K : ((hypercube 9).induce (U : Set (Q 9))).ConnectedComponent) :
    (defect w (signedBiadjacency w (componentFinset U K) b)).det =
      (componentDefect w U b K).det := by
  classical
  let C := componentFinset U K
  let e : ↥(componentParityFinset U b K) ≃ Rows C b :=
    { toFun := fun x => ⟨⟨x.val, (Finset.mem_filter.mp x.property).1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp x.property).2⟩⟩
      invFun := fun x => ⟨x.val.val,
        Finset.mem_filter.mpr ⟨x.val.property, (Finset.mem_filter.mp x.property).2⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  let f : ↥(componentParityFinset U (!b) K) ≃ Q9BoundaryGram.Interior C b :=
    { toFun := fun y => ⟨⟨y.val, (Bool.not_eq_iff.mp
          (Finset.mem_filter.mp y.property).2.symm).symm⟩,
        (Finset.mem_filter.mp y.property).1⟩
      invFun := fun y => ⟨y.val.val,
        Finset.mem_filter.mpr ⟨y.property, Bool.eq_not_of_ne y.val.property⟩⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  let M := signedBiadjacency w C b
  rw [componentDefect_det_eq]
  change (defect w M).det = (defect w (M.submatrix e f)).det
  rw [← Matrix.det_submatrix_equiv_self e (defect w M)]
  apply congrArg Matrix.det
  unfold defect
  change (∑ a, w a ^ 2) • (1 : Matrix (Rows C b) (Rows C b) ℝ).submatrix e e -
    (M * Mᵀ).submatrix e e = _
  rw [Matrix.submatrix_one_equiv, ← Matrix.submatrix_mul_equiv M Mᵀ e f e,
    ← Matrix.transpose_submatrix]

open Classical in
/-- Every 258-point induced subcubic support in Q9 has two actual balanced
cubic components with universally singular signed defects and trivial XOR stabilizers. -/
theorem exists_two_aperiodic_components (U : Finset (Q 9)) (hU : U.card = 258)
    (hdeg : ∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) :
    ∃ K L : Comp U, K ≠ L ∧ ∀ A : Comp U, A = K ∨ A = L →
      ((hypercube 9).induce (componentFinset U A : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced (componentFinset U A) ∧
      (∀ w : Fin 9 → ℝ, (componentDefect w U false A).det = 0) ∧
      ∀ t : Q 9, (∀ x ∈ componentFinset U A, xorTranslate t x ∈ componentFinset U A) →
        t = fun _ => false := by
  obtain ⟨K, L, hKL, hs⟩ := exists_two_weighted_singular_components U hU hdeg false
  refine ⟨K, L, hKL, fun A hA => ?_⟩
  have hdet (w : Fin 9 → ℝ) : (componentDefect w U false A).det = 0 := by
    rcases hA with rfl | rfl
    · exact (hs w).1
    · exact (hs w).2
  obtain ⟨hr, hb⟩ := regular_and_balanced_of_component_singular U A hdeg (hdet fun _ => 1)
  refine ⟨hr, hb, hdet, no_nonzero_period_of_signed_gram_saturation _ hr (component_connected U A)
    hb (fun w _ => ?_)⟩
  exact (signed_defect_det_eq_component w U false A).trans (hdet w)


#print axioms exists_two_aperiodic_components

end D5.S3.Combinatorics.Graph.HypercubeCritical.Translation.Q9ActualAperiodicity
