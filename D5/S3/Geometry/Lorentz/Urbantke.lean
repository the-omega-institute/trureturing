/- GID: D5/S3/Geometry/Lorentz/Urbantke
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/Urbantke
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Universal Urbantke identities, chiral conformal reconstruction, and complex Lorentzian reality. -/

import OmegaBuild.Commands
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Geometry.Lorentz.Urbantke

open Matrix Polynomial Module
open scoped Matrix
/-- The oriented pair order is 01, 02, 03, 23, 31, 12. -/
abbrev PairIndex := Fin 3 ⊕ Fin 3
private abbrev Matrix4 (K : Type*) := Matrix (Fin 4) (Fin 4) K
private abbrev Matrix3 (K : Type*) := Matrix (Fin 3) (Fin 3) K
private abbrev PairMatrix (K : Type*) := Matrix PairIndex PairIndex K
private abbrev FormTriple (K : Type*) := Matrix PairIndex (Fin 3) K
private def pairLeft : PairIndex → Fin 4
  | .inl _ => 0
  | .inr i => ![2, 3, 1] i
private def pairRight : PairIndex → Fin 4
  | .inl i => i.succ
  | .inr i => ![3, 1, 2] i
private def pairSwap : PairIndex → PairIndex := Sum.elim Sum.inr Sum.inl
/-- The wedge pairing evaluated against the positive coordinate volume. -/
def W (K : Type*) [CommRing K] : PairMatrix K :=
  fromBlocks 0 1 1 0
/-- The exterior square in the oriented pair basis. -/
def exteriorSquare {K : Type*} [CommRing K] (A : Matrix4 K) : PairMatrix K :=
  fun p q => A (pairLeft p) (pairLeft q) * A (pairRight p) (pairRight q) -
    A (pairLeft p) (pairRight q) * A (pairRight p) (pairLeft q)
/-- The wedge Gram matrix of the three columns. -/
def wedgeGram {K : Type*} [CommRing K] (B : FormTriple K) : Matrix3 K := Bᵀ * W K * B
/-- The volume coefficient determined by the wedge Gram matrix. -/
def density {K : Type*} [Field K] (B : FormTriple K) : K :=
  (wedgeGram B).det / 8
section ExteriorRing
variable {K : Type*} [CommRing K]
private theorem exterior_transpose (A : Matrix4 K) :
    exteriorSquare Aᵀ = (exteriorSquare A)ᵀ :=
  Matrix.ext fun i j => by simp [exteriorSquare, mul_comm]
private theorem exterior_one :
    exteriorSquare (1 : Matrix4 K) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [exteriorSquare, pairLeft, pairRight, Matrix.one_apply]
private theorem exterior_smul (c : K) (A : Matrix4 K) :
    exteriorSquare (c • A) = c ^ 2 • exteriorSquare A := by
  ext i j
  simp only [exteriorSquare, Matrix.smul_apply, smul_eq_mul]
  ring
private theorem exterior_map {L : Type*} [CommRing L] (f : K →+* L) (A : Matrix4 K) :
    exteriorSquare (A.map f) = (exteriorSquare A).map f :=
  Matrix.ext fun i j => by simp [exteriorSquare, Matrix.map_apply]
private theorem exterior_mul (A B : Matrix4 K) :
    exteriorSquare (A * B) = exteriorSquare A * exteriorSquare B := by
  ext i j
  simp [Matrix.mul_apply, exteriorSquare, Fintype.sum_sum_type,
    Fin.sum_univ_succ, pairLeft, pairRight]
  ring
private theorem W_sq (K : Type*) [CommRing K] : W K * W K = 1 := by
  simp [W, fromBlocks_multiply, fromBlocks_one]

set_option maxHeartbeats 500000 in
private theorem exterior_wedge (A : Matrix4 K) :
    exteriorSquare A * W K * (exteriorSquare A)ᵀ = det A • W K := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, exteriorSquare, W,
      pairLeft, pairRight, Matrix.one_apply, Matrix.det_succ_row_zero A, Matrix.det_fin_three,
      Matrix.submatrix_apply, Fin.succAbove] <;> ring
end ExteriorRing
section ExteriorField
variable {K : Type*} [Field K]
private theorem exterior_det_ne (A : Matrix4 K) (hA : A.det ≠ 0) : (exteriorSquare A).det ≠ 0 := by
  apply Matrix.det_ne_zero_of_left_inverse (B := exteriorSquare A⁻¹)
  rw [← exterior_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), exterior_one]
private theorem exterior_inv (A : Matrix4 K) (hA : A.det ≠ 0) : exteriorSquare A⁻¹ = (exteriorSquare A)⁻¹ := by
  apply (Matrix.inv_eq_left_inv ?_).symm
  rw [← exterior_mul, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA), exterior_one]
private theorem pair_covers : ∀ i j : Fin 4, i ≠ j →
    ∃ p : PairIndex, (pairLeft p = i ∧ pairRight p = j) ∨
      (pairLeft p = j ∧ pairRight p = i) := by decide
private theorem proportional_minors (A : Matrix4 K) (c : K) (h : exteriorSquare A = c • (1 : PairMatrix K))
    {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) :
    let I : Matrix4 K := 1
    A i k * A j l - A i l * A j k = c * (I i k * I j l - I i l * I j k) := by
  dsimp only
  have hm (p q : PairIndex) :
      exteriorSquare A p q = c * exteriorSquare (1 : Matrix4 K) p q := by
    rw [h, exterior_one, Matrix.smul_apply, smul_eq_mul]
  obtain ⟨p, ⟨hp, hp'⟩ | ⟨hp, hp'⟩⟩ := pair_covers i j hij <;>
    obtain ⟨q, ⟨hq, hq'⟩ | ⟨hq, hq'⟩⟩ := pair_covers k l hkl <;>
    specialize hm p q <;> unfold exteriorSquare at hm <;> rw [hp, hp', hq, hq'] at hm <;>
    first | linear_combination hm | linear_combination -hm

/-- A nonzero scalar action on the oriented second exterior power forces a scalar matrix. -/
theorem exteriorSquare_eq_smul_id_imp_scalar (A : Matrix4 K) (c : K) (hc : c ≠ 0)
    (h : exteriorSquare A = c • (1 : PairMatrix K)) : ∃ a : K, a ≠ 0 ∧ A = a • (1 : Matrix4 K) := by
  have third : ∀ i k : Fin 4, ∃ j : Fin 4, j ≠ i ∧ j ≠ k := by decide
  have diag (i j : Fin 4) (hij : i ≠ j) :
      A i i * A j j - A i j * A j i = c := by
    simpa [Matrix.one_apply, hij, Ne.symm hij] using proportional_minors A c h hij hij
  have off (k i : Fin 4) (hki : k ≠ i) : A k i = 0 := by
    obtain ⟨j, hji, hjk⟩ := third i k
    have hr : A k i * A j j - A k j * A j i = 0 := by
      simpa [Matrix.one_apply, hki, hjk, Ne.symm hjk] using
        proportional_minors A c h (Ne.symm hjk) (Ne.symm hji)
    have hl : A k i * A i j - A k j * A i i = 0 := by
      simpa [Matrix.one_apply, hki, hjk, Ne.symm hjk] using
        proportional_minors A c h hki (Ne.symm hji)
    apply (mul_eq_zero.mp ?_).resolve_left hc
    linear_combination A i i * hr - A j i * hl - A k i * diag i j (Ne.symm hji)
  have prod (i j : Fin 4) (hij : i ≠ j) : A i i * A j j = c := by
    simpa [off i j hij, off j i (Ne.symm hij)] using diag i j hij
  have nz (i : Fin 4) : A i i ≠ 0 := by
    obtain ⟨j, hji, _⟩ := third i i
    intro hi
    exact hc (by rw [← prod i j (Ne.symm hji), hi, zero_mul])
  refine ⟨A 0 0, nz 0, ?_⟩
  ext i k
  by_cases hik : i = k
  · subst k
    obtain ⟨j, hji, hj0⟩ := third i 0
    have he := (prod i j (Ne.symm hji)).trans (prod 0 j (Ne.symm hj0)).symm
    simpa [Matrix.smul_apply] using mul_right_cancel₀ (nz j) he
  · simp [Matrix.smul_apply, hik, off i k hik]

/-- A proportional pair of exterior-square matrices determines a single conformal class. -/
theorem urbantke_conformal_uniqueness (g₁ g₂ : Matrix4 K) (h₁ : g₁.det ≠ 0) (c : K) (hc : c ≠ 0)
    (h : exteriorSquare g₂ = c • exteriorSquare g₁) : ∃ a : K, a ≠ 0 ∧ g₂ = a • g₁ := by
  have hg₁ := isUnit_iff_ne_zero.mpr h₁
  have he : exteriorSquare (g₂ * g₁⁻¹) = c • (1 : PairMatrix K) := by
    rw [exterior_mul, h, Matrix.smul_mul, ← exterior_mul, Matrix.mul_nonsing_inv _ hg₁,
      exterior_one]
  obtain ⟨a, ha, hA⟩ := exteriorSquare_eq_smul_id_imp_scalar _ c hc he
  refine ⟨a, ha, ?_⟩
  simpa [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hg₁, Matrix.smul_mul] using
    congrArg (fun M => M * g₁) hA
end ExteriorField
private theorem mul_W_apply {K : Type*} [CommRing K] (A : PairMatrix K)
    (i j : PairIndex) : (A * W K) i j = A i (pairSwap j) := by
  conv_lhs => rw [← fromBlocks_toBlocks A, W, fromBlocks_multiply]
  rcases i with i | i <;> rcases j with j | j <;>
    simp [pairSwap, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]
section Polynomial
variable {R T : Type*} [CommRing R] [CommRing T]
private def formRow (B : FormTriple R) (a b : Fin 4) : Fin 3 → R :=
  ![![0, B (.inl 0), B (.inl 1), B (.inl 2)],
    ![-B (.inl 0), 0, B (.inr 2), -B (.inr 1)],
    ![-B (.inl 1), -B (.inr 2), 0, B (.inr 0)],
    ![-B (.inl 2), B (.inr 1), -B (.inr 0), 0]] a b
private def triple (a b c : Fin 3 → R) : Matrix3 R := of ![a, b, c]
private def cubic (B : FormTriple R) : Matrix4 R :=
  fun a b => ∑ p : PairIndex, (
    (triple (formRow B a (pairLeft p)) (formRow B b (pairRight p)) (B (pairSwap p))).det -
    (triple (formRow B a (pairRight p)) (formRow B b (pairLeft p)) (B (pairSwap p))).det)
private theorem formRow_map (f : R →+* T) (B : FormTriple R) (a b : Fin 4) :
    formRow (B.map f) a b = f ∘ formRow B a b := by
  funext i
  fin_cases a <;> fin_cases b <;>
    simp [formRow, Pi.neg_apply, Matrix.map_apply]
private theorem cubic_map (f : R →+* T) (B : FormTriple R) : (cubic B).map f = cubic (B.map f) := by
  ext a b
  have h (u v w : Fin 3 → R) : (triple u v w).map f = triple (f ∘ u) (f ∘ v) (f ∘ w) := by
    ext i j
    fin_cases i <;> rfl
  simp only [Matrix.map_apply, cubic, map_sum, map_sub, formRow_map]
  apply Finset.sum_congr rfl
  intro p _
  simp only [f.map_det]
  change ((triple _ _ _).map f).det - ((triple _ _ _).map f).det = _
  simp only [h]
  rfl
private theorem map_W (f : R →+* T) : (W R).map f = W T := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [W, Matrix.one_apply]
private theorem wedgeGram_map (f : R →+* T) (B : FormTriple R) : (wedgeGram B).map f = wedgeGram (B.map f) := by
  simp only [wedgeGram, Matrix.map_mul, map_W]
  rfl
private theorem formRow_mul (B : FormTriple R) (C : Matrix3 R) (a b : Fin 4) :
    formRow (B * C) a b = formRow B a b ᵥ* C := by
  fin_cases a <;> fin_cases b <;> simp [formRow, Matrix.neg_vecMul] <;> rfl
private theorem cubic_mul (B : FormTriple R) (C : Matrix3 R) :
    cubic (B * C) = C.det • cubic B := by
  have ht (a b : Fin 3 → R) (p : PairIndex) :
      triple (a ᵥ* C) (b ᵥ* C) ((B * C) p) = triple a b (B p) * C := by
    ext i j
    fin_cases i <;> rfl
  ext a b
  simp only [cubic, formRow_mul, ht, det_mul, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end Polynomial

/-- The cubic density with the two alternating symbols and coefficient 1/12.
The internal alternating contraction is a determinant of three rows. Each oriented
complementary pair in the last two slots contributes twice. -/
def urbantke {K : Type*} [Field K] (B : FormTriple K) : Matrix4 K :=
  (1 / 6 : K) • cubic B

private theorem urbantke_mul {K : Type*} [Field K] (B : FormTriple K) (C : Matrix3 K) :
    urbantke (B * C) = C.det • urbantke B := by
  rw [urbantke, cubic_mul, smul_comm, ← urbantke]
private def graph {R : Type*} (E H : Matrix3 R) : FormTriple R
  | .inl i => E i
  | .inr i => H i
private theorem graph_mul {R : Type*} [CommRing R] (E H C : Matrix3 R) :
    graph E H * C = graph (E * C) (H * C) := by
  ext i j
  rcases i with i | i <;> rfl
private theorem wedgeGram_graph {R : Type*} [CommRing R] (H : Matrix3 R) :
    wedgeGram (graph 1 H) = H + Hᵀ := by
  ext i j
  simp [wedgeGram, W, graph, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, add_comm]
private def blockMetric {R : Type*} [Zero R] [One R] (A : Matrix3 R) : Matrix4 R :=
  !![1, 0, 0, 0; 0, A 0 0, A 0 1, A 0 2;
     0, A 1 0, A 1 1, A 1 2; 0, A 2 0, A 2 1, A 2 2]
private def symPart {K : Type*} [Field K] (H : Matrix3 K) :=
  (1 / 2 : K) • (H + Hᵀ)
private def shear {K : Type*} [Field K] (H : Matrix3 K) : Matrix4 K :=
  !![1, (H 2 1 - H 1 2) / 2, (H 0 2 - H 2 0) / 2, (H 1 0 - H 0 1) / 2;
     0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
private theorem det_blockMetric {R : Type*} [CommRing R] (A : Matrix3 R) : (blockMetric A).det = A.det := by
  rw [det_succ_row_zero]
  simp [blockMetric, Fin.sum_univ_succ]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl
private theorem det_shear {K : Type*} [Field K] (H : Matrix3 K) : (shear H).det = 1 := by
  rw [← det_transpose, det_succ_row_zero]
  simp [shear, Fin.sum_univ_succ, det_fin_three]
private theorem adjugate_fin_three {R : Type*} [CommRing R] (A : Matrix3 R) (i j : Fin 3) :
    A.adjugate i j =
      A (![1, 2, 0] j) (![1, 2, 0] i) * A (![2, 0, 1] j) (![2, 0, 1] i) -
      A (![1, 2, 0] j) (![2, 0, 1] i) * A (![2, 0, 1] j) (![1, 2, 0] i) := by
  rw [adjugate_apply, det_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.updateRow_apply] <;> ring
section Chart
variable {K : Type*} [Field K] [CharZero K]

set_option maxHeartbeats 1500000 in
private theorem urbantke_graph (H : Matrix3 K) :
    urbantke (graph 1 H) = (shear H)ᵀ * blockMetric (symPart H).adjugate * shear H := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [urbantke, cubic, formRow, triple, graph, pairSwap, pairLeft, pairRight, shear,
      blockMetric, symPart, adjugate_fin_three, det_fin_three, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul] <;> norm_num [Finset.filter_singleton, Fin.succ] <;> ring
private theorem graph_shear (H : Matrix3 K) :
    exteriorSquare ((shear H)ᵀ) * graph 1 (symPart H) = graph 1 H := by
  ext p j
  rcases p with p | p <;> fin_cases p <;> fin_cases j <;>
    simp [exteriorSquare, pairLeft, pairRight, shear, graph, symPart,
      Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.one_apply] <;> ring
omit [CharZero K] in
private theorem exterior_blockMetric (A : Matrix3 K) :
    exteriorSquare (blockMetric A) = fromBlocks A 0 0 (A.adjugate)ᵀ := by
  ext p q
  rcases p with i | i <;> rcases q with j | j <;>
    fin_cases i <;> fin_cases j <;>
    simp [exteriorSquare, pairLeft, pairRight, blockMetric, adjugate_fin_three]
private theorem block_mul_graph {R : Type*} [CommRing R] (A B C D E H : Matrix3 R) :
    fromBlocks A B C D * graph E H = graph (A * E + B * H) (C * E + D * H) := by
  ext i j
  rcases i with i | i <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, graph]
private def ChartIdentities (B : FormTriple K) : Prop :=
  (urbantke B)ᵀ = urbantke B ∧ (urbantke B).det = density B ^ 2 ∧
    exteriorSquare (urbantke B) * W K * B = density B • B
private theorem graph_identities (H : Matrix3 K) : ChartIdentities (graph 1 H) := by
  let S := symPart H
  have hS : Sᵀ = S := by simp [S, symPart, add_comm]
  have hA := (adjugate_transpose S).trans (congrArg adjugate hS)
  have hm : (blockMetric S.adjugate)ᵀ = blockMetric S.adjugate := by
    ext i j
    fin_cases i <;> fin_cases j <;> first | rfl | exact congrFun (congrFun hA _) _
  have hD : density (graph 1 H) = S.det := by
    have h : H + Hᵀ = (2 : K) • S := by simp [S, symPart, smul_smul]
    rw [density, wedgeGram_graph, h, det_smul]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [urbantke_graph, ← show S = symPart H from rfl]
    simp [transpose_mul, hm, Matrix.mul_assoc]
  · rw [hD, urbantke_graph, det_mul, det_mul, det_transpose, det_shear, one_mul, mul_one,
      det_blockMetric, det_adjugate]
    simp [S]
  let M := exteriorSquare (shear H)
  let G := graph (1 : Matrix3 K) S
  have hG : Mᵀ * G = graph 1 H := by
    simpa only [M, G, S, exterior_transpose] using graph_shear H
  have hM : M * W K * Mᵀ = W K := by simp [M, exterior_wedge, det_shear]
  have hb : exteriorSquare (blockMetric S.adjugate) * W K * G = S.det • G := by
    rw [exterior_blockMetric, adjugate_adjugate', W, fromBlocks_multiply]
    norm_num only [mul_zero, zero_mul, zero_add, add_zero, Matrix.mul_one, transpose_smul]
    rw [block_mul_graph]
    norm_num [adjugate_mul, hS]
    ext i j
    rcases i with i | i <;> rfl
  rw [urbantke_graph, exterior_mul, exterior_mul, exterior_transpose, hD]
  change Mᵀ * exteriorSquare (blockMetric S.adjugate) * M * W K * graph 1 H = S.det • graph 1 H
  rw [← hG, ← Matrix.mul_smul, ← hb]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (W K) Mᵀ G, ← Matrix.mul_assoc M (W K * Mᵀ) G,
    ← Matrix.mul_assoc M (W K) Mᵀ, hM]
private theorem chart_identities (E H : Matrix3 K) (hE : E.det ≠ 0) : ChartIdentities (graph E H) := by
  let G := graph 1 (H * E⁻¹)
  have hG : G * E = graph E H := by
    simp [G, graph_mul, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hE)]
  obtain ⟨hs, hd, he⟩ := graph_identities (H * E⁻¹)
  change (urbantke G)ᵀ = urbantke G at hs
  have hD : density (G * E) = E.det ^ 2 * density G := by
    have h : wedgeGram (G * E) = Eᵀ * wedgeGram G * E := by
      simp [wedgeGram, transpose_mul, Matrix.mul_assoc]
    rw [density, density, h, det_mul, det_mul, det_transpose]
    ring
  unfold ChartIdentities
  rw [← hG, urbantke_mul, hD, transpose_smul, hs, det_smul, hd, exterior_smul]
  refine ⟨rfl, by norm_num [G, mul_pow, ← pow_mul], ?_⟩
  rw [Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc (exteriorSquare _ * W K) G E,
    he, Matrix.smul_mul, mul_smul]
private theorem eval_eq_at_zero {p q r : K[X]} (hr : r ≠ 0)
    (h : ∀ t, r.eval t ≠ 0 → p.eval t = q.eval t) : p.eval 0 = q.eval 0 := by
  have hp : p - q = 0 := Polynomial.eq_zero_of_infinite_isRoot _ <|
    (Polynomial.finite_setOfPred_isRoot hr).infinite_compl.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Polynomial.IsRoot.def] at ht ⊢
      rw [Polynomial.eval_sub, h t ht, sub_self]
  rw [sub_eq_zero.mp hp]
private theorem all_graph_identities (E H : Matrix3 K) : ChartIdentities (graph E H) := by
  let EP := (-E).charmatrix
  let BP := graph EP (H.map Polynomial.C)
  let UP := Polynomial.C (1 / 6 : K) • cubic BP
  let DP := (wedgeGram BP).det * Polynomial.C (1 / 8 : K)
  let VP := exteriorSquare UP * W K[X] * BP
  have hEP (t : K) : EP.map (Polynomial.evalRingHom t) = E + t • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [EP, charmatrix, Matrix.scalar_apply, hij, add_comm]
  have hB (t : K) : BP.map (Polynomial.evalRingHom t) = graph (E + t • 1) H := by
    ext i j
    rcases i with i | i
    · exact congrFun (congrFun (hEP t) i) j
    · simp [BP, graph]
  have hU (t : K) : UP.map (Polynomial.evalRingHom t) = urbantke (graph (E + t • 1) H) := by
    ext i j
    have h := congrFun (congrFun (cubic_map (Polynomial.evalRingHom t) BP) i) j
    rw [hB] at h
    simpa [UP, urbantke, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] using
      congrArg (fun x => (1 / 6 : K) * x) h
  have hD (t : K) : DP.eval t = density (graph (E + t • 1) H) := by
    have h := (Polynomial.evalRingHom t).map_det (wedgeGram BP)
    change _ = ((wedgeGram BP).map (Polynomial.evalRingHom t)).det at h
    rw [wedgeGram_map, hB] at h
    simpa [DP, density, div_eq_mul_inv] using congrArg (fun x => x * (1 / 8 : K)) h
  have hV (t : K) : VP.map (Polynomial.evalRingHom t) =
      exteriorSquare (urbantke (graph (E + t • 1) H)) * W K * graph (E + t • 1) H := by
    dsimp only [VP]
    rw [Matrix.map_mul, Matrix.map_mul, map_W, ← exterior_map, hU, hB]
  have hr : EP.det ≠ 0 := (charpoly_monic (-E)).ne_zero
  have h (t : K) (ht : EP.det.eval t ≠ 0) := chart_identities (E + t • 1) H (by
    have he := (Polynomial.evalRingHom t).map_det EP
    change EP.det.eval t = (EP.map (Polynomial.evalRingHom t)).det at he
    rw [hEP] at he
    rwa [← he])
  have u (t : K) (i j : Fin 4) : (UP i j).eval t = urbantke (graph (E + t • 1) H) i j :=
    congrFun (congrFun (hU t) i) j
  have v (t : K) (i : PairIndex) (j : Fin 3) : (VP i j).eval t = _ :=
    congrFun (congrFun (hV t) i) j
  have d (t : K) : UP.det.eval t = (urbantke (graph (E + t • 1) H)).det := by
    exact ((Polynomial.evalRingHom t).map_det UP).trans (congrArg det (hU t))
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    have he := eval_eq_at_zero (p := UP j i) (q := UP i j) hr fun t ht => by
      rw [u, u]
      exact congrFun (congrFun (h t ht).1 i) j
    simpa only [u, transpose_apply, zero_smul, add_zero] using he
  · have he := eval_eq_at_zero (p := UP.det) (q := DP ^ 2) hr fun t ht => by
      simpa only [d, Polynomial.eval_pow, hD] using (h t ht).2.1
    simpa only [d, Polynomial.eval_pow, hD, zero_smul, add_zero] using he
  · ext i j
    have b (t : K) : (BP i j).eval t = graph (E + t • 1) H i j :=
      congrFun (congrFun (hB t) i) j
    have he := eval_eq_at_zero (p := VP i j) (q := DP * BP i j) hr fun t ht => by
      rw [v, Polynomial.eval_mul, hD, b]
      exact congrFun (congrFun (h t ht).2.2 i) j
    simpa only [v, Polynomial.eval_mul, hD, b, zero_smul, add_zero,
      Matrix.smul_apply, smul_eq_mul] using he

/-- The cubic Urbantke matrix is symmetric and satisfies both polynomial identities,
including on triples whose electric block or wedge Gram matrix is singular. -/
theorem urbantke_polynomial_identities (B : FormTriple K) :
    (urbantke B)ᵀ = urbantke B ∧
    (urbantke B).det = (wedgeGram B).det ^ 2 / 64 ∧
    exteriorSquare (urbantke B) * W K * B = density B • B := by
  have h : graph (fun i => B (.inl i)) (fun i => B (.inr i)) = B := by
    ext i j
    rcases i with i | i <;> rfl
  obtain ⟨hs, hd, he⟩ := h ▸ all_graph_identities (fun i => B (.inl i)) (fun i => B (.inr i))
  exact ⟨hs, hd.trans (by rw [density, div_pow]; norm_num), he⟩
end Chart
private theorem W_symm (K : Type*) [CommRing K] : (W K)ᵀ = W K := by
  simp [W, fromBlocks_transpose]
section Hodge
variable {K : Type*} [Field K]

/-- The covariant two-form Hodge operator with oriented volume coefficient `v`. -/
def hodge (g : Matrix4 K) (v : K) : PairMatrix K := (v • W K) * (exteriorSquare g)⁻¹
private theorem hodge_mul_exterior (g : Matrix4 K)
    (v : K) (hg : g.det ≠ 0) : hodge g v * exteriorSquare g = v • W K := by
  rw [hodge, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (exterior_det_ne g hg)),
    Matrix.mul_one]
private theorem hodge_self_adjoint (g : Matrix4 K)
    (v : K) (hs : gᵀ = g) : (hodge g v)ᵀ * W K = W K * hodge g v := by
  simp [hodge, transpose_mul, transpose_nonsing_inv, ← exterior_transpose, hs, W_symm,
    Matrix.mul_assoc, ← Matrix.mul_assoc (W K), W_sq]
private theorem hodge_square (g : Matrix4 K) (v : K) (hs : gᵀ = g) (hg : g.det ≠ 0) :
    hodge g v ^ 2 = (v ^ 2 / g.det) • (1 : PairMatrix K) := by
  have h := exterior_wedge g⁻¹
  rw [← exterior_transpose, transpose_nonsing_inv, hs, exterior_inv g hg,
    det_nonsing_inv, Ring.inverse_eq_inv] at h
  simp only [pow_two, hodge, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [Matrix.mul_assoc (W K), ← Matrix.mul_assoc (exteriorSquare g)⁻¹, h,
    Matrix.mul_smul, W_sq, smul_smul, div_eq_mul_inv]
private theorem hodge_trace (g : Matrix4 K) (v : K) (hs : gᵀ = g) (hg : g.det ≠ 0) : (hodge g v).trace = 0 := by
  let A := g⁻¹
  have hA : Aᵀ = A := by rw [show A = g⁻¹ from rfl, transpose_nonsing_inv, hs]
  have hij (i j : Fin 4) : A i j = A j i := congr_fun (congr_fun hA j) i
  rw [hodge, Matrix.smul_mul, trace_smul, ← exterior_inv g hg, trace_mul_comm]
  suffices (exteriorSquare A * W K).trace = 0 by rw [this, smul_zero]
  simp [trace, mul_W_apply, Fintype.sum_sum_type, Fin.sum_univ_three, pairSwap,
    exteriorSquare, pairLeft, pairRight, hij 1 0, hij 2 0, hij 3 0, hij 2 1, hij 3 1, hij 3 2]
  ring
private theorem chiral_rank (B : FormTriple K) (hQ : (wedgeGram B).det ≠ 0) :
    LinearIndependent K B.col ∧ finrank K (LinearMap.range B.mulVecLin) = 3 := by
  have hi : Function.Injective B.mulVec := by
    intro x y h
    apply mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hQ))
    simpa only [wedgeGram, ← mulVec_mulVec] using congrArg (fun z => Bᵀ *ᵥ (W K *ᵥ z)) h
  refine ⟨Matrix.mulVec_injective_iff.mp hi, ?_⟩
  rw [LinearMap.finrank_range_of_inj hi, Module.finrank_fin_fun]
variable [CharZero K]
private theorem chiral_eigenspaces (B : FormTriple K) (hQ : (wedgeGram B).det ≠ 0)
    (H : PairMatrix K) (hH : H ^ 2 = 1) (ht : H.trace = 0)
    (hs : Hᵀ * W K = W K * H) (hB : H * B = B) :
    (∀ x, H *ᵥ x = x ↔ ∃ y, B *ᵥ y = x) ∧
      (∀ x, H *ᵥ x = -x ↔ Bᵀ *ᵥ (W K *ᵥ x) = 0) := by
  let P : PairMatrix K := (1 / 2 : K) • (1 + H)
  have hPP : P * P = P := by
    rw [show P = (1 / 2 : K) • (1 + H) from rfl, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add H, Matrix.one_mul, Matrix.mul_one, ← pow_two, hH, smul_smul]
    module
  have hP := (LinearMap.isProj_range_iff_isIdempotentElem P.toLin').2 (by
    rw [isIdempotentElem_iff, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP])
  have hr : ((finrank K (LinearMap.range P.toLin') : ℕ) : K) = 3 := by
    rw [← hP.trace, Matrix.trace_toLin'_eq]
    norm_num [P, trace_smul, trace_add, trace_one, ht, Fintype.card_sum]
  have hPB : P * B = B := by
    simp only [P, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, hB]
    module
  have hrange : LinearMap.range B.mulVecLin = LinearMap.range P.toLin' := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro _ ⟨y, rfl⟩
      exact ⟨B *ᵥ y, by simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply,
        mulVec_mulVec, hPB]⟩
    · rw [(chiral_rank B hQ).2]
      have hPr : finrank K (LinearMap.range P.toLin') = 3 := by exact_mod_cast hr
      exact hPr.le
  have hp (x : PairIndex → K) : H *ᵥ x = x ↔ ∃ y, B *ᵥ y = x := by
    refine ⟨fun hx => ?_, fun ⟨y, hy⟩ => by rw [← hy, mulVec_mulVec, hB]⟩
    change x ∈ LinearMap.range B.mulVecLin
    rw [hrange]
    refine ⟨x, ?_⟩
    simp only [Matrix.toLin'_apply', Matrix.mulVecLin_apply, P, smul_mulVec, add_mulVec, one_mulVec, hx]
    module
  have hleft : Bᵀ * (W K * H) = Bᵀ * W K := by
    rw [← hs, ← Matrix.mul_assoc, ← transpose_mul, hB]
  have orth (x : PairIndex → K) : Bᵀ *ᵥ (W K *ᵥ (H *ᵥ x)) = Bᵀ *ᵥ (W K *ᵥ x) := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hleft, ← mulVec_mulVec]
  refine ⟨hp, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    have he := orth x
    rw [hx, mulVec_neg, mulVec_neg, neg_eq_iff_add_eq_zero, ← two_smul K,
      smul_eq_zero_iff_right (by norm_num : (2 : K) ≠ 0)] at he
    exact he
  · intro hx
    have hfix : H *ᵥ (x + H *ᵥ x) = x + H *ᵥ x := by
      rw [mulVec_add, mulVec_mulVec, ← pow_two, hH, one_mulVec, add_comm]
    obtain ⟨y, hy⟩ := (hp _).1 hfix
    have hy' : wedgeGram B *ᵥ y = 0 := by
      rw [wedgeGram, ← mulVec_mulVec, ← mulVec_mulVec, hy, mulVec_add, mulVec_add, orth, hx,
        add_zero]
    have hy0 := mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hQ))
      (hy'.trans (mulVec_zero _).symm)
    simpa [hy0, eq_comm, add_eq_zero_iff_neg_eq] using hy

/-- A nondegenerate wedge Gram form determines a three-dimensional chiral plane. -/
theorem urbantke_nondegenerate_iff_and_chiral_star (B : FormTriple K) :
    ((urbantke B).det ≠ 0 ↔ (wedgeGram B).det ≠ 0) ∧
    ((wedgeGram B).det ≠ 0 →
      let H := hodge (urbantke B) (density B)
      LinearIndependent K B.col ∧ finrank K (LinearMap.range B.mulVecLin) = 3 ∧
        H ^ 2 = 1 ∧ H * B = B ∧
        (∀ x, H *ᵥ x = x ↔ ∃ y, B *ᵥ y = x) ∧
        (∀ x, H *ᵥ x = -x ↔ Bᵀ *ᵥ (W K *ᵥ x) = 0)) := by
  obtain ⟨hs, hd, he⟩ := urbantke_polynomial_identities B
  have hd' : (urbantke B).det = density B ^ 2 := by rw [hd, density]; ring
  have hiff : (urbantke B).det ≠ 0 ↔ (wedgeGram B).det ≠ 0 := by simp [hd', density]
  refine ⟨hiff, fun hQ => ?_⟩
  have hU := hiff.2 hQ
  have h2 : hodge (urbantke B) (density B) ^ 2 = 1 := by
    rw [hodge_square _ _ hs hU, ← hd', div_self hU, one_smul]
  have hfix : hodge (urbantke B) (density B) * B = B := by
    have hm := congrArg (fun A : FormTriple K => (exteriorSquare (urbantke B))⁻¹ * A) he
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (exterior_det_ne _ hU)), Matrix.one_mul] at hm
    simpa [hodge, ← Matrix.mul_assoc, W_sq] using (congrArg (fun A : FormTriple K => W K * A) hm).symm
  have hr := chiral_rank B hQ
  exact ⟨hr.1, hr.2, h2, hfix, chiral_eigenspaces B hQ _ h2
    (hodge_trace _ _ hs hU) (hodge_self_adjoint _ _ hs) hfix⟩
omit [CharZero K] in
private theorem chiral_operator_unique (B : FormTriple K) (hQ : (wedgeGram B).det ≠ 0) {H₁ H₂ : PairMatrix K}
    (h₁ : H₁ * B = B) (h₂ : H₂ * B = B)
    (k₁ : ∀ x, Bᵀ *ᵥ (W K *ᵥ x) = 0 → H₁ *ᵥ x = -x)
    (k₂ : ∀ x, Bᵀ *ᵥ (W K *ᵥ x) = 0 → H₂ *ᵥ x = -x) : H₁ = H₂ := by
  apply Matrix.mulVec_injective
  funext x
  let y := (wedgeGram B)⁻¹ *ᵥ (Bᵀ *ᵥ (W K *ᵥ x))
  let z := x - B *ᵥ y
  have hy : wedgeGram B *ᵥ y = Bᵀ *ᵥ (W K *ᵥ x) := by
    rw [show y = (wedgeGram B)⁻¹ *ᵥ (Bᵀ *ᵥ (W K *ᵥ x)) from rfl,
      mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hQ), one_mulVec]
  have hz : Bᵀ *ᵥ (W K *ᵥ z) = 0 := by
    simp only [z, mulVec_sub, sub_eq_zero, mulVec_mulVec]
    simpa only [wedgeGram, mulVec_mulVec, Matrix.mul_assoc] using hy.symm
  have hx : B *ᵥ y + z = x := add_sub_cancel _ _
  conv_lhs => rw [← hx, mulVec_add, mulVec_mulVec, h₁, k₁ _ hz]
  conv_rhs => rw [← hx, mulVec_add, mulVec_mulVec, h₂, k₂ _ hz]
private theorem hodge_minus_of_orthogonal (B : FormTriple K) (hQ : (wedgeGram B).det ≠ 0)
    (g : Matrix4 K) (v : K) (hs : gᵀ = g) (hg : g.det ≠ 0)
    (hv : v ^ 2 = g.det) (hB : hodge g v * B = B) (x : PairIndex → K)
    (hx : Bᵀ *ᵥ (W K *ᵥ x) = 0) : hodge g v *ᵥ x = -x := by
  have hsq : hodge g v ^ 2 = 1 := by
    rw [hodge_square _ _ hs hg, hv, div_self hg, one_smul]
  exact ((chiral_eigenspaces B hQ _ hsq (hodge_trace _ _ hs hg)
    (hodge_self_adjoint _ _ hs) hB).2 x).2 hx
omit [CharZero K] in
private theorem exterior_proportional_of_hodge_eq (g₁ g₂ : Matrix4 K) (v₁ v₂ : K)
    (hg₁ : g₁.det ≠ 0) (hg₂ : g₂.det ≠ 0) (hn₁ : v₁ ≠ 0)
    (hh : hodge g₁ v₁ = hodge g₂ v₂) :
    exteriorSquare g₂ = (v₂ / v₁) • exteriorSquare g₁ := by
  have h₁ := hodge_mul_exterior g₁ v₁ hg₁
  have hi : IsUnit (hodge g₁ v₁) := by
    apply (isUnit_iff_isUnit_det _).2 (isUnit_det_of_right_inverse
      (B := exteriorSquare g₁ * (v₁⁻¹ • W K)) ?_)
    rw [← Matrix.mul_assoc, h₁, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      inv_mul_cancel₀ hn₁, one_smul, W_sq]
  apply hi.mul_left_cancel
  rw [Matrix.mul_smul, h₁, smul_smul, div_mul_cancel₀ _ hn₁, hh, hodge_mul_exterior g₂ v₂ hg₂]

/-- A nondegenerate chiral plane with a fixed choice of eigenvalue determines the conformal class. -/
theorem urbantke_conformal_uniqueness_of_chiral_plane (g₁ g₂ : Matrix4 K) (v₁ v₂ : K)
    (hs₁ : g₁ᵀ = g₁) (hs₂ : g₂ᵀ = g₂) (hg₁ : g₁.det ≠ 0) (hg₂ : g₂.det ≠ 0)
    (hv₁ : v₁ ^ 2 = g₁.det) (hv₂ : v₂ ^ 2 = g₂.det)
    (B : FormTriple K) (hQ : (wedgeGram B).det ≠ 0)
    (h₁ : hodge g₁ v₁ * B = B) (h₂ : hodge g₂ v₂ * B = B) : ∃ a : K, a ≠ 0 ∧ g₂ = a • g₁ := by
  have hh := chiral_operator_unique B hQ h₁ h₂
    (hodge_minus_of_orthogonal B hQ g₁ v₁ hs₁ hg₁ hv₁ h₁)
    (hodge_minus_of_orthogonal B hQ g₂ v₂ hs₂ hg₂ hv₂ h₂)
  have hn₁ : v₁ ≠ 0 := fun h => hg₁ (by simp [← hv₁, h])
  refine urbantke_conformal_uniqueness g₁ g₂ hg₁ (v₂ / v₁) (div_ne_zero ?_ hn₁)
    (exterior_proportional_of_hodge_eq g₁ g₂ v₁ v₂ hg₁ hg₂ hn₁ hh)
  exact fun h => hg₂ (by simp [← hv₂, h])
end Hodge
private theorem conj_hodge (U : Matrix4 ℂ) (D : ℂ) (hU : U.det ≠ 0)
    (hUbar : ((starRingEnd ℂ).mapMatrix U).det ≠ 0) :
    (hodge U D).map (starRingEnd ℂ) = hodge ((starRingEnd ℂ).mapMatrix U) (star D) := by
  let f := starRingEnd ℂ
  have h := congrArg (fun M : PairMatrix ℂ => M.map f) (hodge_mul_exterior U D hU)
  rw [Matrix.map_mul, ← exterior_map, Matrix.map_smul' _ _ _ (map_mul f), map_W] at h
  change (hodge U D).map f = (f D • W ℂ) * (exteriorSquare (U.map f))⁻¹
  change (U.map f).det ≠ 0 at hUbar
  rw [← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (exterior_det_ne _ hUbar)), Matrix.mul_one]
private theorem real_representative (U : Matrix4 ℂ) (hU : U.det ≠ 0)
    (hs : Uᵀ = U) {a : ℂ} (ha₀ : a ≠ 0) (ha : (starRingEnd ℂ).mapMatrix U = a • U) :
    ∃ (g : Matrix4 ℝ) (l : ℂ), l ≠ 0 ∧ star l = a * l ∧ gᵀ = g ∧
      U = l • Complex.ofRealHom.mapMatrix g := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, U i j ≠ 0 := by
    by_contra! h
    exact hU (by rw [show U = 0 by ext i j; exact h i j, det_zero])
  let l := U i j
  let g := U.map fun z => (z / l).re
  have hentry (r s : Fin 4) : star (U r s) = a * U r s := congrFun (congrFun ha r) s
  refine ⟨g, l, hij, hentry i j, congrArg (fun M => M.map (fun z : ℂ => (z / l).re)) hs, ?_⟩
  ext r s
  have hreal : star (U r s / l) = U r s / l := by
    change (starRingEnd ℂ) (U r s / l) = U r s / l
    rw [map_div₀, show (starRingEnd ℂ) (U r s) = a * U r s from hentry r s,
      show (starRingEnd ℂ) l = a * l from hentry i j]
    field_simp
  change U r s = l * (((U r s / l).re : ℝ) : ℂ)
  rw [Complex.conj_eq_iff_re.mp hreal, ← mul_div_assoc, mul_comm l, mul_div_cancel_right₀ _ hij]

/-- Orthogonality to the conjugate triple gives a real Lorentzian conformal representative. -/
theorem urbantke_lorentz_reality (B : FormTriple ℂ)
    (hQ : (wedgeGram B).det ≠ 0) (h : Bᵀ * W ℂ * B.map star = 0) :
    ∃ (g : Matrix4 ℝ) (l : ℂ), l ≠ 0 ∧ gᵀ = g ∧ g.det < 0 ∧
      urbantke B = l • Complex.ofRealHom.mapMatrix g ∧
      hodge g (Real.sqrt |g.det|) ^ 2 = -(1 : PairMatrix ℝ) := by
  let U := urbantke B
  let D := density B
  obtain ⟨hs, hdet, _⟩ := urbantke_polynomial_identities B
  have hD : D ^ 2 = U.det := by change density B ^ 2 = _; rw [hdet, density, div_pow]; norm_num
  have hD₀ : D ≠ 0 := div_ne_zero hQ (by norm_num)
  obtain ⟨hU, hchiral⟩ := urbantke_nondegenerate_iff_and_chiral_star B
  obtain ⟨_, _, _, hb, _, hminus⟩ := hchiral hQ
  have hU := hU.mpr hQ
  have hm := fun x => (hminus x).mpr
  have hbar : hodge U D * B.map star = -(B.map star) := by
    apply ext_of_mulVec_single
    intro j
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    apply hm
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
  let f := starRingEnd ℂ
  let Ubar := f.mapMatrix U
  have hUbar : Ubar.det ≠ 0 := by
    rw [← f.map_det]
    exact fun hz => hU (f.injective (hz.trans f.map_zero.symm))
  have hsbar : Ubarᵀ = Ubar := congrArg f.mapMatrix hs
  have hDbar : (-star D) ^ 2 = Ubar.det := by rw [neg_sq, ← f.map_det, ← hD]; exact (f.map_pow _ _).symm
  have hneg : hodge Ubar (-star D) = -(hodge Ubar (star D)) := by simp [hodge, neg_smul]
  have hbbar : hodge Ubar (-star D) * B = B := by
    have h' := congrArg (fun M : FormTriple ℂ => M.map f) hbar
    have hinv : (B.map star).map f = B := by ext i j; exact star_star _
    have hminus : (-(B.map star)).map f = -B := by ext i j; simp [f]
    rw [Matrix.map_mul, conj_hodge _ _ hU hUbar, hinv, hminus] at h'
    rw [hneg, Matrix.neg_mul, h', neg_neg]
  have hh := chiral_operator_unique B hQ hb hbbar hm
    (hodge_minus_of_orthogonal B hQ Ubar _ hsbar hUbar hDbar hbbar)
  have hDbar₀ : -star D ≠ 0 := by simpa using hD₀
  have he := exterior_proportional_of_hodge_eq U Ubar D _ hU hUbar hD₀ hh
  obtain ⟨a, ha₀, ha⟩ := urbantke_conformal_uniqueness U Ubar hU _ (div_ne_zero hDbar₀ hD₀) he
  obtain ⟨g, l, hl, hlbar, hg, hG⟩ := real_representative U hU hs ha₀ ha
  rw [ha, exterior_smul] at he
  have hn : exteriorSquare U ≠ 0 := fun h => exterior_det_ne U hU (by simp [h])
  have hp := (eq_div_iff hD₀).mp ((smul_left_inj hn).mp he)
  let c := D / l ^ 2
  have hc : star c = -c := by
    change (starRingEnd ℂ) (D / l ^ 2) = _
    rw [map_div₀, map_pow]
    change star D / (star l) ^ 2 = -(D / l ^ 2)
    rw [hlbar, show star D = -(a ^ 2 * D) by rw [hp, neg_neg]]
    field_simp
  have hr : c.re = 0 := eq_zero_of_neg_eq (congrArg Complex.re hc).symm
  have hi : c.im ≠ 0 := fun h => div_ne_zero hD₀ (pow_ne_zero _ hl) (Complex.ext hr h)
  have hdetc : c ^ 2 = (g.det : ℂ) := by
    dsimp [c]
    rw [div_pow, ← pow_mul]
    apply (div_eq_iff (pow_ne_zero _ hl)).mpr
    rw [hD, hG, det_smul, Fintype.card_fin, ← Complex.ofRealHom.map_det, mul_comm]
    rfl
  have hre := congrArg Complex.re hdetc
  rw [pow_two, Complex.mul_re, hr, mul_zero, zero_sub, Complex.ofReal_re] at hre
  have hdet := hre ▸ neg_neg_of_pos (mul_self_pos.mpr hi)
  refine ⟨g, l, hl, hg, hdet, hG, ?_⟩
  rw [hodge_square g _ hg hdet.ne, Real.sq_sqrt (abs_nonneg _), abs_of_neg hdet,
    neg_div, div_self hdet.ne, neg_one_smul]
private def scalarGraph (z : ℂ) : FormTriple ℂ :=
  graph 1 (z • (1 : Matrix3 ℂ))
private theorem scalarGraph_gram (z : ℂ) :
    wedgeGram (scalarGraph z) = (2 * z) • (1 : Matrix3 ℂ) := by
  rw [scalarGraph, wedgeGram_graph, transpose_smul, transpose_one, ← add_smul, two_mul]
private theorem scalarGraph_urbantke (z : ℂ) :
    urbantke (scalarGraph z) = diagonal ![1, z ^ 2, z ^ 2, z ^ 2] := by
  have hs : symPart (z • (1 : Matrix3 ℂ)) = z • 1 := by
    rw [symPart, transpose_smul, transpose_one, ← add_smul, smul_smul]
    congr 1
    ring
  have hl : shear (z • (1 : Matrix3 ℂ)) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [shear, Matrix.one_apply]
  rw [scalarGraph, urbantke_graph, hs, hl, transpose_one, Matrix.one_mul, Matrix.mul_one,
    adjugate_smul, adjugate_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [blockMetric, Matrix.one_apply, diagonal_apply]

/-- The chiral basis given by the graph of the imaginary unit has Lorentzian reality. -/
theorem urbantke_lorentz_witness :
    let B := scalarGraph Complex.I
    wedgeGram B = (2 * Complex.I) • (1 : Matrix3 ℂ) ∧
      urbantke B = diagonal ![1, -1, -1, -1] ∧
      Bᵀ * W ℂ * B.map star = 0 ∧ density B = -Complex.I := by
  dsimp only
  refine ⟨scalarGraph_gram _, by rw [scalarGraph_urbantke, Complex.I_sq], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [W, scalarGraph, graph, Matrix.mul_apply,
      Fintype.sum_sum_type, Matrix.one_apply, smul_eq_mul]
  · rw [density, scalarGraph_gram, det_smul, det_one, mul_one, Fintype.card_fin,
      mul_pow, Complex.I_pow_three]
    ring

/-- Complex simplicity can hold even though the Urbantke metric has no real conformal representative. -/
theorem simplicity_not_sufficient_for_real_lorentz :
    let B := scalarGraph (1 + Complex.I)
    wedgeGram B = (2 * (1 + Complex.I)) • (1 : Matrix3 ℂ) ∧
      (wedgeGram B).det ≠ 0 ∧ urbantke B = diagonal ![1, 2 * Complex.I, 2 * Complex.I, 2 * Complex.I] ∧
      ¬ ∃ (g : Matrix4 ℝ) (l : ℂ), urbantke B = l • Complex.ofRealHom.mapMatrix g := by
  dsimp only
  have hz : (1 + Complex.I) ^ 2 = 2 * Complex.I := by ring_nf; simp [Complex.I_sq]
  have hU : urbantke (scalarGraph (1 + Complex.I)) =
      diagonal ![1, 2 * Complex.I, 2 * Complex.I, 2 * Complex.I] := by
    rw [scalarGraph_urbantke, hz]
  refine ⟨scalarGraph_gram _, ?_, hU, ?_⟩
  · rw [scalarGraph_gram, det_smul, det_one, mul_one]
    refine pow_ne_zero _ (mul_ne_zero (by norm_num) fun h => ?_)
    simpa using congrArg Complex.re h
  · rintro ⟨g, l, h⟩
    rw [hU] at h
    have h₀ : 1 = l * (g 0 0 : ℂ) := by simpa using congrFun (congrFun h 0) 0
    have h₁ : 2 * Complex.I = l * (g 1 1 : ℂ) := by simpa using congrFun (congrFun h 1) 1
    have hg : g 0 0 ≠ 0 := fun he => by simp [he] at h₀
    have hl : l.im = 0 := by simpa [Complex.mul_im, hg] using congrArg Complex.im h₀
    have hi₁ := congrArg Complex.im h₁
    norm_num [Complex.mul_im, hl] at hi₁
end D5.S3.Geometry.Lorentz.Urbantke
