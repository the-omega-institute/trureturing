/- GID: D5/S3/Geometry/Lorentz/PlebanskiCoframe
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Oriented coframe action, electric charts, and real coframe lifts. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.Lorentz.Urbantke
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Basic.Sign.Basic

/-!
Omega original.

Matrix identities for the oriented coframe action, electric charts, and the
real coframe lift of complex orthogonal changes of chiral frame.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.Geometry.PlebanskiCoframe

open Matrix D5.S3.Geometry.Lorentz.Urbantke
open scoped Matrix
universe u

open private pairLeft pairRight exterior_one exterior_transpose exterior_mul
  exterior_wedge exterior_smul graph_shear symPart urbantke_mul from
  D5.S3.Geometry.Lorentz.Urbantke
open private shear from D5.S3.Geometry.Lorentz.Urbantke

abbrev FormTriple (K : Type u) := Matrix PairIndex (Fin 3) K
abbrev M3 (K : Type u) := Matrix (Fin 3) (Fin 3) K
abbrev M4 (K : Type u) := Matrix (Fin 4) (Fin 4) K
def graph {K : Type u} (E H : M3 K) : FormTriple K
  | .inl i => E i
  | .inr i => H i

def model {K : Type u} [Ring K] (z : K) : FormTriple K :=
  graph 1 (z • (1 : M3 K))

def action {K : Type u} [CommRing K] (A : M4 K) (B : FormTriple K) : FormTriple K :=
  exteriorSquare A * B

section Algebra

variable {K : Type u} [Field K] [CharZero K]

private def minor (A : M4 K) (p q : PairIndex) : K :=
  A (pairLeft p) (pairLeft q) * A (pairRight p) (pairRight q) -
    A (pairLeft p) (pairRight q) * A (pairRight p) (pairLeft q)
omit [CharZero K] in private theorem exterior_apply (A : M4 K) (p q : PairIndex) :
    exteriorSquare A p q = minor A p q := rfl

omit [CharZero K] in theorem exterior_wedge_congruence (A : M4 K) :
    (exteriorSquare A)ᵀ * W K * exteriorSquare A = A.det • W K := by
  simpa only [exterior_transpose, det_transpose, transpose_transpose] using
    exterior_wedge Aᵀ

omit [CharZero K] in theorem action_mul (A C : M4 K) (B : FormTriple K) :
    action (A * C) B = action A (action C B) := by
  simp [action, exterior_mul, Matrix.mul_assoc]
omit [CharZero K] in theorem action_one (B : FormTriple K) : action 1 B = B := by
  simp [action, exterior_one]
omit [CharZero K] in theorem wedgeGram_graph (E H : M3 K) :
    wedgeGram (graph E H) = Eᵀ * H + Hᵀ * E := by
  ext i j
  simp [wedgeGram, W, graph, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, add_comm]
omit [CharZero K] in theorem wedgeGram_model (z : K) :
    wedgeGram (model z) = (2 * z) • (1 : M3 K) := by
  rw [model, wedgeGram_graph, transpose_one, Matrix.one_mul, transpose_smul, transpose_one,
    Matrix.smul_mul, Matrix.one_mul, ← add_smul, two_mul]
private def skew (x : PairIndex → K) : M4 K :=
  !![0, x (.inl 0), x (.inl 1), x (.inl 2);
    -x (.inl 0), 0, x (.inr 2), -x (.inr 1);
    -x (.inl 1), -x (.inr 2), 0, x (.inr 0);
    -x (.inl 2), x (.inr 1), -x (.inr 0), 0]
omit [CharZero K] in private theorem skew_action (A : M4 K) (x : PairIndex → K) :
    skew (exteriorSquare A *ᵥ x) = A * skew x * Aᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [skew, Matrix.mul_apply, mulVec, dotProduct, exterior_apply, minor,
      pairLeft, pairRight, Fintype.sum_sum_type, Fin.sum_univ_succ] <;> ring
private def cubicTerm (B : FormTriple K) (i j k : Fin 3) : M4 K :=
  skew (B.col i) * skew (W K *ᵥ B.col k) * (skew (B.col j))ᵀ
def cyclicCubic (B : FormTriple K) : M4 K :=
  (1 / 6 : K) • (cubicTerm B 0 1 2 + cubicTerm B 1 2 0 + cubicTerm B 2 0 1 -
    (cubicTerm B 1 0 2 + cubicTerm B 2 1 0 + cubicTerm B 0 2 1))
private def compPair : PairIndex → PairIndex := Sum.elim Sum.inr Sum.inl
private def rows (a b c : Fin 3 → K) : M3 K := of ![a, b, c]
private def pairCubic (B : FormTriple K) : M4 K :=
  (1 / 6 : K) • fun a b => ∑ p : PairIndex, (
    (rows (fun i => skew (B.col i) a (pairLeft p)) (fun i => skew (B.col i) b (pairRight p))
      (B (compPair p))).det -
    (rows (fun i => skew (B.col i) a (pairRight p)) (fun i => skew (B.col i) b (pairLeft p))
      (B (compPair p))).det)
omit [CharZero K] in private theorem urbantke_pair (B : FormTriple K) : urbantke B = pairCubic B := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl
private def pairTerm (B : FormTriple K) (i j k : Fin 3) (a b : Fin 4) (p : PairIndex) : K :=
  (skew (B.col i) a (pairLeft p) * skew (B.col j) b (pairRight p) -
    skew (B.col i) a (pairRight p) * skew (B.col j) b (pairLeft p)) * B (compPair p) k
set_option maxHeartbeats 800000 in
omit [CharZero K] in private theorem cubicTerm_apply (B : FormTriple K) (i j k : Fin 3) (a b : Fin 4) :
    cubicTerm B i j k a b = ∑ p, pairTerm B i j k a b p := by
  simp only [cubicTerm, Matrix.mul_apply, transpose_apply]
  fin_cases a <;> fin_cases b <;>
    simp [pairTerm, skew, pairLeft, pairRight, compPair, Matrix.col, mulVec, dotProduct,
      W, Matrix.one_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.succ] <;> ring
omit [CharZero K] in theorem urbantke_cyclic (B : FormTriple K) : urbantke B = cyclicCubic B := by
  rw [urbantke_pair, pairCubic, cyclicCubic]
  congr 1
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, cubicTerm_apply,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  simp [pairTerm, rows, Matrix.det_fin_three]
  ring
omit [CharZero K] in private theorem skew_smul (t : K) (x : PairIndex → K) :
    skew (t • x) = t • skew x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [skew]
omit [CharZero K] in theorem cubicTerm_action (A : M4 K) (B : FormTriple K) (i j k : Fin 3) :
    cubicTerm (action A B) i j k = A.det • (A * cubicTerm B i j k * Aᵀ) := by
  have hmid : Aᵀ * skew (W K *ᵥ (exteriorSquare A *ᵥ B.col k)) * A =
      A.det • skew (W K *ᵥ B.col k) := by
    have hs := (skew_action Aᵀ (W K *ᵥ (exteriorSquare A *ᵥ B.col k))).symm
    rw [transpose_transpose, exterior_transpose, mulVec_mulVec, mulVec_mulVec,
      ← Matrix.mul_assoc (exteriorSquare A)ᵀ (W K), exterior_wedge_congruence, smul_mulVec, skew_smul] at hs
    simpa only [mulVec_mulVec] using hs
  simp only [cubicTerm, action, col_mul_eq_mulVec_col, skew_action, transpose_mul,
    transpose_transpose]
  calc
    _ = A * (skew (B.col i) * (Aᵀ *
        skew (W K *ᵥ (exteriorSquare A *ᵥ B.col k)) * A) *
        (skew (B.col j))ᵀ) * Aᵀ := by
      simp [Matrix.mul_assoc]
    _ = _ := by rw [hmid]; simp [Matrix.mul_assoc]

def modelMetric (z : K) : M4 K := diagonal ![1, z ^ 2, z ^ 2, z ^ 2]
set_option maxHeartbeats 500000 in
theorem urbantke_model (z : K) : urbantke (model z) = modelMetric z := by
  rw [urbantke_pair]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [pairCubic, skew, rows, pairLeft, pairRight, compPair, modelMetric, model, graph,
      Matrix.col, Matrix.diagonal_apply, Matrix.det_fin_three, Matrix.one_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Matrix.smul_apply, Fin.succ] <;> ring
def electric (B : FormTriple K) : M3 K := fun i => B (.inl i)
def magnetic (B : FormTriple K) : M3 K := fun i => B (.inr i)
omit [Field K] [CharZero K] in theorem graph_blocks (B : FormTriple K) : graph (electric B) (magnetic B) = B := by
  ext i j
  cases i <;> rfl
theorem urbantke_electric (B : FormTriple K) : urbantke B 0 0 = (electric B).det := by
  rw [urbantke_pair]
  simp [pairCubic, skew, rows, pairLeft, pairRight, compPair, electric, Matrix.col,
    Matrix.det_fin_three, Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.succ]
  ring
def spatial : FormTriple K := graph 0 1

set_option maxHeartbeats 400000 in
omit [CharZero K] in
theorem urbantke_spatial : urbantke (spatial : FormTriple K) = 0 := by
  rw [urbantke_pair]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairCubic, skew, rows, pairLeft, pairRight, compPair, Matrix.col,
      spatial, graph, Matrix.det_fin_three, Matrix.one_apply, Matrix.smul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.succ]

def block (a : K) (E : M3 K) : M4 K :=
  !![a, 0, 0, 0; 0, E 0 0, E 0 1, E 0 2;
    0, E 1 0, E 1 1, E 1 2; 0, E 2 0, E 2 1, E 2 2]
def coordinateShear (x y z : K) : M4 K :=
  !![1, 0, 0, 0; x, 1, 0, 0; y, 0, 1, 0; z, 0, 0, 1]
omit [CharZero K] in theorem det_block (a : K) (E : M3 K) : (block a E).det = a * E.det := by
  rw [det_succ_row_zero]
  simp [block, Fin.sum_univ_succ, det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
omit [CharZero K] in theorem det_coordinateShear (x y z : K) : (coordinateShear x y z).det = 1 := by
  rw [det_succ_row_zero]
  simp [coordinateShear, Fin.sum_univ_succ, det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
omit [CharZero K] in private theorem exterior_block (a : K) (E : M3 K) :
    exteriorSquare (block a E) = fromBlocks (a • E) 0 0 E.adjugateᵀ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [exterior_apply, minor, pairLeft, pairRight, block, Fin.succ,
      Matrix.adjugate_apply, det_fin_three, Matrix.updateRow_apply] <;> ring
omit [CharZero K] in theorem act_block_graph (a : K) (E P Q : M3 K) :
    action (block a E) (graph P Q) = graph (a • E * P) (E.adjugateᵀ * Q) := by
  rw [action, exterior_block]
  ext i j
  cases i <;> simp [graph, Matrix.mul_apply, Fintype.sum_sum_type]
theorem act_shear (z : K) (H : M3 K) (hH : H + Hᵀ = (2 * z) • (1 : M3 K)) :
    action (shear H)ᵀ (model z) = graph 1 H := by
  have h := graph_shear H
  change action (shear H)ᵀ (graph 1 (symPart H)) =
    graph 1 H at h
  have hs : symPart H = z • (1 : M3 K) := by
    change (1 / 2 : K) • (H + Hᵀ) = _
    rw [hH, smul_smul]
    congr 1
    ring
  rw [hs] at h
  exact h
def topShear (x y z : K) : M4 K := (coordinateShear x y z)ᵀ

def dilate (z : K) : M4 K := block 1 (z • (1 : M3 K))
omit [CharZero K] in theorem dilate_model (z t : K) :
    action (dilate z) (model t) = z • model (z * t) := by
  rw [dilate, model, act_block_graph, adjugate_smul, adjugate_one]
  ext i j
  cases i <;> simp [graph, model, smul_smul]
  ring
def quaternionRight (q : Fin 4 → K) : M4 K :=
  !![q 0, -q 1, -q 2, -q 3; q 1, q 0, q 3, -q 2;
     q 2, -q 3, q 0, q 1; q 3, q 2, -q 1, q 0]
omit [CharZero K] in theorem quaternion_model (q : Fin 4 → K) :
    action (quaternionRight q) (model 1) = (∑ i, q i ^ 2) • model 1 := by
  ext p j
  rcases p with p | p <;> fin_cases p <;> fin_cases j <;>
    norm_num [action, quaternionRight, model, graph, exterior_apply, minor, pairLeft, pairRight,
      Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.succ, Matrix.one_apply] <;> ring
omit [CharZero K] in theorem action_smul (A : M4 K) (t : K) (B : FormTriple K) :
    action A (t • B) = t • action A B := by simp [action]

omit [CharZero K] in
theorem action_scale (t : K) (A : M4 K) (B : FormTriple K) :
    action (t • A) B = t ^ 2 • action A B := by
  simp [action, exterior_smul]

end Algebra

theorem reflected_model (z : ℝ) :
    action (block (-1) (1 : M3 ℝ)) (model (-z)) = -model z := by
  rw [model, act_block_graph, adjugate_one, transpose_one, Matrix.mul_one, one_mul]
  ext i j
  cases i <;> simp [graph, model]

open SignType

def lorentzMetric {K : Type*} [Ring K] : M4 K :=
  diagonal fun i => if i = (0 : Fin 4) then 1 else -1

theorem lorentzMetric_model : Complex.ofRealHom.mapMatrix lorentzMetric = modelMetric Complex.I := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [RingHom.mapMatrix_apply, lorentzMetric, modelMetric, Complex.I_sq]

private theorem lorentz_signs :
    ∀ q : Fin 4 → SignType, q 0 * q 1 * q 2 * q 3 = -1 →
      ∃ (p : Fin 4) (s : Bool), ∀ i, q (Equiv.swap 0 p i) =
        if i = 0 then (if s then 1 else -1) else (if s then -1 else 1) := by decide

theorem signed_lorentz_factor (g : M4 ℝ) (hs : gᵀ = g) (hd : g.det < 0) :
    ∃ (A : M4 ℝ) (s : Bool), 0 < A.det ∧
      g = (if s then (1 : ℝ) else -1) • (A * lorentzMetric * Aᵀ) := by
  have hh : g.IsHermitian := by simpa [Matrix.IsHermitian, Matrix.star_eq_conjTranspose] using hs
  let ev := hh.eigenvalues
  let O : M4 ℝ := hh.eigenvectorUnitary
  have hg : g = O * diagonal ev * Oᵀ := by
    simpa [O, ev, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using hh.spectral_theorem
  have hp : sign (ev 0) * sign (ev 1) * sign (ev 2) * sign (ev 3) = -1 := by
    have h := sign_neg hd
    rwa [hh.det_eq_prod_eigenvalues, Fin.prod_univ_four, sign_mul, sign_mul, sign_mul] at h
  obtain ⟨p, s, hsign⟩ := lorentz_signs (fun i => sign (ev i)) hp
  let e : Equiv.Perm (Fin 4) := Equiv.swap 0 p
  let d : Fin 4 → ℝ := fun i => Real.sqrt |ev (e i)|
  let F : M4 ℝ := O.submatrix id e * diagonal d
  have hdiag : (if s then (1 : ℝ) else -1) • (diagonal d * lorentzMetric * diagonal d) =
      (diagonal ev).submatrix e e := by
    rw [submatrix_diagonal_equiv, lorentzMetric, diagonal_mul_diagonal, diagonal_mul_diagonal,
      ← diagonal_smul]
    congr 1
    funext i
    have h := sign_mul_abs (ev (e i))
    rw [show sign (ev (e i)) = _ from hsign i,
      ← (show d i ^ 2 = _ from Real.sq_sqrt (abs_nonneg (ev (e i))))] at h
    change (if s then (1 : ℝ) else -1) * (d i * (if i = 0 then 1 else -1) * d i) = _
    by_cases hi : i = 0 <;> cases s <;> norm_num [hi] at h ⊢ <;> nlinarith only [h]
  have hF : (if s then (1 : ℝ) else -1) • (F * lorentzMetric * Fᵀ) = g := by
    have h := congrArg (fun M : M4 ℝ => O.submatrix id e * M * Oᵀ.submatrix e id) hdiag
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id, ← hg] at h
    simpa only [F, transpose_mul, diagonal_transpose, transpose_submatrix, Matrix.mul_assoc,
      Matrix.mul_smul, Matrix.smul_mul] using h
  have hn : F.det ≠ 0 := by
    intro h
    have h' := congrArg Matrix.det hF
    simp only [det_smul, det_mul, h, zero_mul, mul_zero] at h'
    exact hd.ne h'.symm
  by_cases hpos : 0 < F.det
  · exact ⟨F, s, hpos, hF.symm⟩
  · let J : M4 ℝ := lorentzMetric
    have hJ : J.det = -1 := by norm_num [J, lorentzMetric, det_diagonal, Fin.prod_univ_four]
    have hJJ : J * J = 1 := by
      rw [show J = diagonal (fun i : Fin 4 => if i = 0 then (1 : ℝ) else -1) from rfl,
        diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases hi : i = 0 <;> simp [hi]
    have hT : Jᵀ = J := diagonal_transpose _
    refine ⟨F * J, s, ?_, ?_⟩
    · rw [det_mul, hJ, mul_neg_one]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hn)
    · change g = (if s then (1 : ℝ) else -1) • (F * J * J * (F * J)ᵀ)
      rw [transpose_mul, Matrix.mul_assoc F J J, hJJ, Matrix.mul_one, hT]
      simpa only [Matrix.mul_assoc] using hF.symm

theorem internal_frame {K : Type u} [Field K] [CharZero K]
    (B C : FormTriple K) (c : K) (hc : c ≠ 0)
    (hQ : wedgeGram B = c • (1 : M3 K))
    (hQ' : wedgeGram C = c • (1 : M3 K)) (hU : urbantke B = urbantke C) :
    ∃ R : M3 K, Rᵀ * R = 1 ∧ R.det = 1 ∧ B = C * R := by
  have hB : (wedgeGram B).det ≠ 0 := by simp [hQ, hc]
  have hC : (wedgeGram C).det ≠ 0 := by simp [hQ', hc]
  have hb := ((urbantke_nondegenerate_iff_and_chiral_star B).2 hB).2.2.2.1
  have hr := ((urbantke_nondegenerate_iff_and_chiral_star C).2 hC).2.2.2.2.1
  have hd : density B = density C := by simp [density, hQ, hQ']
  rw [hU, hd] at hb
  have hcol (j : Fin 3) : ∃ y, C *ᵥ y = B.col j := by
    apply (hr (B.col j)).1
    rw [← col_mul_eq_mulVec_col, hb]
  choose f hf using hcol
  let R : M3 K := (Matrix.of f)ᵀ
  have he : B = C * R := by
    ext i j
    exact (congrFun (hf j) i).symm
  have horth : Rᵀ * R = (1 : M3 K) := by
    apply smul_right_injective _ hc
    calc
      c • (Rᵀ * R) = Rᵀ * wedgeGram C * R := by rw [hQ']; simp
      _ = wedgeGram (C * R) := by simp [wedgeGram, Matrix.mul_assoc, transpose_mul]
      _ = _ := by rw [← he, hQ]
  have hus : urbantke C ≠ 0 := fun h =>
    (urbantke_nondegenerate_iff_and_chiral_star C).1.mpr hC (by simp [h])
  refine ⟨R, horth, smul_left_injective K hus ?_, he⟩
  change R.det • urbantke C = (1 : K) • urbantke C
  rw [one_smul, ← urbantke_mul, ← he, hU]

private def quaternionLeft (q : Fin 4 → ℂ) : M4 ℂ :=
  !![q 0, -q 1, -q 2, -q 3; q 1, q 0, -q 3, q 2;
     q 2, q 3, q 0, -q 1; q 3, -q 2, q 1, q 0]

private def quaternionRotation (a b c d : ℂ) : M3 ℂ :=
  !![a^2+b^2-c^2-d^2, 2*(b*c-a*d), 2*(b*d+a*c);
     2*(b*c+a*d), a^2-b^2+c^2-d^2, 2*(c*d-a*b);
     2*(b*d-a*c), 2*(c*d+a*b), a^2-b^2-c^2+d^2]

private theorem quaternion_left_act (q : Fin 4 → ℂ) :
    action (quaternionLeft q) (model 1) =
      model (1 : ℂ) * quaternionRotation (q 0) (q 1) (q 2) (q 3) := by
  let R := quaternionRotation (q 0) (q 1) (q 2) (q 3)
  have h : model (1 : ℂ) * R = graph R R := by
    ext p j
    cases p <;> simp [model, graph, Matrix.mul_apply, Matrix.one_apply]
  change action (quaternionLeft q) (model 1) = model (1 : ℂ) * R
  rw [h]
  dsimp only [R]
  ext p j
  rcases p with p | p <;> fin_cases p <;> fin_cases j <;>
    norm_num [action, quaternionLeft, quaternionRotation, model, graph, exterior_apply, minor,
      pairLeft, pairRight, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_succ, Fin.succ,
      Matrix.one_apply] <;> ring

local macro "quaternion_ring" : tactic => `(tactic|
  (norm_num [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply, Matrix.adjugate_apply,
    Matrix.det_fin_three, Matrix.updateRow_apply] <;> ring))

private theorem rotationChart (R : M3 ℂ) (ho : Rᵀ * R = 1) (hd : R.det = 1) :
    let a := 1 + R 0 0 + R 1 1 + R 2 2
    let b := R 2 1 - R 1 2
    let c := R 0 2 - R 2 0
    let d := R 1 0 - R 0 1
    a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 4 * a ∧
      quaternionRotation a b c d = (4 * a) • R := by
  have ht := mul_eq_one_comm.mp ho
  have ha : R.adjugate = Rᵀ :=
    Matrix.right_inv_eq_left_inv (by rw [Matrix.mul_adjugate, hd, one_smul]) ho
  have entry (M N : M3 ℂ) (h : M = N) (i j : Fin 3) : M i j = N i j := congrFun (congrFun h i) j
  have hc := entry _ _ ho
  have hr := entry _ _ ht
  have hm := entry _ _ ha
  dsimp only
  constructor
  · linear_combination (norm := quaternion_ring) (hc 0 0) + (hc 1 1) + (hc 2 2) + 2 * ((hm 0 0) + (hm 1 1) + (hm 2 2))
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [quaternionRotation]
    · linear_combination (norm := quaternion_ring) -(hc 0 0) - 2*(hr 0 0) + (hc 1 1) + (hc 2 2) + 2*((hm 0 0)-(hm 1 1)-(hm 2 2))
    · linear_combination (norm := quaternion_ring) 2*(-(hc 0 1)-(hr 0 1)+(hm 0 1)+(hm 1 0))
    · linear_combination (norm := quaternion_ring) 2*(-(hc 0 2)-(hr 0 2)+(hm 0 2)+(hm 2 0))
    · linear_combination (norm := quaternion_ring) 2*(-(hc 0 1)-(hr 0 1)+(hm 0 1)+(hm 1 0))
    · linear_combination (norm := quaternion_ring) (hc 0 0) - (hc 1 1) - 2*(hr 1 1) + (hc 2 2) + 2*(-(hm 0 0)+(hm 1 1)-(hm 2 2))
    · linear_combination (norm := quaternion_ring) 2*(-(hc 1 2)-(hr 1 2)+(hm 1 2)+(hm 2 1))
    · linear_combination (norm := quaternion_ring) 2*(-(hc 0 2)-(hr 0 2)+(hm 0 2)+(hm 2 0))
    · linear_combination (norm := quaternion_ring) 2*(-(hc 1 2)-(hr 1 2)+(hm 1 2)+(hm 2 1))
    · linear_combination (norm := quaternion_ring) -(hc 0 0) + 2*(hr 0 0) - (hc 1 1) + 2*(hr 1 1) - 3*(hc 2 2) + 2*(-(hm 0 0)-(hm 1 1)+(hm 2 2))

private def reflectedConj (q : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ![star (q 0), -star (q 1), -star (q 2), -star (q 3)]

private def lorentzQuaternion (z : ℂ) (q : Fin 4 → ℂ) : M4 ℂ :=
  dilate z * (quaternionLeft q * quaternionRight (reflectedConj q)) * dilate (-z)

set_option maxHeartbeats 600000 in
private theorem lorentzQuaternion_real (z : ℂ) (hz : z = Complex.I ∨ z = -Complex.I)
    (q : Fin 4 → ℂ) :
    Complex.ofRealHom.mapMatrix ((lorentzQuaternion z q).map Complex.re) = lorentzQuaternion z q := by
  ext i j
  change (((lorentzQuaternion z q i j).re : ℝ) : ℂ) = lorentzQuaternion z q i j
  apply Complex.ext
  · rfl
  · rcases hz with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
      simp [lorentzQuaternion, dilate, block, quaternionLeft, quaternionRight, reflectedConj,
        Matrix.mul_apply, Fin.sum_univ_succ, Complex.mul_re, Complex.mul_im,
        Complex.add_im] <;> ring

theorem action_right_complex (A : M4 ℂ) (B : FormTriple ℂ) (R : M3 ℂ) :
    action A (B * R) = action A B * R := (Matrix.mul_assoc _ _ _).symm

set_option maxHeartbeats 500000 in
private theorem chart_lorentz_lift (z : ℂ) (hz : z = Complex.I ∨ z = -Complex.I)
    (R : M3 ℂ) (ho : Rᵀ * R = 1) (hd : R.det = 1) (ht : 1 + R 0 0 + R 1 1 + R 2 2 ≠ 0) :
    ∃ A : M4 ℝ, action (Complex.ofRealHom.mapMatrix A) (model z) = model z * R := by
  have hz₂ : z ^ 2 = -1 := by rcases hz with rfl | rfl <;> simp [Complex.I_sq]
  let a := 1 + R 0 0 + R 1 1 + R 2 2
  let q : Fin 4 → ℂ := ![a, R 2 1 - R 1 2, R 0 2 - R 2 0, R 1 0 - R 0 1]
  let n : ℂ := 4 * a
  have ⟨hnorm, hnR⟩ := rotationChart R ho hd
  change quaternionRotation (q 0) (q 1) (q 2) (q 3) = n • R at hnR
  have hstar : (∑ j, reflectedConj q j ^ 2) = star n := by
    rw [← (show (∑ j, q j ^ 2) = n by
      simpa [q, n, a, Fin.sum_univ_succ, add_assoc] using hnorm), star_sum]
    simp [reflectedConj, Fin.sum_univ_succ, star_pow]
  let c := Real.sqrt (Complex.normSq n)⁻¹
  let A : M4 ℝ := c • (lorentzQuaternion z q).map Complex.re
  have hA : Complex.ofRealHom.mapMatrix A = (c : ℂ) • lorentzQuaternion z q := by
    change ((c • (lorentzQuaternion z q).map Complex.re).map Complex.ofReal) = _
    rw [Matrix.map_smul' _ _ _ Complex.ofReal_mul]
    exact congrArg ((c : ℂ) • ·) (lorentzQuaternion_real z hz q)
  have hp : action (lorentzQuaternion z q) (model z) = (n * star n) • (model z * R) := by
    simp only [lorentzQuaternion, action_mul, dilate_model,
      show -z * z = 1 by rw [neg_mul, ← pow_two, hz₂, neg_neg], action_smul,
      quaternion_model, hstar, quaternion_left_act, hnR, Matrix.mul_smul,
      action_right_complex, mul_one, Matrix.smul_mul, smul_smul]
    congr 1
    linear_combination -(star n * n) * hz₂
  have hc : (c : ℂ)^2 * (n * star n) = 1 := by
    rw [show n * star n = _ from Complex.mul_conj n, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Real.sq_sqrt (inv_nonneg.mpr (Complex.normSq_nonneg _)),
      inv_mul_cancel₀ (ne_of_gt (Complex.normSq_pos.mpr (mul_ne_zero (by norm_num) ht))), Complex.ofReal_one]
  refine ⟨A, ?_⟩
  rw [hA]
  change exteriorSquare ((c : ℂ) • lorentzQuaternion z q) * model z = _
  rw [exterior_smul, Matrix.smul_mul]
  change (c : ℂ)^2 • action (lorentzQuaternion z q) (model z) = _
  rw [hp, smul_smul, hc, one_smul]

private def spatialFlip (i : Fin 3) : Fin 3 → ℝ := fun j => if j = i then 1 else -1

theorem exists_real_coframe_rotation (z : ℂ) (hz : z = Complex.I ∨ z = -Complex.I)
    (R : M3 ℂ) (ho : Rᵀ * R = 1) (hd : R.det = 1) :
    ∃ A : M4 ℝ, action (Complex.ofRealHom.mapMatrix A) (model z) = model z * R := by

  let t (P : M3 ℂ) := 1 + P 0 0 + P 1 1 + P 2 2
  let S (i : Fin 3) : M3 ℂ := diagonal fun j => (spatialFlip i j : ℂ)
  by_cases h : t R = 0
  · have hs : ∃ i, t (R * S i) ≠ 0 := by
      by_contra! H
      have h0 := H 0
      have h1 := H 1
      have h2 := H 2
      simp [t, S, spatialFlip, Matrix.mul_diagonal] at h0 h1 h2 h
      have hx : (4 : ℂ) = 0 := by linear_combination h0 + h1 + h2 + h
      norm_num at hx
    obtain ⟨i, hi⟩ := hs
    have hs₁ : (S i)ᵀ = S i := diagonal_transpose _
    have hs₂ : S i * S i = 1 := by
      change diagonal (fun j => (spatialFlip i j : ℂ)) * diagonal (fun j => (spatialFlip i j : ℂ)) = _
      rw [diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext j
      by_cases hji : j = i <;> simp [spatialFlip, hji]
    have hs₃ : (S i).det = 1 := by
      fin_cases i <;> norm_num [S, spatialFlip, det_diagonal, Fin.prod_univ_succ]
    obtain ⟨A, hact⟩ := chart_lorentz_lift z hz (R * S i)
      (by rw [transpose_mul, ← Matrix.mul_assoc _ _ (S i), Matrix.mul_assoc (S i)ᵀ, ho, mul_one, hs₁, hs₂])
      (by rw [det_mul, hd, hs₃, mul_one]) hi
    let C := block 1 (diagonal (spatialFlip i))
    have hC : Complex.ofRealHom.mapMatrix C = block 1 (S i) := by ext j k; fin_cases j <;> fin_cases k <;> rfl
    have hCA : action (block 1 (S i)) (model z) = model z * S i := by
      have ha : (S i).adjugate = S i :=
        Matrix.right_inv_eq_left_inv (by rw [Matrix.mul_adjugate, hs₃, one_smul]) hs₂
      rw [model, act_block_graph, ha, hs₁]
      ext p j
      cases p <;> simp [graph, Matrix.mul_apply, Matrix.one_apply]
      exact mul_comm _ _
    refine ⟨A * C, ?_⟩
    rw [map_mul, action_mul, hC, hCA, action_right_complex, hact, Matrix.mul_assoc,
        Matrix.mul_assoc R (S i) (S i), hs₂, mul_one]
  · exact chart_lorentz_lift z hz R ho hd h

end Omega.Geometry.PlebanskiCoframe
