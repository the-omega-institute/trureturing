/- GID: D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation
   generality: I
   mirror-B: D5/B/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.claim; result=D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.result; claim=D5/S0/FiniteGeometry/Polytopes/JohnsonPaparellaHadamardPolyhedraRefutation.claim
   digest: Hadamard closure does not imply exact spectracone representation. -/

/-
result:
  proof_shape: bind-only
  escape_witness: none
  admission_basis: open-problem-resolution (#22419; Refuted)
  Direct frozen dependencies: none.
Private helpers (all proof_shape: bind-only; escape_witness: none;
Direct frozen dependencies: none):
  factors_pos: consumer(s) cone_decomposition.
  normal_center: consumer(s) normal_first, active_entry.
  vertex_mem: consumer(s) products_mem, midpoint_mem, no_nine_forms, spectral_real_forms.
  normal_first: consumer(s) small_mem.
  normal_bounds: consumer(s) small_mem.
  vertex_first: consumer(s) products_mem.
  vertex_bounds: consumer(s) products_mem.
  small_mem: consumer(s) products_mem.
  products_mem: consumer(s) generator_mul.
  reconstruction: consumer(s) cone_decomposition.
  cone_decomposition: consumer(s) generator_mul, realCone_mul.
  cone_add3: consumer(s) generator_mul, realCone_mul, midpoint_mem.
  generator_mul: consumer(s) realCone_mul.
  realCone_mul: consumer(s) complexCone_mul.
  perturb_finite: consumer(s) active_entry.
  midpoint_mem: consumer(s) active_entry.
  edge_vanishes: consumer(s) active_entry.
  active_entry: consumer(s) no_nine_forms.
  midpoint_zero_endpoints: consumer(s) no_nine_forms.
  distinct_edges_independent: consumer(s) no_nine_forms.
  no_nine_forms: consumer(s) complexCone_not_spectral.
  halfspace_real: consumer(s) complexCone_polyhedral.
  sourceNormal_ne: consumer(s) complexCone_polyhedral.
  complexCone_polyhedral: consumer(s) result.
  complexCone_mul: consumer(s) result.
  entry_formula: consumer(s) entry_re, entry_im.
  entry_re: consumer(s) spectral_real_forms.
  entry_im: consumer(s) spectral_real_forms.
  spectral_real_forms: consumer(s) complexCone_not_spectral.
  complexCone_not_spectral: consumer(s) result.
The proofs use Mathlib dotProduct, vector operations, Fin.castSucc and finite minimum owners.
The source definitions retain their finite real-half-space and complex-order meanings.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/


import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


/-!
# A Hadamard-closed cone without a spectracone representation

An explicit three-coordinate cone refutes the cone converse in
Johnson–Paparella Question 9.1.
-/

namespace D5.S0.FiniteGeometry.Polytopes.JohnsonPaparellaHadamardPolyhedraRefutation

open scoped BigOperators ComplexOrder

/-- Section 2.3: H(a,b) = {x : Re <x,a> >= b}. -/
def halfSpace {n : ℕ} (a : Fin n → ℂ) (b : ℝ) : Set (Fin n → ℂ) :=
  {x | b ≤ (∑ i : Fin n, star (a i) * x i).re}

/-- Section 2.3: a finite intersection of H(a_k,b_k), with nonzero normals. -/
def IsSourcePolyhedron {n : ℕ} (K : Set (Fin n → ℂ)) : Prop :=
  ∃ (m : ℕ) (_ : 0 < m) (a : Fin m → Fin n → ℂ) (b : Fin m → ℝ),
    (∀ k : Fin m, a k ≠ 0) ∧
      K = {x | ∀ k : Fin m, x ∈ halfSpace (a k) (b k)}

/-- Section 2.3: a bounded polyhedron. -/
def IsSourcePolytope {n : ℕ} (K : Set (Fin n → ℂ)) : Prop :=
  IsSourcePolyhedron K ∧ Bornology.IsBounded K

/-- Section 2.3: a finite intersection of homogeneous half-spaces H(a_k). -/
def IsSourcePolyhedralCone {n : ℕ} (K : Set (Fin n → ℂ)) : Prop :=
  ∃ (m : ℕ) (_ : 0 < m) (a : Fin m → Fin n → ℂ),
    (∀ k : Fin m, a k ≠ 0) ∧
      K = {x | ∀ k : Fin m, x ∈ halfSpace (a k) 0}

/-- Definition 4.1(i). ComplexOrder means real and entrywise nonnegative. -/
noncomputable def spectracone {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | ∀ (i : Fin n) (j : Fin n),
    (0 : ℂ) ≤ (S * Matrix.diagonal x * S⁻¹) i j}

/-- Definition 4.1(ii). The vector 1 is the source's all-ones vector e. -/
noncomputable def spectratope {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℂ) : Set (Fin n → ℂ) :=
  {x | x ∈ spectracone S ∧
    (S * Matrix.diagonal x * S⁻¹).mulVec (1 : Fin n → ℂ) = 1}

/-- The two affirmative converses asked in Question 9.1, in the same coordinate
size n. Multiplication of vectors is coordinatewise. No identity, spectral
admissibility, pointedness, or full-dimension assumption is added. -/
def claim : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (K : Set (Fin n → ℂ)),
    ((IsSourcePolyhedralCone K →
      (∀ (x : Fin n → ℂ) (y : Fin n → ℂ), x ∈ K → y ∈ K → x * y ∈ K) →
      ∃ (S : Matrix (Fin n) (Fin n) ℂ), S.det ≠ 0 ∧ K = spectracone S) ∧
     (IsSourcePolytope K →
      (∀ (x : Fin n → ℂ) (y : Fin n → ℂ), x ∈ K → y ∈ K → x * y ∈ K) →
      ∃ (S : Matrix (Fin n) (Fin n) ℂ), S.det ≠ 0 ∧ K = spectratope S))

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000



private noncomputable def vertex : Fin 15 → (Fin 3 → ℝ) := ![
  ![1, (-1 / 4), 0],
  ![1, (-99 / 404), (-5 / 101)],
  ![1, (-3 / 13), (-5 / 52)],
  ![1, (-91 / 436), (-15 / 109)],
  ![1, (-21 / 116), (-5 / 29)],
  ![1, (-3 / 20), (-1 / 5)],
  ![1, (-2 / 17), (-15 / 68)],
  ![1, (-51 / 596), (-35 / 149)],
  ![1, (-9 / 164), (-10 / 41)],
  ![1, (-19 / 724), (-45 / 181)],
  ![1, 0, (-1 / 4)],
  ![1, (1 / 4), 0],
  ![1, 1, 1],
  ![1, 0, (1 / 4)],
  ![1, 0, 0]]

private noncomputable def normal : Fin 14 → (Fin 3 → ℝ) := ![
  ![1, 4, (2 / 5)],
  ![1, (196 / 51), (20 / 17)],
  ![1, (188 / 53), (100 / 53)],
  ![1, (22 / 7), (5 / 2)],
  ![1, (8 / 3), 3],
  ![1, (28 / 13), (44 / 13)],
  ![1, (116 / 71), (260 / 71)],
  ![1, (44 / 39), (50 / 13)],
  ![1, (28 / 43), (170 / 43)],
  ![1, (4 / 19), 4],
  ![1, -4, 4],
  ![1, -4, 3],
  ![1, 3, -4],
  ![1, 4, -4]]

private noncomputable def betaFactor : Fin 14 → ℝ := ![(51 / 2), (5353 / 200), (728 / 25), (327 / 10), (377 / 10), (355 / 8), (1326 / 25), (6407 / 100), (779 / 10), (181 / 20), 4, (4 / 7), 1, (10 / 11)]
private noncomputable def gammaFactor : Fin 14 → ℝ := ![(101 / 22), 26, (5559 / 200), (1537 / 50), 35, (204 / 5), (1937 / 40), (2911 / 50), (7059 / 100), 86, (19 / 20), 1, (4 / 7), 4]

private def realCone (x : (Fin 3 → ℝ)) : Prop := ∀ i : Fin 14, 0 ≤ dotProduct (normal i) x

private def complexCone : Set (Fin 3 → ℂ) :=
  {z | (∀ k, (z k).im = 0) ∧ realCone (fun k => (z k).re)}

private theorem factors_pos (i : Fin 14) : 0 < betaFactor i ∧ 0 < gammaFactor i := by
  fin_cases i <;> norm_num [betaFactor, gammaFactor]

private theorem normal_center (i : Fin 14) : dotProduct (normal i) (vertex 14) = 1 := by
  fin_cases i <;> norm_num [Matrix.vec3_dotProduct, normal, vertex]

private theorem vertex_mem (j : Fin 15) : realCone (vertex j) := by
  intro i
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.vec3_dotProduct, normal, vertex]

private theorem normal_first (i : Fin 14) : normal i 0 = 1 := by
  simpa [Matrix.vec3_dotProduct, Matrix.vecHead, vertex] using normal_center i

private theorem normal_bounds (i : Fin 14) : |normal i 1| ≤ 4 ∧ |normal i 2| ≤ 4 := by
  fin_cases i <;> norm_num [normal]

private theorem vertex_first (i : Fin 15) : vertex i 0 = 1 := by
  fin_cases i <;> norm_num [vertex]

private theorem vertex_bounds (i : Fin 15) (hi : i ≠ 12) :
    |vertex i 1| ≤ 1/4 ∧ |vertex i 2| ≤ 1/4 := by
  fin_cases i <;> norm_num [vertex] at *

private theorem small_mem (x : (Fin 3 → ℝ)) (h0 : x 0 = 1)
    (h1 : |x 1| ≤ 1/16) (h2 : |x 2| ≤ 1/16) : realCone x := by
  intro i
  have hmul1 : |normal i 1 * x 1| ≤ 1/4 := by
    rw [abs_mul]
    have hh := mul_le_mul (normal_bounds i).1 h1 (abs_nonneg (x 1)) (by norm_num : (0:ℝ) ≤ 4)
    norm_num at hh
    exact hh
  have hmul2 : |normal i 2 * x 2| ≤ 1/4 := by
    rw [abs_mul]
    have hh := mul_le_mul (normal_bounds i).2 h2 (abs_nonneg (x 2)) (by norm_num : (0:ℝ) ≤ 4)
    norm_num at hh
    exact hh
  simp only [Matrix.vec3_dotProduct]
  rw [normal_first, h0]
  linarith [(abs_le.mp hmul1).1, (abs_le.mp hmul2).1]

private theorem products_mem (i j : Fin 15) : realCone (vertex i * vertex j) := by
  have hunit : vertex 12 = 1 := by exact List.ofFn_inj.mp rfl
  by_cases hi : i = 12
  · simpa [hi, hunit] using vertex_mem j
  by_cases hj : j = 12
  · simpa [hj, hunit] using vertex_mem i
  apply small_mem
  · simp [Pi.mul_apply, vertex_first]
  · rw [Pi.mul_apply, abs_mul]
    have hh := mul_le_mul (vertex_bounds i hi).1 (vertex_bounds j hj).1
      (abs_nonneg (vertex j 1)) (by norm_num : (0:ℝ) ≤ 1/4)
    norm_num at hh
    exact hh
  · rw [Pi.mul_apply, abs_mul]
    have hh := mul_le_mul (vertex_bounds i hi).2 (vertex_bounds j hj).2
      (abs_nonneg (vertex j 2)) (by norm_num : (0:ℝ) ≤ 1/4)
    norm_num at hh
    exact hh

private theorem reconstruction (i : Fin 14) (x : (Fin 3 → ℝ)) :
    x = fun k => dotProduct (normal i) x * vertex 14 k +
      (betaFactor i * (dotProduct (normal (i + 1)) x - dotProduct (normal i) x)) *
        vertex (Fin.castSucc i) k +
      (gammaFactor i * (dotProduct (normal (i + 13)) x - dotProduct (normal i) x)) *
        vertex (Fin.castSucc (i + 1)) k := by
  funext k
  fin_cases i <;> fin_cases k <;>
    norm_num [Matrix.vec3_dotProduct, Matrix.vecHead, Matrix.vecTail, normal, vertex, betaFactor, gammaFactor, Fin.add_def, Fin.castSucc] <;> ring



private theorem cone_decomposition (x : (Fin 3 → ℝ)) (hx : realCone x) :
    ∃ (i : Fin 14) (a b c : ℝ), 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
      x = fun k => a * vertex 14 k + b * vertex (Fin.castSucc i) k + c * vertex (Fin.castSucc (i + 1)) k := by
  obtain ⟨i, hi⟩ := Finite.exists_min (fun j => dotProduct (normal j) x)
  refine ⟨i, _, _, _, hx i, mul_nonneg (factors_pos i).1.le (sub_nonneg.mpr (hi _)),
    mul_nonneg (factors_pos i).2.le (sub_nonneg.mpr (hi _)), reconstruction i x⟩

private theorem cone_add3 (a b c : ℝ) (x y z : (Fin 3 → ℝ))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : realCone x) (hy : realCone y) (hz : realCone z) :
    realCone (fun k => a * x k + b * y k + c * z k) := by
  intro i
  have heq : dotProduct (normal i) (fun k => a * x k + b * y k + c * z k) =
      a * dotProduct (normal i) x + b * dotProduct (normal i) y + c * dotProduct (normal i) z := by
    simp only [Matrix.vec3_dotProduct]
    ring
  rw [heq]
  exact add_nonneg (add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))) (mul_nonneg hc (hz i))

private theorem generator_mul (x : (Fin 3 → ℝ)) (hx : realCone x) (j : Fin 15) :
    realCone (x * vertex j) := by
  obtain ⟨i, a, b, c, ha, hb, hc, heq⟩ := cone_decomposition x hx
  have he : x * vertex j = fun k =>
      a * (vertex 14 * vertex j) k + b * (vertex (Fin.castSucc i) * vertex j) k +
      c * (vertex (Fin.castSucc (i + 1)) * vertex j) k := by
    funext k
    simp only [Pi.mul_apply, congrFun heq k]
    ring
  rw [he]
  exact cone_add3 _ _ _ _ _ _ ha hb hc (products_mem 14 j)
    (products_mem (Fin.castSucc i) j) (products_mem (Fin.castSucc (i + 1)) j)

private theorem realCone_mul (x y : (Fin 3 → ℝ)) (hx : realCone x) (hy : realCone y) :
    realCone (x * y) := by
  obtain ⟨i, a, b, c, ha, hb, hc, heq⟩ := cone_decomposition y hy
  have he : x * y = fun k =>
      a * (x * vertex 14) k + b * (x * vertex (Fin.castSucc i)) k +
      c * (x * vertex (Fin.castSucc (i + 1))) k := by
    funext k
    simp only [Pi.mul_apply, congrFun heq k]
    ring
  rw [he]
  exact cone_add3 _ _ _ _ _ _ ha hb hc (generator_mul x hx 14)
    (generator_mul x hx (Fin.castSucc i)) (generator_mul x hx (Fin.castSucc (i + 1)))


private theorem perturb_finite {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, a i = 0 → 0 ≤ b i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ a i + t * b i := by
  classical
  let δ : ι → ℝ := fun i => if a i = 0 then 1 else a i / (|b i| + 1)
  have hd : ∀ i, 0 < δ i := by
    intro i
    dsimp [δ]
    split_ifs with h
    · norm_num
    · exact div_pos (lt_of_le_of_ne (ha i) (Ne.symm h)) (by positivity)
  obtain ⟨j, hj⟩ := Finite.exists_min δ
  refine ⟨δ j, hd j, fun i => ?_⟩
  by_cases he : a i = 0
  · rw [he, zero_add]
    exact mul_nonneg (hd j).le (hb i he)
  · have hle : δ j * (|b i| + 1) ≤ a i :=
      (le_div_iff₀ (by positivity : 0 < |b i| + 1)).mp (by simpa [δ, he] using hj i)
    have hlo := mul_le_mul_of_nonneg_left (neg_abs_le (b i)) (hd j).le
    nlinarith [hd j]

private theorem midpoint_mem (i : Fin 10) : realCone (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩))) := by
  have h := cone_add3 (1/2) (1/2) 0 (vertex ⟨i.val, by omega⟩)
    (vertex ⟨i.val + 1, by omega⟩) (vertex 14)
    (by norm_num) (by norm_num) (by norm_num)
    (vertex_mem _) (vertex_mem _) (vertex_mem _)
  convert h using 1
  ext k
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, invOf_eq_inv]
  ring

private theorem edge_vanishes (i : Fin 10) : dotProduct (normal ⟨i.val, by omega⟩) (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩))) = 0 := by
  fin_cases i <;> norm_num [Matrix.vec3_dotProduct, normal, vertex, Pi.smul_apply, Pi.add_apply, smul_eq_mul, invOf_eq_inv]

private theorem active_entry {ι : Type*} [Fintype ι] [Nonempty ι]
    (L : ι → (Fin 3 → ℝ)) (heq : ∀ x, realCone x ↔ ∀ j, 0 ≤ dotProduct (L j) x) (i : Fin 10) :
    ∃ j, dotProduct (L j) (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩))) = 0 ∧ 0 < dotProduct (L j) (vertex 14) := by
  by_contra! h
  have ha : ∀ j, 0 ≤ dotProduct (L j) (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩))) := (heq _).mp (midpoint_mem i)
  obtain ⟨t, ht, hp⟩ := perturb_finite
    (fun j => dotProduct (L j) (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩)))) (fun j => -dotProduct (L j) (vertex 14)) ha
    (fun j hj => neg_nonneg.mpr (h j hj))
  have hc : realCone (fun k => ((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩)) k - t * vertex 14 k) := by
    apply (heq _).mpr
    intro j
    have hh := hp j
    convert hh using 1 <;> (simp only [Matrix.vec3_dotProduct]; ring)
  have hn := hc ⟨i.val, by omega⟩
  have hid : dotProduct (normal ⟨i.val, by omega⟩) (fun k => ((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩)) k - t * vertex 14 k) = -t := by
    calc
      _ = dotProduct (normal ⟨i.val, by omega⟩) (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩))) -
          t * dotProduct (normal ⟨i.val, by omega⟩) (vertex 14) := by simp only [Matrix.vec3_dotProduct]; ring
      _ = -t := by rw [edge_vanishes, normal_center]; ring
  rw [hid] at hn
  linarith

private theorem midpoint_zero_endpoints (a : (Fin 3 → ℝ)) (i : Fin 10)
    (ha : ∀ j : Fin 15, 0 ≤ dotProduct a (vertex j)) (hz : dotProduct a (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩))) = 0) :
    dotProduct a (vertex ⟨i.val, by omega⟩) = 0 ∧
    dotProduct a (vertex ⟨i.val + 1, by omega⟩) = 0 := by
  have he : dotProduct a (((2⁻¹ : ℝ) • (vertex ⟨i.val, by omega⟩ + vertex ⟨i.val + 1, by omega⟩))) =
      (dotProduct a (vertex ⟨i.val, by omega⟩) + dotProduct a (vertex ⟨i.val + 1, by omega⟩)) / 2 := by
    simp only [Matrix.vec3_dotProduct, Pi.smul_apply, Pi.add_apply, smul_eq_mul, invOf_eq_inv]
    ring
  rw [he] at hz
  constructor <;> linarith [ha ⟨i.val, by omega⟩, ha ⟨i.val + 1, by omega⟩]

private theorem distinct_edges_independent (a : (Fin 3 → ℝ)) (i j : Fin 10) (hij : i ≠ j)
    (hi0 : dotProduct a (vertex ⟨i.val, by omega⟩) = 0)
    (hi1 : dotProduct a (vertex ⟨i.val + 1, by omega⟩) = 0)
    (hj0 : dotProduct a (vertex ⟨j.val, by omega⟩) = 0)
    (hj1 : dotProduct a (vertex ⟨j.val + 1, by omega⟩) = 0) :
    dotProduct a (vertex 14) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.vec3_dotProduct, vertex] at * <;> linarith

private theorem no_nine_forms (L : (Fin 3 × Fin 3) → (Fin 3 → ℝ)) :
    ¬ (∀ x, realCone x ↔ ∀ j, 0 ≤ dotProduct (L j) x) := by
  intro heq
  choose f hf using active_entry L heq
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hnonneg (k : Fin 15) : 0 ≤ dotProduct (L (f i)) (vertex k) := (heq _).mp (vertex_mem k) _
    obtain ⟨hi0, hi1⟩ := midpoint_zero_endpoints _ i hnonneg (hf i).1
    obtain ⟨hj0, hj1⟩ := midpoint_zero_endpoints _ j hnonneg (by simpa [hij] using (hf j).1)
    have hh := distinct_edges_independent _ i j hne hi0 hi1 hj0 hj1
    linarith [(hf i).2]
  have hc := Fintype.card_le_of_injective f hinj
  norm_num at hc

private theorem halfspace_real (a : (Fin 3 → ℝ)) (z : Fin 3 → ℂ) :
    z ∈ halfSpace (fun k => (a k : ℂ)) 0 ↔ 0 ≤ dotProduct a (fun k => (z k).re) := by
  simp [halfSpace, Fin.sum_univ_succ, Matrix.vec3_dotProduct, add_assoc]

private noncomputable def sourceNormal (i : Fin 20) : Fin 3 → ℂ :=
  if h : i.val < 14 then (fun k => ((normal ⟨i.val, h⟩ k : ℝ) : ℂ))
  else ![![Complex.I, 0, 0], ![-Complex.I, 0, 0],
    ![0, Complex.I, 0], ![0, -Complex.I, 0],
    ![0, 0, Complex.I], ![0, 0, -Complex.I]] ⟨i.val - 14, by omega⟩

private theorem sourceNormal_ne (i : Fin 20) : sourceNormal i ≠ 0 := by
  intro h
  fin_cases i <;>
    first
    | have hh := congrFun h 0; norm_num [sourceNormal, normal, Complex.ext_iff] at hh; done
    | have hh := congrFun h 1; norm_num [sourceNormal, normal, Complex.ext_iff] at hh; done
    | have hh := congrFun h 2; norm_num [sourceNormal, normal, Complex.ext_iff] at hh; done

private theorem complexCone_polyhedral : IsSourcePolyhedralCone complexCone := by
  refine ⟨20, by decide, sourceNormal, sourceNormal_ne, ?_⟩
  ext z
  constructor
  · rintro ⟨him, hr⟩ i
    by_cases hi : i.val < 14
    · simp only [sourceNormal, dite_eq_left hi]
      exact (halfspace_real _ z).mpr (hr ⟨i.val, hi⟩)
    · fin_cases i <;> norm_num at hi <;>
        simp [halfSpace, sourceNormal, Fin.sum_univ_succ, him]
  · intro hz
    have him : ∀ k : Fin 3, (z k).im = 0 := by
      intro k
      fin_cases k
      · change (z (0 : Fin 3)).im = 0
        have hp := hz 14
        have hn := hz 15
        norm_num [halfSpace, sourceNormal, Fin.sum_univ_succ] at hp hn
        linarith
      · change (z (1 : Fin 3)).im = 0
        have hp := hz 16
        have hn := hz 17
        norm_num [halfSpace, sourceNormal, Fin.sum_univ_succ] at hp hn
        linarith
      · change (z (2 : Fin 3)).im = 0
        have hp := hz 18
        have hn := hz 19
        norm_num [halfSpace, sourceNormal, Fin.sum_univ_succ] at hp hn
        linarith
    refine ⟨him, fun i => ?_⟩
    have hh := hz ⟨i.val, by omega⟩
    have hi : i.val < 14 := i.isLt
    simpa only [sourceNormal, dite_eq_left hi, halfspace_real] using hh

private theorem complexCone_mul (x y : Fin 3 → ℂ)
    (hx : x ∈ complexCone) (hy : y ∈ complexCone) : x * y ∈ complexCone := by
  rcases hx with ⟨hxi, hxr⟩
  rcases hy with ⟨hyi, hyr⟩
  refine ⟨fun k => ?_, ?_⟩
  · simp [Pi.mul_apply, Complex.mul_im, hxi, hyi]
  · have he : (fun k => ((x * y) k).re) =
        ((fun k => (x k).re) * (fun k => (y k).re)) := by
      funext k
      simp [Pi.mul_apply, Complex.mul_re, hxi, hyi]
    rw [he]
    exact realCone_mul (fun k => (x k).re) (fun k => (y k).re) hxr hyr

private theorem entry_formula (S : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) (x : (Fin 3 → ℝ)) :
    (S * Matrix.diagonal (fun k => (x k : ℂ)) * S⁻¹) i j =
      (S i * S⁻¹.transpose j) 0 * (x 0 : ℂ) + (S i * S⁻¹.transpose j) 1 * (x 1 : ℂ) +
      (S i * S⁻¹.transpose j) 2 * (x 2 : ℂ) := by
  simp [Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_succ, Pi.mul_apply, Matrix.transpose_apply]
  ring

private theorem entry_re (S : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) (x : (Fin 3 → ℝ)) :
    ((S * Matrix.diagonal (fun k => (x k : ℂ)) * S⁻¹) i j).re =
      dotProduct (fun k => ((S i * S⁻¹.transpose j) k).re) x := by
  rw [entry_formula]
  simp [Matrix.vec3_dotProduct]

private theorem entry_im (S : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) (x : (Fin 3 → ℝ)) :
    ((S * Matrix.diagonal (fun k => (x k : ℂ)) * S⁻¹) i j).im =
      dotProduct (fun k => ((S i * S⁻¹.transpose j) k).im) x := by
  rw [entry_formula]
  simp [Matrix.vec3_dotProduct]

private theorem spectral_real_forms (S : Matrix (Fin 3) (Fin 3) ℂ)
    (heq : complexCone = spectracone S) :
    ∀ x : (Fin 3 → ℝ), realCone x ↔ ∀ j : Fin 3 × Fin 3,
      0 ≤ dotProduct (fun k => ((S j.1 * S⁻¹.transpose j.2) k).re) x := by
  have hreality (i j : Fin 3) : ∀ k : Fin 3, ((S i * S⁻¹.transpose j) k).im = 0 := by
    have hv (q : Fin 15) :
        dotProduct (fun k => ((S i * S⁻¹.transpose j) k).im) (vertex q) = 0 := by
      have hm : (fun k => (vertex q k : ℂ)) ∈ complexCone :=
        ⟨by simp, by simpa only [Complex.ofReal_re] using vertex_mem q⟩
      rw [heq] at hm
      have hz := (Complex.nonneg_iff.mp (hm i j)).2
      rw [entry_im] at hz
      exact hz.symm
    have h0 := hv 14
    have h1 := hv 11
    have h2 := hv 13
    simp only [Matrix.vec3_dotProduct] at h0 h1 h2
    change ((S i * S⁻¹.transpose j) 0).im * 1 + ((S i * S⁻¹.transpose j) 1).im * 0 + ((S i * S⁻¹.transpose j) 2).im * 0 = 0 at h0
    change ((S i * S⁻¹.transpose j) 0).im * 1 + ((S i * S⁻¹.transpose j) 1).im * (1/4) + ((S i * S⁻¹.transpose j) 2).im * 0 = 0 at h1
    change ((S i * S⁻¹.transpose j) 0).im * 1 + ((S i * S⁻¹.transpose j) 1).im * 0 + ((S i * S⁻¹.transpose j) 2).im * (1/4) = 0 at h2
    simp only [mul_one, mul_zero, add_zero] at h0 h1 h2
    intro k
    fin_cases k
    · change ((S i * S⁻¹.transpose j) 0).im = 0
      exact h0
    · change ((S i * S⁻¹.transpose j) 1).im = 0
      linarith
    · change ((S i * S⁻¹.transpose j) 2).im = 0
      linarith
  intro x
  have hm : (fun k => (x k : ℂ)) ∈ complexCone ↔ realCone x := by
    simp [complexCone]
  rw [← hm, heq]
  change (∀ i j, (0 : ℂ) ≤ (S * Matrix.diagonal (fun k => (x k : ℂ)) * S⁻¹) i j) ↔ _
  simp only [Complex.nonneg_iff, entry_re, entry_im]
  constructor
  · intro h j
    exact (h j.1 j.2).1
  · intro h i j
    refine ⟨h (i,j), ?_⟩
    simp only [Matrix.vec3_dotProduct, hreality, zero_mul, zero_add]

private theorem complexCone_not_spectral (S : Matrix (Fin 3) (Fin 3) ℂ) :
    complexCone ≠ spectracone S := by
  intro heq
  exact no_nine_forms (fun j k => ((S j.1 * S⁻¹.transpose j.2) k).re) (spectral_real_forms S heq)

theorem result : ¬ claim := by
  intro h
  obtain ⟨S, _, heq⟩ := (h 3 (by norm_num) complexCone).1
    complexCone_polyhedral complexCone_mul
  exact complexCone_not_spectral S heq


end D5.S0.FiniteGeometry.Polytopes.JohnsonPaparellaHadamardPolyhedraRefutation
