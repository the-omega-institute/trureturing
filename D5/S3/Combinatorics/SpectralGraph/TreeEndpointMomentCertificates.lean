/- GID: D5/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/TreeEndpointMomentCertificates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic, mathlib/module/Mathlib.RingTheory.Polynomial.Chebyshev]
   utility: none
   digest: Actual tree stems and positive Jacobi prefixes determine endpoint compatibility. -/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

/-! Polynomial states and rooted finite tree endpoint compatibility. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates

open Matrix Polynomial Finset SimpleGraph

section Algebra

variable {K : Type*} [Field K]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The affine change of variable for a uniform diagonal and link. -/
def affinePolynomial (a c : K) : K[X] := C c⁻¹ * (X - C a)

/-- The fixed monic chain recurrence evaluated in the original spectral variable. -/
def chainPolynomial (a c : K) (j : ℕ) : K[X] :=
  (Chebyshev.S K (j : ℤ)).comp (affinePolynomial a c)

private theorem chain_zero (a c : K) : chainPolynomial a c 0 = 1 := by
  simp [chainPolynomial]

private theorem chain_one (a c : K) : chainPolynomial a c 1 = affinePolynomial a c := by
  simp [chainPolynomial]

private theorem chain_step (a c : K) (j : ℕ) :
    chainPolynomial a c (j + 2) =
      affinePolynomial a c * chainPolynomial a c (j + 1) - chainPolynomial a c j := by
  simp only [chainPolynomial, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Chebyshev.S_add_two,
    mul_comp, sub_comp, X_comp]

private theorem chain_degree (a c : K) (j : ℕ) : (chainPolynomial a c j).natDegree ≤ j := by
  induction j using Nat.twoStepInduction with
  | zero => simp [chain_zero]
  | one => rw [chain_one]; unfold affinePolynomial; compute_degree
  | more j ih ih' =>
    rw [chain_step]
    exact (natDegree_sub_le _ _).trans (max_le
      ((natDegree_mul_le).trans (by
        have h : (affinePolynomial a c).natDegree ≤ 1 := by
          unfold affinePolynomial; compute_degree
        omega)) (by omega))

/-- The actual polynomial state at a selected coordinate. -/
def polynomialVector (M : Matrix V V K) (o : V) (p : K[X]) : V → K :=
  (aeval M p) *ᵥ Pi.single o 1

/-- Its zero-based fixed chain vectors, including the initial unit vector. -/
def chainVector (M : Matrix V V K) (o : V) (a c : K) (j : ℕ) : V → K :=
  polynomialVector M o (chainPolynomial a c j)

private theorem vector_zero (M : Matrix V V K) (o : V) (a c : K) :
    chainVector M o a c 0 = Pi.single o 1 := by
  rw [chainVector, chain_zero, polynomialVector, aeval_one, Matrix.one_mulVec]

private theorem vector_one (M : Matrix V V K) (o : V) (a c : K) :
    chainVector M o a c 1 = c⁻¹ • (M *ᵥ Pi.single o 1 - a • Pi.single o 1) := by
  simp only [chainVector, chain_one, polynomialVector, affinePolynomial, map_mul, map_sub,
    aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]

private theorem vector_step (M : Matrix V V K) (o : V) (a c : K) (j : ℕ) :
    chainVector M o a c (j + 2) =
      c⁻¹ • (M *ᵥ chainVector M o a c (j + 1) - a • chainVector M o a c (j + 1)) -
        chainVector M o a c j := by
  simp only [chainVector, chain_step, polynomialVector, affinePolynomial, map_mul, map_sub,
    aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    Matrix.sub_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, Matrix.one_mulVec]

private theorem power_pairing (M : Matrix V V K) (hs : M.IsSymm) (o : V) (i j : ℕ) :
    ((M ^ i) *ᵥ Pi.single o 1) ⬝ᵥ ((M ^ j) *ᵥ Pi.single o 1) =
      (M ^ (i + j)) o o := by
  rw [dotProduct_comm, ← dotProduct_transpose_mulVec, (hs.pow i).eq,
    Matrix.mulVec_mulVec, ← pow_add]
  simp [Matrix.mulVec_single_one, dotProduct_comm]

private theorem vector_pairing (M : Matrix V V K) (hs : M.IsSymm) (o : V)
    (p q : K[X]) :
    polynomialVector M o p ⬝ᵥ polynomialVector M o q =
      ∑ i ∈ range (p.natDegree + 1), ∑ j ∈ range (q.natDegree + 1),
        p.coeff i * q.coeff j * (M ^ (i + j)) o o := by
  simp only [polynomialVector, aeval_eq_sum_range, Matrix.sum_mulVec,
    Matrix.smul_mulVec, sum_dotProduct, dotProduct_sum, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [power_pairing M hs]
  ring

private theorem prefix_pairing {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix V V K) (J : Matrix W W K) (hs : M.IsSymm) (ht : J.IsSymm)
    (o : V) (z : W) (d : ℕ)
    (hm : ∀ k ≤ d, (M ^ k) o o = (J ^ k) z z)
    (p q : K[X]) (hd : p.natDegree + q.natDegree ≤ d) :
    polynomialVector M o p ⬝ᵥ polynomialVector M o q =
      polynomialVector J z p ⬝ᵥ polynomialVector J z q := by
  rw [vector_pairing M hs, vector_pairing J ht]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hm (i + j) (by have := mem_range.mp hi; have := mem_range.mp hj; omega)]

private theorem polynomialVector_X_mul (M : Matrix V V K) (o : V) (p : K[X]) :
    polynomialVector M o (X * p) = M *ᵥ polynomialVector M o p := by
  simp only [polynomialVector, map_mul, aeval_X, Matrix.mulVec_mulVec]

theorem prefix_chain_pairing {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix V V K) (J : Matrix W W K) (hs : M.IsSymm) (ht : J.IsSymm)
    (o : V) (z : W) (a c : K) (d i j : ℕ)
    (hm : ∀ k ≤ d, (M ^ k) o o = (J ^ k) z z) (hd : i + j ≤ d) :
    chainVector M o a c i ⬝ᵥ chainVector M o a c j =
      chainVector J z a c i ⬝ᵥ chainVector J z a c j := by
  exact prefix_pairing M J hs ht o z d hm _ _
    (by have := chain_degree a c i; have := chain_degree a c j; omega)

theorem prefix_chain_diagonal {W : Type*} [Fintype W] [DecidableEq W]
    (M : Matrix V V K) (J : Matrix W W K) (hs : M.IsSymm) (ht : J.IsSymm)
    (o : V) (z : W) (a c : K) (d j : ℕ)
    (hm : ∀ k ≤ d, (M ^ k) o o = (J ^ k) z z) (hd : 2 * j + 1 ≤ d) :
    chainVector M o a c j ⬝ᵥ (M *ᵥ chainVector M o a c j) =
      chainVector J z a c j ⬝ᵥ (J *ᵥ chainVector J z a c j) := by
  have hh := prefix_pairing M J hs ht o z d hm (chainPolynomial a c j)
    (X * chainPolynomial a c j) (by
      have h := chain_degree a c j
      have h' := natDegree_mul_le (p := (X : K[X])) (q := chainPolynomial a c j)
      simp only [natDegree_X] at h'
      omega)
  simpa only [polynomialVector_X_mul, chainVector] using hh

end Algebra

section Jacobi

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Symmetric tridiagonality with genuinely positive adjacent links, at any finite order. -/
structure PositiveJacobi {n : ℕ} (J : Matrix (Fin n) (Fin n) K) : Prop where
  symmetric : J.IsSymm
  band : ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → J i j = 0
  positive : ∀ j (h : j + 1 < n), 0 < J ⟨j, by omega⟩ ⟨j + 1, h⟩

/-- A coordinate vector whose value is zero when the requested coordinate is absent. -/
def unitAt (n j : ℕ) : Fin n → K := fun i => if i.val = j then 1 else 0

/-- A diagonal coefficient, extended by zero past the actual matrix. -/
def diagonalAt {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (j : ℕ) : K :=
  if h : j < n then J ⟨j, h⟩ ⟨j, h⟩ else 0

/-- An adjacent coefficient, extended by zero past the last actual link. -/
def nextLink {n : ℕ} (J : Matrix (Fin n) (Fin n) K) (j : ℕ) : K :=
  if h : j + 1 < n then J ⟨j, by omega⟩ ⟨j + 1, h⟩ else 0

private theorem unitAt_single {n j : ℕ} (h : j < n) :
    (unitAt n j : Fin n → K) = Pi.single ⟨j, h⟩ 1 := by
  ext i
  simp [unitAt, Pi.single_apply, Fin.ext_iff]

private theorem unitAt_absent {n j : ℕ} (h : n ≤ j) : (unitAt n j : Fin n → K) = 0 := by
  ext i
  have : i.val ≠ j := by have := i.isLt; omega
  simp [unitAt, this]

private theorem unitAt_pairing (n j : ℕ) :
    (unitAt n j : Fin n → K) ⬝ᵥ unitAt n j = if j < n then 1 else 0 := by
  split_ifs with h
  · rw [unitAt_single h]
    simp
  · rw [unitAt_absent (Nat.le_of_not_gt h)]
    simp

private theorem unitAt_diagonal {n j : ℕ} (J : Matrix (Fin n) (Fin n) K) (h : j < n) :
    (unitAt n j : Fin n → K) ⬝ᵥ (J *ᵥ unitAt n j) = J ⟨j, h⟩ ⟨j, h⟩ := by
  rw [unitAt_single h]
  simp

private theorem jacobi_column {n j : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (hJ : PositiveJacobi J) (hj : j < n) (a c : K)
    (ha : J ⟨j, hj⟩ ⟨j, hj⟩ = a)
    (hc : 0 < j → nextLink J (j - 1) = c) :
    J *ᵥ unitAt n j = a • unitAt n j +
      (if j = 0 then 0 else c • unitAt n (j - 1)) + nextLink J j • unitAt n (j + 1) := by
  have hcol : J *ᵥ unitAt n j = J.col ⟨j, hj⟩ := by
    rw [unitAt_single hj, Matrix.mulVec_single_one]
  rw [hcol]
  ext i
  simp only [col_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases he : i.val = j
  · have hie : i = ⟨j, hj⟩ := Fin.ext he
    rw [hie, ha]
    by_cases hz : j = 0
    · simp [unitAt, hz]
    · have hm : j ≠ j - 1 := by omega
      simp [unitAt, hz, hm]
  · by_cases hp : i.val + 1 = j
    · have hjp : 0 < j := by omega
      have hei : i.val = j - 1 := by omega
      have hl := hc hjp
      have hlt : j - 1 + 1 < n := by omega
      simp only [nextLink, dite_eq_left hlt] at hl
      have hi : i = ⟨j - 1, by omega⟩ := Fin.ext hei
      have hj' : (⟨j - 1 + 1, hlt⟩ : Fin n) = ⟨j, hj⟩ := by
        apply Fin.ext
        change j - 1 + 1 = j
        omega
      rw [hj'] at hl
      rw [hi, hl]
      simp [unitAt, ne_of_gt hjp, show j - 1 ≠ j by omega,
        show j - 1 ≠ j + 1 by omega]
    · by_cases hn : i.val = j + 1
      · have hlt : j + 1 < n := hn ▸ i.isLt
        have hi : i = ⟨j + 1, hlt⟩ := Fin.ext hn
        rw [hi, hJ.symmetric.apply]
        by_cases hz : j = 0
        · subst j
          have h1 : 1 < n := by omega
          simp [unitAt, nextLink, h1]
        · simp [unitAt, nextLink, hlt, hz, show j + 1 ≠ j - 1 by omega]
      · have hfar : i.val + 1 < j ∨ j + 1 < i.val := by omega
        rw [hJ.band i ⟨j, hj⟩ hfar]
        by_cases h0 : j = 0
        · have hi0 : i.val ≠ 0 := by omega
          have hi1 : i.val ≠ 1 := by omega
          simp [unitAt, h0, hi0, hi1]
        · simp [unitAt, he, hn, h0, show i.val ≠ j - 1 by omega]

private theorem jacobi_next_vector {n j : ℕ} (J : Matrix (Fin n) (Fin n) K)
    (hJ : PositiveJacobi J) (hj : j < n) (a c : K) (hc : 0 < c)
    (ha : J ⟨j, hj⟩ ⟨j, hj⟩ = a)
    (hp : 0 < j → nextLink J (j - 1) = c)
    (hw : chainVector J ⟨0, by omega⟩ a c j = unitAt n j)
    (hprev : 0 < j → chainVector J ⟨0, by omega⟩ a c (j - 1) = unitAt n (j - 1)) :
    chainVector J ⟨0, by omega⟩ a c (j + 1) =
      (c⁻¹ * nextLink J j) • unitAt n (j + 1) := by
  have hcol := jacobi_column J hJ hj a c ha hp
  by_cases hz : j = 0
  · subst j
    rw [vector_one]
    have he : (Pi.single (⟨0, by omega⟩ : Fin n) 1 : Fin n → K) = unitAt n 0 :=
      (unitAt_single (by omega)).symm
    rw [he, hcol]
    simp only [ite_true, add_zero, add_sub_cancel_left, smul_smul]
  · have hjp : 0 < j := Nat.pos_of_ne_zero hz
    have he : j + 1 = (j - 1) + 2 := by omega
    have he' : j - 1 + 1 = j := by omega
    conv_lhs => rw [he, vector_step, he']
    rw [hw, hprev hjp, hcol, ite_eq_right hz]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt hc]
    <;> ring

/-- A unit recurrence prefix fixes every existing coefficient and earns all required coordinates. -/
theorem positive_jacobi_prefix_rigidity {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    (J : Matrix (Fin n) (Fin n) K) (hJ : PositiveJacobi J) (a c : K) (hc : 0 < c)
    (hunit : ∀ j < r, chainVector J ⟨0, hn⟩ a c j ⬝ᵥ chainVector J ⟨0, hn⟩ a c j = 1)
    (hdiag : ∀ j < r,
      chainVector J ⟨0, hn⟩ a c j ⬝ᵥ (J *ᵥ chainVector J ⟨0, hn⟩ a c j) = a) :
    r ≤ n ∧
      (∀ j < r, diagonalAt J j = a) ∧
      (∀ j, j + 1 < r → nextLink J j = c) ∧
      chainVector J ⟨0, hn⟩ a c r ⬝ᵥ chainVector J ⟨0, hn⟩ a c r =
        (c⁻¹ * nextLink J (r - 1)) ^ 2 * (if r < n then 1 else 0) := by
  have step : ∀ j < r,
      j < n ∧ chainVector J ⟨0, hn⟩ a c j = unitAt n j ∧
        (∀ k < j, nextLink J k = c) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hz : j = 0
      · subst j
        refine ⟨hn, ?_, by simp⟩
        rw [vector_zero, unitAt_single hn]
      · have hjp : j - 1 < r := by omega
        obtain ⟨hprevn, hprev, hlinks⟩ := ih (j - 1) (by omega) hjp
        have ha : J ⟨j - 1, hprevn⟩ ⟨j - 1, hprevn⟩ = a := by
          simpa only [hprev, unitAt_diagonal J hprevn] using hdiag (j - 1) hjp
        have hp : 0 < j - 1 → nextLink J (j - 1 - 1) = c := by
          intro hh
          exact hlinks _ (by omega)
        have hpp : 0 < j - 1 →
            chainVector J ⟨0, hn⟩ a c (j - 1 - 1) = unitAt n (j - 1 - 1) := by
          intro hh
          exact (ih _ (by omega) (by omega)).2.1
        have hw := jacobi_next_vector J hJ hprevn a c hc ha hp hprev hpp
        have he : j - 1 + 1 = j := by omega
        rw [he] at hw
        have hu := hunit j hj
        rw [hw, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
          unitAt_pairing] at hu
        have hjn : j < n := by
          by_contra hh
          simp only [if_neg hh, mul_zero] at hu
          exact zero_ne_one hu
        rw [if_pos hjn, mul_one] at hu
        have hlpos : 0 < nextLink J (j - 1) := by
          simpa only [nextLink, dif_pos (show j - 1 + 1 < n by omega)] using
            hJ.positive (j - 1) (by omega)
        have hratio : c⁻¹ * nextLink J (j - 1) = 1 := by
          have hh := mul_pos (inv_pos.mpr hc) hlpos
          nlinarith [sq_nonneg (c⁻¹ * nextLink J (j - 1) - 1)]
        have hl : nextLink J (j - 1) = c := by
          calc
            _ = c * (c⁻¹ * nextLink J (j - 1)) := by field_simp
            _ = c := by rw [hratio, mul_one]
        refine ⟨hjn, ?_, ?_⟩
        · rw [hw, hratio, one_smul]
        · intro k hk
          by_cases heq : k = j - 1
          · simpa [heq] using hl
          · exact hlinks k (by omega)
  have hlast := step (r - 1) (by omega)
  have hbound : r ≤ n := by omega
  refine ⟨hbound, ?_, ?_, ?_⟩
  · intro j hj
    have h := hdiag j hj
    rw [(step j hj).2.1, unitAt_diagonal J (by omega)] at h
    simpa only [diagonalAt, dite_eq_left (show j < n by omega)] using h
  · intro j hj
    exact (step (j + 1) hj).2.2 j (by omega)
  · have ha : J ⟨r - 1, hlast.1⟩ ⟨r - 1, hlast.1⟩ = a := by
      simpa only [hlast.2.1, unitAt_diagonal J hlast.1] using hdiag (r - 1) (by omega)
    have hw := jacobi_next_vector J hJ hlast.1 a c hc ha
      (fun h => hlast.2.2 _ (by omega)) hlast.2.1
      (fun h => (step _ (by omega)).2.1)
    have hw' : chainVector J ⟨0, hn⟩ a c r =
        (c⁻¹ * nextLink J (r - 1)) • unitAt n r := by
      simpa only [Nat.sub_add_cancel hr] using hw
    rw [hw', smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      unitAt_pairing]
    ring

end Jacobi

section Tree

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every proper stem vertex has exactly its preceding and following stem neighbors. -/
def IsStem {o z : V} (p : G.Walk o z) : Prop :=
  ∀ j < p.length, ∀ x,
    G.Adj (p.getVert j) x ↔
      (0 < j ∧ x = p.getVert (j - 1)) ∨ x = p.getVert (j + 1)

/-- Actual forward neighbors at the last vertex, with only the incoming edge removed. -/
def forward {o z : V} (p : G.Walk o z) : Finset V :=
  (G.neighborFinset z).filter (fun x => p.length = 0 ∨ x ≠ p.penultimate)

private theorem forward_mem {o z : V} (p : G.Walk o z) (x : V) :
    x ∈ forward p ↔ G.Adj z x ∧ (p.length = 0 ∨ x ≠ p.penultimate) := by
  simp [forward]

private theorem last_neighbors {o z : V} (p : G.Walk o z) (x : V) :
    G.Adj z x ↔ (0 < p.length ∧ x = p.penultimate) ∨ x ∈ forward p := by
  rw [forward_mem]
  constructor
  · intro hx
    by_cases h : 0 < p.length ∧ x = p.penultimate
    · exact Or.inl h
    · right
      refine ⟨hx, ?_⟩
      by_cases hz : p.length = 0
      · exact Or.inl hz
      · exact Or.inr (fun he => h ⟨by omega, he⟩)
  · rintro (⟨hl, rfl⟩ | ⟨hx, _⟩)
    · exact (p.adj_penultimate (Walk.not_nil_iff_lt_length.mpr hl)).symm
    · exact hx

private theorem concat_getVert {o z y : V} (p : G.Walk o z) (h : G.Adj z y)
    (j : ℕ) (hj : j ≤ p.length) : (p.concat h).getVert j = p.getVert j := by
  rw [Walk.concat_eq_append, Walk.getVert_append', ite_eq_left hj]

private theorem stem_extend {o z y : V} (p : G.Walk o z) (hp : IsStem p)
    (hy : forward p = {y}) (hadj : G.Adj z y) : IsStem (p.concat hadj) := by
  intro j hj x
  rw [Walk.length_concat] at hj
  by_cases hlt : j < p.length
  · rw [concat_getVert p hadj j (by omega),
      concat_getVert p hadj (j - 1) (by omega),
      concat_getVert p hadj (j + 1) (by omega)]
    exact hp j hlt x
  · have he : j = p.length := by omega
    subst j
    rw [concat_getVert p hadj p.length le_rfl, Walk.getVert_length,
      concat_getVert p hadj (p.length - 1) (by omega)]
    have hend : (p.concat hadj).getVert (p.length + 1) = y := by
      simpa only [Walk.length_concat] using (p.concat hadj).getVert_length
    rw [hend]
    change G.Adj z x ↔ (0 < p.length ∧ x = p.penultimate) ∨ x = y
    rw [last_neighbors p, hy, mem_singleton]

private theorem forward_not_support {o z : V} (p : G.Walk o z)
    (hG : G.IsAcyclic) (hp : p.IsPath) {y : V} (hy : y ∈ forward p) :
    y ∉ p.support := by
  intro hmem
  have hf := (forward_mem p y).mp hy
  have he := hG.eq_penultimate_of_adj_end hp hf.1 hmem
  rcases hf.2 with hz | hne
  · have hpz : p.penultimate = z := by
      change p.getVert (p.length - 1) = z
      rw [show p.length - 1 = p.length by omega, Walk.getVert_length]
    exact hf.1.ne (he.trans hpz).symm
  · exact hne he

private theorem maximal_stem (o : V) :
    ∃ (z : V) (p : G.Walk o z), p.IsPath ∧ IsStem p ∧
      ∀ (w : V) (q : G.Walk o w), q.IsPath → IsStem q → q.length ≤ p.length := by
  classical
  let S := (range (Fintype.card V)).filter (fun k =>
    ∃ (z : V) (p : G.Walk o z), p.IsPath ∧ IsStem p ∧ p.length = k)
  have h0 : 0 ∈ S := by
    refine mem_filter.mpr ⟨mem_range.mpr (Fintype.card_pos_iff.mpr ⟨o⟩), ?_⟩
    exact ⟨o, Walk.nil, Walk.IsPath.nil, by simp [IsStem], rfl⟩
  obtain ⟨k, hk, hmax⟩ := S.exists_max_image id ⟨0, h0⟩
  obtain ⟨z, p, hp, hs, he⟩ := (mem_filter.mp hk).2
  refine ⟨z, p, hp, hs, ?_⟩
  intro w q hq ht
  rw [he]
  exact hmax q.length (mem_filter.mpr ⟨mem_range.mpr hq.length_lt,
    w, q, hq, ht, rfl⟩)

private theorem maximal_forward_ne_one {o z : V} (p : G.Walk o z)
    (hG : G.IsAcyclic) (hp : p.IsPath) (hs : IsStem p)
    (hmax : ∀ (w : V) (q : G.Walk o w), q.IsPath → IsStem q → q.length ≤ p.length) :
    (forward p).card ≠ 1 := by
  intro h
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h
  have hym : y ∈ forward p := hy.symm ▸ mem_singleton_self y
  have hadj := ((forward_mem p y).mp hym).1
  have hpath := hp.concat (forward_not_support p hG hp hym) hadj
  have hlen := hmax y (p.concat hadj) hpath (stem_extend p hs hy hadj)
  rw [Walk.length_concat] at hlen
  omega

private theorem forward_bound {o z : V} (p : G.Walk o z)
    (hd : ∀ x, G.degree x ≤ 3) : (forward p).card ≤ 3 := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (hd z)

private theorem forward_bound_nonempty {o z : V} (p : G.Walk o z)
    (hd : ∀ x, G.degree x ≤ 3) (hl : 0 < p.length) : (forward p).card ≤ 2 := by
  have he : forward p = (G.neighborFinset z).erase p.penultimate := by
    ext x
    simp [forward, show p.length ≠ 0 by omega, and_comm]
  have hm : p.penultimate ∈ G.neighborFinset z := by
    exact (G.mem_neighborFinset z p.penultimate).mpr
      (p.adj_penultimate (Walk.not_nil_iff_lt_length.mpr hl)).symm
  have hh := Finset.card_erase_add_one hm
  rw [← he] at hh
  have hdeg := hd z
  change (G.neighborFinset z).card ≤ 3 at hdeg
  omega

private theorem zero_forward_hamiltonian {o z : V} (p : G.Walk o z)
    (hG : G.Connected) (hp : p.IsPath) (hs : IsStem p) (hf : forward p = ∅) :
    p.IsHamiltonian := by
  have closed : ∀ x ∈ p.support, ∀ y, G.Adj x y → y ∈ p.support := by
    intro x hx y hxy
    obtain ⟨j, he, hj⟩ := Walk.mem_support_iff_exists_getVert.mp hx
    by_cases hlt : j < p.length
    · rw [← he] at hxy
      rcases (hs j hlt y).mp hxy with ⟨_, rfl⟩ | rfl <;>
        exact p.getVert_mem_support _
    · have heq : j = p.length := by omega
      subst j
      rw [Walk.getVert_length] at he
      subst x
      rcases (last_neighbors p y).mp hxy with ⟨_, rfl⟩ | hmem
      · exact p.getVert_mem_support _
      · simpa [hf] using hmem
  apply hp.isHamiltonian_of_mem
  intro y
  obtain ⟨q⟩ := hG o y
  have hwalk : ∀ {x y} (q : G.Walk x y), x ∈ p.support → y ∈ p.support := by
    intro x y q
    induction q with
    | nil => exact id
    | @cons x w y h q ih => exact fun hx => ih (closed x hx w h)
  exact hwalk q p.start_mem_support

/-- A genuine path graph isomorphism carrying the selected actual port to its first endpoint.
The index `n` is one less than the order, so the singleton is included. -/
def EndpointPath (G : SimpleGraph V) (o : V) : Prop :=
  ∃ (n : ℕ) (e : G ≃g pathGraph (n + 1)), e o = 0

private theorem zero_forward_endpoint {o z : V} (p : G.Walk o z)
    (hG : G.Connected) (hp : p.IsPath) (hs : IsStem p) (hf : forward p = ∅) :
    ∃ e : G ≃g pathGraph (p.length + 1), e o = 0 := by
  have hh := zero_forward_hamiltonian p hG hp hs hf
  have edges : ∀ x y, G.Adj x y → p.toSubgraph.Adj x y := by
    intro x y hxy
    obtain ⟨j, he, hj⟩ := Walk.mem_support_iff_exists_getVert.mp (hh.mem_support x)
    rw [← he] at hxy ⊢
    by_cases hlt : j < p.length
    · rcases (hs j hlt y).mp hxy with ⟨hpos, rfl⟩ | rfl
      · have h := p.toSubgraph_adj_getVert (by omega : j - 1 < p.length)
        simpa only [Nat.sub_add_cancel hpos] using h.symm
      · exact p.toSubgraph_adj_getVert hlt
    · have heq : j = p.length := by omega
      subst j
      rw [Walk.getVert_length] at hxy ⊢
      rcases (last_neighbors p y).mp hxy with ⟨hpos, rfl⟩ | hy
      · exact (p.toSubgraph_adj_penultimate (Walk.not_nil_iff_lt_length.mpr hpos)).symm
      · simp [hf] at hy
  let f : p.toSubgraph.coe ≃g G := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, p.mem_verts_toSubgraph.mpr (hh.mem_support x)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by intro x y; exact ⟨edges x y, fun h => h.adj_sub⟩ }
  let e : pathGraph (p.length + 1) ≃g G := hp.pathGraphIsoToSubgraph.trans f
  have he0 : e 0 = o := by
    change p.support[0] = o
    rw [Walk.support_getElem_eq_getVert]
    exact p.getVert_zero
  refine ⟨e.symm, ?_⟩
  apply e.injective
  simpa only [e.apply_symm_apply] using he0.symm

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The uniform law on the very same actual graph and coordinates. -/
def uniformMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (a c : K) : Matrix V V K :=
  a • 1 + c • G.adjMatrix K

/-- Squared Euclidean length, expressed over the coefficient field. -/
def chainNorm (M : Matrix V V K) (o : V) (a c : K) (j : ℕ) : K :=
  chainVector M o a c j ⬝ᵥ chainVector M o a c j

/-- An actual finite boundary indicator in the original vertex coordinates. -/
def indicatorVector (s : Finset V) : V → K := fun x => if x ∈ s then 1 else 0

private theorem uniform_recurrence (a c : K) (hc : c ≠ 0) (v : V → K) :
    c⁻¹ • (uniformMatrix G a c *ᵥ v - a • v) = G.adjMatrix K *ᵥ v := by
  simp only [uniformMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem uniform_vector_one (a c : K) (hc : c ≠ 0) (o : V) :
    chainVector (uniformMatrix G a c) o a c 1 = G.adjMatrix K *ᵥ Pi.single o 1 := by
  rw [vector_one, uniform_recurrence a c hc]

private theorem uniform_vector_step (a c : K) (hc : c ≠ 0) (o : V) (j : ℕ) :
    chainVector (uniformMatrix G a c) o a c (j + 2) =
      G.adjMatrix K *ᵥ chainVector (uniformMatrix G a c) o a c (j + 1) -
        chainVector (uniformMatrix G a c) o a c j := by
  rw [vector_step, uniform_recurrence a c hc]

private theorem stem_adjacency_action {o z : V} (p : G.Walk o z)
    (hp : p.IsPath) (hs : IsStem p) (j : ℕ) (hj : j < p.length) :
    G.adjMatrix K *ᵥ Pi.single (p.getVert j) 1 =
      (if j = 0 then 0 else Pi.single (p.getVert (j - 1)) 1) +
        Pi.single (p.getVert (j + 1)) 1 := by
  rw [Matrix.mulVec_single_one]
  ext x
  simp only [col_apply, adjMatrix_apply, Pi.add_apply]
  have hx : G.Adj x (p.getVert j) ↔
      (0 < j ∧ x = p.getVert (j - 1)) ∨ x = p.getVert (j + 1) :=
    (G.adj_comm x (p.getVert j)).trans (hs j hj x)
  simp only [hx]
  by_cases hz : j = 0
  · subst j
    simp [Pi.single_apply, eq_comm]
  · have hjp : 0 < j := by omega
    have hne : p.getVert (j - 1) ≠ p.getVert (j + 1) := by
      intro he
      have hh := hp.getVert_injOn (by simp; omega) (by simp; omega) he
      omega
    simp only [ite_eq_right hz, hjp, true_and, Pi.single_apply]
    by_cases ha : x = p.getVert (j - 1) <;>
      by_cases hb : x = p.getVert (j + 1) <;> simp_all

private theorem stem_vectors {o z : V} (p : G.Walk o z) (hp : p.IsPath) (hs : IsStem p)
    (a c : K) (hc : c ≠ 0) (j : ℕ) (hj : j ≤ p.length) :
    chainVector (uniformMatrix G a c) o a c j = Pi.single (p.getVert j) 1 := by
  induction j using Nat.twoStepInduction with
  | zero => simp only [vector_zero, Walk.getVert_zero]
  | one =>
    rw [uniform_vector_one a c hc]
    simpa only [Walk.getVert_zero, ite_true, zero_add] using
      (stem_adjacency_action (K := K) p hp hs 0 (by omega))
  | more j ih ih' =>
    rw [uniform_vector_step a c hc, ih' (by omega), ih (by omega),
      stem_adjacency_action p hp hs (j + 1) (by omega)]
    simp

private theorem final_adjacency_action {o z : V} (p : G.Walk o z) :
    G.adjMatrix K *ᵥ Pi.single z 1 =
      (if p.length = 0 then 0 else Pi.single p.penultimate 1) + indicatorVector (forward p) := by
  rw [Matrix.mulVec_single_one]
  ext x
  simp only [col_apply, adjMatrix_apply, Pi.add_apply, indicatorVector]
  have hx : G.Adj x z ↔ (0 < p.length ∧ x = p.penultimate) ∨ x ∈ forward p :=
    (G.adj_comm x z).trans (last_neighbors p x)
  simp only [hx]
  by_cases hz : p.length = 0
  · simp [hz]
  · have hpos : 0 < p.length := by omega
    have hnot : p.penultimate ∉ forward p := by simp [forward, hz]
    simp only [ite_eq_right hz, hpos, true_and, Pi.single_apply]
    by_cases ha : x = p.penultimate <;>
      by_cases hb : x ∈ forward p <;> simp_all

private theorem final_vector {o z : V} (p : G.Walk o z) (hp : p.IsPath) (hs : IsStem p)
    (a c : K) (hc : c ≠ 0) :
    chainVector (uniformMatrix G a c) o a c (p.length + 1) = indicatorVector (forward p) := by
  by_cases hz : p.length = 0
  · have hoz : o = z := by
      have hh := p.getVert_length
      simpa only [hz, Walk.getVert_zero] using hh
    rw [hz, zero_add, uniform_vector_one a c hc]
    conv_lhs => rw [hoz]
    simpa only [hz, ite_true, zero_add] using (final_adjacency_action (K := K) p)
  · have hpos : 0 < p.length := by omega
    have he : p.length + 1 = (p.length - 1) + 2 := by omega
    rw [he, uniform_vector_step a c hc]
    have he' : p.length - 1 + 1 = p.length := by omega
    rw [he', stem_vectors p hp hs a c hc p.length le_rfl,
      stem_vectors p hp hs a c hc (p.length - 1) (by omega), Walk.getVert_length,
      final_adjacency_action p, ite_eq_right hz]
    change Pi.single p.penultimate 1 + indicatorVector (forward p) -
      Pi.single p.penultimate 1 = _
    exact add_sub_cancel_left _ _

private theorem indicator_pairing (s : Finset V) :
    (indicatorVector s : V → K) ⬝ᵥ indicatorVector s = s.card := by
  classical
  simp [indicatorVector, dotProduct, ← Finset.sum_filter]

private theorem stem_gram {o z : V} (p : G.Walk o z) (hp : p.IsPath) (hs : IsStem p)
    (a c : K) (hc : c ≠ 0) (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) :
    chainVector (uniformMatrix G a c) o a c i ⬝ᵥ
      chainVector (uniformMatrix G a c) o a c j = if i = j then 1 else 0 := by
  rw [stem_vectors p hp hs a c hc i hi, stem_vectors p hp hs a c hc j hj]
  by_cases he : i = j
  · simp [he]
  · have hne : p.getVert i ≠ p.getVert j := by
      intro hh
      exact he (hp.getVert_injOn hi hj hh)
    simp [he, hne]

private theorem stem_diagonal {o z : V} (p : G.Walk o z) (hp : p.IsPath) (hs : IsStem p)
    (a c : K) (hc : c ≠ 0) (j : ℕ) (hj : j ≤ p.length) :
    chainVector (uniformMatrix G a c) o a c j ⬝ᵥ
      (uniformMatrix G a c *ᵥ chainVector (uniformMatrix G a c) o a c j) = a := by
  rw [stem_vectors p hp hs a c hc j hj]
  simp [uniformMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
    dotProduct_smul, Matrix.one_mulVec]

/-- The first nonunit recurrence norm is earned on the actual finite subcubic tree. -/
theorem tree_first_departure (hG : G.IsTree) (hd : ∀ x, G.degree x ≤ 3)
    (o : V) (a c : K) (hc : 0 < c) :
    ∃ (z : V) (p : G.Walk o z), p.IsPath ∧ IsStem p ∧
      1 ≤ p.length + 1 ∧ p.length + 1 ≤ Fintype.card V ∧
      (∀ i < p.length + 1, ∀ j < p.length + 1,
        chainVector (uniformMatrix G a c) o a c i ⬝ᵥ
          chainVector (uniformMatrix G a c) o a c j = if i = j then 1 else 0) ∧
      (∀ j < p.length + 1, chainVector (uniformMatrix G a c) o a c j ⬝ᵥ
        (uniformMatrix G a c *ᵥ chainVector (uniformMatrix G a c) o a c j) = a) ∧
      chainNorm (uniformMatrix G a c) o a c (p.length + 1) = (forward p).card ∧
      ((forward p).card = 0 ∨ (forward p).card = 2 ∨ (forward p).card = 3) ∧
      (0 < p.length → (forward p).card ≠ 3) ∧
      ((forward p).card = 0 → ∃ e : G ≃g pathGraph (p.length + 1), e o = 0) ∧
      (∀ j < p.length + 1, chainVector (uniformMatrix G a c) o a c j =
        Pi.single (p.getVert j) 1) ∧
      chainVector (uniformMatrix G a c) o a c (p.length + 1) =
        indicatorVector (forward p) := by
  obtain ⟨z, p, hp, hs, hmax⟩ := maximal_stem (G := G) o
  have hne := maximal_forward_ne_one p hG.2 hp hs hmax
  have hb := forward_bound p hd
  refine ⟨z, p, hp, hs, by omega, by have := hp.length_lt; omega,
    ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    exact stem_gram p hp hs a c (ne_of_gt hc) i j (by omega) (by omega)
  · intro j hj
    exact stem_diagonal p hp hs a c (ne_of_gt hc) j (by omega)
  · rw [chainNorm, final_vector p hp hs a c (ne_of_gt hc), indicator_pairing]
  · intro hl
    have hh := forward_bound_nonempty p hd hl
    omega
  · intro hf
    exact zero_forward_endpoint p hG.1 hp hs (Finset.card_eq_zero.mp hf)
  · intro j hj
    exact stem_vectors p hp hs a c (ne_of_gt hc) j (by omega)
  · exact final_vector p hp hs a c (ne_of_gt hc)

end Tree

end D5.S3.Combinatorics.SpectralGraph.TreeEndpointMomentCertificates
