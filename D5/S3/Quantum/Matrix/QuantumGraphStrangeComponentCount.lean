/- GID: D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Quantum graph components equal graph components plus loop-free isolated strange edges. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Matrix.RecordCapacity
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Matrix.Basis

/-! # The component count of diagonal-orthogonal quantum graphs -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount

open scoped BigOperators ComplexOrder
open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The realigned projector, with the diagonal-coordinate block diagonal. -/
def realignedProjector {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q =>
    if p.1 = p.2 then
      if q = (p.1, p.1) then d p.1 else 0
    else if q = p then A p.1 p.2
    else if q = (p.2, p.1) then C p.1 p.2 else 0

/-- Realignment reads the first and third indices as output indices. -/
def adjacency {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) : Mat n →ₗ[ℂ] Mat n where
  toFun Z i k := ∑ j, ∑ l, realignedProjector A C d (i, j) (k, l) * Z j l
  map_add' X Y := by
    funext i k
    change (∑ j, ∑ l, realignedProjector A C d (i, j) (k, l) * (X j l + Y j l)) =
      (∑ j, ∑ l, realignedProjector A C d (i, j) (k, l) * X j l) +
      (∑ j, ∑ l, realignedProjector A C d (i, j) (k, l) * Y j l)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' a X := by
    funext i k
    change (∑ j, ∑ l, realignedProjector A C d (i, j) (k, l) * (a * X j l)) =
      a * (∑ j, ∑ l, realignedProjector A C d (i, j) (k, l) * X j l)
    simp only [Finset.mul_sum, mul_left_comm]

/-- A self-adjoint idempotent matrix. -/
def IsOrthogonalProjector {n : ℕ} (P : Mat n) : Prop :=
  P.IsHermitian ∧ P * P = P

/-- Removing the diagonal gives the matrix governing undirectedness. -/
def offDiagonal {n : ℕ} (A : Mat n) : Mat n :=
  fun i j => if i = j then 0 else A i j

/-- Nonzero projectors resolving the identity and separating left multiplication. -/
def HasComponents {n : ℕ} (G : Mat n →ₗ[ℂ] Mat n) (k : ℕ) : Prop :=
  ∃ P : Fin k → Mat n,
    (∀ s, IsOrthogonalProjector (P s) ∧ P s ≠ 0) ∧
    (∑ s, P s) = 1 ∧
    ∀ s t, s ≠ t → ∀ Z, P s * G (P t * Z) = 0

/-- The simple graph records exactly the nonzero off-diagonal two-by-two blocks. -/
def underlyingGraph {n : ℕ} (A C : Mat n) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ (A i j ≠ 0 ∨ A j i ≠ 0 ∨ C i j ≠ 0 ∨ C j i ≠ 0)
  symm := ⟨by
    intro i j h
    exact ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨by intro i; simp⟩

/-- A two-vertex component whose strange edge has no loop at either endpoint. -/
def IsLoopFreeStrangeComponent {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : (underlyingGraph A C).ConnectedComponent) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ Q.supp = {i, j} ∧
    (underlyingGraph A C).Adj i j ∧ A i j = (1 / 2 : ℂ) ∧ d i = 0 ∧ d j = 0

/-- The number of connected components of the underlying simple graph. -/
def graphComponentCount {n : ℕ} (A C : Mat n) : ℕ := by
  classical
  exact Fintype.card (underlyingGraph A C).ConnectedComponent

/-- The number of loop-free isolated strange edges, counted as components. -/
def loopFreeStrangeComponentCount {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) : ℕ := by
  classical
  exact Fintype.card {Q : (underlyingGraph A C).ConnectedComponent //
    IsLoopFreeStrangeComponent A C d Q}

/-- The exact count, for arbitrary size, phase, and common diagonal. -/
def claim : Prop :=
  ∀ (n : ℕ) (A C : Mat n) (d : Fin n → ℂ),
    (∀ i, A i i = d i) → (∀ i, C i i = d i) →
    (realignedProjector A C d).IsHermitian →
    realignedProjector A C d * realignedProjector A C d = realignedProjector A C d →
    (offDiagonal A).IsHermitian →
    IsGreatest {k | HasComponents (adjacency A C d) k}
      (graphComponentCount A C + loopFreeStrangeComponentCount A C d)

private def column {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (q : Fin n × Fin n) : Mat n :=
  fun i j => realignedProjector A C d (i, j) q

private theorem column_diag {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) (i : Fin n) :
    column A C d (i, i) = Matrix.single i i (d i) := by
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = i <;> by_cases hab : a = b <;>
    simp_all [column, realignedProjector, Matrix.single, Prod.mk.injEq, eq_comm]

private theorem column_off {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    {i j : Fin n} (hij : i ≠ j) :
    column A C d (i, j) = Matrix.single i j (A i j) + Matrix.single j i (C j i) := by
  ext a b
  by_cases hab : a = b <;> by_cases hai : a = i <;> by_cases haj : a = j <;>
    by_cases hbi : b = i <;> by_cases hbj : b = j <;>
    simp_all [column, realignedProjector, Matrix.single, Prod.mk.injEq, eq_comm]

private theorem xr_row_off {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    {i j : Fin n} (hij : i ≠ j) (q : Fin n × Fin n) :
    realignedProjector A C d (i, j) q =
      (if q = (i, j) then A i j else 0) + (if q = (j, i) then C i j else 0) := by
  simp only [realignedProjector, hij, if_false]
  by_cases hq : q = (i, j)
  · subst q
    simp [hij, hij.symm]
  · simp [hq]

private theorem xr_mul_row {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    {i j : Fin n} (hij : i ≠ j)
    (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) (q : Fin n × Fin n) :
    (realignedProjector A C d * M) (i, j) q =
      A i j * M (i, j) q + C i j * M (j, i) q := by
  classical
  simp only [Matrix.mul_apply, xr_row_off A C d hij, add_mul, Finset.sum_add_distrib]
  simp

private theorem block_hermitian {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hU : (offDiagonal A).IsHermitian) {i j : Fin n} (hij : i ≠ j) :
    A j i = A i j ∧ star (A i j) = A i j ∧ C j i = star (C i j) := by
  have ha : star (A i j) = A i j := by
    simpa [realignedProjector, hij] using hH.apply (i, j) (i, j)
  have ha' : star (A j i) = A j i := by
    simpa [realignedProjector, hij.symm] using hH.apply (j, i) (j, i)
  have hu : star (A j i) = A i j := by
    simpa [offDiagonal, hij, hij.symm] using hU.apply i j
  have hc : star (C i j) = C j i := by
    simpa [realignedProjector, hij, hij.symm] using hH.apply (j, i) (i, j)
  exact ⟨ha'.symm.trans hu, ha, hc.symm⟩

private theorem block_equations {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    {i j : Fin n} (hij : i ≠ j) :
    A i j * A i j + C i j * C j i = A i j ∧
      A i j * C i j + C i j * A j i = C i j := by
  constructor
  · have h := congrArg (fun M => M (i, j) (i, j)) hI
    rw [xr_mul_row A C d hij] at h
    simpa [realignedProjector, hij, hij.symm] using h
  · have h := congrArg (fun M => M (i, j) (j, i)) hI
    rw [xr_mul_row A C d hij] at h
    simpa [realignedProjector, hij, hij.symm] using h

private theorem block_cases {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) {i j : Fin n} (hij : i ≠ j) :
    (A i j = 0 ∧ A j i = 0 ∧ C i j = 0 ∧ C j i = 0) ∨
    (A i j = 1 ∧ A j i = 1 ∧ C i j = 0 ∧ C j i = 0) ∨
    (A i j = (1 / 2 : ℂ) ∧ A j i = (1 / 2 : ℂ) ∧
      C i j * C j i = (1 / 4 : ℂ) ∧ C i j ≠ 0 ∧ C j i ≠ 0) := by
  obtain ⟨ha, hreal, hcstar⟩ := block_hermitian A C d hH hU hij
  obtain ⟨hdiag, hoff⟩ := block_equations A C d hI hij
  by_cases hc : C i j = 0
  · have hc' : C j i = 0 := by simp only [hcstar, hc, star_zero]
    have hfactor : A i j * (A i j - 1) = 0 := by
      rw [hc, zero_mul, add_zero] at hdiag
      linear_combination hdiag
    rcases mul_eq_zero.mp hfactor with hzero | hone
    · exact Or.inl ⟨hzero, ha.trans hzero, hc, hc'⟩
    · have h := sub_eq_zero.mp hone
      exact Or.inr (Or.inl ⟨h, ha.trans h, hc, hc'⟩)
  · have hfactor : (2 * A i j - 1) * C i j = 0 := by
      rw [ha] at hoff
      linear_combination hoff
    have hhalf : A i j = (1 / 2 : ℂ) := by
      have h := (mul_eq_zero.mp hfactor).resolve_right hc
      linear_combination (1 / 2 : ℂ) * h
    have hprod : C i j * C j i = (1 / 4 : ℂ) := by
      rw [hhalf] at hdiag
      linear_combination hdiag
    refine Or.inr (Or.inr ⟨hhalf, ha.trans hhalf, hprod, hc, ?_⟩)
    intro hz
    rw [hz, mul_zero] at hprod
    norm_num at hprod

private theorem edge_a_ne_zero {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) {i j : Fin n}
    (hij : (underlyingGraph A C).Adj i j) : A i j ≠ 0 := by
  rcases block_cases A C d hH hI hU hij.1 with h | h | h
  · rcases h with ⟨h₁, h₂, h₃, h₄⟩
    exact (hij.2.elim (fun h => h h₁)
      (fun h => h.elim (fun h => h h₂) (fun h => h.elim (fun h => h h₃) (fun h => h h₄)))).elim
  · rw [h.1]
    exact one_ne_zero
  · rw [h.1]
    norm_num

private theorem commutant_diagonal_edge {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) (P : Mat n)
    (hcomm : ∀ q, P * column A C d q = column A C d q * P)
    {i j : Fin n} (hij : (underlyingGraph A C).Adj i j) : P i i = P j j := by
  have h := congrArg (fun M => M i j) (hcomm (i, j))
  rw [column_off A C d hij.1] at h
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_apply, Matrix.single,
    hij.1, hij.1.symm] at h
  apply mul_right_cancel₀ (edge_a_ne_zero A C d hH hI hU hij)
  simpa only [mul_comm] using h

private theorem commutant_support_edge {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) (P : Mat n)
    (hcomm : ∀ q, P * column A C d q = column A C d q * P)
    {i j r : Fin n} (hij : (underlyingGraph A C).Adj i j) (hri : r ≠ i) (hrj : r ≠ j) :
    P r i = 0 := by
  have h := congrArg (fun M => M r j) (hcomm (i, j))
  rw [column_off A C d hij.1] at h
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_apply, Matrix.single,
    hij.1, hij.1.symm, hri, hri.symm, hrj, hrj.symm] at h
  exact h.resolve_right (edge_a_ne_zero A C d hH hI hU hij)

private theorem commutant_offdiag_relation {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (P : Mat n) (hcomm : ∀ q, P * column A C d q = column A C d q * P)
    {i j : Fin n} (hij : i ≠ j) : P i j * A j i = C i j * P j i := by
  have h := congrArg (fun M => M i i) (hcomm (j, i))
  rw [column_off A C d hij.symm] at h
  simpa [Matrix.mul_add, Matrix.add_mul, Matrix.mul_apply, Matrix.single,
    hij, hij.symm] using h

private theorem commutant_offdiag_loops {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (P : Mat n) (hcomm : ∀ q, P * column A C d q = column A C d q * P)
    {i j : Fin n} (hij : i ≠ j) (hne : P i j ≠ 0) : d i = 0 ∧ d j = 0 := by
  have hi := congrArg (fun M => M i j) (hcomm (i, i))
  have hj := congrArg (fun M => M i j) (hcomm (j, j))
  rw [column_diag] at hi hj
  simp [Matrix.mul_apply, Matrix.single, hij, hij.symm] at hi hj
  exact ⟨hi.resolve_right hne, hj.resolve_left hne⟩

private theorem component_pair {n : ℕ} (g : SimpleGraph (Fin n)) {i j : Fin n}
    (hij : g.Adj i j) (hi : ∀ u, g.Adj i u → u = j) (hj : ∀ u, g.Adj j u → u = i) :
    (g.connectedComponentMk i).supp = {i, j} := by
  have hmi : i ∈ (g.connectedComponentMk i).supp :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  have hmj := ((g.connectedComponentMk i).mem_supp_congr_adj hij).mp hmi
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hv
    change g.connectedComponentMk v = g.connectedComponentMk i at hv
    have hr := (SimpleGraph.ConnectedComponent.exact hv).symm
    have ht := (SimpleGraph.reachable_iff_reflTransGen i v).mp hr
    clear hv hr
    induction ht with
    | refl => exact Or.inl rfl
    | @tail b c hpath hbc ih =>
      rcases ih with rfl | rfl
      · exact Or.inr (hi c hbc)
      · exact Or.inl (hj c hbc)
  · rintro (rfl | rfl)
    · exact hmi
    · exact hmj

private theorem commutant_diagonal_reachable {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) (P : Mat n)
    (hcomm : ∀ q, P * column A C d q = column A C d q * P)
    {i j : Fin n} (hr : (underlyingGraph A C).Reachable i j) : P i i = P j j := by
  have ht := (SimpleGraph.reachable_iff_reflTransGen i j).mp hr
  clear hr
  induction ht with
  | refl => rfl
  | tail hpath hbc ih =>
    exact ih.trans (commutant_diagonal_edge A C d hH hI hU P hcomm hbc)

private theorem commutant_offdiag_exceptional {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) (P : Mat n) (hP : P.IsHermitian)
    (hcomm : ∀ q, P * column A C d q = column A C d q * P)
    {i j : Fin n} (hij : i ≠ j) (hne : P i j ≠ 0)
    (hex : ∃ u, (underlyingGraph A C).Adj i u) :
    IsLoopFreeStrangeComponent A C d ((underlyingGraph A C).connectedComponentMk i) := by
  have hne' : P j i ≠ 0 := by
    intro hz
    exact hne (star_eq_zero.mp ((hP.apply j i).trans hz))
  have hi : ∀ u, (underlyingGraph A C).Adj i u → u = j := by
    intro u hiu
    by_contra hu
    exact hne' (commutant_support_edge A C d hH hI hU P hcomm hiu hij.symm
      (fun h => hu h.symm))
  obtain ⟨u, hiu⟩ := hex
  have hadj : (underlyingGraph A C).Adj i j := (hi u hiu) ▸ hiu
  have hj : ∀ u, (underlyingGraph A C).Adj j u → u = i := by
    intro u hju
    by_contra hu
    exact hne (commutant_support_edge A C d hH hI hU P hcomm hju hij
      (fun h => hu h.symm))
  have hhalf : A i j = (1 / 2 : ℂ) := by
    rcases block_cases A C d hH hI hU hij with h | h | h
    · exact False.elim ((edge_a_ne_zero A C d hH hI hU hadj) h.1)
    · have he := commutant_offdiag_relation A C d P hcomm hij
      rw [h.2.1, h.2.2.1, mul_one, zero_mul] at he
      exact False.elim (hne he)
    · exact h.1
  exact ⟨i, j, hij, component_pair _ hadj hi hj, hadj, hhalf,
    commutant_offdiag_loops A C d P hcomm hij hne⟩

private def CommutantResolution {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) (k : ℕ) : Prop :=
  ∃ P : Fin k → Mat n,
    (∀ s, IsOrthogonalProjector (P s) ∧ P s ≠ 0) ∧
    (∑ s, P s) = 1 ∧
    ∀ s q, P s * column A C d q = column A C d q * P s

private theorem adjacency_kraus {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (Z : Mat n) :
    adjacency A C d Z = ∑ q, column A C d q * Z * (column A C d q)ᴴ := by
  have hc : MatrixMap.choi_matrix (adjacency A C d) = realignedProjector A C d := by
    ext ⟨i, j⟩ ⟨k, l⟩
    change (∑ a, ∑ b, realignedProjector A C d (i, a) (k, b) *
      Matrix.single j l (1 : ℂ) a b) = realignedProjector A C d (i, j) (k, l)
    simp [Matrix.single, ite_and]
  have hk : MatrixMap.choi_matrix (MatrixMap.of_kraus (column A C d) (column A C d)) =
      realignedProjector A C d := by
    rw [MatrixMap.choi_of_kraus]
    ext p q
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, column]
    change (∑ r, realignedProjector A C d p r * star (realignedProjector A C d q r)) =
      realignedProjector A C d p q
    simpa only [Matrix.mul_apply, hH.apply] using congrArg (fun M => M p q) hI
  have heq := MatrixMap.choi_matrix_inj (hc.trans hk.symm)
  simpa only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
    using congrArg (fun F : Mat n →ₗ[ℂ] Mat n => F Z) heq

private theorem gram_sum_zero {n : ℕ} {ι : Type*} (T : Finset ι) (K : ι → Mat n)
    (h : (∑ r ∈ T, K r * (K r)ᴴ) = 0) : ∀ r ∈ T, K r = 0 := by
  intro r hr
  have ht : (∑ t ∈ T, Matrix.trace (K t * (K t)ᴴ)) = 0 := by
    simpa only [Matrix.trace_sum, Matrix.trace_zero] using congrArg Matrix.trace h
  exact Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp
    ((Finset.sum_eq_zero_iff_of_nonneg
      (fun t _ => (Matrix.posSemidef_self_mul_conjTranspose (K t)).trace_nonneg)).mp ht r hr)

private theorem resolution_orthogonal {n k : ℕ} (P : Fin k → Mat n)
    (hP : ∀ s, IsOrthogonalProjector (P s)) (hsum : (∑ s, P s) = 1) :
    ∀ s t, s ≠ t → P s * P t = 0 := by
  classical
  intro s t hst
  have hgram : (∑ r ∈ Finset.univ.erase s, (P s * P r) * (P s * P r)ᴴ) = 0 := by
    calc
      _ = P s * (∑ r ∈ Finset.univ.erase s, P r) * P s := by
        simp only [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Matrix.conjTranspose_mul, (hP r).1, (hP s).1]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P r) (P r), (hP r).2]
      _ = P s * (1 - P s) * P s := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ s), hsum]
      _ = 0 := by rw [mul_sub, mul_one, (hP s).2, sub_self, zero_mul]
  exact gram_sum_zero (Finset.univ.erase s) (fun r => P s * P r) hgram t
    (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ t⟩)

private theorem separating_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (K : ι → Mat n) (P Q : Mat n)
    (hP : IsOrthogonalProjector P) (hQ : IsOrthogonalProjector Q) :
    (∀ Z, P * (∑ q, K q * (Q * Z) * (K q)ᴴ) = 0) ↔
      ∀ q, P * K q * Q = 0 := by
  constructor
  · intro h q
    have hz : P * (∑ r, K r * Q * (K r)ᴴ) * P = 0 := by
      simpa only [Matrix.mul_one, Matrix.zero_mul] using
        congrArg (fun M => M * P) (h 1)
    have hg : (∑ r, (P * K r * Q) * (P * K r * Q)ᴴ) = 0 := by
      calc
        _ = P * (∑ r, K r * Q * (K r)ᴴ) * P := by
          simp only [Matrix.mul_sum, Matrix.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ.1, hP.1]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q Q, hQ.2]
        _ = 0 := hz
    exact gram_sum_zero Finset.univ (fun r => P * K r * Q) hg q (Finset.mem_univ q)
  · intro h Z
    rw [Matrix.mul_sum]
    apply Finset.sum_eq_zero
    intro q hq
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h q,
      Matrix.zero_mul, Matrix.zero_mul]

private theorem commutant_reduction {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (k : ℕ) :
    HasComponents (adjacency A C d) k ↔ CommutantResolution A C d k := by
  classical
  constructor
  · rintro ⟨P, hP, hsum, hsep⟩
    have hcross : ∀ s t, s ≠ t → ∀ q, P s * column A C d q * P t = 0 := by
      intro s t hst
      apply (separating_iff (column A C d) (P s) (P t) (hP s).1 (hP t).1).mp
      intro Z
      rw [← adjacency_kraus A C d hH hI]
      exact hsep s t hst Z
    refine ⟨P, hP, hsum, ?_⟩
    intro s q
    have hleft : P s * column A C d q = P s * column A C d q * P s := by
      calc
        _ = P s * column A C d q * (∑ t, P t) := by rw [hsum, Matrix.mul_one]
        _ = ∑ t, P s * column A C d q * P t := Matrix.mul_sum _ _ _
        _ = P s * column A C d q * P s := by
          apply Finset.sum_eq_single s
          · intro t ht hts
            exact hcross s t hts.symm q
          · simp
    have hright : column A C d q * P s = P s * column A C d q * P s := by
      calc
        _ = (∑ t, P t) * column A C d q * P s := by rw [hsum, Matrix.one_mul]
        _ = ∑ t, P t * column A C d q * P s := by rw [Matrix.sum_mul, Matrix.sum_mul]
        _ = P s * column A C d q * P s := by
          apply Finset.sum_eq_single s
          · intro t ht hts
            exact hcross t s hts q
          · simp
    exact hleft.trans hright.symm
  · rintro ⟨P, hP, hsum, hcomm⟩
    have ho := resolution_orthogonal P (fun s => (hP s).1) hsum
    refine ⟨P, hP, hsum, ?_⟩
    intro s t hst Z
    rw [adjacency_kraus A C d hH hI]
    apply (separating_iff (column A C d) (P s) (P t) (hP s).1 (hP t).1).mpr ?_ Z
    intro q
    rw [hcomm s q, Matrix.mul_assoc, ho s t hst, Matrix.mul_zero]

private def representative {n : ℕ} (g : SimpleGraph (Fin n)) (Q : g.ConnectedComponent) : Fin n :=
  Classical.choose Q.exists_rep

private theorem representative_spec {n : ℕ} (g : SimpleGraph (Fin n))
    (Q : g.ConnectedComponent) : g.connectedComponentMk (representative g Q) = Q :=
  Classical.choose_spec Q.exists_rep

private theorem exceptional_other_exists {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    ∃ j, (underlyingGraph A C).connectedComponentMk j = Q.val ∧
      j ≠ representative (underlyingGraph A C) Q.val := by
  obtain ⟨i, j, hij, hpair, hrest⟩ := Q.prop
  have hi : (underlyingGraph A C).connectedComponentMk i = Q.val := by
    change i ∈ Q.val.supp
    rw [hpair]
    simp
  have hj : (underlyingGraph A C).connectedComponentMk j = Q.val := by
    change j ∈ Q.val.supp
    rw [hpair]
    simp
  by_cases hr : representative (underlyingGraph A C) Q.val = i
  · exact ⟨j, hj, by simpa only [hr] using hij.symm⟩
  · exact ⟨i, hi, Ne.symm hr⟩

private def otherVertex {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    Fin n := Classical.choose (exceptional_other_exists A C d Q)

private theorem other_vertex_spec {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    (underlyingGraph A C).connectedComponentMk (otherVertex A C d Q) = Q.val ∧
      otherVertex A C d Q ≠ representative (underlyingGraph A C) Q.val :=
  Classical.choose_spec (exceptional_other_exists A C d Q)

private abbrev CountIndex {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :=
  (underlyingGraph A C).ConnectedComponent ⊕
    {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}

private def selectedVertex {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) : CountIndex A C d → Fin n
  | Sum.inl Q => representative (underlyingGraph A C) Q
  | Sum.inr Q => otherVertex A C d Q

private theorem selected_vertex_injective {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :
    Function.Injective (selectedVertex A C d) := by
  intro a b hab
  have hcomp := congrArg (underlyingGraph A C).connectedComponentMk hab
  cases a with
  | inl Q =>
    cases b with
    | inl R =>
      simp only [selectedVertex, representative_spec] at hcomp
      exact congrArg Sum.inl hcomp
    | inr R =>
      change representative (underlyingGraph A C) Q = otherVertex A C d R at hab
      simp only [selectedVertex, representative_spec, (other_vertex_spec A C d R).1] at hcomp
      exact False.elim ((other_vertex_spec A C d R).2 (hab.symm.trans (congrArg _ hcomp)))
  | inr Q =>
    cases b with
    | inl R =>
      change otherVertex A C d Q = representative (underlyingGraph A C) R at hab
      simp only [selectedVertex, representative_spec, (other_vertex_spec A C d Q).1] at hcomp
      exact False.elim ((other_vertex_spec A C d Q).2 (hab.trans (congrArg _ hcomp.symm)))
    | inr R =>
      simp only [selectedVertex, (other_vertex_spec A C d Q).1,
        (other_vertex_spec A C d R).1] at hcomp
      exact congrArg Sum.inr (Subtype.ext hcomp)

private theorem exceptional_supp_selected {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    Q.val.supp = {representative (underlyingGraph A C) Q.val, otherVertex A C d Q} := by
  obtain ⟨i, j, hij, hpair, hrest⟩ := Q.prop
  have hr : representative (underlyingGraph A C) Q.val ∈ Q.val.supp :=
    representative_spec _ _
  have ho : otherVertex A C d Q ∈ Q.val.supp := (other_vertex_spec A C d Q).1
  have hne := (other_vertex_spec A C d Q).2
  rw [hpair] at hr ho ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr ho
  rcases hr with hr | hr <;> rcases ho with ho | ho <;>
    simp_all [Set.pair_comm]

private theorem selected_card {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :
    Nat.card (CountIndex A C d) = graphComponentCount A C + loopFreeStrangeComponentCount A C d := by
  classical
  simp only [Nat.card_eq_fintype_card, CountIndex, Fintype.card_sum,
    graphComponentCount, loopFreeStrangeComponentCount]

private theorem exceptional_mem_selected {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (i : Fin n)
    (hi : IsLoopFreeStrangeComponent A C d ((underlyingGraph A C).connectedComponentMk i)) :
    i ∈ Set.range (selectedVertex A C d) := by
  let Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q} :=
    ⟨(underlyingGraph A C).connectedComponentMk i, hi⟩
  have hm : i ∈ Q.val.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  rw [exceptional_supp_selected A C d Q] at hm
  rcases hm with hm | hm
  · exact ⟨Sum.inl Q.val, hm.symm⟩
  · exact ⟨Sum.inr Q, hm.symm⟩

private theorem isolated_mem_selected {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (i : Fin n) (hi : (underlyingGraph A C).IsIsolated i) :
    i ∈ Set.range (selectedVertex A C d) := by
  have hr : representative (underlyingGraph A C)
      ((underlyingGraph A C).connectedComponentMk i) = i := by
    by_contra hne
    have hp := SimpleGraph.ConnectedComponent.exact
      (representative_spec (underlyingGraph A C) ((underlyingGraph A C).connectedComponentMk i))
    obtain ⟨v, hv⟩ := hp.symm.nonempty_neighborSet_left (Ne.symm hne)
    exact hi v hv
  exact ⟨Sum.inl ((underlyingGraph A C).connectedComponentMk i), hr⟩

private theorem omitted_vertex_properties {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (i : Fin n) (hi : i ∉ Set.range (selectedVertex A C d)) :
    ¬IsLoopFreeStrangeComponent A C d ((underlyingGraph A C).connectedComponentMk i) ∧
      ∃ u, (underlyingGraph A C).Adj i u := by
  classical
  refine ⟨fun hx => hi (exceptional_mem_selected A C d i hx), ?_⟩
  by_contra h
  exact hi (isolated_mem_selected A C d i (fun u hu => h ⟨u, hu⟩))

private theorem compressed_square {n : ℕ} {W : Type*} [Fintype W] (e : W → Fin n)
    (he : Function.Injective e) (P : Mat n)
    (hzero : ∀ i, i ∉ Set.range e → ∀ j, j ≠ i → P j i = 0) :
    P.submatrix e e * P.submatrix e e = (P * P).submatrix e e := by
  classical
  ext a b
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  calc
    _ = ∑ i ∈ Finset.univ.image e, P (e a) i * P i (e b) :=
      (Finset.sum_image (fun x _ y _ hxy => he hxy)).symm
    _ = ∑ i, P (e a) i * P i (e b) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i hi hnot
      have houtside : i ∉ Set.range e := by
        rintro ⟨w, hw⟩
        exact hnot (Finset.mem_image.mpr ⟨w, Finset.mem_univ w, hw⟩)
      rw [hzero i houtside (e a) (fun h => houtside ⟨a, h⟩), zero_mul]

private theorem commutant_upper_bound_of_local {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hdiag : ∀ P : Mat n,
      (∀ q, P * column A C d q = column A C d q * P) →
      ∀ i j, (underlyingGraph A C).Reachable i j → P i i = P j j)
    (hsupport : ∀ P : Mat n, P.IsHermitian →
      (∀ q, P * column A C d q = column A C d q * P) →
      ∀ i j, i ≠ j → P i j ≠ 0 → (∃ u, (underlyingGraph A C).Adj i u) →
        IsLoopFreeStrangeComponent A C d ((underlyingGraph A C).connectedComponentMk i))
    (k : ℕ) (h : CommutantResolution A C d k) :
    k ≤ graphComponentCount A C + loopFreeStrangeComponentCount A C d := by
  classical
  obtain ⟨P, hP, hsum, hcomm⟩ := h
  let W := CountIndex A C d
  let e : W → Fin n := selectedVertex A C d
  have he : Function.Injective e := selected_vertex_injective A C d
  have hz (s : Fin k) (i : Fin n) (hi : i ∉ Set.range e) (j : Fin n) (hji : j ≠ i) :
      P s j i = 0 := by
    by_contra hne
    have hne' : P s i j ≠ 0 := by
      intro hzero
      apply hne
      rw [← (hP s).1.1.apply j i, hzero, star_zero]
    obtain ⟨hnex, hex⟩ := omitted_vertex_properties A C d i hi
    exact hnex (hsupport (P s) (hP s).1.1 (hcomm s) i j hji.symm hne' hex)
  let Q : Fin k → Matrix W W ℂ := fun s => (P s).submatrix e e
  have hid (s : Fin k) : IsIdempotentElem (Q s) := by
    change (P s).submatrix e e * (P s).submatrix e e = (P s).submatrix e e
    rw [compressed_square e he (P s) (hz s), (hP s).1.2]
  have hne (s : Fin k) : Q s ≠ 0 := by
    intro hzero
    apply (hP s).2
    ext i j
    by_cases hi : i ∈ Set.range e
    · obtain ⟨a, rfl⟩ := hi
      by_cases hj : j ∈ Set.range e
      · obtain ⟨b, rfl⟩ := hj
        exact congrArg (fun M => M a b) hzero
      · exact hz s j hj (e a) (fun h => hj ⟨a, h⟩)
    · by_cases hji : j = i
      · subst j
        let R := (underlyingGraph A C).connectedComponentMk i
        have hr : (underlyingGraph A C).Reachable i
            (representative (underlyingGraph A C) R) :=
          (SimpleGraph.ConnectedComponent.exact (representative_spec _ R)).symm
        exact (hdiag (P s) (hcomm s) i _ hr).trans
          (congrArg (fun M : Matrix W W ℂ => M (Sum.inl R) (Sum.inl R)) hzero)
      · rw [← (hP s).1.1.apply i j, hz s i hi j hji, star_zero]
        rfl
  have hsumQ : (∑ s, Q s) = 1 := by
    calc
      _ = (∑ s, P s).submatrix e e := by
        ext a b
        simp only [Q, Matrix.sum_apply, Matrix.submatrix_apply]
      _ = 1 := by rw [hsum, Matrix.submatrix_one e he]
  let f : Matrix W W ℂ ≃ₐ[ℂ] Module.End ℂ (W → ℂ) := Matrix.toLinAlgEquiv'
  have hbound := D5.S3.Quantum.Matrix.RecordCapacity.card_le_finrank_of_idempotent_sum
    (fun s => f (Q s)) (fun s => (hid s).map f)
    (fun s hs => hne s (f.injective (hs.trans f.map_zero.symm)))
    (by rw [← map_sum, hsumQ, map_one])
  have hbound' : k ≤ Fintype.card W := by
    simpa only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] using hbound
  exact hbound'.trans_eq (by
    simpa only [Nat.card_eq_fintype_card] using selected_card A C d)

private theorem commutant_upper_bound {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hA : ∀ i, A i i = d i) (hC : ∀ i, C i i = d i)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) (k : ℕ)
    (h : CommutantResolution A C d k) :
    k ≤ graphComponentCount A C + loopFreeStrangeComponentCount A C d := by
  exact commutant_upper_bound_of_local A C d
    (fun P hcomm i j hr => commutant_diagonal_reachable A C d hH hI hU P hcomm hr)
    (fun P hP hcomm i j hij hne hex =>
      commutant_offdiag_exceptional A C d hH hI hU P hP hcomm hij hne hex) k h

private theorem commutant_attainment {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hA : ∀ i, A i i = d i) (hC : ∀ i, C i i = d i)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiagonal A).IsHermitian) :
    CommutantResolution A C d
      (graphComponentCount A C + loopFreeStrangeComponentCount A C d) := by
  sorry

theorem result : claim := by
  intro n A C d hA hC hH hI hU
  constructor
  · exact (commutant_reduction A C d hH hI _).mpr
      (commutant_attainment A C d hA hC hH hI hU)
  · intro k hk
    exact commutant_upper_bound A C d hA hC hH hI hU k
      ((commutant_reduction A C d hH hI k).mp hk)

end D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount
