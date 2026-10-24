/- GID: D5/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/QuantumGraphStrangeComponentCount
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Quantum graph components equal graph components plus loopless isolated strange edges. -/

import D5.S3.Quantum.Matrix.RecordCapacity
import D5.S3.Quantum.Matrix.CfmRadialDerivative
import D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment

/-! # The component count of diagonal-orthogonal quantum graphs -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount

open scoped BigOperators ComplexOrder MatrixOrder
open _root_.Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

open D5.S3.Quantum.Matrix.CfmRadialDerivative (Mat)
open D5.S3.Quantum.QuantumChannels.CoherenceBreakingAmendment (offDiag)

/-- The realigned projector, with the diagonal-coordinate block diagonal. -/
def realignedProjector {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q =>
    if p.1 = p.2 then
      if q = (p.1, p.1) then d p.1 else 0
    else if q = p then A p.1 p.2
    else if q = (p.2, p.1) then C p.1 p.2 else 0

/-- Realignment reads the first and third indices as output indices. -/
def adjacency {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) : Mat n →ₗ[ℂ] Mat n :=
  MatrixMap.of_choi_matrix (realignedProjector A C d)

/-- Nonzero projectors resolving the identity and separating left multiplication. -/
def HasComponents {n : ℕ} (G : Mat n →ₗ[ℂ] Mat n) (k : ℕ) : Prop :=
  ∃ P : Fin k → Mat n,
    (∀ s, IsStarProjection (P s) ∧ P s ≠ 0) ∧
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
    (offDiag A).IsHermitian →
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
    (hU : (offDiag A).IsHermitian) {i j : Fin n} (hij : i ≠ j) :
    A j i = A i j ∧ star (A i j) = A i j ∧ C j i = star (C i j) := by
  have ha : star (A i j) = A i j := by
    simpa [realignedProjector, hij] using hH.apply (i, j) (i, j)
  have ha' : star (A j i) = A j i := by
    simpa [realignedProjector, hij.symm] using hH.apply (j, i) (j, i)
  have hu : star (A j i) = A i j := by
    have h := hU.apply i j
    change star (if j = i then (0 : ℂ) else A j i) =
      (if i = j then 0 else A i j) at h
    simpa only [if_neg hij, if_neg hij.symm] using h
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
    (hU : (offDiag A).IsHermitian) {i j : Fin n} (hij : i ≠ j) :
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
    (hU : (offDiag A).IsHermitian) {i j : Fin n}
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
    (hU : (offDiag A).IsHermitian) (P : Mat n)
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
    (hU : (offDiag A).IsHermitian) (P : Mat n)
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
    (hU : (offDiag A).IsHermitian) (P : Mat n)
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
    (hU : (offDiag A).IsHermitian) (P : Mat n) (hP : P.IsHermitian)
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
    (∀ s, IsStarProjection (P s) ∧ P s ≠ 0) ∧
    (∑ s, P s) = 1 ∧
    ∀ s q, P s * column A C d q = column A C d q * P s
private theorem adjacency_kraus {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (Z : Mat n) :
    adjacency A C d Z = ∑ q, column A C d q * Z * (column A C d q)ᴴ := by
  have hc : MatrixMap.choi_matrix (adjacency A C d) = realignedProjector A C d := by
    ext ⟨i, j⟩ ⟨k, l⟩
    change (∑ a, ∑ b, Matrix.single j l (1 : ℂ) a b *
      realignedProjector A C d (i, a) (k, b)) = realignedProjector A C d (i, j) (k, l)
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
  simpa only [Matrix.self_mul_conjTranspose_eq_zero] using
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun r (_ : r ∈ T) => (Matrix.posSemidef_self_mul_conjTranspose (K r)).nonneg)).mp h
private theorem resolution_orthogonal {n k : ℕ} (P : Fin k → Mat n)
    (hP : ∀ s, IsStarProjection (P s)) (hsum : (∑ s, P s) = 1) :
    ∀ s t, s ≠ t → P s * P t = 0 := by
  classical
  intro s t hst
  have hPs : (P s).IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr (hP s).isSelfAdjoint
  have hgram : (∑ r ∈ Finset.univ.erase s, (P s * P r) * (P s * P r)ᴴ) = 0 := by
    calc
      _ = P s * (∑ r ∈ Finset.univ.erase s, P r) * P s := by
        simp only [Matrix.mul_sum, Matrix.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        have hPr : (P r).IsHermitian :=
          Matrix.isHermitian_iff_isSelfAdjoint.mpr (hP r).isSelfAdjoint
        rw [Matrix.conjTranspose_mul, hPr, hPs]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (P r) (P r), (hP r).isIdempotentElem.eq]
      _ = P s * (1 - P s) * P s := by
        rw [Finset.sum_erase_eq_sub (Finset.mem_univ s), hsum]
      _ = 0 := by rw [mul_sub, mul_one, (hP s).isIdempotentElem.eq, sub_self, zero_mul]
  exact gram_sum_zero (Finset.univ.erase s) (fun r => P s * P r) hgram t
    (Finset.mem_erase.mpr ⟨hst.symm, Finset.mem_univ t⟩)
private theorem separating_iff {n : ℕ} {ι : Type*} [Fintype ι]
    (K : ι → Mat n) (P Q : Mat n)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) :
    (∀ Z, P * (∑ q, K q * (Q * Z) * (K q)ᴴ) = 0) ↔
      ∀ q, P * K q * Q = 0 := by
  constructor
  · intro h q
    have hPH : P.IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hP.isSelfAdjoint
    have hQH : Q.IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hQ.isSelfAdjoint
    have hz : P * (∑ r, K r * Q * (K r)ᴴ) * P = 0 := by
      simpa only [Matrix.mul_one, Matrix.zero_mul] using
        congrArg (fun M => M * P) (h 1)
    have hg : (∑ r, (P * K r * Q) * (P * K r * Q)ᴴ) = 0 := by
      calc
        _ = P * (∑ r, K r * Q * (K r)ᴴ) * P := by
          simp only [Matrix.mul_sum, Matrix.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQH, hPH]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q Q, hQ.isIdempotentElem.eq]
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
private theorem exceptional_other_exists {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    ∃ j, (underlyingGraph A C).connectedComponentMk j = Q.val ∧
      j ≠ Q.val.out := by
  obtain ⟨i, j, hij, hpair, hrest⟩ := Q.prop
  have hi : (underlyingGraph A C).connectedComponentMk i = Q.val := by
    change i ∈ Q.val.supp
    rw [hpair]
    simp
  have hj : (underlyingGraph A C).connectedComponentMk j = Q.val := by
    change j ∈ Q.val.supp
    rw [hpair]
    simp
  by_cases hr : Q.val.out = i
  · exact ⟨j, hj, by simpa only [hr] using hij.symm⟩
  · exact ⟨i, hi, Ne.symm hr⟩
private def otherVertex {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    Fin n := Classical.choose (exceptional_other_exists A C d Q)
private theorem other_vertex_spec {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    (underlyingGraph A C).connectedComponentMk (otherVertex A C d Q) = Q.val ∧
      otherVertex A C d Q ≠ Q.val.out :=
  Classical.choose_spec (exceptional_other_exists A C d Q)
private abbrev CountIndex {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :=
  (underlyingGraph A C).ConnectedComponent ⊕
    {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}
private def selectedVertex {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) : CountIndex A C d → Fin n
  | Sum.inl Q => Q.out
  | Sum.inr Q => otherVertex A C d Q
private theorem selected_vertex_injective {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :
    Function.Injective (selectedVertex A C d) := by
  intro a b hab
  have hcomp := congrArg (underlyingGraph A C).connectedComponentMk hab
  cases a with
  | inl Q =>
    cases b with
    | inl R =>
      exact congrArg Sum.inl
        ((Quot.out_eq Q).symm.trans (hcomp.trans (Quot.out_eq R)))
    | inr R =>
      change Q.out = otherVertex A C d R at hab
      have hQR : Q = R.val :=
        (Quot.out_eq Q).symm.trans (hcomp.trans (other_vertex_spec A C d R).1)
      exact False.elim ((other_vertex_spec A C d R).2 (hab.symm.trans (congrArg _ hQR)))
  | inr Q =>
    cases b with
    | inl R =>
      change otherVertex A C d Q = R.out at hab
      have hRQ : R = Q.val :=
        (Quot.out_eq R).symm.trans (hcomp.symm.trans (other_vertex_spec A C d Q).1)
      exact False.elim ((other_vertex_spec A C d Q).2 (hab.trans (congrArg _ hRQ)))
    | inr R =>
      simp only [selectedVertex, (other_vertex_spec A C d Q).1,
        (other_vertex_spec A C d R).1] at hcomp
      exact congrArg Sum.inr (Subtype.ext hcomp)

private theorem exceptional_supp_selected {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    Q.val.supp = {Q.val.out, otherVertex A C d Q} := by
  obtain ⟨i, j, hij, hpair, hrest⟩ := Q.prop
  have hr : Q.val.out ∈ Q.val.supp :=
    Quot.out_eq _
  have ho : otherVertex A C d Q ∈ Q.val.supp := (other_vertex_spec A C d Q).1
  have hne := (other_vertex_spec A C d Q).2
  rw [hpair] at hr ho ⊢
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr ho
  rcases hr with hr | hr <;> rcases ho with ho | ho <;>
    simp_all [Set.pair_comm]

private theorem selected_card {n : ℕ} (A C : Mat n) (d : Fin n → ℂ) :
    Nat.card (CountIndex A C d) =
      graphComponentCount A C + loopFreeStrangeComponentCount A C d := by
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
  have hr : ((underlyingGraph A C).connectedComponentMk i).out = i := by
    by_contra hne
    have hp := SimpleGraph.ConnectedComponent.exact
      (Quot.out_eq ((underlyingGraph A C).connectedComponentMk i))
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
      have hPh : (P s).IsHermitian :=
        Matrix.isHermitian_iff_isSelfAdjoint.mpr (hP s).1.isSelfAdjoint
      rw [← hPh.apply j i, hzero, star_zero]
    obtain ⟨hnex, hex⟩ := omitted_vertex_properties A C d i hi
    have hPh : (P s).IsHermitian :=
      Matrix.isHermitian_iff_isSelfAdjoint.mpr (hP s).1.isSelfAdjoint
    exact hnex (hsupport (P s) hPh (hcomm s) i j hji.symm hne' hex)
  let Q : Fin k → Matrix W W ℂ := fun s => (P s).submatrix e e
  have hid (s : Fin k) : IsIdempotentElem (Q s) := by
    change (P s).submatrix e e * (P s).submatrix e e = (P s).submatrix e e
    rw [compressed_square e he (P s) (hz s), (hP s).1.isIdempotentElem.eq]
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
            R.out :=
          (SimpleGraph.ConnectedComponent.exact (Quot.out_eq R)).symm
        exact (hdiag (P s) (hcomm s) i _ hr).trans
          (congrArg (fun M : Matrix W W ℂ => M (Sum.inl R) (Sum.inl R)) hzero)
      · have hPh : (P s).IsHermitian :=
          Matrix.isHermitian_iff_isSelfAdjoint.mpr (hP s).1.isSelfAdjoint
        rw [← hPh.apply i j, hz s i hi j hji, star_zero]
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
    (hU : (offDiag A).IsHermitian) (k : ℕ)
    (h : CommutantResolution A C d k) :
    k ≤ graphComponentCount A C + loopFreeStrangeComponentCount A C d := by
  exact commutant_upper_bound_of_local A C d
    (fun P hcomm i j hr => commutant_diagonal_reachable A C d hH hI hU P hcomm hr)
    (fun P hP hcomm i j hij hne hex =>
      commutant_offdiag_exceptional A C d hH hI hU P hP hcomm hij hne hex) k h

attribute [local instance] Classical.propDecidable

private def componentProjection {n : ℕ} (A C : Mat n)
    (Q : (underlyingGraph A C).ConnectedComponent) : Mat n := by
  classical
  exact Matrix.diagonal (fun i => if (underlyingGraph A C).connectedComponentMk i = Q then 1 else 0)

private theorem diagonal_commutes_columns {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (f : Fin n → ℂ)
    (hf : ∀ i j, (underlyingGraph A C).Adj i j → f i = f j) (q : Fin n × Fin n) :
    Matrix.diagonal f * column A C d q = column A C d q * Matrix.diagonal f := by
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : i = j
  · subst j
    exact mul_comm _ _
  by_cases hedge : (underlyingGraph A C).Adj i j
  · rw [hf i j hedge, mul_comm]
  have ha : A i j = 0 := by
    by_contra h
    exact hedge ⟨hij, Or.inl h⟩
  have hc : C i j = 0 := by
    by_contra h
    exact hedge ⟨hij, Or.inr (Or.inr (Or.inl h))⟩
  simp [column, realignedProjector, hij, ha, hc]

private theorem component_projection_projector {n : ℕ} (A C : Mat n)
    (Q : (underlyingGraph A C).ConnectedComponent) :
    IsStarProjection (componentProjection A C Q) := by
  classical
  rw [isStarProjection_iff']
  constructor
  · change componentProjection A C Q * componentProjection A C Q = componentProjection A C Q
    simp only [componentProjection, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  · apply Matrix.isHermitian_iff_isSelfAdjoint.mp
    apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    split_ifs <;> simp

private theorem component_projection_ne_zero {n : ℕ} (A C : Mat n)
    (Q : (underlyingGraph A C).ConnectedComponent) : componentProjection A C Q ≠ 0 := by
  classical
  intro hz
  have h := congrArg (fun M => M Q.out Q.out) hz
  have hQ : (underlyingGraph A C).connectedComponentMk Q.out = Q := Quot.out_eq Q
  simpa [componentProjection, hQ] using h

private theorem component_projection_commutes {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : (underlyingGraph A C).ConnectedComponent) (q : Fin n × Fin n) :
    componentProjection A C Q * column A C d q = column A C d q * componentProjection A C Q := by
  classical
  apply diagonal_commutes_columns
  intro i j hij
  rw [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hij]

private theorem component_projection_sum {n : ℕ} (A C : Mat n) :
    (∑ Q, componentProjection A C Q) = 1 := by
  classical
  ext i j
  by_cases hij : i = j <;> simp [componentProjection, Matrix.sum_apply, Matrix.one_apply, hij]

private theorem cross_component_columns_zero {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : (underlyingGraph A C).ConnectedComponent) {i j : Fin n}
    (hi : i ∈ Q.supp) (hj : j ∉ Q.supp) :
    column A C d (i, j) = 0 ∧ column A C d (j, i) = 0 := by
  have hij : i ≠ j := by rintro rfl; exact hj hi
  have hnadj : ¬(underlyingGraph A C).Adj i j := by
    intro h
    exact hj ((Q.mem_supp_congr_adj h).mp hi)
  have hzero : A i j = 0 ∧ A j i = 0 ∧ C i j = 0 ∧ C j i = 0 := by
    by_contra h
    exact hnadj ⟨hij, by tauto⟩
  simp only [column_off A C d hij, column_off A C d hij.symm,
    hzero.1, hzero.2.1, hzero.2.2.1, hzero.2.2.2, Matrix.single_zero, add_zero, and_self]

private structure ComponentSplit {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : (underlyingGraph A C).ConnectedComponent) where
  plus : Mat n
  minus : Mat n
  plus_projector : IsStarProjection plus
  minus_projector : IsStarProjection minus
  plus_ne_zero : plus ≠ 0
  minus_ne_zero : minus ≠ 0
  complete : plus + minus = componentProjection A C Q
  plus_commutes : ∀ q, plus * column A C d q = column A C d q * plus
  minus_commutes : ∀ q, minus * column A C d q = column A C d q * minus

private theorem phase_square_root (b : ℂ) (hb : b * star b = (1 / 4 : ℂ)) :
    ∃ z : ℂ, z ^ 2 = 2 * b ∧ z * star z = 1 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (2 * b) (n := 2) (by norm_num)
  refine ⟨z, hz, ?_⟩
  have hs : (z * star z) ^ 2 = 1 := by
    calc
      _ = z ^ 2 * star (z ^ 2) := by simp only [star_pow]; ring
      _ = 4 * (b * star b) := by rw [hz]; simp only [star_mul]; norm_num; ring
      _ = 1 := by rw [hb]; norm_num
  have hfactor : (z * star z - 1) * (z * star z + 1) = 0 := by linear_combination hs
  rcases mul_eq_zero.mp hfactor with h | h
  · exact sub_eq_zero.mp h
  · have hneg : z * star z = -1 := eq_neg_of_add_eq_zero_left h
    have hn := mul_star_self_nonneg z
    rw [hneg] at hn
    norm_num at hn

private def pairDiagonal {n : ℕ} (i j : Fin n) : Mat n :=
  Matrix.single i i 1 + Matrix.single j j 1

private def edgeFlip {n : ℕ} (i j : Fin n) (z : ℂ) : Mat n :=
  Matrix.single i j (star z) + Matrix.single j i z

private def edgeProjection {n : ℕ} (i j : Fin n) (z : ℂ) : Mat n :=
  (1 / 2 : ℂ) • (pairDiagonal i j + edgeFlip i j z)

private theorem edge_projection_data {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (z : ℂ) (hz : z * star z = 1) :
    IsStarProjection (edgeProjection i j z) ∧ edgeProjection i j z ≠ 0 ∧
      pairDiagonal i j * edgeProjection i j z = edgeProjection i j z ∧
      edgeProjection i j z * pairDiagonal i j = edgeProjection i j z := by
  have hDD : pairDiagonal i j * pairDiagonal i j = pairDiagonal i j := by
    simp [pairDiagonal, add_mul, mul_add, hij, hij.symm]
  have hDH : pairDiagonal i j * edgeFlip i j z = edgeFlip i j z := by
    simp [pairDiagonal, edgeFlip, add_mul, mul_add, hij, hij.symm]
  have hHD : edgeFlip i j z * pairDiagonal i j = edgeFlip i j z := by
    simp [pairDiagonal, edgeFlip, add_mul, mul_add, hij, hij.symm, add_comm]
  have hHH : edgeFlip i j z * edgeFlip i j z = pairDiagonal i j := by
    have hz' : (starRingEnd ℂ) z * z = 1 := by rw [mul_comm]; exact hz
    have hz'' : z * (starRingEnd ℂ) z = 1 := hz
    simp [pairDiagonal, edgeFlip, add_mul, mul_add, hij, hij.symm, hz', hz'', add_comm]
  have hproj : IsStarProjection (edgeProjection i j z) := by
    rw [isStarProjection_iff']
    constructor
    · change edgeProjection i j z * edgeProjection i j z = edgeProjection i j z
      simp only [edgeProjection, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        add_mul, mul_add, hDD, hDH, hHD, hHH]
      ext a b
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      ring
    · apply Matrix.isHermitian_iff_isSelfAdjoint.mp
      change (edgeProjection i j z)ᴴ = edgeProjection i j z
      simp [edgeProjection, pairDiagonal, edgeFlip, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_add, add_comm, add_left_comm, add_assoc]
  have hne : edgeProjection i j z ≠ 0 := by
    intro hz
    have h := congrArg (fun M => M i i) hz
    norm_num [edgeProjection, pairDiagonal, edgeFlip, Matrix.single, hij, hij.symm] at h
  refine ⟨hproj, hne, ?_, ?_⟩
  · simp only [edgeProjection, Matrix.mul_smul, mul_add, hDD, hDH]
  · simp only [edgeProjection, Matrix.smul_mul, add_mul, hDD, hHD]

private theorem component_projection_pair {n : ℕ} (A C : Mat n)
    (Q : (underlyingGraph A C).ConnectedComponent) {i j : Fin n}
    (hij : i ≠ j) (hpair : Q.supp = {i, j}) :
    componentProjection A C Q = pairDiagonal i j := by
  classical
  unfold componentProjection pairDiagonal
  rw [← Matrix.diagonal_single, ← Matrix.diagonal_single, Matrix.diagonal_add]
  congr 1
  funext a
  have hm : (underlyingGraph A C).connectedComponentMk a = Q ↔ a = i ∨ a = j := by
    change a ∈ Q.supp ↔ _
    rw [hpair]
    rfl
  by_cases hai : a = i <;> by_cases haj : a = j <;>
    simp_all [Pi.single_apply, eq_comm]

private theorem pair_commutes_all {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (Q : (underlyingGraph A C).ConnectedComponent) {i j : Fin n}
    (hij : i ≠ j) (hpair : Q.supp = {i, j}) (hdi : d i = 0) (hdj : d j = 0)
    (P : Mat n) (hDP : pairDiagonal i j * P = P) (hPD : P * pairDiagonal i j = P)
    (hcij : P * column A C d (i, j) = column A C d (i, j) * P)
    (hcji : P * column A C d (j, i) = column A C d (j, i) * P) :
    ∀ q, P * column A C d q = column A C d q * P := by
  intro ⟨a, b⟩
  by_cases ha : a = i ∨ a = j
  · by_cases hb : b = i ∨ b = j
    · rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · simp [column_diag, hdi]
      · exact hcij
      · exact hcji
      · simp [column_diag, hdj]
    · have hma : a ∈ Q.supp := by simpa only [hpair, Set.mem_insert_iff, Set.mem_singleton_iff]
        using ha
      have hmb : b ∉ Q.supp := by simpa only [hpair, Set.mem_insert_iff, Set.mem_singleton_iff]
        using hb
      rw [(cross_component_columns_zero A C d Q hma hmb).1, Matrix.mul_zero, Matrix.zero_mul]
  · by_cases hb : b = i ∨ b = j
    · have hmb : b ∈ Q.supp := by simpa only [hpair, Set.mem_insert_iff, Set.mem_singleton_iff]
        using hb
      have hma : a ∉ Q.supp := by simpa only [hpair, Set.mem_insert_iff, Set.mem_singleton_iff]
        using ha
      rw [(cross_component_columns_zero A C d Q hmb hma).2, Matrix.mul_zero, Matrix.zero_mul]
    · have hai : a ≠ i := fun h => ha (Or.inl h)
      have haj : a ≠ j := fun h => ha (Or.inr h)
      have hbi : b ≠ i := fun h => hb (Or.inl h)
      have hbj : b ≠ j := fun h => hb (Or.inr h)
      have hDK : pairDiagonal i j * column A C d (a, b) = 0 := by
        by_cases hab : a = b
        · subst b
          simp [column_diag, pairDiagonal, add_mul, hai, haj, hai.symm, haj.symm]
        · simp [column_off A C d hab, pairDiagonal, add_mul, mul_add,
            hai, haj, hbi, hbj, hai.symm, haj.symm, hbi.symm, hbj.symm]
      have hKD : column A C d (a, b) * pairDiagonal i j = 0 := by
        have h := component_projection_commutes A C d Q (a, b)
        rw [component_projection_pair A C Q hij hpair, hDK] at h
        exact h.symm
      calc
        _ = (P * pairDiagonal i j) * column A C d (a, b) := by rw [hPD]
        _ = 0 := by rw [Matrix.mul_assoc, hDK, Matrix.mul_zero]
        _ = column A C d (a, b) * P := by
          rw [← hDP, ← Matrix.mul_assoc, hKD, Matrix.zero_mul]

private theorem exceptional_split {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiag A).IsHermitian)
    (Q : {Q : (underlyingGraph A C).ConnectedComponent // IsLoopFreeStrangeComponent A C d Q}) :
    Nonempty (ComponentSplit A C d Q.val) := by
  obtain ⟨i, j, hij, hpair, hadj, hhalf, hdi, hdj⟩ := Q.prop
  obtain ⟨ha, hreal, hcstar⟩ := block_hermitian A C d hH hU hij
  have hcstar' : star (C j i) = C i j := by rw [hcstar, star_star]
  have hprod : C i j * C j i = (1 / 4 : ℂ) := by
    have h := (block_equations A C d hI hij).1
    rw [hhalf] at h
    linear_combination h
  have hb : C j i * star (C j i) = (1 / 4 : ℂ) := by
    rw [hcstar', mul_comm]
    exact hprod
  obtain ⟨z, hzsq, hzunit⟩ := phase_square_root (C j i) hb
  let P := edgeProjection i j z
  obtain ⟨hP, hPne, hDP, hPD⟩ := edge_projection_data hij z hzunit
  have hD := component_projection_pair A C Q.val hij hpair
  have hDH : pairDiagonal i j * edgeFlip i j z = edgeFlip i j z := by
    simp [pairDiagonal, edgeFlip, add_mul, mul_add, hij, hij.symm]
  have hHD : edgeFlip i j z * pairDiagonal i j = edgeFlip i j z := by
    simp [pairDiagonal, edgeFlip, add_mul, mul_add, hij, hij.symm, add_comm]
  have hPH : P * edgeFlip i j z = edgeFlip i j z * P := by
    simp only [P, edgeProjection, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hDH, hHD]
  have hcol : column A C d (i, j) = (z / 2) • edgeFlip i j z := by
    have h₁ : z / 2 * star z = (1 / 2 : ℂ) := by linear_combination (1 / 2 : ℂ) * hzunit
    have h₂ : z / 2 * z = C j i := by linear_combination (1 / 2 : ℂ) * hzsq
    simp only [column_off A C d hij, hhalf, edgeFlip, smul_add,
      Matrix.smul_single, smul_eq_mul, h₁, h₂]
  have hcij : P * column A C d (i, j) = column A C d (i, j) * P := by
    rw [hcol, Matrix.mul_smul, Matrix.smul_mul, hPH]
  have hcoladj : column A C d (j, i) = (column A C d (i, j))ᴴ := by
    rw [column_off A C d hij.symm, column_off A C d hij]
    simp [ha, hhalf, hcstar', Matrix.conjTranspose_add, add_comm]
  have hcji : P * column A C d (j, i) = column A C d (j, i) * P := by
    rw [hcoladj]
    have h := congrArg Matrix.conjTranspose hcij
    have hPHerm : Pᴴ = P :=
      (Matrix.isHermitian_iff_isSelfAdjoint.mpr hP.isSelfAdjoint).eq
    simpa only [Matrix.conjTranspose_mul, hPHerm] using h.symm
  have hcomm := pair_commutes_all A C d Q.val hij hpair hdi hdj P hDP hPD hcij hcji
  let R := componentProjection A C Q.val - P
  have hPR : IsStarProjection R := by
    constructor
    · exact hP.isIdempotentElem.sub (component_projection_projector A C Q.val).isIdempotentElem
        (by rw [hD]; exact hPD) (by rw [hD]; exact hDP)
    · exact (component_projection_projector A C Q.val).isSelfAdjoint.sub hP.isSelfAdjoint
  have hRne : R ≠ 0 := by
    intro hz
    have he := congrArg (fun M => M i i) hz
    norm_num [R, P, hD, edgeProjection, pairDiagonal, edgeFlip, Matrix.single, hij, hij.symm] at he
  refine ⟨{
    plus := P
    minus := R
    plus_projector := hP
    minus_projector := hPR
    plus_ne_zero := hPne
    minus_ne_zero := hRne
    complete := ?_
    plus_commutes := hcomm
    minus_commutes := ?_ }⟩
  · dsimp only [R]
    abel
  · intro q
    dsimp only [R]
    rw [sub_mul, mul_sub, component_projection_commutes A C d Q.val q, hcomm q]

private theorem resolution_from_splits {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (split : ∀ Q : {Q : (underlyingGraph A C).ConnectedComponent //
      IsLoopFreeStrangeComponent A C d Q}, ComponentSplit A C d Q.val) :
    CommutantResolution A C d
      (graphComponentCount A C + loopFreeStrangeComponentCount A C d) := by
  classical
  let F : CountIndex A C d → Mat n
    | Sum.inl Q => if hQ : IsLoopFreeStrangeComponent A C d Q then
        (split ⟨Q, hQ⟩).plus else componentProjection A C Q
    | Sum.inr Q => (split Q).minus
  have hprops (w : CountIndex A C d) :
      (IsStarProjection (F w) ∧ F w ≠ 0) ∧
        ∀ q, F w * column A C d q = column A C d q * F w := by
    cases w with
    | inl Q =>
      by_cases hQ : IsLoopFreeStrangeComponent A C d Q
      · simp only [F, dif_pos hQ]
        exact ⟨⟨(split ⟨Q, hQ⟩).plus_projector, (split ⟨Q, hQ⟩).plus_ne_zero⟩,
          (split ⟨Q, hQ⟩).plus_commutes⟩
      · simp only [F, dif_neg hQ]
        exact ⟨⟨component_projection_projector A C Q, component_projection_ne_zero A C Q⟩,
          component_projection_commutes A C d Q⟩
    | inr Q =>
      exact ⟨⟨(split Q).minus_projector, (split Q).minus_ne_zero⟩, (split Q).minus_commutes⟩
  have hsub : (∑ Q, (split Q).minus) =
      ∑ Q, if hQ : IsLoopFreeStrangeComponent A C d Q then (split ⟨Q, hQ⟩).minus else 0 := by
    apply Fintype.sum_of_injective (fun Q => Q.val) Subtype.val_injective
    · intro Q hn
      have hnot : ¬IsLoopFreeStrangeComponent A C d Q := by
        intro hQ
        exact hn ⟨⟨Q, hQ⟩, rfl⟩
      simp only [dif_neg hnot]
    · intro Q
      simp only [dif_pos Q.prop]
  have hsum : (∑ w, F w) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ Q, F (Sum.inl Q)) + (∑ Q, (split Q).minus) = 1
    rw [hsub, ← Finset.sum_add_distrib]
    calc
      _ = ∑ Q, componentProjection A C Q := by
        apply Finset.sum_congr rfl
        intro Q hQ
        by_cases hx : IsLoopFreeStrangeComponent A C d Q
        · simp only [F, dif_pos hx]
          exact (split ⟨Q, hx⟩).complete
        · simp only [F, dif_neg hx, add_zero]
      _ = 1 := component_projection_sum A C
  have hcard : Fintype.card (CountIndex A C d) =
      graphComponentCount A C + loopFreeStrangeComponentCount A C d := by
    simpa only [Nat.card_eq_fintype_card] using selected_card A C d
  let e : Fin (graphComponentCount A C + loopFreeStrangeComponentCount A C d) ≃
      CountIndex A C d :=
    (finCongr hcard.symm).trans (Fintype.equivFin _).symm
  exact ⟨fun s => F (e s), fun s => (hprops (e s)).1,
    (Equiv.sum_comp e F).trans hsum, fun s q => (hprops (e s)).2 q⟩

private theorem commutant_attainment {n : ℕ} (A C : Mat n) (d : Fin n → ℂ)
    (hA : ∀ i, A i i = d i) (hC : ∀ i, C i i = d i)
    (hH : (realignedProjector A C d).IsHermitian)
    (hI : realignedProjector A C d * realignedProjector A C d = realignedProjector A C d)
    (hU : (offDiag A).IsHermitian) :
    CommutantResolution A C d
      (graphComponentCount A C + loopFreeStrangeComponentCount A C d) := by
  exact resolution_from_splits A C d
    (fun Q => Classical.choice (exceptional_split A C d hH hI hU Q))

theorem result : claim := by
  intro n A C d hA hC hH hI hU
  constructor
  · exact (commutant_reduction A C d hH hI _).mpr
      (commutant_attainment A C d hA hC hH hI hU)
  · intro k hk
    exact commutant_upper_bound A C d hA hC hH hI hU k
      ((commutant_reduction A C d hH hI k).mp hk)

end D5.S3.Quantum.Matrix.QuantumGraphStrangeComponentCount
