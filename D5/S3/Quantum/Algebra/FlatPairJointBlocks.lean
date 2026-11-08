/- GID: D5/S3/Quantum/Algebra/FlatPairJointBlocks
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FlatPairJointBlocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original-space circle and quaternionic frames for a flat skew pair. -/

module

public import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Tactic

/-! Complete original-vector block specifications and metric orbit relations. -/

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open Module.End

namespace D5.S3.Quantum.Algebra.FlatPairJointBlocks

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- A complete orthonormal frame on the given space, grouped into circle and
quaternionic blocks. Parameters vary independently from block to block. Empty
index sets include the zero space. The quaternionic frame is ordered as
`q, J₁ q, J₂ q, J₁ J₂ q`. -/
def HasFlatPairJointBlocks (A D : F →ₗ[ℝ] F) : Prop :=
  ∃ (c h : ℕ)
    (b : OrthonormalBasis ((Fin c × Fin 2) ⊕ (Fin h × Fin 4)) ℝ F)
    (a d : Fin c → ℝ) (lam t : Fin h → ℝ),
    (∀ i, a i ^ 2 + d i ^ 2 = 1 ∧
      A (b (.inl (i, 0))) = a i • b (.inl (i, 1)) ∧
      A (b (.inl (i, 1))) = -(a i) • b (.inl (i, 0)) ∧
      D (b (.inl (i, 0))) = d i • b (.inl (i, 1)) ∧
      D (b (.inl (i, 1))) = -(d i) • b (.inl (i, 0))) ∧
    (∀ i, 0 < lam i ∧ lam i < 1 ∧ -1 < t i ∧ t i < 1 ∧
      A (b (.inr (i, 0))) = Real.sqrt (lam i) • b (.inr (i, 1)) ∧
      A (b (.inr (i, 1))) = -Real.sqrt (lam i) • b (.inr (i, 0)) ∧
      A (b (.inr (i, 2))) = Real.sqrt (lam i) • b (.inr (i, 3)) ∧
      A (b (.inr (i, 3))) = -Real.sqrt (lam i) • b (.inr (i, 2)) ∧
      D (b (.inr (i, 0))) = Real.sqrt (1 - lam i) •
        (t i • b (.inr (i, 1)) + Real.sqrt (1 - t i ^ 2) • b (.inr (i, 2))) ∧
      D (b (.inr (i, 1))) = Real.sqrt (1 - lam i) •
        (-(t i) • b (.inr (i, 0)) - Real.sqrt (1 - t i ^ 2) • b (.inr (i, 3))) ∧
      D (b (.inr (i, 2))) = Real.sqrt (1 - lam i) •
        (t i • b (.inr (i, 3)) - Real.sqrt (1 - t i ^ 2) • b (.inr (i, 0))) ∧
      D (b (.inr (i, 3))) = Real.sqrt (1 - lam i) •
        (-(t i) • b (.inr (i, 2)) + Real.sqrt (1 - t i ^ 2) • b (.inr (i, 1))))

private theorem flat_pair_joint_fiber_relations (A D : F →ₗ[ℝ] F)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ)
    (hD : ∀ x y, ⟪D x, y⟫_ℝ = -⟪x, D y⟫_ℝ)
    (hflat : -(A * A) - D * D = 1) :
    let P := -(A * A)
    let S := (- (1 / 2 : ℝ)) • (A * D + D * A)
    P.IsSymmetric ∧ S.IsSymmetric ∧ Commute P S ∧
    Nonempty (DirectSum.Decomposition (fun m : Eigenvalues P × Eigenvalues S =>
      eigenspace P m.1 ⊓ eigenspace S m.2)) ∧
    (∀ r s : ℝ, ∀ x ∈ eigenspace P r ⊓ eigenspace S s,
      A x ∈ eigenspace P r ⊓ eigenspace S s ∧
      D x ∈ eigenspace P r ⊓ eigenspace S s) := by
  dsimp only
  let P := -(A * A)
  let S := (- (1 / 2 : ℝ)) • (A * D + D * A)
  have hP : P.IsSymmetric := by
    intro x y
    simp only [P, LinearMap.neg_apply, Module.End.mul_apply, inner_neg_left,
      inner_neg_right, hA, neg_neg]
  have hS : S.IsSymmetric := by
    intro x y
    simp only [S, LinearMap.smul_apply, LinearMap.add_apply, Module.End.mul_apply,
      real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
      hA, hD, inner_neg_right, neg_neg]
    ring
  have hP' : P = 1 + D * D := by
    dsimp [P]
    exact sub_eq_iff_eq_add.mp hflat
  have hPA : Commute P A := by dsimp [P, Commute, SemiconjBy]; noncomm_ring
  have hPD : Commute P D := by rw [hP']; dsimp [Commute, SemiconjBy]; noncomm_ring
  have hAAD : A * A * D = D * (A * A) := by
    have h := hPD.eq
    simpa only [P, neg_mul, mul_neg, neg_inj] using h
  have hDDA : D * D * A = A * (D * D) := by
    have h := hPA.eq
    rw [hP'] at h
    simp only [add_mul, mul_add, one_mul, mul_one] at h
    exact add_left_cancel h
  have hSA : Commute S A := by
    dsimp [S, Commute, SemiconjBy]
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    calc
      (A * D + D * A) * A = A * D * A + D * (A * A) := by noncomm_ring
      _ = A * D * A + A * A * D := by rw [hAAD]
      _ = A * (A * D + D * A) := by noncomm_ring
  have hSD : Commute S D := by
    dsimp [S, Commute, SemiconjBy]
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    calc
      (A * D + D * A) * D = A * (D * D) + D * A * D := by noncomm_ring
      _ = D * D * A + D * A * D := by rw [hDDA]
      _ = D * (A * D + D * A) := by noncomm_ring
  have hPS : Commute P S := by
    dsimp [S]
    exact (hPA.mul_right hPD).add_right (hPD.mul_right hPA) |>.smul_right _
  refine ⟨hP, hS, hPS, ⟨Commute.isSymmetric_directSumDecomposition hP hS hPS⟩, ?_⟩
  intro r s x hx
  simp only [Submodule.mem_inf, mem_eigenspace_iff] at hx ⊢
  have move (T : F →ₗ[ℝ] F) (hPT : Commute P T) (hST : Commute S T) :
      P (T x) = r • T x ∧ S (T x) = s • T x := by
    constructor
    · rw [← Module.End.mul_apply, hPT.eq, Module.End.mul_apply, hx.1, map_smul]
    · rw [← Module.End.mul_apply, hST.eq, Module.End.mul_apply, hx.2, map_smul]
  exact ⟨move A hPA hSA, move D hPD hSD⟩

omit [FiniteDimensional ℝ F] in
private theorem circle_orbit_span_data (J : F →ₗ[ℝ] F)
    (hJ : ∀ x y, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ)
    (hJ2 : ∀ x, J (J x) = -x) (q : F) (hq : ⟪q, q⟫_ℝ = 1) :
    Orthonormal ℝ ![q, J q] ∧
    J q = (![q, J q] : Fin 2 → F) 1 ∧ J (J q) = -q ∧
    ∀ x ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F)),
      J x ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F)) := by
  have hcross : ⟪q, J q⟫_ℝ = 0 := by
    have h := hJ q q
    rw [real_inner_comm q (J q)] at h
    linarith
  have hnorm : ⟪J q, J q⟫_ℝ = 1 := by
    rw [hJ, hJ2, inner_neg_right, neg_neg, hq]
  refine ⟨?_, rfl, hJ2 q, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact hq
    · exact hcross
    · exact (real_inner_comm q (J q)).trans hcross
    · exact hnorm
  · have hqmem : q ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F)) :=
      Submodule.subset_span ⟨0, rfl⟩
    have hJmem : J q ∈ Submodule.span ℝ (Set.range (![q, J q] : Fin 2 → F)) :=
      Submodule.subset_span ⟨1, rfl⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      fin_cases i
      · exact hJmem
      · change J (J q) ∈ _
        rw [hJ2]
        exact Submodule.neg_mem _ hqmem
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

omit [FiniteDimensional ℝ F] in
private theorem quaternion_orbit_span_data (I J : F →ₗ[ℝ] F)
    (hI : ∀ x y, ⟪I x, y⟫_ℝ = -⟪x, I y⟫_ℝ)
    (hJ : ∀ x y, ⟪J x, y⟫_ℝ = -⟪x, J y⟫_ℝ)
    (hI2 : ∀ x, I (I x) = -x) (hJ2 : ∀ x, J (J x) = -x)
    (hIJ : ∀ x, I (J x) = -J (I x)) (q : F) (hq : ⟪q, q⟫_ℝ = 1) :
    let v : Fin 4 → F := ![q, I q, J q, I (J q)]
    Orthonormal ℝ v ∧
    (∀ k, I (v k) = (![v 1, -v 0, v 3, -v 2] : Fin 4 → F) k) ∧
    (∀ k, J (v k) = (![v 2, -v 3, -v 0, v 1] : Fin 4 → F) k) ∧
    (∀ x ∈ Submodule.span ℝ (Set.range v), I x ∈ Submodule.span ℝ (Set.range v)) ∧
    (∀ x ∈ Submodule.span ℝ (Set.range v), J x ∈ Submodule.span ℝ (Set.range v)) := by
  dsimp only
  have hJI (x : F) : J (I x) = -I (J x) := by
    rw [hIJ, neg_neg]
  have isoI (x y : F) : ⟪I x, I y⟫_ℝ = ⟪x, y⟫_ℝ := by
    rw [hI, hI2, inner_neg_right, neg_neg]
  have isoJ (x y : F) : ⟪J x, J y⟫_ℝ = ⟪x, y⟫_ℝ := by
    rw [hJ, hJ2, inner_neg_right, neg_neg]
  have skewIJ (x y : F) : ⟪I (J x), y⟫_ℝ = -⟪x, I (J y)⟫_ℝ := by
    rw [hI, hJ, neg_neg, hJI, inner_neg_right]
  have diag (T : F →ₗ[ℝ] F)
      (hT : ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ) (x : F) :
      ⟪x, T x⟫_ℝ = 0 := by
    have hh := hT x x
    rw [real_inner_comm x (T x)] at hh
    linarith
  have diagIJ : ⟪q, I (J q)⟫_ℝ = 0 := by
    have hh := skewIJ q q
    rw [real_inner_comm q (I (J q))] at hh
    linarith
  have hcross : ⟪I q, J q⟫_ℝ = 0 := by rw [hI, diagIJ, neg_zero]
  have horth : Orthonormal ℝ (![q, I q, J q, I (J q)] : Fin 4 → F) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j
    · exact hq
    · exact diag I hI q
    · exact diag J hJ q
    · exact diagIJ
    · exact (real_inner_comm q (I q)).trans (diag I hI q)
    · exact (isoI q q).trans hq
    · exact hcross
    · exact (isoI q (J q)).trans (diag J hJ q)
    · exact (real_inner_comm q (J q)).trans (diag J hJ q)
    · exact (real_inner_comm (I q) (J q)).trans hcross
    · exact (isoJ q q).trans hq
    · exact diag I hI (J q)
    · exact (real_inner_comm q (I (J q))).trans diagIJ
    · exact (real_inner_comm (I q) (I (J q))).trans
        ((isoI q (J q)).trans (diag J hJ q))
    · exact (real_inner_comm (J q) (I (J q))).trans (diag I hI (J q))
    · exact (isoI (J q) (J q)).trans ((isoJ q q).trans hq)
  have tableI : ∀ k : Fin 4, I ((![q, I q, J q, I (J q)] : Fin 4 → F) k) =
      (![I q, -q, I (J q), -J q] : Fin 4 → F) k := by
    intro k; fin_cases k <;> simp [hI2]
  have tableJ : ∀ k : Fin 4, J ((![q, I q, J q, I (J q)] : Fin 4 → F) k) =
      (![J q, -I (J q), -q, I q] : Fin 4 → F) k := by
    intro k; fin_cases k <;> simp [hJ2, hJI, map_neg, hI2]
  refine ⟨horth, ?_, ?_, ?_, ?_⟩
  · simpa using tableI
  · simpa using tableJ
  all_goals
    have memv (k : Fin 4) :
        (![q, I q, J q, I (J q)] : Fin 4 → F) k ∈
          Submodule.span ℝ (Set.range (![q, I q, J q, I (J q)] : Fin 4 → F)) :=
      Submodule.subset_span ⟨k, rfl⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      fin_cases k <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, hI2, hJ2, hJI, map_neg, neg_neg]
      all_goals first
        | exact memv 0
        | exact memv 1
        | exact memv 2
        | exact memv 3
        | exact Submodule.neg_mem _ (memv 0)
        | exact Submodule.neg_mem _ (memv 1)
        | exact Submodule.neg_mem _ (memv 2)
        | exact Submodule.neg_mem _ (memv 3)
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
    | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

private theorem flat_pair_complement_descent_data (A D : F →ₗ[ℝ] F)
    (hA : ∀ x y, ⟪A x, y⟫_ℝ = -⟪x, A y⟫_ℝ)
    (hD : ∀ x y, ⟪D x, y⟫_ℝ = -⟪x, D y⟫_ℝ)
    (hflat : -(A * A) - D * D = 1)
    (V : Submodule ℝ F) (hV : V ≠ ⊥)
    (hAV : ∀ x ∈ V, A x ∈ V) (hDV : ∀ x ∈ V, D x ∈ V) :
    ∃ (hAc : ∀ x ∈ Vᗮ, A x ∈ Vᗮ) (hDc : ∀ x ∈ Vᗮ, D x ∈ Vᗮ),
      (∀ x y : Vᗮ, ⟪A.restrict hAc x, y⟫_ℝ = -⟪x, A.restrict hAc y⟫_ℝ) ∧
      (∀ x y : Vᗮ, ⟪D.restrict hDc x, y⟫_ℝ = -⟪x, D.restrict hDc y⟫_ℝ) ∧
      -(A.restrict hAc * A.restrict hAc) - D.restrict hDc * D.restrict hDc = 1 ∧
      Module.finrank ℝ Vᗮ < Module.finrank ℝ F := by
  have comp (T : F →ₗ[ℝ] F)
      (hT : ∀ x y, ⟪T x, y⟫_ℝ = -⟪x, T y⟫_ℝ)
      (hTV : ∀ x ∈ V, T x ∈ V) : ∀ x ∈ Vᗮ, T x ∈ Vᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal] at hx ⊢
    intro y hy
    have hz := hx (T y) (hTV y hy)
    have hh := hT y x
    linarith
  let hAc := comp A hA hAV
  let hDc := comp D hD hDV
  refine ⟨hAc, hDc, ?_, ?_, ?_, ?_⟩
  · intro x y; exact hA x y
  · intro x y; exact hD x y
  · ext x
    apply Subtype.ext
    exact DFunLike.congr_fun hflat (x : F)
  · have hpos : 0 < Module.finrank ℝ V := Submodule.finrank_pos.mpr hV
    have hadd := V.finrank_add_finrank_orthogonal
    omega

end D5.S3.Quantum.Algebra.FlatPairJointBlocks
