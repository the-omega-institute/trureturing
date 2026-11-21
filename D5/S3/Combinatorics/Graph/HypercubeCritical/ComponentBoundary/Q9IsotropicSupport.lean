/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicSupport
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9IsotropicSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Transfer of real supported eigenvectors to prime-field kernels. -/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The modular kernel condition gives a necessary support test in the
signed cube approach to Hong–Wu–Xia Problem 2. -/

public section

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicSupport

open Matrix

/-- Injectivity of a rectangular integer matrix modulo a prime implies real injectivity. -/
theorem real_mulVec_injective_of_zmod {m n : Type*} [Finite m] [Fintype n]
    {p : ℕ} [Fact p.Prime] (M : Matrix m n ℤ)
    (h : Function.Injective (M.map (Int.castRingHom (ZMod p))).mulVec) :
    Function.Injective (M.map (Int.castRingHom ℝ)).mulVec := by
  classical
  let _ := Fintype.ofFinite m
  let castMod := Int.castRingHom (ZMod p)
  let castReal := Int.castRingHom ℝ
  let B := M.map castMod
  obtain ⟨left, hleft⟩ :=
    B.toLin'.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr h)
  have hmatrix : LinearMap.toMatrix' left * B = 1 := by
    simpa only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]
      using congrArg LinearMap.toMatrix' hleft
  let lift : Matrix n m ℤ := fun i j => ((LinearMap.toMatrix' left i j).val : ℤ)
  have hlift : lift.map castMod = LinearMap.toMatrix' left := by
    ext i j
    change (((LinearMap.toMatrix' left i j).val : ℤ) : ZMod p) = _
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hproduct : (lift * M).map castMod = 1 := by
    calc
      _ = lift.map castMod * B := Matrix.ext fun i j =>
        RingHom.map_matrix_mul lift M i j castMod
      _ = 1 := by rw [hlift, hmatrix]
  have hdet : castMod (lift * M).det = 1 := by
    rw [castMod.map_det]
    change ((lift * M).map castMod).det = 1
    rw [hproduct, Matrix.det_one]
  have hdetInt : (lift * M).det ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hdet
    exact zero_ne_one hdet
  have hdetReal : ((lift * M).map castReal).det ≠ 0 := by
    change (castReal.mapMatrix (lift * M)).det ≠ 0
    rw [← castReal.map_det]
    exact (Int.cast_ne_zero.mpr hdetInt : ((lift * M).det : ℝ) ≠ 0)
  have hproductReal : (lift * M).map castReal = lift.map castReal * M.map castReal :=
    Matrix.ext fun i j => RingHom.map_matrix_mul lift M i j castReal
  intro x y hxy
  apply Matrix.mulVec_injective_of_det_ne_zero hdetReal
  rw [hproductReal, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]

private theorem mulVec_restrict_columns {ι R : Type*} [Fintype ι] [Semiring R]
    (K : Finset ι) (T : Matrix ι ι R) (x : ι → R) (hx : ∀ i ∉ K, x i = 0) :
    (T.submatrix id (Subtype.val : K → ι)).mulVec (fun j : K => x j) = T.mulVec x := by
  funext i
  change (∑ j : K, T i j * x j) = ∑ j, T i j * x j
  rw [← Finset.sum_subtype K (fun _ => Iff.rfl) (fun j => T i j * x j)]
  exact Finset.sum_subset (Finset.subset_univ K) fun j _ hj => by rw [hx j hj, mul_zero]

/-- A nonzero real eigenvector supported in K yields a nonzero modular kernel
vector supported in K when the integer eigenvalue vanishes modulo p. -/
theorem exists_zmod_kernel_supported_of_real_eigenvector
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℤ) (K : Finset ι)
    {p : ℕ} [Fact p.Prime] {s : ℤ} (hs : (s : ZMod p) = 0)
    {f : ι → ℝ} (hf : f ≠ 0) (hsupport : ∀ i ∉ K, f i = 0)
    (heigen : (A.map (Int.castRingHom ℝ)).mulVec f = (s : ℝ) • f) :
    ∃ g : ι → ZMod p, g ≠ 0 ∧ (∀ i ∉ K, g i = 0) ∧
      (A.map (Int.castRingHom (ZMod p))).mulVec g = 0 := by
  classical
  let shift := A - s • (1 : Matrix ι ι ℤ)
  let M := shift.submatrix id (Subtype.val : K → ι)
  have castShift {R : Type} [Ring R] :
      shift.map (Int.castRingHom R) = A.map (Int.castRingHom R) -
        (s : R) • (1 : Matrix ι ι R) := by
    let c := Int.castRingHom R
    change (A - s • (1 : Matrix ι ι ℤ)).map c = A.map c - c s • (1 : Matrix ι ι R)
    rw [Matrix.map_sub c c.map_sub, Matrix.map_smul' c _ _ c.map_mul,
      Matrix.map_one c c.map_zero c.map_one]
  let fK : K → ℝ := fun j => f j
  have hfK : fK ≠ 0 := by
    intro hz
    apply hf
    funext i
    by_cases hi : i ∈ K
    · exact congrFun hz ⟨i, hi⟩
    · exact hsupport i hi
  have hreal : (M.map (Int.castRingHom ℝ)).mulVec fK = 0 := by
    change ((shift.map (Int.castRingHom ℝ)).submatrix id (Subtype.val : K → ι)).mulVec
      (fun j : K => f j) = 0
    rw [mulVec_restrict_columns K _ f hsupport, castShift (R := ℝ), Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, heigen, sub_self]
  have hmod : ∃ gK : K → ZMod p, gK ≠ 0 ∧
      (M.map (Int.castRingHom (ZMod p))).mulVec gK = 0 := by
    by_contra! h
    have hinj : Function.Injective (M.map (Int.castRingHom (ZMod p))).mulVec := by
      change Function.Injective ⇑(M.map (Int.castRingHom (ZMod p))).mulVecLin
      exact LinearMap.ker_eq_bot.mp
        (Matrix.ker_mulVecLin_eq_bot_iff.mpr fun v hv => not_not.mp (fun hn => h v hn hv))
    exact hfK (real_mulVec_injective_of_zmod M hinj (hreal.trans (Matrix.mulVec_zero _).symm))
  obtain ⟨gK, hgK, hzero⟩ := hmod
  let g : ι → ZMod p := fun i => if hi : i ∈ K then gK ⟨i, hi⟩ else 0
  have hrestrict : (fun j : K => g j) = gK := by
    funext j
    simp [g, j.property]
  have hgSupport (i : ι) (hi : i ∉ K) : g i = 0 := dite_eq_right hi
  refine ⟨g, ?_, hgSupport, ?_⟩
  · intro hz
    apply hgK
    rw [← hrestrict, hz]
    rfl
  · have hshiftMod : shift.map (Int.castRingHom (ZMod p)) =
        A.map (Int.castRingHom (ZMod p)) := by
      rw [castShift (R := ZMod p), hs, zero_smul, sub_zero]
    rw [← hshiftMod, ← mulVec_restrict_columns K _ g hgSupport, hrestrict]
    exact hzero

/-- If the integer matrix has no entries within either parity class, one parity alone
supports a nonzero modular kernel vector in K. -/
theorem exists_zmod_kernel_supported_on_one_parity_of_real_eigenvector
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℤ) (K : Finset ι) (parity : ι → Bool)
    (hA : ∀ i j, parity i = parity j → A i j = 0)
    {p : ℕ} [Fact p.Prime] {s : ℤ} (hs : (s : ZMod p) = 0)
    {f : ι → ℝ} (hf : f ≠ 0) (hsupport : ∀ i ∉ K, f i = 0)
    (heigen : (A.map (Int.castRingHom ℝ)).mulVec f = (s : ℝ) • f) :
    ∃ (b : Bool) (g : ι → ZMod p), g ≠ 0 ∧ (∀ i ∉ K, g i = 0) ∧
      (∀ i, parity i ≠ b → g i = 0) ∧ (A.map (Int.castRingHom (ZMod p))).mulVec g = 0 := by
  classical
  obtain ⟨g, hg, hgK, hkernel⟩ :=
    exists_zmod_kernel_supported_of_real_eigenvector A K hs hf hsupport heigen
  have hcuts (b : Bool) :
      (A.map (Int.castRingHom (ZMod p))).mulVec (fun j => if parity j = b then g j else 0) =
        0 := by
    funext i
    change (∑ j, (A i j : ZMod p) * (if parity j = b then g j else 0)) = 0
    by_cases hi : parity i = b
    · apply Finset.sum_eq_zero
      intro j _
      by_cases hj : parity j = b
      · simp [hj, hA i j (hi.trans hj.symm)]
      · simp [hj]
    · calc
        _ = ∑ j, (A i j : ZMod p) * g j := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hj : parity j = b
          · rw [ite_eq_left hj]
          · have hij : parity i = parity j := by
              cases h₁ : parity i <;> cases h₂ : parity j <;> cases b <;> simp_all
            simp [hA i j hij]
        _ = 0 := congrFun hkernel i
  have hex : ∃ j, g j ≠ 0 := by
    by_contra! h
    exact hg (funext h)
  obtain ⟨j, hj⟩ := hex
  refine ⟨parity j, fun i => if parity i = parity j then g i else 0, ?_, ?_, ?_, hcuts _⟩
  · intro hz
    apply hj
    simpa using congrFun hz j
  · intro i hi
    simp [hgK i hi]
  · intro i hi
    simp [hi]

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicSupport
