/- GID: D5/S3/Quantum/Foundation/QutritSchurPlane
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/QutritSchurPlane
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original pure lifts fill the qutrit quotient four-plane. -/

import D5.S3.Quantum.Foundation.QutritPureLift
import D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.HermitianMat.Unitary

/-! The full affine section of an actual qutrit in the quotient by another actual qutrit. -/

noncomputable section
open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.QutritSchurPlane

open CircuitBalancedConfirmation WholePairBallConfirmation HitSectionGeneration SectionROGFrame
open D5.S3.Quantum.Entanglement.BipartiteSectorDecomposition (hermitian_space_finrank)

private abbrev Index := Unit ⊕ Fin 2

private def pivot : Index := Sum.inl ()

private def block (d : ℝ) (w : Fin 2 → ℂ) (A : HermitianMat (Fin 2) ℂ) :
    HermitianMat Index ℂ :=
  ⟨Matrix.fromBlocks (fun _ _ => (d : ℂ))
      (fun _ j => star (w j)) (fun i _ => w i) A.mat,
    Matrix.IsHermitian.fromBlocks
      (by
        ext i j
        change star (d : ℂ) = d
        simp)
      (by
        ext i j
        change star (star (w i)) = w i
        exact star_star _) A.H⟩

private theorem block_mat (d : ℝ) (w : Fin 2 → ℂ) (A : HermitianMat (Fin 2) ℂ) :
    (block d w A).mat = Matrix.fromBlocks (fun _ _ => (d : ℂ))
      (fun _ j => star (w j)) (fun i _ => w i) A.mat := rfl

private def core : HermitianMat (Fin 2) ℂ →ₗ[ℝ] HermitianMat Index ℂ where
  toFun := block 0 0
  map_add' A B := HermitianMat.ext (by
    change (block 0 0 (A + B)).mat = (block 0 0 A + block 0 0 B).mat
    rw [HermitianMat.mat_add, block_mat, block_mat, block_mat]
    exact Matrix.ext fun i j => by cases i <;> cases j <;> simp [Matrix.fromBlocks])
  map_smul' r A := HermitianMat.ext (by
    change (block 0 0 (r • A)).mat = (r • block 0 0 A).mat
    rw [HermitianMat.mat_smul, block_mat, block_mat]
    exact Matrix.ext fun i j => by cases i <;> cases j <;> simp [Matrix.fromBlocks])

private def cross : (Fin 2 → ℂ) →ₗ[ℝ] HermitianMat Index ℂ where
  toFun w := block 0 w 0
  map_add' w z := HermitianMat.ext (by
    change (block 0 (w + z) 0).mat = (block 0 w 0 + block 0 z 0).mat
    rw [HermitianMat.mat_add, block_mat, block_mat, block_mat]
    exact Matrix.ext fun i j => by cases i <;> cases j <;> simp [Matrix.fromBlocks])
  map_smul' r w := HermitianMat.ext (by
    change (block 0 (r • w) 0).mat = (r • block 0 w 0).mat
    rw [HermitianMat.mat_smul, block_mat, block_mat]
    exact Matrix.ext fun i j => by
      cases i <;> cases j <;> simp [Matrix.fromBlocks, Algebra.smul_def])

private theorem cross_apply (w : Fin 2 → ℂ) : cross w = block 0 w 0 := rfl

private theorem core_apply (A : HermitianMat (Fin 2) ℂ) : core A = block 0 0 A := rfl

private def corner (X : HermitianMat Index ℂ) : ℝ := (X.mat pivot pivot).re

private def column (X : HermitianMat Index ℂ) (i : Fin 2) : ℂ := X.mat (Sum.inr i) pivot

private def lower (X : HermitianMat Index ℂ) : HermitianMat (Fin 2) ℂ :=
  ⟨X.mat.submatrix Sum.inr Sum.inr, X.H.submatrix Sum.inr⟩

private theorem diag_real {ι : Type*} (X : HermitianMat ι ℂ) (i : ι) :
    ((X.mat i i).re : ℂ) = X.mat i i := by
  have h := congrFun (congrFun X.H i) i
  change star (X.mat i i) = X.mat i i at h
  have hi := congrArg Complex.im h
  apply Complex.ext <;> simp_all

private theorem block_decomp (X : HermitianMat Index ℂ) :
    X = block (corner X) 0 0 + cross (column X) + core (lower X) := by
  apply HermitianMat.ext
  rw [HermitianMat.mat_add, HermitianMat.mat_add, cross_apply, core_apply]
  apply Matrix.ext
  rintro (i | i) (j | j)
  · cases i
    cases j
    simpa [block, corner, pivot, Matrix.fromBlocks] using (diag_real X pivot).symm
  · cases i
    have h := congrFun (congrFun X.H (Sum.inl ())) (Sum.inr j)
    simpa [block, column, pivot, Matrix.fromBlocks, Matrix.conjTranspose_apply] using h.symm
  · cases j
    simp [block, column, pivot, Matrix.fromBlocks]
  · change X.mat (Sum.inr i) (Sum.inr j) = 0 + 0 + X.mat (Sum.inr i) (Sum.inr j)
    simp

private theorem core_injective : Function.Injective core := by
  intro A B h
  exact HermitianMat.ext (by ext i j; exact congrArg (fun X : HermitianMat Index ℂ =>
    X.mat (Sum.inr i) (Sum.inr j)) h)

private theorem core_eq_of_zero_col (X : HermitianMat Index ℂ)
    (h : ∀ i, X.mat i pivot = 0) :
    X = core (lower X) := by
  have hd : corner X = 0 := by dsimp [corner]; rw [h]; rfl
  have hw : column X = 0 := by funext i; exact h _
  calc
    X = _ := block_decomp X
    _ = core (lower X) := by
      rw [hd, hw, map_zero, add_zero]
      rw [show block 0 0 (0 : HermitianMat (Fin 2) ℂ) = 0 from map_zero core, zero_add]

/-- Reindex complex Hermitian matrices by an equivalence of their index sets. -/
def reindexEquiv {ι κ : Type*} (σ : ι ≃ κ) :
    HermitianMat ι ℂ ≃ₗ[ℝ] HermitianMat κ ℂ where
  toFun X := X.reindex σ
  invFun X := X.reindex σ.symm
  left_inv X := by simp [HermitianMat.reindex_reindex]
  right_inv X := by simp [HermitianMat.reindex_reindex]
  map_add' _ _ := (HermitianMat.reindex_add ..).symm
  map_smul' _ _ := (HermitianMat.reindex_smul ..).symm

/-- Unitary congruence on complex Hermitian matrices, with inverse congruence by the adjoint. -/
def unitaryEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) : HermitianMat ι ℂ ≃ₗ[ℝ] HermitianMat ι ℂ :=
  { HermitianMat.conjLinear ℝ U.val with
    invFun := HermitianMat.conj (star U).val
    left_inv := fun X => by
      change (X.conj U.val).conj (star U).val = X
      rw [HermitianMat.conj_conj]
      rw [show (star U).val * U.val = 1 from Unitary.coe_star_mul_self U, HermitianMat.conj_one]
    right_inv := fun X => by
      change (X.conj (star U).val).conj U.val = X
      rw [HermitianMat.conj_conj]
      rw [show U.val * (star U).val = 1 from Unitary.coe_mul_star_self U, HermitianMat.conj_one] }

/-- Pairing with a real diagonal Hermitian matrix reads a weighted sum of the diagonal entries. -/
theorem diagonal_read {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (X : HermitianMat ι ℂ) :
    ⟪HermitianMat.diagonal ℂ d, X⟫_ℝ = ∑ i, d i * (X.mat i i).re := by
  rw [HermitianMat.inner_eq_re_trace]
  simp [Matrix.trace, Matrix.diagonal_mul]

private theorem diagonal_pos_col (d : Index → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hdp : 0 < d pivot) (X : HermitianMat Index ℂ) (hX : 0 ≤ X)
    (hz : ⟪HermitianMat.diagonal ℂ d, X⟫_ℝ = 0) :
    ∀ i, X.mat i pivot = 0 := by
  have hpsd := HermitianMat.zero_le_iff.mp hX
  have hdiag (i : Index) : 0 ≤ (X.mat i i).re :=
    (Complex.nonneg_iff.mp (hpsd.diag_nonneg (i := i))).1
  have hs : d pivot * (X.mat pivot pivot).re ≤
      ∑ i, d i * (X.mat i i).re :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hd i) (hdiag i)) (Finset.mem_univ _)
  rw [← diagonal_read, hz] at hs
  have hzero : X.mat pivot pivot = 0 := by
    rw [← diag_real X pivot]
    exact_mod_cast (show (X.mat pivot pivot).re = 0 by
      have := hdiag pivot
      nlinarith)
  have hq : star (Pi.single pivot (1 : ℂ)) ⬝ᵥ
      (X.mat *ᵥ Pi.single pivot 1) = 0 := by
    simpa [Matrix.mulVec_single] using hzero
  have hv := hpsd.dotProduct_mulVec_zero_iff.mp hq
  intro i
  simpa [Matrix.mulVec_single] using congrFun hv i

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u g : V →ₗ[ℝ] ℝ}

private abbrev spanFace (F : C.Face) := Submodule.span ℝ (F : Set V)

omit [FiniteDimensional ℝ V] in
/-- A unit rank-one projector in a trace-preserving Hermitian cone chart onto a face
maps to an extreme point of the ambient normalized cone base. -/
theorem unit_rankOne_original {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : C.Face) (I : HermitianMat ι ℂ →ₗ[ℝ] V)
    (hI : Function.Injective I) (hJ : ∀ x ∈ J, x ∈ LinearMap.range I)
    (hcone : ∀ X, I X ∈ J ↔ 0 ≤ X)
    (htrace : ∀ X, u (I X) = X.trace)
    (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    I (rankOne v) ∈ pure C u := by
  let K := SectionROGFrame.base (⊤ : Submodule ℝ (HermitianMat ι ℂ))
  have hK : K = CircuitBalancedConfirmation.base HermitianExclusionKernel.cone
      HermitianExclusionKernel.unit := by
    ext X
    simp [K, SectionROGFrame.base, CircuitBalancedConfirmation.base,
      HermitianExclusionKernel.cone, HermitianExclusionKernel.unit]
  have hKconv : Convex ℝ K := hK.symm ▸ CircuitBalancedConfirmation.base_convex _ _
  have hmem : rankOne v ∈ K.extremePoints ℝ := by
    change rankOne v ∈ (SectionROGFrame.base ⊤).extremePoints ℝ
    rw [whole_pure_carrier _ HermitianExclusionBall.whole_rog]
    exact ⟨v, hv, rfl, Submodule.mem_top⟩
  have h := affine_extreme_image K hKconv I.toAffineMap
    (fun _ _ _ _ he => hI he) hmem
  change I (rankOne v) ∈ (I '' K).extremePoints ℝ at h
  have himage : I '' K = CircuitBalancedConfirmation.base J.toPointedCone u := by
    ext x
    constructor
    · rintro ⟨X, hX, rfl⟩
      exact ⟨(hcone X).mpr hX.2.1, (htrace X).trans hX.2.2⟩
    · intro hx
      obtain ⟨X, rfl⟩ := hJ x hx.1
      exact ⟨X, ⟨Submodule.mem_top, (hcone X).mp hx.1,
        (htrace X).symm.trans hx.2⟩, rfl⟩
  rw [himage] at h
  exact (face_base_extreme J).extremePoints_subset_extremePoints h

private theorem hermitian_finrank (n : ℕ) :
    Module.finrank ℝ (HermitianMat (Fin n) ℂ) = n ^ 2 := by
  let e : HermitianMat (Fin n) ℂ ≃ₗ[ℝ]
      D5.S3.Quantum.Measurement.BasisMeasurementProjection.HermitianSpace n :=
    { toFun := fun A => ⟨A.mat, A.property⟩
      invFun := fun A => ⟨A.val, A.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finrank_eq.trans (hermitian_space_finrank n)

/-- The actual binary intersection fills the entire lower Hermitian block.
The dimension comparison takes place before passing to the quotient. -/
private theorem adapted_coordinates
    (F J B : C.Face)
    (hg : ∀ x ∈ C, 0 ≤ g x)
    (hg0 : ∀ x ∈ C, g x = 0 ↔ x ∈ F)
    (hB : (B : Set V) = (F : Set V) ∩ (J : Set V))
    (hBdim : Module.finrank ℝ (spanFace B) = 4)
    (e : spanFace J ≃ₗ[ℝ] HermitianMat (Fin 3) ℂ)
    (hcone : ∀ z : spanFace J, (z : V) ∈ J ↔ 0 ≤ e z)
    (htrace : ∀ z : spanFace J, (e z).trace = u z) :
    ∃ (I : HermitianMat Index ℂ →ₗ[ℝ] V) (c : ℝ),
      Function.Injective I ∧ LinearMap.range I = spanFace J ∧
      (∀ X, I X ∈ J ↔ 0 ≤ X) ∧ (∀ X, u (I X) = X.trace) ∧
      0 < c ∧ (∀ X, g (I X) = c * corner X) ∧
      LinearMap.range (I.comp core) = spanFace B := by
  classical
  let I₀ : HermitianMat (Fin 3) ℂ →ₗ[ℝ] V :=
    (spanFace J).subtype.comp e.symm.toLinearMap
  have hI₀ (X) : I₀ X ∈ J ↔ 0 ≤ X := by simpa [I₀] using hcone (e.symm X)
  obtain ⟨G, hG, hrep⟩ := HermitianExclusionKernel.positive_representative (g.comp I₀)
    (fun X hX => hg _ (J.isFaceOf.le ((hI₀ X).mpr hX)))
  have hGne : G ≠ 0 := by
    intro h
    have hle : spanFace J ≤ spanFace B := by
      apply Submodule.span_le.mpr
      intro x hx
      have hxg : g x = 0 := by
        simpa [I₀, h] using hrep (e ⟨x, Submodule.subset_span hx⟩)
      exact Submodule.subset_span (by
        rw [hB]
        exact ⟨(hg0 x (J.isFaceOf.le hx)).mp hxg, hx⟩)
    have hr := Submodule.finrank_mono hle
    rw [e.finrank_eq, hermitian_finrank, hBdim] at hr
    norm_num at hr
  have heigen (i) : 0 ≤ G.H.eigenvalues i :=
    (G.H.posSemidef_iff_eigenvalues_nonneg.mp (HermitianMat.zero_le_iff.mp hG)) i
  obtain ⟨i, hi⟩ : ∃ i, 0 < G.H.eigenvalues i := by
    by_contra! h
    apply hGne
    rw [G.eq_conj_diagonal]
    have hd : G.H.eigenvalues = 0 := funext fun j => le_antisymm (h j) (heigen j)
    simp [hd]
  let σ₀ : Fin 3 ≃ Index := Fintype.equivOfCardEq (by decide)
  let σ := σ₀.trans (Equiv.swap (σ₀ i) pivot)
  have hσ : σ i = pivot := by simp [σ]
  let d : Index → ℝ := G.H.eigenvalues ∘ σ.symm
  have hdp : 0 < d pivot := by simpa [d, ← hσ] using hi
  let U := G.H.eigenvectorUnitary
  let E := (reindexEquiv σ.symm).trans (unitaryEquiv U)
  let I := I₀.comp E.toLinearMap
  have hI : Function.Injective I :=
    Subtype.val_injective.comp (e.symm.injective.comp E.injective)
  have hR : LinearMap.range I = spanFace J := by
    ext x
    constructor
    · rintro ⟨X, rfl⟩
      exact (e.symm (E X)).property
    · intro hx
      exact ⟨E.symm (e ⟨x, hx⟩), by simp [I, I₀]⟩
  have hEc (X : HermitianMat Index ℂ) : E X = (X.reindex σ.symm).conj U.val := rfl
  have hIC (X) : I X ∈ J ↔ 0 ≤ X := by
    change I₀ (E X) ∈ J ↔ 0 ≤ X
    rw [hI₀, hEc, ← (HermitianMat.conj U.val).map_zero,
      HermitianMat.le_conj_unitary, HermitianMat.zero_le_iff,
      HermitianMat.zero_le_iff, HermitianMat.mat_reindex]
    exact Matrix.posSemidef_submatrix_equiv σ
  have hIT (X) : u (I X) = X.trace := by
    change u (e.symm (E X) : spanFace J) = X.trace
    rw [← htrace, e.apply_symm_apply, hEc, HermitianMat.trace_conj_unitary,
      HermitianMat.trace_reindex]
  have hread (X : HermitianMat Index ℂ) :
      g (I X) = ⟪HermitianMat.diagonal ℂ d, X⟫_ℝ := by
    change (g.comp I₀) (E X) = _
    rw [hrep, hEc, G.eq_conj_diagonal, HermitianMat.inner_conj_unitary,
      diagonal_read, diagonal_read]
    apply Fintype.sum_equiv σ
    intro j
    change G.H.eigenvalues j * (X.mat (σ j) (σ j)).re =
      G.H.eigenvalues (σ.symm (σ j)) * (X.mat (σ j) (σ j)).re
    rw [σ.symm_apply_apply]
  have hsubset : spanFace B ≤ LinearMap.range (I.comp core) := by
    apply Submodule.span_le.mpr
    intro x hx
    rw [hB] at hx
    have hxJ : x ∈ LinearMap.range I := by rw [hR]; exact Submodule.subset_span hx.2
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp hxJ
    have hzero := (hg0 _ (J.isFaceOf.le hx.2)).mpr hx.1
    have hz := diagonal_pos_col d (fun j => heigen _) hdp X
      ((hIC X).mp hx.2) ((hread X).symm.trans hzero)
    exact ⟨lower X, congrArg I (core_eq_of_zero_col X hz).symm⟩
  have hcore : LinearMap.range (I.comp core) = spanFace B := by
    symm
    apply Submodule.eq_of_le_of_finrank_le hsubset
    have hinj : Function.Injective (I.comp core) := hI.comp core_injective
    rw [LinearMap.finrank_range_of_inj hinj, hermitian_finrank, hBdim]
    norm_num
  have hcore_g (A) : g (I (core A)) = 0 := by
    have hle : spanFace B ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      intro x hx
      rw [hB] at hx
      exact (hg0 x (J.isFaceOf.le hx.2)).mpr hx.1
    apply hle
    rw [← hcore]
    exact ⟨A, rfl⟩
  refine ⟨I, d pivot, hI, hR, hIC, hIT, hdp, fun X => ?_, hcore⟩
  have hcross (w) : g (I (cross w)) = 0 := by
    rw [hread, diagonal_read]
    apply Finset.sum_eq_zero
    intro j _
    cases j <;> simp [cross_apply, block, Matrix.fromBlocks]
  have hcorner (a) : g (I (block a 0 0)) = d pivot * a := by
    rw [hread, diagonal_read, Fintype.sum_sum_type]
    simp [block, pivot, Matrix.fromBlocks]
  conv_lhs => rw [block_decomp X]
  simp only [map_add, hcore_g, hcross, hcorner, add_zero]

/-- At positive pivot t the rank-one outer product realizes every off-column w. -/
private theorem schur_completion (t : ℝ) (ht : 0 < t) (w : Fin 2 → ℂ) :
    ∃ v : EuclideanSpace ℂ Index, v ≠ 0 ∧
      corner (rankOne v) = t ∧ column (rankOne v) = w := by
  let s : ℂ := (Real.sqrt t : ℝ)
  let f : Index → ℂ := Sum.elim (fun _ => s) (fun i => w i / s)
  let v := WithLp.toLp 2 f
  have hs : s ≠ 0 := by dsimp [s]; exact_mod_cast (Real.sqrt_pos.2 ht).ne'
  have hstar : star s = s := by simp [s]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro h
    apply hs
    exact congrArg (fun z : EuclideanSpace ℂ Index => (z : Index → ℂ) pivot) h
  · change (s * star s).re = t
    rw [hstar]
    simp [s, ← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
  · funext i
    change (w i / s) * star s = w i
    rw [hstar, div_mul_cancel₀ _ hs]

/-- The original support-one pure rays of J project onto the whole support-one
slice of its homogeneous quotient image. The shared binary dimension also
forces the exact homogeneous intersection, through unique original lifts. -/
theorem original_qutrit_quotient_affine_plane
    (F J B : C.Face)
    (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : ∀ x ∈ C, 0 ≤ g x)
    (hg0 : ∀ x ∈ C, g x = 0 ↔ x ∈ F)
    (hballs : wholePairBalls C u)
    (hB : (B : Set V) = (F : Set V) ∩ (J : Set V))
    (hBdim : Module.finrank ℝ (Submodule.span ℝ (B : Set V)) = 4)
    (eF : Submodule.span ℝ (F : Set V) ≃ₗ[ℝ] HermitianMat (Fin 3) ℂ)
    (hconeF : ∀ z : Submodule.span ℝ (F : Set V), (z : V) ∈ F ↔ 0 ≤ eF z)
    (htraceF : ∀ z : Submodule.span ℝ (F : Set V), (eF z).trace = u z)
    (eJ : Submodule.span ℝ (J : Set V) ≃ₗ[ℝ] HermitianMat (Fin 3) ℂ)
    (hconeJ : ∀ z : Submodule.span ℝ (J : Set V), (z : V) ∈ J ↔ 0 ≤ eJ z)
    (htraceJ : ∀ z : Submodule.span ℝ (J : Set V), (eJ z).trace = u z) :
    let S := Submodule.span ℝ (F : Set V)
    let T := Submodule.span ℝ (J : Set V)
    let π := S.mkQ
    let R := {r : V | ∃ (p : pure C u) (a : ℝ),
      (p : V) ∈ J ∧ (p : V) ∉ F ∧ 0 < a ∧ r = a • (p : V) ∧ g r = 1}
    S ⊓ T = Submodule.span ℝ (B : Set V) ∧
      ∃ (gQ : (V ⧸ S) →ₗ[ℝ] ℝ) (q₀ : V ⧸ S)
        (L : (Fin 2 → ℂ) →ₗ[ℝ] (V ⧸ S)),
        gQ.comp π = g ∧ Function.Injective L ∧
        Module.finrank ℝ (LinearMap.range L) = 4 ∧
        π '' R = {q | q ∈ T.map π ∧ gQ q = 1} ∧
        {q | q ∈ T.map π ∧ gQ q = 1} =
          (AffineSubspace.mk' q₀ (LinearMap.range L) : Set (V ⧸ S)) := by
  dsimp only
  let S := spanFace F
  let T := spanFace J
  let π := S.mkQ
  let R := {r : V | ∃ (p : pure C u) (a : ℝ),
      (p : V) ∈ J ∧ (p : V) ∉ F ∧ 0 < a ∧ r = a • (p : V) ∧ g r = 1}
  have hgF (x) (hx : x ∈ F) : g x = 0 := (hg0 x (F.isFaceOf.le hx)).mpr hx
  have hS : S ≤ LinearMap.ker g := Submodule.span_le.mpr hgF
  have hBF : spanFace B ≤ S := Submodule.span_mono (by rw [hB]; exact Set.inter_subset_left)
  have hBJ : spanFace B ≤ T := Submodule.span_mono (by rw [hB]; exact Set.inter_subset_right)
  obtain ⟨I, c, hI, hR, hIC, hIT, hc, hread, hcore⟩ :=
    adapted_coordinates F J B hg hg0 hB hBdim eJ hconeJ htraceJ
  let t := c⁻¹
  have ht : 0 < t := inv_pos.mpr hc
  have hct : c * t = 1 := mul_inv_cancel₀ hc.ne'
  let q₀ := π (I (block t 0 0))
  let L := π.comp (I.comp cross)
  let gQ := S.liftQ g hS
  have hgQ (x : V) : gQ (π x) = g x := rfl
  have hkill (A) : π (I (core A)) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero S).mpr
    apply hBF
    rw [← hcore]
    exact ⟨A, rfl⟩
  have hsection (X : HermitianMat Index ℂ) (hX : corner X = t) :
      π (I X) = q₀ + L (column X) := by
    conv_lhs => rw [block_decomp X, hX]
    simp [q₀, L, map_add, hkill]
  have hcompletion (w : Fin 2 → ℂ) :
      ∃ X, corner X = t ∧ column X = w ∧ I X ∈ R := by
    obtain ⟨v, hv, hvt, hvw⟩ := schur_completion t ht w
    let m := ‖v‖ ^ 2
    have hm : 0 < m := sq_pos_of_pos (norm_pos_iff.mpr hv)
    let n := ‖v‖⁻¹ • v
    have hn : ‖n‖ = 1 := by simp [n, norm_smul, norm_ne_zero_iff.mpr hv]
    have hscale : m • rankOne n = rankOne v := by
      change m • rankOne (WithLp.ofLp (‖v‖⁻¹ • v)) = rankOne v
      rw [WithLp.ofLp_smul, rankOne_real_smul, smul_smul]
      have hscalar : m * (‖v‖⁻¹ * ‖v‖⁻¹) = 1 := by
        dsimp [m]
        field_simp [norm_ne_zero_iff.mpr hv]
      rw [hscalar, one_smul]
    have Hp := unit_rankOne_original J I hI
      (fun x hx => by rw [hR]; exact Submodule.subset_span hx) hIC hIT n hn
    let p : pure C u := ⟨I (rankOne n), Hp⟩
    have hpJ : (p : V) ∈ J := (hIC _).mpr (rankOne_nonneg _)
    have hpr : I (rankOne v) = m • (p : V) := by
      change I (rankOne v) = m • I (rankOne n)
      rw [← map_smul, hscale]
    have hgp : g (I (rankOne v)) = 1 := by rw [hread, hvt, hct]
    have hpF : (p : V) ∉ F := by
      intro hp
      rw [hpr, map_smul, hgF _ hp, smul_zero] at hgp
      norm_num at hgp
    exact ⟨rankOne v, hvt, hvw, p, m, hpJ, hpF, hm, hpr, hgp⟩
  have hlu := QutritPureLift.unique_original_pure_lift F hu hg hgF hballs eF hconeF htraceF
  have hL : Function.Injective L := by
    intro w z he
    obtain ⟨X, htX, hwX, hXR⟩ := hcompletion w
    obtain ⟨Y, htY, hwY, hYR⟩ := hcompletion z
    have reads : π (I X) = π (I Y) := by rw [hsection X htX, hsection Y htY, hwX, hwY, he]
    obtain ⟨p, a, _, _, ha, hp, hgp⟩ := hXR
    obtain ⟨q, b, _, _, hb, hq, hgq⟩ := hYR
    have hxy := hlu (show ∃ (p : pure C u) (a : ℝ),
        0 < a ∧ I X = a • (p : V) ∧ g (I X) = 1 from ⟨p, a, ha, hp, hgp⟩)
      (show ∃ (q : pure C u) (b : ℝ),
        0 < b ∧ I Y = b • (q : V) ∧ g (I Y) = 1 from ⟨q, b, hb, hq, hgq⟩) reads
    rw [← hwX, ← hwY, hI hxy]
  have hinter : S ⊓ T = spanFace B := by
    refine le_antisymm ?_ (le_inf hBF hBJ)
    rintro x ⟨hxF, hxJ⟩
    have hxI : x ∈ LinearMap.range I := by rw [hR]; exact hxJ
    obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp hxI
    have hp : π (I X) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hxF
    have hz : corner X = 0 := by
      have hgX : g (I X) = 0 := hS hxF
      rw [hread] at hgX
      exact (mul_eq_zero.mp hgX).resolve_left hc.ne'
    have hw : L (column X) = 0 := by
      conv_lhs at hp => rw [block_decomp X, hz]
      simpa [map_add, hkill, L, show block 0 0 (0 : HermitianMat (Fin 2) ℂ) = 0
        from map_zero core] using hp
    have hw0 := hL (hw.trans (L.map_zero).symm)
    rw [← hcore]
    refine ⟨lower X, ?_⟩
    change I (core (lower X)) = I X
    apply congrArg I
    calc
      _ = block (corner X) 0 0 + cross (column X) + core (lower X) := by
        rw [hz, hw0, map_zero, add_zero,
          show block 0 0 (0 : HermitianMat (Fin 2) ℂ) = 0 from map_zero core, zero_add]
      _ = X := (block_decomp X).symm
  have hmap (X : HermitianMat Index ℂ) : π (I X) ∈ T.map π :=
    ⟨I X, by change I X ∈ spanFace J; rw [← hR]; exact LinearMap.mem_range_self I X, rfl⟩
  have hplane : {q | q ∈ T.map π ∧ gQ q = 1} =
      (AffineSubspace.mk' q₀ (LinearMap.range L) : Set (V ⧸ S)) := by
    ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hy⟩
      have hxI : x ∈ LinearMap.range I := by rw [hR]; exact hx
      obtain ⟨X, rfl⟩ := LinearMap.mem_range.mp hxI
      have hX : corner X = t := by
        change gQ (π (I X)) = 1 at hy
        rw [hgQ, hread] at hy
        exact mul_left_cancel₀ hc.ne' (hy.trans hct.symm)
      rw [SetLike.mem_coe, AffineSubspace.mem_mk', hsection X hX]
      exact ⟨column X, by simp [vsub_eq_sub, add_sub_cancel_left]⟩
    · intro hy
      rw [SetLike.mem_coe, AffineSubspace.mem_mk'] at hy
      obtain ⟨w, hw⟩ := hy
      have hsum : y = q₀ + L w := by
        rw [hw, vsub_eq_sub]
        abel
      obtain ⟨X, htX, hwX, hXR⟩ := hcompletion w
      rw [hsum, ← hwX, ← hsection X htX]
      refine ⟨hmap X, ?_⟩
      rw [hgQ, hread, htX, hct]
  refine ⟨hinter, gQ, q₀, L, rfl, hL, ?_, ?_, hplane⟩
  · rw [LinearMap.finrank_range_of_inj hL, Module.finrank_pi_fintype,
      Complex.finrank_real_complex]
    decide
  · change π '' R = {q | q ∈ T.map π ∧ gQ q = 1}
    apply Set.Subset.antisymm
    · rintro _ ⟨r, ⟨p, a, hpJ, _, ha, rfl, hgp⟩, rfl⟩
      refine ⟨⟨_, T.smul_mem _ (Submodule.subset_span hpJ), rfl⟩, ?_⟩
      exact (hgQ _).trans hgp
    · intro y hy
      rw [hplane, SetLike.mem_coe, AffineSubspace.mem_mk'] at hy
      obtain ⟨w, hw⟩ := hy
      obtain ⟨X, htX, hwX, hXR⟩ := hcompletion w
      refine ⟨I X, hXR, ?_⟩
      rw [hsection X htX, hwX, hw, vsub_eq_sub]
      abel

end D5.S3.Quantum.Foundation.QutritSchurPlane
