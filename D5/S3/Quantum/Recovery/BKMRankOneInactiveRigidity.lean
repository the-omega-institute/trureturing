/- GID: D5/S3/Quantum/Recovery/BKMRankOneInactiveRigidity
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMRankOneInactiveRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Active and inactive blocks at zero actual BKM gap for a rank-one observable. -/

import D5.S3.Quantum.Recovery.BKMObservableProductRigidity

/-! # Rank-one active and inactive blocks for the actual BKM gap -/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Matrix.SpectralPower (mpow mpow_one)
open D5.S3.Quantum.Recovery.BKMFlagRefinement (lift bkmGap)
open D5.S3.Quantum.Recovery.BKMObservableRigidity (mpow_add mpow_zero)
open D5.S3.Quantum.Recovery.BKMObservableProductRigidity
  (ratioPiece modularPiece relativeDensity bkmGap_eq_zero_iff_commute_ratioPieces)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
  (partialTraceRight partialTraceRight_add partialTraceRight_kronecker)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport
  (partialTraceRight_posDef partialTraceRight_embed_mul partialTraceRight_mul_embed)

namespace D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity

universe u
variable {n : Type*} [Fintype n]
variable {R E : Type u} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E]

private def spectralValues (s : n → ℝ) : Finset ℝ :=
  Finset.univ.image s

private def diagonalSlice (s : n → ℝ) (w : n → ℂ) (a : ℝ) : n → ℂ :=
  fun i => if s i = a then w i else 0

/-- The component of a vector in the whole eigenspace at a retained eigenvalue. -/
def activeSpectralPiece {S : Matrix R R ℂ} (hS : S.IsHermitian) (w : R → ℂ) (a : ℝ) :
    R → ℂ :=
  let U : Matrix R R ℂ := hS.eigenvectorUnitary
  U *ᵥ diagonalSlice hS.eigenvalues (Uᴴ *ᵥ w) a

private def lineProjection (w : n → ℂ) : Matrix n n ℂ :=
  (star w ⬝ᵥ w)⁻¹ • vecMulVec w (star w)

/-- Orthogonal projection onto the span of the grouped spectral pieces of the vector.
A zero piece contributes the zero matrix. -/
def activeProjection {S : Matrix R R ℂ} (hS : S.IsHermitian) (w : R → ℂ) : Matrix R R ℂ :=
  ∑ a ∈ spectralValues hS.eigenvalues, lineProjection (activeSpectralPiece hS w a)

private theorem outer_mulVec (v w z : n → ℂ) :
    vecMulVec v w *ᵥ z = (w ⬝ᵥ z) • v := by
  rw [vecMulVec_mulVec]
  ext i
  exact mul_comm _ _

private theorem lineProjection_hermitian (w : n → ℂ) : (lineProjection w).IsHermitian := by
  change (lineProjection w)ᴴ = lineProjection w
  have h : star (star w ⬝ᵥ w) = star w ⬝ᵥ w := (star_dotProduct w w).symm
  rw [lineProjection, Matrix.conjTranspose_smul, Matrix.conjTranspose_vecMulVec, star_star,
    star_inv₀, h]

private theorem lineProjection_mulVec (w z : n → ℂ) :
    lineProjection w *ᵥ z = ((star w ⬝ᵥ w)⁻¹ * (star w ⬝ᵥ z)) • w := by
  rw [lineProjection, Matrix.smul_mulVec, outer_mulVec, smul_smul]

private theorem lineProjection_self (w : n → ℂ) : lineProjection w *ᵥ w = w := by
  by_cases hw : w = 0
  · simp [hw]
  have hnorm : star w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_star_self_eq_zero.mp h)
  rw [lineProjection_mulVec, inv_mul_cancel₀ hnorm, one_smul]

private theorem diagonalSlice_orthogonal (s : n → ℝ) (w : n → ℂ) {a b : ℝ} (hab : a ≠ b) :
    star (diagonalSlice s w a) ⬝ᵥ diagonalSlice s w b = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : s i = a <;> simp [diagonalSlice, h, hab]

private theorem sum_diagonalSlice (s : n → ℝ) (w : n → ℂ) :
    ∑ a ∈ spectralValues s, diagonalSlice s w a = w := by
  ext i
  simp only [Finset.sum_apply, diagonalSlice]
  rw [Finset.sum_eq_single (s i)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · exact fun ha => (ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).elim

private theorem unitary_dotProduct {U : Matrix R R ℂ} (hU : Uᴴ * U = 1) (v w : R → ℂ) :
    star (U *ᵥ v) ⬝ᵥ (U *ᵥ w) = star v ⬝ᵥ w := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hU, one_mulVec]

private theorem activeProjection_spec {S : Matrix R R ℂ} (hS : S.IsHermitian) (w : R → ℂ) :
    let P := activeProjection hS w
    P.IsHermitian ∧ P * P = P ∧ P *ᵥ w = w ∧
      ∀ z, P *ᵥ z = z ↔ z ∈ Submodule.span ℂ (Set.range (activeSpectralPiece hS w)) := by
  classical
  let U : Matrix R R ℂ := hS.eigenvectorUnitary
  let s := hS.eigenvalues
  let v := Uᴴ *ᵥ w
  let z := activeSpectralPiece hS w
  let P := activeProjection hS w
  change P.IsHermitian ∧ P * P = P ∧ P *ᵥ w = w ∧
    ∀ x, P *ᵥ x = x ↔ x ∈ Submodule.span ℂ (Set.range z)
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  have hU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  have hfixed (a : ℝ) : P *ᵥ z a = z a := by
    change (∑ b ∈ spectralValues s, lineProjection (z b)) *ᵥ z a = z a
    rw [sum_mulVec, Finset.sum_eq_single a]
    · exact lineProjection_self _
    · intro b _ hb
      rw [lineProjection_mulVec, show star (z b) ⬝ᵥ z a = 0 from
        (unitary_dotProduct hU _ _).trans (diagonalSlice_orthogonal s v hb),
        mul_zero, zero_smul]
    · intro ha
      have hz : diagonalSlice s v a = 0 := by
        funext i
        have hi : s i ≠ a := fun he =>
          ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
        simp [diagonalSlice, hi]
      simp [z, activeSpectralPiece, U, s, v, hz]
  have hrange (x : R → ℂ) : P *ᵥ x ∈ Submodule.span ℂ (Set.range z) := by
    change (∑ b ∈ spectralValues s, lineProjection (z b)) *ᵥ x ∈ _
    rw [sum_mulVec]
    apply Submodule.sum_mem
    intro b _
    rw [lineProjection_mulVec]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  have hpreserve (x : R → ℂ) (hx : x ∈ Submodule.span ℂ (Set.range z)) : P *ᵥ x = x := by
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hfixed a
    | zero => exact mulVec_zero _
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
    | smul c x _ hx => rw [mulVec_smul, hx]
  refine ⟨?_, ?_, ?_, fun x => ⟨fun hx => hx ▸ hrange x, hpreserve x⟩⟩
  · change (∑ b ∈ spectralValues s, lineProjection (z b))ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl fun b _ => (lineProjection_hermitian (z b)).eq
  · apply Matrix.mulVec_injective
    funext x
    exact (mulVec_mulVec x P P).symm.trans (hpreserve _ (hrange x))
  · have hw : ∑ b ∈ spectralValues s, z b = w := by
      change ∑ b ∈ spectralValues s, U *ᵥ diagonalSlice s v b = w
      rw [← mulVec_sum, sum_diagonalSlice, show U *ᵥ v = w by
        rw [show v = Uᴴ *ᵥ w from rfl, mulVec_mulVec, hU', one_mulVec]]
    exact hpreserve _ (hw ▸ Submodule.sum_mem _ fun b _ =>
      Submodule.subset_span ⟨b, rfl⟩)

private theorem sum_rankOne_ratioPieces {s : n → ℝ} (hs : ∀ i, 0 < s i) (w : n → ℂ) :
    ∑ r ∈ (Finset.univ.image fun ij : n × n => s ij.1 / s ij.2),
      ratioPiece s r (vecMulVec w (star w)) = vecMulVec w (star w) := by
  ext i j
  simp only [Matrix.sum_apply, ratioPiece, Matrix.of_apply, ← div_eq_iff (hs j).ne']
  rw [Finset.sum_eq_single (s i / s j)]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · exact fun hr => (hr (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩)).elim

private def ratioCoefficient (s : n → ℝ) (w y : n → ℂ) (r a : ℝ) : ℂ :=
  ∑ j, if a = r * s j then star (w j) * y j else 0

private theorem rankOne_ratioPiece_mulVec (s : n → ℝ) (w y : n → ℂ) (r : ℝ) :
    ratioPiece s r (vecMulVec w (star w)) *ᵥ y =
      ∑ a ∈ spectralValues s, ratioCoefficient s w y r a • diagonalSlice s w a := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, diagonalSlice, mul_ite, mul_zero]
  rw [Finset.sum_eq_single (s i)]
  · simp only [ratioCoefficient, Finset.sum_mul, ite_mul, zero_mul,
      Matrix.mulVec, dotProduct, ratioPiece, Matrix.of_apply, vecMulVec_apply, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro j _
    split <;> simp [mul_left_comm, mul_comm]
  · intro a _ ha
    simp [Ne.symm ha]
  · exact fun ha => (ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).elim

/-- The extremal occupied eigenvalue separates coefficients in the grouped ratio tests. -/
private theorem ratioTests_separate {s : n → ℝ} (hs : ∀ i, 0 < s i) {w : n → ℂ}
    (hw : w ≠ 0) (d : ℝ → ℂ)
    (h : ∀ r, ∑ a ∈ spectralValues s, ratioCoefficient s w w r a * d a = 0) :
    ∀ a ∈ spectralValues s, d a = 0 := by
  classical
  have occupied : (Finset.univ.filter fun j => w j ≠ 0).Nonempty := by
    by_contra hempty
    apply hw
    funext j
    by_contra hj
    exact hempty ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ s occupied
  have hj0 := (Finset.mem_filter.mp hj).2
  let bad := (spectralValues s).filter fun a => d a ≠ 0
  suffices hbad : ¬ bad.Nonempty by
    intro a ha
    by_contra hd
    exact hbad ⟨a, Finset.mem_filter.mpr ⟨ha, hd⟩⟩
  intro hbad
  let a := bad.max' hbad
  have ha := Finset.mem_filter.mp (Finset.max'_mem bad hbad)
  have haPos : 0 < a := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha.1
    change 0 < bad.max' hbad
    exact hi ▸ hs i
  let r := a / s j
  have hr : 0 < r := div_pos haPos (hs j)
  have hraj : r * s j = a := div_mul_cancel₀ _ (hs j).ne'
  have hterm := h r
  rw [Finset.sum_eq_single a] at hterm
  · have hcoeff : ratioCoefficient s w w r a =
        star (diagonalSlice s w (s j)) ⬝ᵥ diagonalSlice s w (s j) := by
      apply Finset.sum_congr rfl
      intro k _
      have he : a = r * s k ↔ s k = s j := by
        rw [← hraj, mul_right_inj' hr.ne', eq_comm]
      by_cases hk : s k = s j
      · rw [ite_eq_left (he.mpr hk)]
        simp [diagonalSlice, hk]
      · rw [ite_eq_right (fun h => hk (he.mp h))]
        simp [diagonalSlice, hk]
    rw [hcoeff] at hterm
    rcases mul_eq_zero.mp hterm with hz | hz
    · have hzero := congrFun (dotProduct_star_self_eq_zero.mp hz) j
      exact hj0 (by simpa [diagonalSlice] using hzero)
    · exact ha.2 hz
  · intro b hb hba
    by_cases hd : d b = 0
    · rw [hd, mul_zero]
    have hlt : b < a := lt_of_le_of_ne
      (Finset.le_max' bad b (Finset.mem_filter.mpr ⟨hb, hd⟩)) hba
    have hz : ratioCoefficient s w w r b = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : w k = 0
      · simp [hk]
      have hlow : a ≤ r * s k := hraj ▸
        mul_le_mul_of_nonneg_left (hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)) hr.le
      simp [ne_of_lt (hlt.trans_le hlow)]
    rw [hz, zero_mul]
  · exact fun hn => (hn ha.1).elim

private theorem commute_ratioPieces_mulVec_slice {s : n → ℝ} (hs : ∀ i, 0 < s i)
    {w : n → ℂ} (hw : star w ⬝ᵥ w = 1) (X : Matrix n n ℂ)
    (hX : ∀ r, Commute X (ratioPiece s r (vecMulVec w (star w)))) (a : ℝ) :
    X *ᵥ diagonalSlice s w a = (star w ⬝ᵥ (X *ᵥ w)) • diagonalSlice s w a := by
  let K := vecMulVec w (star w)
  let c := star w ⬝ᵥ (X *ᵥ w)
  have hw' : w ≠ 0 := fun he => by simp [he] at hw
  have hK : Commute X K := by
    change X * vecMulVec w (star w) = vecMulVec w (star w) * X
    rw [← sum_rankOne_ratioPieces hs w, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun r _ => (hX r).eq
  have hvec : X *ᵥ w = c • w := by
    have he := congrArg (fun (M : Matrix n n ℂ) => M *ᵥ w) hK.eq
    simpa only [← mulVec_mulVec, show K = vecMulVec w (star w) from rfl, outer_mulVec,
      hw, one_smul, c] using he
  by_cases ha : a ∈ spectralValues s
  · ext i
    let d := fun b => (X *ᵥ diagonalSlice s w b) i - c * diagonalSlice s w b i
    have hd (r : ℝ) : ∑ b ∈ spectralValues s, ratioCoefficient s w w r b * d b = 0 := by
      have he := congrArg (fun (M : Matrix n n ℂ) => M *ᵥ w) (hX r).eq
      simp only [← mulVec_mulVec] at he
      rw [hvec, mulVec_smul, rankOne_ratioPiece_mulVec, mulVec_sum, Finset.smul_sum] at he
      have hi := congrFun he i
      simp only [mulVec_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hi
      simp only [d, mul_sub, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      refine hi.trans (Finset.sum_congr rfl fun b _ => ?_)
      ring
    exact sub_eq_zero.mp (ratioTests_separate hs hw' d hd a ha)
  · have hz : diagonalSlice s w a = 0 := by
      funext i
      have hi : s i ≠ a := fun he => ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
      simp [diagonalSlice, hi]
    simp [hz]

omit [Fintype n] in
private theorem rankOne_ratioPiece_adjoint {s : n → ℝ} (w : n → ℂ) {r : ℝ} (hr : r ≠ 0) :
    (ratioPiece s r (vecMulVec w (star w)))ᴴ =
      ratioPiece s r⁻¹ (vecMulVec w (star w)) := by
  ext i j
  have he : s j = r * s i ↔ s i = r⁻¹ * s j := by
    constructor
    · intro h
      rw [h, inv_mul_cancel_left₀ hr]
    · intro h
      rw [h, mul_inv_cancel_left₀ hr]
  simp only [Matrix.conjTranspose_apply, ratioPiece, Matrix.of_apply]
  by_cases hij : s i = r⁻¹ * s j
  · simp only [ite_eq_left hij, ite_eq_left (he.mpr hij), vecMulVec_apply,
      Pi.star_apply, star_mul, star_star]
  · have hji : s j ≠ r * s i := fun h => hij (he.mp h)
    simp only [ite_eq_right hij, ite_eq_right hji, star_zero]

private theorem sandwich_mul {V W : Matrix R R ℂ} (h : W * V = 1) (X Y : Matrix R R ℂ) :
    (V * X * W) * (V * Y * W) = V * (X * Y) * W := by
  calc
    _ = V * (X * ((W * V) * (Y * W))) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.one_mul]; simp only [Matrix.mul_assoc]

private theorem sandwich_cancel {V W : Matrix R R ℂ} (h : W * V = 1) (X : Matrix R R ℂ) :
    W * (V * X * W) * V = X := by
  calc
    _ = (W * V) * X * (W * V) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, Matrix.one_mul, Matrix.mul_one]

private theorem modal_mulVec_slice {S : Matrix R R ℂ} (hS : S.PosDef)
    {w : R → ℂ} (hw : star w ⬝ᵥ w = 1) (X : Matrix R R ℂ)
    (hX : ∀ r, Commute X (modularPiece hS.isHermitian r (vecMulVec w (star w))))
    (a : ℝ) :
    X *ᵥ activeSpectralPiece hS.isHermitian w a =
      (star w ⬝ᵥ (X *ᵥ w)) • activeSpectralPiece hS.isHermitian w a := by
  let U : Matrix R R ℂ := hS.isHermitian.eigenvectorUnitary
  let s := hS.isHermitian.eigenvalues
  let v := Uᴴ *ᵥ w
  let Y := Uᴴ * X * U
  have hu : Uᴴ * U = 1 := Unitary.coe_star_mul_self hS.isHermitian.eigenvectorUnitary
  have hu' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hS.isHermitian.eigenvectorUnitary
  have hv : star v ⬝ᵥ v = 1 :=
    (unitary_dotProduct (by rw [conjTranspose_conjTranspose]; exact hu') w w).trans hw
  have hK : Uᴴ * vecMulVec w (star w) * U = vecMulVec v (star v) := by
    rw [mul_vecMulVec, vecMulVec_mul, star_mulVec, conjTranspose_conjTranspose]
  have hY (r : ℝ) : Commute Y (ratioPiece s r (vecMulVec v (star v))) := by
    let L := ratioPiece s r (vecMulVec v (star v))
    have he := (hX r).eq
    change X * (U * ratioPiece s r (Uᴴ * vecMulVec w (star w) * U) * Uᴴ) =
      (U * ratioPiece s r (Uᴴ * vecMulVec w (star w) * U) * Uᴴ) * X at he
    rw [hK] at he
    have he' := congrArg (fun T => Uᴴ * T * U) he
    change Uᴴ * (X * (U * L * Uᴴ)) * U = Uᴴ * ((U * L * Uᴴ) * X) * U at he'
    rw [← sandwich_mul hu' X (U * L * Uᴴ), ← sandwich_mul hu' (U * L * Uᴴ) X,
      sandwich_cancel hu L] at he'
    exact he'
  have hcoeff : star v ⬝ᵥ (Y *ᵥ v) = star w ⬝ᵥ (X *ᵥ w) := by
    have he : Y *ᵥ v = Uᴴ *ᵥ (X *ᵥ w) := by
      simp only [Y, v, mulVec_mulVec, Matrix.mul_assoc, hu', Matrix.mul_one]
    rw [he]
    exact unitary_dotProduct (by rw [conjTranspose_conjTranspose]; exact hu') _ _
  have he := commute_ratioPieces_mulVec_slice hS.eigenvalues_pos hv Y hY a
  rw [hcoeff] at he
  have hy : U * Y = X * U := by
    rw [show Y = Uᴴ * X * U from rfl, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu', Matrix.one_mul]
  have he' := congrArg (fun x => U *ᵥ x) he
  change U *ᵥ (Y *ᵥ diagonalSlice s v a) = U *ᵥ
    ((star w ⬝ᵥ (X *ᵥ w)) • diagonalSlice s v a) at he'
  rw [mulVec_mulVec, hy, ← mulVec_mulVec (diagonalSlice s v a) X U, mulVec_smul] at he'
  exact he'


private theorem modal_support {S : Matrix R R ℂ} (hS : S.PosDef)
    (w : R → ℂ) (r : ℝ) :
    let P := activeProjection hS.isHermitian w
    let L := modularPiece hS.isHermitian r (vecMulVec w (star w))
    P * L = L ∧ L * P = L := by
  intro P L
  let U : Matrix R R ℂ := hS.isHermitian.eigenvectorUnitary
  let s := hS.isHermitian.eigenvalues
  let v := Uᴴ *ᵥ w
  let K := vecMulVec w (star w)
  have hK : Uᴴ * K * U = vecMulVec v (star v) := by
    simp only [K, v, mul_vecMulVec, vecMulVec_mul, star_mulVec, conjTranspose_conjTranspose]
  let mode := fun t => modularPiece hS.isHermitian t K
  have hmode (t : ℝ) : mode t = U * ratioPiece s t (vecMulVec v (star v)) * Uᴴ := by
    change U * ratioPiece s t (Uᴴ * K * U) * Uᴴ = _
    rw [hK]
  have hleft (t : ℝ) : P * mode t = mode t := by
    apply Matrix.mulVec_injective
    funext y
    rw [← mulVec_mulVec]
    apply ((activeProjection_spec hS.isHermitian w).2.2.2 _).mpr
    rw [hmode, ← mulVec_mulVec, ← mulVec_mulVec, rankOne_ratioPiece_mulVec, mulVec_sum]
    simp only [mulVec_smul]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨a, rfl⟩)
  have hP : P.IsHermitian := (activeProjection_spec hS.isHermitian w).1
  refine ⟨hleft r, ?_⟩
  change mode r * P = mode r
  by_cases hr : r = 0
  · have hz : mode r = 0 := by
      have hzero : ratioPiece s r (vecMulVec v (star v)) = 0 := by
        ext i j
        simp [ratioPiece, hr, s, (hS.eigenvalues_pos i).ne']
      rw [hmode, hzero, Matrix.mul_zero, Matrix.zero_mul]
    rw [hz, Matrix.zero_mul]
  · have hadj : (mode r⁻¹)ᴴ = mode r := by
      rw [hmode, hmode r, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, rankOne_ratioPiece_adjoint v (inv_ne_zero hr),
        inv_inv, Matrix.mul_assoc]
    have h := congrArg Matrix.conjTranspose (hleft r⁻¹)
    simpa only [Matrix.conjTranspose_mul, hP.eq, hadj] using h

omit [DecidableEq R] in
private def jointSlice (B : Matrix (R × E) (R × E) ℂ) (e f : E) : Matrix R R ℂ :=
  Matrix.of fun i j => B (i, e) (j, f)

omit [DecidableEq R] in
private theorem jointSlice_mul_lift (B : Matrix (R × E) (R × E) ℂ)
    (M : Matrix R R ℂ) (e f : E) :
    jointSlice (B * lift M) e f = jointSlice B e f * M := by
  ext i j
  simp [jointSlice, Matrix.mul_apply, Fintype.sum_prod_type, lift, Matrix.one_apply, mul_ite]

omit [DecidableEq R] in
private theorem jointSlice_lift_mul (M : Matrix R R ℂ)
    (B : Matrix (R × E) (R × E) ℂ) (e f : E) :
    jointSlice (lift M * B) e f = M * jointSlice B e f := by
  ext i j
  simp [jointSlice, Matrix.mul_apply, Fintype.sum_prod_type, lift, Matrix.one_apply, ite_mul]

private def compressionMap (w : R → ℂ) : Matrix (R × E) E ℂ :=
  Matrix.of fun p e => w p.1 * (1 : Matrix E E ℂ) p.2 e

omit [DecidableEq R] in
private theorem compressionMap_isometry {w : R → ℂ} (hw : star w ⬝ᵥ w = 1) :
    (compressionMap (E := E) w)ᴴ * compressionMap (E := E) w = 1 := by
  ext e f
  by_cases h : f = e
  · subst f
    simpa [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      compressionMap, Matrix.one_apply, mul_ite, dotProduct] using hw
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      compressionMap, Matrix.one_apply, mul_ite, h, Ne.symm h]

omit [DecidableEq R] in
private theorem compression_entry (B : Matrix (R × E) (R × E) ℂ) (w : R → ℂ) (e f : E) :
    ((compressionMap (E := E) w)ᴴ * B * compressionMap (E := E) w) e f =
      star w ⬝ᵥ (jointSlice B e f *ᵥ w) := by
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply, compressionMap,
    Matrix.one_apply, apply_ite, ite_mul, Matrix.mulVec, dotProduct, jointSlice]

private theorem relativeDensity_posDef {A : Matrix (R × E) (R × E) ℂ} (hA : A.PosDef)
    (hS : (partialTraceRight A).PosDef) : (relativeDensity A).PosDef := by
  let J := mpow (partialTraceRight A) (-(1 / 2))
  have hJ : J.PosDef := by
    change (mpow _ _).PosDef
    rw [mpow, ← CFC.rpow_eq_cfc_real hS.posSemidef.nonneg]
    exact CFC.rpow_nonneg.posSemidef.posDef_iff_isUnit.mpr (hS.isUnit.cfcRpow _)
  have hL : (lift (ι := E) J).PosDef := hJ.kronecker Matrix.PosDef.one
  change (lift J * A * lift J).PosDef
  have h := hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hL.isUnit)
  rwa [hL.isHermitian.eq] at h

private theorem partialTrace_relativeDensity (A : Matrix (R × E) (R × E) ℂ)
    (hS : (partialTraceRight A).PosDef) : partialTraceRight (relativeDensity A) = 1 := by
  unfold relativeDensity lift
  rw [partialTraceRight_mul_embed, partialTraceRight_embed_mul]
  let S := partialTraceRight A
  change mpow S (-(1 / 2)) * S * mpow S (-(1 / 2)) = 1
  calc
    _ = mpow S (-(1 / 2)) * mpow S 1 * mpow S (-(1 / 2)) := by
      rw [mpow_one hS.isHermitian]
    _ = _ := by
      rw [mpow_add hS, mpow_add hS,
        show -(1 / 2 : ℝ) + 1 + -(1 / 2) = 0 by norm_num, mpow_zero hS]

/-- For a faithful joint state and a unit rank-one observable, zero actual BKM gap
is equivalent to a unique faithful auxiliary density on the active retained span,
with the actual inactive partial trace equal to the complementary projection. -/
theorem bkmGap_rankOne_eq_zero_iff_activeBlock [Nonempty E]
    (A : Matrix (R × E) (R × E) ℂ) (hA : A.PosDef) (_htrace : A.trace = 1)
    (w : R → ℂ) (hw : star w ⬝ᵥ w = 1) :
    let P := activeProjection (partialTraceRight_posDef A hA).isHermitian w
    let Q := 1 - P
    let B := relativeDensity A
    bkmGap A (vecMulVec w (star w)) = 0 ↔
      ∃! T : Matrix E E ℂ, T.PosDef ∧ T.trace = 1 ∧
        B = P ⊗ₖ T + lift Q * B * lift Q ∧
        partialTraceRight (lift Q * B * lift Q) = Q ∧
        ∀ x : R × E → ℂ, x ≠ 0 → lift Q *ᵥ x = x →
          0 < star x ⬝ᵥ ((lift Q * B * lift Q) *ᵥ x) := by
  classical
  intro P Q B
  let S := partialTraceRight A
  have hS : S.PosDef := partialTraceRight_posDef A hA
  let K := vecMulVec w (star w)
  have hK : K.IsHermitian := by simp [K, Matrix.IsHermitian, Matrix.conjTranspose_vecMulVec]
  obtain ⟨hP, hPP, hPw, _⟩ := activeProjection_spec hS.isHermitian w
  change P.IsHermitian at hP
  change P * P = P at hPP
  change P *ᵥ w = w at hPw
  have hQ : Q.IsHermitian := Matrix.isHermitian_one.sub hP
  have hQQ : Q * Q = Q := by
    change (1 - P) * (1 - P) = 1 - P
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, sub_zero]
  have hPQ : P * Q = 0 := by
    change P * (1 - P) = 0
    rw [Matrix.mul_sub, Matrix.mul_one, hPP, sub_self]
  have hB : B.PosDef := relativeDensity_posDef hA hS
  have htraceB : partialTraceRight B = 1 := partialTrace_relativeDensity A hS
  have htraceQ : partialTraceRight (lift Q * B * lift Q) = Q := by
    simp only [lift, partialTraceRight_mul_embed, partialTraceRight_embed_mul,
      htraceB, Matrix.mul_one, hQQ]
  have hinactive (x : R × E → ℂ) (hx : x ≠ 0) (hfix : lift Q *ᵥ x = x) :
      0 < star x ⬝ᵥ ((lift Q * B * lift Q) *ᵥ x) := by
    rw [← mulVec_mulVec, hfix, ← mulVec_mulVec, dotProduct_mulVec,
      show star x ᵥ* lift Q = star x by
        rw [← show (lift Q : Matrix (R × E) (R × E) ℂ)ᴴ = lift Q by
          simp [lift, Matrix.conjTranspose_kronecker, hQ.eq], ← star_mulVec, hfix]]
    exact hB.dotProduct_mulVec_pos hx
  have hP0 : P ≠ 0 := by
    intro hp
    have hz : w = 0 := by simpa [hp] using hPw.symm
    simp [hz] at hw
  rw [bkmGap_eq_zero_iff_commute_ratioPieces A hA K hK]
  constructor
  · intro h
    let V := compressionMap (E := E) w
    let T := Vᴴ * B * V
    have hV : Vᴴ * V = 1 := compressionMap_isometry hw
    have hT : T.PosDef := hB.conjTranspose_mul_mul_same fun x y he => by
      have he' := congrArg (fun z => Vᴴ *ᵥ z) he
      simpa only [mulVec_mulVec, hV, one_mulVec] using he'
    have hBP : B * lift P = P ⊗ₖ T := by
      ext ⟨i,e⟩ ⟨j,f⟩
      let X := jointSlice B e f
      have hX (r : ℝ) : Commute X (modularPiece hS.isHermitian r K) := by
        have he := congrArg (fun M => jointSlice M e f) (h r).eq
        change X * modularPiece hS.isHermitian r K = modularPiece hS.isHermitian r K * X
        simpa only [jointSlice_mul_lift, jointSlice_lift_mul, X] using he
      have he : X * P = T e f • P := by
        change X * (∑ a ∈ spectralValues hS.isHermitian.eigenvalues,
          lineProjection (activeSpectralPiece hS.isHermitian w a)) =
          T e f • ∑ a ∈ spectralValues hS.isHermitian.eigenvalues,
            lineProjection (activeSpectralPiece hS.isHermitian w a)
        rw [Matrix.mul_sum, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [lineProjection, Matrix.mul_smul, Matrix.mul_vecMulVec,
          modal_mulVec_slice hS hw X hX, smul_vecMulVec, smul_comm,
          show T e f = star w ⬝ᵥ (X *ᵥ w) from compression_entry B w e f]
      have he' := congrArg (fun (M : Matrix R R ℂ) => M i j) he
      rw [← jointSlice_mul_lift] at he'
      simpa [jointSlice, Matrix.kronecker_apply, mul_comm] using he'
    have hPB : lift P * B = P ⊗ₖ T := by
      have he := congrArg Matrix.conjTranspose hBP
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_kronecker, lift,
        hP.eq, Matrix.conjTranspose_one, hB.isHermitian.eq, hT.isHermitian.eq] using he
    have hlSum : lift (ι := E) P + lift Q = 1 := by
      have he : P + Q = 1 := by
        change P + (1 - P) = 1
        abel
      simp only [lift, ← Matrix.add_kronecker, he, Matrix.one_kronecker_one]
    have hblock : B = P ⊗ₖ T + lift Q * B * lift Q := by
      have hz : lift P * B * lift Q = 0 := by
        rw [hPB]
        simp only [lift, ← Matrix.mul_kronecker_mul, hPQ, Matrix.zero_kronecker]
      calc
        B = B * lift P + B * lift Q := by rw [← Matrix.mul_add, hlSum, Matrix.mul_one]
        _ = P ⊗ₖ T + (lift P + lift Q) * B * lift Q := by
          rw [hBP, hlSum, Matrix.one_mul]
        _ = _ := by rw [Matrix.add_mul, Matrix.add_mul, hz, zero_add]
    have hTtrace : T.trace = 1 := by
      have he := congrArg partialTraceRight hblock
      rw [htraceB, partialTraceRight_add,
        show partialTraceRight (P ⊗ₖ T) = T.trace • P from partialTraceRight_kronecker P T,
        htraceQ] at he
      have he' : T.trace • P = (1 : ℂ) • P := by
        rw [one_smul]
        calc
          _ = 1 - Q := eq_sub_of_add_eq he.symm
          _ = P := sub_sub_cancel _ _
      exact (smul_left_injective ℂ hP0) he'
    refine ⟨T, ⟨hT, hTtrace, hblock, htraceQ, hinactive⟩, ?_⟩
    intro Y hY
    have he : P ⊗ₖ Y = P ⊗ₖ T := add_right_cancel (hY.2.2.1.symm.trans hblock)
    obtain ⟨i, j, hij⟩ : ∃ i j, P i j ≠ 0 := by
      by_contra! hz
      exact hP0 (Matrix.ext fun i j => hz i j)
    ext e f
    exact mul_left_cancel₀ hij (congrArg
      (fun (M : Matrix (R × E) (R × E) ℂ) => M (i,e) (j,f)) he)
  · rintro ⟨T, ⟨_, _, hblock, _, _⟩, _⟩ r
    let L := modularPiece hS.isHermitian r K
    obtain ⟨hPL, hLP⟩ := modal_support hS w r
    change P * L = L at hPL
    change L * P = L at hLP
    have hQL : Q * L = 0 := by
      change (1 - P) * L = 0
      rw [Matrix.sub_mul, Matrix.one_mul, hPL, sub_self]
    have hLQ : L * Q = 0 := by
      change L * (1 - P) = 0
      rw [Matrix.mul_sub, Matrix.mul_one, hLP, sub_self]
    change B * lift L = lift L * B
    rw [hblock, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc (lift Q * B),
      ← Matrix.mul_assoc (lift L) (lift Q * B) (lift Q),
      ← Matrix.mul_assoc (lift L) (lift Q) B]
    simp only [lift, ← Matrix.mul_kronecker_mul, hPL, hLP, hQL, hLQ, Matrix.mul_one,
      Matrix.one_mul, Matrix.zero_kronecker, Matrix.zero_mul, Matrix.mul_zero, add_zero]

#print axioms bkmGap_rankOne_eq_zero_iff_activeBlock

end D5.S3.Quantum.Recovery.BKMRankOneInactiveRigidity
