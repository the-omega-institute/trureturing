/- GID: D5/S3/Quantum/Decoherence/GibbsBathBandwidthEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/GibbsBathBandwidthEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-level record spectra force a product output, exact bath sizes, and heat at minimum Gibbs bandwidth. -/

/-
Equality in the minimum Gibbs bath bandwidth bound.
The bath is the first tensor factor, as in GibbsBathBandwidth.Retains.
Formalizes the two-level argument in bath-bandwidth-equality.txt using the
staged GibbsBathBandwidth and LabelResetBandwidth results.
-/
import D5.S3.Quantum.Decoherence.LabelResetBandwidth
import D5.S3.Quantum.Decoherence.ProductRecordBandwidth

open Matrix Unitary
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open D5.S3.Quantum.Information.PartialTraceMutualInformation

namespace GibbsBathBandwidth

noncomputable section

set_option maxHeartbeats 800000

variable {M B : Type*} [Fintype M] [DecidableEq M] [Nonempty M]
  [Fintype B] [DecidableEq B] [Nonempty B]

omit [Nonempty B] [Nonempty M] in
private def tensorUnitary (V : unitary (Matrix B B ℂ)) (T : unitary (Matrix M M ℂ)) :
    unitary (Matrix (B × M) (B × M) ℂ) :=
  ⟨(V : Matrix B B ℂ) ⊗ₖ (T : Matrix M M ℂ), kronecker_mem_unitary V.prop T.prop⟩

omit [Nonempty B] [Nonempty M] in
private theorem conj_tensor (V : unitary (Matrix B B ℂ)) (T : unitary (Matrix M M ℂ))
    (A : Matrix B B ℂ) (C : Matrix M M ℂ) :
    conjStarAlgAut ℂ (Matrix (B × M) (B × M) ℂ) (tensorUnitary V T) (A ⊗ₖ C) =
      (conjStarAlgAut ℂ (Matrix B B ℂ) V A) ⊗ₖ
      (conjStarAlgAut ℂ (Matrix M M ℂ) T C) := by
  let W : Matrix B B ℂ := V
  let J : Matrix M M ℂ := T
  simp only [conjStarAlgAut_apply]
  change (W ⊗ₖ J) * (A ⊗ₖ C) * (W ⊗ₖ J)ᴴ = (W * A * Wᴴ) ⊗ₖ (J * C * Jᴴ)
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]

omit [Nonempty M] in
private theorem conj_scale_one (T : unitary (Matrix M M ℂ)) (r : ℝ) :
    conjStarAlgAut ℂ _ T (r • (1 : Matrix M M ℂ)) = r • 1 := by
  change (conjStarAlgAut ℂ _ T) ((r : ℂ) • (1 : Matrix M M ℂ)) = _
  rw [map_smul, map_one]
  rfl

omit [Nonempty M] [Fintype M] in
private theorem diagonalReal_constant (r : ℝ) :
    diagonalReal (fun _ : M => r) = r • (1 : Matrix M M ℂ) := by
  calc
    diagonalReal (fun _ : M => r) = diagonal (r • (fun _ : M => (1 : ℂ))) := by
      unfold diagonalReal
      apply congrArg diagonal
      funext i
      simp [Pi.smul_apply, Complex.real_smul]
    _ = _ := by rw [diagonal_smul, diagonal_one]

omit [Nonempty B] [Nonempty M] [Fintype B] [Fintype M] in
private theorem diagonalReal_tensor (x : B → ℝ) (y : M → ℝ) :
    diagonalReal x ⊗ₖ diagonalReal y =
      diagonalReal (fun i : B × M => x i.1 * y i.2) := by
  rw [diagonalReal, diagonalReal, diagonalReal, diagonal_kronecker_diagonal]
  simp [Complex.ofReal_mul]

omit [Nonempty B] [Nonempty M] in
private theorem diagonal_input (β : ℝ) (E : B → ℝ) (V : unitary (Matrix B B ℂ)) :
    gibbsBath β E V ⊗ₖ mixed M =
      conjStarAlgAut ℂ (Matrix (B × M) (B × M) ℂ) (tensorUnitary V (1 : unitary (Matrix M M ℂ)))
        (diagonalReal (fun i : B × M => gibbsWeight β E i.1 * (Fintype.card M : ℝ)⁻¹)) := by
  rw [← diagonalReal_tensor (gibbsWeight β E) (fun _ : M => (Fintype.card M : ℝ)⁻¹),
    diagonalReal_constant, conj_tensor, conj_scale_one]
  rfl

omit [Nonempty B] [Nonempty M] in
private theorem diagonal_output {ρ : Matrix M M ℂ} (hρ : ρ.IsHermitian) :
    mixed B ⊗ₖ ρ =
      conjStarAlgAut ℂ (Matrix (B × M) (B × M) ℂ) (tensorUnitary (1 : unitary (Matrix B B ℂ)) hρ.eigenvectorUnitary)
        (diagonalReal (fun i : B × M => (Fintype.card B : ℝ)⁻¹ * hρ.eigenvalues i.2)) := by
  rw [← diagonalReal_tensor (fun _ : B => (Fintype.card B : ℝ)⁻¹) hρ.eigenvalues,
    diagonalReal_constant, conj_tensor, conj_scale_one]
  exact congrArg (fun C => mixed B ⊗ₖ C) hρ.spectral_theorem

omit [DecidableEq B] in
private theorem gibbs_quotient (β : ℝ) (E : B → ℝ) (i j : B) :
    gibbsWeight β E i / gibbsWeight β E j = Real.exp (β * (E j - E i)) := by
  have hZ : 0 < ∑ k, Real.exp (-β * E k) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  unfold gibbsWeight
  rw [div_div_div_cancel_right₀ hZ.ne', ← Real.exp_sub]
  congr 1
  ring

omit [DecidableEq B] in
private theorem gibbs_strictAnti {β : ℝ} (hβ : 0 < β) (E : B → ℝ) {i j : B}
    (h : E i < E j) : gibbsWeight β E j < gibbsWeight β E i := by
  have hZ : 0 < ∑ k, Real.exp (-β * E k) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  unfold gibbsWeight
  apply (div_lt_div_iff_of_pos_right hZ).2
  exact Real.exp_lt_exp.mpr (mul_lt_mul_of_neg_left h (neg_neg_of_pos hβ))

omit [DecidableEq B] in
private theorem gibbs_anti {β : ℝ} (hβ : 0 < β) (E : B → ℝ) {i j : B}
    (h : E i ≤ E j) : gibbsWeight β E j ≤ gibbsWeight β E i :=
  h.lt_or_eq.elim (fun hlt => (gibbs_strictAnti hβ E hlt).le)
    (fun heq => by simp [gibbsWeight, heq])

/-- At the minimum width both exterior inequalities on the marginal are equalities. -/
theorem minimumWidth_endpoints {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ) {iMin iMax : B}
    (hMin : E iMin = minValue E) (hMax : E iMax = maxValue E) :
    (Fintype.card B : ℝ) * (gibbsWeight β E iMax * (Fintype.card M : ℝ)⁻¹) =
      minValue hρ.isHermitian.eigenvalues ∧
    (Fintype.card B : ℝ) * (gibbsWeight β E iMin * (Fintype.card M : ℝ)⁻¹) =
      maxValue hρ.isHermitian.eigenvalues := by
  let l := minValue hρ.isHermitian.eigenvalues
  let u := maxValue hρ.isHermitian.eigenvalues
  let x := (Fintype.card B : ℝ) * (gibbsWeight β E iMax * (Fintype.card M : ℝ)⁻¹)
  let y := (Fintype.card B : ℝ) * (gibbsWeight β E iMin * (Fintype.card M : ℝ)⁻¹)
  change x = l ∧ y = u
  obtain ⟨i, hi⟩ := minValue_attained hρ.isHermitian.eigenvalues
  obtain ⟨j, hj⟩ := maxValue_attained hρ.isHermitian.eigenvalues
  have hl : 0 < l := by simpa only [l, ← hi] using hρ.eigenvalues_pos i
  have hu : 0 < u := by simpa only [u, ← hj] using hρ.eigenvalues_pos j
  have hx : 0 < x := by dsimp [x]; positivity [Fintype.card_pos (α := B), Fintype.card_pos (α := M), gibbsWeight_pos β E iMax]
  obtain ⟨hlo, hhi⟩ := marginal_bounds hβ E V ρ U hU hMin hMax
  have hxl : x ≤ l := by
    simpa only [l, ← hi] using (scalar_le_iff_eigenvalues hρ.isHermitian x).mp hlo i
  have huy : u ≤ y := by
    simpa only [u, ← hj] using (le_scalar_iff_eigenvalues hρ.isHermitian y).mp hhi j
  have hlog : β * (E iMax - E iMin) = Real.log (u / l) := by
    rw [hMin, hMax, ← energyWidth, hw]
    change β * (β⁻¹ * Real.log (u / l)) = Real.log (u / l)
    rw [← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul]
  have hr : y / x = u / l := by
    have hs : ((Fintype.card B : ℝ) * (Fintype.card M : ℝ)⁻¹) ≠ 0 := by positivity
    have factor (k : B) : (Fintype.card B : ℝ) *
        (gibbsWeight β E k * (Fintype.card M : ℝ)⁻¹) =
        ((Fintype.card B : ℝ) * (Fintype.card M : ℝ)⁻¹) * gibbsWeight β E k := by ring
    dsimp [x, y]
    rw [factor, factor]
    rw [mul_div_mul_left _ _ hs, gibbs_quotient, hlog, Real.exp_log (div_pos hu hl)]
  have hcross : y * l = u * x := (div_eq_div_iff hx.ne' hl.ne').mp hr
  have hzero : (y - u) * l + u * (l - x) = 0 := by linarith
  have h₁ : 0 ≤ (y - u) * l := mul_nonneg (sub_nonneg.mpr huy) hl.le
  have h₂ : 0 ≤ u * (l - x) := mul_nonneg hu.le (sub_nonneg.mpr hxl)
  have hz₁ : (y - u) * l = 0 := by linarith
  have hz₂ : u * (l - x) = 0 := by linarith
  exact ⟨(sub_eq_zero.mp ((mul_eq_zero.mp hz₂).resolve_left hu.ne')).symm,
    sub_eq_zero.mp ((mul_eq_zero.mp hz₁).resolve_right hl.ne')⟩

/-- The actual joint output is between the two scalar bounds on the input spectrum. -/
theorem minimumWidth_joint_bounds {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ) :
    let Ω := conjStarAlgAut ℂ _ U (gibbsBath β E V ⊗ₖ mixed M)
    (minValue hρ.isHermitian.eigenvalues / (Fintype.card B : ℝ)) •
        (1 : Matrix (B × M) (B × M) ℂ) ≤ Ω ∧
      Ω ≤ (maxValue hρ.isHermitian.eigenvalues / (Fintype.card B : ℝ)) •
        (1 : Matrix (B × M) (B × M) ℂ) := by
  dsimp only
  obtain ⟨i, hi⟩ := minValue_attained E
  obtain ⟨j, hj⟩ := maxValue_attained E
  obtain ⟨hlo, hhi⟩ := minimumWidth_endpoints hβ E V hρ U hU hw hi hj
  have hb : 0 < (Fintype.card B : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [← hlo, ← hhi, mul_div_cancel_left₀ _ hb.ne', mul_div_cancel_left₀ _ hb.ne',
    diagonal_input, ← conjStarAlgAut_mul_apply]
  let W := U * tensorUnitary V (1 : unitary (Matrix M M ℂ))
  let t : B × M → ℝ := fun k => gibbsWeight β E k.1 * (Fintype.card M : ℝ)⁻¹
  have diagonal_nonneg (p q : B × M → ℝ) (h : ∀ k, p k ≤ q k) :
      (diagonalReal q - diagonalReal p).PosSemidef := by
    rw [diagonalReal, diagonalReal, diagonal_sub, posSemidef_diagonal_iff]
    exact fun k => Complex.nonneg_iff.mpr ⟨by simpa using sub_nonneg.mpr (h k), by simp⟩
  constructor
  · rw [Matrix.le_iff, ← conj_scale_one W, ← map_sub, conjStarAlgAut_apply,
      ← diagonalReal_constant]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact diagonal_nonneg _ _ (fun k => mul_le_mul_of_nonneg_right
      (gibbs_anti hβ E (hj ▸ le_maxValue E k.1)) (by positivity))
  · rw [Matrix.le_iff, ← conj_scale_one W, ← map_sub, conjStarAlgAut_apply,
      ← diagonalReal_constant]
    apply Matrix.PosSemidef.mul_mul_conjTranspose_same
    exact diagonal_nonneg _ _ (fun k => mul_le_mul_of_nonneg_right
      (gibbs_anti hβ E (hi ▸ minValue_le E k.1)) (by positivity))

omit [Nonempty M] [Nonempty B] [Fintype M] [DecidableEq M] [DecidableEq B] in
private theorem partialTrace_sub (A C : Matrix (B × M) (B × M) ℂ) :
    partialTraceLeft (A - C) = partialTraceLeft A - partialTraceLeft C := by
  apply eq_sub_of_add_eq
  rw [← partialTraceLeft_add, sub_add_cancel]

omit [Nonempty M] [Nonempty B] [Fintype M] in
private theorem partialTrace_scalar (r : ℝ) :
    partialTraceLeft (r • (1 : Matrix (B × M) (B × M) ℂ)) =
      ((Fintype.card B : ℝ) * r) • (1 : Matrix M M ℂ) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [partialTraceLeft, Complex.real_smul, nsmul_eq_mul]
  · simp [partialTraceLeft, h]

omit [Nonempty M] [Nonempty B] [Fintype M] in
private theorem psd_column_zero {A : Matrix (B × M) (B × M) ℂ} [Fintype M]
    (hA : A.PosSemidef) {i : M} (h : partialTraceLeft A i i = 0) (b : B) (j : B × M) :
    A j (b, i) = 0 := by
  have hdiag : ∀ k : B, 0 ≤ (A (k, i) (k, i)).re :=
    fun _ => (Complex.nonneg_iff.mp hA.diag_nonneg).1
  have hsum : ∑ k : B, (A (k, i) (k, i)).re = 0 := by
    have hr := congrArg Complex.reLm h
    unfold partialTraceLeft at hr
    rw [map_sum] at hr
    exact hr
  have hz : A (b, i) (b, i) = 0 := by
    apply Complex.ext
    · exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hdiag k)).mp hsum b (Finset.mem_univ _)
    · simpa only [Complex.zero_im] using (Complex.nonneg_iff.mp (hA.diag_nonneg (i := (b, i)))).2.symm
  have hquad : star (Pi.single (b, i) (1 : ℂ)) ⬝ᵥ
      (A *ᵥ Pi.single (b, i) 1) = 0 := by
    simpa [Pi.star_single, Matrix.mulVec_single_one, single_dotProduct] using hz
  simpa [Matrix.mulVec_single_one] using congrFun (hA.dotProduct_mulVec_zero_iff.mp hquad) j

/-- The joint output in the bath basis and a record eigenbasis. -/
def recordBasisOutput {ρ : Matrix M M ℂ} (hρ : ρ.IsHermitian)
    (Ω : Matrix (B × M) (B × M) ℂ) : Matrix (B × M) (B × M) ℂ :=
  conjStarAlgAut ℂ (Matrix (B × M) (B × M) ℂ)
    (tensorUnitary (1 : unitary (Matrix B B ℂ)) (star hρ.eigenvectorUnitary)) Ω

omit [Nonempty M] [Nonempty B] in
private theorem recordBasis_marginal {ρ : Matrix M M ℂ} (hρ : ρ.IsHermitian)
    {Ω : Matrix (B × M) (B × M) ℂ} (hm : partialTraceLeft Ω = ρ) :
    partialTraceLeft (recordBasisOutput hρ Ω) = diagonalReal hρ.eigenvalues := by
  unfold recordBasisOutput
  rw [LabelResetBandwidth.conj_eq_pad]
  change partialTraceLeft (LabelResetBandwidth.pad
    ((1 : Matrix B B ℂ) ⊗ₖ (↑(star hρ.eigenvectorUnitary) : Matrix M M ℂ)) Ω) = _
  rw [LabelResetBandwidth.partialTrace_pad, hm]
  change conjStarAlgAut ℂ (Matrix M M ℂ) (star hρ.eigenvectorUnitary) ρ = _
  conv_lhs => arg 2; rw [hρ.spectral_theorem]
  rw [← conjStarAlgAut_mul_apply, Unitary.star_mul_self, map_one]
  rfl

/-- Each extremal slack is positive and has a zero column for every bath
coordinate paired with any record eigenvector at its corresponding endpoint.
These columns span the full extremal record eigenspace tensored with the bath. -/
theorem minimumWidth_extreme_slack {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ) :
    let Ω := recordBasisOutput hρ.isHermitian (conjStarAlgAut ℂ _ U (gibbsBath β E V ⊗ₖ mixed M))
    let l := minValue hρ.isHermitian.eigenvalues
    let u := maxValue hρ.isHermitian.eigenvalues
    let L := Ω - (l / (Fintype.card B : ℝ)) • 1
    let H := (u / (Fintype.card B : ℝ)) • 1 - Ω
    L.PosSemidef ∧ H.PosSemidef ∧
      (∀ i, hρ.isHermitian.eigenvalues i = l → ∀ b j, L j (b, i) = 0) ∧
      (∀ i, hρ.isHermitian.eigenvalues i = u → ∀ b j, H j (b, i) = 0) := by
  dsimp only
  let Ω := conjStarAlgAut ℂ _ U (gibbsBath β E V ⊗ₖ mixed M)
  let T := tensorUnitary (1 : unitary (Matrix B B ℂ)) (star hρ.isHermitian.eigenvectorUnitary)
  let l := minValue hρ.isHermitian.eigenvalues
  let u := maxValue hρ.isHermitian.eigenvalues
  have hb : 0 < (Fintype.card B : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨hL, hH⟩ := minimumWidth_joint_bounds hβ E V hρ U hU hw
  have hpsd (A : Matrix (B × M) (B × M) ℂ) (h : A.PosSemidef) :
      (conjStarAlgAut ℂ _ T A).PosSemidef := by
    rw [conjStarAlgAut_apply]
    exact h.mul_mul_conjTranspose_same _
  have h₁ : (recordBasisOutput hρ.isHermitian Ω - (l / (Fintype.card B : ℝ)) • 1).PosSemidef := by
    simpa only [recordBasisOutput, T, map_sub, conj_scale_one] using hpsd _ (Matrix.le_iff.mp hL)
  have h₂ : ((u / (Fintype.card B : ℝ)) • 1 - recordBasisOutput hρ.isHermitian Ω).PosSemidef := by
    simpa only [recordBasisOutput, T, map_sub, conj_scale_one] using hpsd _ (Matrix.le_iff.mp hH)
  have hm := recordBasis_marginal hρ.isHermitian hU
  have hscalar (s : ℝ) : partialTraceLeft ((s / (Fintype.card B : ℝ)) •
      (1 : Matrix (B × M) (B × M) ℂ)) = s • (1 : Matrix M M ℂ) := by
    rw [partialTrace_scalar, mul_div_cancel₀ _ hb.ne']
  refine ⟨h₁, h₂, ?_, ?_⟩
  · intro i hi
    apply psd_column_zero h₁
    rw [partialTrace_sub, hm, hscalar]
    simp [diagonalReal, hi, l, Complex.real_smul]
  · intro i hi
    apply psd_column_zero h₂
    rw [partialTrace_sub, hm, hscalar]
    simp [diagonalReal, hi, u, Complex.real_smul]

/-- Both slacks annihilate every vector in their respective extreme tensor subspaces.
In the record eigenbasis, the subspaces consist of vectors supported on the
corresponding eigenvalue indices, with arbitrary bath coordinates. -/
theorem minimumWidth_extreme_slack_annihilates {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ) :
    let Ω := recordBasisOutput hρ.isHermitian (conjStarAlgAut ℂ _ U (gibbsBath β E V ⊗ₖ mixed M))
    let l := minValue hρ.isHermitian.eigenvalues
    let u := maxValue hρ.isHermitian.eigenvalues
    (∀ f : B × M → ℂ, (∀ i, hρ.isHermitian.eigenvalues i.2 ≠ l → f i = 0) →
      (Ω - (l / (Fintype.card B : ℝ)) • 1) *ᵥ f = 0) ∧
    (∀ f : B × M → ℂ, (∀ i, hρ.isHermitian.eigenvalues i.2 ≠ u → f i = 0) →
      ((u / (Fintype.card B : ℝ)) • 1 - Ω) *ᵥ f = 0) := by
  obtain ⟨_, _, hl, hu⟩ := minimumWidth_extreme_slack hβ E V hρ U hU hw
  dsimp only
  have zero_on_support (A : Matrix (B × M) (B × M) ℂ) (a : ℝ)
      (h : ∀ i, hρ.isHermitian.eigenvalues i = a → ∀ b j, A j (b, i) = 0)
      (f : B × M → ℂ) (hf : ∀ i, hρ.isHermitian.eigenvalues i.2 ≠ a → f i = 0) :
      A *ᵥ f = 0 := by
    ext j
    apply Finset.sum_eq_zero
    rintro ⟨b, i⟩ _
    change A j (b, i) * f (b, i) = 0
    by_cases hi : hρ.isHermitian.eigenvalues i = a
    · rw [h i hi b j, zero_mul]
    · rw [hf (b, i) hi, mul_zero]
  exact ⟨zero_on_support _ _ hl, zero_on_support _ _ hu⟩

/-- A two-valued positive record spectrum forces the actual joint output
at minimum bandwidth to be the product with the maximally mixed bath. -/
theorem minimumWidth_product {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues) :
    conjStarAlgAut ℂ _ U (gibbsBath β E V ⊗ₖ mixed M) = mixed B ⊗ₖ ρ := by
  let Ω := conjStarAlgAut ℂ _ U (gibbsBath β E V ⊗ₖ mixed M)
  let T := tensorUnitary (1 : unitary (Matrix B B ℂ)) hρ.isHermitian.eigenvectorUnitary
  let e := hρ.isHermitian.eigenvalues
  obtain ⟨_, _, hl, hu⟩ := minimumWidth_extreme_slack hβ E V hρ U hU hw
  have hbasis : recordBasisOutput hρ.isHermitian Ω =
      diagonalReal (fun i : B × M => (Fintype.card B : ℝ)⁻¹ * e i.2) := by
    ext j k
    rcases k with ⟨b, i⟩
    have hd (a : ℝ) (ha : e i = a) :
        diagonalReal (fun k : B × M => (Fintype.card B : ℝ)⁻¹ * e k.2) j (b, i) =
          ((a / (Fintype.card B : ℝ)) • (1 : Matrix (B × M) (B × M) ℂ)) j (b, i) := by
      by_cases hj : j = (b, i)
      · subst j
        simp [diagonalReal, e, ha, Complex.real_smul, div_eq_inv_mul]
      · simp [diagonalReal, hj]
    rcases htwo i with h | h
    · exact (sub_eq_zero.mp (hl i h b j)).trans (hd _ h).symm
    · exact (sub_eq_zero.mp (hu i h b j)).symm.trans (hd _ h).symm
  have ht : tensorUnitary (1 : unitary (Matrix B B ℂ)) (star hρ.isHermitian.eigenvectorUnitary) =
      star T := by
    apply Subtype.ext
    change (1 : Matrix B B ℂ) ⊗ₖ (↑(star hρ.isHermitian.eigenvectorUnitary) : Matrix M M ℂ) =
      ((1 : Matrix B B ℂ) ⊗ₖ (↑hρ.isHermitian.eigenvectorUnitary : Matrix M M ℂ))ᴴ
    rw [conjTranspose_kronecker, conjTranspose_one, coe_star]
    rfl
  unfold recordBasisOutput at hbasis
  rw [ht] at hbasis
  change Ω = mixed B ⊗ₖ ρ
  rw [diagonal_output hρ.isHermitian, ← hbasis, ← conjStarAlgAut_mul_apply,
    Unitary.mul_star_self, map_one]
  rfl

section Multiplicity

open Polynomial

/-- Multiplicity of a real value in a finite spectral list. -/
def multiplicity {I : Type*} [Fintype I] (f : I → ℝ) (a : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => f i = a).card

private theorem spectrum_count {I : Type*} [Fintype I] (f : I → ℝ) (a : ℝ) :
    (Finset.univ.val.map f).count a = multiplicity f a := by
  classical
  rw [Multiset.count_map]
  change (Finset.univ.filter (fun i => a = f i)).card = _
  unfold multiplicity
  congr 1
  ext i
  simp [eq_comm]

omit [Nonempty B] [Nonempty M] [DecidableEq B] [DecidableEq M] in
private theorem multiplicity_prod_left (f : B → ℝ) (a : ℝ) :
    multiplicity (fun i : B × M => f i.1) a = multiplicity f a * Fintype.card M := by
  classical
  unfold multiplicity
  have h : (Finset.univ.filter (fun i : B × M => f i.1 = a)) =
      (Finset.univ.filter (fun i => f i = a) ×ˢ (Finset.univ : Finset M)) := by
    ext i
    simp
  rw [h, Finset.card_product, Finset.card_univ]

omit [Nonempty B] [Nonempty M] [DecidableEq B] [DecidableEq M] in
private theorem multiplicity_prod_right (f : M → ℝ) (a : ℝ) :
    multiplicity (fun i : B × M => f i.2) a = Fintype.card B * multiplicity f a := by
  classical
  unfold multiplicity
  have h : (Finset.univ.filter (fun i : B × M => f i.2 = a)) =
      ((Finset.univ : Finset B) ×ˢ Finset.univ.filter (fun i => f i = a)) := by
    ext i
    simp
  rw [h, Finset.card_product, Finset.card_univ]

private theorem multiplicity_congr {I : Type*} [Fintype I] {f g : I → ℝ} {a b : ℝ}
    (h : ∀ i, f i = a ↔ g i = b) : multiplicity f a = multiplicity g b := by
  classical
  unfold multiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h i

private theorem diagonal_charpoly {I : Type*} [Fintype I] [DecidableEq I] (f : I → ℝ) :
    (diagonalReal f).charpoly =
      ((Finset.univ.val.map f).map fun a : ℝ => X - C (a : ℂ)).prod := by
  rw [diagonalReal, Matrix.charpoly_diagonal, Multiset.map_map, Finset.prod_map_val]
  rfl

private theorem diagonal_roots {I : Type*} [Fintype I] [DecidableEq I] (f : I → ℝ) :
    (diagonalReal f).charpoly.roots = (Finset.univ.val.map f).map Complex.ofReal := by
  rw [diagonalReal, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp [Multiset.map_map]
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

omit [Nonempty B] [Nonempty M] in
private theorem input_output_charpoly (β : ℝ) (E : B → ℝ) (V : unitary (Matrix B B ℂ))
    {ρ : Matrix M M ℂ} (hρ : ρ.IsHermitian) :
    (gibbsBath β E V ⊗ₖ mixed M).charpoly = (mixed B ⊗ₖ ρ).charpoly ↔
      Finset.univ.val.map (fun i : B × M => gibbsWeight β E i.1 * (Fintype.card M : ℝ)⁻¹) =
        Finset.univ.val.map (fun i : B × M => (Fintype.card B : ℝ)⁻¹ * hρ.eigenvalues i.2) := by
  rw [diagonal_input, diagonal_output hρ, conjStarAlgAut_apply, conjStarAlgAut_apply,
    charpoly_conj_unitary (coe_star_mul_self _), charpoly_conj_unitary (coe_star_mul_self _)]
  constructor
  · intro hc
    apply Multiset.map_injective Complex.ofReal_injective
    simpa only [diagonal_roots] using congrArg Polynomial.roots hc
  · intro he
    rw [diagonal_charpoly, diagonal_charpoly, he]

omit [DecidableEq B] in
private theorem gibbs_eq_iff_energy_eq {β : ℝ} (hβ : 0 < β) (E : B → ℝ) (i j : B) :
    gibbsWeight β E i = gibbsWeight β E j ↔ E i = E j := by
  constructor
  · intro h
    rcases lt_trichotomy (E i) (E j) with hlt | heq | hgt
    · exact ((gibbs_strictAnti hβ E hlt).ne h.symm).elim
    · exact heq
    · exact ((gibbs_strictAnti hβ E hgt).ne h).elim
  · intro h
    simp [gibbsWeight, h]

/-- At minimum width the bath has only its two extremal energies, and the
ambient orbit multiplicities give the exact two integer identities. -/
theorem minimumWidth_bath_multiplicities {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues) :
    (∀ i, E i = minValue E ∨ E i = maxValue E) ∧
    multiplicity E (minValue E) * Fintype.card M =
      Fintype.card B * multiplicity hρ.isHermitian.eigenvalues
        (maxValue hρ.isHermitian.eigenvalues) ∧
    multiplicity E (maxValue E) * Fintype.card M =
      Fintype.card B * multiplicity hρ.isHermitian.eigenvalues
        (minValue hρ.isHermitian.eigenvalues) := by
  classical
  let e := hρ.isHermitian.eigenvalues
  let x (i : B) := gibbsWeight β E i * (Fintype.card M : ℝ)⁻¹
  let y (i : M) := (Fintype.card B : ℝ)⁻¹ * e i
  let l := minValue e
  let u := maxValue e
  obtain ⟨j, hj⟩ := minValue_attained E
  obtain ⟨k, hk⟩ := maxValue_attained E
  have hb : (Fintype.card B : ℝ) ≠ 0 := by positivity
  have hd : (Fintype.card M : ℝ) ≠ 0 := by positivity
  obtain ⟨hl, hu⟩ := minimumWidth_endpoints hβ E V hρ U hU hw hj hk
  have hl' : x k = (Fintype.card B : ℝ)⁻¹ * l :=
    (eq_inv_mul_iff_mul_eq₀ hb).2 hl
  have hu' : x j = (Fintype.card B : ℝ)⁻¹ * u :=
    (eq_inv_mul_iff_mul_eq₀ hb).2 hu
  have hout := minimumWidth_product hβ E V hρ U hU hw htwo
  have hc : (gibbsBath β E V ⊗ₖ mixed M).charpoly = (mixed B ⊗ₖ ρ).charpoly := by
    rw [← hout, conjStarAlgAut_apply, charpoly_conj_unitary (coe_star_mul_self U)]
  have hm := (input_output_charpoly β E V hρ.isHermitian).mp hc
  change Finset.univ.val.map (fun i : B × M => x i.1) =
    Finset.univ.val.map (fun i : B × M => y i.2) at hm
  have hx (i i' : B) : x i = x i' ↔ E i = E i' := by
    dsimp [x]
    rw [mul_left_inj' (inv_ne_zero hd), gibbs_eq_iff_energy_eq hβ]
  have hy (i : M) (a : ℝ) : y i = (Fintype.card B : ℝ)⁻¹ * a ↔ e i = a :=
    mul_right_inj' (inv_ne_zero hb)
  have counts (i : B) (a : ℝ) (hi : x i = (Fintype.card B : ℝ)⁻¹ * a) :
      multiplicity E (E i) * Fintype.card M = Fintype.card B * multiplicity e a := by
    have h := congrArg (Multiset.count (x i)) hm
    rw [spectrum_count, spectrum_count, multiplicity_prod_left, multiplicity_prod_right] at h
    have hleft : multiplicity x (x i) = multiplicity E (E i) :=
      multiplicity_congr (fun j' => hx j' i)
    have hright : multiplicity y (x i) = multiplicity e a := by
      rw [hi]
      exact multiplicity_congr (fun k' => hy k' a)
    rw [hleft, hright] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    let i₀ : M := Classical.choice inferInstance
    have hmem : x i ∈ Finset.univ.val.map (fun ij : B × M => x ij.1) :=
      Multiset.mem_map.mpr ⟨(i, i₀), by simp, rfl⟩
    rw [hm] at hmem
    obtain ⟨⟨_, m⟩, _, hm'⟩ := Multiset.mem_map.mp hmem
    change y m = x i at hm'
    rcases htwo m with hlo | hhi
    · right
      rw [← hk, ← hx]
      exact hm'.symm.trans (((hy m l).2 hlo).trans hl'.symm)
    · left
      rw [← hj, ← hx]
      exact hm'.symm.trans (((hy m u).2 hhi).trans hu'.symm)
  · simpa only [hj] using counts j u hu'
  · simpa only [hk] using counts k l hl'

private theorem div_gcd_dvd_iff {d p b : ℕ} (hd : 0 < d) :
    d / Nat.gcd d p ∣ b ↔ d ∣ b * p := by
  have hg : 0 < Nat.gcd d p := Nat.gcd_pos_of_pos_left _ hd
  have hdg := Nat.gcd_dvd_left d p
  have hpg := Nat.gcd_dvd_right d p
  have cp := Nat.coprime_div_gcd_div_gcd hg
  have hmul : b * p / Nat.gcd d p = b * (p / Nat.gcd d p) :=
    Nat.mul_div_assoc _ hpg
  rw [← Nat.div_dvd_div_iff_right hdg (dvd_mul_of_dvd_right hpg _), hmul]
  exact ⟨fun h => dvd_mul_of_dvd_left h _, fun h => cp.dvd_of_dvd_mul_right h⟩

/-- A bath at minimum width has dimension divisible by d/gcd(d,p). -/
theorem minimumWidth_dimension_dvd {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues) :
    Fintype.card M / Nat.gcd (Fintype.card M) (multiplicity hρ.isHermitian.eigenvalues
      (maxValue hρ.isHermitian.eigenvalues)) ∣ Fintype.card B := by
  apply (div_gcd_dvd_iff Fintype.card_pos).2
  obtain ⟨_, h, _⟩ := minimumWidth_bath_multiplicities hβ E V hρ U hU hw htwo
  exact ⟨_, h.symm.trans (Nat.mul_comm _ _)⟩

private theorem sum_two_levels {I : Type*} [Fintype I] {f g : I → ℝ} {l u x y : ℝ}
    (hlu : l ≠ u) (htwo : ∀ i, f i = l ∨ f i = u)
    (hl : ∀ i, f i = l → g i = x) (hu : ∀ i, f i = u → g i = y) :
    ∑ i, g i = (multiplicity f l : ℝ) * x + (multiplicity f u : ℝ) * y := by
  classical
  let sl := Finset.univ.filter (fun i => f i = l)
  let su := Finset.univ.filter (fun i => f i = u)
  have hc : (Finset.univ.filter fun i => ¬ f i = l) = su := by
    ext i
    simp only [su, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (htwo i).elim (fun h => by simp [h, hlu]) (fun h => by simp [h, hlu.symm])
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => f i = l) g, hc]
  change ∑ i ∈ sl, g i + ∑ i ∈ su, g i = (sl.card : ℝ) * x + (su.card : ℝ) * y
  have h₁ : ∑ i ∈ sl, g i = ∑ _i ∈ sl, x :=
    Finset.sum_congr rfl (fun i hi => hl i (Finset.mem_filter.mp hi).2)
  have h₂ : ∑ i ∈ su, g i = ∑ _i ∈ su, y :=
    Finset.sum_congr rfl (fun i hi => hu i (Finset.mem_filter.mp hi).2)
  rw [h₁, h₂]
  simp [nsmul_eq_mul]

private theorem multiplicity_pos {I : Type*} [Fintype I] {f : I → ℝ} {a : ℝ}
    (h : ∃ i, f i = a) : 0 < multiplicity f a := by
  classical
  obtain ⟨i, hi⟩ := h
  exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

private theorem gibbsBath_posDef' (β : ℝ) (E : B → ℝ) (V : unitary (Matrix B B ℂ)) :
    (gibbsBath β E V).PosDef := by
  rw [gibbsBath, conjStarAlgAut_apply]
  exact isUnit_coe.posDef_star_right_conjugate_iff.mpr
    (diagonalReal_posDef _ (gibbsWeight_pos β E))

private theorem mixed_posDef' (I : Type*) [Fintype I] [DecidableEq I]
    (hI : 0 < (Fintype.card I : ℝ)) : (mixed I).PosDef := by
  rw [mixed, ← diagonalReal_constant]
  exact diagonalReal_posDef _ (fun _ => inv_pos.mpr hI)

private theorem multiplicity_eq_zero {I : Type*} [Fintype I] {f : I → ℝ} {a : ℝ}
    (h : ∀ i, f i ≠ a) : multiplicity f a = 0 := by
  classical
  simp [multiplicity, h]

/-- Every positive bath dimension divisible by d/gcd(d,p) attains the minimum.
The constructed bath has energies zero and the required width. -/
theorem minimumWidth_dimension_attained {β : ℝ} (hβ : 0 < β)
    {ρ : Matrix M M ℂ} (hρ : ρ.PosDef) (htr : ρ.trace = 1)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues)
    (hstrict : minValue hρ.isHermitian.eigenvalues < maxValue hρ.isHermitian.eigenvalues)
    (hdiv : Fintype.card M / Nat.gcd (Fintype.card M) (multiplicity hρ.isHermitian.eigenvalues
      (maxValue hρ.isHermitian.eigenvalues)) ∣ Fintype.card B) :
    ∃ (E : B → ℝ) (U : unitary (Matrix (B × M) (B × M) ℂ)),
      (∀ i, E i = 0 ∨ E i = requiredWidth β hρ) ∧
      energyWidth E = requiredWidth β hρ ∧
      conjStarAlgAut ℂ _ U (gibbsBath β E 1 ⊗ₖ mixed M) = mixed B ⊗ₖ ρ ∧
      Retains (gibbsBath β E 1) ρ U := by
  classical
  let e := hρ.isHermitian.eigenvalues
  let l := minValue e
  let u := maxValue e
  let p := multiplicity e u
  let q := multiplicity e l
  let d := Fintype.card M
  let b := Fintype.card B
  have hd : 0 < d := Fintype.card_pos
  have hb : 0 < b := Fintype.card_pos
  have hdl : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hbl : 0 < (b : ℝ) := Nat.cast_pos.mpr hb
  obtain ⟨i, hi⟩ := minValue_attained e
  have hl : 0 < l := by simpa only [l, ← hi] using hρ.eigenvalues_pos i
  have hu : 0 < u := hl.trans hstrict
  have hp : 0 < p := multiplicity_pos (maxValue_attained e)
  have hq : 0 < q := multiplicity_pos (minValue_attained e)
  have hqd : q + p = d := by
    have hs := sum_two_levels (g := fun _ : M => (1 : ℝ)) hstrict.ne htwo
      (fun _ _ => rfl) (fun _ _ => rfl)
    have hs' : (d : ℝ) = (q : ℝ) + (p : ℝ) := by simpa [d, q, p] using hs
    exact_mod_cast hs'.symm
  have hn : (p : ℝ) * u + (q : ℝ) * l = 1 := by
    have hs := sum_two_levels hstrict.ne htwo (fun _ h => h) (fun _ h => h)
    rw [hρ.isHermitian.trace_eq_sum_eigenvalues] at htr
    have hsum : (∑ i, e i) = (1 : ℝ) := by
      apply Complex.ofReal_injective
      push_cast
      exact htr
    change (∑ i, e i) = (q : ℝ) * l + (p : ℝ) * u at hs
    rw [hs, add_comm] at hsum
    exact hsum
  obtain ⟨n, hnNat⟩ := (div_gcd_dvd_iff hd).mp hdiv
  change b * p = d * n at hnNat
  have hnb : n ≤ b := by
    apply Nat.le_of_mul_le_mul_left _ hd
    rw [← hnNat, mul_comm d b]
    exact Nat.mul_le_mul_left _ (by omega)
  let m := b - n
  have hmNat : b * q = d * m := by
    dsimp [m]
    rw [Nat.mul_sub, ← hnNat, mul_comm d b, ← Nat.mul_sub,
      show d - p = q by omega]
  have hnpos : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hz, mul_zero] at hnNat
    exact (Nat.ne_of_gt (Nat.mul_pos hb hp)) hnNat
  have hmpos : 0 < m := by
    by_contra h
    have hz : m = 0 := by omega
    rw [hz, mul_zero] at hmNat
    exact (Nat.ne_of_gt (Nat.mul_pos hb hq)) hmNat
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset B))
    (by simpa [b] using hnb)
  have hSc : Sᶜ.card = m := by rw [Finset.card_compl, hS]
  let W := requiredWidth β hρ
  have hW : 0 < W := mul_pos (inv_pos.mpr hβ)
    (Real.log_pos ((one_lt_div hl).2 hstrict))
  let E (i : B) := if i ∈ S then 0 else W
  obtain ⟨j, hj⟩ := Finset.card_pos.mp (hS.symm ▸ hnpos)
  obtain ⟨k, hk⟩ := Finset.card_pos.mp (hSc.symm ▸ hmpos)
  have hk' : k ∉ S := Finset.mem_compl.mp hk
  have hmin : minValue E = 0 := by
    have h : E j = 0 := by simp [E, hj]
    rw [minValue_eq j, h]
    intro i
    rw [h]
    by_cases hi' : i ∈ S <;> simp [E, hi', hW.le]
  have hmax : maxValue E = W := by
    have h : E k = W := by simp [E, hk']
    rw [maxValue_eq k, h]
    intro i
    rw [h]
    by_cases hi' : i ∈ S <;> simp [E, hi', hW.le]
  have hlevels : ∀ i, E i = 0 ∨ E i = W := by
    intro i
    by_cases h : i ∈ S <;> simp [E, h]
  have hcnt₀ : multiplicity E 0 = n := by
    unfold multiplicity
    rw [← hS]
    congr 1
    ext i
    by_cases hi' : i ∈ S <;> simp [E, hi', hW.ne']
  have hcntW : multiplicity E W = m := by
    unfold multiplicity
    rw [← hSc]
    congr 1
    ext i
    by_cases hi' : i ∈ S <;> simp [E, hi', hW.ne]
  have hexp : Real.exp (-β * W) = l / u := by
    change Real.exp (-β * (β⁻¹ * Real.log (u / l))) = l / u
    rw [neg_mul, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul,
      Real.exp_neg, Real.exp_log (div_pos hu hl), inv_div]
  have hnReal : (b : ℝ) * p = d * n := by exact_mod_cast hnNat
  have hmReal : (b : ℝ) * q = d * m := by exact_mod_cast hmNat
  have hZ : ∑ i, Real.exp (-β * E i) = (b : ℝ) / ((d : ℝ) * u) := by
    rw [sum_two_levels (f := E) (g := fun i => Real.exp (-β * E i)) hW.ne hlevels
      (fun i hi' => by rw [hi', mul_zero, Real.exp_zero])
      (fun i hi' => by rw [hi', hexp]), hcnt₀, hcntW]
    apply (eq_div_iff (mul_ne_zero hdl.ne' hu.ne')).2
    calc
      ((n : ℝ) * 1 + m * (l / u)) * (d * u) =
          ((d : ℝ) * n) * u + (d * m) * l := by field_simp
      _ = b := by rw [← hnReal, ← hmReal, mul_assoc, mul_assoc, ← mul_add, hn, mul_one]
  let x (i : B) := gibbsWeight β E i * (d : ℝ)⁻¹
  let y (i : M) := (b : ℝ)⁻¹ * e i
  have hx (i : B) : (E i = 0 → x i = (b : ℝ)⁻¹ * u) ∧
      (E i = W → x i = (b : ℝ)⁻¹ * l) := by
    constructor <;> intro he
    · dsimp [x, gibbsWeight]
      rw [hZ, he, mul_zero, Real.exp_zero]
      field_simp
    · dsimp [x, gibbsWeight]
      rw [hZ, he, hexp]
      field_simp
  have hxL (i : B) : x i = (b : ℝ)⁻¹ * l ↔ E i = W := by
    refine ⟨fun hh => (hlevels i).elim (fun hz => ?_) id, (hx i).2⟩
    exact (hstrict.ne (((mul_right_inj' (inv_ne_zero hbl.ne')).1
      (((hx i).1 hz).symm.trans hh)).symm)).elim
  have hxU (i : B) : x i = (b : ℝ)⁻¹ * u ↔ E i = 0 := by
    refine ⟨fun hh => (hlevels i).elim id (fun hz => ?_), (hx i).1⟩
    exact (hstrict.ne ((mul_right_inj' (inv_ne_zero hbl.ne')).1
      (((hx i).2 hz).symm.trans hh))).elim
  have hs : Finset.univ.val.map (fun i : B × M => x i.1) =
      Finset.univ.val.map (fun i : B × M => y i.2) := by
    apply Multiset.ext.mpr
    intro a
    rw [spectrum_count, spectrum_count, multiplicity_prod_left, multiplicity_prod_right]
    by_cases hL : a = (b : ℝ)⁻¹ * l
    · subst a
      have h₁ := multiplicity_congr hxL
      have h₂ : multiplicity y ((b : ℝ)⁻¹ * l) = q :=
        multiplicity_congr (fun _ => mul_right_inj' (inv_ne_zero hbl.ne'))
      rw [h₁, h₂, hcntW, mul_comm m d, ← hmNat]
    by_cases hU : a = (b : ℝ)⁻¹ * u
    · subst a
      have h₁ := multiplicity_congr hxU
      have h₂ : multiplicity y ((b : ℝ)⁻¹ * u) = p :=
        multiplicity_congr (fun _ => mul_right_inj' (inv_ne_zero hbl.ne'))
      rw [h₁, h₂, hcnt₀, mul_comm n d, ← hnNat]
    have hz {z : ℝ} (h : z = (b : ℝ)⁻¹ * l ∨ z = (b : ℝ)⁻¹ * u) : z ≠ a :=
      fun he => h.elim (fun h' => hL (he.symm.trans h')) (fun h' => hU (he.symm.trans h'))
    have hx0 : multiplicity x a = 0 := multiplicity_eq_zero
      (fun i => hz ((hlevels i).elim (fun h => Or.inr ((hx i).1 h))
        (fun h => Or.inl ((hx i).2 h))))
    have hy0 : multiplicity y a = 0 := multiplicity_eq_zero
      (fun i => hz ((htwo i).elim (fun h => Or.inl (congrArg _ h))
        (fun h => Or.inr (congrArg _ h))))
    rw [hx0, hy0, zero_mul, mul_zero]
  have hSrc := ((gibbsBath_posDef' β E (1 : unitary (Matrix B B ℂ))).kronecker
    (mixed_posDef' M hdl)).isHermitian
  have hTgt := ((mixed_posDef' B hbl).kronecker hρ).isHermitian
  obtain ⟨U, hU⟩ := LabelResetBandwidth.exists_unitary_of_charpoly_eq
    hSrc hTgt ((input_output_charpoly β E 1 hρ.isHermitian).mpr hs)
  refine ⟨E, U, hlevels, by simp [energyWidth, hmin, hmax, W], hU, ?_⟩
  unfold Retains
  rw [hU]
  change partialTraceLeft (Matrix.kronecker (mixed B) ρ) = ρ
  rw [partialTraceLeft_kronecker, trace_mixed, one_smul]

/-- The bath energy increase, computed from the actual final joint matrix. -/
def bathHeat (H τ : Matrix B B ℂ) (Ω : Matrix (B × M) (B × M) ℂ) : ℝ :=
  (H * partialTraceRight Ω).trace.re - (H * τ).trace.re

omit [Nonempty B] [Nonempty M] [DecidableEq M] in
private theorem trace_conj_diagonal_mul (V : unitary (Matrix B B ℂ)) (E t : B → ℝ) :
    ((conjStarAlgAut ℂ _ V (diagonalReal E)) *
      (conjStarAlgAut ℂ _ V (diagonalReal t))).trace.re = ∑ i, E i * t i := by
  rw [← map_mul, conjStarAlgAut_apply, Matrix.trace_mul_cycle, coe_star_mul_self, one_mul,
    diagonalReal, diagonalReal, diagonal_mul_diagonal, trace_diagonal]
  rw [show (∑ i, (E i : ℂ) * (t i : ℂ)) = ((∑ i, E i * t i : ℝ) : ℂ) by push_cast; rfl]
  simp

/-- At minimum width the actual bath heat equals W q (1/d - μ₋).
This uses the two Hamiltonian eigenspaces and works for any common energy shift. -/
theorem minimumWidth_heat {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ)) {ρ : Matrix M M ℂ} (hρ : ρ.PosDef) (htr : ρ.trace = 1)
    (U : unitary (Matrix (B × M) (B × M) ℂ)) (hU : Retains (gibbsBath β E V) ρ U)
    (hw : energyWidth E = requiredWidth β hρ)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues)
    (hstrict : minValue hρ.isHermitian.eigenvalues < maxValue hρ.isHermitian.eigenvalues) :
    bathHeat (conjStarAlgAut ℂ _ V (diagonalReal E)) (gibbsBath β E V)
      (conjStarAlgAut ℂ _ U (gibbsBath β E V ⊗ₖ mixed M)) =
        energyWidth E *
          (multiplicity hρ.isHermitian.eigenvalues (minValue hρ.isHermitian.eigenvalues) : ℝ) *
          ((Fintype.card M : ℝ)⁻¹ - minValue hρ.isHermitian.eigenvalues) := by
  let b : ℝ := Fintype.card B
  let d : ℝ := Fintype.card M
  let l := minValue hρ.isHermitian.eigenvalues
  let q : ℝ := multiplicity hρ.isHermitian.eigenvalues l
  let x := minValue E
  let y := maxValue E
  let W := energyWidth E
  have hb : b ≠ 0 := by positivity
  have hd : d ≠ 0 := by positivity
  obtain ⟨j, hj⟩ := minValue_attained E
  obtain ⟨k, hk⟩ := maxValue_attained E
  obtain ⟨hl, _⟩ := minimumWidth_endpoints hβ E V hρ U hU hw hj hk
  obtain ⟨hlevels, _, hmult⟩ := minimumWidth_bath_multiplicities hβ E V hρ U hU hw htwo
  have hW : 0 < W := by
    have hlpos : 0 < l := by
      obtain ⟨i, hi⟩ := minValue_attained hρ.isHermitian.eigenvalues
      simpa only [l, ← hi] using hρ.eigenvalues_pos i
    rw [show W = energyWidth E from rfl, hw]
    exact mul_pos (inv_pos.mpr hβ) (Real.log_pos ((one_lt_div hlpos).2 hstrict))
  have hxy : x ≠ y := fun h => hW.ne' (sub_eq_zero.mpr h.symm)
  have hweight (i : B) (hi : E i = y) : gibbsWeight β E i = d * l / b := by
    have he : gibbsWeight β E i = gibbsWeight β E k :=
      (gibbs_eq_iff_energy_eq hβ E i k).2 (hi.trans hk.symm)
    rw [he]
    change b * (gibbsWeight β E k * d⁻¹) = l at hl
    field_simp at hl ⊢
    linarith
  have hm : (multiplicity E y : ℝ) * d = b * q := by
    dsimp only [y, d, b, q, l]
    exact_mod_cast hmult
  have hmass : ∑ i : B, (b⁻¹ - gibbsWeight β E i) = 0 := by
    rw [Finset.sum_sub_distrib, sum_gibbsWeight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change b * b⁻¹ - 1 = 0
    rw [mul_inv_cancel₀ hb, sub_self]
  have hunif : mixed B = conjStarAlgAut ℂ _ V (diagonalReal fun _ : B => b⁻¹) := by
    rw [diagonalReal_constant, conj_scale_one]
    rfl
  unfold bathHeat
  have hmixed : partialTraceRight (Matrix.kronecker (mixed B) ρ) = mixed B := by
    rw [partialTraceRight_kronecker, htr, one_smul]
  rw [minimumWidth_product hβ E V hρ U hU hw htwo]
  change ((conjStarAlgAut ℂ _ V (diagonalReal E)) *
      partialTraceRight (Matrix.kronecker (mixed B) ρ)).trace.re -
    ((conjStarAlgAut ℂ _ V (diagonalReal E)) * gibbsBath β E V).trace.re =
      W * q * (d⁻¹ - l)
  rw [hmixed, hunif, gibbsBath,
    trace_conj_diagonal_mul, trace_conj_diagonal_mul, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  change (∑ i, E i * (b⁻¹ - gibbsWeight β E i)) = W * q * (d⁻¹ - l)
  have hshift : (∑ i, (E i - x) * (b⁻¹ - gibbsWeight β E i)) =
      ∑ i, E i * (b⁻¹ - gibbsWeight β E i) := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hmass, mul_zero, sub_zero]
  rw [← hshift, sum_two_levels (f := E) hxy hlevels
    (fun _ hi => by rw [hi, sub_self, zero_mul])
    (fun i hi => by rw [hi, hweight i hi]), mul_zero, zero_add]
  have hc : (multiplicity E y : ℝ) = b * q / d := (eq_div_iff hd).2 hm
  rw [hc, show W = y - x from rfl]
  field_simp

end Multiplicity

section Ambient

open LabelResetBandwidth

variable {X R : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype R] [DecidableEq R]

/-- The actual ambient reset output is the product on the prescribed label line
and the entire record support, with the original zero modes included by padding. -/
theorem minimumWidth_ambient_product {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ))
    (v : X → R → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (K : Matrix R X ℂ) (hK : Kᴴ * K = 1)
    {ρ : Matrix X X ℂ} (hρ : ρ.PosDef) (havg : average v = pad K ρ)
    (U : unitary (Total X B R))
    (hU : Resets v w (conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V))))
    (hwidth : energyWidth E = requiredWidth β hρ)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues) :
    conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V)) =
      pad (resetEmbedding w ((1 : Matrix B B ℂ) ⊗ₖ K)) (mixed B ⊗ₖ ρ) := by
  obtain ⟨T, hT, hm, hp⟩ :=
    reduce_reset_unitary v hv w hw K hK havg (gibbsBath_posDef' β E V) U hU
  have hret : Retains (gibbsBath β E V) ρ T :=
    (congrArg partialTraceLeft hT).trans hm
  rw [hp, ← hT, minimumWidth_product hβ E V hρ T hret hwidth htwo]

/-- The finite positive bath dimensions permitting an actual ambient reset at
the minimum bandwidth are precisely the multiples of d/gcd(d,p). -/
theorem minimumWidth_ambient_dimension_iff {β : ℝ} (hβ : 0 < β)
    (v : X → R → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (K : Matrix R X ℂ) (hK : Kᴴ * K = 1)
    {ρ : Matrix X X ℂ} (hρ : ρ.PosDef) (havg : average v = pad K ρ)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues)
    (hstrict : minValue hρ.isHermitian.eigenvalues < maxValue hρ.isHermitian.eigenvalues) :
    (∃ (E : B → ℝ) (V : unitary (Matrix B B ℂ)) (U : unitary (Total X B R)),
      energyWidth E = requiredWidth β hρ ∧
      Resets v w (conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V)))) ↔
    Fintype.card X / Nat.gcd (Fintype.card X) (multiplicity hρ.isHermitian.eigenvalues
      (maxValue hρ.isHermitian.eigenvalues)) ∣ Fintype.card B := by
  constructor
  · rintro ⟨E, V, U, hwidth, hU⟩
    obtain ⟨T, hT⟩ := (reset_unitary_orbit_iff v hv w hw K hK havg
      (gibbsBath_posDef' β E V)).mp ⟨U, hU⟩
    exact minimumWidth_dimension_dvd hβ E V hρ T hT hwidth htwo
  · intro hdiv
    have htr : ρ.trace = 1 := by rw [← trace_pad K hK, ← havg, average_trace v hv]
    obtain ⟨E, T, _, hwidth, _, hT⟩ := minimumWidth_dimension_attained hβ hρ htr htwo hstrict hdiv
    obtain ⟨U, hU⟩ := (reset_unitary_orbit_iff v hv w hw K hK havg
      (gibbsBath_posDef' β E (1 : unitary (Matrix B B ℂ)))).mpr ⟨T, hT⟩
    exact ⟨E, 1, U, hwidth, hU⟩

omit [Nonempty B] [Nonempty X] [Fintype X] [Fintype B] [Fintype R] [DecidableEq B] [DecidableEq R]
  [DecidableEq X] in
private theorem reset_pad_tensor (w : X → ℂ) {I D : Type*} [Fintype I]
    (K : Matrix D I ℂ) (A : Matrix I I ℂ) :
    pad (resetEmbedding w K) A = pure w ⊗ₖ pad K A := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp only [pad, Matrix.mul_apply, resetEmbedding, LabelResetBandwidth.pure, vecMulVec_apply, Pi.star_apply,
    Matrix.kronecker_apply, conjTranspose_apply, star_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Heat computed from the actual ambient output after tracing out the reset label. -/
theorem minimumWidth_ambient_heat {β : ℝ} (hβ : 0 < β) (E : B → ℝ)
    (V : unitary (Matrix B B ℂ))
    (v : X → R → ℂ) (hv : ∀ x, star (v x) ⬝ᵥ v x = 1)
    (w : X → ℂ) (hw : star w ⬝ᵥ w = 1) (K : Matrix R X ℂ) (hK : Kᴴ * K = 1)
    {ρ : Matrix X X ℂ} (hρ : ρ.PosDef) (havg : average v = pad K ρ)
    (U : unitary (Total X B R))
    (hU : Resets v w (conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V))))
    (hwidth : energyWidth E = requiredWidth β hρ)
    (htwo : ∀ i, hρ.isHermitian.eigenvalues i = minValue hρ.isHermitian.eigenvalues ∨
      hρ.isHermitian.eigenvalues i = maxValue hρ.isHermitian.eigenvalues)
    (hstrict : minValue hρ.isHermitian.eigenvalues < maxValue hρ.isHermitian.eigenvalues) :
    bathHeat (conjStarAlgAut ℂ _ V (diagonalReal E)) (gibbsBath β E V)
      (partialTraceLeft (conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V)))) =
        energyWidth E *
          (multiplicity hρ.isHermitian.eigenvalues (minValue hρ.isHermitian.eigenvalues) : ℝ) *
          ((Fintype.card X : ℝ)⁻¹ - minValue hρ.isHermitian.eigenvalues) := by
  let Ω := ((1 : Matrix B B ℂ) ⊗ₖ K)ᴴ *
    partialTraceLeft (conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V))) *
      ((1 : Matrix B B ℂ) ⊗ₖ K)
  obtain ⟨T, hT, hm, hp⟩ :=
    reduce_reset_unitary v hv w hw K hK havg (gibbsBath_posDef' β E V) U hU
  change conjStarAlgAut ℂ _ T (gibbsBath β E V ⊗ₖ mixed X) = Ω at hT
  have hret : Retains (gibbsBath β E V) ρ T :=
    (congrArg partialTraceLeft hT).trans hm
  have htr : ρ.trace = 1 := by rw [← trace_pad K hK, ← havg, average_trace v hv]
  have hprod := minimumWidth_product hβ E V hρ T hret hwidth htwo
  rw [hT] at hprod
  have hpad : pad ((1 : Matrix B B ℂ) ⊗ₖ K) (mixed B ⊗ₖ ρ) =
      Matrix.kronecker (mixed B) (pad K ρ) := by
    rw [pad, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← mul_kronecker_mul, one_mul, mul_one]
    rfl
  have hout : partialTraceLeft (conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V))) =
      Matrix.kronecker (mixed B) (pad K ρ) := by
    rw [hp, reset_pad_tensor]
    change partialTraceLeft (Matrix.kronecker (pure w)
      (pad ((1 : Matrix B B ℂ) ⊗ₖ K) Ω)) = _
    rw [partialTraceLeft_kronecker, trace_pure w hw, one_smul, hprod, hpad]
  have hfinal : partialTraceRight
      (partialTraceLeft (conjStarAlgAut ℂ _ U (initial v (gibbsBath β E V)))) =
      partialTraceRight (conjStarAlgAut ℂ _ T (gibbsBath β E V ⊗ₖ mixed X)) := by
    rw [hout, partialTraceRight_kronecker, trace_pad K hK, hT, hprod]
    change _ = partialTraceRight (Matrix.kronecker (mixed B) ρ)
    rw [partialTraceRight_kronecker]
  unfold bathHeat
  rw [hfinal]
  exact minimumWidth_heat hβ E V hρ htr T hret hwidth htwo hstrict

end Ambient

end

end GibbsBathBandwidth
