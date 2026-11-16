/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianOccupationCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Ordinary source coefficients of the normally convergent original occupation germ. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic

/-! Source differentiation is performed on a fixed-cutoff contraction germ.
The radius is never made uniform in the cutoff. Positive ordinary frequencies
make every fixed energy layer finite, including the zero layer. The external
coordinates remain literal; their coefficient extraction and restoration of
the original Wick readout are separate obligations. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open scoped BigOperators Topology ContDiff Ring
open Filter Metric

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients

open LatticeGeneratingFieldLocality LatticeHalfFock LatticePositiveEnergy
open OriginalGaussianExternalBlocks OriginalGaussianSourceMeans
open OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic
open scoped Matrix

universe u
variable {X : Type u} [Fintype X] [DecidableEq X]

private theorem energy_embedding (D : LatticeData) (N : ℕ) (d : Internal D N →₀ ℕ) :
    oscillatorEnergy (d.embDomain (OriginalSourceInverseCoefficient.boxLabel D N)) =
      internalEnergy D N d := by
  simp only [oscillatorEnergy, Finsupp.weight_apply, Finsupp.sum_embDomain,
    OriginalSourceInverseCoefficient.boxLabel, internalEnergy, smul_eq_mul]
  apply Finsupp.sum_congr
  intro i hi
  exact Nat.mul_comm _ _

theorem energy_layer_finite (D : LatticeData) (N n : ℕ) :
    {d : Internal D N →₀ ℕ | internalEnergy D N d = n}.Finite := by
  letI : Finite {d : Exponent D // oscillatorEnergy d ≤ n} := oscillatorLeFinite D n
  have hs : {d : Exponent D | oscillatorEnergy d ≤ n}.Finite := by
    exact Set.finite_coe_iff.mp (inferInstance : Finite {d : Exponent D // oscillatorEnergy d ≤ n})
  apply (hs.preimage (Finsupp.embDomain_injective
    (OriginalSourceInverseCoefficient.boxLabel D N)).injOn).subset
  intro d hd
  change oscillatorEnergy (d.embDomain (OriginalSourceInverseCoefficient.boxLabel D N)) ≤ n
  rw [energy_embedding, hd]

private theorem term_contDiff (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (d : Internal D N →₀ ℕ) (x y : X → ℂ) :
    ContDiff ℂ (⊤ : ℕ∞ω) (fun z => occupationTerm D a N e d (z, x, y)) := by
  simp_rw [original_occupation_scales]
  exact (contDiff_id.pow (2 * internalEnergy D N d)).mul contDiff_const

private theorem term_coefficient (D : LatticeData) (a : Charge D) (N : ℕ)
    (e : X → External D) (d : Internal D N →₀ ℕ) (x y : X → ℂ) (n : ℕ) :
    coefficient (2 * n) (fun z => occupationTerm D a N e d (z, x, y)) =
      if internalEnergy D N d = n then rawOccupationTerm D a N e d x y else 0 := by
  simp_rw [original_occupation_scales]
  rw [coefficient, iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]
  by_cases h : internalEnergy D N d = n
  · simp [h, Nat.factorial_ne_zero]
  · have hn : 2 * n ≠ 2 * internalEnergy D N d := by omega
    simp [h, hn]

theorem iterated_partial_diff {I : Type*} {F : I → ℂ → ℂ}
    (hF : ∀ i, ContDiff ℂ (⊤ : ℕ∞ω) (F i)) (s : Finset I) (m : ℕ) :
    Differentiable ℂ (iteratedDeriv m (fun z => ∑ i ∈ s, F i z)) := by
  have hc : ContDiff ℂ (⊤ : ℕ∞ω) (fun z => ∑ i ∈ s, F i z) :=
    ContDiff.sum (fun i hi => hF i)
  exact hc.differentiable_iteratedDeriv m (WithTop.coe_lt_top (m : ℕ∞))

/-- Every fixed ordinary source coefficient of the actual mixed occupation
sum is its finite energy layer. The two external coordinate families are
retained on their unit polydisks, and order zero needs no separate premise. -/
private theorem occupation_energy_coefficient (D : LatticeData) (a : Charge D)
    (N : ℕ) (e : X → External D) (x y : X → ℂ)
    (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1) (n : ℕ) :
    coefficient (2 * n) (fun z => ∑' d, occupationTerm D a N e d (z, x, y)) =
      ∑ᶠ d : Internal D N →₀ ℕ,
        if internalEnergy D N d = n then rawOccupationTerm D a N e d x y else 0 := by
  classical
  obtain ⟨r, hr, hr1, M, hM, hb⟩ := original_occupation_majorant_on_germ D a N e
  let F := fun d z => occupationTerm D a N e d (z, x, y)
  have hn : TendstoLocallyUniformlyOn
      (fun s : Finset (Internal D N →₀ ℕ) => fun z => ∑ d ∈ s, F d z)
      (fun z => ∑' d, F d z) atTop (ball (0 : ℂ) r) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    exact tendstoUniformlyOn_tsum hM (fun d z hz =>
      hb (z, x, y) ⟨(mem_ball_zero_iff.mp hz).le, hx, hy⟩ d)
  have hd (m : ℕ) : TendstoLocallyUniformlyOn
      (fun s : Finset (Internal D N →₀ ℕ) =>
        iteratedDeriv m (fun z => ∑ d ∈ s, F d z))
      (iteratedDeriv m (fun z => ∑' d, F d z)) atTop (ball (0 : ℂ) r) := by
    induction m with
    | zero => simpa using hn
    | succ m ih =>
      simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv
        (Eventually.of_forall (fun s =>
          (iterated_partial_diff (fun d => term_contDiff D a N e d x y) s m).differentiableOn))
        isOpen_ball
  have hs : HasSum (fun d => coefficient (2 * n) (F d))
      (coefficient (2 * n) (fun z => ∑' d, F d z)) := by
    have ht := ((hd (2 * n)).tendsto_at (a := (0 : ℂ)) (by simpa using hr)).div_const
      ((2 * n).factorial : ℂ)
    change Tendsto _ atTop (𝓝 _) at ht
    rw [HasSum]
    have hsum (s : Finset (Internal D N →₀ ℕ)) :
        iteratedDeriv (2 * n) (fun z => ∑ d ∈ s, F d z) 0 /
            ((2 * n).factorial : ℂ) = ∑ d ∈ s, coefficient (2 * n) (F d) := by
      rw [iteratedDeriv_fun_sum]
      · simp only [coefficient, Finset.sum_div]
      · intro d hd
        exact (term_contDiff D a N e d x y).contDiffAt.of_le (by simp)
    simp_rw [hsum] at ht
    exact ht
  have hfin : Function.HasFiniteSupport (fun d : Internal D N →₀ ℕ =>
      if internalEnergy D N d = n then rawOccupationTerm D a N e d x y else 0) := by
    apply (energy_layer_finite D N n).subset
    intro d hd
    by_contra h
    exact hd (if_neg h)
  change HasSum (fun d => coefficient (2 * n) (fun z => occupationTerm D a N e d (z, x, y))) _ at hs
  simp_rw [term_coefficient D a N e _ x y n] at hs
  exact hs.tsum_eq.symm.trans (tsum_eq_finsum hfin)

/-- The twice-energy source coefficient of the actual fixed-cutoff sewn
mixed generating function equals its finite occupation-energy layer. The
ordinary coefficient divides by the full (2*n)!; both external coordinate
families remain unchanged for their subsequent ordinary extraction. -/
private theorem mixed_finite_sewing_energy_coefficient (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ) (e : X → External D)
    (x y : X → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1) (n : ℕ) :
    coefficient (2 * n) (fun z =>
      Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
        Complex.exp (finiteMixedExponent D a N e (z, x, y))) =
      ∑ᶠ d : Internal D N →₀ ℕ,
        if internalEnergy D N d = n then rawOccupationTerm D a N e d x y else 0 := by
  obtain ⟨r, hr, hr1, hn, he⟩ := original_occupation_sewing_on_germ D hu a N e
  have hg : (fun z => ∑' d, occupationTerm D a N e d (z, x, y)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
        Complex.exp (finiteMixedExponent D a N e (z, x, y))) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    exact he (z, x, y) ⟨(mem_ball_zero_iff.mp hz).le, hx, hy⟩
  have hc := congrArg (fun v : ℂ => v / ((2 * n).factorial : ℂ))
    (hg.iteratedDeriv_eq (2 * n))
  exact hc.symm.trans (occupation_energy_coefficient D a N e x y hx hy n)

private theorem translate_quadratic {I J : Type*} [Fintype I] [Fintype J]
    (K : Matrix I I ℂ) (T : Matrix I J ℂ) (P : Matrix J J ℂ)
    (m : I → ℂ) (b t : J → ℂ) (hK : K.IsSymm) :
    (1 / 2 : ℂ) * (t ⬝ᵥ P.mulVec t) + b ⬝ᵥ t +
        (1 / 2 : ℂ) * ((m + T.mulVec t) ⬝ᵥ K.mulVec (m + T.mulVec t)) =
      (1 / 2 : ℂ) * (m ⬝ᵥ K.mulVec m) +
        (1 / 2 : ℂ) * (t ⬝ᵥ (P + T.transpose * K * T).mulVec t) +
        (b + T.transpose.mulVec (K.mulVec m)) ⬝ᵥ t := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.add_mulVec,
    ]
  simp only [← Matrix.mulVec_mulVec]
  rw [hK.dotProduct_mulVec_comm (x := m) (y := T.mulVec t),
    Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm (T.transpose.mulVec (K.mulVec m)) t,
    Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm (K.mulVec (T.mulVec t)) (T.mulVec t),
    dotProduct_comm (K.mulVec m) (T.mulVec t)]
  ring

private theorem unit_pair {I J : Type*} [Fintype I] [Fintype J]
    (K : Matrix I J ℂ) (u : I → ℂ) (v : J → ℂ) :
    (Matrix.of (fun (_ : Unit) i => u i) * K *
      Matrix.of (fun j (_ : Unit) => v j)) () () =
      u ⬝ᵥ K.mulVec v := by
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.mulVec, dotProduct,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private theorem unit_quadratic {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (u v : I → ℂ) :
    (1 / 2 : ℂ) * ∑ i, ∑ j,
      FiniteGaussianSewing.effectiveKernel (0 : Matrix Unit Unit ℂ)
        (0 : Matrix Unit Unit ℂ) A B (fun _ i => u i) (fun i _ => v i) i j =
      (1 / 2 : ℂ) * (Sum.elim u v ⬝ᵥ
        (FiniteGaussianSewing.covariance A B).mulVec (Sum.elim u v)) := by
  let U : Matrix Unit I ℂ := Matrix.of (fun _ i => u i)
  let V : Matrix I Unit ℂ := Matrix.of (fun i _ => v i)
  have h₁ : (U * (1 - B * A)⁻¹ʳ * B * U.transpose) () () =
      u ⬝ᵥ ((1 - B * A)⁻¹ʳ * B).mulVec u := by
    rw [Matrix.mul_assoc U _ B]
    exact unit_pair _ u u
  have h₂ : (U * (1 - B * A)⁻¹ʳ * V) () () =
      u ⬝ᵥ (1 - B * A)⁻¹ʳ.mulVec v := unit_pair _ u v
  have h₃ : (V.transpose * (1 - A * B)⁻¹ʳ * U.transpose) () () =
      v ⬝ᵥ (1 - A * B)⁻¹ʳ.mulVec u := unit_pair _ v u
  have h₄ : (V.transpose * (1 - A * B)⁻¹ʳ * A * V) () () =
      v ⬝ᵥ ((1 - A * B)⁻¹ʳ * A).mulVec v := by
    rw [Matrix.mul_assoc V.transpose _ A]
    exact unit_pair _ v v
  change (1 / 2 : ℂ) * ∑ i, ∑ j,
    FiniteGaussianSewing.effectiveKernel 0 0 A B U V i j = _
  simp only [FiniteGaussianSewing.effectiveKernel, Fintype.sum_sum_type,
    Fintype.sum_unique, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
    Matrix.zero_apply, zero_add, h₁, h₂, h₃, h₄]
  rw [FiniteGaussianSewing.covariance, Matrix.fromBlocks_mulVec]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Function.comp_def, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The mixed exponent obtained by actual finite affine sewing collects
into the literal finite constant, effective covariance and effective mean.
Only the fixed-cutoff contraction conditions used by sewing are required. -/
theorem original_finite_mixed_exponent_collect (D : LatticeData) (a : Charge D)
    (N : ℕ) (e : X → External D) (z : ℂ) (x y : X → ℂ)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((leftRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((rightRow D N e z).submatrix Sum.inl Sum.inl)‖ < 1) :
    finiteMixedExponent D a N e (z, x, y) = effectiveConstant D a N e z +
      (1 / 2 : ℂ) * ∑ i, ∑ j,
        originalEffectiveKernel D N e z i j * (Sum.elim x y i) * (Sum.elim x y j) +
      ∑ i, effectiveMean D a N e z i * Sum.elim x y i := by
  let L := leftRow D N e z
  let R := rightRow D N e z
  let A := L.submatrix Sum.inl Sum.inl
  let B := R.submatrix Sum.inl Sum.inl
  let C := FiniteGaussianSewing.covariance A B
  let V := L.submatrix Sum.inr Sum.inl
  let W := R.submatrix Sum.inl Sum.inr
  let T := Matrix.fromBlocks V.transpose 0 0 W
  let P := Matrix.fromBlocks (L.submatrix Sum.inr Sum.inr) 0 0
    (R.submatrix Sum.inr Sum.inr)
  let m := Sum.elim (fun i => leftMean D a N e z (.inl i))
    (fun i => rightMean D a N e z (.inl i))
  let b := Sum.elim (fun i => leftMean D a N e z (.inr i))
    (fun i => rightMean D a N e z (.inr i))
  let t := Sum.elim x y
  have hsym := original_rows_symm D N e z
  have hC : C.IsSymm := FiniteGaussianSewing.covariance_symm A B
    (fun i j => hsym.1 (.inl i) (.inl j))
    (fun i j => hsym.2 (.inl i) (.inl j)) hA hB
  have hT : T.mulVec t = Sum.elim
      (fun i => ∑ j, L (.inl i) (.inr j) * x j)
      (fun i => ∑ j, R (.inl i) (.inr j) * y j) := by
    funext i
    cases i with
    | inl i =>
      simp only [T, V, t, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply,
        zero_mul, Finset.sum_const_zero, add_zero, Sum.elim_inl, Sum.elim_inr,
        Matrix.transpose_apply, Matrix.submatrix_apply]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [L]
      rw [hsym.1 (.inr j) (.inl i)]
    | inr i => simp [T, W, t, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  have hE : P + T.transpose * C * T = originalEffectiveKernel D N e z := by
    simp only [P, T, C, FiniteGaussianSewing.covariance,
      Matrix.fromBlocks_transpose, Matrix.transpose_transpose, Matrix.transpose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.fromBlocks_add, Matrix.mul_assoc]
    simp only [originalEffectiveKernel, FiniteGaussianSewing.effectiveKernel,
      L, R, V, W, A, B, Matrix.mul_assoc]
  have hm : b + T.transpose.mulVec (C.mulVec m) = effectiveMean D a N e z := by
    ext i
    cases i <;>
      simp [b, T, C, m, V, W, A, B, L, R, effectiveMean,
        FiniteGaussianSewing.covariance, Matrix.fromBlocks_transpose,
        Matrix.fromBlocks_mulVec, Matrix.mulVec_add, Matrix.mulVec_mulVec,
        add_comm, add_left_comm, add_assoc]
  have hh := translate_quadratic C T P m b t hC
  rw [hE, hm, hT] at hh
  have hsum (K : Matrix (X ⊕ X) (X ⊕ X) ℂ) :
      t ⬝ᵥ K.mulVec t = ∑ i, ∑ j, K i j * t i * t j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hc : (1 / 2 : ℂ) * (m ⬝ᵥ C.mulVec m) = effectiveConstant D a N e z := by
    rw [← unit_quadratic]
    simp only [effectiveConstant, Fintype.sum_sum_type, Fintype.sum_unique]
    dsimp only [C, A, B, L, R, m]
    ring
  have hq : finiteMixedExponent D a N e (z, x, y) =
      (1 / 2 : ℂ) * (t ⬝ᵥ P.mulVec t) + b ⬝ᵥ t +
      (1 / 2 : ℂ) * ((m + Sum.elim
        (fun i => ∑ j, L (.inl i) (.inr j) * x j)
        (fun i => ∑ j, R (.inl i) (.inr j) * y j)) ⬝ᵥ C.mulVec
        (m + Sum.elim (fun i => ∑ j, L (.inl i) (.inr j) * x j)
          (fun i => ∑ j, R (.inl i) (.inr j) * y j))) := by
    rw [finiteMixedExponent, unit_quadratic]
    have hmix : Sum.elim
        (mixedMean L (leftMean D a N e z) x)
        (mixedMean R (rightMean D a N e z) y) =
        m + Sum.elim (fun i => ∑ j, L (.inl i) (.inr j) * x j)
          (fun i => ∑ j, R (.inl i) (.inr j) * y j) := by
      ext (i | i) <;> rfl
    change externalExponent L (leftMean D a N e z) x +
      externalExponent R (rightMean D a N e z) y +
      (1 / 2 : ℂ) * (_ ⬝ᵥ C.mulVec _) = _
    rw [hmix]
    congr 1
    have hP : t ⬝ᵥ P.mulVec t =
        (∑ i, ∑ j, L (.inr i) (.inr j) * x i * x j) +
        (∑ i, ∑ j, R (.inr i) (.inr j) * y i * y j) := by
      simp only [P, t, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec,
        add_zero, zero_add, dotProduct, Fintype.sum_sum_type,
        Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
        Matrix.zero_apply, zero_mul, Finset.sum_const_zero, Finset.mul_sum]
      try simp only [add_zero, zero_add, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
        apply Finset.sum_congr rfl <;> intro j hj <;> ring
    have hb : b ⬝ᵥ t = (∑ i, leftMean D a N e z (.inr i) * x i) +
        (∑ i, rightMean D a N e z (.inr i) * y i) := by
      simp only [b, t, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hP, hb]
    dsimp only [externalExponent]
    ring
  rw [hq, hh, hc, hsum]
  rfl

/-- Source extraction after collecting the literal effective Gaussian.
The external coordinates have not been differentiated or specialized. -/
theorem original_finite_sewing_energy_coefficient (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (N : ℕ) (e : X → External D)
    (x y : X → ℂ) (hx : ∀ j, ‖x j‖ ≤ 1) (hy : ∀ j, ‖y j‖ ≤ 1) (n : ℕ) :
    coefficient (2 * n) (fun z =>
      Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
      Complex.exp (effectiveConstant D a N e z) *
      Complex.exp ((1 / 2 : ℂ) * ∑ i, ∑ j,
        originalEffectiveKernel D N e z i j * Sum.elim x y i * Sum.elim x y j +
        ∑ i, effectiveMean D a N e z i * Sum.elim x y i)) =
      ∑ᶠ d : Internal D N →₀ ℕ,
        if internalEnergy D N d = n then rawOccupationTerm D a N e d x y else 0 := by
  obtain ⟨r, hr, hr1, hc⟩ := original_rows_contract_on_germ D N e
  have he : (fun z =>
      Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
        Complex.exp (finiteMixedExponent D a N e (z, x, y))) =ᶠ[𝓝 (0 : ℂ)]
      (fun z =>
      Complex.exp (-(D.rank : ℂ) / 2 * OriginalGaussianDeterminant.finiteLog N z) *
      Complex.exp (effectiveConstant D a N e z) *
      Complex.exp ((1 / 2 : ℂ) * ∑ i, ∑ j,
        originalEffectiveKernel D N e z i j * Sum.elim x y i * Sum.elim x y j +
        ∑ i, effectiveMean D a N e z i * Sum.elim x y i)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    have hz' := hc z (mem_ball_zero_iff.mp hz).le
    rw [original_finite_mixed_exponent_collect D a N e z x y hz'.1 hz'.2.1]
    simp only [Complex.exp_add]
    ring
  have hh := congrArg (fun v : ℂ => v / ((2 * n).factorial : ℂ))
    (he.iteratedDeriv_eq (2 * n))
  exact hh.symm.trans (mixed_finite_sewing_energy_coefficient D hu a N e x y hx hy n)

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianOccupationCoefficients
