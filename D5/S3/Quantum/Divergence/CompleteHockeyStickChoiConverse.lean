/- GID: D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse
   mirror-E: none(waiver:finite-matrix-proof)
   anchors: []
   utility: none
   digest: Full Choi support slices characterize strict complete hockey-stick contraction. -/

import D5.S3.Quantum.Divergence.CompleteHockeyStickChoiSupport
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation

/-!
For a normalized Choi matrix J, choose one preimage under its positive
square root for each reference slice of a unit output vector w. The
rectangular matrix X of preimages then satisfies
(sqrt(J) X)(sqrt(J) X)ᴴ = I ⊗ |w⟩⟨w|. The operator norm bounds XXᴴ
by c I for c = ‖XXᴴ‖ + 2. Congruence gives c J ≥ I ⊗ |w⟩⟨w|.

Thus p = c⁻¹ lies in (0,1) and the unnormalized Choi matrix of the
subtracted map is positive. Its normalized residual has trace-preserving
action, which gives the Kraus completeness identity by trace duality.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse

open _root_.Matrix
open scoped BigOperators ComplexOrder Kronecker Matrix.Norms.L2Operator MatrixOrder
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open D5.S3.Quantum.Foundation.FiniteDiamondDistance (IsPure pureState)
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (act)
open D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (completeCoefficient)
open UnitaryReconstruction.LiuWildChoiObstruction (normalizedChoi normalizedChoi_entry pairMatrix)

universe u

variable {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B]

set_option maxHeartbeats 800000 in
/-- Full reference slices over a nonzero Choi-support vector give a positive
replacement component with pure output and a trace-preserving residual. -/
theorem exists_replacement_of_choi_support (N : QuantumChannel A B)
    (v : B → ℂ) (hv : v ≠ 0)
    (hSupport : ∀ i : A, (fun z : A × B => if z.1 = i then v z.2 else 0) ∈
      (pairMatrix (normalizedChoi N)).mulVecLin.range) :
    ∃ (p : ℝ) (τ : DensityState B) (M : QuantumChannel A B),
      0 < p ∧ p < 1 ∧ IsPure τ ∧
        ∀ Z : Matrix A A ℂ, act N Z = (1 - p) • act M Z + p • (Z.trace • pairMatrix τ) := by
  classical
  obtain ⟨t, ht, hvt⟩ : ∃ t : ℝ, 0 < t ∧ (t : ℂ) = star v ⬝ᵥ v :=
    RCLike.pos_iff_exists_ofReal.mp (Matrix.dotProduct_star_self_pos_iff.mpr hv)
  let s : ℝ := (Real.sqrt t)⁻¹
  let w : B → ℂ := (s : ℂ) • v
  have hs : star (s : ℂ) = (s : ℂ) := by simp
  have hs₂ : s * s * t = 1 := by
    dsimp only [s]
    rw [← pow_two, inv_pow, Real.sq_sqrt ht.le, inv_mul_cancel₀ ht.ne']
  have hw : star w ⬝ᵥ w = 1 := by
    calc
      _ = ((s * s * t : ℝ) : ℂ) := by
        simp only [w, star_smul, hs, smul_dotProduct, dotProduct_smul, ← hvt,
          smul_eq_mul, Complex.ofReal_mul, mul_assoc]
      _ = 1 := by rw [hs₂, Complex.ofReal_one]
  let τ : DensityState B := pureState w hw
  let J := pairMatrix (normalizedChoi N)
  have hJ : J.PosSemidef := density_posSemidef (normalizedChoi N)
  let S := CFC.sqrt J
  have hSS : S * S = J := CFC.sqrt_mul_sqrt_self J hJ.nonneg
  have hSstar : Sᴴ = S := (CFC.sqrt_nonneg J).posSemidef.isHermitian.eq
  let Y : Matrix (A × B) A ℂ := fun z i => if z.1 = i then w z.2 else 0
  have hpre (i : A) : ∃ x : (A × B) → ℂ, S *ᵥ x = fun z => Y z i := by
    have hcol : (fun z => Y z i) ∈ J.mulVecLin.range := by
      have hscale : (fun z => Y z i) =
          (s : ℂ) • (fun z : A × B => if z.1 = i then v z.2 else 0) := by
        funext z
        by_cases hz : z.1 = i <;> simp [Y, w, hz]
      rw [hscale]
      exact J.mulVecLin.range.smul_mem (s : ℂ) (hSupport i)
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hcol
    change J *ᵥ z = (fun y => Y y i) at hz
    refine ⟨S *ᵥ z, ?_⟩
    rwa [Matrix.mulVec_mulVec, hSS]
  choose x hx using hpre
  let X : Matrix (A × B) A ℂ := fun z i => x i z
  have hY : S * X = Y := by
    ext z i
    exact congrFun (hx i) z
  let T := (1 : Matrix A A ℂ) ⊗ₖ pairMatrix τ
  have hYY : Y * Yᴴ = T := by
    ext ⟨i, b⟩ ⟨j, b'⟩
    change (∑ k : A, (if i = k then w b else 0) * star (if j = k then w b' else 0)) =
      (1 : Matrix A A ℂ) i j * (w b * star (w b'))
    calc
      _ = (if i = i then w b else 0) * star (if j = i then w b' else 0) := by
        apply Finset.sum_eq_single i
        · intro k _ hki
          simp [Ne.symm hki]
        · simp
      _ = _ := by
        by_cases hij : i = j
        · subst j
          simp
        · simp [hij, Ne.symm hij]
  let G := X * Xᴴ
  let c : ℝ := ‖G‖ + 2
  have hc : 1 < c := by
    dsimp only [c]
    linarith [norm_nonneg G]
  let p : ℝ := c⁻¹
  have hc₀ : 0 < c := (by norm_num : (0 : ℝ) < 1).trans hc
  have hp : 0 < p := inv_pos.mpr hc₀
  have hp₁ : p < 1 := (inv_lt_one₀ hc₀).mpr hc
  have hpc : p * c = 1 := inv_mul_cancel₀ hc₀.ne'
  have hnorm : G ≤ ‖G‖ • (1 : Matrix (A × B) (A × B) ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (IsSelfAdjoint.le_algebraMap_norm_self G
        (Matrix.posSemidef_self_mul_conjTranspose X).isHermitian.isSelfAdjoint)
  have hbound : (c • (1 : Matrix (A × B) (A × B) ℂ) - G).PosSemidef := by
    apply Matrix.le_iff.mp (hnorm.trans (Matrix.le_iff.mpr ?_))
    rw [← sub_smul]
    apply Matrix.PosSemidef.one.smul
    dsimp only [c]
    linarith
  have hGram : S * G * Sᴴ = T := by
    calc
      _ = (S * X) * (S * X)ᴴ := by
        simp only [G, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = T := by rw [hY, hYY]
  have hdom : (c • J - T).PosSemidef := by
    have h := hbound.mul_mul_conjTranspose_same S
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hGram, hSstar, hSS] at h
  have hsmall : (J - p • T).PosSemidef := by
    simpa only [smul_sub, smul_smul, hpc, one_smul] using hdom.smul hp.le
  let d : ℝ := Fintype.card A
  have hd : 1 ≤ d := by
    dsimp only [d]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos : 0 < Fintype.card A))
  have hresidual : (d • J - p • T).PosSemidef := by
    have hsum : (d - 1) • J + J = d • J := by rw [sub_smul, one_smul, sub_add_cancel]
    simpa only [← add_sub_assoc, hsum] using (hJ.smul (sub_nonneg.mpr hd)).add hsmall

  -- Form the trace-normalized residual as a linear map on all input matrices.
  let F : MatrixMap A B ℂ :=
    CStarMatrix.ofMatrixₗ.symm.toLinearMap.comp
      (N.toCompletelyPositiveMap.toLinearMap.comp CStarMatrix.ofMatrixₗ.toLinearMap)
  let R : MatrixMap A B ℂ := (Matrix.traceLinearMap A ℂ ℂ).smulRight (pairMatrix τ)
  let q : ℝ := 1 - p
  have hq : 0 < q := sub_pos.mpr hp₁
  let L : MatrixMap A B ℂ := q⁻¹ • (F - p • R)
  have hL (Z : Matrix A A ℂ) :
      L Z = q⁻¹ • (act N Z - p • (Z.trace • pairMatrix τ)) := by
    simp only [L, LinearMap.smul_apply, LinearMap.sub_apply]
    <;> rfl
  have hcard₀ : (Fintype.card A : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  -- PhyslibLeaf takes the output index first. A simultaneous row and column
  -- swap of the reference-first residual preserves positive semidefiniteness.
  have hChoi : L.choi_matrix =
      q⁻¹ • ((d • J - p • T).submatrix (Prod.swap : B × A → A × B) Prod.swap) := by
    ext ⟨b, i⟩ ⟨b', j⟩
    have hNij : act N (Matrix.single i j 1) b b' = (d • J) (i, b) (j, b') := by
      simp only [d, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_natCast, J,
        normalizedChoi_entry, ← mul_assoc, mul_inv_cancel₀ hcard₀, one_mul]
      <;> rfl
    have hRij : ((Matrix.single i j (1 : ℂ)).trace • pairMatrix τ) b b' =
        T (i, b) (j, b') := by
      change (Matrix.single i j (1 : ℂ)).trace * pairMatrix τ b b' =
        (1 : Matrix A A ℂ) i j * pairMatrix τ b b'
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    change L (Matrix.single i j 1) b b' =
      q⁻¹ • ((d • J - p • T) (i, b) (j, b'))
    calc
      _ = q⁻¹ • (act N (Matrix.single i j 1) b b' -
          p • (((Matrix.single i j (1 : ℂ)).trace • pairMatrix τ) b b')) := by
        rw [hL]
        <;> rfl
      _ = _ := by
        rw [hNij, hRij]
        <;> rfl
  have hCP : L.IsCompletelyPositive := by
    apply (MatrixMap.choi_PSD_iff_CP_map L).mpr
    rw [hChoi]
    exact (hresidual.submatrix (Prod.swap : B × A → A × B)).smul (inv_nonneg.mpr hq.le)
  have hTP (Z : Matrix A A ℂ) : (L Z).trace = Z.trace := by
    have hNtrace : (act N Z).trace = Z.trace := N.trace_preserving (CStarMatrix.ofMatrix Z)
    have hτtrace : (pairMatrix τ).trace = 1 := τ.2.2
    have hsub : Z.trace - p • Z.trace = q • Z.trace := by
      dsimp only [q]
      rw [sub_smul, one_smul]
    rw [hL, Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
      hNtrace, hτtrace]
    simp only [smul_eq_mul, mul_one, hsub, smul_smul, inv_mul_cancel₀ hq.ne', one_smul]
  obtain ⟨K, hK⟩ := MatrixMap.IsCompletelyPositive.exists_kraus L hCP
  have hKact (Z : Matrix A A ℂ) : L Z = ∑ k, K k * Z * (K k)ᴴ := by
    rw [hK]
    simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  have hKcomplete : (∑ k, (K k)ᴴ * K k) = 1 := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro Z
    rw [Matrix.sum_mul, Matrix.trace_sum, Matrix.one_mul, ← hTP Z, hKact Z, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun k _ => (Matrix.trace_mul_cycle (K k) Z (K k)ᴴ).symm
  obtain ⟨M, hM⟩ := finite_kraus_quantum_channel K hKcomplete
  refine ⟨p, τ, M, hp, hp₁, ⟨w, rfl⟩, ?_⟩
  intro Z
  have hMact : act M Z = L Z := (hM Z).trans (hKact Z).symm
  change act N Z = q • act M Z + p • (Z.trace • pairMatrix τ)
  rw [hMact, hL, smul_smul, mul_inv_cancel₀ hq.ne', one_smul, sub_add_cancel]

section Coefficients

variable {A B : Type} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B]

/-- The replacement witness bounds the coefficient strictly below one even
at parameter one. -/
theorem coefficient_lt_one_of_choi_support (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 ≤ γ)
    (v : B → ℂ) (hv : v ≠ 0)
    (hSupport : ∀ i : A, (fun z : A × B => if z.1 = i then v z.2 else 0) ∈
      (pairMatrix (normalizedChoi N)).mulVecLin.range) :
    completeCoefficient N γ false < 1 := by
  obtain ⟨p, τ, M, hp, hp₁, _, hN⟩ := exists_replacement_of_choi_support N v hv hSupport
  exact (CompleteHockeyStickChoiSupport.coefficient_le_of_replacement
    N M τ hp.le hp₁.le hγ hN).trans_lt (sub_lt_self 1 hp)

/-- For each parameter greater than one, strict contraction occurs exactly
when the Choi support contains a full reference factor over a nonzero vector. -/
theorem coefficient_lt_one_iff (N : QuantumChannel A B) (γ : ℝ) (hγ : 1 < γ) :
    completeCoefficient N γ false < 1 ↔
      ∃ v : B → ℂ, v ≠ 0 ∧ ∀ i : A, (fun z : A × B => if z.1 = i then v z.2 else 0) ∈
        (pairMatrix (normalizedChoi N)).mulVecLin.range := by
  classical
  constructor
  · intro hlt
    by_contra h
    have hS (v : B → ℂ) (hv : ∀ i : A,
        (fun z : A × B => if z.1 = i then v z.2 else 0) ∈
          (pairMatrix (normalizedChoi N)).mulVecLin.range) : v = 0 := by
      by_contra hv₀
      exact h ⟨v, hv₀, hv⟩
    rw [CompleteHockeyStickChoiSupport.result N γ hγ hS] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  · rintro ⟨v, hv, hS⟩
    exact coefficient_lt_one_of_choi_support N γ hγ.le v hv hS

end Coefficients

end D5.S3.Quantum.Divergence.CompleteHockeyStickChoiConverse
