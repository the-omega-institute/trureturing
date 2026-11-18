/- GID: D5/S3/Quantum/Algebra/CompressionKernel/NativeThreeKernelGeometry
   generality: I
   mirror-B: D5/B/S3/Quantum/Algebra/CompressionKernel/NativeThreeKernelGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native width-three Hermitian compression kernels share a kernel vector or neutral plane. -/

import D5.S3.Quantum.Algebra.CompressionKernel.CommonKernelSlice
import D5.S3.Quantum.Algebra.CompressionKernel.NativeThreeInertiaBridge
import D5.S3.Quantum.Algebra.CompressionKernel.NormalizedSingularHermitianKernel

/-! The full real Hermitian compression kernel at coefficient width three. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Module
open scoped BigOperators ComplexOrder ComplexConjugate
open D5.S3.Quantum.Algebra.CommonCoefficientPlane
open D5.S3.Quantum.Algebra.CommonKernelSlice
open D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
open D5.S3.Quantum.Algebra.NativeThreeInertiaBridge
open D5.S3.Quantum.Algebra.NormalizedSingularHermitianKernel

namespace D5.S3.Quantum.Algebra.NativeThreeKernelGeometry

open private linearIndependent_mix from D5.S3.Quantum.Algebra.CommonCoefficientPlane

set_option maxHeartbeats 800000 in
-- Three finite matrix expansions feed the common-kernel slice.
private theorem primitive_exclusion {a b : ℕ} (hab : a < b)
    (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
    (hinj : Function.Injective (stack X).mulVecLin)
    (C : Matrix (Fin 3) (Fin 3) ℂ) (hC : IsUnit C)
    (hprimitive : ∀ H : Matrix (Fin 3) (Fin 3) ℂ,
      (H.IsHermitian ∧ compression X H = 0) ↔
        ∃ x y z : ℝ, Cᴴ * H * C =
          Complex.I • !![(0 : ℂ), (x : ℂ), (y : ℂ);
            -(x : ℂ), 0, (z : ℂ); -(y : ℂ), -(z : ℂ), 0]) : False := by
  let A := C⁻¹
  have hA : IsUnit A := Matrix.isUnit_nonsing_inv_iff.mpr hC
  have hAC : A * C = 1 :=
    Matrix.nonsing_inv_mul C ((Matrix.isUnit_iff_isUnit_det C).mp hC)
  let Y := mix A X
  have hYinj : Function.Injective (stack Y).mulVecLin :=
    injective_stack_mix A hA X hinj
  have hskew (x y z : ℝ) :
      compression Y (Complex.I • !![(0 : ℂ), (x : ℂ), (y : ℂ);
        -(x : ℂ), 0, (z : ℂ); -(y : ℂ), -(z : ℂ), 0]) = 0 := by
    let S : Matrix (Fin 3) (Fin 3) ℂ :=
      Complex.I • !![(0 : ℂ), (x : ℂ), (y : ℂ);
        -(x : ℂ), 0, (z : ℂ); -(y : ℂ), -(z : ℂ), 0]
    have hrecover : Cᴴ * (Aᴴ * S * A) * C = S := by
      calc
        _ = (A * C)ᴴ * S * (A * C) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = S := by rw [hAC]; simp
    have hzero := ((hprimitive (Aᴴ * S * A)).mpr ⟨x, y, z, hrecover⟩).2
    change compression Y S = 0
    rw [show Y = mix A X from rfl, compression_mix]
    exact hzero
  have h01 : (Y 0)ᴴ * Y 1 = (Y 1)ᴴ * Y 0 := by
    ext r s
    have he := congrFun (congrFun (hskew 1 0 0) r) s
    simp [compression_eq_sum, Fin.sum_univ_three, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] at he
    have hz : Complex.I * (((Y 0)ᴴ * Y 1) r s - ((Y 1)ᴴ * Y 0) r s) = 0 := by
      linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero)
  have h02 : (Y 0)ᴴ * Y 2 = (Y 2)ᴴ * Y 0 := by
    ext r s
    have he := congrFun (congrFun (hskew 0 1 0) r) s
    simp [compression_eq_sum, Fin.sum_univ_three, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] at he
    have hz : Complex.I * (((Y 0)ᴴ * Y 2) r s - ((Y 2)ᴴ * Y 0) r s) = 0 := by
      linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero)
  have h12 : (Y 1)ᴴ * Y 2 = (Y 2)ᴴ * Y 1 := by
    ext r s
    have he := congrFun (congrFun (hskew 0 0 1) r) s
    simp [compression_eq_sum, Fin.sum_univ_three, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul] at he
    have hz : Complex.I * (((Y 1)ᴴ * Y 2) r s - ((Y 2)ᴴ * Y 1) r s) = 0 := by
      linear_combination he
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero)
  have hcomm : ∀ i j, (Y i)ᴴ * Y j = (Y j)ᴴ * Y i := by
    intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · exact h01
    · exact h02
    · exact h01.symm
    · rfl
    · exact h12
    · exact h02.symm
    · exact h12.symm
    · rfl
  have hcommon : (⨅ i, LinearMap.ker (Y i).mulVecLin) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    apply stack_injective_on_common_kernel Y hYinj
    intro i
    simp only [Submodule.mem_iInf] at hv
    exact hv i
  obtain ⟨t, htinj, hba⟩ :=
    common_kernel_slice_injective_of_common_kernel_bot Y hcomm hcommon
  exact (Nat.not_lt_of_ge hba) hab

private theorem normalized_graph_trichotomy :
    normalizedGraphTrichotomy := by
  intro K hD hHerm hSing
  obtain ⟨c, hc, hlinear | hconjugate⟩ :=
    universal_common_graph_orientation K hD hHerm hSing
  · obtain hkernel | hplane :=
      linear_graph_common_kernel_or_neutral_plane K hD hHerm hSing c hc hlinear
    · exact Or.inl hkernel
    · exact Or.inr (Or.inl hplane)
  · by_cases honto : ∀ u : ℂ, ∃ H ∈ K, H 0 2 = u
    · obtain ⟨C, hC, hiff⟩ :=
        surjective_conjugate_graph_primitive K hD hHerm hSing c hc hconjugate honto
      exact Or.inr (Or.inr ⟨C, hC, hiff⟩)
    · obtain hkernel | hplane :=
        conjugate_graph_proper_image_common_kernel_or_neutral_plane
          K hD hHerm hSing c hc hconjugate honto
      · exact Or.inl hkernel
      · exact Or.inr (Or.inl hplane)

set_option maxHeartbeats 800000 in
-- The proof combines finite matrix expansions and two congruence transports.
/-- At the strict native threshold, the compression Hermitian kernel has a
common nonzero kernel vector or a common complex neutral two-plane. -/
theorem native_three_compression_kernel_geometry :
    ∀ (a b : ℕ), a < b →
      ∀ (X : Fin 3 → Matrix (Fin a) (Fin b) ℂ),
        LinearIndependent ℂ X →
        Function.Injective (stack X).mulVecLin →
        (∃ v : Fin 3 → ℂ, v ≠ 0 ∧
          ∀ T : Matrix (Fin 3) (Fin 3) ℂ,
            T.IsHermitian → compression X T = 0 → T *ᵥ v = 0) ∨
        (∃ W : Submodule ℂ (Fin 3 → ℂ), Module.finrank ℂ W = 2 ∧
          ∀ T : Matrix (Fin 3) (Fin 3) ℂ,
            T.IsHermitian → compression X T = 0 →
            ∀ u ∈ W, ∀ v ∈ W, star u ⬝ᵥ (T *ᵥ v) = 0) := by
  intro a b hab X hX hinj
  by_cases hzero : ∀ T : Matrix (Fin 3) (Fin 3) ℂ,
      T.IsHermitian → compression X T = 0 → T = 0
  · right
    let J : Matrix (Fin 3) (Fin 2) ℂ := !![1, 0; 0, 1; 0, 0]
    have hJ : Function.Injective J.mulVecLin := by
      intro u v he
      funext r
      fin_cases r
      · simpa [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 0
      · simpa [J, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun he 1
    refine ⟨LinearMap.range J.mulVecLin, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hJ]
      simp
    · intro T hT hPhi u hu v hv
      rw [hzero T hT hPhi]
      simp
  · obtain ⟨T, hT, hPhi, hne⟩ : ∃ T : Matrix (Fin 3) (Fin 3) ℂ,
        T.IsHermitian ∧ compression X T = 0 ∧ T ≠ 0 := by
      simpa only [not_forall, exists_prop] using hzero
    obtain ⟨e, hp, hn, hz⟩ := spectral_signs hab X hX hinj T hT hPhi hne
    obtain ⟨B, hB, hD⟩ := signature_congruence T hT e hp hn hz
    let A := B⁻¹
    have hA : IsUnit A := Matrix.isUnit_nonsing_inv_iff.mpr hB
    have hBA : B * A = 1 := Matrix.mul_nonsing_inv B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB)
    have hrecover (Q : Matrix (Fin 3) (Fin 3) ℂ) :
        Aᴴ * (Bᴴ * Q * B) * A = Q := by
      calc
        _ = (B * A)ᴴ * Q * (B * A) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Q := by rw [hBA]; simp
    let Y := mix A X
    have hY : LinearIndependent ℂ Y := linearIndependent_mix A hA X hX
    have hYinj : Function.Injective (stack Y).mulVecLin :=
      injective_stack_mix A hA X hinj
    have hYSig : compression Y signature = 0 := by
      rw [show Y = mix A X from rfl, compression_mix, ← hD, hrecover, hPhi]
    have htrich := normalized_graph_trichotomy
    let K : Submodule ℝ (Matrix (Fin 3) (Fin 3) ℂ) :=
      { carrier := {Q | Q.IsHermitian ∧ compression Y Q = 0}
        zero_mem' := by
          change (0 : Matrix (Fin 3) (Fin 3) ℂ).IsHermitian ∧ compression Y 0 = 0
          simp [compression]
        add_mem' := by
          intro Q R hQ hR
          change Q.IsHermitian ∧ compression Y Q = 0 at hQ
          change R.IsHermitian ∧ compression Y R = 0 at hR
          refine ⟨hQ.1.add hR.1, ?_⟩
          rw [compression_eq_sum] at hQ hR ⊢
          calc
            (∑ x, ∑ s, (Q x s + R x s) • ((Y x)ᴴ * Y s)) =
                (∑ x, ∑ s, Q x s • ((Y x)ᴴ * Y s)) +
                  (∑ x, ∑ s, R x s • ((Y x)ᴴ * Y s)) := by
                    simp only [add_smul, Finset.sum_add_distrib]
            _ = 0 := by rw [hQ.2, hR.2, add_zero]
        smul_mem' := by
          intro r Q hQ
          change Q.IsHermitian ∧ compression Y Q = 0 at hQ
          refine ⟨hQ.1.smul (IsSelfAdjoint.all r), ?_⟩
          rw [compression_eq_sum] at hQ ⊢
          calc
            (∑ x, ∑ s, (r • Q x s) • ((Y x)ᴴ * Y s)) =
                (r : ℂ) • (∑ x, ∑ s, Q x s • ((Y x)ᴴ * Y s)) := by
                  simp only [Complex.real_smul, mul_smul, Finset.smul_sum]
            _ = 0 := by rw [hQ.2, smul_zero] }
    have hKD : D ∈ K := by
      change D.IsHermitian ∧ compression Y D = 0
      refine ⟨?_, ?_⟩
      · apply Matrix.IsHermitian.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [D]
      · have hDSig : D = signature := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [D, signature]
        rw [hDSig]
        exact hYSig
    have hKHerm : ∀ Q : Matrix (Fin 3) (Fin 3) ℂ, Q ∈ K → Q.IsHermitian := by
      intro Q hQ
      change Q.IsHermitian ∧ compression Y Q = 0 at hQ
      exact hQ.1
    have hKdet : ∀ Q : Matrix (Fin 3) (Fin 3) ℂ, Q ∈ K → Q.det = 0 := by
      intro Q hQ
      change Q.IsHermitian ∧ compression Y Q = 0 at hQ
      by_cases hneQ : Q = 0
      · simp [hneQ]
      · obtain ⟨eq, heqpos, heqneg, heqzero⟩ :=
          spectral_signs hab Y hY hYinj Q hQ.1 hQ.2 hneQ
        rw [hQ.1.det_eq_prod_eigenvalues]
        have heqzero' : ((hQ.1.eigenvalues (eq 2) : ℝ) : ℂ) = 0 := by
          exact_mod_cast heqzero
        exact Finset.prod_eq_zero (Finset.mem_univ (eq 2)) heqzero'
    obtain hkernel | hplane | hprimitive := htrich K hKD hKHerm hKdet
    · refine Or.inl ?_
      obtain ⟨v, hv, hKv⟩ := hkernel
      let w := B *ᵥ v
      have hw : w ≠ 0 := by
        intro hw0
        apply hv
        apply (Matrix.mulVec_injective_iff_isUnit.mpr hB)
        simpa [w, Matrix.mulVec_mulVec] using hw0
      refine ⟨w, hw, ?_⟩
      intro T hT hTPhi
      have hQ : Bᴴ * T * B ∈ K := by
        change (Bᴴ * T * B).IsHermitian ∧ compression Y (Bᴴ * T * B) = 0
        refine ⟨Matrix.isHermitian_conjTranspose_mul_mul B hT, ?_⟩
        rw [show Y = mix A X from rfl, compression_mix, hrecover]
        exact hTPhi
      have hz := hKv (Bᴴ * T * B) hQ
      have hstarB : IsUnit Bᴴ := hB.star
      apply (Matrix.mulVec_injective_iff_isUnit.mpr hstarB)
      simpa [w, Matrix.mulVec_mulVec, Matrix.mul_assoc] using hz
    · refine Or.inr ?_
      obtain ⟨W, hdim, hW⟩ := hplane
      let Korig : Set (Matrix (Fin 3) (Fin 3) ℂ) :=
        {T | T.IsHermitian ∧ compression X T = 0}
      obtain ⟨W', hdim', hW'⟩ := common_plane_transport Korig B hB W hdim (by
        intro T hTK u hu v hv
        apply hW (Bᴴ * T * B)
        · change (Bᴴ * T * B).IsHermitian ∧ compression Y (Bᴴ * T * B) = 0
          refine ⟨Matrix.isHermitian_conjTranspose_mul_mul B hTK.1, ?_⟩
          rw [show Y = mix A X from rfl, compression_mix, hrecover]
          exact hTK.2
        · exact hu
        · exact hv)
      refine ⟨W', hdim', ?_⟩
      intro T hT hTPhi u hu v hv
      exact hW' T ⟨hT, hTPhi⟩ u hu v hv
    · obtain ⟨C, hC, hiff⟩ := hprimitive
      have hprimitive' : ∀ H : Matrix (Fin 3) (Fin 3) ℂ,
          (H.IsHermitian ∧ compression Y H = 0) ↔
            ∃ x y z : ℝ, Cᴴ * H * C =
              Complex.I • !![(0 : ℂ), (x : ℂ), (y : ℂ);
                -(x : ℂ), 0, (z : ℂ); -(y : ℂ), -(z : ℂ), 0] := by
        intro H
        simpa [K, iSkew3] using hiff H
      exact False.elim (primitive_exclusion hab Y hYinj C hC hprimitive')

end D5.S3.Quantum.Algebra.NativeThreeKernelGeometry
