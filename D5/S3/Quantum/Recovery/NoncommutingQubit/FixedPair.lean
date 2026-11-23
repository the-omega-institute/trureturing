/- GID: D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/NoncommutingQubit/FixedPair
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: A finite qubit channel fixing a noncommuting pair is the identity. -/

import D5.S3.Quantum.Recovery.ActualChannelAlgebra
import D5.S3.Quantum.FixedPointProjection

/-! Rigidity of a finite qubit channel with a noncommuting fixed pair. -/

noncomputable section

open Matrix D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Recovery.NoncommutingQubit

set_option autoImplicit false
set_option relaxedAutoImplicit false

local notation "Qubit" => Matrix (Fin 2) (Fin 2) ℂ

/-- Vanishing weight on the other eigenline forces each Kraus entry to vanish there. -/
private theorem eigenline_weight {s : Type*} [Fintype s] (K : s → Qubit) (i j : Fin 2) :
    (MatrixMap.of_kraus K K (Matrix.single j j 1) i i).re =
      ∑ a, Complex.normSq (K a i j) := by
  simp only [MatrixMap.of_kraus_apply, Matrix.sum_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_apply]
  have hcolumn (k : Fin 2) : (K a * Matrix.single j j (1 : ℂ) : Qubit) i k =
      if k = j then K a i j else 0 := by
    by_cases h : k = j
    · subst k
      simp
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ h, ite_eq_right h]
  simp only [hcolumn, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.conjTranspose_apply]
  change (K a i j * starRingEnd ℂ (K a i j)).re = _
  rw [Complex.mul_conj, Complex.ofReal_re]

private theorem identity_in_eigenbasis {s : Type*} [Fintype s] (K : s → Qubit)
    (hTP : (MatrixMap.of_kraus K K).IsTracePreserving)
    (A : Qubit) (hA : A.IsHermitian) (h01 : A 0 1 ≠ 0)
    (hFix : MatrixMap.of_kraus K K A = A)
    (hDiff : MatrixMap.of_kraus K K (Matrix.single 0 0 1 - Matrix.single 1 1 1) =
      Matrix.single 0 0 1 - Matrix.single 1 1 1) :
    MatrixMap.of_kraus K K = LinearMap.id := by
  let L := MatrixMap.of_kraus K K
  let P (i : Fin 2) : Qubit := Matrix.single i i 1
  let weight (i j : Fin 2) : ℝ := (L (P j) i i).re
  have hpos (i j : Fin 2) : 0 ≤ weight i j := by
    rw [show weight i j = ∑ a, Complex.normSq (K a i j) from eigenline_weight K i j]
    exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have ht (j : Fin 2) : weight 0 j + weight 1 j = 1 := by
    have h := congrArg Complex.re (hTP (P j))
    simpa [P, weight, L, Matrix.trace, Fin.sum_univ_two] using
      (show (Matrix.trace (L (P j))).re = (Matrix.trace (P j)).re from h)
  have hd0 : weight 0 0 - weight 0 1 = 1 := by
    have h := congrArg (fun M : Qubit => (M 0 0).re) hDiff
    simpa [P, L, weight, map_sub] using h
  have hd1 : weight 1 0 - weight 1 1 = -1 := by
    have h := congrArg (fun M : Qubit => (M 1 1).re) hDiff
    simpa [P, L, weight, map_sub] using h
  have h10 : weight 1 0 = 0 := by linarith [ht 0, hpos 1 0, hpos 0 1]
  have h01' : weight 0 1 = 0 := by linarith [hd1, ht 1, hpos 1 0, hpos 0 1]
  have hoff (a : s) (i j : Fin 2) (hij : i ≠ j) : K a i j = 0 := by
    have hz : weight i j = 0 := by fin_cases i <;> fin_cases j <;> simp_all
    have hsum : ∑ b, Complex.normSq (K b i j) = 0 := (eigenline_weight K i j).symm.trans hz
    exact Complex.normSq_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun b _ => Complex.normSq_nonneg (K b i j))).mp
        hsum a (Finset.mem_univ _))
  have hdiag (a : s) : K a = Matrix.diagonal (fun i => K a i i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ h, hoff a i j h]
  let c (i j : Fin 2) : ℂ := ∑ a, K a i i * star (K a j j)
  have hschur (X : Qubit) (i j : Fin 2) : L X i j = c i j * X i j := by
    change MatrixMap.of_kraus K K X i j = _
    simp only [MatrixMap.of_kraus_apply, Matrix.sum_apply, c, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    have ha := hdiag a
    conv_lhs => rw [ha, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change _ * _ * star (K a j j) = _
    ring
  have hcii (i : Fin 2) : c i i = 1 := by
    have h := hTP (P i)
    change Matrix.trace (L (P i)) = Matrix.trace (P i) at h
    simp only [Matrix.trace, Matrix.diag_apply, hschur, P] at h
    simpa [Finset.sum_ite_eq', Matrix.single_apply] using h
  have hA10 : A 1 0 ≠ 0 := by
    intro hz
    exact h01 (by simpa [hz] using (hA.apply 0 1).symm)
  have hc (i j : Fin 2) : c i j = 1 := by
    by_cases hij : i = j
    · subst j
      exact hcii i
    · have hn : A i j ≠ 0 := by
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact h01
        · exact hA10
        · exact (hij rfl).elim
      have h : L A i j = A i j := congrArg (fun M : Qubit => M i j) hFix
      rw [hschur] at h
      exact mul_right_cancel₀ hn (h.trans (one_mul _).symm)
  ext X i j
  change L X i j = X i j
  rw [hschur, hc, one_mul]

set_option maxHeartbeats 1600000 in
-- The comparison of the original and conjugated Kraus actions needs extra elaboration.
/-- A CPTP map of the actual qubit matrix algebra that fixes two noncommuting
density matrices acts as the identity on every complex matrix. -/
theorem cptp_eq_id_of_noncommuting_fixed_pair (L : MatrixMap (Fin 2) (Fin 2) ℂ)
    (hCP : L.IsCompletelyPositive) (hTP : L.IsTracePreserving)
    (A B : Qubit) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAt : A.trace = 1) (hBt : B.trace = 1)
    (hAB : A * B ≠ B * A) (hLA : L A = A) (hLB : L B = B) :
    L = LinearMap.id := by
  classical
  obtain ⟨K, rfl⟩ := MatrixMap.IsCompletelyPositive.exists_kraus L hCP
  let L := MatrixMap.of_kraus K K
  let D := A - B
  have hD : D.IsHermitian := hA.isHermitian.sub hB.isHermitian
  let F := (Unitary.conjStarAlgAut ℂ Qubit hD.eigenvectorUnitary).symm
  let A' := F A
  let B' := F B
  let L' := MatrixMap.of_kraus (fun a => F (K a)) (fun a => F (K a))
  have hConj (X : Qubit) : L' (F X) = F (L X) := by
    change MatrixMap.of_kraus _ _ (F X) = F (MatrixMap.of_kraus K K X)
    simp only [MatrixMap.of_kraus_apply, map_sum, map_mul, ← Matrix.star_eq_conjTranspose,
      map_star]
  have traceF (X : Qubit) : (F X).trace = X.trace := by
    change (star (hD.eigenvectorUnitary : Qubit) * X * hD.eigenvectorUnitary.val).trace = _
    rw [Matrix.trace_mul_cycle, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  have hTP' : L'.IsTracePreserving := by
    intro Y
    obtain ⟨X, rfl⟩ := F.surjective Y
    change (L' (F X)).trace = (F X).trace
    rw [hConj, traceF, traceF]
    exact hTP X
  let z : Fin 2 → ℂ := RCLike.ofReal ∘ hD.eigenvalues
  have hdiag : F D = Matrix.diagonal z := by
    simpa only [F, z, Unitary.conjStarAlgAut_symm] using
      hD.conjStarAlgAut_star_eigenvectorUnitary
  have htr : z 0 + z 1 = 0 := by
    rw [← Fin.sum_univ_two, ← Matrix.trace_diagonal, ← hdiag, traceF,
      show D.trace = 0 by simp [D, Matrix.trace_sub, hAt, hBt]]
  have hZ : F D = z 0 • (Matrix.single 0 0 1 - Matrix.single 1 1 1) := by
    rw [hdiag]
    have hz1 : z 1 = -z 0 := by linear_combination htr
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz1]
  have hzne : z 0 ≠ 0 := by
    intro hz
    have hd : D = 0 := F.injective ((hZ.trans (by rw [hz, zero_smul])).trans (map_zero F).symm)
    have heq : A = B := sub_eq_zero.mp hd
    exact hAB (by rw [heq])
  have hFixedZ : L' (Matrix.single 0 0 1 - Matrix.single 1 1 1) =
      Matrix.single 0 0 1 - Matrix.single 1 1 1 := by
    have h : L' (F D) = F D := by
      rw [hConj]
      congr 1
      change (MatrixMap.of_kraus K K) (A - B) = A - B
      rw [map_sub, hLA, hLB]
    rw [hZ, map_smul] at h
    exact smul_right_injective _ hzne h
  have hA' : A'.IsHermitian := by
    change star (F A) = F A
    rw [← map_star, Matrix.star_eq_conjTranspose, hA.isHermitian.eq]
  have hA'01 : A' 0 1 ≠ 0 := by
    intro hz
    have hz' : A' 1 0 = 0 := by rw [← hA'.apply 1 0, hz, star_zero]
    have hA'diag : A' = Matrix.diagonal (fun i => A' i i) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz, hz']
    have hD' : A' - B' = Matrix.diagonal z := by
      simpa only [D, map_sub, A', B'] using hdiag
    have hB' : B' = Matrix.diagonal (fun i => A' i i - z i) := by
      have h : B' = A' - Matrix.diagonal z := by rw [← hD']; abel
      calc
        B' = A' - Matrix.diagonal z := h
        _ = _ := by nth_rw 1 [hA'diag]; rw [← Matrix.diagonal_sub]
    apply hAB
    apply F.injective
    rw [map_mul, map_mul]
    change A' * B' = B' * A'
    rw [hB', hA'diag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun i => mul_comm _ _)
  have hL' : L' = LinearMap.id :=
    identity_in_eigenbasis _ hTP' A' hA' hA'01 ((hConj A).trans (congrArg F hLA)) hFixedZ
  apply LinearMap.ext
  intro X
  apply F.injective
  change F (L X) = F X
  rw [← hConj, hL']
  rfl

#print axioms cptp_eq_id_of_noncommuting_fixed_pair

section PhysicalChannel

open scoped TensorProduct
open D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 2000000 in
-- The canonical pointwise theorem has dependent spectral subspaces and tensor instances.
/-- If an actual CPTP recovery restores two states with noncommuting qubit
outputs, the physical channel is a partial trace in tensor coordinates
whenever one restored state is faithful. The same environment state gives
the product recovery on all qubit matrices. The last equality characterizes
the partial trace by its trace pairing with every qubit observable. -/
theorem tensor_form_of_noncommuting_qubit_recovery
    (Φ : MatrixMap n (Fin 2) ℂ) (R : MatrixMap (Fin 2) n ℂ)
    (hΦcp : Φ.IsCompletelyPositive) (hΦtp : Φ.IsTracePreserving)
    (hRcp : R.IsCompletelyPositive) (hRtp : R.IsTracePreserving)
    (S T : Matrix n n ℂ) (hS : S.PosDef) (hT : T.PosSemidef)
    (hSt : S.trace = 1) (hTt : T.trace = 1)
    (hrecS : R (Φ S) = S) (hrecT : R (Φ T) = T)
    (hnc : Φ S * Φ T ≠ Φ T * Φ S) :
    Φ.comp R = LinearMap.id ∧
    ∃ K : Submodule ℂ (EuclideanSpace ℂ n),
      letI : NormedAddCommGroup (K ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :=
        TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := K) (F := EuclideanSpace ℂ (Fin 2))
      letI : InnerProductSpace ℂ (K ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) :=
        TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := K) (F := EuclideanSpace ℂ (Fin 2))
      ∃ (U : (K ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) →ₗ[ℂ] EuclideanSpace ℂ n)
        (κ : K →ₗ[ℂ] K),
        (LinearMap.adjoint U).comp U = LinearMap.id ∧
        U.comp (LinearMap.adjoint U) = LinearMap.id ∧
        κ.IsPositive ∧
        (∀ w : K, w ≠ 0 → 0 < (inner ℂ w (κ w)).re) ∧
        LinearMap.trace ℂ K κ = 1 ∧
        (∀ Z : Qubit, (R Z).toEuclideanLin =
          (U.comp (TensorProduct.map κ Z.toEuclideanLin)).comp (LinearMap.adjoint U)) ∧
        (∀ (X : Matrix n n ℂ) (Z : Qubit),
          (Φ X * Z).trace = LinearMap.trace ℂ (EuclideanSpace ℂ n)
            (X.toEuclideanLin.comp
              ((U.comp (TensorProduct.map LinearMap.id Z.toEuclideanLin)).comp
                (LinearMap.adjoint U)))) := by
  classical
  obtain ⟨E, hE⟩ := MatrixMap.IsCompletelyPositive.exists_kraus R hRcp
  obtain ⟨A, hA⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Φ hΦcp
  have hR (Z : Qubit) : R Z = ∑ a, E a * Z * (E a)ᴴ := by
    rw [hE, MatrixMap.of_kraus_apply]
  have hΦ (X : Matrix n n ℂ) : Φ X = ∑ b, A b * X * (A b)ᴴ := by
    rw [hA, MatrixMap.of_kraus_apply]
  have hETP : ∑ a, (E a)ᴴ * E a = 1 :=
    Original8340Global.kraus_normalization_from_actual_trace E fun X => hR X ▸ hRtp X
  have hATP : ∑ b, (A b)ᴴ * A b = 1 :=
    Original8340Global.kraus_normalization_from_actual_trace A fun X => hΦ X ▸ hΦtp X
  let J (p : (Fin 2 × n) × (n × Fin 2)) := A p.1 * E p.2
  have hJE (Z : Qubit) : (Φ.comp R) Z = MatrixMap.of_kraus J J Z := by
    change Φ (R Z) = MatrixMap.of_kraus J J Z
    rw [hΦ, hR]
    simp only [MatrixMap.of_kraus_apply, J, Fintype.sum_prod_type, Matrix.conjTranspose_mul,
      Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
  have hJ : MatrixMap.IsCompletelyPositive (Φ.comp R) := by
    rw [LinearMap.ext hJE]
    exact MatrixMap.of_kraus_isCompletelyPositive J
  have hleftMap : Φ.comp R = LinearMap.id :=
    cptp_eq_id_of_noncommuting_fixed_pair (Φ.comp R) hJ
      (fun Z => (hΦtp (R Z)).trans (hRtp Z)) (Φ S) (Φ T)
      (hΦ _ ▸ Matrix.nonneg_iff_posSemidef.mp
        (Finset.sum_nonneg fun b _ => (hS.posSemidef.mul_mul_conjTranspose_same (A b)).nonneg))
      (hΦ _ ▸ Matrix.nonneg_iff_posSemidef.mp
        (Finset.sum_nonneg fun b _ => (hT.mul_mul_conjTranspose_same (A b)).nonneg))
      ((hΦtp S).trans hSt) ((hΦtp T).trans hTt) hnc
      (congrArg Φ hrecS) (congrArg Φ hrecT)
  refine ⟨hleftMap, ?_⟩
  have hleft (Z : Qubit) :
      (∑ b, A b * (∑ a, E a * Z * (E a)ᴴ) * (A b)ᴴ) = Z := by
    rw [← hR, ← hΦ]
    exact DFunLike.congr_fun hleftMap Z
  have hn : Nonempty n := by
    by_contra h
    let : IsEmpty n := not_nonempty_iff.mp h
    simp at hSt
  let : Nonempty n := hn
  obtain ⟨Θ, _, κ, _, _, _, _, hΘadj, hjL, hjR, _, _, _, hκ, hκpos, _, _, hκtr,
    _, hfactor, _⟩ :=
    Original8340InheritedCoreAttempt.whole_pointwise_core_attempt E hETP A hATP hleft 0 0
  obtain ⟨_, _, hQY, _, _, hSandwich, _, _, hsupport⟩ :=
    kraus_left_inverse_spectral_relations E A hATP hleft 0
  let Q := ∑ a, E a * (E a)ᴴ
  let P := spectralSupport Q
  let W := spectralInverseSqrt Q
  have hP : P = 1 := by
    have hPS : P * S = S := by
      rw [← hrecS, hR]
      exact hsupport (Φ S)
    have hSInv : S * S⁻¹ = 1 :=
      Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit)
    calc
      P = P * (S * S⁻¹) := by rw [hSInv, Matrix.mul_one]
      _ = 1 := by rw [← Matrix.mul_assoc, hPS, hSInv]
  let K := LinearMap.range
    ((W * (∑ a, E a * (Matrix.single 0 0 1 : Qubit) * (E a)ᴴ) * W).toEuclideanLin)
  let E0 := LinearMap.range P.toEuclideanLin
  let U : (K ⊗[ℂ] EuclideanSpace ℂ (Fin 2)) →ₗ[ℂ] EuclideanSpace ℂ n :=
    E0.subtype.comp Θ.toLinearMap
  have hUadj : LinearMap.adjoint U =
      Θ.symm.toLinearMap.comp (LinearMap.adjoint E0.subtype) := by
    change LinearMap.adjoint (E0.subtype.comp Θ.toLinearMap) = _
    rw [LinearMap.adjoint_comp, hΘadj]
  have hUL : (LinearMap.adjoint U).comp U = LinearMap.id := by
    rw [hUadj]
    apply LinearMap.ext
    intro z
    change Θ.symm (LinearMap.adjoint E0.subtype (E0.subtype (Θ z))) = z
    have hj : LinearMap.adjoint E0.subtype (E0.subtype (Θ z)) = Θ z :=
      DFunLike.congr_fun hjL (Θ z)
    rw [hj, Θ.symm_apply_apply]
  have hUR : U.comp (LinearMap.adjoint U) = LinearMap.id := by
    rw [hUadj]
    apply LinearMap.ext
    intro x
    change E0.subtype (Θ (Θ.symm (LinearMap.adjoint E0.subtype x))) = x
    rw [Θ.apply_symm_apply]
    have hj : E0.subtype (LinearMap.adjoint E0.subtype x) = P.toEuclideanLin x :=
      DFunLike.congr_fun hjR x
    rw [hj, hP]
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_one] using (LinearMap.id_apply x)
  have hRform (Z : Qubit) : (R Z).toEuclideanLin =
      (U.comp (TensorProduct.map κ Z.toEuclideanLin)).comp (LinearMap.adjoint U) := by
    rw [hR]
    exact hfactor Z
  refine ⟨K, U, κ, hUL, hUR, hκ, hκpos, hκtr, hRform, ?_⟩
  have hQform : Q.toEuclideanLin =
      (U.comp (TensorProduct.map κ LinearMap.id)).comp (LinearMap.adjoint U) := by
    have hQ : Q = R 1 := by simp [Q, hR, Matrix.mul_one]
    rw [hQ, hRform]
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_one]
  have hQinv : (W * W) * Q = 1 := by
    have hWQ : W * Q = Q * W :=
      ((Commute.refl Q).cfc_real (fun x : ℝ => (Real.sqrt x)⁻¹)).eq
    rw [Matrix.mul_assoc, hWQ, ← Matrix.mul_assoc, show W * Q * W = P from hSandwich, hP]
  intro X Z
  let V := (U.comp (TensorProduct.map LinearMap.id Z.toEuclideanLin)).comp (LinearMap.adjoint U)
  have hQcancel : Function.Injective (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n =>
      Q.toEuclideanLin.comp f) := by
    intro f g hfg
    have h := congrArg (fun B => (W * W).toEuclideanLin.comp B) hfg
    simpa only [← LinearMap.comp_assoc, Matrix.toEuclideanLin, ← Matrix.toLpLin_mul_same,
      hQinv, Matrix.toLpLin_one, LinearMap.id_comp] using h
  have hYZ : (leftInverseObservable A Z).toEuclideanLin = V := by
    apply hQcancel
    change Q.toEuclideanLin.comp (leftInverseObservable A Z).toEuclideanLin =
      Q.toEuclideanLin.comp V
    have hQYZ : Q * leftInverseObservable A Z = R Z := (hQY Z).trans (hR Z).symm
    calc
      _ = (R Z).toEuclideanLin := by
        rw [← hQYZ]
        exact (Matrix.toLpLin_mul_same 2 Q (leftInverseObservable A Z)).symm
      _ = Q.toEuclideanLin.comp V := by
        rw [hRform, hQform]
        apply LinearMap.ext
        intro x
        let y := TensorProduct.map LinearMap.id Z.toEuclideanLin (LinearMap.adjoint U x)
        change U (TensorProduct.map κ Z.toEuclideanLin (LinearMap.adjoint U x)) =
          U (TensorProduct.map κ LinearMap.id (LinearMap.adjoint U (U y)))
        have hy : LinearMap.adjoint U (U y) = y := DFunLike.congr_fun hUL y
        rw [hy]
        congr 1
        have hm := TensorProduct.map_comp κ LinearMap.id LinearMap.id Z.toEuclideanLin
        rw [LinearMap.comp_id, LinearMap.id_comp] at hm
        exact DFunLike.congr_fun hm (LinearMap.adjoint U x)
  change (Φ X * Z).trace = LinearMap.trace ℂ (EuclideanSpace ℂ n) (X.toEuclideanLin.comp V)
  rw [← hYZ, ← Matrix.toLpLin_mul_same]
  change (Φ X * Z).trace = LinearMap.trace ℂ (EuclideanSpace ℂ n)
    ((X * leftInverseObservable A Z).toEuclideanLin)
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq, hΦ]
  simpa only [leftInverseObservable] using FixedPointProjection.Kraus.rawPair A X Z

end PhysicalChannel

#print axioms tensor_form_of_noncommuting_qubit_recovery

end D5.S3.Quantum.Recovery.NoncommutingQubit
