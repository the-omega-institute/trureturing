/- GID: D5/S3/Quantum/Recovery/NoncommutingQubit/FixedPair
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/NoncommutingQubit/FixedPair
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: A finite qubit channel fixing a noncommuting pair is the identity. -/

import D5.S3.Quantum.Recovery.ActualChannelAlgebra

noncomputable section

open Matrix PhyslibLeaf
open scoped Matrix BigOperators

namespace D5.S3.Quantum.Recovery.NoncommutingQubit

set_option autoImplicit false
set_option relaxedAutoImplicit false

local notation "Qubit" => Matrix (Fin 2) (Fin 2) ℂ

private theorem kraus_apply {n d s : Type*} [Fintype d] [Fintype s]
    (K : s → Matrix n d ℂ) (X : Matrix d d ℂ) :
    MatrixMap.of_kraus K K X = ∑ a, K a * X * (K a)ᴴ := by
  simp only [MatrixMap.of_kraus, LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- Vanishing weight on the other eigenline forces each Kraus entry to vanish there. -/
private theorem eigenline_weight {s : Type*} [Fintype s] (K : s → Qubit) (i j : Fin 2) :
    (MatrixMap.of_kraus K K (Matrix.single j j 1) i i).re =
      ∑ a, Complex.normSq (K a i j) := by
  rw [kraus_apply, Matrix.sum_apply, Finset.sum_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_assoc, Matrix.single_mul_apply_same]
  simp only [Matrix.mul_apply, Matrix.single, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [Complex.mul_conj, ← starRingEnd_apply]

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
    rw [kraus_apply, Matrix.sum_apply, Finset.sum_apply, Finset.sum_mul]
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
    · have hn : A i j ≠ 0 := by fin_cases i <;> fin_cases j <;> simp_all
      have h : L A i j = A i j := congrArg (fun M : Qubit => M i j) hFix
      rw [hschur, ← one_mul (A i j)] at h
      exact mul_right_cancel₀ hn h
  ext X i j
  change L X i j = X i j
  rw [hschur, hc, one_mul]

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
    rw [kraus_apply, kraus_apply, map_sum]
    simp only [map_mul, ← Matrix.star_eq_conjTranspose, map_star]
  have traceF (X : Qubit) : (F X).trace = X.trace := by
    change (star (hD.eigenvectorUnitary : Qubit) * X * hD.eigenvectorUnitary.val).trace = _
    rw [Matrix.trace_mul_cycle, ← Unitary.coe_star, Unitary.coe_mul_star_self, Matrix.one_mul]
  have hTP' : L'.IsTracePreserving := by
    intro Y
    obtain ⟨X, rfl⟩ := F.surjective Y
    rw [hConj, traceF, traceF]
    exact hTP X
  let z : Fin 2 → ℂ := fun i => (hD.eigenvalues i : ℂ)
  have hdiag : F D = Matrix.diagonal z := by
    conv_lhs => rw [hD.spectral_theorem]
    exact F.symm_apply_apply _
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
    have hd : D = 0 := F.injective (by simp [hZ, hz])
    have heq : A = B := sub_eq_zero.mp hd
    exact hAB (by rw [heq])
  have hFixedZ : L' (Matrix.single 0 0 1 - Matrix.single 1 1 1) =
      Matrix.single 0 0 1 - Matrix.single 1 1 1 := by
    have h : L' (F D) = F D := by rw [hConj]; congr 1; simp [D, L, hLA, hLB]
    rw [hZ, map_smul, ← smul_sub] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left hzne)
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
      rw [h]
      conv_lhs => rw [hA'diag, ← Matrix.diagonal_sub]
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
  rw [← hConj, hL']
  rfl

#print axioms cptp_eq_id_of_noncommuting_fixed_pair

end D5.S3.Quantum.Recovery.NoncommutingQubit
