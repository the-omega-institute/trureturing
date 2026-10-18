/- GID: D5/S3/Quantum/Schatten/ExpandingDiagonal
   generality: G
   mirror-B: D5/B/S3/Quantum/Schatten/ExpandingDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite matching minimizes diagonal products over expanding matrices. -/

import D5.S3.Quantum.Schatten.UnitarilyInvariantNorm
import D5.S3.Quantum.Schatten.PowerMajorization
import D5.S3.Quantum.Schatten.UINormContinuity
import D5.S3.Quantum.Schatten.LowerGelfandNaimark
import D5.S3.Quantum.Schatten.ExpandingGram
import D5.S3.Quantum.Schatten.DiagonalSingularValues
import Mathlib.Data.Fin.Tuple.Sort

/-! Subset log-majorization gives the opposite-matching bound for expanding diagonal products. -/

noncomputable section
open Matrix Finset
open scoped BigOperators Topology ComplexOrder
namespace D5.S3.Quantum.Schatten

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Geometry.AlphaGeometry.MajorizationTransfer.FiniteVector

private def sortedSV {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℝ :=
  singularValuesSorted X ⟨i.val, by simpa only [Fintype.card_fin] using i.isLt⟩

private theorem N_eq_sortedSV {n : ℕ} (ν : UINorm n)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ν.N X = ν.N (diagonal (fun i => (sortedSV X i : ℂ))) := by
  obtain ⟨ρ, hρ⟩ := exists_sorting_equiv X
  let e : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv
  let σ : Equiv.Perm (Fin n) := e.trans ρ
  have hσ (i : Fin n) : singularValues X (σ i) = sortedSV X i := hρ (e i)
  rw [ν.N_eq_singularValues X, ← ν.N_diagonal_perm (singularValues X) σ]
  congr 2
  funext i
  exact congrArg Complex.ofReal (hσ i)

private theorem prefixSum_eq_fin_sum {n k : ℕ} (x : Fin n → ℝ) (hk : k ≤ n) :
    prefixSum k x = ∑ i : Fin k, x ⟨i.val, by omega⟩ := by
  unfold prefixSum
  apply Finset.sum_bij (fun i hi => (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin k))
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun q : Fin k => q.val) hij)
  · intro j hj
    refine ⟨⟨j.val, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.isLt
  · intro i hi; rfl

private theorem prefixProduct_congr {n k l : ℕ} (x : Fin n → ℝ)
    (h : k = l) (hk : k ≤ n) (hl : l ≤ n) :
    (∏ j : Fin k, x ⟨j.val, by omega⟩) =
      ∏ j : Fin l, x ⟨j.val, by omega⟩ := by
  subst l
  rfl

/-- Bounds on all coordinate-subset products control every unitarily invariant diagonal gauge. -/
theorem UINorm.N_diagonal_subsetProducts_le {n : ℕ} (ν : UINorm n)
    (x y : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hyanti : Antitone y)
    (hprod : ∀ I : Finset (Fin n),
      (∏ i ∈ I, x i) ≤ ∏ j : Fin I.card, y ⟨j.val, by
        have h := Finset.card_le_card (Finset.subset_univ I)
        simp only [Finset.card_univ, Fintype.card_fin] at h
        omega⟩) :
    ν.N (diagonal (fun i => (x i : ℂ))) ≤
      ν.N (diagonal (fun i => (y i : ℂ))) := by
  classical
  let σ : Equiv.Perm (Fin n) := Tuple.sort (α := OrderDual ℝ) x
  let z : Fin n → ℝ := fun i => x (σ i)
  have hzanti : Antitone z := Tuple.monotone_sort (α := OrderDual ℝ) x
  have hz : ∀ i, 0 ≤ z i := fun i => hx (σ i)
  have hp (k : ℕ) (hk : k ≤ n) :
      (∏ j : Fin k, z ⟨j.val, by omega⟩) ≤
        ∏ j : Fin k, y ⟨j.val, by omega⟩ := by
    let e : Fin k ↪ Fin n :=
      ⟨fun i => σ ⟨i.val, by omega⟩, fun i j hij =>
        Fin.ext (congrArg (fun q : Fin n => q.val) (σ.injective hij))⟩
    have hh := hprod (Finset.univ.map e)
    have hcard : (Finset.univ.map e).card = k := by simp
    rw [prefixProduct_congr y hcard (by omega) hk] at hh
    simpa only [Finset.prod_map,
      Function.Embedding.coeFn_mk, z, e] using hh
  have hsum (k : ℕ) (hk : k ≤ n) :
      (∑ j : Fin k, z ⟨j.val, by omega⟩) ≤
        ∑ j : Fin k, y ⟨j.val, by omega⟩ := by
    apply weak_log_maj_sum_le (n := k)
      (fun i : Fin k => hz ⟨i.val, by omega⟩) (fun i : Fin k => hy ⟨i.val, by omega⟩)
      (fun i j hij => hzanti hij) (fun i j hij => hyanti hij)
    intro l hl
    exact hp l (hl.trans hk)
  have hpre (k : ℕ) : prefixSum k z ≤ prefixSum k y := by
    by_cases hk : k ≤ n
    · simpa only [prefixSum_eq_fin_sum _ hk] using hsum k hk
    · rw [prefixSum_eq_full_sum_of_le z (by omega),
        prefixSum_eq_full_sum_of_le y (by omega)]
      simpa only [prefixSum_eq_fin_sum _ le_rfl,
        prefixSum_eq_full_sum_of_le _ le_rfl] using
        (show prefixSum n z ≤ prefixSum n y by
          simpa only [prefixSum_eq_fin_sum _ le_rfl] using hsum n le_rfl)
  have h := ν.N_diagonal_weakMajorization z y hzanti hz hy hpre
  simpa only [z, ν.N_diagonal_perm x σ] using h

private theorem diagonal_lower_of_positive_perturbations {n : ℕ} (ν : UINorm n)
    (a b : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (T : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ ε : ℝ, 0 < ε →
      ν.N (diagonal (fun i => ((a i + ε : ℝ) : ℂ)) * σ.permMatrix ℂ *
        diagonal (fun i => ((b i + ε : ℝ) : ℂ))) ≤
      ν.N (diagonal (fun i => ((a i + ε : ℝ) : ℂ)) * T *
        diagonal (fun i => ((b i + ε : ℝ) : ℂ)))) :
    ν.N (diagonal (fun i => (a i : ℂ)) * σ.permMatrix ℂ *
      diagonal (fun i => (b i : ℂ))) ≤
      ν.N (diagonal (fun i => (a i : ℂ)) * T * diagonal (fun i => (b i : ℂ))) := by
  have hA : Continuous (fun ε : ℝ => diagonal (fun i : Fin n =>
      ((a i + ε : ℝ) : ℂ))) :=
    (continuous_pi fun i => Complex.continuous_ofReal.comp
      (continuous_const.add continuous_id)).matrix_diagonal
  have hB : Continuous (fun ε : ℝ => diagonal (fun i : Fin n =>
      ((b i + ε : ℝ) : ℂ))) :=
    (continuous_pi fun i => Complex.continuous_ofReal.comp
      (continuous_const.add continuous_id)).matrix_diagonal
  have hleft : Continuous (fun ε : ℝ =>
      ν.N (diagonal (fun i => ((a i + ε : ℝ) : ℂ)) * σ.permMatrix ℂ *
        diagonal (fun i => ((b i + ε : ℝ) : ℂ)))) :=
    ν.continuous_N.comp ((hA.mul continuous_const).mul hB)
  have hright : Continuous (fun ε : ℝ =>
      ν.N (diagonal (fun i => ((a i + ε : ℝ) : ℂ)) * T *
        diagonal (fun i => ((b i + ε : ℝ) : ℂ)))) :=
    ν.continuous_N.comp ((hA.mul continuous_const).mul hB)
  have hL := hleft.tendsto 0
  have hR := hright.tendsto 0
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ν.N (diagonal (fun i => ((a i + ε : ℝ) : ℂ)) * σ.permMatrix ℂ *
        diagonal (fun i => ((b i + ε : ℝ) : ℂ))) ≤
      ν.N (diagonal (fun i => ((a i + ε : ℝ) : ℂ)) * T *
        diagonal (fun i => ((b i + ε : ℝ) : ℂ))) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h ε hε
  simpa only [add_zero] using le_of_tendsto_of_tendsto
    (hL.mono_left nhdsWithin_le_nhds) (hR.mono_left nhdsWithin_le_nhds) hevent

private theorem positive_diagonal_expanding_lower {n : ℕ} (ν : UINorm n)
    (a b : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (α β : Equiv.Perm (Fin n)) (hα : Antitone (a ∘ α)) (hβ : Monotone (b ∘ β))
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : (Tᴴ * T - 1).PosSemidef) :
    ν.N (diagonal (fun i => ((a (α i) * b (β i) : ℝ) : ℂ))) ≤
      ν.N (diagonal (fun i => (a i : ℂ)) * T * diagonal (fun i => (b i : ℂ))) := by
  classical
  let A := diagonal (fun i => (a i : ℂ))
  let B := diagonal (fun i => (b i : ℂ))
  let D := diagonal (fun i => (((b i)⁻¹ : ℝ) : ℂ))
  let C := A * T * B
  let c : Fin n → ℝ := fun i => a (α i) * b (β i)
  let e : Fin n ↪ Fin (Fintype.card (Fin n)) :=
    (Fin.castOrderIso (Fintype.card_fin n).symm).toEquiv.toEmbedding
  have hA : IsUnit A.det := by
    rw [show A.det = ∏ i, (a i : ℂ) from det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      Complex.ofReal_ne_zero.mpr (ha i).ne')
  have hB : IsUnit B.det := by
    rw [show B.det = ∏ i, (b i : ℂ) from det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      Complex.ofReal_ne_zero.mpr (hb i).ne')
  have hD : IsUnit D.det := by
    rw [show D.det = ∏ i, (((b i)⁻¹ : ℝ) : ℂ) from det_diagonal]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ =>
      Complex.ofReal_ne_zero.mpr (inv_pos.mpr (hb i)).ne')
  have hC : IsUnit C.det := by
    simpa only [C, det_mul] using (hA.mul (expanding_isUnit_det T hT)).mul hB
  have hBD : B * D = 1 := by
    have hentry (i : Fin n) : (b i : ℂ) * (((b i)⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hb i).ne', Complex.ofReal_one]
    simp only [B, D, diagonal_mul_diagonal, hentry, diagonal_one]
  have hCD : C * D = A * T := by
    simp only [C, Matrix.mul_assoc, hBD, Matrix.mul_one]
  have hβinv : Antitone ((fun i => (b i)⁻¹) ∘ β) := by
    intro i j hij
    exact inv_anti₀ (hb (β i)) (hβ hij)
  have hpoint (i : Fin n) : c i ≤
      singularValuesSorted (C * D) (e i) / singularValuesSorted D (e i) := by
    have hdom := expanding_right_singularValuesSorted A T hT (e i)
    rw [show singularValuesSorted A (e i) = a (α i) from
      singularValuesSorted_diagonal_of_antitone_perm a (fun i => (ha i).le) α hα (e i)]
      at hdom
    rw [hCD, show singularValuesSorted D (e i) = (b (β i))⁻¹ from
      singularValuesSorted_diagonal_of_antitone_perm (fun i => (b i)⁻¹)
        (fun i => (inv_pos.mpr (hb i)).le) β hβinv (e i), div_inv_eq_mul]
    exact mul_le_mul_of_nonneg_right hdom (hb (β i)).le
  change ν.N (diagonal (fun i => (c i : ℂ))) ≤ ν.N C
  rw [N_eq_sortedSV ν C]
  apply ν.N_diagonal_subsetProducts_le c (sortedSV C)
    (fun i => mul_nonneg (ha _).le (hb _).le)
    (fun i => singularValuesSorted_nonneg C (e i))
    (fun i j hij => singularValuesSorted_antitone C hij)
  intro I
  have hr := lower_gelfand_naimark_ratio C D hC hD (I.map e)
  have hprod : (∏ i ∈ I, c i) ≤
      ∏ i ∈ I.map e, singularValuesSorted (C * D) i / singularValuesSorted D i := by
    rw [Finset.prod_map]
    exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg (ha _).le (hb _).le)
      (fun i _ => hpoint i)
  have hcard : (I.map e).card = I.card := Finset.card_map _
  rw [prefixProduct_congr (singularValuesSorted C) hcard (by
    have h := Finset.card_le_card (Finset.subset_univ (I.map e))
    simpa only [Finset.card_univ, Fintype.card_fin] using h) (by
      have h := Finset.card_le_card (Finset.subset_univ I)
      simpa only [Finset.card_univ, Fintype.card_fin] using h)] at hr
  exact hprod.trans hr

/-- A single permutation minimizes nonnegative diagonal products over all expanding factors. -/
theorem UINorm.exists_permutation_expanding_lower_bound {n : ℕ} (ν : UINorm n)
    (a b : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∃ σ : Equiv.Perm (Fin n), ∀ T : Matrix (Fin n) (Fin n) ℂ,
      (Tᴴ * T - 1).PosSemidef →
      ν.N (diagonal (fun i => (a i : ℂ)) * σ.permMatrix ℂ *
        diagonal (fun i => (b i : ℂ))) ≤
      ν.N (diagonal (fun i => (a i : ℂ)) * T * diagonal (fun i => (b i : ℂ))) := by
  let α : Equiv.Perm (Fin n) := Tuple.sort (α := OrderDual ℝ) a
  let β : Equiv.Perm (Fin n) := Tuple.sort b
  let σ : Equiv.Perm (Fin n) := α.symm.trans β
  have hα : Antitone (a ∘ α) := Tuple.monotone_sort (α := OrderDual ℝ) a
  have hβ : Monotone (b ∘ β) := Tuple.monotone_sort b
  refine ⟨σ, fun T hT => ?_⟩
  apply diagonal_lower_of_positive_perturbations ν a b σ T
  intro ε hε
  have h := positive_diagonal_expanding_lower ν (fun i => a i + ε)
    (fun i => b i + ε) (fun i => by linarith [ha i]) (fun i => by linarith [hb i])
    α β (fun i j hij => add_le_add (hα hij) le_rfl)
    (fun i j hij => add_le_add (hβ hij) le_rfl) T hT
  have heq : ν.N (diagonal (fun i => ((a i + ε : ℝ) : ℂ)) * σ.permMatrix ℂ *
      diagonal (fun i => ((b i + ε : ℝ) : ℂ))) =
      ν.N (diagonal (fun i => (((a (α i) + ε) * (b (β i) + ε) : ℝ) : ℂ))) := by
    rw [ν.N_diagonal_permMatrix]
    have hh := ν.N_diagonal_perm (fun i => (a i + ε) * (b (σ i) + ε)) α
    simpa only [σ, Equiv.trans_apply, Equiv.symm_apply_apply] using hh.symm
  exact heq.le.trans h

end D5.S3.Quantum.Schatten
