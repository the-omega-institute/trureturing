/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveFourth/SpectrumEndpoint
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lift the four-copy polynomial signs to spectra of cardinality at most three. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveFourth.PolynomialSupport
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumProduct
import Mathlib.Data.Finset.Sort

/-! Pad the finite spectrum with positive values and apply the appropriate
four-copy bound to its ordered three-value superset. -/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace RefinedBMV.ThreeBlockGram.PositiveSpectrum

private theorem exists_ordered_triple (S : Finset ℝ)
    (hS : ∀ a ∈ S, 0 ≤ a) (hc : S.card ≤ 3) :
    ∃ s : Fin 3 → ℝ, StrictMono s ∧ (∀ i, 0 ≤ s i) ∧
      ∀ a ∈ S, ∃ i, s i = a := by
  classical
  let T := insert (0 : ℝ) S
  let m := T.max' (Finset.insert_nonempty _ _)
  have hm : 0 ≤ m := Finset.le_max' T _ (Finset.mem_insert_self _ _)
  let U : Finset ℝ := {m + 1, m + 2, m + 3}
  have hu : U.card = 3 := Finset.card_eq_three.mpr
    ⟨m + 1, m + 2, m + 3, by linarith, by linarith, by linarith, rfl⟩
  have hSU : S ⊆ S ∪ U := Finset.subset_union_left
  have hUS : U ⊆ S ∪ U := Finset.subset_union_right
  obtain ⟨V, hSV, hVU, hV⟩ := Finset.exists_subsuperset_card_eq
    hSU hc (hu.symm.le.trans (Finset.card_le_card hUS))
  let s := V.orderEmbOfFin hV
  refine ⟨s, s.strictMono, ?_, ?_⟩
  · intro i
    rcases Finset.mem_union.mp (hVU (V.orderEmbOfFin_mem hV i)) with h | h
    · exact hS (s i) h
    · simp only [U, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h | h <;> linarith
  · intro a ha
    have h : a ∈ Set.range s := by
      simpa only [s, Finset.range_orderEmbOfFin, Finset.mem_coe] using hSV ha
    exact h

theorem product_bound_of_three_value_signs {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (hp : 0 < p) (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hcard : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 3)
    (hunit : ∀ r t : ℝ, 0 < r → r < 1 → 0 < t → t < 1 →
      (kernelQuarticData (fun i j k l ↦
        2 * spectralDefect p ![r^4*t^4, t^4, 1] i j k l)).SixSigns) :
    trace (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ FourCopyGap.wordMean p A B := by
  classical
  obtain ⟨s, horder, hs, hcover⟩ := exists_ordered_triple
    (Finset.univ.image hA.isHermitian.eigenvalues)
    (by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hA.eigenvalues_nonneg i) hcard
  have hmem (i : n) : ∃ j : Fin 3, hA.isHermitian.eigenvalues i = s j := by
    obtain ⟨j, hj⟩ := hcover _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    exact ⟨j, hj.symm⟩
  rcases (hs 0).eq_or_lt with hz | hpos
  · have h01 := horder (show (0 : Fin 3) < 1 by decide)
    have h12 := horder (show (1 : Fin 3) < 2 by decide)
    have h₁ : 0 < s 1 := hz.trans_lt h01
    have htriple : s = ![0, s 1, s 2] := by
      funext i
      fin_cases i <;> simp [hz.symm]
    exact ZeroSpectrum.product_bound_scaled_zero_spectrum p hp h₁ h12 A B hA hB
      (by simpa only [← htriple] using hmem)
  · have hpositive (i : Fin 3) : 0 < s i := hpos.trans_le (horder.monotone (Fin.zero_le _))
    have hbinary (i j : Fin 3) (hij : i < j) :
        (g (spectralDefect p s) i j)^2 < 2 * f (spectralDefect p s) i j *
          f (spectralDefect p s) j i :=
      spectralDefect_binary_conditioning p hp s i j (hpositive i) (hpositive j)
        (horder.injective.ne hij.ne)
    apply product_bound_of_spectrum_subset_of_sharpSupport p A B hA hB s hs hmem hbinary
    apply sharpSupport_of_normalized_positive_spectrum p s hpositive horder
    intro r t hr hr1 ht ht1
    let v : Fin 3 → ℝ := ![r^4*t^4, t^4, 1]
    have hv01 : v 0 < v 1 := by
      change r^4 * t^4 < t^4
      simpa using mul_lt_mul_of_pos_right
        (show r^4 < (1 : ℝ) by simpa using pow_lt_pow_left₀ hr1 hr.le (by decide : 4 ≠ 0))
        (pow_pos ht 4)
    have hv12 : v 1 < v 2 := by
      change t^4 < (1 : ℝ)
      simpa using pow_lt_pow_left₀ ht1 ht.le (by decide : 4 ≠ 0)
    have hv (i : Fin 3) : 0 < v i := by
      fin_cases i <;> simp [v] <;> positivity
    have hvorder : StrictMono v := by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      fin_cases i
      · exact hv01
      · exact hv12
    exact sharpSupport_of_positive_spectrum_signs p hp v hv hvorder
      (hunit r t hr hr1 ht ht1)

end RefinedBMV.ThreeBlockGram.PositiveSpectrum
