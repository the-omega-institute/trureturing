/- GID: D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Energy/OriginalNeutralEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original neutral word estimates and orthogonal finite energy recombination. -/

import D5.S3.VertexAlgebra.Energy.OriginalWordEnergy

/-! Neutral normal-product words and orthogonal energy recombination.

These are the original consumed proof components of OriginalChargedEnergy:
the zero-charge specialization of the shared seed-parametrized word induction and
recombination of every finite energy component using the actual Sugawara mode.
No field, metric, support restriction or energy exponent is changed by the split.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator Matrix
open ComplexConjugate

namespace D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

open LatticeGeneratingFieldLocality LatticeInvolution LatticePositiveEnergy
open SourceBPZ.OriginalMatterHermitian SourceBPZ.OriginalSourcePairing
open SourceBPZ.TransverseHermitian OriginalGram
open LatticeSugawaraCurrents LatticeAllStateField LatticeAllStateReconstruction
open LatticeActualGeneratorLocality
open private Hm_finsum_right Hm_finset_sum_left Hm_finset_sum_right from
  D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian

variable {D : LatticeData}

open private normD_sq original_current_energy_le originalCore normD_add_le normD_smul normD_sum_le from
  D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy

open private wordWeight wordOrder wordConstant wordConstant_nonneg
  wordOrder_le occurrence_weight word_mode_grade negative_grade_eq_zero
  derivative_zero_strip word_cons_finite seeded_word_energy_le from
  D5.S3.VertexAlgebra.Energy.OriginalWordEnergy

/-- The existing neutral prerequisite is the zero-charge identity-seed
specialization of the one arbitrary-charge induction. -/
private theorem original_word_energy_le (hD : (gramReal D).PosDef)
    (ω : List (Index D)) : ∀ (E F M : ℕ) (n : ℤ),
    (E : ℤ)+wordWeight ω-n-1=F → E ≤ M → F ≤ M →
    ∀ v : Carrier D, v ∈ grade D (E : ℤ) →
      normD (((wordField D 0 ω)[[n]]) v) ≤
        wordConstant ω * ((M : ℝ)+1)^(wordOrder ω) * normD v := by
  have hseed : ∀ (E F M : ℕ) (n : ℤ),
      (E : ℤ)+chargeEnergy D (0 : Charge D)-n-1=F → E ≤ M → F ≤ M →
      ∀ v : Carrier D, v ∈ grade D (E : ℤ) →
        normD (((actualField D 0)[[n]]) v) ≤
          (1 : ℝ) * ((M : ℝ)+1)^0 * normD v := by
    intro E F M n hEF hE hF v hv
    rw [actual_zero, identity_modes]
    split_ifs <;> simp [normD, Real.sqrt_nonneg]
  simpa only [chargeEnergy_zero, add_zero, zero_add, one_mul] using
    seeded_word_energy_le hD 0 1 (by norm_num) 0 hseed ω

private def neutralConstant (p : Oscillator D) : ℝ :=
  1 + ∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e)

private theorem neutralConstant_pos (p : Oscillator D) : 0 < neutralConstant p := by
  have hn : 0 ≤ ∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e) :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (norm_nonneg _) (wordConstant_nonneg _))
  unfold neutralConstant
  linarith

private theorem neutral_polynomial_expansion (p : Oscillator D) (n : ℤ) (v : Carrier D) :
    ((Y D (Finsupp.single 0 p))[[n]]) v =
      ∑ e ∈ p.support, p.coeff e • (((wordField D 0 (occurrences D e))[[n]]) v) := by
  have hp : p = ∑ e ∈ p.support, p.coeff e • MvPolynomial.monomial e 1 := by
    simpa only [MvPolynomial.smul_monomial, smul_eq_mul, mul_one] using MvPolynomial.as_sum p
  rw [Y_single]
  conv_lhs => rw [hp]
  simp only [map_sum, map_smul, polynomialField_monomial, Finset.sum_apply,
    LinearMap.sum_apply, Pi.smul_apply, LinearMap.smul_apply]

/-- One constant controls every original mixed state in every nonnegative grade. -/
private theorem original_neutral_grade_le (hD : (gramReal D).PosDef)
    (p : Oscillator D) (w : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p w)
    (E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (((Y D (Finsupp.single 0 p))[[(w : ℤ)-1]]) v) ≤
      neutralConstant p * ((E : ℝ)+1)^(2*w) * normD v := by
  classical
  let B := ((E : ℝ)+1)^(2*w)*normD v
  have hvn : 0 ≤ normD v := Real.sqrt_nonneg _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hterm (e : Index D →₀ ℕ) (he : e ∈ p.support) :
      normD (p.coeff e • (((wordField D 0 (occurrences D e))[[(w : ℤ)-1]]) v)) ≤
        (‖p.coeff e‖ * wordConstant (occurrences D e))*B := by
    have hw : wordWeight (occurrences D e) = w := by
      rw [occurrence_weight]
      exact hp (MvPolynomial.mem_support_iff.mp he)
    have ho : wordOrder (occurrences D e) ≤ 2*w := by
      simpa only [hw] using wordOrder_le (occurrences D e)
    have hpow : ((E : ℝ)+1)^(wordOrder (occurrences D e)) ≤ ((E : ℝ)+1)^(2*w) :=
      pow_le_pow_right₀ (by have hn := Nat.cast_nonneg (α := ℝ) E; linarith) ho
    have hword := original_word_energy_le hD (occurrences D e) E E E ((w : ℤ)-1)
      (by rw [hw]; omega) le_rfl le_rfl v hv
    have hword' : normD (((wordField D 0 (occurrences D e))[[(w : ℤ)-1]]) v) ≤
        wordConstant (occurrences D e)*((E : ℝ)+1)^(2*w)*normD v :=
      hword.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (wordConstant_nonneg _)) hvn)
    rw [normD_smul hD]
    exact (mul_le_mul_of_nonneg_left hword' (norm_nonneg _)).trans_eq (by dsimp [B]; ring)
  rw [neutral_polynomial_expansion]
  calc
    _ ≤ ∑ e ∈ p.support,
        normD (p.coeff e • (((wordField D 0 (occurrences D e))[[(w : ℤ)-1]]) v)) :=
      normD_sum_le hD _ _
    _ ≤ ∑ e ∈ p.support, (‖p.coeff e‖ * wordConstant (occurrences D e))*B :=
      Finset.sum_le_sum hterm
    _ = (∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e))*B :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (1+∑ e ∈ p.support, ‖p.coeff e‖ * wordConstant (occurrences D e))*B :=
      mul_le_mul_of_nonneg_right (by linarith) hB
    _ = _ := by dsimp [neutralConstant, B]; ring

private theorem Hm_cauchy_schwarz (hD : (gramReal D).PosDef) (u v : Carrier D) :
    ‖Hm u v‖ ≤ normD u * normD v := by
  letI := originalCore hD
  exact InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℂ) u v

private theorem Hm_grade_orthogonal
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (E F : ℤ) (hEF : E ≠ F) (u v : Carrier D)
    (hu : u ∈ grade D E) (hv : v ∈ grade D F) : Hm u v = 0 := by
  have he := (actualL0_eigen_iff_grade D H hHG hGH E u).mpr hu
  have hf := (actualL0_eigen_iff_grade D H hHG hGH F v).mpr hv
  have hh := Hm_sugawaraMode H hHG hGH 0 u v
  rw [neg_zero, he, hf, Hm_smul_left, Hm_smul_right] at hh
  simp only [map_intCast] at hh
  have hz : ((E : ℂ)-(F : ℂ))*Hm u v=0 := by linear_combination hh
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (by exact_mod_cast hEF))

private theorem normD_orthogonal_sum (hD : (gramReal D).PosDef)
    {ι : Type} (s : Finset ι) (f : ι → Carrier D)
    (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Hm (f i) (f j) = 0) :
    normD (∑ i ∈ s, f i)^2 = ∑ i ∈ s, normD (f i)^2 := by
  classical
  rw [normD_sq hD, Hm_finset_sum_left, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Hm_finset_sum_right, normD_sq hD]
  congr 1
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact hf i hi j hj (Ne.symm hji)
  · exact fun hn => (hn hi).elim

private theorem energy_power_grade
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (E : ℤ) (v : Carrier D) (hv : v ∈ grade D E) (N : ℕ) :
    ((1+sugawaraMode D H 0)^N) v = ((E : ℂ)+1)^N • v := by
  have he := (actualL0_eigen_iff_grade D H hHG hGH E v).mpr hv
  have hs : (1+sugawaraMode D H 0) v = ((E : ℂ)+1) • v := by
    simp only [LinearMap.add_apply, Module.End.one_apply, he, add_smul, one_smul]
    exact add_comm _ _
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hs, smul_smul, pow_succ']
    congr 1
    exact mul_comm _ _

/-- Orthogonal finite energy recombination for the actual energy operator. -/
private theorem energy_bound_of_grades (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (T : Module.End ℂ (Carrier D)) (shift : ℤ) (K : ℝ) (hK : 0 ≤ K) (N : ℕ)
    (hT : ∀ (E : ℤ) (v : Carrier D), v ∈ grade D E → T v ∈ grade D (E+shift))
    (hbound : ∀ (E : ℕ) (v : Carrier D), v ∈ grade D (E : ℤ) →
      normD (T v) ≤ K*((E : ℝ)+1)^N*normD v) (v : Carrier D) :
    normD (T v) ≤ K*normD (((1+sugawaraMode D H 0)^N) v) := by
  classical
  let s := stateEnergies D v
  let f := fun E => gradeProjection D E v
  let R := (1+sugawaraMode D H 0)^N
  have hf (E : ℤ) : f E ∈ grade D E := gradeProjection_mem D E v
  have hr (E : ℤ) : R (f E) ∈ grade D E := by
    rw [energy_power_grade H hHG hGH E _ (hf E) N]
    exact (grade D E).smul_mem _ (hf E)
  have hs : ∑ E ∈ s, f E = v := sum_gradeProjections D v
  have hsumT : normD (T v)^2 = ∑ E ∈ s, normD (T (f E))^2 := by
    calc
      _ = normD (∑ E ∈ s, T (f E))^2 := by rw [← map_sum, hs]
      _ = _ := normD_orthogonal_sum hD s _ (by
        intro E hE F hF hEF
        exact Hm_grade_orthogonal H hHG hGH (E+shift) (F+shift)
          (by omega) _ _ (hT E _ (hf E)) (hT F _ (hf F)))
  have hsumR : normD (R v)^2 = ∑ E ∈ s, normD (R (f E))^2 := by
    calc
      _ = normD (∑ E ∈ s, R (f E))^2 := by rw [← map_sum, hs]
      _ = _ := normD_orthogonal_sum hD s _ (by
        intro E hE F hF hEF
        exact Hm_grade_orthogonal H hHG hGH E F hEF _ _ (hr E) (hr F))
  have hb (E : ℤ) (hE : E ∈ s) : normD (T (f E)) ≤ K*normD (R (f E)) := by
    have hn := stateEnergies_nonneg hD v E hE
    have hc : (E.toNat : ℤ)=E := Int.toNat_of_nonneg hn
    have h := hbound E.toNat (f E) (by rw [hc]; exact hf E)
    have hnormbase : ‖((E : ℂ)+1)‖ = (E.toNat : ℝ)+1 := by
      have hc' : ((E : ℂ)+1)=((E.toNat+1 : ℕ) : ℂ) := by
        rw [← hc]
        push_cast
        rfl
      rw [hc', Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
    have hnorm : normD (R (f E)) = ((E.toNat : ℝ)+1)^N*normD (f E) := by
      rw [energy_power_grade H hHG hGH E _ (hf E) N, normD_smul hD, norm_pow, hnormbase]
    rw [hnorm]
    simpa only [mul_assoc] using h
  have hsq : normD (T v)^2 ≤ (K*normD (R v))^2 := by
    rw [hsumT, mul_pow, hsumR, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro E hE
    have hh : normD (T (f E))^2 ≤ (K*normD (R (f E)))^2 :=
      (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hK (Real.sqrt_nonneg _))).mpr (hb E hE)
    rw [mul_pow] at hh
    exact hh
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hK (Real.sqrt_nonneg _))).mp hsq

private theorem neutral_state_grade (p : Oscillator D) (w : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p w) :
    Finsupp.single (0 : Charge D) p ∈ grade D (w : ℤ) := by
  rw [mem_grade_iff]
  intro a ha
  by_cases hb : (0 : Charge D)=a.1
  · rw [Finsupp.single_apply, if_pos hb]
    apply hp.coeff_eq_zero a.2
    intro he
    apply ha
    simp only [energy, ← hb, chargeEnergy_zero, zero_add, oscillatorEnergy]
    exact_mod_cast he
  · simp [Finsupp.single_apply, hb]

private theorem original_neutral_energy_le (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (p : Oscillator D) (w : ℕ)
    (hp : MvPolynomial.IsWeightedHomogeneous (fun x : Index D => x.2+1) p w)
    (v : Carrier D) :
    normD (((Y D (Finsupp.single 0 p))[[(w : ℤ)-1]]) v) ≤
      neutralConstant p * normD (((1+sugawaraMode D H 0)^(2*w)) v) := by
  apply energy_bound_of_grades hD H hHG hGH _ 0 (neutralConstant p)
    (neutralConstant_pos p).le (2*w) _ _ v
  · intro E u hu
    have hg := LatticeCoefficientEnergy.actual_mode_grade D w E ((w : ℤ)-1)
      (Finsupp.single 0 p) u (neutral_state_grade p w hp) hu
    convert hg using 1 <;> congr 1 <;> omega
  · exact fun E u hu => original_neutral_grade_le hD p w hp E u hu

#check @original_neutral_energy_le
#print axioms original_neutral_energy_le

#check @original_neutral_grade_le
#print axioms original_neutral_grade_le

#check @original_word_energy_le
#print axioms original_word_energy_le

#check @word_mode_grade
#print axioms word_mode_grade
#check @derivative_zero_strip
#print axioms derivative_zero_strip
#check @word_cons_finite
#print axioms word_cons_finite

end D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
