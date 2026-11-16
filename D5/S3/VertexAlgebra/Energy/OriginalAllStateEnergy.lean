/- GID: D5/S3/VertexAlgebra/Energy/OriginalAllStateEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Energy/OriginalAllStateEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original homogeneous and finite-energy all-state order-two-weight bounds. -/

import D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

/-! Uniform energy control of literal original homogeneous fields.
proof_shape: homogeneous_energy_bound: content; finite_energy_bound: content
admission_basis: escape-witness
escape_witness: The pre-relaxation charged seed and the single arbitrary-charge
normal-word induction give order 2d+wordWeight+length. Exact nonzero fixed-state
coefficient grading bounds this by 2W; finite input-grade orthogonality then
gives a constant independent of every mode and every original mixed input.
No completion, unitary-VOA assumption, support multiplier or intercept is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator Matrix

namespace D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy

open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeAllStateField
open LatticeSugawaraCurrents OriginalGram
open Lattice.OriginalChargedEnergy
open private normD_smul normD_sum_le from
  D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy
open private wordWeight wordOrder wordConstant wordConstant_nonneg wordOrder_le
  occurrence_weight seeded_word_energy_le negative_grade_eq_zero from
  D5.S3.VertexAlgebra.Energy.OriginalWordEnergy
open private energy_bound_of_grades energy_power_grade from
  D5.S3.VertexAlgebra.Energy.OriginalNeutralEnergy
open private totalChargedConstant totalChargedConstant_pos
  charged_pre_relaxation_grade_le from
  D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy

variable {D : LatticeData}

private def seedConstant (a : Charge D) : ℝ := by
  classical
  exact if a=0 then 1 else totalChargedConstant a

private theorem seedConstant_pos (a : Charge D) : 0 < seedConstant a := by
  classical
  unfold seedConstant
  split_ifs
  · norm_num
  · exact totalChargedConstant_pos a

/-- Order 2d between bounded endpoints, before any mode-scale relaxation.
Charge zero is the actual identity field, with numerical seed (1,0). -/
private theorem charged_seed_energy_le (hD : (gramReal D).PosDef)
    (a : Charge D) (E F M : ℕ) (n : ℤ)
    (hEF : (E : ℤ)+chargeEnergy D a-n-1=F) (hE : E ≤ M) (hF : F ≤ M)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (((actualField D a)[[n]]) v) ≤
      seedConstant a * ((M : ℝ)+1)^(2*(chargeEnergy D a).toNat) * normD v := by
  classical
  by_cases ha : a=0
  · subst a
    rw [actual_zero, identity_modes]
    split_ifs <;> simp [seedConstant, chargeEnergy_zero, normD, Real.sqrt_nonneg]
  · let m := n-chargeEnergy D a+1
    have hn : m+chargeEnergy D a-1=n := by dsimp [m]; omega
    have hgrade : (E : ℤ)-m=(F : ℤ) := by dsimp [m]; omega
    have hnat : ((E : ℤ)-m).toNat=F := by rw [hgrade]; simp
    have hh := charged_pre_relaxation_grade_le hD a ha m E v hv
    rw [hn, hnat] at hh
    have hscale :
        (if 0 ≤ n then (E : ℝ)+1 else (F : ℝ)+1) ≤ (M : ℝ)+1 := by
      split_ifs
      · exact_mod_cast Nat.add_le_add_right hE 1
      · exact_mod_cast Nat.add_le_add_right hF 1
    have hb : 0 ≤ (if 0 ≤ n then (E : ℝ)+1 else (F : ℝ)+1) := by
      split_ifs <;> positivity
    have hp := pow_le_pow_left₀ hb hscale (2*(chargeEnergy D a).toNat)
    rw [seedConstant, if_neg ha]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (totalChargedConstant_pos a).le)
      (Real.sqrt_nonneg _))

private def stateConstant (s : Carrier D) : ℝ := by
  classical
  exact 1 + ∑ a ∈ s.support, ∑ e ∈ (s a).support,
    ‖(s a).coeff e‖ * (seedConstant a * wordConstant (occurrences D e))

private theorem stateConstant_pos (s : Carrier D) : 0 < stateConstant s := by
  classical
  have hn : 0 ≤ ∑ a ∈ s.support, ∑ e ∈ (s a).support,
      ‖(s a).coeff e‖ * (seedConstant a * wordConstant (occurrences D e)) :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun e _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (seedConstant_pos a).le
        (wordConstant_nonneg _))))
  unfold stateConstant
  linarith

private theorem original_state_expansion (s : Carrier D) (n : ℤ) (v : Carrier D) :
    ((Y D s)[[n]]) v =
      ∑ a ∈ s.support, ∑ e ∈ (s a).support,
        (s a).coeff e • (((wordField D a (occurrences D e))[[n]]) v) := by
  classical
  have h := congrArg (fun A : VertexOperator ℂ (Carrier D) => (A[[n]]) v)
    (stateField_expansion D s)
  simpa only [map_sum, map_smul, Finset.sum_apply, LinearMap.sum_apply, Pi.smul_apply,
    LinearMap.smul_apply, MvPolynomial.basisMonomials,
    AddMonoidAlgebra.coeffLinearEquiv_apply, MvPolynomial.support] using h

/-- Fixed-state triangle estimates use the genuine total state weight,
while the input may already mix all original charge sectors. -/
private theorem homogeneous_between_grades (hD : (gramReal D).PosDef)
    (W : ℕ) (s : Carrier D) (hs : s ∈ grade D (W : ℤ))
    (E F M : ℕ) (n : ℤ) (hEF : (E : ℤ)+W-n-1=F)
    (hE : E ≤ M) (hF : F ≤ M)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (((Y D s)[[n]]) v) ≤
      stateConstant s * ((M : ℝ)+1)^(2*W) * normD v := by
  classical
  let b : ℝ := (M : ℝ)+1
  let Q := b^(2*W)*normD v
  let c := fun a e =>
    ‖(s a).coeff e‖ * (seedConstant a * wordConstant (occurrences D e))
  have hQ : 0 ≤ Q := mul_nonneg (by dsimp [b]; positivity) (Real.sqrt_nonneg _)
  have hterm (a : Charge D) (e : Index D →₀ ℕ) (he : e ∈ (s a).support) :
      normD ((s a).coeff e • (((wordField D a (occurrences D e))[[n]]) v)) ≤
        c a e * Q := by
    have he' : energy D (a,e)=(W : ℤ) := by
      by_contra hn
      exact (MvPolynomial.mem_support_iff.mp he)
        ((mem_grade_iff D W s).mp hs (a,e) hn)
    have hw : chargeEnergy D a+(wordWeight (occurrences D e) : ℤ)=(W : ℤ) := by
      simpa only [energy, oscillatorEnergy, occurrence_weight] using he'
    have hd : ((chargeEnergy D a).toNat : ℤ)=chargeEnergy D a :=
      Int.toNat_of_nonneg (chargeEnergy_nonneg D hD a)
    have hweight : (chargeEnergy D a).toNat+wordWeight (occurrences D e)=W := by
      exact_mod_cast (show (((chargeEnergy D a).toNat : ℕ) : ℤ)+
        (wordWeight (occurrences D e) : ℤ)=(W : ℤ) by rw [hd]; exact hw)
    have ho : 2*(chargeEnergy D a).toNat+wordOrder (occurrences D e) ≤ 2*W := by
      have hh := wordOrder_le (occurrences D e)
      omega
    have ht := seeded_word_energy_le hD a (seedConstant a) (seedConstant_pos a).le
      (2*(chargeEnergy D a).toNat) (charged_seed_energy_le hD a)
      (occurrences D e) E F M n (by omega) hE hF v hv
    have hp : b^(2*(chargeEnergy D a).toNat+wordOrder (occurrences D e)) ≤ b^(2*W) :=
      pow_le_pow_right₀ (by dsimp [b]; have hh := Nat.cast_nonneg (α := ℝ) M; linarith) ho
    have ht' : normD (((wordField D a (occurrences D e))[[n]]) v) ≤
        (seedConstant a * wordConstant (occurrences D e))*b^(2*W)*normD v :=
      ht.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp
          (mul_nonneg (seedConstant_pos a).le (wordConstant_nonneg _)))
        (Real.sqrt_nonneg _))
    rw [normD_smul hD]
    exact (mul_le_mul_of_nonneg_left ht' (norm_nonneg _)).trans_eq
      (by dsimp [c, Q]; ring)
  rw [original_state_expansion]
  calc
    _ ≤ ∑ a ∈ s.support, normD (∑ e ∈ (s a).support,
        (s a).coeff e • (((wordField D a (occurrences D e))[[n]]) v)) :=
      normD_sum_le hD _ _
    _ ≤ ∑ a ∈ s.support, ∑ e ∈ (s a).support, c a e * Q :=
      Finset.sum_le_sum (fun a _ => (normD_sum_le hD _ _).trans
        (Finset.sum_le_sum (fun e he => hterm a e he)))
    _ = (∑ a ∈ s.support, ∑ e ∈ (s a).support, c a e)*Q := by
      simp_rw [← Finset.sum_mul]
    _ ≤ (1+∑ a ∈ s.support, ∑ e ∈ (s a).support, c a e)*Q :=
      mul_le_mul_of_nonneg_right (by linarith) hQ
    _ = _ := by dsimp [stateConstant, c, Q, b]; ring

private theorem homogeneous_circle_grade_le (hD : (gramReal D).PosDef)
    (W : ℕ) (s : Carrier D) (hs : s ∈ grade D (W : ℤ))
    (m : ℤ) (E : ℕ) (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    normD (((Y D s)[[m+(W : ℤ)-1]]) v) ≤
      stateConstant s * (1+|(m : ℝ)|)^(2*W) *
        ((E : ℝ)+1)^(2*W) * normD v := by
  have hg : ((Y D s)[[m+(W : ℤ)-1]]) v ∈ grade D ((E : ℤ)-m) := by
    convert LatticeCoefficientEnergy.actual_mode_grade D W E (m+(W : ℤ)-1) s v hs hv
      using 1 <;> congr 1 <;> omega
  by_cases hn : (E : ℤ)-m < 0
  · rw [negative_grade_eq_zero hD _ hn _ hg]
    simpa [normD] using (show 0 ≤ stateConstant s * (1+|(m : ℝ)|)^(2*W) *
      ((E : ℝ)+1)^(2*W) * normD v by
        exact mul_nonneg (mul_nonneg (mul_nonneg (stateConstant_pos s).le
          (by positivity)) (by positivity)) (Real.sqrt_nonneg _))
  · let F := ((E : ℤ)-m).toNat
    let M := max E F
    have hF : (F : ℤ)=(E : ℤ)-m := Int.toNat_of_nonneg (by omega)
    have hFr : (F : ℝ)=(E : ℝ)-(m : ℝ) := by exact_mod_cast hF
    have hM : (M : ℝ)+1 ≤ (1+|(m : ℝ)|)*((E : ℝ)+1) := by
      have hh : (M : ℝ) ≤ (E : ℝ)+|(m : ℝ)| := by
        dsimp [M]
        rw [Nat.cast_max]
        apply max_le
        · linarith [abs_nonneg (m : ℝ)]
        · rw [hFr]
          linarith [neg_le_abs (m : ℝ)]
      nlinarith [abs_nonneg (m : ℝ),
        mul_nonneg (Nat.cast_nonneg (α := ℝ) E) (abs_nonneg (m : ℝ))]
    have ht := homogeneous_between_grades hD W s hs E F M (m+(W : ℤ)-1)
      (by omega) (le_max_left _ _) (le_max_right _ _) v hv
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (M : ℝ)+1) hM (2*W)
    calc
      _ ≤ stateConstant s * ((1+|(m : ℝ)|)*((E : ℝ)+1))^(2*W) * normD v :=
        ht.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (stateConstant_pos s).le) (Real.sqrt_nonneg _))
      _ = _ := by rw [mul_pow]; ring

private theorem original_homogeneous_energy_le (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (W : ℕ) (s : Carrier D) (hs : s ∈ grade D (W : ℤ))
    (m : ℤ) (v : Carrier D) :
    normD (((Y D s)[[m+(W : ℤ)-1]]) v) ≤
      stateConstant s * (1+|(m : ℝ)|)^(2*W) *
        normD (((1+sugawaraMode D H 0)^(2*W)) v) := by
  apply energy_bound_of_grades hD H hHG hGH _ (-m)
    (stateConstant s * (1+|(m : ℝ)|)^(2*W))
    (mul_nonneg (stateConstant_pos s).le (by positivity)) (2*W) _ _ v
  · intro E u hu
    convert LatticeCoefficientEnergy.actual_mode_grade D W E (m+(W : ℤ)-1) s u hs hu
      using 1 <;> congr 1 <;> omega
  · exact fun E u hu => homogeneous_circle_grade_le hD W s hs m E u hu

/-- One positive constant, chosen before all integer circle modes and all
original mixed inputs, controls every literal original homogeneous field.
The energy operator is the actual Sugawara zero mode with both inverse laws. -/
theorem homogeneous_energy_bound (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (W : ℕ) (s : Carrier D) (hs : s ∈ grade D (W : ℤ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℤ) (v : Carrier D),
      normD (((Y D s)[[m+(W : ℤ)-1]]) v) ≤
        C * (1+|(m : ℝ)|)^(2*W) *
          normD (((1+sugawaraMode D H 0)^(2*W)) v) := by
  exact ⟨stateConstant s, stateConstant_pos s,
    fun m v => original_homogeneous_energy_le hD H hHG hGH W s hs m v⟩

/-- Finite spectral domination: the existing orthogonal recombination lemma
sums the squared grade estimates, so no input-support factor is introduced. -/
private theorem energy_power_mono (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (k N : ℕ) (hk : k ≤ N) (v : Carrier D) :
    normD (((1+sugawaraMode D H 0)^k) v) ≤
      normD (((1+sugawaraMode D H 0)^N) v) := by
  have hb := energy_bound_of_grades hD H hHG hGH
    ((1+sugawaraMode D H 0)^k) 0 1 (by norm_num) N
    (by
      intro E u hu
      rw [energy_power_grade H hHG hGH E u hu k]
      simpa only [add_zero] using (grade D E).smul_mem (((E : ℂ)+1)^k) hu)
    (by
      intro E u hu
      rw [energy_power_grade H hHG hGH E u hu k, normD_smul hD, norm_pow]
      have he : ‖((E : ℂ)+1)‖=(E : ℝ)+1 := by
        rw [show ((E : ℂ)+1)=((E+1 : ℕ) : ℂ) by push_cast; rfl,
          Complex.norm_natCast, Nat.cast_add, Nat.cast_one]
      rw [Int.cast_natCast, he]
      have hp := pow_le_pow_right₀
        (by have hh := Nat.cast_nonneg (α := ℝ) E; linarith : 1 ≤ (E : ℝ)+1) hk
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hp (show 0 ≤ normD u from Real.sqrt_nonneg _)) v
  simpa only [one_mul] using hb

/-- The sup includes zero as the empty supremum.  With positive Gram it is
exactly the largest actual state energy, or zero for the zero state. -/
private def maxWeight (s : Carrier D) : ℕ :=
  (stateEnergies D s).sup (fun E => E.toNat)

/-- A coherent common Laurent-mode bound for any original finite state.
Every component of weight W uses circle index n-W+1; only the fixed state
components are summed by the triangle inequality. -/
theorem finite_energy_bound (hD : (gramReal D).PosDef)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H*gramComplex D=1) (hGH : gramComplex D*H=1)
    (s : Carrier D) :
    let Wmax := (stateEnergies D s).sup (fun E => E.toNat)
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (v : Carrier D),
      normD (((Y D s)[[n]]) v) ≤
        C * (1+|(n : ℝ)|)^(2*Wmax) *
          normD (((1+sugawaraMode D H 0)^(2*Wmax)) v) := by
  classical
  dsimp only
  let S := stateEnergies D s
  let N := 2*maxWeight s
  let f := fun E => gradeProjection D E s
  let c := fun E => stateConstant (f E) * ((E.toNat : ℝ)+2)^(2*E.toNat)
  let C := 1+∑ E ∈ S, c E
  have hc (E : ℤ) : 0 ≤ c E := by
    dsimp [c]
    exact mul_nonneg (stateConstant_pos _).le (by positivity)
  have hC : 0 < C := by
    have hh := Finset.sum_nonneg (fun E (_ : E ∈ S) => hc E)
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro n v
  let Q := (1+|(n : ℝ)|)^N * normD (((1+sugawaraMode D H 0)^N) v)
  have hQ : 0 ≤ Q := mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hterm (E : ℤ) (hE : E ∈ S) :
      normD (((Y D (f E))[[n]]) v) ≤ c E * Q := by
    have hnonneg := stateEnergies_nonneg hD s E hE
    have hcast : (E.toNat : ℤ)=E := Int.toNat_of_nonneg hnonneg
    have hW : E.toNat ≤ maxWeight s := Finset.le_sup hE
    have hN : 2*E.toNat ≤ N := by dsimp [N]; omega
    have hg : f E ∈ grade D (E.toNat : ℤ) := by
      rw [hcast]
      exact gradeProjection_mem D E s
    have ht := original_homogeneous_energy_le hD H hHG hGH E.toNat (f E) hg
      (n-(E.toNat : ℤ)+1) v
    rw [show n-(E.toNat : ℤ)+1+(E.toNat : ℤ)-1=n by omega] at ht
    have hm : 1+|((n-(E.toNat : ℤ)+1 : ℤ) : ℝ)| ≤
        ((E.toNat : ℝ)+2)*(1+|(n : ℝ)|) := by
      have hh : |(n : ℝ)-(E.toNat : ℝ)+1| ≤
          |(n : ℝ)|+(E.toNat : ℝ)+1 := by
        calc
          _ ≤ |(n : ℝ)-(E.toNat : ℝ)|+|1| := abs_add_le _ _
          _ ≤ |(n : ℝ)|+(E.toNat : ℝ)+1 := by
            have ha : |(n : ℝ)-(E.toNat : ℝ)| ≤ |(n : ℝ)|+(E.toNat : ℝ) := by
              simpa only [sub_eq_add_neg, abs_neg,
                abs_of_nonneg (Nat.cast_nonneg (α := ℝ) E.toNat)] using
                abs_add_le (n : ℝ) (-(E.toNat : ℝ))
            norm_num only [abs_one]
            linarith
      push_cast
      nlinarith [abs_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) E.toNat,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) E.toNat) (abs_nonneg (n : ℝ))]
    have hp := pow_le_pow_left₀ (by positivity :
      0 ≤ 1+|((n-(E.toNat : ℤ)+1 : ℤ) : ℝ)|) hm (2*E.toNat)
    have hn := pow_le_pow_right₀
      (by linarith [abs_nonneg (n : ℝ)] : 1 ≤ 1+|(n : ℝ)|) hN
    have hpower := energy_power_mono hD H hHG hGH (2*E.toNat) N hN v
    have hcoeff : stateConstant (f E) *
        (1+|((n-(E.toNat : ℤ)+1 : ℤ) : ℝ)|)^(2*E.toNat) ≤
        c E * (1+|(n : ℝ)|)^N := by
      calc
        _ ≤ stateConstant (f E) *
            (((E.toNat : ℝ)+2)*(1+|(n : ℝ)|))^(2*E.toNat) :=
          mul_le_mul_of_nonneg_left hp (stateConstant_pos _).le
        _ = c E * (1+|(n : ℝ)|)^(2*E.toNat) := by dsimp [c]; rw [mul_pow]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hn (hc E)
    exact ht.trans ((mul_le_mul hcoeff hpower (Real.sqrt_nonneg _)
      (mul_nonneg (hc E) (by positivity))).trans_eq (by dsimp [Q]; ring))
  have hs : ∑ E ∈ S, f E = s := sum_gradeProjections D s
  have hsum : ((Y D s)[[n]]) v = ∑ E ∈ S, ((Y D (f E))[[n]]) v := by
    conv_lhs => rw [← hs]
    simp only [map_sum, Finset.sum_apply, LinearMap.sum_apply]
  rw [hsum]
  calc
    _ ≤ ∑ E ∈ S, normD (((Y D (f E))[[n]]) v) := normD_sum_le hD _ _
    _ ≤ ∑ E ∈ S, c E * Q := Finset.sum_le_sum hterm
    _ = (∑ E ∈ S, c E)*Q := (Finset.sum_mul _ _ _).symm
    _ ≤ C*Q := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hQ
    _ = _ := by dsimp [C, Q, N, maxWeight]; ring

#check @homogeneous_energy_bound
#print axioms homogeneous_energy_bound
#check @finite_energy_bound
#print axioms finite_energy_bound
#print axioms energy_power_mono
#print axioms charged_seed_energy_le
#print axioms homogeneous_between_grades
end D5.S3.VertexAlgebra.Energy.OriginalAllStateEnergy
