/- GID: D5/S3/VertexAlgebra/Energy/OriginalNeutralEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Energy/OriginalNeutralEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original neutral word estimates and orthogonal finite energy recombination. -/

import D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy

/-! Neutral normal-product words and orthogonal energy recombination.

These are the original consumed proof components of OriginalChargedEnergy:
the complete two-branch word induction, its vanishing derivative strip, and
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

private def wordWeight (ω : List (Index D)) : ℕ :=
  (ω.map (fun x => x.2+1)).sum

open private word_off_energy from D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
open private word_charge chargeSpace from D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
open private wordMap wordCoeff from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow

private theorem word_mode_grade (ω : List (Index D)) (E n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D E) :
    ((wordField D 0 ω)[[n]]) v ∈ grade D (E + wordWeight ω - n - 1) := by
  classical
  rw [grade_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨β,d⟩, he, rfl⟩ := hx
    rw [carrierBasis_apply]
    obtain ⟨p,hp⟩ := word_charge D 0 β ω n (MvPolynomial.monomial d 1)
    have hsingle : ((wordField D 0 ω)[[n]])
        (Finsupp.single β (MvPolynomial.monomial d 1)) = Finsupp.single β p := by
      simpa using hp.symm
    rw [mem_grade_iff]
    intro a ha
    by_cases hb : β = a.1
    · have hc := word_off_energy D 0 β ω n a.2 d
      change energy D (β,d) = E at he
      have hw : (ω.map (fun x => (x.2+1 : ℤ))).sum = (wordWeight ω : ℤ) := by
        simp [wordWeight, Nat.cast_list_sum, List.map_map, Function.comp_def]
      have hh : (CanonicalOccupationSewing.level D a.2 : ℤ) ≠
          (CanonicalOccupationSewing.level D d : ℤ) +
            (ω.map (fun x => (x.2+1 : ℤ))).sum - n - 1 - bilinear D 0 β := by
        simp only [bilinear, Pi.zero_apply, Int.cast_zero, zero_mul,
          Finset.sum_const_zero, sub_zero, hw]
        simp only [energy, hb] at he ha
        dsimp [CanonicalOccupationSewing.level]
        omega
      have hz := hc hh
      change ((((wordField D 0 ω)[[n]])
        (Finsupp.single β (MvPolynomial.monomial d 1))) (0+β)).coeff a.2 = 0 at hz
      simpa [hb] using hz
    · rw [hsingle]
      simp [Finsupp.single_apply, hb]
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using (grade D _).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [map_smul] using (grade D _).smul_mem c ih

private theorem negative_grade_eq_zero (hD : (gramReal D).PosDef) (E : ℤ)
    (hE : E < 0) (v : Carrier D) (hv : v ∈ grade D E) : v = 0 := by
  apply (carrierCoeffEquiv D).injective
  ext a
  change (v a.1).coeff a.2 = 0
  apply (mem_grade_iff D E v).mp hv a
  have hn := chargeEnergy_nonneg D hD a.1
  dsimp [energy]
  omega

open private derivative_modes from D5.S3.VertexAlgebra.LatticeAllStateField

private theorem derivative_zero_strip (i : Fin D.rank) (r : ℕ) (m : ℤ)
    (hm : 0 ≤ m) (hr : m < r) :
    ((FieldNormalProduct.dividedDerivative r
      (LatticeFiniteNegativeGeneration.neutralField D i))[[m]]) = 0 := by
  rw [derivative_modes D (i,r)]
  obtain ⟨q,hq⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ -m-1+(r : ℤ) by omega)
  rw [hq, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (show q < r by omega)]
  simp

private theorem current_mode_grade (i : Fin D.rank) (E m : ℤ)
    (v : Carrier D) (hv : v ∈ grade D E) :
    LatticeFiniteNegativeGeneration.neutralMode D i m v ∈ grade D (E-m) := by
  have hs : LatticeActualConformalState.currentState D i ∈ grade D 1 := by
    rw [grade_eq_span]
    apply Submodule.subset_span
    refine ⟨(0,Finsupp.single (i,0) 1), ?_, ?_⟩
    · simp [energy, oscillatorEnergy, Finsupp.weight_single]
    · simp [carrierBasis_apply, LatticeActualConformalState.currentState,
        MvPolynomial.X]
  have hg := LatticeCoefficientEnergy.actual_mode_grade D 1 E m
    (LatticeActualConformalState.currentState D i) v hs hv
  rw [LatticeActualConformalState.current_state_field,
    LatticeSugawaraCurrents.neutralField_ncoeff] at hg
  convert hg using 1 <;> congr 1 <;> omega

private def wordLeft (x : Index D) (ω : List (Index D)) (n : ℤ)
    (v : Carrier D) (q : ℕ) : Carrier D :=
  ((FieldNormalProduct.dividedDerivative x.2
      (LatticeFiniteNegativeGeneration.neutralField D x.1))[[-(q : ℤ)-1]])
    (((wordField D 0 ω)[[n+q]]) v)

private def wordRight (x : Index D) (ω : List (Index D)) (n : ℤ)
    (v : Carrier D) (q : ℕ) : Carrier D :=
  ((wordField D 0 ω)[[n-q-1]])
    (((FieldNormalProduct.dividedDerivative x.2
      (LatticeFiniteNegativeGeneration.neutralField D x.1))[[q]]) v)

private theorem wordLeft_vanish (hD : (gramReal D).PosDef)
    (x : Index D) (ω : List (Index D)) (E F : ℕ) (n : ℤ)
    (hEF : (E : ℤ)+wordWeight (x::ω)-n-1=F)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (q : ℕ)
    (hq : F < q+x.2+1) : wordLeft x ω n v q = 0 := by
  have hg := word_mode_grade ω E (n+q) v hv
  have hw : wordWeight (x::ω) = x.2+1+wordWeight ω := by
    simp [wordWeight]
  have hz := negative_grade_eq_zero hD _ (by rw [hw] at hEF; push_cast at hEF; omega)
    _ hg
  simp [wordLeft, hz]

private theorem wordRight_strip (x : Index D) (ω : List (Index D))
    (n : ℤ) (v : Carrier D) (q : ℕ) (hq : q < x.2) :
    wordRight x ω n v q = 0 := by
  have hz := derivative_zero_strip (D := D) x.1 x.2 q (by omega) (by omega)
  simp [wordRight, hz]

private theorem wordRight_vanish (hD : (gramReal D).PosDef)
    (x : Index D) (ω : List (Index D)) (E : ℕ) (n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (q : ℕ)
    (hq : E+x.2 < q) : wordRight x ω n v q = 0 := by
  have hg := current_mode_grade x.1 E ((q : ℤ)-x.2) v hv
  have hz := negative_grade_eq_zero hD _ (by omega) _ hg
  dsimp [wordRight]
  rw [derivative_modes D x, LinearMap.smul_apply, hz, smul_zero, map_zero]

/-- Exact finite recursion of the literal normal product, at a general mode.
The derivative strip remains in the second finite range with zero summands. -/
private theorem word_cons_finite (hD : (gramReal D).PosDef)
    (x : Index D) (ω : List (Index D)) (E F : ℕ) (n : ℤ)
    (hEF : (E : ℤ)+wordWeight (x::ω)-n-1=F)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    ((wordField D 0 (x::ω))[[n]]) v =
      (∑ q ∈ Finset.range (F+1), wordLeft x ω n v q) +
      ∑ q ∈ Finset.range (E+x.2+1), wordRight x ω n v q := by
  classical
  rw [wordField, (FieldNormalProduct.normalMinusOne _ _).2]
  congr 1
  · change (∑ᶠ q, wordLeft x ω n v q) = _
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hn
    exact hq (wordLeft_vanish hD x ω E F n hEF v hv q (by
      have hn' : F+1 ≤ q := by simpa using hn
      omega))
  · change (∑ᶠ q, wordRight x ω n v q) = _
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hn
    exact hq (wordRight_vanish hD x ω E n v hv q (by
      have hn' : E+x.2+1 ≤ q := by simpa using hn
      omega))

private def derivativeConstant (r : ℕ) : ℝ :=
  ((r : ℝ)+1)^r / (r.factorial : ℝ)

private theorem derivativeConstant_nonneg (r : ℕ) : 0 ≤ derivativeConstant r := by
  unfold derivativeConstant
  positivity

private theorem choose_energy_le (r M t : ℕ) (ht : t ≤ M+r) :
    (t.choose r : ℝ) ≤ derivativeConstant r * ((M : ℝ)+1)^r := by
  have ht' : (t : ℝ) ≤ ((r : ℝ)+1)*((M : ℝ)+1) := by
    have hh : (t : ℝ) ≤ (M : ℝ)+r := by exact_mod_cast ht
    nlinarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) r]
  calc
    _ ≤ (t : ℝ)^r / (r.factorial : ℝ) := Nat.choose_le_pow_div r t
    _ ≤ (((r : ℝ)+1)*((M : ℝ)+1))^r / (r.factorial : ℝ) :=
      div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) ht' r) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow]; unfold derivativeConstant; ring

open private signed_derivative_choose from
  D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow

private theorem derivative_negative_coeff_le (r M q : ℕ) (hq : q+r ≤ M+r) :
    ‖((Ring.choose (-(-(q : ℤ)-1)-1+r) r : ℤ) : ℂ)‖ ≤
      derivativeConstant r * ((M : ℝ)+1)^r := by
  rw [show -(-(q : ℤ)-1)-1+r = ((q+r : ℕ) : ℤ) by omega,
    Ring.choose_natCast]
  simpa only [Int.cast_natCast, Complex.norm_natCast] using choose_energy_le r M (q+r) hq

private theorem derivative_positive_coeff_le (r M q : ℕ) (hq : q ≤ M+r) :
    ‖((Ring.choose (-(q : ℤ)-1+r) r : ℤ) : ℂ)‖ ≤
      derivativeConstant r * ((M : ℝ)+1)^r := by
  rw [signed_derivative_choose]
  simpa only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Complex.norm_natCast] using choose_energy_le r M q hq

private def wordOrder (ω : List (Index D)) : ℕ := wordWeight ω + ω.length

private def wordConstant : List (Index D) → ℝ
  | [] => 1
  | x::ω => ((x.2 : ℝ)+2) * derivativeConstant x.2 *
      Real.sqrt (3*(D.G x.1 x.1 : ℝ)) * wordConstant ω

private theorem wordConstant_nonneg (ω : List (Index D)) :
    0 ≤ wordConstant ω := by
  induction ω with
  | nil => norm_num [wordConstant]
  | cons x ω ih =>
    dsimp [wordConstant]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (derivativeConstant_nonneg _)) (Real.sqrt_nonneg _)) ih

/-- The actual nested neutral word is uniformly bounded between any two
nonnegative grades; no charge, support-size or oscillator-degree factor occurs. -/
private theorem original_word_energy_le (hD : (gramReal D).PosDef)
    (ω : List (Index D)) : ∀ (E F M : ℕ) (n : ℤ),
    (E : ℤ)+wordWeight ω-n-1=F → E ≤ M → F ≤ M →
    ∀ v : Carrier D, v ∈ grade D (E : ℤ) →
      normD (((wordField D 0 ω)[[n]]) v) ≤
        wordConstant ω * ((M : ℝ)+1)^(wordOrder ω) * normD v := by
  induction ω with
  | nil =>
    intro E F M n hEF hE hF v hv
    rw [wordField, actual_zero, identity_modes]
    split_ifs with hn
    · simp [wordConstant, wordOrder, wordWeight]
    · simp [wordConstant, wordOrder, wordWeight, normD, Real.sqrt_nonneg]
  | cons x ω ih =>
    intro E F M n hEF hE hF v hv
    classical
    let b : ℝ := (M : ℝ)+1
    let A := derivativeConstant x.2
    let L := Real.sqrt (3*(D.G x.1 x.1 : ℝ))
    let K := wordConstant ω
    let P := wordOrder ω
    let T := A*L*K*b^(x.2+1+P)*normD v
    have hA : 0 ≤ A := derivativeConstant_nonneg _
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hK : 0 ≤ K := wordConstant_nonneg _
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hvn : 0 ≤ normD v := Real.sqrt_nonneg _
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hw : wordWeight (x::ω) = x.2+1+wordWeight ω := by simp [wordWeight]
    have hp : wordOrder (x::ω) = x.2+2+P := by
      dsimp [wordOrder, P]
      rw [hw]
      omega
    have hleft (q : ℕ) : normD (wordLeft x ω n v q) ≤ T := by
      by_cases hq : F < q+x.2+1
      · rw [wordLeft_vanish hD x ω E F n hEF v hv q hq]
        simpa [normD] using hT
      have hq' : q+x.2+1 ≤ F := by omega
      let G := F-(q+x.2+1)
      have hG : G ≤ M := by dsimp [G]; omega
      have htail : (E : ℤ)+wordWeight ω-(n+q)-1=G := by
        rw [hw] at hEF
        dsimp [G]
        push_cast at hEF
        omega
      have hg : ((wordField D 0 ω)[[n+q]]) v ∈ grade D (G : ℤ) := by
        rw [← htail]
        exact word_mode_grade ω E (n+q) v hv
      have ht := ih E G M (n+q) htail hE hG v hv
      have hc := original_current_energy_le hD x.1 (-(q : ℤ)-1-x.2) G F M
        (by dsimp [G]; omega) hG hF _ hg
      have ha := derivative_negative_coeff_le x.2 M q (by omega)
      rw [wordLeft, derivative_modes D x, LinearMap.smul_apply, normD_smul hD]
      calc
        _ ≤ (A*b^x.2) * (L*b*normD (((wordField D 0 ω)[[n+q]]) v)) :=
          mul_le_mul ha hc (Real.sqrt_nonneg _) (by positivity)
        _ ≤ (A*b^x.2) * (L*b*(K*b^P*normD v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ht (mul_nonneg hL hb)) (by positivity)
        _ = T := by dsimp [T]; rw [pow_add, pow_add, pow_one]; ring
    have hright (q : ℕ) : normD (wordRight x ω n v q) ≤ T := by
      by_cases hs : q < x.2
      · rw [wordRight_strip x ω n v q hs]
        simpa [normD] using hT
      by_cases hq : E+x.2 < q
      · rw [wordRight_vanish hD x ω E n v hv q hq]
        simpa [normD] using hT
      let G := E-(q-x.2)
      have hG : G ≤ M := by dsimp [G]; omega
      have hcurr : (E : ℤ)-((q : ℤ)-x.2)=G := by dsimp [G]; omega
      have hg : LatticeFiniteNegativeGeneration.neutralMode D x.1
          ((q : ℤ)-x.2) v ∈ grade D (G : ℤ) := by
        rw [← hcurr]
        exact current_mode_grade x.1 E _ v hv
      have htail : (G : ℤ)+wordWeight ω-(n-q-1)-1=F := by
        rw [hw] at hEF
        push_cast at hEF
        omega
      have ht := ih G F M (n-q-1) htail hG hF _ hg
      have hc := original_current_energy_le hD x.1 ((q : ℤ)-x.2) E G M
        hcurr hE hG v hv
      have ha := derivative_positive_coeff_le x.2 M q (by omega)
      rw [wordRight, derivative_modes D x, LinearMap.smul_apply, map_smul,
        normD_smul hD]
      calc
        _ ≤ (A*b^x.2) * (K*b^P*
            normD (LatticeFiniteNegativeGeneration.neutralMode D x.1 ((q : ℤ)-x.2) v)) :=
          mul_le_mul ha ht (Real.sqrt_nonneg _) (by positivity)
        _ ≤ (A*b^x.2) * (K*b^P*(L*b*normD v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hc (by positivity)) (by positivity)
        _ = T := by dsimp [T]; rw [pow_add, pow_add, pow_one]; ring
    have hsumL : (∑ q ∈ Finset.range (F+1), normD (wordLeft x ω n v q)) ≤
        ((F : ℝ)+1)*T := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (F+1), T := Finset.sum_le_sum (fun q _ => hleft q)
        _ = _ := by simp
    have hsumR : (∑ q ∈ Finset.range (E+x.2+1), normD (wordRight x ω n v q)) ≤
        ((E : ℝ)+x.2+1)*T := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (E+x.2+1), T := Finset.sum_le_sum (fun q _ => hright q)
        _ = _ := by simp
    have hcount : ((F : ℝ)+1)+((E : ℝ)+x.2+1) ≤ ((x.2 : ℝ)+2)*b := by
      have he : (E : ℝ) ≤ M := by exact_mod_cast hE
      have hf : (F : ℝ) ≤ M := by exact_mod_cast hF
      dsimp [b]
      nlinarith [Nat.cast_nonneg (α := ℝ) x.2, Nat.cast_nonneg (α := ℝ) M]
    rw [word_cons_finite hD x ω E F n hEF v hv]
    calc
      _ ≤ normD (∑ q ∈ Finset.range (F+1), wordLeft x ω n v q) +
          normD (∑ q ∈ Finset.range (E+x.2+1), wordRight x ω n v q) := normD_add_le hD _ _
      _ ≤ ((F : ℝ)+1)*T + ((E : ℝ)+x.2+1)*T :=
        add_le_add ((normD_sum_le hD _ _).trans hsumL) ((normD_sum_le hD _ _).trans hsumR)
      _ = (((F : ℝ)+1)+((E : ℝ)+x.2+1))*T := by ring
      _ ≤ (((x.2 : ℝ)+2)*b)*T := mul_le_mul_of_nonneg_right hcount hT
      _ = _ := by
        rw [hp]
        change (((x.2 : ℝ)+2)*b)*T =
          (((x.2 : ℝ)+2)*A*L*K)*b^(x.2+2+P)*normD v
        dsimp [T]
        rw [show x.2+2+P = (x.2+1+P)+1 by omega, pow_succ]
        ring

private theorem wordOrder_le (ω : List (Index D)) : wordOrder ω ≤ 2*wordWeight ω := by
  have hh : ω.length ≤ wordWeight ω := by
    induction ω with
    | nil => simp [wordWeight]
    | cons x ω ih => simp only [List.length_cons, wordWeight, List.map_cons,
        List.sum_cons] at *; omega
  unfold wordOrder
  omega

private theorem occurrence_weight (e : Index D →₀ ℕ) :
    wordWeight (occurrences D e) = Finsupp.weight (fun x : Index D => x.2+1) e := by
  exact LatticeHalfFockFiniteCorrection.wordWeight_occurrences D e

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

private theorem stateEnergies_nonneg (hD : (gramReal D).PosDef)
    (v : Carrier D) (E : ℤ) (hE : E ∈ stateEnergies D v) : 0 ≤ E := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hE
  have hn := chargeEnergy_nonneg D hD a.1
  dsimp [energy]
  omega

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
