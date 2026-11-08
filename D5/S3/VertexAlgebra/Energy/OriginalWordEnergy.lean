/- GID: D5/S3/VertexAlgebra/Energy/OriginalWordEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Energy/OriginalWordEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Seed-parametrized arbitrary-charge original normal-word energy induction. -/

import D5.S3.VertexAlgebra.Energy.OriginalCurrentEnergy

/-! One literal arbitrary-charge normal-word induction.
The seed is a numerical between-grade estimate on the original actualField.
The neutral prerequisite discharges it with the literal identity field; the
all-state consumer discharges it with the pre-relaxation charged estimate.
Both normal-product branches and the strict derivative zero strip are retained.
All declarations are private consumed proof components, not novelty endpoints.
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

open private word_off_energy charge_energy_add from D5.S3.VertexAlgebra.Energy.LatticeCoefficientEnergy
open private word_charge chargeSpace from D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
open private wordMap wordCoeff from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow

private theorem word_mode_grade (a : Charge D) (ω : List (Index D)) (E n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D E) :
    ((wordField D a ω)[[n]]) v ∈
      grade D (E + chargeEnergy D a + wordWeight ω - n - 1) := by
  classical
  rw [grade_eq_span] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨β,d⟩, he, rfl⟩ := hx
    rw [carrierBasis_apply]
    obtain ⟨p,hp⟩ := word_charge D a β ω n (MvPolynomial.monomial d 1)
    have hsingle : ((wordField D a ω)[[n]])
        (Finsupp.single β (MvPolynomial.monomial d 1)) = Finsupp.single (a+β) p := hp.symm
    rw [mem_grade_iff]
    intro t ht
    by_cases hb : a+β = t.1
    · have hc := word_off_energy D a β ω n t.2 d
      change energy D (β,d) = E at he
      have hw : (ω.map (fun x => (x.2+1 : ℤ))).sum = (wordWeight ω : ℤ) := by
        simp [wordWeight, Nat.cast_list_sum, List.map_map, Function.comp_def]
      have hcharge := charge_energy_add D a β
      have hh : (CanonicalOccupationSewing.level D t.2 : ℤ) ≠
          (CanonicalOccupationSewing.level D d : ℤ) +
            (ω.map (fun x => (x.2+1 : ℤ))).sum - n - 1 - bilinear D a β := by
        rw [hw]
        simp only [energy, ← hb] at he ht
        dsimp [CanonicalOccupationSewing.level]
        omega
      have hz := hc hh
      change ((((wordField D a ω)[[n]])
        (Finsupp.single β (MvPolynomial.monomial d 1))) (a+β)).coeff t.2 = 0 at hz
      simpa only [hb] using hz
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

private def wordLeft (a : Charge D) (x : Index D) (ω : List (Index D)) (n : ℤ)
    (v : Carrier D) (q : ℕ) : Carrier D :=
  ((FieldNormalProduct.dividedDerivative x.2
      (LatticeFiniteNegativeGeneration.neutralField D x.1))[[-(q : ℤ)-1]])
    (((wordField D a ω)[[n+q]]) v)

private def wordRight (a : Charge D) (x : Index D) (ω : List (Index D)) (n : ℤ)
    (v : Carrier D) (q : ℕ) : Carrier D :=
  ((wordField D a ω)[[n-q-1]])
    (((FieldNormalProduct.dividedDerivative x.2
      (LatticeFiniteNegativeGeneration.neutralField D x.1))[[q]]) v)

private theorem wordLeft_vanish (hD : (gramReal D).PosDef)
    (a : Charge D) (x : Index D) (ω : List (Index D)) (E F : ℕ) (n : ℤ)
    (hEF : (E : ℤ)+chargeEnergy D a+wordWeight (x::ω)-n-1=F)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (q : ℕ)
    (hq : F < q+x.2+1) : wordLeft a x ω n v q = 0 := by
  have hg := word_mode_grade a ω E (n+q) v hv
  have hw : wordWeight (x::ω) = x.2+1+wordWeight ω := by
    simp [wordWeight]
  have hz := negative_grade_eq_zero hD _ (by rw [hw] at hEF; push_cast at hEF; omega)
    _ hg
  simp [wordLeft, hz]

private theorem wordRight_strip (a : Charge D) (x : Index D) (ω : List (Index D))
    (n : ℤ) (v : Carrier D) (q : ℕ) (hq : q < x.2) :
    wordRight a x ω n v q = 0 := by
  have hz := derivative_zero_strip (D := D) x.1 x.2 q (by omega) (by omega)
  simp [wordRight, hz]

private theorem wordRight_vanish (hD : (gramReal D).PosDef)
    (a : Charge D) (x : Index D) (ω : List (Index D)) (E : ℕ) (n : ℤ)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) (q : ℕ)
    (hq : E+x.2 < q) : wordRight a x ω n v q = 0 := by
  have hg := current_mode_grade x.1 E ((q : ℤ)-x.2) v hv
  have hz := negative_grade_eq_zero hD _ (by omega) _ hg
  dsimp [wordRight]
  rw [derivative_modes D x, LinearMap.smul_apply, hz, smul_zero, map_zero]

/-- Exact finite recursion of the literal normal product, at a general mode.
The derivative strip remains in the second finite range with zero summands. -/
private theorem word_cons_finite (hD : (gramReal D).PosDef)
    (a : Charge D) (x : Index D) (ω : List (Index D)) (E F : ℕ) (n : ℤ)
    (hEF : (E : ℤ)+chargeEnergy D a+wordWeight (x::ω)-n-1=F)
    (v : Carrier D) (hv : v ∈ grade D (E : ℤ)) :
    ((wordField D a (x::ω))[[n]]) v =
      (∑ q ∈ Finset.range (F+1), wordLeft a x ω n v q) +
      ∑ q ∈ Finset.range (E+x.2+1), wordRight a x ω n v q := by
  classical
  rw [wordField, (FieldNormalProduct.normalMinusOne _ _).2]
  congr 1
  · change (∑ᶠ q, wordLeft a x ω n v q) = _
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hn
    exact hq (wordLeft_vanish hD a x ω E F n hEF v hv q (by
      have hn' : F+1 ≤ q := by simpa using hn
      omega))
  · change (∑ᶠ q, wordRight a x ω n v q) = _
    apply finsum_eq_sum_of_support_subset
    intro q hq
    by_contra hn
    exact hq (wordRight_vanish hD a x ω E n v hv q (by
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

/-- A numerical actual-field seed propagates through the single original
two-branch recurrence on arbitrary charge, without an input-support factor. -/
private theorem seeded_word_energy_le (hD : (gramReal D).PosDef)
    (a : Charge D) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) (B : ℕ)
    (hseed : ∀ (E F M : ℕ) (n : ℤ),
      (E : ℤ)+chargeEnergy D a-n-1=F → E ≤ M → F ≤ M →
      ∀ v : Carrier D, v ∈ grade D (E : ℤ) →
        normD (((actualField D a)[[n]]) v) ≤
          K₀ * ((M : ℝ)+1)^B * normD v)
    (ω : List (Index D)) : ∀ (E F M : ℕ) (n : ℤ),
    (E : ℤ)+chargeEnergy D a+wordWeight ω-n-1=F → E ≤ M → F ≤ M →
    ∀ v : Carrier D, v ∈ grade D (E : ℤ) →
      normD (((wordField D a ω)[[n]]) v) ≤
        (K₀ * wordConstant ω) * ((M : ℝ)+1)^(B+wordOrder ω) * normD v := by
  induction ω with
  | nil =>
    intro E F M n hEF hE hF v hv
    simpa only [wordField, wordWeight, List.map_nil, List.sum_nil, Nat.cast_zero,
      add_zero, wordOrder, List.length_nil, wordConstant, mul_one] using
      hseed E F M n (by simpa [wordWeight] using hEF) hE hF v hv
  | cons x ω ih =>
    intro E F M n hEF hE hF v hv
    classical
    let b : ℝ := (M : ℝ)+1
    let A := derivativeConstant x.2
    let L := Real.sqrt (3*(D.G x.1 x.1 : ℝ))
    let K := K₀ * wordConstant ω
    let P := B + wordOrder ω
    let T := A*L*K*b^(x.2+1+P)*normD v
    have hA : 0 ≤ A := derivativeConstant_nonneg _
    have hL : 0 ≤ L := Real.sqrt_nonneg _
    have hK : 0 ≤ K := mul_nonneg hK₀ (wordConstant_nonneg _)
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hvn : 0 ≤ normD v := Real.sqrt_nonneg _
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hw : wordWeight (x::ω) = x.2+1+wordWeight ω := by simp [wordWeight]
    have hp : B+wordOrder (x::ω) = x.2+2+P := by
      dsimp [wordOrder, P]
      rw [hw]
      omega
    have hleft (q : ℕ) : normD (wordLeft a x ω n v q) ≤ T := by
      by_cases hq : F < q+x.2+1
      · rw [wordLeft_vanish hD a x ω E F n hEF v hv q hq]
        simpa [normD] using hT
      have hq' : q+x.2+1 ≤ F := by omega
      let G := F-(q+x.2+1)
      have hG : G ≤ M := by dsimp [G]; omega
      have htail : (E : ℤ)+chargeEnergy D a+wordWeight ω-(n+q)-1=G := by
        rw [hw] at hEF
        dsimp [G]
        push_cast at hEF
        omega
      have hg : ((wordField D a ω)[[n+q]]) v ∈ grade D (G : ℤ) := by
        rw [← htail]
        exact word_mode_grade a ω E (n+q) v hv
      have ht := ih E G M (n+q) htail hE hG v hv
      have hc := original_current_energy_le hD x.1 (-(q : ℤ)-1-x.2) G F M
        (by dsimp [G]; omega) hG hF _ hg
      have ha := derivative_negative_coeff_le x.2 M q (by omega)
      rw [wordLeft, derivative_modes D x, LinearMap.smul_apply, normD_smul hD]
      calc
        _ ≤ (A*b^x.2) * (L*b*normD (((wordField D a ω)[[n+q]]) v)) :=
          mul_le_mul ha hc (Real.sqrt_nonneg _) (by positivity)
        _ ≤ (A*b^x.2) * (L*b*(K*b^P*normD v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ht (mul_nonneg hL hb)) (by positivity)
        _ = T := by
          dsimp only [T]
          simp only [pow_add, pow_one]
          ring
    have hright (q : ℕ) : normD (wordRight a x ω n v q) ≤ T := by
      by_cases hs : q < x.2
      · rw [wordRight_strip a x ω n v q hs]
        simpa [normD] using hT
      by_cases hq : E+x.2 < q
      · rw [wordRight_vanish hD a x ω E n v hv q hq]
        simpa [normD] using hT
      let G := E-(q-x.2)
      have hG : G ≤ M := by dsimp [G]; omega
      have hcurr : (E : ℤ)-((q : ℤ)-x.2)=G := by dsimp [G]; omega
      have hg : LatticeFiniteNegativeGeneration.neutralMode D x.1
          ((q : ℤ)-x.2) v ∈ grade D (G : ℤ) := by
        rw [← hcurr]
        exact current_mode_grade x.1 E _ v hv
      have htail : (G : ℤ)+chargeEnergy D a+wordWeight ω-(n-q-1)-1=F := by
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
        _ = T := by
          dsimp only [T]
          simp only [pow_add, pow_one]
          ring
    have hsumL : (∑ q ∈ Finset.range (F+1), normD (wordLeft a x ω n v q)) ≤
        ((F : ℝ)+1)*T := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (F+1), T := Finset.sum_le_sum (fun q _ => hleft q)
        _ = _ := by simp
    have hsumR : (∑ q ∈ Finset.range (E+x.2+1), normD (wordRight a x ω n v q)) ≤
        ((E : ℝ)+x.2+1)*T := by
      calc
        _ ≤ ∑ _q ∈ Finset.range (E+x.2+1), T := Finset.sum_le_sum (fun q _ => hright q)
        _ = _ := by simp
    have hcount : ((F : ℝ)+1)+((E : ℝ)+x.2+1) ≤ ((x.2 : ℝ)+2)*b := by
      have he : (E : ℝ) ≤ M := by exact_mod_cast hE
      have hf : (F : ℝ) ≤ M := by exact_mod_cast hF
      dsimp [b]
      nlinarith [Nat.cast_nonneg (α := ℝ) x.2, Nat.cast_nonneg (α := ℝ) M]
    rw [word_cons_finite hD a x ω E F n hEF v hv]
    calc
      _ ≤ normD (∑ q ∈ Finset.range (F+1), wordLeft a x ω n v q) +
          normD (∑ q ∈ Finset.range (E+x.2+1), wordRight a x ω n v q) := normD_add_le hD _ _
      _ ≤ ((F : ℝ)+1)*T + ((E : ℝ)+x.2+1)*T :=
        add_le_add ((normD_sum_le hD _ _).trans hsumL) ((normD_sum_le hD _ _).trans hsumR)
      _ = (((F : ℝ)+1)+((E : ℝ)+x.2+1))*T := by ring
      _ ≤ (((x.2 : ℝ)+2)*b)*T := mul_le_mul_of_nonneg_right hcount hT
      _ = _ := by
        rw [hp]
        change (((x.2 : ℝ)+2)*b)*T =
          (K₀ * (((x.2 : ℝ)+2)*A*L*wordConstant ω))*b^(x.2+2+P)*normD v
        dsimp [T, K]
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

#check @seeded_word_energy_le
#print axioms seeded_word_energy_le
#check @word_mode_grade
#print axioms word_mode_grade
#check @word_cons_finite
#print axioms word_cons_finite
end D5.S3.VertexAlgebra.Lattice.OriginalChargedEnergy
