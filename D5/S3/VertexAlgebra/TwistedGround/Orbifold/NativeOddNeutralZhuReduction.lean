/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddNeutralZhuReduction
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddNeutralZhuReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual quadratic Zhu products reduce neutral odd sources to the weight-one currents. -/

import D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance

/-!
Quadratic Zhu products reduce odd neutral oscillator words to literal currents.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeInvolution LatticePositiveEnergy LatticeSugawaraConformal
open LatticeSugawaraCurrents LatticeActualConformalState MvPolynomial
open LatticeFiniteNegativeGeneration (neutralField)
open Lattice.ActualFixedC2
open ActualLeechHyperbolic (leechData)
open private embed polynomialLength single_state_field jet_negative_length jet_nonneg_length
  from D5.S3.VertexAlgebra.Lattice.FixedC2.ActualFixedC2NeutralMonomials
open private derivative_creativity
  from D5.S3.VertexAlgebra.LatticeAllStateField
open private multiplication_recursion
  from D5.S3.VertexAlgebra.Sectors.LatticeDualCosetModule
open private oddPart oddPart_on_odd oddResidue_nat exists_single_charge_zero
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
open private theta_gradeProjection
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection

noncomputable section

private abbrev neutralJet (D : LatticeData) (x : Index D) :=
  FieldNormalProduct.dividedDerivative x.2 (neutralField D x.1)

private theorem neutralLength_eq_span_words (D : LatticeData) (n : ℕ) :
    neutralLength D n = Submodule.span ℂ
      {v | ∃ w : List (Index D), w.length = n ∧ v = neutralWord D w} := by
  unfold neutralLength polynomialLength
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨neutralPolynomial D w, ⟨w, hw, rfl⟩, rfl⟩

/-- The neutral oscillator filtration at a fixed parity. -/
private def neutralLengthLEParity (D : LatticeData) (n : ℕ) : Submodule ℂ (Carrier D) :=
  Submodule.span ℂ {v | ∃ w : List (Index D),
    w.length ≤ n ∧ w.length % 2 = n % 2 ∧ v = neutralWord D w}

private theorem neutralLength_le_filtration (D : LatticeData) {k n : ℕ}
    (hle : k ≤ n) (hpar : k % 2 = n % 2) :
    neutralLength D k ≤ neutralLengthLEParity D n := by
  rw [neutralLength_eq_span_words]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨w, hw, rfl⟩
  exact Submodule.subset_span ⟨w, by simpa only [hw] using hle,
    by simpa only [hw] using hpar, rfl⟩

private theorem nonneg_jet_on_length (D : LatticeData) (x : Index D) (m : ℤ)
    (hm : 0 ≤ m) {n : ℕ} {v : Carrier D} (hv : v ∈ neutralLength D n) :
    ((neutralJet D x)[[m]]) v ∈ neutralLength D (n - 1) := by
  rw [neutralLength_eq_span_words] at hv
  change v ∈ (neutralLength D (n - 1)).comap ((neutralJet D x)[[m]])
  refine (Submodule.span_le.mpr ?_) hv
  rintro _ ⟨w, rfl, rfl⟩
  change ((neutralJet D x)[[m]]) (neutralWord D w) ∈ neutralLength D (w.length - 1)
  cases w with
  | nil =>
    rw [show neutralWord D [] = vacuum D from rfl, derivative_creativity D x m hm]
    exact Submodule.zero_mem _
  | cons y w => exact jet_nonneg_length D x m hm y w

private theorem nonneg_jet_on_length_zero (D : LatticeData) (x : Index D) (m : ℤ)
    (hm : 0 ≤ m) {v : Carrier D} (hv : v ∈ neutralLength D 0) :
    ((neutralJet D x)[[m]]) v = 0 := by
  rw [neutralLength_eq_span_words] at hv
  refine LinearMap.mem_ker.mp
    (show v ∈ LinearMap.ker ((neutralJet D x)[[m]]) from ?_)
  refine (Submodule.span_le.mpr ?_) hv
  rintro _ ⟨w, hw, rfl⟩
  have hnil : w = [] := List.length_eq_zero_iff.mp hw
  subst w
  exact LinearMap.mem_ker.mpr (derivative_creativity D x m hm)

private theorem neutralPair_field (D : LatticeData) (x y : Index D) :
    Y D (neutralPair D x.1 y.1 x.2 y.2).val =
      (FieldNormalProduct.normalMinusOne (neutralJet D x) (neutralJet D y)).1 := by
  change Y D (Finsupp.single 0 (X x * X y)) = _
  rw [multiplication_recursion D x 0 (X y)]
  change (FieldNormalProduct.normalMinusOne (neutralJet D x) (Y D (embed D (X y)))).1 = _
  rw [single_state_field D y]

/-- Both normal-ordering sums of a nonnegative quadratic mode preserve the
same-parity filtration. A double contraction belongs to exact length two
below the input, and vanishes on a singleton. -/
private theorem neutralPair_nonneg_mode_mem_length (D : LatticeData) (x y : Index D)
    (r : ℤ) (hr : 0 ≤ r) (w : List (Index D)) :
    mu D (neutralPair D x.1 y.1 x.2 y.2).val r (neutralWord D w) ∈
      neutralLengthLEParity D w.length := by
  cases w with
  | nil =>
    rw [show neutralWord D [] = vacuum D from rfl, show
      mu D _ r (vacuum D) = 0 from stateField_creativity D _ r hr]
    exact Submodule.zero_mem _
  | cons z w =>
    let N := neutralLengthLEParity D (z :: w).length
    let A := neutralJet D x
    let B := neutralJet D y
    let v := neutralWord D (z :: w)
    change ((Y D (neutralPair D x.1 y.1 x.2 y.2).val)[[r]]) v ∈ N
    rw [neutralPair_field, (FieldNormalProduct.normalMinusOne A B).2]
    apply N.add_mem
    · apply finsum_induction _ N.zero_mem (fun _ _ => N.add_mem)
      intro j
      have h := jet_negative_length D x (-(j : ℤ) - 1) (by omega) w.length _
        (jet_nonneg_length D y (r + j) (by omega) z w)
      exact neutralLength_le_filtration D (k := w.length + 1) (n := (z :: w).length)
        (by simp) (by simp) h
    · apply finsum_induction _ N.zero_mem (fun _ _ => N.add_mem)
      intro j
      have hj := jet_nonneg_length D x (j : ℤ) (by omega) z w
      by_cases hm : r - (j : ℤ) - 1 < 0
      · have h := jet_negative_length D y _ hm w.length _ hj
        exact neutralLength_le_filtration D (k := w.length + 1) (n := (z :: w).length)
          (by simp) (by simp) h
      · by_cases hw : w.length = 0
        · have hj0 : ((A[[(j : ℤ)]])) v ∈ neutralLength D 0 := by
            simpa only [hw] using hj
          change (B[[r - (j : ℤ) - 1]]) ((A[[(j : ℤ)]]) v) ∈ N
          rw [nonneg_jet_on_length_zero D y _ (by omega) hj0]
          exact N.zero_mem
        · have h := nonneg_jet_on_length D y (r - (j : ℤ) - 1) (by omega) hj
          exact neutralLength_le_filtration D (k := w.length - 1) (n := (z :: w).length)
            (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega) h

private theorem theta_neutral_word (D : LatticeData) (w : List (Index D)) :
    theta D (neutralWord D w) = (-1 : ℂ)^w.length • neutralWord D w := by
  change thetaLinear D (Finsupp.single 0 (neutralPolynomial D w)) =
    _ • Finsupp.single 0 (neutralPolynomial D w)
  have hs : sigma D (neutralPolynomial D w) =
      (-1 : ℂ)^w.length • neutralPolynomial D w := sigma_word_product D w
  rw [theta_single, neg_zero, hs, Finsupp.smul_single]

/-- A vacuum-charge word of odd oscillator length in the actual odd carrier. -/
private def oddNeutralWord (D : LatticeData) (w : List (Index D)) (hw : Odd w.length) :
    OddCarrier D :=
  ⟨neutralWord D w, (mem_eigenspace D (-1) _).mpr (by
    rw [theta_neutral_word, hw.neg_one_pow])⟩

private theorem oddPart_neutral_word (D : LatticeData) (w : List (Index D))
    (hw : Odd w.length) : oddPart D (neutralWord D w) = oddNeutralWord D w hw :=
  oddPart_on_odd (oddNeutralWord D w hw)

private def neutralWordWeight (D : LatticeData) (w : List (Index D)) : ℕ :=
  (w.map (oscillatorWeight D)).sum

private theorem neutralPolynomial_weight (D : LatticeData) (w : List (Index D)) :
    IsWeightedHomogeneous (oscillatorWeight D) (neutralPolynomial D w) (neutralWordWeight D w) := by
  induction w with
  | nil => exact isWeightedHomogeneous_one ℂ (oscillatorWeight D)
  | cons x w ih => exact (isWeightedHomogeneous_X ℂ (oscillatorWeight D) x).mul ih

private theorem neutralWord_grade (D : LatticeData) (w : List (Index D)) :
    neutralWord D w ∈ grade D (neutralWordWeight D w : ℤ) := by
  have h := Lattice.ActualZhuCurrentRelations.single_weighted_grade
    D 0 _ _ (neutralPolynomial_weight D w)
  change Finsupp.single (0 : Charge D) (neutralPolynomial D w) ∈
    grade D (neutralWordWeight D w : ℤ)
  rw [chargeEnergy_zero, zero_add] at h
  exact h

/-- Conformal weight of the actual neutral pair used for the left Zhu product. -/
private theorem neutralPair_grade (D : LatticeData) (x y : Index D) :
    (neutralPair D x.1 y.1 x.2 y.2).val ∈ grade D ((x.2 + 1 + (y.2 + 1) : ℕ) : ℤ) := by
  have h := neutralWord_grade D [x, y]
  change Finsupp.single 0 (X x * (X y * 1)) ∈ grade D
    ((x.2 + 1 + (y.2 + 1) : ℕ) : ℤ) at h
  rw [mul_one] at h
  exact h

private theorem odd_cons_cons (D : LatticeData) (x y : Index D) (w : List (Index D))
    (hw : Odd w.length) : Odd (x :: y :: w).length := by
  rw [Nat.odd_iff] at hw ⊢
  simp only [List.length_cons]
  omega

/-- Subtracting the leading concatenation from the actual left quadratic Zhu
residue gives odd words of length at most the input length. -/
private theorem oddZhuResidue_neutralPair_sub_word_mem (D : LatticeData)
    (x y : Index D) (w : List (Index D)) (hw : Odd w.length) :
    let a := neutralPair D x.1 y.1 x.2 y.2
    let d := x.2 + 1 + (y.2 + 1)
    (oddZhuResidue a (oddNeutralWord D w hw) (d : ℤ) (-1) -
      oddNeutralWord D (x :: y :: w) (odd_cons_cons D x y w hw)).val ∈
        neutralLengthLEParity D w.length := by
  dsimp only
  let N := neutralLengthLEParity D w.length
  rw [oddResidue_nat]
  change (minusSpace D).subtype (_ - _) ∈ N
  rw [map_sub, map_sum, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_smul, map_smul]
  have hlead : (oddMode D (neutralPair D x.1 y.1 x.2 y.2) (-1)
        (oddNeutralWord D w hw)).val - neutralWord D (x :: y :: w) ∈ N :=
    neutralLength_le_filtration D le_rfl rfl (quadratic_word_length D x y w)
  have htail : (∑ i ∈ Finset.range (x.2 + 1 + (y.2 + 1)),
      ((x.2 + 1 + (y.2 + 1)).choose (i + 1) : ℂ) •
        (oddMode D (neutralPair D x.1 y.1 x.2 y.2) (-1 + ((i + 1 : ℕ) : ℤ))
          (oddNeutralWord D w hw)).val) ∈ N := by
    apply N.sum_mem
    intro i _
    exact N.smul_mem _ (neutralPair_nonneg_mode_mem_length D x y _ (by omega) w)
  rw [add_sub_assoc]
  exact N.add_mem htail hlead

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

local instance (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    AddCommGroup (twistedTop D hu s) :=
  @Submodule.addCommGroup ℂ (Twisted D hu s) _ _ _ (twistedTop D hu s)

private def oddLeftZhu (a : FixedCarrier D) (d : ℕ) : Module.End ℂ (OddCarrier D) :=
  ∑ i ∈ Finset.range (d + 1), (d.choose i : ℂ) • oddMode D a (-1 + (i : ℤ))

private theorem oddLeftZhu_apply (a : FixedCarrier D) (d : ℕ) (b : OddCarrier D) :
    oddLeftZhu a d b = oddZhuResidue a b (d : ℤ) (-1) := by
  simp only [oddResidue_nat, oddLeftZhu, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Left Zhu balance extends linearly to every actual odd source, including
states with several conformal grades. -/
private theorem zhuTopEvaluation_left (F : LawfulMixedField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (v : twistedTop D hu s)
    (d : ℕ) (ha : a.val ∈ grade D (d : ℤ)) :
    zhuTopEvaluation F v (oddZhuResidue a b (d : ℤ) (-1)) =
      fixedTopZero (!s) a d ha (zhuTopEvaluation F v b) := by
  let part (h : ℤ) : OddCarrier D := ⟨gradeProjection D h b.val, by
    change gradeProjection D h b.val ∈ eigenspace D (-1)
    rw [mem_eigenspace, theta_gradeProjection,
      (mem_eigenspace D (-1) b.val).mp b.property, map_smul]⟩
  have hsum : (∑ h ∈ stateEnergies D b.val, part h) = b := by
    apply Subtype.ext
    change (minusSpace D).subtype (∑ h ∈ stateEnergies D b.val, part h) = b.val
    rw [map_sum]
    exact sum_gradeProjections D b.val
  rw [← oddLeftZhu_apply a d b]
  let left := (zhuTopEvaluation F v).comp (oddLeftZhu a d)
  let right := (fixedTopZero (!s) a d ha).comp (zhuTopEvaluation F v)
  change left b = right b
  rw [← hsum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro h _
  change zhuTopEvaluation F v (oddLeftZhu a d (part h)) =
    fixedTopZero (!s) a d ha (zhuTopEvaluation F v (part h))
  rw [oddLeftZhu_apply]
  exact (zhuTopEvaluation_balanced F a (part h) v d h ha
    (gradeProjection_mem D h b.val)).1

private def topEvaluationAgreement (F G : LawfulMixedField D hu s) :
    Submodule ℂ (OddCarrier D) :=
  ⨅ v : twistedTop D hu s, LinearMap.ker (zhuTopEvaluation F v - zhuTopEvaluation G v)

private theorem mem_topEvaluationAgreement (F G : LawfulMixedField D hu s) (b : OddCarrier D) :
    b ∈ topEvaluationAgreement F G ↔
      ∀ v : twistedTop D hu s, zhuTopEvaluation F v b = zhuTopEvaluation G v b := by
  simp only [topEvaluationAgreement, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, sub_eq_zero]

private theorem topEvaluationAgreement_left (F G : LawfulMixedField D hu s)
    (a : FixedCarrier D) (b : OddCarrier D) (d : ℕ)
    (ha : a.val ∈ grade D (d : ℤ)) (he : b ∈ topEvaluationAgreement F G) :
    oddZhuResidue a b (d : ℤ) (-1) ∈ topEvaluationAgreement F G := by
  apply (mem_topEvaluationAgreement F G _).mpr
  intro v
  rw [zhuTopEvaluation_left F a b v d ha, zhuTopEvaluation_left G a b v d ha,
    (mem_topEvaluationAgreement F G b).mp he v]

private theorem oddSingleton_grade (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (hk : Odd ([(i, k)] : List (Index D)).length) :
    (oddNeutralWord D [(i, k)] hk).val ∈ grade D ((k + 1 : ℕ) : ℤ) :=
  neutralWord_grade D [(i, k)]

private theorem oddSingleton_zero (D : LatticeData) (i : Fin D.rank)
    (hh : Odd ([(i, 0)] : List (Index D)).length) :
    oddNeutralWord D [(i, 0)] hh = oddCurrent D i := by
  apply Subtype.ext
  change Finsupp.single 0 (X (i, 0) * 1) = _
  rw [mul_one]
  change Finsupp.single 0 (X (i, 0)) =
    LatticeFiniteNegativeGeneration.neutralMode D i (-1) (vacuum D)
  simpa only [currentState, neutralField_ncoeff] using (current_state_creation D i).symm

private theorem oddSingleton_translation (D : LatticeData) (i : Fin D.rank) (k : ℕ)
    (hk : Odd ([(i, k)] : List (Index D)).length)
    (hk' : Odd ([(i, k + 1)] : List (Index D)).length) :
    oddTranslation D (oddNeutralWord D [(i, k)] hk) =
      (k + 1 : ℂ) • oddNeutralWord D [(i, k + 1)] hk' := by
  apply Subtype.ext
  change translation D (Finsupp.single 0 (X (i, k) * 1)) =
    (k + 1 : ℂ) • Finsupp.single 0 (X (i, k + 1) * 1)
  simp only [mul_one, translation_single, chargePolynomial, Pi.zero_apply, Int.cast_zero,
    zero_smul, Finset.sum_const_zero, zero_mul, add_zero, oscillatorDerivation,
    MvPolynomial.mkDerivation_X, Finsupp.smul_single]

private theorem oddSingleton_mem_topAgreement (F G : LawfulMixedField D hu s)
    (hcurr : ∀ i : Fin D.rank, oddCurrent D i ∈ topEvaluationAgreement F G)
    (i : Fin D.rank) (k : ℕ) (hk : Odd ([(i, k)] : List (Index D)).length) :
    oddNeutralWord D [(i, k)] hk ∈ topEvaluationAgreement F G := by
  revert hk
  induction k with
  | zero =>
    intro hk
    rw [oddSingleton_zero]
    exact hcurr i
  | succ k ih =>
    intro hk
    let b := oddNeutralWord D [(i, k)] (by simp)
    let c := oddNeutralWord D [(i, k + 1)] hk
    have ht : oddTranslation D b = (k + 1 : ℂ) • c :=
      oddSingleton_translation D i k _ _
    have hb : b.val ∈ grade D ((k + 1 : ℕ) : ℤ) := oddSingleton_grade D i k _
    have hc : c.val ∈ grade D (((k + 1) + 1 : ℕ) : ℤ) :=
      oddSingleton_grade D i (k + 1) _
    have hct : (oddTranslation D b).val ∈ grade D (((k + 1) + 1 : ℕ) : ℤ) := by
      rw [ht]
      exact (grade D _).smul_mem _ hc
    have he : oddTranslation D b ∈ topEvaluationAgreement F G := by
      apply (mem_topEvaluationAgreement F G _).mpr
      intro v
      apply Subtype.ext
      rw [zhuTopEvaluation_homogeneous F v _ _ hct, zhuTopEvaluation_homogeneous G v _ _ hct,
        F.derivative, G.derivative]
      have hi : twistedTopZhuIndex s (((k + 1) + 1 : ℕ) : ℤ) - 1 =
          twistedTopZhuIndex s ((k + 1 : ℕ) : ℤ) := by
        cases s <;> simp only [twistedTopZhuIndex, Bool.false_eq_true, ite_false, ite_true,
          Nat.cast_add, Nat.cast_one] <;> omega
      rw [hi, ← zhuTopEvaluation_homogeneous F v _ b hb,
        ← zhuTopEvaluation_homogeneous G v _ b hb,
        (mem_topEvaluationAgreement F G b).mp (ih (by simp)) v]
    rw [ht] at he
    have hn : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
      (topEvaluationAgreement F G).smul_mem (k + 1 : ℂ)⁻¹ he

private theorem oddNeutralWord_mem_topAgreement (F G : LawfulMixedField D hu s)
    (hcurr : ∀ i : Fin D.rank, oddCurrent D i ∈ topEvaluationAgreement F G)
    (w : List (Index D)) (hw : Odd w.length) :
    oddNeutralWord D w hw ∈ topEvaluationAgreement F G := by
  let S := topEvaluationAgreement F G
  suffices all_lengths : ∀ n (u : List (Index D)) (hu' : Odd u.length),
      u.length = n → oddNeutralWord D u hu' ∈ S by
    exact all_lengths w.length w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hou hlen
    rcases u with _ | ⟨x, _ | ⟨y, w⟩⟩
    · simp at hou
    · exact oddSingleton_mem_topAgreement F G hcurr x.1 x.2 hou
    · have hw : Odd w.length := by
        rw [Nat.odd_iff] at hou ⊢
        simp only [List.length_cons] at hou
        omega
      have hlt : w.length < n := by simp only [List.length_cons] at hlen; omega
      let b := oddNeutralWord D w hw
      let a := neutralPair D x.1 y.1 x.2 y.2
      let d := x.2 + 1 + (y.2 + 1)
      let p := oddZhuResidue a b (d : ℤ) (-1)
      let c := oddNeutralWord D (x :: y :: w) hou
      have hp : p ∈ S := topEvaluationAgreement_left F G a b d (neutralPair_grade D x y)
        (ih w.length hlt w hw rfl)
      have hc : (p - c).val ∈ neutralLengthLEParity D w.length :=
        oddZhuResidue_neutralPair_sub_word_mem D x y w hw
      have hspan : neutralLengthLEParity D w.length ≤ S.comap (oddPart D) := by
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨t, ht, hpar, rfl⟩
        have hot : Odd t.length := by
          rw [Nat.odd_iff] at hw ⊢
          omega
        change oddPart D (neutralWord D t) ∈ S
        rw [oddPart_neutral_word D t hot]
        exact ih t.length (lt_of_le_of_lt ht hlt) t hot rfl
      have hdiff : p - c ∈ S := by
        have hproj : oddPart D (p - c).val ∈ S := hspan hc
        simpa only [oddPart_on_odd] using hproj
      simpa only [sub_sub_cancel] using S.sub_mem hp hdiff

/-- For any actual lattice datum, agreement on all weight-one currents and
twisted top inputs extends to the unrestricted neutral odd source. -/
theorem zhuTopEvaluation_eq_on_chargeZero_of_currents
    (F G : LawfulMixedField D hu s)
    (hcurr : ∀ (i : Fin D.rank) (v : twistedTop D hu s),
      zhuTopEvaluation F v (oddCurrent D i) = zhuTopEvaluation G v (oddCurrent D i))
    (b : chargeZeroOdd D) (v : twistedTop D hu s) :
    zhuTopEvaluation F v b.val = zhuTopEvaluation G v b.val := by
  let S := topEvaluationAgreement F G
  have hi (i : Fin D.rank) : oddCurrent D i ∈ S :=
    (mem_topEvaluationAgreement F G _).mpr (hcurr i)
  have hall (w : List (Index D)) : oddPart D (neutralWord D w) ∈ S := by
    rcases Nat.even_or_odd w.length with he | ho
    · have hz : oddPart D (neutralWord D w) = 0 := by
        apply Subtype.ext
        change (2 : ℂ)⁻¹ • (neutralWord D w - theta D (neutralWord D w)) = 0
        rw [theta_neutral_word, he.neg_one_pow, one_smul, sub_self, smul_zero]
      rw [hz]
      exact S.zero_mem
    · rw [oddPart_neutral_word D w ho]
      exact oddNeutralWord_mem_topAgreement F G hi w ho
  obtain ⟨p, hp⟩ := exists_single_charge_zero b.val.val b.property
  let lift : Oscillator D →ₗ[ℂ] OddCarrier D := (oddPart D).comp (Finsupp.lsingle 0)
  have hpMem : lift p ∈ S := by
    clear hp
    induction p using MvPolynomial.induction_on' with
    | monomial e z =>
      have he : monomial e z = z • neutralPolynomial D (occurrences D e) := by
        change monomial e z = z • ((occurrences D e).map (fun x => (X x : Oscillator D))).prod
        rw [occurrences_product, smul_monomial, smul_eq_mul, mul_one]
      rw [he, map_smul]
      exact S.smul_mem z (hall (occurrences D e))
    | add p q hp hq =>
      rw [map_add]
      exact S.add_mem hp hq
  have heq : lift p = b.val := by
    change oddPart D (Finsupp.single 0 p) = b.val
    rw [← hp, oddPart_on_odd]
  rw [heq] at hpMem
  exact (mem_topEvaluationAgreement F G _).mp hpMem v

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
