/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddCurrentTopDetection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeOddCurrentTopDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal weight-one neutral currents detect the native lawful Leech mixed fields. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddNeutralZhuReduction
import D5.S3.VertexAlgebra.StateField.SkewSymmetry

/-!
The commutator residue of a fixed state and a current is expanded by lattice skew
symmetry. On a nonzero charge, the current zero mode has a nonzero pairing, and
every positive current mode has lower source weight before translation.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeInvolution LatticePositiveEnergy
open LatticeActualVertexAlgebra LatticeSugawaraConformal MvPolynomial
open LatticeFiniteNegativeGeneration (neutralMode neutralPolynomialMode norm_positive)
open LatticeSugawaraCurrents (neutralMode_single)
open ActualLeechHyperbolic (leechData leech_spec)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open StateFieldResidueReconstruction (integerBinomial)

open private topEvaluationAgreement mem_topEvaluationAgreement
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddNeutralZhuReduction
open private oddCurrent_grade_one
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private antisymmetrize charge_pairing_sum current_mode
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
open private oddPart oddPart_grade oddPart_on_odd oddResidue_finite
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
open private theta_gradeProjection
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTopDetection

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

local instance (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    AddCommGroup (twistedTop D hu s) :=
  @Submodule.addCommGroup ℂ (Twisted D hu s) _ _ _ (twistedTop D hu s)

private theorem agreement_translation (F G : LawfulMixedField D hu s)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (b : OddCarrier D) (h : ℤ) (hb : b.val ∈ grade D h)
    (he : b ∈ topEvaluationAgreement F G) :
    (oddTranslation D b).val ∈ grade D (h + 1) ∧
      oddTranslation D b ∈ topEvaluationAgreement F G := by
  have ht : (oddTranslation D b).val ∈ grade D (h + 1) := by
    have hv : vacuum D ∈ grade D 0 := by
      rw [grade_zero D hD]
      exact Submodule.subset_span (Set.mem_singleton _)
    change translation D b.val ∈ _
    rw [translation_as_mode]
    have hm := actual_mode_grade D (actualInverse D) (actualInverse_left D hu)
      (actualInverse_right D hu) h 0 (-2) b.val (vacuum D) hb hv
    rwa [show h + 0 - (-2) - 1 = h + 1 by omega] at hm
  refine ⟨ht, (mem_topEvaluationAgreement F G _).mpr fun v => ?_⟩
  apply Subtype.ext
  rw [zhuTopEvaluation_homogeneous F v _ _ ht, zhuTopEvaluation_homogeneous G v _ _ ht,
    F.derivative, G.derivative, show twistedTopZhuIndex s (h + 1) - 1 =
      twistedTopZhuIndex s h by cases s <;> simp only [twistedTopZhuIndex,
        Bool.false_eq_true, ite_false, ite_true] <;> omega,
    ← zhuTopEvaluation_homogeneous F v h b hb, ← zhuTopEvaluation_homogeneous G v h b hb,
    (mem_topEvaluationAgreement F G b).mp he v]

private theorem agreement_translation_pow (F G : LawfulMixedField D hu s)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (b : OddCarrier D) (h : ℤ) (hb : b.val ∈ grade D h)
    (he : b ∈ topEvaluationAgreement F G) (j : ℕ) :
    ((oddTranslation D ^ j) b).val ∈ grade D (h + j) ∧
      (oddTranslation D ^ j) b ∈ topEvaluationAgreement F G := by
  induction j with
  | zero =>
    simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero] using And.intro hb he
  | succ j ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.cast_succ, add_assoc] using
      agreement_translation F G hD _ _ ih.1 ih.2

private def currentOnFixed (i : Fin D.rank) (k : ℤ) (a : FixedCarrier D) : OddCarrier D :=
  ⟨mu D (oddCurrent D i).val k a.val, (mem_eigenspace D (-1) _).mpr (by
    change theta D (((Y D (oddCurrent D i).val)[[k]]) a.val) =
      (-1 : ℂ) • (((Y D (oddCurrent D i).val)[[k]]) a.val)
    simpa only [mul_one] using mode_eigenvalue_selection D (-1) 1
      (oddCurrent D i).val a.val ((mem_eigenspace D (-1) _).mp (oddCurrent D i).property)
      (by rw [one_smul]; exact (mem_fixedSpace D _).mp a.property) k)⟩

private theorem oddTranslation_pow_val (j : ℕ) (b : OddCarrier D) :
    ((oddTranslation D ^ j) b).val = (translation D ^ j) b.val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [pow_succ', Module.End.mul_apply]
    change translation D (((oddTranslation D ^ j) b).val) = _
    rw [ih]

private theorem residue_agreement_of_current (F G : LawfulMixedField D hu s)
    (a : FixedCarrier D) (d : ℕ) (ha : a.val ∈ grade D (d : ℤ)) (i : Fin D.rank)
    (hi : oddCurrent D i ∈ topEvaluationAgreement F G) :
    oddZhuResidue a (oddCurrent D i) ((d : ℤ) - 1) 0 ∈ topEvaluationAgreement F G := by
  apply (mem_topEvaluationAgreement F G _).mpr
  intro v
  have hf := zhuTopEvaluation_residue F a (oddCurrent D i) v d 1 ((d : ℤ) - 1) 0
    ha (oddCurrent_grade_one D i) le_rfl (by omega)
  have hg := zhuTopEvaluation_residue G a (oddCurrent D i) v d 1 ((d : ℤ) - 1) 0
    ha (oddCurrent_grade_one D i) le_rfl (by omega)
  rw [hf, hg, (mem_topEvaluationAgreement F G _).mp hi v,
    (mem_topEvaluationAgreement F G _).mp hi (fixedTopZero s a d ha v)]

private theorem current_zero_agreement (F G : LawfulMixedField D hu s)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : FixedCarrier D) (d : ℕ) (ha : a.val ∈ grade D (d : ℤ)) (i : Fin D.rank)
    (hi : oddCurrent D i ∈ topEvaluationAgreement F G)
    (lower : ∀ (h : ℤ) (b : OddCarrier D), h < (d : ℤ) →
      b.val ∈ grade D h → b ∈ topEvaluationAgreement F G) :
    currentOnFixed i 0 a ∈ topEvaluationAgreement F G := by
  classical
  let S := topEvaluationAgreement F G
  let term (k : ℤ) (j : ℕ) : OddCarrier D :=
    (((-1 : ℂ) ^ (k + (j : ℤ) + 1)) / (j.factorial : ℂ)) •
      (oddTranslation D ^ j) (currentOnFixed i (k + j) a)
  have hs (k : ℤ) : Function.HasFiniteSupport (term k) ∧
      oddMode D a k (oddCurrent D i) = ∑ᶠ j : ℕ, term k j := by
    obtain ⟨hfin, h⟩ := (StateField.SkewSymmetry.skew_symmetry (actualVertexAlgebra D)
      a.val (oddCurrent D i).val).1 k
    have hval (j : ℕ) : (term k j).val =
        (((-1 : ℂ) ^ (k + (j : ℤ) + 1)) / (j.factorial : ℂ)) •
          (translation D ^ j) (mu D (oddCurrent D i).val (k + j) a.val) := by
      simp only [term, Submodule.coe_smul, oddTranslation_pow_val]
      rfl
    have hf : Function.HasFiniteSupport (term k) := hfin.subset (by
      intro j hj hz
      apply hj
      apply Subtype.ext
      exact (hval j).trans hz)
    refine ⟨hf, Subtype.ext ?_⟩
    change (oddMode D a k (oddCurrent D i)).val =
      (minusSpace D).subtype (∑ᶠ j : ℕ, term k j)
    rw [map_finsum _ hf]
    simp only [Submodule.subtype_apply, hval]
    exact h
  have hp (k : ℤ) (j : ℕ) (hk : 0 < k + (j : ℤ)) : term k j ∈ S := by
    let b := currentOnFixed i (k + j) a
    have hb : b.val ∈ grade D ((d : ℤ) - (k + j)) := by
      have h := actual_mode_grade D (actualInverse D) (actualInverse_left D hu)
        (actualInverse_right D hu) 1 (d : ℤ) (k + j) (oddCurrent D i).val a.val
        (oddCurrent_grade_one D i) ha
      rwa [show 1 + (d : ℤ) - (k + j) - 1 = (d : ℤ) - (k + j) by omega] at h
    exact S.smul_mem _ (agreement_translation_pow F G hD b _ hb
      (lower _ b (by omega) hb) j).2
  have hm (k : ℤ) (hk : 0 < k) : oddMode D a k (oddCurrent D i) ∈ S := by
    rw [(hs k).2]
    apply finsum_induction _ S.zero_mem (fun _ _ => S.add_mem)
    intro j
    exact hp k j (by omega)
  have hq (b : OddCarrier D) : S.mkQ b = 0 ↔ b ∈ S := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hres := (hq _).mpr (residue_agreement_of_current F G a d ha i hi)
  unfold oddZhuResidue at hres
  rw [map_finsum S.mkQ (oddResidue_finite a (oddCurrent D i) ((d : ℤ) - 1) 0),
    finsum_eq_single _ 0] at hres
  · simp only [Nat.cast_zero, add_zero, integerBinomial, Ring.choose_zero_right,
      Int.cast_one, one_smul] at hres
    rw [(hs 0).2, map_finsum S.mkQ (hs 0).1, finsum_eq_single _ 0] at hres
    · have hlead := (hq _).mp hres
      simpa [term] using S.neg_mem hlead
    · intro j hj
      exact (hq _).mpr (hp 0 j (by omega))
  · intro j hj
    exact (hq _).mpr (S.smul_mem _ (hm (0 + (j : ℤ)) (by omega)))

private def fixedSymmetric (x : Carrier D) : FixedCarrier D :=
  ⟨x + theta D x, (mem_fixedSpace D _).mpr (by
    rw [map_add, show theta D (theta D x) = x from theta_involutive D x, add_comm])⟩

private theorem fixedSymmetric_grade (x : Carrier D) (d : ℤ) (hx : x ∈ grade D d) :
    (fixedSymmetric x).val ∈ grade D d := by
  have ht := (congrArg (theta D) (gradeProjection_eq_self_of_mem_grade D d x hx)).symm
  rw [theta_gradeProjection] at ht
  exact (grade D d).add_mem hx (ht.symm ▸ gradeProjection_mem D d (theta D x))

private theorem current_zero_symmetric (c : Charge D) (p : Oscillator D) (i : Fin D.rank) :
    currentOnFixed i 0 (fixedSymmetric (Finsupp.single c p)) =
      (bilinear D (unitCharge D i) c : ℂ) • antisymmetrize D (Finsupp.single c p) := by
  apply Subtype.ext
  change mu D (oddCurrent D i).val 0 (Finsupp.single c p + theta D (Finsupp.single c p)) =
    (bilinear D (unitCharge D i) c : ℂ) • (Finsupp.single c p - theta D (Finsupp.single c p))
  rw [current_mode, map_add]
  have htheta : neutralMode D i 0 (theta D (Finsupp.single c p)) =
      -theta D (neutralMode D i 0 (Finsupp.single c p)) := by
    rw [theta_neutralMode, neg_neg]
  have hmode : neutralMode D i 0 (Finsupp.single c p) =
      (bilinear D (unitCharge D i) c : ℂ) • Finsupp.single c p := by
    rw [neutralMode_single, Finsupp.smul_single]
    simp [neutralPolynomialMode]
  rw [htheta, hmode, map_smul, ← sub_eq_add_neg, smul_sub]

private theorem agreement_of_currents (F G : LawfulMixedField D hu s)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hcurr : ∀ i : Fin D.rank, oddCurrent D i ∈ topEvaluationAgreement F G) :
    ∀ b : OddCarrier D, b ∈ topEvaluationAgreement F G := by
  classical
  let S := topEvaluationAgreement F G
  have hn (h : ℤ) (hh : h < 0) (b : OddCarrier D) (hb : b.val ∈ grade D h) : b ∈ S := by
    suffices hz : b = 0 from hz.symm ▸ S.zero_mem
    apply Subtype.ext
    apply Finsupp.ext
    intro c
    change b.val c = 0
    apply MvPolynomial.eq_zero_iff.mpr
    intro m
    apply (mem_grade_iff D h b.val).mp hb (c, m)
    have hcharge := chargeEnergy_nonneg D hD c
    change chargeEnergy D c + (oscillatorEnergy m : ℤ) ≠ h
    omega
  have allGrades (d : ℕ) (b : OddCarrier D) (hb : b.val ∈ grade D (d : ℤ)) : b ∈ S := by
    induction d using Nat.strong_induction_on generalizing b with
    | h d ih =>
      have lower (h : ℤ) (x : OddCarrier D) (hlt : h < (d : ℤ)) (hx : x.val ∈ grade D h) :
          x ∈ S := by
        by_cases hneg : h < 0
        · exact hn h hneg x hx
        · exact ih h.toNat (by omega) x (by rwa [Int.toNat_of_nonneg (by omega)])
      rw [← oddPart_on_odd b]
      change b.val ∈ S.comap (oddPart D)
      rw [grade_eq_span] at hb
      refine (Submodule.span_le.mpr ?_) hb
      rintro _ ⟨⟨c, m⟩, hm, rfl⟩
      change energy D (c, m) = (d : ℤ) at hm
      rw [carrierBasis_apply]
      let p : Oscillator D := monomial m 1
      change oddPart D (Finsupp.single c p) ∈ S
      by_cases hc : c = 0
      · subst c
        have hz : oddPart D (Finsupp.single 0 p) ∈ chargeZeroOdd D := by
          change (2 : ℂ)⁻¹ • (Finsupp.single (0 : Charge D) p -
            thetaLinear D (Finsupp.single 0 p)) ∈
              Finsupp.supported (Oscillator D) ℂ ({0} : Set (Charge D))
          rw [theta_single, neg_zero]
          exact Submodule.smul_mem _ _ (Submodule.sub_mem _
            (Finsupp.single_mem_supported ℂ _ (by simp)) (Finsupp.single_mem_supported ℂ _ (by simp)))
        exact (mem_topEvaluationAgreement F G _).mpr fun v =>
          zhuTopEvaluation_eq_on_chargeZero_of_currents F G
            (fun i => (mem_topEvaluationAgreement F G _).mp (hcurr i)) ⟨_, hz⟩ v
      have hnorm : (bilinear D c c : ℂ) ≠ 0 := by
        exact_mod_cast ne_of_gt (norm_positive D hD c hc)
      obtain ⟨i, hi⟩ : ∃ i : Fin D.rank, (bilinear D (unitCharge D i) c : ℂ) ≠ 0 := by
        by_contra! hall
        apply hnorm
        rw [← charge_pairing_sum]
        simp only [hall, mul_zero, Finset.sum_const_zero]
      have hg : Finsupp.single c p ∈ grade D (d : ℤ) := by
        change Finsupp.single (c, m).1 (monomial (c, m).2 (1 : ℂ)) ∈ grade D (d : ℤ)
        rw [← carrierBasis_apply, grade_eq_span]
        exact Submodule.subset_span ⟨(c, m), hm, rfl⟩
      have he := current_zero_agreement F G hD (fixedSymmetric (Finsupp.single c p)) d
        (fixedSymmetric_grade _ _ hg) i (hcurr i) lower
      rw [current_zero_symmetric] at he
      have ha : antisymmetrize D (Finsupp.single c p) ∈ S := by
        simpa only [smul_smul, inv_mul_cancel₀ hi, one_smul] using
          S.smul_mem (bilinear D (unitCharge D i) c : ℂ)⁻¹ he
      exact S.smul_mem (2 : ℂ)⁻¹ ha
  intro b
  let part (h : ℤ) : OddCarrier D := oddPart D (gradeProjection D h b.val)
  have hs : (∑ h ∈ stateEnergies D b.val, part h) = b := by
    change (∑ h ∈ stateEnergies D b.val, oddPart D (gradeProjection D h b.val)) = b
    rw [← map_sum, sum_gradeProjections, oddPart_on_odd]
  rw [← hs]
  apply S.sum_mem
  intro h hh
  have hg := oddPart_grade (D := D) h ⟨gradeProjection D h b.val, gradeProjection_mem D h b.val⟩
  exact allGrades h.toNat (part h)
    (by rwa [Int.toNat_of_nonneg (stateEnergies_nonneg hD b.val h hh)])

/-- In either parity direction, the Zhu coefficients of the literal weight-one
Leech currents on the input top determine the entire lawful mixed field. -/
theorem leech_eq_of_zhuTopEvaluation_agrees_on_currents {s : Bool}
    (F G : LawfulMixedField leechData leechUnit s)
    (hcurr : ∀ (i : Fin leechData.rank) (v : twistedTop leechData leechUnit s),
      zhuTopEvaluation F v (oddCurrent leechData i) =
        zhuTopEvaluation G v (oddCurrent leechData i)) :
    F = G := by
  have h := agreement_of_currents F G leech_spec.2.2.1
    (fun i => (mem_topEvaluationAgreement F G _).mpr (hcurr i))
  apply leech_zhuTopEvaluation_injective s
  funext v
  exact LinearMap.ext fun b => (mem_topEvaluationAgreement F G b).mp (h b) v

end

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
