/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityCurrentTopDetection
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/NativeSameParityCurrentTopDetection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Vanishing of integral weight-one top coefficients forces the entire same-parity field to vanish. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParityTopDetection
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddCurrentTopDetection

/-!
The integral Zhu balance reduces charge zero by quadratic mode products.
On nonzero charge, the signed commutator residue of a fixed state with a
current isolates its current zero mode modulo translates of lower weights.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeAllStateReconstruction
open LatticeInvolution LatticePositiveEnergy LatticeActualVertexAlgebra
open LatticeSugawaraConformal MvPolynomial
open LatticeFiniteNegativeGeneration (norm_positive)
open Lattice.ActualFixedC2
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open StateFieldResidueReconstruction (integerBinomial)
open NativeOddTwistedIntertwiner (OddCarrier Twisted twistedTop twistedTopReadout
  oddMode oddTranslation oddCurrent chargeZeroOdd oddZhuResidue fixedTopZero)
open private oddCurrent_grade_one
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddTwistedIntertwiner
open private antisymmetrize charge_pairing_sum
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddSourceRestriction
open private oddPart oddPart_grade oddPart_on_odd oddResidue_finite exists_single_charge_zero
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddZhuTopBalance
open private oddLeftZhu oddLeftZhu_apply oddNeutralWord oddPart_neutral_word
    oddZhuResidue_neutralPair_sub_word_mem neutralLengthLEParity neutralPair_grade
    oddSingleton_zero oddSingleton_grade oddSingleton_translation theta_neutral_word
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddNeutralZhuReduction
open private currentOnFixed oddTranslation_pow_val fixedSymmetric fixedSymmetric_grade
    current_zero_symmetric
  from D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeOddCurrentTopDetection

noncomputable section

variable {D : LatticeData} {hu : IsUnit D.G.det} {s : Bool}

local instance (D : LatticeData) (hu : IsUnit D.G.det) (s : Bool) :
    AddCommGroup (twistedTop D hu s) :=
  @Submodule.addCommGroup ℂ (Twisted D hu s) _ _ _ (twistedTop D hu s)

private def topEvaluationKernel (F : LawfulField D hu s) : Submodule ℂ (OddCarrier D) :=
  ⨅ v : twistedTop D hu s, LinearMap.ker (zhuTopEvaluation F v)

private theorem mem_topEvaluationKernel (F : LawfulField D hu s) (b : OddCarrier D) :
    b ∈ topEvaluationKernel F ↔ ∀ v : twistedTop D hu s, zhuTopEvaluation F v b = 0 := by
  simp only [topEvaluationKernel, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem topEvaluationKernel_left (F : LawfulField D hu s)
    (a : FixedCarrier D) (d : ℕ) (ha : a.val ∈ grade D (d : ℤ))
    (b : OddCarrier D) (hb : b ∈ topEvaluationKernel F) :
    oddZhuResidue a b (d : ℤ) (-1) ∈ topEvaluationKernel F := by
  apply (mem_topEvaluationKernel F _).mpr
  intro v
  let Z := zhuTopEvaluation F v
  let left := Z.comp (oddLeftZhu a d)
  let right := (fixedTopZero s a d ha).comp Z
  let part (h : ℤ) := oddPart D (gradeProjection D h b.val)
  have hsum : (∑ h ∈ stateEnergies D b.val, part h) = b := by
    change (∑ h ∈ stateEnergies D b.val, oddPart D (gradeProjection D h b.val)) = b
    rw [← map_sum, sum_gradeProjections, oddPart_on_odd]
  have hbal : left b = right b := by
    rw [← hsum]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro h _
    have hg : (part h).val ∈ grade D h :=
      oddPart_grade h ⟨gradeProjection D h b.val, gradeProjection_mem D h b.val⟩
    change Z (oddLeftZhu a d (part h)) = fixedTopZero s a d ha (Z (part h))
    rw [oddLeftZhu_apply]
    exact (zhuTopEvaluation_balanced F a (part h) v d h ha hg).1
  change Z (oddZhuResidue a b (d : ℤ) (-1)) = 0
  rw [← oddLeftZhu_apply]
  change left b = 0
  rw [hbal]
  change fixedTopZero s a d ha (Z b) = 0
  rw [(mem_topEvaluationKernel F b).mp hb v, map_zero]

private theorem translation_mem_topEvaluationKernel (F : LawfulField D hu s)
    (b : OddCarrier D) (h : ℤ) (hb : b.val ∈ grade D h)
    (ht : (oddTranslation D b).val ∈ grade D (h + 1)) (he : b ∈ topEvaluationKernel F) :
    oddTranslation D b ∈ topEvaluationKernel F := by
  apply (mem_topEvaluationKernel F _).mpr
  intro v
  apply Subtype.ext
  rw [zhuTopEvaluation_homogeneous F v (h + 1) _ ht, F.derivative,
    show topIndex (h + 1) - 1 = topIndex h by simp only [topIndex]; omega,
    ← zhuTopEvaluation_homogeneous F v h b hb, (mem_topEvaluationKernel F b).mp he v]
  simp only [Submodule.coe_zero, smul_zero]

private theorem oddSingleton_mem_kernel (F : LawfulField D hu s)
    (hcurr : ∀ i : Fin D.rank, oddCurrent D i ∈ topEvaluationKernel F)
    (i : Fin D.rank) (k : ℕ) (hk : Odd ([(i, k)] : List (Index D)).length) :
    oddNeutralWord D [(i, k)] hk ∈ topEvaluationKernel F := by
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
    have ht : oddTranslation D b = (k + 1 : ℂ) • c := oddSingleton_translation D i k _ _
    have hb : b.val ∈ grade D ((k + 1 : ℕ) : ℤ) := oddSingleton_grade D i k _
    have hc : c.val ∈ grade D (((k + 1 : ℕ) : ℤ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using oddSingleton_grade D i (k + 1) hk
    have hgrade : (oddTranslation D b).val ∈ grade D (((k + 1 : ℕ) : ℤ) + 1) := by
      rw [ht]
      exact (grade D _).smul_mem _ hc
    have he := translation_mem_topEvaluationKernel F b _ hb hgrade (ih (by simp))
    rw [ht] at he
    have hn : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
      (topEvaluationKernel F).smul_mem (k + 1 : ℂ)⁻¹ he

private theorem oddNeutralWord_mem_kernel (F : LawfulField D hu s)
    (hcurr : ∀ i : Fin D.rank, oddCurrent D i ∈ topEvaluationKernel F)
    (w : List (Index D)) (hw : Odd w.length) :
    oddNeutralWord D w hw ∈ topEvaluationKernel F := by
  let S := topEvaluationKernel F
  suffices all_lengths : ∀ n (u : List (Index D)) (hu' : Odd u.length),
      u.length = n → oddNeutralWord D u hu' ∈ S by
    exact all_lengths w.length w hw rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u hou hlen
    rcases u with _ | ⟨x, _ | ⟨y, w⟩⟩
    · simp at hou
    · exact oddSingleton_mem_kernel F hcurr x.1 x.2 hou
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
      have hp : p ∈ S := topEvaluationKernel_left F a d (neutralPair_grade D x y) b
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

private theorem chargeZero_mem_kernel (F : LawfulField D hu s)
    (hcurr : ∀ i : Fin D.rank, oddCurrent D i ∈ topEvaluationKernel F)
    (b : chargeZeroOdd D) : b.val ∈ topEvaluationKernel F := by
  let S := topEvaluationKernel F
  have hall (w : List (Index D)) : oddPart D (neutralWord D w) ∈ S := by
    rcases Nat.even_or_odd w.length with he | ho
    · have hz : oddPart D (neutralWord D w) = 0 := by
        apply Subtype.ext
        change (2 : ℂ)⁻¹ • (neutralWord D w - theta D (neutralWord D w)) = 0
        rw [theta_neutral_word, he.neg_one_pow, one_smul, sub_self, smul_zero]
      rw [hz]
      exact S.zero_mem
    · rw [oddPart_neutral_word D w ho]
      exact oddNeutralWord_mem_kernel F hcurr w ho
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
  exact hpMem

private theorem translation_pow_mem_kernel (F : LawfulField D hu s)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (b : OddCarrier D) (h : ℤ) (hb : b.val ∈ grade D h)
    (he : b ∈ topEvaluationKernel F) (j : ℕ) :
    ((oddTranslation D ^ j) b).val ∈ grade D (h + j) ∧
      (oddTranslation D ^ j) b ∈ topEvaluationKernel F := by
  have step (c : OddCarrier D) (k : ℤ) (hc : c.val ∈ grade D k)
      (hker : c ∈ topEvaluationKernel F) :
      (oddTranslation D c).val ∈ grade D (k + 1) ∧
        oddTranslation D c ∈ topEvaluationKernel F := by
    have ht : (oddTranslation D c).val ∈ grade D (k + 1) := by
      have hv : vacuum D ∈ grade D 0 := by
        rw [grade_zero D hD]
        exact Submodule.subset_span (Set.mem_singleton _)
      change translation D c.val ∈ _
      rw [translation_as_mode]
      have hm := actual_mode_grade D (actualInverse D) (actualInverse_left D hu)
        (actualInverse_right D hu) k 0 (-2) c.val (vacuum D) hc hv
      rwa [show k + 0 - (-2) - 1 = k + 1 by omega] at hm
    exact ⟨ht, translation_mem_topEvaluationKernel F c k hc ht hker⟩
  induction j with
  | zero =>
    simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, add_zero] using And.intro hb he
  | succ j ih =>
    simpa only [pow_succ', Module.End.mul_apply, Nat.cast_succ, add_assoc] using step _ _ ih.1 ih.2

private theorem current_residue_mem_kernel (F : LawfulField D hu s)
    (a : FixedCarrier D) (d : ℕ) (ha : a.val ∈ grade D (d : ℤ)) (i : Fin D.rank)
    (hi : oddCurrent D i ∈ topEvaluationKernel F) :
    oddZhuResidue a (oddCurrent D i) ((d : ℤ) - 1) 0 ∈ topEvaluationKernel F := by
  apply (mem_topEvaluationKernel F _).mpr
  intro v
  have hz₁ := (mem_topEvaluationKernel F _).mp hi v
  have hz₂ := (mem_topEvaluationKernel F _).mp hi (fixedTopZero s a d ha v)
  rw [zhuTopEvaluation_residue F a (oddCurrent D i) v d 1 ((d : ℤ) - 1) 0
    ha (oddCurrent_grade_one D i) le_rfl (by omega)]
  simp [hz₁, hz₂]

private theorem current_zero_mem_kernel (F : LawfulField D hu s)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (a : FixedCarrier D) (d : ℕ) (ha : a.val ∈ grade D (d : ℤ)) (i : Fin D.rank)
    (hi : oddCurrent D i ∈ topEvaluationKernel F)
    (lower : ∀ (h : ℤ) (b : OddCarrier D), h < (d : ℤ) →
      b.val ∈ grade D h → b ∈ topEvaluationKernel F) :
    currentOnFixed i 0 a ∈ topEvaluationKernel F := by
  classical
  let S := topEvaluationKernel F
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
    exact S.smul_mem _ (translation_pow_mem_kernel F hD b _ hb
      (lower _ b (by omega) hb) j).2
  have hm (k : ℤ) (hk : 0 < k) : oddMode D a k (oddCurrent D i) ∈ S := by
    rw [(hs k).2]
    apply finsum_induction _ S.zero_mem (fun _ _ => S.add_mem)
    intro j
    exact hp k j (by omega)
  have hq (b : OddCarrier D) : S.mkQ b = 0 ↔ b ∈ S := by
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
  have hres := (hq _).mpr (current_residue_mem_kernel F a d ha i hi)
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

private theorem kernel_of_currents (F : LawfulField D hu s)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hcurr : ∀ i : Fin D.rank, oddCurrent D i ∈ topEvaluationKernel F) :
    ∀ b : OddCarrier D, b ∈ topEvaluationKernel F := by
  classical
  let S := topEvaluationKernel F
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
        exact chargeZero_mem_kernel F hcurr ⟨_, hz⟩
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
      have he := current_zero_mem_kernel F hD (fixedSymmetric (Finsupp.single c p)) d
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

/-- On either actual twisted parity, vanishing of the physical mode zero
of all weight-one currents on the input top forces every coefficient to vanish. -/
theorem coeff_eq_zero_of_current_zero (hrank : 2 ≤ D.rank)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (F : LawfulField D hu s)
    (hcurr : ∀ (i : Fin D.rank) (v : twistedTop D hu s),
      F.coeff 0 (oddCurrent D i) v.val = 0) :
    F.coeff = 0 := by
  have h (i : Fin D.rank) : oddCurrent D i ∈ topEvaluationKernel F := by
    apply (mem_topEvaluationKernel F _).mpr
    intro v
    apply Subtype.ext
    rw [zhuTopEvaluation_homogeneous F v 1 _ (oddCurrent_grade_one D i)]
    change F.coeff 0 (oddCurrent D i) v.val = 0
    exact hcurr i v
  apply coeff_eq_zero_of_twistedZhuTopReadout_zero hrank F
  intro w b v hb
  have hz := congrArg (fun u : twistedTop D hu s => u.val)
    ((mem_topEvaluationKernel F b).mp (kernel_of_currents F hD h b) v)
  rw [zhuTopEvaluation_homogeneous F v w b hb, Submodule.coe_zero] at hz
  rw [hz, map_zero]

end
end D5.S3.VertexAlgebra.TwistedGround.Orbifold.NativeSameParity
