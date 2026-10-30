/- GID: D5/S3/VertexAlgebra/SourceBPZ/OriginalWord
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/SourceBPZ/OriginalWord
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Labelled original word BPZ induction and finite source-flow bridge. -/

import D5.S3.VertexAlgebra.SourceBPZ.NormalScalarTranspose
import D5.S3.VertexAlgebra.LatticeAllStateField
import D5.S3.VertexAlgebra.SourceMobius.OriginalCarrier
import D5.S3.VertexAlgebra.SourceMobius.Coordinates
import D5.S3.VertexAlgebra.Sectors.LatticeSectorIntertwiner
import D5.S3.VertexAlgebra.LatticePositiveEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

noncomputable section
open scoped BigOperators VertexOperator

namespace D5.S3.VertexAlgebra.SourceBPZ

open LatticeGeneratingFieldLocality LatticeFiniteNegativeGeneration
open LatticeSugawaraCurrents FieldNormalProduct LatticeAllStateField
open LatticePositiveEnergy
open LatticeHalfFockFiniteCorrection (sourceWeight wordWeight)
open SourceMobius

/-! A choice keeps a finite labelled occurrence at an order in `0..n`, where
zero deletes the occurrence and positive values lower it to that order. -/

def WordChoice (D : LatticeData) : List (Index D) → Type
  | [] => PUnit
  | x :: w => Fin (x.2 + 2) × WordChoice D w

instance wordChoiceFinite (D : LatticeData) (w : List (Index D)) : Finite (WordChoice D w) := by
  induction w with
  | nil => change Finite PUnit; infer_instance
  | cons x w ih => change Finite (Fin (x.2 + 2) × WordChoice D w); infer_instance

instance wordChoiceFintype (D : LatticeData) (w : List (Index D)) : Fintype (WordChoice D w) :=
  by
    induction w with
    | nil => change Fintype PUnit; infer_instance
    | cons x w ih => change Fintype (Fin (x.2 + 2) × WordChoice D w); infer_instance

def choiceLower (D : LatticeData) : {w : List (Index D)} → WordChoice D w → List (Index D)
  | [], _ => []
  | x :: w, c =>
      if c.1.val = 0 then choiceLower D c.2
      else (x.1, c.1.val - 1) :: choiceLower D c.2

def choiceRetained (D : LatticeData) : {w : List (Index D)} → WordChoice D w → ℕ
  | [], _ => 0
  | x :: w, c => c.1.val + choiceRetained D c.2

def choiceCoefficient (D : LatticeData) (α : Charge D) :
    {w : List (Index D)} → WordChoice D w → ℂ
  | [], _ => 1
  | x :: w, c =>
      (if c.1.val = 0 then (bilinear D (unitCharge D x.1) α : ℂ)
       else ((x.2 + 1).choose c.1.val : ℂ)) * choiceCoefficient D α c.2

def transposeReadout (D : LatticeData) (B : LinearMap.BilinForm ℂ (Carrier D))
    (α : Charge D) : (w : List (Index D)) → ℤ → Carrier D → Carrier D → ℂ
  | w, m, u, v =>
      ∑ c ∈ (Finset.univ : Finset (WordChoice D w)),
        choiceCoefficient D α c *
          B u (((wordField D α (choiceLower D c))[[
            2 * chargeEnergy D α + (wordWeight D w : ℤ) +
              (choiceRetained D c : ℤ) - m - 2]]) v)

theorem word_choice_charge (D : LatticeData) (α β : Charge D)
    (w : List (Index D)) (n : ℤ) (v : Oscillator D) :
    ∃ p : Oscillator D,
      ((wordField D α w)[[n]]) (Finsupp.single β v) = Finsupp.single (α + β) p := by
  classical
  have neutral (x : Index D) (m : ℤ) (δ : Charge D) (p : Oscillator D) :
      ∃ q : Oscillator D,
        ((dividedDerivative x.2 (neutralField D x.1))[[m]])
            (Finsupp.single δ p) = Finsupp.single δ q := by
    refine ⟨((Ring.choose (-m - 1 + x.2) x.2 : ℤ) : ℂ) •
        neutralPolynomialMode D x.1 δ (m - x.2) p, ?_⟩
    change Ring.choose (-m - 1 + x.2) x.2 •
      HVertexOperator.coeff (neutralField D x.1) (-m - 1 + x.2)
        (Finsupp.single δ p) = _
    rw [VertexOperator.coeff_eq_ncoeff, neutralField_ncoeff, neutralMode_single,
      show -(-m - 1 + x.2) - 1 = m - x.2 by omega]
    simp only [LinearMap.smul_apply, ← Finsupp.smul_single, Int.cast_smul_eq_zsmul]
  induction w generalizing n β v with
  | nil =>
      rw [wordField, actualField, VertexOperator.ncoeff_of_coeff,
        (actual_creation_coefficient_transport D α α).2.2.1]
      refine ⟨epsilon D α β • ∑ d ∈ (translatedPolynomial D α v).support,
        (translatedPolynomial D α v).coeff d •
          creationCoeff D α (-n - 1 - bilinear D α β + d), ?_⟩
      simp [rawSingle]
  | cons x tail ih =>
      rw [wordField, (normalMinusOne _ _).2]
      have left : ∃ p : Oscillator D,
          (∑ᶠ j : ℕ,
            ((dividedDerivative x.2 (neutralField D x.1))[[ -(j : ℤ) - 1]])
              (((wordField D α tail)[[n + j]]) (Finsupp.single β v))) =
            Finsupp.single (α + β) p := by
        refine finsum_induction (fun z => ∃ p : Oscillator D,
            z = Finsupp.single (α + β) p) ?_ ?_ ?_
        · exact ⟨0, by simp⟩
        · intro a b ha hb
          obtain ⟨p, hp⟩ := ha
          obtain ⟨q, hq⟩ := hb
          refine ⟨p + q, ?_⟩
          rw [hp, hq, ← Finsupp.single_add]
        · intro j
          obtain ⟨r, hr⟩ := ih (n := n + j) (β := β) v
          obtain ⟨s, hs⟩ := neutral x (-(j : ℤ) - 1) (α + β) r
          refine ⟨s, ?_⟩
          rw [hr, hs]
      have right : ∃ p : Oscillator D,
          (∑ᶠ j : ℕ,
            ((wordField D α tail)[[n - j - 1]])
              (((dividedDerivative x.2 (neutralField D x.1))[[j]])
                (Finsupp.single β v))) =
            Finsupp.single (α + β) p := by
        refine finsum_induction (fun z => ∃ p : Oscillator D,
            z = Finsupp.single (α + β) p) ?_ ?_ ?_
        · exact ⟨0, by simp⟩
        · intro a b ha hb
          obtain ⟨p, hp⟩ := ha
          obtain ⟨q, hq⟩ := hb
          refine ⟨p + q, ?_⟩
          rw [hp, hq, ← Finsupp.single_add]
        · intro j
          obtain ⟨r, hr⟩ := neutral x j β v
          obtain ⟨s, hs⟩ := ih (n := n - j - 1) (β := β) r
          refine ⟨s, ?_⟩
          rw [hr, hs]
      obtain ⟨p, hp⟩ := left
      obtain ⟨q, hq⟩ := right
      refine ⟨p + q, ?_⟩
      rw [hp, hq, ← Finsupp.single_add]

theorem actual_word_transpose (D : LatticeData)
    (B : LinearMap.BilinForm ℂ (Carrier D)) (α : Charge D)
    (hcurrent : ∀ i : Fin D.rank, ∀ k x y,
      B (neutralMode D i k x) y = -B x (neutralMode D i (-k) y))
    (hwordZero : ∀ (w : List (Index D)) (t : ℤ) (z : Carrier D) (i : Fin D.rank),
      neutralMode D i 0 (((wordField D α w)[[t]]) z) =
        ((wordField D α w)[[t]]) (neutralMode D i 0 z) +
          (bilinear D (unitCharge D i) α : ℂ) • ((wordField D α w)[[t]]) z)
    (hprimary : ∀ t x y, B (((actualField D α)[[t]]) x) y =
      paritySign (chargeEnergy D α) *
        B x (((actualField D α)[[2 * chargeEnergy D α - t - 2]]) y)) :
    ∀ (w : List (Index D)) (m : ℤ) (u v : Carrier D),
    B (((wordField D α w)[[m]]) u) v =
      paritySign (chargeEnergy D α) * (-1 : ℂ)^(wordWeight D w) *
        transposeReadout D B α w m u v := by
  intro w
  induction w with
  | nil =>
      intro m u v
      simp only [transposeReadout, wordWeight, WordChoice, Fintype.sum_unique,
        choiceCoefficient, choiceLower, choiceRetained, mul_one, add_zero,
        Int.cast_zero, sub_zero, pow_zero, one_mul]
      simpa [wordField] using hprimary m u v
  | cons x tail ih =>
      intro m u v
      let S : Finset (WordChoice D tail) :=
        @Finset.univ (WordChoice D tail) (wordChoiceFintype D tail)
      let G : WordChoice D tail → VertexOperator ℂ (Carrier D) :=
        fun c => wordField D α (choiceLower D c)
      let K : WordChoice D tail → ℤ := fun c =>
        2 * chargeEnergy D α + (wordWeight D tail : ℤ) +
          (choiceRetained D c : ℤ) - 2
      have htail : ∀ t x' y', B (((wordField D α tail)[[t]]) x') y' =
          ∑ c ∈ S, (paritySign (chargeEnergy D α) * (-1 : ℂ)^(wordWeight D tail) *
            choiceCoefficient D α c) * B x' (((G c)[[K c - t]]) y') := by
        intro t x' y'
        rw [ih t x' y']
        unfold transposeReadout
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        have hm : K c - t =
            2 * chargeEnergy D α + (wordWeight D tail : ℤ) +
              (choiceRetained D c : ℤ) - t - 2 := by
          dsimp [K]
          ring
        rw [hm]
        simp [S, G]
        ring
      have hzero : ∀ c ∈ S, ∀ t z,
          neutralMode D x.1 0 (((G c)[[t]]) z) =
            ((G c)[[t]]) (neutralMode D x.1 0 z) +
              (bilinear D (unitCharge D x.1) α : ℂ) • (((G c)[[t]]) z) := by
        intro c hc t z
        exact hwordZero (choiceLower D c) t z x.1
      have h := consumed_normal_product_form D B x.1 (hcurrent x.1) x.2
        (wordField D α tail) S G
        (fun c => paritySign (chargeEnergy D α) * (-1 : ℂ)^(wordWeight D tail) *
          choiceCoefficient D α c) K (bilinear D (unitCharge D x.1) α : ℂ)
        htail hzero m u v
      have h' := h
      simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib, mul_add] at h'
      change B (((insertion D x.1 x.2 (wordField D α tail))[[m]]) u) v = _
      have hxw : sourceWeight D x = x.2 + 1 := rfl
      simp only [transposeReadout, WordChoice, wordWeight]
      rw [hxw]
      rw [Fintype.sum_prod_type]
      convert h' using 1 <;>
        simp [transposeReadout, S, G, K, wordWeight, choiceCoefficient,
          sourceWeight, choiceLower, choiceRetained, Finset.sum_mul, Finset.mul_sum,
          Finset.sum_add_distrib, Fintype.sum_prod_type, Fin.sum_univ_succ,
          Fin.sum_univ_eq_sum_range, Finset.sum_range_succ', pow_succ] <;>
        ring_nf

end D5.S3.VertexAlgebra.SourceBPZ
