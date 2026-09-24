/- GID: D5/S3/Combinatorics/Interpolation/AbrIteratedTriangularity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrIteratedTriangularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Iterated ABR order preservation and integer triangularity. -/

import D5.S3.Combinatorics.Interpolation.AbrIteratedOrder

/-!
The order lemmas here are the formal content of ABR Lemma 3.3.  They turn the
one-factor result into an iterated triangular system without changing the
coordinate-box filtration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Interpolation.AbrIteratedTriangularity

open scoped BigOperators Pointwise
open MvPolynomial
open D5.S1.Words.Patterns.Separable.CutFactorization
open D5.S3.Combinatorics.Interpolation.AbrCoordinateBoxStraightening
open D5.S3.Combinatorics.Interpolation.AbrResidualPartition
/-- The actual ABR product after the first `k` residual Ferrers columns. -/
def abrProduct {n : Nat} (a : Fin n →₀ Nat) : Nat → MvPolynomial (Fin n) Rat
  | 0 => descentMonomial (indexPerm a)
  | k + 1 => abrProduct a k * MvPolynomial.esymm (Fin n) Rat (columnHeight a k)

/-- The same recursive product over the integers, used to certify that the
rational ABR coefficients are integer casts. -/
def abrProductInt {n : Nat} (a : Fin n →₀ Nat) : Nat → MvPolynomial (Fin n) Int
  | 0 => monomial (descentExponent (indexPerm a)) 1
  | k + 1 => abrProductInt a k * MvPolynomial.esymm (Fin n) Int (columnHeight a k)

theorem abrProduct_eq_map_int {n : Nat} (a : Fin n →₀ Nat) (k : Nat) :
    abrProduct a k = MvPolynomial.map (Int.castRingHom Rat) (abrProductInt a k) := by
  induction k with
  | zero => simp [abrProduct, abrProductInt, descentMonomial]
  | succ k ih =>
      simp [abrProduct, abrProductInt, ih, MvPolynomial.map_esymm]

/-- Every supported exponent of the iterated product is its greedy leader or
is strictly below that leader in the ABR order. -/
theorem abrProduct_support_triangular {n : Nat} (a b : Fin n →₀ Nat)
    (k : Nat) (hb : b ∈ (abrProduct a k).support) :
    b = greedyExponent a k ∨ AbrLower b (greedyExponent a k) := by
  classical
  have hsubsetSum (t : Finset (Fin n)) :
      subsetExponent t = ∑ x ∈ t, Finsupp.single x 1 := by
    ext x
    simp only [subsetExponent, Finsupp.indicator_apply]
    rw [Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply]
    by_cases hx : x ∈ t <;> simp [hx]
  induction k generalizing b with
  | zero =>
      left
      have hbase : descentExponent (indexPerm a) = b := by
        simpa [abrProduct, descentMonomial, greedyExponent] using hb
      exact hbase.symm
  | succ k ih =>
      have hmul := MvPolynomial.support_mul
        (abrProduct a k) (MvPolynomial.esymm (Fin n) Rat (columnHeight a k)) hb
      obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hmul
      rw [MvPolynomial.support_esymm] at hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
      rw [← hsubsetSum] at hcd
      have htcard : t.card = columnHeight a k :=
        (Finset.mem_powersetCard.mp ht).2
      have hstep :
          c + subsetExponent t = leadExponent c (columnHeight a k) ∨
            AbrLower (c + subsetExponent t) (leadExponent c (columnHeight a k)) := by
        by_cases hleader : t = initialSet c (columnHeight a k)
        · left
          simp [leadExponent, hleader]
        · right
          exact oneFactor_abrLower c t htcard hleader
      rcases ih c hc with rfl | hclower
      · rw [← hcd]
        simpa [greedyExponent] using hstep
      · right
        have hgreedy := abrLower_leadExponent hclower (columnHeight a k)
        rcases hstep with hstep | hstep
        · rw [← hcd, hstep]
          simpa [greedyExponent] using hgreedy
        · rw [← hcd]
          simpa [greedyExponent] using abrLower_trans hstep hgreedy

/-- After `k` factors, no coordinate has grown by more than `k` above the
descent box. -/
theorem abrProduct_support_coordinate_le {n : Nat} (a b : Fin n →₀ Nat)
    (k : Nat) (hb : b ∈ (abrProduct a k).support) (i : Fin n) :
    b i ≤ descents (indexPerm a) + k := by
  classical
  have hsubsetSum (t : Finset (Fin n)) :
      subsetExponent t = ∑ x ∈ t, Finsupp.single x 1 := by
    ext x
    simp only [subsetExponent, Finsupp.indicator_apply]
    rw [Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply]
    by_cases hx : x ∈ t <;> simp [hx]
  induction k generalizing b with
  | zero =>
      have hbase : descentExponent (indexPerm a) = b := by
        simpa [abrProduct, descentMonomial] using hb
      rw [← hbase]
      change suffixHeight (indexPerm a) ((indexPerm a).symm i) ≤
        descents (indexPerm a) + 0
      rw [Nat.add_zero]
      unfold suffixHeight descents
      apply Finset.sum_le_sum
      intro j _
      split <;> omega
  | succ k ih =>
      have hmul := MvPolynomial.support_mul
        (abrProduct a k) (MvPolynomial.esymm (Fin n) Rat (columnHeight a k)) hb
      obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hmul
      rw [MvPolynomial.support_esymm] at hd
      obtain ⟨t, _ht, htexp⟩ := Finset.mem_image.mp hd
      have hdexp : d = subsetExponent t :=
        htexp.symm.trans (hsubsetSum t).symm
      have hcBound := ih c hc
      have htBound : subsetExponent t i ≤ 1 := by
        simp only [subsetExponent, Finsupp.indicator_apply]
        split <;> omega
      rw [← hcd, hdexp, Finsupp.add_apply]
      omega

/-- The leader coefficient of every iterated ABR product is one. -/
theorem coeff_abrProduct_leader {n : Nat} (a : Fin n →₀ Nat) (k : Nat) :
    coeff (greedyExponent a k) (abrProduct a k) = 1 := by
  classical
  have hsubsetSum (t : Finset (Fin n)) :
      subsetExponent t = ∑ x ∈ t, Finsupp.single x 1 := by
    ext x
    simp only [subsetExponent, Finsupp.indicator_apply]
    rw [Finsupp.finsetSum_apply]
    simp_rw [Finsupp.single_apply]
    by_cases hx : x ∈ t <;> simp [hx]
  have hsubsetInjective : Function.Injective (subsetExponent (n := n)) := by
    intro s t hst
    ext x
    have hx := congrArg (fun u : Fin n →₀ Nat => u x) hst
    simp only [subsetExponent, Finsupp.indicator_apply] at hx
    by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp_all
  have hcardInitial (u : Fin n →₀ Nat) {m : Nat} (hm : m ≤ n) :
      (initialSet u m).card = m := by
    let order := indexPerm u
    have himage : initialSet u m =
        (Finset.univ.filter fun i : Fin n => i.val < m).image order := by
      ext x
      simp only [initialSet, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, order]
      constructor
      · intro hx
        exact ⟨(indexPerm u).symm x, hx, by simp⟩
      · rintro ⟨i, hi, rfl⟩
        simpa using hi
    rw [himage, Finset.card_image_of_injective _ order.injective]
    simpa [Nat.min_eq_right hm] using (Fin.card_filter_val_lt (n := n) (m := m))
  induction k with
  | zero => simp [abrProduct, greedyExponent, descentMonomial]
  | succ k ih =>
      let g := greedyExponent a k
      let h := columnHeight a k
      let s := initialSet g h
      let e := subsetExponent s
      let pair : (Fin n →₀ Nat) × (Fin n →₀ Nat) := (g, e)
      have hcolumn : h ≤ n := by
        simpa [h, columnHeight] using
          Finset.card_le_card
            (Finset.filter_subset (fun i : Fin n => k < residual a i) Finset.univ)
      have hs : s ∈ Finset.univ.powersetCard h := by
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, by simpa [s] using hcardInitial g hcolumn⟩
      have heCoeff : coeff e (MvPolynomial.esymm (Fin n) Rat h) = 1 := by
        rw [MvPolynomial.esymm_eq_sum_monomial, coeff_sum]
        rw [Finset.sum_eq_single s]
        · simp [e, hsubsetSum]
        · intro t ht hts
          rw [coeff_monomial]
          split_ifs with heq
          · exfalso
            apply hts
            apply hsubsetInjective
            rw [hsubsetSum]
            simpa [e] using heq
          · rfl
        · exact fun hnot => (hnot hs).elim
      have hirrefl (u : Fin n →₀ Nat) : ¬ AbrLower u u := by
        intro hu
        rcases hu with hu | hu
        · exact hu.2 hu.1
        · exact (lt_irrefl _ hu.2).elim
      have hpair : pair ∈ Finset.antidiagonal (greedyExponent a (k + 1)) := by
        rw [Finset.mem_antidiagonal]
        simp [pair, g, e, s, h, greedyExponent, leadExponent]
      rw [abrProduct, MvPolynomial.coeff_mul]
      rw [Finset.sum_eq_single pair]
      · change coeff g (abrProduct a k) *
          coeff e (MvPolynomial.esymm (Fin n) Rat h) = 1
        rw [ih, heCoeff, one_mul]
      · intro x hx hxp
        by_contra hnonzero
        have hxleft : coeff x.1 (abrProduct a k) ≠ 0 := by
          intro hz
          exact hnonzero (by simp [hz])
        have hxright0 :
            coeff x.2 (MvPolynomial.esymm (Fin n) Rat (columnHeight a k)) ≠ 0 := by
          intro hz
          apply hnonzero
          rw [hz, mul_zero]
        have hxright : coeff x.2 (MvPolynomial.esymm (Fin n) Rat h) ≠ 0 := by
          simpa [h] using hxright0
        have hxleftSupport : x.1 ∈ (abrProduct a k).support :=
          MvPolynomial.mem_support_iff.mpr hxleft
        have hxrightSupport : x.2 ∈ (MvPolynomial.esymm (Fin n) Rat h).support :=
          MvPolynomial.mem_support_iff.mpr hxright
        rw [MvPolynomial.support_esymm] at hxrightSupport
        obtain ⟨t, ht, htexp⟩ := Finset.mem_image.mp hxrightSupport
        have htcard : t.card = h := (Finset.mem_powersetCard.mp ht).2
        have hx2 : x.2 = subsetExponent t := by
          exact htexp.symm.trans (hsubsetSum t).symm
        have hxsum : x.1 + subsetExponent t = greedyExponent a (k + 1) := by
          rw [← hx2]
          exact Finset.mem_antidiagonal.mp hx
        rcases abrProduct_support_triangular a x.1 k hxleftSupport with hx1 | hxlower
        · have htlead : t = s := by
            by_contra htne
            have hstep := oneFactor_abrLower g t htcard htne
            have htarget : greedyExponent a (k + 1) = leadExponent g h := by
              simp [greedyExponent, g, h]
            have hstep' : AbrLower (g + subsetExponent t)
                (greedyExponent a (k + 1)) := by
              rw [htarget]
              exact hstep
            have hsum' : g + subsetExponent t = greedyExponent a (k + 1) := by
              simpa [g] using hx1 ▸ hxsum
            have hself : AbrLower (greedyExponent a (k + 1))
                (greedyExponent a (k + 1)) := hsum' ▸ hstep'
            exact hirrefl _ hself
          apply hxp
          apply Prod.ext
          · exact hx1
          · rw [hx2, htlead]
        · have hstep :
              AbrLower (x.1 + subsetExponent t) (leadExponent x.1 h) ∨
                x.1 + subsetExponent t = leadExponent x.1 h := by
            by_cases htlead : t = initialSet x.1 h
            · right
              simp [leadExponent, htlead]
            · left
              exact oneFactor_abrLower x.1 t htcard htlead
          have hlead := abrLower_leadExponent hxlower h
          have htarget : greedyExponent a (k + 1) = leadExponent g h := by
            simp [greedyExponent, g, h]
          rcases hstep with hstep | hstep
          · have hcomp : AbrLower (x.1 + subsetExponent t)
                (greedyExponent a (k + 1)) := by
              rw [htarget]
              exact abrLower_trans hstep hlead
            exact hirrefl _ (hxsum ▸ hcomp)
          · have hcomp : AbrLower (x.1 + subsetExponent t)
                (greedyExponent a (k + 1)) := by
              rw [hstep, htarget]
              exact hlead
            exact hirrefl _ (hxsum ▸ hcomp)
      · exact fun hnot => (hnot hpair).elim

theorem abrProduct_eq_descent_mul_prod {n : Nat} (a : Fin n →₀ Nat) (k : Nat) :
    abrProduct a k = descentMonomial (indexPerm a) *
      ∏ j ∈ Finset.range k, MvPolynomial.esymm (Fin n) Rat (columnHeight a j) := by
  induction k with
  | zero => simp [abrProduct]
  | succ k ih =>
      rw [abrProduct, ih, Finset.prod_range_succ]
      ring

/-- The coefficient-coordinate variable corresponding to residual column
`k`; positivity of that column makes the one-based height a `Fin n` index. -/
def columnIndex {n : Nat} (a : Fin n →₀ Nat) (k : Fin (residualDepth a)) : Fin n :=
  ⟨columnHeight a k.val - 1, by
    have hpos := columnHeight_pos_of_lt_residualDepth a k.isLt
    have hle : columnHeight a k.val ≤ n := by
      simpa [columnHeight] using
        Finset.card_le_card
          (Finset.filter_subset (fun i : Fin n => k.val < residual a i) Finset.univ)
    omega⟩

/-- The ordinary coefficient polynomial whose elementary-symmetric
substitution supplies all residual columns. -/
def abrCoefficientPolynomial {n : Nat} (a : Fin n →₀ Nat) :
    MvPolynomial (Fin n) Rat :=
  ∏ k : Fin (residualDepth a), X (columnIndex a k)

/-- The complete ABR basis polynomial attached to exponent `a`. -/
def abrBasis {n : Nat} (a : Fin n →₀ Nat) : MvPolynomial (Fin n) Rat :=
  abrProduct a (residualDepth a)

#print axioms abrProduct_eq_map_int
#print axioms AbrCoordinateBoxStraightening.inversionCount_indexPerm_lt_of_sorted_eq
#print axioms AbrCoordinateBoxStraightening.oneFactor_abrLower

end D5.S3.Combinatorics.Interpolation.AbrIteratedTriangularity
