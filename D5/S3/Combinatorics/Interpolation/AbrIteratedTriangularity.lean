/- GID: D5/S3/Combinatorics/Interpolation/AbrIteratedTriangularity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Interpolation/AbrIteratedTriangularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Iterated ABR order preservation and integer triangularity. -/

import D5.S3.Combinatorics.Interpolation.AbrResidualPartition

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

theorem abrLower_trans {n : Nat} {a b c : Fin n →₀ Nat}
    (hab : AbrLower a b) (hbc : AbrLower b c) : AbrLower a c := by
  classical
  have htrans {u v w : Fin n →₀ Nat}
      (huv : DominatedBy u v) (hvw : DominatedBy v w) : DominatedBy u w :=
    ⟨huv.1.trans hvw.1, fun k => (huv.2 k).trans (hvw.2 k)⟩
  have hsortedDom {u v : Fin n →₀ Nat}
      (hsorted : (fun i => u (indexPerm u i)) = fun i => v (indexPerm v i)) :
      DominatedBy u v := by
    constructor
    · calc
        (∑ x, u x) = ∑ i, u (indexPerm u i) := by
          symm
          exact Fintype.sum_equiv (indexPerm u)
            (fun i => u (indexPerm u i)) (fun x => u x) (fun _ => rfl)
        _ = ∑ i, v (indexPerm v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [congrFun hsorted i]
        _ = ∑ x, v x := by
          exact Fintype.sum_equiv (indexPerm v)
            (fun i => v (indexPerm v i)) (fun x => v x) (fun _ => rfl)
    · intro k
      unfold prefixWeight
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro i _
      rw [congrFun hsorted i]
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · left
    refine ⟨htrans hab.1 hbc.1, ?_⟩
    intro hca
    exact hab.2 (htrans hbc.1 hca)
  · left
    have hbcDom := hsortedDom hbc.1
    refine ⟨htrans hab.1 hbcDom, ?_⟩
    intro hca
    exact hab.2 (htrans hbcDom hca)
  · left
    have habDom := hsortedDom hab.1
    refine ⟨htrans habDom hbc.1, ?_⟩
    intro hca
    exact hbc.2 (htrans hca habDom)
  · right
    exact ⟨hab.1.trans hbc.1, lt_trans hbc.2 hab.2⟩

theorem abrLower_leadExponent {n : Nat} {a b : Fin n →₀ Nat}
    (hab : AbrLower a b) (h : Nat) :
    AbrLower (leadExponent a h) (leadExponent b h) := by
  classical
  have hlead {u v : Fin n →₀ Nat} (huv : DominatedBy u v) :
      DominatedBy (leadExponent u h) (leadExponent v h) := by
    constructor
    · change (Finset.univ.sum fun x : Fin n =>
          u x + subsetExponent (initialSet u h) x) =
        Finset.univ.sum fun x : Fin n =>
          v x + subsetExponent (initialSet v h) x
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        sum_subsetExponent_eq_card_inter, sum_subsetExponent_eq_card_inter]
      simp [huv.1, card_initialSet_general]
    · intro k
      rw [prefixWeight_leadExponent, prefixWeight_leadExponent]
      exact Nat.add_le_add_right (huv.2 k) _
  rcases hab with hab | hab
  · left
    refine ⟨hlead hab.1, ?_⟩
    intro hreverse
    apply hab.2
    constructor
    · exact hab.1.1.symm
    · intro k
      have hk := hreverse.2 k
      rw [prefixWeight_leadExponent, prefixWeight_leadExponent] at hk
      omega
  · right
    constructor
    · funext i
      rw [indexPerm_leadExponent, indexPerm_leadExponent,
        leadExponent_at_perm, leadExponent_at_perm, congrFun hab.1 i]
    · rw [indexPerm_leadExponent, indexPerm_leadExponent]
      exact hab.2

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
      rw [← subsetExponent_eq_sum_single] at hcd
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
  induction k generalizing b with
  | zero =>
      have hbase : descentExponent (indexPerm a) = b := by
        simpa [abrProduct, descentMonomial] using hb
      rw [← hbase]
      exact descentExponent_le_descents _ _
  | succ k ih =>
      have hmul := MvPolynomial.support_mul
        (abrProduct a k) (MvPolynomial.esymm (Fin n) Rat (columnHeight a k)) hb
      obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hmul
      rw [MvPolynomial.support_esymm] at hd
      obtain ⟨t, _ht, htexp⟩ := Finset.mem_image.mp hd
      have hdexp : d = subsetExponent t :=
        htexp.symm.trans (subsetExponent_eq_sum_single t).symm
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
  induction k with
  | zero => simp [abrProduct, greedyExponent, descentMonomial]
  | succ k ih =>
      let g := greedyExponent a k
      let h := columnHeight a k
      let s := initialSet g h
      let e := subsetExponent s
      let pair : (Fin n →₀ Nat) × (Fin n →₀ Nat) := (g, e)
      have hs : s ∈ Finset.univ.powersetCard h :=
        initialSet_mem_powersetCard g (columnHeight_le a k)
      have heCoeff : coeff e (MvPolynomial.esymm (Fin n) Rat h) = 1 := by
        rw [MvPolynomial.esymm_eq_sum_monomial, coeff_sum]
        rw [Finset.sum_eq_single s]
        · simp [e, subsetExponent_eq_sum_single]
        · intro t ht hts
          rw [coeff_monomial]
          split_ifs with heq
          · exfalso
            apply hts
            apply subsetExponent_injective
            rw [subsetExponent_eq_sum_single]
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
          exact htexp.symm.trans (subsetExponent_eq_sum_single t).symm
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
    have hle := columnHeight_le a k.val
    omega⟩

/-- The ordinary coefficient polynomial whose elementary-symmetric
substitution supplies all residual columns. -/
def abrCoefficientPolynomial {n : Nat} (a : Fin n →₀ Nat) :
    MvPolynomial (Fin n) Rat :=
  ∏ k : Fin (residualDepth a), X (columnIndex a k)

/-- The complete ABR basis polynomial attached to exponent `a`. -/
def abrBasis {n : Nat} (a : Fin n →₀ Nat) : MvPolynomial (Fin n) Rat :=
  abrProduct a (residualDepth a)

theorem totalDegree_abrCoefficientPolynomial_le {n : Nat} (a : Fin n →₀ Nat) :
    (abrCoefficientPolynomial a).totalDegree ≤ residualDepth a := by
  unfold abrCoefficientPolynomial
  calc
    (∏ k : Fin (residualDepth a), X (columnIndex a k)).totalDegree ≤
        ∑ _k : Fin (residualDepth a), 1 := by
      apply (totalDegree_finsetProd _ _).trans_eq
      apply Finset.sum_congr rfl
      intro k _
      rw [totalDegree_X]
    _ = residualDepth a := by simp

theorem esymmSubstitution_abrCoefficientPolynomial {n : Nat} (a : Fin n →₀ Nat) :
    esymmSubstitution (abrCoefficientPolynomial a) =
      ∏ j ∈ Finset.range (residualDepth a),
        MvPolynomial.esymm (Fin n) Rat (columnHeight a j) := by
  unfold abrCoefficientPolynomial
  rw [map_prod]
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have hpos := columnHeight_pos_of_lt_residualDepth a hj
  simp [esymmSubstitution, columnIndex,
    MvPolynomial.aeval_def, hj, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)]

/-- Exact descent-monomial times coefficient-polynomial form of the complete
ABR basis element. -/
theorem abrBasis_eq_descent_mul_esymmSubstitution {n : Nat} (a : Fin n →₀ Nat) :
    abrBasis a = descentMonomial (indexPerm a) *
      esymmSubstitution (abrCoefficientPolynomial a) := by
  rw [abrBasis, abrProduct_eq_descent_mul_prod,
    esymmSubstitution_abrCoefficientPolynomial]

/-- Complete integer-unitriangular endpoint: the target exponent has
coefficient one and every other supported exponent is strictly ABR-lower. -/
theorem abrBasis_triangular {n : Nat} (a b : Fin n →₀ Nat) :
    coeff a (abrBasis a) = 1 ∧
      (b ∈ (abrBasis a).support → b = a ∨ AbrLower b a) := by
  rw [abrBasis]
  constructor
  · have hcoeff := coeff_abrProduct_leader a (residualDepth a)
    rw [greedyExponent_residualDepth] at hcoeff
    exact hcoeff
  · intro hb
    have htri := abrProduct_support_triangular a b (residualDepth a) hb
    rw [greedyExponent_residualDepth] at htri
    exact htri

/-- Every coefficient in the complete triangular product is the cast of an
integer coefficient. -/
theorem abrBasis_coeff_integer {n : Nat} (a b : Fin n →₀ Nat) :
    ∃ z : Int, coeff b (abrBasis a) = (z : Rat) := by
  refine ⟨coeff b (abrProductInt a (residualDepth a)), ?_⟩
  rw [abrBasis, abrProduct_eq_map_int, coeff_map]
  rfl

/-- The complete basis element stays in the coordinate box of its leader. -/
theorem abrBasis_support_coordinate_le {n : Nat} (hn : 0 < n)
    (a b : Fin n →₀ Nat) (hb : b ∈ (abrBasis a).support) (i : Fin n) :
    b i ≤ maxExponent a := by
  have hbound := abrProduct_support_coordinate_le a b (residualDepth a) hb i
  have hdesc : descents (indexPerm a) ≤ maxExponent a := by
    rw [maxExponent_eq_at_zero hn]
    rw [← suffixHeight_zero hn]
    exact suffixHeight_indexPerm_le_exponent a ⟨0, hn⟩
  rw [residualDepth_eq_maxExponent_sub_descents hn] at hbound
  omega

#print axioms abrLower_trans
#print axioms abrLower_leadExponent
#print axioms abrBasis_triangular
#print axioms abrBasis_coeff_integer
#print axioms abrBasis_eq_descent_mul_esymmSubstitution
#print axioms AbrCoordinateBoxStraightening.inversionCount_indexPerm_lt_of_sorted_eq
#print axioms AbrCoordinateBoxStraightening.oneFactor_abrLower

end D5.S3.Combinatorics.Interpolation.AbrIteratedTriangularity
