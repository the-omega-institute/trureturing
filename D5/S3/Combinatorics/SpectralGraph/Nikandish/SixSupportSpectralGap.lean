/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/SixSupportSpectralGap
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/SixSupportSpectralGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full real pair-sum and total-sum gaps for the actual six-cell spectrum. -/
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportInertiaIntervals
import D5.S3.Weil.ZetaLinear.FullRankInertiaPullback
import Mathlib.Tactic

/-! Source: PR3 endpoint-one-spectrum, revision
b93becea662a746badeadba42fdc3d3eb3db9382, blob
b61e5619a508f11c7df335dd468ce61e2aa60000; PR9 global-pair-sum
and total-sum notes, blobs 1c7f2123ef1d8833dc2d3544f9991b9a12ced364
and c0ec47ca31cac4e5756e033f623410c40b52de91.
Root counts are on the entire actual quotient characteristic multiset,
including algebraic multiplicities, not on a scalar proxy polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.SixSupportSpectralGap
open Matrix Polynomial Finset
open D5.S3.Combinatorics.SpectralGraph.SixSupportInertia
open D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianLowRoot
open D5.S3.Combinatorics.SpectralGraph.SixSupportClassificationAlgebra

/-- Multiplicity-counted roots strictly below x in the actual quotient. -/
def below (a b c x : ℝ) : ℕ :=
  (quotient a b c).charpoly.roots.countP (fun t => t < x)

/-- Shifting the actual symmetric representative transports full root counts. -/
theorem shifted_roots (a b c x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    negativeCount (symmetric a b c-Matrix.scalar (Fin 6) x) = below a b c x ∧
    zeroCount (symmetric a b c-Matrix.scalar (Fin 6) x) = multiplicity a b c x := by
  have hs := symmetric_charpoly a b c ha hab hbc
  have hq : (quotient a b c).charpoly = X*quintic a b c := by
    change (D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial.quotientOver a b c).charpoly = _
    rw [D5.S3.Combinatorics.SpectralGraph.SixSupportLaplacianPolynomial.charpoly_zero_factor,
      quintic_eq_reduced]
  have hr : (symmetric a b c-Matrix.scalar (Fin 6) x).charpoly.roots =
      (quotient a b c).charpoly.roots.map (fun t => t-x) := by
    rw [Matrix.charpoly_sub_scalar]
    rw [← hq] at hs
    rw [hs]
    simpa using Polynomial.roots_comp_C_mul_X_add_C (quotient a b c).charpoly 1 x isUnit_one
  constructor
  · unfold negativeCount below
    rw [hr,Multiset.countP_map]
    simp only [sub_neg,Multiset.countP_eq_card_filter]
  · unfold zeroCount SixSupportInertia.multiplicity
    rw [hr,Multiset.countP_map]
    simp only [sub_eq_zero,Multiset.countP_eq_card_filter]

private def lowerWitness (a b c : ℝ) : Matrix (Fin 6) (Fin 3) ℝ :=
  !![0,0,0;0,0,0;0,0,Real.sqrt a*Real.sqrt b*Real.sqrt c;
     1,0,0;0,1,0;0,0,a*b]

private theorem lower_pullback (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (lowerWitness a b c)ᴴ * (symmetric a b c-Matrix.scalar (Fin 6) (a+b)) *
      lowerWitness a b c = diagonal ![-b,-a,-(a+b)*(a*b)^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerWitness,symmetric,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.scalar,Matrix.diagonal_apply,conjTranspose_apply]
  all_goals ring_nf
  all_goals simp [Real.sq_sqrt ha.le,Real.sq_sqrt hb.le,Real.sq_sqrt hc.le]
  all_goals ring

/-- The first three ordered quotient eigenvalues lie strictly below a+b,
for every ordered positive real triple, including repeated parameters. -/
theorem pair_sum_count (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    3 ≤ below a b c (a+b) := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hS := (quotient_geometry a b c ha hb hc).2.1.1
  have hQ : (symmetric a b c-Matrix.scalar (Fin 6) (a+b)).IsHermitian := by
    apply hS.sub
    exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hle := RHLinalg.negIndex_conj_le hQ (lowerWitness a b c)
  rw [← negativeCount_eq (Matrix.isHermitian_conjTranspose_mul_mul (lowerWitness a b c) hQ),
    ← negativeCount_eq hQ,lower_pullback a b c ha hb hc] at hle
  have hd := (diagonal_counts (![-b,-a,-(a+b)*(a*b)^2] : Fin 3 → ℝ)).1
  have hn : #{i : Fin 3 | (![-b,-a,-(a+b)*(a*b)^2] : Fin 3 → ℝ) i < 0} = 3 := by
    have h (i : Fin 3) : (![-b,-a,-(a+b)*(a*b)^2] : Fin 3 → ℝ) i < 0 := by
      fin_cases i
      · change -b < 0; linarith
      · change -a < 0; linarith
      · change -(a+b)*(a*b)^2 < 0
        exact mul_neg_of_neg_of_pos (by linarith) (by positivity)
    simp only [h,Finset.filter_true,Finset.card_univ,Fintype.card_fin]
  rw [hd,hn,(shifted_roots a b c (a+b) ha hab hbc).1] at hle
  exact hle

private def totalResidual (a b c : ℝ) : ℝ :=
  a^2*(b*c-b-c)+b^2*(a*c-a-c)+c^2*(a*b-a-b)

private theorem residual (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    0 ≤ totalResidual a b c ∧
      (totalResidual a b c = 0 ↔ a = 2 ∧ b = 2 ∧ c = 2) := by
  have hb : 2 ≤ b := ha.trans hab
  have hc : 2 ≤ c := hb.trans hbc
  have hbc0 : 0 ≤ b*c-b-c := by
    nlinarith [mul_nonneg (show 0 ≤ b-2 by linarith) (show 0 ≤ c-1 by linarith)]
  have hac0 : 0 ≤ a*c-a-c := by
    nlinarith [mul_nonneg (show 0 ≤ a-2 by linarith) (show 0 ≤ c-1 by linarith)]
  have hab0 : 0 ≤ a*b-a-b := by
    nlinarith [mul_nonneg (show 0 ≤ a-2 by linarith) (show 0 ≤ b-1 by linarith)]
  have h0 : 0 ≤ totalResidual a b c := by unfold totalResidual; positivity
  refine ⟨h0,?_⟩
  constructor
  · intro hz
    have hc2 : c = 2 := by
      by_contra hn
      have hgt : 2 < c := lt_of_le_of_ne hc (Ne.symm hn)
      have hbcpos : 0 < b*c-b-c := by
        nlinarith [mul_nonneg (show 0 ≤ b-2 by linarith) (show 0 ≤ c-1 by linarith)]
      have hp : 0 < a^2*(b*c-b-c) := by positivity
      have hq : 0 ≤ b^2*(a*c-a-c) := by positivity
      have hr : 0 ≤ c^2*(a*b-a-b) := by positivity
      unfold totalResidual at hz
      linarith
    exact ⟨by linarith,by linarith,hc2⟩
  · rintro ⟨rfl,rfl,rfl⟩
    norm_num [totalResidual]

private theorem total_diagonal (a b c : ℝ) (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    (∀ i, 0 < schurDiagonal a b c (a+b+c) i) ∧
    1-∑ i : Fin 3, ![a,b,c] i/schurDiagonal a b c (a+b+c) i =
      totalResidual a b c / ((a+b+c)*a*b*c) := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  have hrepr (i : Fin 3) : schurDiagonal a b c (a+b+c) i =
      (a+b+c)*a*b*c / (![a,b,c] i * (a+b+c- ![a,b,c] i)) := by
    fin_cases i <;> norm_num [schurDiagonal]
    all_goals field_simp [ne_of_gt (add_pos ha hb),
      ne_of_gt (add_pos ha hc), ne_of_gt (add_pos hb hc),
      show -a-b ≠ 0 by linarith, show -a-c ≠ 0 by linarith,
      show -b-c ≠ 0 by linarith]
    all_goals ring
    all_goals simp only [show -a-b = -(a+b) by ring,
      show -a-c = -(a+c) by ring, show -b-c = -(b+c) by ring, inv_neg, neg_neg]
    all_goals field_simp [ne_of_gt (add_pos ha hb),
      ne_of_gt (add_pos ha hc), ne_of_gt (add_pos hb hc)]
    all_goals ring
  have hp (i : Fin 3) : 0 < schurDiagonal a b c (a+b+c) i := by
    rw [hrepr]
    have hi : 0 < (![a,b,c] : Fin 3 → ℝ) i ∧
        0 < a+b+c-(![a,b,c] : Fin 3 → ℝ) i := by
      fin_cases i <;> norm_num <;> constructor <;> linarith
    exact div_pos (by positivity) (mul_pos hi.1 hi.2)
  refine ⟨hp,?_⟩
  simp only [Fin.sum_univ_three]
  rw [hrepr 0,hrepr 1,hrepr 2]
  norm_num
  dsimp [totalResidual]
  field_simp
  <;> ring

/-- Exactly three actual quotient eigenvalues lie below the total sum,
and an eigenvalue equals that sum exactly at the sole boundary triple.
Its boundary multiplicity is one. This is the full source real domain. -/
theorem total_sum_count (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    below a b c (a+b+c) = 3 ∧
      multiplicity a b c (a+b+c) = (if a = 2 ∧ b = 2 ∧ c = 2 then 1 else 0) := by
  classical
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hc0 : 0 < c := hb0.trans_le hbc
  have hd := total_diagonal a b c ha0 hab hbc
  have h := nonsingular_diagonal (schurDiagonal a b c (a+b+c))
    ![Real.sqrt a,Real.sqrt b,Real.sqrt c] (fun i => (hd.1 i).ne')
  have hs (i : Fin 3) : (![Real.sqrt a,Real.sqrt b,Real.sqrt c] i)^2 = ![a,b,c] i := by
    fin_cases i <;> simp [Real.sq_sqrt,ha0.le,hb0.le,hc0.le]
  simp only [hs] at h
  change negativeCount (schur a b c (a+b+c)) = _ ∧
    zeroCount (schur a b c (a+b+c)) = _ at h
  have hn : #{i | schurDiagonal a b c (a+b+c) i < 0} = 0 := by
    have hnot i := not_lt.mpr (hd.1 i).le
    simp [hnot]
  rw [hn,hd.2] at h
  have hr := residual a b c ha hab hbc
  have hden : 0 < (a+b+c)*a*b*c := by positivity
  have hF : 0 ≤ totalResidual a b c/((a+b+c)*a*b*c) := div_nonneg hr.1 hden.le
  rw [if_neg (not_lt.mpr hF),zero_add] at h
  have hzero : totalResidual a b c/((a+b+c)*a*b*c) = 0 ↔ a = 2 ∧ b = 2 ∧ c = 2 := by
    rw [div_eq_zero_iff,or_iff_left hden.ne',hr.2]
  simp only [hzero] at h
  have hshift := shifted_counts a b c (a+b+c) ha0 hab hbc
    (by linarith) (by linarith) (by linarith)
  have hpn : #{i : Fin 3 | ![a,b,c] i-(a+b+c) < 0} = 3 := by
    have hi (i : Fin 3) : ![a,b,c] i-(a+b+c) < 0 := by fin_cases i <;> simp <;> linarith
    simp [hi]
  have hpz : #{i : Fin 3 | ![a,b,c] i-(a+b+c) = 0} = 0 := by
    have hi (i : Fin 3) : ![a,b,c] i-(a+b+c) ≠ 0 := by fin_cases i <;> simp <;> linarith
    simp [hi]
  rw [hpn,hpz,h.1,h.2,Nat.zero_add,Nat.add_zero] at hshift
  have he := shifted_roots a b c (a+b+c) ha0 hab hbc
  exact ⟨he.1.symm.trans hshift.1,he.2.symm.trans hshift.2⟩

/-- The source pair-sum gap also holds with multiplicities: exactly three
roots lie below b+c and none equals it, including the repeated boundary. -/
theorem upper_pair_sum_count (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    below a b c (b+c) = 3 ∧ multiplicity a b c (b+c) = 0 := by
  classical
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hc0 : 0 < c := hb0.trans_le hbc
  have hsum := total_sum_count a b c ha hab hbc
  have hlo := pair_sum_count a b c ha0 hab hbc
  have hmono (x y : ℝ) (hxy : x ≤ y) : below a b c x ≤ below a b c y := by
    dsimp [below]
    simp only [Multiset.countP_eq_card_filter]
    apply Multiset.card_le_card
    exact Multiset.monotone_filter_right _ fun t ht => ht.trans_le hxy
  have h1 : 3 ≤ below a b c (b+c) := hlo.trans (hmono (a+b) (b+c) (by linarith))
  have h2 : below a b c (b+c) ≤ 3 := (hmono (b+c) (a+b+c) (by linarith)).trans_eq hsum.1
  have he : below a b c (b+c) = 3 := le_antisymm h2 h1
  refine ⟨he,?_⟩
  by_contra hn
  obtain ⟨t,ht,heq⟩ := Multiset.countP_pos.mp (Nat.pos_of_ne_zero hn)
  subst t
  have hstrict : below a b c (b+c) < below a b c (a+b+c) := by
    dsimp [below]
    simp only [Multiset.countP_eq_card_filter]
    apply Multiset.card_lt_card
    apply lt_of_le_of_ne
    · exact Multiset.monotone_filter_right _ fun t ht => ht.trans (by linarith)
    · intro heq
      have hm : b+c ∈ (quotient a b c).charpoly.roots.filter (fun t => t < a+b+c) :=
        Multiset.mem_filter.mpr ⟨ht,by linarith⟩
      rw [← heq] at hm
      exact (lt_irrefl (b+c)) (Multiset.mem_filter.mp hm).2
  rw [he,hsum.1] at hstrict
  omega


/-- The complete original global real separation, stated as exact counts
on the actual characteristic multiset. Together with the existing positive
semidefinite/simple-kernel geometry, these are the ordered inequalities
lambda3<a+b<=b+c<lambda4, with the sole lambda4=s boundary retained. -/
theorem result (a b c : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    below a b c (a+b) = 3 ∧ below a b c (b+c) = 3 ∧
      multiplicity a b c (b+c) = 0 ∧ below a b c (a+b+c) = 3 ∧
      multiplicity a b c (a+b+c) = (if a = 2 ∧ b = 2 ∧ c = 2 then 1 else 0) := by
  classical
  have ha0 : 0 < a := by linarith
  have hu := upper_pair_sum_count a b c ha hab hbc
  have ht := total_sum_count a b c ha hab hbc
  have hlo := pair_sum_count a b c ha0 hab hbc
  have hle : below a b c (a+b) ≤ below a b c (b+c) := by
    dsimp [below]
    simp only [Multiset.countP_eq_card_filter]
    apply Multiset.card_le_card
    exact Multiset.monotone_filter_right _ fun t ht => ht.trans_le (by linarith)
  exact ⟨le_antisymm (hle.trans_eq hu.1) hlo,hu.1,hu.2,ht.1,ht.2⟩

#print axioms pair_sum_count
#print axioms total_sum_count
#print axioms upper_pair_sum_count
end D5.S3.Combinatorics.SpectralGraph.SixSupportSpectralGap
