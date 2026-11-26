/- GID: D5/S3/Arith/Additive/PlasticDeletionBound
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticDeletionBound
   mirror-E: none(waiver:real-algebraic-power-families)
   anchors: []
   utility: none
   digest: Arbitrary interval deletions preserve plastic collision templates. -/

import D5.S3.Arith.Additive.PlasticNestedFamily

/-! Arbitrary deletions from plastic-power intervals retain strict golden-power comparisons. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Additive.PlasticDeletionBound

open scoped Pointwise
open D5.S3.Arith.Additive.PlasticPowerCollisions

/-- A deleted exponent spoils at most one translated copy per template offset. -/
private theorem template_deletion_bound (I H J T : Finset ℤ)
    (hzero : (0 : ℤ) ∈ T) (hJ : ∀ t ∈ J, ∀ d ∈ T, t + d ∈ I) :
    J.card ≤ ((I \ H).filter (fun t => ∀ d ∈ T, t+d ∈ I \ H)).card +
      T.card * H.card := by
  classical
  let B := (T ×ˢ H).image (fun p : ℤ × ℤ => p.2-p.1)
  have hsub : J ⊆ ((I \ H).filter (fun t => ∀ d ∈ T, t+d ∈ I \ H)) ∪ B := by
    intro t ht
    by_cases hg : ∀ d ∈ T, t+d ∈ I \ H
    · apply Finset.mem_union_left
      apply Finset.mem_filter.2
      exact ⟨by simpa using hg 0 hzero,hg⟩
    · push Not at hg
      obtain ⟨d,hd,hbad⟩ := hg
      have hh : t+d ∈ H := by
        by_contra hn
        exact hbad (Finset.mem_sdiff.2 ⟨hJ t ht d hd,hn⟩)
      apply Finset.mem_union_right
      exact Finset.mem_image.2 ⟨(d,t+d),Finset.mem_product.2 ⟨hd,hh⟩,by simp⟩
  calc
    J.card ≤ (((I \ H).filter (fun t => ∀ d ∈ T, t+d ∈ I \ H)) ∪ B).card :=
      Finset.card_le_card hsub
    _ ≤ ((I \ H).filter (fun t => ∀ d ∈ T, t+d ∈ I \ H)).card+B.card :=
      Finset.card_union_le _ _
    _ ≤ _ := by
      have hh := Finset.card_image_le (s := T ×ˢ H) (f := fun p : ℤ × ℤ => p.2-p.1)
      simpa [B,Finset.card_product] using Nat.add_le_add_left hh
        (((I \ H).filter (fun t => ∀ d ∈ T, t+d ∈ I \ H)).card)

private theorem interval_template_bound (a : ℤ) (m d : ℕ) (H T : Finset ℤ)
    (hzero : (0 : ℤ) ∈ T) (hT : ∀ x ∈ T, 0 ≤ x ∧ x ≤ d) :
    m-d ≤ ((Finset.Icc a (a+(m:ℤ)-1) \ H).filter
      (fun t => ∀ x ∈ T, t+x ∈ Finset.Icc a (a+(m:ℤ)-1) \ H)).card + T.card*H.card := by
  have hh := template_deletion_bound (Finset.Icc a (a+(m:ℤ)-1)) H
    (Finset.Icc a (a+(m:ℤ)-1-d)) T hzero (by
      intro t ht x hx
      have ht := Finset.mem_Icc.1 ht
      have hx := hT x hx
      exact Finset.mem_Icc.2 ⟨by omega,by omega⟩)
  rw [Int.card_Icc] at hh
  have he : (a+(m:ℤ)-1-d+1-a).toNat = m-d := by omega
  rwa [he] at hh

private theorem four_template_bound (a : ℤ) (m : ℕ) (H : Finset ℤ) :
    let E := Finset.Icc a (a+(m:ℤ)-1) \ H
    4*m ≤
      (E.filter (fun t => t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E)).card +
      (E.filter (fun t => t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E)).card +
      (E.filter (fun t => t+5 ∈ E ∧ t+7 ∈ E)).card +
      (E.filter (fun t => t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E)).card + 26 + 15*H.card := by
  classical
  let E := Finset.Icc a (a+(m:ℤ)-1) \ H
  have h4 := interval_template_bound a m 4 H {0,2,3,4} (by simp) (by
    intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl <;> norm_num)
  have h6 := interval_template_bound a m 6 H {0,3,5,6} (by simp) (by
    intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl <;> norm_num)
  have h7 := interval_template_bound a m 7 H {0,5,7} (by simp) (by
    intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl|rfl <;> norm_num)
  have h9 := interval_template_bound a m 9 H {0,5,8,9} (by simp) (by
    intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl|rfl|rfl <;> norm_num)
  have hf (P : ℤ → Prop) [DecidablePred P] : E.filter (fun t => t ∈ E ∧ P t) = E.filter P := by
    ext t; simp only [Finset.mem_filter]; tauto
  norm_num only [Finset.card_insert_of_notMem,Finset.card_singleton,
    Finset.mem_insert,Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    add_zero, Nat.reduceAdd, Int.reduceEq, not_false_eq_true] at h4 h6 h7 h9
  change m-4 ≤ (E.filter (fun t => t ∈ E ∧ t+2 ∈ E ∧ t+3 ∈ E ∧ t+4 ∈ E)).card+4*H.card at h4
  change m-6 ≤ (E.filter (fun t => t ∈ E ∧ t+3 ∈ E ∧ t+5 ∈ E ∧ t+6 ∈ E)).card+4*H.card at h6
  change m-7 ≤ (E.filter (fun t => t ∈ E ∧ t+5 ∈ E ∧ t+7 ∈ E)).card+3*H.card at h7
  change m-9 ≤ (E.filter (fun t => t ∈ E ∧ t+5 ∈ E ∧ t+8 ∈ E ∧ t+9 ∈ E)).card+4*H.card at h9
  rw [hf] at h4 h6 h7 h9
  change 4*m ≤ _+_+_+_+26+15*H.card
  dsimp only [E] at h4 h6 h7 h9
  omega

/-- The full arbitrary-deletion interval family, including its golden-power comparison. -/
theorem whole_theorem_four_one (r : ℝ) (hr : 1 < r) (hroot : r^3=r+1)
    (n h : ℕ) (hn : 8 ≤ n) (hh : 11*h+24 ≤ 3*n) (a : ℤ) (H : Finset ℤ)
    (hH : H ⊆ Finset.Icc a (a+((n+h:ℕ):ℤ)-1)) (hcardH : H.card=h) :
    let I := Finset.Icc a (a+((n+h:ℕ):ℤ)-1)
    let E := I \ H
    let A := E.image (fun e => r^e)
    let G := (Finset.Icc (0 : ℤ) ((n:ℤ)-1)).image (fun e => Real.goldenRatio^e)
    A.card=n ∧ (A*A).card ≤ 2*(n+h)-1 ∧ 2*(n+h)-1 ≤ 3*n-4 ∧
      (A+A).card ≤ n*(n+1)/2-4*n+26+11*h ∧
      n*(n+1)/2-4*n+26+11*h ≤ (G+G).card-1 := by
  classical
  let I := Finset.Icc a (a+((n+h:ℕ):ℤ)-1)
  let E := I \ H
  let A := E.image (fun e => r^e)
  let G := (Finset.Icc (0 : ℤ) ((n:ℤ)-1)).image (fun e => Real.goldenRatio^e)
  change A.card=n ∧ (A*A).card ≤ 2*(n+h)-1 ∧ 2*(n+h)-1 ≤ 3*n-4 ∧
    (A+A).card ≤ n*(n+1)/2-4*n+26+11*h ∧
    n*(n+1)/2-4*n+26+11*h ≤ (G+G).card-1
  have hcardI : I.card=n+h := by simp only [I,Int.card_Icc]; omega
  have hcardE : E.card=n := by
    dsimp [E]; rw [Finset.card_sdiff_of_subset hH,hcardI,hcardH]; omega
  have hcardA : A.card=n := by
    dsimp [A]; rw [Finset.card_image_of_injective _ (zpow_right_strictMono₀ hr).injective,hcardE]
  have hr0 : r ≠ 0 := by linarith
  have hprodsub : A*A ⊆ (Finset.Icc (2*a) (2*(a+((n+h:ℕ):ℤ)-1))).image (fun e => r^e) := by
    intro x hx
    obtain ⟨u,hu,v,hv,hx⟩ := Finset.mem_mul.1 hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hu
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hv
    have hi := Finset.mem_Icc.1 (Finset.mem_sdiff.1 hi).1
    have hj := Finset.mem_Icc.1 (Finset.mem_sdiff.1 hj).1
    exact Finset.mem_image.2 ⟨i+j,Finset.mem_Icc.2 ⟨by omega,by omega⟩,
      by rw [zpow_add₀ hr0]; exact hx⟩
  have hprod : (A*A).card ≤ 2*(n+h)-1 := by
    have hc := (Finset.card_le_card hprodsub).trans (Finset.card_image_le)
    rw [Int.card_Icc] at hc
    have he : (2*(a+((n+h:ℕ):ℤ)-1)+1-2*a).toNat=2*(n+h)-1 := by omega
    rwa [he] at hc
  have hcoll := sumset_card_add_template_counts r hr hroot E
  rw [hcardE,Nat.choose_two_right,Nat.add_sub_cancel,Nat.mul_comm (n+1) n] at hcoll
  have hcount := four_template_bound a (n+h) H
  change 4*(n+h) ≤ _+_+_+_+26+15*H.card at hcount
  rw [hcardH] at hcount
  have hM : 4*n ≤ n*(n+1)/2 := by
    have hx : 8*n ≤ n*(n+1) := by nlinarith
    omega
  have hgold := PlasticNestedFamily.golden_sum_lower Real.goldenRatio
    Real.one_lt_goldenRatio Real.goldenRatio_sq n (by omega)
  change n*(n+1)/2 ≤ (G+G).card+(n-3) at hgold
  have hsum : (A+A).card ≤ n*(n+1)/2-4*n+26+11*h := by
    dsimp only [A]
    dsimp only [E,I] at hcoll ⊢
    omega
  refine ⟨hcardA,hprod,by omega,hsum,?_⟩
  omega

end D5.S3.Arith.Additive.PlasticDeletionBound
