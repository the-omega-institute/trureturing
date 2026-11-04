/- GID: D5/S3/Arith/Additive/PlasticNestedFamily
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticNestedFamily
   mirror-E: none(waiver:real-algebraic-power-families)
   anchors: []
   utility: none
   digest: The original plastic nested family has exact product and sum counts and beats golden powers. -/

import D5.S3.Arith.Additive.PlasticPowerCollisions
import Mathlib.NumberTheory.Real.GoldenRatio

/-! Native real power sets for the complete original nested-family theorem. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Additive.PlasticNestedFamily

open scoped Pointwise
open D5.S3.Arith.Additive.PlasticPowerCollisions

private theorem golden_normalized (s : ℝ) (hs : 1 < s) (hsq : s ^ 2 = s+1)
    (d a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hbd : b < d)
    (h : 1+s ^ d = s ^ a+s ^ b) : d=3 ∧ a=2 ∧ b=2 := by
  have hspos : 0 < s := by linarith
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hm := zpow_right_strictMono₀ hs
  have htwo : 2 < s ^ (2:ℤ) := by norm_num only [zpow_ofNat]; linarith
  have hgap : s ^ (d-b) = 1+s ^ (a-b)-s ^ (-b) := by
    simp only [zpow_sub₀ hs0,zpow_neg]
    field_simp
    nlinarith
  have hgap2 : d-b < 2 := hm.lt_iff_lt.1 (show s ^ (d-b) < s ^ (2:ℤ) by
    have hx : s ^ (a-b) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hs) (by omega)
    have hy : 0 < s ^ (-b) := zpow_pos hspos _
    exact lt_trans (show s ^ (d-b) < 2 by linarith) htwo)
  have hd : d=b+1 := by omega
  have hinv : s-1=s ^ (-1:ℤ) := by
    norm_num only [zpow_neg,zpow_one]
    rw [inv_eq_one_div]
    apply (eq_div_iff hs0).2
    nlinarith [hsq]
  have hshift : s ^ (b-1)=s ^ b*(s-1) := by
    rw [show b-1=b+(-1) by omega,zpow_add₀ hs0,hinv]
  have hdiff : s ^ a-s ^ (b-1) = 1 := by
    rw [hd,zpow_add₀ hs0,zpow_one] at h
    rw [hshift]
    nlinarith
  have hba : b-1 < a := hm.lt_iff_lt.1 (by linarith)
  have hab' : a=b := by omega
  have he : s ^ (a-2)=1 := by
    rw [hab'] at hdiff ⊢
    simp only [zpow_sub₀ hs0,zpow_one,zpow_ofNat] at hdiff ⊢
    field_simp at hdiff ⊢
    nlinarith [hsq]
  have ha2 : a=2 := by
    have hh := hm.injective (he.trans (zpow_zero s).symm)
    omega
  omega

private theorem golden_sorted (s : ℝ) (hs : 1 < s) (hsq : s ^ 2 = s+1)
    (i j k l : ℤ) (_hij : i ≤ j) (hkl : k ≤ l) (hik : i < k)
    (he : s ^ i+s ^ j = s ^ k+s ^ l) : j=i+3 := by
  have hspos : 0 < s := by linarith
  have hs0 : s ≠ 0 := ne_of_gt hspos
  have hm := zpow_right_strictMono₀ hs
  have hlj : l<j := hm.lt_iff_lt.1 (by have := hm hik; linarith)
  have hn : 1+s ^ (j-i)=s ^ (k-i)+s ^ (l-i) := by
    simp only [zpow_sub₀ hs0]
    field_simp
    nlinarith
  have hc := golden_normalized s hs hsq (j-i) (k-i) (l-i)
    (by omega) (by omega) (by omega) hn
  omega

private theorem golden_sum_lower (s : ℝ) (hs : 1 < s) (hsq : s ^ 2 = s+1)
    (n : ℕ) (hn : 7 ≤ n) :
    n*(n+1)/2 ≤
      (((Finset.Icc (0:ℤ) ((n:ℤ)-1)).image (fun e => s ^ e)) +
       ((Finset.Icc (0:ℤ) ((n:ℤ)-1)).image (fun e => s ^ e))).card + (n-3) := by
  classical
  let E := Finset.Icc (0:ℤ) ((n:ℤ)-1)
  let P := (E ×ˢ E).filter (fun p => p.1 ≤ p.2)
  let O := P.filter (fun p => p.2=p.1+3)
  let Q := P.filter (fun p => p.2≠p.1+3)
  let f : ℤ × ℤ → ℝ := fun p => s ^ p.1+s ^ p.2
  have hinj : Set.InjOn f Q := by
    intro p hp q hq he
    obtain ⟨hpP,hpn⟩ := Finset.mem_filter.1 hp
    obtain ⟨hqP,hqn⟩ := Finset.mem_filter.1 hq
    have hp := (Finset.mem_filter.1 hpP).2
    have hq := (Finset.mem_filter.1 hqP).2
    by_cases heq : p.1=q.1
    · exact Prod.ext heq ((zpow_right_strictMono₀ hs).injective (by
        dsimp [f] at he; rw [heq] at he; linarith))
    · rcases lt_or_gt_of_ne heq with hlt | hgt
      · exact (hpn (golden_sorted s hs hsq _ _ _ _ hp hq hlt he)).elim
      · exact (hqn (golden_sorted s hs hsq _ _ _ _ hq hp hgt he.symm)).elim
  have hsub : Q.image f ⊆ E.image (fun e => s ^ e) + E.image (fun e => s ^ e) := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hp,_⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp,_⟩ := Finset.mem_filter.1 hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.1 hp
    exact Finset.mem_add.2 ⟨s ^ p.1,Finset.mem_image.2 ⟨_,hp1,rfl⟩,
      s ^ p.2,Finset.mem_image.2 ⟨_,hp2,rfl⟩,rfl⟩
  have hQ : Q.card ≤ (E.image (fun e => s ^ e) + E.image (fun e => s ^ e)).card := by
    rw [← Finset.card_image_of_injOn hinj]
    exact Finset.card_le_card hsub
  have hO : O = (Finset.Icc (0:ℤ) ((n:ℤ)-4)).image (fun t => (t,t+3)) := by
    ext p
    constructor
    · intro h
      obtain ⟨hp,he⟩ := Finset.mem_filter.1 h
      obtain ⟨hp,hps⟩ := Finset.mem_filter.1 hp
      obtain ⟨hp1,hp2⟩ := Finset.mem_product.1 hp
      simp only [E,Finset.mem_Icc] at hp1 hp2
      exact Finset.mem_image.2 ⟨p.1,Finset.mem_Icc.2 ⟨hp1.1,by omega⟩,
        Prod.ext rfl he.symm⟩
    · intro h
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 h
      obtain ⟨ht0,htn⟩ := Finset.mem_Icc.1 ht
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_product.2
        ⟨Finset.mem_Icc.2 ⟨ht0,by omega⟩,
         Finset.mem_Icc.2 ⟨by omega,by omega⟩⟩,by dsimp; omega⟩,rfl⟩
  have hcardO : O.card=n-3 := by
    rw [hO,Finset.card_image_of_injective _ (fun x y h =>
      congrArg (fun p : ℤ × ℤ => p.1) h),Int.card_Icc]
    omega
  have hpart : O.card+Q.card=P.card := Finset.card_filter_add_card_filter_not
    (s:=P) (fun p => p.2=p.1+3)
  have hcardP : P.card=(n+1).choose 2 := by
    have hP : P = ((E ×ˢ E).filter (fun p => p.1 < p.2)) ∪ E.diag := by
      ext p
      simp only [P,Finset.mem_filter,Finset.mem_product,Finset.mem_union,Finset.mem_diag]
      constructor
      · rintro ⟨⟨hp,hq⟩,hle⟩
        by_cases he : p.1=p.2
        · exact Or.inr ⟨hp,he⟩
        · exact Or.inl ⟨⟨hp,hq⟩,by omega⟩
      · rintro (⟨⟨hp,hq⟩,hlt⟩ | ⟨hp,he⟩)
        · exact ⟨⟨hp,hq⟩,le_of_lt hlt⟩
        · exact ⟨⟨hp,he ▸ hp⟩,le_of_eq he⟩
    rw [hP,Finset.card_union_of_disjoint]
    · rw [Finset.card_product_filter_lt,Finset.diag_card]
      have hE : E.card=n := by simp only [E,Int.card_Icc]; omega
      rw [hE,Nat.choose_succ_succ']
      simp [Nat.add_comm]
    · apply Finset.disjoint_left.2
      intro p hp hq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_diag.1 hq).2
      omega
  rw [hcardO,hcardP,Nat.choose_two_right] at hpart
  have hnn : n+1-1=n := by omega
  rw [hnn,Nat.mul_comm (n+1) n] at hpart
  change n*(n+1)/2 ≤ (E.image (fun e => s ^ e) + E.image (fun e => s ^ e)).card+(n-3)
  omega

/-- Complete original Theorem 2.1, with the same native real power set in every clause.
Natural indices n ≥ 7 parametrize exactly the original integer indices n ≥ 7. -/
theorem whole_theorem_two_one (r : ℝ) (hr : 1 < r) (hroot : r ^ 3=r+1)
    (n : ℕ) (hn : 7 ≤ n) :
    let E : Finset ℤ := {0,3} ∪ Finset.Icc 5 ((n:ℤ)+2)
    let F : Finset ℤ := {0,3} ∪ Finset.Icc 5 ((n:ℤ)+3)
    let B := E.image (fun e => r ^ e)
    let Bnext := F.image (fun e => r ^ e)
    let G := (Finset.Icc (0:ℤ) ((n:ℤ)-1)).image (fun e => Real.goldenRatio ^ e)
    B ⊂ Bnext ∧ B.card=n ∧
      (B*B).card=2*n+2 ∧ (B*B).card ≤ 3*n-4 ∧
      (B+B).card = n*(n+1)/2 -
        (n-1+(n-8)+(n-9)+(n-11)+(if 8 ≤ n then 1 else 0)+(if 10 ≤ n then 1 else 0)) ∧
      (B+B).card ≤ (G+G).card-2 ∧
      (n=7 → B=({0,3,5,6,7,8,9}:Finset ℤ).image (fun e => r ^ e)) := by
  classical
  dsimp only
  let E : Finset ℤ := {0,3} ∪ Finset.Icc 5 ((n:ℤ)+2)
  let F : Finset ℤ := {0,3} ∪ Finset.Icc 5 ((n:ℤ)+3)
  let B := E.image (fun e => r ^ e)
  let Bnext := F.image (fun e => r ^ e)
  let G := (Finset.Icc (0:ℤ) ((n:ℤ)-1)).image (fun e => Real.goldenRatio ^ e)
  change B ⊂ Bnext ∧ B.card=n ∧ (B*B).card=2*n+2 ∧ (B*B).card ≤ 3*n-4 ∧
    (B+B).card = n*(n+1)/2 -
      (n-1+(n-8)+(n-9)+(n-11)+(if 8 ≤ n then 1 else 0)+(if 10 ≤ n then 1 else 0)) ∧
    (B+B).card ≤ (G+G).card-2 ∧
    (n=7 → B=({0,3,5,6,7,8,9}:Finset ℤ).image (fun e => r ^ e))
  have hr0 : r ≠ 0 := by linarith
  have hm := zpow_right_strictMono₀ hr
  have hcardE : E.card=n := by
    dsimp [E]
    rw [Finset.card_union_of_disjoint]
    · norm_num only [Finset.card_insert_of_notMem
        (by norm_num : (0:ℤ) ∉ ({3}:Finset ℤ)),Finset.card_singleton,Int.card_Icc]
      omega
    · apply Finset.disjoint_left.2
      intro t ht hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      simp only [Finset.mem_Icc] at hi
      omega
  have hcardB : B.card=n := by
    rw [Finset.card_image_of_injective _ hm.injective]
    exact hcardE
  have hnest : B ⊂ Bnext := by
    apply Finset.ssubset_iff_subset_ne.2
    constructor
    · apply Finset.image_subset_image
      intro t ht
      simp only [E,F,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_Icc] at ht ⊢
      omega
    · intro he
      have hh : r ^ ((n:ℤ)+3) ∈ Bnext := Finset.mem_image.2
        ⟨(n:ℤ)+3,Finset.mem_union.2 (Or.inr (Finset.mem_Icc.2 ⟨by omega,le_refl _⟩)),rfl⟩
      rw [← he] at hh
      obtain ⟨i,hi,hei⟩ := Finset.mem_image.1 hh
      have hi' := hm.injective hei
      rw [hi'] at hi
      simp only [E,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_Icc] at hi
      omega
  have hEE : E+E=({0,3}:Finset ℤ) ∪ Finset.Icc 5 (2*(n:ℤ)+4) := by
    ext t
    constructor
    · intro ht
      obtain ⟨i,hi,j,hj,rfl⟩ := Finset.mem_add.1 ht
      simp only [E,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_Icc] at hi hj ⊢
      omega
    · intro ht
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_Icc] at ht
      rcases ht with (rfl | rfl) | ⟨ht5,htn⟩
      · exact Finset.mem_add.2 ⟨0,by simp [E],0,by simp [E],by ring⟩
      · exact Finset.mem_add.2 ⟨0,by simp [E],3,by simp [E],by ring⟩
      · by_cases ht10 : t<10
        · exact Finset.mem_add.2 ⟨0,by simp [E],t,
            Finset.mem_union.2 (Or.inr (Finset.mem_Icc.2 ⟨ht5,by omega⟩)),by ring⟩
        · let a := max 5 (t-((n:ℤ)+2))
          have ha : a ∈ E := Finset.mem_union.2 (Or.inr (Finset.mem_Icc.2
            ⟨by dsimp [a]; omega,by dsimp [a]; omega⟩))
          have hb : t-a ∈ E := Finset.mem_union.2 (Or.inr (Finset.mem_Icc.2
            ⟨by dsimp [a]; omega,by dsimp [a]; omega⟩))
          exact Finset.mem_add.2 ⟨a,ha,t-a,hb,by ring⟩
  have hprod : B*B=(E+E).image (fun e => r ^ e) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,hu,v,hv,hx⟩ := Finset.mem_mul.1 hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hv
      exact Finset.mem_image.2 ⟨i+j,Finset.mem_add.2 ⟨i,hi,j,hj,rfl⟩,
        by rw [zpow_add₀ hr0]; exact hx⟩
    · intro hx
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨i,hi,j,hj,rfl⟩ := Finset.mem_add.1 hk
      exact Finset.mem_mul.2 ⟨r ^ i,Finset.mem_image.2 ⟨i,hi,rfl⟩,
        r ^ j,Finset.mem_image.2 ⟨j,hj,rfl⟩,(zpow_add₀ hr0 _ _).symm⟩
  have hprodcard : (B*B).card=2*n+2 := by
    rw [hprod,Finset.card_image_of_injective _ hm.injective,hEE,
      Finset.card_union_of_disjoint]
    · norm_num only [Finset.card_insert_of_notMem
        (by norm_num : (0:ℤ) ∉ ({3}:Finset ℤ)),Finset.card_singleton,Int.card_Icc]
      omega
    · apply Finset.disjoint_left.2
      intro t ht hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      simp only [Finset.mem_Icc] at hi
      omega
  have hsum := nested_family_sum_card r hr hroot n hn
  change (B+B).card +
    (n-1+(n-8)+(n-9)+(n-11)+(if 8 ≤ n then 1 else 0)+(if 10 ≤ n then 1 else 0)) =
    n*(n+1)/2 at hsum
  have hgold := golden_sum_lower Real.goldenRatio Real.one_lt_goldenRatio
    Real.goldenRatio_sq n hn
  change n*(n+1)/2 ≤ (G+G).card+(n-3) at hgold
  refine ⟨hnest,hcardB,hprodcard,by omega,by omega,?_,?_⟩
  · omega
  · intro he
    have hE : E=({0,3,5,6,7,8,9}:Finset ℤ) := by
      dsimp [E]
      rw [he]
      decide
    exact congrArg (fun T : Finset ℤ => T.image (fun e => r ^ e)) hE

end D5.S3.Arith.Additive.PlasticNestedFamily
