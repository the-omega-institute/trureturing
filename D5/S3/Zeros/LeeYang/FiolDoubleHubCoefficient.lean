/- GID: D5/S3/Zeros/LeeYang/FiolDoubleHubCoefficient
   generality: I
   mirror-B: D5/B/S3/Zeros/LeeYang/FiolDoubleHubCoefficient
   mirror-E: none(waiver:analytic-family-proof)
   anchors: []
   utility: none
   digest: All-parameter physical double-hub coefficient identities. -/
import D5.S3.Zeros.LeeYang.FiolDoubleHubIncidence
import D5.S3.Zeros.LeeYang.QuiverTreeIsingRefutation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Fin.InsertNth

open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Zeros.LeeYang
open FiolDoubleHubEndpoint
open scoped BigOperators
open Polynomial Finset
set_option autoImplicit false
set_option relaxedAutoImplicit false
open FiolDoubleHubEndpoint
namespace FiolDoubleHub

private theorem center_increments (m : ℕ) (A S : Finset (Edge m)) :
    increments A S none = ((A \ S).filter (fun e => e.2=none)).card := by
  classical
  have hs : (Finset.univ.filter (fun e : Edge m => src e=none ∧ e ∈ S)) = ∅ := by
    simp [src]
  have ht : (Finset.univ.filter (fun e : Edge m => tgt e=none ∧ e ∈ A \ S)) =
      (A \ S).filter (fun e => e.2=none) := by
    ext e
    rcases e with ⟨b,o⟩
    cases o <;> simp [tgt] <;> tauto
  simp only [increments,hs,ht,Finset.card_empty,zero_add]

private theorem hub_increments (m : ℕ) (A S : Finset (Edge m)) (b : Bool) :
    increments A S (some (b,none)) = (if (b,none) ∈ S then 1 else 0) +
      ((A \ S).filter (fun e => e.1=b ∧ e.2≠none)).card := by
  classical
  have hs : (Finset.univ.filter (fun e : Edge m => src e=some (b,none) ∧ e ∈ S)) =
      if (b,none) ∈ S then {(b,none)} else ∅ := by
    ext e
    by_cases hb : (b,none) ∈ S
    · simp [src,hb]
      aesop
    · simp [src,hb]
      aesop
  have ht : (Finset.univ.filter (fun e : Edge m => tgt e=some (b,none) ∧ e ∈ A \ S)) =
      (A \ S).filter (fun e => e.1=b ∧ e.2≠none) := by
    ext e
    rcases e with ⟨c,o⟩
    cases o <;> simp [tgt] <;> tauto
  simp only [increments,hs,ht]
  split_ifs <;> simp

private theorem selectedLeaves_card (m : ℕ) (S : Finset (Edge m)) :
    (selectedLeaves m S).card = (S.filter (fun e => e.2≠none)).card := by
  classical
  have he : (selectedLeaves m S).image (fun bi => (bi.1,some bi.2)) =
      S.filter (fun e => e.2≠none) := by
    ext e
    rcases e with ⟨b,o⟩
    cases o <;> simp [selectedLeaves,Finset.mem_image]
  rw [←he,Finset.card_image_of_injective]
  intro x y h
  rcases x with ⟨b,i⟩
  rcases y with ⟨c,j⟩
  simpa using h

private noncomputable def hubFactor (d r : ℕ) : Polynomial ℝ :=
  1 + Polynomial.C ((-1:ℝ)^d) * Polynomial.X^(d+r)

private noncomputable def hubBase (d r : ℕ) : Polynomial ℝ :=
  if Odd d then S (d+r) else H (d+r)

private theorem hubFactor_parity (d r : ℕ) :
    hubFactor d r = (if Odd d then 1-Polynomial.X else 1) * hubBase d r := by
  by_cases ho : Odd d
  · simp only [hubFactor,hubBase,ho,ite_true,ho.neg_one_pow,Polynomial.C_neg,
      Polynomial.C_1,neg_one_mul,←sub_eq_add_neg]
    simpa [S,mul_comm] using (geom_sum_mul_neg (Polynomial.X : Polynomial ℝ) (d+r)).symm
  · have he : Even d := Nat.not_odd_iff_even.mp ho
    simp [hubFactor,hubBase,ho,he.neg_one_pow,H]

private noncomputable def endpointBlock (m : ℕ) (A S : Finset (Edge m)) : Polynomial ℝ :=
  Polynomial.C (18 * ∏ v : Vertex m, endpointRatio (degree v) (increments A S v)) *
    ∏ v : Vertex m, (1+Polynomial.C ((-1:ℝ)^degree v) *
      Polynomial.X^(degree v+increments A S v))

private theorem endpointBlock_reduction (m : ℕ) (A S : Finset (Edge m)) :
    endpointBlock m A S =
      Polynomial.C (18 * endpointRatio 2 (increments A S none) *
        endpointRatio (m+1) (increments A S (some (false,none))) *
        endpointRatio (m+1) (increments A S (some (true,none)))) *
      H (2+increments A S none) *
      hubFactor (m+1) (increments A S (some (false,none))) *
      hubFactor (m+1) (increments A S (some (true,none))) *
      (1-Polynomial.X)^(2*m) *
      (Polynomial.C (1/3:ℝ)*(1+Polynomial.X))^(selectedLeaves m S).card := by
  classical
  let t (v : Vertex m) : Polynomial ℝ :=
    Polynomial.C (endpointRatio (degree v) (increments A S v)) *
      (1+Polynomial.C ((-1:ℝ)^degree v) * Polynomial.X^(degree v+increments A S v))
  have hd : (∏ v : Vertex m,t v) = t none * t (some (false,none)) * t (some (true,none)) *
      ∏ bi : Bool × Fin m, t (some (bi.1,some bi.2)) := by
    change (∏ v : Option (Bool × Option (Fin m)),t v) = _
    simp only [Fintype.prod_option,Fintype.prod_prod_type,Fintype.prod_bool]
    ring
  have hprod : endpointBlock m A S = Polynomial.C 18 * ∏ v : Vertex m,t v := by
    dsimp [endpointBlock,t]
    rw [Finset.prod_mul_distrib]
    simp only [←map_prod,Polynomial.C_mul]
    ring
  rw [hprod,hd]
  have hl := leaf_vertex_product m A S
  change (∏ bi : Bool × Fin m,t (some (bi.1,some bi.2))) = _ at hl
  rw [hl]
  dsimp [t]
  rw [center_degree,hub_degree,hub_degree]
  norm_num [H,hubFactor,Polynomial.C_mul]
  ring

private noncomputable def placementBlock (m : ℕ) (A : Finset (Edge m)) : Polynomial ℝ :=
  ∑ S ∈ A.powerset, endpointBlock m A S

private theorem source_placement_sum (m cutoff : ℕ) (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :
    sourceCoefficient m cutoff = Polynomial.C (200*(12:ℝ)^(2*m)) *
      ∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2, placementBlock m A :=
  actual_source_normalization m cutoff hm hc

end FiolDoubleHub
namespace FiolDoubleHub

private theorem placement_member_card (m : ℕ) (A : Finset (Edge m))
    (hA : A ∈ placementsCC m ∨ A ∈ placementsCPsame m ∨ A ∈ placementsCPopp m ∨
      A ∈ placementsPPsame m ∨ A ∈ placementsPPopp m) : A.card = 2 := by
  classical
  rcases hA with h | h | h | h | h
  · have he : A={(false,none),(true,none)} := by simpa [placementsCC] using h
    rw [he]
    simp
  · obtain ⟨⟨b,i⟩,_,rfl⟩ := Finset.mem_image.mp h
    simp
  · obtain ⟨⟨b,i⟩,_,rfl⟩ := Finset.mem_image.mp h
    simp
  · obtain ⟨⟨b,B⟩,hb,rfl⟩ := Finset.mem_image.mp h
    rw [Finset.card_image_of_injective]
    · exact (Finset.mem_powersetCard.mp (Finset.mem_product.mp hb).2).2
    · intro i j he
      simpa using he
  · obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp h
    simp

private theorem actual_placement_union (m : ℕ) :
    (Finset.univ : Finset (Edge m)).powersetCard 2 =
      placementsCC m ∪ (placementsCPsame m ∪ (placementsCPopp m ∪
        (placementsPPsame m ∪ placementsPPopp m))) := by
  classical
  ext A
  simp only [Finset.mem_powersetCard,Finset.subset_univ,true_and,Finset.mem_union]
  exact ⟨placement_exhaustive m A,placement_member_card m A⟩

private theorem actual_placement_total (m : ℕ) :
    ((Finset.univ : Finset (Edge m)).powersetCard 2).card = (m+1)*(2*m+1) := by
  classical
  rw [Finset.card_powersetCard,Finset.card_univ]
  have hc : Fintype.card (Edge m) = 2*m+2 := by simp [Edge]; omega
  rw [hc]
  have hd := Nat.descFactorial_eq_factorial_mul_choose (2*m+2) 2
  norm_num [Nat.descFactorial,Nat.factorial] at hd
  nlinarith

private theorem placement_card_add (m : ℕ) (hm : 1 ≤ m) :
    (placementsCC m ∪ (placementsCPsame m ∪ (placementsCPopp m ∪
        (placementsPPsame m ∪ placementsPPopp m)))).card =
      (placementsCC m).card + (placementsCPsame m).card + (placementsCPopp m).card +
        (placementsPPsame m).card + (placementsPPopp m).card := by
  rw [←actual_placement_union,actual_placement_total]
  obtain ⟨h0,h1,h2,h3,h4⟩ := placement_counts m
  rw [h0,h1,h2,h3,h4]
  have hs : m-1+1=m := Nat.sub_add_cancel hm
  nlinarith

private theorem five_finset_sum {α R : Type} [DecidableEq α] [AddCommMonoid R]
    (s0 s1 s2 s3 s4 : Finset α) (f : α → R)
    (hc : (s0 ∪ (s1 ∪ (s2 ∪ (s3 ∪ s4)))).card =
      s0.card+s1.card+s2.card+s3.card+s4.card) :
    (∑ x ∈ s0 ∪ (s1 ∪ (s2 ∪ (s3 ∪ s4))), f x) =
      (∑ x ∈ s0,f x)+(∑ x ∈ s1,f x)+(∑ x ∈ s2,f x)+
      (∑ x ∈ s3,f x)+(∑ x ∈ s4,f x) := by
  have h01 := Finset.card_union_le s0 (s1 ∪ (s2 ∪ (s3 ∪ s4)))
  have h12 := Finset.card_union_le s1 (s2 ∪ (s3 ∪ s4))
  have h23 := Finset.card_union_le s2 (s3 ∪ s4)
  have h34 := Finset.card_union_le s3 s4
  have hi0 := Finset.card_union_add_card_inter s0 (s1 ∪ (s2 ∪ (s3 ∪ s4)))
  have hi1 := Finset.card_union_add_card_inter s1 (s2 ∪ (s3 ∪ s4))
  have hi2 := Finset.card_union_add_card_inter s2 (s3 ∪ s4)
  have hi3 := Finset.card_union_add_card_inter s3 s4
  have hd0 : Disjoint s0 (s1 ∪ (s2 ∪ (s3 ∪ s4))) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  have hd1 : Disjoint s1 (s2 ∪ (s3 ∪ s4)) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  have hd2 : Disjoint s2 (s3 ∪ s4) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  have hd3 : Disjoint s3 s4 :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  rw [Finset.sum_union hd0,Finset.sum_union hd1,Finset.sum_union hd2,Finset.sum_union hd3]
  ac_rfl

private theorem actual_placement_sum {R : Type} [AddCommMonoid R]
    (m : ℕ) (hm : 1 ≤ m) (f : Finset (Edge m) → R) :
    (∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,f A) =
      (∑ A ∈ placementsCC m,f A)+(∑ A ∈ placementsCPsame m,f A)+
      (∑ A ∈ placementsCPopp m,f A)+(∑ A ∈ placementsPPsame m,f A)+
      (∑ A ∈ placementsPPopp m,f A) := by
  classical
  rw [actual_placement_union]
  exact five_finset_sum _ _ _ _ _ f (placement_card_add m hm)

end FiolDoubleHub
namespace FiolDoubleHub

private theorem pair_endpoint_expansion {E R : Type} [DecidableEq E] [AddCommMonoid R]
    (e f : E) (hef : e≠f) (g : Finset E → R) :
    (∑ S ∈ ({e,f} : Finset E).powerset,g S) =
      g ∅ + g {e} + g {f} + g {e,f} := by
  rw [Finset.sum_powerset_insert (by simp [hef])]
  have hs (q : Finset E → R) : (∑ S ∈ ({f} : Finset E).powerset,q S) = q ∅+q {f} := by
    change (∑ S ∈ (insert f ∅ : Finset E).powerset,q S) = _
    rw [Finset.sum_powerset_insert (by simp)]
    simp
  rw [hs,hs]
  simp only [Finset.insert_empty]
  ac_rfl

private noncomputable def qCC (d : ℕ) : Polynomial ℝ :=
  Polynomial.C (2*(d:ℝ)^2)*H 2*V d^2 +
  Polynomial.C (8*(d:ℝ))*H 3*U d*V d + Polynomial.C 9*H 4*U d^2
private noncomputable def qCPsame (d : ℕ) : Polynomial ℝ :=
  Polynomial.C ((3/2:ℝ)*(d:ℝ)*((d:ℝ)+1))*H 2*U d*W d +
  Polynomial.C (2*(d:ℝ))*H 2*(1+Polynomial.X)*U d*V d +
  Polynomial.C (4*(d:ℝ))*H 3*U d*V d +
  Polynomial.C 4*H 3*(1+Polynomial.X)*U d^2
private noncomputable def qCPopp (d : ℕ) : Polynomial ℝ :=
  Polynomial.C (2*(d:ℝ)^2)*H 2*V d^2 +
  Polynomial.C (2*(d:ℝ))*H 2*(1+Polynomial.X)*U d*V d +
  Polynomial.C (4*(d:ℝ))*H 3*U d*V d +
  Polynomial.C 4*H 3*(1+Polynomial.X)*U d^2
private noncomputable def qPPsame (d : ℕ) : Polynomial ℝ :=
  Polynomial.C ((3/2:ℝ)*(d:ℝ)*((d:ℝ)+1))*H 2*U d*W d +
  Polynomial.C (4*(d:ℝ))*H 2*(1+Polynomial.X)*U d*V d +
  Polynomial.C 2*H 2*(1+Polynomial.X)^2*U d^2
private noncomputable def qPPopp (d : ℕ) : Polynomial ℝ :=
  Polynomial.C (2*(d:ℝ)^2)*H 2*V d^2 +
  Polynomial.C (4*(d:ℝ))*H 2*(1+Polynomial.X)*U d*V d +
  Polynomial.C 2*H 2*(1+Polynomial.X)^2*U d^2

private theorem h_in_m (m : ℕ) : h (m+1) = if Odd (m+1) then 2*m+2 else 2*m := by
  unfold h
  split_ifs <;> omega

private theorem placement_CC_value (m : ℕ) :
    placementBlock m {(false,none),(true,none)} =
      (1-Polynomial.X)^h (m+1)*qCC (m+1) := by
  classical
  rw [placementBlock,pair_endpoint_expansion _ _ (by simp)]
  simp only [endpointBlock_reduction,center_increments,hub_increments,selectedLeaves_card]
  simp [Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton]
  by_cases ho : Odd (m+1)
  all_goals
    simp only [h_in_m,ho,ite_true,ite_false]
    norm_num [qCC,U,V,W,hubBase,hubFactor_parity,ho,endpointRatio,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,div_eq_mul_inv,map_mul,map_add,map_pow,map_ofNat]
    simp only [pow_add,pow_two]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_natCast,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    ring

private theorem placement_CPsame_value (m : ℕ) (b : Bool) (i : Fin m) :
    placementBlock m {(b,none),(b,some i)} =
      (1-Polynomial.X)^h (m+1)*qCPsame (m+1) := by
  classical
  rw [placementBlock,pair_endpoint_expansion _ _ (by simp)]
  simp only [endpointBlock_reduction,center_increments,hub_increments,selectedLeaves_card]
  cases b <;> by_cases ho : Odd (m+1)
  all_goals
    simp only [h_in_m,ho,ite_true,ite_false]
    norm_num [qCPsame,U,V,W,hubBase,hubFactor_parity,ho,endpointRatio,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,div_eq_mul_inv,map_mul,map_add,map_pow,map_ofNat]
    simp only [pow_add,pow_two]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_natCast,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    ring

private theorem placement_CPopp_value (m : ℕ) (b : Bool) (i : Fin m) :
    placementBlock m {(b,none),(!b,some i)} =
      (1-Polynomial.X)^h (m+1)*qCPopp (m+1) := by
  classical
  rw [placementBlock,pair_endpoint_expansion _ _ (by simp)]
  simp only [endpointBlock_reduction,center_increments,hub_increments,selectedLeaves_card]
  cases b <;> by_cases ho : Odd (m+1)
  all_goals
    simp only [h_in_m,ho,ite_true,ite_false]
    norm_num [qCPopp,U,V,W,hubBase,hubFactor_parity,ho,endpointRatio,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,div_eq_mul_inv,map_mul,map_add,map_pow,map_ofNat]
    simp only [pow_add,pow_two]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_natCast,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    ring

private theorem placement_PPsame_value (m : ℕ) (b : Bool) (i j : Fin m) (hij : i≠j) :
    placementBlock m {(b,some i),(b,some j)} =
      (1-Polynomial.X)^h (m+1)*qPPsame (m+1) := by
  classical
  rw [placementBlock,pair_endpoint_expansion _ _ (by simp [hij])]
  simp only [endpointBlock_reduction,center_increments,hub_increments,selectedLeaves_card]
  cases b <;> by_cases ho : Odd (m+1)
  all_goals
    simp only [h_in_m,ho,ite_true,ite_false]
    norm_num [qPPsame,U,V,W,hubBase,hubFactor_parity,ho,endpointRatio,hij,Ne.symm hij,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,div_eq_mul_inv,map_mul,map_add,map_pow,map_ofNat]
    simp only [pow_add,pow_two]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_natCast,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    ring

private theorem placement_PPopp_value (m : ℕ) (i j : Fin m) :
    placementBlock m {(false,some i),(true,some j)} =
      (1-Polynomial.X)^h (m+1)*qPPopp (m+1) := by
  classical
  rw [placementBlock,pair_endpoint_expansion _ _ (by simp)]
  simp only [endpointBlock_reduction,center_increments,hub_increments,selectedLeaves_card]
  simp [Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton]
  by_cases ho : Odd (m+1)
  all_goals
    simp only [h_in_m,ho,ite_true,ite_false]
    norm_num [qPPopp,U,V,W,hubBase,hubFactor_parity,ho,endpointRatio,
      Finset.sdiff_eq_filter,Finset.filter_insert,Finset.filter_singleton,div_eq_mul_inv,map_mul,map_add,map_pow,map_ofNat]
    simp only [pow_add,pow_two]
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
      Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_natCast,
      Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
    ring

end FiolDoubleHub
namespace FiolDoubleHub

private theorem q_aggregate (m : ℕ) (hm : 1 ≤ m) :
    qCC (m+1) + Polynomial.C ((2*m:ℕ):ℝ)*qCPsame (m+1) +
      Polynomial.C ((2*m:ℕ):ℝ)*qCPopp (m+1) +
      Polynomial.C ((m*(m-1):ℕ):ℝ)*qPPsame (m+1) +
      Polynomial.C ((m^2:ℕ):ℝ)*qPPopp (m+1) = Q (m+1) := by
  simp only [qCC,qCPsame,qCPopp,qPPsame,qPPopp,Q,Nat.cast_add,Nat.cast_one,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hm,div_eq_mul_inv,map_add,map_mul,
    map_pow,map_sub,map_natCast]
  norm_num [map_ofNat]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_C,Polynomial.eval_natCast,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat]
  ring

private theorem weighted_placement_sum (m : ℕ) (hm : 1 ≤ m) :
    (∑ A ∈ (Finset.univ : Finset (Edge m)).powersetCard 2,placementBlock m A) =
      (1-Polynomial.X)^h (m+1)*Q (m+1) := by
  classical
  have sum_value (s : Finset (Finset (Edge m))) (q : Polynomial ℝ)
      (he : ∀ A ∈ s,placementBlock m A=(1-Polynomial.X)^h (m+1)*q) :
      (∑ A ∈ s,placementBlock m A) =
        Polynomial.C (s.card:ℝ)*(1-Polynomial.X)^h (m+1)*q := by
    calc
      _ = ∑ _A ∈ s,(1-Polynomial.X)^h (m+1)*q := Finset.sum_congr rfl he
      _ = _ := by simp [nsmul_eq_mul,mul_assoc]
  have h0 := sum_value (placementsCC m) (qCC (m+1)) (by
    intro A hA
    have ha : A={(false,none),(true,none)} := by simpa [placementsCC] using hA
    subst A
    exact placement_CC_value m)
  have h1 := sum_value (placementsCPsame m) (qCPsame (m+1)) (by
    intro A hA
    obtain ⟨⟨b,i⟩,_,rfl⟩ := Finset.mem_image.mp hA
    exact placement_CPsame_value m b i)
  have h2 := sum_value (placementsCPopp m) (qCPopp (m+1)) (by
    intro A hA
    obtain ⟨⟨b,i⟩,_,rfl⟩ := Finset.mem_image.mp hA
    exact placement_CPopp_value m b i)
  have h3 := sum_value (placementsPPsame m) (qPPsame (m+1)) (by
    intro A hA
    obtain ⟨⟨b,B⟩,hb,rfl⟩ := Finset.mem_image.mp hA
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hb).2).2
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp hc
    simp only [Finset.image_insert,Finset.image_singleton]
    exact placement_PPsame_value m b i j hij)
  have h4 := sum_value (placementsPPopp m) (qPPopp (m+1)) (by
    intro A hA
    obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_image.mp hA
    exact placement_PPopp_value m i j)
  rw [actual_placement_sum m hm,h0,h1,h2,h3,h4]
  obtain ⟨hc0,hc1,hc2,hc3,hc4⟩ := placement_counts m
  rw [hc0,hc1,hc2,hc3,hc4]
  calc
    _ = (1-Polynomial.X)^h (m+1) *
        (qCC (m+1)+Polynomial.C ((2*m:ℕ):ℝ)*qCPsame (m+1)+
          Polynomial.C ((2*m:ℕ):ℝ)*qCPopp (m+1)+
          Polynomial.C ((m*(m-1):ℕ):ℝ)*qPPsame (m+1)+
          Polynomial.C ((m^2:ℕ):ℝ)*qPPopp (m+1)) := by norm_num;ring
    _ = _ := by rw [q_aggregate m hm]

theorem actual_coefficient_identity (m cutoff : ℕ) (hm : 1 ≤ m) (hc : 3 ≤ cutoff) :
    sourceCoefficient m cutoff = Polynomial.C (200*(12:ℝ)^(2*m))*R m := by
  rw [source_placement_sum m cutoff hm hc,weighted_placement_sum m hm]
  rfl

end FiolDoubleHub

end D5.S3.Zeros.LeeYang
