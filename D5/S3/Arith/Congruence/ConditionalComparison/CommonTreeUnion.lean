/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CommonTreeUnion
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/ConditionalComparison/CommonTreeUnion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Common regular subtree law and height-uniform union conditioning. -/

import D5.S3.Arith.Congruence.ConditionalComparison.ArithmeticCoordinates
import D5.S3.Arith.Congruence.ConditionalComparison.ThreePrime.Probability
import D5.S3.Arith.Congruence.ConditionalComparison.Cylinders
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

open scoped BigOperators
open Erdos7 Erdos7.FiniteLaw Finset
namespace Erdos7.CommonTreeUnion

abbrev Choice (s r : ℕ) := {S : Finset (Fin s) // S.card = r}

def Tree (s r : ℕ) : ℕ → Type
  | 0 => PUnit
  | B + 1 => Choice s r × (Fin s → Tree s r B)

noncomputable instance treeFintype (s r B : ℕ) : Fintype (Tree s r B) := by
  induction B with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ B ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Choice s r × (Fin s → Tree s r B)))

noncomputable def law {s r : ℕ} (hrs : r ≤ s) : (B : ℕ) → FiniteLaw (Tree s r B)
  | 0 => FiniteLaw.uniform PUnit
  | B + 1 => by
    classical
    haveI : Nonempty (Choice s r) := by
      obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
        (show r ≤ (Finset.univ : Finset (Fin s)).card by simpa using hrs)
      exact ⟨⟨S, hS⟩⟩
    exact (FiniteLaw.uniform (Choice s r)).joint
      (fun _ => FiniteLaw.piLaw (fun _ : Fin s => law hrs B))

def selected {s r : ℕ} : (B : ℕ) → Tree s r B → Word s B → Prop
  | 0, _, _ => True
  | B + 1, θ, w => w 0 ∈ θ.1.val ∧ selected B (θ.2 (w 0)) (Fin.tail w)

def Hit {s r B : ℕ} (θ : Tree s r B) (F : Word s B → Prop) : Prop :=
  ∃ w, F w ∧ selected B θ w

noncomputable instance hitDecidable {s r B : ℕ} (F : Word s B → Prop) :
    DecidablePred (fun θ : Tree s r B => Hit θ F) := Classical.decPred _

set_option maxHeartbeats 2000000 in
theorem union_conditioning {s r : ℕ} (hr : 2 ≤ r) (hrs : r < s)
    (B d : ℕ) (hd : d ≤ B) (w : Word s d) (F : Word s B → Prop) :
    (s : ℚ) * (r - 1) * (law hrs.le B).prob (fun θ => Hit θ (fun v => HasPrefix v w hd)) *
      (law hrs.le B).prob (fun θ => Hit θ F) ≤
    (r : ℚ) * (s - 1) * (law hrs.le B).prob
      (fun θ => Hit θ (fun v => HasPrefix v w hd) ∧ Hit θ F) := by
  classical
  haveI : Nonempty (Choice s r) := by
    obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
      (show r ≤ (Finset.univ : Finset (Fin s)).card by simpa using hrs.le)
    exact ⟨⟨S, hS⟩⟩
  have hrootJoint {s r : ℕ} (hrs : r ≤ s) (B : ℕ)
      [Nonempty (Choice s r)] (E : Tree s r (B+1) → Prop) [dE : DecidablePred E] :
      (law hrs (B+1)).prob E =
        (FiniteLaw.uniform (Choice s r)).expect (fun S =>
          (FiniteLaw.piLaw (fun _ : Fin s => law hrs B)).prob
            (fun x => E (S,x))) := by
    classical
    unfold FiniteLaw.prob
    have h := FiniteLaw.joint_expect (Ω := Choice s r) (Ξ := Fin s → Tree s r B)
      (FiniteLaw.uniform (Choice s r))
      (fun _ => FiniteLaw.piLaw (fun _ : Fin s => law hrs B))
      (fun z => @ite ℚ (E z) (dE z) 1 0)
    refine h.trans ?_
    apply FiniteLaw.expect_congr
    intro S
    apply FiniteLaw.expect_congr
    intro x
    by_cases he : E (S,x) <;> simp [he]
  have hprobD {X : Type} [Fintype X] (ν : FiniteLaw X) (P : X → Prop)
      (dP : DecidablePred P) : @FiniteLaw.prob X _ ν P dP =
        @FiniteLaw.prob X _ ν P (Classical.decPred P) := by
    exact @FiniteLaw.prob_congr X _ ν P P dP (Classical.decPred P) (fun _ => Iff.rfl)
  let average {α : Type} (V : Finset α) (k : ℕ) (g : Finset α → ℚ) : ℚ :=
    (∑ S ∈ V.powersetCard k, g S) / (Nat.choose V.card k : ℚ)
  have havgCongr {α : Type} {V : Finset α} {k : ℕ} {g h : Finset α → ℚ}
      (hgh : ∀ S ∈ V.powersetCard k, g S = h S) : average V k g = average V k h := by
    dsimp [average]
    congr 1
    exact Finset.sum_congr rfl hgh
  have hsplit {α : Type} [DecidableEq α] (R : Finset α) (i : α) (hi : i ∉ R)
      (k : ℕ) (hk : k + 1 ≤ R.card) (g : Finset α → ℚ) :
      average (insert i R) (k+1) g =
        ((k+1 : ℕ) : ℚ) / (R.card+1 : ℕ) * average R k (fun S => g (insert i S)) +
        (1 - ((k+1 : ℕ) : ℚ) / (R.card+1 : ℕ)) * average R (k+1) g := by
    classical
    have hnmem : ∀ S ∈ R.powersetCard k, i ∉ S := by
      intro S hS hiS
      exact hi ((mem_powersetCard.mp hS).1 hiS)
    have hd : Disjoint (R.powersetCard (k+1)) ((R.powersetCard k).image (insert i)) := by
      apply disjoint_left.mpr
      intro S hS hI
      obtain ⟨T, _, rfl⟩ := mem_image.mp hI
      exact hi ((mem_powersetCard.mp hS).1 (mem_insert_self i T))
    have hinj : ∀ S ∈ R.powersetCard k, ∀ T ∈ R.powersetCard k,
        insert i S = insert i T → S = T := by
      intro S hS T hT heq
      have he := congrArg (fun U : Finset α => U.erase i) heq
      simpa [hnmem S hS, hnmem T hT] using he
    have hsplit : (∑ S ∈ (insert i R).powersetCard (k+1), g S) =
        (∑ S ∈ R.powersetCard (k+1), g S) +
        ∑ S ∈ R.powersetCard k, g (insert i S) := by
      rw [powersetCard_succ_insert hi, sum_union hd, sum_image hinj]
    have ha : (Nat.choose R.card k : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : k ≤ R.card)).ne'
    have hb : (Nat.choose R.card (k+1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hk).ne'
    have hc : (Nat.choose (R.card+1) (k+1) : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : k+1 ≤ R.card+1)).ne'
    have hn : ((R.card+1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hpascal : (Nat.choose (R.card+1) (k+1) : ℚ) =
        (Nat.choose R.card k : ℚ) + (Nat.choose R.card (k+1) : ℚ) := by
      exact_mod_cast Nat.choose_succ_succ' R.card k
    have hmul : ((R.card+1 : ℕ) : ℚ) * (Nat.choose R.card k : ℚ) =
        (Nat.choose (R.card+1) (k+1) : ℚ) * ((k+1 : ℕ) : ℚ) := by
      exact_mod_cast Nat.add_one_mul_choose_eq R.card k
    have hratio : (Nat.choose R.card k : ℚ) / Nat.choose (R.card+1) (k+1) =
        ((k+1 : ℕ) : ℚ) / (R.card+1 : ℕ) := by
      apply (div_eq_div_iff hc hn).mpr
      simpa only [mul_comm] using hmul
    have hratio' : (Nat.choose R.card (k+1) : ℚ) / Nat.choose (R.card+1) (k+1) =
        1 - ((k+1 : ℕ) : ℚ) / (R.card+1 : ℕ) := by
      rw [← hratio]
      apply (eq_sub_iff_add_eq).mpr
      rw [← add_div, add_comm, ← hpascal]
      exact div_self hc
    unfold average
    rw [hsplit, card_insert_of_notMem hi, ← hratio', ← hratio]
    field_simp
    <;> ring
  have huniform {α : Type} [Fintype α] [DecidableEq α] (k : ℕ)
      [Nonempty {S : Finset α // S.card = k}] (g : Finset α → ℚ) :
      (FiniteLaw.uniform {S : Finset α // S.card = k}).expect (fun S => g S.val) =
        average (univ : Finset α) k g := by
    classical
    have hm : ∀ S : Finset α, S ∈ (univ : Finset α).powersetCard k ↔ S.card = k := by
      intro S
      simp
    have hc : Fintype.card {S : Finset α // S.card = k} =
        Nat.choose (univ : Finset α).card k := by
      rw [Fintype.card_of_subtype ((univ : Finset α).powersetCard k) hm,
        card_powersetCard]
    unfold FiniteLaw.expect average
    simp_rw [FiniteLaw.uniform_weight]
    rw [← mul_sum, ← Finset.sum_subtype ((univ : Finset α).powersetCard k) hm g, hc]
    ring
  have halgebra (r s : ℚ) (hr : 1 < r) (hrs : r < s)
      (a q z u v : ℚ) (ha : 0 ≤ a) (hq : 0 ≤ q)
      (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
      (hdel : (r-1)*v ≤ r*u)
      (hchild : s*(r-1)*a*q ≤ r*(s-1)*z) :
      s*(r-1)*(r/s*a)*(r/s*(u+(1-u)*q)+(1-r/s)*v) ≤
        r*(s-1)*(r/s*(a*u+(1-u)*z)) := by
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    have hs0 : 0 < s := lt_trans hr0 hrs
    have hsm : 0 < s-1 := by linarith
    let t := r/s
    let κ := s*(r-1)/(r*(s-1))
    have ht0 : 0 ≤ t := le_of_lt (div_pos hr0 hs0)
    have ht1 : t ≤ 1 := (div_le_one hs0).mpr (le_of_lt hrs)
    have hk0 : 0 ≤ κ := le_of_lt (div_pos (mul_pos hs0 (by linarith)) (mul_pos hr0 hsm))
    have hkrel : (r-1)*(1-κ*t) = r*κ*(1-t) := by
      dsimp [κ,t]
      field_simp [hr0.ne', hs0.ne', hsm.ne']
      <;> ring
    have hcd : κ*a*q ≤ z := by
      dsimp [κ]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
      apply (div_le_iff₀ (mul_pos hr0 hsm)).mpr
      nlinarith only [hchild]
    have hdw : κ*(1-t)*v ≤ (1-κ*t)*u := by
      have h := mul_le_mul_of_nonneg_left hdel (mul_nonneg hk0 (sub_nonneg.mpr ht1))
      have h' : (r-1)*(κ*(1-t)*v) ≤ (r-1)*((1-κ*t)*u) := by
        calc
          _ = κ*(1-t)*((r-1)*v) := by ring
          _ ≤ κ*(1-t)*(r*u) := h
          _ = (r-1)*((1-κ*t)*u) := by rw [show κ*(1-t)*(r*u) = (r*κ*(1-t))*u by ring, ← hkrel]; ring
      exact (mul_le_mul_iff_right₀ (show 0 < r-1 by linarith)).mp h'
    have hqb : κ*(t*(u+(1-u)*q)+(1-t)*v) ≤ u+κ*(1-u)*q := by
      have hc := mul_nonneg (mul_nonneg (mul_nonneg hk0 (sub_nonneg.mpr hu1)) hq) (sub_nonneg.mpr ht1)
      nlinarith
    have hzb : a*(u+κ*(1-u)*q) ≤ a*u+(1-u)*z := by
      have hc := mul_le_mul_of_nonneg_left hcd (sub_nonneg.mpr hu1)
      nlinarith
    have hres : κ*(t*a)*(t*(u+(1-u)*q)+(1-t)*v) ≤ t*(a*u+(1-u)*z) := by
      calc
        _ = t*(a*(κ*(t*(u+(1-u)*q)+(1-t)*v))) := by ring
        _ ≤ t*(a*(u+κ*(1-u)*q)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqb ha) ht0
        _ ≤ _ := mul_le_mul_of_nonneg_left hzb ht0
    have hscale : r*(s-1)*κ = s*(r-1) := by
      dsimp [κ]
      field_simp [hr0.ne', hsm.ne']
      <;> ring
    calc
      _ = (r*(s-1))*(κ*(t*a)*(t*(u+(1-u)*q)+(1-t)*v)) := by
        rw [← hscale]
        dsimp [t]
        ring
      _ ≤ (r*(s-1))*(t*(a*u+(1-u)*z)) :=
        mul_le_mul_of_nonneg_left hres (le_of_lt (mul_pos hr0 hsm))
      _ = _ := rfl
  have havgAffine {α : Type} (V : Finset α) (k : ℕ) (hk : k ≤ V.card)
      (g : Finset α → ℚ) (c d : ℚ) :
      average V k (fun S => c + d*g S) = c+d*average V k g := by
    have hden : (Nat.choose V.card k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    simp only [average, Finset.sum_add_distrib, Finset.sum_const, Finset.card_powersetCard,
      nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
    <;> ring
  have havgBound {α : Type} (V : Finset α) (k : ℕ) (hk : k ≤ V.card)
      (g : Finset α → ℚ) (hg : ∀ S ∈ V.powersetCard k, 0 ≤ g S ∧ g S ≤ 1) :
      0 ≤ average V k g ∧ average V k g ≤ 1 := by
    have hden : (0 : ℚ) < Nat.choose V.card k := by exact_mod_cast Nat.choose_pos hk
    constructor
    · exact div_nonneg (Finset.sum_nonneg fun S hS => (hg S hS).1) hden.le
    · apply (div_le_one hden).mpr
      calc
        _ ≤ ∑ S ∈ V.powersetCard k, (1 : ℚ) := Finset.sum_le_sum fun S hS => (hg S hS).2
        _ = _ := by simp [Finset.card_powersetCard]
  have havgConst {α : Type} (V : Finset α) (k : ℕ) (hk : k ≤ V.card) (c : ℚ) :
      average V k (fun _ => c) = c := by
    simpa only [zero_mul, add_zero] using havgAffine V k hk (fun _ => 0) c 0
  have erase_sum_ambient {β : Type} [DecidableEq β] (V : Finset β)
      (k : ℕ) (f : Finset β → ℚ) :
      (∑ S ∈ V.powersetCard (k + 1), ∑ x ∈ S, f (S.erase x)) =
        ((V.card - k : ℕ) : ℚ) * ∑ R ∈ V.powersetCard k, f R := by
    classical
    calc
      (∑ S ∈ V.powersetCard (k + 1), ∑ x ∈ S, f (S.erase x)) =
          ∑ (S ∈ V.powersetCard (k + 1)) (x ∈ V) with x ∈ S, f (S.erase x) := by
        rw [← Finset.sum_finset_product']
        grind
      _ = ∑ (R ∈ V.powersetCard k) (x ∈ V) with x ∉ R, f R := by
        apply Finset.sum_bij' (fun ⟨S, x⟩ _ => ⟨S.erase x, x⟩)
          (fun ⟨R, x⟩ _ => ⟨insert x R, x⟩)
        · intro p hp; dsimp at hp ⊢; congr 1; grind
        · intro p hp; dsimp at hp ⊢; congr 1; grind
        all_goals grind
      _ = ∑ R ∈ V.powersetCard k, ∑ x ∈ V \ R, f R := by
        rw [← Finset.sum_finset_product']
        grind
      _ = ((V.card - k : ℕ) : ℚ) * ∑ R ∈ V.powersetCard k, f R := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        have hRV := (Finset.mem_powersetCard.mp hR).1
        have hRk := (Finset.mem_powersetCard.mp hR).2
        simp [Finset.card_sdiff_of_subset hRV, hRk]
  have delete_hit_count {α : Type} [DecidableEq α] (k : ℕ) (S D : Finset α) (hS : S.card = k + 1) :
      (k : ℚ) * (if (S ∩ D).Nonempty then 1 else 0) ≤
        ∑ x ∈ S, (if (S.erase x ∩ D).Nonempty then (1 : ℚ) else 0) := by
    classical
    by_cases hh : (S ∩ D).Nonempty
    · obtain ⟨d, hd⟩ := hh
      obtain ⟨hdS, hdD⟩ := Finset.mem_inter.mp hd
      have he : (S.erase d).card = k := by
        rw [Finset.card_erase_of_mem hdS, hS]
        omega
      have hc : (k : ℚ) = ∑ x ∈ S.erase d, (1 : ℚ) := by simp [he]
      have hret : ∀ x ∈ S.erase d, (S.erase x ∩ D).Nonempty := by
        intro x hx
        exact ⟨d, Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr
          ⟨(Finset.mem_erase.mp hx).1.symm, hdS⟩, hdD⟩⟩
      have hh' : (S ∩ D).Nonempty := ⟨d, hd⟩
      simp only [if_pos hh', mul_one]
      calc
        (k : ℚ) = ∑ x ∈ S.erase d, (1 : ℚ) := hc
        _ = ∑ x ∈ S.erase d,
            (if (S.erase x ∩ D).Nonempty then (1 : ℚ) else 0) :=
          Finset.sum_congr rfl (fun x hx => by rw [if_pos (hret x hx)])
        _ ≤ ∑ x ∈ S, (if (S.erase x ∩ D).Nonempty then (1 : ℚ) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun _ _ _ => by split_ifs <;> norm_num)
    · simp only [if_neg hh, mul_zero]
      exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have delete_average {α : Type} [DecidableEq α] (V : Finset α) (k : ℕ) (hk : k + 1 ≤ V.card)
      (f : Finset α → ℚ) :
      average V (k + 1) (fun S => (∑ x ∈ S, f (S.erase x)) / (k + 1 : ℕ)) =
        average V k f := by
    classical
    have hk₀ : k ≤ V.card := by omega
    have hC₀ : (0 : ℚ) < V.card.choose k := by exact_mod_cast Nat.choose_pos hk₀
    have hC₁ : (0 : ℚ) < V.card.choose (k + 1) := by exact_mod_cast Nat.choose_pos hk
    have hkp : (0 : ℚ) < (k + 1 : ℕ) := by positivity
    have hchoose : (V.card.choose (k + 1) : ℚ) * (k + 1 : ℕ) =
        (V.card.choose k : ℚ) * ((V.card - k : ℕ) : ℚ) := by
      exact_mod_cast Nat.choose_succ_right_eq V.card k
    unfold average
    rw [← Finset.sum_div, erase_sum_ambient, div_div]
    apply (div_eq_div_iff (mul_ne_zero hkp.ne' hC₁.ne') hC₀.ne').2
    calc
      _ = (∑ R ∈ V.powersetCard k, f R) *
          ((V.card.choose k : ℚ) * ((V.card - k : ℕ) : ℚ)) := by ring
      _ = (∑ R ∈ V.powersetCard k, f R) *
          ((V.card.choose (k + 1) : ℚ) * (k + 1 : ℕ)) := by rw [hchoose]
      _ = _ := by ring
  have hit_average_bound {α : Type} [DecidableEq α] (V D : Finset α) (k : ℕ) (hk : k + 1 ≤ V.card) :
      (k : ℚ) / (k + 1 : ℕ) *
        average V (k + 1) (fun S => if (S ∩ D).Nonempty then 1 else 0) ≤
        average V k (fun S => if (S ∩ D).Nonempty then 1 else 0) := by
    classical
    have hC : (0 : ℚ) < V.card.choose (k + 1) := by exact_mod_cast Nat.choose_pos hk
    have hkp : (0 : ℚ) < (k + 1 : ℕ) := by positivity
    have hpoint : ∀ S ∈ V.powersetCard (k + 1),
        (k : ℚ) / (k + 1 : ℕ) * (if (S ∩ D).Nonempty then 1 else 0) ≤
        (∑ x ∈ S, (if (S.erase x ∩ D).Nonempty then (1 : ℚ) else 0)) / (k + 1 : ℕ) := by
      intro S hS
      have hc := delete_hit_count k S D (Finset.mem_powersetCard.mp hS).2
      simpa only [div_mul_eq_mul_div] using div_le_div_of_nonneg_right hc hkp.le
    calc
      _ = average V (k + 1) (fun S => (k : ℚ) / (k + 1 : ℕ) *
          (if (S ∩ D).Nonempty then 1 else 0)) := by
        unfold average
        rw [← Finset.mul_sum]
        ring
      _ ≤ average V (k + 1) (fun S =>
          (∑ x ∈ S, (if (S.erase x ∩ D).Nonempty then (1 : ℚ) else 0)) / (k + 1 : ℕ)) := by
        unfold average
        exact div_le_div_of_nonneg_right (Finset.sum_le_sum hpoint) hC.le
      _ = _ := delete_average V k hk (fun S => if (S ∩ D).Nonempty then 1 else 0)
  have random_hit_average_bound {α : Type} [DecidableEq α] {Ω : Type} [Fintype Ω] (μ : Erdos7.FiniteLaw Ω)
      (V : Finset α) (D : Ω → Finset α) (k : ℕ) (hk : k + 1 ≤ V.card) :
      (k : ℚ) / (k + 1 : ℕ) *
        μ.expect (fun ω => average V (k + 1) (fun S => if (S ∩ D ω).Nonempty then 1 else 0)) ≤
        μ.expect (fun ω => average V k (fun S => if (S ∩ D ω).Nonempty then 1 else 0)) := by
    classical
    rw [← μ.expect_smul]
    exact μ.expect_mono (fun ω => hit_average_bound V (D ω) k hk)
  have avg_expect {α : Type} [DecidableEq α] {Ω : Type} [Fintype Ω] (μ : Erdos7.FiniteLaw Ω)
      (V : Finset α) (k : ℕ) (f : Finset α → Ω → ℚ) :
      average V k (fun S => μ.expect (f S)) =
        μ.expect (fun ω => average V k (fun S => f S ω)) := by
    classical
    unfold average Erdos7.FiniteLaw.expect
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    rw [← Finset.mul_sum]
    ring
  have expected_union_bound {α : Type} [DecidableEq α] [Fintype α] {Ω : Type} [Fintype Ω]
      (μ : Erdos7.FiniteLaw Ω) (H : α → Ω → Prop)
      (V : Finset α) (k : ℕ) (hk : k + 1 ≤ V.card) :
      (k : ℚ) * average V (k + 1) (fun S => μ.prob (fun ω => ∃ j ∈ S, H j ω)) ≤
        (k + 1 : ℕ) * average V k (fun S => μ.prob (fun ω => ∃ j ∈ S, H j ω)) := by
    classical
    have hkp : (0 : ℚ) < (k + 1 : ℕ) := by positivity
    have hb := random_hit_average_bound μ V
      (fun ω => Finset.univ.filter (fun j => H j ω)) k hk
    simp only [Finset.Nonempty, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and] at hb
    rw [← avg_expect μ V (k + 1), ← avg_expect μ V k] at hb
    change (k : ℚ) / (k + 1 : ℕ) *
        average V (k + 1) (fun S => μ.prob (fun ω => ∃ j ∈ S, H j ω)) ≤
        average V k (fun S => μ.prob (fun ω => ∃ j ∈ S, H j ω)) at hb
    calc
      _ = (k + 1 : ℕ) * ((k : ℚ) / (k + 1 : ℕ) *
          average V (k + 1) (fun S => μ.prob (fun ω => ∃ j ∈ S, H j ω))) := by
        field_simp [hkp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hb hkp.le
  have hproduct {α Ω : Type} [Fintype α] [DecidableEq α] [Fintype Ω]
      (μ : α → FiniteLaw Ω) (S : Finset α) (i : α) (hi : i ∉ S)
      (A : Ω → Prop) (H : α → Ω → Prop)
      [DecidablePred A] [∀ j, DecidablePred (H j)] :
      (piLaw μ).prob (fun x ↦ A (x i) ∧ ∃ j ∈ S, H j (x j)) =
        (μ i).prob A * (piLaw μ).prob (fun x ↦ ∃ j ∈ S, H j (x j)) ∧
      (piLaw μ).prob (fun x ↦ A (x i)) = (μ i).prob A ∧
      (piLaw μ).prob (fun x ↦ ∃ j ∈ insert i S, H j (x j)) =
        (piLaw μ).prob (fun x ↦ ∃ j ∈ S, H j (x j)) +
          (1 - (piLaw μ).prob (fun x ↦ ∃ j ∈ S, H j (x j))) * (μ i).prob (H i) ∧
      (piLaw μ).prob (fun x ↦ A (x i) ∧ ∃ j ∈ insert i S, H j (x j)) =
        (μ i).prob A * (piLaw μ).prob (fun x ↦ ∃ j ∈ S, H j (x j)) +
          (1 - (piLaw μ).prob (fun x ↦ ∃ j ∈ S, H j (x j))) *
            (μ i).prob (fun y ↦ A y ∧ H i y) := by
    classical
    have hcoord (C : α → Ω → Prop)
        (dc : ∀ j, DecidablePred (C j))
        (dall : DecidablePred (fun x : α → Ω ↦ ∀ j, C j (x j))) :
        @FiniteLaw.prob (α → Ω) _ (piLaw μ) (fun x ↦ ∀ j, C j (x j)) dall =
          ∏ j, @FiniteLaw.prob Ω _ (μ j) (C j) (dc j) := by
      let B : α → Ω → Bool := fun j y ↦ @decide (C j y) (dc j y)
      calc
        _ = (piLaw μ).prob (fun x ↦ ∀ j, B j (x j) = true) := by
          apply prob_congr
          intro x
          simp only [B, decide_eq_true_eq]
        _ = ∏ j, (μ j).prob (fun y ↦ B j y = true) :=
          piLaw_prob_forall_bool_with_decider μ B _
        _ = _ := by
          apply Finset.prod_congr rfl
          intro j _
          apply prob_congr
          intro y
          simp only [B, decide_eq_true_eq]
    have hsub {X : Type} [Fintype X] (ν : FiniteLaw X) (P Q : X → Prop)
        [DecidablePred P] [DecidablePred Q] :
        ν.prob (fun x ↦ P x ∧ Q x) =
          ν.prob P - ν.prob (fun x ↦ P x ∧ ¬Q x) := by
      unfold prob
      rw [← expect_sub]
      apply ν.expect_congr
      intro x
      by_cases hp : P x <;> by_cases hq : Q x <;> simp [hp, hq]
    have hnot {X : Type} [Fintype X] (ν : FiniteLaw X) (P : X → Prop)
        [DecidablePred P] :
        ν.prob (fun x ↦ ¬P x) = 1 - ν.prob P := by
      have hn := ν.prob_add_not P
      simp only [hprobD] at hn ⊢
      linarith only [hn]
    have hnone :
        (piLaw μ).prob (fun x ↦ ¬ ∃ j ∈ S, H j (x j)) =
          ∏ j ∈ S, (μ j).prob (fun y ↦ ¬H j y) := by
      calc
        _ = (piLaw μ).prob (fun x ↦ ∀ j, j ∈ S → ¬H j (x j)) := by
          apply prob_congr
          intro x
          simp
        _ = ∏ j, (μ j).prob (fun y ↦ j ∈ S → ¬H j y) := hcoord (fun j y ↦ j ∈ S → ¬H j y) _ _
        _ = ∏ j, if j ∈ S then (μ j).prob (fun y ↦ ¬H j y) else 1 := by
          apply Finset.prod_congr rfl
          intro j _
          by_cases hj : j ∈ S
          · rw [if_pos hj]
            apply prob_congr
            intro y
            simp only [hj, true_implies]
          · rw [if_neg hj]
            calc
              _ = (μ j).prob (fun _ ↦ True) := by
                apply prob_congr
                intro y
                simp only [hj, false_implies]
              _ = 1 := prob_true _
        _ = _ := Finset.prod_ite_mem_eq S _
    have hjoint (P : Ω → Prop) [DecidablePred P] :
        (piLaw μ).prob (fun x ↦ P (x i) ∧ ¬ ∃ j ∈ S, H j (x j)) =
          (μ i).prob P * ∏ j ∈ S, (μ j).prob (fun y ↦ ¬H j y) := by
      calc
        _ = (piLaw μ).prob
            (fun x ↦ ∀ j, (j = i → P (x j)) ∧ (j ∈ S → ¬H j (x j))) := by
          apply prob_congr
          intro x
          constructor
          · rintro ⟨ha, hh⟩ j
            exact ⟨fun hji ↦ by simpa only [hji] using ha,
              fun hj hhj ↦ hh ⟨j, hj, hhj⟩⟩
          · intro h
            refine ⟨(h i).1 rfl, ?_⟩
            rintro ⟨j, hj, hhj⟩
            exact (h j).2 hj hhj
        _ = ∏ j, (μ j).prob
            (fun y ↦ (j = i → P y) ∧ (j ∈ S → ¬H j y)) := hcoord (fun j y ↦ (j = i → P y) ∧ (j ∈ S → ¬H j y)) _ _
        _ = ∏ j, (if j = i then (μ i).prob P else 1) *
            (if j ∈ S then (μ j).prob (fun y ↦ ¬H j y) else 1) := by
          apply Finset.prod_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            rw [if_pos rfl, if_neg hi, mul_one]
            apply prob_congr
            intro y
            simp only [true_implies, hi, false_implies, and_true]
          · rw [if_neg hji]
            by_cases hj : j ∈ S
            · rw [if_pos hj, one_mul]
              apply prob_congr
              intro y
              simp only [hji, false_implies, hj, true_implies, true_and]
            · rw [if_neg hj, one_mul]
              calc
                _ = (μ j).prob (fun _ ↦ True) := by
                  apply prob_congr
                  intro y
                  simp only [hji, hj, false_implies, and_self]
                _ = 1 := prob_true _
        _ = _ := by
          rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Finset.prod_ite_mem_eq]
    have hmarginal (P : Ω → Prop) [DecidablePred P] : (piLaw μ).prob (fun x ↦ P (x i)) = (μ i).prob P := by
      simpa only [hprobD] using FiniteLaw.piLaw_prob_coordinate μ i P
    have hind :
        (piLaw μ).prob (fun x ↦ A (x i) ∧ ∃ j ∈ S, H j (x j)) =
          (μ i).prob A * (piLaw μ).prob (fun x ↦ ∃ j ∈ S, H j (x j)) := by
      rw [hsub (piLaw μ) (fun x ↦ A (x i)), hmarginal, hjoint,
        ← hnone, hnot]
      ring
    refine ⟨hind, hmarginal A, ?_, ?_⟩
    · have hc :
          (piLaw μ).prob (fun x ↦ ¬ ∃ j ∈ insert i S, H j (x j)) =
            (piLaw μ).prob (fun x ↦ ¬H i (x i) ∧ ¬ ∃ j ∈ S, H j (x j)) := by
        apply prob_congr
        intro x
        simp
      rw [hjoint (fun y ↦ ¬H i y), ← hnone, hnot, hnot] at hc
      rw [hnot] at hc
      linear_combination -hc
    · have hc :
          (piLaw μ).prob (fun x ↦ A (x i) ∧ ¬ ∃ j ∈ insert i S, H j (x j)) =
            (piLaw μ).prob (fun x ↦ (A (x i) ∧ ¬H i (x i)) ∧
              ¬ ∃ j ∈ S, H j (x j)) := by
        apply prob_congr
        intro x
        simp [and_assoc]
      rw [hjoint (fun y ↦ A y ∧ ¬H i y), ← hnone, hnot] at hc
      rw [hsub (piLaw μ) (fun x ↦ A (x i)), hmarginal A, hc,
        hsub (μ i) A (H i)]
      ring
  have hrQ : (1 : ℚ) < r := by exact_mod_cast (show 1 < r by omega)
  have hrsQ : (r : ℚ) < s := by exact_mod_cast hrs
  have hleaf : ∀ B (θ : Tree s r B), ∃ v, selected B θ v := by
    intro B
    induction B with
    | zero =>
      intro θ
      exact ⟨Fin.elim0, trivial⟩
    | succ B ih =>
      intro θ
      obtain ⟨a, ha⟩ := Finset.card_pos.mp
        (show 0 < θ.1.val.card by simpa only [θ.1.property] using (show 0 < r by omega))
      obtain ⟨v, hv⟩ := ih (θ.2 a)
      exact ⟨Fin.cons a v, by simpa only [selected, Fin.cons_zero, Fin.tail_cons] using And.intro ha hv⟩
  have hempty (B : ℕ) (w : Word s 0) (h0 : 0 ≤ B) (F : Word s B → Prop) :
      (s : ℚ) * (r - 1) * (law hrs.le B).prob (fun θ => Hit θ (fun v => HasPrefix v w h0)) *
        (law hrs.le B).prob (fun θ => Hit θ F) ≤
      (r : ℚ) * (s - 1) * (law hrs.le B).prob
        (fun θ => Hit θ (fun v => HasPrefix v w h0) ∧ Hit θ F) := by
    have hA (θ : Tree s r B) : Hit θ (fun v => HasPrefix v w h0) := by
      obtain ⟨v, hv⟩ := hleaf B θ
      exact ⟨v, by intro j; exact Fin.elim0 j, hv⟩
    have hAp : (law hrs.le B).prob (fun θ => Hit θ (fun v => HasPrefix v w h0)) = 1 := by
      calc
        _ = (law hrs.le B).prob (fun _ => True) := by
          apply (law hrs.le B).prob_congr
          intro θ
          exact iff_true_intro (hA θ)
        _ = 1 := (law hrs.le B).prob_true
    have hAH : (law hrs.le B).prob (fun θ => Hit θ (fun v => HasPrefix v w h0) ∧ Hit θ F) =
        (law hrs.le B).prob (fun θ => Hit θ F) := by
      apply (law hrs.le B).prob_congr
      intro θ
      exact and_iff_right (hA θ)
    rw [hAp, hAH]
    have hq := (law hrs.le B).prob_nonneg (fun θ => Hit θ F)
    have hprod := mul_nonneg (sub_nonneg.mpr hrsQ.le) hq
    nlinarith
  induction B generalizing d with
  | zero =>
    have hd0 : d = 0 := by omega
    subst d
    exact hempty 0 w hd F
  | succ B ih =>
    cases d with
    | zero => exact hempty (B+1) w hd F
    | succ d =>
      let μ := law hrs.le B
      let π := FiniteLaw.piLaw (fun _ : Fin s => μ)
      let i := w 0
      let A : Tree s r B → Prop := fun θ => Hit θ (fun v => HasPrefix v (Fin.tail w) (Nat.le_of_succ_le_succ hd))
      let H : Fin s → Tree s r B → Prop := fun j θ => Hit θ (fun v => F (Fin.cons j v))
      let U : Finset (Fin s) → ℚ := fun S => π.prob (fun x => ∃ j ∈ S, H j (x j))
      let R : Finset (Fin s) := Finset.univ.erase i
      let u := average R (r-1) U
      let v := average R r U
      let a := μ.prob A
      let q := μ.prob (H i)
      let z := μ.prob (fun θ => A θ ∧ H i θ)
      have hchild : (s : ℚ)*(r-1)*a*q ≤ (r : ℚ)*(s-1)*z :=
        ih d (Nat.le_of_succ_le_succ hd) (Fin.tail w) (fun v => F (Fin.cons i v))
      have hRcard : R.card = s-1 := by simp [R]
      have hiR : i ∉ R := Finset.notMem_erase _ _
      have hRr : r ≤ R.card := by rw [hRcard]; omega
      have hRr' : r-1 ≤ R.card := by omega
      have hR : insert i R = Finset.univ := by simp [R]
      have hrpred : r-1+1 = r := by omega
      -- All product-law and root-average identities are established from the actual laws here.
      have hRsum : R.card+1 = s := by rw [hRcard]; omega
      have hnmem (k : ℕ) (S : Finset (Fin s)) (hS : S ∈ R.powersetCard k) : i ∉ S := by
        intro hi
        exact hiR ((Finset.mem_powersetCard.mp hS).1 hi)
      have hrootsplit (g : Finset (Fin s) → ℚ) :
          average Finset.univ r g = (r : ℚ)/s * average R (r-1) (fun S => g (insert i S)) +
            (1-(r : ℚ)/s) * average R r g := by
        simpa only [hrpred, hRsum, hR] using hsplit R i hiR (r-1) (by omega) g
      have hprod (S : Finset (Fin s)) (hiS : i ∉ S) :=
        hproduct (fun _ : Fin s => μ) S i hiS A H
      have hUinsert : average R (r-1) (fun S => U (insert i S)) = u+(1-u)*q := by
        calc
          _ = average R (r-1) (fun S => q+(1-q)*U S) := by
            apply havgCongr
            intro S hS
            have hp := (hprod S (hnmem _ S hS)).2.2.1
            change U (insert i S) = q + (1-q)*U S
            have hp' : U (insert i S) = U S + (1-U S)*q := by
              simpa only [U, q, π, hprobD] using hp
            rw [hp']
            ring
          _ = q+(1-q)*u := havgAffine R (r-1) hRr' U q (1-q)
          _ = _ := by ring
      have hrootHit (θ : Tree s r (B+1)) :
          Hit θ F ↔ ∃ j ∈ θ.1.val, H j (θ.2 j) := by
        dsimp [H]
        simp only [Hit, selected, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.tail_cons]
        aesop
      have hHroot : (law hrs.le (B+1)).prob (fun θ => Hit θ F) =
          (r : ℚ)/s*(u+(1-u)*q)+(1-(r : ℚ)/s)*v := by
        calc
          _ = (FiniteLaw.uniform (Choice s r)).expect (fun S => U S.val) := by
            rw [hrootJoint hrs.le B]
            apply FiniteLaw.expect_congr
            intro S
            apply FiniteLaw.prob_congr
            intro x
            exact hrootHit (S,x)
          _ = average Finset.univ r U := huniform r U
          _ = _ := by rw [hrootsplit, hUinsert]
      have hpref (a' : Fin s) (v' : Word s B) :
          HasPrefix (Fin.cons a' v') w hd ↔
            a' = i ∧ HasPrefix v' (Fin.tail w) (Nat.le_of_succ_le_succ hd) := by
        constructor
        · intro h
          exact ⟨h 0, fun j => h j.succ⟩
        · rintro ⟨ha', hv'⟩ j
          exact Fin.cases ha' (fun k => hv' k) j
      have hprefix (θ : Tree s r (B+1)) :
          Hit θ (fun v => HasPrefix v w hd) ↔ i ∈ θ.1.val ∧ A (θ.2 i) := by
        simp only [Hit, selected, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.tail_cons]
        simp_rw [hpref]
        dsimp [A, Hit]
        aesop
      let UA : Finset (Fin s) → ℚ := fun S => π.prob (fun x => i ∈ S ∧ A (x i))
      have hUAin : average R (r-1) (fun S => UA (insert i S)) = a := by
        calc
          _ = average R (r-1) (fun _ => a) := by
            apply havgCongr
            intro S hS
            dsimp [UA]
            simp only [Finset.mem_insert_self, true_and]
            exact (hprod S (hnmem _ S hS)).2.1
          _ = a := havgConst R (r-1) hRr' a
      have hUAout : average R r UA = 0 := by
        calc
          _ = average R r (fun _ => 0) := by
            apply havgCongr
            intro S hS
            simp [UA, hnmem _ S hS]
          _ = 0 := havgConst R r hRr 0
      have hAroot : (law hrs.le (B+1)).prob (fun θ => Hit θ (fun v => HasPrefix v w hd)) =
          (r : ℚ)/s*a := by
        calc
          _ = (FiniteLaw.uniform (Choice s r)).expect (fun S => UA S.val) := by
            rw [hrootJoint hrs.le B]
            apply FiniteLaw.expect_congr
            intro S
            apply FiniteLaw.prob_congr
            intro x
            exact hprefix (S,x)
          _ = average Finset.univ r UA := huniform r UA
          _ = _ := by rw [hrootsplit, hUAin, hUAout]; ring
      let UAH : Finset (Fin s) → ℚ := fun S => π.prob
        (fun x => (i ∈ S ∧ A (x i)) ∧ ∃ j ∈ S, H j (x j))
      have hUAHin : average R (r-1) (fun S => UAH (insert i S)) = a*u+(1-u)*z := by
        calc
          _ = average R (r-1) (fun S => z+(a-z)*U S) := by
            apply havgCongr
            intro S hS
            have hp := (hprod S (hnmem _ S hS)).2.2.2
            dsimp [UAH]
            simp only [Finset.mem_insert_self, true_and]
            change π.prob (fun x => A (x i) ∧ ∃ j ∈ insert i S, H j (x j)) = z+(a-z)*U S
            have hp' : π.prob (fun x => A (x i) ∧ ∃ j ∈ insert i S, H j (x j)) =
                a*U S+(1-U S)*z := by
              simpa only [a, z, U, π, hprobD] using hp
            rw [hp']
            ring
          _ = z+(a-z)*u := havgAffine R (r-1) hRr' U z (a-z)
          _ = _ := by ring
      have hUAHout : average R r UAH = 0 := by
        calc
          _ = average R r (fun _ => 0) := by
            apply havgCongr
            intro S hS
            simp [UAH, hnmem _ S hS]
          _ = 0 := havgConst R r hRr 0
      have hAHroot : (law hrs.le (B+1)).prob
          (fun θ => Hit θ (fun v => HasPrefix v w hd) ∧ Hit θ F) =
          (r : ℚ)/s*(a*u+(1-u)*z) := by
        calc
          _ = (FiniteLaw.uniform (Choice s r)).expect (fun S => UAH S.val) := by
            rw [hrootJoint hrs.le B]
            apply FiniteLaw.expect_congr
            intro S
            dsimp only [UAH]
            simp only [hprobD]
            refine @FiniteLaw.prob_congr (Fin s → Tree s r B) _ π
              (fun x => Hit (s := s) (r := r) (B := B+1) (S,x) (fun v => HasPrefix v w hd) ∧
                Hit (s := s) (r := r) (B := B+1) (S,x) F)
              (fun x => (i ∈ S.val ∧ A (x i)) ∧ ∃ j ∈ S.val, H j (x j))
              (Classical.decPred _) (Classical.decPred _) ?_
            intro x
            exact and_congr (hprefix (S,x)) (hrootHit (S,x))
          _ = average Finset.univ r UAH := huniform r UAH
          _ = _ := by rw [hrootsplit, hUAHin, hUAHout]; ring
      have hu : 0 ≤ u ∧ u ≤ 1 := havgBound R (r-1) hRr' U (fun S _ =>
        ⟨π.prob_nonneg _, π.prob_le_one _⟩)
      have hdel : ((r : ℚ)-1)*v ≤ r*u := by
        have ht := expected_union_bound π (fun j x => H j (x j)) R (r-1) (by omega)
        simpa only [u, v, U, π, hprobD, hrpred,
          Nat.cast_sub (show 1 ≤ r by omega), Nat.cast_one] using ht
      rw [hAroot, hHroot, hAHroot]
      exact halgebra r s hrQ hrsQ a q z u v (μ.prob_nonneg A) (μ.prob_nonneg (H i)) hu.1 hu.2 hdel hchild

end Erdos7.CommonTreeUnion
