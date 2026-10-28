/- GID: D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphySurgery
   generality: I
   mirror-B: D5/B/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphySurgery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Partition.Finpartition]
   utility: none
   digest: Native matching surgery and exact ordered join counts. -/

import D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyComponents

/-! Surgery on the original complete matching domain. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow

open Equiv
open D5.S0.Certificates.Combinatorics.DeformedJucysMurphyNoncommutation
open D5.S3.Combinatorics.PerfectMatchings.InvolutionOrbitSplit
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyWalk
open D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyCharge
open scoped BigOperators

attribute [local instance] Classical.propDecidable

private theorem component_swap {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hab : Component p a b) (x : Fin (2 * k)) :
    Component p x (Equiv.swap a b x) := by
  by_cases hxa : x = a
  · subst x
    simpa only [Equiv.swap_apply_left] using hab
  · by_cases hxb : x = b
    · subst x
      simpa only [Equiv.swap_apply_right] using component_symm p hab
    · rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
      exact .refl

private theorem component_act_le {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hab : Component p a b) {x y : Fin (2 * k)}
    (hxy : Component (act a b p) x y) : Component p x y := by
  induction hxy with
  | refl => exact .refl
  | @tail u v h huv ih =>
    apply ih.trans
    rcases huv with hp | he
    · change Equiv.swap a b (p.val (Equiv.swap a b u)) = v at hp
      rw [← hp]
      exact (component_swap p hab u).trans
        ((show Component p (Equiv.swap a b u) (p.val (Equiv.swap a b u)) from
          .single (Or.inl rfl)).trans
          (component_swap p hab (p.val (Equiv.swap a b u))))
    · exact .single (Or.inr he)

theorem act_involutive {k : ℕ} (p : P k) (a b : Fin (2 * k)) :
    act a b (act a b p) = p := by
  apply Subtype.ext
  funext x
  simp only [act, Equiv.swap_apply_self]

private theorem component_act_iff {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hab : Component p a b) (hnew : Component (act a b p) a b)
    (x y : Fin (2 * k)) :
    Component (act a b p) x y ↔ Component p x y := by
  constructor
  · exact component_act_le p hab
  · intro h
    apply component_act_le (act a b p) hnew
    simpa only [act_involutive] using h

private theorem matching_inverse {k : ℕ} (p : P k) :
    (matchingPerm p)⁻¹ = matchingPerm p := by
  apply Equiv.ext
  intro x
  apply (matchingPerm p).injective
  exact ((matchingPerm p).apply_symm_apply x).trans (p.property.1 x).symm

private theorem reverse_rotation {k : ℕ} (p : P k) (x y : Fin (2 * k)) :
    (matchingPerm (e k) * matchingPerm p).SameCycle x y ↔
      (matchingPerm p * matchingPerm (e k)).SameCycle x y := by
  have hi : matchingPerm (e k) * matchingPerm p =
      (matchingPerm p * matchingPerm (e k))⁻¹ := by
    rw [mul_inv_rev, matching_inverse, matching_inverse]
  rw [hi, Perm.sameCycle_inv]

private theorem boundary_injective {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hab : a ≠ b) (hpartner : p.val a ≠ b) :
    Function.Injective
      (D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.OriginalCut.boundaryLabel
        (matchingPerm p) (p.val a) (p.val b)) := by
  have hpa := p.property.2 a
  have hpb := p.property.2 b
  have hpab : p.val a ≠ p.val b := p.property.1.injective.ne hab
  have hpba : p.val b ≠ a := by
    intro h
    apply hpartner
    have hh := congrArg p.val h
    exact (p.property.1 b).symm.trans hh |>.symm
  intro i j hij
  change ![p.val a, p.val b, p.val (p.val a), p.val (p.val b)] i =
    ![p.val a, p.val b, p.val (p.val a), p.val (p.val b)] j at hij
  rw [p.property.1, p.property.1] at hij
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    simp only [Matrix.cons_val_zero, Matrix.cons_val_succ] at hij
    first
    | exact False.elim (hab hij)
    | exact False.elim (hab hij.symm)
    | exact False.elim (hpa hij)
    | exact False.elim (hpa hij.symm)
    | exact False.elim (hpb hij)
    | exact False.elim (hpb hij.symm)
    | exact False.elim (hpab hij)
    | exact False.elim (hpab hij.symm)
    | exact False.elim (hpba hij)
    | exact False.elim (hpba hij.symm)
    | exact False.elim (hpartner hij)
    | exact False.elim (hpartner hij.symm)

private theorem opposite_act_connected {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hc : Component p a b) (hcharge : charge p a ≠ charge p b) :
    Component (act a b p) a b := by
  by_cases hp : p.val a = b
  · subst b
    rw [act_partner]
    exact hc
  have hab : a ≠ b := fun h => hcharge (congrArg (charge p) h)
  have hbad : (matchingPerm p * matchingPerm (e k)).SameCycle (p.val a) b := by
    rcases (connected_iff_rotation_orbits (matchingPerm p) (matchingPerm (e k))
      p.property.1 (e k).property.1 a b).mp hc with h | h
    · exact False.elim (hcharge (charge_of_sameCycle p h))
    · exact h
  have hold : (matchingPerm (e k) * matchingPerm p).SameCycle
      ((e k).val (p.val a)) (p.val b) := by
    apply (reverse_rotation p _ _).mpr
    have hstep : (matchingPerm p * matchingPerm (e k)).SameCycle
        ((e k).val (p.val a)) a := by
      have h := (Perm.SameCycle.refl (matchingPerm p * matchingPerm (e k))
        ((e k).val (p.val a))).apply_right
      change (matchingPerm p * matchingPerm (e k)).SameCycle
        ((e k).val (p.val a)) (p.val ((e k).val ((e k).val (p.val a)))) at h
      rwa [(e k).property.1, p.property.1] at h
    exact hstep.trans (by
      have hconn : Component p a (p.val b) := hc.tail (Or.inl rfl)
      apply (same_charge_iff p hconn).mp
      rw [charge_partner]
      cases ha : charge p a <;> cases hb : charge p b <;> simp_all)
  have hs := D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.band_switch
    (matchingPerm (e k)) (matchingPerm p) (e k).property.1 p.property.1
    (e k).property.2 p.property.2 (p.val a) (p.val b) (boundary_injective p hab hp)
  have hswap :
      D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.OriginalCut.switchSwap
        (matchingPerm p) (p.val a) (p.val b) = Equiv.swap a b := by
    unfold D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.OriginalCut.switchSwap
    have ha : matchingPerm p (p.val a) = a := p.property.1 a
    have hb : matchingPerm p (p.val b) = b := p.property.1 b
    ext x
    simp only [Equiv.swap_apply_def, ha, hb]
    split_ifs <;> rfl
  have hact : Equiv.swap a b * matchingPerm p * Equiv.swap a b =
      matchingPerm (act a b p) := by rfl
  have hh := hs.2.1.mpr hold
  rw [hswap, hact] at hh
  change (matchingPerm (e k) * matchingPerm (act a b p)).SameCycle
    ((e k).val (p.val a)) (p.val b) at hh
  have hconn : Component (act a b p) ((e k).val (p.val a)) (p.val b) :=
    rotation_connected (act a b p) ((reverse_rotation (act a b p) _ _).mp hh)
  have hleft : Component (act a b p) b ((e k).val (p.val a)) := by
    have hp' : (act a b p).val b = p.val a := by
      change Equiv.swap a b (p.val (Equiv.swap a b b)) = p.val a
      rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (p.property.2 a) hp]
    exact (show Component (act a b p) b (p.val a) from
      .single (Or.inl hp')).tail (Or.inr rfl)
  have hright : Component (act a b p) a (p.val b) := by
    apply Relation.ReflTransGen.single
    left
    change Equiv.swap a b (p.val (Equiv.swap a b a)) = p.val b
    rw [Equiv.swap_apply_left]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      apply hp
      have hh := congrArg p.val h
      exact ((p.property.1 b).symm.trans hh).symm
    · exact p.property.2 b
  exact hright.trans (component_symm _ (hleft.trans hconn))

private theorem ct_opposite_act {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hc : Component p a b) (hcharge : charge p a ≠ charge p b) :
    ct (act a b p) = ct p := by
  have hnew := opposite_act_connected p hc hcharge
  have he : edgeSetoid (act a b p) = edgeSetoid p := by
    apply Setoid.ext
    intro h i
    exact component_act_iff p hc hnew _ _
  apply Nat.Partition.ext
  change (Finpartition.ofSetoid (edgeSetoid (act a b p))).parts.val.map Finset.card =
    (Finpartition.ofSetoid (edgeSetoid p)).parts.val.map Finset.card
  rw [he]

theorem two_triangular_sum {K : Type*} [CommRing K] (k : ℕ)
    (g : Fin k → Fin k → K) (hs : ∀ i j, g i j = g j i)
    (hd : ∀ i, g i i = 0) :
    2 * (∑ q : Fin k, ∑ h : Fin q.val,
      g q ⟨h.val, by omega⟩) = ∑ i : Fin k, ∑ j : Fin k, g i j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ht : (∑ q : Fin (k + 1), ∑ h : Fin q.val, g q ⟨h.val, by omega⟩) =
        (∑ q : Fin k, ∑ h : Fin q.val, g q.castSucc ⟨h.val, by omega⟩) +
          ∑ h : Fin k, g (Fin.last k) h.castSucc := by
      rw [Fin.sum_univ_castSucc]
      congr 1
    have hf : (∑ i : Fin (k + 1), ∑ j : Fin (k + 1), g i j) =
        (∑ i : Fin k, ∑ j : Fin k, g i.castSucc j.castSucc) +
        (∑ i : Fin k, g i.castSucc (Fin.last k)) +
        ∑ j : Fin k, g (Fin.last k) j.castSucc := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.sum_univ_castSucc, Finset.sum_add_distrib, hd, add_zero]
    have hc : (∑ i : Fin k, g i.castSucc (Fin.last k)) =
        ∑ i : Fin k, g (Fin.last k) i.castSucc :=
      Finset.sum_congr rfl (fun i _ => hs _ _)
    have hi := ih (fun i j => g i.castSucc j.castSucc)
      (fun i j => hs _ _) (fun i => hd _)
    change 2 * (∑ q : Fin k, ∑ h : Fin q.val,
      g q.castSucc ⟨h.val, by omega⟩) =
      ∑ i : Fin k, ∑ j : Fin k, g i.castSucc j.castSucc at hi
    rw [ht, hf, hc]
    linear_combination hi

theorem component_sum {K : Type*} [CommSemiring K] {k : ℕ}
    (p : P k) (f : Finset (Fin k) → K) :
    (∑ i : Fin k, f ((edgeComponents p).part i)) =
      ∑ C ∈ (edgeComponents p).parts, (C.card : K) * f C := by
  let Q := edgeComponents p
  calc
    _ = ∑ i : (Finset.univ : Finset (Fin k)), f (Q.part i.val) := by simp [Q]
    _ = ∑ C : Q.parts, ∑ i : C.val, f (Q.part i.val) := by
      calc
        _ = ∑ c : (Σ C : Q.parts, C.val), f (Q.part c.2.val) :=
          Q.equivSigmaParts.sum_comp (fun c => f (Q.part c.2.val))
        _ = _ := Fintype.sum_sigma _
    _ = ∑ C : Q.parts, (C.val.card : K) * f C.val := by
      apply Finset.sum_congr rfl
      intro C _
      have he : ∀ i : C.val, Q.part i.val = C.val := fun i =>
        Q.part_eq_of_mem C.property i.property
      simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
    _ = _ := Finset.sum_coe_sort Q.parts (fun C => (C.card : K) * f C)

private theorem component_pair_sum {K : Type*} [CommSemiring K] {k : ℕ}
    (p : P k) (f : Finset (Fin k) → Finset (Fin k) → K) :
    (∑ i : Fin k, ∑ j : Fin k,
      f ((edgeComponents p).part i) ((edgeComponents p).part j)) =
      ∑ C ∈ (edgeComponents p).parts, ∑ D ∈ (edgeComponents p).parts,
        (C.card : K) * (D.card : K) * f C D := by
  rw [component_sum p (fun C => ∑ j : Fin k, f C ((edgeComponents p).part j))]
  apply Finset.sum_congr rfl
  intro C _
  rw [component_sum p (f C), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  exact (mul_assoc _ _ _).symm

private theorem internal_pair_count {K : Type*} [Field K] [CharZero K]
    {k : ℕ} (p : P k) :
    (∑ q : Fin k, ∑ h : Fin q.val,
      if Component p (edgeVertex q) (earlierVertex q h 0) then (1 : K) else 0) =
      ((ct p).parts.map fun r => (Nat.choose r 2 : K)).sum := by
  let Q := edgeComponents p
  let g : Fin k → Fin k → K := fun i j =>
    if i ≠ j ∧ (edgeSetoid p).r i j then 1 else 0
  have hs : ∀ i j, g i j = g j i := by
    intro i j
    simp only [g]
    congr 1
    exact propext (and_congr ne_comm ⟨(edgeSetoid p).symm, (edgeSetoid p).symm⟩)
  have hd : ∀ i, g i i = 0 := by intro i; simp [g]
  have hg : ∀ i, (∑ j, g i j) = ((Q.part i).card - 1 : ℕ) := by
    intro i
    have he : (Finset.univ.filter fun j => i ≠ j ∧ (edgeSetoid p).r i j) =
        (Q.part i).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      rw [show j ∈ Q.part i ↔ (edgeSetoid p).r i j from edge_component_membership p i j]
      exact and_congr ne_comm Iff.rfl
    rw [show (∑ j, g i j) = ∑ j ∈ Finset.univ.filter
      (fun j => i ≠ j ∧ (edgeSetoid p).r i j), (1 : K) from
        (Finset.sum_filter _ _).symm, he]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_erase_of_mem (Q.mem_part (Finset.mem_univ i))]
  have hparts : (∑ i : Fin k, (((Q.part i).card - 1 : ℕ) : K)) =
      ∑ C ∈ Q.parts, (C.card : K) * (((C.card - 1 : ℕ) : K)) := by
    exact component_sum p (fun C => (((C.card - 1 : ℕ) : K)))
  have hp : ∀ C ∈ Q.parts, (C.card : K) * (((C.card - 1 : ℕ) : K)) =
      2 * (Nat.choose C.card 2 : K) := by
    intro C hC
    have hpos : 1 ≤ C.card := Finset.card_pos.mpr (Q.nonempty_of_mem_parts hC)
    rw [Nat.cast_sub hpos, Nat.cast_one, Nat.cast_choose_two]
    ring
  have ht := two_triangular_sum k g hs hd
  have htri : (∑ q : Fin k, ∑ h : Fin q.val, g q ⟨h.val, by omega⟩) =
      ∑ q : Fin k, ∑ h : Fin q.val,
        if Component p (edgeVertex q) (earlierVertex q h 0) then (1 : K) else 0 := by
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro h _
    have hne : q ≠ (⟨h.val, by omega⟩ : Fin k) := by
      intro he
      exact (Nat.ne_of_gt h.isLt) (congrArg Fin.val he)
    have hv : edgeVertex (⟨h.val, by omega⟩ : Fin k) = earlierVertex q h 0 := by
      apply Fin.ext
      simp only [edgeVertex, earlierVertex, Fin.val_zero, zero_add]
    change (if q ≠ (⟨h.val, by omega⟩ : Fin k) ∧
      Component p (edgeVertex q) (edgeVertex ⟨h.val, by omega⟩) then (1 : K) else 0) = _
    rw [hv]
    split_ifs <;> simp_all
  rw [htri] at ht
  simp_rw [hg] at ht
  rw [hparts] at ht
  have htwice : (∑ C ∈ Q.parts, (C.card : K) * (((C.card - 1 : ℕ) : K))) =
      2 * ∑ C ∈ Q.parts, (Nat.choose C.card 2 : K) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hp
  rw [htwice] at ht
  apply (mul_left_cancel₀ (two_ne_zero : (2 : K) ≠ 0))
  convert ht using 1
  simp only [ct, Q, Multiset.map_map, Function.comp_def, ← Finset.sum_eq_multiset_sum]

private theorem opposite_internal_indicator {k : ℕ} (lam : Nat.Partition k) (p : P k)
    (q : Fin k) (h : Fin q.val)
    (hc : Component p (edgeVertex q) (earlierVertex q h 0)) :
    indicator lam (act (oppositeChargeVertex p q h) (edgeVertex q) p) =
      (indicator lam p : RatFunc ℂ) := by
  have hc1 : Component p (edgeVertex q) (earlierVertex q h 1) := by
    rw [← earlier_identity_partner]
    exact hc.tail (Or.inr rfl)
  have ho : Component p (edgeVertex q) (oppositeChargeVertex p q h) := by
    unfold oppositeChargeVertex
    split <;> assumption
  have hcharge : charge p (oppositeChargeVertex p q h) ≠ charge p (edgeVertex q) := by
    rw [(selected_charges p q h).2]
    cases charge p (edgeVertex q) <;> decide
  unfold indicator
  rw [ct_opposite_act p (component_symm p ho) hcharge]

private theorem native_internal_row (b : RatFunc ℂ) {k : ℕ}
    (lam : Nat.Partition k) (p : P k) :
    S b k (indicator lam) p =
      (∑ q : Fin k, ∑ h : Fin q.val,
        (indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) +
          b * (if Component p (edgeVertex q) (earlierVertex q h 0) then 0 else
            indicator lam (act (oppositeChargeVertex p q h) (edgeVertex q) p)))) +
      b * ((ct p).parts.map fun r => (Nat.choose r 2 : RatFunc ℂ)).sum *
        indicator lam p := by
  rw [native_pair_expansion]
  have hterm (q : Fin k) (h : Fin q.val) :
      indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) +
        b * indicator lam (act (oppositeChargeVertex p q h) (edgeVertex q) p) =
      (indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) +
        b * (if Component p (edgeVertex q) (earlierVertex q h 0) then 0 else
          indicator lam (act (oppositeChargeVertex p q h) (edgeVertex q) p))) +
        (if Component p (edgeVertex q) (earlierVertex q h 0) then
          b * indicator lam p else 0) := by
    by_cases hc : Component p (edgeVertex q) (earlierVertex q h 0)
    · rw [if_pos hc, if_pos hc, opposite_internal_indicator lam p q h hc]
      ring
    · simp only [if_neg hc, add_zero]
  simp_rw [hterm, Finset.sum_add_distrib]
  congr 1
  calc
    _ = (∑ q : Fin k, ∑ h : Fin q.val,
        if Component p (edgeVertex q) (earlierVertex q h 0) then (1 : RatFunc ℂ) else 0) *
          (b * indicator lam p) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      split <;> simp
    _ = _ := by rw [internal_pair_count]; ring

private theorem act_boundary_connected {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hp : p.val a ≠ b)
    (hc : Component (act a b p) (p.val a) (p.val b)) :
    Component (act a b p) a b := by
  have ha : Component (act a b p) a (p.val b) := by
    apply Relation.ReflTransGen.single
    left
    change Equiv.swap a b (p.val (Equiv.swap a b a)) = p.val b
    rw [Equiv.swap_apply_left]
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      apply hp
      exact ((p.property.1 b).symm.trans (congrArg p.val h)).symm
    · exact p.property.2 b
  have hb : Component (act a b p) b (p.val a) := by
    apply Relation.ReflTransGen.single
    left
    change Equiv.swap a b (p.val (Equiv.swap a b b)) = p.val a
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (p.property.2 a) hp]
  exact ha.trans ((component_symm _ hc).trans (component_symm _ hb))

private theorem separate_act_connected {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hnot : ¬ Component p a b) : Component (act a b p) a b := by
  have hab : a ≠ b := by rintro rfl; exact hnot .refl
  have hp : p.val a ≠ b := by
    intro h
    exact hnot (.single (Or.inl h))
  have hr : D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.RegularAt
      (matchingPerm (e k)) (matchingPerm p) (p.val a) (p.val b) := by
    constructor
    · intro h
      apply hnot
      have hh := rotation_connected p ((reverse_rotation p _ _).mp h)
      exact (show Component p a (p.val a) from .single (Or.inl rfl)).trans
        (hh.trans (show Component p (p.val b) b from .single (Or.inl (p.property.1 b))))
    · intro h
      apply hnot
      have hh := rotation_connected p ((reverse_rotation p _ _).mp h)
      exact (show Component p a (p.val a) from .single (Or.inl rfl)).trans
        ((show Component p (p.val a) ((e k).val (p.val a)) from
          .single (Or.inr rfl)).trans
          (hh.trans (show Component p (p.val b) b from .single (Or.inl (p.property.1 b)))))
  have hs := D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.band_switch
    (matchingPerm (e k)) (matchingPerm p) (e k).property.1 p.property.1
    (e k).property.2 p.property.2 (p.val a) (p.val b) (boundary_injective p hab hp)
  have hswap : D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.OriginalCut.switchSwap
      (matchingPerm p) (p.val a) (p.val b) = Equiv.swap a b := by
    unfold D5.S3.Combinatorics.PerfectMatchings.FiniteBandSwitch.OriginalCut.switchSwap
    have ha : matchingPerm p (p.val a) = a := p.property.1 a
    have hb : matchingPerm p (p.val b) = b := p.property.1 b
    ext x
    simp only [Equiv.swap_apply_def, ha, hb]
    split_ifs <;> rfl
  have hact : Equiv.swap a b * matchingPerm p * Equiv.swap a b =
      matchingPerm (act a b p) := by rfl
  have hh := hs.1.mpr hr
  rw [hswap, hact] at hh
  exact act_boundary_connected p hp
    (rotation_connected (act a b p) ((reverse_rotation (act a b p) _ _).mp hh))

private theorem component_act_invariant {k : ℕ} (p : P k) (a b : Fin (2 * k))
    (T : Fin (2 * k) → Prop)
    (hs : ∀ x, T x → T (Equiv.swap a b x))
    (hp : ∀ x, T x → T (p.val x))
    (he : ∀ x, T x → T ((e k).val x))
    {x y : Fin (2 * k)} (hx : T x) (hxy : Component (act a b p) x y) : T y := by
  induction hxy with
  | refl => exact hx
  | @tail u v h huv ih =>
    rcases huv with h | h
    · change Equiv.swap a b (p.val (Equiv.swap a b u)) = v at h
      rw [← h]
      exact hs _ (hp _ (hs _ ih))
    · change (e k).val u = v at h
      rw [← h]
      exact he _ ih

private theorem join_component_iff {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hnot : ¬ Component p a b) (x : Fin (2 * k)) :
    Component (act a b p) a x ↔ Component p a x ∨ Component p b x := by
  have hn := separate_act_connected p hnot
  have old_le {u v : Fin (2 * k)} (h : Component p u v) :
      Component (act a b p) u v := by
    apply component_act_le (act a b p) hn
    simpa only [act_involutive] using h
  constructor
  · intro h
    apply component_act_invariant p a b
      (fun z => Component p a z ∨ Component p b z) _ _ _ (Or.inl .refl) h
    · intro z hz
      by_cases ha : z = a
      · subst z
        rw [Equiv.swap_apply_left]
        exact Or.inr .refl
      · by_cases hb : z = b
        · subst z
          rw [Equiv.swap_apply_right]
          exact Or.inl .refl
        · rwa [Equiv.swap_apply_of_ne_of_ne ha hb]
    · intro z hz
      exact hz.imp (fun h => h.tail (Or.inl rfl)) (fun h => h.tail (Or.inl rfl))
    · intro z hz
      exact hz.imp (fun h => h.tail (Or.inr rfl)) (fun h => h.tail (Or.inr rfl))
  · rintro (h | h)
    · exact old_le h
    · exact hn.trans (old_le h)

private theorem edge_component_at {k : ℕ} (p : P k) (a : Fin (2 * k)) (h : Fin k) :
    h ∈ (edgeComponents p).part (edgeIndex a) ↔ Component p a (edgeVertex h) := by
  rw [edge_component_membership, component_iff_edge_components,
    component_iff_edge_components, edgeIndex_vertex]

private theorem join_edge_component {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hnot : ¬ Component p a b) :
    (edgeComponents (act a b p)).part (edgeIndex a) =
      (edgeComponents p).part (edgeIndex a) ∪ (edgeComponents p).part (edgeIndex b) := by
  ext h
  simp only [Finset.mem_union, edge_component_at, join_component_iff p hnot]

private theorem join_component_size {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hnot : ¬ Component p a b) :
    ((edgeComponents (act a b p)).part (edgeIndex a)).card =
      ((edgeComponents p).part (edgeIndex a)).card +
      ((edgeComponents p).part (edgeIndex b)).card := by
  rw [join_edge_component p hnot, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro h ha hb
  exact hnot (((edge_component_at p a h).mp ha).trans
    (component_symm p ((edge_component_at p b h).mp hb)))

private theorem untouched_component_iff {k : ℕ} (p : P k) {a b x : Fin (2 * k)}
    (hnot : ¬ Component p a b) (ha : ¬ Component p a x) (hb : ¬ Component p b x)
    (y : Fin (2 * k)) : Component (act a b p) x y ↔ Component p x y := by
  constructor
  · intro h
    apply component_act_invariant p a b (Component p x) _ _ _ .refl h
    · intro z hz
      have hza : z ≠ a := by
        rintro rfl
        exact ha (component_symm p hz)
      have hzb : z ≠ b := by
        rintro rfl
        exact hb (component_symm p hz)
      rwa [Equiv.swap_apply_of_ne_of_ne hza hzb]
    · intro z hz
      exact hz.tail (Or.inl rfl)
    · intro z hz
      exact hz.tail (Or.inr rfl)
  · intro h
    apply component_act_le (act a b p) (separate_act_connected p hnot)
    simpa only [act_involutive] using h

private theorem untouched_edge_component {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hnot : ¬ Component p a b) (i : Fin k)
    (ha : i ∉ (edgeComponents p).part (edgeIndex a))
    (hb : i ∉ (edgeComponents p).part (edgeIndex b)) :
    (edgeComponents (act a b p)).part i = (edgeComponents p).part i := by
  have ha' : ¬ Component p a (edgeVertex i) := fun h => ha ((edge_component_at p a i).mpr h)
  have hb' : ¬ Component p b (edgeVertex i) := fun h => hb ((edge_component_at p b i).mpr h)
  ext j
  rw [edge_component_membership, edge_component_membership]
  exact untouched_component_iff p hnot ha' hb' _

private theorem join_parts {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hnot : ¬ Component p a b) :
    (edgeComponents (act a b p)).parts =
      insert ((edgeComponents p).part (edgeIndex a) ∪ (edgeComponents p).part (edgeIndex b))
        (((edgeComponents p).parts.erase ((edgeComponents p).part (edgeIndex a))).erase
          ((edgeComponents p).part (edgeIndex b))) := by
  let Q := edgeComponents p
  let R := edgeComponents (act a b p)
  let A := Q.part (edgeIndex a)
  let B := Q.part (edgeIndex b)
  have hA : A ∈ Q.parts := Q.part_mem.mpr (Finset.mem_univ _)
  have hB : B ∈ Q.parts := Q.part_mem.mpr (Finset.mem_univ _)
  have hmerged : R.part (edgeIndex a) = A ∪ B := join_edge_component p hnot
  have hR : A ∪ B ∈ R.parts := by
    rw [← hmerged]
    exact R.part_mem.mpr (Finset.mem_univ _)
  have change_at (i : Fin k) (hi : i ∈ A ∪ B) : R.part i = A ∪ B := by
    have hm : i ∈ R.part (edgeIndex a) := by rwa [hmerged]
    exact (R.part_eq_of_mem (R.part_mem.mpr (Finset.mem_univ _)) hm).trans hmerged
  have unchanged_at (i : Fin k) (hi : i ∉ A ∪ B) : R.part i = Q.part i := by
    exact untouched_edge_component p hnot i
      (fun h => hi (Finset.mem_union_left B h)) (fun h => hi (Finset.mem_union_right A h))
  change R.parts = insert (A ∪ B) ((Q.parts.erase A).erase B)
  ext C
  constructor
  · intro hC
    obtain ⟨i, hi⟩ := R.nonempty_of_mem_parts hC
    have heq : R.part i = C := R.part_eq_of_mem hC hi
    by_cases hiu : i ∈ A ∪ B
    · exact Finset.mem_insert.mpr (Or.inl (heq.symm.trans (change_at i hiu)))
    · apply Finset.mem_insert.mpr
      right
      have old : Q.part i = C := (unchanged_at i hiu).symm.trans heq
      have hCQ : C ∈ Q.parts := old ▸ Q.part_mem.mpr (Finset.mem_univ _)
      have hCA : C ≠ A := by
        intro h
        apply hiu
        exact Finset.mem_union_left B (h ▸ (old ▸ Q.mem_part (Finset.mem_univ i)))
      have hCB : C ≠ B := by
        intro h
        apply hiu
        exact Finset.mem_union_right A (h ▸ (old ▸ Q.mem_part (Finset.mem_univ i)))
      exact Finset.mem_erase.mpr ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hCQ⟩⟩
  · intro hC
    rcases Finset.mem_insert.mp hC with hC | hC
    · exact hC ▸ hR
    · obtain ⟨hCB, hC⟩ := Finset.mem_erase.mp hC
      obtain ⟨hCA, hCQ⟩ := Finset.mem_erase.mp hC
      obtain ⟨i, hi⟩ := Q.nonempty_of_mem_parts hCQ
      have old : Q.part i = C := Q.part_eq_of_mem hCQ hi
      have hiu : i ∉ A ∪ B := by
        intro hm
        rcases Finset.mem_union.mp hm with hm | hm
        · exact hCA (old.symm.trans (Q.part_eq_of_mem hA hm))
        · exact hCB (old.symm.trans (Q.part_eq_of_mem hB hm))
      have heq : R.part i = C := (unchanged_at i hiu).trans old
      exact heq ▸ R.part_mem.mpr (Finset.mem_univ _)

theorem ct_join {k : ℕ} (p : P k) {a b : Fin (2 * k)}
    (hnot : ¬ Component p a b) :
    (ct (act a b p)).parts =
      (((ct p).parts.erase (((edgeComponents p).part (edgeIndex a)).card)).erase
        (((edgeComponents p).part (edgeIndex b)).card)) +
      {((edgeComponents p).part (edgeIndex a)).card +
        ((edgeComponents p).part (edgeIndex b)).card} := by
  let Q := edgeComponents p
  let A := Q.part (edgeIndex a)
  let B := Q.part (edgeIndex b)
  have hA : A ∈ Q.parts := Q.part_mem.mpr (Finset.mem_univ _)
  have hB : B ∈ Q.parts := Q.part_mem.mpr (Finset.mem_univ _)
  have hAB : A ≠ B := by
    intro h
    apply hnot
    apply (component_iff_edge_components p a b).mpr
    apply (edge_component_membership p (edgeIndex a) (edgeIndex b)).mp
    change edgeIndex b ∈ A
    rw [h]
    exact Q.mem_part (Finset.mem_univ _)
  have hU : A ∪ B ∉ Q.parts := by
    intro h
    have hAU : A = A ∪ B := Q.eq_of_mem_parts hA h
      (Q.mem_part (Finset.mem_univ (edgeIndex a)))
      (Finset.mem_union_left B (Q.mem_part (Finset.mem_univ (edgeIndex a))))
    have hbA : edgeIndex b ∈ A := by
      rw [hAU]
      exact Finset.mem_union_right A (Q.mem_part (Finset.mem_univ (edgeIndex b)))
    exact hAB (Q.eq_of_mem_parts hA hB hbA (Q.mem_part (Finset.mem_univ _)))
  have hU' : A ∪ B ∉ (Q.parts.erase A).erase B := fun h =>
    hU (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hB' : B ∈ Q.parts.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hcard : (A ∪ B).card = A.card + B.card := by
    have h := join_component_size p hnot
    rwa [join_edge_component p hnot] at h
  change (edgeComponents (act a b p)).parts.val.map Finset.card =
    (((Q.parts.val.map Finset.card).erase A.card).erase B.card) + {A.card + B.card}
  rw [join_parts p hnot]
  change (insert (A ∪ B) ((Q.parts.erase A).erase B)).val.map Finset.card = _
  rw [Finset.insert_val_of_notMem hU', Multiset.map_cons, Finset.erase_val,
    Multiset.map_erase_of_mem Finset.card _ hB', Finset.erase_val,
    Multiset.map_erase_of_mem Finset.card _ hA, hcard]
  simpa only [Multiset.singleton_add] using
    (add_comm ({A.card + B.card} : Multiset ℕ)
      (((Q.parts.val.map Finset.card).erase A.card).erase B.card))

private theorem earlier_index {k : ℕ} (q : Fin k) (h : Fin q.val) (eps : Fin 2) :
    edgeIndex (earlierVertex q h eps) = (⟨h.val, by omega⟩ : Fin k) := by
  apply Fin.ext
  dsimp only [edgeIndex, earlierVertex]
  omega

theorem selected_indices {k : ℕ} (p : P k) (q : Fin k) (h : Fin q.val) :
    edgeIndex (equalChargeVertex p q h) = (⟨h.val, by omega⟩ : Fin k) ∧
      edgeIndex (oppositeChargeVertex p q h) = (⟨h.val, by omega⟩ : Fin k) := by
  unfold equalChargeVertex oppositeChargeVertex
  split <;> exact ⟨earlier_index q h _, earlier_index q h _⟩

private theorem selected_join_parts {k : ℕ} (p : P k) (q : Fin k) (h : Fin q.val)
    (hc : ¬ Component p (edgeVertex q) (earlierVertex q h 0)) :
    let rho := (ct p).parts
    let r := ((edgeComponents p).part q).card
    let s := ((edgeComponents p).part (⟨h.val, by omega⟩ : Fin k)).card
    (ct (act (equalChargeVertex p q h) (edgeVertex q) p)).parts =
        ((rho.erase r).erase s) + {r + s} ∧
      (ct (act (oppositeChargeVertex p q h) (edgeVertex q) p)).parts =
        ((rho.erase r).erase s) + {r + s} := by
  have hn (a : Fin (2 * k))
      (ha : edgeIndex a = (⟨h.val, by omega⟩ : Fin k)) :
      ¬ Component p a (edgeVertex q) := by
    intro hh
    apply hc
    apply (component_iff_edge_components p _ _).mpr
    have hr := (component_iff_edge_components p a (edgeVertex q)).mp hh
    rw [ha, edgeIndex_vertex] at hr
    simpa only [earlier_index, edgeIndex_vertex] using (edgeSetoid p).symm hr
  constructor
  · have he := ct_join p (hn _ (selected_indices p q h).1)
    simpa only [(selected_indices p q h).1, edgeIndex_vertex,
      Multiset.erase_comm, add_comm] using he
  · have he := ct_join p (hn _ (selected_indices p q h).2)
    simpa only [(selected_indices p q h).2, edgeIndex_vertex,
      Multiset.erase_comm, add_comm] using he

private noncomputable def joinIndicator {K : Type*} [Zero K] [One K]
    {k : ℕ} (lam : Nat.Partition k) (p : P k) (q : Fin k) (h : Fin q.val) : K :=
  let r := ((edgeComponents p).part q).card
  let s := ((edgeComponents p).part (⟨h.val, by omega⟩ : Fin k)).card
  if lam.parts = (((ct p).parts.erase r).erase s) + {r + s} then 1 else 0

private theorem selected_join_indicators {k : ℕ} (lam : Nat.Partition k)
    (p : P k) (q : Fin k) (h : Fin q.val)
    (hc : ¬ Component p (edgeVertex q) (earlierVertex q h 0)) :
    indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) =
        (joinIndicator lam p q h : RatFunc ℂ) ∧
      indicator lam (act (oppositeChargeVertex p q h) (edgeVertex q) p) =
        (joinIndicator lam p q h : RatFunc ℂ) := by
  constructor
  · unfold indicator joinIndicator
    apply if_congr _ rfl rfl
    exact (Nat.Partition.ext_iff).trans
      (by rw [(selected_join_parts p q h hc).1]; exact eq_comm)
  · unfold indicator joinIndicator
    apply if_congr _ rfl rfl
    exact (Nat.Partition.ext_iff).trans
      (by rw [(selected_join_parts p q h hc).2]; exact eq_comm)

private theorem native_surgery_row (b : RatFunc ℂ) {k : ℕ}
    (lam : Nat.Partition k) (p : P k) :
    S b k (indicator lam) p =
      (∑ q : Fin k, ∑ h : Fin q.val,
        if Component p (edgeVertex q) (earlierVertex q h 0) then
          indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p)
        else (1 + b) * joinIndicator lam p q h) +
      b * ((ct p).parts.map fun r => (Nat.choose r 2 : RatFunc ℂ)).sum *
        indicator lam p := by
  rw [native_internal_row]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro h _
  by_cases hc : Component p (edgeVertex q) (earlierVertex q h 0)
  · simp only [if_pos hc, mul_zero, add_zero]
  · rw [if_neg hc, if_neg hc, (selected_join_indicators lam p q h hc).1,
      (selected_join_indicators lam p q h hc).2]
    ring

private noncomputable def joinKernel {K : Type*} [Zero K] [One K] {k : ℕ}
    (lam : Nat.Partition k) (p : P k) (C D : Finset (Fin k)) : K :=
  if lam.parts = (((ct p).parts.erase C.card).erase D.card) + {C.card + D.card}
    then 1 else 0

private theorem external_pair_count {K : Type*} [Field K] [CharZero K]
    {k : ℕ} (lam : Nat.Partition k) (p : P k) :
    2 * (∑ q : Fin k, ∑ h : Fin q.val,
      if Component p (edgeVertex q) (earlierVertex q h 0) then 0 else
        (joinIndicator lam p q h : K)) =
      (((ct p).parts.map fun r =>
        (((ct p).parts.erase r).map fun (s : ℕ) => (r : K) * (s : K) *
          if lam.parts = (((ct p).parts.erase r).erase s) + {r + s} then 1 else 0).sum).sum) := by
  let Q := edgeComponents p
  let g : Fin k → Fin k → K := fun i j =>
    if Q.part i = Q.part j then 0 else joinKernel lam p (Q.part i) (Q.part j)
  have hsymm (C D : Finset (Fin k)) :
      (joinKernel lam p C D : K) = joinKernel lam p D C := by
    unfold joinKernel
    rw [Multiset.erase_comm, Nat.add_comm C.card D.card]
  have hs : ∀ i j, g i j = g j i := by
    intro i j
    dsimp only [g]
    by_cases h : Q.part i = Q.part j
    · simp only [h, if_true]
    · rw [if_neg h, if_neg (Ne.symm h), hsymm]
  have hd : ∀ i, g i i = 0 := by intro i; simp only [g, if_true]
  have hrelation (i j : Fin k) : Component p (edgeVertex i) (edgeVertex j) ↔
      Q.part i = Q.part j := by
    rw [← edge_component_membership]
    exact (Q.mem_part_iff_part_eq_part (Finset.mem_univ _) (Finset.mem_univ _)).trans eq_comm
  have htri : (∑ q : Fin k, ∑ h : Fin q.val, g q ⟨h.val, by omega⟩) =
      ∑ q : Fin k, ∑ h : Fin q.val,
        if Component p (edgeVertex q) (earlierVertex q h 0) then 0 else
          (joinIndicator lam p q h : K) := by
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro h _
    have hv : earlierVertex q h 0 = edgeVertex (⟨h.val, by omega⟩ : Fin k) := by
      apply Fin.ext
      simp only [earlierVertex, edgeVertex, Fin.val_zero, zero_add]
    rw [hv, hrelation]
    by_cases hi : Q.part q = Q.part (⟨h.val, by omega⟩ : Fin k)
    · simp [g, hi]
    · simp [g, hi, joinKernel, joinIndicator, Q]
  have hfull := component_pair_sum p (fun C D =>
    if C = D then (0 : K) else joinKernel lam p C D)
  change (∑ i : Fin k, ∑ j : Fin k, g i j) = _ at hfull
  have herase (C : Finset (Fin k)) :
      (∑ D ∈ Q.parts, (C.card : K) * (D.card : K) *
        (if C = D then 0 else joinKernel lam p C D)) =
      ∑ D ∈ Q.parts.erase C, (C.card : K) * (D.card : K) * joinKernel lam p C D := by
    calc
      _ = ∑ D ∈ Q.parts.erase C, (C.card : K) * (D.card : K) *
          (if C = D then 0 else joinKernel lam p C D) := by
        symm
        apply Finset.sum_subset (Finset.erase_subset _ _)
        intro D hD hnot
        have he : D = C := by
          by_contra hn
          exact hnot (Finset.mem_erase.mpr ⟨hn, hD⟩)
        subst D
        simp only [if_true, mul_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro D hD
        rw [if_neg (Finset.ne_of_mem_erase hD).symm]
  have hmap (C : Finset (Fin k)) (hC : C ∈ Q.parts) :
      (∑ D ∈ Q.parts.erase C, (C.card : K) * (D.card : K) * joinKernel lam p C D) =
      ((((ct p).parts.erase C.card).map fun (s : ℕ) => (C.card : K) * (s : K) *
        if lam.parts = (((ct p).parts.erase C.card).erase s) + {C.card + s} then 1 else 0).sum) := by
    change _ = (((Q.parts.val.map Finset.card).erase C.card).map _).sum
    rw [← Multiset.map_erase_of_mem Finset.card _ hC, Multiset.map_map]
    rw [← Finset.erase_val, ← Finset.sum_eq_multiset_sum]
    rfl
  have hocc : (∑ C ∈ Q.parts, ∑ D ∈ Q.parts,
      (C.card : K) * (D.card : K) *
        (if C = D then 0 else joinKernel lam p C D)) =
      (((ct p).parts.map fun r =>
        (((ct p).parts.erase r).map fun (s : ℕ) => (r : K) * (s : K) *
          if lam.parts = (((ct p).parts.erase r).erase s) + {r + s} then 1 else 0).sum).sum) := by
    change _ = ((Q.parts.val.map Finset.card).map _).sum
    rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
    apply Finset.sum_congr rfl
    intro C hC
    exact (herase C).trans (hmap C hC)
  have ht := two_triangular_sum k g hs hd
  rw [htri, hfull, hocc] at ht
  exact ht

theorem native_counted_join_row (b : RatFunc ℂ) {k : ℕ}
    (lam : Nat.Partition k) (p : P k) :
    S b k (indicator lam) p =
      (∑ q : Fin k, ∑ h : Fin q.val,
        if Component p (edgeVertex q) (earlierVertex q h 0) then
          indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) else 0) +
      (1 + b) / 2 * (((ct p).parts.map fun r =>
        (((ct p).parts.erase r).map fun (s : ℕ) => (r : RatFunc ℂ) * (s : RatFunc ℂ) *
          if lam.parts = (((ct p).parts.erase r).erase s) + {r + s} then 1 else 0).sum).sum) +
      b * ((ct p).parts.map fun r => (Nat.choose r 2 : RatFunc ℂ)).sum *
        indicator lam p := by
  rw [native_surgery_row]
  have hs : (∑ q : Fin k, ∑ h : Fin q.val,
      if Component p (edgeVertex q) (earlierVertex q h 0) then
        indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p)
      else (1 + b) * joinIndicator lam p q h) =
    (∑ q : Fin k, ∑ h : Fin q.val,
      if Component p (edgeVertex q) (earlierVertex q h 0) then
        indicator lam (act (equalChargeVertex p q h) (edgeVertex q) p) else 0) +
    (1 + b) * (∑ q : Fin k, ∑ h : Fin q.val,
      if Component p (edgeVertex q) (earlierVertex q h 0) then 0 else
        (joinIndicator lam p q h : RatFunc ℂ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    split <;> simp
  rw [hs]
  have he := external_pair_count (K := RatFunc ℂ) lam p
  linear_combination (1 + b) / 2 * he


end D5.S3.Combinatorics.PerfectMatchings.DeformedJucysMurphyRow
