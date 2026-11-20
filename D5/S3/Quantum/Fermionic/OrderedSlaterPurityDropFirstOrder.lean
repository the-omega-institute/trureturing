/- GID: D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropFirstOrder
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/OrderedSlaterPurityDropFirstOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First-order correction and its equality criterion for a strict Slater purity drop. -/

import D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropEquality

/-! # First-order correction to the Slater purity-drop bound

Average the linear excesses of the basis-bit probabilities and retained parity
factors over the free difference bits. Equality holds exactly when no solution
of the binary constraints has two distinct factors above their lower bounds. -/

open scoped BigOperators Matrix
open D5.S3.Quantum.Fermionic OrderedSlaterCut SlaterPairCutRank
open D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropBound
open D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropEquality
open D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropEquality

namespace D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropFirstOrder

private theorem product_excess_first_order {I : Type*} (s : Finset I) (g : I → ℝ)
    (hn : ∀ i, 0 ≤ g i) :
    1 + ∑ i ∈ s, g i ≤ ∏ i ∈ s, (1 + g i) ∧
      ((∏ i ∈ s, (1 + g i)) = 1 + ∑ i ∈ s, g i ↔
        ∀ i ∈ s, ∀ j ∈ s, i ≠ j → g i = 0 ∨ g j = 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hpos : 0 < 1 + g a := by linarith [hn a]
      have hsum : 0 ≤ ∑ i ∈ s, g i := Finset.sum_nonneg fun i _ => hn i
      have hcross := mul_nonneg (hn a) hsum
      have hmul := mul_le_mul_of_nonneg_left ih.1 hpos.le
      refine ⟨by nlinarith, ?_, ?_⟩
      · intro heq
        have hz : g a * (∑ i ∈ s, g i) = 0 := by nlinarith
        have heq' : (1 + g a) * (∏ i ∈ s, (1 + g i)) =
            (1 + g a) * (1 + ∑ i ∈ s, g i) := by nlinarith
        have hold := ih.2.mp (mul_left_cancel₀ hpos.ne' heq')
        have hnew (j : I) (hj : j ∈ s) : g a = 0 ∨ g j = 0 := by
          rcases mul_eq_zero.mp hz with h | h
          · exact Or.inl h
          · exact Or.inr ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp h j hj)
        intro i hi j hj hij
        by_cases hia : i = a
        · subst i
          exact hnew j ((Finset.mem_insert.mp hj).resolve_left hij.symm)
        · have hi' := (Finset.mem_insert.mp hi).resolve_left hia
          by_cases hja : j = a
          · subst j
            exact (hnew i hi').symm
          · exact hold i hi' j ((Finset.mem_insert.mp hj).resolve_left hja) hij
      · intro h
        have heq := ih.2.mpr (fun i hi j hj =>
          h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
        rw [heq]
        have hz : g a * (∑ i ∈ s, g i) = 0 := by
          by_cases hga : g a = 0
          · simp [hga]
          · have hzero : ∀ i ∈ s, g i = 0 := fun i hi =>
              (h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
                (fun heq => ha (heq ▸ hi))).resolve_left hga
            rw [Finset.sum_eq_zero hzero, mul_zero]
        nlinarith

open Classical in
private theorem weighted_normalized_first_order_le {Y I : Type*} [Fintype Y] [Fintype I]
    (w : Y → ℝ) (g : Y → I → ℝ) (hw : ∀ y, 0 < w y)
    (hnorm : ∑ y, w y = 1) (hgn : ∀ y i, 0 ≤ g y i) :
    let weightedProduct := ∑ y, w y * ∏ i, (1 + g y i)
    let firstOrder := 1 + ∑ i, ∑ y, w y * g y i
    firstOrder ≤ weightedProduct ∧
      (weightedProduct = firstOrder ↔ ∀ y i j, i ≠ j → g y i = 0 ∨ g y j = 0) := by
  intro weightedProduct firstOrder
  have hsum : (∑ y, w y * (1 + ∑ i, g y i)) = firstOrder := by
    simp_rw [mul_add, mul_one, Finset.mul_sum]
    rw [Finset.sum_add_distrib, hnorm, Finset.sum_comm]
  have hrel (y : Y) : w y * (1 + ∑ i, g y i) ≤ w y * ∏ i, (1 + g y i) :=
    mul_le_mul_of_nonneg_left (product_excess_first_order Finset.univ (g y) (hgn y)).1 (hw y).le
  have hpoint (y : Y) : (∏ i, (1 + g y i)) = 1 + ∑ i, g y i ↔
      ∀ i j, i ≠ j → g y i = 0 ∨ g y j = 0 := by
    simpa using (product_excess_first_order Finset.univ (g y) (hgn y)).2
  refine ⟨?_, ?_⟩
  · rw [← hsum]
    exact Finset.sum_le_sum (fun y _ => hrel y)
  · constructor
    · intro heq y
      apply (hpoint y).mp
      by_contra hne
      have hlt : 1 + ∑ i, g y i < ∏ i, (1 + g y i) :=
        lt_of_le_of_ne (product_excess_first_order Finset.univ (g y) (hgn y)).1 (Ne.symm hne)
      have hstrict : firstOrder < weightedProduct := by
        rw [← hsum]
        exact Finset.sum_lt_sum (fun y' _ => hrel y')
          ⟨y, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt (hw y)⟩
      exact (ne_of_lt hstrict) heq.symm
    · intro h
      have heq (y : Y) : ∏ i, (1 + g y i) = 1 + ∑ i, g y i := (hpoint y).mpr (h y)
      change (∑ y, w y * ∏ i, (1 + g y i)) = _
      simp_rw [heq]
      exact hsum

open Classical in
private theorem weighted_first_order_le {Y I : Type*} [Fintype Y] [Fintype I]
    (w : Y → ℝ) (lower : I → ℝ) (factor : Y → I → ℝ)
    (hw : ∀ y, 0 < w y) (hnorm : ∑ y, w y = 1)
    (hlo : ∀ i, 0 < lower i) (hle : ∀ y i, lower i ≤ factor y i) :
    let bound := (∏ i, lower i) * (1 + ∑ i, ∑ y, w y * (factor y i / lower i - 1))
    let value := ∑ y, w y * ∏ i, factor y i
    bound ≤ value ∧
      (value = bound ↔ ∀ y i j, i ≠ j → factor y i = lower i ∨ factor y j = lower j) := by
  let g (y : Y) (i : I) := factor y i / lower i - 1
  have hgn (y : Y) (i : I) : 0 ≤ g y i :=
    sub_nonneg.mpr ((le_div_iff₀ (hlo i)).mpr (by simpa using hle y i))
  have hrel (y : Y) (i : I) : factor y i = lower i * (1 + g y i) := by
    dsimp [g]
    field_simp [(hlo i).ne']
    ring
  have hzero (y : Y) (i : I) : g y i = 0 ↔ factor y i = lower i := by
    change factor y i / lower i - 1 = 0 ↔ factor y i = lower i
    rw [sub_eq_zero, div_eq_iff (hlo i).ne', one_mul]
  have hpos : 0 < ∏ i, lower i := Finset.prod_pos fun i _ => hlo i
  have hvalue : (∑ y, w y * ∏ i, factor y i) =
      (∏ i, lower i) * ∑ y, w y * ∏ i, (1 + g y i) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hprod : (∏ i, factor y i) = (∏ i, lower i) * ∏ i, (1 + g y i) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hrel y i
    rw [hprod]
    ring
  intro bound value
  change (∏ i, lower i) * (1 + ∑ i, ∑ y, w y * g y i) ≤ _ ∧ _
  have hval : value = (∏ i, lower i) * ∑ y, w y * ∏ i, (1 + g y i) := hvalue
  have hbound : bound = (∏ i, lower i) * (1 + ∑ i, ∑ y, w y * g y i) := rfl
  rw [hval, hbound]
  have hscaled := weighted_normalized_first_order_le w g hw hnorm hgn
  refine ⟨mul_le_mul_of_nonneg_left hscaled.1 hpos.le, ?_⟩
  rw [mul_right_inj' hpos.ne']
  simpa only [hzero] using hscaled.2

open Classical in
private theorem weighted_fiber_first_order {L P F T R : Type*}
    [Fintype L] [Fintype P] [Fintype F] [Fintype R] [DecidableEq T]
    (C : Matrix T L (ZMod 2)) (t : T) (split : P ⊕ F ≃ L)
    (hlin : LinearIndependent (ZMod 2) fun j : P => C.col (split (.inl j)))
    (hspan : Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col))
    (hsol : ∃ x, C *ᵥ x = Pi.single t 1)
    (q : L → ℝ) (hq : ∀ j, 0 < q j ∧ q j < 1)
    (p : R → ℝ) (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 1 ∧ p k ≠ 1 / 2)
    (rows : Matrix R L (ZMod 2))
    [Fintype {x : L → ZMod 2 // C *ᵥ x = Pi.single t 1}] :
    let W := {x : L → ZMod 2 // C *ᵥ x = Pi.single t 1}
    let w (x : W) := ∏ j : F, diffMass (q (split (.inr j))) (x.val (split (.inr j)))
    let lower : P ⊕ R → ℝ :=
      Sum.elim (fun j => diffMass (q (split (.inl j))) 1) (fun k => squaredBias (p k))
    let factor (x : W) : P ⊕ R → ℝ :=
      Sum.elim (fun j => diffMass (q (split (.inl j))) (x.val (split (.inl j))))
        (fun k => parityFactor (p k) (rows k ⬝ᵥ x.val))
    let corrected := (∏ a, lower a) * (1 + ∑ a, ∑ x : W, w x * (factor x a / lower a - 1))
    let value := ∑ x : W, (∏ j : L, diffMass (q j) (x.val j)) *
        ∏ k : R, parityFactor (p k) (rows k ⬝ᵥ x.val)
    corrected ≤ value ∧
      (value = corrected ↔
        ∀ x a b, a ≠ b → factor x a = lower a ∨ factor x b = lower b) := by
  intro W w lower factor corrected value
  let free := fiberFreeEquiv C split (Pi.single t 1) hlin hspan hsol
  have hpositive (j : L) (b : ZMod 2) : 0 < diffMass (q j) b :=
    (mul_pos (mul_pos (by norm_num) (hq j).1) (sub_pos.mpr (hq j).2)).trans_le
      (diffMass_lower _ b)
  have hw (x : W) : 0 < w x := Finset.prod_pos fun _ _ => hpositive _ _
  have hnorm : ∑ x, w x = 1 := by
    have hsum : (∑ x, w x) =
        ∑ y : F → ZMod 2, ∏ j : F, diffMass (q (split (.inr j))) (y j) :=
      Fintype.sum_equiv free _ _ fun _ => rfl
    rw [hsum, ← Fintype.prod_sum]
    simp only [diffMass_sum, Finset.prod_const_one]
  have hlo (a : P ⊕ R) : 0 < lower a := by
    cases a with
    | inl j => exact hpositive _ _
    | inr k => exact sq_pos_of_ne_zero (fun h => (hp k).2.2 (by linarith))
  have hle (x : W) (a : P ⊕ R) : lower a ≤ factor x a := by
    cases a with
    | inl j =>
      change diffMass (q (split (.inl j))) 1 ≤
        diffMass (q (split (.inl j))) (x.val (split (.inl j)))
      simpa [diffMass] using diffMass_lower (q (split (.inl j))) (x.val (split (.inl j)))
    | inr k =>
      change squaredBias (p k) ≤ parityFactor (p k) (rows k ⬝ᵥ x.val)
      by_cases h : rows k ⬝ᵥ x.val = 0
      · simpa [parityFactor, h] using squaredBias_le_one (hp k).1 (hp k).2.1
      · simp [parityFactor, h]
  have hvalue : value = ∑ x, w x * ∏ a, factor x a := by
    change (∑ x : W, (∏ j : L, diffMass (q j) (x.val j)) *
        ∏ k : R, parityFactor (p k) (rows k ⬝ᵥ x.val)) = _
    apply Finset.sum_congr rfl
    intro x _
    have hsplit : (∏ j : L, diffMass (q j) (x.val j)) =
        (∏ j : P, diffMass (q (split (.inl j))) (x.val (split (.inl j)))) * w x := by
      unfold w
      rw [← Fintype.prod_sum_type (fun a : P ⊕ F => diffMass (q (split a)) (x.val (split a)))]
      exact Fintype.prod_equiv split.symm _ _ fun j => by rw [split.apply_symm_apply]
    rw [hsplit, Fintype.prod_sum_type]
    change _ = w x * ((∏ j : P, diffMass (q (split (.inl j))) (x.val (split (.inl j)))) *
      ∏ k : R, parityFactor (p k) (rows k ⬝ᵥ x.val))
    ring
  rw [hvalue]
  exact weighted_first_order_le w lower factor hw hnorm hlo hle

set_option maxHeartbeats 2300000 in
-- The comparison of the two presentations of the weighted fiber converts
-- finite sums whose active-column subtypes carry different decision procedures.
open Classical in
/-- The old product bound times one plus the expected sum of the relative
factor excesses. Equality requires that no feasible difference string
raises two distinct factors above their lower bounds. -/
theorem orderedMarginal_purity_drop_first_order {ι P F : Type*}
    [LinearOrder ι] [Fintype ι] [Fintype P] [Fintype F]
    {m n : ℕ} {I : Set ι} (left : (Fin m × Bool) ↪ I) (right : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hl : ∀ k, (left (k, false) : ι) < left (k, true))
    (hr : ∀ j, (right (j, false) : ι) < right (j, true))
    (before after : Fin (m + n) → Bool → ℂ) (p : Fin m → ℝ) (q : Fin n → ℝ) (i : Fin m)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (hp : ∀ k e, before (Fin.castAdd n k) e * star (before (Fin.castAdd n k) e) =
      endpointMass (p k) e)
    (hq : ∀ j e, before (Fin.natAdd m j) e * star (before (Fin.natAdd m j) e) =
      endpointMass (q j) e)
    (hp' : ∀ k e, after (Fin.castAdd n k) e * star (after (Fin.castAdd n k) e) =
      endpointMass (Function.update p i (1 / 2) k) e)
    (hq' : ∀ j e, after (Fin.natAdd m j) e * star (after (Fin.natAdd m j) e) =
      endpointMass (q j) e)
    (split : P ⊕ F ≃ {j : Fin n // 0 < q j ∧ q j < 1}) :
    let A := alternationMatrix (fun k e => (left (k, e) : ι)) (fun j e => (right (j, e) : ι))
    let L := {j : Fin n // 0 < q j ∧ q j < 1}
    let active : Matrix (Fin m) L (ZMod 2) := fun k j => A k j
    let T := {k : Fin m // k = i ∨ p k = 1 / 2}
    let C : Matrix T L (ZMod 2) := fun k j => A k j
    let t : T := ⟨i, Or.inl rfl⟩
    let other := Finset.univ.filter fun k => k ≠ i ∧ p k ≠ 1 / 2
    let purity (weight : Fin (m + n) → Bool → ℂ) :=
      let B := orderedCut I (cutPairOrbitals left right weight)
      (((B * Bᴴ) ^ 2).trace).re
    let drop := purity before - purity after
    let R := {k // k ∈ other}
    let W := {x : L → ZMod 2 // C *ᵥ x = Pi.single t 1}
    let w (x : W) := ∏ j : F, diffMass (q (split (.inr j))) (x.val (split (.inr j)))
    let lower : P ⊕ R → ℝ := Sum.elim (fun j => diffMass (q (split (.inl j))) 1)
      (fun k => squaredBias (p k))
    let factor (x : W) : P ⊕ R → ℝ :=
      Sum.elim (fun j => diffMass (q (split (.inl j))) (x.val (split (.inl j))))
        (fun k => parityFactor (p k) ((active *ᵥ x.val) k))
    let corrected := squaredBias (p i) * ((∏ a, lower a) *
      (1 + ∑ a, ∑ x : W, w x * (factor x a / lower a - 1)))
    LinearIndependent (ZMod 2) (fun j : P => C.col (split (.inl j))) →
    Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col) →
    0 < drop →
    corrected ≤ drop ∧
      (drop = corrected ↔
        ∀ x a b, a ≠ b → factor x a = lower a ∨ factor x b = lower b) := by
  intro A L active T C t other purity drop R W w lower factor corrected hlin hspan hdrop
  have hbefore : purity before = puritySum A p q :=
    marginal_eq_real left right hl hr before p q hp hq
  have hafter : purity after = puritySum A (Function.update p i (1 / 2)) q :=
    marginal_eq_real left right hl hr after _ q hp' hq'
  have hvalue : drop = puritySum A p q - puritySum A (Function.update p i (1 / 2)) q := by
    change purity before - purity after = _
    rw [hbefore, hafter]
  have hpi : p i ≠ 1 / 2 := by
    intro hi
    have unchanged : Function.update p i (1 / 2) = p := by
      rw [← hi, Function.update_eq_self]
    exact (lt_irrefl (0 : ℝ)) (by simpa only [hvalue, unchanged, sub_self] using hdrop)
  let target : T → ZMod 2 := fun k => if k.val = i then 1 else 0
  have htarget : target = Pi.single t 1 := by
    funext k
    by_cases hk : k.val = i
    · have hkt : k = t := Subtype.ext hk
      rw [hkt]
      simp only [target, show t.val = i from rfl, ite_true, Pi.single_eq_same]
    · have hkt : k ≠ t := fun h => hk (congrArg Subtype.val h)
      simp [target, hk, Pi.single_eq_of_ne hkt]
  obtain ⟨hsol, _⟩ := balancing_difference_ge_fiber A p q i hp0 hp1 hq0 hq1
    (hvalue ▸ hdrop)
  change ∃ x, C *ᵥ x = target at hsol
  rw [htarget] at hsol
  let rows : Matrix R L (ZMod 2) := fun k j => active k j
  have hpR (k : R) : 0 ≤ p k ∧ p k ≤ 1 ∧ p k ≠ 1 / 2 :=
    ⟨hp0 k, hp1 k, (Finset.mem_filter.mp k.property).2.2⟩
  have hsum : drop = squaredBias (p i) * ∑ x : L → ZMod 2,
      if C *ᵥ x = target then (∏ j : L, diffMass (q j) (x j)) *
        ∏ k ∈ other, parityFactor (p k) ((active *ᵥ x) k) else 0 := by
    have hsource := hvalue.trans (difference_eq_weighted_fiber A p q i hq0 hq1)
    convert hsource using 2
    apply Finset.sum_congr
    · ext x
      simp
    · intro x _
      congr!
  rw [htarget] at hsum
  rw [← Finset.sum_filter, ← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ] at hsum
  let value := ∑ x : W, (∏ j : L, diffMass (q j) (x.val j)) *
      ∏ k : R, parityFactor (p k) (rows k ⬝ᵥ x.val)
  have hsum' : drop = squaredBias (p i) * value := by
    rw [hsum]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    change (∏ k ∈ other, parityFactor (p k) ((active *ᵥ x.val) k)) =
      ∏ k : R, parityFactor (p k) ((active *ᵥ x.val) k)
    exact Finset.prod_subtype other (fun _ => Iff.rfl) _
  have hb : 0 < squaredBias (p i) := sq_pos_of_ne_zero (fun h => hpi (by linarith))
  have hcorr : corrected = squaredBias (p i) *
      ((∏ a, lower a) * (1 + ∑ a, ∑ x : W, w x * (factor x a / lower a - 1))) := rfl
  have hcore :
      (∏ a, lower a) * (1 + ∑ a, ∑ x : W, w x * (factor x a / lower a - 1)) ≤ value ∧
      (value = (∏ a, lower a) * (1 + ∑ a, ∑ x : W, w x * (factor x a / lower a - 1)) ↔
        ∀ x a b, a ≠ b → factor x a = lower a ∨ factor x b = lower b) :=
    weighted_fiber_first_order C t split hlin hspan hsol
      (fun j : L => q j) (fun j => j.property) (fun k : R => p k) hpR rows
  rw [hsum', hcorr]
  refine ⟨mul_le_mul_of_nonneg_left hcore.1 hb.le, ?_⟩
  rw [mul_right_inj' hb.ne']
  exact hcore.2

end D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropFirstOrder
