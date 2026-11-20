/- GID: D5/S3/Quantum/Fermionic/OrderedSlaterPurityDropEquality
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/OrderedSlaterPurityDropEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact equality in the column-basis lower bound for a strict Slater purity drop. -/

import D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropBound
import D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropEquality

/-! # Equality in the purity decrease of an ordered Slater marginal

The exact purity difference is a positive weighted sum over the binary fiber of the
selected retained row and the other balanced rows. Each biased pivot column and each
nondeterministic biased retained row must evaluate to one throughout this fiber. -/

open scoped BigOperators Matrix
open D5.S3.Quantum.Fermionic OrderedSlaterCut SlaterPairCutRank
open D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropBound
open D5.S3.Quantum.Fermionic.WeightedSlaterPurityDropEquality

namespace D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropEquality

open Classical in
private theorem active_difference {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    (A : Matrix U V (ZMod 2)) (p : U → ℝ) (q : V → ℝ) (i : U)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) :
    let L := {j : V // 0 < q j ∧ q j < 1}
    let active : Matrix U L (ZMod 2) := fun k j => A k j
    puritySum A p q - puritySum A (Function.update p i (1 / 2)) q =
      ∑ w : L → ZMod 2, if (active *ᵥ w) i = 0 then 0 else
        (∏ j : L, diffMass (q j) (w j)) * squaredBias (p i) *
          ∏ k ∈ Finset.univ.erase i, parityFactor (p k) ((active *ᵥ w) k) := by
  intro L active
  rw [difference_from_balancing]
  let extend (w : L → ZMod 2) (j : V) :=
    if h : 0 < q j ∧ q j < 1 then w ⟨j, h⟩ else 0
  have extend_active (w : L → ZMod 2) (j : L) : extend w j = w j := by
    simp [extend, j.property]
  have extend_injective : Function.Injective extend := by
    intro w v he
    funext j
    simpa only [extend_active] using congrFun he (j : V)
  let term (w : V → ZMod 2) :=
    if (A *ᵥ w) i = 0 then 0 else
      (∏ j, diffMass (q j) (w j)) * squaredBias (p i) *
        ∏ k ∈ Finset.univ.erase i, parityFactor (p k) ((A *ᵥ w) k)
  have hzero (w : V → ZMod 2) (hw : w ∉ Finset.univ.image extend) : term w = 0 := by
    have hbad : ∃ j : V, ¬ (0 < q j ∧ q j < 1) ∧ w j ≠ 0 := by
      by_contra h
      apply hw
      apply Finset.mem_image.mpr
      refine ⟨fun j : L => w j, Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : 0 < q j ∧ q j < 1
      · simp [extend, hj]
      · have hz : w j = 0 := by
          by_contra hnz
          exact h ⟨j, hj, hnz⟩
        simp [extend, hj, hz]
    obtain ⟨j, hj, hnz⟩ := hbad
    have hmass : diffMass (q j) (w j) = 0 := by
      rcases deterministic_probability (hq0 j) (hq1 j) hj with h | h <;>
        simp [diffMass, h, hnz]
    have hprod := Finset.prod_eq_zero (f := fun t => diffMass (q t) (w t))
      (Finset.mem_univ j) hmass
    simp [term, hprod]
  change (∑ w, term w) = _
  calc
    (∑ w, term w) = ∑ w ∈ Finset.univ.image extend, term w := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) (fun w _ => hzero w)
    _ = ∑ w : L → ZMod 2, term (extend w) :=
      Finset.sum_image extend_injective.injOn
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      have hrow (k : U) : (A *ᵥ extend w) k = (active *ᵥ w) k := by
        rw [mulVec_restrict_active A q (extend w) (fun j h => by simp [extend, h])]
        change (∑ j : L, A k j * extend w j) = ∑ j : L, A k j * w j
        simp only [extend_active]
      have hmass : (∏ j : L, diffMass (q j) (w j)) =
          ∏ j : V, diffMass (q j) (extend w j) := by
        simp_rw [← extend_active w]
        rw [← Finset.subtype_univ,
          Finset.prod_subtype_eq_prod_filter (fun j => diffMass (q j) (extend w j))]
        apply Finset.prod_subset (Finset.filter_subset _ _)
        intro j _ hj
        have hja : ¬ (0 < q j ∧ q j < 1) := by simpa using hj
        rcases deterministic_probability (hq0 j) (hq1 j) hja with h | h <;>
          simp [extend, diffMass, h]
      simp_rw [term, hrow, hmass]

open Classical in
private theorem difference_eq_weighted_fiber {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    (A : Matrix U V (ZMod 2)) (p : U → ℝ) (q : V → ℝ) (i : U)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1) :
    let L := {j : V // 0 < q j ∧ q j < 1}
    let active : Matrix U L (ZMod 2) := fun k j => A k j
    let R := {k : U // k = i ∨ p k = 1 / 2}
    let C : Matrix R L (ZMod 2) := fun k j => A k j
    let target : R → ZMod 2 := fun k => if k.val = i then 1 else 0
    let other := Finset.univ.filter (fun k => k ≠ i ∧ p k ≠ 1 / 2)
    puritySum A p q - puritySum A (Function.update p i (1 / 2)) q =
      squaredBias (p i) * ∑ w : L → ZMod 2,
        if C *ᵥ w = target then (∏ j : L, diffMass (q j) (w j)) *
          ∏ k ∈ other, parityFactor (p k) ((active *ᵥ w) k) else 0 := by
  intro L active R C target other
  rw [active_difference A p q i hq0 hq1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  let a := active *ᵥ w
  have hC (k : R) : (C *ᵥ w) k = a k := rfl
  change (if a i = 0 then 0 else (∏ j : L, diffMass (q j) (w j)) * squaredBias (p i) *
    ∏ k ∈ Finset.univ.erase i, parityFactor (p k) (a k)) =
    squaredBias (p i) * (if C *ᵥ w = target then (∏ j : L, diffMass (q j) (w j)) *
      ∏ k ∈ other, parityFactor (p k) (a k) else 0)
  by_cases hw : C *ᵥ w = target
  · have hi : a i = 1 := by
      have h := (hC ⟨i, Or.inl rfl⟩).symm.trans (congrFun hw ⟨i, Or.inl rfl⟩)
      simpa [target] using h
    have hprod : (∏ k ∈ other, parityFactor (p k) (a k)) =
        ∏ k ∈ Finset.univ.erase i, parityFactor (p k) (a k) := by
      apply Finset.prod_subset
      · intro k hk
        exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hk).2.1, Finset.mem_univ _⟩
      · intro k hk hnot
        have hki := Finset.ne_of_mem_erase hk
        have hb : p k = 1 / 2 := by simpa [other, hki] using hnot
        have h := (hC ⟨k, Or.inr hb⟩).symm.trans (congrFun hw ⟨k, Or.inr hb⟩)
        have hz : a k = 0 := by simpa [target, hki] using h
        simp [parityFactor, hz]
    simp only [hi, one_ne_zero, ite_false, hw, ite_true, hprod]
    ring
  · by_cases hi : a i = 0
    · simp [hi, hw]
    · have hone : a i = 1 :=
        (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) _ |>.resolve_left hi
      have hex : ∃ k : R, k.val ≠ i ∧ a k ≠ 0 := by
        by_contra hn
        apply hw
        funext k
        rw [hC]
        by_cases hki : k.val = i
        · simp [target, hki, hone]
        · have hz : a k = 0 := by
            by_contra hnz
            exact hn ⟨k, hki, hnz⟩
          simp [target, hki, hz]
      obtain ⟨k, hki, hk⟩ := hex
      have hzero : parityFactor (p k) (a k) = 0 := by
        norm_num [parityFactor, hk, squaredBias, k.property.resolve_left hki]
      have hprod := Finset.prod_eq_zero (f := fun k : U => parityFactor (p k) (a k))
        (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩) hzero
      simp [hi, hw, hprod]

private theorem diffMass_eq (q : ℝ) (a : ZMod 2) :
    diffMass q a = 2 * q * (1 - q) ↔ q = 1 / 2 ∨ a = 1 := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl
  · simp only [diffMass, ite_true, zero_ne_one, or_false]
    have h : (1 - q) ^ 2 + q ^ 2 - 2 * q * (1 - q) = (1 - 2 * q) ^ 2 := by ring
    rw [← sub_eq_zero, h, sq_eq_zero_iff]
    exact ⟨fun e => by linarith, fun e => by linarith⟩
  · simp [diffMass]

private theorem parityFactor_eq_bias (p : ℝ) (a : ZMod 2) :
    parityFactor p a = squaredBias p ↔ p = 0 ∨ p = 1 ∨ a = 1 := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl
  · simp only [parityFactor, ite_true, squaredBias, zero_ne_one, or_false]
    constructor
    · intro h
      have hprod : p * (1 - p) = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with hp | hp
      · exact Or.inl hp
      · exact Or.inr (by linarith)
    · rintro (rfl | rfl) <;> norm_num
  · simp [parityFactor]

open Classical in
private theorem normalized_fiber_eq_iff {L P F T R : Type*}
    [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq T] [Fintype R]
    (C : Matrix T L (ZMod 2)) (i : T) (split : P ⊕ F ≃ L)
    (hlin : LinearIndependent (ZMod 2) (fun j : P => C.col (split (.inl j))))
    (hspan : Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col))
    (hsol : ∃ x, C *ᵥ x = Pi.single i 1)
    (q : L → ℝ) (hq : ∀ j, 0 < q j ∧ q j < 1)
    (p : R → ℝ) (hp : ∀ k, 0 ≤ p k ∧ p k ≤ 1 ∧ p k ≠ 1 / 2)
    (rows : Matrix R L (ZMod 2)) :
    let S := Submodule.span (ZMod 2) (Set.range fun k : {t : T // t ≠ i} => C k.val)
    (∑ x : L → ZMod 2, if C *ᵥ x = Pi.single i 1 then
      (∏ j : L, diffMass (q j) (x j)) *
        ∏ k, parityFactor (p k) (rows k ⬝ᵥ x) else 0) =
      (∏ j : P, 2 * q (split (.inl j)) * (1 - q (split (.inl j)))) *
        (∏ k, squaredBias (p k)) ↔
      (∀ j : P, q (split (.inl j)) ≠ 1 / 2 → Pi.single (split (.inl j)) 1 - C i ∈ S) ∧
      (∀ k, 0 < p k → p k < 1 → rows k - C i ∈ S) := by
  intro S
  let : Finite F := Finite.of_injective (fun j => split (.inr j))
    (fun _ _ h => Sum.inr.inj (split.injective h))
  let := Fintype.ofFinite F
  let weight (y : F → ZMod 2) := ∏ j, diffMass (q (split (.inr j))) (y j)
  let mass (j : P) (b : ZMod 2) := diffMass (q (split (.inl j))) b
  have hpos (j : L) (b : ZMod 2) : 0 < diffMass (q j) b :=
    (mul_pos (mul_pos (by norm_num) (hq j).1) (sub_pos.mpr (hq j).2)).trans_le
      (diffMass_lower _ b)
  have hweight (y : F → ZMod 2) : 0 < weight y :=
    Finset.prod_pos fun j _ => hpos _ _
  have hnorm : ∑ y, weight y = 1 := by
    unfold weight
    rw [← Fintype.prod_sum]
    simp only [diffMass_sum, Finset.prod_const_one]
  have hbias (k : R) : 0 < squaredBias (p k) :=
    sq_pos_of_ne_zero (fun h => (hp k).2.2 (by linarith))
  have hcom := weighted_pivot_fiber_eq_iff C i split hlin hspan hsol weight mass
    (fun k => squaredBias (p k)) rows hweight hnorm
    (fun j => hpos (split (.inl j)) 1)
    (fun j => by simpa [mass, diffMass] using diffMass_lower (q (split (.inl j))) 0)
    hbias (fun k => squaredBias_le_one (hp k).1 (hp k).2.1)
  have hmass_one (j : P) : mass j 1 = 2 * q (split (.inl j)) * (1 - q (split (.inl j))) := by
    simp [mass, diffMass]
  have hmass_strict (j : P) : mass j 1 < mass j 0 ↔ q (split (.inl j)) ≠ 1 / 2 := by
    rw [lt_iff_le_and_ne]
    constructor
    · rintro ⟨_, hne⟩ heq
      exact hne ((diffMass_eq _ 0).mpr (Or.inl heq)).symm
    · intro hne
      refine ⟨?_, ?_⟩
      · simpa [mass, diffMass] using diffMass_lower (q (split (.inl j))) 0
      · intro h
        exact hne (((diffMass_eq _ 0).mp (h.symm.trans (hmass_one j))).resolve_right zero_ne_one)
  have hbias_strict (k : R) : squaredBias (p k) < 1 ↔ 0 < p k ∧ p k < 1 := by
    rw [lt_iff_le_and_ne]
    constructor
    · rintro ⟨_, hn⟩
      refine ⟨lt_of_le_of_ne (hp k).1 ?_, lt_of_le_of_ne (hp k).2.1 ?_⟩
      · intro h
        simp [← h, squaredBias] at hn
      · intro h
        norm_num [h, squaredBias] at hn
    · rintro ⟨h0, h1⟩
      refine ⟨squaredBias_le_one (hp k).1 (hp k).2.1, ?_⟩
      intro h
      have h' := (parityFactor_eq_bias (p k) 0).mp (by simp [parityFactor, h])
      exact h'.elim h0.ne' (fun e => e.elim h1.ne zero_ne_one)
  have hfactor (p : ℝ) (a : ZMod 2) :
      parityFactor p a = (if a = 1 then squaredBias p else 1) := by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) a with rfl | rfl <;>
      simp [parityFactor]
  have hsplit (x : L → ZMod 2) : (∏ j : L, diffMass (q j) (x j)) =
      (∏ j : P, mass j (x (split (.inl j)))) * weight (fun j => x (split (.inr j))) := by
    unfold mass weight
    rw [← Fintype.prod_sum_type (fun j : P ⊕ F => diffMass (q (split j)) (x (split j)))]
    exact Fintype.prod_equiv split.symm _ _ fun j => by rw [split.apply_symm_apply]
  simp only [hmass_strict, hbias_strict, and_imp] at hcom
  simp only [hmass_one] at hcom
  convert hcom using 2
  apply Finset.sum_congr rfl
  intro x _
  split
  · simp_rw [hsplit, hfactor]
    ring
  · rfl

set_option maxHeartbeats 800000 in
-- The conversion compares finite sums on a dependent subtype of active columns.
open Classical in
private theorem balancing_eq_iff {U V P F : Type*}
    [Fintype U] [DecidableEq U] [Fintype V] [Fintype P]
    (A : Matrix U V (ZMod 2)) (p : U → ℝ) (q : V → ℝ) (i : U)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (hpi : p i ≠ 1 / 2)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j ≤ 1)
    (split : P ⊕ F ≃ {j : V // 0 < q j ∧ q j < 1}) :
    let L := {j : V // 0 < q j ∧ q j < 1}
    let active : Matrix U L (ZMod 2) := fun k j => A k j
    let T := {k : U // k = i ∨ p k = 1 / 2}
    let C : Matrix T L (ZMod 2) := fun k j => A k j
    let t : T := ⟨i, Or.inl rfl⟩
    let other := Finset.univ.filter fun k => k ≠ i ∧ p k ≠ 1 / 2
    let S := Submodule.span (ZMod 2) (Set.range fun k : {t' : T // t' ≠ t} => C k.val)
    let drop := puritySum A p q - puritySum A (Function.update p i (1 / 2)) q
    LinearIndependent (ZMod 2) (fun j : P => C.col (split (.inl j))) →
    Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col) →
    0 < drop →
    ((drop = squaredBias (p i) * ((∏ k ∈ other, squaredBias (p k)) *
        ∏ j : P, 2 * q (split (.inl j)) * (1 - q (split (.inl j))))) ↔
      (∀ j : P, q (split (.inl j)) ≠ 1 / 2 → Pi.single (split (.inl j)) 1 - C t ∈ S) ∧
      (∀ k : U, k ∈ other → 0 < p k → p k < 1 → active k - C t ∈ S)) := by
  intro L active T C t other S drop hlin hspan hdrop
  let target : T → ZMod 2 := fun k => if k.val = i then 1 else 0
  have htarget : target = Pi.single t 1 := by
    funext k
    by_cases hki : k.val = i
    · have ht : k = t := Subtype.ext hki
      rw [ht]
      change (if t.val = i then 1 else 0) = _
      simp only [show t.val = i from rfl, ite_true, Pi.single_eq_same]
    · have ht : k ≠ t := fun h => hki (congrArg Subtype.val h)
      simp [target, hki, Pi.single_eq_of_ne ht]
  obtain ⟨hsol, _⟩ := balancing_difference_ge_fiber A p q i hp0 hp1 hq0 hq1 hdrop
  change ∃ x, C *ᵥ x = target at hsol
  rw [htarget] at hsol
  let rows : Matrix {k // k ∈ other} L (ZMod 2) := fun k j => active k j
  have hbias (k : {k // k ∈ other}) : p k ≠ 1 / 2 :=
    (Finset.mem_filter.mp k.property).2.2
  have hcore := normalized_fiber_eq_iff C t split hlin hspan hsol
    (fun j : L => q j) (fun j => j.property) (fun k : {k // k ∈ other} => p k)
    (fun k => ⟨hp0 k, hp1 k, hbias k⟩) rows
  have hsum : drop = squaredBias (p i) * ∑ w : L → ZMod 2,
      if C *ᵥ w = target then (∏ j : L, diffMass (q j) (w j)) *
        ∏ k ∈ other, parityFactor (p k) ((active *ᵥ w) k) else 0 := by
    exact difference_eq_weighted_fiber A p q i hq0 hq1
  have hsum' : drop = squaredBias (p i) * ∑ w : L → ZMod 2,
      if C *ᵥ w = Pi.single t 1 then (∏ j : L, diffMass (q j) (w j)) *
        ∏ k : {k // k ∈ other}, parityFactor (p k) (rows k ⬝ᵥ w) else 0 := by
    rw [hsum, htarget]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    split
    · congr 1
      change (∏ k ∈ other, parityFactor (p k) ((active *ᵥ w) k)) =
        ∏ k : {k // k ∈ other}, parityFactor (p k) ((active *ᵥ w) k)
      exact Finset.prod_subtype other (fun _ => Iff.rfl) _
    · rfl
  have hnz : squaredBias (p i) ≠ 0 :=
    (sq_pos_of_ne_zero (fun h => hpi (by linarith))).ne'
  rw [hsum', mul_right_inj' hnz, mul_comm (∏ k ∈ other, _)]
  have hprod :
      (∏ k : {k // k ∈ other}, squaredBias (p k)) = ∏ k ∈ other, squaredBias (p k) := by
    exact (Finset.prod_subtype other (fun _ => Iff.rfl) (fun k => squaredBias (p k))).symm
  rw [hprod] at hcore
  change _ ↔ _ ∧ _
  convert hcore using 2
  · apply Finset.sum_congr
    · ext w
      simp only [Finset.mem_univ]
    · intro w _
      by_cases hw : C *ᵥ w = Pi.single t 1 <;> simp [hw]
  · constructor
    · exact fun h k => h k k.property
    · exact fun h k hk => h ⟨k, hk⟩

set_option maxHeartbeats 1000000 in
-- The physical marginal has two cut matrices with dependent row and column types.
open Classical in
theorem orderedMarginal_purity_drop_eq_iff {ι P F : Type*} [LinearOrder ι] [Fintype ι] [Fintype P]
    {m n : ℕ} {I : Set ι} (left : (Fin m × Bool) ↪ I) (right : (Fin n × Bool) ↪ ↥(Iᶜ))
    (hl : ∀ k, (left (k, false) : ι) < left (k, true))
    (hr : ∀ j, (right (j, false) : ι) < right (j, true))
    (before after : Fin (m + n) → Bool → ℂ) (p : Fin m → ℝ) (q : Fin n → ℝ) (i : Fin m)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1) (hpi : p i ≠ 1 / 2)
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
    let S := Submodule.span (ZMod 2) (Set.range fun k : {t' : T // t' ≠ t} => C k.val)
    let purity (weight : Fin (m + n) → Bool → ℂ) :=
      let B := orderedCut I (cutPairOrbitals left right weight)
      (((B * Bᴴ) ^ 2).trace).re
    let drop := purity before - purity after
    LinearIndependent (ZMod 2) (fun j : P => C.col (split (.inl j))) →
    Submodule.span (ZMod 2) (Set.range fun j : P => C.col (split (.inl j))) =
      Submodule.span (ZMod 2) (Set.range C.col) →
    0 < drop →
    ((drop = squaredBias (p i) * ((∏ k ∈ other, squaredBias (p k)) *
        ∏ j : P, 2 * q (split (.inl j)) * (1 - q (split (.inl j))))) ↔
      (∀ j : P, q (split (.inl j)) ≠ 1 / 2 → Pi.single (split (.inl j)) 1 - C t ∈ S) ∧
      (∀ k : Fin m, k ∈ other → 0 < p k → p k < 1 → active k - C t ∈ S)) := by
  intro A L active T C t other S purity drop hlin hspan hdrop
  have hbefore : purity before = puritySum A p q :=
    marginal_eq_real left right hl hr before p q hp hq
  have hafter : purity after = puritySum A (Function.update p i (1 / 2)) q :=
    marginal_eq_real left right hl hr after _ q hp' hq'
  have hvalue : drop = puritySum A p q - puritySum A (Function.update p i (1 / 2)) q := by
    change purity before - purity after = _
    rw [hbefore, hafter]
  rw [hvalue] at hdrop ⊢
  have h := balancing_eq_iff A p q i hp0 hp1 hpi hq0 hq1 split hlin hspan hdrop
  have hinst :
      @Subtype.instDecidableEq (Fin n) (fun j => 0 < q j ∧ q j < 1)
        (fun k l => Classical.propDecidable (k = l)) =
      @Subtype.instDecidableEq (Fin n) (fun j => 0 < q j ∧ q j < 1)
        (instDecidableEqFin n) :=
    Subsingleton.elim _ _
  have hsingle (j : P) :
      @Pi.single L (fun _ => ZMod 2) _ (@Subtype.instDecidableEq (Fin n) _
        (fun k l => Classical.propDecidable (k = l))) (split (.inl j)) 1 =
      Pi.single (split (.inl j)) 1 := by
    rw [hinst]
  simp only [hsingle] at h
  exact h

end D5.S3.Quantum.Fermionic.OrderedSlaterPurityDropEquality
