/- GID: D5/S3/Combinatorics/Matroids/IntegralLinkRestriction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Matroids/IntegralLinkRestriction
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Integral lifting for signed matroid link restriction. -/

module

public import D5.S3.Combinatorics.Matroids.CircuitCycleDecomposition

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset
open scoped Matroid

namespace D5.S3.Combinatorics.Matroids.IntegralLinkRestriction

open OrderedCycleFactorization
open CircuitCycleDecomposition (topCycles CircuitThrough circuit_cycle_decomposition)
open D5.S3.HomologicalAlgebra.OrderedFaceSign (insertionSign)

variable {V : Type*} [LinearOrder V]

/-- Remove the first block in an oriented join with the face on the contracted vertices. -/
def linkRestrict (A : Finset V) (z : Chain V) : Chain V :=
  fun T => if Disjoint T A then shuffleSign A T * z (T ∪ A) else 0

private lemma singleton_restrict (x : V) (z : Chain V) (T : Finset V) :
    linkRestrict {x} z T = if x ∈ T then 0 else insertionSign T x * z (insert x T) := by
  simp [linkRestrict, shuffleSign, insertionSign, Finset.disjoint_singleton_right]

variable [Fintype V]

private lemma linkRestrict_cycle {M : Matroid V} {A : Finset V}
    (hA : M.Indep (A : Set V)) {z : Chain V} (hz : TopCycle M z) :
    TopCycle (M ／ (A : Set V)) (linkRestrict A z) := by
  refine ⟨fun T hT => ?_, fun S => ?_⟩
  · unfold linkRestrict
    split
    · rename_i hd
      rw [hz.vanishes, mul_zero]
      exact fun hb => hT ((contract_base_iff hA.isBasis_self hd).2 hb)
    · rfl
  by_cases hs : Disjoint S A
  · have hSA : (S ∪ A) ∩ A = A := by simp
    have hSS : (S ∪ A) \ A = S := by
      simp [union_sdiff_distrib, Finset.sdiff_eq_self_iff_disjoint.mpr hs]
    have hsum :
        boundaryOn univ (linkRestrict A z) S =
          (shuffleSign A S * (-1) ^ A.card) * boundaryOn univ z (S ∪ A) := by
      unfold boundaryOn
      rw [mul_sum]
      have hsub : univ \ (S ∪ A) ⊆ (univ : Finset V) \ S :=
        by
          intro y hy
          exact mem_sdiff.mpr ⟨mem_univ _, fun hm => (mem_sdiff.mp hy).2 (mem_union_left _ hm)⟩
      rw [← sum_subset hsub (f := fun y =>
        insertionSign S y * linkRestrict A z (insert y S))]
      · apply sum_congr rfl
        intro y hy
        have hyA : y ∉ A := fun hm => (mem_sdiff.mp hy).2 (mem_union_right _ hm)
        have hd : Disjoint (insert y S) A := disjoint_insert_left.mpr ⟨hyA, hs⟩
        have hsign := right_insertion_sign (S ∪ A) A (mem_sdiff.mp hy).2
        rw [hSA, hSS] at hsign
        have hs₁ : insertionSign S y * insertionSign S y = 1 := sign_sq _
        have hs₂ : insertionSign (S ∪ A) y * insertionSign (S ∪ A) y = 1 := sign_sq _
        have htransport :
            insertionSign S y * shuffleSign A (insert y S) =
              shuffleSign A S * (-1) ^ A.card * insertionSign (S ∪ A) y := by
          calc
            _ = (insertionSign (S ∪ A) y * insertionSign (S ∪ A) y) *
                (insertionSign S y * shuffleSign A (insert y S)) := by rw [hs₂, one_mul]
            _ = (insertionSign (S ∪ A) y * shuffleSign A (insert y S)) *
                (insertionSign S y * insertionSign (S ∪ A) y) := by ring
            _ = (insertionSign S y * insertionSign S y) *
                (shuffleSign A S * (-1) ^ A.card * insertionSign (S ∪ A) y) := by
                  rw [hsign]
                  ring
            _ = _ := by rw [hs₁, one_mul]
        rw [linkRestrict, ite_eq_left hd, insert_union, ← mul_assoc, htransport, mul_assoc]
      · intro y hy hyn
        have hyA : y ∈ A := by
          by_contra hn
          exact hyn (mem_sdiff.mpr ⟨mem_univ _, by simp [hn, (mem_sdiff.mp hy).2]⟩)
        have hd : ¬ Disjoint (insert y S) A :=
          fun hd => disjoint_left.mp hd (mem_insert_self _ _) hyA
        rw [linkRestrict, ite_eq_right hd, mul_zero]
    rw [hsum, hz.cycle, mul_zero]
  · apply sum_eq_zero
    intro y _
    rw [linkRestrict, ite_eq_right (fun hd => hs (hd.mono_left (subset_insert _ _))), mul_zero]

private abbrev lastOrder (x : V) : LinearOrder V :=
  LinearOrder.lift' (fun y => (toLex (if y = x then (1 : ℕ) else 0, y)))
    (fun _ _ h => congrArg (fun a => (ofLex a).2) h)

omit [Fintype V] in
private lemma last_lt_iff (x a b : V) :
    @LT.lt V (lastOrder x).toLT a b ↔
      (a ≠ x ∧ b = x) ∨ (a ≠ x ∧ b ≠ x ∧ a < b) := by
  change toLex (if a = x then (1 : ℕ) else 0, a) <
    toLex (if b = x then (1 : ℕ) else 0, b) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  by_cases ha : a = x <;> by_cases hb : b = x <;> simp_all

omit [Fintype V] in
private lemma passive_insert_last {M : Matroid V} {x : V}
    (hx : M.IsNonloop x) (hc : ¬ M.IsColoop x) {B : Finset V}
    (hB : @PassiveBase V (lastOrder x) (M ／ ({x} : Set V)) B) :
    @PassiveBase V (lastOrder x) M (insert x B) := by
  have hxB : x ∉ B := fun hm => (hB.1.subset_ground hm).2 (Set.mem_singleton _)
  have hbase := (hx.indep.contract_isBase_iff.1 hB.1).1
  have hbase' : M.IsBase (↑(insert x B) : Set V) := by
    simpa only [Finset.coe_insert, Set.union_singleton, Set.union_comm] using hbase
  refine ⟨hbase', fun a ha => ?_⟩
  rcases mem_insert.mp ha with he | ha
  · subst a
    rw [Matroid.isColoop_iff_forall_mem_isBase] at hc
    push Not at hc
    obtain ⟨C, hC, hxC⟩ := hc
    obtain ⟨y, ⟨_, hy⟩, h⟩ :=
      hbase'.exchange_mem hC (show x ∈ (↑(insert x B) : Set V) from mem_insert_self _ _) hxC
    have hyx : y ≠ x := fun he => hy (he ▸ mem_insert_self _ _)
    refine ⟨y, hy, (last_lt_iff x y x).2 (Or.inl ⟨hyx, rfl⟩), ?_⟩
    simpa only [Finset.coe_insert, Finset.coe_erase, Set.insert_sdiff_of_mem (B : Set V) (Set.mem_singleton x),
      Set.sdiff_singleton_eq_self (show x ∉ (B : Set V) from hxB)] using h
  · obtain ⟨y, hyB, hya, hy⟩ := hB.2 a ha
    simp only [Finset.coe_insert, Finset.coe_erase] at hy ⊢
    have hyx : y ≠ x := fun he => (hy.subset_ground (Set.mem_insert _ _)).2 he
    have hax : a ≠ x := fun he => hxB (he ▸ ha)
    refine ⟨y, by simp [hyx, hyB], hya, ?_⟩
    rw [Set.insert_sdiff_of_notMem (B : Set V) (show x ∉ ({a} : Set V) by simp [Ne.symm hax]),
      Set.insert_comm]
    simpa only [Set.union_singleton] using
      (hx.indep.contract_isBase_iff.1 hy).1

private def moveSign (x : V) (F : Finset V) : ℤ :=
  if x ∈ F then (-1) ^ (F.filter (x < ·)).card else 1

omit [Fintype V] in
private lemma moveSign_sq (x : V) (F : Finset V) :
    moveSign x F * moveSign x F = 1 := by
  unfold moveSign
  split
  · exact sign_sq _
  · simp

private def reorient (x : V) (z : Chain V) : Chain V :=
  fun F => moveSign x F * z F

omit [Fintype V] in
private lemma last_filter_ne (x y : V) (R : Finset V) (hyx : y ≠ x) :
    @Finset.filter V (fun a => @LT.lt V (lastOrder x).toLT a y) ((lastOrder x).toDecidableLT · y) R =
      (R.erase x).filter (· < y) := by
  ext a
  simp [last_lt_iff, hyx, and_comm, and_left_comm, and_assoc]

omit [Fintype V] in
private lemma last_filter_self (x : V) (R : Finset V) (hx : x ∉ R) :
    @Finset.filter V (fun a => @LT.lt V (lastOrder x).toLT a x) ((lastOrder x).toDecidableLT · x) R = R := by
  ext a
  have ha (hm : a ∈ R) : a ≠ x := fun he => hx (he ▸ hm)
  simp only [mem_filter, last_lt_iff]
  exact ⟨And.left, fun h => ⟨h, Or.inl ⟨ha h, trivial⟩⟩⟩

omit [Fintype V] in
private lemma moveSign_insert_self (x : V) (R : Finset V) (hx : x ∉ R) :
    @insertionSign V (lastOrder x) R x =
      insertionSign R x * moveSign x (insert x R) := by
  have hpart :
      (R.filter (· < x)).card + (R.filter (x < ·)).card = R.card := by
    rw [← card_union_of_disjoint]
    · congr 1
      ext a
      by_cases ha : a ∈ R
      · rcases lt_or_gt_of_ne (show a ≠ x from fun h => hx (h ▸ ha)) with h | h
        · simp [ha, h]
        · simp [ha, h]
      · simp [ha]
    · exact disjoint_left.mpr fun a ha hb => (mem_filter.mp ha).2.not_gt (mem_filter.mp hb).2
  unfold insertionSign moveSign
  rw [last_filter_self x R hx, ite_eq_left (mem_insert_self _ _), filter_insert, ite_eq_right (lt_irrefl x),
    ← hpart, pow_add]

omit [Fintype V] in
private lemma moveSign_incidence (x y : V) (R : Finset V) (hy : y ∉ R) :
    @insertionSign V (lastOrder x) R y * moveSign x (insert y R) =
      moveSign x R * insertionSign R y := by
  by_cases hyx : y = x
  · subst y
    rw [moveSign_insert_self x R hy, mul_assoc, moveSign_sq, mul_one, moveSign, ite_eq_right hy, one_mul]
  by_cases hx : x ∈ R
  · have hxi : x ∈ insert y R := mem_insert_of_mem hx
    unfold insertionSign moveSign
    rw [last_filter_ne x y R hyx, ite_eq_left hx, ite_eq_left hxi, filter_insert]
    by_cases hxy : x < y
    · have hfilter : R.filter (· < y) = insert x ((R.erase x).filter (· < y)) := by
        conv_lhs => rw [← insert_erase hx, filter_insert, ite_eq_left hxy]
      rw [ite_eq_left hxy, card_insert_of_notMem (fun h => hy (mem_filter.mp h).1),
        hfilter, card_insert_of_notMem (by simp), pow_succ, pow_succ]
      ring
    · rw [ite_eq_right hxy, filter_erase, erase_eq_of_notMem (by simp [hxy])]
      ring
  · have hxi : x ∉ insert y R := by simp [Ne.symm hyx, hx]
    unfold insertionSign moveSign
    rw [last_filter_ne x y R hyx, erase_eq_of_notMem hx, ite_eq_right hx, ite_eq_right hxi,
      mul_one, one_mul]

private lemma boundary_reorient (x : V) (z : Chain V) (R : Finset V) :
    @boundaryOn V (lastOrder x) univ (reorient x z) R =
      moveSign x R * boundaryOn univ z R := by
  unfold boundaryOn
  rw [mul_sum]
  apply sum_congr (show _ = _ by ext y; simp)
  intro y hy
  have hyn : y ∉ R := by simpa using hy
  have hi : (letI : DecidableEq V := (lastOrder x).toDecidableEq; insert y R) = insert y R := by
    ext a
    simp
  rw [hi, reorient, ← mul_assoc, moveSign_incidence x y R hyn, mul_assoc]

private lemma topCycle_of_reorient (M : Matroid V) (x : V) (z : Chain V)
    (hz : @TopCycle V (lastOrder x) _ M (reorient x z)) : TopCycle M z := by
  have hu (F : Finset V) : moveSign x F ≠ 0 := left_ne_zero_of_mul (by
    rw [moveSign_sq]
    exact one_ne_zero)
  refine ⟨fun F hF => ?_, fun R => ?_⟩
  · exact (mul_eq_zero.mp (@TopCycle.vanishes V (lastOrder x) _ M _ hz F hF)).resolve_left (hu F)
  · have h := (boundary_reorient x z R).symm.trans (@TopCycle.cycle V (lastOrder x) _ M _ hz R)
    exact (mul_eq_zero.mp h).resolve_left (hu R)

omit [Fintype V] in
private lemma reorient_involutive (x : V) (z : Chain V) :
    reorient x (reorient x z) = z := by
  funext F
  simp only [reorient, ← mul_assoc, moveSign_sq, one_mul]

omit [Fintype V] in
private lemma passive_contraction_order {M : Matroid V} {x : V} {B : Finset V}
    (hB : PassiveBase (M ／ ({x} : Set V)) B) :
    @PassiveBase V (lastOrder x) (M ／ ({x} : Set V)) B := by
  refine ⟨hB.1, fun a ha => ?_⟩
  obtain ⟨y, hyB, hylt, hy⟩ := hB.2 a ha
  have ha' : a ≠ x := fun h => (hB.1.subset_ground ha).2 h
  have hy' : y ≠ x := fun h => (hy.subset_ground
    (show y ∈ (↑(insert y (B.erase a)) : Set V) from mem_insert_self _ _)).2 h
  refine ⟨y, hyB, (last_lt_iff x y a).2 (Or.inr ⟨hy', ha', hylt⟩), ?_⟩
  simpa only [Finset.coe_insert, Finset.coe_erase] using hy

/-- Every integral top cycle of a singleton contraction lifts along signed link restriction
when the contracted vertex is a nonloop and a noncoloop. -/
theorem exists_topCycle_linkRestrict_singleton {M : Matroid V} {x : V}
    (hx : M.IsNonloop x) (hc : ¬ M.IsColoop x) {w : Chain V}
    (hw : TopCycle (M ／ ({x} : Set V)) w) :
    ∃ z : Chain V, TopCycle M z ∧ linkRestrict {x} z = w := by
  classical
  let B : Finset (Finset V) := univ.filter (PassiveBase (M ／ ({x} : Set V)))
  have hnormalized (T : B) :
      ∃ z, @Normalized V (lastOrder x) _ M (insert x T.val) z :=
    (@normalized_factorization V (lastOrder x) _ M (insert x T.val)
      (passive_insert_last hx hc (passive_contraction_order (mem_filter.mp T.property).2))).1.exists
  choose z hz using hnormalized
  let Z : topCycles M := ∑ T : B, (w T.val * @insertionSign V (lastOrder x) T.val x) •
    (⟨reorient x (z T), topCycle_of_reorient M x _
      (by rw [reorient_involutive]; exact @Normalized.toTopCycle V (lastOrder x) _ M _ _ (hz T))⟩ : topCycles M)
  have hZ : TopCycle M Z.val := Z.property
  refine ⟨Z.val, hZ, topCycle_ext (linkRestrict_cycle (by simpa using hx.indep) hZ)
    (by simpa using hw) fun T hT => ?_⟩
  have hT' : PassiveBase (M ／ ({x} : Set V)) T := by simpa using hT
  have hxT : x ∉ T := fun hm => (hT'.1.subset_ground hm).2 (Set.mem_singleton _)
  let i : B := ⟨T, mem_filter.mpr ⟨mem_univ _, hT'⟩⟩
  rw [singleton_restrict, ite_eq_right hxT]
  simp only [Z, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    zsmul_eq_mul]
  change insertionSign T x * (∑ j : B, (w j.val * @insertionSign V (lastOrder x) j.val x) *
    reorient x (z j) (insert x T)) = w T
  rw [Fintype.sum_eq_single i]
  · rw [reorient, (@Normalized.coordinate V (lastOrder x) _ M _ _ (hz i)) _ (passive_insert_last hx hc (passive_contraction_order hT')),
      ite_eq_left (show insert x T = insert x i.val from rfl), mul_one]
    change insertionSign T x * ((w T * @insertionSign V (lastOrder x) T x) *
      moveSign x (insert x T)) = w T
    rw [moveSign_insert_self x T hxT]
    calc
      _ = (insertionSign T x * insertionSign T x) *
            (moveSign x (insert x T) * moveSign x (insert x T)) * w T := by ring
      _ = _ := by rw [show insertionSign T x * insertionSign T x = 1 from sign_sq _,
        moveSign_sq, one_mul, one_mul]
  · intro j hji
    have hxj : x ∉ j.val := fun hm => ((mem_filter.mp j.property).2.1.subset_ground hm).2
      (Set.mem_singleton _)
    have hne : insert x T ≠ insert x j.val := by
      intro he
      apply hji
      exact Subtype.ext (show j.val = i.val from by
        change j.val = T
        simpa only [erase_insert hxT, erase_insert hxj] using
          congrArg (fun F => F.erase x) he.symm)
    rw [reorient, (@Normalized.coordinate V (lastOrder x) _ M _ _ (hz j)) _ (passive_insert_last hx hc (passive_contraction_order hT')),
      ite_eq_right hne, mul_zero, mul_zero]


omit [Fintype V] in
private lemma singleton_then_link (x : V) (A : Finset V) (hx : x ∉ A) (z : Chain V) :
    linkRestrict A (linkRestrict {x} z) =
      fun T => insertionSign A x * linkRestrict (insert x A) z T := by
  funext T
  by_cases hd : Disjoint T A
  · by_cases hxT : x ∈ T
    · have hn : ¬ Disjoint T (insert x A) :=
        fun h => disjoint_left.mp h hxT (mem_insert_self _ _)
      simp [linkRestrict, hd, hn, hxT]
    · have hd' : Disjoint T (insert x A) := disjoint_insert_right.mpr ⟨hxT, hd⟩
      have hi : x ∉ T ∪ A := by simp [hxT, hx]
      have he : T ∪ insert x A = insert x (T ∪ A) := union_insert _ _ _
      have hf : insertionSign (T ∪ A) x = insertionSign T x * insertionSign A x := by
        unfold insertionSign
        rw [filter_union, card_union_of_disjoint
          (hd.mono (filter_subset _ _) (filter_subset _ _)), pow_add]
      have hs : shuffleSign (insert x A) T = insertionSign T x * shuffleSign A T := by
        unfold shuffleSign insertionSign
        rw [sum_insert hx, pow_add]
      conv_lhs => rw [linkRestrict, ite_eq_left hd, singleton_restrict, ite_eq_right hi, hf]
      rw [linkRestrict, ite_eq_left hd', he, hs]
      ring
  · have hd' : ¬ Disjoint T (insert x A) :=
      fun h => hd (h.mono_right (subset_insert _ _))
    simp [linkRestrict, hd, hd']

/-- Signed restriction to the link of an independent face maps integral top cycles onto
all integral top cycles of the contraction if the face contains no coloop. -/
private theorem exists_topCycle_linkRestrict_iff {M : Matroid V} {A : Finset V}
    (hA : M.Indep (A : Set V)) (hc : ∀ x ∈ A, ¬ M.IsColoop x) (w : Chain V) :
    (∃ z : Chain V, TopCycle M z ∧ linkRestrict A z = w) ↔
      TopCycle (M ／ (A : Set V)) w := by
  classical
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact linkRestrict_cycle hA hz
  induction A using Finset.induction_on generalizing M w with
  | empty =>
      intro hw
      refine ⟨w, ?_, ?_⟩
      · simpa using hw
      · funext T
        simp [linkRestrict, shuffleSign]
  | insert x A hx ih =>
      intro hw
      have hxI : M.Indep ({x} : Set V) := hA.subset (by simp)
      have hxN : M.IsNonloop x := hxI.isNonloop_of_mem (Set.mem_singleton _)
      have hxc : ¬ M.IsColoop x := hc x (mem_insert_self _ _)
      have hA' : (M ／ ({x} : Set V)).Indep (A : Set V) := by
        apply hxI.contract_indep_iff.2
        refine ⟨Set.disjoint_singleton_right.mpr hx, ?_⟩
        simpa only [Finset.coe_insert, Set.union_singleton] using hA
      have hc' : ∀ y ∈ A, ¬ (M ／ ({x} : Set V)).IsColoop y := by
        intro y hy hcol
        exact hc y (mem_insert_of_mem hy) (Matroid.contract_isColoop_iff.1 hcol).1
      have hminor : M ／ ({x} : Set V) ／ (A : Set V) =
          M ／ (↑(insert x A) : Set V) := by
        rw [Matroid.contract_contract, Finset.coe_insert, Set.singleton_union]
      have hw' : TopCycle (M ／ ({x} : Set V) ／ (A : Set V))
          (insertionSign A x • w) :=
        (topCycles _).smul_mem _ (hminor.symm ▸ hw)
      obtain ⟨v, hv, hvr⟩ := ih hA' hc' _ hw'
      obtain ⟨z, hz, hzr⟩ := exists_topCycle_linkRestrict_singleton hxN hxc hv
      refine ⟨z, hz, funext fun T => ?_⟩
      have he := congrFun ((singleton_then_link x A hx z).symm.trans
        (by rw [hzr, hvr])) T
      exact mul_left_cancel₀ (insertionSign_ne_zero A x) he

/-- A coloop annihilates the entire integral top-cycle lattice. -/
lemma topCycle_eq_zero_of_isColoop {M : Matroid V} {x : V}
    (hx : M.IsColoop x) {z : Chain V} (hz : TopCycle M z) : z = 0 := by
  obtain ⟨e, _, _⟩ := circuit_cycle_decomposition M x hx.mem_ground
  have : IsEmpty (CircuitThrough M x) :=
    ⟨fun C => C.property.1.not_isColoop_of_mem C.property.2 hx⟩
  have he : e (⟨z, hz⟩ : topCycles M) = e 0 := by
    funext C
    exact isEmptyElim C
  exact congrArg Subtype.val (e.injective he)

/-- The integral image of signed restriction to the link of an independent face.
A coloop in the contracted face forces the image to be zero. -/
theorem exists_topCycle_linkRestrict_iff_coloop {M : Matroid V} {A : Finset V}
    (hA : M.Indep (A : Set V)) (w : Chain V) :
    (∃ z : Chain V, TopCycle M z ∧ linkRestrict A z = w) ↔
      TopCycle (M ／ (A : Set V)) w ∧ ((∃ x ∈ A, M.IsColoop x) → w = 0) := by
  have hzero : linkRestrict A (0 : Chain V) = 0 := by
    funext T
    simp [linkRestrict]
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨linkRestrict_cycle hA hz, ?_⟩
    rintro ⟨x, _, hx⟩
    rw [topCycle_eq_zero_of_isColoop hx hz, hzero]
  · rintro ⟨hw, h⟩
    by_cases hc : ∃ x ∈ A, M.IsColoop x
    · exact ⟨0, (topCycles M).zero_mem, hzero.trans (h hc).symm⟩
    · exact (exists_topCycle_linkRestrict_iff hA
        (fun x hx hcol => hc ⟨x, hx, hcol⟩) w).2 hw

end D5.S3.Combinatorics.Matroids.IntegralLinkRestriction
