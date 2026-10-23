/- GID: D5/S3/Combinatorics/Partitions/TernaryPartitionCounting
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/TernaryPartitionCounting
   mirror-E: none(waiver:structural-counting-foundation)
   anchors: []
   utility: none
   digest: Surjective merger transport and arbitrary-weight four-party ternary partition counting. -/

import D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Setoid.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Basic.Real.Basic
import Lean.Elab.Tactic.Decide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Partitions.TernaryPartitionCounting

/-!
Admission basis: escape-witness. The arbitrary-index merger transport uses the
same-delivery ternary orbit classification to construct quotient colourings,
reanchor at an arbitrary chosen target anchor, and select unique representatives.
Its consumer merger_sum_upperSum feeds result; result is consumed by the original
StabilizerMultiEntropyCollapse.partition_count. No source-anchor preservation
hypothesis is imposed. Arbitrary additive commutative monoids are retained for
merger_sum_transport; result permits arbitrary real weights and opposite-pair
representatives in each arity.
The repository search reuses the existing private structural proof and pinned
Mathlib setoid kernels, finite pigeonhole, finite sums and finite orders. The
fifteen-partition audit is a consumed normalization auxiliary, not a standalone
finite-instance result or a general partition coefficient formula.
Structural helper judgement (all are consumed on the existing result path):
  partition: proof_shape: bind-only; consumer: partition_eq_iff, representative_injOn.
  partition_eq_iff: proof_shape: bind-only; consumer: representative_injOn, pulled_partition_mem_image.
  representative_injOn: proof_shape: content (after helper expansion); consumer: representative_sum, pulled_representative_injOn.
  representative_sum: proof_shape: content (after helper expansion); consumer: full_sum_upperSum.
  four_party_partition_ne_bot: proof_shape: bind-only; consumer: partitionSupport_ne_bot.
  nonzero_partition_ne_top: proof_shape: bind-only; consumer: partitionSupport_ne_top.
  factor_through_merger: proof_shape: bind-only; consumer: compatible_partition_has_representative.
  compatible_partition_has_representative: proof_shape: content (after helper expansion); consumer: merger_sum_transport.
  pullPartition: proof_shape: bind-only; consumer: pulled_representative_injOn, pulled_partition_mem_image.
  pulled_representative_injOn: proof_shape: content (after helper expansion); consumer: merger_sum_transport.
  pulled_partition_mem_image: proof_shape: content (after helper expansion); consumer: merger_sum_transport.
  merger_sum_transport: proof_shape: content (after helper expansion); consumer: merger_sum_upperSum.
  relation: proof_shape: bind-only; consumer: Valid, FourPartition.
  Valid: proof_shape: bind-only; consumer: FourPartition.
  FourPartition: proof_shape: bind-only; consumer: discrete, indiscrete.
  discrete: proof_shape: bind-only; consumer: coefficient_cancel, weighted_sum_expansion.
  indiscrete: proof_shape: bind-only; consumer: coefficient_cancel, weighted_sum_expansion.
  edgeCount: proof_shape: bind-only; consumer: coefficient, coefficient_cancel.
  coefficient: proof_shape: bind-only; consumer: catalogue_coefficient, coefficient_cancel.
  toSetoid: proof_shape: bind-only; consumer: to_from, from_to.
  code: proof_shape: bind-only; consumer: relation_code, fromSetoid.
  relation_code: proof_shape: bind-only; consumer: fromSetoid, to_from.
  fromSetoid: proof_shape: bind-only; consumer: to_from, from_to.
  to_from: proof_shape: bind-only; consumer: fromSetoid_le_iff.
  from_to: proof_shape: bind-only; consumer: encodePartition_surjective.
  toSetoid_le_iff: proof_shape: bind-only; consumer: fromSetoid_le_iff.
  fromSetoid_le_iff: proof_shape: bind-only; consumer: encodePartition_le_iff.
  catalogue: proof_shape: bind-only; consumer: catalogue_bijective, pairPartition.
  catalogue_bijective: proof_shape: bind-only; consumer: coefficient_cancel, weighted_sum_expansion.
  pairPartition: proof_shape: bind-only; consumer: weighted_sum_expansion, four_party_counting_identity.
  triplePartition: proof_shape: bind-only; consumer: weighted_sum_expansion, four_party_counting_identity.
  doublePartition: proof_shape: bind-only; consumer: weighted_sum_expansion, four_party_counting_identity.
  catalogue_coefficient: proof_shape: bind-only; consumer: weighted_sum_expansion.
  coefficient_cancel: proof_shape: bind-only; consumer: weighted_upper_sum_cancel.
  weighted_sum_expansion: proof_shape: bind-only; consumer: four_party_counting_identity.
  upperSum: proof_shape: bind-only; consumer: weighted_upper_sum_cancel, four_party_counting_identity.
  weighted_upper_sum_cancel: proof_shape: bind-only; consumer: four_party_counting_identity.
  four_party_counting_identity: proof_shape: bind-only; consumer: result.
  anchorEquiv: proof_shape: bind-only; consumer: colourValue2, colourValue3.
  colourValue2: proof_shape: bind-only; consumer: result.
  colourValue3: proof_shape: bind-only; consumer: result.
  colourValue4: proof_shape: bind-only; consumer: partitionSum_full_upperSum.
  mergeMap: proof_shape: bind-only; consumer: mergeMap_surjective, encoded_merger_kernel.
  mergeMap_surjective: proof_shape: bind-only; consumer: merger_sum_upperSum.
  pairMergers: proof_shape: bind-only; consumer: pairMergers_surjective, pairMergers_partition.
  singletonCuts: proof_shape: bind-only; consumer: singletonCuts_surjective, singletonCuts_partition.
  balancedCuts: proof_shape: bind-only; consumer: balancedCuts_surjective, balancedCuts_partition.
  pairMergers_surjective: proof_shape: bind-only; consumer: result.
  singletonCuts_surjective: proof_shape: bind-only; consumer: result.
  balancedCuts_surjective: proof_shape: bind-only; consumer: result.
  encodePartition: proof_shape: bind-only; consumer: encodePartition_le_iff, encodePartition_injective.
  encodePartition_le_iff: proof_shape: bind-only; consumer: encodePartition_injective, encodePartition_bot.
  encodePartition_injective: proof_shape: bind-only; consumer: partitionSupport_ne_bot, partitionSupport_ne_top.
  encodePartition_surjective: proof_shape: bind-only; consumer: encodePartition_bot, encodePartition_top.
  encodePartition_bot: proof_shape: bind-only; consumer: partitionSupport_ne_bot, full_sum_upperSum.
  encodePartition_top: proof_shape: bind-only; consumer: partitionSupport_ne_top.
  partitionSupport: proof_shape: bind-only; consumer: partitionSupport_ne_bot, partitionSupport_ne_top.
  partitionSupport_ne_bot: proof_shape: bind-only; consumer: result.
  partitionSupport_ne_top: proof_shape: bind-only; consumer: result.
  encoded_upperSum: proof_shape: bind-only; consumer: merger_sum_upperSum, full_sum_upperSum.
  encoded_merger_kernel: proof_shape: bind-only; consumer: merger_sum_upperSum.
  merger_sum_upperSum: proof_shape: content (after helper expansion); consumer: partitionSum_as_upperSum.
  full_sum_upperSum: proof_shape: content (after helper expansion); consumer: partitionSum_full_upperSum.
  separation: proof_shape: bind-only; consumer: separation_encoded, partitionSum_as_upperSum.
  separation_encoded: proof_shape: bind-only; consumer: partitionSum_as_upperSum, partitionSum_full_upperSum.
  pairMergers_partition: proof_shape: bind-only; consumer: result.
  singletonCuts_partition: proof_shape: bind-only; consumer: result.
  balancedCuts_partition: proof_shape: bind-only; consumer: result.
  partitionSumR: proof_shape: bind-only; consumer: partitionSum_as_upperSum, partitionSum_full_upperSum.
  partitionSum_as_upperSum: proof_shape: content (after helper expansion); consumer: result.
  partitionSum_full_upperSum: proof_shape: content (after helper expansion); consumer: result.
  result: proof_shape: content (after helper expansion); consumer: StabilizerMultiEntropyCollapse.partition_count.
  The content entries use the same-delivery arbitrary-index ternary partition
  classification on their live path; the remaining entries only organize,
  encode, or normalize that transport and the finite four-party coefficients.
  The local decidability, order and interval instances supply the catalogue
  and interval-sum proofs; they introduce no independent mathematical claim.
Utility: none. The delivered result is structural weighted transport. The finite
catalogue helpers only normalize the four-point coefficients on its live path.
The only project import is TernaryPartitionOrbit; no Quantum or Reg dependency.
-/

/-- The separation matrix of a ternary colouring of four labelled parties. -/
def cutPattern (v : Fin 4 → ZMod 3) : Matrix (Fin 4) (Fin 4) Bool :=
  ![![decide (v 0 ≠ v 0), decide (v 0 ≠ v 1), decide (v 0 ≠ v 2), decide (v 0 ≠ v 3)],
    ![decide (v 1 ≠ v 0), decide (v 1 ≠ v 1), decide (v 1 ≠ v 2), decide (v 1 ≠ v 3)],
    ![decide (v 2 ≠ v 0), decide (v 2 ≠ v 1), decide (v 2 ≠ v 2), decide (v 2 ≠ v 3)],
    ![decide (v 3 ≠ v 0), decide (v 3 ≠ v 1), decide (v 3 ≠ v 2), decide (v 3 ≠ v 3)]]

private lemma cutPattern_apply (v : Fin 4 → ZMod 3) (i j : Fin 4) :
    cutPattern v i j = decide (v i ≠ v j) := by
  rw [cutPattern.eq_1]
  fin_cases i <;> fin_cases j <;> rfl

def colourValue {q : ℕ} (t : Fin (q - 1) → ZMod 3) (c : Fin q) : ZMod 3 :=
  ∑ i : Fin (q - 1), t i * (if (i : ℕ) = (c : ℕ) then 1 else 0)

open Classical
open scoped BigOperators
open D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit

def partition {α : Type*} (u : α → ZMod 3) : Setoid (Option α) :=
  Setoid.ker (anchored u)

private theorem partition_eq_iff {α : Type*} (u v : α → ZMod 3) :
    partition u = partition v ↔ SamePartition (anchored u) (anchored v) := by
  constructor
  · intro h i j
    exact Iff.of_eq (congrArg (fun r : Setoid (Option α) => r i j) h)
  · intro h
    exact Setoid.ext h

-- This is the load-bearing use of the new affine/anchored theorem: the mode
-- image is a genuine partition set, with no multiplicities hidden by `image`.
private theorem representative_injOn {α : Type*}
    (P : Finset (α → ZMod 3)) (h0 : (0 : α → ZMod 3) ∉ P)
    (hP : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P)) :
    Set.InjOn partition (P : Set (α → ZMod 3)) := by
  intro u hu v hv huv
  have hu0 : u ≠ 0 := by
    intro h
    exact h0 (h ▸ hu)
  obtain ⟨w, _, hw⟩ := D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit.result (P : Set (α → ZMod 3)) hP u hu0
  have hu' : u ∈ P ∧ SamePartition (anchored u) (anchored u) :=
    ⟨hu, fun _ _ => Iff.rfl⟩
  have hv' : v ∈ P ∧ SamePartition (anchored u) (anchored v) :=
    ⟨hv, (partition_eq_iff u v).mp huv⟩
  exact (hw u hu').trans (hw v hv').symm

private theorem representative_sum {α A : Type*} [AddCommMonoid A]
    (P : Finset (α → ZMod 3)) (h0 : (0 : α → ZMod 3) ∉ P)
    (hP : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (f : Setoid (Option α) → A) :
    (∑ u ∈ P, f (partition u)) = ∑ Q ∈ P.image partition, f Q := by
  classical
  exact (Finset.sum_image (representative_injOn P h0 hP)).symm

-- No finite setoid enumeration is needed for this obstruction. It directly
-- reuses Mathlib's finite pigeonhole theorem, via `ker_eq_bot_iff`.
private theorem four_party_partition_ne_bot (u : Fin 3 → ZMod 3) :
    partition u ≠ ⊥ := by
  intro h
  have hinj : Function.Injective (anchored u) := Setoid.ker_eq_bot_iff.mp h
  have hcard := Fintype.card_le_of_injective (anchored u) hinj
  norm_num [Fintype.card_option] at hcard

private theorem nonzero_partition_ne_top {α : Type*} (u : α → ZMod 3) (hu : u ≠ 0) :
    partition u ≠ ⊤ := by
  intro h
  apply hu
  funext a
  have ha : anchored u (some a) = anchored u none := by
    change partition u (some a) none
    rw [h]
    trivial
  simpa [anchored] using ha

-- A merger's fibers are contained in the coloring partition exactly when that
-- coloring factors through the merger. The function is chosen on actual fibers;
-- surjectivity ensures every target label is represented.
private theorem factor_through_merger {α β : Type*}
    (m : Option α → Option β) (hm : Function.Surjective m)
    (u : α → ZMod 3) (hcompat : Setoid.ker m ≤ partition u) :
    ∃ g : Option β → ZMod 3, anchored u = g ∘ m := by
  classical
  let g : Option β → ZMod 3 := fun b => anchored u (Function.surjInv hm b)
  refine ⟨g, ?_⟩
  funext a
  apply hcompat
  exact (Function.rightInverse_surjInv hm (m a)).symm

-- Merger factorization followed by representative selection. This is the
-- surjectivity half of the merger-to-compatible-partitions sum transport.
private theorem compatible_partition_has_representative {α β : Type*}
    (P : Set (β → ZMod 3))
    (hP : ∀ v : β → ZMod 3, v ≠ 0 → (v ∈ P ↔ -v ∉ P))
    (m : Option α → Option β) (hm : Function.Surjective m)
    (u : α → ZMod 3) (hu : u ≠ 0)
    (hcompat : Setoid.ker m ≤ partition u) :
    ∃ v : β → ZMod 3,
      v ∈ P ∧ partition u = Setoid.ker (anchored v ∘ m) := by
  classical
  obtain ⟨g, hg⟩ := factor_through_merger m hm u hcompat
  let v : β → ZMod 3 := fun b => g (some b) - g none
  have hv : anchored v = fun b => g b - g none := by
    funext b
    cases b <;> simp [anchored, v]
  have hv0 : v ≠ 0 := by
    intro h
    have hgconst (b : Option β) : g b = g none := by
      apply sub_eq_zero.mp
      have hb : anchored v b = 0 := by rw [h]; cases b <;> rfl
      simpa only [hv] using hb
    apply hu
    funext a
    calc
      u a = g (m (some a)) := congrFun hg (some a)
      _ = g none := hgconst _
      _ = g (m none) := (hgconst _).symm
      _ = 0 := (congrFun hg none).symm
  obtain ⟨w, ⟨hw, hpart⟩, _⟩ := result P hP v hv0
  refine ⟨w, hw, Setoid.ext (fun i j => ?_)⟩
  change anchored u i = anchored u j ↔ anchored w (m i) = anchored w (m j)
  calc
    anchored u i = anchored u j ↔ g (m i) = g (m j) := by rw [hg]; rfl
    _ ↔ anchored v (m i) = anchored v (m j) := by rw [hv]; exact sub_left_inj.symm
    _ ↔ anchored w (m i) = anchored w (m j) := hpart (m i) (m j)

def pullPartition {α β : Type*} (m : Option α → Option β)
    (v : β → ZMod 3) : Setoid (Option α) :=
  Setoid.ker (anchored v ∘ m)

private theorem pulled_representative_injOn {α β : Type*}
    (P : Finset (β → ZMod 3)) (h0 : (0 : β → ZMod 3) ∉ P)
    (hP : ∀ v : β → ZMod 3, v ≠ 0 → (v ∈ P ↔ -v ∉ P))
    (m : Option α → Option β) (hm : Function.Surjective m) :
    Set.InjOn (pullPartition m) (P : Set (β → ZMod 3)) := by
  intro v hv w hw h
  apply representative_injOn P h0 hP hv hw
  apply Setoid.ext
  intro i j
  obtain ⟨a, rfl⟩ := hm i
  obtain ⟨b, rfl⟩ := hm j
  exact Iff.of_eq (congrArg (fun Q : Setoid (Option α) => Q a b) h)

private theorem pulled_partition_mem_image {α β : Type*}
    (P : Finset (α → ZMod 3))
    (hP : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (m : Option α → Option β) (hm : Function.Surjective m)
    (v : β → ZMod 3) (hv : v ≠ 0) :
    pullPartition m v ∈ P.image partition := by
  classical
  let u : α → ZMod 3 := fun a => anchored v (m (some a)) - anchored v (m none)
  have hu : anchored u = fun a => anchored v (m a) - anchored v (m none) := by
    funext a
    cases a <;> simp [anchored, u]
  have hu0 : u ≠ 0 := by
    intro h
    have hconstant (b : Option β) : anchored v b = anchored v (m none) := by
      obtain ⟨a, rfl⟩ := hm b
      apply sub_eq_zero.mp
      have ha : anchored u a = 0 := by rw [h]; cases a <;> rfl
      simpa only [hu] using ha
    apply hv
    funext b
    calc
      v b = anchored v (some b) := rfl
      _ = anchored v (m none) := hconstant _
      _ = anchored v none := (hconstant _).symm
      _ = 0 := rfl
  obtain ⟨w, ⟨hw, hpart⟩, _⟩ := result (P : Set (α → ZMod 3)) hP u hu0
  apply Finset.mem_image.mpr
  refine ⟨w, hw, ?_⟩
  calc
    partition w = partition u := ((partition_eq_iff u w).mpr hpart).symm
    _ = pullPartition m v := by
      apply Setoid.ext
      intro i j
      change anchored u i = anchored u j ↔ anchored v (m i) = anchored v (m j)
      rw [hu]
      exact sub_left_inj

-- The full finite transport: each merger sum counts each compatible coloring
-- partition once. Both directions consume representative selection, not a
-- 13-entry numerical enumeration.
theorem merger_sum_transport {α β A : Type*} [AddCommMonoid A]
    (Pα : Finset (α → ZMod 3)) (h0α : (0 : α → ZMod 3) ∉ Pα)
    (hPα : ∀ u : α → ZMod 3, u ≠ 0 → (u ∈ Pα ↔ -u ∉ Pα))
    (Pβ : Finset (β → ZMod 3)) (h0β : (0 : β → ZMod 3) ∉ Pβ)
    (hPβ : ∀ v : β → ZMod 3, v ≠ 0 → (v ∈ Pβ ↔ -v ∉ Pβ))
    (m : Option α → Option β) (hm : Function.Surjective m)
    (f : Setoid (Option α) → A) :
    (∑ v ∈ Pβ, f (pullPartition m v)) =
      ∑ Q ∈ (Pα.image partition).filter (fun Q => Setoid.ker m ≤ Q), f Q := by
  classical
  refine Finset.sum_bij (fun v _ => pullPartition m v) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro v hv
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply pulled_partition_mem_image Pα hPα m hm v
      intro h
      exact h0β (h ▸ hv)
    · intro i j hij
      change anchored v (m i) = anchored v (m j)
      exact congrArg (anchored v) hij
  · intro v hv w hw h
    exact pulled_representative_injOn Pβ h0β hPβ m hm hv hw h
  · intro Q hQ
    obtain ⟨hQ, hcompat⟩ := Finset.mem_filter.mp hQ
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hQ
    have hu0 : u ≠ 0 := by
      intro h
      exact h0α (h ▸ hu)
    obtain ⟨v, hv, heq⟩ := compatible_partition_has_representative
      (Pβ : Set (β → ZMod 3)) hPβ m hm u hu0 hcompat
    exact ⟨v, hv, heq.symm⟩

private def relation (c : Fin 6 → Bool) : Fin 4 → Fin 4 → Bool :=
  ![![true, c 0, c 1, c 2], ![c 0, true, c 3, c 4],
    ![c 1, c 3, true, c 5], ![c 2, c 4, c 5, true]]

private def Valid (c : Fin 6 → Bool) : Prop :=
  ∀ i j k : Fin 4,
    relation c i j = true → relation c j k = true → relation c i k = true

private abbrev FourPartition := {c : Fin 6 → Bool // Valid c}

private instance : DecidablePred Valid := fun c =>
  inferInstanceAs (Decidable (∀ i j k : Fin 4,
    relation c i j = true → relation c j k = true → relation c i k = true))

private instance : PartialOrder FourPartition where
  le c d := ∀ k : Fin 6, c.val k = true → d.val k = true
  le_refl _ _ h := h
  le_trans _ _ _ hcd hde k h := hde k (hcd k h)
  le_antisymm c d hcd hdc := by
    apply Subtype.ext
    funext k
    have hc := hcd k
    have hd := hdc k
    cases hck : c.val k <;> cases hdk : d.val k <;> simp_all

private instance : DecidableLE FourPartition := fun c d =>
  inferInstanceAs (Decidable (∀ k : Fin 6, c.val k = true → d.val k = true))

private instance : DecidableLT FourPartition := by
  intro c d
  by_cases hcd : c ≤ d
  · by_cases hdc : d ≤ c
    · exact isFalse (fun h => h.2 hdc)
    · exact isTrue ⟨hcd, hdc⟩
  · exact isFalse (fun h => hcd h.1)

private def discrete : FourPartition := ⟨fun _ => false, by decide⟩

private def indiscrete : FourPartition := ⟨fun _ => true, by decide⟩

private instance : BoundedOrder FourPartition where
  bot := discrete
  top := indiscrete
  bot_le c k h := by cases h
  le_top c k h := rfl

private instance : LocallyFiniteOrder FourPartition := Fintype.toLocallyFiniteOrder

private def edgeCount (c : FourPartition) : ℕ :=
  ∑ k : Fin 6, if c.val k then 1 else 0

private def coefficient (c : FourPartition) : ℤ :=
  match edgeCount c with
  | 0 => 1
  | 1 => -1
  | 2 => 1
  | 3 => 2
  | _ => -6

private def toSetoid (c : FourPartition) : Setoid (Fin 4) where
  r i j := relation c.val i j = true
  iseqv.refl i := by fin_cases i <;> rfl
  iseqv.symm := by
    intro i j h
    fin_cases i <;> fin_cases j <;> exact h
  iseqv.trans := fun {i j k} hij hjk => c.property i j k hij hjk

private noncomputable def code (Q : Setoid (Fin 4)) : Fin 6 → Bool := by
  classical
  exact ![decide (Q 0 1), decide (Q 0 2), decide (Q 0 3),
    decide (Q 1 2), decide (Q 1 3), decide (Q 2 3)]

private theorem relation_code (Q : Setoid (Fin 4)) (i j : Fin 4) :
    relation (code Q) i j = true ↔ Q i j := by
  classical
  fin_cases i <;> fin_cases j <;>
    simp [relation, code, Q.refl'] <;>
    constructor <;> intro h <;> exact Q.symm' h

private noncomputable def fromSetoid (Q : Setoid (Fin 4)) : FourPartition :=
  ⟨code Q, fun i j k hij hjk =>
    (relation_code Q i k).mpr
      (Q.trans' ((relation_code Q i j).mp hij) ((relation_code Q j k).mp hjk))⟩

private theorem to_from (Q : Setoid (Fin 4)) : toSetoid (fromSetoid Q) = Q := by
  apply Setoid.ext
  exact relation_code Q

private theorem from_to (c : FourPartition) : fromSetoid (toSetoid c) = c := by
  apply Subtype.ext
  funext k
  have hdecide : ∀ b : Bool, decide (b = true) = b := by
    intro b
    cases b <;> rfl
  fin_cases k
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 0 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 1 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 2 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 3 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 4 <;> unfold toSetoid <;> simp [relation, h]
  · simp [fromSetoid, code, hdecide]
    cases h : c.val 5 <;> unfold toSetoid <;> simp [relation, h]

private theorem toSetoid_le_iff (c d : FourPartition) :
    toSetoid c ≤ toSetoid d ↔ c ≤ d := by
  constructor
  · intro h k
    fin_cases k
    · exact @h 0 1
    · exact @h 0 2
    · exact @h 0 3
    · exact @h 1 2
    · exact @h 1 3
    · exact @h 2 3
  · intro h i j
    fin_cases i <;> fin_cases j <;>
      first | exact id | exact h 0 | exact h 1 | exact h 2 |
        exact h 3 | exact h 4 | exact h 5

private theorem fromSetoid_le_iff (Q R : Setoid (Fin 4)) :
    fromSetoid Q ≤ fromSetoid R ↔ Q ≤ R := by
  rw [← toSetoid_le_iff, to_from, to_from]

private def catalogue : Fin 15 → FourPartition :=
  ![discrete,
    ⟨![true, false, false, false, false, false], by decide⟩,
    ⟨![false, true, false, false, false, false], by decide⟩,
    ⟨![false, false, true, false, false, false], by decide⟩,
    ⟨![false, false, false, true, false, false], by decide⟩,
    ⟨![false, false, false, false, true, false], by decide⟩,
    ⟨![false, false, false, false, false, true], by decide⟩,
    ⟨![true, true, false, true, false, false], by decide⟩,
    ⟨![true, false, true, false, true, false], by decide⟩,
    ⟨![false, true, true, false, false, true], by decide⟩,
    ⟨![false, false, false, true, true, true], by decide⟩,
    ⟨![true, false, false, false, false, true], by decide⟩,
    ⟨![false, true, false, false, true, false], by decide⟩,
    ⟨![false, false, true, true, false, false], by decide⟩,
    indiscrete]

set_option maxHeartbeats 1000000 in
-- Kernel reduction checks the complete finite partition catalogue.
private theorem catalogue_bijective : Function.Bijective catalogue := by decide

private def pairPartition (k : Fin 6) : FourPartition := catalogue ⟨k.val + 1, by omega⟩
private def triplePartition (k : Fin 4) : FourPartition := catalogue ⟨k.val + 7, by omega⟩
private def doublePartition (k : Fin 3) : FourPartition := catalogue ⟨k.val + 11, by omega⟩

private theorem catalogue_coefficient : ∀ k : Fin 15,
    coefficient (catalogue k) =
      (![1, -1, -1, -1, -1, -1, -1, 2, 2, 2, 2, 1, 1, 1, -6] : Fin 15 → ℤ) k := by
  decide

-- The finite audit covers all fifteen equivalence relations.  We keep the
-- cancellation kernel-auditable by rewriting the finite sum through the
-- explicit catalogue and reducing the fifteen cases with `norm_num`.
set_option maxHeartbeats 4000000 in
-- Kernel reduction normalizes each of the fifteen interval sums.
set_option maxRecDepth 100000 in
private theorem coefficient_cancel (Q : FourPartition) (hQ : Q ≠ ⊥) :
    (∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, coefficient p) = 0 := by
  have hIcc : Finset.univ.filter (fun p : FourPartition => p ≤ Q) =
      Finset.Icc (⊥ : FourPartition) Q := by
    ext p
    simp
  have hfilter :
      (∑ p : FourPartition, if p ≤ Q then coefficient p else 0) =
        ∑ j : Fin 15, if catalogue j ≤ Q then coefficient (catalogue j) else 0 := by
    exact (catalogue_bijective.sum_comp
      (fun p => if p ≤ Q then coefficient p else 0)).symm
  rw [← hIcc, Finset.sum_filter]
  rw [hfilter]
  obtain ⟨k, rfl⟩ := catalogue_bijective.surjective Q
  fin_cases k
  all_goals try exact (hQ rfl).elim
  all_goals
    norm_num [catalogue, coefficient, edgeCount, Fin.sum_univ_succ,
      discrete, indiscrete] at hQ ⊢ <;> decide

-- This expansion is over all fifteen *partitions*. The mode representative
-- theorem and merger_sum_transport are what justify replacing these upper
-- partition sums with the Fourier mode sums in the existing entropy theorem.
private theorem weighted_sum_expansion (G : FourPartition → ℝ) :
    (∑ p : FourPartition, (coefficient p : ℝ) * G p) =
      G ⊥ - (∑ k : Fin 6, G (pairPartition k)) +
        2 * (∑ k : Fin 4, G (triplePartition k)) +
        (∑ k : Fin 3, G (doublePartition k)) - 6 * G ⊤ := by
  calc
    _ = ∑ k : Fin 15, (coefficient (catalogue k) : ℝ) * G (catalogue k) :=
      (catalogue_bijective.sum_comp (fun p => (coefficient p : ℝ) * G p)).symm
    _ = _ := by
      simp only [catalogue_coefficient]
      have hbot : (⊥ : FourPartition) = discrete := rfl
      have htop : (⊤ : FourPartition) = indiscrete := rfl
      rw [hbot, htop]
      norm_num [Fin.sum_univ_succ, pairPartition, triplePartition, doublePartition, catalogue]
      ring_nf

private def upperSum (Ω : Finset FourPartition) (f : FourPartition → ℝ)
    (p : FourPartition) : ℝ :=
  ∑ Q ∈ Ω, if p ≤ Q then f Q else 0

-- The integer audit supplies the real cancellation by casting its finite sum;
-- no unproved identification of integer and real Möbius functions is used.
private theorem weighted_upper_sum_cancel (Ω : Finset FourPartition)
    (hΩ : ∀ Q ∈ Ω, Q ≠ ⊥) (f : FourPartition → ℝ) :
    (∑ p : FourPartition, (coefficient p : ℝ) * upperSum Ω f p) = 0 := by
  unfold upperSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro Q hQ
  have hcast : (∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, (coefficient p : ℝ)) = 0 := by
    simpa only [Int.cast_sum, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ℝ)) (coefficient_cancel Q (hΩ Q hQ))
  have hIcc : Finset.univ.filter (fun p : FourPartition => p ≤ Q) =
      Finset.Icc ⊥ Q := by
    ext p
    simp
  calc
    (∑ p : FourPartition, (coefficient p : ℝ) * (if p ≤ Q then f Q else 0)) =
        ∑ p : FourPartition, if p ≤ Q then (coefficient p : ℝ) * f Q else 0 := by
      simp_rw [mul_ite, mul_zero]
    _ = ∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, (coefficient p : ℝ) * f Q := by
      rw [← Finset.sum_filter, hIcc]
    _ = (∑ p ∈ Finset.Icc (⊥ : FourPartition) Q, (coefficient p : ℝ)) * f Q := by
      rw [Finset.sum_mul]
    _ = 0 := by rw [hcast, zero_mul]

-- This is the source question's coefficient identity for an arbitrary weight
-- on a family of nontrivial, non-discrete four-point coloring partitions.
-- The remaining exact merger bindings replace each upperSum by partitionSum.
private theorem four_party_counting_identity (Ω : Finset FourPartition)
    (hΩbot : ∀ Q ∈ Ω, Q ≠ ⊥) (hΩtop : ∀ Q ∈ Ω, Q ≠ ⊤)
    (f : FourPartition → ℝ) :
    upperSum Ω f ⊥ - (∑ k : Fin 6, upperSum Ω f (pairPartition k)) +
      2 * (∑ k : Fin 4, upperSum Ω f (triplePartition k)) +
      (∑ k : Fin 3, upperSum Ω f (doublePartition k)) = 0 := by
  have htop : upperSum Ω f ⊤ = 0 := by
    unfold upperSum
    apply Finset.sum_eq_zero
    intro Q hQ
    apply if_neg
    intro h
    exact hΩtop Q hQ (top_le_iff.mp h)
  have h := weighted_sum_expansion (upperSum Ω f)
  rw [weighted_upper_sum_cancel Ω hΩbot f, htop, mul_zero, sub_zero] at h
  exact h.symm

open D5.S3.Combinatorics.Partitions.TernaryPartitionOrbit
open scoped BigOperators

private def anchorEquiv (r : ℕ) : Fin (r + 1) ≃ Option (Fin r) :=
  finSuccEquiv' (Fin.last r)

private theorem colourValue2 : ∀ (t : Fin 1 → ZMod 3) (c : Fin 2),
    colourValue t c = anchored t (anchorEquiv 1 c) := by decide

private theorem colourValue3 : ∀ (t : Fin 2 → ZMod 3) (c : Fin 3),
    colourValue t c = anchored t (anchorEquiv 2 c) := by decide

private theorem colourValue4 : ∀ (t : Fin 3 → ZMod 3) (c : Fin 4),
    colourValue t c = anchored t (anchorEquiv 3 c) := by decide

private def mergeMap {r : ℕ} (m : Fin 4 → Fin (r + 1)) :
    Option (Fin 3) → Option (Fin r) :=
  anchorEquiv r ∘ m ∘ (anchorEquiv 3).symm

private theorem mergeMap_surjective {r : ℕ} (m : Fin 4 → Fin (r + 1))
    (hm : Function.Surjective m) : Function.Surjective (mergeMap m) :=
  (anchorEquiv r).surjective.comp (hm.comp (anchorEquiv 3).symm.surjective)

def pairMergers : Fin 6 → Fin 4 → Fin 3 :=
  ![![0, 0, 1, 2], ![0, 1, 0, 2], ![0, 1, 2, 0],
    ![1, 0, 0, 2], ![1, 0, 2, 0], ![1, 2, 0, 0]]

def singletonCuts : Fin 4 → Fin 4 → Fin 2 :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0], ![0, 1, 0, 0], ![1, 0, 0, 0]]

def balancedCuts : Fin 3 → Fin 4 → Fin 2 :=
  ![![0, 0, 1, 1], ![0, 1, 0, 1], ![0, 1, 1, 0]]

private theorem pairMergers_surjective :
    ∀ k : Fin 6, Function.Surjective (pairMergers k) := by decide

private theorem singletonCuts_surjective :
    ∀ k : Fin 4, Function.Surjective (singletonCuts k) := by decide

private theorem balancedCuts_surjective :
    ∀ k : Fin 3, Function.Surjective (balancedCuts k) := by decide

private noncomputable def encodePartition (Q : Setoid (Option (Fin 3))) : FourPartition :=
  fromSetoid (Setoid.comap (anchorEquiv 3) Q)

private theorem encodePartition_le_iff (Q R : Setoid (Option (Fin 3))) :
    encodePartition Q ≤ encodePartition R ↔ Q ≤ R := by
  rw [encodePartition, encodePartition, fromSetoid_le_iff]
  constructor
  · intro h i j hij
    obtain ⟨a, rfl⟩ := (anchorEquiv 3).surjective i
    obtain ⟨b, rfl⟩ := (anchorEquiv 3).surjective j
    exact h hij
  · exact fun h => Setoid.comap_monotone _ h

private theorem encodePartition_injective : Function.Injective encodePartition := by
  intro Q R h
  exact le_antisymm ((encodePartition_le_iff Q R).mp h.le)
    ((encodePartition_le_iff R Q).mp h.ge)

private theorem encodePartition_surjective : Function.Surjective encodePartition := by
  intro c
  refine ⟨Setoid.comap (anchorEquiv 3).symm (toSetoid c), ?_⟩
  unfold encodePartition
  have h : Setoid.comap (anchorEquiv 3)
      (Setoid.comap (anchorEquiv 3).symm (toSetoid c)) = toSetoid c := by
    apply Setoid.ext
    intro i j
    simp only [Setoid.comap_rel, Equiv.symm_apply_apply]
  rw [h, from_to]

private theorem encodePartition_bot : encodePartition ⊥ = ⊥ := by
  apply le_antisymm
  · obtain ⟨Q, hQ⟩ := encodePartition_surjective ⊥
    rw [← hQ]
    exact (encodePartition_le_iff _ _).mpr bot_le
  · exact bot_le

private theorem encodePartition_top : encodePartition ⊤ = ⊤ := by
  apply le_antisymm
  · exact le_top
  · obtain ⟨Q, hQ⟩ := encodePartition_surjective ⊤
    rw [← hQ]
    exact (encodePartition_le_iff _ _).mpr le_top

private noncomputable def partitionSupport (P : Finset (Fin 3 → ZMod 3)) :
    Finset FourPartition := (P.image partition).image encodePartition

private theorem partitionSupport_ne_bot (P : Finset (Fin 3 → ZMod 3)) :
    ∀ Q ∈ partitionSupport P, Q ≠ ⊥ := by
  intro Q hQ
  unfold partitionSupport at hQ
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hR
  intro h
  apply four_party_partition_ne_bot u
  apply encodePartition_injective
  exact h.trans encodePartition_bot.symm

private theorem partitionSupport_ne_top (P : Finset (Fin 3 → ZMod 3))
    (h0 : (0 : Fin 3 → ZMod 3) ∉ P) :
    ∀ Q ∈ partitionSupport P, Q ≠ ⊤ := by
  intro Q hQ
  unfold partitionSupport at hQ
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hR
  have hu0 : u ≠ 0 := fun h => h0 (h ▸ hu)
  intro h
  apply nonzero_partition_ne_top u hu0
  apply encodePartition_injective
  exact h.trans encodePartition_top.symm

private theorem encoded_upperSum (P : Finset (Fin 3 → ZMod 3))
    (f : FourPartition → ℝ) (K : Setoid (Option (Fin 3))) :
    upperSum (partitionSupport P) f (encodePartition K) =
      ∑ Q ∈ (P.image partition).filter (fun Q => K ≤ Q), f (encodePartition Q) := by
  classical
  unfold upperSum partitionSupport
  rw [Finset.sum_image (fun _ _ _ _ h => encodePartition_injective h)]
  simp only [encodePartition_le_iff, Finset.sum_filter]

-- The merger's source anchor need not map to the target anchor. Its kernel is
-- carried correctly because conjugation uses equivalences on both label sets.
private theorem encoded_merger_kernel {r : ℕ} (m : Fin 4 → Fin (r + 1)) :
    encodePartition (Setoid.ker (mergeMap m)) = fromSetoid (Setoid.ker m) := by
  unfold encodePartition
  congr 1
  apply Setoid.ext
  intro i j
  change mergeMap m (anchorEquiv 3 i) = mergeMap m (anchorEquiv 3 j) ↔ m i = m j
  simp only [mergeMap, Function.comp_apply, Equiv.symm_apply_apply,
    Equiv.apply_eq_iff_eq]

private theorem merger_sum_upperSum {r : ℕ}
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (R : Finset (Fin r → ZMod 3)) (h0R : (0 : Fin r → ZMod 3) ∉ R)
    (hR : ∀ u : Fin r → ZMod 3, u ≠ 0 → (u ∈ R ↔ -u ∉ R))
    (m : Fin 4 → Fin (r + 1)) (hm : Function.Surjective m)
    (f : FourPartition → ℝ) :
    (∑ t ∈ R, f (encodePartition (pullPartition (mergeMap m) t))) =
      upperSum (partitionSupport P) f (fromSetoid (Setoid.ker m)) := by
  rw [← encoded_merger_kernel m, encoded_upperSum]
  exact merger_sum_transport P h0 hP R h0R hR (mergeMap m)
    (mergeMap_surjective m hm) (fun Q => f (encodePartition Q))

private theorem full_sum_upperSum
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (f : FourPartition → ℝ) :
    (∑ t ∈ P, f (encodePartition (partition t))) =
      upperSum (partitionSupport P) f ⊥ := by
  rw [← encodePartition_bot, encoded_upperSum]
  simpa using representative_sum P h0 hP (fun Q => f (encodePartition Q))

private def separation (c : FourPartition) : Matrix (Fin 4) (Fin 4) Bool :=
  fun i j => !(relation c.val i j)

private theorem separation_encoded (v : Option (Fin 3) → ZMod 3)
    (i j : Fin 4) :
    separation (encodePartition (Setoid.ker v)) i j =
      decide (v (anchorEquiv 3 i) ≠ v (anchorEquiv 3 j)) := by
  classical
  have h := relation_code (Setoid.comap (anchorEquiv 3) (Setoid.ker v)) i j
  change (!(relation (code (Setoid.comap (anchorEquiv 3) (Setoid.ker v))) i j)) = _
  by_cases he : v (anchorEquiv 3 i) = v (anchorEquiv 3 j)
  · have ht := h.mpr he
    simp [ht, he]
  · have ht : relation (code (Setoid.comap (anchorEquiv 3) (Setoid.ker v))) i j = false := by
      cases hr : relation (code (Setoid.comap (anchorEquiv 3) (Setoid.ker v))) i j
      · rfl
      · exact False.elim (he (h.mp hr))
    simp [ht, he]

private theorem pairMergers_partition (k : Fin 6) :
    fromSetoid (Setoid.ker (pairMergers k)) = pairPartition k := by
  apply Subtype.ext
  funext e
  fin_cases k <;> fin_cases e <;>
    simp [fromSetoid, code, Setoid.ker_def, pairMergers, pairPartition, catalogue]

private theorem singletonCuts_partition (k : Fin 4) :
    fromSetoid (Setoid.ker (singletonCuts k)) = triplePartition k := by
  apply Subtype.ext
  funext e
  fin_cases k <;> fin_cases e <;>
    simp [fromSetoid, code, Setoid.ker_def, singletonCuts, triplePartition, catalogue]

private theorem balancedCuts_partition (k : Fin 3) :
    fromSetoid (Setoid.ker (balancedCuts k)) = doublePartition k := by
  apply Subtype.ext
  funext e
  fin_cases k <;> fin_cases e <;>
    simp [fromSetoid, code, Setoid.ker_def, balancedCuts, doublePartition, catalogue]

-- The source uses `q - 1` in its public arity.  This r-indexed spelling keeps
-- the dependent finite type normalized while proving the transport bridge.
def partitionSumR (r : ℕ) (P : Finset (Fin r → ZMod 3))
    (m : Fin 4 → Fin (r + 1)) (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) : ℝ :=
  ∑ t ∈ P, f (cutPattern (colourValue (q := r + 1) t ∘ m))

private theorem partitionSum_as_upperSum {r : ℕ}
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (R : Finset (Fin r → ZMod 3)) (h0R : (0 : Fin r → ZMod 3) ∉ R)
    (hR : ∀ u : Fin r → ZMod 3, u ≠ 0 → (u ∈ R ↔ -u ∉ R))
    (hcolour : ∀ (t : Fin r → ZMod 3) (c : Fin (r + 1)),
      colourValue (q := r + 1) t c = anchored t (anchorEquiv r c))
    (m : Fin 4 → Fin (r + 1)) (hm : Function.Surjective m)
    (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) :
    partitionSumR r R m f =
      upperSum (partitionSupport P) (fun c => f (separation c))
        (fromSetoid (Setoid.ker m)) := by
  unfold partitionSumR
  calc
    _ = ∑ t ∈ R, f (separation (encodePartition (pullPartition (mergeMap m) t))) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      funext i j
      rw [cutPattern_apply]
      change decide (colourValue (q := r + 1) t (m i) ≠ colourValue (q := r + 1) t (m j)) =
        separation (encodePartition (Setoid.ker (anchored t ∘ mergeMap m))) i j
      rw [separation_encoded]
      simp only [Function.comp_apply, mergeMap, Equiv.symm_apply_apply, hcolour]
    _ = _ := merger_sum_upperSum P h0 hP R h0R hR m hm (fun c => f (separation c))

private theorem partitionSum_full_upperSum
    (P : Finset (Fin 3 → ZMod 3)) (h0 : (0 : Fin 3 → ZMod 3) ∉ P)
    (hP : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P ↔ -u ∉ P))
    (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) :
    partitionSumR 3 P id f =
      upperSum (partitionSupport P) (fun c => f (separation c)) ⊥ := by
  unfold partitionSumR
  calc
    _ = ∑ t ∈ P, f (separation (encodePartition (partition t))) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      funext i j
      rw [cutPattern_apply]
      change decide (colourValue (q := 4) t i ≠ colourValue (q := 4) t j) =
        separation (encodePartition (Setoid.ker (anchored t))) i j
      rw [separation_encoded, colourValue4, colourValue4]
    _ = _ := full_sum_upperSum P h0 hP (fun c => f (separation c))

-- The same generic representative family drives the full and all merger sums.
-- The function f is arbitrary; only the fifteen-element partition poset is
-- finitely audited, while arbitrary weighted mode sums are transported by the
-- structural classification theorem.
theorem result
    (P3 : Finset (Fin 3 → ZMod 3)) (h03 : (0 : Fin 3 → ZMod 3) ∉ P3)
    (hP3 : ∀ u : Fin 3 → ZMod 3, u ≠ 0 → (u ∈ P3 ↔ -u ∉ P3))
    (P2 : Finset (Fin 2 → ZMod 3)) (h02 : (0 : Fin 2 → ZMod 3) ∉ P2)
    (hP2 : ∀ u : Fin 2 → ZMod 3, u ≠ 0 → (u ∈ P2 ↔ -u ∉ P2))
    (P1 : Finset (Fin 1 → ZMod 3)) (h01 : (0 : Fin 1 → ZMod 3) ∉ P1)
    (hP1 : ∀ u : Fin 1 → ZMod 3, u ≠ 0 → (u ∈ P1 ↔ -u ∉ P1))
    (f : Matrix (Fin 4) (Fin 4) Bool → ℝ) :
    partitionSumR 3 P3 id f -
      (∑ k : Fin 6, partitionSumR 2 P2 (pairMergers k) f) +
      2 * (∑ k : Fin 4, partitionSumR 1 P1 (singletonCuts k) f) +
      (∑ k : Fin 3, partitionSumR 1 P1 (balancedCuts k) f) = 0 := by
  have hp (k : Fin 6) : partitionSumR 2 P2 (pairMergers k) f =
      upperSum (partitionSupport P3) (fun c => f (separation c)) (pairPartition k) := by
    rw [partitionSum_as_upperSum P3 h03 hP3 P2 h02 hP2 colourValue3
      (pairMergers k) (pairMergers_surjective k) f, pairMergers_partition]
  have ht (k : Fin 4) : partitionSumR 1 P1 (singletonCuts k) f =
      upperSum (partitionSupport P3) (fun c => f (separation c)) (triplePartition k) := by
    rw [partitionSum_as_upperSum P3 h03 hP3 P1 h01 hP1 colourValue2
      (singletonCuts k) (singletonCuts_surjective k) f, singletonCuts_partition]
  have hd (k : Fin 3) : partitionSumR 1 P1 (balancedCuts k) f =
      upperSum (partitionSupport P3) (fun c => f (separation c)) (doublePartition k) := by
    rw [partitionSum_as_upperSum P3 h03 hP3 P1 h01 hP1 colourValue2
      (balancedCuts k) (balancedCuts_surjective k) f, balancedCuts_partition]
  rw [partitionSum_full_upperSum P3 h03 hP3 f]
  simp_rw [hp, ht, hd]
  exact four_party_counting_identity (partitionSupport P3)
    (partitionSupport_ne_bot P3) (partitionSupport_ne_top P3 h03)
    (fun c => f (separation c))

end D5.S3.Combinatorics.Partitions.TernaryPartitionCounting
