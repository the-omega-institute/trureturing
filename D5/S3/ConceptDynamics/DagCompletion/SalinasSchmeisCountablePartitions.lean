/- GID: D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/DagCompletion/SalinasSchmeisCountablePartitions
   mirror-E: none(waiver:pure-mathematical-argument)
   anchors: []
   utility: none
   digest: Constructs inherited omega partitions of the ordinal sum and maximal-ray extensions. -/

/- The literal maximal-ray partition refines each inherited ray by the countable
   fiber of points assigned to that maximal element, then prepends their base points.
   Escape audits for the public partition theorems are unfinished under the linked
   source-family issue https://github.com/the-omega-institute/trureturing/issues/28004.
   A lawful enrolled readout and observational variation are unresolved. -/

import D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisLexicographicFiberExtension
import Mathlib.Basic.Denumerable
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Cofinal
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Sum.Order

/-! Cofinal partitions of the naturals and literal inherited omega partitions of two extensions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisCountablePartitions

open SalinasSchmeisOmegaChainExtensionRefutation (IsExtension IsOmegaChain)
open SalinasSchmeisLexicographicFiberExtension (lexFiber lexFiberExtension lexFiberOrderIso)

universe u v

/-- The parts cover with a unique index, and each is infinite and cofinal. -/
def IsCofinalNatPartition {I : Type u} (S : I → Set ℕ) : Prop :=
  (∀ n : ℕ, ∃! i, n ∈ S i) ∧ ∀ i, (S i).Infinite ∧ IsCofinal (S i)

/-- Residues modulo the number of parts, written as increasing ranges. -/
def residuePart {m : ℕ} (i : Fin m) : Set ℕ :=
  Set.range (fun k : ℕ => (i : ℕ) + m * k)

/-- The successor has the prescribed power of two and a positive odd factor. -/
def twoAdicPart (i : ℕ) : Set ℕ :=
  Set.range (fun k : ℕ => 2 ^ i * (2 * k + 1) - 1)

private theorem residueStrictMono {m : ℕ} (hm : 0 < m) (i : Fin m) :
    StrictMono (fun k : ℕ => (i : ℕ) + m * k) := by
  intro k l h
  exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left h hm) i.val

private theorem infiniteCofinalRange {f : ℕ → ℕ} (hf : Function.Injective f) :
    (Set.range f).Infinite ∧ IsCofinal (Set.range f) :=
  let hi := Set.infinite_range_of_injective hf
  ⟨hi, not_bddAbove_iff_isCofinal.mp hi.not_bddAbove⟩

/-- For positive modulus the displayed residue ranges partition the naturals. -/
theorem residuePartition (m : ℕ) (hm : 0 < m) :
    IsCofinalNatPartition (@residuePart m) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  let e := Nat.divModEquiv m
  have rangeEq (i : Fin m) (k : ℕ) : e.symm (k, i) = (i : ℕ) + m * k := by
    change k * m + (i : ℕ) = (i : ℕ) + m * k
    rw [Nat.mul_comm k m, Nat.add_comm]
  refine ⟨fun n => ?_, fun i => ?_⟩
  · refine ⟨(e n).2, ⟨(e n).1, ?_⟩, ?_⟩
    · change (↑(e n).2 : ℕ) + m * (e n).1 = n
      rw [← rangeEq]
      exact e.symm_apply_apply n
    · rintro i ⟨k, hk⟩
      have h : e.symm (k, i) = n := (rangeEq _ _).trans hk
      exact congrArg Prod.snd ((e.apply_symm_apply _).symm.trans (congrArg e h))
  · exact infiniteCofinalRange (residueStrictMono hm i).injective

private theorem twoAdic_succ (i k : ℕ) :
    (2 ^ i * (2 * k + 1) - 1) + 1 = 2 ^ i * (2 * k + 1) := by
  have h : 0 < 2 ^ i * (2 * k + 1) := Nat.mul_pos (pow_pos (by decide) _) (by omega)
  omega

private theorem twoAdicStrictMono (i : ℕ) :
    StrictMono (fun k : ℕ => 2 ^ i * (2 * k + 1) - 1) := by
  intro k l h
  dsimp
  apply Nat.lt_of_succ_lt_succ
  change (2 ^ i * (2 * k + 1) - 1) + 1 < (2 ^ i * (2 * l + 1) - 1) + 1
  rw [twoAdic_succ, twoAdic_succ]
  exact Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos (by decide) _)

private theorem twoAdic_exponent (i k : ℕ) :
    (2 ^ i * (2 * k + 1)).factorization 2 = i := by
  have h : ¬ 2 ∣ 2 * k + 1 := by omega
  rw [Nat.factorization_mul (pow_ne_zero _ (by decide)) (by omega)]
  change (2 ^ i).factorization 2 + (2 * k + 1).factorization 2 = i
  rw [Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd h,
    Nat.add_zero]

/-- Factoring the positive successor gives the unique index of the displayed ranges. -/
theorem twoAdicPartition : IsCofinalNatPartition twoAdicPart := by
  refine ⟨fun n => ?_, fun i => ?_⟩
  · obtain ⟨i, _, ⟨k, rfl⟩, h⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.succ_ne_zero n)
    refine ⟨i, ⟨k, ?_⟩, ?_⟩
    · change 2 ^ i * (2 * k + 1) - 1 = n
      rw [← h]
      exact Nat.succ_sub_one n
    · rintro j ⟨l, hl⟩
      change 2 ^ j * (2 * l + 1) - 1 = n at hl
      have heq : 2 ^ j * (2 * l + 1) = 2 ^ i * (2 * k + 1) := by
        rw [← twoAdic_succ j l, hl]
        exact h
      rw [← twoAdic_exponent j l, ← twoAdic_exponent i k, heq]
  · exact infiniteCofinalRange (twoAdicStrictMono i).injective

private theorem reindexPartition {I : Type u} {J : Type v} {S : J → Set ℕ}
    (hS : IsCofinalNatPartition S) (e : I ≃ J) : IsCofinalNatPartition (S ∘ e) := by
  refine ⟨fun n => ?_, fun i => hS.2 (e i)⟩
  obtain ⟨j, hj, huniq⟩ := hS.1 n
  refine ⟨e.symm j, ?_, fun i hi => e.injective ?_⟩
  · simpa only [Function.comp_apply, e.apply_symm_apply] using hj
  · rw [e.apply_symm_apply]
    exact huniq _ hi

/-- A nonempty countable type indexes an infinite cofinal partition of the naturals. -/
theorem countablePartition (I : Type u) [Nonempty I] [Countable I] :
    ∃ S : I → Set ℕ, IsCofinalNatPartition S := by
  classical
  rcases finite_or_infinite I with h | h
  · let := Fintype.ofFinite I
    let e := Fintype.equivFin I
    exact ⟨residuePart ∘ e, reindexPartition (residuePartition _ Fintype.card_pos) e⟩
  · let e : I ≃ ℕ := Classical.choice (inferInstance : Nonempty (I ≃ ℕ))
    exact ⟨twoAdicPart ∘ e, reindexPartition twoAdicPartition e⟩

private theorem prependOmega {X : Type u} [PartialOrder X] (x : X) (e : ℕ ↪o X)
    (hx : ∀ n, x < e n) : IsOmegaChain (insert x (Set.range e)) := by
  let f : ℕ → X := fun n => Nat.casesOn n x e
  have hf : StrictMono f := by
    intro i j hij
    cases j with
    | zero => exact (Nat.not_lt_zero _ hij).elim
    | succ j =>
      cases i with
      | zero => exact hx j
      | succ i => exact e.strictMono (Nat.lt_of_succ_lt_succ hij)
  let g := OrderEmbedding.ofStrictMono f hf
  have hr : Set.range g = insert x (Set.range e) := by
    ext y
    constructor
    · rintro ⟨(_ | n), rfl⟩
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ ⟨n, rfl⟩
    · intro hy
      rcases Set.mem_insert_iff.mp hy with rfl | ⟨n, rfl⟩
      · exact ⟨0, rfl⟩
      · exact ⟨n + 1, rfl⟩
  rw [← hr]
  exact ⟨g.orderIso⟩

private theorem prependInfinitePart {X : Type u} [PartialOrder X] (x : X)
    (e : ℕ ↪o X) {S : Set ℕ} (hS : S.Infinite) (hx : ∀ n ∈ S, x < e n) :
    IsOmegaChain (insert x (e '' S)) := by
  let : Infinite S := hS.to_subtype
  let f := ((Nat.Subtype.orderIsoOfNat S).toOrderEmbedding.trans
    (OrderEmbedding.subtype (· ∈ S))).trans e
  have hr : Set.range f = e '' S := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨_, (Nat.Subtype.orderIsoOfNat S n).property, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨k, hk⟩ := (Nat.Subtype.orderIsoOfNat S).surjective ⟨n, hn⟩
      exact ⟨k, congrArg (fun t : S => e t.val) hk⟩
  rw [← hr]
  exact prependOmega x f (fun n => hx _ (Nat.Subtype.orderIsoOfNat S n).property)

private theorem partitionOfUniqueIndex {I : Type u} {X : Type v} (C : I → Set X)
    (hn : ∀ i, (C i).Nonempty) (hu : ∀ x : X, ∃! i, x ∈ C i) :
    Setoid.IsPartition (Set.range C) := by
  refine ⟨?_, fun x => ?_⟩
  · rintro ⟨i, hi⟩
    exact (hn i).ne_empty hi
  · obtain ⟨i, hi, uniq⟩ := hu x
    refine ⟨C i, ⟨⟨i, rfl⟩, hi⟩, ?_⟩
    rintro _ ⟨⟨j, rfl⟩, hj⟩
    exact congrArg C (uniq j hj)

variable {P : Type u} [PartialOrder P]

/-- The base is induced in the ordinal sum. -/
def ordinalSumBase : P ↪o P ⊕ₗ ℕ :=
  OrderEmbedding.ofMapLEIff Sum.inlₗ (fun _ _ => Sum.Lex.inl_le_inl_iff)

private def ordinalSumTail : ℕ ↪o P ⊕ₗ ℕ :=
  OrderEmbedding.ofMapLEIff Sum.inrₗ (fun _ _ => Sum.Lex.inr_le_inr_iff)

/-- The part of the ordinal sum formed from a base point and its selected tail. -/
def ordinalSumPart (S : P → Set ℕ) (p : P) : Set (P ⊕ₗ ℕ) :=
  insert (Sum.inlₗ p) (Sum.inrₗ '' S p)

/-- Partition the actual ordinal sum using one selected cofinal set per base point. -/
theorem ordinalSumPartition [Nonempty P] [Countable P] :
    IsExtension P (P ⊕ₗ ℕ) ∧ ∃ S : P → Set ℕ, IsCofinalNatPartition S ∧
      Setoid.IsPartition (Set.range (ordinalSumPart S)) ∧
      ∀ p, IsOmegaChain (ordinalSumPart S p) := by
  obtain ⟨S, hS⟩ := countablePartition P
  refine ⟨⟨ordinalSumBase⟩, S, hS, partitionOfUniqueIndex _ (fun p => ⟨_, Set.mem_insert _ _⟩) ?_, ?_⟩
  · intro x
    rcases x with p | n
    · refine ⟨p, Set.mem_insert _ _, ?_⟩
      intro q hq
      rcases Set.mem_insert_iff.mp hq with h | ⟨_, _, h⟩
      · exact Sum.inl.inj h.symm
      · cases h
    · obtain ⟨p, hp, hup⟩ := hS.1 n
      refine ⟨p, Set.mem_insert_of_mem _ ⟨n, hp, rfl⟩, ?_⟩
      intro q hq
      rcases Set.mem_insert_iff.mp hq with h | ⟨k, hk, h⟩
      · cases h
      · exact hup q (Sum.inr.inj h ▸ hk)
  · intro p
    exact prependInfinitePart (Sum.inlₗ p) ordinalSumTail (hS.2 p).1
      (fun n _ => Sum.Lex.inl_lt_inr p n)

/-- The index type of the rays, with maximality in the whole original poset. -/
abbrev MaximalPoints (P : Type u) [PartialOrder P] := {m : P // IsMax m}

/-- The original base and a disjoint ray over each maximal point. -/
def MaximalRayExtension (P : Type u) [PartialOrder P] :=
  P ⊕ (MaximalPoints P ×ₗ ℕ)

/-- The tagged base point of the maximal-ray extension. -/
def MaximalRayExtension.base (p : P) : MaximalRayExtension P :=
  Sum.inl p

/-- The tagged point at a given natural coordinate on a maximal ray. -/
def MaximalRayExtension.ray (m : MaximalPoints P) (n : ℕ) : MaximalRayExtension P :=
  Sum.inr (toLex (m, n))

private def maximalRayLE : MaximalRayExtension P → MaximalRayExtension P → Prop
  | .inl p, .inl q => p ≤ q
  | .inl p, .inr y => p ≤ (ofLex y).1.val
  | .inr _, .inl _ => False
  | .inr x, .inr y => x ≤ y

instance maximalRayOrder : PartialOrder (MaximalRayExtension P) where
  le := maximalRayLE
  le_refl x := by
    rcases x with p | x
    · exact le_rfl
    · exact le_rfl
  le_trans x y z hxy hyz := by
    rcases x with p | x <;> rcases y with q | y <;> rcases z with r | z
    · exact le_trans hxy hyz
    · exact le_trans hxy hyz
    · exact False.elim hyz
    · exact le_trans hxy (Prod.Lex.toLex_le_toLex'.mp hyz).1
    · exact False.elim hxy
    · exact False.elim hxy
    · exact False.elim hyz
    · exact le_trans hxy hyz
  le_antisymm x y hxy hyx := by
    rcases x with p | x <;> rcases y with q | y
    · exact congrArg Sum.inl (le_antisymm hxy hyx)
    · exact False.elim hyx
    · exact False.elim hxy
    · exact congrArg Sum.inr (le_antisymm hxy hyx)

/-- The base is induced in the maximal-ray extension. -/
def maximalRayBase : P ↪o MaximalRayExtension P :=
  OrderEmbedding.ofMapLEIff MaximalRayExtension.base (fun _ _ => Iff.rfl)

private def rayInclusion : (MaximalPoints P ×ₗ ℕ) ↪o MaximalRayExtension P :=
  OrderEmbedding.ofMapLEIff Sum.inr (fun _ _ => Iff.rfl)

/-- A part consists of a base point and its selected subset of the assigned ray. -/
def maximalRayPart (a : P → MaximalPoints P)
    (S : (m : MaximalPoints P) → {p : P // a p = m} → Set ℕ)
    (p : P) : Set (MaximalRayExtension P) :=
  insert (MaximalRayExtension.base p) (MaximalRayExtension.ray (a p) '' S (a p) ⟨p, rfl⟩)

/-- Partition each literal maximal ray using the fiber of points assigned to it. -/
theorem maximalRayPartition [Countable P] (a : P → MaximalPoints P)
    (ha : ∀ p, p ≤ (a p).val) :
    IsExtension P (MaximalRayExtension P) ∧
    ∃ S : (m : MaximalPoints P) → {p : P // a p = m} → Set ℕ,
      (∀ m, IsCofinalNatPartition (S m)) ∧
      Setoid.IsPartition (Set.range (maximalRayPart a S)) ∧
      ∀ p, IsOmegaChain (maximalRayPart a S p) := by
  classical
  have hf (m : MaximalPoints P) : ∃ S, IsCofinalNatPartition
      (I := {p : P // a p = m}) S := by
    have hfix : a m.val = m := Subtype.ext (le_antisymm (m.property (ha m.val)) (ha m.val))
    let : Nonempty {p : P // a p = m} := ⟨⟨m.val, hfix⟩⟩
    exact countablePartition _
  choose S hS using hf
  refine ⟨⟨maximalRayBase⟩, S, hS, partitionOfUniqueIndex _ (fun p => ⟨_, Set.mem_insert _ _⟩) ?_, ?_⟩
  · intro x
    rcases x with p | x
    · refine ⟨p, Set.mem_insert _ _, ?_⟩
      intro q hq
      rcases Set.mem_insert_iff.mp hq with h | ⟨_, _, h⟩
      · exact Sum.inl.inj h.symm
      · cases h
    · obtain ⟨C, ⟨⟨m, rfl⟩, hx⟩, _⟩ :=
        (lexFiberExtension (P := MaximalPoints P) (0 : ℕ)).2.1.2 x
      change (ofLex x).1 = m at hx
      rcases x with ⟨i, n⟩
      change i = m at hx
      subst i
      have rayCover (m : MaximalPoints P) (n : ℕ) :
          ∃! q : P, (Sum.inr (toLex (m, n)) : MaximalRayExtension P) ∈ maximalRayPart a S q := by
        have memRay (q : P) (hq : a q = m) :
            n ∈ S m ⟨q, hq⟩ ↔
              (Sum.inr (toLex (m, n)) : MaximalRayExtension P) ∈ maximalRayPart a S q := by
          subst m
          constructor
          · intro h
            exact Set.mem_insert_of_mem _ ⟨n, h, rfl⟩
          · intro h
            rcases Set.mem_insert_iff.mp h with hm | ⟨k, hk, hm⟩
            · cases hm
            · have : k = n := congrArg Prod.snd (Sum.inr.inj hm)
              exact this ▸ hk
        obtain ⟨⟨p, hp⟩, hpn, hup⟩ := (hS m).1 n
        refine ⟨p, (memRay p hp).mp hpn, ?_⟩
        intro q hq
        obtain ⟨k, _, heq⟩ :=
          (Set.mem_insert_iff.mp hq).resolve_left (by intro h; cases h)
        have htag : a q = m := congrArg Prod.fst (Sum.inr.inj heq)
        exact congrArg Subtype.val (hup ⟨q, htag⟩ ((memRay q htag).mpr hq))
      exact rayCover m n
  · intro p
    let e : ℕ ↪o MaximalRayExtension P := ((lexFiberOrderIso (A := ℕ) (a p)).toOrderEmbedding.trans
      (OrderEmbedding.subtype (· ∈ lexFiber (A := ℕ) (a p)))).trans rayInclusion
    exact prependInfinitePart (MaximalRayExtension.base p) e ((hS (a p)).2 ⟨p, rfl⟩).1
      (fun _ _ => lt_iff_le_not_ge.mpr ⟨ha p, id⟩)

end D5.S3.ConceptDynamics.DagCompletion.SalinasSchmeisCountablePartitions
