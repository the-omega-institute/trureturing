/- GID: D5/S0/Certificates/Algebra/CappedUnionDavenport
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/CappedUnionDavenport
   mirror-E: none(waiver:structural-proof)
   anchors: [mathlib/module/Mathlib.Algebra.BigOperators.Fin]
   utility: none
   digest: In the capped union monoid P_fin(U) x {0,1,2} the relative Davenport constant of (A,k) is |A|+k. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Bounds.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Relative Davenport constants of the capped union monoid. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.Algebra.CappedUnionDavenport

/-
proof_shape:
  Capped, MinimalFor, minimalLengths: definition
  add_support, add_level, zero_support, zero_level: bind-only (consumers: the monoid
    instance, sum_eq)
  sum_eq: content (consumers: upper, lower)
  witness, mem_witness_support: definition and bind-only (consumer: lower)
  upper, lower: content (consumer: result)
  result: content
escape_witness: in a minimal sequence each single deletion changes the sum, so a term is
  either level-critical (at most k such terms, by the capped level arithmetic) or the unique
  carrier of a support point (an injection into A); the k marked terms with the singletons of A
  attain |A| + k.
admission_basis: escape-witness
-/

/-- An element `(A, i)` of `S_U = P_fin(U) × {0, 1, 2}`. -/
@[ext]
structure Capped (U : Type*) where
  support : Finset U
  level : Fin 3

variable {U : Type*}

/-- The identity `(∅, 0)`. -/
private instance : Zero (Capped U) := ⟨⟨∅, 0⟩⟩

private theorem zero_support : (0 : Capped U).support = ∅ := rfl
private theorem zero_level : ((0 : Capped U).level : ℕ) = 0 := rfl

variable [DecidableEq U]

/-- `(A, i) + (B, j) = (A ∪ B, min 2 (i + j))`. -/
private instance : Add (Capped U) :=
  ⟨fun x y => ⟨x.support ∪ y.support, ⟨min 2 (x.level.val + y.level.val), by omega⟩⟩⟩

private theorem add_support (x y : Capped U) : (x + y).support = x.support ∪ y.support := rfl
private theorem add_level (x y : Capped U) :
    ((x + y).level : ℕ) = min 2 (x.level.val + y.level.val) := rfl

private instance : AddCommMonoid (Capped U) where
  add_assoc x y z := by
    ext1
    · simp only [add_support, Finset.union_assoc]
    · apply Fin.ext; simp only [add_level]; omega
  zero_add x := by
    ext1
    · simp only [add_support, zero_support, Finset.empty_union]
    · apply Fin.ext; simp only [add_level, zero_level]; have := x.level.isLt; omega
  add_zero x := by
    ext1
    · simp only [add_support, zero_support, Finset.union_empty]
    · apply Fin.ext; simp only [add_level, zero_level]; have := x.level.isLt; omega
  add_comm x y := by
    ext1
    · simp only [add_support, Finset.union_comm]
    · apply Fin.ext; simp only [add_level]; omega
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl

/-- The sum of a finite family: union of supports and capped total level. -/
private theorem sum_eq {ι : Type*} (I : Finset ι) (f : ι → Capped U) :
    (∑ i ∈ I, f i).support = I.sup (fun i => (f i).support) ∧
    ((∑ i ∈ I, f i).level : ℕ) = min 2 (∑ i ∈ I, ((f i).level : ℕ)) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨rfl, rfl⟩
  | insert a I ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sup_insert, add_support, add_level, ih.1, ih.2]
    refine ⟨rfl, ?_⟩
    omega


/-- A sequence summing to `t` none of whose proper subsequences, the empty one
included, sums to `t`. -/
def MinimalFor {n : ℕ} (f : Fin n → Capped U) (t : Capped U) : Prop :=
  ∑ i, f i = t ∧ ∀ I : Finset (Fin n), I ≠ Finset.univ → ∑ i ∈ I, f i ≠ t

/-- The lengths of minimal sequences with sum `t`; `D_t(S_U)` is their supremum. -/
def minimalLengths (t : Capped U) : Set ℕ := {n | ∃ f : Fin n → Capped U, MinimalFor f t}

private theorem upper (A : Finset U) (k : Fin 3) (n : ℕ) (f : Fin n → Capped U)
    (hf : MinimalFor f ⟨A, k⟩) : n ≤ A.card + k := by
  obtain ⟨hsum, hmin⟩ := hf
  obtain ⟨hS, hK⟩ := sum_eq Finset.univ f
  rw [hsum] at hS hK
  simp only at hS hK
  -- each single deletion changes the sum
  have hdel (i : Fin n) : ((Finset.univ.erase i).sup fun j => (f j).support) ≠ A ∨
      min 2 (∑ j ∈ Finset.univ.erase i, ((f j).level : ℕ)) ≠ (k : ℕ) := by
    have hne := hmin (Finset.univ.erase i) (fun h => by
      have := Finset.mem_univ i; rw [← h] at this; simp at this)
    obtain ⟨h1, h2⟩ := sum_eq (Finset.univ.erase i) f
    by_contra hc
    simp only [not_or, not_not] at hc
    apply hne
    ext1
    · rw [h1, hc.1]
    · apply Fin.ext; rw [h2, hc.2]
  have hsplit (i : Fin n) : ((f i).level : ℕ) + ∑ j ∈ Finset.univ.erase i, ((f j).level : ℕ) =
      ∑ j, ((f j).level : ℕ) :=
    Finset.add_sum_erase Finset.univ (fun j => ((f j).level : ℕ)) (Finset.mem_univ i)
  let P : Fin n → Prop := fun i =>
    min 2 (∑ j ∈ Finset.univ.erase i, ((f j).level : ℕ)) ≠ (k : ℕ)
  have hcard := Finset.card_filter_add_card_filter_not (s := Finset.univ) P
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  -- deletions that keep the level must lose a point of the support
  have hex (i : Fin n) (hi : ¬ P i) :
      ∃ a ∈ A, a ∉ (Finset.univ.erase i).sup fun j => (f j).support := by
    have h1 : ((Finset.univ.erase i).sup fun j => (f j).support) ≠ A := by
      rcases hdel i with h | h
      · exact h
      · exact absurd h hi
    have hsub : ((Finset.univ.erase i).sup fun j => (f j).support) ⊆ A := by
      rw [hS]; exact Finset.sup_mono (Finset.erase_subset _ _)
    exact Finset.exists_of_ssubset (lt_of_le_of_ne hsub h1)
  have hC2 : (Finset.univ.filter fun i => ¬ P i).card ≤ A.card := by
    let C2 := Finset.univ.filter fun i => ¬ P i
    let g : {i // i ∈ C2} → {a // a ∈ A} := fun i =>
      ⟨(hex i.1 (Finset.mem_filter.mp i.2).2).choose,
        (hex i.1 (Finset.mem_filter.mp i.2).2).choose_spec.1⟩
    have hinj : Function.Injective g := by
      intro i j hij
      by_contra hne
      have hne' : i.1 ≠ j.1 := fun h => hne (Subtype.ext h)
      have hai := (hex i.1 (Finset.mem_filter.mp i.2).2).choose_spec.2
      have haj := (hex j.1 (Finset.mem_filter.mp j.2).2).choose_spec
      have heq : (hex i.1 (Finset.mem_filter.mp i.2).2).choose =
          (hex j.1 (Finset.mem_filter.mp j.2).2).choose := congrArg Subtype.val hij
      rw [heq] at hai
      set a := (hex j.1 (Finset.mem_filter.mp j.2).2).choose
      have haA : a ∈ Finset.univ.sup fun m => (f m).support := by rw [← hS]; exact haj.1
      obtain ⟨m, -, ham⟩ := Finset.mem_sup.mp haA
      have hmj : m = j.1 := by
        by_contra hmj
        exact haj.2 (Finset.mem_sup.mpr ⟨m, Finset.mem_erase.mpr ⟨hmj, Finset.mem_univ _⟩, ham⟩)
      subst hmj
      exact hai (Finset.mem_sup.mpr ⟨j.1, Finset.mem_erase.mpr ⟨Ne.symm hne', Finset.mem_univ _⟩, ham⟩)
    have := Fintype.card_le_of_injective g hinj
    rwa [Fintype.card_coe, Fintype.card_coe] at this
  -- level-critical deletions are at most k
  have hC1 : (Finset.univ.filter P).card ≤ k := by
    set L := ∑ j, ((f j).level : ℕ) with hL
    have hcrit (i : Fin n) (hi : P i) : 1 ≤ ((f i).level : ℕ) ∧ L ≤ ((f i).level : ℕ) + 1 := by
      have h := hsplit i
      have hi' : min 2 (∑ j ∈ Finset.univ.erase i, ((f j).level : ℕ)) ≠ (k : ℕ) := hi
      omega
    have hsum_le : ∑ i ∈ Finset.univ.filter P, ((f i).level : ℕ) ≤ L :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have h1 : (Finset.univ.filter P).card • 1 ≤ ∑ i ∈ Finset.univ.filter P, ((f i).level : ℕ) :=
      Finset.card_nsmul_le_sum _ _ 1 (fun i hi => (hcrit i (Finset.mem_filter.mp hi).2).1)
    have h2 : (Finset.univ.filter P).card • (L - 1) ≤
        ∑ i ∈ Finset.univ.filter P, ((f i).level : ℕ) :=
      Finset.card_nsmul_le_sum _ _ (L - 1) (fun i hi => by
        have := (hcrit i (Finset.mem_filter.mp hi).2).2; omega)
    simp only [smul_eq_mul, mul_one] at h1 h2
    set c := (Finset.univ.filter P).card
    by_contra hck
    have hc2 : 2 ≤ c := by omega
    have hL3 : 3 ≤ L := by omega
    have := Nat.mul_le_mul_right (L - 1) hc2
    omega
  omega

/-- The extremal sequence: the singletons of `A` at level zero, then `k` copies of `(∅, 1)`. -/
private noncomputable def witness (A : Finset U) (k : ℕ) : Fin (A.card + k) → Capped U :=
  Fin.append (fun j : Fin A.card => (⟨{(A.equivFin.symm j).1}, 0⟩ : Capped U))
    (fun _ : Fin k => (⟨∅, 1⟩ : Capped U))

omit [DecidableEq U] in
private theorem mem_witness_support (A : Finset U) (k : ℕ) (i : Fin (A.card + k)) (a : U) :
    a ∈ (witness A k i).support ↔ ∃ j : Fin A.card, i = Fin.castAdd k j ∧ a = (A.equivFin.symm j).1 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [witness, Fin.append_left, Finset.mem_singleton]
    constructor
    · intro h; exact ⟨j, rfl, h⟩
    · rintro ⟨j', hj, ha⟩
      rw [Fin.castAdd_inj.mp hj]; exact ha
  · simp only [witness, Fin.append_right, Finset.notMem_empty, false_iff, not_exists, not_and]
    intro j' hj
    exact absurd hj (by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega)

private theorem lower (A : Finset U) (k : Fin 3) :
    MinimalFor (witness A k) ⟨A, k⟩ := by
  have hlev : ∑ i, ((witness A k i).level : ℕ) = k := by
    rw [Fin.sum_univ_add]
    simp [witness, Fin.append_left, Fin.append_right]
  have hsupI (I : Finset (Fin (A.card + k))) (a : U) :
      a ∈ I.sup (fun i => (witness A k i).support) ↔
        ∃ j : Fin A.card, Fin.castAdd k j ∈ I ∧ a = (A.equivFin.symm j).1 := by
    rw [Finset.mem_sup]
    constructor
    · rintro ⟨i, hi, ha⟩
      obtain ⟨j, rfl, rfl⟩ := (mem_witness_support A k i a).mp ha
      exact ⟨j, hi, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨_, hj, (mem_witness_support A k _ _).mpr ⟨j, rfl, rfl⟩⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨h1, h2⟩ := sum_eq Finset.univ (witness A k)
    ext1
    · rw [h1]
      ext a
      rw [hsupI]
      constructor
      · rintro ⟨j, -, rfl⟩; exact (A.equivFin.symm j).2
      · intro ha
        exact ⟨A.equivFin ⟨a, ha⟩, Finset.mem_univ _, by simp⟩
    · apply Fin.ext; rw [h2, hlev]; have := k.isLt; simp only; omega
  · intro I hI heq
    obtain ⟨i, hi⟩ : ∃ i, i ∉ I := by
      by_contra h
      exact hI (Finset.eq_univ_of_forall fun x => by_contra fun hx => h ⟨x, hx⟩)
    obtain ⟨h1, h2⟩ := sum_eq I (witness A k)
    rw [heq] at h1 h2
    simp only at h1 h2
    revert hi
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · intro hj
      have ha : (A.equivFin.symm j).1 ∈ A := (A.equivFin.symm j).2
      have ha' := (Finset.ext_iff.mp h1 _).mp ha
      rw [hsupI] at ha'
      obtain ⟨j', hj', heq'⟩ := ha'
      have : j = j' := A.equivFin.symm.injective (Subtype.ext heq')
      subst this
      exact hj hj'
    · intro hj
      have hsub : I ⊆ Finset.univ.erase (Fin.natAdd A.card j) := fun x hx =>
        Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hx), Finset.mem_univ _⟩
      have hle := Finset.sum_le_sum_of_subset (f := fun i => ((witness A k i).level : ℕ)) hsub
      have hsplit := Finset.add_sum_erase Finset.univ (fun i => ((witness A k i).level : ℕ))
        (Finset.mem_univ (Fin.natAdd A.card j))
      rw [hlev] at hsplit
      have hone : ((witness A k (Fin.natAdd A.card j)).level : ℕ) = 1 := by
        simp [witness, Fin.append_right]
      omega

/-- The exact relative Davenport constant: for every type `U`, finite `A ⊆ U` and level
`k ∈ {0, 1, 2}`, the longest minimal sequences with sum `(A, k)` have length `|A| + k`. -/
theorem result (A : Finset U) (k : Fin 3) :
    IsGreatest (minimalLengths (⟨A, k⟩ : Capped U)) (A.card + k) :=
  ⟨⟨witness A k, lower A k⟩, fun _ ⟨f, hf⟩ => upper A k _ f hf⟩

#print axioms result

end D5.S0.Certificates.Algebra.CappedUnionDavenport
