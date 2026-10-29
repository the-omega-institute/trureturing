/- GID: D5/S0/Certificates/Algebra/WangConjecture326Refutation
   generality: G
   mirror-B: D5/B/S0/Certificates/Algebra/WangConjecture326Refutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Defs, mathlib/module/Mathlib.GroupTheory.Congruence.Defs, mathlib/module/Mathlib.Data.ENat.Lattice]
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/Algebra/WangConjecture326Refutation.claim; result=D5/S0/Certificates/Algebra/WangConjecture326Refutation.result; claim=D5/S0/Certificates/Algebra/WangConjecture326Refutation.claim
   digest: One infinite periodic semigroup has finite algebraic Davenport constant and unbounded nongroup relative constants. -/

import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.GroupTheory.Congruence.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.Semigroup
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.Tactic

/-! # Wang's Conjecture 3.26

The ordinary convolution algebra retains every basis label. Periodicity is
pointwise finiteness of the positive cyclic subsemigroup, with no finiteness
assumption on the ambient semigroup. All coefficients are positional.
-/

namespace D5.S0.Certificates.Algebra.WangConjecture326Refutation

noncomputable section

/-- Positive cyclic generation does not adjoin a zeroth multiple. -/
def cyclic {S : Type*} [AddSemigroup S] (a : S) : AddSubsemigroup S :=
  AddSubsemigroup.closure {a}

/-- Every individual positive cyclic subsemigroup is finite. -/
def Periodic (S : Type*) [AddSemigroup S] : Prop :=
  ∀ a : S, (cyclic a : Set S).Finite

/-- Idempotency in the actual positive cyclic subsemigroup. -/
def IsCyclicIdempotent {S : Type*} [AddSemigroup S] (a e : S) : Prop :=
  e ∈ cyclic a ∧ e + e = e

/-- Choice of the cyclic idempotent; the fallback is unused for periodic S. -/
def cyclicIdempotent {S : Type*} [AddSemigroup S] (a : S) : S := by
  classical
  exact if h : ∃ e, IsCyclicIdempotent a e then h.choose else a

private theorem periodic_idempotent {S : Type*} [AddSemigroup S]
    (hp : Periodic S) (a : S) : IsCyclicIdempotent a (cyclicIdempotent a) := by
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  have ha : a ∈ cyclic a := AddSubsemigroup.subset_closure (by simp)
  obtain ⟨e, he, hee⟩ := exists_idempotent_in_compact_add_subsemigroup
    (fun _ : S => continuous_of_discreteTopology) (cyclic a : Set S)
    ⟨a, ha⟩ (hp a).isCompact (fun _ hx _ hy => (cyclic a).add_mem hx hy)
  have h : ∃ e, IsCyclicIdempotent a e := ⟨e, he, hee⟩
  simpa [cyclicIdempotent, h] using h.choose_spec

/-- A group identity may be any element of the positive cyclic subsemigroup. -/
def CyclicIsGroup {S : Type*} [AddSemigroup S] (a : S) : Prop :=
  ∃ e ∈ cyclic a, (∀ x ∈ cyclic a, e + x = x) ∧
    ∀ x ∈ cyclic a, ∃ y ∈ cyclic a, x + y = e

/-- Ordinary semigroup-algebra factor over an arbitrary commutative unitary ring. -/
def factor {S R : Type*} [AddCommSemigroup S] [CommRing R] (a : S) (c : R) :
    AddMonoidAlgebra R S :=
  AddMonoidAlgebra.single a 1 - AddMonoidAlgebra.single (cyclicIdempotent a) c

/-- Nonempty products require no unit in the semigroup algebra.
Length zero contributes only zero to the length supremum. -/
def factorProduct {S R : Type*} [AddCommSemigroup S] [CommRing R] :
    List S → (ℕ → R) → AddMonoidAlgebra R S
  | [], _ => 0
  | a :: l, c => (l.zipIdx).foldl
      (fun p xi => p * factor xi.1 (c (xi.2 + 1))) (factor a (c 0))

/-- Each occupied position has its own independently quantified nonzero coefficient. -/
def GoodSequence {S R : Type*} [AddCommSemigroup S] [CommRing R] (l : List S) : Prop :=
  ∀ c : ℕ → R, (∀ i, i < l.length → c i ≠ 0) → factorProduct l c ≠ 0

/-- Supremum of all finite admissible lengths; top means unbounded finite lengths. -/
def algebraicD (S R : Type*) [AddCommSemigroup S] [CommRing R] : ℕ∞ :=
  ⨆ (l : List S) (_ : GoodSequence (R := R) l), (l.length : ℕ∞)

/-- Principal ideals include their generator even when S has no identity. -/
def principalIdeal {S : Type*} [AddSemigroup S] (a : S) : Set S :=
  {x | x = a ∨ ∃ c, x = a + c}

/-- The actual Green relation in a commutative semigroup. -/
def greenCon (S : Type*) [AddCommSemigroup S] : AddCon S where
  r a b := principalIdeal a = principalIdeal b
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  add' := by
    intro a b c d hab hcd
    have move {a b c : S} (h : principalIdeal a = principalIdeal b) :
        principalIdeal (a+c) = principalIdeal (b+c) := by
      have step {a b : S} (h : a ∈ principalIdeal b) :
          principalIdeal (a+c) ⊆ principalIdeal (b+c) := by
        rcases h with rfl | ⟨z, rfl⟩
        · exact Set.Subset.rfl
        · rintro x (rfl | ⟨w, rfl⟩)
          · exact Or.inr ⟨z, by ac_rfl⟩
          · exact Or.inr ⟨z+w, by ac_rfl⟩
      apply Set.Subset.antisymm
      · apply step; rw [← h]; exact Or.inl rfl
      · apply step; rw [h]; exact Or.inl rfl
    exact (move hab).trans (by simpa [add_comm] using move (c := b) hcd)

/-- The empty sequence sums only to an identity already present in S. -/
def SequenceSum {S : Type*} [AddSemigroup S] : List S → S → Prop
  | [], a => ∀ x : S, a + x = x ∧ x + a = x
  | x :: l, a => l.foldl (· + ·) x = a

/-- No proper subsequence, including the empty one, has the same sum. -/
def IrreducibleAt {S : Type*} [AddSemigroup S] (l : List S) (a : S) : Prop :=
  SequenceSum l a ∧ ∀ u, u.Sublist l → u.length < l.length → ¬ SequenceSum u a

/-- Relative Davenport constant at one sum, not the global reducibility threshold. -/
def relativeD {S : Type*} [AddSemigroup S] (a : S) : ℕ∞ :=
  ⨆ (l : List S) (_ : IrreducibleAt l a), (l.length : ℕ∞)

/-- Exactly the source's supremum over nongroup positive cyclic elements. -/
def nongroupSup (S : Type*) [AddCommSemigroup S] : ℕ∞ :=
  ⨆ (a : S) (_ : ¬ CyclicIsGroup a), relativeD ((greenCon S).toQuotient a)

/-- The complete universal implication of arXiv:2509.18724v1 Conjecture 3.26. -/
def claim : Prop :=
  ∀ (S : Type) [AddCommSemigroup S], Periodic S →
    ∀ (R : Type) [CommRing R], algebraicD S R < ⊤ → nongroupSup S < ⊤

/-- Finite subsets of N with a level in {0,1,2}. The carrier is not finite. -/
structure Model where
  support : Finset ℕ
  level : Fin 3
  deriving DecidableEq

instance : Infinite Model := Infinite.of_injective
  (fun n : ℕ => (⟨{n},0⟩ : Model)) (by
    intro n m h
    exact Finset.singleton_injective (congrArg Model.support h))

/-- Union and min-capped addition, never modular Fin addition. -/
def modelAdd (x y : Model) : Model :=
  ⟨x.support ∪ y.support, ⟨min 2 (x.level.val + y.level.val), by omega⟩⟩

instance : Add Model := ⟨modelAdd⟩
instance : Zero Model := ⟨⟨∅, 0⟩⟩

private theorem model_ext {x y : Model} (hA : x.support = y.support)
    (hk : x.level = y.level) : x = y := by
  cases x; cases y; simp_all

@[simp] private theorem support_add (x y : Model) :
    (x+y).support = x.support ∪ y.support := rfl

@[simp] private theorem level_add_val (x y : Model) :
    (x+y).level.val = min 2 (x.level.val+y.level.val) := rfl

instance : AddCommMonoid Model where
  add_assoc x y z := by
    apply model_ext
    · exact Finset.union_assoc _ _ _
    · apply Fin.ext; change min 2 (min 2 (_+_) + _) = min 2 (_ + min 2 (_+_)); omega
  add_comm x y := by
    apply model_ext
    · exact Finset.union_comm _ _
    · apply Fin.ext; change min 2 (_+_) = min 2 (_+_); omega
  zero_add x := by
    apply model_ext
    · exact Finset.empty_union _
    · apply Fin.ext; change min 2 (0+x.level.val) = x.level.val; omega
  add_zero x := by
    apply model_ext
    · exact Finset.union_empty _
    · apply Fin.ext; change min 2 (x.level.val+0) = x.level.val; omega
  nsmul := nsmulRec

/-- The idempotent reached after two positive summands. -/
def modelE (x : Model) : Model := ⟨x.support, if x.level = 0 then 0 else 2⟩

private theorem model_laws (x : Model) :
    x+x = modelE x ∧ x+modelE x = modelE x ∧ modelE x+modelE x = modelE x := by
  obtain ⟨A, k⟩ := x
  fin_cases k <;> simp [modelE, modelAdd, HAdd.hAdd, Add.add]

private theorem model_cyclic (x : Model) :
    (cyclic x : Set Model) = {x, modelE x} := by
  let T : AddSubsemigroup Model :=
    { carrier := {x, modelE x}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
        rcases ha with ha | ha <;> rcases hb with hb | hb
        all_goals rw [ha,hb]
        · exact Or.inr (model_laws x).1
        · exact Or.inr (model_laws x).2.1
        · exact Or.inr (by rw [add_comm]; exact (model_laws x).2.1)
        · exact Or.inr (model_laws x).2.2 }
  apply Set.Subset.antisymm
  · have h : cyclic x ≤ T := AddSubsemigroup.closure_le.mpr (by
      intro a ha
      have he : a = x := ha
      subst a
      exact Or.inl rfl)
    exact h
  · intro a ha
    have hx : x ∈ cyclic x := AddSubsemigroup.subset_closure (by simp)
    rcases ha with rfl | ha
    · exact hx
    · rw [Set.mem_singleton_iff] at ha
      rw [ha, ← (model_laws x).1]
      exact (cyclic x).add_mem hx hx

private theorem model_periodic : Periodic Model := by
  intro x; rw [model_cyclic]; exact Set.toFinite _

private theorem model_e (x : Model) : cyclicIdempotent x = modelE x := by
  have h := periodic_idempotent model_periodic x
  have hm : cyclicIdempotent x ∈ (cyclic x : Set Model) := h.1
  rw [model_cyclic] at hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with hx | hx
  · have he := h.2
    rw [hx, (model_laws x).1] at he
    exact hx.trans he.symm
  · exact hx

private theorem pair_vanish (x y : Model) : factor x (1 : ℚ) * factor y 1 = 0 := by
  by_cases hx : x.level = 0 ∨ x.level = 2
  · have he : modelE x = x := by
      obtain ⟨A,k⟩ := x; rcases hx with hx | hx <;> simp_all [modelE]
    simp [factor, model_e, he]
  by_cases hy : y.level = 0 ∨ y.level = 2
  · have he : modelE y = y := by
      obtain ⟨A,k⟩ := y; rcases hy with hy | hy <;> simp_all [modelE]
    simp [factor, model_e, he]
  have hx1 : x.level = 1 := by apply Fin.ext; simp only [Fin.ext_iff] at hx ⊢; omega
  have hy1 : y.level = 1 := by apply Fin.ext; simp only [Fin.ext_iff] at hy ⊢; omega
  have hxy : x+y = x+modelE y ∧ x+y = modelE x+y ∧
      x+y = modelE x+modelE y := by
    obtain ⟨A,k⟩ := x; obtain ⟨B,l⟩ := y
    simp_all [modelE, modelAdd, HAdd.hAdd, Add.add]
  simp only [factor, model_e, sub_mul, mul_sub,
    AddMonoidAlgebra.single_mul_single, mul_one, ← hxy.1, ← hxy.2.1, ← hxy.2.2]
  abel

private theorem zero_fold (l : List (Model × ℕ)) :
    l.foldl (fun p xi => p * factor xi.1 (1 : ℚ)) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa only [List.foldl_cons, zero_mul] using ih

private theorem finite_d : algebraicD Model ℚ ≤ 1 := by
  refine iSup_le fun l => iSup_le fun hl => ?_
  have hlen : l.length ≤ 1 := by
    by_contra hlen
    obtain ⟨x,y,t,rfl⟩ : ∃ x y t, l = x::y::t := by
      cases l with
      | nil => simp at hlen
      | cons x t => cases t with
        | nil => simp at hlen
        | cons y t => exact ⟨x,y,t,rfl⟩
    apply hl (fun _ => 1) (by simp)
    simpa [factorProduct, List.zipIdx_cons, pair_vanish, List.foldl_cons] using
      zero_fold (t.zipIdx 1)
  exact_mod_cast hlen

private theorem ideal_coordinates (x a : Model) :
    x ∈ principalIdeal a ↔ a.support ⊆ x.support ∧ a.level.val ≤ x.level.val := by
  constructor
  · rintro (rfl | ⟨c, rfl⟩)
    · exact ⟨Finset.Subset.refl _, le_rfl⟩
    · constructor
      · exact Finset.subset_union_left
      · change _ ≤ min 2 (_+_); omega
  · rintro ⟨hA,hk⟩
    refine Or.inr ⟨⟨x.support, ⟨x.level.val-a.level.val, by omega⟩⟩, ?_⟩
    apply model_ext
    · exact (Finset.union_eq_right.mpr hA).symm
    · apply Fin.ext; change _ = min 2 (_+(_-_)); omega

private theorem quotient_injective : Function.Injective (greenCon Model).toQuotient := by
  intro a b h
  have hg : principalIdeal a = principalIdeal b := Quotient.exact h
  have ha : a ∈ principalIdeal b := by rw [← hg]; exact Or.inl rfl
  have hb : b ∈ principalIdeal a := by rw [hg]; exact Or.inl rfl
  rw [ideal_coordinates] at ha hb
  apply model_ext
  · exact Finset.Subset.antisymm hb.1 ha.1
  · exact Fin.ext (Nat.le_antisymm hb.2 ha.2)

/-- A subadditive weight detecting all n independent singleton terms and the marker. -/
def weight (x : Model) : ℕ := x.support.card + if x.level = 0 then 0 else 1

private theorem weight_add (x y : Model) : weight (x+y) ≤ weight x + weight y := by
  have hc := Finset.card_union_le x.support y.support
  unfold weight
  rw [support_add]
  by_cases hx : x.level = 0 <;> by_cases hy : y.level = 0
  · have hxy : (x+y).level = 0 := by
      apply Fin.ext
      rw [level_add_val]
      simp [hx,hy]
    simp only [hx,hy,hxy,ite_true,add_zero]; exact hc
  · simp only [hx,hy,ite_true,ite_false,add_zero]; split_ifs <;> omega
  · simp only [hx,hy,ite_true,ite_false,add_zero]; split_ifs <;> omega
  · simp only [hx,hy,ite_false]; split_ifs <;> omega

/-- The marked transient and one fresh singleton at each stage. -/
def witnessSequence : ℕ → List Model
  | 0 => [⟨∅,1⟩]
  | n+1 => ⟨{n},0⟩ :: witnessSequence n

/-- All targets belong to this one fixed infinite carrier. -/
def target (n : ℕ) : Model := ⟨Finset.range n,1⟩

private theorem sequence_facts (n : ℕ) :
    (witnessSequence n).length = n+1 ∧ (witnessSequence n).sum = target n ∧
      ∀ x ∈ witnessSequence n, weight x = 1 := by
  induction n with
  | zero => simp [witnessSequence, target, weight]
  | succ n ih =>
    refine ⟨by simp [witnessSequence,ih.1], ?_, ?_⟩
    · rw [witnessSequence,List.sum_cons,ih.2.1]
      apply model_ext
      · simp [target,Finset.range_add_one,Finset.union_comm]
      · rfl
    · intro x hx
      simp only [witnessSequence,List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp [weight]
      · exact ih.2.2 x hx

private theorem weight_sum (l : List Model) (h : ∀ x ∈ l, weight x = 1) :
    weight l.sum ≤ l.length := by
  induction l with
  | nil => change 0 ≤ 0; exact le_rfl
  | cons x l ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    have hw := weight_add x l.sum
    simp only [List.sum_cons,List.length_cons]
    omega

private theorem sum_iff {M : Type*} [AddMonoid M] (l : List M) (a : M) :
    SequenceSum l a ↔ l.sum = a := by
  cases l with
  | nil =>
    constructor
    · intro h; simpa using (h 0).1.symm
    · intro h; simp only [List.sum_nil] at h; subst a; simp [SequenceSum]
  | cons x l =>
    simp only [SequenceSum,List.sum_eq_foldl,List.foldl_cons,zero_add]

private def quotientHom : Model →+ (greenCon Model).Quotient where
  toFun := (greenCon Model).toQuotient
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem quotient_irreducible (n : ℕ) : IrreducibleAt
    ((witnessSequence n).map quotientHom) (quotientHom (target n)) := by
  constructor
  · rw [sum_iff, ← map_list_sum, (sequence_facts n).2.1]
  · intro u hu hlen hsum
    obtain ⟨v,hv,rfl⟩ := List.sublist_map_iff.mp hu
    rw [sum_iff, ← map_list_sum] at hsum
    have heq : v.sum = target n := quotient_injective hsum
    have hw := weight_sum v (fun x hx => (sequence_facts n).2.2 x (hv.subset hx))
    rw [heq] at hw
    have htarget : weight (target n) = n+1 := by simp [weight,target]
    simp only [List.length_map,(sequence_facts n).1] at hlen
    omega

private theorem nongroup_target (n : ℕ) : ¬ CyclicIsGroup (target n) := by
  rintro ⟨e,he,hid,_⟩
  have ht : target n ∈ cyclic (target n) := AddSubsemigroup.subset_closure (by simp)
  have h := hid (target n) ht
  change e ∈ (cyclic (target n) : Set Model) at he
  rw [model_cyclic] at he
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at he
  rcases he with rfl | he
  · have hh := congrArg (fun x : Model => x.level.val) h
    change min 2 (1+1) = 1 at hh; omega
  · rw [he,add_comm,(model_laws _).2.1] at h
    have hh := congrArg (fun x : Model => x.level.val) h
    norm_num [modelE,target] at hh

private theorem unbounded_relative : nongroupSup Model = ⊤ := by
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  have hl : (n+1 : ℕ∞) ≤ relativeD (quotientHom (target n)) :=
    le_iSup_of_le ((witnessSequence n).map quotientHom)
      (le_iSup_of_le (quotient_irreducible n) (by simp [(sequence_facts n).1]))
  have hu : relativeD (quotientHom (target n)) ≤ nongroupSup Model :=
    le_iSup_of_le (target n) (le_iSup_of_le (nongroup_target n) le_rfl)
  exact (by simp : (n : ℕ∞) ≤ n+1).trans (hl.trans hu)

/- admission_basis: open-problem-resolution (issue #23896).
proof_shape: bind-only for every authored theorem, including result.
The remaining private theorems serve the result's derivation; none is an escape witness.
The Infinite Model instance independently certifies the fixed witness's infinitude;
it is not consumed by result and is not a result helper or escape witness.
Only the designated literal refutation theorem is public and audit-exempt. -/
/-- The entire published implication fails for the single infinite periodic model. -/
theorem result : ¬ claim := by
  intro h
  have hf : algebraicD Model ℚ < ⊤ := lt_of_le_of_lt finite_d (by simp)
  have hc := h Model model_periodic ℚ hf
  rw [unbounded_relative] at hc
  exact (lt_irrefl _ hc)

end

end D5.S0.Certificates.Algebra.WangConjecture326Refutation
