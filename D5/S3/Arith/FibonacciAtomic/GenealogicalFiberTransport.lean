/- GID: D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Ordered source fibers and injective Fibonacci genealogical transport. -/

import D5.S3.Arith.FibonacciAtomic.GraftAffineClosure
import D5.S3.TotalVariation.Pinsker
import Mathlib.Algebra.Free
import Mathlib.Combinatorics.Enumerative.Catalan.Tree
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sets
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport

open scoped BigOperators
open GraftAffineClosure (step quantity)

/-- Actual nonempty ordered binary trees; true labels alpha and false labels beta. -/
abbrev Source := FreeMagma Bool

/-- Leaf substitution, extended by the universal property of the free magma. -/
def substitution : Source →ₙ* Source :=
  FreeMagma.lift fun b => if b then .of false else .mul (.of false) (.of true)

/-- Numbers of alpha and beta leaves. -/
def composition : Source → ℕ × ℕ
  | .of true => (1, 0)
  | .of false => (0, 1)
  | .mul s t => composition s + composition t

/-- A fiber is a subset of the actual source algebra. -/
def Fiber (v : ℕ × ℕ) := {t : Source // composition t = v}

/-- The Catalan and binomial expression for a composition fiber. -/
def fiberCount (v : ℕ × ℕ) : ℕ :=
  catalan (v.1 + v.2 - 1) * Nat.choose (v.1 + v.2) v.1

/-- Recursive leaf-label data on an ordered binary shape. -/
def TreeLabels : BinaryTree Unit → Type
  | .nil => Bool
  | .node _ l r => TreeLabels l × TreeLabels r

/-- Recover the actual labeled source, retaining the given ordered shape. -/
def assemble : (s : BinaryTree Unit) → TreeLabels s → Source
  | .nil, b => .of b
  | .node _ l r, p => .mul (assemble l p.1) (assemble r p.2)

/-- Separate a source into its ordered shape and the labels on that shape. -/
def decompose : Source → Σ s : BinaryTree Unit, TreeLabels s
  | .of b => ⟨.nil, b⟩
  | .mul s t => ⟨.node () (decompose s).1 (decompose t).1,
      ((decompose s).2, (decompose t).2)⟩

/-- Labeled shapes and the actual free magma are equivalent. -/
def sourceEquiv : Source ≃ Σ s : BinaryTree Unit, TreeLabels s where
  toFun := decompose
  invFun p := assemble p.1 p.2
  left_inv t := by
    induction t with
    | of b => rfl
    | mul s t hs ht => simpa only [decompose, assemble, hs, ht]
  right_inv p := by
    rcases p with ⟨s, x⟩
    induction s with
    | nil => rfl
    | node u l r hl hr =>
      cases u
      rcases x with ⟨x, y⟩
      simpa only [assemble, decompose] using
        congrArg₂ (fun a b : Σ s : BinaryTree Unit, TreeLabels s =>
          (⟨.node () a.1 b.1, (a.2, b.2)⟩ : Σ s : BinaryTree Unit, TreeLabels s))
          (hl x) (hr y)

/-- Left-to-right labels are functions on the leaf positions. -/
def labelsEquiv : (s : BinaryTree Unit) → TreeLabels s ≃ (Fin s.numLeaves → Bool)
  | .nil => by
    change Bool ≃ (Fin 1 → Bool)
    exact
      { toFun := fun b _ => b
        invFun := fun f => f 0
        left_inv := fun _ => rfl
        right_inv := fun f => funext fun i => congrArg f (Subsingleton.elim _ _) }
  | .node _ l r =>
    { toFun := fun p => Fin.addCases (labelsEquiv l p.1) (labelsEquiv r p.2)
      invFun := fun f => ((labelsEquiv l).symm (fun i => f (Fin.castAdd r.numLeaves i)),
        (labelsEquiv r).symm (fun i => f (Fin.natAdd l.numLeaves i)))
      left_inv := by
        intro p
        apply Prod.ext <;> simp
      right_inv := by
        intro f
        funext i
        refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp }

/-- Complete shape and indexed leaf-label encoding of the actual source. -/
def indexedEquiv : Source ≃ Σ s : BinaryTree Unit, Fin s.numLeaves → Bool :=
  sourceEquiv.trans (Equiv.sigmaCongrRight labelsEquiv)

/-- The native substitution has no collisions between leaves and compound sources. -/
private theorem substitution_injective : Function.Injective substitution := by
  have no_alpha (t : Source) : substitution t ≠ .of true := by
    cases t with
    | of b =>
      cases b <;> simp only [substitution, FreeMagma.lift_of, Bool.false_eq_true,
        ↓reduceIte] <;> intro h <;> injection h <;> contradiction
    | mul s t => intro h; change FreeMagma.mul _ _ = .of true at h; cases h
  intro s
  induction s with
  | of b =>
    intro t h
    cases b with
    | false =>
      cases t with
      | of c => cases c <;> simp_all [substitution]
      | mul t u =>
        change FreeMagma.mul (.of false) (.of true) =
          FreeMagma.mul (substitution t) (substitution u) at h
        injection h with ht hu
        exact False.elim (no_alpha u hu.symm)
    | true =>
      cases t with
      | of c => cases c <;> simp_all [substitution]
      | mul t u => change .of false = FreeMagma.mul _ _ at h; cases h
  | mul s u hs hu =>
    intro t h
    cases t with
    | of b =>
      cases b with
      | false =>
        change FreeMagma.mul (substitution s) (substitution u) =
          FreeMagma.mul (.of false) (.of true) at h
        injection h with h1 h2
        exact False.elim (no_alpha u h2)
      | true => change FreeMagma.mul _ _ = .of false at h; cases h
    | mul t v =>
      change FreeMagma.mul (substitution s) (substitution u) =
        FreeMagma.mul (substitution t) (substitution v) at h
      injection h with h1 h2
      exact congrArg₂ FreeMagma.mul (hs h1) (hu h2)

/-- The composition of a shaped source is the sum of its actual leaf labels. -/
private theorem assemble_composition (s : BinaryTree Unit) (f : Fin s.numLeaves → Bool) :
    composition (assemble s ((labelsEquiv s).symm f)) =
      (∑ i, if f i then 1 else 0, ∑ i, if f i then 0 else 1) := by
  induction s with
  | nil =>
    change composition (.of (f (0 : Fin 1))) =
      (∑ i : Fin 1, if f i then 1 else 0, ∑ i : Fin 1, if f i then 0 else 1)
    cases h : f (0 : Fin 1) <;> simp only [Fin.sum_univ_one, h, Bool.false_eq_true, ↓reduceIte, composition]
  | node u l r hl hr =>
    change composition (assemble l ((labelsEquiv l).symm
      (fun i => f (Fin.castAdd r.numLeaves i)))) +
      composition (assemble r ((labelsEquiv r).symm
        (fun i => f (Fin.natAdd l.numLeaves i)))) = _
    rw [hl, hr]
    apply Prod.ext
    · change (∑ i, if f (Fin.castAdd r.numLeaves i) then 1 else 0) +
        (∑ i, if f (Fin.natAdd l.numLeaves i) then 1 else 0) =
        ∑ i : Fin (l.numLeaves + r.numLeaves), if f i then 1 else 0
      exact (Fin.sum_univ_add (a := l.numLeaves) (b := r.numLeaves)
        (fun i => if f i then (1 : ℕ) else 0)).symm
    · change (∑ i, if f (Fin.castAdd r.numLeaves i) then 0 else 1) +
        (∑ i, if f (Fin.natAdd l.numLeaves i) then 0 else 1) =
        ∑ i : Fin (l.numLeaves + r.numLeaves), if f i then 0 else 1
      exact (Fin.sum_univ_add (a := l.numLeaves) (b := r.numLeaves)
        (fun i => if f i then (0 : ℕ) else 1)).symm

/-- A Boolean assignment is the set of positions assigned alpha. -/
noncomputable def positionsEquiv (L : ℕ) : (Fin L → Bool) ≃ Finset (Fin L) :=
  (Equiv.piCongrRight fun _ => Equiv.propEquivBool.symm).trans Fintype.finsetEquivSet.symm

/-- The actual tree is encoded by its shape and its alpha positions. -/
noncomputable def positionedEquiv : Source ≃ Σ s : BinaryTree Unit, Finset (Fin s.numLeaves) :=
  indexedEquiv.trans (Equiv.sigmaCongrRight fun s => positionsEquiv s.numLeaves)

/-- The fixed-composition fiber corresponds to the shapes and alpha-position subsets. -/
noncomputable def fiberEquiv (v : ℕ × ℕ) (hv : 1 ≤ v.1 + v.2) :
    Fiber v ≃ Σ s : BinaryTree.treesOfNumNodesEq (v.1 + v.2 - 1),
      {A : Finset (Fin s.val.numLeaves) // A.card = v.1} := by
  classical
  have actual_composition (s : BinaryTree Unit) (A : Finset (Fin s.numLeaves)) :
      composition (positionedEquiv.symm ⟨s, A⟩) = (A.card, s.numLeaves - A.card) := by
    change composition (assemble s ((labelsEquiv s).symm ((positionsEquiv _).symm A))) = _
    rw [assemble_composition]
    have hf (i : Fin s.numLeaves) : ((positionsEquiv _).symm A i = true) ↔ i ∈ A := by
      change (@decide (i ∈ A) (Classical.propDecidable _) = true) ↔ i ∈ A
      simp only [decide_eq_true_eq]
    simp_rw [hf]
    have htrue : (∑ i : Fin s.numLeaves, if i ∈ A then 1 else 0) = A.card := by
      simp
    have htotal : (∑ i : Fin s.numLeaves, if i ∈ A then 1 else 0) +
        (∑ i : Fin s.numLeaves, if i ∈ A then 0 else 1) = s.numLeaves := by
      rw [← Finset.sum_add_distrib]
      have hpoint (i : Fin s.numLeaves) :
          (if i ∈ A then (1 : ℕ) else 0) + (if i ∈ A then 0 else 1) = 1 := by
        split_ifs <;> rfl
      simp_rw [hpoint]
      simp
    apply Prod.ext
    · exact htrue
    · dsimp only
      omega
  let e := positionedEquiv.symm.subtypeEquiv (p := fun p =>
    p.1.numNodes = v.1 + v.2 - 1 ∧ p.2.card = v.1)
    (q := fun t => composition t = v) (by
      rintro ⟨s, A⟩
      rw [actual_composition, Prod.mk.injEq]
      have hcard : A.card ≤ s.numLeaves := by
        simpa using Finset.card_le_card (Finset.subset_univ A)
      have hleaves := s.numLeaves_eq_numNodes_succ
      change (s.numNodes = v.1 + v.2 - 1 ∧ A.card = v.1) ↔
        A.card = v.1 ∧ s.numLeaves - A.card = v.2
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> omega)
  refine e.symm.trans ?_
  exact
    { toFun := fun p => ⟨⟨p.val.1, BinaryTree.mem_treesOfNumNodesEq.mpr p.property.1⟩,
        ⟨p.val.2, p.property.2⟩⟩
      invFun := fun p => ⟨⟨p.1.val, p.2.val⟩,
        BinaryTree.mem_treesOfNumNodesEq.mp p.1.property, p.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Every actual composition fiber is finite, including the empty zero fiber. -/
noncomputable instance fiberFintype (v : ℕ × ℕ) : Fintype (Fiber v) := by
  classical
  by_cases hv : 1 ≤ v.1 + v.2
  · exact Fintype.ofEquiv _ (fiberEquiv v hv).symm
  · have length_composition (t : Source) : (composition t).1 + (composition t).2 = t.length := by
      induction t with
      | of b => cases b <;> rfl
      | mul s t hs ht => simp only [composition, Prod.fst_add, Prod.snd_add, FreeMagma.length]
                         omega
    letI : IsEmpty (Fiber v) := ⟨fun t => by
      have hp := t.val.length_pos
      have hl := length_composition t.val
      rw [t.property] at hl
      omega⟩
    exact Fintype.ofIsEmpty

/-- Iterated native substitution as a map of the actual composition fibers. -/
def fiberMap (v : ℕ × ℕ) (n : ℕ) : Fiber v → Fiber (step^[n] v) := by
  have one_step (t : Source) : composition (substitution t) = step (composition t) := by
    induction t with
    | of b => cases b <;> rfl
    | mul s t hs ht =>
      change composition (substitution s) + composition (substitution t) = _
      rw [hs, ht]
      ext <;> simp [step, composition, add_assoc, add_comm, add_left_comm]
  have transport (n : ℕ) (t : Source) : composition (substitution^[n] t) =
      step^[n] (composition t) := by
    induction n with
    | zero => rfl
    | succ n hn => rw [Function.iterate_succ_apply', one_step, hn,
        Function.iterate_succ_apply']
  exact fun t => ⟨substitution^[n] t.val, by rw [transport, t.property]⟩

/-- Real uniform mass on the actual finite fiber. -/
noncomputable def uniformMass (v : ℕ × ℕ) : Fiber v → ℝ :=
  fun _ => (Nat.card (Fiber v) : ℝ)⁻¹

/-- The actual pushforward sums the source mass over all preimages of a target tree. -/
noncomputable def pushedMass (v : ℕ × ℕ) (n : ℕ) : Fiber (step^[n] v) → ℝ :=
  by classical exact fun y => ∑ x : Fiber v, if fiberMap v n x = y then uniformMass v x else 0

/-- Total variation on the same target composition fiber. -/
noncomputable def transportVariation (v : ℕ × ℕ) (n : ℕ) : ℝ :=
  D5.S3.TotalVariation.Pinsker.totalVariation (pushedMass v n) (uniformMass (step^[n] v))

/-- Actual fibers have their Catalan and binomial cardinality. -/
private theorem fiber_cardinality (v : ℕ × ℕ) (hv : 1 ≤ v.1 + v.2) :
    Nat.card (Fiber v) = fiberCount v := by
  classical
  rw [Nat.card_congr (fiberEquiv v hv), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp_rw [Fintype.card_finset_len, Fintype.card_fin]
  have hleaves (s : BinaryTree.treesOfNumNodesEq (v.1 + v.2 - 1)) :
      s.val.numLeaves = v.1 + v.2 := by
    have hs := BinaryTree.mem_treesOfNumNodesEq.mp s.property
    rw [BinaryTree.numLeaves_eq_numNodes_succ, hs]
    omega
  simp_rw [hleaves]
  simp [fiberCount, Fintype.card_coe, BinaryTree.treesOfNumNodesEq_card_eq_catalan]

#print axioms substitution_injective
#print axioms fiberEquiv
#print axioms fiber_cardinality
#print axioms fiberMap

end D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
