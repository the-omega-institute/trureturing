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

instance fiberDecidableEq (v : ℕ × ℕ) : DecidableEq (Fiber v) :=
  inferInstanceAs (DecidableEq {t : Source // composition t = v})

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

/-- Exact hidden fibers, probability transport, and asymptotic singularity. -/
theorem result :
    (∀ a b : ℕ, 1 ≤ a + b →
      Finite (Fiber (a, b)) ∧ Nat.card (Fiber (a, b)) = fiberCount (a, b) ∧
      Nonempty (Fiber (a, b)) ∧
      (∀ t : Fiber (a, b), ∀ n : ℕ,
        composition (substitution^[n] t.val) = step^[n] (a, b) ∧
        quantity (composition (substitution^[n] t.val)) = quantity (step^[n] (a, b))) ∧
      (∀ n : ℕ, Function.Injective (fiberMap (a, b) n) ∧
        (Finset.univ.image (fiberMap (a, b) n)).card = fiberCount (a, b) ∧
        (∀ y, 0 ≤ pushedMass (a, b) n y ∧ 0 ≤ uniformMass (step^[n] (a, b)) y) ∧
        (∑ y, pushedMass (a, b) n y) = 1 ∧
        (∑ y, uniformMass (step^[n] (a, b)) y) = 1 ∧
        transportVariation (a, b) n = 1 - (fiberCount (a, b) : ℝ) /
          (fiberCount (step^[n] (a, b)) : ℝ)) ∧
      (2 ≤ a + b → 1 - (2 : ℝ)⁻¹ ^ b ≤ transportVariation (a, b) 1) ∧
      Filter.Tendsto (transportVariation (a, b)) Filter.atTop (nhds 1)) ∧
    transportVariation (1, 1) 1 = (2 / 3 : ℝ) := by
  classical
  have count_pos (v : ℕ × ℕ) (hv : 1 ≤ v.1 + v.2) : 0 < fiberCount v := by
    have hc : 0 < catalan (v.1 + v.2 - 1) := by
      have hp := Nat.centralBinom_pos (v.1 + v.2 - 1)
      rw [← succ_mul_catalan_eq_centralBinom] at hp
      by_contra hn
      have hzero : catalan (v.1 + v.2 - 1) = 0 := by omega
      simp only [hzero, mul_zero] at hp
      omega
    exact Nat.mul_pos hc (Nat.choose_pos (by omega))
  have step_nonempty (v : ℕ × ℕ) (hv : 1 ≤ v.1 + v.2) (n : ℕ) :
      1 ≤ (step^[n] v).1 + (step^[n] v).2 := by
    induction n with
    | zero => exact hv
    | succ n hn => simpa only [Function.iterate_succ_apply', step] using
        (show 1 ≤ (step^[n] v).2 + ((step^[n] v).1 + (step^[n] v).2) by omega)
  have map_injective (v : ℕ × ℕ) (n : ℕ) : Function.Injective (fiberMap v n) := by
    intro x y h
    apply Subtype.ext
    exact (substitution_injective.iterate n) (congrArg Subtype.val h)
  have variation (v : ℕ × ℕ) (hv : 1 ≤ v.1 + v.2) (n : ℕ) :
      transportVariation v n = 1 - (fiberCount v : ℝ) /
        (fiberCount (step^[n] v) : ℝ) := by
    let S := Finset.univ.image (fiberMap v n)
    let k : ℝ := Nat.card (Fiber v)
    let m : ℝ := Nat.card (Fiber (step^[n] v))
    have hk : 0 < k := by
      dsimp [k]
      rw [fiber_cardinality v hv]
      exact_mod_cast count_pos v hv
    have hm : 0 < m := by
      dsimp [m]
      rw [fiber_cardinality _ (step_nonempty v hv n)]
      exact_mod_cast count_pos _ (step_nonempty v hv n)
    have hS : S.card = Nat.card (Fiber v) := by
      dsimp [S]
      rw [Finset.card_image_of_injective _ (map_injective v n), Finset.card_univ,
        Nat.card_eq_fintype_card]
    have hkm : k ≤ m := by
      have h := Finset.card_le_univ S
      rw [hS, ← Nat.card_eq_fintype_card] at h
      change (Nat.card (Fiber v) : ℝ) ≤ (Nat.card (Fiber (step^[n] v)) : ℝ)
      exact_mod_cast h
    have push_value (y : Fiber (step^[n] v)) :
        pushedMass v n y = if y ∈ S then k⁻¹ else 0 := by
      dsimp only [pushedMass, uniformMass]
      by_cases hy : y ∈ S
      · rcases Finset.mem_image.mp hy with ⟨x, _, rfl⟩
        simp only [(map_injective v n).eq_iff, Finset.sum_ite_eq', Finset.mem_univ,
          ↓reduceIte, hy, k]
      · rw [if_neg hy]
        apply Finset.sum_eq_zero
        intro x _
        have hne : fiberMap v n x ≠ y := by
          intro h
          exact hy (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, h⟩)
        simp only [hne, ↓reduceIte]
    have uniform_value (y : Fiber (step^[n] v)) : uniformMass (step^[n] v) y = m⁻¹ := rfl
    have hS_sum : (∑ y ∈ S, |pushedMass v n y - uniformMass (step^[n] v) y|) =
        k * (k⁻¹ - m⁻¹) := by
      calc
        _ = ∑ _y ∈ S, (k⁻¹ - m⁻¹) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [push_value, uniform_value, if_pos hy, abs_of_nonneg]
          exact sub_nonneg.mpr ((inv_le_inv₀ hm hk).mpr hkm)
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hS]; rfl
    have hC_sum : (∑ y ∈ Sᶜ, |pushedMass v n y - uniformMass (step^[n] v) y|) =
        (m - k) * m⁻¹ := by
      calc
        _ = ∑ _y ∈ Sᶜ, m⁻¹ := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [push_value, uniform_value, if_neg (Finset.mem_compl.mp hy)]
          simp [abs_of_nonneg (inv_nonneg.mpr hm.le)]
        _ = _ := by
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_compl, hS]
          rw [Nat.cast_sub (by
            rw [← Nat.card_eq_fintype_card]
            change (Nat.card (Fiber v) : ℕ) ≤ Nat.card (Fiber (step^[n] v))
            have hreal : (Nat.card (Fiber v) : ℝ) ≤ (Nat.card (Fiber (step^[n] v)) : ℝ) := hkm
            exact_mod_cast hreal)]
          simp only [k, m, Nat.card_eq_fintype_card]
    change (1 / 2 : ℝ) * ∑ y, |pushedMass v n y - uniformMass (step^[n] v) y| = _
    rw [← Finset.sum_add_sum_compl S, hS_sum, hC_sum]
    have hcounts : (fiberCount v : ℝ) / (fiberCount (step^[n] v) : ℝ) = k / m := by
      simp only [k, m, fiber_cardinality v hv,
        fiber_cardinality _ (step_nonempty v hv n)]
    rw [hcounts]
    field_simp
    <;> ring
  constructor
  · intro a b hv
    have hv' : 1 ≤ (a, b).1 + (a, b).2 := hv
    have hnonempty : Nonempty (Fiber (a, b)) := by
      apply Fintype.card_pos_iff.mp
      rw [← Nat.card_eq_fintype_card, fiber_cardinality _ hv']
      exact count_pos _ hv'
    refine ⟨inferInstance, fiber_cardinality _ hv', hnonempty, ?_, ?_, ?_, ?_⟩
    · intro t n
      have h := (fiberMap (a, b) n t).property
      exact ⟨h, congrArg quantity h⟩
    · intro n
      refine ⟨map_injective _ n, ?_, ?_, ?_, ?_, variation _ hv' n⟩
      · rw [Finset.card_image_of_injective _ (map_injective _ n), Finset.card_univ,
          ← Nat.card_eq_fintype_card, fiber_cardinality _ hv']
      · intro y
        constructor
        · unfold pushedMass
          exact Finset.sum_nonneg fun x _ => by
            split_ifs <;> simp [uniformMass]
        · simp [uniformMass]
      · unfold pushedMass
        rw [Finset.sum_comm]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
        simp only [uniformMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card]
        exact mul_inv_cancel₀ (by exact_mod_cast
          (show Nat.card (Fiber (a, b)) ≠ 0 by rw [fiber_cardinality _ hv']; exact (count_pos _ hv').ne'))
      · simp only [uniformMass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card]
        exact mul_inv_cancel₀ (by exact_mod_cast
          (show Nat.card (Fiber (step^[n] (a, b))) ≠ 0 by
            rw [fiber_cardinality _ (step_nonempty _ hv' n)]
            exact (count_pos _ (step_nonempty _ hv' n)).ne'))
    · sorry
    · sorry
  · have h := variation (1, 1) (by decide) 1
    norm_num [fiberCount, step, catalan_one, catalan_two] at h
    exact h

#print axioms result

end D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
