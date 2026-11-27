/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.BitVec, mathlib/module/Mathlib.LinearAlgebra.Matrix.ToLinearEquiv]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.claim; result=D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.result; claim=D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9LocalSaturation72Refutation.claim
   digest: The 72-point three-pair-one-triple support has positive weighted kernels on both parities while every parity contains a row whose neighbor directions fail the partition condition. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedSaturation
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9WeightedStarLift
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Laurent.Q9LaurentDirectionTypes
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves
import Mathlib.Data.BitVec
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Batteries.Tactic.OpenPrivate

/-! A connected balanced cubic support with universal weighted singularity and
overlapping neighbor direction triples on both parities. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9LocalSaturation72Refutation

open scoped BigOperators Matrix
open Finset
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced flip)
open CoordinateHalves.CubeBitMoves (toggle)
open Q9IsotropicHuang (parity flipSign)
open BalancedCubeComponentBoundary (directions mem_directions directions_card)
open SupportedEigenSaturation (selected_neighbor_card)
open Q9BoundaryGram (Interior)
open Q9WeightedSaturation (Rows biadjacency defect)
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open BalancedCubeGirth (adjacent_exists_flip)
open private paritySide from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeLowerBound

abbrev Q9 := Q 9
abbrev Word := BitVec 9

/-! The three pair blocks are `{0,1}`, `{2,3}`, `{4,5}` and the final block is
`{6,7,8}`.  The constructors below use one occupied coordinate in each
selected block. -/

def pairAxis : Fin 3 → Fin 2 → Fin 9 := ![![0, 1], ![2, 3], ![4, 5]]
def tripleAxis : Fin 3 → Fin 9 := ![6, 7, 8]
def otherPair : Fin 3 → Fin 2 → Fin 3 := ![![1, 2], ![0, 2], ![0, 1]]

def pairBit (i : Fin 3) (j : Fin 2) : Word :=
  BitVec.ofNat 9 (2 ^ (pairAxis i j).val)

def tripleBit (j : Fin 3) : Word :=
  BitVec.ofNat 9 (2 ^ (tripleAxis j).val)

abbrev CenterCode := Fin 2 × Fin 2 × Fin 2 × Fin 3
abbrev MiddleCode := Fin 3 × Fin 2 × Fin 2 × Fin 3
abbrev LeafCode := Fin 3 × Fin 2 × Fin 2
abbrev EvenCode := CenterCode ⊕ LeafCode

def centerPair (c : CenterCode) : Fin 3 → Fin 2 := ![c.1, c.2.1, c.2.2.1]

private def centerWord (c : CenterCode) : Word :=
  pairBit 0 c.1 ^^^ pairBit 1 c.2.1 ^^^ pairBit 2 c.2.2.1 ^^^ tripleBit c.2.2.2

private def middleWord (m : MiddleCode) : Word :=
  pairBit (otherPair m.1 0) m.2.1 ^^^
    pairBit (otherPair m.1 1) m.2.2.1 ^^^ tripleBit m.2.2.2

private def leafWord (l : LeafCode) : Word :=
  pairBit (otherPair l.1 0) l.2.1 ^^^ pairBit (otherPair l.1 1) l.2.2

def centerVertex (c : CenterCode) : Q9 := cubeBitVec 9 (centerWord c)
def middleVertex (m : MiddleCode) : Q9 := cubeBitVec 9 (middleWord m)
def leafVertex (l : LeafCode) : Q9 := cubeBitVec 9 (leafWord l)

def centers : Finset Q9 := (univ : Finset CenterCode).image centerVertex
def middles : Finset Q9 := (univ : Finset MiddleCode).image middleVertex
def leaves : Finset Q9 := (univ : Finset LeafCode).image leafVertex

/-- The exact 72-point support. -/
def support : Finset Q9 := centers ∪ middles ∪ leaves

private theorem center_parity (c : CenterCode) : parity (centerVertex c) = false := by
  revert c
  decide +kernel

private theorem middle_parity (m : MiddleCode) : parity (middleVertex m) = true := by
  revert m
  decide +kernel

private theorem leaf_parity (l : LeafCode) : parity (leafVertex l) = false := by
  revert l
  decide +kernel

theorem support_card : support.card = 72 := by
  decide +kernel

abbrev EvenRows := Rows support false
abbrev OddRows := Rows support true
abbrev OddInterior := Interior support false
abbrev EvenInterior := Interior support true

private def centerRow (c : CenterCode) : EvenRows :=
  ⟨⟨centerVertex c,
      mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨c, mem_univ _, rfl⟩))⟩,
    mem_filter.mpr ⟨mem_univ _, center_parity c⟩⟩

private def leafRow (l : LeafCode) : EvenRows :=
  ⟨⟨leafVertex l, mem_union_right _ (mem_image.mpr ⟨l, mem_univ _, rfl⟩)⟩,
    mem_filter.mpr ⟨mem_univ _, leaf_parity l⟩⟩

private def evenRow : EvenCode → EvenRows := Sum.elim centerRow leafRow

private def middleRow (m : MiddleCode) : OddRows :=
  ⟨⟨middleVertex m,
      mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨m, mem_univ _, rfl⟩))⟩,
    mem_filter.mpr ⟨mem_univ _, middle_parity m⟩⟩

private def middleColumn (m : MiddleCode) : OddInterior := by
  refine ⟨⟨middleVertex m, ?_⟩, ?_⟩
  · change parity (middleVertex m) ≠ false
    rw [middle_parity]
    decide
  · exact mem_union_left _ (mem_union_right _ (mem_image.mpr ⟨m, mem_univ _, rfl⟩))

private def centerInterior (c : CenterCode) : EvenInterior := by
  refine ⟨⟨centerVertex c, ?_⟩, ?_⟩
  · change parity (centerVertex c) ≠ true
    rw [center_parity]
    decide
  · exact mem_union_left _ (mem_union_left _ (mem_image.mpr ⟨c, mem_univ _, rfl⟩))

private def leafInterior (l : LeafCode) : EvenInterior := by
  refine ⟨⟨leafVertex l, ?_⟩, ?_⟩
  · change parity (leafVertex l) ≠ true
    rw [leaf_parity]
    decide
  · exact mem_union_right _ (mem_image.mpr ⟨l, mem_univ _, rfl⟩)

private def evenInterior : EvenCode → EvenInterior := Sum.elim centerInterior leafInterior

private def evenWord : EvenCode → Word := Sum.elim centerWord leafWord

private theorem evenWord_injective : Function.Injective evenWord := by
  decide +kernel

private theorem middleWord_injective : Function.Injective middleWord := by
  decide +kernel

private theorem even_codes_of_mem {x : Q9} (hx : x ∈ support) (hp : parity x = false) :
    ∃ e, cubeBitVec 9 (evenWord e) = x := by
  rcases mem_union.mp hx with h | h
  · rcases mem_union.mp h with h | h
    · obtain ⟨c, _, rfl⟩ := mem_image.mp h
      exact ⟨Sum.inl c, rfl⟩
    · obtain ⟨m, _, rfl⟩ := mem_image.mp h
      exact ((show true ≠ false by decide) ((middle_parity m).symm.trans hp)).elim
  · obtain ⟨l, _, rfl⟩ := mem_image.mp h
    exact ⟨Sum.inr l, rfl⟩

private theorem odd_codes_of_mem {x : Q9} (hx : x ∈ support) (hp : parity x = true) :
    ∃ m, middleVertex m = x := by
  rcases mem_union.mp hx with h | h
  · rcases mem_union.mp h with h | h
    · obtain ⟨c, _, rfl⟩ := mem_image.mp h
      exact (Bool.false_ne_true ((center_parity c).symm.trans hp)).elim
    · obtain ⟨m, _, rfl⟩ := mem_image.mp h
      exact ⟨m, rfl⟩
  · obtain ⟨l, _, rfl⟩ := mem_image.mp h
    exact (Bool.false_ne_true ((leaf_parity l).symm.trans hp)).elim

private theorem evenRow_val (e : EvenCode) :
    (evenRow e).1.1 = cubeBitVec 9 (evenWord e) := by cases e <;> rfl

private theorem evenInterior_val (e : EvenCode) :
    (evenInterior e).1.1 = cubeBitVec 9 (evenWord e) := by cases e <;> rfl

private theorem evenRow_bijective : Function.Bijective evenRow := by
  constructor
  · intro x y h
    apply evenWord_injective
    apply (cubeBitVec 9).injective
    rw [← evenRow_val, ← evenRow_val, h]
  · intro y
    have hp : parity y.1.1 = false := (mem_filter.mp y.property).2
    obtain ⟨e, he⟩ := even_codes_of_mem y.1.property hp
    exact ⟨e, Subtype.ext (Subtype.ext ((evenRow_val e).trans he))⟩

private theorem middleColumn_bijective : Function.Bijective middleColumn := by
  constructor
  · intro x y h
    exact middleWord_injective ((cubeBitVec 9).injective (congrArg (fun z => z.1.1) h))
  · intro y
    have hp : parity y.1.1 = true := by
      cases h : parity y.1.1
      · exact (y.1.property h).elim
      · rfl
    obtain ⟨m, hm⟩ := odd_codes_of_mem y.property hp
    exact ⟨m, Subtype.ext (Subtype.ext hm)⟩

private theorem middleRow_bijective : Function.Bijective middleRow := by
  constructor
  · intro x y h
    exact middleWord_injective ((cubeBitVec 9).injective (congrArg (fun z => z.1.1) h))
  · intro y
    have hp : parity y.1.1 = true := (mem_filter.mp y.property).2
    obtain ⟨m, hm⟩ := odd_codes_of_mem y.1.property hp
    exact ⟨m, Subtype.ext (Subtype.ext hm)⟩

private theorem evenInterior_bijective : Function.Bijective evenInterior := by
  constructor
  · intro x y h
    apply evenWord_injective
    apply (cubeBitVec 9).injective
    rw [← evenInterior_val, ← evenInterior_val, h]
  · intro y
    have hp : parity y.1.1 = false := by
      cases h : parity y.1.1
      · rfl
      · exact (y.1.property h).elim
    obtain ⟨e, he⟩ := even_codes_of_mem y.property hp
    exact ⟨e, Subtype.ext (Subtype.ext ((evenInterior_val e).trans he))⟩

private def evenRowEquiv : EvenCode ≃ EvenRows := Equiv.ofBijective evenRow evenRow_bijective
private def oddColumnEquiv : MiddleCode ≃ OddInterior :=
  Equiv.ofBijective middleColumn middleColumn_bijective
private def oddRowEquiv : MiddleCode ≃ OddRows :=
  Equiv.ofBijective middleRow middleRow_bijective
private def evenColumnEquiv : EvenCode ≃ EvenInterior :=
  Equiv.ofBijective evenInterior evenInterior_bijective

/-! The occupancy quotient has three arms. Arm `i` joins the centre occupancy
to the middle and then leaf occupancies that omit pair `i`. -/

private def middleDrop (c : CenterCode) (i : Fin 3) : MiddleCode :=
  (i, centerPair c (otherPair i 0), centerPair c (otherPair i 1), c.2.2.2)

private def middleAdd (l : LeafCode) (t : Fin 3) : MiddleCode :=
  (l.1, l.2.1, l.2.2, t)

private def codeMatrix (w : Fin 9 → ℝ) : Matrix EvenCode MiddleCode ℝ := fun e m =>
  match e with
  | Sum.inl c => ∑ i : Fin 3,
      if middleDrop c i = m then w (pairAxis i (centerPair c i)) else 0
  | Sum.inr l => ∑ t : Fin 3,
      if middleAdd l t = m then w (tripleAxis t) else 0

private def pairSquareSum (w : Fin 9 → ℝ) (i : Fin 3) : ℝ :=
  ∑ a : Fin 2, w (pairAxis i a) ^ 2

private def tripleSquareSum (w : Fin 9 → ℝ) : ℝ :=
  ∑ t : Fin 3, w (tripleAxis t) ^ 2

private def pairTotal (w : Fin 9 → ℝ) : ℝ := ∑ i : Fin 3, pairSquareSum w i

private theorem weight_square_sum (w : Fin 9 → ℝ) :
    (∑ a, w a ^ 2) = pairTotal w + tripleSquareSum w := by
  simp [pairTotal, pairSquareSum, tripleSquareSum, pairAxis, tripleAxis, Fin.sum_univ_succ]
  ring

private def centerMonomial (w : Fin 9 → ℝ) (c : CenterCode) : ℝ :=
  w (pairAxis 0 c.1) * w (pairAxis 1 c.2.1) *
    w (pairAxis 2 c.2.2.1) * w (tripleAxis c.2.2.2)

private def middleMonomial (w : Fin 9 → ℝ) (m : MiddleCode) : ℝ :=
  w (pairAxis (otherPair m.1 0) m.2.1) *
    w (pairAxis (otherPair m.1 1) m.2.2.1) * w (tripleAxis m.2.2.2)

private def leafMonomial (w : Fin 9 → ℝ) (l : LeafCode) : ℝ :=
  w (pairAxis (otherPair l.1 0) l.2.1) *
    w (pairAxis (otherPair l.1 1) l.2.2)

private def pVec (w : Fin 9 → ℝ) : EvenCode → ℝ
  | Sum.inl c => pairTotal w * centerMonomial w c
  | Sum.inr l => tripleSquareSum w * pairSquareSum w l.1 * leafMonomial w l

private def qVec (w : Fin 9 → ℝ) (m : MiddleCode) : ℝ :=
  pairSquareSum w m.1 * middleMonomial w m

private theorem flip_word (x : Word) (a : Fin 9) :
    flip (cubeBitVec 9 x) a = cubeBitVec 9 (toggle x a) :=
  (cubeBitVec_xor_single x a).symm

private theorem center_axes :
    ∀ (c : CenterCode) (m : MiddleCode),
      (univ.filter fun a => toggle (centerWord c) a = middleWord m) =
        ((univ : Finset (Fin 3)).filter fun i => middleDrop c i = m).image
          (fun i => pairAxis i (centerPair c i)) := by
  decide +kernel

private theorem leaf_axes :
    ∀ (l : LeafCode) (m : MiddleCode),
      (univ.filter fun a => toggle (leafWord l) a = middleWord m) =
        ((univ : Finset (Fin 3)).filter fun t => middleAdd l t = m).image tripleAxis := by
  decide +kernel

private theorem center_axis_injective (c : CenterCode) :
    Function.Injective (fun i => pairAxis i (centerPair c i)) := by
  revert c
  decide +kernel

private theorem code_matrix_eq (w : Fin 9 → ℝ) :
    (biadjacency w support false).submatrix evenRowEquiv oddColumnEquiv = codeMatrix w := by
  ext e m
  change (∑ a : Fin 9, if flip ((evenRow e).1.1) a = middleVertex m then w a else 0) = _
  simp only [evenRow_val, middleVertex, flip_word, Equiv.apply_eq_iff_eq]
  rw [← Finset.sum_filter]
  cases e with
  | inl c =>
    change (∑ a ∈ univ.filter (fun a => toggle (centerWord c) a = middleWord m), w a) = _
    rw [center_axes, Finset.sum_image (center_axis_injective c).injOn]
    exact Finset.sum_filter _ _
  | inr l =>
    change (∑ a ∈ univ.filter (fun a => toggle (leafWord l) a = middleWord m), w a) = _
    have ht : Function.Injective tripleAxis := by decide +kernel
    rw [leaf_axes, Finset.sum_image ht.injOn]
    exact Finset.sum_filter _ _

private def centerFill (m : MiddleCode) (a : Fin 2) : CenterCode :=
  let entry (i : Fin 3) := if i = m.1 then a
    else if i = otherPair m.1 0 then m.2.1 else m.2.2.1
  (entry 0, entry 1, entry 2, m.2.2.2)

private def middleLeaf (m : MiddleCode) : LeafCode := (m.1, m.2.1, m.2.2.1)

private theorem center_inputs :
    ∀ m : MiddleCode,
      ((univ : Finset (CenterCode × Fin 3)).filter fun ci => middleDrop ci.1 ci.2 = m) =
        univ.image (fun a : Fin 2 => (centerFill m a, m.1)) := by
  decide +kernel

private theorem leaf_inputs :
    ∀ m : MiddleCode,
      ((univ : Finset (LeafCode × Fin 3)).filter fun lt => middleAdd lt.1 lt.2 = m) =
        {(middleLeaf m, m.2.2.2)} := by
  decide +kernel

private theorem center_fill_injective :
    ∀ m : MiddleCode, Function.Injective (fun a : Fin 2 => (centerFill m a, m.1)) := by
  decide +kernel

private theorem center_forward_term (w : Fin 9 → ℝ) (c : CenterCode) (i : Fin 3) :
    w (pairAxis i (centerPair c i)) * qVec w (middleDrop c i) =
      pairSquareSum w i * centerMonomial w c := by
  rcases c with ⟨a, b, c, t⟩
  fin_cases i
  · change w (pairAxis 0 a) *
        (pairSquareSum w 0 * (w (pairAxis 1 b) * w (pairAxis 2 c) * w (tripleAxis t))) =
      pairSquareSum w 0 * centerMonomial w (a, b, c, t)
    unfold centerMonomial
    ring
  · change w (pairAxis 1 b) *
        (pairSquareSum w 1 * (w (pairAxis 0 a) * w (pairAxis 2 c) * w (tripleAxis t))) =
      pairSquareSum w 1 * centerMonomial w (a, b, c, t)
    unfold centerMonomial
    ring
  · change w (pairAxis 2 c) *
        (pairSquareSum w 2 * (w (pairAxis 0 a) * w (pairAxis 1 b) * w (tripleAxis t))) =
      pairSquareSum w 2 * centerMonomial w (a, b, c, t)
    unfold centerMonomial
    ring

private theorem p_center_fill (w : Fin 9 → ℝ) (m : MiddleCode) (a : Fin 2) :
    w (pairAxis m.1 (centerPair (centerFill m a) m.1)) * pVec w (Sum.inl (centerFill m a)) =
      w (pairAxis m.1 a) ^ 2 * (pairTotal w * middleMonomial w m) := by
  rcases m with ⟨i, b, c, t⟩
  fin_cases i
  · change w (pairAxis 0 a) * (pairTotal w * centerMonomial w (a, b, c, t)) =
      w (pairAxis 0 a) ^ 2 * (pairTotal w * middleMonomial w (0, b, c, t))
    change _ = w (pairAxis 0 a) ^ 2 *
      (pairTotal w * (w (pairAxis 1 b) * w (pairAxis 2 c) * w (tripleAxis t)))
    unfold centerMonomial
    ring
  · change w (pairAxis 1 a) * (pairTotal w * centerMonomial w (b, a, c, t)) =
      w (pairAxis 1 a) ^ 2 * (pairTotal w * middleMonomial w (1, b, c, t))
    change _ = w (pairAxis 1 a) ^ 2 *
      (pairTotal w * (w (pairAxis 0 b) * w (pairAxis 2 c) * w (tripleAxis t)))
    unfold centerMonomial
    ring
  · change w (pairAxis 2 a) * (pairTotal w * centerMonomial w (b, c, a, t)) =
      w (pairAxis 2 a) ^ 2 * (pairTotal w * middleMonomial w (2, b, c, t))
    change _ = w (pairAxis 2 a) ^ 2 *
      (pairTotal w * (w (pairAxis 0 b) * w (pairAxis 1 c) * w (tripleAxis t)))
    unfold centerMonomial
    ring

private theorem code_forward (w : Fin 9 → ℝ) : codeMatrix w *ᵥ qVec w = pVec w := by
  funext e
  rw [Matrix.mulVec, dotProduct]
  cases e with
  | inl c =>
    change (∑ m : MiddleCode, (∑ i : Fin 3,
      if middleDrop c i = m then w (pairAxis i (centerPair c i)) else 0) * qVec w m) = _
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, mem_univ, ite_true, center_forward_term, ← Finset.sum_mul]
    rfl
  | inr l =>
    change (∑ m : MiddleCode, (∑ t : Fin 3,
      if middleAdd l t = m then w (tripleAxis t) else 0) * qVec w m) = _
    simp_rw [Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, mem_univ, ite_true]
    calc
      _ = ∑ t : Fin 3, w (tripleAxis t) ^ 2 * (pairSquareSum w l.1 * leafMonomial w l) := by
        apply Finset.sum_congr rfl
        intro t _
        simp only [qVec, middleMonomial, middleAdd, leafMonomial]
        ring
      _ = _ := by rw [← Finset.sum_mul]; unfold pVec tripleSquareSum; ring

private theorem sum_fiber {A B : Type*} [Fintype A] [Fintype B]
    (P : A → B → Prop) [DecidableRel P] (v : A → B → ℝ) :
    (∑ x, ∑ y, if P x y then v x y else 0) =
      ∑ xy ∈ univ.filter (fun xy : A × B => P xy.1 xy.2), v xy.1 xy.2 := by
  rw [Finset.sum_filter]
  exact (Fintype.sum_prod_type' (fun x y => if P x y then v x y else 0)).symm

private theorem code_backward (w : Fin 9 → ℝ) :
    (codeMatrix w)ᵀ *ᵥ pVec w = (pairTotal w + tripleSquareSum w) • qVec w := by
  funext m
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fintype.sum_sum_type]
  change
    (∑ c : CenterCode, (∑ i : Fin 3,
        if middleDrop c i = m then w (pairAxis i (centerPair c i)) else 0) *
        pVec w (Sum.inl c)) +
    (∑ l : LeafCode, (∑ t : Fin 3,
        if middleAdd l t = m then w (tripleAxis t) else 0) *
        pVec w (Sum.inr l)) = _
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [sum_fiber, sum_fiber, center_inputs, leaf_inputs,
    Finset.sum_image (center_fill_injective m).injOn, Finset.sum_singleton]
  simp_rw [p_center_fill]
  rw [← Finset.sum_mul]
  simp only [pVec, middleLeaf, qVec, middleMonomial, leafMonomial, Pi.smul_apply, smul_eq_mul]
  change pairSquareSum w m.1 * _ + _ = _
  ring

private theorem code_kernel (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i) :
    codeMatrix w *ᵥ qVec w = pVec w ∧
      (codeMatrix w)ᵀ *ᵥ pVec w = (pairTotal w + tripleSquareSum w) • qVec w ∧
      pVec w ≠ 0 ∧ qVec w ≠ 0 := by
  have hpair (i : Fin 3) : 0 < pairSquareSum w i := by
    rw [pairSquareSum, Fin.sum_univ_two]
    exact add_pos (pow_pos (hw _) _) (pow_pos (hw _) _)
  have htotal : 0 < pairTotal w := by
    rw [pairTotal, Fin.sum_univ_three]
    exact add_pos (add_pos (hpair 0) (hpair 1)) (hpair 2)
  refine ⟨code_forward w, code_backward w, ?_, ?_⟩
  · intro h
    let e : EvenCode := Sum.inl (0, 0, 0, 0)
    have hp : 0 < pVec w e := by
      unfold e pVec centerMonomial
      exact mul_pos htotal (mul_pos (mul_pos (mul_pos (hw _) (hw _)) (hw _)) (hw _))
    exact hp.ne' (congrFun h e)
  · intro h
    let m : MiddleCode := (0, 0, 0, 0)
    have hq : 0 < qVec w m := by
      unfold qVec middleMonomial
      exact mul_pos (hpair _) (mul_pos (mul_pos (hw _) (hw _)) (hw _))
    exact hq.ne' (congrFun h m)

private def evenKernel (w : Fin 9 → ℝ) : EvenRows → ℝ :=
  pVec w ∘ evenRowEquiv.symm

private def oddKernel (w : Fin 9 → ℝ) : OddRows → ℝ :=
  qVec w ∘ oddRowEquiv.symm

private theorem even_kernel (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i) :
    defect w (biadjacency w support false) *ᵥ evenKernel w = 0 ∧
      evenKernel w ≠ 0 := by
  classical
  obtain ⟨hforward, hback, hp, hq⟩ := code_kernel w hw
  let M := biadjacency w support false
  have hM : M *ᵥ (qVec w ∘ oddColumnEquiv.symm) = evenKernel w := by
    have hsub := Matrix.submatrix_mulVec_equiv M (qVec w) evenRowEquiv oddColumnEquiv
    rw [code_matrix_eq, hforward] at hsub
    funext x
    obtain ⟨e, rfl⟩ := evenRowEquiv.surjective x
    simpa [evenKernel, Function.comp_def] using (congrFun hsub e).symm
  have hMT : Mᵀ *ᵥ evenKernel w =
      (pairTotal w + tripleSquareSum w) • (qVec w ∘ oddColumnEquiv.symm) := by
    have hsub := Matrix.submatrix_mulVec_equiv Mᵀ (pVec w) oddColumnEquiv evenRowEquiv
    have ht : (M.submatrix evenRowEquiv oddColumnEquiv)ᵀ =
        Mᵀ.submatrix oddColumnEquiv evenRowEquiv := by
      simp [Matrix.transpose_submatrix]
    rw [← ht, code_matrix_eq, hback] at hsub
    funext x
    obtain ⟨m, rfl⟩ := oddColumnEquiv.surjective x
    simpa [evenKernel, Function.comp_def] using (congrFun hsub m).symm
  constructor
  · rw [defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hMT, Matrix.mulVec_smul, hM, weight_square_sum, sub_self]
  · intro h
    apply hp
    funext e
    simpa [evenKernel] using congrFun h (evenRowEquiv e)

private theorem odd_kernel (w : Fin 9 → ℝ) (hw : ∀ i, 0 < w i) :
    defect w (biadjacency w support true) *ᵥ oddKernel w = 0 ∧
      oddKernel w ≠ 0 := by
  classical
  obtain ⟨hforward, hback, hp, hq⟩ := code_kernel w hw
  let M := biadjacency w support false
  let N := biadjacency w support true
  have htranspose :
      (N.submatrix oddRowEquiv evenColumnEquiv) =
        (M.submatrix evenRowEquiv oddColumnEquiv)ᵀ := by
    ext m e
    change (∑ a : Fin 9, if flip (middleVertex m) a = (evenInterior e).1.1 then w a else 0) =
      ∑ a : Fin 9, if flip (evenRow e).1.1 a = middleVertex m then w a else 0
    rw [evenInterior_val, evenRow_val]
    apply Finset.sum_congr rfl
    intro a _
    have hf : flip (middleVertex m) a = cubeBitVec 9 (evenWord e) ↔
        flip (cubeBitVec 9 (evenWord e)) a = middleVertex m := by
      constructor <;> intro h <;> rw [← h, BalancedCriticalSpectrum.flip_flip]
    simp only [hf]
  let pColumn := pVec w ∘ evenColumnEquiv.symm
  have hN : N *ᵥ pColumn =
      (pairTotal w + tripleSquareSum w) • oddKernel w := by
    have hsub := Matrix.submatrix_mulVec_equiv N (pVec w) oddRowEquiv evenColumnEquiv
    rw [htranspose, code_matrix_eq, hback] at hsub
    funext x
    obtain ⟨m, rfl⟩ := oddRowEquiv.surjective x
    simpa [pColumn, oddKernel, Function.comp_def] using (congrFun hsub m).symm
  have hNT : Nᵀ *ᵥ oddKernel w = pColumn := by
    have hsub := Matrix.submatrix_mulVec_equiv Nᵀ (qVec w) evenColumnEquiv oddRowEquiv
    rw [← Matrix.transpose_submatrix, htranspose, Matrix.transpose_transpose,
      code_matrix_eq, hforward] at hsub
    funext x
    obtain ⟨e, rfl⟩ := evenColumnEquiv.surjective x
    simpa [pColumn, oddKernel, Function.comp_def] using (congrFun hsub e).symm
  constructor
  · rw [defect, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hNT, hN, weight_square_sum, sub_self]
  · intro h
    apply hq
    funext m
    simpa [oddKernel] using congrFun h (oddRowEquiv m)

private def supportWords : Finset Word :=
  (univ.image centerWord ∪ univ.image middleWord) ∪ univ.image leafWord

private theorem support_image : supportWords.image (cubeBitVec 9) = support := by
  simp only [supportWords, support, centers, middles, leaves, Finset.image_union,
    Finset.image_image, Function.comp_def]
  rfl

private theorem exists_support_word {x : Q9} (hx : x ∈ support) :
    ∃ y ∈ supportWords, cubeBitVec 9 y = x := by
  rw [← support_image] at hx
  exact Finset.mem_image.mp hx

private theorem mem_support_word (x : Word) : cubeBitVec 9 x ∈ support ↔ x ∈ supportWords := by
  rw [← support_image, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, h⟩
    exact (cubeBitVec 9).injective h ▸ hy
  · intro h
    exact ⟨x, h, rfl⟩

private def wordDirections (x : Word) : Finset (Fin 9) :=
  univ.filter (fun a => toggle x a ∈ supportWords)

private theorem wordDirections_eq (x : Word) :
    directions support (cubeBitVec 9 x) = wordDirections x := by
  ext a
  rw [mem_directions, flip_word, mem_support_word, wordDirections, Finset.mem_filter]
  simp

private theorem wordDegree_three : ∀ x ∈ supportWords, (wordDirections x).card = 3 := by
  decide +kernel

open scoped Classical in
theorem support_induced_cubic :
    ((hypercube 9).induce (support : Set Q9)).IsRegularOfDegree 3 := by
  intro x
  obtain ⟨y, hy, he⟩ := exists_support_word x.property
  have hcard : (directions support x.val).card = 3 := by
    rw [← he, wordDirections_eq]
    exact wordDegree_three y hy
  rw [directions_card] at hcard
  have hf : (support.filter fun y => (hypercube 9).Adj x.val y) =
      (hypercube 9).neighborFinset x.val ∩ support := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rwa [hf, selected_neighbor_card x.property] at hcard

/- A spanning tree listed in parent-first order. Each entry gives the parent
word and the coordinate to flip to reach the child. -/
private def treeSteps : List (Word × Fin 9) :=
  [(85, 0), (85, 2), (85, 4), (84, 1), (84, 6), (81, 3), (81, 6),
   (69, 5), (69, 6), (86, 2), (86, 4), (20, 7), (20, 8), (89, 0),
   (89, 4), (17, 7), (17, 8), (101, 0), (101, 2), (5, 7), (5, 8),
   (82, 3), (82, 6), (70, 5), (70, 6), (148, 0), (148, 1), (276, 0),
   (276, 1), (88, 6), (73, 5), (73, 6), (145, 3), (273, 3), (100, 6),
   (97, 6), (133, 5), (261, 5), (90, 4), (18, 7), (18, 8), (102, 2),
   (6, 7), (6, 8), (24, 7), (24, 8), (105, 0), (9, 7), (9, 8),
   (36, 7), (36, 8), (33, 7), (33, 8), (74, 5), (74, 6), (146, 3),
   (274, 3), (98, 6), (134, 5), (262, 5), (104, 6), (137, 5), (265, 5),
   (10, 7), (10, 8), (34, 7), (34, 8), (40, 7), (40, 8), (138, 5),
   (266, 5)]

private def treeCheck (allowed : Finset Word) (seen : List Word) : List (Word × Fin 9) → Bool
  | [] => decide (allowed ⊆ seen.toFinset)
  | (x, a) :: rest =>
    let y := toggle x a
    seen.contains x && decide (y ∈ allowed) && treeCheck allowed (y :: seen) rest

private theorem treeCheck_ok : treeCheck supportWords [85] treeSteps = true := by
  decide +kernel

private abbrev SupportPoint := (support : Set Q9)
private abbrev supportGraph := (hypercube 9).induce (support : Set Q9)

private def wordPoint (x : Word) (hx : x ∈ supportWords) : SupportPoint :=
  ⟨cubeBitVec 9 x, (mem_support_word x).mpr hx⟩

private def rootPoint : SupportPoint := wordPoint 85 (by decide +kernel)

private theorem treeCheck_sound {allowed : Finset Word} (hallowed : allowed ⊆ supportWords)
    (steps : List (Word × Fin 9)) (seen : List Word)
    (hseen : ∀ x ∈ seen, ∃ hx, supportGraph.Reachable rootPoint (wordPoint x hx))
    (hcheck : treeCheck allowed seen steps = true) :
    ∀ x (hx : x ∈ allowed), supportGraph.Reachable rootPoint (wordPoint x (hallowed hx)) := by
  induction steps generalizing seen with
  | nil =>
    intro x hx
    change decide (allowed ⊆ seen.toFinset) = true at hcheck
    have hs : allowed ⊆ seen.toFinset := of_decide_eq_true hcheck
    have h : x ∈ seen := List.mem_toFinset.mp (hs hx)
    obtain ⟨_, hr⟩ := hseen x h
    exact hr
  | cons step rest ih =>
    obtain ⟨x, a⟩ := step
    simp only [treeCheck, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at hcheck
    obtain ⟨⟨hx, hym⟩, hrest⟩ := hcheck
    have hy := hallowed hym
    obtain ⟨hxm, hr⟩ := hseen x hx
    let y := toggle x a
    have ha : supportGraph.Adj (wordPoint x hxm) (wordPoint y hy) := by
      change (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 y)
      rw [show cubeBitVec 9 y = flip (cubeBitVec 9 x) a from (flip_word x a).symm]
      exact BalancedCriticalSpectrum.flip_adj _ _
    apply ih (y :: seen) _ hrest
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨hy, hr.trans ha.reachable⟩
    · exact hseen z hz

theorem support_connected :
    ((hypercube 9).induce (support : Set Q9)).Connected := by
  apply (SimpleGraph.connected_iff _).mpr
  refine ⟨?_, ⟨rootPoint⟩⟩
  have hr (x : SupportPoint) : supportGraph.Reachable rootPoint x := by
    obtain ⟨y, hy, he⟩ := exists_support_word x.property
    have hx : wordPoint y hy = x := Subtype.ext he
    rw [← hx]
    refine treeCheck_sound (Finset.Subset.refl _) treeSteps [85] ?_ treeCheck_ok y hy
    intro z hz
    have hz' : z = 85 := by simpa using hz
    subst z
    exact ⟨_, SimpleGraph.Reachable.refl rootPoint⟩
  exact fun x y => (hr x).symm.trans (hr y)

/-! A fixed Huang switching sign.  On this support the false-prefix sign is
the coboundary of the four-bit character `x₁+x₂+x₅+x₇`. -/

private def localSign (x : Q9) : ℤ :=
  (if x 1 then -1 else 1) * (if x 2 then -1 else 1) *
    (if x 5 then -1 else 1) * (if x 7 then -1 else 1)

private theorem localSign_cases (x : Q9) : localSign x = 1 ∨ localSign x = -1 := by
  unfold localSign
  cases x 1 <;> cases x 2 <;> cases x 5 <;> cases x 7 <;> decide +kernel

private theorem localSign_word_edge :
    ∀ x ∈ supportWords, ∀ a : Fin 9, toggle x a ∈ supportWords →
      localSign (cubeBitVec 9 x) * localSign (cubeBitVec 9 (toggle x a)) =
        flipSign a (cubeBitVec 9 x) := by
  decide +kernel

private theorem localSign_switch : IsBalanced support := by
  let sigma : Q9 → ℝ := fun x => localSign x
  refine ⟨sigma, ?_, ?_⟩
  · intro x _
    rcases localSign_cases x with h | h <;> simp [sigma, h]
  · intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := adjacent_exists_flip hxy
    obtain ⟨z, hz, rfl⟩ := exists_support_word hx
    rw [← flipSign_cast]
    have hz' := (mem_support_word (toggle z i)).mp (flip_word z i ▸ hy)
    have hs := (localSign_word_edge z hz i hz').symm
    change (flipSign i (cubeBitVec 9 z) : ℝ) =
      (localSign (cubeBitVec 9 z) : ℝ) * (localSign (flip (cubeBitVec 9 z) i) : ℝ)
    rw [flip_word]
    exact_mod_cast hs

abbrev Side (C : Finset Q9) (b : Bool) := {x : Q9 // x ∈ C ∧ parity x = b}

def directionPartition (C : Finset Q9) (b : Bool) : Prop :=
  ∀ x : Side C b, ∀ k : Fin 9,
    ∃! i : {i // i ∈ BalancedCubeComponentBoundary.directions C x.val},
      k ∈ BalancedCubeComponentBoundary.directions C (flip x.val i.val)

private theorem two_directions_fail {x : Q9} {k i j : Fin 9}
    (hi : i ∈ directions support x) (hj : j ∈ directions support x) (hne : i ≠ j)
    (hki : k ∈ directions support (flip x i)) (hkj : k ∈ directions support (flip x j)) :
    ¬ (∃! a : {a // a ∈ directions support x}, k ∈ directions support (flip x a.val)) := by
  rintro ⟨a, _, ha⟩
  exact hne (congrArg Subtype.val ((ha ⟨i, hi⟩ hki).trans (ha ⟨j, hj⟩ hkj).symm))

private theorem even_partition_fails : ¬ directionPartition support false := by
  intro h
  let c : CenterCode := (0, 0, 0, 0)
  let x : Side support false := ⟨centerVertex c, (centerRow c).1.property, center_parity c⟩
  refine two_directions_fail (i := 0) (j := 2) (k := 6) (x := x.val) ?_ ?_ ?_ ?_ ?_ (h x 6)
  all_goals
    try simp only [x, c, centerVertex, mem_directions, flip_word, mem_support_word]
    decide +kernel

private theorem odd_partition_fails : ¬ directionPartition support true := by
  intro h
  let m : MiddleCode := (0, 0, 0, 0)
  let x : Side support true := ⟨middleVertex m, (middleRow m).1.property, middle_parity m⟩
  refine two_directions_fail (i := 0) (j := 1) (k := 2) (x := x.val) ?_ ?_ ?_ ?_ ?_ (h x 2)
  all_goals
    try simp only [x, m, middleVertex, mem_directions, flip_word, mem_support_word]
    decide +kernel

def universallyWeightedSingular (C : Finset Q9) : Prop :=
  ∀ b : Bool, ∀ w : Fin 9 → ℝ, (∀ i, 0 < w i) →
    ∃ f ≠ 0, defect w (biadjacency w C b) *ᵥ f = 0

theorem support_universallyWeightedSingular : universallyWeightedSingular support := by
  intro b w hw
  cases b with
  | false =>
      obtain ⟨hzero, hne⟩ := even_kernel w hw
      exact ⟨evenKernel w, hne, hzero⟩
  | true =>
      obtain ⟨hzero, hne⟩ := odd_kernel w hw
      exact ⟨oddKernel w, hne, hzero⟩

open scoped Classical in
def claim : Prop :=
  ∀ C : Finset Q9,
    C.card = 72 →
    ((hypercube 9).induce (C : Set Q9)).IsRegularOfDegree 3 →
    ((hypercube 9).induce (C : Set Q9)).Connected →
    IsBalanced C → universallyWeightedSingular C →
    ∃ b : Bool, directionPartition C b

theorem result : ¬ claim := by
  intro h
  obtain ⟨b, hb⟩ := h support support_card support_induced_cubic support_connected
    localSign_switch support_universallyWeightedSingular
  cases b with
  | false => exact even_partition_fails hb
  | true => exact odd_partition_fails hb

#print axioms result

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9LocalSaturation72Refutation
