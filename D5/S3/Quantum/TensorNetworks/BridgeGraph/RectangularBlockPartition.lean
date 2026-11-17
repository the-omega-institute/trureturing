/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/RectangularBlockPartition
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/RectangularBlockPartition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangle partitions give unitary paired factors and exact realignment rank. -/

import D5.S3.Quantum.Entanglement.SequentialRegisterCircuit
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Paired partial permutations on a partition into equal-cardinality rectangles. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Matrix
open scoped BigOperators Classical

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition

universe u v w z
variable {X : Type u} {Y : Type v} {T : Type w}
  [Fintype X] [Fintype Y] [Fintype T] [DecidableEq X] [DecidableEq Y]
  (I : T → Finset X) (J : T → Finset Y)
  (φ : ∀ t, {y // y ∈ J t} ≃ {x // x ∈ I t})

def block (t : T) : Matrix X Y ℂ := by
  classical
  exact fun i j => if ∃ y : {y // y ∈ J t}, y.val = j ∧ (φ t y).val = i then 1 else 0

def operator : Matrix (X × Y) (Y × X) ℂ :=
  ∑ t, kronecker (block I J φ t) (block I J φ t)ᴴ

/-- The local carriers of the two factors determine this order of realignment. -/
def realign (U : Matrix (X × Y) (Y × X) ℂ) : Matrix (X × Y) (Y × X) ℂ :=
  fun p q => U (p.1, q.1) (p.2, q.2)

/-- Empty blocks are omitted from the achieved factor count. -/
abbrev Active := {t // (J t).Nonempty}

private def flatten
    (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) :
    (Σ t, {x // x ∈ I t} × {y // y ∈ J t}) ≃ X × Y :=
  Equiv.ofBijective (fun a => (a.2.1.val, a.2.2.val)) (by
    constructor
    · rintro ⟨t, x, y⟩ ⟨s, x', y'⟩ he
      have hx : x.val = x'.val := congrArg Prod.fst he
      have hy : y.val = y'.val := congrArg Prod.snd he
      have ht : t = s := (h x.val y.val).unique ⟨x.property, y.property⟩
        ⟨hx ▸ x'.property, hy ▸ y'.property⟩
      subst s
      have hxx : x = x' := Subtype.ext hx
      have hyy : y = y' := Subtype.ext hy
      subst x'; subst y'
      rfl
    · rintro ⟨x, y⟩
      obtain ⟨t, ht, _⟩ := h x y
      exact ⟨⟨t, ⟨x, ht.1⟩, ⟨y, ht.2⟩⟩, rfl⟩)

/-- The input (j,l) is routed within its unique rectangle to (φ(j),φ⁻¹(l)). -/
def route (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) : (Y × X) ≃ (X × Y) :=
  ((Equiv.prodComm Y X).trans (flatten I J h).symm).trans
    ((Equiv.sigmaCongrRight (fun t =>
      (Equiv.prodComm {x // x ∈ I t} {y // y ∈ J t}).trans
        ((φ t).prodCongr (φ t).symm))).trans (flatten I J h))

private theorem route_apply
    (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) (t : T)
    (l : {x // x ∈ I t}) (j : {y // y ∈ J t}) :
    route I J φ h (j.val, l.val) = ((φ t j).val, ((φ t).symm l).val) := by
  have he : (flatten I J h).symm (l.val, j.val) = ⟨t, l, j⟩ :=
    (flatten I J h).symm_apply_apply ⟨t, l, j⟩
  change (flatten I J h) ((Equiv.sigmaCongrRight (fun t =>
    (Equiv.prodComm {x // x ∈ I t} {y // y ∈ J t}).trans
      ((φ t).prodCongr (φ t).symm))) ((flatten I J h).symm (l.val, j.val))) = _
  rw [he]
  rfl

private theorem block_support (t : T) (i : X) (j : Y)
    (hb : block I J φ t i j ≠ 0) : i ∈ I t ∧ j ∈ J t := by
  classical
  unfold block at hb
  split_ifs at hb with he
  · obtain ⟨y, hy, hx⟩ := he
    exact ⟨hx ▸ (φ t y).property, hy ▸ y.property⟩
  · exact (hb rfl).elim

private theorem block_column (t : T) (i : X) (j : {y // y ∈ J t}) :
    block I J φ t i j.val = if (φ t j).val = i then 1 else 0 := by
  classical
  have he : (∃ y : {y // y ∈ J t}, y.val = j.val ∧ (φ t y).val = i) ↔
      (φ t j).val = i := by
    constructor
    · rintro ⟨y, hy, hx⟩
      simpa only [Subtype.ext hy] using hx
    · intro hx
      exact ⟨j, rfl, hx⟩
  simp only [block, he]

private theorem block_row (t : T) (l : {x // x ∈ I t}) (k : Y) :
    block I J φ t l.val k = if ((φ t).symm l).val = k then 1 else 0 := by
  classical
  have he : (∃ y : {y // y ∈ J t}, y.val = k ∧ (φ t y).val = l.val) ↔
      ((φ t).symm l).val = k := by
    constructor
    · rintro ⟨y, hy, hx⟩
      have hh : φ t y = l := Subtype.ext hx
      simpa only [← hh, Equiv.symm_apply_apply] using hy
    · intro hk
      exact ⟨(φ t).symm l, hk, by simp⟩
  simp only [block, he]

private theorem operator_coordinate
    (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) :
    operator I J φ =
      D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix
        (route I J φ h).toEmbedding := by
  classical
  ext ⟨i, k⟩ ⟨j, l⟩
  obtain ⟨t, ht, hu⟩ := h l j
  have hs : ∀ s ∈ Finset.univ, s ≠ t →
      block I J φ s i j * star (block I J φ s l k) = 0 := by
    intro s _ hst
    by_cases h1 : block I J φ s i j = 0
    · simp [h1]
    by_cases h2 : block I J φ s l k = 0
    · simp [h2]
    exact (hst (hu s ⟨(block_support I J φ s l k h2).1,
      (block_support I J φ s i j h1).2⟩)).elim
  simp only [operator, Matrix.sum_apply, Matrix.kronecker_apply,
    Matrix.conjTranspose_apply,
    D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix]
  change (∑ s, block I J φ s i j * star (block I J φ s l k)) =
    if route I J φ h (j, l) = (i, k) then 1 else 0
  rw [Finset.sum_eq_single t hs (by simp)]
  rw [route_apply I J φ h t ⟨l, ht.1⟩ ⟨j, ht.2⟩,
    block_column I J φ t i ⟨j, ht.2⟩, block_row I J φ t ⟨l, ht.1⟩ k]
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

private theorem rank_realign_sum_le {R : Type z} [Fintype R]
    (M : R → Matrix X Y ℂ) (N : R → Matrix Y X ℂ) :
    (realign (∑ r, kronecker (M r) (N r))).rank ≤ Fintype.card R := by
  classical
  let B : Matrix (X × Y) R ℂ := fun p r => M r p.1 p.2
  let C : Matrix R (Y × X) ℂ := fun r q => N r q.1 q.2
  have he : realign (∑ r, kronecker (M r) (N r)) = B * C := by
    ext p q
    simp [realign, Matrix.mul_apply, B, C, Matrix.sum_apply, Matrix.kronecker_apply]
  rw [he]
  exact (Matrix.rank_mul_le_left B C).trans (Matrix.rank_le_card_width B)

private theorem drop_empty :
    operator I J φ = ∑ t : Active J, kronecker (block I J φ t.val) (block I J φ t.val)ᴴ := by
  classical
  symm
  unfold operator
  apply Finset.sum_bij_ne_zero (fun t _ _ => t.val)
  · intro t ht hne
    exact Finset.mem_univ _
  · intro a ha b hb hne hne' he
    exact Subtype.ext he
  · intro t ht hne
    have hj : (J t).Nonempty := by
      by_contra hn
      have hz : block I J φ t = 0 := by
        ext i j
        have he : ¬ ∃ y : {y // y ∈ J t}, y.val = j ∧ (φ t y).val = i := by
          rintro ⟨y, _, _⟩
          exact hn ⟨y.val, y.property⟩
        simp [block, he]
      simp [hz] at hne
    exact ⟨⟨t, hj⟩, Finset.mem_univ _, hne, rfl⟩
  · intro t ht hne
    rfl

private def sampleY (t : Active J) : {y // y ∈ J t.val} :=
  ⟨t.property.choose, t.property.choose_spec⟩

private def samplePair (t : Active J) : X × Y :=
  ((φ t.val (sampleY J t)).val, (sampleY J t).val)

private theorem block_sample
    (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) (u : T) (t : Active J) :
    block I J φ u (samplePair I J φ t).1 (samplePair I J φ t).2 =
      if u = t.val then 1 else 0 := by
  classical
  by_cases hut : u = t.val
  · subst u
    simp [samplePair, block_column]
  · have hz : block I J φ u (samplePair I J φ t).1 (samplePair I J φ t).2 = 0 := by
      by_contra hn
      exact hut ((h _ _).unique (block_support I J φ u _ _ hn)
        ⟨(φ t.val (sampleY J t)).property, (sampleY J t).property⟩)
    simp [hut, hz]

private theorem identity_minor
    (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) :
    (realign (operator I J φ)).submatrix (samplePair I J φ)
      (fun t => ((samplePair I J φ t).2, (samplePair I J φ t).1)) =
        (1 : Matrix (Active J) (Active J) ℂ) := by
  classical
  ext s t
  simp only [Matrix.submatrix_apply, realign, operator, Matrix.sum_apply,
    Matrix.kronecker_apply, Matrix.conjTranspose_apply]
  change (∑ u, block I J φ u (samplePair I J φ s).1 (samplePair I J φ s).2 *
    star (block I J φ u (samplePair I J φ t).1 (samplePair I J φ t).2)) =
      if s = t then 1 else 0
  simp_rw [block_sample I J φ h]
  rw [Finset.sum_eq_single s.val]
  · simp [Matrix.one_apply, Subtype.val_injective.eq_iff]
  · intro u _ hu
    simp [hu]
  · simp

/-- The paired partial permutations are unitary on their original rectangular carriers.
The nonempty blocks give an exact factor count, certified by an identity minor and
by a lower bound for every decomposition into arbitrary complex tensor factors. -/
theorem unitary_exact_width
    (h : ∀ x y, ∃! t, x ∈ I t ∧ y ∈ J t) :
    (operator I J φ)ᴴ * operator I J φ = 1 ∧
    operator I J φ * (operator I J φ)ᴴ = 1 ∧
    (realign (operator I J φ)).rank = Fintype.card (Active J) ∧
    operator I J φ =
      ∑ t : Active J, kronecker (block I J φ t.val) (block I J φ t.val)ᴴ ∧
    (∃ (rows : Active J → X × Y) (cols : Active J → Y × X),
      (realign (operator I J φ)).submatrix rows cols = 1) ∧
    ∀ (R : Type z) [Fintype R] (M : R → Matrix X Y ℂ) (N : R → Matrix Y X ℂ),
      operator I J φ = ∑ r, kronecker (M r) (N r) →
        Fintype.card (Active J) ≤ Fintype.card R := by
  classical
  let e := route I J φ h
  have hc := operator_coordinate I J φ h
  have hct :
      (D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix e.toEmbedding)ᴴ =
        D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinateMatrix
          e.symm.toEmbedding := by
    ext p q
    change star (if e p = q then (1 : ℂ) else 0) =
      if e.symm q = p then 1 else 0
    simp only [Equiv.symm_apply_eq]
    by_cases hh : e p = q
    · have hq : q = e p := hh.symm
      rw [if_pos hh, if_pos hq, star_one]
    · have hq : q ≠ e p := Ne.symm hh
      rw [if_neg hh, if_neg hq, star_zero]
  have hcol : (operator I J φ)ᴴ * operator I J φ = 1 := by
    rw [hc]
    exact D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinate_gram _
  have hrow : operator I J φ * (operator I J φ)ᴴ = 1 := by
    have hh := D5.S3.Quantum.Entanglement.SequentialRegisterCircuit.coordinate_gram
      e.symm.toEmbedding
    rw [← hct, Matrix.conjTranspose_conjTranspose] at hh
    rw [hc]
    exact hh
  have hm := identity_minor I J φ h
  have hlo : Fintype.card (Active J) ≤ (realign (operator I J φ)).rank := by
    have hh := Matrix.rank_submatrix_le (realign (operator I J φ)) (samplePair I J φ)
      (fun t => ((samplePair I J φ t).2, (samplePair I J φ t).1))
    rw [hm, Matrix.rank_one] at hh
    exact hh
  have hhi : (realign (operator I J φ)).rank ≤ Fintype.card (Active J) := by
    rw [drop_empty I J φ]
    exact rank_realign_sum_le _ _
  have hr := Nat.le_antisymm hhi hlo
  refine ⟨hcol, hrow, hr, drop_empty I J φ,
    ⟨samplePair I J φ, fun t => ((samplePair I J φ t).2, (samplePair I J φ t).1), hm⟩, ?_⟩
  intro R _ M N he
  rw [← hr, he]
  exact rank_realign_sum_le M N

end D5.S3.Quantum.TensorNetworks.BridgeGraph.RectangularBlockPartition
