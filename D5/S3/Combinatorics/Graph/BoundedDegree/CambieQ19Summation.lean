/- GID: D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Fintype.Prod]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.claim; result=D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Summation.result; claim=D5/S3/Combinatorics/Graph/BoundedDegree/CambieQ19Settlement.claim
   digest: Factor the Cambie configuration moments into local attachment contributions. -/

import D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Moments
import D5.S3.Combinatorics.Graph.ZeroForcing.CycleConnectedForcing

/-! The fixed counterexample to Question 1.9 of Cambie, Jooken and Wagner.
The support and tree classifications feed the four transported moments. Grouping cyclic
intervals by their attachment marks gives the finite sums for the exact rational difference.

admission_basis: escape-witness. The interval and independent edge-deletion classifications
are used to transport both counts and both order sums from actual graph objects. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement

open SimpleGraph
open D5.S3.Combinatorics.Graph.ZeroForcing
open scoped BigOperators

/-- Count and sum of vertex orders, with the same multiplicity on each configuration. -/
abbrev CountOrder := ℕ × ℕ

private def contribution (count order : ℕ) : CountOrder := (count, count * order)

private def combine (a b : CountOrder) : CountOrder :=
  (a.1 * b.1, a.2 * b.1 + a.1 * b.2)

private theorem combine_contribution (w v a b : ℕ) :
    combine (contribution w a) (contribution v b) = contribution (w*v) (a+b) := by
  unfold combine contribution
  congr 1
  ring

private theorem sum_combine_left {ι : Type} [Fintype ι] (f : ι → CountOrder) (b : CountOrder) :
    ∑ i, combine (f i) b = combine (∑ i, f i) b := by
  apply Prod.ext
  · simp only [combine, Prod.fst_sum]
    rw [Finset.sum_mul]
  · simp only [combine, Prod.snd_sum, Prod.fst_sum, Finset.sum_add_distrib, Finset.sum_mul]

private theorem sum_combine_right {ι : Type} [Fintype ι] (a : CountOrder) (f : ι → CountOrder) :
    ∑ i, combine a (f i) = combine a (∑ i, f i) := by
  apply Prod.ext
  · simp only [combine, Prod.fst_sum]
    rw [Finset.mul_sum]
  · simp only [combine, Prod.fst_sum, Prod.snd_sum, Finset.sum_add_distrib, Finset.mul_sum]

private noncomputable def weight (tree : Bool) (c : Configuration) : ℕ :=
  if tree then Nat.card (DeletionChoices c) else 1

/-- Configuration moments for induced supports, or for tree subgraphs with multiplicity. -/
noncomputable def codeMoments (tree : Bool) : CountOrder :=
  ∑ c : Configuration, contribution (weight tree c) c.vertexOrder

private def fullWeight (tree : Bool) (m : ℕ) (full : Bool) : ℕ :=
  if tree && full then m else 1

private noncomputable def circleWeight (tree : Bool) (c : CycleInterval 4997) : ℕ := by
  classical
  exact fullWeight tree 5000 (decide (c.cycleVertices = Set.univ))

private def triangleWeight (tree : Bool) (t : Finset (Fin 3)) : ℕ :=
  fullWeight tree 3 (decide (t = Finset.univ))

private theorem weight_onCore (tree : Bool) (c : CycleInterval 4997)
    (p : PathPrefix c.cycleVertices 0) (q : PathPrefix c.cycleVertices 1000)
    (t : TriangleExtension c.cycleVertices) :
    weight tree (.onCore c p q t) = circleWeight tree c * triangleWeight tree t.val := by
  classical
  have hT : triangleSet (Configuration.vertices (.onCore c p q t)) = Set.univ ↔
      t.val = Finset.univ := by
    change (↑t.val : Set (Fin 3)) = Set.univ ↔ _
    rw [← Finset.coe_univ, Finset.coe_inj]
  cases tree
  · rfl
  · have hc : coreSet (Configuration.vertices (.onCore c p q t)) = c.cycleVertices := rfl
    rw [weight, ite_eq_left rfl, deletionChoices_card, hc]
    simp only [circleWeight, triangleWeight, fullWeight, Bool.true_and, decide_eq_true_eq, hT]

private theorem weight_first (tree : Bool) (p : PathInterval 500) : weight tree (.firstOnly p) = 1 := by
  classical
  have hc : coreSet (Configuration.vertices (.firstOnly p)) ≠ Set.univ :=
    Set.empty_ne_univ
  have ht : triangleSet (Configuration.vertices (.firstOnly p)) ≠ Set.univ :=
    Set.empty_ne_univ
  cases tree
  · rfl
  · rw [weight, ite_eq_left rfl, deletionChoices_card]; simp [hc, ht]

private theorem weight_second (tree : Bool) (p : PathInterval 500) : weight tree (.secondOnly p) = 1 := by
  classical
  have hc : coreSet (Configuration.vertices (.secondOnly p)) ≠ Set.univ :=
    Set.empty_ne_univ
  have ht : triangleSet (Configuration.vertices (.secondOnly p)) ≠ Set.univ :=
    Set.empty_ne_univ
  cases tree
  · rfl
  · rw [weight, ite_eq_left rfl, deletionChoices_card]; simp [hc, ht]

private theorem weight_triangle (tree : Bool) (t : {t : Finset (Fin 3) // t.Nonempty}) :
    weight tree (.triangleOnly t) = triangleWeight tree t.val := by
  classical
  have hc : coreSet (Configuration.vertices (.triangleOnly t)) ≠ Set.univ :=
    Set.empty_ne_univ
  have ht : triangleSet (Configuration.vertices (.triangleOnly t)) = Set.univ ↔
      t.val = Finset.univ := by
    change (↑t.val : Set (Fin 3)) = Set.univ ↔ _
    rw [← Finset.coe_univ, Finset.coe_inj]
  cases tree
  · rfl
  · rw [weight, ite_eq_left rfl, deletionChoices_card]
    simp [hc, ht, triangleWeight, fullWeight]

private abbrev Extensions (c : CycleInterval 4997) :=
  PathPrefix c.cycleVertices 0 × PathPrefix c.cycleVertices 1000 × TriangleExtension c.cycleVertices

private def configurationParts :
    Configuration ≃ (Σ c : CycleInterval 4997, Extensions c) ⊕
      PathInterval 500 ⊕ PathInterval 500 ⊕ {t : Finset (Fin 3) // t.Nonempty} where
  toFun
    | .onCore c p q t => .inl ⟨c, p, q, t⟩
    | .firstOnly p => .inr (.inl p)
    | .secondOnly p => .inr (.inr (.inl p))
    | .triangleOnly t => .inr (.inr (.inr t))
  invFun
    | .inl ⟨c, p, q, t⟩ => .onCore c p q t
    | .inr (.inl p) => .firstOnly p
    | .inr (.inr (.inl p)) => .secondOnly p
    | .inr (.inr (.inr t)) => .triangleOnly t
  left_inv := by intro c; cases c <;> rfl
  right_inv := by rintro (⟨c, p, q, t⟩ | p | p | t) <;> rfl

private noncomputable instance (c : CycleInterval 4997) (m : Fin 5000) :
    Fintype (PathPrefix c.cycleVertices m) := Fintype.ofFinite _

private noncomputable instance (c : CycleInterval 4997) :
    Fintype (TriangleExtension c.cycleVertices) := Fintype.ofFinite _

private def localPath (b : Bool) : CountOrder :=
  if b then (501, 125250) else (1, 0)

private def localTriangle (tree b : Bool) : CountOrder :=
  if b then if tree then (7, 14) else (5, 8) else (1, 0)

open scoped Classical in
private theorem attached_path (c : CycleInterval 4997) (m : Fin 5000) :
    ∑ p : PathPrefix c.cycleVertices m, contribution 1 p.val.val =
      localPath (decide (m ∈ c.cycleVertices)) := by
  classical
  by_cases hm : m ∈ c.cycleVertices
  · let e : Fin 501 ≃ PathPrefix c.cycleVertices m :=
      ⟨fun p => ⟨p, fun _ => hm⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩
    rw [← e.sum_comp (fun p => contribution 1 p.val.val)]
    apply Prod.ext
    · simp [contribution, localPath, hm, Prod.fst_sum]
    · simp only [e, contribution, Nat.one_mul, Prod.snd_sum, Equiv.coe_fn_mk]
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => n), Finset.sum_range_id]
      norm_num [localPath, hm]
  · let e : Unit ≃ PathPrefix c.cycleVertices m :=
      ⟨fun _ => ⟨0, fun h => (Nat.lt_irrefl 0 h).elim⟩, fun _ => (), fun _ => rfl,
        fun p => Subtype.ext (Fin.ext (by
          exact (Nat.eq_zero_of_not_pos (hm ∘ p.property)).symm))⟩
    rw [← e.sum_comp (fun p => contribution 1 p.val.val)]
    simp [e, localPath, hm, contribution]

private abbrev RootedTriangle := {t : Finset (Fin 3) // t.Nonempty → (0 : Fin 3) ∈ t}
private abbrev DetachedTriangle := {t : Finset (Fin 3) // t.Nonempty}

private theorem rooted_triangle_table (tree : Bool) :
    (∑ t : RootedTriangle, contribution (triangleWeight tree t.val) t.val.card) =
      localTriangle tree true := by
  cases tree <;> decide +kernel

private theorem detached_triangle_table (tree : Bool) :
    (∑ t : DetachedTriangle, contribution (triangleWeight tree t.val) t.val.card) =
      (if tree then (9, 18) else (7, 12)) := by
  cases tree <;> decide +kernel

open scoped Classical in
private theorem attached_triangle (tree : Bool) (c : CycleInterval 4997) :
    (∑ t : TriangleExtension c.cycleVertices, contribution (triangleWeight tree t.val) t.val.card) =
      localTriangle tree (decide ((500 : Fin 5000) ∈ c.cycleVertices)) := by
  classical
  by_cases hm : (500 : Fin 5000) ∈ c.cycleVertices
  · let e : RootedTriangle ≃ TriangleExtension c.cycleVertices :=
      ⟨fun t => ⟨t.val, fun h => ⟨hm, t.property h⟩⟩,
        fun t => ⟨t.val, fun h => (t.property h).2⟩, fun _ => rfl, fun _ => rfl⟩
    rw [← e.sum_comp (fun t => contribution (triangleWeight tree t.val) t.val.card)]
    simpa only [e, Equiv.coe_fn_mk, decide_eq_true hm] using rooted_triangle_table tree
  · let e : Unit ≃ TriangleExtension c.cycleVertices :=
      ⟨fun _ => ⟨∅, fun h => (Finset.not_nonempty_empty h).elim⟩, fun _ => (), fun _ => rfl,
        fun t => Subtype.ext ((Finset.not_nonempty_iff_eq_empty.mp
          (fun h => hm (t.property h).1)).symm)⟩
    rw [← e.sum_comp (fun t => contribution (triangleWeight tree t.val) t.val.card)]
    have he : (∅ : Finset (Fin 3)) ≠ Finset.univ :=
      fun h => (Finset.notMem_empty 0) (h.symm ▸ Finset.mem_univ (0 : Fin 3))
    cases tree <;> simp [e, localTriangle, hm, contribution, triangleWeight, fullWeight, he]

open scoped Classical in
private noncomputable def arcContribution (tree : Bool) (c : CycleInterval 4997) : CountOrder :=
  combine (combine (combine (contribution (circleWeight tree c) c.cycleOrder)
    (localPath (decide ((0 : Fin 5000) ∈ c.cycleVertices))))
    (localPath (decide ((1000 : Fin 5000) ∈ c.cycleVertices))))
    (localTriangle tree (decide ((500 : Fin 5000) ∈ c.cycleVertices)))

private theorem attached_sum (tree : Bool) (c : CycleInterval 4997) :
    (∑ pq : Extensions c, contribution (weight tree (.onCore c pq.1 pq.2.1 pq.2.2))
      (Configuration.vertexOrder (.onCore c pq.1 pq.2.1 pq.2.2))) =
      arcContribution tree c := by
  classical
  simp only [weight_onCore, Configuration.vertexOrder]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have term (p : PathPrefix c.cycleVertices 0) (q : PathPrefix c.cycleVertices 1000)
      (t : TriangleExtension c.cycleVertices) :
      contribution (circleWeight tree c * triangleWeight tree t.val)
        (c.cycleOrder + p.val.val + q.val.val + t.val.card) =
        combine (combine (combine (contribution (circleWeight tree c) c.cycleOrder)
          (contribution 1 p.val.val)) (contribution 1 q.val.val))
          (contribution (triangleWeight tree t.val) t.val.card) := by
    rw [combine_contribution, Nat.mul_one, combine_contribution, Nat.mul_one, combine_contribution]
  simp_rw [term, sum_combine_right, attached_triangle, sum_combine_left,
    sum_combine_right, attached_path]
  rw [sum_combine_left, sum_combine_right, attached_path]
  rfl

private def pathMoments : CountOrder :=
  ∑ p : PathInterval 500, contribution 1 p.order

set_option maxRecDepth 5000 in
private theorem codeMoments_decompose (tree : Bool) :
    codeMoments tree = (∑ c : CycleInterval 4997, arcContribution tree c) +
      (pathMoments + (pathMoments + (if tree then (9,18) else (7,12)))) := by
  classical
  unfold codeMoments
  rw [← configurationParts.symm.sum_comp
    (fun c => contribution (weight tree c) c.vertexOrder)]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma, configurationParts, Equiv.coe_fn_symm_mk,
    weight_first, weight_second, weight_triangle, Configuration.vertexOrder]
  have h := attached_sum tree
  simp only [Configuration.vertexOrder] at h
  simp_rw [h, detached_triangle_table]
  rfl

/-- Endpoint order sums in an interval of indices, where index zero has order one. -/
private def intervalMoments (lo hi : ℕ) : CountOrder :=
  let count := hi - lo
  (count, count * (lo + 1) + count * (count - 1) / 2)

private def intervalIndexEquiv {n lo hi : ℕ} (hhi : hi ≤ n) :
    Fin (hi - lo) ≃ {i : Fin n // lo ≤ i.val ∧ i.val < hi} where
  toFun i := ⟨⟨lo + i.val, by have h := i.isLt; omega⟩,
    by change lo ≤ lo + i.val ∧ lo + i.val < hi; have h := i.isLt; omega⟩
  invFun i := ⟨i.val.val - lo, by have h := i.property; omega⟩
  left_inv i := Fin.ext (by simp)
  right_inv i := Subtype.ext (Fin.ext (by have h := i.property; simp; omega))

private theorem sum_fin_lengths (lo count : ℕ) :
    ∑ i : Fin count, contribution 1 (lo + i.val + 1) =
      (count, count * (lo + 1) + count * (count - 1) / 2) := by
  apply Prod.ext
  · simp [contribution, Prod.fst_sum]
  · simp only [contribution, Nat.one_mul, Prod.snd_sum, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun x : ℕ => x), Finset.sum_range_id, Nat.mul_add]
    simp only [Nat.mul_one]
    ac_rfl

private theorem sum_interval_indices {n lo hi : ℕ} (hhi : hi ≤ n) :
    ∑ i : {i : Fin n // lo ≤ i.val ∧ i.val < hi}, contribution 1 (i.val.val + 1) =
      intervalMoments lo hi := by
  rw [← (intervalIndexEquiv hhi).sum_comp
    (fun i : {i : Fin n // lo ≤ i.val ∧ i.val < hi} => contribution 1 (i.val.val + 1))]
  exact sum_fin_lengths lo (hi-lo)

private def endpointEquiv (a : Fin 500) :
    {b : Fin 500 // a ≤ b} ≃ {i : Fin 500 // a.val ≤ i.val ∧ i.val < 500} where
  toFun b := ⟨b.val, b.property, b.val.isLt⟩
  invFun i := ⟨i.val, i.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def pathByStart : (Σ a : Fin 500, {b : Fin 500 // a ≤ b}) ≃ PathInterval 500 where
  toFun p := ⟨(p.1, p.2.val), p.2.property⟩
  invFun p := ⟨p.val.1, p.val.2, p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem pathMoments_rows :
    pathMoments = ∑ a : Fin 500, intervalMoments 0 (500 - a.val) := by
  unfold pathMoments
  rw [← pathByStart.sum_comp (fun p => contribution 1 p.order), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  let e := (intervalIndexEquiv (lo := a.val) (hi := 500) (n := 500) le_rfl).trans
    (endpointEquiv a).symm
  rw [← e.sum_comp (fun b : {b : Fin 500 // a ≤ b} => contribution 1 (pathByStart ⟨a,b⟩).order)]
  have h (i : Fin (500 - a.val)) : (pathByStart ⟨a, e i⟩).order = i.val + 1 := by
    change a.val + i.val + 1 - a.val = i.val + 1
    omega
  simp only [h]
  simpa [intervalMoments] using sum_fin_lengths 0 (500 - a.val)

private abbrev MarkFlags := Bool × Bool × Bool

private def attachments (tree : Bool) (f : MarkFlags) : CountOrder :=
  combine (combine (localPath f.1) (localPath f.2.1)) (localTriangle tree f.2.2)

private theorem combine_assoc (a b c : CountOrder) :
    combine (combine a b) c = combine a (combine b c) := by
  apply Prod.ext <;> simp only [combine] <;> ring

private def offsets (start : Fin 5000) : ℕ × ℕ × ℕ :=
  (((0 : Fin 5000) - start).val, ((1000 : Fin 5000) - start).val, ((500 : Fin 5000) - start).val)

private def flagsAt (d : ℕ × ℕ × ℕ) (i : ℕ) : MarkFlags :=
  (decide (d.1 ≤ i), decide (d.2.1 ≤ i), decide (d.2.2 ≤ i))

private def flagsLo (d : ℕ × ℕ × ℕ) (f : MarkFlags) : ℕ :=
  max (if f.1 then d.1 else 0) (max (if f.2.1 then d.2.1 else 0) (if f.2.2 then d.2.2 else 0))

private def flagsHi (d : ℕ × ℕ × ℕ) (f : MarkFlags) : ℕ :=
  min 4999 (min (if f.1 then 4999 else d.1)
    (min (if f.2.1 then 4999 else d.2.1) (if f.2.2 then 4999 else d.2.2)))

private theorem flagsHi_le (d : ℕ × ℕ × ℕ) (f : MarkFlags) : flagsHi d f ≤ 4999 :=
  min_le_left _ _

private theorem flagsAt_eq (d : ℕ × ℕ × ℕ) (i : Fin 4999) (f : MarkFlags) :
    flagsAt d i.val = f ↔ flagsLo d f ≤ i.val ∧ i.val < flagsHi d f := by
  obtain ⟨a,b,c⟩ := f
  have hi := i.isLt
  cases a <;> cases b <;> cases c <;>
    simp [flagsAt, flagsLo, flagsHi, hi, not_le] <;> tauto

private def intervalFibers (d : ℕ × ℕ × ℕ) :
    Fin 4999 ≃ Σ f : MarkFlags, {i : Fin 4999 // flagsLo d f ≤ i.val ∧ i.val < flagsHi d f} :=
  (Equiv.sigmaFiberEquiv (fun i : Fin 4999 => flagsAt d i.val)).symm.trans
    (Equiv.sigmaCongrRight fun f => Equiv.subtypeEquivRight fun i => flagsAt_eq d i f)

private def startRow (tree : Bool) (d : ℕ × ℕ × ℕ) : CountOrder :=
  ∑ f : MarkFlags, combine (intervalMoments (flagsLo d f) (flagsHi d f)) (attachments tree f)

private theorem sum_startRow (tree : Bool) (d : ℕ × ℕ × ℕ) :
    ∑ i : Fin 4999, combine (contribution 1 (i.val + 1)) (attachments tree (flagsAt d i.val)) =
      startRow tree d := by
  rw [← (intervalFibers d).symm.sum_comp
    (fun i : Fin 4999 =>
      combine (contribution 1 (i.val + 1)) (attachments tree (flagsAt d i.val))), Fintype.sum_sigma]
  unfold startRow
  apply Finset.sum_congr rfl
  intro f _
  change (∑ i : {i : Fin 4999 // flagsLo d f ≤ i.val ∧ i.val < flagsHi d f},
      combine (contribution 1 (i.val.val + 1)) (attachments tree (flagsAt d i.val.val))) = _
  have h (i : {i : Fin 4999 // flagsLo d f ≤ i.val ∧ i.val < flagsHi d f}) :
      flagsAt d i.val.val = f := (flagsAt_eq d i.val f).mpr i.property
  simp_rw [h, sum_combine_left, sum_interval_indices (flagsHi_le d f)]

private def properLength : Fin 4999 ≃ {l : Fin 5000 // 0 < l.val} where
  toFun i := ⟨⟨i.val+1, by have hi := i.isLt; omega⟩, Nat.zero_lt_succ _⟩
  invFun l := ⟨l.val.val-1, by have hl := l.val.isLt; omega⟩
  left_inv i := Fin.ext (by simp)
  right_inv l := Subtype.ext (Fin.ext (by have hl := l.property; simp; omega))

private theorem proper_mem_iff (start : Fin 5000) (i : Fin 4999) (m : Fin 5000) :
    m ∈ CycleInterval.cycleVertices (m := 4997) (.inr (start, properLength i)) ↔
      (m - start).val ≤ i.val := by
  change (m ∈ CycleConnectedForcing.arc (m := 4997) start (i.val+1)) ↔ _
  rw [CycleConnectedForcing.mem_arc]
  exact Nat.lt_succ_iff

private theorem proper_arc_not_full (start : Fin 5000) (i : Fin 4999) :
    CycleInterval.cycleVertices (m := 4997) (.inr (start, properLength i)) ≠ Set.univ := by
  intro h
  have hmem : start - 1 ∈ CycleInterval.cycleVertices (m := 4997) (.inr (start, properLength i)) :=
    h.symm ▸ Set.mem_univ _
  have hm := (proper_mem_iff start i (start - 1)).mp hmem
  rw [show start - 1 - start = (0 : Fin 5000) - 1 by abel] at hm
  have hi := i.isLt
  change 4999 ≤ i.val at hm
  omega

private theorem proper_arc_contribution (tree : Bool) (start : Fin 5000) (i : Fin 4999) :
    arcContribution tree (.inr (start, properLength i)) =
      combine (contribution 1 (i.val+1)) (attachments tree (flagsAt (offsets start) i.val)) := by
  classical
  have hw : circleWeight tree (.inr (start, properLength i)) = 1 := by
    simp [circleWeight, fullWeight, proper_arc_not_full start i]
  have ho : CycleInterval.cycleOrder (m := 4997) (.inr (start, properLength i)) = i.val + 1 := rfl
  simp only [arcContribution, hw, ho, attachments, flagsAt, offsets, proper_mem_iff, combine_assoc]
  rfl

private def fullArc (tree : Bool) : CountOrder :=
  combine (contribution (if tree then 5000 else 1) 5000)
    (attachments tree (true,true,true))

private theorem sum_arc_rows (tree : Bool) :
    (∑ c : CycleInterval 4997, arcContribution tree c) =
      fullArc tree + ∑ a : Fin 5000, startRow tree (offsets a) := by
  classical
  unfold CycleInterval
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hfull : (∑ a : Unit, arcContribution tree (.inl a)) = fullArc tree := by
    simp only [Fintype.sum_unique, arcContribution, CycleInterval.cycleVertices, CycleInterval.cycleOrder,
      circleWeight, Set.mem_univ, decide_true, fullWeight, Bool.and_true, fullArc, attachments]
    simp only [combine_assoc]
  rw [hfull]
  apply congrArg (fun x => fullArc tree + x)
  apply Finset.sum_congr rfl
  intro a _
  rw [← properLength.sum_comp (fun l => arcContribution tree (.inr (a,l)))]
  simp_rw [proper_arc_contribution]
  exact sum_startRow tree (offsets a)

private def properArcBlocks (tree : Bool) : CountOrder :=
  ∑ b : Fin 50, ∑ a : Fin 100, startRow tree (offsets (finProdFinEquiv (b,a)))

private theorem properArcBlocks_eq (tree : Bool) :
    (∑ a : Fin 5000, startRow tree (offsets a)) = properArcBlocks tree := by
  rw [← (finProdFinEquiv (m := 50) (n := 100)).sum_comp
    (fun a => startRow tree (offsets a)), Fintype.sum_prod_type]
  rfl

private def evaluatedMoments (tree : Bool) : CountOrder :=
  (fullArc tree + properArcBlocks tree) +
    ((∑ a : Fin 500, intervalMoments 0 (500-a.val)) +
      ((∑ a : Fin 500, intervalMoments 0 (500-a.val)) + (if tree then (9,18) else (7,12))))

private theorem codeMoments_eq_evaluated (tree : Bool) : codeMoments tree = evaluatedMoments tree := by
  rw [codeMoments_decompose, sum_arc_rows, properArcBlocks_eq, pathMoments_rows]
  rfl

set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
private theorem evaluated_induced :
    evaluatedMoments false = (10425438990512, 43855001336852520) := by
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 4000000 in
private theorem evaluated_trees :
    evaluatedMoments true = (14578492765509, 61323620645707018) := by
  decide +kernel

/-- Exact count and total order of the connected vertex supports of the witness. -/
theorem induced_exact_moments :
    (Nat.card (ConnectedSets G500),
      (letI : Fintype (ConnectedSets G500) := Fintype.ofFinite _
       ∑ S : ConnectedSets G500, Nat.card S.val)) = (10425438990512, 43855001336852520) := by
  suffices h : _ = codeMoments false from
    h.trans ((codeMoments_eq_evaluated false).trans evaluated_induced)
  apply Prod.ext
  · rw [connectedCount_transport]
    simp [codeMoments, contribution, weight, Prod.fst_sum, Nat.card_eq_fintype_card]
  · rw [connectedOrder_transport]
    simp [codeMoments, contribution, weight, Prod.snd_sum]

/-- Exact count and total order of the actual tree subgraphs of the witness. -/
theorem tree_exact_moments :
    (totalSubtreeCount G500, totalSubtreeOrder G500) = (14578492765509, 61323620645707018) := by
  suffices h : _ = codeMoments true from
    h.trans ((codeMoments_eq_evaluated true).trans evaluated_trees)
  apply Prod.ext
  · rw [subtreeCount_transport]
    simp [codeMoments, contribution, weight, Prod.fst_sum]
  · rw [subtreeOrder_transport]
    simp [codeMoments, contribution, weight, Prod.snd_sum, Nat.mul_comm]

/-- The exact rational difference between the two means on the fixed graph. -/
theorem exactGap :
    meanConnectedOrder G500 - meanSubtreeOrder G500 =
      (1769250196421378505239933 : ℚ) / 18998398362554330511481326 := by
  have hiN := congrArg Prod.fst induced_exact_moments
  have hiR := congrArg Prod.snd induced_exact_moments
  have htN := congrArg Prod.fst tree_exact_moments
  have htR := congrArg Prod.snd tree_exact_moments
  dsimp only [Prod.fst, Prod.snd] at hiN hiR htN htR
  unfold meanConnectedOrder meanSubtreeOrder
  rw [hiN, hiR, htN, htR]
  norm_num

/-- The tree mean of the witness is strictly smaller than its connected-support mean. -/
theorem strictComparison : meanSubtreeOrder G500 < meanConnectedOrder G500 := by
  apply sub_pos.mp
  rw [exactGap]
  norm_num

/-- The literal negation of Question 1.9. -/
theorem result : ¬ claim := by
  intro h
  exact (not_le_of_gt strictComparison) (h Vertex inferInstance G500 G500_connected)

#print axioms induced_exact_moments
#print axioms tree_exact_moments
#print axioms exactGap
#print axioms strictComparison
#print axioms result

end D5.S3.Combinatorics.Graph.BoundedDegree.CambieQ19Settlement
