/- GID: D5/S3/LatticeGauge/RectangleGeometry
   generality: G
   mirror-B: none(waiver:covered-by-lattice-reflection-positivity4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangle cycles, central changes of variables, and plaquette adjacency. -/

import D5.S3.LatticeGauge.Basic

/-!
Omega original.

Rectangle cycles, central changes of variables, and plaquette adjacency.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate Topology
open MeasureTheory Matrix Filter

namespace Omega.LatticeGauge

variable {n : Fin 4 → ℕ} {G : Type*} [Group G] {d : ℕ}
variable [MeasurableSpace G]

section Central

variable [MeasurableMul₂ G] [MeasurableInv G]

private def signedValue {E : Type*} (u : E → G) (edge : E × Bool) : G :=
  if edge.2 then u edge.1 else (u edge.1)⁻¹

def signedExponent {E : Type*} (a : E → ℤ) (edge : E × Bool) : ℤ :=
  if edge.2 then a edge.1 else -a edge.1

def twist {E : Type*} (z : G) (a : E → ℤ) (u : E → G) (e : E) : G :=
  z ^ a e * u e

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
private theorem twist_edge {E : Type*} (z : Subgroup.center G) (a : E → ℤ)
    (u : E → G) (edge : E × Bool) :
    signedValue (twist (z : G) a u) edge =
      (z : G) ^ signedExponent a edge * signedValue u edge := by
  obtain ⟨e, b⟩ := edge
  cases b
  · simp only [signedValue, signedExponent, twist, Bool.false_eq_true, ↓reduceIte,
      _root_.mul_inv_rev, zpow_neg]
    have hc : Commute (u e) ((z : G) ^ a e) :=
      Subgroup.mem_center_iff.mp (z ^ a e).property (u e)
    exact hc.inv_inv.eq
  · rfl

def pathHolonomy {E : Type*} (u : E → G) (path : List (E × Bool)) : G :=
  (path.map (signedValue u)).prod

def circulation {E : Type*} (a : E → ℤ) (path : List (E × Bool)) : ℤ :=
  (path.map (signedExponent a)).sum

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem twist_holonomy {E : Type*} (z : Subgroup.center G) (a : E → ℤ)
    (u : E → G) (path : List (E × Bool)) :
    pathHolonomy (twist (z : G) a u) path = (z : G) ^ circulation a path * pathHolonomy u path := by
  induction path with
  | nil => simp [pathHolonomy, circulation]
  | cons e path ih =>
    change signedValue (twist (z : G) a u) e * pathHolonomy (twist (z : G) a u) path =
      (z : G) ^ (signedExponent a e + circulation a path) * (signedValue u e * pathHolonomy u path)
    rw [twist_edge, ih, zpow_add]
    have hc : Commute (signedValue u e) ((z : G) ^ circulation a path) :=
      Subgroup.mem_center_iff.mp (z ^ circulation a path).property _
    rw [hc.mul_mul_mul_comm]

theorem measurable_path {E : Type*} (path : List (E × Bool)) :
    Measurable (fun u : E → G => pathHolonomy u path) := by
  induction path with
  | nil => exact measurable_const
  | cons e path ih =>
    have he : Measurable (fun u : E → G => signedValue u e) := by
      unfold signedValue
      split
      · exact measurable_pi_apply e.1
      · exact (measurable_pi_apply e.1).inv
    exact he.mul ih

def squareEdges (p : Plaquette n) : List (Link n × Bool) :=
  let ⟨⟨v, i, j⟩, hij, hi, hj⟩ := p
  [(⟨(v, i), hi⟩, true),
    (⟨(shift v i, j), by simpa [shift_apply_of_ne v hij.ne.symm] using hj⟩, true),
    (⟨(shift v j, i), by simpa [shift_apply_of_ne v hij.ne] using hi⟩, false),
    (⟨(v, j), hj⟩, false)]

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem square_eq_path (p : Plaquette n) (u : Link n → G) :
    squareHolonomy u p = pathHolonomy u (squareEdges p) := by
  obtain ⟨⟨v, i, j⟩, h, hi, hj⟩ := p
  simp [squareHolonomy, pathHolonomy, squareEdges, signedValue, mul_assoc]

def twistEquiv {E : Type*} (z : G) (a : E → ℤ) : (E → G) ≃ᵐ (E → G) :=
  MeasurableEquiv.mulLeft (fun e => z ^ a e)

omit [MeasurableInv G] in
theorem twist_preserving {E : Type*} [Fintype E] (μ : Measure G)
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (z : G) (a : E → ℤ) :
    MeasurePreserving (twistEquiv z a) (configMeasure μ E) (configMeasure μ E) :=
  by
    unfold configMeasure
    exact measurePreserving_mul_left _ _

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem trace_central_mul (D : GaugeData G d) (z : G) (ζ : ℂ)
    (hz : D.rep z = ζ • 1) (a : G) :
    (D.rep (z * a)).trace = ζ * (D.rep a).trace := by
  rw [map_mul, hz, Matrix.smul_mul, one_mul, Matrix.trace_smul, smul_eq_mul]

omit [MeasurableMul₂ G] [MeasurableInv G] in
theorem trace_central_inv_mul (D : GaugeData G d) (z : G) (ζ : ℂ)
    (hz : D.rep z = ζ • 1) (a : G) :
    (D.rep (z⁻¹ * a)).trace = conj ζ * (D.rep a).trace := by
  apply trace_central_mul
  rw [rep_inv, hz, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  rfl

end Central
section RectangleProjection

def rayCochain (i j : Fin 4) (a b : ℕ) (e : Link n) : ℤ :=
  if e.val.2 = i ∧ (e.val.1 i).val = a ∧ b < (e.val.1 j).val then 1 else 0

theorem shift_val_same {v : Vertex n} {i : Fin 4} (h : (v i).val < n i) :
    (shift v i i).val = (v i).val + 1 := by
  simp [shift, Fin.val_add, Nat.mod_eq_of_lt (by omega : (v i).val + 1 < n i + 1)]

theorem ray_circulation (i j : Fin 4) (hij : i < j) (a b : ℕ) (p : Plaquette n) :
    circulation (rayCochain i j a b) (squareEdges p) =
      if p.val.2.1 = i ∧ p.val.2.2 = j ∧ (p.val.1 i).val = a ∧ (p.val.1 j).val = b
      then -1 else 0 := by
  obtain ⟨⟨v, k, l⟩, hkl, hk, hl⟩ := p
  by_cases hki : k = i
  · subst k
    by_cases hlj : l = j
    · subst l
      simp only [circulation, squareEdges, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, signedExponent, Bool.false_eq_true, ↓reduceIte, rayCochain, hij.ne.symm,
        false_and, true_and, shift_apply_of_ne v hij.ne,
        shift_val_same hl, add_zero, zero_add]
      by_cases ha : (v i).val = a
      · simp only [ha, true_and]
        split_ifs <;> omega
      · simp [ha]
    · simp [circulation, squareEdges, signedExponent, rayCochain, hlj, hkl.ne.symm,
        shift_apply_of_ne v hkl.ne, shift_apply_of_ne v (Ne.symm hlj)]
  · by_cases hli : l = i
    · subst l
      have hkj : k ≠ j := by
        intro h
        subst k
        exact (not_lt_of_ge hij.le) hkl
      simp [circulation, squareEdges, signedExponent, rayCochain, hki,
        shift_apply_of_ne v (Ne.symm hki), shift_apply_of_ne v hkj.symm]
    · simp [circulation, squareEdges, signedExponent, rayCochain, hki, hli]

end RectangleProjection

section Rectangle

/-- A planar rectangle in an open four-dimensional box, with ordered coordinate axes. -/
structure Rectangle (n : Fin 4 → ℕ) where
  origin : Vertex n
  i : Fin 4
  j : Fin 4
  axes : i < j
  width : ℕ
  height : ℕ
  bound_i : (origin i).val + width ≤ n i
  bound_j : (origin j).val + height ≤ n j

namespace Rectangle

private def vertex (r : Rectangle n) (x y : ℕ) (hx : x ≤ r.width) (hy : y ≤ r.height) : Vertex n :=
  Function.update (Function.update r.origin r.i ⟨(r.origin r.i).val + x, by have := r.bound_i; omega⟩)
    r.j ⟨(r.origin r.j).val + y, by have := r.bound_j; omega⟩

private theorem vertex_i (r : Rectangle n) (x y : ℕ) (hx : x ≤ r.width) (hy : y ≤ r.height) :
    (r.vertex x y hx hy r.i).val = (r.origin r.i).val + x := by
  simp [vertex, Function.update_of_ne r.axes.ne]

private theorem vertex_j (r : Rectangle n) (x y : ℕ) (hx : x ≤ r.width) (hy : y ≤ r.height) :
    (r.vertex x y hx hy r.j).val = (r.origin r.j).val + y := by
  simp [vertex]

def horizontal (r : Rectangle n) (y : ℕ) (hy : y ≤ r.height) (x : Fin r.width) : Link n :=
  ⟨(r.vertex x y x.isLt.le hy, r.i), by
    simp only [vertex_i]
    have := r.bound_i
    omega⟩

private def vertical (r : Rectangle n) (x : ℕ) (hx : x ≤ r.width) (y : Fin r.height) : Link n :=
  ⟨(r.vertex x y hx y.isLt.le, r.j), by
    simp only [vertex_j]
    have := r.bound_j
    omega⟩

/-- The bottom, right, top and left sides, traversed in that order. -/
def edges (r : Rectangle n) : List (Link n × Bool) :=
  List.ofFn (fun x => (r.horizontal 0 (Nat.zero_le _) x, true)) ++
  List.ofFn (fun y => (r.vertical r.width le_rfl y, true)) ++
  (List.ofFn (fun x => (r.horizontal r.height le_rfl x, false))).reverse ++
  (List.ofFn (fun y => (r.vertical 0 (Nat.zero_le _) y, false))).reverse

theorem cell_ray (r : Rectangle n) (a : Fin r.width) (b : Fin r.height) :
    circulation (rayCochain r.i r.j ((r.origin r.i).val + a) ((r.origin r.j).val + b)) r.edges = -1 := by
  simp only [circulation, edges, List.map_append, List.sum_append, List.map_reverse, List.sum_reverse,
    List.map_ofFn, List.sum_ofFn, Function.comp_def, signedExponent, rayCochain, horizontal, vertical, vertex_i, vertex_j,
    r.axes.ne.symm, false_and, neg_zero, Finset.sum_const_zero, add_zero, true_and, ↓reduceIte]
  have hyes : (r.origin r.j).val + b.val < (r.origin r.j).val + r.height := by omega
  simp only [hyes, and_true, Nat.add_left_cancel_iff]
  simp only [show ∀ x : Fin r.width, (x.val = a.val) = (x = a) from
    fun x => propext ⟨Fin.ext, congrArg Fin.val⟩]
  simp

end Rectangle
end Rectangle

def squareLinks (p : Plaquette n) : Finset (Link n) :=
  let ⟨⟨v, i, j⟩, hij, hi, hj⟩ := p
  {⟨(v,i),hi⟩, ⟨(shift v i,j), by simpa [shift_apply_of_ne v hij.ne.symm] using hj⟩,
    ⟨(shift v j,i), by simpa [shift_apply_of_ne v hij.ne] using hi⟩, ⟨(v,j),hj⟩}

def incidentSquares (e : Link n) : Finset (Plaquette n) :=
  Finset.univ.filter fun p => e ∈ squareLinks p

private def otherAxis (e : Link n) (p : Plaquette n) : Fin 4 :=
  if p.val.2.1 = e.val.2 then p.val.2.2 else p.val.2.1

private theorem shift_injective (axis : Fin 4) : Function.Injective (fun v : Vertex n => shift v axis) := by
  intro v w h
  ext i
  by_cases hi : i = axis
  · subst i
    have h' := congr_fun h axis
    simp only [shift, Function.update_self] at h'
    exact congrArg Fin.val (add_right_cancel h')
  · exact congrArg Fin.val (by simpa only [shift_apply_of_ne _ hi] using congr_fun h i)

private theorem incident_otherAxis (e : Link n) (p : Plaquette n) (h : e ∈ squareLinks p) :
    let k := otherAxis e p
    k ≠ e.val.2 ∧ p.val.2.1 = min e.val.2 k ∧ p.val.2.2 = max e.val.2 k ∧
      (e.val.1 = p.val.1 ∨ e.val.1 = shift p.val.1 k) := by
  rcases p with ⟨⟨v,i,j⟩, hij, hi, hj⟩
  simp only [squareLinks, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  all_goals
    simp [otherAxis, hij.ne, hij.ne.symm, min_eq_left hij.le, min_eq_right hij.le,
      max_eq_left hij.le, max_eq_right hij.le]

theorem incidentSquares_card_le (e : Link n) : (incidentSquares e).card ≤ 6 := by
  classical
  let encode : (incidentSquares e) → {k : Fin 4 // k ≠ e.val.2} × Bool := fun p =>
    (⟨otherAxis e p, (incident_otherAxis e p ((Finset.mem_filter.mp p.property).2)).1⟩,
      decide (e.val.1 = p.val.val.1))
  have hinj : Function.Injective encode := by
    intro p q he
    have hp := incident_otherAxis e p ((Finset.mem_filter.mp p.property).2)
    have hq := incident_otherAxis e q ((Finset.mem_filter.mp q.property).2)
    have hk : otherAxis e p = otherAxis e q := congrArg (fun v => v.1.val) he
    rw [hk] at hp
    have hi := hp.2.1.trans hq.2.1.symm
    have hj := hp.2.2.1.trans hq.2.2.1.symm
    have hs : decide (e.val.1 = p.val.val.1) = decide (e.val.1 = q.val.val.1) := congrArg Prod.snd he
    have hbase : p.val.val.1 = q.val.val.1 := by
      by_cases hp' : e.val.1 = p.val.val.1
      · have hq' : e.val.1 = q.val.val.1 := by simpa [hp', eq_comm] using hs
        exact hp'.symm.trans hq'
      · have hq' : ¬ e.val.1 = q.val.val.1 := by simpa [hp', eq_comm] using hs
        exact shift_injective (otherAxis e q)
          ((hp.2.2.2.resolve_left hp').symm.trans (hq.2.2.2.resolve_left hq'))
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hbase (Prod.ext hi hj)
  have h := Fintype.card_le_of_injective encode hinj
  simpa [Fintype.card_subtype_compl, Finset.card_filter] using h

private theorem squareLinks_card_le (p : Plaquette n) : (squareLinks p).card ≤ 4 := by
  rcases p with ⟨⟨v,i,j⟩, hij, hi, hj⟩
  exact (Finset.card_insert_le _ _).trans
    (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))

def squareAdj (p q : Plaquette n) : Prop :=
  p ≠ q ∧ ∃ e ∈ squareLinks p, e ∈ squareLinks q

private instance (p q : Plaquette n) : Decidable (squareAdj p q) :=
  inferInstanceAs (Decidable (p ≠ q ∧ ∃ e ∈ squareLinks p, e ∈ squareLinks q))

theorem adjacentSquares_card_le (p : Plaquette n) :
    ((Finset.univ : Finset (Plaquette n)).filter (squareAdj p)).card ≤ 20 := by
  classical
  have hsub : Finset.univ.filter (squareAdj p) ⊆
      (squareLinks p).biUnion (fun e => (incidentSquares e).erase p) := by
    intro q hq
    obtain ⟨hn, e, he, hq'⟩ := (Finset.mem_filter.mp hq).2
    exact Finset.mem_biUnion.mpr ⟨e, he, Finset.mem_erase.mpr
      ⟨Ne.symm hn, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq'⟩⟩⟩
  calc
    _ ≤ ((squareLinks p).biUnion (fun e => (incidentSquares e).erase p)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ e ∈ squareLinks p, ((incidentSquares e).erase p).card := Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ squareLinks p, 5 := by
      apply Finset.sum_le_sum
      intro e he
      have hu : p ∈ incidentSquares e := by simpa [incidentSquares] using he
      have hv := incidentSquares_card_le e
      rw [Finset.card_erase_of_mem hu]
      omega
    _ = (squareLinks p).card * 5 := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (squareLinks_card_le p)

theorem incidentSquares_clique (e : Link n) (p q : Plaquette n)
    (hp : p ∈ incidentSquares e) (hq : q ∈ incidentSquares e) (hn : p ≠ q) : squareAdj p q :=
  ⟨hn, e, (Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hq).2⟩

private def restrictedCoboundary {E V : Type*} [DecidableEq E] (source target : E → V)
    (S : Finset E) (potential : V → ℤ) (e : E) : ℤ :=
  if e ∈ S then potential (source e) - potential (target e) else 0

private theorem cycle_has_transition {L : ℕ} (s : Fin L → Prop) (hyes : ∃ k, s k)
    (hno : ∃ k, ¬s k) : ∃ k, ¬(s k ↔ s (finRotate L k)) := by
  classical
  by_contra! h
  obtain ⟨i, hi⟩ := hyes
  obtain ⟨j, hj⟩ := hno
  cases L with
  | zero => exact i.elim0
  | succ n =>
    have hconst (k : Fin (n+1)) : s k ↔ s 0 := by
      induction k using Fin.induction with
      | zero => rfl
      | succ k ih =>
        have heq : finRotate (n+1) k.castSucc = k.succ := by
          simp
        rw [← heq, ← h k.castSucc, ih]
    exact hj ((hconst j).mpr ((hconst i).mp hi))

theorem restricted_coboundary_detects_partial_cycle {E V : Type*} [DecidableEq E]
    (source target : E → V) (S : Finset E) {L : ℕ}
    (vertices : Fin L → V) (edge : Fin L → E × Bool) (hv : Function.Injective vertices)
    (hsrc : ∀ k, (if (edge k).2 then source (edge k).1 else target (edge k).1) = vertices k)
    (hdst : ∀ k, (if (edge k).2 then target (edge k).1 else source (edge k).1) =
      vertices (finRotate L k))
    (hmeet : ∃ k, (edge k).1 ∈ S) (hmiss : ∃ k, (edge k).1 ∉ S) :
    ∃ f : V → ℤ,
      circulation (restrictedCoboundary source target S f) (List.ofFn edge) = 1 ∨
      circulation (restrictedCoboundary source target S f) (List.ofFn edge) = -1 := by
  classical
  obtain ⟨i, hi⟩ := cycle_has_transition (fun k => (edge k).1 ∈ S) hmeet hmiss
  let j := finRotate L i
  let f : V → ℤ := fun v => if v = vertices j then 1 else 0
  refine ⟨f, ?_⟩
  have hval (k : Fin L) : f (vertices k) = if k = j then 1 else 0 := by
    simp only [f, hv.eq_iff]
  have hc (k : Fin L) : signedExponent (restrictedCoboundary source target S f) (edge k) =
      (if (edge k).1 ∈ S then f (vertices k) - f (vertices (finRotate L k)) else 0) := by
    have hs := hsrc k
    have ht := hdst k
    cases he : (edge k).2
    · simp only [he, Bool.false_eq_true, ite_false] at hs ht
      simp only [signedExponent, restrictedCoboundary, he, Bool.false_eq_true, ite_false, ← hs, ← ht]
      split_ifs <;> omega
    · simp only [he, ite_true] at hs ht
      simp only [signedExponent, restrictedCoboundary, he, ite_true, hs, ht]
  have hsum :
      circulation (restrictedCoboundary source target S f) (List.ofFn edge) =
      (if (edge j).1 ∈ S then 1 else 0) - (if (edge i).1 ∈ S then 1 else 0) := by
    rw [circulation, List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_apply, hc, hval, j, (finRotate L).injective.eq_iff]
    calc
      _ = ∑ k : Fin L, ((if k = j then if (edge k).1 ∈ S then (1 : ℤ) else 0 else 0) -
          (if k = i then if (edge k).1 ∈ S then (1 : ℤ) else 0 else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : (edge k).1 ∈ S <;>
          simp only [← show j = finRotate L i from rfl, hk, ite_true, ite_false, ite_self, sub_zero]
      _ = _ := by simp [Finset.sum_sub_distrib, j]
  rw [hsum]
  by_cases a : (edge i).1 ∈ S
  · have b : (edge j).1 ∉ S := fun b => hi (iff_of_true a b)
    simp [a, b]
  · have b : (edge j).1 ∈ S := by
      by_contra b
      exact hi (iff_of_false a b)
    simp [a, b]

section RectangleCycle

private def orientedStart (a : Link n × Bool) : Vertex n := if a.2 then src a.1 else dst a.1
private def orientedEnd (a : Link n × Bool) : Vertex n := if a.2 then dst a.1 else src a.1

namespace Rectangle

abbrev perimeter (r : Rectangle n) := r.width + r.height + r.width + r.height

def cycleEdge (r : Rectangle n) (k : Fin r.perimeter) : Link n × Bool :=
  if h₁ : k.val < r.width then (r.horizontal 0 (Nat.zero_le _) ⟨k, h₁⟩, true)
  else if h₂ : k.val < r.width + r.height then
    (r.vertical r.width le_rfl ⟨k.val - r.width, by omega⟩, true)
  else if h₃ : k.val < r.width + r.height + r.width then
    (r.horizontal r.height le_rfl ⟨r.width - 1 - (k.val - (r.width + r.height)), by omega⟩, false)
  else (r.vertical 0 (Nat.zero_le _) ⟨r.height - 1 - (k.val - (r.width + r.height + r.width)),
    by have := k.isLt; unfold perimeter at this; omega⟩, false)

theorem cycleEdge_eq (r : Rectangle n) : List.ofFn r.cycleEdge = r.edges := by
  apply List.ext_getElem
  · simp [edges, perimeter, Nat.add_assoc]
  intro k h₁ h₂
  simp only [List.getElem_ofFn]
  simp only [cycleEdge, edges, List.getElem_append, List.length_append, List.length_reverse,
    List.length_ofFn, List.getElem_reverse, List.getElem_ofFn]
  split_ifs <;> first | rfl | congr 3 <;> omega

private def xy (r : Rectangle n) (k : ℕ) : ℕ × ℕ :=
  if k < r.width then (k, 0)
  else if k < r.width + r.height then (r.width, k - r.width)
  else if k < r.width + r.height + r.width then (r.width - (k - (r.width + r.height)), r.height)
  else (0, r.height - (k - (r.width + r.height + r.width)))

private theorem xy_bounds (r : Rectangle n) (k : ℕ) :
    (r.xy k).1 ≤ r.width ∧ (r.xy k).2 ≤ r.height := by
  unfold xy
  split_ifs <;> omega

def cycleVertex (r : Rectangle n) (k : Fin r.perimeter) : Vertex n :=
  r.vertex (r.xy k).1 (r.xy k).2 (r.xy_bounds k).1 (r.xy_bounds k).2

private theorem vertex_val (r : Rectangle n) (x y : ℕ) (hx : x ≤ r.width) (hy : y ≤ r.height)
    (l : Fin 4) :
    (r.vertex x y hx hy l).val =
      if l = r.i then (r.origin l).val + x
      else if l = r.j then (r.origin l).val + y else (r.origin l).val := by
  by_cases hi : l = r.i
  · subst l; simp [vertex_i]
  by_cases hj : l = r.j
  · subst l; simp [vertex_j, r.axes.ne.symm]
  simp [vertex, hi, hj]

theorem cycleVertex_injective (r : Rectangle n) (hw : 0 < r.width) (hh : 0 < r.height) :
    Function.Injective r.cycleVertex := by
  intro a b heq
  have hx := congrArg (fun v : Vertex n => (v r.i).val) heq
  have hy := congrArg (fun v : Vertex n => (v r.j).val) heq
  simp only [cycleVertex, vertex_i, vertex_j, Nat.add_left_cancel_iff] at hx hy
  apply Fin.ext
  have ha : a.val < r.perimeter := a.isLt
  have hb : b.val < r.perimeter := b.isLt
  simp only [perimeter] at ha hb
  simp only [xy] at hx hy
  split_ifs at hx hy <;> simp only at hx hy <;> omega

private theorem shift_vertex_i (r : Rectangle n) (x y : ℕ) (hx : x < r.width) (hy : y ≤ r.height) :
    shift (r.vertex x y hx.le hy) r.i =
      r.vertex (x + 1) y hx hy := by
  have h : (r.vertex x y hx.le hy r.i).val < n r.i := by
    rw [vertex_i]
    have := r.bound_i
    omega
  funext l
  apply Fin.ext
  by_cases hi : l = r.i
  · subst l
    simp only [shift_val_same h, vertex_i]
    omega
  · simp [shift_apply_of_ne _ hi, vertex_val, hi]

private theorem shift_vertex_j (r : Rectangle n) (x y : ℕ) (hx : x ≤ r.width) (hy : y < r.height) :
    shift (r.vertex x y hx hy.le) r.j =
      r.vertex x (y + 1) hx hy := by
  have h : (r.vertex x y hx hy.le r.j).val < n r.j := by
    rw [vertex_j]
    have := r.bound_j
    omega
  funext l
  apply Fin.ext
  by_cases hj : l = r.j
  · subst l
    simp only [shift_val_same h, vertex_j]
    omega
  · simp [shift_apply_of_ne _ hj, vertex_val, hj]

private theorem vertex_congr (r : Rectangle n) {a b x y : ℕ} {ha : a ≤ r.width}
    {hb : b ≤ r.height} {hx : x ≤ r.width} {hy : y ≤ r.height}
    (h₁ : a = x) (h₂ : b = y) : r.vertex a b ha hb = r.vertex x y hx hy := by
  subst x y
  rfl

theorem cycleEdge_start (r : Rectangle n) (k : Fin r.perimeter) :
    orientedStart (r.cycleEdge k) = r.cycleVertex k := by
  have hk : k.val < r.width + r.height + r.width + r.height := k.isLt
  simp only [cycleEdge, cycleVertex]
  split_ifs <;> simp only [orientedStart, Bool.false_eq_true, ite_false, ite_true, horizontal, vertical, src, dst]
  · apply vertex_congr <;> simp [xy, *]
  · apply vertex_congr <;> simp [xy, *]
  · rw [shift_vertex_i]
    · apply vertex_congr <;> simp [xy, *]
      omega
    · omega
  · rw [shift_vertex_j]
    · apply vertex_congr <;> simp [xy, *]
      omega
    · omega

private theorem finRotate_val {L : ℕ} (k : Fin L) :
    (finRotate L k).val = if k.val + 1 < L then k.val + 1 else 0 := by
  cases L with
  | zero => exact k.elim0
  | succ L =>
    rw [coe_finRotate]
    have := k.isLt
    split_ifs with h h' h' <;> (simp_all [Fin.ext_iff]; try omega)

theorem cycleEdge_end (r : Rectangle n) (hw : 0 < r.width) (hh : 0 < r.height)
    (k : Fin r.perimeter) : orientedEnd (r.cycleEdge k) = r.cycleVertex (finRotate _ k) := by
  have hk : k.val < r.perimeter := k.isLt
  simp only [perimeter] at hk
  simp only [cycleEdge, cycleVertex]
  split_ifs <;> simp only [orientedEnd, Bool.false_eq_true, ite_false, ite_true, horizontal, vertical, src, dst]
  · rw [shift_vertex_i]
    · apply vertex_congr <;> simp only [xy, finRotate_val, perimeter]
      · split_ifs <;> omega
      · split_ifs <;> omega
    · omega
  · rw [shift_vertex_j]
    · apply vertex_congr <;> simp only [xy, finRotate_val, perimeter]
      · split_ifs <;> omega
      · split_ifs <;> omega
    · omega
  · apply vertex_congr <;> simp only [xy, finRotate_val, perimeter]
    · split_ifs <;> omega
    · split_ifs <;> omega
  · apply vertex_congr <;> simp only [xy, finRotate_val, perimeter]
    · split_ifs <;> omega
    · split_ifs <;> omega

end Rectangle
end RectangleCycle

end Omega.LatticeGauge
