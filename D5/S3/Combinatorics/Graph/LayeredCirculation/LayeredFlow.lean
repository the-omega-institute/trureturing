/- GID: D5/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LayeredCirculation/LayeredFlow
   mirror-E: none(waiver:algebraically-proved)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic]
   utility: none
   digest: Complete five-pattern overlap laws correspond to normalized three-state layered circulations. -/

import D5.S3.Combinatorics.Graph.LayeredCirculation.PositiveCircuitSupplier
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Order.WithBot
import Mathlib.Algebra.Tropical.BigOperators
import Mathlib.LinearAlgebra.Matrix.Trace

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum

open scoped BigOperators
open Maths Maths.AdditiveTransport
noncomputable section

/-- The original order is 000, 100, 010, 001, 101. -/
def pattern : Fin 5 → Bool × Bool × Bool :=
  ![(false, false, false), (true, false, false), (false, true, false),
    (false, false, true), (true, false, true)]

/-- The original seam order is 00, 01, 10. -/
def seam : Fin 3 → Bool × Bool := ![(false, false), (false, true), (true, false)]

def sourceState : Fin 5 → Fin 3 := ![0, 2, 1, 0, 2]
def targetState : Fin 5 → Fin 3 := ![0, 0, 2, 1, 1]

/-- Nonnegative probability laws, including their zero boundaries, with all four
binary overlap equations. The 11 equation is identically zero. -/
def IsLocalLaw {n : ℕ} (p : ZMod n → Fin 5 → ℝ) : Prop :=
  (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ = 1) ∧
  ∀ i b c,
    (∑ σ, if (pattern σ).2.1 = b ∧ (pattern σ).2.2 = c then p i σ else 0) =
    ∑ σ, if (pattern σ).1 = b ∧ (pattern σ).2.1 = c then p (i + 1) σ else 0

def localScore {n : ℕ} [NeZero n] (f p : ZMod n → Fin 5 → ℝ) : ℝ :=
  ∑ i, ∑ σ, f i σ * p i σ

/-- Each five-pattern edge retains its position label. -/
def layeredGraph (n : ℕ) : EdgeGraph (ZMod n × Fin 3) (ZMod n × Fin 5) where
  source e := (e.1, sourceState e.2)
  target e := (e.1 + 1, targetState e.2)

theorem labels (σ : Fin 5) :
    seam (sourceState σ) = ((pattern σ).1, (pattern σ).2.1) ∧
    seam (targetState σ) = ((pattern σ).2.1, (pattern σ).2.2) := by
  fin_cases σ <;> decide

private theorem overlap_iff {n : ℕ} (p : ZMod n → Fin 5 → ℝ) :
    (∀ i b c,
      (∑ σ, if (pattern σ).2.1 = b ∧ (pattern σ).2.2 = c then p i σ else 0) =
      ∑ σ, if (pattern σ).1 = b ∧ (pattern σ).2.1 = c then p (i + 1) σ else 0) ↔
    ∀ i s,
      (∑ σ, if targetState σ = s then p i σ else 0) =
      ∑ σ, if sourceState σ = s then p (i + 1) σ else 0 := by
  constructor
  · intro h i s
    fin_cases s
    · simpa [Fin.sum_univ_five, pattern, sourceState, targetState] using h i false false
    · simpa [Fin.sum_univ_five, pattern, sourceState, targetState] using h i false true
    · simpa [Fin.sum_univ_five, pattern, sourceState, targetState] using h i true false
  · intro h i b c
    cases b <;> cases c
    · simpa [Fin.sum_univ_five, pattern, sourceState, targetState] using h i 0
    · simpa [Fin.sum_univ_five, pattern, sourceState, targetState] using h i 1
    · simpa [Fin.sum_univ_five, pattern, sourceState, targetState] using h i 2
    · simp [Fin.sum_univ_five, pattern]

/-- Literal edge balance at every vertex, without a normalization assumption. -/
def IsCirculation {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Prop :=
  ∀ v,
    (∑ e, if (layeredGraph n).source e = v then p e.1 e.2 else 0) =
    ∑ e, if (layeredGraph n).target e = v then p e.1 e.2 else 0

private theorem incidence_sums {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) (i : ZMod n) (s : Fin 3) :
    (∑ e, if (layeredGraph n).source e = (i,s) then p e.1 e.2 else 0) =
        (∑ σ, if sourceState σ = s then p i σ else 0) ∧
    (∑ e, if (layeredGraph n).target e = (i,s) then p e.1 e.2 else 0) =
        (∑ σ, if targetState σ = s then p (i-1) σ else 0) := by
  constructor
  · simp only [Fintype.sum_prod_type, layeredGraph, Prod.mk.injEq, ite_and]
    rw [Finset.sum_comm]
    simp
  · have heq (j : ZMod n) : j+1=i ↔ j=i-1 := by
      constructor
      · intro h; rw [← h, add_sub_cancel_right]
      · intro h; rw [h, sub_add_cancel]
    simp only [Fintype.sum_prod_type, layeredGraph, Prod.mk.injEq, heq, ite_and]
    rw [Finset.sum_comm]
    simp

private theorem overlap_circulation_iff {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) :
    (∀ i s, (∑ σ, if targetState σ = s then p i σ else 0) =
      ∑ σ, if sourceState σ = s then p (i + 1) σ else 0) ↔ IsCirculation p := by
  constructor
  · intro h ⟨i,s⟩
    rw [(incidence_sums p i s).1, (incidence_sums p i s).2]
    simpa using (h (i-1) s).symm
  · intro h i s
    have hv := h (i+1,s)
    rw [(incidence_sums p (i+1) s).1, (incidence_sums p (i+1) s).2] at hv
    simpa using hv.symm

theorem local_law_iff {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) :
    IsLocalLaw p ↔ (∀ i σ, 0 ≤ p i σ) ∧ (∀ i, ∑ σ, p i σ = 1) ∧ IsCirculation p := by
  simp only [IsLocalLaw, and_congr_right_iff]
  intro _ _
  exact (overlap_iff p).trans (overlap_circulation_iff p)

/-- The number of departures from a labeled layer counts repeated traversals. -/
def layerCount {n : ℕ} {a b : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a b) (i : ZMod n) : ℕ :=
  ∑ σ, w.edgeMultiplicity (i,σ)

private theorem layer_balance {n : ℕ} [NeZero n] {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) (i : ZMod n) :
    layerCount w (i+1) = layerCount w i := by
  have hv (s : Fin 3) := w.edgeMultiplicity_balanced (i+1,s)
  have hreal : ∀ s : Fin 3,
      (∑ σ, if sourceState σ = s then w.edgeMultiplicity (i+1,σ) else 0) =
      ∑ σ, if targetState σ = s then w.edgeMultiplicity (i,σ) else 0 := by
    intro s
    have := hv s
    simp only [EdgeGraph.outgoingMultiplicity, EdgeGraph.incomingMultiplicity,
      Finset.sum_filter, Fintype.sum_prod_type, layeredGraph, Prod.mk.injEq,
      add_left_inj, ite_and] at this
    have hswap : ∀ (k : ZMod n) (g : Fin 5 → Fin 3),
        (∑ j, ∑ σ, if j = k then (if g σ = s then w.edgeMultiplicity (j,σ) else 0) else 0) =
          ∑ σ, if g σ = s then w.edgeMultiplicity (k,σ) else 0 := by
      intro k g
      rw [Finset.sum_comm]
      simp
    rw [hswap, hswap] at this
    exact this
  have hs :
      (∑ s : Fin 3, ∑ σ, if sourceState σ = s then w.edgeMultiplicity (i+1,σ) else 0) =
      ∑ s : Fin 3, ∑ σ, if targetState σ = s then w.edgeMultiplicity (i,σ) else 0 :=
    Finset.sum_congr rfl (fun s _ => hreal s)
  simpa [layerCount, Fin.sum_univ_three, Fin.sum_univ_five, sourceState, targetState,
    add_assoc, add_comm, add_left_comm] using hs

theorem layer_count_uniform {n : ℕ} [NeZero n] {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) (i : ZMod n) :
    layerCount w i = layerCount w 0 := by
  have hall (k : ℕ) : layerCount w (k : ZMod n) = layerCount w 0 := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.cast_add, Nat.cast_one] using (layer_balance w k).trans ih
  simpa only [ZMod.natCast_zmod_val] using hall i.val

theorem length_eq_layer_count {n : ℕ} [NeZero n] {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) : w.length = n * layerCount w 0 := by
  have ht := Maths.AdditiveTransport.sum_edgeMultiplicity_eq_length w
  rw [Fintype.sum_prod_type] at ht
  change (∑ i, layerCount w i) = w.length at ht
  simp_rw [layer_count_uniform w] at ht
  simpa only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, Nat.cast_id] using ht.symm

/-- Traversal counts divided by the number of circuits around the layers. -/
def walkLaw {n : ℕ} {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) : ZMod n → Fin 5 → ℝ :=
  fun i σ => w.edgeMultiplicity (i,σ) / layerCount w 0

theorem walk_law_local {n : ℕ} [NeZero n] {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) (hw : 0 < w.length) : IsLocalLaw (walkLaw w) := by
  have hm : 0 < layerCount w 0 := by
    by_contra h
    have hz : layerCount w 0 = 0 := by omega
    rw [length_eq_layer_count, hz, mul_zero] at hw
    omega
  have hmr : (0:ℝ) < layerCount w 0 := by exact_mod_cast hm
  rw [local_law_iff]
  refine ⟨fun i σ => div_nonneg (Nat.cast_nonneg _) hmr.le, ?_, ?_⟩
  · intro i
    simp only [walkLaw, ← Finset.sum_div, ← Nat.cast_sum]
    change (layerCount w i : ℝ) / layerCount w 0 = 1
    rw [layer_count_uniform, div_self hmr.ne']
  · intro v
    have hb := w.edgeMultiplicity_balanced v
    have hbr :
        (∑ e, if (layeredGraph n).source e = v then (w.edgeMultiplicity e : ℝ) else 0) =
        ∑ e, if (layeredGraph n).target e = v then (w.edgeMultiplicity e : ℝ) else 0 := by
      simp only [EdgeGraph.outgoingMultiplicity, EdgeGraph.incomingMultiplicity,
        Finset.sum_filter] at hb
      exact_mod_cast hb
    have hd (P : Prop) [Decidable P] (x : ℝ) :
        (if P then x / (layerCount w 0 : ℝ) else 0) =
          (if P then x else 0) / layerCount w 0 := by split_ifs <;> simp
    simp only [walkLaw, hd, ← Finset.sum_div]
    exact congrArg (fun x : ℝ => x / layerCount w 0) hbr

theorem walk_law_score {n : ℕ} [NeZero n] (f : ZMod n → Fin 5 → ℝ)
    {a : ZMod n × Fin 3} (w : (layeredGraph n).Walk a a) :
    localScore f (walkLaw w) =
      Maths.MaxPlusPotential.walkWeight (fun e => f e.1 e.2) w / layerCount w 0 := by
  simp only [localScore, walkLaw, ← mul_div_assoc, ← Finset.sum_div]
  rw [← Fintype.sum_prod_type' (fun i σ => f i σ * (w.edgeMultiplicity (i,σ) : ℝ))]
  have ht := Maths.AdditiveTransport.sum_edgeMultiplicity_mul_eq_walkWeight_general
    (fun e : ZMod n × Fin 5 => f e.1 e.2) w
  simpa only [mul_comm] using congrArg (fun x : ℝ => x / layerCount w 0) ht

private def forwardWalk {V E : Type*} {G : EdgeGraph V E} {a : V} :
    {b : V} → G.Walk a b → (signedGraph G).Walk a b
  | _, .nil => .nil
  | _, .concat w e h => .concat (forwardWalk w) (e,false) h

private theorem forwardWalk_length {V E : Type*} {G : EdgeGraph V E} {a b : V}
    (w : G.Walk a b) : (forwardWalk w).length = w.length := by
  induction w with
  | nil => rfl
  | concat w e h ih => simpa [forwardWalk] using congrArg Nat.succ ih

private theorem forwardWalk_edges {V E : Type*} {G : EdgeGraph V E} {a b : V}
    (w : G.Walk a b) : (forwardWalk w).edges = w.edges.map (fun e => (e,false)) := by
  induction w with
  | nil => rfl
  | concat w e h ih => simp [forwardWalk, ih]

private theorem exists_forward_projection {V E : Type*} {G : EdgeGraph V E} {a b : V}
    (w : (signedGraph G).Walk a b) (hw : ∀ e ∈ w.edges, e.2 = false) :
    ∃ q : G.Walk a b, forwardWalk q = w := by
  induction w with
  | nil => exact ⟨.nil, rfl⟩
  | concat w e h ih =>
    have he := hw e (by simp)
    have hold : ∀ e ∈ w.edges, e.2 = false := by
      intro d hd
      exact hw d (by simp [hd])
    rcases e with ⟨e,orientation⟩
    cases orientation with
    | true => exact Bool.noConfusion he
    | false =>
      obtain ⟨q,hq⟩ := ih hold
      exact ⟨q.concat e h, by simp only [forwardWalk, hq]⟩

private theorem forwardWalk_simple {V E : Type*} {G : EdgeGraph V E} {a : V}
    (w : G.Walk a a) (hw : IsSimpleCycle (forwardWalk w)) : IsSimpleCycle w := by
  refine ⟨by simpa only [forwardWalk_length] using hw.1, ?_⟩
  intro v before inner after he hi hout
  apply hw.2 v (forwardWalk before) (forwardWalk inner) (forwardWalk after)
  · simp only [forwardWalk_edges, he, List.map_append]
  · simpa only [forwardWalk_length] using hi
  · simpa only [forwardWalk_length] using hout

private theorem forwardWalk_multiplicity {V E : Type*} [DecidableEq E]
    {G : EdgeGraph V E} {a b : V} (w : G.Walk a b) (e : E) :
    (forwardWalk w).edgeMultiplicity (e,false) = w.edgeMultiplicity e ∧
    (forwardWalk w).edgeMultiplicity (e,true) = 0 := by
  induction w with
  | nil => simp [forwardWalk]
  | concat w d h ih =>
    simp only [forwardWalk, EdgeGraph.Walk.edgeMultiplicity, ih.1, ih.2,
      Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, and_false,
      and_true, if_false, add_zero]

theorem positive_coefficient_forward {V E ι : Type*}
    [Fintype E] [DecidableEq E] [Fintype ι]
    (G : EdgeGraph V E) (coefficient : SignedEdge E → ℝ)
    (weight : ι → ℝ) (base : ι → V)
    (cycle : ∀ i, (signedGraph G).Walk (base i) (base i))
    (hweight : ∀ i, 0 ≤ weight i) (hs : ∀ i, IsSimpleCycle (cycle i))
    (hc : ∀ e, coefficient e = ∑ i, weight i * circuitCoefficient (cycle i) e)
    (hz : ∀ e, coefficient (e,true) = 0) (i : ι) (hi : 0 < weight i) :
    ∀ e ∈ (cycle i).edges, e.2 = false := by
  intro ⟨e,orientation⟩ he
  cases orientation with
  | false => rfl
  | true =>
    have ht (j : ι) : 0 ≤ weight j * circuitCoefficient (cycle j) (e,true) :=
      mul_nonneg (hweight j) (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hle := Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ i)
    have hzero : (∑ j, weight j * circuitCoefficient (cycle j) (e,true)) = 0 :=
      (hc (e,true)).symm.trans (hz e)
    rw [hzero] at hle
    have hcount : 0 < (cycle i).edgeMultiplicity (e,true) :=
      ((cycle i).edgeMultiplicity_pos_iff_mem_edges _).mpr he
    have hnum : (0 : ℝ) < (cycle i).edgeMultiplicity (e,true) := by exact_mod_cast hcount
    have hlen : (0 : ℝ) < (cycle i).length := by exact_mod_cast (hs i).1
    exact (not_lt_of_ge hle (mul_pos hi (div_pos hnum hlen))).elim

private def lawCertificate {n : ℕ} (p : ZMod n → Fin 5 → ℝ) :
    SignedEdge (ZMod n × Fin 5) → ℝ
  | (e,false) => p e.1 e.2 / n
  | (_,true) => 0

private theorem law_certificate_normalized {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) :
    Maths.FiniteInequality.IsNormalizedCertificate
      (signedDelta (layeredGraph n)) (lawCertificate p) := by
  classical
  obtain ⟨hnonneg, hnorm, hbal⟩ := (local_law_iff p).mp hp
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  refine ⟨?_, ?_, ?_⟩
  · intro ⟨e,b⟩
    cases b
    · exact div_nonneg (hnonneg e.1 e.2) (Nat.cast_nonneg _)
    · exact le_rfl
  · simp only [Fintype.sum_prod_type, Fintype.sum_bool, lawCertificate, add_zero, zero_add]
    simp only [← Finset.sum_div, hnorm, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
    exact div_self hn
  · intro v
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, lawCertificate,
      zero_mul, add_zero, zero_add]
    have hinc :
        (∑ e : ZMod n × Fin 5, p e.1 e.2 * signedDelta (layeredGraph n) (e,false) v) = 0 := by
      simp only [signedDelta, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
      have hb := hbal v
      simp_rw [eq_comm] at hb
      exact sub_eq_zero.mpr hb.symm
    rw [Fintype.sum_prod_type] at hinc
    simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [hinc, zero_div]

theorem simple_cycle_winding {n : ℕ} [NeZero n] {a : ZMod n × Fin 3}
    (w : (layeredGraph n).Walk a a) (hw : IsSimpleCycle w) :
    1 ≤ layerCount w 0 ∧ layerCount w 0 ≤ 3 ∧ w.length = n * layerCount w 0 := by
  have hlen := length_eq_layer_count w
  have hshort := hw.length_le_card
  simp only [Fintype.card_prod, ZMod.card, Fintype.card_fin] at hshort
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hm : 0 < layerCount w 0 := by
    by_contra h
    have hz : layerCount w 0 = 0 := by omega
    have hh := hw.1
    rw [hlen, hz, mul_zero] at hh
    exact (Nat.lt_irrefl 0) hh
  refine ⟨hm, ?_, hlen⟩
  rw [hlen] at hshort
  exact Nat.le_of_mul_le_mul_left hshort hn

theorem local_simple_cycle_decomposition {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) :
    ∃ (ι : Type) (_ : Fintype ι) (weight : ι → ℝ) (base : ι → ZMod n × Fin 3)
      (cycle : ∀ i, (layeredGraph n).Walk (base i) (base i)),
      (∀ i, 0 ≤ weight i) ∧ (∑ i, weight i) = 1 ∧
      (∀ i, 0 < weight i → IsSimpleCycle (cycle i)) ∧
      (∀ i, 0 < weight i → 1 ≤ layerCount (cycle i) 0 ∧ layerCount (cycle i) 0 ≤ 3) ∧
      (∀ i, 0 < weight i → IsLocalLaw (walkLaw (cycle i))) ∧
      (∀ j σ, p j σ = ∑ i, weight i * walkLaw (cycle i) j σ) ∧
      ∀ i, weight i = layerCount (cycle i) 0 * (weight i / layerCount (cycle i) 0) := by
  classical
  obtain ⟨ι, inst, weight, base, signedCycle, hnonneg, hsum, hsimple, heq⟩ :=
    exists_simpleSignedCircuit_decomposition (layeredGraph n) (lawCertificate p)
      (law_certificate_normalized p hp)
  have hforward (i : ι) (hi : 0 < weight i) :
      ∀ e ∈ (signedCycle i).edges, e.2 = false :=
    positive_coefficient_forward (layeredGraph n) (lawCertificate p)
      weight base signedCycle hnonneg hsimple heq (fun _ => rfl) i hi
  let cycle : ∀ i, (layeredGraph n).Walk (base i) (base i) := fun i =>
    if hi : 0 < weight i then
      (exists_forward_projection (signedCycle i) (hforward i hi)).choose else .nil
  have hcycle (i : ι) (hi : 0 < weight i) : forwardWalk (cycle i) = signedCycle i := by
    simp only [cycle, dif_pos hi]
    exact (exists_forward_projection (signedCycle i) (hforward i hi)).choose_spec
  have hcSimple (i : ι) (hi : 0 < weight i) : IsSimpleCycle (cycle i) := by
    apply forwardWalk_simple
    rw [hcycle i hi]
    exact hsimple i
  have hm (i : ι) (hi : 0 < weight i) : 0 < layerCount (cycle i) 0 :=
    (simple_cycle_winding (cycle i) (hcSimple i hi)).1
  refine ⟨ι, inst, weight, base, cycle, hnonneg, hsum, hcSimple, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨(simple_cycle_winding (cycle i) (hcSimple i hi)).1,
      (simple_cycle_winding (cycle i) (hcSimple i hi)).2.1⟩
  · intro i hi
    exact walk_law_local (cycle i) (hcSimple i hi).1
  · intro j σ
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    have hh := heq ((j,σ),false)
    change p j σ / n = ∑ i, weight i * circuitCoefficient (signedCycle i) ((j,σ),false) at hh
    have hrec : p j σ =
        ∑ i, (n : ℝ) * (weight i * circuitCoefficient (signedCycle i) ((j,σ),false)) := by
      rw [← Finset.mul_sum, ← hh]
      field_simp
    rw [hrec]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < weight i
    · have hlen : (signedCycle i).length = n * layerCount (cycle i) 0 := by
        rw [← hcycle i hi, forwardWalk_length]
        exact length_eq_layer_count (cycle i)
      have hmul := (forwardWalk_multiplicity (cycle i) (j,σ)).1
      rw [hcycle i hi] at hmul
      simp only [circuitCoefficient, hmul, hlen, Nat.cast_mul, walkLaw]
      have hmi : (layerCount (cycle i) 0 : ℝ) ≠ 0 := by exact_mod_cast (hm i hi).ne'
      field_simp
    · have hz : weight i = 0 := le_antisymm (le_of_not_gt hi) (hnonneg i)
      simp only [hz, zero_mul, mul_zero]
  · intro i
    by_cases hi : 0 < weight i
    · have hmi : (layerCount (cycle i) 0 : ℝ) ≠ 0 := by exact_mod_cast (hm i hi).ne'
      field_simp
    · have hz : weight i = 0 := le_antisymm (le_of_not_gt hi) (hnonneg i)
      simp only [hz, zero_div, mul_zero]

private theorem circulation_layer_uniform {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) (hp : IsCirculation p) (i : ZMod n) :
    (∑ σ, p i σ) = ∑ σ, p 0 σ := by
  have hstep (j : ZMod n) : (∑ σ, p (j+1) σ) = ∑ σ, p j σ := by
    have h := (overlap_circulation_iff p).mpr hp
    have hs :
        (∑ s : Fin 3, ∑ σ, if sourceState σ=s then p (j+1) σ else 0) =
        ∑ s : Fin 3, ∑ σ, if targetState σ=s then p j σ else 0 :=
      Finset.sum_congr rfl (fun s _ => (h j s).symm)
    simpa [Fin.sum_univ_three,Fin.sum_univ_five,sourceState,targetState,
      add_assoc,add_comm,add_left_comm] using hs
  have hall (k : ℕ) : (∑ σ, p (k:ZMod n) σ) = ∑ σ, p 0 σ := by
    induction k with
    | zero => simp
    | succ k ih => simpa only [Nat.cast_add,Nat.cast_one] using (hstep k).trans ih
  simpa only [ZMod.natCast_zmod_val] using hall i.val

private theorem positive_support_cycle {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) (hnonneg : ∀ i σ, 0 ≤ p i σ)
    (hbal : IsCirculation p) (hne : p ≠ 0) :
    ∃ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a),
      IsSimpleCycle w ∧ ∀ e ∈ w.edges, 0 < p e.1 e.2 := by
  classical
  have hpos : ∃ i σ, 0 < p i σ := by
    by_contra h
    push Not at h
    apply hne
    funext i σ
    exact le_antisymm (h i σ) (hnonneg i σ)
  obtain ⟨i,σ,hpos⟩ := hpos
  let mass : ℝ := ∑ σ, p 0 σ
  have hm : 0 < mass := by
    have hl := Finset.single_le_sum (fun τ _ => hnonneg i τ) (Finset.mem_univ σ)
    rw [circulation_layer_uniform p hbal i] at hl
    exact hpos.trans_le hl
  let q : ZMod n → Fin 5 → ℝ := fun i σ => p i σ / mass
  have hq : IsLocalLaw q := by
    rw [local_law_iff]
    refine ⟨fun i σ => div_nonneg (hnonneg i σ) hm.le, ?_, ?_⟩
    · intro j
      simp only [q,← Finset.sum_div,circulation_layer_uniform p hbal j]
      exact div_self hm.ne'
    · intro v
      have hd (P : Prop) [Decidable P] (x : ℝ) :
          (if P then x/mass else 0) = (if P then x else 0)/mass := by split_ifs <;> simp
      simp only [q,hd,← Finset.sum_div]
      exact congrArg (fun x : ℝ => x/mass) (hbal v)
  obtain ⟨ι,inst,weight,base,cycle,hnw,hsw,hsimple,_,_,hrec,_⟩ :=
    local_simple_cycle_decomposition q hq
  have hex : ∃ k : ι, 0 < weight k := by
    by_contra h
    push Not at h
    have hz (k : ι) : weight k=0 := le_antisymm (h k) (hnw k)
    simp only [hz,Finset.sum_const_zero] at hsw
    norm_num at hsw
  obtain ⟨k,hk⟩ := hex
  refine ⟨base k,cycle k,hsimple k hk,?_⟩
  intro e he
  have hcount := ((cycle k).edgeMultiplicity_pos_iff_mem_edges e).mpr he
  have hcnt : (0:ℝ) < (cycle k).edgeMultiplicity e := by exact_mod_cast hcount
  have hturn : (0:ℝ) < layerCount (cycle k) 0 := by
    exact_mod_cast (simple_cycle_winding (cycle k) (hsimple k hk)).1
  have ht : 0 < weight k * walkLaw (cycle k) e.1 e.2 := mul_pos hk (div_pos hcnt hturn)
  have hle : weight k * walkLaw (cycle k) e.1 e.2 ≤ ∑ j, weight j * walkLaw (cycle j) e.1 e.2 :=
    Finset.single_le_sum (fun j _ => mul_nonneg (hnw j)
      (div_nonneg (Nat.cast_nonneg ((cycle j).edgeMultiplicity e))
        (Nat.cast_nonneg (layerCount (cycle j) 0)))) (Finset.mem_univ k)
  rw [← hrec e.1 e.2] at hle
  have hh : 0 < p e.1 e.2 / mass := ht.trans_le hle
  rcases div_pos_iff.mp hh with ⟨h,_⟩ | ⟨_,h⟩
  · exact h
  · exact (not_lt_of_ge hm.le h).elim

/-- The initial part of a cycle with no proper positive closed subwalk visits no vertex twice. -/
theorem cycle_initial_visited_nodup {V E : Type*} {G : EdgeGraph V E} {a : V}
    (edge : E) (initial : G.Walk (G.target edge) a) (legal : G.source edge = a)
    (hminimal : ∀ (v : V) (before : G.Walk (G.target edge) v)
      (inner : G.Walk v v) (after : G.Walk v (G.target edge)),
      (initial.concat edge legal).edges = before.edges ++ inner.edges ++ after.edges →
      0 < inner.length → 0 < before.length + after.length → False) :
    initial.visited.Nodup := by
  by_contra h
  obtain ⟨v, before, inner, after, hinner, hedges⟩ :=
    initial.exists_closedSubwalk_of_not_nodup h
  apply hminimal v before inner (after.concat edge legal)
  · simp only [EdgeGraph.Walk.edges_concat, hedges, List.append_assoc]
  · exact hinner
  · simp

private theorem simple_cycle_edges_nodup {V E : Type*} {G : EdgeGraph V E} {a : V}
    (w : G.Walk a a) (hw : IsSimpleCycle w) : w.edges.Nodup := by
  cases w with
  | nil => simp
  | concat initial edge legal =>
    have hinit := cycle_initial_visited_nodup edge initial legal hw.2
    have hnot : edge ∉ initial.edges := by
      intro hmem
      obtain ⟨before,after,hedges⟩ := initial.exists_splitAtEdge edge hmem
      let single := EdgeGraph.Walk.singleton (G:=G) edge
      apply hw.2 (G.source edge) before (single.append (after.castFinish legal.symm)) single
      · simp only [single,EdgeGraph.Walk.singleton,EdgeGraph.Walk.edges_concat,hedges,EdgeGraph.Walk.edges_append,
          EdgeGraph.Walk.edges_castFinish,EdgeGraph.Walk.edges]
        simp only [List.append_assoc,List.singleton_append,List.cons_append,List.nil_append]
      · simp [single,EdgeGraph.Walk.singleton]
      · simp [single,EdgeGraph.Walk.singleton]
    simp only [EdgeGraph.Walk.edges_concat,List.nodup_append]
    refine ⟨initial.edges_nodup_of_visited_nodup hinit,List.nodup_singleton _,?_⟩
    intro e he d hd
    have hh : d=edge := List.mem_singleton.mp hd
    subst d
    intro h
    subst e
    exact hnot he

def positiveSupport {n : ℕ} [NeZero n] (p : ZMod n → Fin 5 → ℝ) : Finset (ZMod n × Fin 5) :=
  Finset.univ.filter (fun e => 0 < p e.1 e.2)

def subtractCycle {n : ℕ} {a : ZMod n × Fin 3}
    (p : ZMod n → Fin 5 → ℝ) (w : (layeredGraph n).Walk a a) (α : ℝ) :
    ZMod n → Fin 5 → ℝ := fun i σ => p i σ - α * w.edgeMultiplicity (i,σ)

theorem positive_cycle_erasure {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) (hnonneg : ∀ i σ, 0 ≤ p i σ)
    (hbal : IsCirculation p) (hne : p ≠ 0) :
    ∃ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a) (α : ℝ),
      IsSimpleCycle w ∧ 0 < α ∧
      (∀ e ∈ w.edges, α ≤ p e.1 e.2) ∧
      (∃ e ∈ w.edges, p e.1 e.2=α) ∧
      (∀ i σ, 0 ≤ subtractCycle p w α i σ) ∧
      IsCirculation (subtractCycle p w α) ∧
      (positiveSupport (subtractCycle p w α)).card < (positiveSupport p).card ∧
      ∀ e, (w.edgeMultiplicity e : ℝ) = if e ∈ w.edges then 1 else 0 := by
  classical
  obtain ⟨a,w,hsimple,hpositive⟩ := positive_support_cycle p hnonneg hbal hne
  have hnd := simple_cycle_edges_nodup w hsimple
  have hneEdges : w.edges ≠ [] := by
    rw [← List.length_pos_iff,w.edges_length]
    exact hsimple.1
  let values := w.edges.toFinset.image (fun e => p e.1 e.2)
  have hv : values.Nonempty := (by simpa only [List.toFinset_nonempty_iff] using hneEdges : w.edges.toFinset.Nonempty).image _
  let α := values.min' hv
  have hαmem := Finset.min'_mem values hv
  obtain ⟨critical,hcritical,hcrit⟩ := Finset.mem_image.mp hαmem
  have hcriticalEdges : critical ∈ w.edges := List.mem_toFinset.mp hcritical
  have hαpos : 0 < α := by
    change 0 < values.min' hv
    rw [← hcrit]
    exact hpositive critical hcriticalEdges
  have hαle (e : ZMod n × Fin 5) (he : e ∈ w.edges) : α ≤ p e.1 e.2 :=
    Finset.min'_le values _ (Finset.mem_image.mpr ⟨e,List.mem_toFinset.mpr he,rfl⟩)
  have hind (e : ZMod n × Fin 5) : (w.edgeMultiplicity e : ℝ) = if e ∈ w.edges then 1 else 0 := by
    by_cases he : e ∈ w.edges
    · rw [if_pos he,(w.edgeMultiplicity_eq_one_iff_mem_edges hnd e).mpr he,Nat.cast_one]
    · have hz : w.edgeMultiplicity e=0 := by
        apply Nat.eq_zero_of_not_pos
        simpa only [w.edgeMultiplicity_pos_iff_mem_edges] using he
      rw [if_neg he,hz,Nat.cast_zero]
  have hr (i : ZMod n) (σ : Fin 5) : 0 ≤ subtractCycle p w α i σ := by
    unfold subtractCycle
    rw [hind]
    by_cases he : (i,σ) ∈ w.edges
    · rw [if_pos he,mul_one]
      exact sub_nonneg.mpr (hαle _ he)
    · rw [if_neg he,mul_zero,sub_zero]
      exact hnonneg i σ
  have hcir : IsCirculation (subtractCycle p w α) := by
    intro v
    have hc := w.edgeMultiplicity_balanced v
    have hcr :
        (∑ e, if (layeredGraph n).source e=v then (w.edgeMultiplicity e:ℝ) else 0) =
        ∑ e, if (layeredGraph n).target e=v then (w.edgeMultiplicity e:ℝ) else 0 := by
      simp only [EdgeGraph.outgoingMultiplicity,EdgeGraph.incomingMultiplicity,Finset.sum_filter] at hc
      exact_mod_cast hc
    have hd (P : Prop) [Decidable P] (x y : ℝ) :
        (if P then x-α*y else 0) = (if P then x else 0)-α*(if P then y else 0) := by
      split_ifs <;> ring
    simp only [subtractCycle,hd,Finset.sum_sub_distrib,← Finset.mul_sum]
    rw [hbal v,hcr]
  have hz : subtractCycle p w α critical.1 critical.2=0 := by
    unfold subtractCycle
    rw [hind,if_pos hcriticalEdges,mul_one,hcrit,sub_self]
  have hsub : positiveSupport (subtractCycle p w α) ⊆ positiveSupport p := by
    intro e he
    simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and] at he ⊢
    dsimp [subtractCycle] at he
    have hc : 0 ≤ α * (w.edgeMultiplicity e : ℝ) := mul_nonneg hαpos.le (Nat.cast_nonneg _)
    linarith
  have hstrict : positiveSupport (subtractCycle p w α) ⊂ positiveSupport p := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub,?_⟩
    intro heq
    have hc : critical ∈ positiveSupport p := by simp [positiveSupport,hpositive critical hcriticalEdges]
    rw [← heq] at hc
    simp only [positiveSupport,Finset.mem_filter,Finset.mem_univ,true_and,hz,lt_self_iff_false] at hc
  refine ⟨a,w,α,hsimple,hαpos,hαle,⟨critical,hcriticalEdges,hcrit⟩,hr,hcir,
    Finset.card_lt_card hstrict,hind⟩

/-- Every component has positive real amplitude; its probability weight is its
winding number times that amplitude. -/
def HasPositiveCycleDecomposition {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (base : ι → ZMod n × Fin 3)
    (cycle : ∀ i, (layeredGraph n).Walk (base i) (base i)) (α : ι → ℝ),
    (∀ i, IsSimpleCycle (cycle i) ∧ 0 < α i ∧
      1 ≤ layerCount (cycle i) 0 ∧ layerCount (cycle i) 0 ≤ 3 ∧
      IsLocalLaw (walkLaw (cycle i)) ∧
      (cycle i).length=layerCount (cycle i) 0 * n ∧
      (∀ j, layerCount (cycle i) j=layerCount (cycle i) 0) ∧
      ∀ e, ((cycle i).edgeMultiplicity e : ℝ) = if e ∈ (cycle i).edges then 1 else 0) ∧
    (∑ i, (layerCount (cycle i) 0 : ℝ) * α i) = 1 ∧
    (∀ j σ, p j σ = ∑ i, α i * (if (j,σ) ∈ (cycle i).edges then 1 else 0)) ∧
    ∀ j σ, p j σ = ∑ i, ((layerCount (cycle i) 0 : ℝ) * α i) * walkLaw (cycle i) j σ

theorem positive_cycle_decomposition {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) (hp : IsLocalLaw p) : HasPositiveCycleDecomposition p := by
  classical
  obtain ⟨ι,inst,weight,base,cycle,hnw,hsw,hsimple,hturn,hlaw,hrec,hweight⟩ :=
    local_simple_cycle_decomposition p hp
  let J := {i : ι // 0 < weight i}
  let amplitude (i : J) : ℝ := weight i.val / layerCount (cycle i.val) 0
  have hm (i : J) : (0:ℝ) < layerCount (cycle i.val) 0 := by
    exact_mod_cast (hturn i.val i.property).1
  have hw (i : J) : (layerCount (cycle i.val) 0 : ℝ) * amplitude i = weight i.val := by
    exact (hweight i.val).symm
  have hs (g : ι → ℝ) (hg : ∀ i, ¬0 < weight i → g i=0) :
      (∑ i, g i) = ∑ i : J, g i.val := by
    exact Finset.sum_congr_set {i | 0 < weight i} g (fun i : J => g i.val)
      (fun _ _ => rfl) hg
  have hind (i : J) (e : ZMod n × Fin 5) :
      ((cycle i.val).edgeMultiplicity e : ℝ) = if e ∈ (cycle i.val).edges then 1 else 0 := by
    have hnd := simple_cycle_edges_nodup (cycle i.val) (hsimple i.val i.property)
    by_cases he : e ∈ (cycle i.val).edges
    · rw [if_pos he,((cycle i.val).edgeMultiplicity_eq_one_iff_mem_edges hnd e).mpr he,Nat.cast_one]
    · have hz : (cycle i.val).edgeMultiplicity e=0 := by
        apply Nat.eq_zero_of_not_pos
        simpa only [(cycle i.val).edgeMultiplicity_pos_iff_mem_edges] using he
      rw [if_neg he,hz,Nat.cast_zero]
  refine ⟨J,inferInstance,(fun i => base i.val),(fun i => cycle i.val),amplitude,?_,?_,?_,?_⟩
  · intro i
    exact ⟨hsimple i.val i.property,div_pos i.property (hm i),
      (hturn i.val i.property).1,(hturn i.val i.property).2,hlaw i.val i.property,
      by rw [length_eq_layer_count,Nat.mul_comm],layer_count_uniform (cycle i.val),hind i⟩
  · simp_rw [hw]
    rw [← hs weight (fun i hi => le_antisymm (le_of_not_gt hi) (hnw i))]
    exact hsw
  · intro j σ
    rw [hrec,hs (fun i => weight i * walkLaw (cycle i) j σ) (by
      intro i hi
      have hz : weight i=0 := le_antisymm (le_of_not_gt hi) (hnw i)
      rw [hz,zero_mul])]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hind i (j,σ)]
    dsimp [walkLaw,amplitude]
    ring
  · intro j σ
    simp_rw [hw]
    rw [← hs (fun i => weight i * walkLaw (cycle i) j σ) (by
      intro i hi
      have hz : weight i=0 := le_antisymm (le_of_not_gt hi) (hnw i)
      rw [hz,zero_mul])]
    exact hrec j σ

/-- The positive residual certificate records the actual minimum edge erasure,
conservation, and strict decrease of finite positive support. -/
def HasPositiveCycleErasure {n : ℕ} [NeZero n]
    (p : ZMod n → Fin 5 → ℝ) : Prop :=
  ∃ (a : ZMod n × Fin 3) (w : (layeredGraph n).Walk a a) (α : ℝ),
    IsSimpleCycle w ∧ 0 < α ∧
    (∀ e ∈ w.edges, α ≤ p e.1 e.2) ∧
    (∃ e ∈ w.edges, p e.1 e.2=α) ∧
    (∀ i σ, 0 ≤ subtractCycle p w α i σ) ∧
    IsCirculation (subtractCycle p w α) ∧
    (positiveSupport (subtractCycle p w α)).card < (positiveSupport p).card ∧
    ∀ e, (w.edgeMultiplicity e : ℝ) = if e ∈ w.edges then 1 else 0


private theorem local_law_closed {n : ℕ} [NeZero n] :
    IsClosed {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p} := by
  have heval (i : ZMod n) (σ : Fin 5) :
      Continuous (fun p : ZMod n → Fin 5 → ℝ => p i σ) :=
    (continuous_apply σ).comp (continuous_apply i)
  have hs (v : ZMod n × Fin 3) : Continuous
      (fun p : ZMod n → Fin 5 → ℝ =>
        ∑ e, if (layeredGraph n).source e=v then p e.1 e.2 else 0) := by
    apply continuous_finset_sum
    intro e _
    split_ifs
    · exact heval e.1 e.2
    · exact continuous_const
  have ht (v : ZMod n × Fin 3) : Continuous
      (fun p : ZMod n → Fin 5 → ℝ =>
        ∑ e, if (layeredGraph n).target e=v then p e.1 e.2 else 0) := by
    apply continuous_finset_sum
    intro e _
    split_ifs
    · exact heval e.1 e.2
    · exact continuous_const
  have hset : {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p} =
      {p | ∀ i σ, 0 ≤ p i σ} ∩
        ({p | ∀ i, ∑ σ, p i σ=1} ∩ {p | IsCirculation p}) := by
    ext p
    exact local_law_iff p
  rw [hset]
  apply IsClosed.inter
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun σ => isClosed_le continuous_const (heval i σ)
  · apply IsClosed.inter
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun i => isClosed_eq (continuous_finset_sum _ (fun σ _ => heval i σ))
        continuous_const
    · unfold IsCirculation
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun v => isClosed_eq (hs v) (ht v)

/-- Complete-overlap laws form a compact subset of the actual real coordinate cube. -/
theorem local_law_compact {n : ℕ} [NeZero n] :
    IsCompact {p : ZMod n → Fin 5 → ℝ | IsLocalLaw p} := by
  have hbox : IsCompact {p : ZMod n → Fin 5 → ℝ | ∀ i σ, p i σ ∈ Set.Icc (0:ℝ) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_pi_infinite (fun _ => isCompact_Icc))
  apply hbox.of_isClosed_subset local_law_closed
  intro p hp i σ
  refine ⟨hp.1 i σ,?_⟩
  have hh := Finset.single_le_sum (fun τ _ => hp.1 i τ) (Finset.mem_univ σ)
  rwa [hp.2.1 i] at hh

end
end D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum
