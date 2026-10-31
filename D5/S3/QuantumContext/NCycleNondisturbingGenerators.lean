/- GID: D5/S3/QuantumContext/NCycleNondisturbingGenerators
   generality: I
   mirror-B: D5/B/S3/QuantumContext/NCycleNondisturbingGenerators
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Binary cyclic nondisturbing laws are mixtures of deterministic and parity laws. -/

import D5.S3.Combinatorics.Graph.LayeredCirculation.LayeredFlow
import D5.S3.Estimation.DecisionRisk.DescentDefectBounds
import D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence
import D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation

/-! The normalized circulation supplier applied to the two-outcome layered cycle graph. -/

set_option autoImplicit false

noncomputable section

open Finset Maths Maths.AdditiveTransport
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds (deterministicPostprocess)

namespace D5.S3.QuantumContext.NCycleNondisturbingGenerators

private def graph (n : ℕ) : EdgeGraph (Fin n × Bool) (Fin n × Bool × Bool) :=
  { source := fun e => (e.1, e.2.1)
    target := fun e => (finRotate n e.1, e.2.2) }

/-- Union of deterministic cycle laws and parity laws with mass 1/2 when `b xor c = γ i`. -/
def allGenerators (n : ℕ) : Set (Fin n → Bool → Bool → ℝ) :=
  Set.range (fun s : Fin n → Bool => fun i b c =>
    deterministicPostprocess (fun j => (s j, s (finRotate n j))) i (b, c)) ∪
  Set.range (fun γ : Fin n → Bool => fun i b c =>
    D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation.parityBox
      (fun _ _ => γ i) 0 0 b c)

private lemma departures_visited {v e : Type} [Fintype e] [DecidableEq e] [DecidableEq v]
    {g : EdgeGraph v e} {a b : v} (w : g.Walk a b) (u : v) :
    g.outgoingMultiplicity w.edgeMultiplicity u + (if b = u then 1 else 0) =
      w.visited.count u := by
  induction w with
  | nil =>
    change (∑ edge with g.source edge = u, 0) + (if a = u then 1 else 0) = [a].count u
    simp [List.count_singleton, beq_iff_eq]
  | @concat b w e he ih =>
    rw [EdgeGraph.Walk.outgoingMultiplicity_edgeMultiplicity_concat]
    change (g.outgoingMultiplicity w.edgeMultiplicity u + (if g.source e = u then 1 else 0)) +
      (if g.target e = u then 1 else 0) = (w.visited ++ [g.target e]).count u
    conv_rhs => simp only [List.count_append, List.count_singleton, beq_iff_eq]
    rw [he]
    omega

private lemma simple_departures_le_one {v e : Type} [Fintype e] [DecidableEq e]
    [DecidableEq v] {g : EdgeGraph v e} {a : v} (w : g.Walk a a)
    (hw : IsSimpleCycle w) (u : v) : g.outgoingMultiplicity w.edgeMultiplicity u ≤ 1 := by
  cases w with
  | nil => exact (Nat.not_lt_zero _ hw.1).elim
  | concat initial edge legal =>
    have hinit :=
      D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum.cycle_initial_visited_nodup
        edge initial legal hw.2
    have hi := departures_visited initial u
    have hcount : initial.visited.count u ≤ 1 := (List.nodup_iff_count_le_one.mp hinit) u
    rw [EdgeGraph.Walk.outgoingMultiplicity_edgeMultiplicity_concat, legal]
    exact hi.le.trans hcount

private lemma circuit_generator {n : ℕ} (hn : 0 < n) {a : Fin n × Bool}
    (w : (signedGraph (graph n)).Walk a a) (hw : IsSimpleCycle w)
    (hz : ∀ e : Fin n × Bool × Bool, w.edgeMultiplicity (e, true) = 0) :
    (fun i b c => (n : ℝ) * circuitCoefficient w ((i, b, c), false)) ∈ allGenerators n := by
  cases n with
  | zero => omega
  | succ k =>
    let count : Fin (k + 1) → Bool → Bool → ℕ := fun i b c =>
      w.edgeMultiplicity ((i, b, c), false)
    let mass : Fin (k + 1) → ℕ := fun i => ∑ b, ∑ c, count i b c
    have hzero (i : Fin (k + 1)) (b c : Bool) :
        w.edgeMultiplicity ((i, b, c), true) = 0 := hz (i, b, c)
    have hout (i : Fin (k + 1)) (b : Bool) :
        (signedGraph (graph (k + 1))).outgoingMultiplicity w.edgeMultiplicity (i, b) =
          ∑ c, count i b c := by
      change (∑ e with (signedGraph (graph (k + 1))).source e = (i, b),
        w.edgeMultiplicity e) = ∑ c, count i b c
      simp only [sum_filter, Fintype.sum_prod_type,
        Fintype.sum_bool, hzero, ite_self, zero_add]
      dsimp only [signedGraph, graph]
      cases b <;> simp [Prod.mk.injEq, ite_and, count, sum_add_distrib] <;> rfl
    have hin (i : Fin (k + 1)) (c : Bool) :
        (signedGraph (graph (k + 1))).incomingMultiplicity w.edgeMultiplicity
          (finRotate (k + 1) i, c) = ∑ b, count i b c := by
      simp only [EdgeGraph.incomingMultiplicity, sum_filter, Fintype.sum_prod_type,
        Fintype.sum_bool, hzero, ite_self, zero_add]
      dsimp only [signedGraph, graph]
      cases c <;> simp [Prod.mk.injEq, ite_and, count, sum_add_distrib] <;> rfl
    have hrow (i : Fin (k + 1)) (b : Bool) : (∑ c, count i b c) ≤ 1 := by
      rw [← hout]
      exact simple_departures_le_one w hw (i, b)
    have hbalance (i : Fin (k + 1)) (c : Bool) :
        (∑ d, count (finRotate (k + 1) i) c d) = ∑ b, count i b c := by
      have h := w.edgeMultiplicity_balanced (finRotate (k + 1) i, c)
      rwa [hout, hin] at h
    have hstep (i : Fin (k + 1)) : mass (finRotate (k + 1) i) = mass i := by
      have h₀ := hbalance i false
      have h₁ := hbalance i true
      simp only [mass, Fintype.sum_bool] at h₀ h₁ ⊢
      omega
    have hmass (i : Fin (k + 1)) : mass i = mass 0 := by
      exact D5.S3.Combinatorics.Circle.Orbit.ZeroIncidence.all_equal_of_adjacent
        (Nat.succ_pos k) mass (fun i => (hstep i).symm) i
    have hlength : w.length = (k + 1) * mass 0 := by
      have h := sum_edgeMultiplicity_eq_length w
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, hz, zero_add] at h
      change (∑ i, mass i) = w.length at h
      simp_rw [hmass] at h
      simpa only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] using h.symm
    have hupper : mass 0 ≤ 2 := by
      have h := hw.length_le_card
      rw [hlength] at h
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at h
      exact le_of_mul_le_mul_left h (Nat.succ_pos k)
    have hpositive : 0 < mass 0 := by
      have hp := hw.1
      rw [hlength] at hp
      exact Nat.pos_of_mul_pos_left hp
    have hnreal : (k : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero k
    have hcases : mass 0 = 1 ∨ mass 0 = 2 := by
      simpa only [hpositive.ne', false_or] using (Order.le_two_iff.mp hupper)
    rcases hcases with hm | hm
    · let s : Fin (k + 1) → Bool := fun i => decide ((∑ c, count i true c) = 1)
      have hrows (i : Fin (k + 1)) (b : Bool) :
          (∑ c, count i b c) = if s i = b then 1 else 0 := by
        have hi : (∑ c, count i true c) + (∑ c, count i false c) = 1 := by
          simpa only [mass, Fintype.sum_bool] using (hmass i).trans hm
        cases b <;> by_cases he : (∑ c, count i true c) = 1 <;>
          simp only [s, he, decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false,
            ite_true, ite_false] <;> omega
      have htable (m : Bool → Bool → ℕ) (u v : Bool)
          (hr : ∀ b, (∑ c, m b c) = if u = b then 1 else 0)
          (hc : ∀ c, (∑ b, m b c) = if v = c then 1 else 0) :
          ∀ b c, m b c = if u = b ∧ v = c then 1 else 0 := by
        let f : Bool → Bool → ℝ := fun b c => m b c
        let g : Bool → Bool → ℝ := fun b c => if u = b ∧ v = c then 1 else 0
        have hfrow (b : Bool) : (∑ c, f b c) = if u = b then 1 else 0 := by
          dsimp only [f]
          rw [← Nat.cast_sum, hr b]
          split_ifs <;> norm_num
        have hfcol (c : Bool) : (∑ b, f b c) = if v = c then 1 else 0 := by
          dsimp only [f]
          rw [← Nat.cast_sum, hc c]
          split_ifs <;> norm_num
        have hgrow (b : Bool) : (∑ c, g b c) = if u = b then 1 else 0 := by
          by_cases h : u = b <;> simp [g, h]
        have hgcol (c : Bool) : (∑ b, g b c) = if v = c then 1 else 0 := by
          by_cases h : v = c <;> simp [g, h]
        have hzero : m (!u) (!v) = 0 := by
          have hz : (∑ c, m (!u) c) = 0 := by simpa using hr (!u)
          exact sum_eq_zero_iff.mp hz (!v) (mem_univ _)
        have heq := D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation.binary_eq f g (!u) (!v)
          (by simp_rw [hfrow, hgrow])
          (by rw [hfrow, hgrow]) (by rw [hfcol, hgcol])
          (by simp [f, g, hzero])
        intro b c
        have h := congrFun (congrFun heq b) c
        dsimp only [f, g] at h
        split_ifs at h ⊢ <;> exact_mod_cast h
      have hcounts (i : Fin (k + 1)) (b c : Bool) :
          count i b c = if s i = b ∧ s (finRotate (k + 1) i) = c then 1 else 0 :=
        htable (count i) (s i) (s (finRotate (k + 1) i)) (hrows i)
          (fun c => (hbalance i c).symm.trans (hrows _ c)) b c
      refine Or.inl ⟨s, ?_⟩
      ext i b c
      simp only [deterministicPostprocess, Prod.mk.injEq]
      change (if s i = b ∧ s (finRotate (k + 1) i) = c then (1 : ℝ) else 0) =
        (k + 1 : ℕ) * ((count i b c : ℝ) / (w.length : ℝ))
      rw [hlength, hm, mul_one, hcounts]
      split_ifs <;> simp [hnreal]
    · have hrows (i : Fin (k + 1)) (b : Bool) : (∑ c, count i b c) = 1 := by
        have hi : (∑ c, count i true c) + (∑ c, count i false c) = 2 := by
          simpa only [mass, Fintype.sum_bool] using (hmass i).trans hm
        have h₀ := hrow i false
        have h₁ := hrow i true
        cases b <;> omega
      let γ : Fin (k + 1) → Bool := fun i => decide (count i false true = 1)
      have htable (m : Bool → Bool → ℕ)
          (hr : ∀ b, (∑ c, m b c) = 1) (hc : ∀ c, (∑ b, m b c) = 1) :
          ∀ b c, m b c = if Bool.xor b c = decide (m false true = 1) then 1 else 0 := by
        let f : Bool → Bool → ℝ := fun b c => m b c
        let g : Bool → Bool → ℝ := fun b c =>
          if Bool.xor b c = decide (m false true = 1) then 1 else 0
        have hfrow (b : Bool) : (∑ c, f b c) = 1 := by
          dsimp only [f]
          rw [← Nat.cast_sum, hr b]
          norm_num
        have hfcol (c : Bool) : (∑ b, f b c) = 1 := by
          dsimp only [f]
          rw [← Nat.cast_sum, hc c]
          norm_num
        have hgrow (b : Bool) : (∑ c, g b c) = 1 := by
          cases h : decide (m false true = 1) <;> cases b <;> norm_num [g, h, Fintype.sum_bool]
        have hgcol (c : Bool) : (∑ b, g b c) = 1 := by
          cases h : decide (m false true = 1) <;> cases c <;> norm_num [g, h, Fintype.sum_bool]
        have hcorner : f false true = g false true := by
          by_cases he : m false true = 1
          · simp [f, g, he]
          · have hz : m false true = 0 := by
              have h := hr false
              simp only [Fintype.sum_bool] at h
              omega
            simp [f, g, hz]
        have heq := D5.S3.Quantum.Entanglement.BinaryDetectionThresholdRefutation.binary_eq f g false true
          (by simp_rw [hfrow, hgrow]) (by rw [hfrow, hgrow]) (by rw [hfcol, hgcol]) hcorner
        intro b c
        have h := congrFun (congrFun heq b) c
        dsimp only [f, g] at h
        split_ifs at h ⊢ <;> exact_mod_cast h
      have hcounts (i : Fin (k + 1)) (b c : Bool) :
          count i b c = if Bool.xor b c = γ i then 1 else 0 :=
        htable (count i) (hrows i) (fun c => (hbalance i c).symm.trans (hrows _ c)) b c
      refine Or.inr ⟨γ, ?_⟩
      ext i b c
      change (if Bool.xor b c = γ i then (1 / 2 : ℝ) else 0) =
        (k + 1 : ℕ) * ((count i b c : ℝ) / (w.length : ℝ))
      rw [hlength, hm, hcounts]
      split_ifs <;> simp [Nat.cast_mul, hnreal]
      field_simp


/-- Circulation decomposition for binary cyclic probability tables. -/
theorem decomposition (n : ℕ) (hn : 0 < n) (r : Fin n → Bool → Bool → ℝ)
    (hr₀ : ∀ i b c, 0 ≤ r i b c) (hr₁ : ∀ i, ∑ b, ∑ c, r i b c = 1)
    (hr₂ : ∀ i c, ∑ b, r i b c = ∑ d, r (finRotate n i) c d) :
    r ∈ convexHull ℝ (allGenerators n) := by
  classical
  have hnreal : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  let coefficient : SignedEdge (Fin n × Bool × Bool) → ℝ := fun e =>
    if e.2 then 0 else r e.1.1 e.1.2.1 e.1.2.2 / n
  have hcertificate : Maths.FiniteInequality.IsNormalizedCertificate
      (signedDelta (graph n)) coefficient := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨⟨i, b, c⟩, d⟩
      cases d
      · exact div_nonneg (hr₀ i b c) (Nat.cast_nonneg _)
      · exact le_rfl
    · rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, coefficient, Bool.false_eq_true, ite_false, ite_true, zero_add]
      rw [← sum_div]
      simp only [Fintype.sum_prod_type, hr₁, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      exact div_self hnreal
    · rintro ⟨j, c⟩
      obtain ⟨i, rfl⟩ := (finRotate n).surjective j
      have hin : (∑ e : Fin n × Bool × Bool,
          if (finRotate n i, c) = (graph n).target e then r e.1 e.2.1 e.2.2 else 0) =
          ∑ b, r i b c := by
        dsimp only [graph]
        simp [Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
      have hout : (∑ e : Fin n × Bool × Bool,
          if (finRotate n i, c) = (graph n).source e then r e.1 e.2.1 e.2.2 else 0) =
          ∑ d, r (finRotate n i) c d := by
        dsimp only [graph]
        simp [Fintype.sum_prod_type, Prod.mk.injEq, ite_and]
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, coefficient, Bool.false_eq_true, ite_false, ite_true,
        zero_mul, zero_add]
      change (∑ e : Fin n × Bool × Bool, r e.1 e.2.1 e.2.2 / (n : ℝ) *
        ((if (finRotate n i, c) = (graph n).target e then 1 else 0) -
          (if (finRotate n i, c) = (graph n).source e then 1 else 0))) = 0
      have hinc : (∑ e : Fin n × Bool × Bool, r e.1 e.2.1 e.2.2 *
          ((if (finRotate n i, c) = (graph n).target e then 1 else 0) -
            (if (finRotate n i, c) = (graph n).source e then 1 else 0))) = 0 := by
        simp only [mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib]
        rw [hin, hout, hr₂ i c]
        exact sub_self _
      simp only [div_mul_eq_mul_div, ← sum_div, hinc, zero_div]
  obtain ⟨ι, inst, weight, base, cycle, hweight, hsum, hsimple, hrep⟩ :=
    exists_simpleSignedCircuit_decomposition (graph n) coefficient hcertificate
  let q : ι → Fin n → Bool → Bool → ℝ := fun j =>
    if 0 < weight j then
      fun i b c => (n : ℝ) * circuitCoefficient (cycle j) ((i, b, c), false)
    else fun _ b c => if false = b ∧ false = c then 1 else 0
  have hq (j : ι) : q j ∈ allGenerators n := by
    by_cases hj : 0 < weight j
    · have hz (e : Fin n × Bool × Bool) : (cycle j).edgeMultiplicity (e, true) = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro he
        have hforward :=
          D5.S3.Combinatorics.Graph.LayeredCirculation.LocalOptimum.positive_coefficient_forward
            (graph n) coefficient weight base cycle hweight hsimple hrep (fun _ => rfl) j hj
            (e, true) (((cycle j).edgeMultiplicity_pos_iff_mem_edges _).mp he)
        exact Bool.noConfusion hforward
      simpa only [q, if_pos hj] using circuit_generator hn (cycle j) (hsimple j) hz
    · change (if 0 < weight j then _ else _) ∈ _
      rw [if_neg hj]
      exact Or.inl ⟨fun _ => false, by
        simp only [deterministicPostprocess, Prod.mk.injEq]⟩
  apply mem_convexHull_of_exists_fintype weight q hweight hsum hq
  ext i b c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hterm (j : ι) : weight j * q j i b c =
      weight j * ((n : ℝ) * circuitCoefficient (cycle j) ((i, b, c), false)) := by
    by_cases hj : 0 < weight j
    · simp only [q, if_pos hj]
    · have hz : weight j = 0 := le_antisymm (le_of_not_gt hj) (hweight j)
      simp only [hz, zero_mul]
  calc
    (∑ j, weight j * q j i b c) =
      ∑ j, weight j * ((n : ℝ) * circuitCoefficient (cycle j) ((i, b, c), false)) :=
        sum_congr rfl fun j _ => hterm j
    _ = (n : ℝ) * ∑ j, weight j * circuitCoefficient (cycle j) ((i, b, c), false) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = (n : ℝ) * (r i b c / n) := by rw [← hrep]; rfl
    _ = r i b c := mul_div_cancel₀ _ hnreal


end D5.S3.QuantumContext.NCycleNondisturbingGenerators
