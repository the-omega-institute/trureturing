/- GID: D5/S3/Combinatorics/Probability/CommonReservoir
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/CommonReservoir
   mirror-E: none(waiver:symbolic-graph-probability-estimate)
   anchors: []
   utility: none
   digest: Five simultaneous reservoir events on the actual common tagged product space. -/

import D5.S3.Combinatorics.Probability.CommonReservoirGraph

/-! Five simultaneous graph reservoir events and the actual literal palette. -/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

namespace D5.S3.Combinatorics.Probability.CommonReservoir

open D5.S3.Combinatorics.Graph.Rainbow.TwoEdgeChoices
open TripleReservoir CommonReservoirRows CommonReservoirGraph

variable {V C : Type*} [Fintype V] [Fintype C]

def CommonEvent (G : Digraph V) (c : V → V → C) (p ν : ℝ)
    (L : V → Fin (Fintype.card V) → Finset V) (ω : (V ⊕ C) → Bool) : Prop :=
  let t := p ^ 3 * ν * Fintype.card V
  SizeEvent p ω ∧ DegreeEvent G c p ω ∧
    BaseEvent G c ν (3 * t / 100 + 5 / ν) ω ∧
    RankEvent G c ν (t / 50 + 20 / ν) L ω ∧
    IncomingEvent G c (t / 50 + 20 / ν) ω

private theorem forall_failure {Ω I : Type*} [Fintype I] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Q : I → Ω → Prop) (b : ℝ)
    (h : ∀ i, P.real {ω | ¬Q i ω} ≤ b) :
    P.real {ω | ¬∀ i, Q i ω} ≤ Fintype.card I * b := by
  classical
  have heq : {ω | ¬∀ i, Q i ω} = ⋃ i, {ω | ¬Q i ω} := by ext ω; simp
  rw [heq]
  exact (measureReal_iUnion_fintype_le _).trans
    ((sum_le_sum fun i _ => h i).trans_eq (by simp))

private theorem parameters (p ν α n : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hν : 0 < ν) (hν1 : ν < 1 / 2) (hα : ν ≤ α) (hn : 0 < n)
    (hlog : 3 < Real.log n) (hscale : 144 * Real.log n ≤ p ^ 3 * ν ^ 2 * n) :
    let t := p ^ 3 * ν * n
    288 * Real.log n ≤ t ∧
    3 * t / 100 + 5 / ν < 3 * t / 64 ∧
    t / 50 + 20 / ν < t / 8 ∧
    t ≤ p ^ 2 * ν * n ∧ t ≤ p ^ 2 * α * n ∧
    144 * Real.log n ≤ p * n ∧ 144 * Real.log n ≤ p * α * n := by
  dsimp only
  let t := p ^ 3 * ν * n
  have ht : 0 < t := by dsimp [t]; positivity
  have hνt : 144 * Real.log n ≤ ν * t := by dsimp [t]; nlinarith [hscale]
  have hνt' : 432 < ν * t := by linarith
  have htlog : 288 * Real.log n ≤ t := by nlinarith
  have hbase : 3 * t / 100 + 5 / ν < 3 * t / 64 := by
    apply (mul_lt_mul_iff_of_pos_right hν).mp
    field_simp
    nlinarith
  have hrank : t / 50 + 20 / ν < t / 8 := by
    apply (mul_lt_mul_iff_of_pos_right hν).mp
    field_simp
    nlinarith
  have hp32 : p ^ 3 ≤ p ^ 2 := by nlinarith [sq_nonneg p, mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hp1)]
  have h1 : t ≤ p ^ 2 * ν * n := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp32 hν.le) hn.le
  have h2 : t ≤ p ^ 2 * α * n := h1.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα (sq_nonneg p)) hn.le)
  have hνle : ν ≤ 1 := by linarith
  have hp2p : p ^ 2 ≤ p := by nlinarith
  have h3 : p ^ 3 * ν ^ 2 * n ≤ p * n := by
    have hν2 : ν ^ 2 ≤ 1 := by nlinarith
    have hp3 : p ^ 3 ≤ p := hp32.trans hp2p
    exact mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left hν2 (pow_nonneg hp.le 3)).trans (by simpa using hp3)) hn.le
  have h4 : p ^ 3 * ν ^ 2 * n ≤ p * α * n := by
    have hν2 : ν ^ 2 ≤ ν := by nlinarith
    have hp3 : p ^ 3 ≤ p := hp32.trans hp2p
    have hν2α : ν ^ 2 ≤ α := hν2.trans hα
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hp3 hν2α (sq_nonneg ν) hp.le) hn.le
  exact ⟨htlog, hbase, hrank, h1, h2, hscale.trans h3, hscale.trans h4⟩

set_option maxHeartbeats 800000 in
/-- All five events concern the same outcome. The only families supplied in advance
are deterministic layers; no stochastic certificate or per-star law is an input. -/
theorem common_event_exponential_bound (G : Digraph V) (c : V → V → C)
    (hout : OutProper G c) (hin : InProper G c) (hloop : ∀ x, ¬ G.Adj x x)
    (p : Set.Icc (0 : ℝ) 1) (ν α : ℝ) (hν : 0 < ν) (hn : 0 < Fintype.card V)
    (hdegO : ∀ u, α * Fintype.card V ≤ ((outNeighbors G u).card : ℝ))
    (hdegI : ∀ w, α * Fintype.card V ≤ ((incoming G univ w).card : ℝ))
    (hmeanR : (p : ℝ) ^ 3 * ν * Fintype.card V ≤ (p : ℝ) ^ 2 * ν * Fintype.card V)
    (hmeanI : (p : ℝ) ^ 3 * ν * Fintype.card V ≤ (p : ℝ) ^ 2 * α * Fintype.card V)
    (hTb : 3 * ((p : ℝ) ^ 3 * ν * Fintype.card V) / 100 + 5 / ν <
      3 * ((p : ℝ) ^ 3 * ν * Fintype.card V) / 64)
    (hTr : ((p : ℝ) ^ 3 * ν * Fintype.card V) / 50 + 20 / ν <
      ((p : ℝ) ^ 3 * ν * Fintype.card V) / 8)
    (L : V → Fin (Fintype.card V) → Finset V) :
    1 - (Real.exp (-((p : ℝ) * Fintype.card V) / 3) +
      2 * Fintype.card V * Real.exp (-((p : ℝ) * α * Fintype.card V) / 5) +
      (Fintype.card V : ℝ) ^ 2 * Real.exp (-(9 * ((p : ℝ) ^ 3 * ν * Fintype.card V)) / 512) +
      (Fintype.card V : ℝ) ^ 3 * Real.exp (-((p : ℝ) ^ 3 * ν * Fintype.card V) / 32) +
      Fintype.card V * Real.exp (-((p : ℝ) ^ 3 * ν * Fintype.card V) / 8)) ≤
      (reservoirLaw p).real {ω | CommonEvent G c p ν L ω} := by
  classical
  let P : Measure ((V ⊕ C) → Bool) := reservoirLaw p
  have hp : IsProbabilityMeasure P := by dsimp [P, reservoirLaw]; infer_instance
  let := hp
  let n : ℝ := Fintype.card V
  let t : ℝ := (p : ℝ) ^ 3 * ν * n
  let Tb := 3 * t / 100 + 5 / ν
  let Tr := t / 50 + 20 / ν
  let S := {ω : (V ⊕ C) → Bool | ¬SizeEvent (p : ℝ) ω}
  let D := {ω : (V ⊕ C) → Bool | ¬DegreeEvent G c (p : ℝ) ω}
  let B := {ω : (V ⊕ C) → Bool | ¬BaseEvent G c ν Tb ω}
  let R := {ω : (V ⊕ C) → Bool | ¬RankEvent G c ν Tr L ω}
  let I := {ω : (V ⊕ C) → Bool | ¬IncomingEvent G c Tr ω}
  have hS : P.real S ≤ Real.exp (-((p : ℝ) * n) / 3) := by
    refine (measureReal_mono ?_).trans (vertex_upper_tail (V := V) (C := C) p)
    intro ω hω
    exact le_of_lt (show 2 * (p : ℝ) * Fintype.card V < vertexCount ω from
      not_le.mp hω)
  have hB : P.real B ≤ n ^ 2 * Real.exp (-(9 * t) / 512) := by
    have hh := forall_failure P (fun z : V × V => fun ω =>
      z.2 ∉ exceptions G c z.1 (ν * Fintype.card V / 16) →
      ν * Fintype.card V / 4 ≤ ((twoStep G z.1 z.2).card : ℝ) →
        Tb ≤ baseCount G c z.1 z.2 ω) (Real.exp (-(9 * t) / 512)) (by
      intro z
      by_cases hw : z.2 ∉ exceptions G c z.1 (ν * Fintype.card V / 16)
      · by_cases hs : ν * Fintype.card V / 4 ≤ ((twoStep G z.1 z.2).card : ℝ)
        · simpa [P, t, n, hw, hs] using
            graph_base_lower_tail G c hout hin hloop p ν Tb hν hn hTb z.1 z.2 hw hs
        · simp [hs, Real.exp_nonneg]
      · simp [hw, Real.exp_nonneg])
    have he : {ω : (V ⊕ C) → Bool | ¬∀ z : V × V,
      z.2 ∉ exceptions G c z.1 (ν * Fintype.card V / 16) →
      ν * Fintype.card V / 4 ≤ ((twoStep G z.1 z.2).card : ℝ) →
        Tb ≤ baseCount G c z.1 z.2 ω} = B := by
      ext ω; simp [B, BaseEvent]
    rw [he] at hh
    simpa [n, Fintype.card_prod, pow_two] using hh
  have hR : P.real R ≤ n ^ 3 * Real.exp (-t / 32) := by
    have hh := forall_failure P (fun z : V × Fin (Fintype.card V) × V => fun ω =>
      ν * n / 4 ≤ ((incoming G (L z.1 z.2.1) z.2.2).card : ℝ) →
        Tr ≤ incomingCount G c (L z.1 z.2.1) z.2.2 ω) (Real.exp (-t / 32)) (by
      intro z
      let A := incoming G (L z.1 z.2.1) z.2.2
      by_cases hs : ν * n / 4 ≤ (A.card : ℝ)
      · have hm : t / 4 ≤ (p : ℝ) ^ 2 * A.card := by
          have h := mul_le_mul_of_nonneg_left hs (sq_nonneg (p : ℝ))
          dsimp [t, n] at *
          nlinarith
        have hsub : {ω | ¬(ν * n / 4 ≤ (A.card : ℝ) →
            Tr ≤ incomingCount G c (L z.1 z.2.1) z.2.2 ω)} ⊆
            {ω | incomingCount G c (L z.1 z.2.1) z.2.2 ω ≤
              (1 - (1 / 2 : ℝ)) * ((p : ℝ) ^ 2 * A.card)} := by
          intro ω hω
          have ht : incomingCount G c (L z.1 z.2.1) z.2.2 ω < Tr :=
            not_le.mp (not_imp.mp hω).2
          dsimp [Tr, t, n] at *
          linarith
        refine (measureReal_mono hsub).trans
          ((graph_incoming_lower_tail G c hin p _ _ (1 / 2) (by norm_num)).trans
            (Real.exp_le_exp.mpr ?_))
        nlinarith
      · change ¬ν * n / 4 ≤ ((incoming G (L z.1 z.2.1) z.2.2).card : ℝ) at hs
        simp [hs, Real.exp_nonneg])
    have he : {ω : (V ⊕ C) → Bool | ¬∀ z : V × Fin (Fintype.card V) × V,
      ν * n / 4 ≤ ((incoming G (L z.1 z.2.1) z.2.2).card : ℝ) →
        Tr ≤ incomingCount G c (L z.1 z.2.1) z.2.2 ω} = R := by
      ext ω; simp [R, RankEvent, n]
    rw [he] at hh
    simpa [n, Fintype.card_prod, pow_succ, mul_assoc] using hh
  have hI : P.real I ≤ n * Real.exp (-t / 8) := by
    apply forall_failure P (fun w ω => Tr ≤ incomingCount G c univ w ω)
    intro w
    have hm : t ≤ (p : ℝ) ^ 2 * (incoming G univ w).card := hmeanI.trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hdegI w) (sq_nonneg (p : ℝ)))
    have hsub : {ω | ¬Tr ≤ incomingCount G c univ w ω} ⊆
        {ω | incomingCount G c univ w ω ≤
          (1 - (1 / 2 : ℝ)) * ((p : ℝ) ^ 2 * (incoming G univ w).card)} := by
      intro ω hω
      have ht := not_le.mp hω
      have ht0 : 0 ≤ t := by
        exact mul_nonneg (mul_nonneg (pow_nonneg p.property.1 3) hν.le) (Nat.cast_nonneg _)
      dsimp [Tr, t, n] at *
      linarith
    refine (measureReal_mono hsub).trans
      ((graph_incoming_lower_tail G c hin p univ w (1 / 2) (by norm_num)).trans
        (Real.exp_le_exp.mpr ?_))
    nlinarith
  have hDo (u : V) : P.real {ω | ¬(1 - 3 * (p : ℝ)) *
      (outNeighbors G u).card ≤ retainedOut G c u ω} ≤
        Real.exp (-((p : ℝ) * α * n) / 5) := by
    have hh := pair_loss_upper_tail p (fun x : outNeighbors G u => (x : V))
      (fun x => c u x) Subtype.val_injective (fun x y h => Subtype.ext
        (hout u (mem_filter.mp x.property).2 (mem_filter.mp y.property).2 h))
    simp only [Fintype.card_coe] at hh
    refine (measureReal_mono ?_).trans (hh.trans (Real.exp_le_exp.mpr ?_))
    · intro ω hω
      have ht := not_le.mp hω
      dsimp [retainedOut] at ht
      change 3 * (p : ℝ) * (outNeighbors G u).card ≤ _
      linarith
    · have hh := mul_le_mul_of_nonneg_left (hdegO u) p.property.1
      dsimp [n]; linarith
  have hDi (w : V) : P.real {ω | ¬(1 - 3 * (p : ℝ)) *
      (incoming G univ w).card ≤ retainedIn G c w ω} ≤
        Real.exp (-((p : ℝ) * α * n) / 5) := by
    have hh := pair_loss_upper_tail p (fun x : incoming G univ w => (x : V))
      (fun x => c x w) Subtype.val_injective (fun x y h => Subtype.ext
        (hin w (mem_filter.mp x.property).2 (mem_filter.mp y.property).2 h))
    simp only [Fintype.card_coe] at hh
    refine (measureReal_mono ?_).trans (hh.trans (Real.exp_le_exp.mpr ?_))
    · intro ω hω
      have ht := not_le.mp hω
      dsimp [retainedIn] at ht
      change 3 * (p : ℝ) * (incoming G univ w).card ≤ _
      linarith
    · have hh := mul_le_mul_of_nonneg_left (hdegI w) p.property.1
      dsimp [n]; linarith
  have hD : P.real D ≤ 2 * n * Real.exp (-((p : ℝ) * α * n) / 5) := by
    have he : D = {ω | ¬∀ u, (1 - 3 * (p : ℝ)) * (outNeighbors G u).card ≤
        retainedOut G c u ω} ∪
      {ω | ¬∀ w, (1 - 3 * (p : ℝ)) * (incoming G univ w).card ≤
        retainedIn G c w ω} := by
          ext ω
          simp only [D, DegreeEvent, Set.mem_union, Set.mem_ofPred_eq, not_and_or]
    rw [he]
    have h₁ := forall_failure P _ _ hDo
    have h₂ := forall_failure P _ _ hDi
    have h₃ := measureReal_union_le (μ := P)
      {ω | ¬∀ u, (1 - 3 * (p : ℝ)) * (outNeighbors G u).card ≤ retainedOut G c u ω}
      {ω | ¬∀ w, (1 - 3 * (p : ℝ)) * (incoming G univ w).card ≤ retainedIn G c w ω}
    dsimp [n] at *
    linarith
  have he : {ω : (V ⊕ C) → Bool | ¬CommonEvent G c p ν L ω} =
      (((S ∪ D) ∪ B) ∪ R) ∪ I := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, CommonEvent]
    change ¬(SizeEvent (p : ℝ) ω ∧ DegreeEvent G c (p : ℝ) ω ∧
      BaseEvent G c ν Tb ω ∧ RankEvent G c ν Tr L ω ∧ IncomingEvent G c Tr ω) ↔ _
    simp only [S, D, B, R, I, Set.mem_setOf_eq]
    tauto
  have hfail : P.real {ω | ¬CommonEvent G c p ν L ω} ≤
      Real.exp (-((p : ℝ) * n) / 3) + 2 * n * Real.exp (-((p : ℝ) * α * n) / 5) +
      n ^ 2 * Real.exp (-(9 * t) / 512) + n ^ 3 * Real.exp (-t / 32) + n * Real.exp (-t / 8) := by
    rw [he]
    have h₁ := measureReal_union_le (μ := P) S D
    have h₂ := measureReal_union_le (μ := P) (S ∪ D) B
    have h₃ := measureReal_union_le (μ := P) ((S ∪ D) ∪ B) R
    have h₄ := measureReal_union_le (μ := P) (((S ∪ D) ∪ B) ∪ R) I
    linarith
  have hc := measureReal_add_measureReal_compl (μ := P)
    (Set.toFinite {ω | CommonEvent G c p ν L ω}).measurableSet
  have hec : {ω : (V ⊕ C) → Bool | CommonEvent G c p ν L ω}ᶜ =
      {ω | ¬CommonEvent G c p ν L ω} := rfl
  rw [hec, probReal_univ] at hc
  change 1 - _ ≤ P.real _
  dsimp [t, n] at hfail
  linarith

private theorem scaled_exp_bound (n x : ℝ) (hn : 0 < n) (j k : ℕ)
    (hx : ((j + k : ℕ) : ℝ) * Real.log n ≤ x) :
    n ^ j * Real.exp (-x) ≤ 1 / n ^ k := by
  have he (i : ℕ) : n ^ i = Real.exp ((i : ℝ) * Real.log n) := by
    rw [Real.exp_nat_mul, Real.exp_log hn]
  rw [he j, ← Real.exp_add, he k, one_div, ← Real.exp_neg, Real.exp_le_exp]
  push_cast at hx
  linarith

/-- The probability block with the original thresholds and constant 5/n.
The three numerical consequences of robust expansion in the parameter lemma
(ν<1/2, n≥64 and log n>3) are explicit here. Deriving them from the original
robust-expander hypotheses is separate from this stochastic theorem. -/
theorem common_reservoir_probability (G : Digraph V) (c : V → V → C)
    (hout : OutProper G c) (hin : InProper G c) (hloop : ∀ x, ¬ G.Adj x x)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ)) (ν α : ℝ)
    (hν : 0 < ν) (hν1 : ν < 1 / 2) (hα : ν ≤ α)
    (hn : 64 ≤ Fintype.card V) (hlog : 3 < Real.log (Fintype.card V : ℝ))
    (hscale : 144 * Real.log (Fintype.card V : ℝ) ≤
      (p : ℝ) ^ 3 * ν ^ 2 * Fintype.card V)
    (hdegO : ∀ u, α * Fintype.card V ≤ ((outNeighbors G u).card : ℝ))
    (hdegI : ∀ w, α * Fintype.card V ≤ ((incoming G univ w).card : ℝ))
    (L : V → Fin (Fintype.card V) → Finset V) :
    1 - 5 / (Fintype.card V : ℝ) ≤
      (reservoirLaw p).real {ω | CommonEvent G c p ν L ω} := by
  have hn0 : 0 < Fintype.card V := by omega
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn0
  have hn2 : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast (show 2 ≤ Fintype.card V by omega)
  obtain ⟨ht, hTb, hTr, hmR, hmI, hpn, hpan⟩ := parameters (p : ℝ) ν α
    (Fintype.card V) hp p.property.2 hν hν1 hα hnR hlog hscale
  have hh := common_event_exponential_bound G c hout hin hloop p ν α hν hn0
    hdegO hdegI hmR hmI hTb hTr L
  let n : ℝ := Fintype.card V
  let t := (p : ℝ) ^ 3 * ν * n
  have hl0 : 0 ≤ Real.log n := by dsimp [n]; linarith
  have hS : Real.exp (-((p : ℝ) * n) / 3) ≤ 1 / n := by
    have h := scaled_exp_bound n ((p : ℝ) * n / 3) hnR 0 1 (by dsimp [n] at *; norm_num; linarith)
    simpa [neg_div] using h
  have hD : n * Real.exp (-((p : ℝ) * α * n) / 5) ≤ 1 / n := by
    have h := scaled_exp_bound n ((p : ℝ) * α * n / 5) hnR 1 1 (by dsimp [n] at *; norm_num; linarith)
    simpa [neg_div] using h
  have hB : n ^ 2 * Real.exp (-(9 * t) / 512) ≤ 1 / n := by
    have h := scaled_exp_bound n (9 * t / 512) hnR 2 1
      (by dsimp [t, n] at *; norm_num; linarith)
    simpa [neg_div] using h
  have hR : n ^ 3 * Real.exp (-t / 32) ≤ 1 / n ^ 2 := by
    have h := scaled_exp_bound n (t / 32) hnR 3 2
      (by dsimp [t, n] at *; norm_num; linarith)
    simpa [neg_div] using h
  have hI : n * Real.exp (-t / 8) ≤ 1 / n ^ 2 := by
    have h := scaled_exp_bound n (t / 8) hnR 1 2
      (by dsimp [t, n] at *; norm_num; linarith)
    simpa [neg_div] using h
  have hRI : 1 / n ^ 2 + 1 / n ^ 2 ≤ 1 / n := by
    rw [← add_div]
    apply (div_le_div_iff₀ (pow_pos hnR 2) hnR).mpr
    nlinarith
  have hsum : Real.exp (-((p : ℝ) * n) / 3) +
      2 * n * Real.exp (-((p : ℝ) * α * n) / 5) +
      n ^ 2 * Real.exp (-(9 * t) / 512) + n ^ 3 * Real.exp (-t / 32) +
      n * Real.exp (-t / 8) ≤ 5 / n := by
    simp only [div_eq_mul_inv] at hS hD hB hR hI hRI ⊢
    nlinarith only [hS, hD, hB, hR, hI, hRI]
  exact (sub_le_sub_left hsum 1).trans hh

section LiteralPalette

variable {Colour : Type*}

/-- Only literal colours actually used by edges are sampled. -/
def ActualPalette (G : Digraph V) (c : V → V → Colour) :=
  {q : Colour // ∃ u w, G.Adj u w ∧ c u w = q}

instance actualPaletteFintype (G : Digraph V) (c : V → V → Colour) :
    Fintype (ActualPalette G c) := by
  classical
  apply Set.Finite.fintype
  apply (Set.finite_range (fun z : V × V => c z.1 z.2)).subset
  rintro q ⟨u, w, huw, rfl⟩
  exact ⟨(u, w), rfl⟩

/-- The arbitrary default is used only on nonedges and never enters a graph count. -/
def paletteColour (G : Digraph V) (c : V → V → Colour) (q₀ : ActualPalette G c)
    (u w : V) : ActualPalette G c := by
  classical
  exact if h : G.Adj u w then ⟨c u w, u, w, h, rfl⟩ else q₀

/-- Passing to the actual finite palette preserves equality of literal edge colours. -/
theorem palette_colour_eq_iff (G : Digraph V) (c : V → V → Colour)
    (q₀ : ActualPalette G c) (u w x y : V) (huw : G.Adj u w) (hxy : G.Adj x y) :
    paletteColour G c q₀ u w = paletteColour G c q₀ x y ↔ c u w = c x y := by
  classical
  simp only [paletteColour, huw, hxy, ↓reduceDIte]
  exact Subtype.ext_iff

/-- A global colour type may be infinite or even coincide with the vertex type.
The probability concerns the actual finite palette and a sum-tagged product law. -/
theorem actual_palette_common_reservoir (G : Digraph V) (c : V → V → Colour)
    (hout : OutProper G c) (hin : InProper G c) (hloop : ∀ x, ¬ G.Adj x x)
    (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ)) (ν α : ℝ)
    (hν : 0 < ν) (hν1 : ν < 1 / 2) (hα : ν ≤ α)
    (hn : 64 ≤ Fintype.card V) (hlog : 3 < Real.log (Fintype.card V : ℝ))
    (hscale : 144 * Real.log (Fintype.card V : ℝ) ≤
      (p : ℝ) ^ 3 * ν ^ 2 * Fintype.card V)
    (hdegO : ∀ u, α * Fintype.card V ≤ ((outNeighbors G u).card : ℝ))
    (hdegI : ∀ w, α * Fintype.card V ≤ ((incoming G univ w).card : ℝ))
    (L : V → Fin (Fintype.card V) → Finset V) :
    ∃ q₀ : ActualPalette G c,
      1 - 5 / (Fintype.card V : ℝ) ≤
        (reservoirLaw p).real {ω | CommonEvent G (paletteColour G c q₀) p ν L ω} := by
  classical
  have hn0 : 0 < Fintype.card V := by omega
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn0
  let u : V := Classical.choice (Fintype.card_pos_iff.mp hn0)
  have hdegree : 0 < ((outNeighbors G u).card : ℝ) :=
    (mul_pos (lt_of_lt_of_le hν hα) hnR).trans_le (hdegO u)
  obtain ⟨w, hw⟩ := card_pos.mp (show 0 < (outNeighbors G u).card by exact_mod_cast hdegree)
  let q₀ : ActualPalette G c := ⟨c u w, u, w, (mem_filter.mp hw).2, rfl⟩
  have ho : OutProper G (paletteColour G c q₀) := by
    intro v x hx y hy hxy
    exact hout v hx hy ((palette_colour_eq_iff G c q₀ v x v y hx hy).mp hxy)
  have hi : InProper G (paletteColour G c q₀) := by
    intro v x hx y hy hxy
    exact hin v hx hy ((palette_colour_eq_iff G c q₀ x v y v hx hy).mp hxy)
  exact ⟨q₀, common_reservoir_probability G (paletteColour G c q₀) ho hi hloop p hp
    ν α hν hν1 hα hn hlog hscale hdegO hdegI L⟩

end LiteralPalette

example : Set.Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩

example : (Fin 65536 ⊕ (Fin 65536 × Fin 65536)) → Bool := fun _ => false

-- A concrete model of every numerical and graph hypothesis of the probability block.
-- Its degrees are computed symbolically by erasing one vertex, without enumeration.
example :
    let W := Fin 65536
    let H : Digraph W := ⟨fun u w => u ≠ w⟩
    let c : W → W → W × W := fun u w => (u, w)
    OutProper H c ∧ InProper H c ∧ (∀ x, ¬H.Adj x x) ∧
      (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 / 4 ∧ (1 / 4 : ℝ) < 1 / 2 ∧
      (1 / 4 : ℝ) ≤ 1 / 4 ∧ 64 ≤ Fintype.card W ∧
      3 < Real.log (Fintype.card W : ℝ) ∧
      144 * Real.log (Fintype.card W : ℝ) ≤
        (1 : ℝ) ^ 3 * (1 / 4) ^ 2 * Fintype.card W ∧
      (∀ u, (1 / 4 : ℝ) * Fintype.card W ≤ ((outNeighbors H u).card : ℝ)) ∧
      (∀ w, (1 / 4 : ℝ) * Fintype.card W ≤ ((incoming H univ w).card : ℝ)) := by
  classical
  dsimp only
  have hlog : Real.log (65536 : ℝ) = 16 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 16
    norm_num at h
    exact h
  have hlo : (2 / 3 : ℝ) ≤ Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
    norm_num at h ⊢; exact h
  have hhi : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢; exact h
  have ho (u : Fin 65536) :
      outNeighbors (⟨fun u w : Fin 65536 => u ≠ w⟩ : Digraph _) u = univ.erase u := by
    ext w; simp [outNeighbors, ne_comm]
  have hi (w : Fin 65536) :
      incoming (⟨fun u w : Fin 65536 => u ≠ w⟩ : Digraph _) univ w = univ.erase w := by
    ext u; simp [incoming]
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, le_rfl, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro u x hx y hy hxy; exact congrArg Prod.snd hxy
  · intro w x hx y hy hxy; exact congrArg Prod.fst hxy
  · intro x h; exact h rfl
  · norm_num; rw [hlog]; linarith
  · norm_num; rw [hlog]; linarith
  · intro u; rw [ho]; norm_num [card_erase_of_mem (mem_univ u)]
  · intro w; rw [hi]; norm_num [card_erase_of_mem (mem_univ w)]

end D5.S3.Combinatorics.Probability.CommonReservoir
