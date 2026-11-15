/- GID: D5/S1/Words/Patterns/BarkerRegularRelationCounting
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/BarkerRegularRelationCounting
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Literal repetition-word counts for loopless relations of constant indegree. -/

/-
The source model is the regular-relation extension of Ma and Zhang's cyclic
repetition enumeration. The eight-letter theorem and its original settlement
remain in BarkerCyclicRepetitionCounting.

Candidate admission_basis: escape-witness, the uniform literal-word fiber law
in weight_transition and its unique first-letter/suffix correspondence in
phaseCount_cons, consumed by relation_enumeration through actual cardinalities.
The series elimination and scalar recurrence are consumed bind-only steps.
Utility is none: the conclusion is an all-length symbolic enumeration.
Direct frozen theorem dependencies: none; the original owner supplies the
pinned Mathlib dependency neighborhood and is reused by exact applications.

Escape registration is unfinished. Linked issue:
https://github.com/the-omega-institute/trureturing/issues/25339
The targets are relation_enumeration, event_enumeration, and
binary_substring_equivalence. Missing evidence is an enrolled
source-owned reconstruction of its complete q,d,R telescope and conjunction,
an actual-positive bridge for both full count and exact-event cardinalities,
whole-family variation, slot sensitivity, and
observational dependence. For binary_substring_equivalence the missing template
also reconstructs the complete binary word, its actual contiguous sublists,
signed counts, and the original overlapping event chain. Its actual-positive
realization, whole-family variation, slot sensitivity and observational
dependence are not supplied. No validated registration is asserted.

C admission candidate: strip_states proves by induction the exact possible
starting heights for each actual word and its first event; its live consumer
events_iff_strip feeds binary_substring_equivalence. The reverse strip bridge
constructs a starting height from a minimum actual prefix and bounds every
other prefix by a genuine intervening sublist. No word cardinality is used.
proof_shape: binary_substring_equivalence: content.
escape_witness: strip_states on its live derivation path.
The auxiliary equalities and logical bridges are consumed in that proof;
no terminal bind-only specialization is retained.
-/

import D5.S1.Words.Patterns.BarkerCyclicRepetitionCounting

/-! Literal word enumeration for regular incoming event relations. -/

set_option autoImplicit false

noncomputable section
namespace D5.S1.Words.Patterns.BarkerRegularRelationCounting
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Ordered equality-event labels, retaining overlapping adjacent equal pairs. -/
def eventLabels {q : ℕ} (w : List (Fin q)) : List (Fin q) :=
  ((w.zip w.tail).filter (fun p => p.1 = p.2)).map Prod.snd

/-- The relation constrains successive events; the word itself is linear. -/
def Admissible {q n : ℕ} (R : Fin q → Fin q → Prop) (w : Fin n → Fin q) : Prop :=
  (eventLabels (List.ofFn w)).IsChain R

/-- Cardinality of actual labeled words, without any rotation or alphabet quotient. -/
def count {q : ℕ} (R : Fin q → Fin q → Prop) (n : ℕ) : ℕ :=
  Nat.card {w : Fin n → Fin q // Admissible R w}

private def weight {q : ℕ} (R : Fin q → Fin q → Prop)
    (b : Fin q) (es : List (Fin q)) (i : Fin 3) : ℚ := by
  classical
  exact if es.IsChain R then
    match es with
    | [] => if i = 0 then 1 else 0
    | r :: _ => if i = (if R b r then 1 else 2) then 1 else 0
  else 0

private def prependEvents {q : ℕ} (a b : Fin q) (es : List (Fin q)) : List (Fin q) :=
  if a = b then b :: es else es

private theorem eventLabels_cons {q : ℕ} (a b : Fin q) (l : List (Fin q)) :
    eventLabels (a :: b :: l) = prependEvents a b (eventLabels (b :: l)) := by
  simp [eventLabels, prependEvents, List.zip_cons_cons]; split_ifs <;> simp_all

private theorem weight_partition {q : ℕ} (R : Fin q → Fin q → Prop)
    (b : Fin q) (es : List (Fin q)) :
    weight R b es 0 + weight R b es 1 + weight R b es 2 =
      if es.IsChain R then 1 else 0 := by
  classical
  cases es <;> simp [weight] <;> split_ifs <;> simp_all

private theorem predecessor_sum {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hd : ∀ r, Nat.card {b : Fin q // R b r} = d) (r : Fin q) :
    (∑ a : Fin q, if R a r then (1 : ℚ) else 0) = d := by
  classical
  have h := hd r
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter] at h
  exact_mod_cast h

private theorem weight_transition {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ r, Nat.card {b : Fin q // R b r} = d)
    (b : Fin q) (es : List (Fin q)) :
    (∑ a : Fin q, weight R a (prependEvents a b es) 0) = (q - 1 : ℚ) * weight R b es 0 ∧
    (∑ a : Fin q, weight R a (prependEvents a b es) 1) =
      (d - 1 : ℚ) * weight R b es 1 + d * weight R b es 2 ∧
    (∑ a : Fin q, weight R a (prependEvents a b es) 2) =
      weight R b es 0 + (q - d + 1 : ℚ) * weight R b es 1 +
        (q - d - 1 : ℚ) * weight R b es 2 := by
  classical
  cases es with
  | nil =>
    have h0 : ∀ a, weight R a (prependEvents a b []) 0 =
        1 - (if a = b then 1 else 0 : ℚ) := by
      intro a
      by_cases h : a = b <;> simp [prependEvents, weight, h, hl]
    have h1 : ∀ a, weight R a (prependEvents a b []) 1 = 0 := by
      intro a
      by_cases h : a = b <;> simp [prependEvents, weight, h, hl]
    have h2 : ∀ a, weight R a (prependEvents a b []) 2 =
        (if a = b then 1 else 0 : ℚ) := by
      intro a
      by_cases h : a = b <;> simp [prependEvents, weight, h, hl]
    simp only [h0, h1, h2]
    simp [Finset.sum_sub_distrib, weight]
  | cons r rs =>
    by_cases ht : (r :: rs).IsChain R
    · have h0 : ∀ a, weight R a (prependEvents a b (r :: rs)) 0 = 0 := by
        intro a
        by_cases h : a = b <;> simp [prependEvents, weight, h, ht, List.isChain_cons_cons, hl]
        split_ifs <;> norm_num
      have h1 : ∀ a, weight R a (prependEvents a b (r :: rs)) 1 =
          (if R a r then 1 else 0 : ℚ) -
            (if a = b then 1 else 0 : ℚ) * (if R b r then 1 else 0 : ℚ) := by
        intro a
        by_cases h : a = b
        · subst a
          simp [prependEvents, weight, ht, List.isChain_cons_cons, hl]
        · by_cases ha : R a r <;>
            simp [prependEvents, weight, h, ht, ha]
      have h2 : ∀ a, weight R a (prependEvents a b (r :: rs)) 2 =
          1 - (if R a r then 1 else 0 : ℚ) - (if a = b then 1 else 0 : ℚ) +
            2 * (if a = b then 1 else 0 : ℚ) * (if R b r then 1 else 0 : ℚ) := by
        intro a
        by_cases h : a = b
        · subst a
          by_cases hb : R b r <;>
            norm_num [prependEvents, weight, ht, List.isChain_cons_cons, hl, hb]
        · by_cases ha : R a r <;>
            simp [prependEvents, weight, h, ht, ha]
      simp only [h0, h1, h2, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_mul, Finset.mul_sum]
      simp only [predecessor_sum R hd, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      refine ⟨?_, ?_, ?_⟩ <;> by_cases hb : R b r <;> simp [weight, ht, hb] <;> ring
    · simp [weight, prependEvents, apply_ite, List.isChain_cons_cons, ht]

private def phaseCount {q : ℕ} (R : Fin q → Fin q → Prop) (n : ℕ) (i : Fin 3) : ℚ :=
  ∑ w : Fin (n + 1) → Fin q, weight R (w 0) (eventLabels (List.ofFn w)) i

private theorem count_partition {q : ℕ} (R : Fin q → Fin q → Prop) (n : ℕ) :
    (count R (n + 1) : ℚ) = phaseCount R n 0 + phaseCount R n 1 + phaseCount R n 2 := by
  classical
  unfold count phaseCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  have hw := (weight_partition R (w 0) (eventLabels (List.ofFn w))).symm
  by_cases h : Admissible R w
  · have h' : (eventLabels (List.ofFn w)).IsChain R := h
    simpa only [ite_eq_left h, ite_eq_left h'] using hw
  · have h' : ¬ (eventLabels (List.ofFn w)).IsChain R := h
    simpa only [ite_eq_right h, ite_eq_right h'] using hw

private theorem phaseCount_cons {q : ℕ} (R : Fin q → Fin q → Prop) (n : ℕ) (i : Fin 3) :
    phaseCount R (n + 1) i =
      ∑ w : Fin (n + 1) → Fin q,
        ∑ a : Fin q, weight R a (prependEvents a (w 0) (eventLabels (List.ofFn w))) i := by
  classical
  unfold phaseCount
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1 + 1) => Fin q)).sum_comp
    (fun w => weight R (w 0) (eventLabels (List.ofFn w)) i)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro a _
  change weight R a (eventLabels (List.ofFn (Fin.cons a w))) i = _
  rw [List.ofFn_cons, List.ofFn_succ (f := w), eventLabels_cons]

private theorem phaseCount_initial {q : ℕ} (R : Fin q → Fin q → Prop) :
    phaseCount R 0 0 = q ∧ phaseCount R 0 1 = 0 ∧ phaseCount R 0 2 = 0 := by
  classical
  simp [phaseCount, List.ofFn_succ, eventLabels, weight]

private theorem phaseCount_step {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ r, Nat.card {b : Fin q // R b r} = d) (n : ℕ) :
    phaseCount R (n + 1) 0 = (q - 1 : ℚ) * phaseCount R n 0 ∧
    phaseCount R (n + 1) 1 =
      (d - 1 : ℚ) * phaseCount R n 1 + d * phaseCount R n 2 ∧
    phaseCount R (n + 1) 2 =
      phaseCount R n 0 + (q - d + 1 : ℚ) * phaseCount R n 1 +
        (q - d - 1 : ℚ) * phaseCount R n 2 := by
  classical
  simp only [phaseCount_cons]
  unfold phaseCount
  constructor
  · simp_rw [(weight_transition R hl hd _ _).1, Finset.mul_sum]
  constructor
  · simp_rw [(weight_transition R hl hd _ _).2.1, Finset.sum_add_distrib, Finset.mul_sum]
  · simp_rw [(weight_transition R hl hd _ _).2.2, Finset.sum_add_distrib, Finset.mul_sum]

private def stateSeries {q : ℕ} (R : Fin q → Fin q → Prop) (i : Fin 3) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => phaseCount R n i)

private theorem stateSeries_equations {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ r, Nat.card {b : Fin q // R b r} = d) :
    stateSeries R 0 = PowerSeries.C (q : ℚ) +
      PowerSeries.C (q - 1 : ℚ) * (PowerSeries.X * stateSeries R 0) ∧
    stateSeries R 1 = PowerSeries.X *
      (PowerSeries.C (d - 1 : ℚ) * stateSeries R 1 + PowerSeries.C (d : ℚ) * stateSeries R 2) ∧
    stateSeries R 2 = PowerSeries.X *
      (stateSeries R 0 + PowerSeries.C (q - d + 1 : ℚ) * stateSeries R 1 +
        PowerSeries.C (q - d - 1 : ℚ) * stateSeries R 2) := by
  constructor
  · ext n
    cases n with
    | zero => simp [stateSeries, phaseCount_initial]
    | succ n =>
      simpa only [stateSeries, PowerSeries.coeff_mk, map_add (PowerSeries.coeff (n + 1)),
        map_add (PowerSeries.coeff n),
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C,
        Nat.succ_ne_zero, ite_false, zero_add] using (phaseCount_step R hl hd n).1
  constructor
  · ext n
    cases n with
    | zero => simp [stateSeries, phaseCount_initial]
    | succ n =>
      simpa only [stateSeries, PowerSeries.coeff_mk, map_add (PowerSeries.coeff (n + 1)),
        map_add (PowerSeries.coeff n),
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] using (phaseCount_step R hl hd n).2.1
  · ext n
    cases n with
    | zero => simp [stateSeries, phaseCount_initial]
    | succ n =>
      simpa only [stateSeries, PowerSeries.coeff_mk, map_add (PowerSeries.coeff (n + 1)),
        map_add (PowerSeries.coeff n),
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] using (phaseCount_step R hl hd n).2.2

/-- The positive-index literal-word series has constant coefficient zero. -/
def sourceSeries {q : ℕ} (R : Fin q → Fin q → Prop) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (count R n : ℚ))

private theorem sourceSeries_eq {q : ℕ} (R : Fin q → Fin q → Prop) :
    sourceSeries R = PowerSeries.X * (stateSeries R 0 + stateSeries R 1 + stateSeries R 2) := by
  ext n
  cases n with
  | zero => simp [sourceSeries]
  | succ n => simp [sourceSeries, stateSeries, count_partition]

private theorem sourceSeries_formula {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ r, Nat.card {b : Fin q // R b r} = d) :
    sourceSeries R = PowerSeries.C (q : ℚ) * PowerSeries.X *
      (1 - PowerSeries.C (q - 3 : ℚ) * PowerSeries.X -
        PowerSeries.C (q + d - 2 : ℚ) * PowerSeries.X ^ 2) *
      ((1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X) *
        (1 - PowerSeries.C (q - 2 : ℚ) * PowerSeries.X -
          PowerSeries.C (q + d - 1 : ℚ) * PowerSeries.X ^ 2))⁻¹ := by
  let Q : PowerSeries ℚ := PowerSeries.C (q : ℚ)
  let D : PowerSeries ℚ := PowerSeries.C (d : ℚ)
  have he := stateSeries_equations R hl hd
  simp only [map_sub, map_add, map_one, map_ofNat] at he ⊢
  change sourceSeries R = Q * PowerSeries.X *
    (1 - (Q - 3) * PowerSeries.X - (Q + D - 2) * PowerSeries.X ^ 2) *
    ((1 - (Q - 1) * PowerSeries.X) *
      (1 - (Q - 2) * PowerSeries.X - (Q + D - 1) * PowerSeries.X ^ 2))⁻¹
  have hu : (1 - (Q - 1) * PowerSeries.X) * stateSeries R 0 = Q := by
    linear_combination he.1
  have hab : (stateSeries R 1 + stateSeries R 2) *
      (1 - (Q - 2) * PowerSeries.X - (Q + D - 1) * PowerSeries.X ^ 2) =
      PowerSeries.X * (1 + PowerSeries.X) * stateSeries R 0 := by
    linear_combination
      (1 + 2 * PowerSeries.X) * he.2.1 +
      (1 + PowerSeries.X) * he.2.2
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp [Q, D] :
    PowerSeries.constantCoeff ((1 - (Q - 1) * PowerSeries.X) *
      (1 - (Q - 2) * PowerSeries.X - (Q + D - 1) * PowerSeries.X ^ 2)) ≠ 0)).2
  rw [sourceSeries_eq]
  calc
    PowerSeries.X * (stateSeries R 0 + stateSeries R 1 + stateSeries R 2) *
        ((1 - (Q - 1) * PowerSeries.X) *
          (1 - (Q - 2) * PowerSeries.X - (Q + D - 1) * PowerSeries.X ^ 2)) =
      PowerSeries.X * (stateSeries R 0 *
        (1 - (Q - 2) * PowerSeries.X - (Q + D - 1) * PowerSeries.X ^ 2) +
        (stateSeries R 1 + stateSeries R 2) *
          (1 - (Q - 2) * PowerSeries.X - (Q + D - 1) * PowerSeries.X ^ 2)) *
        (1 - (Q - 1) * PowerSeries.X) := by ring
    _ = PowerSeries.X * (stateSeries R 0 *
        (1 - (Q - 2) * PowerSeries.X - (Q + D - 1) * PowerSeries.X ^ 2) +
        PowerSeries.X * (1 + PowerSeries.X) * stateSeries R 0) *
        (1 - (Q - 1) * PowerSeries.X) := by rw [hab]
    _ = PowerSeries.X * (1 - (Q - 3) * PowerSeries.X -
        (Q + D - 2) * PowerSeries.X ^ 2) *
        ((1 - (Q - 1) * PowerSeries.X) * stateSeries R 0) := by ring
    _ = Q * PowerSeries.X * (1 - (Q - 3) * PowerSeries.X -
        (Q + D - 2) * PowerSeries.X ^ 2) := by rw [hu]; ring

private theorem count_initial {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ r, Nat.card {b : Fin q // R b r} = d) :
    count R 0 = 1 ∧ (count R 1 : ℚ) = q ∧ (count R 2 : ℚ) = (q : ℚ)^2 ∧
      (count R 3 : ℚ) = (q : ℚ)^3 - q := by
  constructor
  · simp [count, Admissible, eventLabels, Nat.card_eq_fintype_card]
  change (count R (0 + 1) : ℚ) = q ∧ (count R ((0 + 1) + 1) : ℚ) = (q : ℚ)^2 ∧
    (count R (((0 + 1) + 1) + 1) : ℚ) = (q : ℚ)^3 - q
  simp only [count_partition,
    phaseCount_step R hl hd, phaseCount_initial]
  constructor
  · ring
  constructor <;> ring

private theorem count_recurrence {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ r, Nat.card {b : Fin q // R b r} = d) (n : ℕ) :
    (count R (n + 4) : ℚ) = (2 * q - 3 : ℚ) * count R (n + 3) +
      (-(q : ℚ)^2 + 4*q + d - 3) * count R (n + 2) -
        (q - 1 : ℚ) * (q + d - 1 : ℚ) * count R (n + 1) := by
  change (count R ((n + 3) + 1) : ℚ) =
    (2 * q - 3 : ℚ) * count R ((n + 2) + 1) +
      (-(q : ℚ)^2 + 4*q + d - 3) * count R ((n + 1) + 1) -
        (q - 1 : ℚ) * (q + d - 1 : ℚ) * count R (n + 1)
  simp only [count_partition, phaseCount_step R hl hd]
  ring

/-- The universal enumeration of literal words for a loopless constant-indegree relation.
The recurrence starts at positive length; the empty word has count one separately. -/
theorem relation_enumeration {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ r, Nat.card {b : Fin q // R b r} = d) :
    (count R 0 = 1 ∧ (count R 1 : ℚ) = q ∧ (count R 2 : ℚ) = (q : ℚ)^2 ∧
      (count R 3 : ℚ) = (q : ℚ)^3 - q) ∧
    sourceSeries R = PowerSeries.C (q : ℚ) * PowerSeries.X *
      (1 - PowerSeries.C (q - 3 : ℚ) * PowerSeries.X -
        PowerSeries.C (q + d - 2 : ℚ) * PowerSeries.X ^ 2) *
      ((1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X) *
        (1 - PowerSeries.C (q - 2 : ℚ) * PowerSeries.X -
          PowerSeries.C (q + d - 1 : ℚ) * PowerSeries.X ^ 2))⁻¹ ∧
    ∀ n : ℕ, (count R (n + 4) : ℚ) =
      (2*q - 3 : ℚ) * count R (n + 3) +
        (-(q : ℚ)^2 + 4*q + d - 3) * count R (n + 2) -
          (q - 1 : ℚ) * (q + d - 1 : ℚ) * count R (n + 1) := by
  exact ⟨count_initial R hl hd, sourceSeries_formula R hl hd, count_recurrence R hl hd⟩


/-- The actual admissible-word fiber with exactly r adjacent equality events. -/
def eventCount {q : ℕ} (R : Fin q → Fin q → Prop) (n r : ℕ) : ℕ :=
  Nat.card {w : Fin n → Fin q // Admissible R w ∧
    (eventLabels (List.ofFn w)).length = r}

private def fiberWeight {q : ℕ} (R : Fin q → Fin q → Prop)
    (r : ℕ) (b : Fin q) (es : List (Fin q)) (i : Fin 3) : ℚ :=
  if es.length = r then weight R b es i else 0

private theorem equal_weight {q : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (b : Fin q) (es : List (Fin q)) :
    weight R b (prependEvents b b es) 0 = 0 ∧
    weight R b (prependEvents b b es) 1 = 0 ∧
    weight R b (prependEvents b b es) 2 = weight R b es 0 + weight R b es 1 := by
  cases es with
  | nil => simp [weight, prependEvents, hl]
  | cons c cs =>
    by_cases ht : (c :: cs).IsChain R <;> by_cases hb : R b c <;>
      simp [weight, prependEvents, List.isChain_cons_cons, hl, ht, hb]

private theorem fiberWeight_sum {q : ℕ} (R : Fin q → Fin q → Prop)
    (r : ℕ) (b : Fin q) (es : List (Fin q)) (i : Fin 3) :
    (∑ a : Fin q, fiberWeight R r a (prependEvents a b es) i) =
      (if es.length = r then (1 : ℚ) else 0) *
        (∑ a : Fin q, weight R a (prependEvents a b es) i) +
      ((if es.length + 1 = r then (1 : ℚ) else 0) -
        (if es.length = r then (1 : ℚ) else 0)) *
          weight R b (prependEvents b b es) i := by
  classical
  rw [Finset.mul_sum]
  rw [show ((if es.length + 1 = r then (1 : ℚ) else 0) -
      (if es.length = r then (1 : ℚ) else 0)) *
        weight R b (prependEvents b b es) i =
      ∑ a : Fin q, if a = b then
        ((if es.length + 1 = r then (1 : ℚ) else 0) -
        (if es.length = r then (1 : ℚ) else 0)) *
          weight R a (prependEvents a b es) i else 0 by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a = b
  · subst a
    simp only [fiberWeight, prependEvents, ite_true, List.length_cons]
    split_ifs <;> ring
  · simp [fiberWeight, prependEvents, h]

private def fiberPhase {q : ℕ} (R : Fin q → Fin q → Prop)
    (r n : ℕ) (i : Fin 3) : ℚ :=
  ∑ w : Fin (n + 1) → Fin q, fiberWeight R r (w 0) (eventLabels (List.ofFn w)) i

private theorem fiberPhase_cons {q : ℕ} (R : Fin q → Fin q → Prop)
    (r n : ℕ) (i : Fin 3) :
    fiberPhase R r (n + 1) i = ∑ w : Fin (n + 1) → Fin q,
      ∑ a : Fin q, fiberWeight R r a (prependEvents a (w 0) (eventLabels (List.ofFn w))) i := by
  classical
  unfold fiberPhase
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1 + 1) => Fin q)).sum_comp
    (fun w => fiberWeight R r (w 0) (eventLabels (List.ofFn w)) i)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro a _
  change fiberWeight R r a (eventLabels (List.ofFn (Fin.cons a w))) i = _
  rw [List.ofFn_cons, List.ofFn_succ (f := w), eventLabels_cons]

private theorem fiberPhase_step {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ c, Nat.card {b : Fin q // R b c} = d)
    (r n : ℕ) :
    fiberPhase R r (n + 1) 0 = (q - 1 : ℚ) * fiberPhase R r n 0 ∧
    fiberPhase R r (n + 1) 1 =
      (d - 1 : ℚ) * fiberPhase R r n 1 + d * fiberPhase R r n 2 ∧
    fiberPhase R r (n + 1) 2 =
      (q - d : ℚ) * fiberPhase R r n 1 + (q - d - 1 : ℚ) * fiberPhase R r n 2 +
        (if r = 0 then 0 else fiberPhase R (r - 1) n 0 + fiberPhase R (r - 1) n 1) := by
  have hf (b : Fin q) (es : List (Fin q)) :
      (∑ a : Fin q, fiberWeight R r a (prependEvents a b es) 0) =
        (q - 1 : ℚ) * fiberWeight R r b es 0 ∧
      (∑ a : Fin q, fiberWeight R r a (prependEvents a b es) 1) =
        (d - 1 : ℚ) * fiberWeight R r b es 1 + d * fiberWeight R r b es 2 ∧
      (∑ a : Fin q, fiberWeight R r a (prependEvents a b es) 2) =
        (q - d : ℚ) * fiberWeight R r b es 1 +
        (q - d - 1 : ℚ) * fiberWeight R r b es 2 +
        (if r = 0 then 0 else fiberWeight R (r - 1) b es 0 +
          fiberWeight R (r - 1) b es 1) := by
    simp only [fiberWeight_sum, (weight_transition R hl hd b es).1,
      (weight_transition R hl hd b es).2.1, (weight_transition R hl hd b es).2.2,
      (equal_weight R hl b es).1, (equal_weight R hl b es).2.1,
      (equal_weight R hl b es).2.2, mul_zero, add_zero]
    cases r with
    | zero => simp [fiberWeight]; split_ifs <;> (repeat' constructor) <;> ring
    | succ r =>
      have h : es.length + 1 = r + 1 ↔ es.length = r := by omega
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        ite_false, h, fiberWeight]
      split_ifs <;> (repeat' constructor) <;> ring
  simp only [fiberPhase_cons]
  constructor
  · simp only [(hf _ _).1, fiberPhase, Finset.mul_sum]
  constructor
  · simp only [(hf _ _).2.1, fiberPhase, Finset.sum_add_distrib, Finset.mul_sum]
  · simp_rw [(hf _ _).2.2]
    cases r <;> simp [fiberPhase, Finset.sum_add_distrib, Finset.mul_sum]

private theorem fiberPhase_initial {q : ℕ} (R : Fin q → Fin q → Prop) (r : ℕ) :
    fiberPhase R r 0 0 = (if r = 0 then q else 0) ∧
    fiberPhase R r 0 1 = 0 ∧ fiberPhase R r 0 2 = 0 := by
  cases r <;> simp [fiberPhase, fiberWeight, List.ofFn_succ, eventLabels, weight]

private theorem eventCount_partition {q : ℕ} (R : Fin q → Fin q → Prop) (r n : ℕ) :
    (eventCount R (n + 1) r : ℚ) =
      fiberPhase R r n 0 + fiberPhase R r n 1 + fiberPhase R r n 2 := by
  classical
  unfold eventCount fiberPhase
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : (eventLabels (List.ofFn w)).length = r
  · simp only [fiberWeight, h, ite_true, weight_partition]
    simp [Admissible, h]
  · simp only [fiberWeight, h, ite_false, add_zero, and_false]

private def fiberSeries {q : ℕ} (R : Fin q → Fin q → Prop)
    (r : ℕ) (i : Fin 3) : PowerSeries ℚ :=
  PowerSeries.X * PowerSeries.mk (fun n => fiberPhase R r n i)

/-- Positive-length series of actual exact-event fibers. -/
def eventSeries {q : ℕ} (R : Fin q → Fin q → Prop) (r : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun n => if n = 0 then 0 else (eventCount R n r : ℚ))

private theorem eventSeries_partition {q : ℕ} (R : Fin q → Fin q → Prop) (r : ℕ) :
    eventSeries R r = fiberSeries R r 0 + fiberSeries R r 1 + fiberSeries R r 2 := by
  ext n
  cases n <;> simp [eventSeries, fiberSeries, eventCount_partition]

private theorem fiberSeries_equations {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ c, Nat.card {b : Fin q // R b c} = d) (r : ℕ) :
    fiberSeries R r 0 = (if r = 0 then PowerSeries.C (q : ℚ) * PowerSeries.X else 0) +
      PowerSeries.C (q - 1 : ℚ) * (PowerSeries.X * fiberSeries R r 0) ∧
    fiberSeries R r 1 = PowerSeries.X *
      (PowerSeries.C (d - 1 : ℚ) * fiberSeries R r 1 + PowerSeries.C (d : ℚ) * fiberSeries R r 2) ∧
    fiberSeries R r 2 = PowerSeries.X *
      (PowerSeries.C (q - d : ℚ) * fiberSeries R r 1 +
        PowerSeries.C (q - d - 1 : ℚ) * fiberSeries R r 2 +
          (if r = 0 then 0 else fiberSeries R (r - 1) 0 + fiberSeries R (r - 1) 1)) := by
  have basic (i : Fin 3) : PowerSeries.coeff 0 (fiberSeries R r i) = 0 := by
    simp only [fiberSeries, PowerSeries.coeff_zero_X_mul]
  constructor
  · ext n
    cases n with
    | zero => cases r <;> simp [fiberSeries]
    | succ n =>
      cases n with
      | zero =>
        cases r <;> simp only [fiberSeries, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_zero_X_mul, fiberPhase_initial, ite_true,
          Nat.succ_ne_zero, ite_false, mul_zero, add_zero, PowerSeries.coeff_C_mul_X_pow,
          pow_one, PowerSeries.coeff_X, ite_true, mul_one, Nat.cast_zero, map_zero]
      | succ n =>
        have step := (fiberPhase_step R hl hd r n).1
        cases r <;> simpa only [fiberSeries, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul,
          Nat.succ_ne_zero, ite_false, ite_true, map_zero,
          PowerSeries.coeff_X, Nat.add_eq_zero_iff, and_false, one_ne_zero,
          mul_zero, zero_add, PowerSeries.coeff_C_mul, Nat.add_eq_right,
          Nat.succ_ne_zero] using step
  constructor
  · ext n
    cases n with
    | zero => simp only [basic, PowerSeries.coeff_zero_X_mul]
    | succ n =>
      cases n with
      | zero => simp only [fiberSeries, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul,
          PowerSeries.coeff_zero_X_mul, fiberPhase_initial, mul_zero, add_zero]
      | succ n => simpa only [fiberSeries, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul] using
            (fiberPhase_step R hl hd r n).2.1
  · ext n
    cases n with
    | zero => simp only [basic, PowerSeries.coeff_zero_X_mul]
    | succ n =>
      cases n with
      | zero => cases r <;> simp [fiberSeries, fiberPhase_initial]
      | succ n =>
        have step := (fiberPhase_step R hl hd r n).2.2
        cases r <;> simpa only [fiberSeries, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C_mul,
          Nat.succ_ne_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false, ite_true, map_zero, add_zero,
          Nat.add_sub_cancel] using step


private theorem fiberSeries_zero_parts {q : ℕ} (R : Fin q → Fin q → Prop) :
    (∀ r, fiberSeries R (r + 1) 0 = 0) ∧
    fiberSeries R 0 1 = 0 ∧ fiberSeries R 0 2 = 0 := by
  have hp (r : ℕ) (b : Fin q) (es : List (Fin q)) :
      fiberWeight R (r + 1) b es 0 = 0 := by
    cases es <;> simp [fiberWeight, weight] <;> split_ifs <;> norm_num
  have hz (b : Fin q) (es : List (Fin q)) :
      fiberWeight R 0 b es 1 = 0 ∧ fiberWeight R 0 b es 2 = 0 := by
    cases es <;> simp [fiberWeight, weight]
  constructor
  · intro r
    simp [fiberSeries, fiberPhase, hp]
    ext n; simp
  constructor
  · simp [fiberSeries, fiberPhase, fun b es => (hz b es).1]
    ext n; simp
  · simp [fiberSeries, fiberPhase, fun b es => (hz b es).2]
    ext n; simp

private theorem eventSeries_laws {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ c, Nat.card {b : Fin q // R b c} = d) :
    let x : PowerSeries ℚ := PowerSeries.X
    let H := 1 - PowerSeries.C (q - 1 : ℚ) * x
    eventSeries R 0 * H = PowerSeries.C (q : ℚ) * x ∧
    eventSeries R 1 * H ^ 2 = PowerSeries.C (q : ℚ) * x ^ 2 ∧
    ∀ r, eventSeries R (r + 2) * ((1 + x) * H) =
      PowerSeries.C (d : ℚ) * x ^ 2 * eventSeries R (r + 1) := by
  dsimp only
  let x : PowerSeries ℚ := PowerSeries.X
  let Q : PowerSeries ℚ := PowerSeries.C (q : ℚ)
  let D : PowerSeries ℚ := PowerSeries.C (d : ℚ)
  let H := 1 - PowerSeries.C (q - 1 : ℚ) * x
  let V := fun r => fiberSeries R r 1 + fiberSeries R r 2
  have hz := fiberSeries_zero_parts R
  have he r := fiberSeries_equations R hl hd r
  have hzero : eventSeries R 0 = fiberSeries R 0 0 := by
    simp [eventSeries_partition, hz.2.1, hz.2.2]
  have hpos r : eventSeries R (r + 1) = V (r + 1) := by
    simp [eventSeries_partition, hz.1, V]
  have ha r : (1 + x) * fiberSeries R r 1 = D * x * V r := by
    have h := (he r).2.1
    simp only [map_sub, map_one] at h
    dsimp [V, x, D]
    linear_combination h
  have hv r : H * V (r + 1) = x * (fiberSeries R r 0 + fiberSeries R r 1) := by
    have a := (he (r + 1)).2.1
    have b := (he (r + 1)).2.2
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false,
      Nat.add_sub_cancel, map_sub, map_add, map_one] at a b
    dsimp [H, V, x]
    simp only [map_sub, map_one]
    linear_combination a + b
  have hu : eventSeries R 0 * H = Q * x := by
    rw [hzero]
    have h := (he 0).1
    simp only [ite_true] at h
    dsimp [H, Q, x]
    linear_combination h
  refine ⟨hu, ?_, ?_⟩
  · rw [hpos]
    have h := hv 0
    rw [hz.2.1, add_zero, ← hzero] at h
    change V 1 * H ^ 2 = Q * x ^ 2
    calc
      V 1 * H ^ 2 = (H * V 1) * H := by ring
      _ = (x * eventSeries R 0) * H := by rw [h]
      _ = Q * x ^ 2 := by linear_combination x * hu
  · intro r
    rw [show r + 2 = (r + 1) + 1 by omega, hpos, hpos]
    have h := hv (r + 1)
    rw [hz.1, zero_add] at h
    change V (r + 1 + 1) * ((1 + x) * H) = D * x ^ 2 * V (r + 1)
    calc
      V (r + 1 + 1) * ((1 + x) * H) = (1 + x) * (H * V (r + 1 + 1)) := by ring
      _ = (1 + x) * (x * fiberSeries R (r + 1) 1) := by rw [h]
      _ = x * ((1 + x) * fiberSeries R (r + 1) 1) := by ring
      _ = D * x ^ 2 * V (r + 1) := by rw [ha]; ring

private theorem eventSeries_formula {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ c, Nat.card {b : Fin q // R b c} = d) (r : ℕ) :
    eventSeries R (r + 1) = PowerSeries.C ((q : ℚ) * (d : ℚ) ^ r) *
      PowerSeries.X ^ (2 * (r + 1)) *
      ((1 + PowerSeries.X) ^ r *
        (1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X) ^ (r + 2))⁻¹ := by
  let x : PowerSeries ℚ := PowerSeries.X
  let Q : PowerSeries ℚ := PowerSeries.C (q : ℚ)
  let D : PowerSeries ℚ := PowerSeries.C (d : ℚ)
  let H := 1 - PowerSeries.C (q - 1 : ℚ) * x
  have laws := eventSeries_laws R hl hd
  have h r : eventSeries R (r + 1) * ((1 + x) ^ r * H ^ (r + 2)) =
      Q * D ^ r * x ^ (2 * (r + 1)) := by
    induction r with
    | zero => simpa [x, Q, H] using laws.2.1
    | succ r ih =>
      calc
        eventSeries R (r + 1 + 1) * ((1 + x) ^ (r + 1) * H ^ (r + 1 + 2)) =
          (eventSeries R (r + 2) * ((1 + x) * H)) * ((1 + x) ^ r * H ^ (r + 2)) := by
            rw [show r + 1 + 2 = (r + 2) + 1 by omega, pow_succ, pow_succ]
            ring
        _ = (D * x ^ 2 * eventSeries R (r + 1)) * ((1 + x) ^ r * H ^ (r + 2)) := by
          rw [laws.2.2 r]
        _ = D * x ^ 2 * (eventSeries R (r + 1) * ((1 + x) ^ r * H ^ (r + 2))) := by ring
        _ = D * x ^ 2 * (Q * D ^ r * x ^ (2 * (r + 1))) := by rw [ih]
        _ = Q * D ^ (r + 1) * x ^ (2 * (r + 1 + 1)) := by
          rw [pow_succ, show 2 * (r + 1 + 1) = 2 * (r + 1) + 2 by omega, pow_add]
          ring
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
    PowerSeries.constantCoeff ((1 + PowerSeries.X) ^ r *
      (1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X) ^ (r + 2)) ≠ 0)).2
  simpa only [map_mul, map_pow, x, Q, D, H] using h r


/-- Eventful words marked by y: the coefficient of y^(r+1) is their literal x-series. -/
def markedSeries {q : ℕ} (R : Fin q → Fin q → Prop) : PowerSeries (PowerSeries ℚ) :=
  PowerSeries.X * PowerSeries.mk (fun r => eventSeries R (r + 1))

private theorem markedSeries_formula {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ c, Nat.card {b : Fin q // R b c} = d) :
    let x : PowerSeries ℚ := PowerSeries.X
    let y : PowerSeries (PowerSeries ℚ) := PowerSeries.X
    let H := 1 - PowerSeries.C (q - 1 : ℚ) * x
    markedSeries R = y * PowerSeries.C (x * (1 + x) * eventSeries R 0) *
      Ring.inverse (PowerSeries.C ((1 + x) * H) -
        y * PowerSeries.C (PowerSeries.C (d : ℚ) * x ^ 2)) := by
  dsimp only
  let x : PowerSeries ℚ := PowerSeries.X
  let H := 1 - PowerSeries.C (q - 1 : ℚ) * x
  let D : PowerSeries ℚ := PowerSeries.C (d : ℚ)
  let Z : PowerSeries (PowerSeries ℚ) :=
    PowerSeries.C ((1 + x) * H) - PowerSeries.X * PowerSeries.C (D * x ^ 2)
  have hz : IsUnit Z := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp only [Z, map_sub, PowerSeries.constantCoeff_C, map_mul,
      PowerSeries.constantCoeff_X, zero_mul, sub_zero]
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp [H, x]
  have laws := eventSeries_laws R hl hd
  have hh : H ≠ 0 := by
    intro h
    have := congrArg PowerSeries.constantCoeff h
    simp [H, x] at this
  have hfirst : eventSeries R 1 * H = x * eventSeries R 0 := by
    apply mul_right_cancel₀ hh
    linear_combination laws.2.1 - x * laws.1
  apply (Ring.eq_mul_inverse_iff_mul_eq _ _ Z hz).2
  change markedSeries R * Z = PowerSeries.X * PowerSeries.C (x * (1 + x) * eventSeries R 0)
  rw [mul_sub, show markedSeries R * (PowerSeries.X * PowerSeries.C (D * x ^ 2)) =
    PowerSeries.X * (markedSeries R * PowerSeries.C (D * x ^ 2)) by ring]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [markedSeries]
  | succ n =>
    cases n with
    | zero =>
      simp only [markedSeries, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_X,
        PowerSeries.coeff_zero_X_mul, zero_mul, sub_zero,
        PowerSeries.coeff_C, ite_true, one_mul]
      change eventSeries R 1 * ((1 + x) * H) = x * (1 + x) * eventSeries R 0
      linear_combination (1 + x) * hfirst
    | succ n =>
      simp only [markedSeries, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_mk, map_sub, PowerSeries.coeff_X,
        PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, zero_mul]
      have h := laws.2.2 n
      dsimp [D, H, x] at h ⊢
      linear_combination h

private theorem eventCount_coeff {q : ℕ} (R : Fin q → Fin q → Prop) (r n : ℕ) :
    (eventCount R n (r + 1) : ℚ) = PowerSeries.coeff n (eventSeries R (r + 1)) := by
  cases n with
  | zero => simp [eventCount, Admissible, eventLabels, eventSeries, Nat.card_eq_fintype_card]
  | succ n => simp only [eventSeries, PowerSeries.coeff_mk, Nat.succ_ne_zero, ite_false]

/-- Complete exact-event enumeration of actual words, including degenerate indegree zero.
The event number is r+1 so r=0 retains d^0=1. The last identity is in Q[[x]][[y]]. -/
theorem event_enumeration {q d : ℕ} (R : Fin q → Fin q → Prop)
    (hl : ∀ a, ¬ R a a) (hd : ∀ c, Nat.card {b : Fin q // R b c} = d) :
    (eventCount R 0 0 = 1 ∧ ∀ r, eventCount R 0 (r + 1) = 0) ∧
    eventSeries R 0 = PowerSeries.C (q : ℚ) * PowerSeries.X *
      (1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X)⁻¹ ∧
    (∀ r, eventSeries R (r + 1) = PowerSeries.C ((q : ℚ) * (d : ℚ) ^ r) *
      PowerSeries.X ^ (2 * (r + 1)) *
      ((1 + PowerSeries.X) ^ r *
        (1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X) ^ (r + 2))⁻¹) ∧
    (∀ r n, (eventCount R n (r + 1) : ℚ) = PowerSeries.coeff n
      (PowerSeries.C ((q : ℚ) * (d : ℚ) ^ r) * PowerSeries.X ^ (2 * (r + 1)) *
      ((1 + PowerSeries.X) ^ r *
        (1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X) ^ (r + 2))⁻¹)) ∧
    (∀ r n, n < 2 * (r + 1) → eventCount R n (r + 1) = 0) ∧
    (∀ r, eventCount R (2 * (r + 1)) (r + 1) = q * d ^ r) ∧
    (let x : PowerSeries ℚ := PowerSeries.X
     let y : PowerSeries (PowerSeries ℚ) := PowerSeries.X
     let H := 1 - PowerSeries.C (q - 1 : ℚ) * x
     markedSeries R = y * PowerSeries.C (x * (1 + x) * eventSeries R 0) *
      Ring.inverse (PowerSeries.C ((1 + x) * H) -
        y * PowerSeries.C (PowerSeries.C (d : ℚ) * x ^ 2))) := by
  have hc r n := (eventCount_coeff R r n).trans
    (congrArg (PowerSeries.coeff n) (eventSeries_formula R hl hd r))
  refine ⟨?_, ?_, eventSeries_formula R hl hd, hc, ?_, ?_, markedSeries_formula R hl hd⟩
  · constructor
    · simp [eventCount, Admissible, eventLabels, Nat.card_eq_fintype_card]
    · intro r
      have h := eventCount_coeff R r 0
      simpa [eventSeries] using h
  · apply (PowerSeries.eq_mul_inv_iff_mul_eq (by simp :
      PowerSeries.constantCoeff (1 - PowerSeries.C (q - 1 : ℚ) * PowerSeries.X) ≠ 0)).2
    exact (eventSeries_laws R hl hd).1
  · intro r n hn
    have h := hc r n
    rw [mul_assoc, mul_comm (PowerSeries.X ^ (2 * (r + 1))), ← mul_assoc,
      PowerSeries.coeff_mul_X_pow', ite_eq_right (by omega)] at h
    exact_mod_cast h
  · intro r
    have h := hc r (2 * (r + 1))
    rw [mul_assoc, mul_comm (PowerSeries.X ^ (2 * (r + 1))), ← mul_assoc,
      PowerSeries.coeff_mul_X_pow', ite_eq_left (le_refl _), Nat.sub_self] at h
    have h' : (eventCount R (2 * (r + 1)) (r + 1) : ℚ) = (q : ℚ) * (d : ℚ) ^ r := by
      simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h
    exact_mod_cast h'

/-- Zero is a step -1 and one is a step +1, in the source's signed convention. -/
def binaryStep (a : Fin 2) : ℤ := 2 * (a.val : ℤ) - 1

/-- The number of ones minus the number of zeros of the actual binary list. -/
def signedImbalance (w : List (Fin 2)) : ℤ := (w.map binaryStep).sum

/-- Every actual contiguous sublist, including the empty one, has signed bound two. -/
private def SubstringBound (w : List (Fin 2)) : Prop :=
  ∀ u : List (Fin 2), u.IsInfix w → -2 ≤ signedImbalance u ∧ signedImbalance u ≤ 2

private def strip : List (Fin 2) → ℤ → Prop
  | [], h => 0 ≤ h ∧ h ≤ 2
  | a :: l, h => 0 ≤ h ∧ h ≤ 2 ∧ strip l (h + binaryStep a)

private theorem strip_outside (w : List (Fin 2)) (h : ℤ)
    (hh : h < 0 ∨ 2 < h) : ¬ strip w h := by
  cases w <;> simp only [strip] <;> omega

-- The induction checks the three strip heights against both letters and the first event.
set_option maxHeartbeats 1000000 in
private theorem strip_states (b : Fin 2) (l : List (Fin 2)) :
    (strip (b :: l) 0 ↔ (eventLabels (b :: l)).IsChain (· ≠ ·) ∧
      b = 1 ∧ (eventLabels (b :: l)).head? ≠ some 0) ∧
    (strip (b :: l) 1 ↔ (eventLabels (b :: l)).IsChain (· ≠ ·) ∧
      (eventLabels (b :: l)).head? ≠ some b) ∧
    (strip (b :: l) 2 ↔ (eventLabels (b :: l)).IsChain (· ≠ ·) ∧
      b = 0 ∧ (eventLabels (b :: l)).head? ≠ some 1) := by
  induction l generalizing b with
  | nil => fin_cases b <;> norm_num [strip, binaryStep, eventLabels]
  | cons c cs ih =>
    have ht0 := strip_outside (c :: cs) (-1) (by omega)
    have ht3 := strip_outside (c :: cs) 3 (by omega)
    have hc := ih c
    clear ih
    cases he : eventLabels (c :: cs) with
    | nil =>
      simp only [he] at hc
      simp only [eventLabels_cons, he]
      fin_cases b <;> fin_cases c <;>
        norm_num [strip, binaryStep, eventLabels_cons, prependEvents, he] at hc ht0 ht3 ⊢ <;> tauto
    | cons d ds =>
      simp only [he] at hc
      simp only [eventLabels_cons, he]
      fin_cases b <;> fin_cases c <;> fin_cases d <;>
        norm_num [strip, binaryStep, eventLabels_cons, prependEvents, he,
          List.isChain_cons_cons] at hc ht0 ht3 ⊢ <;> tauto

private theorem imbalance_append (u v : List (Fin 2)) :
    signedImbalance (u ++ v) = signedImbalance u + signedImbalance v := by
  simp [signedImbalance]

private theorem strip_append (u v : List (Fin 2)) (h : ℤ) :
    strip (u ++ v) h ↔ strip u h ∧ strip v (h + signedImbalance u) := by
  induction u generalizing h with
  | nil =>
    cases v <;> simp [strip, signedImbalance] <;> tauto
  | cons a u ih =>
    simp only [List.cons_append, strip, ih, signedImbalance, List.map_cons,
      List.sum_cons, and_assoc, add_assoc]

private theorem strip_iff_prefix (w : List (Fin 2)) (h : ℤ) :
    strip w h ↔ ∀ k : ℕ,
      0 ≤ h + signedImbalance (w.take k) ∧ h + signedImbalance (w.take k) ≤ 2 := by
  induction w generalizing h with
  | nil => simp [strip, signedImbalance]
  | cons a w ih =>
    constructor
    · rintro ⟨h0, h2, hw⟩ k
      cases k with
      | zero => simpa [signedImbalance] using And.intro h0 h2
      | succ k =>
        simpa [signedImbalance, add_assoc] using (ih (h + binaryStep a)).mp hw k
    · intro hp
      have hz := hp 0
      simp only [List.take_zero, signedImbalance, List.map_nil, List.sum_nil,
        add_zero] at hz
      refine ⟨hz.1, hz.2, (ih _).mpr ?_⟩
      intro k
      simpa [signedImbalance, add_assoc] using hp (k + 1)

private theorem strip_to_substrings (w : List (Fin 2)) (h : ℤ)
    (hw : strip w h) : SubstringBound w := by
  rintro u ⟨a, b, rfl⟩
  rw [List.append_assoc] at hw
  have ha := ((strip_append a (u ++ b) h).mp hw).1
  have hu := ((strip_append u b (h + signedImbalance a)).mp
    ((strip_append a (u ++ b) h).mp hw).2).1
  have hi := (strip_iff_prefix a h).mp ha a.length
  have hj := (strip_iff_prefix u (h + signedImbalance a)).mp hu u.length
  simp only [List.take_length] at hi hj
  omega

private theorem prefix_difference (w : List (Fin 2)) (hw : SubstringBound w)
    (i j : ℕ) :
    -2 ≤ signedImbalance (w.take j) - signedImbalance (w.take i) ∧
      signedImbalance (w.take j) - signedImbalance (w.take i) ≤ 2 := by
  have ordered (i j : ℕ) (hij : i ≤ j) :
      -2 ≤ signedImbalance (w.take j) - signedImbalance (w.take i) ∧
        signedImbalance (w.take j) - signedImbalance (w.take i) ≤ 2 := by
    obtain ⟨u, hu⟩ := List.take_prefix_take_left (l := w) hij
    have hin : u.IsInfix w := by
      refine ⟨w.take i, w.drop j, ?_⟩
      rw [hu, List.take_append_drop]
    have hb := hw u hin
    have he := congrArg signedImbalance hu
    rw [imbalance_append] at he
    omega
  rcases le_total i j with hij | hji
  · exact ordered i j hij
  · have h := ordered j i hji
    omega

private theorem substrings_to_strip (w : List (Fin 2)) (hw : SubstringBound w) :
    ∃ h : ℤ, strip w h := by
  classical
  obtain ⟨i, _, hi⟩ := (Finset.univ : Finset (Fin (w.length + 1))).exists_min_image
    (fun j => signedImbalance (w.take j.val)) (by simp)
  refine ⟨-signedImbalance (w.take i.val), (strip_iff_prefix _ _).mpr ?_⟩
  intro k
  have hmin := hi ⟨min k w.length, by omega⟩ (Finset.mem_univ _)
  have ht : w.take (min k w.length) = w.take k := by
    rcases le_total k w.length with hk | hk
    · rw [Nat.min_eq_left hk]
    · rw [Nat.min_eq_right hk, List.take_length, List.take_of_length_le hk]
  simp only [ht] at hmin
  have hmax := (prefix_difference w hw i.val k).2
  omega

private theorem events_iff_strip (w : List (Fin 2)) :
    (eventLabels w).IsChain (· ≠ ·) ↔ ∃ h : ℤ, strip w h := by
  cases w with
  | nil => simp [eventLabels, strip]; exact ⟨0, by omega, by omega⟩
  | cons b l =>
    have hs := strip_states b l
    constructor
    · intro he
      cases ht : (eventLabels (b :: l)).head? with
      | none =>
        refine ⟨1, hs.2.1.mpr ⟨he, ?_⟩⟩
        simp [ht]
      | some c =>
        by_cases hcb : c = b
        · subst c
          fin_cases b
          · refine ⟨2, hs.2.2.mpr ⟨he, rfl, ?_⟩⟩
            change (eventLabels (0 :: l)).head? = some 0 at ht
            change (eventLabels (0 :: l)).head? ≠ some 1
            rw [ht]; decide
          · refine ⟨0, hs.1.mpr ⟨he, rfl, ?_⟩⟩
            change (eventLabels (1 :: l)).head? = some 1 at ht
            change (eventLabels (1 :: l)).head? ≠ some 0
            rw [ht]; decide
        · refine ⟨1, hs.2.1.mpr ⟨he, ?_⟩⟩
          simpa [ht] using hcb
    · rintro ⟨h, hh⟩
      have hh' : 0 ≤ h ∧ h ≤ 2 := ⟨hh.1, hh.2.1⟩
      have hc : h = 0 ∨ h = 1 ∨ h = 2 := by omega
      rcases hc with rfl | rfl | rfl
      · exact (hs.1.mp hh).1
      · exact (hs.2.1.mp hh).1
      · exact (hs.2.2.mp hh).1

private theorem imbalance_counts (w : List (Fin 2)) :
    signedImbalance w = (w.count 1 : ℤ) - (w.count 0 : ℤ) := by
  induction w with
  | nil => simp [signedImbalance]
  | cons a w ih =>
    change binaryStep a + signedImbalance w = _
    rw [ih]
    fin_cases a <;> simp [binaryStep, List.count_cons] <;> omega

/-- Every finite binary word satisfies the original overlapping event-label rule exactly
when every actual contiguous substring has ones-minus-zeros between -2 and 2. -/
theorem binary_substring_equivalence (w : List (Fin 2)) :
    (eventLabels w).IsChain (fun a b => b.val = (a.val + 1) % 2) ↔
      ∀ u : List (Fin 2), u.IsInfix w →
        -2 ≤ (u.count 1 : ℤ) - (u.count 0 : ℤ) ∧
          (u.count 1 : ℤ) - (u.count 0 : ℤ) ≤ 2 := by
  have hrel : (fun a b : Fin 2 => b.val = (a.val + 1) % 2) = (· ≠ ·) := by
    funext a b
    fin_cases a <;> fin_cases b <;> simp
  simp_rw [← imbalance_counts]
  change (eventLabels w).IsChain _ ↔ SubstringBound w
  rw [hrel, events_iff_strip]
  exact ⟨fun ⟨h, hh⟩ => strip_to_substrings w h hh, substrings_to_strip w⟩

end D5.S1.Words.Patterns.BarkerRegularRelationCounting
