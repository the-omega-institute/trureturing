/- GID: D5/S1/Words/Patterns/BarkerRegularRelationCounting
   generality: I
   mirror-B: D5/B/S1/Words/Patterns/BarkerRegularRelationCounting
   mirror-E: none
   anchors: []
   utility: none
   digest: Literal repetition-word counts for loopless relations of constant indegree. -/

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

end D5.S1.Words.Patterns.BarkerRegularRelationCounting
