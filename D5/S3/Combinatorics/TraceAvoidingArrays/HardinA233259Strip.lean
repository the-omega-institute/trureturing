/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.finite_certificate
   digest: Hardin's order-four recurrence for the literal four-row pair-exclusion arrays. -/
/-
admission_basis: open-problem-resolution (#28807; Proved)
escape_witness: none
Legal: proof_shape=bind-only; consumers=instDecidableLegal, a, legal_iff
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=literal_card, a_sum, counting_bridge, finite_certificate, result
cellOrder: proof_shape=bind-only; consumers=RowNormal, Canon, row_major_lt, a_sum, L_card
RowNormal: proof_shape=bind-only; consumers=normal_iff, legal_iff, literal_card
Canon: proof_shape=bind-only; consumers=alternating_canon, canon_two_eq, CanonicalPatterns
row_major_lt: proof_shape=bind-only; consumers=normal_iff
normal_iff: proof_shape=bind-only; consumers=legal_iff
legal_iff: proof_shape=bind-only; consumers=literal_card
literal_card: proof_shape=bind-only; consumers=a_sum
proper_relabel: proof_shape=bind-only; consumers=L_card
proper_two_labels: proof_shape=bind-only; consumers=used_two_or_three, L_card
columns_constant: proof_shape=bind-only; consumers=two_label_classification
alternating_proper: proof_shape=bind-only; consumers=canonical_two_card
two_label_classification: proof_shape=bind-only; consumers=canon_two_eq
used_two_or_three: proof_shape=bind-only; consumers=weighted_count
omitted_label: proof_shape=bind-only; consumers=canon_two_eq
alternating_used: proof_shape=bind-only; consumers=canonical_two_card
alternating_canon: proof_shape=bind-only; consumers=canonical_two_card
canon_two_eq: proof_shape=bind-only; consumers=canonical_two_card
CanonicalPatterns: proof_shape=bind-only; consumers=canonical_two_card, a_sum, L_card, weighted_count, counting_bridge
canonical_two_card: proof_shape=bind-only; consumers=weighted_count
a_sum: proof_shape=bind-only; consumers=weighted_count
L_card: proof_shape=bind-only; consumers=counting_bridge
weighted_count: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=bind-only; consumers=scale_recurrence, Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip.Bridge.family
scale_recurrence: proof_shape=bind-only; consumers=finite_certificate, result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=external-open-problem-resolution(#28807)
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

/-! Literal normalized colourings and their canonical pair-pattern count. -/
set_option maxRecDepth 100000
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open D5.S3.Combinatorics.TraceAvoidingArrays
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder (normal used alternating)

def Legal {n : ℕ} (A : Fin 4 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
    (∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 4),
      (r = s ∨ r.val + 1 = s.val) →
      A (s, j) ≠ A (r, ⟨j.val + 1, h⟩) ∧
        (A (s, j)).val + (A (r, ⟨j.val + 1, h⟩)).val ≠ 5) ∧ normal A

private instance instDecidableLegal {n : ℕ} (A : Fin 4 × Fin n → Fin 6) :
    Decidable (Legal A) := by
  letI := HardinA233177Ladder.instDecidableNormal A
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 4 × Fin n → Fin 6 => Legal A)).card

open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore (Proper L)
attribute [local irreducible] a L

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin 4 × Fin n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective

private abbrev RowNormal {n : ℕ} (A : Fin 4 × Fin n → Fin 6) :=
  @HardinA233177Canonical.Normal (Fin 4 × Fin n) (cellOrder n).toLT A

private abbrev Canon {n : ℕ} (P : Fin 4 × Fin n → Fin 3) :=
  @HardinA233177Canonical.Canonical (Fin 4 × Fin n) (cellOrder n).toLT 3 P

private theorem row_major_lt {n : ℕ} (p q : Fin 4 × Fin n) :
    @LT.lt (Fin 4 × Fin n) (cellOrder n).toLT p q ↔
      p.1.val * n + p.2.val < q.1.val * n + q.2.val := by
  change p.2.val + n * p.1.val < q.2.val + n * q.1.val ↔ _
  simp only [Nat.add_comm, Nat.mul_comm]

private theorem normal_iff {n : ℕ} (A : Fin 4 × Fin n → Fin 6) :
    normal A ↔ RowNormal A := by
  simp only [normal, RowNormal, HardinA233177Canonical.Normal, row_major_lt]

private theorem legal_iff {n : ℕ} (hn : 0 < n) (A : Fin 4 × Fin n → Fin 6) :
    Legal A ↔ Proper (beta ∘ A) ∧ A (0, ⟨0, hn⟩) = 0 ∧
      RowNormal A := by
  have hfirst : (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ↔
      A (0, ⟨0, hn⟩) = 0 := by
    constructor
    · rintro ⟨j, hj, h⟩
      simpa only [show j = ⟨0, hn⟩ from Fin.ext hj] using h
    · exact fun h => ⟨⟨0, hn⟩, rfl, h⟩
  simp only [Legal, hfirst, normal_iff, Proper, Function.comp_apply,
    HardinA233251TriangleStrip.colour_bond_iff]
  tauto

private theorem literal_card {n : ℕ} (hn : 0 < n) :
    a n = Nat.card {A : Fin 4 × Fin n → Fin 6 //
      Proper (beta ∘ A) ∧ A (0, ⟨0, hn⟩) = 0 ∧ RowNormal A} := by
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, legal_iff hn]

private theorem proper_relabel {n : ℕ} (e : Equiv.Perm (Fin 3))
    (P : Fin 4 × Fin n → Fin 3) : Proper (e ∘ P) ↔ Proper P := by
  simp only [Proper, Function.comp_apply, e.injective.ne_iff]

private theorem proper_two_labels {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 4 × Fin n → Fin 3) (hp : Proper P) : ∃ i j, P i ≠ P j := by
  exact ⟨(0, ⟨0, by omega⟩), (0, ⟨1, by omega⟩),
    hp ⟨0, by omega⟩ (by change 0 + 1 < n; omega) 0 0 (by decide)⟩

private theorem columns_constant {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 4 × Fin n → Fin 3) (hp : Proper P)
    (d : Fin 3) (hd : ∀ i, P i ≠ d) : ∀ j r, P (r, j) = P (0, j) := by
  have finite_fact : ∀ a b c d : Fin 3,
      a ≠ d → b ≠ d → c ≠ d → a ≠ c → b ≠ c → a = b := by decide +kernel
  intro j
  have adjacent (r : Fin 3) : P (r.castSucc, j) = P (r.succ, j) := by
    by_cases hj : j.val + 1 < n
    · let k : Fin n := ⟨j.val + 1, hj⟩
      exact finite_fact _ _ (P (r.castSucc, k)) d (hd _) (hd _) (hd _)
        (hp j hj r.castSucc r.castSucc (Or.inl rfl))
        (hp j hj r.castSucc r.succ (Or.inr (by simp)))
    · have hjpos : 0 < j.val := by have := j.isLt; omega
      let k : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hkn : k.val + 1 < n := by dsimp [k]; omega
      have hkj : (⟨k.val + 1, hkn⟩ : Fin n) = j := by
        apply Fin.ext
        dsimp [k]
        omega
      have h1 := hp k hkn r.succ r.succ (Or.inl rfl)
      have h2 := hp k hkn r.castSucc r.succ (Or.inr (by simp))
      rw [hkj] at h1 h2
      exact finite_fact _ _ (P (r.succ, k)) d (hd _) (hd _) (hd _)
        (Ne.symm h2) (Ne.symm h1)
  intro r
  fin_cases r
  · rfl
  · exact (adjacent 0).symm
  · exact (adjacent 1).symm.trans (adjacent 0).symm
  · exact (adjacent 2).symm.trans ((adjacent 1).symm.trans (adjacent 0).symm)

private theorem alternating_proper (n : ℕ) (a b : Fin 3) (hab : a ≠ b) :
    Proper (alternating n a b) := by
  intro j hj r s _
  change (if j.val % 2 = 0 then a else b) ≠
    (if (j.val + 1) % 2 = 0 then a else b)
  split_ifs <;> first | exact hab | exact hab.symm | omega

private theorem two_label_classification {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 4 × Fin n → Fin 3) (hp : Proper P)
    (d : Fin 3) (hd : ∀ i, P i ≠ d) :
    ∃ a b : Fin 3, a ≠ b ∧ P = alternating n a b := by
  let R : Fin 4 × Fin n → Fin 3 := fun p => P (0, p.2)
  have hR : HardinA233177PairTransfer.Proper R := by
    intro j hj r s _
    exact hp j hj 0 0 (Or.inl rfl)
  obtain ⟨a, b, hab, hRalt⟩ := HardinA233177Ladder.two_label_classification
    hn R hR d (fun p => hd (0, p.2))
  refine ⟨a, b, hab, ?_⟩
  funext p
  have h := congrFun hRalt ((0 : Fin 4), p.2)
  exact (columns_constant hn P hp d hd p.2 p.1).trans h

private theorem used_two_or_three {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 4 × Fin n → Fin 3) (hp : Proper P) : used P = 2 ∨ used P = 3 := by
  obtain ⟨i, j, hij⟩ := proper_two_labels hn P hp
  have hlo : 1 < (Set.range P).ncard :=
    Set.one_lt_ncard_iff_nontrivial.mpr
      ⟨P i, Set.mem_range_self i, P j, Set.mem_range_self j, hij⟩
  have hhi : (Set.range P).ncard ≤ 3 := by
    simpa using Set.ncard_le_card (Set.range P)
  rw [used, Nat.card_coe_set_eq]
  omega

private theorem omitted_label {n : ℕ} (P : Fin 4 × Fin n → Fin 3)
    (h : used P = 2) : ∃ d, ∀ i, P i ≠ d := by
  classical
  by_contra hn
  push Not at hn
  have hr : Set.range P = Set.univ := Set.range_eq_univ.mpr hn
  have : used P = 3 := by simp [used, hr]
  omega

private theorem alternating_used {n : ℕ} (hn : 2 ≤ n) (a b : Fin 3) (hab : a ≠ b) :
    used (alternating n a b) = 2 := by
  have ha : a ∈ Set.range (alternating n a b) :=
    ⟨(0, ⟨0, by omega⟩), by simp [alternating]⟩
  have hb : b ∈ Set.range (alternating n a b) :=
    ⟨(0, ⟨1, by omega⟩), by simp [alternating]⟩
  have hr : Set.range (alternating n a b) = {a, b} := by
    apply Set.Subset.antisymm
    · rintro x ⟨p, rfl⟩
      simp only [alternating]
      split_ifs <;> simp
    · exact Set.insert_subset ha (Set.singleton_subset_iff.mpr hb)
  rw [used, hr, Nat.card_coe_set_eq]
  exact Set.ncard_pair hab

private theorem alternating_canon {n : ℕ} (hn : 0 < n) :
    Canon (alternating n 0 1) := by
  intro p b hb
  change b < (if p.2.val % 2 = 0 then (0 : Fin 3) else 1) at hb
  by_cases hp : p.2.val % 2 = 0
  · simp only [hp, ite_true] at hb
    exact False.elim ((Fin.not_lt_zero _) hb)
  · simp only [hp, ite_false] at hb
    have hb0 : b = 0 := Fin.ext (by change b.val < 1 at hb; omega)
    subst b
    refine ⟨(0, ⟨0, hn⟩), ?_, by simp [alternating]⟩
    change 0 < p.2.val + n * p.1.val
    have hj : 0 < p.2.val := by omega
    omega

private theorem canon_two_eq {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 4 × Fin n → Fin 3) (hp : Proper P) (hc : Canon P) (hu : used P = 2) :
    P = alternating n 0 1 := by
  obtain ⟨d, hd⟩ := omitted_label P hu
  obtain ⟨a, b, hab, rfl⟩ := two_label_classification hn P hp d hd
  have ha : a = 0 := by
    by_contra ha
    have hpos : (0 : Fin 3) < a := Fin.pos_iff_ne_zero.mpr ha
    obtain ⟨q, hq, _⟩ := hc (0, ⟨0, by omega⟩) 0 hpos
    change q.2.val + n * q.1.val < 0 at hq
    omega
  subst a
  have hb : b = 1 := by
    fin_cases b
    · exact False.elim (hab rfl)
    · rfl
    · obtain ⟨q, hq, he⟩ := hc (0, ⟨1, by omega⟩) 1
        (by change (1 : Fin 3) < 2; decide)
      let z : Fin 4 × Fin n := (0, ⟨0, by omega⟩)
      have hqz : q = z := by
        apply finProdFinEquiv.injective
        apply Fin.ext
        change q.2.val + n * q.1.val = 0
        change q.2.val + n * q.1.val < 1 at hq
        omega
      rw [hqz] at he
      norm_num [z, alternating] at he
  subst b
  rfl

private abbrev CanonicalPatterns (n : ℕ) :=
  {P : Fin 4 × Fin n → Fin 3 // Proper P ∧ Canon P}

private theorem canonical_two_card {n : ℕ} (hn : 2 ≤ n) :
    Nat.card {P : CanonicalPatterns n // used P.val = 2} = 1 := by
  classical
  let p : {P : CanonicalPatterns n // used P.val = 2} :=
    ⟨⟨alternating n 0 1, alternating_proper n 0 1 (by decide),
      alternating_canon (by omega)⟩, alternating_used hn 0 1 (by decide)⟩
  let : Unique {P : CanonicalPatterns n // used P.val = 2} := {
    default := p
    uniq := fun q => Subtype.ext (Subtype.ext
      (canon_two_eq hn q.val.val q.val.property.1 q.val.property.2 q.property)) }
  simp only [Nat.card_eq_fintype_card, Fintype.card_unique]

open scoped Classical in
private theorem a_sum {n : ℕ} (hn : 2 ≤ n) :
    a n = ∑ P : CanonicalPatterns n, 2 ^ (4 * n - used P.val) := by
  classical
  let z : Fin 4 × Fin n := (0, ⟨0, by omega⟩)
  have hz : ∀ i, @LE.le (Fin 4 × Fin n) (cellOrder n).toLE z i := by
    intro i
    change 0 ≤ i.2.val + n * i.1.val
    omega
  rw [literal_card (by omega)]
  have h := @HardinA233177Canonical.normalized_card (Fin 4 × Fin n)
    inferInstance (cellOrder n) z hz Proper
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  refine h.trans ?_
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_univ]
  · intro P _
    rfl

private theorem L_card {n : ℕ} (hn : 2 ≤ n) :
    L n = 6 * Nat.card (CanonicalPatterns n) := by
  classical
  have h := @HardinA233177Canonical.canonical_pattern_card (Fin 4 × Fin n)
    inferInstance (cellOrder n) Proper proper_relabel (proper_two_labels hn)
  simpa only [L, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

private theorem weighted_count {n : ℕ} (hn : 2 ≤ n) :
    a n = 2 ^ (4 * n - 3) * (Nat.card (CanonicalPatterns n) + 1) := by
  classical
  let w := 2 ^ (4 * n - 3)
  have h2 : 2 ^ (4 * n - 2) = 2 * w := by
    have he : 4 * n - 2 = (4 * n - 3) + 1 := by omega
    rw [he, pow_succ]
    exact Nat.mul_comm _ _
  have summand (P : CanonicalPatterns n) :
      2 ^ (4 * n - used P.val) = w + w * (if used P.val = 2 then 1 else 0) := by
    rcases used_two_or_three hn P.val P.property.1 with hu | hu
    · simp only [hu, ite_true]
      rw [h2]
      ring
    · have hh : used P.val ≠ 2 := by omega
      simp only [hu, show (3 : ℕ) ≠ 2 from by decide, ite_false, mul_zero, add_zero]
      rfl
  have hcount : (∑ P : CanonicalPatterns n, if used P.val = 2 then (1 : ℕ) else 0) = 1 := by
    simp only [Finset.sum_boole, Nat.cast_id]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using canonical_two_card hn
  rw [a_sum hn]
  simp_rw [summand]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcount]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]
  dsimp [w]
  ring

theorem counting_bridge {n : ℕ} (hn : 2 ≤ n) :
    48 * (a n : ℤ) = (16 : ℤ) ^ n * ((L n : ℤ) + 6) := by
  have ha : (a n : ℤ) = (2 : ℤ) ^ (4 * n - 3) *
      ((Nat.card (CanonicalPatterns n) : ℤ) + 1) := by exact_mod_cast weighted_count hn
  have hL : (L n : ℤ) = 6 * (Nat.card (CanonicalPatterns n) : ℤ) := by
    exact_mod_cast L_card hn
  have hp : (16 : ℤ) ^ n = 8 * (2 : ℤ) ^ (4 * n - 3) := by
    calc
      (16 : ℤ) ^ n = (2 : ℤ) ^ (4 * n) := by rw [pow_mul]; norm_num
      _ = 8 * (2 : ℤ) ^ (4 * n - 3) := by
        have he : 4 * n = (4 * n - 3) + 3 := by omega
        rw [he, pow_add]
        norm_num
        ring
  rw [ha, hL, hp]
  ring

private theorem scale_recurrence (m : ℕ) (hm : 2 ≤ m)
    (h : (L (m + 4) : ℤ) + 6 =
      10 * ((L (m + 3) : ℤ) + 6) - 24 * ((L (m + 2) : ℤ) + 6) +
        21 * ((L (m + 1) : ℤ) + 6) - 6 * ((L m : ℤ) + 6)) :
    (a (m + 4) : ℤ) =
      160 * (a (m + 3) : ℤ) - 6144 * (a (m + 2) : ℤ) +
        86016 * (a (m + 1) : ℤ) - 393216 * (a m : ℤ) := by
  have hb (i : ℕ) : 48 * (a (m+i) : ℤ) =
      (16 : ℤ)^m * 16^i * ((L (m+i) : ℤ) + 6) := by
    rw [← pow_add]
    exact counting_bridge (by omega)
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  norm_num only [Nat.add_zero, pow_zero, pow_one, mul_one] at h0 h1 h2 h3 h4
  apply (mul_left_cancel₀ (show (48 : ℤ) ≠ 0 by norm_num))
  linear_combination h4 - 160*h3 + 6144*h2 - 86016*h1 + 393216*h0 +
    (16 : ℤ)^m * 65536*h

/-- The finite base case needed at the first permitted recurrence index. -/
theorem finite_certificate : (a 9 : ℤ) =
    160 * (a 8 : ℤ) - 6144 * (a 7 : ℤ) + 86016 * (a 6 : ℤ) -
      393216 * (a 5 : ℤ) := by
  apply scale_recurrence 5 (by decide)
  exact HardinA233259PairTransfer.recurrence 0

/-- Hardin's recurrence with the index shift exposing every predecessor. -/
theorem result (n : ℕ) : (a (n+9) : ℤ) =
    160 * (a (n+8) : ℤ) - 6144 * (a (n+7) : ℤ) +
      86016 * (a (n+6) : ℤ) - 393216 * (a (n+5) : ℤ) := by
  cases n with
  | zero => exact finite_certificate
  | succ n =>
    have h := scale_recurrence (n+6) (by omega)
      (HardinA233259PairTransfer.recurrence (n+1))
    simpa only [Nat.add_assoc] using h

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
