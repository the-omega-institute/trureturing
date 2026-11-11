/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.finite_certificate,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259Strip.counting_bridge,D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233259PairTransferRecurrence.recurrence
   digest: Hardin's order-four recurrence for the literal four-row pair-exclusion arrays. -/
/-
admission_basis: open-problem-resolution (#28807; Proved)
escape_witness: none (bind-only; column constancy reuses HardinA233260Literal.columns_constant through row padding; the recurrence reuses HardinA233259PairTransferRecurrence.recurrence)
Legal: proof_shape=bind-only; consumers=instDecidableLegal, a, legal_iff
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=literal_card, a_sum, counting_bridge, finite_certificate, result
legal_iff: proof_shape=bind-only; consumers=literal_card
literal_card: proof_shape=bind-only; consumers=a_sum
proper_relabel: proof_shape=bind-only; consumers=L_card
proper_two_labels: proof_shape=bind-only; consumers=used_two_or_three, L_card
columns_constant: proof_shape=bind-only; consumers=canon_two_eq
alternating_proper: proof_shape=bind-only; consumers=canonical_two_card
used_two_or_three: proof_shape=bind-only; consumers=weighted_count
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
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferRecurrence
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259PairTransferCore
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal

/-! Literal normalized colourings and their canonical pair-pattern count. -/
set_option maxRecDepth 100000
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open D5.S3.Combinatorics.TraceAvoidingArrays
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
  (normal used alternating cellOrder RowNormal Canon normal_iff omitted_label
    alternating_used alternating_canon)

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
  let row : Fin 5 → Fin 4 := fun r => ⟨min r.val 3, by omega⟩
  let Q : Fin 5 × Fin n → Fin 3 := fun p => P (row p.1, p.2)
  have hQ : HardinA233260Literal.Proper Q := by
    intro j hj r s hrs
    change P (row r, j) ≠ P (row s, ⟨j.val + 1, hj⟩)
    apply hp j hj (row s) (row r)
    by_cases h : row s = row r
    · exact Or.inl h
    · right
      change min s.val 3 + 1 = min r.val 3
      have hne : min s.val 3 ≠ min r.val 3 := fun e => h (Fin.ext e)
      rcases hrs with hrs | hrs
      · exact (h (congrArg row hrs.symm)).elim
      · have hr := r.isLt
        have hs := s.isLt
        omega
  have hcol := HardinA233260Literal.columns_constant hn Q hQ d
    (fun i => hd (row i.1, i.2))
  intro j r
  have h := hcol j r.castSucc
  change P (row r.castSucc, j) = P (row 0, j) at h
  rw [show row r.castSucc = r from Fin.ext (by dsimp [row]; omega),
    show row 0 = 0 from rfl] at h
  exact h

private theorem alternating_proper (n : ℕ) (a b : Fin 3) (hab : a ≠ b) :
    Proper (alternating n a b) := by
  intro j hj r s hrs
  apply HardinA233177Ladder.alternating_proper n a b hab j hj s r
  rcases hrs with h | h
  · subst r
    omega
  · omega

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

private theorem canon_two_eq {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 4 × Fin n → Fin 3) (hp : Proper P) (hc : Canon P) (hu : used P = 2) :
    P = alternating n 0 1 := by
  obtain ⟨d, hd⟩ := omitted_label P hu
  have hcol := columns_constant hn P hp d hd
  have hproper : HardinA233177PairTransfer.Proper P := by
    intro j hj r s _
    rw [hcol j r, hcol ⟨j.val + 1, hj⟩ s]
    exact hp j hj 0 0 (Or.inl rfl)
  exact HardinA233177Ladder.canon_two_eq hn P hproper hc hu

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
  exact HardinA233259PairTransferRecurrence.recurrence 0

section
-- Keep the result source literal while elaborating the legacy spelling to its owner.
local notation "HardinA233259PairTransfer.recurrence" =>
  HardinA233259PairTransferRecurrence.recurrence

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

end

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233259Strip
