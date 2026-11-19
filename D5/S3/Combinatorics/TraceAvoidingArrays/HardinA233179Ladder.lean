/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233179Ladder.finite_certificate
   digest: Hardin's order-24 recurrence for the literal normalized six-row complementary-pair ladder. -/
/-
admission_basis: open-problem-resolution (#28655; Proved)
escape_witness: none; frozen canonical counting and four-row classification, existing
  unfrozen transfer theorems, and finite/arithmetic normalization supply the result.
normal: proof_shape=bind-only; consumers=instDecidableNormal, Legal, normal_iff
Legal: proof_shape=bind-only; consumers=instDecidableLegal, a
instDecidableNormal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=literal_card, result
cellOrder: proof_shape=bind-only; consumers=RowNormal, Canon
RowNormal: proof_shape=bind-only; consumers=normal_iff
Canon: proof_shape=bind-only; consumers=canonical_two_card
row_major_lt: proof_shape=bind-only; consumers=normal_iff
normal_iff: proof_shape=bind-only; consumers=legal_iff
legal_iff: proof_shape=bind-only; consumers=literal_card
literal_card: proof_shape=bind-only; consumers=a_sum
used: proof_shape=bind-only; consumers=used_two_or_three, weighted_count
used_eq_card: proof_shape=bind-only; consumers=used_two_or_three, alternating_used
proper_relabel: proof_shape=bind-only; consumers=L_card
proper_two_labels: proof_shape=bind-only; consumers=used_two_or_three, L_card
alternating: proof_shape=bind-only; consumers=canonical_two_card
alternating_proper: proof_shape=bind-only; consumers=canonical_two_card
two_label_classification: proof_shape=bind-only; consumers=canon_two_eq
used_two_or_three: proof_shape=bind-only; consumers=weighted_count
omitted_label: proof_shape=bind-only; consumers=canon_two_eq
alternating_used: proof_shape=bind-only; consumers=canonical_two_card
alternating_canon: proof_shape=bind-only; consumers=canonical_two_card
canon_two_eq: proof_shape=bind-only; consumers=canonical_two_card
CanonicalPatterns: proof_shape=bind-only; consumers=weighted_count
canonical_two_card: proof_shape=bind-only; consumers=weighted_count
a_sum: proof_shape=bind-only; consumers=weighted_count
L_card: proof_shape=bind-only; consumers=counting_bridge
weighted_count: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=bind-only; consumers=scale_recurrence
scale_recurrence: proof_shape=bind-only; consumers=finite_certificate, result
finite_certificate: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Ladder
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177PairTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer

/-! Canonical pair patterns reduce the literal normalization to independent side bits. -/
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder

open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open D5.S3.Combinatorics.TraceAvoidingArrays

def normal {n : ℕ} (A : Fin 6 × Fin n → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 1) ∧
    (A p = 3 →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 2)

def Legal {n : ℕ} (A : Fin 6 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
    (∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 6),
      (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
      A (r, j) ≠ A (s, ⟨j.val + 1, h⟩) ∧
        (A (r, j)).val + (A (s, ⟨j.val + 1, h⟩)).val ≠ 5) ∧ normal A

private instance instDecidableNormal {n : ℕ} (A : Fin 6 × Fin n → Fin 6) :
    Decidable (normal A) := inferInstanceAs (Decidable (∀ _, _ ∧ _))

private instance instDecidableLegal {n : ℕ} (A : Fin 6 × Fin n → Fin 6) :
    Decidable (Legal A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 6 × Fin n → Fin 6 => Legal A)).card

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179PairTransfer (Proper L)
attribute [local irreducible] a L

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin 6 × Fin n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective

private abbrev RowNormal {n : ℕ} (A : Fin 6 × Fin n → Fin 6) :=
  @HardinA233177Canonical.Normal (Fin 6 × Fin n) (cellOrder n).toLT A

private abbrev Canon {n : ℕ} (P : Fin 6 × Fin n → Fin 3) :=
  @HardinA233177Canonical.Canonical (Fin 6 × Fin n) (cellOrder n).toLT 3 P

private theorem row_major_lt {n : ℕ} (p q : Fin 6 × Fin n) :
    @LT.lt (Fin 6 × Fin n) (cellOrder n).toLT p q ↔
      p.1.val * n + p.2.val < q.1.val * n + q.2.val := by
  change p.2.val + n * p.1.val < q.2.val + n * q.1.val ↔ _
  simp only [Nat.add_comm, Nat.mul_comm]

private theorem normal_iff {n : ℕ} (A : Fin 6 × Fin n → Fin 6) :
    normal A ↔ RowNormal A := by
  simp only [normal, RowNormal, HardinA233177Canonical.Normal, row_major_lt]

private theorem legal_iff {n : ℕ} (hn : 0 < n) (A : Fin 6 × Fin n → Fin 6) :
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
    a n = Nat.card {A : Fin 6 × Fin n → Fin 6 //
      Proper (beta ∘ A) ∧ A (0, ⟨0, hn⟩) = 0 ∧ RowNormal A} := by
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, legal_iff hn]

private noncomputable def used {n : ℕ} (P : Fin 6 × Fin n → Fin 3) : ℕ :=
  Nat.card (Set.range P)

private theorem used_eq_card {n : ℕ} (P : Fin 6 × Fin n → Fin 3) :
    used P = (Finset.univ.image P).card := by
  have he : Set.range P = (↑(Finset.univ.image P) : Set (Fin 3)) := by
    ext x
    simp
  rw [used, he, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private theorem proper_relabel {n : ℕ} (e : Equiv.Perm (Fin 3))
    (P : Fin 6 × Fin n → Fin 3) : Proper (e ∘ P) ↔ Proper P := by
  simp only [Proper, Function.comp_apply, e.injective.ne_iff]

private theorem proper_two_labels {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 6 × Fin n → Fin 3) (hp : Proper P) : ∃ i j, P i ≠ P j := by
  exact ⟨(0, ⟨0, by omega⟩), (0, ⟨1, by omega⟩),
    hp ⟨0, by omega⟩ (by change 0 + 1 < n; omega) 0 0 (by decide)⟩

private def alternating (n : ℕ) (a b : Fin 3) : Fin 6 × Fin n → Fin 3 :=
  fun p => if p.2.val % 2 = 0 then a else b

private theorem alternating_proper (n : ℕ) (a b : Fin 3) (hab : a ≠ b) :
    Proper (alternating n a b) := by
  intro j hj r s _
  dsimp [alternating]
  have hpar : (j.val + 1) % 2 = 0 ↔ ¬ j.val % 2 = 0 := by omega
  by_cases h : j.val % 2 = 0 <;> simp [h, hpar, hab, Ne.symm hab]

private theorem two_label_classification {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 6 × Fin n → Fin 3) (hp : Proper P)
    (d : Fin 3) (hd : ∀ i, P i ≠ d) :
    ∃ a b : Fin 3, a ≠ b ∧ P = alternating n a b := by
  let upper : Fin 4 × Fin n → Fin 3 := fun p => P (⟨p.1.val, by omega⟩, p.2)
  let lower : Fin 4 × Fin n → Fin 3 := fun p => P (⟨p.1.val + 2, by omega⟩, p.2)
  have hu : HardinA233177PairTransfer.Proper upper := by
    intro j hj r s hrs
    exact hp j hj ⟨r.val, by omega⟩ ⟨s.val, by omega⟩ hrs
  have hl : HardinA233177PairTransfer.Proper lower := by
    intro j hj r s hrs
    exact hp j hj ⟨r.val + 2, by omega⟩ ⟨s.val + 2, by omega⟩
      (by dsimp; omega)
  obtain ⟨a, b, hab, hu⟩ := HardinA233177Ladder.two_label_classification hn upper hu d
    (fun p => hd (⟨p.1.val, by omega⟩, p.2))
  obtain ⟨c, e, _, hl⟩ := HardinA233177Ladder.two_label_classification hn lower hl d
    (fun p => hd (⟨p.1.val + 2, by omega⟩, p.2))
  have hac : a = c := by
    have h0 := congrFun hu (2, ⟨0, by omega⟩)
    have h1 := congrFun hl (0, ⟨0, by omega⟩)
    exact h0.symm.trans h1
  have hbe : b = e := by
    have h0 := congrFun hu (2, ⟨1, by omega⟩)
    have h1 := congrFun hl (0, ⟨1, by omega⟩)
    exact h0.symm.trans h1
  subst c
  subst e
  refine ⟨a, b, hab, ?_⟩
  funext p
  rcases p with ⟨r, j⟩
  by_cases hr : r.val < 4
  · exact congrFun hu (⟨r.val, hr⟩, j)
  · have hr2 : r.val - 2 < 4 := by omega
    have hrow : (⟨r.val - 2 + 2, by omega⟩ : Fin 6) = r := Fin.ext (by dsimp; omega)
    have h := congrFun hl (⟨r.val - 2, hr2⟩, j)
    change P (⟨r.val - 2 + 2, _⟩, j) = alternating n a b (r, j) at h
    simpa only [hrow] using h

private theorem used_two_or_three {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 6 × Fin n → Fin 3) (hp : Proper P) : used P = 2 ∨ used P = 3 := by
  classical
  obtain ⟨i, j, hij⟩ := proper_two_labels hn P hp
  have hpair : ({P i, P j} : Finset (Fin 3)) ⊆ Finset.univ.image P := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hl : 2 ≤ used P := by
    simpa [used_eq_card, hij] using Finset.card_le_card hpair
  have hu : used P ≤ 3 := by
    rw [used_eq_card]
    simpa using Finset.card_le_card (Finset.subset_univ (Finset.univ.image P))
  omega

private theorem omitted_label {n : ℕ} (P : Fin 6 × Fin n → Fin 3)
    (h : used P = 2) : ∃ d, ∀ i, P i ≠ d := by
  classical
  by_contra hn
  push Not at hn
  have hr : Set.range P = Set.univ := Set.range_eq_univ.mpr hn
  have : used P = 3 := by simp [used, hr]
  omega

private theorem alternating_used {n : ℕ} (hn : 2 ≤ n) (a b : Fin 3) (hab : a ≠ b) :
    used (alternating n a b) = 2 := by
  classical
  have hr : Finset.univ.image (alternating n a b) = ({a, b} : Finset (Fin 3)) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨p, rfl⟩
      dsimp [alternating]
      split_ifs <;> simp
    · rintro (rfl | rfl)
      · exact ⟨(0, ⟨0, by omega⟩), by simp [alternating]⟩
      · exact ⟨(0, ⟨1, by omega⟩), by simp [alternating]⟩
  rw [used_eq_card, hr]
  simp [hab]

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
    (P : Fin 6 × Fin n → Fin 3) (hp : Proper P) (hc : Canon P) (hu : used P = 2) :
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
      let z : Fin 6 × Fin n := (0, ⟨0, by omega⟩)
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
  {P : Fin 6 × Fin n → Fin 3 // Proper P ∧ Canon P}

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
    a n = ∑ P : CanonicalPatterns n, 2 ^ (6 * n - used P.val) := by
  classical
  let z : Fin 6 × Fin n := (0, ⟨0, by omega⟩)
  have hz : ∀ i, @LE.le (Fin 6 × Fin n) (cellOrder n).toLE z i := by
    intro i
    change 0 ≤ i.2.val + n * i.1.val
    omega
  rw [literal_card (by omega)]
  have h := @HardinA233177Canonical.normalized_card (Fin 6 × Fin n)
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
  have h := @HardinA233177Canonical.canonical_pattern_card (Fin 6 × Fin n)
    inferInstance (cellOrder n) Proper proper_relabel (proper_two_labels hn)
  simpa only [L, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

private theorem weighted_count {n : ℕ} (hn : 2 ≤ n) :
    a n = 2 ^ (6 * n - 3) * (Nat.card (CanonicalPatterns n) + 1) := by
  classical
  let w := 2 ^ (6 * n - 3)
  have h2 : 2 ^ (6 * n - 2) = 2 * w := by
    have he : 6 * n - 2 = (6 * n - 3) + 1 := by omega
    rw [he, pow_succ]
    exact Nat.mul_comm _ _
  have summand (P : CanonicalPatterns n) :
      2 ^ (6 * n - used P.val) = w + w * (if used P.val = 2 then 1 else 0) := by
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
    48 * (a n : ℤ) = (64 : ℤ) ^ n * ((L n : ℤ) + 6) := by
  have ha : (a n : ℤ) = (2 : ℤ) ^ (6 * n - 3) *
      ((Nat.card (CanonicalPatterns n) : ℤ) + 1) := by exact_mod_cast weighted_count hn
  have hL : (L n : ℤ) = 6 * (Nat.card (CanonicalPatterns n) : ℤ) := by
    exact_mod_cast L_card hn
  have hp : (64 : ℤ) ^ n = 8 * (2 : ℤ) ^ (6 * n - 3) := by
    calc
      (64 : ℤ) ^ n = (2 : ℤ) ^ (6 * n) := by rw [pow_mul]; norm_num
      _ = 8 * (2 : ℤ) ^ (6 * n - 3) := by
        have he : 6 * n = (6 * n - 3) + 3 := by omega
        rw [he, pow_add]
        norm_num
        ring
  rw [ha, hL, hp]
  ring

private theorem scale_recurrence (m : ℕ) (hm : 2 ≤ m)
    (h : (L (m+24) : ℤ) + 6 =
      7 * ((L (m+23) : ℤ) + 6) + 103 * ((L (m+22) : ℤ) + 6) - 365 * ((L (m+21) : ℤ) + 6) - 2896 *
        ((L (m+20) : ℤ) + 6) + 7168 * ((L (m+19) : ℤ) + 6) + 32291 * ((L (m+18) : ℤ) + 6) - 75471 *
        ((L (m+17) : ℤ) + 6) - 161805 * ((L (m+16) : ℤ) + 6) + 426135 * ((L (m+15) : ℤ) + 6) +
        333692 * ((L (m+14) : ℤ) + 6) - 1225001 * ((L (m+13) : ℤ) + 6) - 155206 * ((L (m+12) : ℤ) +
        6) + 1850161 * ((L (m+11) : ℤ) + 6) - 363389 * ((L (m+10) : ℤ) + 6) - 1524689 * ((L (m+9) :
        ℤ) + 6) + 557502 * ((L (m+8) : ℤ) + 6) + 690388 * ((L (m+7) : ℤ) + 6) - 312941 * ((L (m+6) :
        ℤ) + 6) - 166928 * ((L (m+5) : ℤ) + 6) + 81406 * ((L (m+4) : ℤ) + 6) + 19997 * ((L (m+3) :
        ℤ) + 6) - 9672 * ((L (m+2) : ℤ) + 6) - 906 * ((L (m+1) : ℤ) + 6) + 420 * ((L m : ℤ) + 6)) :
    (a (m+24) : ℤ) =
      448 * (a (m+23) : ℤ) + 421888 * (a (m+22) : ℤ) - 95682560 * (a (m+21) : ℤ) - 48586817536 * (a
        (m+20) : ℤ) + 7696581394432 * (a (m+19) : ℤ) + 2219020623282176 * (a (m+18) : ℤ) -
        331924968239529984 * (a (m+17) : ℤ) - 45544058606667694080 * (a (m+16) : ℤ) +
        7676565708838105251840 * (a (m+15) : ℤ) + 384720682715267981115392 * (a (m+14) : ℤ) -
        90389119748153097756606464 * (a (m+13) : ℤ) - 732939612340266155036901376 * (a (m+12) : ℤ) +
        559176850836005482125888323584 * (a (m+11) : ℤ) - 7028965514623047698676841447424 * (a
        (m+10) : ℤ) - 1887473560557987165955670813966336 * (a (m+9) : ℤ) +
        44169859058027396737075939400220672 * (a (m+8) : ℤ) + 3500683050361467360162023730212503552
        * (a (m+7) : ℤ) - 101555160700421718306247628235154128896 * (a (m+6) : ℤ) -
        3466958920006006825501354764976208740352 * (a (m+5) : ℤ) +
        108207134224866861549607317549181730553856 * (a (m+4) : ℤ) +
        1701156622829501613469275506203267231121408 * (a (m+3) : ℤ) -
        52659376845749069097884147249280994259238912 * (a (m+2) : ℤ) -
        315694924216699133847365011797178367569035264 * (a (m+1) : ℤ) +
        9366312983382861719445001674512311832511774720 * (a m : ℤ) := by
  have hb (i : ℕ) : 48 * (a (m+i) : ℤ) =
      (64 : ℤ)^m * 64^i * ((L (m+i) : ℤ) + 6) := by
    rw [← pow_add]
    exact counting_bridge (by omega)
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  have h3 := hb 3
  have h4 := hb 4
  have h5 := hb 5
  have h6 := hb 6
  have h7 := hb 7
  have h8 := hb 8
  have h9 := hb 9
  have h10 := hb 10
  have h11 := hb 11
  have h12 := hb 12
  have h13 := hb 13
  have h14 := hb 14
  have h15 := hb 15
  have h16 := hb 16
  have h17 := hb 17
  have h18 := hb 18
  have h19 := hb 19
  have h20 := hb 20
  have h21 := hb 21
  have h22 := hb 22
  have h23 := hb 23
  have h24 := hb 24
  norm_num only [Nat.add_zero, pow_zero, pow_one, mul_one] at h0 h1 h2 h3 h4 h5 h6
  norm_num only [Nat.add_zero, pow_zero, pow_one, mul_one] at h7 h8 h9 h10 h11 h12 h13
  norm_num only [Nat.add_zero, pow_zero, pow_one, mul_one] at h14 h15 h16 h17 h18 h19 h20
  norm_num only [Nat.add_zero, pow_zero, pow_one, mul_one] at h21 h22 h23 h24
  apply (mul_left_cancel₀ (show (48 : ℤ) ≠ 0 by norm_num))
  linear_combination h24 - 448 * h23 - 421888 * h22 + 95682560 * h21 + 48586817536 * h20 -
    7696581394432 * h19 - 2219020623282176 * h18 + 331924968239529984 * h17 + 45544058606667694080 *
    h16 - 7676565708838105251840 * h15 - 384720682715267981115392 * h14 + 90389119748153097756606464
    * h13 + 732939612340266155036901376 * h12 - 559176850836005482125888323584 * h11 +
    7028965514623047698676841447424 * h10 + 1887473560557987165955670813966336 * h9 -
    44169859058027396737075939400220672 * h8 - 3500683050361467360162023730212503552 * h7 +
    101555160700421718306247628235154128896 * h6 + 3466958920006006825501354764976208740352 * h5 -
    108207134224866861549607317549181730553856 * h4 - 1701156622829501613469275506203267231121408 *
    h3 + 52659376845749069097884147249280994259238912 * h2 +
    315694924216699133847365011797178367569035264 * h1 -
    9366312983382861719445001674512311832511774720 * h0 + (64 : ℤ)^m *
    22300745198530623141535718272648361505980416 * h
theorem finite_certificate : (a 26 : ℤ) =
    448 * (a (25) : ℤ) + 421888 * (a (24) : ℤ) - 95682560 * (a (23) : ℤ) - 48586817536 * (a (22) :
      ℤ) + 7696581394432 * (a (21) : ℤ) + 2219020623282176 * (a (20) : ℤ) - 331924968239529984 * (a
      (19) : ℤ) - 45544058606667694080 * (a (18) : ℤ) + 7676565708838105251840 * (a (17) : ℤ) +
      384720682715267981115392 * (a (16) : ℤ) - 90389119748153097756606464 * (a (15) : ℤ) -
      732939612340266155036901376 * (a (14) : ℤ) + 559176850836005482125888323584 * (a (13) : ℤ) -
      7028965514623047698676841447424 * (a (12) : ℤ) - 1887473560557987165955670813966336 * (a (11)
      : ℤ) + 44169859058027396737075939400220672 * (a (10) : ℤ) +
      3500683050361467360162023730212503552 * (a (9) : ℤ) - 101555160700421718306247628235154128896
      * (a (8) : ℤ) - 3466958920006006825501354764976208740352 * (a (7) : ℤ) +
      108207134224866861549607317549181730553856 * (a (6) : ℤ) +
      1701156622829501613469275506203267231121408 * (a (5) : ℤ) -
      52659376845749069097884147249280994259238912 * (a (4) : ℤ) -
      315694924216699133847365011797178367569035264 * (a (3) : ℤ) +
      9366312983382861719445001674512311832511774720 * (a (2) : ℤ) := by
  apply scale_recurrence 2 (by decide)
  have h0 := HardinA233179PairTransfer.initial_values 0
  have h1 := HardinA233179PairTransfer.initial_values 1
  have h2 := HardinA233179PairTransfer.initial_values 2
  have h3 := HardinA233179PairTransfer.initial_values 3
  have h4 := HardinA233179PairTransfer.initial_values 4
  have h5 := HardinA233179PairTransfer.initial_values 5
  have h6 := HardinA233179PairTransfer.initial_values 6
  have h7 := HardinA233179PairTransfer.initial_values 7
  have h8 := HardinA233179PairTransfer.initial_values 8
  have h9 := HardinA233179PairTransfer.initial_values 9
  have h10 := HardinA233179PairTransfer.initial_values 10
  have h11 := HardinA233179PairTransfer.initial_values 11
  have h12 := HardinA233179PairTransfer.initial_values 12
  have h13 := HardinA233179PairTransfer.initial_values 13
  have h14 := HardinA233179PairTransfer.initial_values 14
  have h15 := HardinA233179PairTransfer.initial_values 15
  have h16 := HardinA233179PairTransfer.initial_values 16
  have h17 := HardinA233179PairTransfer.initial_values 17
  have h18 := HardinA233179PairTransfer.initial_values 18
  have h19 := HardinA233179PairTransfer.initial_values 19
  have h20 := HardinA233179PairTransfer.initial_values 20
  have h21 := HardinA233179PairTransfer.initial_values 21
  have h22 := HardinA233179PairTransfer.initial_values 22
  have h23 := HardinA233179PairTransfer.initial_values 23
  have h24 := HardinA233179PairTransfer.initial_values 24
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  norm_num at h8 h9 h10 h11 h12 h13 h14 h15
  norm_num at h16 h17 h18 h19 h20 h21 h22 h23
  norm_num at h24
  norm_num
  omega
theorem result (n : ℕ) : (a (n+26) : ℤ) =
    448 * (a (n+25) : ℤ) + 421888 * (a (n+24) : ℤ) - 95682560 * (a (n+23) : ℤ) - 48586817536 * (a
      (n+22) : ℤ) + 7696581394432 * (a (n+21) : ℤ) + 2219020623282176 * (a (n+20) : ℤ) -
      331924968239529984 * (a (n+19) : ℤ) - 45544058606667694080 * (a (n+18) : ℤ) +
      7676565708838105251840 * (a (n+17) : ℤ) + 384720682715267981115392 * (a (n+16) : ℤ) -
      90389119748153097756606464 * (a (n+15) : ℤ) - 732939612340266155036901376 * (a (n+14) : ℤ) +
      559176850836005482125888323584 * (a (n+13) : ℤ) - 7028965514623047698676841447424 * (a (n+12)
      : ℤ) - 1887473560557987165955670813966336 * (a (n+11) : ℤ) +
      44169859058027396737075939400220672 * (a (n+10) : ℤ) + 3500683050361467360162023730212503552 *
      (a (n+9) : ℤ) - 101555160700421718306247628235154128896 * (a (n+8) : ℤ) -
      3466958920006006825501354764976208740352 * (a (n+7) : ℤ) +
      108207134224866861549607317549181730553856 * (a (n+6) : ℤ) +
      1701156622829501613469275506203267231121408 * (a (n+5) : ℤ) -
      52659376845749069097884147249280994259238912 * (a (n+4) : ℤ) -
      315694924216699133847365011797178367569035264 * (a (n+3) : ℤ) +
      9366312983382861719445001674512311832511774720 * (a (n+2) : ℤ) := by
  cases n with
  | zero => exact finite_certificate
  | succ n =>
    have h := scale_recurrence (n+3) (by omega) (by
      simpa only [Nat.add_assoc] using HardinA233179PairTransfer.recurrence n)
    simpa only [Nat.add_assoc] using h
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233179Ladder
