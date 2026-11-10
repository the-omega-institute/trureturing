/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Literal five-row antidiagonal arrays and their exact complementary-pair count. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Tactic

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal

open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open D5.S3.Combinatorics.TraceAvoidingArrays

def normal {n : ℕ} (A : Fin 5 × Fin n → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 1) ∧
    (A p = 3 →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 2)

def Legal {n : ℕ} (A : Fin 5 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
    (∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 5),
      (r = s ∨ r.val = s.val + 1) →
      A (r, j) ≠ A (s, ⟨j.val + 1, h⟩) ∧
        (A (r, j)).val + (A (s, ⟨j.val + 1, h⟩)).val ≠ 5) ∧ normal A

private instance instDecidableNormal {n : ℕ} (A : Fin 5 × Fin n → Fin 6) :
    Decidable (normal A) := inferInstanceAs (Decidable (∀ _, _ ∧ _))

private instance instDecidableLegal {n : ℕ} (A : Fin 5 × Fin n → Fin 6) :
    Decidable (Legal A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 5 × Fin n → Fin 6 => Legal A)).card

def Proper {n : ℕ} (P : Fin 5 × Fin n → Fin 3) : Prop :=
  ∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 5),
    (r = s ∨ r.val = s.val + 1) → P (r, j) ≠ P (s, ⟨j.val + 1, h⟩)

private instance instDecidableProper {n : ℕ} (P : Fin 5 × Fin n → Fin 3) :
    Decidable (Proper P) := inferInstanceAs (Decidable (∀ _ _ _ _, _ → _))

def L (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun P : Fin 5 × Fin n → Fin 3 => Proper P)).card

attribute [local irreducible] a L

private abbrev cellOrder (n : ℕ) : LinearOrder (Fin 5 × Fin n) :=
  LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective

private abbrev RowNormal {n : ℕ} (A : Fin 5 × Fin n → Fin 6) :=
  @HardinA233177Canonical.Normal (Fin 5 × Fin n) (cellOrder n).toLT A

private abbrev Canon {n : ℕ} (P : Fin 5 × Fin n → Fin 3) :=
  @HardinA233177Canonical.Canonical (Fin 5 × Fin n) (cellOrder n).toLT 3 P

private theorem row_major_lt {n : ℕ} (p q : Fin 5 × Fin n) :
    @LT.lt (Fin 5 × Fin n) (cellOrder n).toLT p q ↔
      p.1.val * n + p.2.val < q.1.val * n + q.2.val := by
  change p.2.val + n * p.1.val < q.2.val + n * q.1.val ↔ _
  simp only [Nat.add_comm, Nat.mul_comm]

private theorem normal_iff {n : ℕ} (A : Fin 5 × Fin n → Fin 6) :
    normal A ↔ RowNormal A := by
  simp only [normal, RowNormal, HardinA233177Canonical.Normal, row_major_lt]

private theorem legal_iff {n : ℕ} (hn : 0 < n) (A : Fin 5 × Fin n → Fin 6) :
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
    a n = Nat.card {A : Fin 5 × Fin n → Fin 6 //
      Proper (beta ∘ A) ∧ A (0, ⟨0, hn⟩) = 0 ∧ RowNormal A} := by
  classical
  rw [a, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, legal_iff hn]

private noncomputable def used {n : ℕ} (P : Fin 5 × Fin n → Fin 3) : ℕ :=
  Nat.card (Set.range P)

private theorem used_eq_card {n : ℕ} (P : Fin 5 × Fin n → Fin 3) :
    used P = (Finset.univ.image P).card := by
  have he : Set.range P = (↑(Finset.univ.image P) : Set (Fin 3)) := by
    ext x
    simp
  rw [used, he, Nat.card_coe_set_eq, Set.ncard_coe_finset]

private theorem proper_relabel {n : ℕ} (e : Equiv.Perm (Fin 3))
    (P : Fin 5 × Fin n → Fin 3) : Proper (e ∘ P) ↔ Proper P := by
  simp only [Proper, Function.comp_apply, e.injective.ne_iff]

private theorem proper_two_labels {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 5 × Fin n → Fin 3) (hp : Proper P) : ∃ i j, P i ≠ P j := by
  exact ⟨(0, ⟨0, by omega⟩), (0, ⟨1, by omega⟩),
    hp ⟨0, by omega⟩ (by change 0 + 1 < n; omega) 0 0 (by decide)⟩

private theorem columns_constant {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 5 × Fin n → Fin 3) (hp : Proper P)
    (d : Fin 3) (hd : ∀ i, P i ≠ d) : ∀ j r, P (r, j) = P (0, j) := by
  have finite_fact : ∀ a b c d : Fin 3,
      a ≠ d → b ≠ d → c ≠ d → a ≠ c → b ≠ c → a = b := by decide +kernel
  intro j
  have adjacent (r : Fin 4) : P (r.castSucc, j) = P (r.succ, j) := by
    by_cases hj : j.val + 1 < n
    · let k : Fin n := ⟨j.val + 1, hj⟩
      exact finite_fact _ _ (P (r.castSucc, k)) d (hd _) (hd _) (hd _)
        (hp j hj r.castSucc r.castSucc (Or.inl rfl))
        (hp j hj r.succ r.castSucc (Or.inr (by simp)))
    · have hjpos : 0 < j.val := by have := j.isLt; omega
      let k : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
      have hkn : k.val + 1 < n := by dsimp [k]; omega
      have hkj : (⟨k.val + 1, hkn⟩ : Fin n) = j := by
        apply Fin.ext
        dsimp [k]
        omega
      have h1 := hp k hkn r.succ r.castSucc (Or.inr (by simp))
      have h2 := hp k hkn r.succ r.succ (Or.inl rfl)
      rw [hkj] at h1 h2
      exact finite_fact _ _ (P (r.succ, k)) d (hd _) (hd _) (hd _)
        (Ne.symm h1) (Ne.symm h2)
  intro r
  fin_cases r
  · rfl
  · exact (adjacent 0).symm
  · exact (adjacent 1).symm.trans (adjacent 0).symm
  · exact (adjacent 2).symm.trans ((adjacent 1).symm.trans (adjacent 0).symm)
  · exact (adjacent 3).symm.trans ((adjacent 2).symm.trans ((adjacent 1).symm.trans (adjacent 0).symm))

private def alternating (n : ℕ) (a b : Fin 3) : Fin 5 × Fin n → Fin 3 :=
  fun p => if p.2.val % 2 = 0 then a else b

private theorem alternating_proper (n : ℕ) (a b : Fin 3) (hab : a ≠ b) :
    Proper (alternating n a b) := by
  intro j hj r s _
  dsimp [alternating]
  have hpar : (j.val + 1) % 2 = 0 ↔ ¬ j.val % 2 = 0 := by omega
  by_cases h : j.val % 2 = 0 <;> simp [h, hpar, hab, Ne.symm hab]

private theorem two_label_classification {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 5 × Fin n → Fin 3) (hp : Proper P)
    (d : Fin 3) (hd : ∀ i, P i ≠ d) :
    ∃ a b : Fin 3, a ≠ b ∧ P = alternating n a b := by
  let a := P (0, ⟨0, by omega⟩)
  let b := P (0, ⟨1, by omega⟩)
  have hab : a ≠ b := hp ⟨0, by omega⟩ (by change 0 + 1 < n; omega) 0 0 (by decide)
  have ha : a ≠ d := hd _
  have hb : b ≠ d := hd _
  have row_zero : ∀ k (hk : k < n),
      P (0, ⟨k, hk⟩) = if k % 2 = 0 then a else b := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hstep := hp ⟨k, hk'⟩ hk 0 0 (by decide)
      have hpar : (k + 1) % 2 = 0 ↔ ¬ k % 2 = 0 := by omega
      have finite_fact : ∀ a b c d : Fin 3,
          a ≠ d → b ≠ d → c ≠ d → a ≠ c → b ≠ c → a = b := by decide +kernel
      by_cases hj : k % 2 = 0
      · have hcur : P (0, ⟨k, hk'⟩) = a := by simpa [hj] using ih hk'
        rw [hcur] at hstep
        simpa [hpar, hj] using finite_fact (P (0, ⟨k + 1, hk⟩)) b a d
          (hd _) hb ha (Ne.symm hstep) (Ne.symm hab)
      · have hcur : P (0, ⟨k, hk'⟩) = b := by simpa [hj] using ih hk'
        rw [hcur] at hstep
        simpa [hpar, hj] using finite_fact (P (0, ⟨k + 1, hk⟩)) a b d
          (hd _) ha hb (Ne.symm hstep) hab
  refine ⟨a, b, hab, ?_⟩
  funext p
  exact (columns_constant hn P hp d hd p.2 p.1).trans (row_zero p.2.val p.2.isLt)

private theorem used_two_or_three {n : ℕ} (hn : 2 ≤ n)
    (P : Fin 5 × Fin n → Fin 3) (hp : Proper P) : used P = 2 ∨ used P = 3 := by
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

private theorem omitted_label {n : ℕ} (P : Fin 5 × Fin n → Fin 3)
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
    (P : Fin 5 × Fin n → Fin 3) (hp : Proper P) (hc : Canon P) (hu : used P = 2) :
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
      let z : Fin 5 × Fin n := (0, ⟨0, by omega⟩)
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
  {P : Fin 5 × Fin n → Fin 3 // Proper P ∧ Canon P}

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
    a n = ∑ P : CanonicalPatterns n, 2 ^ (5 * n - used P.val) := by
  classical
  let z : Fin 5 × Fin n := (0, ⟨0, by omega⟩)
  have hz : ∀ i, @LE.le (Fin 5 × Fin n) (cellOrder n).toLE z i := by
    intro i
    change 0 ≤ i.2.val + n * i.1.val
    omega
  rw [literal_card (by omega)]
  have h := @HardinA233177Canonical.normalized_card (Fin 5 × Fin n)
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
  have h := @HardinA233177Canonical.canonical_pattern_card (Fin 5 × Fin n)
    inferInstance (cellOrder n) Proper proper_relabel (proper_two_labels hn)
  simpa only [L, Nat.card_eq_fintype_card, Fintype.card_subtype] using h

private theorem weighted_count {n : ℕ} (hn : 2 ≤ n) :
    a n = 2 ^ (5 * n - 3) * (Nat.card (CanonicalPatterns n) + 1) := by
  classical
  let w := 2 ^ (5 * n - 3)
  have h2 : 2 ^ (5 * n - 2) = 2 * w := by
    have he : 5 * n - 2 = (5 * n - 3) + 1 := by omega
    rw [he, pow_succ]
    exact Nat.mul_comm _ _
  have summand (P : CanonicalPatterns n) :
      2 ^ (5 * n - used P.val) = w + w * (if used P.val = 2 then 1 else 0) := by
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
    48 * (a n : ℤ) = (32 : ℤ) ^ n * ((L n : ℤ) + 6) := by
  have ha : (a n : ℤ) = (2 : ℤ) ^ (5 * n - 3) *
      ((Nat.card (CanonicalPatterns n) : ℤ) + 1) := by exact_mod_cast weighted_count hn
  have hL : (L n : ℤ) = 6 * (Nat.card (CanonicalPatterns n) : ℤ) := by
    exact_mod_cast L_card hn
  have hp : (32 : ℤ) ^ n = 8 * (2 : ℤ) ^ (5 * n - 3) := by
    calc
      (32 : ℤ) ^ n = (2 : ℤ) ^ (5 * n) := by rw [pow_mul]; norm_num
      _ = 8 * (2 : ℤ) ^ (5 * n - 3) := by
        have he : 5 * n = (5 * n - 3) + 3 := by omega
        rw [he, pow_add]
        norm_num
        ring
  rw [ha, hL, hp]
  ring

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
