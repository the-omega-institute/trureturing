/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal
   generality: I
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233260Literal.counting_bridge
   digest: Literal five-row antidiagonal arrays and their exact complementary-pair count. -/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.Combinatorics.TraceAvoidingArrays.TransferMatrix

/-! Exact literal normalization and finite column transfer for five-row antidiagonal arrays. -/

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

theorem columns_constant {n : ℕ} (hn : 2 ≤ n)
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


open scoped BigOperators
private abbrev Col := Fin 3 × Fin 3 × Fin 3 × Fin 3 × Fin 3
private def column (c : Col) : Fin 5 → Fin 3 := ![c.1,c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2]
private def compatible (a b : Col) : Prop :=
  column a 0 ≠ column b 0 ∧ column a 1 ≠ column b 1 ∧
  column a 2 ≠ column b 2 ∧ column a 3 ≠ column b 3 ∧ column a 4 ≠ column b 4 ∧
  column a 1 ≠ column b 0 ∧ column a 2 ≠ column b 1 ∧
  column a 3 ≠ column b 2 ∧ column a 4 ≠ column b 3
private instance (a b : Col) : Decidable (compatible a b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
private theorem compatible_iff (a b : Col) : compatible a b ↔
    ∀ r s : Fin 5, (r = s ∨ r.val = s.val + 1) → column a r ≠ column b s := by
  constructor
  · intro h r s hrs
    fin_cases r <;> fin_cases s <;> norm_num at hrs <;> simp_all [compatible]
  · intro h
    exact ⟨h 0 0 (by decide), h 1 1 (by decide), h 2 2 (by decide),
      h 3 3 (by decide), h 4 4 (by decide), h 1 0 (by decide),
      h 2 1 (by decide), h 3 2 (by decide), h 4 3 (by decide)⟩
private def cls (c : Col) : Fin 41 :=
  let index : Fin 243 := ⟨c.1.val + 3*c.2.1.val + 9*c.2.2.1.val +
    27*c.2.2.2.1.val + 81*c.2.2.2.2.val, by
      have := c.1.isLt; have := c.2.1.isLt; have := c.2.2.1.isLt
      have := c.2.2.2.1.isLt; have := c.2.2.2.2.isLt; omega⟩
  ![0, 27, 27, 14, 9, 40, 14, 40, 9, 5, 18, 36, 23, 3, 31, 32, 22, 13, 5, 36, 18, 32, 13, 22, 23, 31, 3, 2, 24, 30, 17, 6, 37, 20, 34, 12, 8, 15, 39, 26, 1, 28, 38, 16, 10, 11, 33, 21, 35, 7, 19, 29, 25, 4, 2, 30, 24, 20, 12, 34, 17, 37, 6, 11, 21, 33, 29, 4, 25, 35, 19, 7, 8, 39, 15, 38, 10, 16, 26, 28, 1, 1, 26, 28, 15, 8, 39, 16, 38, 10, 6, 17, 37, 24, 2, 30, 34, 20, 12, 7, 35, 19, 33, 11, 21, 25, 29, 4, 3, 23, 31, 18, 5, 36, 22, 32, 13, 9, 14, 40, 27, 0, 27, 40, 14, 9, 13, 32, 22, 36, 5, 18, 31, 23, 3, 4, 29, 25, 21, 11, 33, 19, 35, 7, 12, 20, 34, 30, 2, 24, 37, 17, 6, 10, 38, 16, 39, 8, 15, 28, 26, 1, 1, 28, 26, 16, 10, 38, 15, 39, 8, 7, 19, 35, 25, 4, 29, 33, 21, 11, 6, 37, 17, 34, 12, 20, 24, 30, 2, 4, 25, 29, 19, 7, 35, 21, 33, 11, 10, 16, 38, 28, 1, 26, 39, 15, 8, 12, 34, 20, 37, 6, 17, 30, 24, 2, 3, 31, 23, 22, 13, 32, 18, 36, 5, 13, 22, 32, 31, 3, 23, 36, 18, 5, 9, 40, 14, 40, 9, 14, 27, 27, 0] index
private def Q : Matrix (Fin 41) (Fin 41) ℤ := ![
  ![2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
  ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1]]
private def weights : Fin 41 → ℤ := ![96, 96, 48, 96, 48, 48, 24, 24, 48, 96, 48, 24, 24, 48, 48, 24, 24, 12, 24, 12, 12, 12, 24, 48, 24, 24, 48, 96, 48, 24, 24, 48, 24, 12, 12, 12, 24, 12, 24, 24, 48]
private def representatives : Fin 41 → Col := ![(0,0,0,0,0), (0,0,0,0,1), (0,0,0,1,0), (0,0,0,1,1), (0,0,0,1,2), (0,0,1,0,0), (0,0,1,0,1), (0,0,1,0,2), (0,0,1,1,0), (0,0,1,1,1), (0,0,1,1,2), (0,0,1,2,0), (0,0,1,2,1), (0,0,1,2,2), (0,1,0,0,0), (0,1,0,0,1), (0,1,0,0,2), (0,1,0,1,0), (0,1,0,1,1), (0,1,0,1,2), (0,1,0,2,0), (0,1,0,2,1), (0,1,0,2,2), (0,1,1,0,0), (0,1,1,0,1), (0,1,1,0,2), (0,1,1,1,0), (0,1,1,1,1), (0,1,1,1,2), (0,1,1,2,0), (0,1,1,2,1), (0,1,1,2,2), (0,1,2,0,0), (0,1,2,0,1), (0,1,2,0,2), (0,1,2,1,0), (0,1,2,1,1), (0,1,2,1,2), (0,1,2,2,0), (0,1,2,2,1), (0,1,2,2,2)]
private def relabel (e : Equiv.Perm (Fin 3)) : Col ≃ Col :=
  Equiv.prodCongr e (Equiv.prodCongr e (Equiv.prodCongr e (Equiv.prodCongr e e)))
private theorem column_relabel (e : Equiv.Perm (Fin 3)) (c : Col) (r : Fin 5) :
    column (relabel e c) r = e (column c r) := by
  fin_cases r <;> rfl
private theorem compatible_relabel (e : Equiv.Perm (Fin 3)) (a b : Col) :
    compatible (relabel e a) (relabel e b) ↔ compatible a b := by
  simp only [compatible, column_relabel, e.injective.ne_iff]
set_option maxRecDepth 100000 in
private theorem class_relabel : ∀ e : Equiv.Perm (Fin 3), ∀ c : Col,
    cls (relabel e c) = cls c := by decide +kernel
set_option maxRecDepth 100000 in
private theorem class_rep : ∀ c : Col, ∃ e : Equiv.Perm (Fin 3),
    relabel e c = representatives (cls c) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem representative_rows : ∀ i s : Fin 41,
    (∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0) =
      Q i s := by
  have h : List.ofFn (fun i : Fin 41 => List.ofFn (fun s : Fin 41 =>
      ∑ c : Col, if compatible (representatives i) c ∧ cls c = s then (1 : ℤ) else 0)) =
      List.ofFn (fun i : Fin 41 => List.ofFn (fun s : Fin 41 => Q i s)) := by
    decide +kernel
  intro i s
  exact congrFun (List.ofFn_inj.mp (congrFun (List.ofFn_inj.mp h) i)) s
private theorem quotient_rows (b : Col) (s : Fin 41) :
    (∑ c : Col, if compatible b c ∧ cls c = s then (1 : ℤ) else 0) = Q (cls b) s := by
  obtain ⟨e, he⟩ := class_rep b
  calc
    _ = ∑ c : Col, if compatible (relabel e b) (relabel e c) ∧
        cls (relabel e c) = s then (1 : ℤ) else 0 := by
      simp only [compatible_relabel, class_relabel]
    _ = ∑ c : Col, if compatible (representatives (cls b)) c ∧
        cls c = s then (1 : ℤ) else 0 := by
      rw [he]
      exact (relabel e).sum_comp (fun c =>
        if compatible (representatives (cls b)) c ∧ cls c = s then (1 : ℤ) else 0)
    _ = _ := representative_rows _ _
private def classWeights : Fin 41 → ℤ :=
  ![3,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem initial_class_counts : ∀ i : Fin 41,
    (∑ a : Col, if cls a = i then (1 : ℤ) else 0) = classWeights i := by
  decide +kernel
set_option maxRecDepth 100000 in
private theorem initial_weights (s : Fin 41) :
    (∑ a : Col, ∑ b : Col,
      if compatible a b ∧ cls b = s then (1 : ℤ) else 0) = weights s := by
  calc
    _ = ∑ a : Col, Q (cls a) s := Finset.sum_congr rfl (fun a _ => quotient_rows a s)
    _ = ∑ i : Fin 41, (∑ a : Col, if cls a = i then (1 : ℤ) else 0) * Q i s := by
      simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp
    _ = ∑ i : Fin 41, classWeights i * Q i s := by simp_rw [initial_class_counts]
    _ = _ := by fin_cases s <;> rfl
private def gridEquiv (n : ℕ) : (Fin 5 × Fin n → Fin 3) ≃ (Fin n → Col) where
  toFun P j := (P (0,j),P (1,j),P (2,j),P (3,j),P (4,j))
  invFun f p := column (f p.2) p.1
  left_inv P := by funext p; rcases p with ⟨r,j⟩; fin_cases r <;> rfl
  right_inv f := rfl
private theorem column_grid (n : ℕ) (P : Fin 5 × Fin n → Fin 3)
    (j : Fin n) (r : Fin 5) : column (gridEquiv n P j) r = P (r,j) := by
  fin_cases r <;> rfl
private theorem tail_iff (a b : Col) (xs : List Col) :
    TransferMatrix.tailGood compatible (fun _ _ _ => True) a b xs ↔
      (b :: xs).IsChain compatible := by
  induction xs generalizing a b with
  | nil => simp [TransferMatrix.tailGood]
  | cons c xs ih => simp [TransferMatrix.tailGood, List.isChain_cons_cons, ih]
private theorem good_iff (xs : List Col) :
    TransferMatrix.good compatible (fun _ _ _ => True) xs ↔ xs.IsChain compatible := by
  cases xs with
  | nil => simp [TransferMatrix.good]
  | cons a xs =>
    cases xs with
    | nil => simp [TransferMatrix.good]
    | cons b xs => simp [TransferMatrix.good, tail_iff, List.isChain_cons_cons]
private theorem grid_good (n : ℕ) (P : Fin 5 × Fin n → Fin 3) :
    Proper P ↔ TransferMatrix.good compatible (fun _ _ _ => True)
      (List.ofFn (gridEquiv n P)) := by
  rw [good_iff, List.isChain_ofFn]
  simp only [Proper, compatible_iff, column_grid]
  constructor
  · intro h j hj
    exact h ⟨j, by omega⟩ hj
  · intro h j hj
    exact h j.val hj

section CountBridge
attribute [local irreducible] compatible cls Q weights

private theorem count_transfer (n : ℕ) :
    (L (n+2) : ℤ) = dotProduct weights ((Q^n).mulVec (1 : Fin 41 → ℤ)) := by
  classical
  let he : {P : Fin 5 × Fin (n+2) → Fin 3 // Proper P} ≃
      {f : Fin (n+2) → Col //
        TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} :=
    Equiv.subtypeEquiv (gridEquiv (n+2)) (fun P => grid_good (n+2) P)
  have hc : L (n+2) = Nat.card {f : Fin (n+2) → Col //
      TransferMatrix.good compatible (fun _ _ _ => True) (List.ofFn f)} := by
    rw [← Nat.card_congr he]
    simp [L, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hc]
  refine TransferMatrix.cardMatrix compatible (fun _ _ _ => True) (fun _ b => cls b)
    Q weights ?_ ?_ n
  · intro a b _ s
    rw [← quotient_rows b s]
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : compatible b c <;> by_cases hs : cls c = s <;> simp [h, hs]
  · intro s
    rw [← initial_weights s]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases h : compatible a b ∧ cls b = s <;> simp [h]

end CountBridge

private def W : Fin 12 → Fin 41 → ℤ := ![
  ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
  ![32, 16, 8, 16, 8, 8, 4, 4, 8, 16, 8, 4, 4, 8, 8, 4, 4, 2, 4, 2, 2, 2, 4, 8, 4, 4, 8, 16, 8, 4, 4, 8, 4, 2, 2, 2, 4, 2, 4, 4, 8],
  ![324, 162, 108, 162, 54, 108, 72, 36, 90, 162, 72, 18, 36, 54, 108, 60, 48, 48, 72, 24, 24, 12, 36, 90, 60, 30, 84, 162, 78, 24, 48, 72, 18, 6, 12, 12, 36, 24, 24, 30, 54],
  ![3744, 1692, 1152, 1656, 432, 1152, 726, 336, 924, 1692, 624, 96, 336, 432, 1188, 630, 450, 486, 756, 216, 252, 72, 324, 972, 654, 264, 906, 1872, 786, 168, 498, 684, 108, 24, 84, 120, 396, 240, 174, 294, 504],
  ![40404, 17832, 12648, 17382, 3864, 12648, 8094, 3324, 10218, 18012, 5934, 660, 3414, 3954, 12738, 6924, 4404, 5436, 8244, 2088, 2616, 528, 3084, 10458, 7254, 2484, 9798, 20202, 8034, 1380, 5394, 6924, 870, 132, 798, 1236, 4404, 2658, 1530, 3294, 5274],
  ![436584, 188052, 136128, 182976, 37776, 135978, 86472, 34188, 109848, 193422, 60300, 5616, 36798, 39786, 137238, 74208, 45192, 58236, 88266, 21246, 28230, 4614, 31314, 111108, 77898, 24858, 104292, 218292, 83760, 12918, 58230, 71868, 8472, 1002, 8568, 12942, 47712, 28236, 15108, 35640, 56184],
  ![4677996, 1999236, 1461936, 1948170, 386868, 1455330, 926688, 356718, 1178040, 2069382, 630552, 54876, 395094, 418638, 1469460, 794802, 474474, 624636, 943740, 220752, 303270, 45402, 330306, 1185714, 836082, 256680, 1113198, 2338998, 886038, 130188, 625854, 762456, 88332, 9474, 91824, 135966, 511590, 302052, 156078, 383238, 599922],
  ![50046816, 21300108, 15641112, 20791860, 4076904, 15561330, 9902268, 3777432, 12589032, 22126926, 6683616, 571320, 4230582, 4449822, 15716778, 8489280, 5034972, 6677232, 10087338, 2335038, 3247422, 473514, 3513666, 12664848, 8941494, 2710746, 11875608, 25023408, 9424500, 1366158, 6699618, 8127012, 936156, 97806, 983160, 1442394, 5473992, 3225036, 1648644, 4099752, 6410148],
  ![534870876, 227362620, 167167956, 222058218, 43370256, 166285254, 105794832, 40244358, 134501088, 236442918, 71231268, 6055104, 45225858, 47469054, 167959452, 90685686, 53679306, 71346924, 107779896, 24868764, 34715958, 5021142, 37490946, 135292734, 95552982, 28855944, 126813030, 267435438, 100549590, 14514312, 71614974, 86765484, 9978108, 1033962, 10509900, 15375594, 58505358, 34447908, 17551962, 43815402, 68483466],
  ![5714699808, 2428286892, 1786071108, 2372039916, 462744516, 1776553854, 1130218524, 429577152, 1436892528, 2526101382, 760417884, 64536228, 483242874, 506892534, 1794483762, 968763108, 573102660, 762233496, 1151459670, 265428474, 370944006, 53524158, 400369098, 1445305332, 1020878634, 307940562, 1354550544, 2857349904, 1073736348, 154803954, 765192474, 926734584, 106523436, 11012070, 112298868, 164148678, 625094184, 367985028, 187315224, 468129420, 731617620],
  ![61051776924, 25939228116, 19081127928, 25339665234, 4941644988, 18979182138, 12074072952, 4588030326, 15350261016, 26986703574, 8121775080, 688964268, 5162740950, 5414409822, 19170864012, 10349117706, 6121303698, 8142986700, 12301097724, 2834784432, 3962993910, 571428762, 4276654674, 15439997250, 10906233570, 3288677688, 14469950022, 30525888462, 11469278094, 1652967300, 8174894358, 9899667984, 1137755148, 117535506, 1199747040, 1753245894, 6678084414, 3931086252, 2000471382, 5001143310, 7815839562],
  ![652216306656, 277099897740, 203843789832, 270698972820, 52785403032, 202753867506, 128986171596, 49009985160, 163985386296, 288297900318, 86758735104, 7358664744, 55153947462, 57839442558, 204802017882, 110558217504, 65389788876, 86991005040, 131411798202, 30281310222, 42336964590, 6103374090, 45685629426, 164943614496, 116510986758, 35129393658, 154579060152, 326108153328, 122520837588, 17656009374, 87332803074, 105755358324, 12153813132, 1255290654, 12816982872, 18728674938, 71342069304, 41995166556, 21368946228, 53427168792, 83495882436]]
private def coefficients : Fin 7 → ℤ := ![-8,48,-84,17,76,-64,16]
private theorem table_zero : W 0 = (1 : Fin 41 → ℤ) := by
  exact List.ofFn_inj.mp rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem table_steps : ∀ k : Fin 11, W k.succ = Q.mulVec (W k.castSucc) := by
  intro k
  fin_cases k <;> exact List.ofFn_inj.mp rfl
private theorem powers_table : ∀ k : Fin 12,
    (Q^k.val).mulVec (1 : Fin 41 → ℤ) = W k :=
  TransferMatrix.tabulatedPowers Q 11 W table_zero table_steps
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem power_polynomial : (Q^(4+7)).mulVec (1 : Fin 41 → ℤ) =
    ∑ j : Fin 7, coefficients j • (Q^(4+j.val)).mulVec (1 : Fin 41 → ℤ) := by
  rw [show 4+7 = (11 : Fin 12).val from rfl, powers_table]
  have hh (j : Fin 7) : (Q^(4+j.val)).mulVec (1 : Fin 41 → ℤ) =
      W ⟨4+j.val, by omega⟩ := powers_table ⟨4+j.val, by omega⟩
  simp_rw [hh]
  exact List.ofFn_inj.mp rfl


private theorem pair_tail (n : ℕ) : (L (n+13) : ℤ) + 6 =
    16 * ((L (n+12) : ℤ)+6) - 64 * ((L (n+11) : ℤ)+6) +
    76 * ((L (n+10) : ℤ)+6) + 17 * ((L (n+9) : ℤ)+6) -
    84 * ((L (n+8) : ℤ)+6) + 48 * ((L (n+7) : ℤ)+6) -
    8 * ((L (n+6) : ℤ)+6) := by
  have h := TransferMatrix.scalarRelationShift Q weights 7 4 coefficients power_polynomial n
  have ht (k : ℕ) : dotProduct weights ((Q^k).mulVec (1 : Fin 41 → ℤ)) =
      (L (k+2) : ℤ) := (count_transfer k).symm
  simp_rw [ht] at h
  norm_num [coefficients, Fin.sum_univ_succ, Nat.add_assoc] at h
  linear_combination h

private theorem scale_recurrence (m : ℕ) (hm : 2 ≤ m)
    (h : (L (m+7) : ℤ)+6 =
      16 * ((L (m+6) : ℤ)+6) - 64 * ((L (m+5) : ℤ)+6) +
      76 * ((L (m+4) : ℤ)+6) + 17 * ((L (m+3) : ℤ)+6) -
      84 * ((L (m+2) : ℤ)+6) + 48 * ((L (m+1) : ℤ)+6) -
      8 * ((L m : ℤ)+6)) :
    (a (m+7) : ℤ) = 512 * (a (m+6) : ℤ) - 65536 * (a (m+5) : ℤ) +
      2490368 * (a (m+4) : ℤ) + 17825792 * (a (m+3) : ℤ) -
      2818572288 * (a (m+2) : ℤ) + 51539607552 * (a (m+1) : ℤ) -
      274877906944 * (a m : ℤ) := by
  have hb (i : ℕ) : 48 * (a (m+i) : ℤ) =
      (32 : ℤ)^m * 32^i * ((L (m+i) : ℤ)+6) := by
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
  norm_num only [Nat.add_zero, pow_zero, pow_one, mul_one] at h0 h1 h2 h3 h4 h5 h6 h7
  apply (mul_left_cancel₀ (show (48 : ℤ) ≠ 0 by norm_num))
  linear_combination h7 - 512*h6 + 65536*h5 - 2490368*h4 - 17825792*h3 +
    2818572288*h2 - 51539607552*h1 + 274877906944*h0 + (32 : ℤ)^m*34359738368*h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem pair_base : (L 12 : ℤ)+6 =
    16*((L 11 : ℤ)+6) - 64*((L 10 : ℤ)+6) + 76*((L 9 : ℤ)+6) +
    17*((L 8 : ℤ)+6) - 84*((L 7 : ℤ)+6) + 48*((L 6 : ℤ)+6) - 8*((L 5 : ℤ)+6) := by
  have ht (k : ℕ) (hk : k < 12) :
      (L (k+2) : ℤ) = dotProduct weights (W ⟨k,hk⟩) := by
    rw [count_transfer]
    exact congrArg (dotProduct weights) (powers_table ⟨k,hk⟩)
  rw [ht 10 (by decide), ht 9 (by decide), ht 8 (by decide), ht 7 (by decide),
    ht 6 (by decide), ht 5 (by decide), ht 4 (by decide), ht 3 (by decide)]
  rfl

private theorem shifted (m : ℕ) :
    (a (m+12) : ℤ) = 512*(a (m+11) : ℤ) - 65536*(a (m+10) : ℤ) +
    2490368*(a (m+9) : ℤ) + 17825792*(a (m+8) : ℤ) -
    2818572288*(a (m+7) : ℤ) + 51539607552*(a (m+6) : ℤ) -
    274877906944*(a (m+5) : ℤ) := by
  cases m with
  | zero => exact scale_recurrence 5 (by decide) pair_base
  | succ m =>
    have h := scale_recurrence (m+6) (by omega) (by
      simpa only [Nat.add_assoc] using pair_tail m)
    simpa only [Nat.add_assoc] using h

theorem result (n : ℤ) (hn : 11 < n) :
    (a n.toNat : ℤ) = 512*(a (n-1).toNat : ℤ) - 65536*(a (n-2).toNat : ℤ) +
    2490368*(a (n-3).toNat : ℤ) + 17825792*(a (n-4).toNat : ℤ) -
    2818572288*(a (n-5).toNat : ℤ) + 51539607552*(a (n-6).toNat : ℤ) -
    274877906944*(a (n-7).toNat : ℤ) := by
  have h := shifted (n.toNat-12)
  have e0 : n.toNat-12+12 = n.toNat := by omega
  have e1 : n.toNat-12+11 = (n-1).toNat := by omega
  have e2 : n.toNat-12+10 = (n-2).toNat := by omega
  have e3 : n.toNat-12+9 = (n-3).toNat := by omega
  have e4 : n.toNat-12+8 = (n-4).toNat := by omega
  have e5 : n.toNat-12+7 = (n-5).toNat := by omega
  have e6 : n.toNat-12+6 = (n-6).toNat := by omega
  have e7 : n.toNat-12+5 = (n-7).toNat := by omega
  simpa only [e0,e1,e2,e3,e4,e5,e6,e7] using h

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
