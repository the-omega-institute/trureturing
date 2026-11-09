/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233124SquareStrip.finite_certificate
   digest: Barker's generating function for normalized six-colour square strips. -/

/-
admission_basis: open-problem-resolution (#28306; Proved)
escape_witness: none
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic

/-! Literal square-strip counts and a three-class row transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip

open HardinA233175PairStrip (Seen allowed advance good finish finish_fst finish_snd good_iff edge_iff)
open HardinA233251TriangleStrip (Row rowLegal)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

def prior {n : ℕ} (f : Fin n → Row) (i : Fin n) (j : Fin 3) (d : Fin 6) : Prop :=
  ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ f r k = d

private instance instDecidablePrior {n : ℕ} (f : Fin n → Row) (i : Fin n) (j : Fin 3) (d : Fin 6) :
    Decidable (prior f i j d) := inferInstanceAs (Decidable (∃ _ _, _ ∧ _))

def normal {n : ℕ} (s : Seen) (f : Fin n → Row) : Prop :=
  ∀ i j, ((f i j = 2 ∨ f i j = 3 ∨ f i j = 4) → s.1 = true ∨ prior f i j 1) ∧
    (f i j = 3 → s.2 = true ∨ prior f i j 2)

private theorem prior_zero {n : ℕ} (c : Row) (f : Fin n → Row) (j : Fin 3) (d : Fin 6) :
    prior (Fin.cons c f) 0 j d ↔ ∃ k, k < j ∧ c k = d := by
  simp [prior, Fin.exists_fin_succ]

private theorem prior_succ {n : ℕ} (c : Row) (f : Fin n → Row)
    (i : Fin n) (j : Fin 3) (d : Fin 6) :
    prior (Fin.cons c f) i.succ j d ↔ (∃ k, c k = d) ∨ prior f i j d := by
  simp [prior, Fin.exists_fin_succ]

private theorem normal_cons {n : ℕ} (s : Seen) (c : Row) (f : Fin n → Row) :
    normal s (Fin.cons c f) ↔ good s c ∧ normal (finish s c) f := by
  simp only [normal, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    prior_zero, prior_succ, good_iff, finish_fst, finish_snd, or_assoc]

def bonds (c d : Row) : Prop :=
  ∀ j : Fin 3, c j ≠ d j ∧ (c j).val + (d j).val ≠ 5

def Legal {n : ℕ} (A : Fin n × Fin 3 → Fin 6) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = 0) ∧
    (∀ i, rowLegal (fun j => A (i, j))) ∧
    (∀ (i : Fin n) (h : i.val + 1 < n), bonds (fun j => A (i, j))
      (fun j => A (⟨i.val + 1, h⟩, j))) ∧
    normal (false, false) (fun i j => A (i, j))

private instance instDecidableNormal {n : ℕ} (s : Seen) (f : Fin n → Row) : Decidable (normal s f) :=
  inferInstanceAs (Decidable (∀ _ _, (_ → _) ∧ (_ → _)))
private instance instDecidableRowLegal (c : Row) : Decidable (rowLegal c) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableBonds (c d : Row) : Decidable (bonds c d) :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))
private instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 3 → Fin 6) : Decidable (Legal A) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The literal filtered finite count; the first-cell condition gives the convention `a 0 = 0`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 3 → Fin 6 => Legal A)).card

def pairs (c : Row) : Fin 3 → Fin 3 := fun j => beta (c j)

def compatible (p : Fin 3 → Fin 3) (c : Row) : Prop :=
  ∀ j, p j ≠ beta (c j)

private instance instDecidableCompatible (p : Fin 3 → Fin 3) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _, _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  have he (x y : Fin 6) : (x ≠ y ∧ x.val + y.val ≠ 5) ↔ beta x ≠ beta y := by
    have hh := edge_iff (fun _ => x) (fun _ => y)
    change (∀ _r _t : Fin 2, x ≠ y ∧ x.val + y.val ≠ 5) ↔
      (∀ _r : Fin 2, beta y ≠ beta x ∧ beta y ≠ beta x) at hh
    simpa only [Fin.forall_fin_two, and_self, ne_comm] using hh
  simp only [bonds, he, compatible, pairs]

private def TailGood : {n : ℕ} → Seen → (Fin 3 → Fin 3) → (Fin n → Row) → Prop
  | 0, _, _, _ => True
  | _ + 1, s, p, f => rowLegal (f 0) ∧ compatible p (f 0) ∧ good s (f 0) ∧
      TailGood (finish s (f 0)) (pairs (f 0)) (Fin.tail f)

private instance instDecidableGood (s : Seen) (c : Row) : Decidable (good s c) := by
  unfold good
  infer_instance

private instance instDecidableTailGood {n : ℕ} (s : Seen) (p : Fin 3 → Fin 3) (f : Fin n → Row) :
    Decidable (TailGood s p f) := by
  induction n generalizing s p with
  | zero => exact isTrue trivial
  | succ n ih =>
    change Decidable (rowLegal (f 0) ∧ compatible p (f 0) ∧ good s (f 0) ∧
      TailGood (finish s (f 0)) (pairs (f 0)) (Fin.tail f))
    haveI := ih (finish s (f 0)) (pairs (f 0)) (Fin.tail f)
    infer_instance

private theorem tail_iff {n : ℕ} (s : Seen) (p : Fin 3 → Fin 3) (f : Fin n → Row) :
    TailGood s p f ↔ normal s f ∧
      (∀ i, rowLegal (f i)) ∧
      (∀ (i : Fin n) (h : i.val + 1 < n), bonds (f i) (f ⟨i.val + 1, h⟩)) ∧
      (∀ (h : 0 < n), compatible p (f ⟨0, h⟩)) := by
  induction n generalizing s p with
  | zero => simp [TailGood, normal]
  | succ n ih =>
    have hn : normal s f ↔ good s (f 0) ∧ normal (finish s (f 0)) (Fin.tail f) := by
      simpa only [Fin.cons_self_tail] using normal_cons s (f 0) (Fin.tail f)
    rw [TailGood, ih, hn]
    have hb : (∀ (i : Fin (n + 1)) (h : i.val + 1 < n + 1),
        bonds (f i) (f ⟨i.val + 1, h⟩)) ↔
        (∀ (h : 0 < n), compatible (pairs (f 0)) (Fin.tail f ⟨0, h⟩)) ∧
        (∀ (i : Fin n) (h : i.val + 1 < n),
          bonds (Fin.tail f i) (Fin.tail f ⟨i.val + 1, h⟩)) := by
      simp only [Fin.forall_fin_succ, Fin.val_zero, Fin.val_succ]
      constructor
      · intro h
        constructor
        · intro hn
          simpa only [bonds_iff, Fin.tail, Fin.succ] using h.1 (by omega)
        · intro i hi
          exact h.2 i (by omega)
      · rintro ⟨h0, ht⟩
        constructor
        · intro hn
          simpa only [bonds_iff, Fin.tail, Fin.succ] using h0 (by omega)
        · intro i hi
          exact ht i (by omega)
    rw [hb]
    simp only [Fin.forall_fin_succ, Fin.tail, Fin.mk_zero, Nat.zero_lt_succ, forall_const]
    tauto

private def step (w : Seen → (Fin 3 → Fin 3) → ℤ) (s : Seen) (p : Fin 3 → Fin 3) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
    w (finish s c) (pairs c) else 0

private def v : ℕ → Seen → (Fin 3 → Fin 3) → ℤ
  | 0, _, _ => 1
  | n + 1, s, p => step (v n) s p

private def count (n : ℕ) (s : Seen) (p : Fin 3 → Fin 3) : ℤ :=
  ∑ f : Fin n → Row, if TailGood s p f then 1 else 0

private theorem count_eq_v (n : ℕ) : count n = v n := by
  induction n with
  | zero => funext s p; simp [count, TailGood, v]
  | succ n ih =>
    funext s p
    rw [count, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Row)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ c : Row, ∑ f : Fin n → Row,
      if TailGood s p (Fin.cons c f) then (1 : ℤ) else 0) = _
    change _ = step (v n) s p
    rw [← ih]
    unfold step count
    apply Finset.sum_congr rfl
    intro c _
    by_cases h : rowLegal c ∧ compatible p c ∧ good s c
    · simp [TailGood, h.1, h.2.1, h.2.2]
    · have hn : ∀ f : Fin n → Row, ¬ TailGood s p (Fin.cons c f) := by
        intro f hf
        exact h ⟨hf.1, hf.2.1, hf.2.2.1⟩
      simp [hn, h]

private def total (w : Seen → (Fin 3 → Fin 3) → ℤ) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
    w (finish (false, false) c) (pairs c) else 0

private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  rw [a, Finset.natCast_card_filter]
  let e : (Fin (n + 1) × Fin 3 → Fin 6) ≃ (Fin (n + 1) → Row) :=
    { toFun := fun A i j => A (i, j)
      invFun := fun f p => f p.1 p.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.sum_comp,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => Row)).sum_comp, Fintype.sum_prod_type]
  unfold total
  apply Finset.sum_congr rfl
  intro c _
  rw [← count_eq_v]
  unfold count
  have hl : ∀ f : Fin n → Row,
      Legal (fun p => (Fin.cons c f : Fin (n + 1) → Row) p.1 p.2) ↔
        (c 0 = 0 ∧ rowLegal c ∧ good (false, false) c) ∧
          TailGood (finish (false, false) c) (pairs c) f := by
    intro f
    rw [tail_iff, Legal, normal_cons]
    have hz : (∃ i : Fin (n + 1), i.val = 0 ∧ (Fin.cons c f : Fin (n + 1) → Row) i 0 = 0) ↔ c 0 = 0 := by
      constructor
      · rintro ⟨i, hi, h⟩
        simpa only [show i = 0 from Fin.ext hi, Fin.cons_zero] using h
      · exact fun h => ⟨0, rfl, h⟩
    rw [hz]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
      Fin.val_zero, Fin.val_succ]
    constructor
    · rintro ⟨hc, hr, hb, hg⟩
      refine ⟨⟨hc, hr.1, hg.1⟩, hg.2, hr.2, ?_, ?_⟩
      · intro i hi
        exact hb.2 i (by omega)
      · intro hn
        have he : (⟨0 + 1, by omega⟩ : Fin (n + 1)) = (⟨0, hn⟩ : Fin n).succ :=
          Fin.ext rfl
        simpa only [bonds_iff, he, Fin.cons_succ] using hb.1 (by omega)
    · rintro ⟨⟨hc, hr, hg⟩, hn, ht, hb, hp⟩
      refine ⟨hc, ⟨hr, ht⟩, ⟨?_, ?_⟩, hg, hn⟩
      · intro h
        have he : (⟨0 + 1, h⟩ : Fin (n + 1)) = (⟨0, by omega⟩ : Fin n).succ :=
          Fin.ext rfl
        simpa only [bonds_iff, he, Fin.cons_succ] using hp (by omega)
      · intro i hi
        exact hb i (by omega)
  change (∑ f : Fin n → Row,
    if Legal (fun p => (Fin.cons c f : Fin (n + 1) → Row) p.1 p.2) then (1 : ℤ) else 0) = _
  simp_rw [hl]
  by_cases h : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c <;> simp [h]

def Valid (s : Seen) (p : Fin 3 → Fin 3) : Prop :=
  s.1 = true ∧ p 0 ≠ p 1 ∧ p 1 ≠ p 2 ∧ (s.2 = false → ∀ j, p j ≠ 2)

private instance instDecidableValid (s : Seen) (p : Fin 3 → Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ → ∀ _, _)))

def boundaryClass (s : Seen) (p : Fin 3 → Fin 3) : Fin 3 :=
  if s.2 then if p 0 = p 2 then 1 else 2 else 0

def transfer (i k : Fin 3) : ℤ :=
  ![![8, 8, 8], ![0, 24, 16], ![0, 16, 16]] i k

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (pairs c) := by
  decide +kernel

def classCount (s : Seen) (p : Fin 3 → Fin 3) (k : Fin 3) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    boundaryClass (finish s c) (pairs c) = k then 1 else 0

def firstCount (k : Fin 3) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    boundaryClass (finish (false, false) c) (pairs c) = k then 1 else 0

private theorem row_counts : ∀ s p, Valid s p → ∀ k,
    classCount s p k = transfer (boundaryClass s p) k := by
  decide +kernel

private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (pairs c) := by
  decide +kernel

private theorem initial_counts : ∀ k, firstCount k = ![2, 0, 1] k := by
  decide +kernel

/-- The single-row transition matrix and the first-row distribution. -/
theorem finite_certificate :
    (∀ s p, Valid s p → ∀ k, classCount s p k = transfer (boundaryClass s p) k) ∧
    (∀ k, firstCount k = ![2, 0, 1] k) :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Fin 3 → ℤ
  | 0, _ => 1
  | n + 1, k => if k = 0 then 8 * w n 0 + 8 * w n 1 + 8 * w n 2
      else if k = 1 then 24 * w n 1 + 16 * w n 2
      else 16 * w n 1 + 16 * w n 2

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 3 → Fin 3) (h : Valid s p) :
    v n s p = w n (boundaryClass s p) := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, step]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (pairs c) = 0 then (1 : ℤ) else 0) * w n 0 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (pairs c) = 1 then (1 : ℤ) else 0) * w n 1 +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧
          boundaryClass (finish s c) (pairs c) = 2 then (1 : ℤ) else 0) * w n 2 := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        generalize hb : boundaryClass (finish s c) (pairs c) = k
        fin_cases k <;> simp [hc, hb]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    change classCount s p 0 * w n 0 + classCount s p 1 * w n 1 +
      classCount s p 2 * w n 2 = _
    rw [finite_certificate.1 s p h 0, finite_certificate.1 s p h 1,
      finite_certificate.1 s p h 2]
    generalize boundaryClass s p = k
    fin_cases k <;> simp [transfer, w]

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = 2 * w n 0 + w n 2 := by
  rw [counting_bridge, total]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (pairs c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (pairs c) = 0 then (1 : ℤ) else 0) *
          w n 0 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (pairs c) = 1 then (1 : ℤ) else 0) *
          w n 1 +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        boundaryClass (finish (false, false) c) (pairs c) = 2 then (1 : ℤ) else 0) *
          w n 2 := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      generalize hb : boundaryClass (finish (false, false) c) (pairs c) = k
      fin_cases k <;> simp [hc, hb]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  change firstCount 0 * w n 0 + firstCount 1 * w n 1 + firstCount 2 * w n 2 = _
  rw [finite_certificate.2 0, finite_certificate.2 1, finite_certificate.2 2]
  simp

private theorem recurrence (n : ℕ) :
    (a (n + 4) : ℤ) = 48 * a (n + 3) - 448 * a (n + 2) + 1024 * a (n + 1) := by
  rw [show n + 4 = (n + 1 + 1 + 1) + 1 by omega,
    show n + 3 = (n + 1 + 1) + 1 by omega, a_eq_w, a_eq_w, a_eq_w, a_eq_w]
  simp [w]
  ring

private theorem zero_count : a 0 = 0 := by
  simp [a, Legal]

open PowerSeries in
/-- Barker's generating-function identity, with the empty coefficient set to zero. -/
theorem result :
    (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) *
      (PowerSeries.mk fun n => (a n : ℤ)) = X * (3 - 64 * X + 192 * X ^ 2) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) * F =
      F - 48 * (F * X ^ 1) + 448 * (F * X ^ 2) - 1024 * (F * X ^ 3) := by ring
  have hr : (X * (3 - 64 * X + 192 * X ^ 2) : PowerSeries ℤ) =
      3 * X - 64 * X ^ 2 + 192 * X ^ 3 := by ring
  change (1 - 8 * X) * (1 - 40 * X + 128 * X ^ 2) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 4 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_right (show n ≠ 1 by omega),
      ite_eq_right (show n ≠ 2 by omega), ite_eq_right (show n ≠ 3 by omega)]
    have hh := recurrence (n - 4)
    have h4 : n - 4 + 4 = n := by omega
    have h3 : n - 4 + 3 = n - 1 := by omega
    have h2 : n - 4 + 2 = n - 2 := by omega
    have h1 : n - 4 + 1 = n - 3 := by omega
    rw [h4, h3, h2, h1] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    have h3 := a_eq_w 2
    norm_num [w] at h1 h2 h3
    interval_cases n <;> norm_num [zero_count, h1, h2, h3]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233124SquareStrip
