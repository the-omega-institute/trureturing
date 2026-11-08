/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.finite_certificate
   digest: Barker's generating function for the literal normalized six-colour three-column strip. -/

/-
admission_basis: open-problem-resolution (#27657; Proved)
escape_witness: none (the settlement of the external open problem is the new content; every declaration below is bind-only)
Finite single-row decisions supply the numerical premises consumed on the result path.
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen
(statement_id sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.allowed
(statement_id sha256:4ee019eb42606605da41b2b090212be244d3bf48d64a2c10dc2d9c6c6f7e6468).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.advance
(statement_id sha256:63e23e390cbc7ee42155ce307351f149d901cd9013daee3d6d2eac775e24af71).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good
(statement_id sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish
(statement_id sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_fst
(statement_id sha256:5859cc0f84f4e6a91313521f32ea6d187c4822bb52d4e438939da5e000940bd5).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_snd
(statement_id sha256:1ada14ea452d6f35f959dbbd5a034265c8c6921cd041422cad27ec166a94d24c).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good_iff
(statement_id sha256:59d0ffb034f7f2361718e6d2566eb24417785b9a178f6fcb44f336c1199d3d62).
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.edge_iff
(statement_id sha256:eb164ba2a30a036eb9157c90341cc0d7664c1e26513ba1fedc8a4964a09ae84a).
Direct frozen dependency: D5.S3.Observer.Separation.BooleanRankThreeK4.beta
(statement_id sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481).
Row: proof_shape=bind-only; consumers=prior, rowLegal, TailGood, step
prior: proof_shape=bind-only; consumers=normal, prior_zero, prior_succ
instDecidablePrior: proof_shape=bind-only; consumers=instDecidableNormal
normal: proof_shape=bind-only; consumers=normal_cons, Legal, tail_iff
prior_zero: proof_shape=bind-only; consumers=normal_cons
prior_succ: proof_shape=bind-only; consumers=normal_cons
normal_cons: proof_shape=bind-only; consumers=tail_iff, counting_bridge
rowLegal: proof_shape=bind-only; consumers=Legal, TailGood, step, classCount, firstCount
bonds: proof_shape=bind-only; consumers=Legal, bonds_iff, tail_iff
Legal: proof_shape=bind-only; consumers=a, counting_bridge
instDecidableNormal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableRowLegal: proof_shape=bind-only; consumers=instDecidableLegal, step, total
instDecidableBonds: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=counting_bridge, a_eq_w, zero_count, result
pairs: proof_shape=bind-only; consumers=bonds_iff, TailGood, step, total, initial_valid
compatible: proof_shape=bind-only; consumers=bonds_iff, TailGood, step, classCount
instDecidableCompatible: proof_shape=bind-only; consumers=instDecidableTailGood, step
bonds_iff: proof_shape=bind-only; consumers=tail_iff, counting_bridge
TailGood: proof_shape=bind-only; consumers=tail_iff, count, count_eq_v
instDecidableGood: proof_shape=bind-only; consumers=instDecidableTailGood, step, total
instDecidableTailGood: proof_shape=bind-only; consumers=count
tail_iff: proof_shape=bind-only; consumers=counting_bridge
step: proof_shape=bind-only; consumers=v, count_eq_v, v_eq_w
v: proof_shape=bind-only; consumers=count_eq_v, counting_bridge, v_eq_w
count: proof_shape=bind-only; consumers=count_eq_v, counting_bridge
count_eq_v: proof_shape=bind-only; consumers=counting_bridge
total: proof_shape=bind-only; consumers=counting_bridge, a_eq_w
counting_bridge: proof_shape=bind-only; consumers=a_eq_w
Valid: proof_shape=bind-only; consumers=valid_next, initial_valid, finite_certificate, v_eq_w
instDecidableValid: proof_shape=bind-only; consumers=valid_next, row_counts, initial_valid
valid_next: proof_shape=bind-only; consumers=v_eq_w
classCount: proof_shape=bind-only; consumers=finite_certificate
firstCount: proof_shape=bind-only; consumers=finite_certificate
row_counts: proof_shape=bind-only; consumers=finite_certificate
initial_valid: proof_shape=bind-only; consumers=a_eq_w
initial_counts: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=v_eq_w, a_eq_w
w: proof_shape=bind-only; consumers=v_eq_w, a_eq_w, recurrence, result
v_eq_w: proof_shape=bind-only; consumers=a_eq_w
a_eq_w: proof_shape=bind-only; consumers=recurrence, result
recurrence: proof_shape=bind-only; consumers=result
zero_count: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic
import Mathlib.RingTheory.PowerSeries.Basic

/-! Literal array counting and a two-class continuation transfer. -/

open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip

open HardinA233175PairStrip (Seen allowed advance good finish finish_fst finish_snd good_iff edge_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)

abbrev Row := Fin 3 → Fin 6

private def prior {n : ℕ} (f : Fin n → Row) (i : Fin n) (j : Fin 3) (d : Fin 6) : Prop :=
  ∃ r k, (r < i ∨ r = i ∧ k < j) ∧ f r k = d

private instance instDecidablePrior {n : ℕ} (f : Fin n → Row) (i : Fin n) (j : Fin 3) (d : Fin 6) :
    Decidable (prior f i j d) := inferInstanceAs (Decidable (∃ _ _, _ ∧ _))

private def normal {n : ℕ} (s : Seen) (f : Fin n → Row) : Prop :=
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

def rowLegal (c : Row) : Prop :=
  ∀ j : Fin 2, c j.castSucc ≠ c j.succ ∧ (c j.castSucc).val + (c j.succ).val ≠ 5

private def bonds (c d : Row) : Prop :=
  ∀ j : Fin 2, c j.succ ≠ d j.castSucc ∧ (c j.succ).val + (d j.castSucc).val ≠ 5

private def Legal {n : ℕ} (A : Fin n × Fin 3 → Fin 6) : Prop :=
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

def pairs (c : Row) : Fin 3 × Fin 3 := (beta (c 1), beta (c 2))

def compatible (p : Fin 3 × Fin 3) (c : Row) : Prop :=
  p.1 ≠ beta (c 0) ∧ p.2 ≠ beta (c 1)

private instance instDecidableCompatible (p : Fin 3 × Fin 3) (c : Row) : Decidable (compatible p c) :=
  inferInstanceAs (Decidable (_ ∧ _))

private theorem bonds_iff (c d : Row) : bonds c d ↔ compatible (pairs c) d := by
  have he (x y : Fin 6) : (x ≠ y ∧ x.val + y.val ≠ 5) ↔ beta x ≠ beta y := by
    have hh := edge_iff (fun _ => x) (fun _ => y)
    change (∀ _r _t : Fin 2, x ≠ y ∧ x.val + y.val ≠ 5) ↔
      (∀ _r : Fin 2, beta y ≠ beta x ∧ beta y ≠ beta x) at hh
    simpa only [Fin.forall_fin_two, and_self, ne_comm] using hh
  simp only [bonds, he, compatible, pairs, Fin.forall_fin_two]
  rfl

private def TailGood : {n : ℕ} → Seen → (Fin 3 × Fin 3) → (Fin n → Row) → Prop
  | 0, _, _, _ => True
  | _ + 1, s, p, f => rowLegal (f 0) ∧ compatible p (f 0) ∧ good s (f 0) ∧
      TailGood (finish s (f 0)) (pairs (f 0)) (Fin.tail f)

private instance instDecidableGood (s : Seen) (c : Row) : Decidable (good s c) := by
  unfold good
  infer_instance

private instance instDecidableTailGood {n : ℕ} (s : Seen) (p : Fin 3 × Fin 3) (f : Fin n → Row) :
    Decidable (TailGood s p f) := by
  induction n generalizing s p with
  | zero => exact isTrue trivial
  | succ n ih =>
    change Decidable (rowLegal (f 0) ∧ compatible p (f 0) ∧ good s (f 0) ∧
      TailGood (finish s (f 0)) (pairs (f 0)) (Fin.tail f))
    haveI := ih (finish s (f 0)) (pairs (f 0)) (Fin.tail f)
    infer_instance

private theorem tail_iff {n : ℕ} (s : Seen) (p : Fin 3 × Fin 3) (f : Fin n → Row) :
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

private def step (w : Seen → (Fin 3 × Fin 3) → ℤ) (s : Seen) (p : Fin 3 × Fin 3) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c then
    w (finish s c) (pairs c) else 0

private def v : ℕ → Seen → (Fin 3 × Fin 3) → ℤ
  | 0, _, _ => 1
  | n + 1, s, p => step (v n) s p

private def count (n : ℕ) (s : Seen) (p : Fin 3 × Fin 3) : ℤ :=
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

private def total (w : Seen → (Fin 3 × Fin 3) → ℤ) : ℤ :=
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

def Valid (s : Seen) (p : Fin 3 × Fin 3) : Prop :=
  s.1 = true ∧ p.1 ≠ p.2 ∧ (s.2 = false → p.1 ≠ 2 ∧ p.2 ≠ 2)

private instance instDecidableValid (s : Seen) (p : Fin 3 × Fin 3) : Decidable (Valid s p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ → _ ∧ _)))

private theorem valid_next : ∀ s p, Valid s p → ∀ c : Row,
    rowLegal c ∧ compatible p c ∧ good s c → Valid (finish s c) (pairs c) := by
  decide +kernel

/-- One-row continuations ending in the specified second seen flag. -/
def classCount (s : Seen) (p : Fin 3 × Fin 3) (b : Bool) : ℤ :=
  ∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
    (finish s c).2 = b then 1 else 0

/-- First rows ending in the specified second seen flag. -/
def firstCount (b : Bool) : ℤ :=
  ∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
    (finish (false, false) c).2 = b then 1 else 0

private theorem row_counts : ∀ s p, Valid s p →
    (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = true then (1 : ℤ) else 0) = (if s.2 then 48 else 20) ∧
    (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = false then (1 : ℤ) else 0) = (if s.2 then 0 else 8) := by
  decide +kernel

private theorem initial_valid : ∀ c : Row,
    c 0 = 0 ∧ rowLegal c ∧ good (false, false) c →
      Valid (finish (false, false) c) (pairs c) := by
  decide +kernel

private theorem initial_counts :
    (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) = 1 ∧
    (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) = 2 := by
  decide +kernel

/-- The single-row class counts and the two first-row class counts. -/
theorem finite_certificate :
    (∀ s p, Valid s p →
      classCount s p true = (if s.2 then 48 else 20) ∧
      classCount s p false = (if s.2 then 0 else 8)) ∧
    firstCount true = 1 ∧ firstCount false = 2 :=
  ⟨row_counts, initial_counts⟩

private def w : ℕ → Bool → ℤ
  | 0, _ => 1
  | n + 1, true => 48 * w n true
  | n + 1, false => 8 * w n false + 20 * w n true

private theorem v_eq_w (n : ℕ) (s : Seen) (p : Fin 3 × Fin 3) (h : Valid s p) :
    v n s p = w n s.2 := by
  induction n generalizing s p with
  | zero => rfl
  | succ n ih =>
    rw [v, step]
    have hs : ∀ c : Row, (if rowLegal c ∧ compatible p c ∧ good s c then
        v n (finish s c) (pairs c) else 0) =
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = true
          then (1 : ℤ) else 0) * w n true +
        (if rowLegal c ∧ compatible p c ∧ good s c ∧ (finish s c).2 = false
          then (1 : ℤ) else 0) * w n false := by
      intro c
      by_cases hc : rowLegal c ∧ compatible p c ∧ good s c
      · rw [ite_eq_left hc, ih _ _ (valid_next s p h c hc)]
        cases hb : (finish s c).2 <;> simp [hc, hb]
      · simp only [← and_assoc] at hc ⊢
        simp [hc]
    simp_rw [hs]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      show (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = true then (1 : ℤ) else 0) = (if s.2 then 48 else 20) from
        (finite_certificate.1 s p h).1,
      show (∑ c : Row, if rowLegal c ∧ compatible p c ∧ good s c ∧
        (finish s c).2 = false then (1 : ℤ) else 0) = (if s.2 then 0 else 8) from
        (finite_certificate.1 s p h).2]
    cases hb : s.2 <;> simp [hb, w] <;> ring

private theorem a_eq_w (n : ℕ) : (a (n + 1) : ℤ) = 2 * w n false + w n true := by
  rw [counting_bridge, total]
  have hs : ∀ c : Row, (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c then
      v n (finish (false, false) c) (pairs c) else 0) =
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) * w n true +
      (if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) * w n false := by
    intro c
    by_cases hc : c 0 = 0 ∧ rowLegal c ∧ good (false, false) c
    · rw [ite_eq_left hc, v_eq_w n _ _ (initial_valid c hc)]
      cases hb : (finish (false, false) c).2 <;> simp [hc, hb]
    · simp only [← and_assoc] at hc ⊢
      simp [hc]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
    show (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = true then (1 : ℤ) else 0) = 1 from
      finite_certificate.2.1,
    show (∑ c : Row, if c 0 = 0 ∧ rowLegal c ∧ good (false, false) c ∧
        (finish (false, false) c).2 = false then (1 : ℤ) else 0) = 2 from
      finite_certificate.2.2]
  ring

private theorem recurrence (n : ℕ) :
    (a (n + 3) : ℤ) = 56 * a (n + 2) - 384 * a (n + 1) := by
  rw [show n + 3 = (n + 1) + 1 + 1 by omega, a_eq_w, a_eq_w, a_eq_w]
  simp only [w]
  ring

private theorem zero_count : a 0 = 0 := by
  simp [a, Legal]

open PowerSeries in
/-- Barker's generating-function identity, with the empty coefficient set to zero. -/
theorem result :
    (1 - 8 * X) * (1 - 48 * X) * (PowerSeries.mk fun n => (a n : ℤ)) =
      X * (3 - 64 * X) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  have hp : (1 - 8 * X) * (1 - 48 * X) * F =
      F - 56 * (F * X ^ 1) + 384 * (F * X ^ 2) := by ring
  have hr : (X * (3 - 64 * X) : PowerSeries ℤ) = 3 * X - 64 * X ^ 2 := by ring
  change (1 - 8 * X) * (1 - 48 * X) * F = _
  rw [hp, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 3 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega)]
    have hh := recurrence (n - 3)
    have h3 : n - 3 + 3 = n := by omega
    have h2 : n - 3 + 2 = n - 1 := by omega
    have h1 : n - 3 + 1 = n - 2 := by omega
    rw [h3, h2, h1] at hh
    linarith
  · have h1 := a_eq_w 0
    have h2 := a_eq_w 1
    change (a 1 : ℤ) = 2 * 1 + 1 at h1
    change (a 2 : ℤ) = 2 * (8 * 1 + 20 * 1) + 48 * 1 at h2
    norm_num only at h1 h2
    interval_cases n <;> norm_num only [zero_count, h1, h2,
      Nat.reduceLeDiff, Nat.reduceSubDiff, Nat.reduceEqDiff, if_true, if_false,
      Nat.cast_zero, mul_zero, sub_self, add_zero]

end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
