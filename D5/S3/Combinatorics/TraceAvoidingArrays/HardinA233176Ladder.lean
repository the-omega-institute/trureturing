/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.finite_certificate
   digest: Barker's integer generating function for the normalized three-row exclusion ladder. -/
/-
admission_basis: open-problem-resolution (#28235; Proved)
escape_witness: none
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen
statement_id: sha256:db13d94501d24f27e6e69604bb633af95ff3309c5698815c44e12d2e52739fce
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.advance
statement_id: sha256:63e23e390cbc7ee42155ce307351f149d901cd9013daee3d6d2eac775e24af71
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.allowed
statement_id: sha256:4ee019eb42606605da41b2b090212be244d3bf48d64a2c10dc2d9c6c6f7e6468
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish
statement_id: sha256:ebae2e26fe8811cb0e473a0168c27f49fa151fa2bcecda8ad3ba0c9fabc41a7f
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_fst
statement_id: sha256:5859cc0f84f4e6a91313521f32ea6d187c4822bb52d4e438939da5e000940bd5
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.finish_snd
statement_id: sha256:1ada14ea452d6f35f959dbbd5a034265c8c6921cd041422cad27ec166a94d24c
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good
statement_id: sha256:f68e874b0a22676cb3053202c645a8ce30010dcd695d55f3e7fce272d4ce5989
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.good_iff
statement_id: sha256:59d0ffb034f7f2361718e6d2566eb24417785b9a178f6fcb44f336c1199d3d62
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.instDecidableAllowed
statement_id: sha256:9e135f0d9ab09759e51e42b0ac88f4af874ef89f0e507400af6cd5a57f0dee70
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.Row
statement_id: sha256:b7c502e020b34fb16b6f45eb8f4662622d3137215aa86d5133861c790e91cd34
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.colour_bond_iff
statement_id: sha256:b9273762bbccc68fc56c48c38b8aba02a46a50a53bfbbe70a660fd21867d6be8
Direct frozen dependency: D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableGood
statement_id: sha256:1b18af22481f3b703bd96b1eff1d82cd4f06b1e61f3b79669043a61a31d15152
Direct frozen dependency: D5.S3.Observer.Separation.BooleanRankThreeK4.beta
statement_id: sha256:1abdc5f3db71567fe05de5aabbe80dddeb5ec5179e4ec7fd49fe71e500518481
Labels: proof_shape=bind-only; consumers=pairs
colEquiv: proof_shape=bind-only; consumers=instFintypeCol
instFintypeCol: proof_shape=bind-only; consumers=step
seen: proof_shape=bind-only; consumers=advance_seen
next: proof_shape=bind-only; consumers=advance_seen
advance_seen: proof_shape=bind-only; consumers=finish_seen
next_mono: proof_shape=bind-only; consumers=endLevel_mono
label_next: proof_shape=bind-only; consumers=valid_next
endLevel: proof_shape=bind-only; consumers=endLevel_mono
endLevel_mono: proof_shape=bind-only; consumers=tailGood_cons
finish_seen: proof_shape=bind-only; consumers=counting_bridge
normal: proof_shape=bind-only; consumers=normal_iff
earlier_iff: proof_shape=bind-only; consumers=normal_iff
normal_iff: proof_shape=bind-only; consumers=legal_iff
Legal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableNormal: proof_shape=bind-only; consumers=instDecidableLegal
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=counting_bridge
pairs: proof_shape=bind-only; consumers=bonds_iff
compatible: proof_shape=bind-only; consumers=instDecidableCompatible
instDecidableCompatible: proof_shape=bind-only; consumers=instDecidableAdmissible
bonds_iff: proof_shape=bind-only; consumers=legal_iff
chain: proof_shape=bind-only; consumers=chain_tail
chain_tail: proof_shape=bind-only; consumers=legal_iff
legal_iff: proof_shape=bind-only; consumers=counting_bridge
TailGood: proof_shape=bind-only; consumers=instDecidableTailGood
instDecidableChain: proof_shape=bind-only; consumers=instDecidableTailGood
instDecidableTailGood: proof_shape=bind-only; consumers=count
admissible: proof_shape=bind-only; consumers=instDecidableAdmissible
instDecidableAdmissible: proof_shape=bind-only; consumers=step
tailGood_cons: proof_shape=bind-only; consumers=count_eq_v
step: proof_shape=bind-only; consumers=v
v: proof_shape=bind-only; consumers=count_eq_v
count: proof_shape=bind-only; consumers=count_eq_v
count_eq_v: proof_shape=bind-only; consumers=counting_bridge
total: proof_shape=bind-only; consumers=counting_bridge
counting_bridge: proof_shape=bind-only; consumers=finite_certificate
Valid: proof_shape=bind-only; consumers=instDecidableValid
instDecidableValid: proof_shape=bind-only; consumers=table_base
valid_next: proof_shape=bind-only; consumers=v_table
initial_valid: proof_shape=bind-only; consumers=total_recurrence
flagIndex: proof_shape=bind-only; consumers=table
links: proof_shape=bind-only; consumers=fastStep
digit: proof_shape=bind-only; consumers=fastStep
key: proof_shape=bind-only; consumers=moves
digit_key: proof_shape=bind-only; consumers=step_fast
moves: proof_shape=bind-only; consumers=moves_certificate
linkKeys: proof_shape=bind-only; consumers=moves_certificate
moves_certificate: proof_shape=bind-only; consumers=step_fast
fastStep: proof_shape=bind-only; consumers=step_fast
weighted_sum: proof_shape=bind-only; consumers=step_fast
step_fast: proof_shape=bind-only; consumers=table_step0
tables: proof_shape=bind-only; consumers=table
table: proof_shape=bind-only; consumers=table_base
table_base: proof_shape=bind-only; consumers=v_table
table_step0: proof_shape=bind-only; consumers=table_steps
table_step1: proof_shape=bind-only; consumers=table_steps
table_step2: proof_shape=bind-only; consumers=table_steps
table_step3: proof_shape=bind-only; consumers=table_steps
table_step4: proof_shape=bind-only; consumers=table_steps
table_step5: proof_shape=bind-only; consumers=table_steps
table_step6: proof_shape=bind-only; consumers=table_steps
table_step7: proof_shape=bind-only; consumers=table_steps
table_step8: proof_shape=bind-only; consumers=table_steps
table_step9: proof_shape=bind-only; consumers=table_steps
table_step10: proof_shape=bind-only; consumers=table_steps
table_steps: proof_shape=bind-only; consumers=v_table
v_table: proof_shape=bind-only; consumers=vector_certificate
table_certificate: proof_shape=bind-only; consumers=vector_certificate
vector_certificate: proof_shape=bind-only; consumers=vector_recurrence
vector_recurrence: proof_shape=bind-only; consumers=total_recurrence
total_recurrence: proof_shape=bind-only; consumers=error_recurrence
total_table: proof_shape=bind-only; consumers=finite_certificate
initial_table0: proof_shape=bind-only; consumers=finite_certificate
initial_table1: proof_shape=bind-only; consumers=finite_certificate
initial_table2: proof_shape=bind-only; consumers=finite_certificate
initial_table3: proof_shape=bind-only; consumers=finite_certificate
initial_table4: proof_shape=bind-only; consumers=finite_certificate
initial_table5: proof_shape=bind-only; consumers=finite_certificate
initial_table6: proof_shape=bind-only; consumers=finite_certificate
initial_table7: proof_shape=bind-only; consumers=finite_certificate
initial_table8: proof_shape=bind-only; consumers=finite_certificate
initial_table9: proof_shape=bind-only; consumers=finite_certificate
initial_table10: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=error_vanish
err: proof_shape=bind-only; consumers=error_recurrence
error_recurrence: proof_shape=bind-only; consumers=error_vanish
error_vanish: proof_shape=bind-only; consumers=recurrence
recurrence: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.Observer.Separation.BooleanRankThreeK4
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.RingTheory.PowerSeries.Basic
/-! Three rows with horizontal and diagonal complementary-pair exclusion. -/
set_option Elab.async false
open scoped BigOperators
namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
open HardinA233175PairStrip
  (Seen allowed advance good finish finish_fst finish_snd good_iff)
open HardinA233251TriangleStrip (Row colour_bond_iff)
open D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
abbrev Labels := Fin 3 → Fin 3
private def colEquiv : (Fin 6 × Fin 6 × Fin 6) ≃ Row where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun d := (d 0, d 1, d 2)
  left_inv _ := rfl
  right_inv d := by ext i; fin_cases i <;> rfl
private instance instFintypeCol : Fintype Row :=
  Fintype.ofEquiv (Fin 6 × Fin 6 × Fin 6) colEquiv
def seen (s : Fin 3) : Seen := (decide (0 < s.val), decide (1 < s.val))
def next (s : Fin 3) (x : Fin 6) : Fin 3 :=
  max s (if x = 1 then 1 else if x = 2 then 2 else 0)
theorem advance_seen : ∀ s x, allowed (seen s) x →
    advance (seen s) x = seen (next s x) := by
  decide +kernel
theorem next_mono (s : Fin 3) (x : Fin 6) : s ≤ next s x := le_max_left _ _
theorem label_next : ∀ s x, allowed (seen s) x → beta x ≤ next s x := by
  decide +kernel
def endLevel : {n : ℕ} → Fin 3 → (Fin n → Fin 6) → Fin 3
  | 0, s, _ => s
  | _ + 1, s, f => endLevel (next s (f 0)) (Fin.tail f)
theorem endLevel_mono {n : ℕ} (s : Fin 3) (f : Fin n → Fin 6) :
    s ≤ endLevel s f := by
  induction n generalizing s with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (next_mono s (f 0)) (ih _ _)
theorem finish_seen {n : ℕ} (s : Fin 3) (f : Fin n → Fin 6)
    (h : good (seen s) f) : finish (seen s) f = seen (endLevel s f) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change allowed (seen s) (f 0) ∧
      good (advance (seen s) (f 0)) (Fin.tail f) at h
    rw [finish, advance_seen s (f 0) h.1]
    exact ih _ _ (by simpa only [advance_seen s (f 0) h.1] using h.2)
def normal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) : Prop :=
  ∀ p,
    ((A p = 2 ∨ A p = 3 ∨ A p = 4) →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 1) ∧
    (A p = 3 →
      ∃ q, q.1.val * n + q.2.val < p.1.val * n + p.2.val ∧ A q = 2)
private theorem earlier_iff {n : ℕ} (A : Fin 3 × Fin n → Fin 6)
    (r : Fin 3) (j : Fin n) (d : Fin 6) :
    (∃ q, q.1.val * n + q.2.val < r.val * n + j.val ∧ A q = d) ↔
      (∃ s k, s < r ∧ A (s, k) = d) ∨ ∃ k, k < j ∧ A (r, k) = d := by
  have he (s : Fin 3) (k : Fin n) :
      s.val * n + k.val < r.val * n + j.val ↔ s < r ∨ s = r ∧ k < j := by
    constructor
    · intro h
      rcases lt_trichotomy s r with hs | he | hr
      · exact Or.inl hs
      · subst s
        exact Or.inr ⟨rfl, by simpa only [Nat.add_lt_add_iff_left, Fin.lt_def] using h⟩
      · have hm := Nat.mul_le_mul_right n (show r.val + 1 ≤ s.val from hr)
        simp only [Nat.add_mul, Nat.one_mul] at hm
        have hj := j.isLt
        omega
    · rintro (hs | ⟨rfl, hk⟩)
      · have hm := Nat.mul_le_mul_right n (show s.val + 1 ≤ r.val from hs)
        simp only [Nat.add_mul, Nat.one_mul] at hm
        have hk := k.isLt
        omega
      · exact Nat.add_lt_add_left hk _
  simp only [Prod.exists, he]
  constructor
  · rintro ⟨s, k, (hs | ⟨rfl, hk⟩), hd⟩
    · exact Or.inl ⟨s, k, hs, hd⟩
    · exact Or.inr ⟨k, hk, hd⟩
  · rintro (⟨s, k, hs, hd⟩ | ⟨k, hk, hd⟩)
    · exact ⟨s, k, Or.inl hs, hd⟩
    · exact ⟨r, k, Or.inr ⟨rfl, hk⟩, hd⟩
private theorem normal_iff {n : ℕ} (A : Fin 3 × Fin n → Fin 6) :
    normal A ↔ good (false, false) (fun j => A (0, j)) ∧
      good (finish (false, false) (fun j => A (0, j))) (fun j => A (1, j)) ∧
      good (finish (finish (false, false) (fun j => A (0, j)))
        (fun j => A (1, j))) (fun j => A (2, j)) := by
  simp only [normal, good_iff, earlier_iff, finish_fst, finish_snd]
  simp only [Bool.false_eq_true, false_or]
  have hr (r : Fin 3) (d : Fin 6) :
      (∃ s k, s < r ∧ A (s, k) = d) ↔
        (r = 1 ∧ ∃ k, A (0, k) = d) ∨
        (r = 2 ∧ ((∃ k, A (0, k) = d) ∨ ∃ k, A (1, k) = d)) := by
    fin_cases r <;> simp [Fin.exists_fin_succ]
  simp_rw [hr]
  constructor
  · intro h
    exact ⟨by simpa using fun j => h (0, j),
      by simpa [or_assoc] using fun j => h (1, j),
      by simpa [or_assoc] using fun j => h (2, j)⟩
  · rintro ⟨ht, hm, hb⟩ ⟨r, j⟩
    fin_cases r
    · simpa using ht j
    · simpa [or_assoc] using hm j
    · simpa [or_assoc] using hb j
def Legal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) : Prop :=
  (∃ j : Fin n, j.val = 0 ∧ A (0, j) = 0) ∧
    (∀ (j : Fin n) (h : j.val + 1 < n) (r s : Fin 3),
      (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
      A (r, j) ≠ A (s, ⟨j.val + 1, h⟩) ∧
        (A (r, j)).val + (A (s, ⟨j.val + 1, h⟩)).val ≠ 5) ∧ normal A
instance instDecidableNormal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) :
    Decidable (normal A) :=
  inferInstanceAs (Decidable (∀ _, (_ → _) ∧ (_ → _)))
private instance instDecidableLegal {n : ℕ} (A : Fin 3 × Fin n → Fin 6) :
    Decidable (Legal A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
/-- Literal filtered count; the first-cell existential sets the empty coefficient to zero. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin 3 × Fin n → Fin 6 => Legal A)).card
attribute [local irreducible] a
def pairs (c : Row) : Labels := fun i => beta (c i)
private def compatible (p : Labels) (c : Row) : Prop :=
  ∀ r s : Fin 3, (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) → beta (c s) ≠ p r
private instance instDecidableCompatible (p : Labels) (c : Row) :
    Decidable (compatible p c) := inferInstanceAs (Decidable (∀ _ _, _ → _))
private theorem bonds_iff (c d : Row) :
    (∀ r s : Fin 3, (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
      c r ≠ d s ∧ (c r).val + (d s).val ≠ 5) ↔ compatible (pairs c) d := by
  simp only [colour_bond_iff, compatible, pairs, ne_comm]
private def chain : {n : ℕ} → Labels → (Fin n → Row) → Prop
  | 0, _, _ => True
  | _ + 1, p, f => compatible p (f 0) ∧ chain (pairs (f 0)) (Fin.tail f)
private theorem chain_tail {n : ℕ} (f : Fin (n + 1) → Row) :
    chain (pairs (f 0)) (Fin.tail f) ↔
      ∀ i : Fin n, compatible (pairs (f i.castSucc)) (f i.succ) := by
  induction n with
  | zero => simp [chain]
  | succ n ih =>
    simpa [chain, Fin.tail, Fin.forall_fin_succ] using
      (and_congr_right (fun _ => ih (Fin.tail f)))
private theorem legal_iff {n : ℕ} (f : Fin (n + 1) → Row) :
    Legal (fun p => f p.2 p.1) ↔ f 0 0 = 0 ∧
      good (false, false) (fun j => f j 0) ∧
      good (finish (false, false) (fun j => f j 0)) (fun j => f j 1) ∧
      good (finish (finish (false, false) (fun j => f j 0))
        (fun j => f j 1)) (fun j => f j 2) ∧
      chain (pairs (f 0)) (Fin.tail f) := by
  have hf : (∃ j : Fin (n + 1), j.val = 0 ∧ f j 0 = 0) ↔ f 0 0 = 0 := by
    constructor
    · rintro ⟨j, hj, h⟩
      simpa only [show j = 0 from Fin.ext hj] using h
    · exact fun h => ⟨0, rfl, h⟩
  have he : (∀ (j : Fin (n + 1)) (h : j.val + 1 < n + 1) (r s : Fin 3),
      (r.val ≤ s.val + 1 ∧ s.val ≤ r.val + 1) →
      f j r ≠ f ⟨j.val + 1, h⟩ s ∧
        (f j r).val + (f ⟨j.val + 1, h⟩ s).val ≠ 5) ↔
      ∀ i : Fin n, compatible (pairs (f i.castSucc)) (f i.succ) := by
    simp only [bonds_iff]
    constructor
    · intro h i
      exact h i.castSucc (by simp)
    · intro h j hj
      exact h ⟨j.val, by omega⟩
  rw [Legal, hf, he, normal_iff, ← chain_tail]
  tauto
private def TailGood {n : ℕ} (q r t b c : Fin 3) (p : Labels)
    (f : Fin n → Row) : Prop :=
  chain p f ∧ good (seen t) (fun i => f i 0) ∧ good (seen b) (fun i => f i 1) ∧
    good (seen c) (fun i => f i 2) ∧
    endLevel t (fun i => f i 0) = q ∧ endLevel b (fun i => f i 1) = r
private instance instDecidableChain {n : ℕ} (p : Labels) (f : Fin n → Row) :
    Decidable (chain p f) := by
  induction n generalizing p with
  | zero => exact isTrue trivial
  | succ n ih => exact @instDecidableAnd _ _ inferInstance (ih _ _)
private instance instDecidableTailGood {n : ℕ} (q r t b c : Fin 3) (p : Labels)
    (f : Fin n → Row) : Decidable (TailGood q r t b c p f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
private def admissible (q r t b c : Fin 3) (p : Labels) (d : Row) : Prop :=
  compatible p d ∧ allowed (seen t) (d 0) ∧ allowed (seen b) (d 1) ∧
    allowed (seen c) (d 2) ∧ next t (d 0) ≤ q ∧ next b (d 1) ≤ r
private instance instDecidableAdmissible (q r t b c : Fin 3) (p : Labels) (d : Row) :
    Decidable (admissible q r t b c p d) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
private theorem tailGood_cons {n : ℕ} (q r t b c : Fin 3) (p : Labels)
    (d : Row) (f : Fin n → Row) :
    TailGood q r t b c p (Fin.cons d f) ↔
      admissible q r t b c p d ∧
        TailGood q r (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d) f := by
  simp only [TailGood, chain, good, endLevel, Fin.cons_zero, Fin.tail_cons]
  by_cases ht : allowed (seen t) (d 0)
  · by_cases hb : allowed (seen b) (d 1)
    · by_cases hc : allowed (seen c) (d 2)
      · rw [advance_seen t (d 0) ht, advance_seen b (d 1) hb,
          advance_seen c (d 2) hc]
        have hq := endLevel_mono (next t (d 0)) (fun i => f i 0)
        have hr := endLevel_mono (next b (d 1)) (fun i => f i 1)
        simp only [admissible, ht, hb, hc, true_and]
        constructor
        · rintro ⟨⟨hp, hh⟩, h0, h1, h2, h3, h4⟩
          exact ⟨⟨hp, h3 ▸ hq, h4 ▸ hr⟩, hh, h0, h1, h2, h3, h4⟩
        · rintro ⟨⟨hp, _, _⟩, hh, h0, h1, h2, h3, h4⟩
          exact ⟨⟨hp, hh⟩, h0, h1, h2, h3, h4⟩
      · simp [admissible, hc]
    · simp [admissible, hb]
  · simp [admissible, ht]
private def step (w : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Labels → ℤ)
    (q r t b c : Fin 3) (p : Labels) : ℤ :=
  ∑ d : Row, if admissible q r t b c p d then
    w q r (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d) else 0
private def v : ℕ → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Labels → ℤ
  | 0, q, r, t, b, _, _ => if t = q ∧ b = r then 1 else 0
  | k + 1, q, r, t, b, c, p => step (v k) q r t b c p
private def count (n : ℕ) (q r t b c : Fin 3) (p : Labels) : ℤ :=
  ∑ f : Fin n → Row, if TailGood q r t b c p f then 1 else 0
private theorem count_eq_v (n : ℕ) : count n = v n := by
  induction n with
  | zero => funext q r t b c p; simp [count, TailGood, v, good, endLevel, chain]
  | succ n ih =>
    funext q r t b c p
    rw [count, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Row)).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ d : Row, ∑ f : Fin n → Row,
      if TailGood q r t b c p (Fin.cons d f) then (1 : ℤ) else 0) = _
    change _ = step (v n) q r t b c p
    rw [← ih]
    unfold step count
    apply Finset.sum_congr rfl
    intro d _
    by_cases h : admissible q r t b c p d <;> simp [tailGood_cons, h]
private def total (w : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Labels → ℤ) : ℤ :=
  ∑ d : Row, ∑ q : Fin 3, ∑ r : Fin 3,
    if d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2) ∧
        next q (d 1) ≤ r then
      w q r 0 (next q (d 1)) (next r (d 2)) (pairs d) else 0
private theorem counting_bridge (n : ℕ) : (a (n + 1) : ℤ) = total (v n) := by
  rw [a, Finset.natCast_card_filter]
  let e : (Fin 3 × Fin (n + 1) → Fin 6) ≃ (Fin (n + 1) → Row) :=
    { toFun := fun A j r => A (r, j)
      invFun := fun f p => f p.2 p.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.symm.sum_comp,
    ← (Fin.consEquiv (fun _ : Fin (n + 1) => Row)).sum_comp, Fintype.sum_prod_type]
  unfold total
  apply Finset.sum_congr rfl
  intro d _
  rw [← count_eq_v]
  unfold count
  trans ∑ f : Fin n → Row, ∑ q : Fin 3, ∑ r : Fin 3,
    if (d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2)) ∧
      TailGood q r 0 (next q (d 1)) (next r (d 2)) (pairs d) f then (1 : ℤ) else 0
  · apply Finset.sum_congr rfl
    intro f _
    change (if Legal (fun p => (Fin.cons d f : Fin (n + 1) → Row) p.2 p.1)
      then (1 : ℤ) else 0) = _
    simp_rw [show ∀ q r : Fin 3,
      ((d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2)) ∧
        TailGood q r 0 (next q (d 1)) (next r (d 2)) (pairs d) f) ↔
      (endLevel 0 (fun i => f i 0) = q ∧
        endLevel (next q (d 1)) (fun i => f i 1) = r ∧ d 0 = 0 ∧
        good (seen 0) (fun i => f i 0) ∧ allowed (seen q) (d 1) ∧
        good (seen (next q (d 1))) (fun i => f i 1) ∧
        allowed (seen r) (d 2) ∧ good (seen (next r (d 2))) (fun i => f i 2) ∧
        chain (pairs d) f) from fun q r => by unfold TailGood; tauto]
    simp only [ite_and, ← Finset.ite_sum_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    simp only [legal_iff]
    have htail (i : Fin 3) :
        Fin.tail (fun j => (Fin.cons d f : Fin (n + 1) → Row) j i) =
          (fun j => f j i) := by
      funext j
      simp [Fin.tail]
    by_cases hd : d 0 = 0
    · have ha : advance (false, false) (d 0) = (false, false) := by rw [hd]; rfl
      simp only [Fin.cons_zero, good, finish, ha]
      simp only [htail, Fin.tail_cons]
      have hs0 : seen 0 = (false, false) := rfl
      have ha0 : allowed (false, false) 0 := by decide +kernel
      simp only [hd, ha0, true_and, ite_true, hs0]
      by_cases ht : good (false, false) (fun i => f i 0)
      · have hft := finish_seen 0 (fun i => f i 0) ht
        change finish (false, false) (fun i => f i 0) = _ at hft
        rw [hft]
        by_cases hm : allowed (seen (endLevel 0 (fun i => f i 0))) (d 1)
        · rw [advance_seen _ _ hm]
          by_cases hb : good (seen (next (endLevel 0 (fun i => f i 0)) (d 1)))
              (fun i => f i 1)
          · rw [finish_seen _ _ hb]
            by_cases hc : allowed
                (seen (endLevel (next (endLevel 0 (fun i => f i 0)) (d 1))
                  (fun i => f i 1))) (d 2)
            · rw [advance_seen _ _ hc]
              simp [ht, hm, hb, hc, ite_and]
            · simp [ht, hm, hb, hc]
          · simp [ht, hm, hb]
        · simp [ht, hm]
      · simp [ht]
    · simp [Fin.cons_zero, hd]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    by_cases h : d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2)
    · by_cases hr : next q (d 1) ≤ r
      · simp [h.1, h.2.1, h.2.2, hr]
      · have hn : ∀ f : Fin n → Row,
            ¬ TailGood q r 0 (next q (d 1)) (next r (d 2)) (pairs d) f := by
          intro f hf
          exact hr (hf.2.2.2.2.2 ▸ endLevel_mono _ _)
        simp [hr, hn]
    · have hn : ∀ f : Fin n → Row,
          ¬ ((d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2)) ∧
            TailGood q r 0 (next q (d 1)) (next r (d 2)) (pairs d) f) :=
        fun _ hf => h hf.1
      have hh : ¬ (d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2) ∧
          next q (d 1) ≤ r) := fun hh => h ⟨hh.1, hh.2.1, hh.2.2.1⟩
      simp only [hn, hh, ite_false, Finset.sum_const_zero]
private def Valid (q r t b c : Fin 3) (p : Labels) : Prop :=
  t ≤ q ∧ q ≤ b ∧ b ≤ r ∧ r ≤ c ∧ p 0 ≤ t ∧ p 1 ≤ b ∧ p 2 ≤ c
private instance instDecidableValid (q r t b c : Fin 3) (p : Labels) :
    Decidable (Valid q r t b c p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
private theorem valid_next (q r t b c : Fin 3) (p : Labels) (d : Row)
    (h : Valid q r t b c p) (hd : admissible q r t b c p d) :
    Valid q r (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d) := by
  rcases h with ⟨_, hqb, _, hrc, _, _, _⟩
  rcases hd with ⟨_, ht, hb, hc, hq, hr⟩
  exact ⟨hq, le_trans hqb (next_mono b (d 1)), hr,
    le_trans hrc (next_mono c (d 2)), label_next t (d 0) ht,
    label_next b (d 1) hb, label_next c (d 2) hc⟩
private theorem initial_valid : ∀ d : Row, ∀ q r : Fin 3,
    d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2) ∧
      next q (d 1) ≤ r → Valid q r 0 (next q (d 1)) (next r (d 2)) (pairs d) := by
  intro d q r ⟨hd, hq, hr, hqr⟩
  refine ⟨by omega, next_mono q (d 1), hqr, next_mono r (d 2), ?_,
    label_next q (d 1) hq, label_next r (d 2) hr⟩
  change beta (d 0) ≤ 0
  rw [hd]
  decide +kernel
private def flagIndex : Array ℕ :=
  #[0,1,2,0,3,4,0,0,5,0,0,0,0,6,7,0,0,8,0,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,0,0,0,0,0,0,10,11,0,0,12,0
  ,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,14,0,0,0,0,0,0,0,0,0,0,0,0
  ,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,16,0,0,17,0,0,0,0,0,0,0,0,18,0,0,0,0
  ,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,20]
private def links : Array (Array ℕ) :=
  #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[
  ],#[],#[],#[],#[],#[],#[],#[3280,3530],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],
  #[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[3523,3532],#[],#[3523],#[],#[],#[],#[],#[],#[]
  ,#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[3523,3532,4277,4286],
  #[4286],#[3523],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],
  #[],#[],#[],#[],#[4252,4261,4279,4288],#[4288],#[4252],#[],#[],#[],#[4252],#[],#[4243,4252],#[],
  #[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[4252,4261,4279,4288],#[
  4288],#[4252],#[],#[],#[],#[4252],#[],#[4243,4252],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],
  #[],#[],#[],#[],#[],#[],#[],#[3284,3532],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[3167,
  3424],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[3527,3536],#[],#[3527],#[],#[],#[],
  #[],#[],#[],#[],#[],#[],#[],#[3410,3428],#[3410],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[]
  ,#[3527,3536,4279,4288],#[4288],#[3527],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[4207],#[3410,3428,
  4189,4207],#[3410],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[4256,4265,4283,4292],#[4292
  ],#[4256],#[],#[],#[],#[4256],#[],#[4247,4256],#[],#[],#[],#[4211],#[4139,4157,4193,4211],#[4139
  ],#[],#[4139],#[4139,4148],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[4256,4265,4283,4292,6520,6529,
  6547,6556],#[4292,6556],#[4256,6520],#[6556],#[6538,6556],#[],#[4256],#[],#[4247,4256],#[6547,
  6556],#[6556],#[],#[4211,6556],#[4139,4157,4193,4211,6484,6502,6538,6556],#[4139,6484],#[],#[
  4139],#[4139,4148],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[6443,6452,6470,6479,6524,6533,6551,6560
  ],#[6479,6560],#[6443,6524],#[6560],#[6542,6560],#[],#[6443],#[],#[6434,6443],#[6551,6560],#[
  6560],#[],#[6398,6560],#[6326,6344,6380,6398,6488,6506,6542,6560],#[6326,6488],#[],#[6326],#[
  6326,6335],#[6443,6452],#[],#[6443],#[],#[6326,6344],#[6326],#[6362,6443],#[6326,6407],#[6326,
  6335,6353,6362,6407,6416,6434,6443]]
def digit (k d : ℕ) : Fin 3 := ⟨k / d % 3, Nat.mod_lt _ (by omega)⟩
private def key (t b c : Fin 3) (p : Labels) : ℕ :=
  243*t.val + 81*b.val + 27*c.val + 9*(p 0).val + 3*(p 1).val + (p 2).val
private theorem digit_key : ∀ (t b c : Fin 3) (p : Labels),
    digit (key t b c p) 243 = t ∧ digit (key t b c p) 81 = b ∧
    digit (key t b c p) 27 = c ∧
    ![digit (key t b c p) 9, digit (key t b c p) 3, digit (key t b c p) 1] = p := by
  intro t b c p
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, ?_⟩
  · dsimp [digit, key]; omega
  · dsimp [digit, key]; omega
  · dsimp [digit, key]; omega
  · ext i
    fin_cases i <;> dsimp [digit, key] <;> omega
private def moves (q r t b c : Fin 3) (p : Labels) : Multiset ℕ :=
  ((Finset.univ.filter (admissible q r t b c p)).val.map fun d =>
    key (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d))
private def linkKeys (q r t b c : Fin 3) (p : Labels) : Multiset ℕ :=
  let i := (flagIndex.getD (81*t.val+27*q.val+9*b.val+3*r.val+c.val) 0)*27 +
    9*(p 0).val+3*(p 1).val+(p 2).val
  ((links.getD i #[]).toList.flatMap fun e => List.replicate (e % 9) (e / 9) : List ℕ)
local elab "check_states" : tactic => Lean.Elab.withEnableInfoTree false do
  Lean.Elab.Tactic.evalTactic (← `(tactic| {
    simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
    intro q r t b c
    fin_cases q <;> fin_cases r <;> fin_cases t <;> fin_cases b <;> fin_cases c
    all_goals first
      | (intro x y z h; exfalso
         rcases h with ⟨htq, hqb, hbr, hrc, _, _, _⟩; omega)
      | (intro x; fin_cases x <;> decide +kernel) }))
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private theorem moves_certificate : ∀ q r t b c p, Valid q r t b c p →
    moves q r t b c p = linkKeys q r t b c p := by check_states
private def fastStep (w : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Labels → ℤ)
    (q r t b c : Fin 3) (p : Labels) : ℤ :=
  let i := (flagIndex.getD (81*t.val+27*q.val+9*b.val+3*r.val+c.val) 0)*27 +
    9*(p 0).val+3*(p 1).val+(p 2).val
  ((links.getD i #[]).toList.map fun e => ((e % 9 : ℕ) : ℤ) *
    w q r (digit (e / 9) 243) (digit (e / 9) 81) (digit (e / 9) 27)
      ![digit (e / 9) 9, digit (e / 9) 3, digit (e / 9) 1]).sum
theorem weighted_sum (es : List ℕ) (g : ℕ → ℤ) :
    ((es.flatMap fun e => List.replicate (e % 9) (e / 9)).map g).sum =
      (es.map fun e => ((e % 9 : ℕ) : ℤ) * g (e / 9)).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_replicate, List.sum_append,
      List.sum_replicate, List.map_cons, List.sum_cons, nsmul_eq_mul, ih]
private theorem step_fast (w : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Labels → ℤ)
    (q r t b c : Fin 3) (p : Labels) (h : Valid q r t b c p) :
    step w q r t b c p = fastStep w q r t b c p := by
  let g (k : ℕ) := w q r (digit k 243) (digit k 81) (digit k 27)
    ![digit k 9, digit k 3, digit k 1]
  calc
    step w q r t b c p = ((moves q r t b c p).map g).sum := by
      simp only [moves, Multiset.map_map, Function.comp_def]
      change (∑ d : Row, if admissible q r t b c p d then
        w q r (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d) else 0) =
        ∑ d ∈ Finset.univ.filter (admissible q r t b c p),
          g (key (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d))
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : admissible q r t b c p d
      · simp only [hd, ite_true]
        dsimp [g]
        rcases digit_key (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d) with
          ⟨h0,h1,h2,h3⟩
        rw [h0,h1,h2,h3]
      · simp [hd]
    _ = ((linkKeys q r t b c p).map g).sum := by rw [moves_certificate _ _ _ _ _ _ h]
    _ = fastStep w q r t b c p := by
      unfold linkKeys fastStep
      exact weighted_sum _ g
private def tables : ℕ → Array (Array ℤ)
  | 0 => #[#[1],#[1,1],#[1,1,1],#[],#[],#[],#[1,1,0,1,1],#[1,1,1,1,1,1],#[],#[1,1,1,1,1,1,1,1,1],
    #[],#[],#[],#[],#[],#[1,1,0,1,1,0,0,0,0,1,1,0,1,1],#[1,1,1,1,1,1,0,0,0,1,1,1,1,1,1],#[],#[1,1,
    1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1],#[],#[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1]]
  | 1 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[6],#[8,0,4],#[4,2],#[16,4,4,0,0,0,4,0,8],#[],
    #[12,0,0,0,0,0,0,0,0,0,0,0,0,12],#[16,0,8,0,0,0,0,0,0,0,0,0,0,16,8],#[8,4,0,0,0,0,0,0,0,0,0,0,
    4,8],#[32,8,8,0,0,0,8,0,16,0,0,0,8,32,8,0,8,16],#[16,4,4,4,8,0,0,0,0,8,4,0,4,16,4],#[64,16,16,
    8,16,0,8,0,16,16,8,0,16,64,16,0,8,16,16,0,8,0,16,8,16,16,64]]
  | 2 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[64],#[96,0,64],#[80,32,32],#[256,64,128,0,0,0
    ,128,0,160],#[80,0,64,0,0,0,64,0,80],#[128,0,0,0,0,0,0,0,0,0,0,0,0,128],#[192,0,128,0,0,0,0,0,
    0,0,0,0,0,192,128],#[160,64,64,0,0,0,0,0,0,0,0,0,64,160,64],#[512,128,256,0,0,0,256,0,320,0,0,
    0,128,512,256,0,256,320],#[576,256,192,256,320,0,128,0,160,320,256,0,256,576,192,0,128,160],#[
    1664,640,640,512,640,0,512,0,640,640,512,0,640,1664,640,0,512,640,640,0,512,0,640,512,640,640,
    1664]]
  | 3 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[768],#[1280,0,768],#[2048,640,640],#[5376,
    1280,2048,0,0,0,2048,0,2560],#[4224,640,2304,0,0,0,2304,0,3328],#[1536,0,0,0,0,0,0,0,0,0,0,0,0
    ,1536],#[2560,0,1536,0,0,0,0,0,0,0,0,0,0,2560,1536],#[4096,1280,1280,0,0,0,0,0,0,0,0,0,1280,
    4096,1280],#[10752,2560,4096,0,0,0,4096,0,5120,0,0,0,2560,10752,4096,0,4096,5120],#[22272,7936
    ,7168,6656,9216,0,4608,0,6656,9216,6656,0,7936,22272,7168,0,4608,6656],#[55296,18432,18432,
    13312,18432,0,13312,0,18432,18432,13312,0,18432,55296,18432,0,13312,18432,18432,0,13312,0,
    18432,13312,18432,18432,55296]]
  | 4 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[9216],#[16384,0,10240],#[39936,10240,16384],
    #[96256,20480,43008,0,0,0,43008,0,53248],#[162816,26624,89088,0,0,0,89088,0,120832],#[18432,0,
    0,0,0,0,0,0,0,0,0,0,0,18432],#[32768,0,20480,0,0,0,0,0,0,0,0,0,0,32768,20480],#[79872,20480,
    32768,0,0,0,0,0,0,0,0,0,20480,79872,32768],#[192512,40960,86016,0,0,0,86016,0,106496,0,0,0,
    40960,192512,86016,0,86016,106496],#[747520,274432,251904,221184,294912,0,178176,0,241664,
    294912,221184,0,274432,747520,251904,0,178176,241664],#[1687552,589824,589824,442368,589824,0,
    442368,0,589824,589824,442368,0,589824,1687552,589824,0,442368,589824,589824,0,442368,0,589824
    ,442368,589824,589824,1687552]]
  | 5 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[114688],#[212992,0,131072],#[835584,212992,
    319488],#[1884160,425984,770048,0,0,0,770048,0,933888],#[5677056,966656,2990080,0,0,0,2990080,
    0,4087808],#[229376,0,0,0,0,0,0,0,0,0,0,0,0,229376],#[425984,0,262144,0,0,0,0,0,0,0,0,0,0,
    425984,262144],#[1671168,425984,638976,0,0,0,0,0,0,0,0,0,425984,1671168,638976],#[3768320,
    851968,1540096,0,0,0,1540096,0,1867776,0,0,0,851968,3768320,1540096,0,1540096,1867776],#[
    24592384,8683520,8339456,6750208,9109504,0,5980160,0,8175616,9109504,6750208,0,8683520,
    24592384,8339456,0,5980160,8175616],#[52953088,18219008,18219008,13500416,18219008,0,13500416,
    0,18219008,18219008,13500416,0,18219008,52953088,18219008,0,13500416,18219008,18219008,0,
    13500416,0,18219008,13500416,18219008,18219008,52953088]]
  | 6 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[1441792],#[2752512,0,1703936],#[16056320,
    3735552,6684672],#[34865152,7471104,15073280,0,0,0,15073280,0,18481152],#[188350464,32702464,
    98369536,0,0,0,98369536,0,133103616],#[2883584,0,0,0,0,0,0,0,0,0,0,0,0,2883584],#[5505024,0,
    3407872,0,0,0,0,0,0,0,0,0,0,5505024,3407872],#[32112640,7471104,13369344,0,0,0,0,0,0,0,0,0,
    7471104,32112640,13369344],#[69730304,14942208,30146560,0,0,0,30146560,0,36962304,0,0,0,
    14942208,69730304,30146560,0,30146560,36962304],#[788267008,277217280,269615104,211812352,
    284688384,0,196739072,0,266207232,284688384,211812352,0,277217280,788267008,269615104,0,
    196739072,266207232],#[1646264320,569376768,569376768,423624704,569376768,0,423624704,0,
    569376768,569376768,423624704,0,569376768,1646264320,569376768,0,423624704,569376768,569376768
    ,0,423624704,0,569376768,423624704,569376768,569376768,1646264320]]
  | 7 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[18350080],#[35651584,0,22020096],#[316145664,
    73924608,128450560],#[667942912,147849216,278921216,0,0,0,278921216,0,338690048],#[6083313664,
    1064828928,3153068032,0,0,0,3153068032,0,4261937152],#[36700160,0,0,0,0,0,0,0,0,0,0,0,0,
    36700160],#[71303168,0,44040192,0,0,0,0,0,0,0,0,0,0,71303168,44040192],#[632291328,147849216,
    256901120,0,0,0,0,0,0,0,0,0,147849216,632291328,256901120],#[1335885824,295698432,557842432,0,
    0,0,557842432,0,677380096,0,0,0,295698432,1335885824,557842432,0,557842432,677380096],#[
    25001197568,8714715136,8583643136,6585057280,8862564352,0,6306136064,0,8523874304,8862564352,
    6585057280,0,8714715136,25001197568,8583643136,0,6306136064,8523874304],#[51338280960,
    17725128704,17725128704,13170114560,17725128704,0,13170114560,0,17725128704,17725128704,
    13170114560,0,17725128704,51338280960,17725128704,0,13170114560,17725128704,17725128704,0,
    13170114560,0,17725128704,13170114560,17725128704,17725128704,51338280960]]
  | 8 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[234881024],#[461373440,0,285212672],#[
    6027214848,1354760192,2529165312],#[12515803136,2709520384,5343543296,0,0,0,5343543296,0,
    6526337024],#[193659404288,34095497216,100004790272,0,0,0,100004790272,0,134863650816],#[
    469762048,0,0,0,0,0,0,0,0,0,0,0,0,469762048],#[922746880,0,570425344,0,0,0,0,0,0,0,0,0,0,
    922746880,570425344],#[12054429696,2709520384,5058330624,0,0,0,0,0,0,0,0,0,2709520384,
    12054429696,5058330624],#[25031606272,5419040768,10687086592,0,0,0,10687086592,0,13052674048,0
    ,0,0,5419040768,25031606272,10687086592,0,10687086592,13052674048],#[787153420288,273544118272
    ,270910095360,205353123840,276253638656,0,200009580544,0,269727301632,276253638656,
    205353123840,0,273544118272,787153420288,270910095360,0,200009580544,269727301632],#[
    1599338446848,552507277312,552507277312,410706247680,552507277312,0,410706247680,0,
    552507277312,552507277312,410706247680,0,552507277312,1599338446848,552507277312,0,
    410706247680,552507277312,552507277312,0,410706247680,0,552507277312,410706247680,552507277312
    ,552507277312,1599338446848]]
  | 9 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[3019898880],#[5972688896,0,3690987520],#[
    115930562560,26105348096,48217718784],#[237833814016,52210696192,100126425088,0,0,0,
    100126425088,0,121802588160],#[6111201591296,1078909206528,3148613681152,0,0,0,3148613681152,0
    ,4242790154240],#[6039797760,0,0,0,0,0,0,0,0,0,0,0,0,6039797760],#[11945377792,0,7381975040,0,
    0,0,0,0,0,0,0,0,0,11945377792,7381975040],#[231861125120,52210696192,96435437568,0,0,0,0,0,0,0
    ,0,0,52210696192,231861125120,96435437568],#[475667628032,104421392384,200252850176,0,0,0,
    200252850176,0,243605176320,0,0,0,104421392384,475667628032,200252850176,0,200252850176,
    243605176320],#[24682640179200,8555172200448,8507256471552,6397353787392,8607382896640,0,
    6297227362304,0,8485580308480,8607382896640,6397353787392,0,8555172200448,24682640179200,
    8507256471552,0,6297227362304,8485580308480],#[49840947986432,17214765793280,17214765793280,
    12794707574784,17214765793280,0,12794707574784,0,17214765793280,17214765793280,12794707574784,
    0,17214765793280,49840947986432,17214765793280,0,12794707574784,17214765793280,17214765793280,
    0,12794707574784,0,17214765793280,12794707574784,17214765793280,17214765793280,49840947986432]
    ]
  | 10 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[38923141120],#[77309411328,0,47781511168],#[
    2200902303744,487210352640,927444500480],#[4479114018816,974420705280,1902670512128,0,0,0,
    1902670512128,0,2320356081664],#[191890817286144,33942321233920,98730560716800,0,0,0,
    98730560716800,0,132951249518592],#[77846282240,0,0,0,0,0,0,0,0,0,0,0,0,77846282240],#[
    154618822656,0,95563022336,0,0,0,0,0,0,0,0,0,0,154618822656,95563022336],#[4401804607488,
    974420705280,1854889000960,0,0,0,0,0,0,0,0,0,974420705280,4401804607488,1854889000960],#[
    8958228037632,1948841410560,3805341024256,0,0,0,3805341024256,0,4640712163328,0,0,0,
    1948841410560,8958228037632,3805341024256,0,3805341024256,4640712163328],#[772042383163392,
    267248434413568,266320184606720,199363791945728,268222855118848,0,197461121433600,0,
    265902499037184,268222855118848,199363791945728,0,267248434413568,772042383163392,
    266320184606720,0,197461121433600,265902499037184],#[1553042994364416,536445710237696,
    536445710237696,398727583891456,536445710237696,0,398727583891456,0,536445710237696,
    536445710237696,398727583891456,0,536445710237696,1553042994364416,536445710237696,0,
    398727583891456,536445710237696,536445710237696,0,398727583891456,0,536445710237696,
    398727583891456,536445710237696,536445710237696,1553042994364416]]
  | 11 => #[#[],#[],#[],#[],#[],#[],#[],#[],#[],#[],#[502511173632],#[1000727379968,0,618475290624
    ],#[41918880808960,9281424326656,17607218429952],#[84838488997888,18562848653312,
    35832912150528,0,0,0,35832912150528,0,43628277792768],#[6006904752963584,1063609996148736,
    3088169532653568,0,0,0,3088169532653568,0,4157163270307840],#[1005022347264,0,0,0,0,0,0,0,0,0,
    0,0,0,1005022347264],#[2001454759936,0,1236950581248,0,0,0,0,0,0,0,0,0,0,2001454759936,
    1236950581248],#[83837761617920,18562848653312,35214436859904,0,0,0,0,0,0,0,0,0,18562848653312
    ,83837761617920,35214436859904],#[169676977995776,37125697306624,71665824301056,0,0,0,
    71665824301056,0,87256555585536,0,0,0,37125697306624,169676977995776,71665824301056,0,
    71665824301056,87256555585536],#[24112457500852224,8339391969755136,8322121906257920,
    6212171977457664,8357954818408448,0,6176339065307136,0,8314326540615680,8357954818408448,
    6212171977457664,0,8339391969755136,24112457500852224,8322121906257920,0,6176339065307136,
    8314326540615680],#[48394591979700224,16715909636816896,16715909636816896,12424343954915328,
    16715909636816896,0,12424343954915328,0,16715909636816896,16715909636816896,12424343954915328,
    0,16715909636816896,48394591979700224,16715909636816896,0,12424343954915328,16715909636816896,
    16715909636816896,0,12424343954915328,0,16715909636816896,12424343954915328,16715909636816896,
    16715909636816896,48394591979700224]]
  | _ => #[]
private def table (k : ℕ) (q r t b c : Fin 3) (p : Labels) : ℤ :=
  let i := (flagIndex.getD (81 * t.val + 27 * q.val + 9 * b.val + 3 * r.val + c.val) 0)
  ((tables k).getD i #[]).getD
    (9 * (p 0).val + 3 * (p 1).val + (p 2).val) 0
local macro "check_step" : tactic => `(tactic| {
  intro q r t b c p h
  rw [step_fast _ q r t b c p h]
  revert q r t b c p
  check_states })
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
private theorem table_base : ∀ q r t b c p, Valid q r t b c p →
    table 0 q r t b c p = v 0 q r t b c p := by
  check_states
private theorem table_step0 : ∀ q r t b c p, Valid q r t b c p →
    table 1 q r t b c p = step (table 0) q r t b c p := by check_step
private theorem table_step1 : ∀ q r t b c p, Valid q r t b c p →
    table 2 q r t b c p = step (table 1) q r t b c p := by check_step
private theorem table_step2 : ∀ q r t b c p, Valid q r t b c p →
    table 3 q r t b c p = step (table 2) q r t b c p := by check_step
private theorem table_step3 : ∀ q r t b c p, Valid q r t b c p →
    table 4 q r t b c p = step (table 3) q r t b c p := by check_step
private theorem table_step4 : ∀ q r t b c p, Valid q r t b c p →
    table 5 q r t b c p = step (table 4) q r t b c p := by check_step
private theorem table_step5 : ∀ q r t b c p, Valid q r t b c p →
    table 6 q r t b c p = step (table 5) q r t b c p := by check_step
private theorem table_step6 : ∀ q r t b c p, Valid q r t b c p →
    table 7 q r t b c p = step (table 6) q r t b c p := by check_step
private theorem table_step7 : ∀ q r t b c p, Valid q r t b c p →
    table 8 q r t b c p = step (table 7) q r t b c p := by check_step
private theorem table_step8 : ∀ q r t b c p, Valid q r t b c p →
    table 9 q r t b c p = step (table 8) q r t b c p := by check_step
private theorem table_step9 : ∀ q r t b c p, Valid q r t b c p →
    table 10 q r t b c p = step (table 9) q r t b c p := by check_step
private theorem table_step10 : ∀ q r t b c p, Valid q r t b c p →
    table 11 q r t b c p = step (table 10) q r t b c p := by check_step
private theorem table_steps (k : Fin 11) : ∀ q r t b c p, Valid q r t b c p →
    table (k.val + 1) q r t b c p = step (table k.val) q r t b c p := by
  fin_cases k
  · exact table_step0
  · exact table_step1
  · exact table_step2
  · exact table_step3
  · exact table_step4
  · exact table_step5
  · exact table_step6
  · exact table_step7
  · exact table_step8
  · exact table_step9
  · exact table_step10
private theorem v_table (k : ℕ) (hk : k ≤ 11) :
    ∀ q r t b c p, Valid q r t b c p → v k q r t b c p = table k q r t b c p := by
  induction k with
  | zero => exact fun q r t b c p h => (table_base q r t b c p h).symm
  | succ k ih =>
    intro q r t b c p h
    rw [v, table_steps ⟨k, by omega⟩ q r t b c p h]
    unfold step
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : admissible q r t b c p d
    · simp only [ite_eq_left hd]
      exact ih (by omega) _ _ _ _ _ _ (valid_next q r t b c p d h hd)
    · simp only [ite_eq_right hd]
private theorem table_certificate : ∀ q r t b c p, Valid q r t b c p →
    table 11 q r t b c p =
      48 * table 10 q r t b c p
      - 192 * table 9 q r t b c p
      - 15360 * table 8 q r t b c p
      + 118784 * table 7 q r t b c p
      + 1605632 * table 6 q r t b c p
      - 12845056 * table 5 q r t b c p
      - 60817408 * table 4 q r t b c p
      + 436207616 * table 3 q r t b c p
      + 805306368 * table 2 q r t b c p
      - 4294967296 * table 1 q r t b c p := by
  check_states
private theorem vector_certificate : ∀ q r t b c p, Valid q r t b c p →
    v 11 q r t b c p =
      48 * v 10 q r t b c p
      - 192 * v 9 q r t b c p
      - 15360 * v 8 q r t b c p
      + 118784 * v 7 q r t b c p
      + 1605632 * v 6 q r t b c p
      - 12845056 * v 5 q r t b c p
      - 60817408 * v 4 q r t b c p
      + 436207616 * v 3 q r t b c p
      + 805306368 * v 2 q r t b c p
      - 4294967296 * v 1 q r t b c p := by
  intro q r t b c p h
  simp only [v_table 11 (by omega) q r t b c p h,
    v_table 10 (by omega) q r t b c p h,
    v_table 9 (by omega) q r t b c p h,
    v_table 8 (by omega) q r t b c p h,
    v_table 7 (by omega) q r t b c p h,
    v_table 6 (by omega) q r t b c p h,
    v_table 5 (by omega) q r t b c p h,
    v_table 4 (by omega) q r t b c p h,
    v_table 3 (by omega) q r t b c p h,
    v_table 2 (by omega) q r t b c p h,
    v_table 1 (by omega) q r t b c p h]
  exact table_certificate q r t b c p h
private theorem vector_recurrence (k : ℕ) :
    ∀ q r t b c p, Valid q r t b c p → v (k + 11) q r t b c p =
      48 * v (k + 10) q r t b c p
      - 192 * v (k + 9) q r t b c p
      - 15360 * v (k + 8) q r t b c p
      + 118784 * v (k + 7) q r t b c p
      + 1605632 * v (k + 6) q r t b c p
      - 12845056 * v (k + 5) q r t b c p
      - 60817408 * v (k + 4) q r t b c p
      + 436207616 * v (k + 3) q r t b c p
      + 805306368 * v (k + 2) q r t b c p
      - 4294967296 * v (k + 1) q r t b c p := by
  induction k with
  | zero => exact vector_certificate
  | succ k ih =>
    intro q r t b c p h
    change step (v (k + 11)) q r t b c p =
      48 * step (v (k + 10)) q r t b c p
      - 192 * step (v (k + 9)) q r t b c p
      - 15360 * step (v (k + 8)) q r t b c p
      + 118784 * step (v (k + 7)) q r t b c p
      + 1605632 * step (v (k + 6)) q r t b c p
      - 12845056 * step (v (k + 5)) q r t b c p
      - 60817408 * step (v (k + 4)) q r t b c p
      + 436207616 * step (v (k + 3)) q r t b c p
      + 805306368 * step (v (k + 2)) q r t b c p
      - 4294967296 * step (v (k + 1)) q r t b c p
    unfold step
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : admissible q r t b c p d
    · simpa only [ite_eq_left hd] using
        ih q r (next t (d 0)) (next b (d 1)) (next c (d 2)) (pairs d)
          (valid_next q r t b c p d h hd)
    · simp only [ite_eq_right hd, mul_zero, add_zero, sub_zero]
private theorem total_recurrence (k : ℕ) : total (v (k + 11)) =
      48 * total (v (k + 10))
      - 192 * total (v (k + 9))
      - 15360 * total (v (k + 8))
      + 118784 * total (v (k + 7))
      + 1605632 * total (v (k + 6))
      - 12845056 * total (v (k + 5))
      - 60817408 * total (v (k + 4))
      + 436207616 * total (v (k + 3))
      + 805306368 * total (v (k + 2))
      - 4294967296 * total (v (k + 1)) := by
  unfold total
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2) ∧
      next q (d 1) ≤ r
  · simpa only [ite_eq_left h] using
      vector_recurrence k q r 0 (next q (d 1)) (next r (d 2)) (pairs d)
        (initial_valid d q r h)
  · simp only [ite_eq_right h, mul_zero, add_zero, sub_zero]
private theorem total_table (k : ℕ) (hk : k ≤ 11) : total (v k) = total (table k) := by
  unfold total
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  by_cases h : d 0 = 0 ∧ allowed (seen q) (d 1) ∧ allowed (seen r) (d 2) ∧
      next q (d 1) ≤ r
  · simp only [ite_eq_left h]
    exact v_table k hk _ _ _ _ _ _ (initial_valid d q r h)
  · simp only [ite_eq_right h]
private theorem initial_table0 : total (table 0) = 11 := by decide +kernel
private theorem initial_table1 : total (table 1) = 80 := by decide +kernel
private theorem initial_table2 : total (table 2) = 2688 := by decide +kernel
private theorem initial_table3 : total (table 3) = 78336 := by decide +kernel
private theorem initial_table4 : total (table 4) = 2469888 := by decide +kernel
private theorem initial_table5 : total (table 5) = 76447744 := by decide +kernel
private theorem initial_table6 : total (table 6) = 2385772544 := by decide +kernel
private theorem initial_table7 : total (table 7) = 74291609600 := by decide +kernel
private theorem initial_table8 : total (table 8) = 2315406802944 := by decide +kernel
private theorem initial_table9 : total (table 9) = 72144847372288 := by decide +kernel
private theorem initial_table10 : total (table 10) = 2248141575290880 := by decide +kernel
/-- Initial coefficients of the literal filtered count, including its empty convention. -/
theorem finite_certificate : (a 0 : ℤ) = 0 ∧ (a 1 : ℤ) = 11 ∧ (a 2 : ℤ) = 80 ∧ (a 3 : ℤ) = 2688 ∧
    (a 4 : ℤ) = 78336 ∧ (a 5 : ℤ) = 2469888 ∧ (a 6 : ℤ) = 76447744 ∧ (a 7 : ℤ) = 2385772544 ∧
    (a 8 : ℤ) = 74291609600 ∧ (a 9 : ℤ) = 2315406802944 ∧ (a 10 : ℤ) = 72144847372288 ∧
    (a 11 : ℤ) = 2248141575290880 := by
  refine ⟨by simp [a, Legal], ?_⟩
  simp only [counting_bridge]
  simp only [
    total_table 0 (by omega), initial_table0, total_table 1 (by omega), initial_table1,
    total_table 2 (by omega), initial_table2, total_table 3 (by omega), initial_table3,
    total_table 4 (by omega), initial_table4, total_table 5 (by omega), initial_table5,
    total_table 6 (by omega), initial_table6, total_table 7 (by omega), initial_table7,
    total_table 8 (by omega), initial_table8, total_table 9 (by omega), initial_table9,
    total_table 10 (by omega), initial_table10, and_self]
private def err (n : ℕ) : ℤ :=
  (a (n + 4) : ℤ) - 32 * a (n + 3) - 64 * a (n + 2) +
    3072 * a (n + 1) - 8192 * a n
private theorem error_recurrence (k : ℕ) :
    err (k + 8) = 16 * err (k + 7) + 256 * err (k + 6) -
      3072 * err (k + 5) - 20480 * err (k + 4) +
      98304 * err (k + 3) + 524288 * err (k + 2) := by
  have h := total_recurrence k
  simp only [← counting_bridge] at h
  simp only [err, Nat.add_assoc]
  linarith
private theorem error_vanish (k : ℕ) : err (k + 2) = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k < 6
    · rcases finite_certificate with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩
      interval_cases k <;>
        norm_num only [err, Nat.reduceAdd, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11]
    · have hr := error_recurrence (k - 6)
      have h1 := ih (k - 1) (by omega)
      have h2 := ih (k - 2) (by omega)
      have h3 := ih (k - 3) (by omega)
      have h4 := ih (k - 4) (by omega)
      have h5 := ih (k - 5) (by omega)
      have h6 := ih (k - 6) (by omega)
      have e0 : k - 6 + 8 = k + 2 := by omega
      have e1 : k - 6 + 7 = k - 1 + 2 := by omega
      have e2 : k - 6 + 6 = k - 2 + 2 := by omega
      have e3 : k - 6 + 5 = k - 3 + 2 := by omega
      have e4 : k - 6 + 4 = k - 4 + 2 := by omega
      have e5 : k - 6 + 3 = k - 5 + 2 := by omega
      rw [e0,e1,e2,e3,e4,e5,h1,h2,h3,h4,h5,h6] at hr
      simpa using hr
private theorem recurrence (n : ℕ) (hn : 6 ≤ n) :
    (a n : ℤ) = 32 * a (n - 1) + 64 * a (n - 2) -
      3072 * a (n - 3) + 8192 * a (n - 4) := by
  have h := error_vanish (n - 6)
  simp only [err] at h
  have e0 : n - 6 + 2 + 4 = n := by omega
  have e1 : n - 6 + 2 + 3 = n - 1 := by omega
  have e2 : n - 6 + 2 + 2 = n - 2 := by omega
  have e3 : n - 6 + 2 + 1 = n - 3 := by omega
  have e4 : n - 6 + 2 = n - 4 := by omega
  rw [e0,e1,e2,e3,e4] at h
  linarith
open PowerSeries
/-- Barker's generating function, with the coefficient at width zero equal to zero. -/
theorem result :
    (1 - 8 * X) * (1 - 24 * X - 256 * X ^ 2 + 1024 * X ^ 3) *
      (PowerSeries.mk fun n => (a n : ℤ)) =
        X * (11 - 272 * X - 576 * X ^ 2 + 20992 * X ^ 3 - 53248 * X ^ 4) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  change (1 - 8 * X) * (1 - 24 * X - 256 * X ^ 2 + 1024 * X ^ 3) * F = _
  have he : (1 - 8 * X) * (1 - 24 * X - 256 * X ^ 2 + 1024 * X ^ 3) * F =
      F - 32 * (F * X ^ 1) - 64 * (F * X ^ 2) +
        3072 * (F * X ^ 3) - 8192 * (F * X ^ 4) := by ring
  have hr : (X * (11 - 272 * X - 576 * X ^ 2 + 20992 * X ^ 3 - 53248 * X ^ 4) :
      PowerSeries ℤ) = 11 * X - 272 * X ^ 2 - 576 * X ^ 3 +
        20992 * X ^ 4 - 53248 * X ^ 5 := by ring
  rw [he, hr]
  ext n
  simp only [map_add, map_sub, coeff_ofNat_mul, coeff_mul_X_pow',
    coeff_X, coeff_X_pow, F, coeff_mk]
  by_cases hn : 6 ≤ n
  · simp only [ite_eq_left (show 1 ≤ n by omega), ite_eq_left (show 2 ≤ n by omega),
      ite_eq_left (show 3 ≤ n by omega), ite_eq_left (show 4 ≤ n by omega),
      ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega), ite_eq_right (show n ≠ 4 by omega),
      ite_eq_right (show n ≠ 5 by omega)]
    have hh := recurrence n hn
    linarith
  · rcases finite_certificate with ⟨h0,h1,h2,h3,h4,h5,_⟩
    interval_cases n <;> norm_num only [h0,h1,h2,h3,h4,h5,ite_true,ite_false]
end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder
