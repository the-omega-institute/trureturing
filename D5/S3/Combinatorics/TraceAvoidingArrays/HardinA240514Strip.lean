/- GID: D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip
   generality: G
   mirror-B: D5/B/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.result; premises=D5/S3/Combinatorics/TraceAvoidingArrays/HardinA240514Strip.finite_certificate
   digest: Literal three-column binary strip counts satisfy Hardin's order-twenty recurrence. -/

/-
admission_basis: open-problem-resolution (#27079; Proved)
escape_witness: none (open-problem-resolution; the settlement itself is the new content)
Direct frozen dependencies: HardinA240513Ladder.equalBit.
Proof shapes and consumers are listed below; every declaration, including the counting
induction, the bounded table checks and the linear propagation, is bind-only.
horizontal: proof_shape=bind-only; consumers=Legal, Boundary, Interior
Legal: proof_shape=bind-only; consumers=a, legal_iff
instDecidableLegal: proof_shape=bind-only; consumers=a
a: proof_shape=bind-only; consumers=counting_bridge, singleton, result
Boundary: proof_shape=bind-only; consumers=TailGood, v, total
Interior: proof_shape=bind-only; consumers=TailGood, step
instDecidableBoundary: proof_shape=bind-only; consumers=v, total
instDecidableInterior: proof_shape=bind-only; consumers=step
TailGood: proof_shape=bind-only; consumers=tailGood_cons, legal_iff, count
instDecidableTailGood: proof_shape=bind-only; consumers=count
tailGood_cons: proof_shape=bind-only; consumers=count_eq_v
legal_iff: proof_shape=bind-only; consumers=counting_bridge
step: proof_shape=bind-only; consumers=v, count_eq_v, table_steps, vector_recurrence
v: proof_shape=bind-only; consumers=count_eq_v, finite_certificate, vector_recurrence, total_recurrence
count: proof_shape=bind-only; consumers=count_eq_v
count_eq_v: proof_shape=bind-only; consumers=counting_bridge
total: proof_shape=bind-only; consumers=counting_bridge, total_recurrence, initial_recurrence
counting_bridge: proof_shape=bind-only; consumers=result
tables: proof_shape=bind-only; consumers=table
table: proof_shape=bind-only; consumers=table_base, table_steps, v_table, table_certificate, initial_recurrence
v_table: proof_shape=bind-only; consumers=finite_certificate, initial_recurrence
table_base: proof_shape=bind-only; consumers=v_table
table_steps: proof_shape=bind-only; consumers=v_table
table_certificate: proof_shape=bind-only; consumers=finite_certificate
finite_certificate: proof_shape=bind-only; consumers=vector_recurrence
vector_recurrence: proof_shape=bind-only; consumers=total_recurrence
total_recurrence: proof_shape=bind-only; consumers=result
singleton: proof_shape=bind-only; consumers=initial_recurrence
initial_recurrence: proof_shape=bind-only; consumers=result
result: proof_shape=bind-only; consumers=terminal result
-/

import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
import Mathlib.Tactic

/-!
Hardin's three-column binary strips exclude exactly two equal orthogonal neighbours
at each cell. The finite transfer relation retains both open end boundaries.
-/

namespace D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip

open HardinA240513Ladder (equalBit)

/-- Equal-valued horizontal neighbours, with open left and right boundaries. -/
def horizontal (r : (Fin 3 → Bool)) (j : Fin 3) : ℕ :=
  (if h : 0 < j.val then equalBit (r ⟨j.val - 1, by omega⟩) (r j) else 0) +
  (if h : j.val + 1 < 3 then equalBit (r ⟨j.val + 1, h⟩) (r j) else 0)

private def Legal {n : ℕ} (A : Fin n × Fin 3 → Bool) : Prop :=
  (∃ i : Fin n, i.val = 0 ∧ A (i, 0) = false) ∧
  ∀ (i : Fin n) (j : Fin 3),
    horizontal (fun c => A (i, c)) j +
      (if h : 0 < i.val then
        equalBit (A (⟨i.val - 1, by omega⟩, j)) (A (i, j)) else 0) +
      (if h : i.val + 1 < n then
        equalBit (A (⟨i.val + 1, h⟩, j)) (A (i, j)) else 0) ≠ 2

private instance instDecidableLegal {n : ℕ} (A : Fin n × Fin 3 → Bool) :
    Decidable (Legal A) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ ∀ _ _, (_ : ℕ) ≠ 2))

/-- The literal filtered count of boards, with first entry false. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin n × Fin 3 → Bool => Legal A)).card

def Boundary (r s : (Fin 3 → Bool)) : Prop :=
  ∀ j, horizontal r j + equalBit (s j) (r j) ≠ 2

def Interior (r s t : (Fin 3 → Bool)) : Prop :=
  ∀ j, horizontal s j + equalBit (r j) (s j) + equalBit (t j) (s j) ≠ 2

private instance instDecidableBoundary (r s : (Fin 3 → Bool)) : Decidable (Boundary r s) :=
  inferInstanceAs (Decidable (∀ _ : Fin 3, (_ : ℕ) ≠ 2))

private instance instDecidableInterior (r s t : (Fin 3 → Bool)) : Decidable (Interior r s t) :=
  inferInstanceAs (Decidable (∀ _ : Fin 3, (_ : ℕ) ≠ 2))

private def TailGood (k : ℕ) (f : Fin (k + 2) → (Fin 3 → Bool)) : Prop :=
  Boundary (f (Fin.last (k + 1))) (f (Fin.last k).castSucc) ∧
  ∀ i : Fin k, Interior (f i.castSucc.castSucc) (f i.castSucc.succ) (f i.succ.succ)

private instance instDecidableTailGood (k : ℕ) (f : Fin (k + 2) → (Fin 3 → Bool)) :
    Decidable (TailGood k f) :=
  inferInstanceAs (Decidable ((_ : Prop) ∧ ∀ _ : Fin k, (_ : Prop)))

private theorem tailGood_cons (k : ℕ) (r : (Fin 3 → Bool)) (f : Fin (k + 2) → (Fin 3 → Bool)) :
    TailGood (k + 1) (Fin.cons r f) ↔ Interior r (f 0) (f 1) ∧ TailGood k f := by
  simp only [TailGood, Fin.forall_fin_succ, Fin.castSucc_zero, Fin.cons_zero,
    Fin.succ_zero_eq_one, Fin.cons_succ, Fin.castSucc_succ, Fin.cons_last]
  tauto

private theorem legal_iff (k : ℕ) (A : Fin (k + 2) × Fin 3 → Bool) :
    Legal A ↔ A (0, 0) = false ∧
      Boundary (fun j => A (0, j)) (fun j => A (1, j)) ∧
      TailGood k (fun i j => A (i, j)) := by
  have first : (∃ i : Fin (k + 2), i.val = 0 ∧ A (i, 0) = false) ↔
      A (0, 0) = false := by
    constructor
    · rintro ⟨i, hi, h⟩
      simpa only [show i = 0 from Fin.ext hi] using h
    · exact fun h => ⟨0, rfl, h⟩
  rw [Legal, first]
  apply and_congr_right
  intro _
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simpa [Boundary] using h 0 j
    · intro j
      have prev : (⟨k, by omega⟩ : Fin (k + 2)) = (Fin.last k).castSucc := Fin.ext rfl
      simpa [Boundary, Fin.val_last, prev] using h (Fin.last (k + 1)) j
    · intro i j
      have hp : 0 < i.castSucc.succ.val := by simp
      have hn : i.castSucc.succ.val + 1 < k + 2 := by simp only [Fin.val_succ, Fin.val_castSucc]; omega
      have prev : (⟨i.val, by omega⟩ : Fin (k + 2)) = i.castSucc.castSucc := Fin.ext rfl
      have next : (⟨i.val + 1 + 1, by omega⟩ : Fin (k + 2)) = i.succ.succ := Fin.ext rfl
      simpa [Interior, hp, hn, prev, next] using h i.castSucc.succ j
  · rintro ⟨ht, hb, hm⟩ i j
    by_cases hi : i.val = 0
    · have he : i = 0 := Fin.ext hi
      subst i
      simpa [Boundary] using ht j
    · by_cases hl : i.val = k + 1
      · have he : i = Fin.last (k + 1) := Fin.ext hl
        subst i
        have prev : (⟨k, by omega⟩ : Fin (k + 2)) = (Fin.last k).castSucc := Fin.ext rfl
        simpa [Boundary, Fin.val_last, prev] using hb j
      · let p : Fin k := ⟨i.val - 1, by omega⟩
        have prev : p.castSucc.castSucc = ⟨i.val - 1, by omega⟩ := Fin.ext rfl
        have cur : p.castSucc.succ = i := Fin.ext (by dsimp [p]; omega)
        have next : p.succ.succ = ⟨i.val + 1, by omega⟩ := Fin.ext (by dsimp [p]; omega)
        simpa only [Interior, prev, cur, next,
          dite_eq_left (show 0 < i.val by omega),
          dite_eq_left (show i.val + 1 < k + 2 by omega)] using hm p j

def step (w : (Fin 3 → Bool) → (Fin 3 → Bool) → ℤ) (r s : (Fin 3 → Bool)) : ℤ :=
  ∑ t : (Fin 3 → Bool), if Interior r s t then w s t else 0

def v : ℕ → (Fin 3 → Bool) → (Fin 3 → Bool) → ℤ
  | 0, r, s => if Boundary s r then 1 else 0
  | k + 1, r, s => step (v k) r s

private def count (k : ℕ) (r s : (Fin 3 → Bool)) : ℤ :=
  ∑ f : Fin k → (Fin 3 → Bool), if TailGood k (Fin.cons r (Fin.cons s f)) then 1 else 0

private theorem count_eq_v (k : ℕ) : count k = v k := by
  induction k with
  | zero => funext r s; simp [count, v, TailGood]
  | succ k ih =>
    funext r s
    rw [count, ← (Fin.consEquiv (fun _ : Fin (k + 1) => (Fin 3 → Bool))).sum_comp]
    rw [Fintype.sum_prod_type]
    change (∑ t : (Fin 3 → Bool), ∑ f : Fin k → (Fin 3 → Bool),
      if TailGood (k + 1) (Fin.cons r (Fin.cons s (Fin.cons t f))) then (1 : ℤ) else 0) = _
    change _ = step (v k) r s
    rw [← ih]
    unfold step count
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : Interior r s t <;> simp [tailGood_cons, h]

private def total (w : (Fin 3 → Bool) → (Fin 3 → Bool) → ℤ) : ℤ :=
  ∑ r : (Fin 3 → Bool), ∑ s : (Fin 3 → Bool), if r 0 = false ∧ Boundary r s then w r s else 0

private theorem counting_bridge (k : ℕ) : (a (k + 2) : ℤ) = total (v k) := by
  rw [a, Finset.natCast_card_filter]
  let e : (Fin (k + 2) × Fin 3 → Bool) ≃ (Fin (k + 2) → (Fin 3 → Bool)) := Equiv.curry _ _ _
  trans ∑ f : Fin (k + 2) → (Fin 3 → Bool),
    if f 0 0 = false ∧ Boundary (f 0) (f 1) ∧ TailGood k f then (1 : ℤ) else 0
  · rw [← e.sum_comp]
    apply Finset.sum_congr rfl
    intro A _
    simp only [e, Equiv.curry_apply, Function.curry, legal_iff]
    rfl
  · rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => (Fin 3 → Bool))).sum_comp,
      Fintype.sum_prod_type]
    unfold total
    apply Finset.sum_congr rfl
    intro r _
    rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => (Fin 3 → Bool))).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    change (∑ f : Fin k → (Fin 3 → Bool),
      if r 0 = false ∧ Boundary r s ∧ TailGood k (Fin.cons r (Fin.cons s f))
        then (1 : ℤ) else 0) = _
    by_cases h : r 0 = false ∧ Boundary r s
    · simp only [h.1, h.2, true_and]
      exact congrFun (congrFun (count_eq_v k) r) s
    · have hh : ∀ p : Prop, ¬ (r 0 = false ∧ Boundary r s ∧ p) := by tauto
      simp [h, hh]

private def tables : Array (Array ℤ) := #[
  #[0,0,1,1,0,1,1,0,0,0,1,0,0,1,1,0,0,0,1,0,0,1,0,1,0,0,1,0,1,1,0,0,0,0,1,1,0,1,0,0,1,0,1,0,0,1,0,
    0,0,1,1,0,0,1,0,0,0,1,1,0,1,1,0,0],
  #[1,0,2,1,0,1,1,1,1,0,2,1,1,1,1,0,0,1,1,0,1,3,0,1,0,1,1,0,1,2,1,1,1,1,2,1,0,1,1,0,1,0,3,1,0,1,1,
    0,0,1,1,1,1,2,0,1,1,1,1,0,1,2,0,1],
  #[3,1,4,1,1,5,1,1,1,1,5,2,2,4,1,0,1,3,3,1,3,7,1,2,0,2,4,1,1,5,2,1,1,2,5,1,1,4,2,0,2,1,7,3,1,3,3,
    1,0,1,4,2,2,5,1,1,1,1,5,1,1,4,1,3],
  #[7,2,9,1,2,14,1,5,2,1,13,5,6,10,1,1,3,7,7,2,7,21,2,6,1,5,10,1,1,13,6,2,2,6,13,1,1,10,5,1,6,2,
    21,7,2,7,7,3,1,1,10,6,5,13,1,2,5,1,14,2,1,9,2,7],
  #[16,3,27,1,3,38,1,14,3,2,36,13,16,28,2,2,7,18,21,6,18,55,6,19,2,13,28,2,2,36,16,3,3,16,36,2,2,
    28,13,2,19,6,55,18,6,21,18,7,2,2,28,16,13,36,2,3,14,1,38,3,1,27,3,16],
  #[43,5,74,2,5,98,2,38,4,3,98,36,44,73,4,3,16,49,55,16,49,150,16,52,3,36,73,3,4,98,44,4,4,44,98,
    4,3,73,36,3,52,16,150,49,16,55,49,16,3,4,73,44,36,98,3,4,38,2,98,5,2,74,5,43],
  #[117,7,202,4,7,264,4,98,7,4,267,98,117,199,7,5,43,134,150,44,134,403,44,136,5,98,199,4,7,267,
    117,7,7,117,267,7,4,199,98,5,136,44,403,134,44,150,134,43,5,7,199,117,98,267,4,7,98,4,264,7,4,
    202,7,117],
  #[319,11,539,7,11,714,7,264,11,7,717,267,316,537,12,7,117,365,403,117,365,1088,117,362,7,267,
    537,7,12,717,316,11,11,316,717,12,7,537,267,7,362,117,1088,365,117,403,365,117,7,12,537,316,
    267,717,7,11,264,7,714,11,7,539,11,319],
  #[858,18,1450,12,18,1935,12,714,18,11,1932,717,853,1453,19,11,319,984,1088,316,984,2934,316,978,
    11,717,1453,11,19,1932,853,18,18,853,1932,19,11,1453,717,11,978,316,2934,984,316,1088,984,319,
    11,19,1453,853,717,1932,11,18,714,12,1935,18,12,1450,18,858],
  #[2308,29,3912,19,29,5221,19,1935,30,18,5212,1932,2306,3918,30,18,858,2649,2934,853,2649,7919,
    853,2649,18,1932,3918,18,30,5212,2306,30,30,2306,5212,30,18,3918,1932,18,2649,853,7919,2649,
    853,2934,2649,858,18,30,3918,2306,1932,5212,18,30,1935,19,5221,29,19,3912,29,2308],
  #[6220,48,10568,30,48,14075,30,5221,48,30,14070,5212,6224,10568,48,29,2308,7144,7919,2306,7144,
    21364,2306,7156,29,5212,10568,30,48,14070,6224,48,48,6224,14070,48,30,10568,5212,29,7156,2306,
    21364,7144,2306,7919,7144,2308,29,48,10568,6224,5212,14070,30,48,5221,30,14075,48,30,10568,48,
    6220],
  #[16788,78,28520,48,78,37960,48,14075,78,48,37970,14070,16792,28508,77,48,6220,19282,21364,6224,
    19282,57647,6224,19296,48,14070,28508,48,77,37970,16792,78,78,16792,37970,77,48,28508,14070,
    48,19296,6224,57647,19282,6224,21364,19282,6220,48,77,28508,16792,14070,37970,48,78,14075,48,
    37960,78,48,28520,78,16788],
  #[45308,126,76943,77,126,102431,77,37960,126,78,102449,37970,45300,76929,125,78,16788,52040,
    57647,16792,52040,155539,16792,52035,78,37970,76929,78,125,102449,45300,126,126,45300,102449,
    125,78,76929,37970,78,52035,16792,155539,52040,16792,57647,52040,16788,78,125,76929,45300,
    37970,102449,78,126,37960,77,102431,126,77,76943,126,45308],
  #[122251,204,207574,125,204,276407,125,102431,203,126,276406,102449,122229,207579,203,126,45308,
    140419,155539,45300,140419,419673,45300,140391,126,102449,207579,126,203,276406,122229,203,
    203,122229,276406,203,126,207579,102449,126,140391,45300,419673,140419,45300,155539,140419,
    45308,126,203,207579,122229,102449,276406,126,203,102431,125,276407,204,125,207574,204,
    122251],
  #[329825,329,560064,203,329,745819,203,276407,329,203,745783,276406,329808,560092,329,204,
    122251,378855,419673,122229,378855,1132349,122229,378838,204,276406,560092,203,329,745783,
    329808,329,329,329808,745783,329,203,560092,276406,204,378838,122229,1132349,378855,122229,
    419673,378855,122251,204,329,560092,329808,276406,745783,203,329,276407,203,745819,329,203,
    560064,329,329825],
  #[889889,532,1511187,329,532,2012310,329,745819,532,329,2012271,745783,889900,1511204,533,329,
    329825,1022189,1132349,329808,1022189,3055279,329808,1022226,329,745783,1511204,329,533,
    2012271,889900,532,532,889900,2012271,533,329,1511204,745783,329,1022226,329808,3055279,
    1022189,329808,1132349,1022189,329825,329,533,1511204,889900,745783,2012271,329,532,745819,
    329,2012310,532,329,1511187,532,889889],
  #[2401076,861,4077505,533,861,5429482,533,2012310,861,532,5429502,2012271,2401104,4077468,862,
    532,889889,2758054,3055279,889900,2758054,8243673,889900,2758129,532,2012271,4077468,532,862,
    5429502,2401104,861,861,2401104,5429502,862,532,4077468,2012271,532,2758129,889900,8243673,
    2758054,889900,3055279,2758054,889889,532,862,4077468,2401104,2012271,5429502,532,861,2012310,
    533,5429482,861,533,4077505,861,2401076],
  #[6478581,1393,11001802,862,1393,14649670,862,5429482,1394,861,14649756,5429502,6478572,
    11001727,1394,861,2401076,7441773,8243673,2401104,7441773,22242878,2401104,7441792,861,
    5429502,11001727,861,1394,14649756,6478572,1394,1394,6478572,14649756,1394,861,11001727,
    5429502,861,7441792,2401104,22242878,7441773,2401104,8243673,7441773,2401076,861,1394,
    11001727,6478572,5429502,14649756,861,1394,5429482,862,14649670,1393,862,11001802,1393,
    6478581],
  #[17480383,2255,29684670,1394,2255,39527500,1394,14649670,2255,1394,39527547,14649756,17480299,
    29684651,2255,1393,6478581,20079258,22242878,6478572,20079258,60015173,6478572,20079152,1393,
    14649756,29684651,1394,2255,39527547,17480299,2255,2255,17480299,39527547,2255,1394,29684651,
    14649756,1393,20079152,6478572,60015173,20079258,6478572,22242878,20079258,6478581,1393,2255,
    29684651,17480299,14649756,39527547,1394,2255,14649670,1394,39527500,2255,1394,29684670,2255,
    17480383],
  #[47165053,3649,80094325,2255,3649,106652270,2255,39527500,3649,2255,106652155,39527547,
    47164950,80094431,3648,2255,17480383,54177303,60015173,17480299,54177303,161931444,17480299,
    54177170,2255,39527547,80094431,2255,3648,106652155,47164950,3649,3649,47164950,106652155,
    3648,2255,80094431,39527547,2255,54177170,17480299,161931444,54177303,17480299,60015173,
    54177303,17480383,2255,3648,80094431,47164950,39527547,106652155,2255,3649,39527500,2255,
    106652270,3649,2255,80094325,3649,47165053],
  #[127259378,5904,216108614,3648,5904,287766433,3648,106652270,5904,3649,287766216,106652155,
    127259381,216108747,5903,3649,47165053,146179702,161931444,47164950,146179702,436919374,
    47164950,146179770,3649,106652155,216108747,3649,5903,287766216,127259381,5904,5904,127259381,
    287766216,5903,3649,216108747,106652155,3649,146179770,47164950,436919374,146179702,47164950,
    161931444,146179702,47165053,3649,5903,216108747,127259381,106652155,287766216,3649,5904,
    106652270,3648,287766433,5904,3648,216108614,5904,127259378]
]

private def table (k : ℕ) (r s : (Fin 3 → Bool)) : ℤ :=
  (tables[k]!)[32 * (r 0).toNat + 16 * (r 1).toNat + 8 * (r 2).toNat +
    4 * (s 0).toNat + 2 * (s 1).toNat + (s 2).toNat]!

set_option maxRecDepth 8192 in
set_option trace.profiler true in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite continuation table.
private theorem table_base : ∀ r s : (Fin 3 → Bool), v 0 r s = table 0 r s := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option trace.profiler true in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite continuation table.
private theorem table_steps : ∀ k : Fin 20, ∀ r s : (Fin 3 → Bool),
    step (table k.val) r s = table (k.val + 1) r s := by
  decide +kernel

private theorem v_table (k : ℕ) (hk : k ≤ 20) : v k = table k := by
  induction k with
  | zero => funext r s; exact table_base r s
  | succ k ih =>
    change step (v k) = table (k + 1)
    rw [ih (by omega)]
    funext r s
    exact table_steps ⟨k, by omega⟩ r s


set_option maxRecDepth 8192 in
set_option trace.profiler true in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite continuation table.
private theorem table_certificate : ∀ r s : (Fin 3 → Bool),
    table 20 r s =
      4 * table 19 r s - 3 * table 18 r s - 2 * table 17 r s + 2 * table 16 r s
        + 2 * table 15 r s - 7 * table 14 r s - 8 * table 13 r s + 15 * table 12 r s
        + 4 * table 11 r s - 8 * table 10 r s - 4 * table 9 r s + 15 * table 8 r s
        + 8 * table 7 r s - 7 * table 6 r s - 2 * table 5 r s + 2 * table 4 r s + 2 * table 3 r s
        - 3 * table 2 r s - 4 * table 1 r s - table 0 r s := by
  decide +kernel

set_option trace.profiler true in
/-- The order-twenty identity holds on the entire continuation vector. -/
theorem finite_certificate : ∀ r s : (Fin 3 → Bool),
    v 20 r s =
      4 * v 19 r s - 3 * v 18 r s - 2 * v 17 r s + 2 * v 16 r s + 2 * v 15 r s - 7 * v 14 r s
        - 8 * v 13 r s + 15 * v 12 r s + 4 * v 11 r s - 8 * v 10 r s - 4 * v 9 r s + 15 * v 8 r s
        + 8 * v 7 r s - 7 * v 6 r s - 2 * v 5 r s + 2 * v 4 r s + 2 * v 3 r s - 3 * v 2 r s
        - 4 * v 1 r s - v 0 r s := by
  simp only [v_table 0 (by decide), v_table 1 (by decide), v_table 2 (by decide),
    v_table 3 (by decide), v_table 4 (by decide), v_table 5 (by decide), v_table 6 (by decide),
    v_table 7 (by decide), v_table 8 (by decide), v_table 9 (by decide), v_table 10 (by decide),
    v_table 11 (by decide), v_table 12 (by decide), v_table 13 (by decide),
    v_table 14 (by decide), v_table 15 (by decide), v_table 16 (by decide),
    v_table 17 (by decide), v_table 18 (by decide), v_table 19 (by decide),
    v_table 20 (by decide)]
  exact table_certificate


private theorem vector_recurrence (k : ℕ) : ∀ r s : (Fin 3 → Bool),
    v (k + 20) r s =
      4 * v (k + 19) r s - 3 * v (k + 18) r s - 2 * v (k + 17) r s + 2 * v (k + 16) r s
        + 2 * v (k + 15) r s - 7 * v (k + 14) r s - 8 * v (k + 13) r s + 15 * v (k + 12) r s
        + 4 * v (k + 11) r s - 8 * v (k + 10) r s - 4 * v (k + 9) r s + 15 * v (k + 8) r s
        + 8 * v (k + 7) r s - 7 * v (k + 6) r s - 2 * v (k + 5) r s + 2 * v (k + 4) r s
        + 2 * v (k + 3) r s - 3 * v (k + 2) r s - 4 * v (k + 1) r s - v k r s := by
  induction k with
  | zero => exact finite_certificate
  | succ k ih =>
    intro r s
    change step (v (k + 20)) r s =
      4 * step (v (k + 19)) r s - 3 * step (v (k + 18)) r s - 2 * step (v (k + 17)) r s
        + 2 * step (v (k + 16)) r s + 2 * step (v (k + 15)) r s - 7 * step (v (k + 14)) r s
        - 8 * step (v (k + 13)) r s + 15 * step (v (k + 12)) r s + 4 * step (v (k + 11)) r s
        - 8 * step (v (k + 10)) r s - 4 * step (v (k + 9)) r s + 15 * step (v (k + 8)) r s
        + 8 * step (v (k + 7)) r s - 7 * step (v (k + 6)) r s - 2 * step (v (k + 5)) r s
        + 2 * step (v (k + 4)) r s + 2 * step (v (k + 3)) r s - 3 * step (v (k + 2)) r s
        - 4 * step (v (k + 1)) r s - step (v k) r s
    unfold step
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases h : Interior r s t
    · simpa only [ite_eq_left h] using ih s t
    · simp only [ite_eq_right h, mul_zero, add_zero, sub_zero]

private theorem total_recurrence (k : ℕ) :
    total (v (k + 20)) =
      4 * total (v (k + 19)) - 3 * total (v (k + 18)) - 2 * total (v (k + 17))
        + 2 * total (v (k + 16)) + 2 * total (v (k + 15)) - 7 * total (v (k + 14))
        - 8 * total (v (k + 13)) + 15 * total (v (k + 12)) + 4 * total (v (k + 11))
        - 8 * total (v (k + 10)) - 4 * total (v (k + 9)) + 15 * total (v (k + 8))
        + 8 * total (v (k + 7)) - 7 * total (v (k + 6)) - 2 * total (v (k + 5))
        + 2 * total (v (k + 4)) + 2 * total (v (k + 3)) - 3 * total (v (k + 2))
        - 4 * total (v (k + 1)) - total (v k) := by
  unfold total
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : r 0 = false ∧ Boundary r s
  · simpa only [ite_eq_left h] using vector_recurrence k r s
  · simp only [ite_eq_right h, mul_zero, add_zero, sub_zero]

private theorem singleton : (a 1 : ℤ) = 3 := by decide +kernel

set_option maxRecDepth 8192 in
set_option trace.profiler true in
set_option maxHeartbeats 8000000 in
-- Kernel reduction checks the finite continuation table.
private theorem initial_recurrence :
    total (v 19) =
      4 * total (v 18) - 3 * total (v 17) - 2 * total (v 16) + 2 * total (v 15)
        + 2 * total (v 14) - 7 * total (v 13) - 8 * total (v 12) + 15 * total (v 11)
        + 4 * total (v 10) - 8 * total (v 9) - 4 * total (v 8) + 15 * total (v 7)
        + 8 * total (v 6) - 7 * total (v 5) - 2 * total (v 4) + 2 * total (v 3) + 2 * total (v 2)
        - 3 * total (v 1) - 4 * total (v 0) - (a 1 : ℤ) := by
  simp only [singleton, v_table 0 (by decide), v_table 1 (by decide), v_table 2 (by decide),
    v_table 3 (by decide), v_table 4 (by decide), v_table 5 (by decide), v_table 6 (by decide),
    v_table 7 (by decide), v_table 8 (by decide), v_table 9 (by decide), v_table 10 (by decide),
    v_table 11 (by decide), v_table 12 (by decide), v_table 13 (by decide),
    v_table 14 (by decide), v_table 15 (by decide), v_table 16 (by decide),
    v_table 17 (by decide), v_table 18 (by decide), v_table 19 (by decide)]
  decide +kernel

/-- Hardin's empirical recurrence for the literal three-column board count. -/
theorem result : ∀ n : ℕ, 21 ≤ n →
    (a n : ℤ) =
      4 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) - 2 * (a (n - 3) : ℤ) + 2 * (a (n - 4) : ℤ)
        + 2 * (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) - 8 * (a (n - 7) : ℤ) + 15 * (a (n - 8) : ℤ)
        + 4 * (a (n - 9) : ℤ) - 8 * (a (n - 10) : ℤ) - 4 * (a (n - 11) : ℤ)
        + 15 * (a (n - 12) : ℤ) + 8 * (a (n - 13) : ℤ) - 7 * (a (n - 14) : ℤ)
        - 2 * (a (n - 15) : ℤ) + 2 * (a (n - 16) : ℤ) + 2 * (a (n - 17) : ℤ)
        - 3 * (a (n - 18) : ℤ) - 4 * (a (n - 19) : ℤ) - (a (n - 20) : ℤ) := by
  intro n hn
  by_cases he : n = 21
  · subst n
    simpa only [← counting_bridge, Nat.reduceAdd, Nat.reduceSub] using initial_recurrence
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 22 := ⟨n - 22, by omega⟩
    simpa only [show k + 22 - 1 = k + 21 by omega,
      show k + 22 - 2 = k + 20 by omega,
      show k + 22 - 3 = k + 19 by omega,
      show k + 22 - 4 = k + 18 by omega,
      show k + 22 - 5 = k + 17 by omega,
      show k + 22 - 6 = k + 16 by omega,
      show k + 22 - 7 = k + 15 by omega,
      show k + 22 - 8 = k + 14 by omega,
      show k + 22 - 9 = k + 13 by omega,
      show k + 22 - 10 = k + 12 by omega,
      show k + 22 - 11 = k + 11 by omega,
      show k + 22 - 12 = k + 10 by omega,
      show k + 22 - 13 = k + 9 by omega,
      show k + 22 - 14 = k + 8 by omega,
      show k + 22 - 15 = k + 7 by omega,
      show k + 22 - 16 = k + 6 by omega,
      show k + 22 - 17 = k + 5 by omega,
      show k + 22 - 18 = k + 4 by omega,
      show k + 22 - 19 = k + 3 by omega,
      show k + 22 - 20 = k + 2 by omega,
      ← counting_bridge, Nat.add_assoc, Nat.reduceAdd] using total_recurrence k


end D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip
