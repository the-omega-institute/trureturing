/- GID: D5/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/Q61ClosedCircleTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.Interval, mathlib/module/Mathlib.Data.Nat.Prime.Basic, mathlib/module/Mathlib.LinearAlgebra.Matrix.Notation, mathlib/module/Mathlib.NumberTheory.Real.Irrational, mathlib/module/Mathlib.Topology.Instances.AddCircle.Real]
   utility: none
   digest: Exact closed-circle transfers via tight three-state min-plus matrix words. -/
import D5.S3.Combinatorics.Graph.Walks.MeyerovitchYoungQ61AssignmentGuards
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Tactic

/-! The closed two-loop register passage in Sections 1–3 of
`q61-two-coordinate-decision.txt`. -/

namespace Q61ClosedCircleTransfer

open Q61AssignmentGuards
open scoped BigOperators

noncomputable section

abbrev Circle := UnitAddCircle
abbrev State := Fin 2 → Circle

def theta : ℝ := Real.sqrt 2 - 1

theorem theta_irrational : Irrational theta := by
  simpa [theta] using irrational_sqrt_two.sub_intCast (1 : ℤ)

theorem theta_bounds : 0 < theta ∧ theta < 1 := by
  have hs : Real.sqrt (2 : ℝ) < 2 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  unfold theta
  exact ⟨by linarith [Real.one_lt_sqrt_two], by linarith⟩

def orbit (n : ℤ) : Circle := ((theta * (n : ℝ) : ℝ) : Circle)

@[simp] theorem orbit_zero : orbit 0 = 0 := by
  simp [orbit, AddCircle.coe_zero]

theorem orbit_add (m n : ℤ) : orbit (m + n) = orbit m + orbit n := by
  simp only [orbit, Int.cast_add, mul_add, AddCircle.coe_add]

theorem orbit_neg (n : ℤ) : orbit (-n) = -orbit n := by
  simp only [orbit, Int.cast_neg, mul_neg, AddCircle.coe_neg]

theorem orbit_eq_zero {n : ℤ} : orbit n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp h
    have he : theta * (n : ℝ) = (m : ℝ) := by
      simpa only [zsmul_eq_mul, mul_one] using hm.symm
    exact (theta_irrational.mul_intCast hn).ne_int m he
  · rintro rfl
    exact orbit_zero

theorem orbit_injective : Function.Injective orbit := by
  intro m n h
  have hz : orbit (m - n) = 0 := by
    rw [sub_eq_add_neg, orbit_add, orbit_neg, h, add_neg_cancel]
  exact sub_eq_zero.mp (orbit_eq_zero.mp hz)

def registers (n m : ℤ) : State := ![orbit n, orbit m]

theorem registers_injective {n m n' m' : ℤ}
    (h : registers n m = registers n' m') : n = n' ∧ m = m' :=
  ⟨orbit_injective (congrFun h 0), orbit_injective (congrFun h 1)⟩

def shift (x : State) (d : Fin 2 → ℤ) : State :=
  fun i => x i + orbit (d i)

private theorem shift_shift (x : State) (d e : Fin 2 → ℤ) :
    shift (shift x d) e = shift x (fun i => d i + e i) := by
  funext i
  exact (add_assoc _ _ _).trans (congrArg (x i + ·) (orbit_add _ _).symm)

structure Operation where
  delta : Fin 2 → ℤ
  testZero : Fin 2 → Bool

def Operation.Allows (op : Operation) (x : State) : Prop :=
  ∀ i, op.testZero i = true → x i = 0

/-- A word of circle operations with every test checked before its update. -/
def CircleRun : List Operation → State → State → Prop
  | [], x, y => y = x
  | op :: ops, x, y => op.Allows x ∧ CircleRun ops (shift x op.delta) y

private theorem run_replicate_append (op : Operation)
    (htest : ∀ i, op.testZero i = false) (k : ℕ) (ops : List Operation) (x y : State) :
    CircleRun (List.replicate k op ++ ops) x y ↔
      CircleRun ops (shift x (fun i => (k : ℤ) * op.delta i)) y := by
  induction k generalizing x with
  | zero =>
      have hz : shift x (fun i => ((0 : ℕ) : ℤ) * op.delta i) = x := by
        funext i
        simp [shift]
      simp only [List.replicate_zero, List.nil_append, hz]
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, CircleRun, ih, shift_shift]
      have hd : (fun i => op.delta i + (k : ℤ) * op.delta i) =
          (fun i => ((k + 1 : ℕ) : ℤ) * op.delta i) := by
        funext i
        push_cast
        ring
      rw [hd]
      simp [Operation.Allows, htest]

structure Transfer where
  b : ℕ
  a : ℕ
  r : ℕ
  s : ℕ

namespace Transfer

def enter (row : Transfer) : Operation := ⟨![-(row.r : ℤ), 0], ![false, true]⟩
def left (row : Transfer) : Operation := ⟨![-(row.b : ℤ), row.a], ![false, false]⟩
def cross (row : Transfer) : Operation := ⟨![row.s, 0], ![true, false]⟩
def right : Operation := ⟨![1, -1], ![false, false]⟩
def leave : Operation := ⟨![0, 0], ![false, true]⟩

def word (row : Transfer) (k j : ℕ) : List Operation :=
  row.enter :: (List.replicate k row.left ++
    (row.cross :: (List.replicate j right ++ [leave])))

def Completes (row : Transfer) (x y : State) : Prop :=
  ∃ k j, CircleRun (row.word k j) x y

private theorem run_word_iff_tests (row : Transfer) (k j : ℕ) (x y : State) :
    let u := shift x ![-((row.b * k + row.r : ℕ) : ℤ), (row.a * k : ℕ)]
    let v := shift u ![(row.s + j : ℕ), -(j : ℤ)]
    CircleRun (row.word k j) x y ↔ x 1 = 0 ∧ u 0 = 0 ∧ v 1 = 0 ∧ y = v := by
  dsimp only
  have hl (i : Fin 2) : row.left.testZero i = false := by
    fin_cases i <;> rfl
  have hr (i : Fin 2) : right.testZero i = false := by
    fin_cases i <;> rfl
  have hd₁ : (fun i => row.enter.delta i + (k : ℤ) * row.left.delta i) =
      ![-((row.b * k + row.r : ℕ) : ℤ), (row.a * k : ℕ)] := by
    funext i
    fin_cases i <;> simp [enter, left] <;> ring
  have hd₂ : (fun i => row.cross.delta i + (j : ℤ) * right.delta i) =
      ![((row.s + j : ℕ) : ℤ), -(j : ℤ)] := by
    funext i
    fin_cases i <;> simp [cross, right]
  have he (z : State) : shift z leave.delta = z := by
    funext i
    fin_cases i <;> simp [shift, leave]
  rw [word, CircleRun, run_replicate_append _ hl, shift_shift, hd₁, CircleRun,
    run_replicate_append _ hr, shift_shift, hd₂, CircleRun, CircleRun, he]
  simp [Operation.Allows, enter, cross, leave, Fin.forall_fin_two]

/-- The exact loop counts and endpoints, for arbitrary circle inputs. -/
theorem run_word_iff (row : Transfer) (k j : ℕ) (x y : State) :
    CircleRun (row.word k j) x y ↔
      j = row.a * k ∧
      x = registers (row.b * k + row.r : ℕ) 0 ∧
      y = registers (row.a * k + row.s : ℕ) 0 := by
  simp only [run_word_iff_tests]
  let u := shift x ![-((row.b * k + row.r : ℕ) : ℤ), (row.a * k : ℕ)]
  let v := shift u ![(row.s + j : ℕ), -(j : ℤ)]
  change (x 1 = 0 ∧ u 0 = 0 ∧ v 1 = 0 ∧ y = v) ↔ _
  have hu₀ : u 0 = x 0 - orbit (row.b * k + row.r : ℕ) := by
    change x 0 + orbit (-((row.b * k + row.r : ℕ) : ℤ)) =
      x 0 - orbit (row.b * k + row.r : ℕ)
    rw [orbit_neg]
    rfl
  have hu₁ : u 1 = x 1 + orbit (row.a * k : ℕ) := rfl
  have hv₀ : v 0 = u 0 + orbit (row.s + j : ℕ) := rfl
  have hv₁ : v 1 = u 1 - orbit (j : ℤ) := by
    simp [v, shift, orbit_neg, sub_eq_add_neg]
  constructor
  · rintro ⟨hsecond, hfirst, hlast, rfl⟩
    have hx₀ : x 0 = orbit (row.b * k + row.r : ℕ) := by
      rwa [hu₀, sub_eq_zero] at hfirst
    have hj : j = row.a * k := by
      rw [hv₁, hu₁, hsecond, zero_add, sub_eq_zero] at hlast
      exact_mod_cast (orbit_injective hlast).symm
    refine ⟨hj, ?_, ?_⟩
    · funext i
      fin_cases i <;> simp [registers, hx₀, hsecond]
    · funext i
      fin_cases i
      · change v 0 = orbit (row.a * k + row.s : ℕ)
        rw [hv₀, hfirst, zero_add, hj, Nat.add_comm row.s]
      · simpa [registers] using hlast
  · rintro ⟨hj, hx, hy⟩
    have hsecond : x 1 = 0 := by simp [hx, registers]
    have hfirst : u 0 = 0 := by simp [hu₀, hx, registers]
    have hlast : v 1 = 0 := by simp [hv₁, hu₁, hsecond, hj]
    refine ⟨hsecond, hfirst, hlast, ?_⟩
    rw [hy]
    funext i
    fin_cases i
    · change orbit (row.a * k + row.s : ℕ) = v 0
      rw [hv₀, hfirst, zero_add, hj, Nat.add_comm row.s]
    · simpa [registers] using hlast.symm

theorem completes_iff (row : Transfer) (x y : State) :
    row.Completes x y ↔
      ∃ k : ℕ, x = registers (row.b * k + row.r : ℕ) 0 ∧
        y = registers (row.a * k + row.s : ℕ) 0 := by
  constructor
  · rintro ⟨k, j, h⟩
    exact ⟨k, ((row.run_word_iff k j x y).mp h).2⟩
  · rintro ⟨k, hx, hy⟩
    exact ⟨k, row.a * k, (row.run_word_iff _ _ _ _).mpr ⟨rfl, hx, hy⟩⟩

/-- Residues use the positive representative `r` in `1,…,b`.
In particular `r = b` selects the positive multiples of `b`. -/
theorem completes_iff_positive_residue (row : Transfer)
    (hr : 0 < row.r) (hrb : row.r ≤ row.b) (x y : State) :
    row.Completes x y ↔
      ∃ n : ℕ, 0 < n ∧ (n - 1) % row.b = row.r - 1 ∧ x = registers n 0 ∧
        y = registers (row.a * ((n - 1) / row.b) + row.s : ℕ) 0 := by
  rw [completes_iff]
  have hb : 0 < row.b := hr.trans_le hrb
  have hlt : row.r - 1 < row.b := by omega
  constructor
  · rintro ⟨k, hx, hy⟩
    have hsub : row.b * k + row.r - 1 = row.b * k + (row.r - 1) := by omega
    refine ⟨row.b * k + row.r, by omega, ?_, hx, ?_⟩
    · rw [hsub, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    · rwa [hsub, Nat.mul_add_div hb, Nat.div_eq_of_lt hlt, add_zero]
  · rintro ⟨n, hn, hmod, hx, hy⟩
    have hd := Nat.div_add_mod (n - 1) row.b
    rw [hmod] at hd
    have hnk : row.b * ((n - 1) / row.b) + row.r = n := by omega
    exact ⟨(n - 1) / row.b, by rwa [hnk], hy⟩

theorem completes_on_numeral (row : Transfer) (n : ℕ) (y : State) :
    row.Completes (registers n 0) y ↔
      ∃ k : ℕ, n = row.b * k + row.r ∧ y = registers (row.a * k + row.s : ℕ) 0 := by
  rw [completes_iff]
  constructor
  · rintro ⟨k, h, hy⟩
    exact ⟨k, by exact_mod_cast (registers_injective h).1, hy⟩
  · rintro ⟨k, rfl, hy⟩
    exact ⟨k, rfl, hy⟩

/-- A row preserves and reflects strict order on its enabled numerals. -/
theorem completes_lt_iff (row : Transfer) (hb : 0 < row.b) (ha : 0 < row.a)
    {n₁ n₂ m₁ m₂ : ℕ}
    (h₁ : row.Completes (registers n₁ 0) (registers m₁ 0))
    (h₂ : row.Completes (registers n₂ 0) (registers m₂ 0)) :
    n₁ < n₂ ↔ m₁ < m₂ := by
  obtain ⟨k₁, hn₁, hm₁⟩ := (row.completes_on_numeral _ _).mp h₁
  obtain ⟨k₂, hn₂, hm₂⟩ := (row.completes_on_numeral _ _).mp h₂
  have hm₁' : m₁ = row.a * k₁ + row.s := by exact_mod_cast (registers_injective hm₁).1
  have hm₂' : m₂ = row.a * k₂ + row.s := by exact_mod_cast (registers_injective hm₂).1
  rw [hn₁, hn₂, hm₁', hm₂', Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right,
    Nat.mul_lt_mul_left hb, Nat.mul_lt_mul_left ha]

end Transfer

def increment (p : ℕ) : Transfer := ⟨1, 5 * p, 1, 5 * p⟩
def decrement (p : ℕ) : Transfer := ⟨p, 5, p, 5⟩
def zeroBranch (p r : ℕ) : Transfer := ⟨p, 5 * p, r, 5 * r⟩

theorem increment_exact (p n : ℕ) (y : State) :
    (increment p).Completes (registers n 0) y ↔
      0 < n ∧ y = registers (5 * p * n : ℕ) 0 := by
  rw [Transfer.completes_on_numeral]
  change (∃ k : ℕ, n = 1 * k + 1 ∧ y = registers (5 * p * k + 5 * p : ℕ) 0) ↔ _
  simp only [one_mul]
  constructor
  · rintro ⟨k, hk, hy⟩
    exact ⟨by omega, by simpa only [hk, Nat.mul_add, Nat.mul_one] using hy⟩
  · rintro ⟨hn, hy⟩
    have hk : n - 1 + 1 = n := by omega
    have hm : 5 * p * (n - 1) + 5 * p = 5 * p * n := calc
      _ = 5 * p * (n - 1 + 1) := by ring
      _ = _ := by rw [hk]
    exact ⟨n - 1, hk.symm, by simpa only [hm] using hy⟩

theorem decrement_exact {p : ℕ} (hp : 0 < p) (n : ℕ) (y : State) :
    (decrement p).Completes (registers n 0) y ↔
      0 < n ∧ p ∣ n ∧ y = registers (5 * (n / p) : ℕ) 0 := by
  rw [Transfer.completes_on_numeral]
  change (∃ k : ℕ, n = p * k + p ∧ y = registers (5 * k + 5 : ℕ) 0) ↔ _
  constructor
  · rintro ⟨k, hk, hy⟩
    have hn : n = p * (k + 1) := hk.trans (by ring)
    have hq : n / p = k + 1 := by rw [hn, Nat.mul_div_cancel_left _ hp]
    exact ⟨by omega, ⟨k + 1, hn⟩, by simpa only [hq, Nat.mul_add, Nat.mul_one] using hy⟩
  · rintro ⟨hn, ⟨q, hq⟩, hy⟩
    cases q with
    | zero => simp [hq] at hn
    | succ k =>
      refine ⟨k, hq.trans (by ring), ?_⟩
      have hqdiv : n / p = k + 1 := by
        rw [hq, Nat.mul_div_cancel_left _ hp]
      simpa only [hqdiv, Nat.mul_add, Nat.mul_one] using hy

theorem zero_branch_exact {p r : ℕ} (_hr : 0 < r) (hrp : r < p) (n : ℕ) (y : State) :
    (zeroBranch p r).Completes (registers n 0) y ↔
      n % p = r ∧ y = registers (5 * n : ℕ) 0 := by
  rw [Transfer.completes_on_numeral]
  change (∃ k : ℕ, n = p * k + r ∧ y = registers (5 * p * k + 5 * r : ℕ) 0) ↔ _
  constructor
  · rintro ⟨k, hk, hy⟩
    have hm : 5 * n = 5 * p * k + 5 * r := by rw [hk]; ring
    exact ⟨by rw [hk, Nat.mul_add_mod, Nat.mod_eq_of_lt hrp], by simpa only [hm] using hy⟩
  · rintro ⟨hmod, hy⟩
    have hk : n = p * (n / p) + r := by
      simpa only [hmod] using (Nat.div_add_mod n p).symm
    refine ⟨n / p, hk, ?_⟩
    have hm : 5 * n = 5 * p * (n / p) + 5 * r :=
      congrArg (5 * ·) hk |>.trans (by ring)
    rwa [← hm]

theorem unique_zero_branch {p n : ℕ} (hp : 0 < p) (h : ¬ p ∣ n) :
    ∃! r : ℕ, 0 < r ∧ r < p ∧
      (zeroBranch p r).Completes (registers n 0) (registers (5 * n : ℕ) 0) := by
  have hr : 0 < n % p := Nat.pos_of_ne_zero (mt Nat.dvd_iff_mod_eq_zero.mpr h)
  have hlt := Nat.mod_lt n hp
  refine ⟨n % p, ⟨hr, hlt, (zero_branch_exact hr hlt _ _).mpr ⟨rfl, rfl⟩⟩, ?_⟩
  rintro r ⟨hr', hlt', hrun⟩
  exact ((zero_branch_exact hr' hlt' _ _).mp hrun).1.symm

abbrev Grows (row : Transfer) : Prop :=
  ∀ ⦃x y : State⦄, row.Completes x y →
    ∃ n m : ℕ, 0 < n ∧ n < m ∧ x = registers n 0 ∧ y = registers m 0

private theorem grows_of_bounds (row : Transfer) (hr : 0 < row.r)
    (hba : row.b ≤ row.a) (hrs : row.r < row.s) : Grows row := by
  intro x y h
  obtain ⟨k, hx, hy⟩ := (row.completes_iff x y).mp h
  have hmul := Nat.mul_le_mul_right k hba
  exact ⟨row.b * k + row.r, row.a * k + row.s, by omega, by omega, hx, hy⟩

theorem increment_grows {p : ℕ} (hp : p = 2 ∨ p = 3) : Grows (increment p) := by
  apply grows_of_bounds (increment p)
  · simp [increment]
  · rcases hp with rfl | rfl <;> decide
  · rcases hp with rfl | rfl <;> decide

theorem decrement_grows {p : ℕ} (hp : p = 2 ∨ p = 3) : Grows (decrement p) :=
  grows_of_bounds _ (by rcases hp with rfl | rfl <;> decide)
    (by rcases hp with rfl | rfl <;> decide) (by rcases hp with rfl | rfl <;> decide)

theorem zero_branch_grows {p r : ℕ} (hr : 0 < r) : Grows (zeroBranch p r) :=
  grows_of_bounds _ hr (by change p ≤ 5 * p; omega) (by change r < 5 * r; omega)

theorem Grows.no_return {row : Transfer} (h : Grows row) (x : State) :
    ¬ row.Completes x x := by
  intro hx
  obtain ⟨n, m, _, hlt, hn, hm⟩ := h hx
  have he : n = m := by exact_mod_cast (registers_injective (hn.symm.trans hm)).1
  omega

/-- The first prime encodes the selected counter. Swapping both primes and
counter values gives the same numeral. -/
def counterCode (p q i j t : ℕ) : ℕ := p ^ i * q ^ j * 5 ^ t

theorem counterCode_swap (p q i j t : ℕ) :
    counterCode p q i j t = counterCode q p j i t := by
  simp only [counterCode, Nat.mul_comm (p ^ i) (q ^ j)]

theorem counterCode_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (i j t : ℕ) :
    0 < counterCode p q i j t := by
  unfold counterCode
  positivity

theorem counterCode_test {p q : ℕ} (hp : p.Prime) (hq : ¬ p ∣ q) (h5 : ¬ p ∣ 5)
    (i j t : ℕ) : p ∣ counterCode p q i j t ↔ 0 < i := by
  have hq' : ¬ p ∣ q ^ j := fun h => hq (hp.dvd_of_dvd_pow h)
  have h5' : ¬ p ∣ 5 ^ t := fun h => h5 (hp.dvd_of_dvd_pow h)
  rw [counterCode, hp.dvd_mul, hp.dvd_mul]
  simp only [hq', h5', or_false]
  cases i with
  | zero => simp [hp.not_dvd_one]
  | succ i => simp [pow_succ, hp.dvd_mul]

theorem counterCode_test_two (i j t : ℕ) :
    2 ∣ counterCode 2 3 i j t ↔ 0 < i :=
  counterCode_test Nat.prime_two (by decide) (by decide) i j t

theorem counterCode_test_three (i j t : ℕ) :
    3 ∣ counterCode 2 3 i j t ↔ 0 < j := by
  rw [counterCode_swap]
  exact counterCode_test Nat.prime_three (by decide) (by decide) j i t

theorem counterCode_increment {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (i j t : ℕ) (y : State) :
    (increment p).Completes (registers (counterCode p q i j t) 0) y ↔
      y = registers (counterCode p q (i + 1) j (t + 1)) 0 := by
  rw [increment_exact, and_iff_right (counterCode_pos hp hq i j t)]
  have hm : 5 * p * counterCode p q i j t = counterCode p q (i + 1) j (t + 1) := by
    simp only [counterCode, pow_succ]
    ring
  rw [hm]

theorem counterCode_decrement {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (i j t : ℕ) (y : State) :
    (decrement p).Completes (registers (counterCode p q (i + 1) j t) 0) y ↔
      y = registers (counterCode p q i j (t + 1)) 0 := by
  have hn : counterCode p q (i + 1) j t = p * counterCode p q i j t := by
    simp only [counterCode, pow_succ]
    ring
  rw [decrement_exact hp, and_iff_right (counterCode_pos hp hq (i + 1) j t),
    and_iff_right (show p ∣ counterCode p q (i + 1) j t from ⟨_, hn⟩), hn,
    Nat.mul_div_cancel_left _ hp]
  have hm : 5 * counterCode p q i j t = counterCode p q i j (t + 1) := by
    simp only [counterCode, pow_succ]
    ring
  rw [hm]

theorem counterCode_zero_branch {p q r : ℕ} (hr : 0 < r) (hrp : r < p)
    (i j t : ℕ) (y : State) :
    (zeroBranch p r).Completes (registers (counterCode p q i j t) 0) y ↔
      counterCode p q i j t % p = r ∧ y = registers (counterCode p q i j (t + 1)) 0 := by
  rw [zero_branch_exact hr hrp]
  have hm : 5 * counterCode p q i j t = counterCode p q i j (t + 1) := by
    simp only [counterCode, pow_succ]
    ring
  rw [hm]

/-! Closed representatives and their finite family of wrap and test choices. -/

abbrev Lift := Fin 2 → ℝ

def OnSquare (t : Lift) : Prop := ∀ i, t i ∈ Set.Icc (0 : ℝ) 1
def reduce (t : Lift) : State := fun i => (t i : Circle)

private theorem coe_eq_zero_iff_int (x : ℝ) :
    (x : Circle) = 0 ↔ ∃ k : ℤ, (k : ℝ) = x := by
  simpa only [zsmul_eq_mul, mul_one] using
    (AddCircle.coe_eq_zero_iff (1 : ℝ) (x := x))

theorem closed_zero_iff {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (x : Circle) = 0 ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := (coe_eq_zero_iff_int x).mp h
    have hlo : (0 : ℤ) ≤ k := by exact_mod_cast (show 0 ≤ (k : ℝ) by rw [hk]; exact hx.1)
    have hhi : k ≤ (1 : ℤ) := by exact_mod_cast (show (k : ℝ) ≤ 1 by rw [hk]; exact hx.2)
    have he : k = 0 ∨ k = 1 := by omega
    rcases he with h₀ | h₁
    · exact Or.inl (by simpa [h₀] using hk.symm)
    · exact Or.inr (by simpa [h₁] using hk.symm)
  · rintro (rfl | rfl)
    · exact AddCircle.coe_zero _
    · exact AddCircle.coe_period _

theorem exists_closed_lift (x : State) : ∃ t : Lift, OnSquare t ∧ reduce t = x := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have h (i : Fin 2) : ∃ v ∈ Set.Ico (0 : ℝ) 1, (v : Circle) = x i :=
    AddCircle.eq_coe_Ico (x i)
  choose t ht he using h
  exact ⟨t, fun i => ⟨(ht i).1, (ht i).2.le⟩, funext he⟩

def wraps (d : ℤ) : Finset ℤ :=
  Finset.Icc (-(d.natAbs : ℤ) - 1) ((d.natAbs : ℤ) + 1)

private theorem wrap_mem {t u : ℝ} {d k : ℤ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) (he : u = t + theta * (d : ℝ) - (k : ℝ)) :
    k ∈ wraps d := by
  have habs : |(d : ℝ)| = (d.natAbs : ℝ) := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hb : |theta * (d : ℝ)| ≤ (d.natAbs : ℝ) := calc
    _ = theta * |(d : ℝ)| := by rw [abs_mul, abs_of_pos theta_bounds.1]
    _ ≤ 1 * |(d : ℝ)| := mul_le_mul_of_nonneg_right theta_bounds.2.le (abs_nonneg _)
    _ = _ := by rw [one_mul, habs]
  have hlo : -(d.natAbs : ℝ) - 1 ≤ (k : ℝ) :=
    by linarith only [(abs_le.mp hb).1, ht.1, hu.2, he]
  have hhi : (k : ℝ) ≤ (d.natAbs : ℝ) + 1 :=
    by linarith only [(abs_le.mp hb).2, ht.2, hu.1, he]
  have hlo' : -(d.natAbs : ℤ) - 1 ≤ k := by exact_mod_cast hlo
  have hhi' : k ≤ (d.natAbs : ℤ) + 1 := by
    norm_num [Nat.cast_add, Int.cast_add, Int.cast_natCast] at hhi ⊢
    exact_mod_cast hhi
  exact Finset.mem_Icc.mpr ⟨hlo', hhi'⟩

/-- Each tested coordinate selects its own closed representative of zero. -/
abbrev Branch (op : Operation) :=
  (∀ i : Fin 2, ↥(wraps (op.delta i))) × (Fin 2 → Bool)

def cut (b : Bool) : ℝ := if b = true then 1 else 0

def translation {op : Operation} (b : Branch op) (i : Fin 2) : ℝ :=
  theta * (op.delta i : ℝ) - ((b.1 i).val : ℝ)

def lower {op : Operation} (b : Branch op) (i : Fin 2) : ℝ :=
  max (max 0 (-translation b i)) (if op.testZero i = true then cut (b.2 i) else 0)

def upper {op : Operation} (b : Branch op) (i : Fin 2) : ℝ :=
  min (min 1 (1 - translation b i)) (if op.testZero i = true then cut (b.2 i) else 1)

def InGuard {op : Operation} (b : Branch op) (t : Lift) : Prop :=
  ∀ i, t i ∈ Set.Icc (lower b i) (upper b i)

def liftAdvance {op : Operation} (b : Branch op) (t : Lift) : Lift :=
  fun i => t i + translation b i

private theorem guard_coord_iff {t delta : ℝ} {tested choice : Bool} :
    t ∈ Set.Icc (max (max 0 (-delta)) (if tested = true then cut choice else 0))
        (min (min 1 (1 - delta)) (if tested = true then cut choice else 1)) ↔
      t ∈ Set.Icc (0 : ℝ) 1 ∧ t + delta ∈ Set.Icc (0 : ℝ) 1 ∧
        (tested = true → t = cut choice) := by
  simp only [Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨⟨h0, hl⟩, hc₀⟩, ⟨⟨h1, hu⟩, hc₁⟩⟩
    refine ⟨⟨h0, h1⟩, ⟨by linarith only [hl], by linarith only [hu]⟩, ?_⟩
    intro h
    rw [if_pos h] at hc₀ hc₁
    exact le_antisymm hc₁ hc₀
  · rintro ⟨⟨h0, h1⟩, ⟨hl, hu⟩, hc⟩
    refine ⟨⟨⟨h0, by linarith only [hl]⟩, ?_⟩, ⟨⟨h1, by linarith only [hu]⟩, ?_⟩⟩
    · by_cases h : tested = true
      · rw [if_pos h, hc h]
      · rwa [if_neg h]
    · by_cases h : tested = true
      · rw [if_pos h, hc h]
      · rwa [if_neg h]

theorem inGuard_iff {op : Operation} (b : Branch op) (t : Lift) :
    InGuard b t ↔ OnSquare t ∧ OnSquare (liftAdvance b t) ∧
      (∀ i, op.testZero i = true → t i = cut (b.2 i)) := by
  constructor
  · intro h
    exact ⟨fun i => (guard_coord_iff.mp (h i)).1,
      fun i => (guard_coord_iff.mp (h i)).2.1,
      fun i => (guard_coord_iff.mp (h i)).2.2⟩
  · rintro ⟨ht, hu, hc⟩ i
    exact guard_coord_iff.mpr ⟨ht i, hu i, hc i⟩

theorem reduce_advance {op : Operation} (b : Branch op) (t : Lift) :
    reduce (liftAdvance b t) = shift (reduce t) op.delta := by
  funext i
  have hk : (((b.1 i).val : ℝ) : Circle) = 0 :=
    (coe_eq_zero_iff_int _).mpr ⟨_, rfl⟩
  have he : t i + translation b i = (t i + theta * (op.delta i : ℝ)) - ((b.1 i).val : ℝ) :=
    by unfold translation; ring
  change ((t i + translation b i : ℝ) : Circle) = (t i : Circle) + orbit (op.delta i)
  rw [he, AddCircle.coe_sub, hk, sub_zero, AddCircle.coe_add]
  simp [orbit]

theorem guard_allows {op : Operation} {b : Branch op} {t : Lift}
    (h : InGuard b t) : op.Allows (reduce t) := by
  obtain ⟨ht, _, hc⟩ := (inGuard_iff b t).mp h
  intro i hi
  apply (closed_zero_iff (ht i)).mpr
  rw [hc i hi]
  cases b.2 i <;> simp [cut]

/-- Every closed source and target representative of a permitted circle step
is realized by a branch, including both representatives at a cut. -/
theorem exists_branch {op : Operation} {t u : Lift} (ht : OnSquare t) (hu : OnSquare u)
    (ha : op.Allows (reduce t)) (he : reduce u = shift (reduce t) op.delta) :
    ∃ b : Branch op, InGuard b t ∧ liftAdvance b t = u := by
  have hwrap (i : Fin 2) : ∃ k ∈ wraps (op.delta i),
      u i = t i + theta * (op.delta i : ℝ) - (k : ℝ) := by
    have hc := congrFun he i
    change (u i : Circle) = (t i : Circle) + orbit (op.delta i) at hc
    have hz : ((t i + theta * (op.delta i : ℝ) - u i : ℝ) : Circle) = 0 := by
      rw [AddCircle.coe_sub, AddCircle.coe_add]
      exact sub_eq_zero.mpr hc.symm
    obtain ⟨k, hk⟩ := (coe_eq_zero_iff_int _).mp hz
    have hk' : u i = t i + theta * (op.delta i : ℝ) - (k : ℝ) := by linarith only [hk]
    exact ⟨k, wrap_mem (ht i) (hu i) hk', hk'⟩
  choose k hk hku using hwrap
  classical
  let b : Branch op := (fun i => ⟨k i, hk i⟩, fun i => if t i = 1 then true else false)
  have hb : liftAdvance b t = u := by
    funext i
    change t i + (theta * (op.delta i : ℝ) - (k i : ℝ)) = u i
    linarith only [hku i]
  refine ⟨b, (inGuard_iff b t).mpr ⟨ht, hb.symm ▸ hu, ?_⟩, hb⟩
  intro i hi
  rcases (closed_zero_iff (ht i)).mp (ha i hi) with hz | ho
  · simp [b, cut, hz]
  · simp [b, cut, ho]

/-! Each passage stays in the same translated square, with offset `2` in
the construction. The offset below is a parameter. -/

abbrev Score := Fin 3 → ℝ

def scoreLift (c : ℝ) (x : Score) : Lift := fun i => x i.succ - x 0 - c
def scoreState (c : ℝ) (x : Score) : State := reduce (scoreLift c x)

private def excess {op : Operation} (c : ℝ) (b : Branch op) : Fin 3 → Fin 3 → ℝ :=
  ![![0, c + upper b 0, c + upper b 1],
    ![-(c + lower b 0), 0, 1],
    ![-(c + lower b 1), 1, 0]]

private def offsets {op : Operation} (b : Branch op) : Fin 3 → ℝ :=
  ![0, translation b 0, translation b 1]

def branchMatrix {op : Operation} (c : ℝ) (b : Branch op) : Matrix (Fin 3) (Fin 3) ℝ :=
  guardMatrix (Equiv.refl _) (offsets b) (excess c b)

private theorem excess_iff {op : Operation} (c : ℝ) (b : Branch op) (x : Score) :
    (∀ i j : Fin 3, i ≠ j → x j - x i ≤ excess c b i j) ↔ InGuard b (scoreLift c x) := by
  constructor
  · intro h i
    have hu₀ := h 0 1 (by decide)
    have hl₀ := h 1 0 (by decide)
    have hu₁ := h 0 2 (by decide)
    have hl₁ := h 2 0 (by decide)
    change x 1 - x 0 ≤ c + upper b 0 at hu₀
    change x 0 - x 1 ≤ -(c + lower b 0) at hl₀
    change x 2 - x 0 ≤ c + upper b 1 at hu₁
    change x 0 - x 2 ≤ -(c + lower b 1) at hl₁
    fin_cases i
    · change lower b 0 ≤ x 1 - x 0 - c ∧ x 1 - x 0 - c ≤ upper b 0
      exact ⟨by linarith only [hl₀], by linarith only [hu₀]⟩
    · change lower b 1 ≤ x 2 - x 0 - c ∧ x 2 - x 0 - c ≤ upper b 1
      exact ⟨by linarith only [hl₁], by linarith only [hu₁]⟩
  · intro h i j hij
    have h₀ : lower b 0 ≤ x 1 - x 0 - c ∧ x 1 - x 0 - c ≤ upper b 0 := h 0
    have h₁ : lower b 1 ≤ x 2 - x 0 - c ∧ x 2 - x 0 - c ≤ upper b 1 := h 1
    have hs := ((inGuard_iff b (scoreLift c x)).mp h).1
    have hs₀ : 0 ≤ x 1 - x 0 - c ∧ x 1 - x 0 - c ≤ 1 := hs 0
    have hs₁ : 0 ≤ x 2 - x 0 - c ∧ x 2 - x 0 - c ≤ 1 := hs 1
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change x 1 - x 0 ≤ c + upper b 0
      linarith only [h₀.2]
    · change x 2 - x 0 ≤ c + upper b 1
      linarith only [h₁.2]
    · change x 0 - x 1 ≤ -(c + lower b 0)
      linarith only [h₀.1]
    · exact (hij rfl).elim
    · change x 2 - x 1 ≤ 1
      linarith only [hs₁.2, hs₀.1]
    · change x 0 - x 2 ≤ -(c + lower b 1)
      linarith only [h₁.1]
    · change x 1 - x 2 ≤ 1
      linarith only [hs₀.2, hs₁.1]
    · exact (hij rfl).elim

/-- The existing guard compiler realizes the rectangle as the zero total
score increment locus, with the stated update on the entire closed guard. -/
theorem branchMatrix_spec {op : Operation} (c : ℝ) (b : Branch op) :
    assignmentCost (branchMatrix c b) (Equiv.refl _) = 0 ∧
    ∀ x : Score, scoreIncrement (branchMatrix c b) x ≤ 0 ∧
      (scoreIncrement (branchMatrix c b) x = 0 ↔ InGuard b (scoreLift c x)) ∧
      (InGuard b (scoreLift c x) →
        scoreLift c (endpointUpdate (branchMatrix c b) x) = liftAdvance b (scoreLift c x)) := by
  obtain ⟨hcost, hspec⟩ := guardMatrix_spec (Equiv.refl (Fin 3)) (offsets b) (excess c b)
  refine ⟨hcost, fun x => ?_⟩
  obtain ⟨hle, heq, hupdate⟩ := hspec x
  refine ⟨hle, heq.trans (excess_iff c b x), fun hg => ?_⟩
  funext i
  have h := hupdate ((excess_iff c b x).mpr hg) 0 i.succ
  have ho : offsets b i.succ - offsets b 0 = translation b i := by
    fin_cases i <;> simp [offsets]
  change endpointUpdate (branchMatrix c b) x i.succ - endpointUpdate (branchMatrix c b) x 0 =
    (x i.succ - x 0) + (offsets b i.succ - offsets b 0) at h
  rw [ho] at h
  change endpointUpdate (branchMatrix c b) x i.succ -
    endpointUpdate (branchMatrix c b) x 0 - c = (x i.succ - x 0 - c) + translation b i
  linarith only [h]

/-- Choose one matrix per operation and advance the actual endpoint scores,
requiring zero score increment at every prefix. -/
def ScoreRun (c : ℝ) : List Operation → Score → State → Prop
  | [], x, y => y = scoreState c x
  | op :: ops, x, y => ∃ b : Branch op, scoreIncrement (branchMatrix c b) x = 0 ∧
      ScoreRun c ops (endpointUpdate (branchMatrix c b) x) y

private theorem tight_step {op : Operation} {c : ℝ} {b : Branch op} {x : Score}
    (hg : InGuard b (scoreLift c x)) :
    let x' := endpointUpdate (branchMatrix c b) x
    OnSquare (scoreLift c x') ∧ scoreState c x' = shift (scoreState c x) op.delta := by
  have hu := ((branchMatrix_spec c b).2 x).2.2 hg
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [hu]
    exact ((inGuard_iff b (scoreLift c x)).mp hg).2.1
  · simp only [scoreState, hu, reduce_advance]

theorem scoreRun_iff_circleRun (c : ℝ) (ops : List Operation) (x : Score) (y : State)
    (hx : OnSquare (scoreLift c x)) :
    ScoreRun c ops x y ↔ CircleRun ops (scoreState c x) y := by
  induction ops generalizing x with
  | nil => rfl
  | cons op ops ih =>
    constructor
    · rintro ⟨b, ht, hrun⟩
      have hg := (((branchMatrix_spec c b).2 x).2.1).mp ht
      obtain ⟨hx', hstate⟩ := tight_step hg
      refine ⟨guard_allows hg, ?_⟩
      rw [← hstate]
      exact (ih _ hx').mp hrun
    · rintro ⟨ha, hrun⟩
      obtain ⟨u, hu, he⟩ := exists_closed_lift (shift (scoreState c x) op.delta)
      obtain ⟨b, hg, _⟩ := exists_branch hx hu ha he
      obtain ⟨hx', hstate⟩ := tight_step hg
      refine ⟨b, (((branchMatrix_spec c b).2 x).2.1).mpr hg, (ih _ hx').mpr ?_⟩
      rwa [hstate]

abbrev Payoff := Matrix (Fin 3) (Fin 3) ℝ

/-- A compiled word chooses one finite branch matrix for each operation. -/
def Compiles (c : ℝ) : List Operation → List Payoff → Prop
  | [], ms => ms = []
  | op :: ops, ms => ∃ (b : Branch op) (tail : List Payoff),
      ms = branchMatrix c b :: tail ∧ Compiles c ops tail

def scoreGain (x : Score) (ms : List Payoff) : ℝ :=
  (∑ i, endpointScores id x ms i) - ∑ i, x i

private theorem scoreGain_cons (x : Score) (m : Payoff) (ms : List Payoff) :
    scoreGain x (m :: ms) =
      scoreGain (endpointUpdate m x) ms + scoreIncrement m x := by
  unfold scoreGain scoreIncrement
  change (∑ i, endpointScores id (endpointUpdate m x) ms i) - (∑ i, x i) = _
  ring

private theorem compiled_gain_nonpos {c : ℝ} {ops : List Operation} {ms : List Payoff}
    (h : Compiles c ops ms) (x : Score) : scoreGain x ms ≤ 0 := by
  induction ops generalizing ms x with
  | nil =>
    change ms = [] at h
    subst ms
    simp [scoreGain, endpointScores]
  | cons op ops ih =>
    obtain ⟨b, tail, rfl, ht⟩ := h
    rw [scoreGain_cons]
    exact add_nonpos (ih (ms := tail) (x := endpointUpdate (branchMatrix c b) x) ht)
      ((branchMatrix_spec c b).2 x).1

/-- A run is tight exactly when a compiled matrix word has zero total gain
and its actual endpoint scores project to the stated output. -/
theorem scoreRun_iff_compiled (c : ℝ) (ops : List Operation) (x : Score) (y : State) :
    ScoreRun c ops x y ↔
      ∃ ms, Compiles c ops ms ∧ scoreGain x ms = 0 ∧ y = scoreState c (endpointScores id x ms) := by
  induction ops generalizing x with
  | nil =>
    simp [ScoreRun, Compiles, scoreGain, endpointScores]
  | cons op ops ih =>
    constructor
    · rintro ⟨b, hb, hrun⟩
      obtain ⟨ms, hc, hg, hy⟩ := (ih _).mp hrun
      refine ⟨branchMatrix c b :: ms, ⟨b, ms, rfl, hc⟩, ?_, hy⟩
      rw [scoreGain_cons, hg, hb, add_zero]
    · rintro ⟨ms, ⟨b, tail, rfl, hc⟩, hg, hy⟩
      have hb := ((branchMatrix_spec c b).2 x).1
      have ht := compiled_gain_nonpos hc (endpointUpdate (branchMatrix c b) x)
      rw [scoreGain_cons] at hg
      refine ⟨b, by linarith only [hb, ht, hg], (ih _).mpr ⟨tail, hc, ?_, hy⟩⟩
      linarith only [hb, ht, hg]

/-- The numeral and affine output characterize completed tight min-plus
passages from every real score whose differences lie in the source square. -/
theorem score_passage_iff (row : Transfer) (hr : 0 < row.r) (hrb : row.r ≤ row.b)
    (c : ℝ) (x : Score) (y : State) (hx : OnSquare (scoreLift c x)) :
    (∃ k j, ScoreRun c (row.word k j) x y) ↔
      ∃ n : ℕ, 0 < n ∧ (n - 1) % row.b = row.r - 1 ∧ scoreState c x = registers n 0 ∧
        y = registers (row.a * ((n - 1) / row.b) + row.s : ℕ) 0 := by
  simp only [scoreRun_iff_circleRun c _ x y hx]
  exact row.completes_iff_positive_residue hr hrb _ _

theorem compiled_passage_iff (row : Transfer) (hr : 0 < row.r) (hrb : row.r ≤ row.b)
    (c : ℝ) (x : Score) (y : State) (hx : OnSquare (scoreLift c x)) :
    (∃ k j ms, Compiles c (row.word k j) ms ∧ scoreGain x ms = 0 ∧
        y = scoreState c (endpointScores id x ms)) ↔
      ∃ n : ℕ, 0 < n ∧ (n - 1) % row.b = row.r - 1 ∧ scoreState c x = registers n 0 ∧
        y = registers (row.a * ((n - 1) / row.b) + row.s : ℕ) 0 := by
  simpa only [scoreRun_iff_compiled] using score_passage_iff row hr hrb c x y hx

end

end Q61ClosedCircleTransfer
