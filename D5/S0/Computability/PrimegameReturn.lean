/- GID: D5/S0/Computability/PrimegameReturn
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Function.Iterate]
   utility: none
   digest: Exact first returns and microstep times of Conway's ordered PRIMEGAME. -/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false
namespace Primegame

/-- Numerator-denominator pairs, in execution priority order. -/
def program : List (ℕ × ℕ) :=
  [(17,91), (78,85), (19,51), (23,38), (29,33), (77,29), (95,23),
    (77,19), (1,17), (11,13), (13,11), (15,2), (1,7), (55,1)]

/-- Select the first fraction whose product with the current integer is integral. -/
def firstStep : List (ℕ × ℕ) → ℕ → ℕ
  | [], n => n
  | (u,v) :: fs, n => if v ∣ n * u then n * u / v else firstStep fs n

def step (n : ℕ) : ℕ := firstStep program n

def checkpoint (n k : ℕ) : ℕ := 13 * 5^n * 7^k

/-- The entire monomial section, including boundary parameters. -/
def IsCheckpoint (x : ℕ) : Prop := ∃ n k, x = checkpoint n k

inductive Control | plain | c11 | c13 | c17 | c19 | c23 | c29
  deriving DecidableEq

def Control.value : Control → ℕ
  | .plain => 1 | .c11 => 11 | .c13 => 13 | .c17 => 17
  | .c19 => 19 | .c23 => 23 | .c29 => 29

structure State where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  control : Control
  deriving DecidableEq

def encode (x : State) : ℕ := 2^x.a * 3^x.b * 5^x.c * 7^x.d * x.control.value

/-- The seven control branches, each still one original fraction step. -/
def next : State → State
  | ⟨a,b,c,d+1,.c13⟩ => ⟨a,b,c,d,.c17⟩
  | ⟨a,b,c,0,.c13⟩ => ⟨a,b,c,0,.c11⟩
  | ⟨a,b,c+1,d,.c17⟩ => ⟨a+1,b+1,c,d,.c13⟩
  | ⟨a,b+1,0,d,.c17⟩ => ⟨a,b,0,d,.c19⟩
  | ⟨a,0,0,d,.c17⟩ => ⟨a,0,0,d,.plain⟩
  | ⟨a+1,b,c,d,.c19⟩ => ⟨a,b,c,d,.c23⟩
  | ⟨0,b,c,d,.c19⟩ => ⟨0,b,c,d+1,.c11⟩
  | ⟨a,b,c,d,.c23⟩ => ⟨a,b,c+1,d,.c19⟩
  | ⟨a,b+1,c,d,.c11⟩ => ⟨a,b,c,d,.c29⟩
  | ⟨a,0,c,d,.c11⟩ => ⟨a,0,c,d,.c13⟩
  | ⟨a,b,c,d,.c29⟩ => ⟨a,b,c,d+1,.c11⟩
  | ⟨a+1,b,c,d,.plain⟩ => ⟨a,b+1,c+1,d,.plain⟩
  | ⟨0,b,c,d+1,.plain⟩ => ⟨0,b,c,d,.plain⟩
  | ⟨0,b,c,0,.plain⟩ => ⟨0,b,c+1,0,.c11⟩

private theorem prime_pow_dvd (p x e : ℕ) (hp : p.Prime) :
    p ∣ x^e ↔ p ∣ x ∧ e ≠ 0 := by
  cases e with
  | zero => simp [hp.not_dvd_one]
  | succ e => simpa using hp.prime.dvd_pow_iff_dvd (Nat.succ_ne_zero e)

private theorem pair_dvd (p q x : ℕ) (h : p.Coprime q) :
    p*q ∣ x ↔ p ∣ x ∧ q ∣ x :=
  ⟨fun h' => ⟨dvd_trans (dvd_mul_right _ _) h', dvd_trans (dvd_mul_left _ _) h'⟩,
   fun h' => h.mul_dvd_of_dvd_of_dvd h'.1 h'.2⟩

private theorem guards (x : ℕ) :
    (91 ∣ x ↔ 7 ∣ x ∧ 13 ∣ x) ∧
    (85 ∣ x ↔ 5 ∣ x ∧ 17 ∣ x) ∧
    (51 ∣ x ↔ 3 ∣ x ∧ 17 ∣ x) ∧
    (38 ∣ x ↔ 2 ∣ x ∧ 19 ∣ x) ∧
    (33 ∣ x ↔ 3 ∣ x ∧ 11 ∣ x) := by
  exact ⟨pair_dvd 7 13 x (by decide), pair_dvd 5 17 x (by decide),
    pair_dvd 3 17 x (by decide), pair_dvd 2 19 x (by decide),
    pair_dvd 3 11 x (by decide)⟩

private theorem reduced_step (n : ℕ) : step n =
    if 91 ∣ n then n*17/91 else if 85 ∣ n then n*78/85 else
    if 51 ∣ n then n*19/51 else if 38 ∣ n then n*23/38 else
    if 33 ∣ n then n*29/33 else if 29 ∣ n then n*77/29 else
    if 23 ∣ n then n*95/23 else if 19 ∣ n then n*77/19 else
    if 17 ∣ n then n/17 else if 13 ∣ n then n*11/13 else
    if 11 ∣ n then n*13/11 else if 2 ∣ n then n*15/2 else
    if 7 ∣ n then n/7 else n*55 := by
  simp only [step, program, firstStep]
  simp only [(show Nat.Coprime 91 17 from by decide).dvd_mul_right,
    (show Nat.Coprime 85 78 from by decide).dvd_mul_right,
    (show Nat.Coprime 51 19 from by decide).dvd_mul_right,
    (show Nat.Coprime 38 23 from by decide).dvd_mul_right,
    (show Nat.Coprime 33 29 from by decide).dvd_mul_right,
    (show Nat.Coprime 29 77 from by decide).dvd_mul_right,
    (show Nat.Coprime 23 95 from by decide).dvd_mul_right,
    (show Nat.Coprime 19 77 from by decide).dvd_mul_right,
    (show Nat.Coprime 13 11 from by decide).dvd_mul_right,
    (show Nat.Coprime 11 13 from by decide).dvd_mul_right,
    (show Nat.Coprime 2 15 from by decide).dvd_mul_right,
    Nat.mul_one, one_dvd, if_true, Nat.div_one]

private theorem dvd_encode (p : ℕ) (hp : p.Prime) (x : State) :
    p ∣ encode x ↔ (p ∣ 2 ∧ x.a ≠ 0) ∨ (p ∣ 3 ∧ x.b ≠ 0) ∨
      (p ∣ 5 ∧ x.c ≠ 0) ∨ (p ∣ 7 ∧ x.d ≠ 0) ∨ p ∣ x.control.value := by
  simp only [encode, hp.dvd_mul, prime_pow_dvd p _ _ hp]
  tauto

set_option maxHeartbeats 2000000 in
-- Each control branch discharges all earlier-priority divisibility guards.
private theorem encode_next (x : State) : step (encode x) = encode (next x) := by
  rcases x with ⟨a,b,c,d,s⟩
  cases s
  case' plain => cases a <;> cases d
  case' c11 => cases b
  case' c13 => cases d
  case' c17 => cases c <;> cases b
  case' c19 => cases a
  all_goals
    simp only [reduced_step, (guards _).1, (guards _).2.1,
      (guards _).2.2.1, (guards _).2.2.2.1, (guards _).2.2.2.2]
    norm_num [dvd_encode 2 (by decide), dvd_encode 3 (by decide),
      dvd_encode 5 (by decide), dvd_encode 7 (by decide),
      dvd_encode 11 (by decide), dvd_encode 13 (by decide),
      dvd_encode 17 (by decide), dvd_encode 19 (by decide),
      dvd_encode 23 (by decide), dvd_encode 29 (by decide), Control.value]
    first | apply Nat.div_eq_of_eq_mul_left (by norm_num) | skip
  all_goals simp [encode, next, Control.value, pow_succ] <;> ring

private def Clear (x : State) : Prop :=
  x.control ≠ .c13 ∨ 0 < x.a ∨ 0 < x.b

private theorem clear_not_checkpoint (x : State) (hc : Clear x) :
    ¬IsCheckpoint (encode x) := by
  rintro ⟨n,k,h⟩
  have h13 : 13 ∣ encode x := by
    rw [h]; exact ⟨5^n*7^k, by simp [checkpoint, Nat.mul_assoc]⟩
  have h2 : ¬2 ∣ encode x := by
    rw [h]
    norm_num [checkpoint, Nat.prime_two.dvd_mul,
      prime_pow_dvd 2 _ _ Nat.prime_two]
  have h3 : ¬3 ∣ encode x := by
    rw [h]
    norm_num [checkpoint, Nat.prime_three.dvd_mul,
      prime_pow_dvd 3 _ _ Nat.prime_three]
  rcases x with ⟨a,b,c,d,s⟩
  cases s <;> norm_num [dvd_encode 13 (by decide), Control.value] at h13
  norm_num [dvd_encode 2 (by decide), dvd_encode 3 (by decide), Control.value] at h2 h3
  simp_all [Clear]

/-- A segment of the actual register iteration, with no interior section crossing. -/
private def Travel (x : State) (t : ℕ) (y : State) : Prop :=
  next^[t] x = y ∧ ∀ i, 0 < i → i < t → Clear (next^[i] x)

private theorem travel_zero (x : State) : Travel x 0 x :=
  ⟨rfl, by intro i hi ht; omega⟩

private theorem travel_one (x y : State) (h : next x = y) : Travel x 1 y :=
  ⟨h, by intro i hi ht; omega⟩

private theorem travel_comp {x y z : State} {m n : ℕ}
    (h : Travel x m y) (g : Travel y n z) (hy : Clear y) : Travel x (m+n) z := by
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm m n, Function.iterate_add_apply, h.1, g.1]
  · intro i hi ht
    rcases lt_trichotomy i m with him | him | him
    · exact h.2 i hi him
    · simpa [him, h.1] using hy
    · have ei : i = (i-m)+m := by omega
      rw [ei, Function.iterate_add_apply, h.1]
      exact g.2 (i-m) (by omega) (by omega)

private theorem travel_u (a b c d j : ℕ) :
    Travel ⟨a,b,c+j,d+j,.c13⟩ (2*j) ⟨a+j,b+j,c,d,.c13⟩ := by
  induction j generalizing a b c d with
  | zero => simpa using travel_zero (⟨a,b,c,d,.c13⟩ : State)
  | succ j ih =>
    have h₁ : Travel ⟨a,b,c+j+1,d+j+1,.c13⟩ 1 ⟨a,b,c+j+1,d+j,.c17⟩ :=
      travel_one _ _ (by simp [next])
    have h₂ : Travel ⟨a,b,c+j+1,d+j,.c17⟩ 1 ⟨a+1,b+1,c+j,d+j,.c13⟩ :=
      travel_one _ _ (by simp [next])
    have h := travel_comp (travel_comp h₁ h₂ (by simp [Clear]))
      (ih (a+1) (b+1) c d) (by simp [Clear])
    convert h using 1 <;> first | omega | (congr 1 <;> omega)

private theorem travel_v (a b c d j : ℕ) :
    Travel ⟨a,b+j,c,d,.c11⟩ (2*j) ⟨a,b,c,d+j,.c11⟩ := by
  induction j generalizing b d with
  | zero => simpa using travel_zero (⟨a,b,c,d,.c11⟩ : State)
  | succ j ih =>
    have h₁ : Travel ⟨a,b+j+1,c,d,.c11⟩ 1 ⟨a,b+j,c,d,.c29⟩ :=
      travel_one _ _ (by simp [next])
    have h₂ : Travel ⟨a,b+j,c,d,.c29⟩ 1 ⟨a,b+j,c,d+1,.c11⟩ :=
      travel_one _ _ (by simp [next])
    have h := travel_comp (travel_comp h₁ h₂ (by simp [Clear]))
      (ih b (d+1)) (by simp [Clear])
    convert h using 1 <;> first | omega | (congr 1 <;> omega)

private theorem travel_w (a b c d j : ℕ) :
    Travel ⟨a+j,b,c,d,.c19⟩ (2*j) ⟨a,b,c+j,d,.c19⟩ := by
  induction j generalizing a c with
  | zero => simpa using travel_zero (⟨a,b,c,d,.c19⟩ : State)
  | succ j ih =>
    have h₁ : Travel ⟨a+j+1,b,c,d,.c19⟩ 1 ⟨a+j,b,c,d,.c23⟩ :=
      travel_one _ _ (by simp [next])
    have h₂ : Travel ⟨a+j,b,c,d,.c23⟩ 1 ⟨a+j,b,c+1,d,.c19⟩ :=
      travel_one _ _ (by simp [next])
    have h := travel_comp (travel_comp h₁ h₂ (by simp [Clear]))
      (ih a (c+1)) (by simp [Clear])
    convert h using 1 <;> first | omega | (congr 1 <;> omega)

private theorem travel_plain (a b c d j : ℕ) :
    Travel ⟨a+j,b,c,d,.plain⟩ j ⟨a,b+j,c+j,d,.plain⟩ := by
  induction j generalizing a b c with
  | zero => simpa using travel_zero (⟨a,b,c,d,.plain⟩ : State)
  | succ j ih =>
    have h₁ : Travel ⟨a+j+1,b,c,d,.plain⟩ 1 ⟨a+j,b+1,c+1,d,.plain⟩ :=
      travel_one _ _ (by simp [next])
    have h := travel_comp h₁ (ih a (b+1) (c+1)) (by simp [Clear])
    convert h using 1 <;> first | omega | (congr 1 <;> omega)

private theorem travel_sevens (b c d : ℕ) :
    Travel ⟨0,b,c,d,.plain⟩ d ⟨0,b,c,0,.plain⟩ := by
  induction d with
  | zero => exact travel_zero _
  | succ d ih =>
    have h₁ : Travel ⟨0,b,c,d+1,.plain⟩ 1 ⟨0,b,c,d,.plain⟩ :=
      travel_one _ _ (by simp [next])
    simpa [Nat.add_comm] using travel_comp h₁ ih (by simp [Clear])

private theorem travel_cycle (a c k : ℕ) (hk : 0 < k) :
    Travel ⟨a,0,c+k,k,.c13⟩ (4*k+2) ⟨a+k,0,c,k,.c13⟩ := by
  have h₁ := travel_u a 0 c 0 k
  have h₂ : Travel ⟨a+k,k,c,0,.c13⟩ 1 ⟨a+k,k,c,0,.c11⟩ :=
    travel_one _ _ (by simp [next])
  have h₃ := travel_v (a+k) 0 c 0 k
  have h₄ : Travel ⟨a+k,0,c,k,.c11⟩ 1 ⟨a+k,0,c,k,.c13⟩ :=
    travel_one _ _ (by simp [next])
  simp only [Nat.zero_add] at h₁ h₃
  have h := travel_comp (travel_comp (travel_comp h₁ h₂
    (by simp [Clear]; omega)) h₃ (by simp [Clear])) h₄ (by simp [Clear])
  convert h using 1
  omega

private theorem travel_cycles (a c k q : ℕ) (hk : 0 < k) :
    Travel ⟨a,0,c+q*k,k,.c13⟩ (q*(4*k+2)) ⟨a+q*k,0,c,k,.c13⟩ := by
  induction q generalizing a c with
  | zero => simpa using travel_zero (⟨a,0,c,k,.c13⟩ : State)
  | succ q ih =>
    have h₁ := travel_cycle a (c+q*k) k hk
    have h₂ := ih (a+k) c
    have h := travel_comp h₁ h₂ (by simp [Clear]; omega)
    simpa only [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem travel_nondvd_tail (a b d : ℕ) :
    Travel ⟨a,0,b+1,(d+1)+(b+1),.c13⟩ (2*(a+b+1)+4*(b+1)+2)
      ⟨0,0,a+b+1,d+1+b,.c13⟩ := by
  have h₁ := travel_u a 0 0 (d+1) (b+1)
  have h₂ : Travel ⟨a+(b+1),b+1,0,d+1,.c13⟩ 1
      ⟨a+(b+1),b+1,0,d,.c17⟩ := travel_one _ _ (by simp [next])
  have h₃ : Travel ⟨a+(b+1),b+1,0,d,.c17⟩ 1
      ⟨a+(b+1),b,0,d,.c19⟩ := travel_one _ _ (by simp [next])
  have h₄ := travel_w 0 b 0 d (a+(b+1))
  have h₅ : Travel ⟨0,b,a+(b+1),d,.c19⟩ 1
      ⟨0,b,a+(b+1),d+1,.c11⟩ := travel_one _ _ (by simp [next])
  have h₆ := travel_v 0 0 (a+(b+1)) (d+1) b
  have h₇ : Travel ⟨0,0,a+(b+1),d+1+b,.c11⟩ 1
      ⟨0,0,a+(b+1),d+1+b,.c13⟩ := travel_one _ _ (by simp [next])
  simp only [Nat.zero_add] at h₁ h₄ h₆
  have h := travel_comp (travel_comp (travel_comp (travel_comp
    (travel_comp (travel_comp h₁ h₂ (by simp [Clear])) h₃ (by simp [Clear]))
    h₄ (by simp [Clear])) h₅ (by simp [Clear])) h₆ (by simp [Clear]))
    h₇ (by simp [Clear])
  convert h using 1 <;> first | omega | congr 1

private theorem travel_dvd_tail (n d : ℕ) :
    Travel ⟨n,0,0,d+1,.c13⟩ (3*n+d+4) ⟨0,0,n+1,n,.c13⟩ := by
  have h₁ : Travel ⟨n,0,0,d+1,.c13⟩ 1 ⟨n,0,0,d,.c17⟩ :=
    travel_one _ _ (by simp [next])
  have h₂ : Travel ⟨n,0,0,d,.c17⟩ 1 ⟨n,0,0,d,.plain⟩ :=
    travel_one _ _ (by simp [next])
  have h₃ := travel_plain 0 0 0 d n
  have h₄ := travel_sevens n n d
  have h₅ : Travel ⟨0,n,n,0,.plain⟩ 1 ⟨0,n,n+1,0,.c11⟩ :=
    travel_one _ _ (by simp [next])
  have h₆ := travel_v 0 0 (n+1) 0 n
  have h₇ : Travel ⟨0,0,n+1,n,.c11⟩ 1 ⟨0,0,n+1,n,.c13⟩ :=
    travel_one _ _ (by simp [next])
  simp only [Nat.zero_add] at h₃ h₆
  have h := travel_comp (travel_comp (travel_comp (travel_comp
    (travel_comp (travel_comp h₁ h₂ (by simp [Clear])) h₃ (by simp [Clear]))
    h₄ (by simp [Clear])) h₅ (by simp [Clear])) h₆ (by simp [Clear]))
    h₇ (by simp [Clear])
  convert h using 1
  omega

private theorem encode_iterate (x : State) (t : ℕ) :
    step^[t] (encode x) = encode (next^[t] x) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, encode_next]

/-- Number of original fraction applications before the next section crossing. -/
def returnTime (n k : ℕ) : ℕ :=
  if k ∣ n then 7*n+2*(n/k)+k+3 else 6*n+2*(n/k)+2

/-- Integer endpoint of a single trial division. -/
def returnPoint (n k : ℕ) : ℕ :=
  if k ∣ n then checkpoint (n+1) n else checkpoint n (k-1)

/-- Exact first return for all valid trial divisors.  The divisible branch also
records the precise time of the intermediate output-axis state. -/
theorem first_return (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    0 < returnTime n k ∧
    step^[returnTime n k] (checkpoint n k) = returnPoint n k ∧
    (∀ t, 0 < t → t < returnTime n k →
      ¬IsCheckpoint (step^[t] (checkpoint n k))) ∧
    (k ∣ n →
      0 < (n/k)*(4*k+2)+2 ∧ (n/k)*(4*k+2)+2 < returnTime n k ∧
      step^[(n/k)*(4*k+2)+2] (checkpoint n k) = 2^n*7^(k-1)) := by
  have hk0 : 0 < k := hk
  have hn : 0 < n := lt_of_lt_of_le hk0 hkn
  let q := n/k
  let r := n%k
  have hr : r < k := Nat.mod_lt n hk0
  have hqr : r+q*k = n := by simpa [r, q, Nat.mul_comm] using Nat.mod_add_div n k
  have hs : encode ⟨0,0,n,k,.c13⟩ = checkpoint n k := by
    simp [encode, checkpoint, Control.value]; ring
  have hc := travel_cycles 0 r k q hk0
  simp only [Nat.zero_add, hqr] at hc
  by_cases hd : k ∣ n
  · have hz : r = 0 := Nat.mod_eq_zero_of_dvd hd
    have hq : q*k = n := by omega
    rw [hz, hq] at hc
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk0)
    have ht := travel_comp hc (travel_dvd_tail n d) (by simp [Clear, hn])
    have he : q*(4*(d+1)+2)+(3*n+d+4) = returnTime n (d+1) := by
      simp only [returnTime, if_pos hd]
      dsimp [q] at hq ⊢
      nlinarith [hq]
    rw [he] at ht
    refine ⟨by simp [returnTime, hd], ?_, ?_, ?_⟩
    · rw [← hs, encode_iterate, ht.1]
      simp [returnPoint, hd, encode, checkpoint, Control.value]; ring
    · intro t hpos hlt
      rw [← hs, encode_iterate]
      exact clear_not_checkpoint _ (ht.2 t hpos hlt)
    · intro _
      refine ⟨by omega, ?_, ?_⟩
      · rw [← he]; dsimp [q]; omega
      · rw [← hs, Nat.add_comm ((n/(d+1))*(4*(d+1)+2)) 2,
          Function.iterate_add_apply, encode_iterate, hc.1]
        rw [encode_iterate]
        simp [Function.iterate_succ_apply, next, encode, Control.value]
  · have hr0 : 0 < r := Nat.pos_of_ne_zero (fun h => hd (Nat.dvd_of_mod_eq_zero h))
    obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr0)
    have hkr : 0 < k-r := Nat.sub_pos_of_lt hr
    obtain ⟨d, hkd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkr)
    have hke : k = (d+1)+(b+1) := by omega
    have hne : n = q*k+b+1 := by omega
    have tail := travel_nondvd_tail (q*k) b d
    have hmid : Clear (⟨q*k,0,r,k,.c13⟩ : State) := by
      have hqpos : 0 < q := Nat.div_pos hkn hk0
      simp only [Clear, ne_eq, not_true_eq_false, false_or, Nat.lt_irrefl, or_false]
      exact Nat.mul_pos hqpos hk0
    have tail' : Travel ⟨q*k,0,r,k,.c13⟩
        (2*(q*k+b+1)+4*(b+1)+2) ⟨0,0,q*k+b+1,d+1+b,.c13⟩ := by
      simpa only [hb, hke] using tail
    have ht := travel_comp hc tail' hmid
    have he : q*(4*k+2)+(2*(q*k+b+1)+4*(b+1)+2) = returnTime n k := by
      simp only [returnTime, if_neg hd]
      change q*(4*k+2)+(2*(q*k+b+1)+4*(b+1)+2) = 6*n+2*q+2
      nlinarith [hne]
    rw [he] at ht
    refine ⟨by simp [returnTime, hd], ?_, ?_, by simp [hd]⟩
    · rw [← hs, encode_iterate, ht.1]
      have he' : d+1+b = k-1 := by omega
      simp [returnPoint, hd, encode, checkpoint, Control.value, ← hne, he']; ring
    · intro t hpos hlt
      rw [← hs, encode_iterate]
      exact clear_not_checkpoint _ (ht.2 t hpos hlt)

end Primegame
