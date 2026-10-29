/- GID: D5/S3/Arith/Congruence/BalaA363411
   generality: I
   mirror-B: D5/B/S3/Arith/Congruence/BalaA363411
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Congruence/BalaA363411.result; premises=D5/S3/Arith/Congruence/BalaA363411.block_twentyfive,D5/S3/Arith/Congruence/BalaA363411.period_twenty,D5/S3/Arith/Congruence/BalaA363411.residues_five,D5/S3/Arith/Congruence/BalaA363411.residues_twentyfive
   digest: Bala real-product five-adic valuation. -/

/-
admission_basis: open-problem-resolution (#18633; Proved)
Mathematical escape witnesses are named per content declaration below.
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21978.
proof_shape: real_one: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411TypeOne.three_nonzero, D5.S3.Arith.Congruence.BalaA363412.uniform_shift.
proof_shape: product_step: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411.seq_cast.
proof_shape: seq_cast: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_cast; consumers: D5.S3.Arith.Congruence.BalaA363411.real_mod_five, D5.S3.Arith.Congruence.BalaA363411.real_not_dvd_twentyfive, D5.S3.Arith.Congruence.BalaA363412.result, D5.S3.Arith.Congruence.BalaA363411TypeOne.result, D5.S3.Arith.Congruence.BalaA363411TypeOne.three_nonzero.
proof_shape: seq_shift: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_shift; consumers: D5.S3.Arith.Congruence.BalaA363411.seq_period, D5.S3.Arith.Congruence.BalaA363411.shift_twentyfive, D5.S3.Arith.Congruence.BalaA363411TypeOne.nonzero_of_block.
proof_shape: seq_period: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_shift; consumers: D5.S3.Arith.Congruence.BalaA363411.period_twenty, D5.S3.Arith.Congruence.BalaA363411.period_hundred, D5.S3.Arith.Congruence.BalaA363412.result.
proof_shape: seq_mod: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411.real_mod_five, D5.S3.Arith.Congruence.BalaA363411.real_not_dvd_twentyfive, D5.S3.Arith.Congruence.BalaA363412.result.
proof_shape: period_twenty: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_shift; consumers: D5.S3.Arith.Congruence.BalaA363411.real_mod_five.
proof_shape: block_twentyfive: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411.shift_twentyfive, D5.S3.Arith.Congruence.BalaA363411.period_hundred.
proof_shape: shift_twentyfive: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_shift; consumers: D5.S3.Arith.Congruence.BalaA363411.period_hundred.
proof_shape: period_hundred: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_shift; consumers: D5.S3.Arith.Congruence.BalaA363411.real_not_dvd_twentyfive.
proof_shape: residues_five: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411.real_mod_five.
proof_shape: residues_twentyfive: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411.real_not_dvd_twentyfive.
proof_shape: real_mod_five: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_cast; consumers: D5.S3.Arith.Congruence.BalaA363411.result.
proof_shape: real_not_dvd_twentyfive: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_cast; consumers: D5.S3.Arith.Congruence.BalaA363411.result.
proof_shape: valuation_one: bind-only; consumers: D5.S3.Arith.Congruence.BalaA363411.result.
proof_shape: result: content; escape_witness: D5.S3.Arith.Congruence.BalaA363411.seq_shift; consumers: none (settling result).
The product and sequence definitions retain the source expressions.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Periodic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 200000

namespace D5.S3.Arith.Congruence.BalaA363411

/-- `∏_{k=0}^{n} (1 + k√-3)` in `ℤ[√-3]`. -/
def P (n : ℕ) : ℤ√(-3) := ∏ k ∈ Finset.range (n + 1), (⟨1, k⟩ : ℤ√(-3))

/-- A363411: the real part of `∏_{k=0}^{n} (1 + k√-3)`. -/
def a (n : ℕ) : ℤ := (P n).re

/-- A363412: `1/√3` times the imaginary part of `∏_{k=0}^{n} (1 + k√-3)`, that is, the
`√-3`-coordinate. -/
def b (n : ℕ) : ℤ := (P n).im

/-- A363411 ("Conjecture: the 5-adic valuation v_5(a(n+2)) = A079998(n)"), where A079998 is the
characteristic function of the multiples of 5. -/
def claim : Prop := ∀ n : ℕ, padicValInt 5 (a (n + 2)) = if 5 ∣ n then 1 else 0

def seq (R : Type*) [CommRing R] : ℕ → R × R
  | 0 => (1, 0)
  | n + 1 => let z := seq R n
    (z.1 - 3 * (n + 1) * z.2, z.2 + (n + 1) * z.1)

theorem real_one {ι : Type*} (s : Finset ι) (f : ι → ℤ) :
    ∃ u : ℤ, (∏ i ∈ s, (⟨1, f i⟩ : ℤ√(-3))).re = 1 + 3*u := by
  classical
  let φ : ℤ√(-3) →+* ZMod 3 := Zsqrtd.lift ⟨0, by decide⟩
  have hm : φ (∏ i ∈ s, (⟨1, f i⟩ : ℤ√(-3))) = 1 := by
    rw [map_prod]
    simp [φ, Zsqrtd.lift_apply_apply]
  have hre : ((∏ i ∈ s, (⟨1, f i⟩ : ℤ√(-3))).re : ZMod 3) = 1 := by
    change ((∏ i ∈ s, (⟨1, f i⟩ : ℤ√(-3))).re : ZMod 3) +
      ((∏ i ∈ s, (⟨1, f i⟩ : ℤ√(-3))).im : ZMod 3) * 0 = 1 at hm
    simpa only [mul_zero, add_zero] using hm
  have hz : (((∏ i ∈ s, (⟨1, f i⟩ : ℤ√(-3))).re - 1 : ℤ) : ZMod 3) = 0 := by
    simp [hre]
  obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
  exact ⟨u, by omega⟩


private theorem product_step (n : ℕ) : P (n+1) = P n * (⟨1, n+1⟩ : ℤ√(-3)) := by
  simp [P, Finset.prod_range_succ, Nat.cast_add, Nat.cast_one]

theorem seq_cast (R : Type*) [CommRing R] (n : ℕ) :
    seq R n = ((a n : R), (b n : R)) := by
  induction n with
  | zero => simp [seq, a, b, P]
  | succ n ih =>
    rw [seq, ih]
    apply Prod.ext <;> simp [a, b, product_step, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

theorem seq_shift (R : Type*) [CommRing R] (q : ℕ) (c : R)
    (hq : (q : R) = 0) (hbase : seq R q = (c, 0)) (n : ℕ) :
    seq R (n+q) = (c * (seq R n).1, c * (seq R n).2) := by
  induction n with
  | zero => simpa [seq] using hbase
  | succ n ih =>
    rw [show n+1+q = (n+q)+1 by omega, seq, ih]
    simp only [seq, Nat.cast_add, hq, add_zero]
    apply Prod.ext <;> dsimp <;> ring

theorem seq_period (R : Type*) [CommRing R] (q : ℕ)
    (hq : (q : R) = 0) (hbase : seq R q = (1, 0)) :
    Function.Periodic (seq R) q := by
  intro n
  simpa using seq_shift R q 1 hq hbase n

theorem seq_mod (R : Type*) [CommRing R] (q : ℕ)
    (hp : Function.Periodic (seq R) q) (n : ℕ) :
    seq R n = seq R (n % q) := (hp.map_mod_nat n).symm

private theorem period_twenty : Function.Periodic (seq (ZMod 5)) 20 :=
  seq_period _ _ (by decide +kernel) (by decide +kernel)

private theorem block_twentyfive : seq (ZMod 25) 25 = (7,0) := by exact Prod.ext rfl rfl

private theorem shift_twentyfive (n : ℕ) :
    seq (ZMod 25) (n+25) = (7*(seq (ZMod 25) n).1, 7*(seq (ZMod 25) n).2) :=
  seq_shift _ _ _ (by decide +kernel) block_twentyfive n

private theorem period_hundred : Function.Periodic (seq (ZMod 25)) 100 := by
  have h50 : seq (ZMod 25) 50 = (24,0) := by
    apply Prod.ext
    · simpa [block_twentyfive, show (7:ZMod 25)*7=24 by decide +kernel] using
        congrArg Prod.fst (shift_twentyfive 25)
    · simpa [block_twentyfive] using congrArg Prod.snd (shift_twentyfive 25)
  have h75 : seq (ZMod 25) 75 = (18,0) := by
    apply Prod.ext
    · simpa [h50, show (7:ZMod 25)*24=18 by decide +kernel] using
        congrArg Prod.fst (shift_twentyfive 50)
    · simpa [h50] using congrArg Prod.snd (shift_twentyfive 50)
  have h100 : seq (ZMod 25) 100 = (1,0) := by
    apply Prod.ext
    · simpa [h75, show (7:ZMod 25)*18=1 by decide +kernel] using
        congrArg Prod.fst (shift_twentyfive 75)
    · simpa [h75] using congrArg Prod.snd (shift_twentyfive 75)
  exact seq_period _ _ (by decide +kernel) h100

private theorem residues_five : ∀ r : Fin 20,
    ((seq (ZMod 5) r).1 = 0 ↔ r.val % 5 = 2) := by decide +kernel

private theorem residues_twentyfive : ∀ r : Fin 100,
    (seq (ZMod 25) r).1 ≠ 0 := by decide +kernel

private theorem real_mod_five (n : ℕ) : (5:ℤ) ∣ a n ↔ n % 5 = 2 := by
  have h := residues_five ⟨n % 20, Nat.mod_lt n (by decide)⟩
  rw [← seq_mod _ _ period_twenty n, seq_cast] at h
  simpa [ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.mod_mod_of_dvd n (by decide : 5 ∣ 20)] using h

private theorem real_not_dvd_twentyfive (n : ℕ) : ¬ (25:ℤ) ∣ a n := by
  have h := residues_twentyfive ⟨n % 100, Nat.mod_lt n (by decide)⟩
  rw [← seq_mod _ _ period_hundred n, seq_cast] at h
  simpa [ZMod.intCast_zmod_eq_zero_iff_dvd] using h

private theorem valuation_one {z : ℤ} (h5 : (5:ℤ) ∣ z) (h25 : ¬ (25:ℤ) ∣ z) :
    padicValInt 5 z = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hn : z ≠ 0 := by intro hz; apply h25; simp [hz]
  have hlow : 1 ≤ padicValInt 5 z := by
    exact (padicValInt_dvd_iff (p:=5) 1 z).mp (by simpa using h5) |>.resolve_left hn
  have hhigh : ¬ 2 ≤ padicValInt 5 z := by
    intro h
    apply h25
    exact (padicValInt_dvd_iff (p:=5) 2 z).mpr (Or.inr h)
  omega

theorem result : D5.S3.Arith.Congruence.BalaA363411.claim := by
  intro n
  have hm : (n+2) % 5 = 2 ↔ 5 ∣ n := by omega
  split_ifs with h
  · exact D5.S3.Arith.Congruence.BalaA363411.valuation_one ((D5.S3.Arith.Congruence.BalaA363411.real_mod_five _).mpr (hm.mpr h))
      (D5.S3.Arith.Congruence.BalaA363411.real_not_dvd_twentyfive _)
  · apply padicValInt.eq_zero_of_not_dvd
    intro hd
    exact h (hm.mp ((D5.S3.Arith.Congruence.BalaA363411.real_mod_five _).mp hd))

end D5.S3.Arith.Congruence.BalaA363411
