/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicModNinePointCount
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicModNinePointCount
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Kernel-checked Euler character counts for the native cubic at primes 109 and 379. -/

import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

set_option autoImplicit false

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicModNinePointCount

def equation {p : ℕ} (l x : ZMod p) : ZMod p :=
  x^3 - 3*(l^2+3)*x + 2*(l^2+3)*l

def enumerated (p : ℕ) [Fact p.Prime] (l : ZMod p) : ℕ :=
  1 + (Finset.univ.filter (fun q : ZMod p × ZMod p => q.2^2 = equation l q.1)).card


private def squarePow {p : ℕ} (a : ZMod p) : ℕ → ZMod p
  | 0 => a
  | n+1 => squarePow a n ^ 2

private theorem squarePow_eq {p : ℕ} (a : ZMod p) (n : ℕ) :
    squarePow a n = a^(2^n) := by
  induction n with
  | zero => simp [squarePow]
  | succ n h => rw [squarePow, h, pow_succ 2 n, pow_mul]

private def fastExp (p : ℕ) (a : ZMod p) : ZMod p :=
  if p=109 then squarePow a 5 * squarePow a 4 * squarePow a 2 * squarePow a 1
  else if p=379 then
    squarePow a 7 * squarePow a 5 * squarePow a 4 * squarePow a 3 * squarePow a 2 * a
  else a^(p/2)

private theorem fastExp_eq (p : ℕ) (a : ZMod p) : fastExp p a = a^(p/2) := by
  by_cases h : p = 109
  · subst p
    unfold fastExp
    simp only [ite_true, squarePow_eq, ← pow_add]
    rfl
  · by_cases h' : p = 379
    · subst p
      unfold fastExp
      simp only [ite_eq_right (by decide : (379:ℕ) ≠ 109), squarePow_eq]
      conv_rhs => rw [show 379/2=188+1 by decide, pow_add, pow_one]
      simp only [← pow_add]
      rfl
    · simp [fastExp, h, h']

private def contribution (p : ℕ) [Fact p.Prime] (l x : ZMod p) : ℕ :=
  if equation l x = 0 then 1 else if fastExp p (equation l x) = 1 then 2 else 0

/-- Linear-size enumeration using Euler's criterion, with one term per x. -/
def fastCount (p : ℕ) [Fact p.Prime] (l : ZMod p) : ℕ :=
  1 + ∑ x : ZMod p, contribution p l x

theorem count_eq_fast (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (l : ZMod p) :
    enumerated p l = fastCount p l := by
  let S : Finset (ZMod p × ZMod p) := Finset.univ.filter (fun q => q.2^2 = equation l q.1)
  have hfiber : S.card = ∑ x : ZMod p, (S.filter (fun q => q.1=x)).card :=
    Finset.card_eq_sum_card_fiberwise (f:=Prod.fst) (t:=Finset.univ) (fun _ _ => Finset.mem_univ _)
  unfold enumerated fastCount
  change 1 + S.card = _
  rw [hfiber]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  let Y : Finset (ZMod p) := Finset.univ.filter (fun y => y^2 = equation l x)
  have hy : (S.filter (fun q => q.1=x)).card = Y.card := by
    apply Finset.card_bij (fun q _ => q.2)
    · intro q hq
      simp only [S, Y, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      simpa only [hq.2] using hq.1
    · intro a ha b hb h
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact Prod.ext (ha.2.trans hb.2.symm) h
    · intro y hy
      refine ⟨(x,y), ?_, rfl⟩
      simpa only [S, Y, Finset.mem_filter, Finset.mem_univ, true_and, and_true] using hy
  rw [hy]
  have hc : (Y.card : ℤ) = quadraticChar (ZMod p) (equation l x) + 1 := by
    simpa only [Y, Set.toFinset_ofPred] using
      (quadraticChar_card_sqrts ((ZMod.ringChar_zmod_n p).substr hp) (equation l x))
  unfold contribution
  rw [fastExp_eq]
  by_cases h : equation l x = 0
  · simp only [h, ite_true]
    simp [h] at hc
    omega
  · rw [ite_eq_right h]
    rw [quadraticChar_eq_pow_of_char_ne_two ((ZMod.ringChar_zmod_n p).substr hp) h,
      ZMod.card p] at hc
    split <;> rename_i he <;> simp [he] at hc ⊢ <;> omega

theorem prime109 : Nat.Prime 109 := by
  apply Nat.prime_def_le_sqrt.2
  refine ⟨by decide, ?_⟩
  intro m h₁ h₂
  have hs : Nat.sqrt 109 < 11 := Nat.sqrt_lt.2 (by decide)
  have hlt : m < 11 := by omega
  exact (by decide : ∀ i : Fin 11, 2 ≤ i.val → ¬ i.val ∣ 109) ⟨m,hlt⟩ h₁

theorem prime379 : Nat.Prime 379 := by
  apply Nat.prime_def_le_sqrt.2
  refine ⟨by decide, ?_⟩
  intro m h₁ h₂
  have hs : Nat.sqrt 379 < 20 := Nat.sqrt_lt.2 (by decide)
  have hlt : m < 20 := by omega
  exact (by decide : ∀ i : Fin 20, 2 ≤ i.val → ¬ i.val ∣ 379) ⟨m,hlt⟩ h₁

private instance : Fact (Nat.Prime 109) := ⟨prime109⟩
private instance : Fact (Nat.Prime 379) := ⟨prime379⟩

private def chunk (p : ℕ) [Fact p.Prime] (l : ZMod p) (off len : ℕ) : ℕ :=
  ∑ i ∈ Finset.range len, contribution p l ((off+i : ℕ): ZMod p)

private theorem fastCount_chunk (p : ℕ) [Fact p.Prime] (l : ZMod p) :
    fastCount p l = 1 + chunk p l 0 p := by
  let hp : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let e : Fin p ≃ ZMod p := (ZMod.finEquiv p).toEquiv
  unfold fastCount chunk
  congr 1
  rw [← Equiv.sum_comp e]
  simp only [zero_add]
  rw [← Fin.sum_univ_eq_sum_range (fun i => contribution p l (i:ZMod p))]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  have hz : ((e x).val : ZMod p) = e x := ZMod.natCast_zmod_val _
  have hv : (e x).val = x.val := by
    dsimp only [e]
    cases p with
    | zero => exact ((Fact.out : Nat.Prime 0).ne_zero rfl).elim
    | succ k => rfl
  rw [hv] at hz
  exact hz.symm

private theorem chunk_split (p : ℕ) [Fact p.Prime] (l : ZMod p) (m n : ℕ) :
    chunk p l 0 (m+n) = chunk p l 0 m + chunk p l m n := by
  simp [chunk, Finset.sum_range_add]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109a_0 : chunk 109 43 0 16 = 12 := by decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109a_16 : chunk 109 43 16 16 = 12 := by decide
private theorem prefix_109a_32 : chunk 109 43 0 32 = 24 := by
  have h : chunk 109 43 0 32 = chunk 109 43 0 16 + chunk 109 43 16 16 :=
    chunk_split 109 43 16 16
  rw [h, block_109a_0, block_109a_16]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109a_32 : chunk 109 43 32 16 = 16 := by decide
private theorem prefix_109a_48 : chunk 109 43 0 48 = 40 := by
  have h : chunk 109 43 0 48 = chunk 109 43 0 32 + chunk 109 43 32 16 :=
    chunk_split 109 43 32 16
  rw [h, prefix_109a_32, block_109a_32]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109a_48 : chunk 109 43 48 16 = 14 := by decide
private theorem prefix_109a_64 : chunk 109 43 0 64 = 54 := by
  have h : chunk 109 43 0 64 = chunk 109 43 0 48 + chunk 109 43 48 16 :=
    chunk_split 109 43 48 16
  rw [h, prefix_109a_48, block_109a_48]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109a_64 : chunk 109 43 64 16 = 20 := by decide
private theorem prefix_109a_80 : chunk 109 43 0 80 = 74 := by
  have h : chunk 109 43 0 80 = chunk 109 43 0 64 + chunk 109 43 64 16 :=
    chunk_split 109 43 64 16
  rw [h, prefix_109a_64, block_109a_64]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109a_80 : chunk 109 43 80 16 = 22 := by decide
private theorem prefix_109a_96 : chunk 109 43 0 96 = 96 := by
  have h : chunk 109 43 0 96 = chunk 109 43 0 80 + chunk 109 43 80 16 :=
    chunk_split 109 43 80 16
  rw [h, prefix_109a_80, block_109a_80]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109a_96 : chunk 109 43 96 13 = 8 := by decide
private theorem prefix_109a_109 : chunk 109 43 0 109 = 104 := by
  have h : chunk 109 43 0 109 = chunk 109 43 0 96 + chunk 109 43 96 13 :=
    chunk_split 109 43 96 13
  rw [h, prefix_109a_96, block_109a_96]
theorem count109a : fastCount 109 43 = 105 := by
  rw [fastCount_chunk, prefix_109a_109]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109b_0 : chunk 109 66 0 16 = 10 := by decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109b_16 : chunk 109 66 16 16 = 24 := by decide
private theorem prefix_109b_32 : chunk 109 66 0 32 = 34 := by
  have h : chunk 109 66 0 32 = chunk 109 66 0 16 + chunk 109 66 16 16 :=
    chunk_split 109 66 16 16
  rw [h, block_109b_0, block_109b_16]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109b_32 : chunk 109 66 32 16 = 20 := by decide
private theorem prefix_109b_48 : chunk 109 66 0 48 = 54 := by
  have h : chunk 109 66 0 48 = chunk 109 66 0 32 + chunk 109 66 32 16 :=
    chunk_split 109 66 32 16
  rw [h, prefix_109b_32, block_109b_32]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109b_48 : chunk 109 66 48 16 = 12 := by decide
private theorem prefix_109b_64 : chunk 109 66 0 64 = 66 := by
  have h : chunk 109 66 0 64 = chunk 109 66 0 48 + chunk 109 66 48 16 :=
    chunk_split 109 66 48 16
  rw [h, prefix_109b_48, block_109b_48]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109b_64 : chunk 109 66 64 16 = 16 := by decide
private theorem prefix_109b_80 : chunk 109 66 0 80 = 82 := by
  have h : chunk 109 66 0 80 = chunk 109 66 0 64 + chunk 109 66 64 16 :=
    chunk_split 109 66 64 16
  rw [h, prefix_109b_64, block_109b_64]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109b_80 : chunk 109 66 80 16 = 14 := by decide
private theorem prefix_109b_96 : chunk 109 66 0 96 = 96 := by
  have h : chunk 109 66 0 96 = chunk 109 66 0 80 + chunk 109 66 80 16 :=
    chunk_split 109 66 80 16
  rw [h, prefix_109b_80, block_109b_80]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_109b_96 : chunk 109 66 96 13 = 8 := by decide
private theorem prefix_109b_109 : chunk 109 66 0 109 = 104 := by
  have h : chunk 109 66 0 109 = chunk 109 66 0 96 + chunk 109 66 96 13 :=
    chunk_split 109 66 96 13
  rw [h, prefix_109b_96, block_109b_96]
theorem count109b : fastCount 109 66 = 105 := by
  rw [fastCount_chunk, prefix_109b_109]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_0 : chunk 379 4 0 16 = 20 := by decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_16 : chunk 379 4 16 16 = 18 := by decide
private theorem prefix_379a_32 : chunk 379 4 0 32 = 38 := by
  have h : chunk 379 4 0 32 = chunk 379 4 0 16 + chunk 379 4 16 16 :=
    chunk_split 379 4 16 16
  rw [h, block_379a_0, block_379a_16]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_32 : chunk 379 4 32 16 = 18 := by decide
private theorem prefix_379a_48 : chunk 379 4 0 48 = 56 := by
  have h : chunk 379 4 0 48 = chunk 379 4 0 32 + chunk 379 4 32 16 :=
    chunk_split 379 4 32 16
  rw [h, prefix_379a_32, block_379a_32]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_48 : chunk 379 4 48 16 = 8 := by decide
private theorem prefix_379a_64 : chunk 379 4 0 64 = 64 := by
  have h : chunk 379 4 0 64 = chunk 379 4 0 48 + chunk 379 4 48 16 :=
    chunk_split 379 4 48 16
  rw [h, prefix_379a_48, block_379a_48]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_64 : chunk 379 4 64 16 = 22 := by decide
private theorem prefix_379a_80 : chunk 379 4 0 80 = 86 := by
  have h : chunk 379 4 0 80 = chunk 379 4 0 64 + chunk 379 4 64 16 :=
    chunk_split 379 4 64 16
  rw [h, prefix_379a_64, block_379a_64]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_80 : chunk 379 4 80 16 = 13 := by decide
private theorem prefix_379a_96 : chunk 379 4 0 96 = 99 := by
  have h : chunk 379 4 0 96 = chunk 379 4 0 80 + chunk 379 4 80 16 :=
    chunk_split 379 4 80 16
  rw [h, prefix_379a_80, block_379a_80]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_96 : chunk 379 4 96 16 = 18 := by decide
private theorem prefix_379a_112 : chunk 379 4 0 112 = 117 := by
  have h : chunk 379 4 0 112 = chunk 379 4 0 96 + chunk 379 4 96 16 :=
    chunk_split 379 4 96 16
  rw [h, prefix_379a_96, block_379a_96]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_112 : chunk 379 4 112 16 = 16 := by decide
private theorem prefix_379a_128 : chunk 379 4 0 128 = 133 := by
  have h : chunk 379 4 0 128 = chunk 379 4 0 112 + chunk 379 4 112 16 :=
    chunk_split 379 4 112 16
  rw [h, prefix_379a_112, block_379a_112]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_128 : chunk 379 4 128 16 = 18 := by decide
private theorem prefix_379a_144 : chunk 379 4 0 144 = 151 := by
  have h : chunk 379 4 0 144 = chunk 379 4 0 128 + chunk 379 4 128 16 :=
    chunk_split 379 4 128 16
  rw [h, prefix_379a_128, block_379a_128]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_144 : chunk 379 4 144 16 = 18 := by decide
private theorem prefix_379a_160 : chunk 379 4 0 160 = 169 := by
  have h : chunk 379 4 0 160 = chunk 379 4 0 144 + chunk 379 4 144 16 :=
    chunk_split 379 4 144 16
  rw [h, prefix_379a_144, block_379a_144]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_160 : chunk 379 4 160 16 = 8 := by decide
private theorem prefix_379a_176 : chunk 379 4 0 176 = 177 := by
  have h : chunk 379 4 0 176 = chunk 379 4 0 160 + chunk 379 4 160 16 :=
    chunk_split 379 4 160 16
  rw [h, prefix_379a_160, block_379a_160]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_176 : chunk 379 4 176 16 = 14 := by decide
private theorem prefix_379a_192 : chunk 379 4 0 192 = 191 := by
  have h : chunk 379 4 0 192 = chunk 379 4 0 176 + chunk 379 4 176 16 :=
    chunk_split 379 4 176 16
  rw [h, prefix_379a_176, block_379a_176]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_192 : chunk 379 4 192 16 = 10 := by decide
private theorem prefix_379a_208 : chunk 379 4 0 208 = 201 := by
  have h : chunk 379 4 0 208 = chunk 379 4 0 192 + chunk 379 4 192 16 :=
    chunk_split 379 4 192 16
  rw [h, prefix_379a_192, block_379a_192]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_208 : chunk 379 4 208 16 = 18 := by decide
private theorem prefix_379a_224 : chunk 379 4 0 224 = 219 := by
  have h : chunk 379 4 0 224 = chunk 379 4 0 208 + chunk 379 4 208 16 :=
    chunk_split 379 4 208 16
  rw [h, prefix_379a_208, block_379a_208]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_224 : chunk 379 4 224 16 = 24 := by decide
private theorem prefix_379a_240 : chunk 379 4 0 240 = 243 := by
  have h : chunk 379 4 0 240 = chunk 379 4 0 224 + chunk 379 4 224 16 :=
    chunk_split 379 4 224 16
  rw [h, prefix_379a_224, block_379a_224]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_240 : chunk 379 4 240 16 = 18 := by decide
private theorem prefix_379a_256 : chunk 379 4 0 256 = 261 := by
  have h : chunk 379 4 0 256 = chunk 379 4 0 240 + chunk 379 4 240 16 :=
    chunk_split 379 4 240 16
  rw [h, prefix_379a_240, block_379a_240]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_256 : chunk 379 4 256 16 = 16 := by decide
private theorem prefix_379a_272 : chunk 379 4 0 272 = 277 := by
  have h : chunk 379 4 0 272 = chunk 379 4 0 256 + chunk 379 4 256 16 :=
    chunk_split 379 4 256 16
  rw [h, prefix_379a_256, block_379a_256]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_272 : chunk 379 4 272 16 = 16 := by decide
private theorem prefix_379a_288 : chunk 379 4 0 288 = 293 := by
  have h : chunk 379 4 0 288 = chunk 379 4 0 272 + chunk 379 4 272 16 :=
    chunk_split 379 4 272 16
  rw [h, prefix_379a_272, block_379a_272]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_288 : chunk 379 4 288 16 = 18 := by decide
private theorem prefix_379a_304 : chunk 379 4 0 304 = 311 := by
  have h : chunk 379 4 0 304 = chunk 379 4 0 288 + chunk 379 4 288 16 :=
    chunk_split 379 4 288 16
  rw [h, prefix_379a_288, block_379a_288]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_304 : chunk 379 4 304 16 = 13 := by decide
private theorem prefix_379a_320 : chunk 379 4 0 320 = 324 := by
  have h : chunk 379 4 0 320 = chunk 379 4 0 304 + chunk 379 4 304 16 :=
    chunk_split 379 4 304 16
  rw [h, prefix_379a_304, block_379a_304]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_320 : chunk 379 4 320 16 = 14 := by decide
private theorem prefix_379a_336 : chunk 379 4 0 336 = 338 := by
  have h : chunk 379 4 0 336 = chunk 379 4 0 320 + chunk 379 4 320 16 :=
    chunk_split 379 4 320 16
  rw [h, prefix_379a_320, block_379a_320]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_336 : chunk 379 4 336 16 = 18 := by decide
private theorem prefix_379a_352 : chunk 379 4 0 352 = 356 := by
  have h : chunk 379 4 0 352 = chunk 379 4 0 336 + chunk 379 4 336 16 :=
    chunk_split 379 4 336 16
  rw [h, prefix_379a_336, block_379a_336]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_352 : chunk 379 4 352 16 = 13 := by decide
private theorem prefix_379a_368 : chunk 379 4 0 368 = 369 := by
  have h : chunk 379 4 0 368 = chunk 379 4 0 352 + chunk 379 4 352 16 :=
    chunk_split 379 4 352 16
  rw [h, prefix_379a_352, block_379a_352]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379a_368 : chunk 379 4 368 11 = 6 := by decide
private theorem prefix_379a_379 : chunk 379 4 0 379 = 375 := by
  have h : chunk 379 4 0 379 = chunk 379 4 0 368 + chunk 379 4 368 11 :=
    chunk_split 379 4 368 11
  rw [h, prefix_379a_368, block_379a_368]
theorem count379a : fastCount 379 4 = 376 := by
  rw [fastCount_chunk, prefix_379a_379]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_0 : chunk 379 76 0 16 = 16 := by decide
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_16 : chunk 379 76 16 16 = 14 := by decide
private theorem prefix_379b_32 : chunk 379 76 0 32 = 30 := by
  have h : chunk 379 76 0 32 = chunk 379 76 0 16 + chunk 379 76 16 16 :=
    chunk_split 379 76 16 16
  rw [h, block_379b_0, block_379b_16]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_32 : chunk 379 76 32 16 = 14 := by decide
private theorem prefix_379b_48 : chunk 379 76 0 48 = 44 := by
  have h : chunk 379 76 0 48 = chunk 379 76 0 32 + chunk 379 76 32 16 :=
    chunk_split 379 76 32 16
  rw [h, prefix_379b_32, block_379b_32]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_48 : chunk 379 76 48 16 = 14 := by decide
private theorem prefix_379b_64 : chunk 379 76 0 64 = 58 := by
  have h : chunk 379 76 0 64 = chunk 379 76 0 48 + chunk 379 76 48 16 :=
    chunk_split 379 76 48 16
  rw [h, prefix_379b_48, block_379b_48]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_64 : chunk 379 76 64 16 = 12 := by decide
private theorem prefix_379b_80 : chunk 379 76 0 80 = 70 := by
  have h : chunk 379 76 0 80 = chunk 379 76 0 64 + chunk 379 76 64 16 :=
    chunk_split 379 76 64 16
  rw [h, prefix_379b_64, block_379b_64]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_80 : chunk 379 76 80 16 = 14 := by decide
private theorem prefix_379b_96 : chunk 379 76 0 96 = 84 := by
  have h : chunk 379 76 0 96 = chunk 379 76 0 80 + chunk 379 76 80 16 :=
    chunk_split 379 76 80 16
  rw [h, prefix_379b_80, block_379b_80]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_96 : chunk 379 76 96 16 = 8 := by decide
private theorem prefix_379b_112 : chunk 379 76 0 112 = 92 := by
  have h : chunk 379 76 0 112 = chunk 379 76 0 96 + chunk 379 76 96 16 :=
    chunk_split 379 76 96 16
  rw [h, prefix_379b_96, block_379b_96]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_112 : chunk 379 76 112 16 = 14 := by decide
private theorem prefix_379b_128 : chunk 379 76 0 128 = 106 := by
  have h : chunk 379 76 0 128 = chunk 379 76 0 112 + chunk 379 76 112 16 :=
    chunk_split 379 76 112 16
  rw [h, prefix_379b_112, block_379b_112]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_128 : chunk 379 76 128 16 = 19 := by decide
private theorem prefix_379b_144 : chunk 379 76 0 144 = 125 := by
  have h : chunk 379 76 0 144 = chunk 379 76 0 128 + chunk 379 76 128 16 :=
    chunk_split 379 76 128 16
  rw [h, prefix_379b_128, block_379b_128]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_144 : chunk 379 76 144 16 = 16 := by decide
private theorem prefix_379b_160 : chunk 379 76 0 160 = 141 := by
  have h : chunk 379 76 0 160 = chunk 379 76 0 144 + chunk 379 76 144 16 :=
    chunk_split 379 76 144 16
  rw [h, prefix_379b_144, block_379b_144]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_160 : chunk 379 76 160 16 = 14 := by decide
private theorem prefix_379b_176 : chunk 379 76 0 176 = 155 := by
  have h : chunk 379 76 0 176 = chunk 379 76 0 160 + chunk 379 76 160 16 :=
    chunk_split 379 76 160 16
  rw [h, prefix_379b_160, block_379b_160]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_176 : chunk 379 76 176 16 = 18 := by decide
private theorem prefix_379b_192 : chunk 379 76 0 192 = 173 := by
  have h : chunk 379 76 0 192 = chunk 379 76 0 176 + chunk 379 76 176 16 :=
    chunk_split 379 76 176 16
  rw [h, prefix_379b_176, block_379b_176]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_192 : chunk 379 76 192 16 = 16 := by decide
private theorem prefix_379b_208 : chunk 379 76 0 208 = 189 := by
  have h : chunk 379 76 0 208 = chunk 379 76 0 192 + chunk 379 76 192 16 :=
    chunk_split 379 76 192 16
  rw [h, prefix_379b_192, block_379b_192]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_208 : chunk 379 76 208 16 = 14 := by decide
private theorem prefix_379b_224 : chunk 379 76 0 224 = 203 := by
  have h : chunk 379 76 0 224 = chunk 379 76 0 208 + chunk 379 76 208 16 :=
    chunk_split 379 76 208 16
  rw [h, prefix_379b_208, block_379b_208]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_224 : chunk 379 76 224 16 = 16 := by decide
private theorem prefix_379b_240 : chunk 379 76 0 240 = 219 := by
  have h : chunk 379 76 0 240 = chunk 379 76 0 224 + chunk 379 76 224 16 :=
    chunk_split 379 76 224 16
  rw [h, prefix_379b_224, block_379b_224]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_240 : chunk 379 76 240 16 = 22 := by decide
private theorem prefix_379b_256 : chunk 379 76 0 256 = 241 := by
  have h : chunk 379 76 0 256 = chunk 379 76 0 240 + chunk 379 76 240 16 :=
    chunk_split 379 76 240 16
  rw [h, prefix_379b_240, block_379b_240]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_256 : chunk 379 76 256 16 = 16 := by decide
private theorem prefix_379b_272 : chunk 379 76 0 272 = 257 := by
  have h : chunk 379 76 0 272 = chunk 379 76 0 256 + chunk 379 76 256 16 :=
    chunk_split 379 76 256 16
  rw [h, prefix_379b_256, block_379b_256]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_272 : chunk 379 76 272 16 = 16 := by decide
private theorem prefix_379b_288 : chunk 379 76 0 288 = 273 := by
  have h : chunk 379 76 0 288 = chunk 379 76 0 272 + chunk 379 76 272 16 :=
    chunk_split 379 76 272 16
  rw [h, prefix_379b_272, block_379b_272]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_288 : chunk 379 76 288 16 = 21 := by decide
private theorem prefix_379b_304 : chunk 379 76 0 304 = 294 := by
  have h : chunk 379 76 0 304 = chunk 379 76 0 288 + chunk 379 76 288 16 :=
    chunk_split 379 76 288 16
  rw [h, prefix_379b_288, block_379b_288]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_304 : chunk 379 76 304 16 = 14 := by decide
private theorem prefix_379b_320 : chunk 379 76 0 320 = 308 := by
  have h : chunk 379 76 0 320 = chunk 379 76 0 304 + chunk 379 76 304 16 :=
    chunk_split 379 76 304 16
  rw [h, prefix_379b_304, block_379b_304]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_320 : chunk 379 76 320 16 = 21 := by decide
private theorem prefix_379b_336 : chunk 379 76 0 336 = 329 := by
  have h : chunk 379 76 0 336 = chunk 379 76 0 320 + chunk 379 76 320 16 :=
    chunk_split 379 76 320 16
  rw [h, prefix_379b_320, block_379b_320]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_336 : chunk 379 76 336 16 = 16 := by decide
private theorem prefix_379b_352 : chunk 379 76 0 352 = 345 := by
  have h : chunk 379 76 0 352 = chunk 379 76 0 336 + chunk 379 76 336 16 :=
    chunk_split 379 76 336 16
  rw [h, prefix_379b_336, block_379b_336]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_352 : chunk 379 76 352 16 = 22 := by decide
private theorem prefix_379b_368 : chunk 379 76 0 368 = 367 := by
  have h : chunk 379 76 0 368 = chunk 379 76 0 352 + chunk 379 76 352 16 :=
    chunk_split 379 76 352 16
  rw [h, prefix_379b_352, block_379b_352]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem block_379b_368 : chunk 379 76 368 11 = 16 := by decide
private theorem prefix_379b_379 : chunk 379 76 0 379 = 383 := by
  have h : chunk 379 76 0 379 = chunk 379 76 0 368 + chunk 379 76 368 11 :=
    chunk_split 379 76 368 11
  rw [h, prefix_379b_368, block_379b_368]
theorem count379b : fastCount 379 76 = 384 := by
  rw [fastCount_chunk, prefix_379b_379]

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicModNinePointCount
