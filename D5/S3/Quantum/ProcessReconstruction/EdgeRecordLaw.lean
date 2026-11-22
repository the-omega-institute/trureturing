/- GID: D5/S3/Quantum/ProcessReconstruction/EdgeRecordLaw
   generality: G
   mirror-B: D5/B/S3/Quantum/ProcessReconstruction/EdgeRecordLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent edge and site records give uniform proper output laws on an open path. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Independent edge and site records give uniform proper output laws on an open path. -/

namespace D5.S3.Quantum.EnvironmentRecords.EdgePath

open scoped BigOperators

/-- Bits use addition in the two-element field for XOR. -/
abbrev Bit := ZMod 2
abbrev Word (n : ℕ) := Fin n → Bit
abbrev Records (n : ℕ) := Word n × Word (n + 1)
abbrev Mask (n : ℕ) := Finset (Fin (n + 1))
abbrev Kept {n : ℕ} (s : Mask n) := s → Bit

noncomputable section

variable {n : ℕ}

theorem xor_self (v : Bit) : v + v = 0 := by
  simpa only [ZMod.neg_eq_self_mod_two] using neg_add_cancel v

def parity (y : Word n) : Bit := ∑ i, y i

/-- The first k site bits, starting at site zero. -/
def prefixXor (y : Word n) (k : ℕ) : Bit :=
  ∑ j ∈ Finset.range k, if h : j < n then y ⟨j, h⟩ else 0

theorem prefix_full (y : Word n) : prefixXor y n = parity y := by
  rw [prefixXor, ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by rw [dite_eq_left i.isLt]

/-- Edge k links sites k-1 and k, with zero virtual edges at both boundaries. -/
def edgeAt (e : Word n) (k : ℕ) : Bit :=
  if h : 0 < k ∧ k < n + 1 then e ⟨k - 1, by omega⟩ else 0

def shift (b : Bit) : Word (n + 1) := Pi.single 0 b

def edgeWord (b : Bit) (e : Word n) : Word (n + 1) :=
  fun i => edgeAt e i.val + edgeAt e (i.val + 1) + shift b i

theorem prefix_edgeWord (b : Bit) (e : Word n) (k : ℕ) (hk : k ≤ n + 1) :
    prefixXor (edgeWord b e - shift b) k = edgeAt e k := by
  induction k with
  | zero => simp [prefixXor, edgeAt]
  | succ k ih =>
    rw [prefixXor, Finset.sum_range_succ, dite_eq_left (by omega : k < n + 1)]
    change prefixXor (edgeWord b e - shift b) k + _ = _
    rw [ih (by omega)]
    simp [edgeWord, ← add_assoc, xor_self]

theorem parity_edgeWord (b : Bit) (e : Word n) : parity (edgeWord b e) = b := by
  have h := prefix_edgeWord b e (n + 1) le_rfl
  rw [prefix_full, show edgeAt e (n + 1) = 0 by simp [edgeAt]] at h
  simp only [parity, Pi.sub_apply, Finset.sum_sub_distrib, shift, Pi.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact sub_eq_zero.mp h

def prefixEdges (b : Bit) (y : Word (n + 1)) : Word n :=
  fun i => prefixXor (y - shift b) (i.val + 1)

theorem prefixEdges_edgeWord (b : Bit) (e : Word n) :
    prefixEdges b (edgeWord b e) = e := by
  funext i
  rw [prefixEdges, prefix_edgeWord _ _ _ (by omega)]
  simp [edgeAt, show i.val + 1 < n + 1 by omega]

private theorem edgeAt_prefixEdges (b : Bit) (y : Word (n + 1)) (hy : parity y = b)
    (k : ℕ) (hk : k ≤ n + 1) :
    edgeAt (prefixEdges b y) k = prefixXor (y - shift b) k := by
  by_cases h : 0 < k ∧ k < n + 1
  · rw [edgeAt, dite_eq_left h, prefixEdges, show k - 1 + 1 = k by omega]
  · rw [edgeAt, dite_eq_right h]
    rcases (show k = 0 ∨ k = n + 1 by omega) with rfl | rfl
    · simp [prefixXor]
    · simp [prefix_full, parity, Finset.sum_sub_distrib, shift, show (∑ i, y i) = b from hy]

theorem edgeWord_prefixEdges (b : Bit) (y : Word (n + 1)) (hy : parity y = b) :
    edgeWord b (prefixEdges b y) = y := by
  funext i
  rw [edgeWord, edgeAt_prefixEdges _ _ hy _ (by omega),
    edgeAt_prefixEdges _ _ hy _ (by omega)]
  have h : prefixXor (y - shift b) (i.val + 1) =
      prefixXor (y - shift b) i.val + (y i - shift b i) := by
    rw [prefixXor, Finset.sum_range_succ, dite_eq_left i.isLt]
    rfl
  rw [h]
  calc
    _ = (prefixXor (y - shift b) i.val + prefixXor (y - shift b) i.val) + y i := by abel
    _ = y i := by rw [xor_self, zero_add]

/-- An explicit bijection whose inverse is the prefix XOR of the unshifted word. -/
def edgeEquiv (b : Bit) : Word n ≃ {y : Word (n + 1) // parity y = b} where
  toFun e := ⟨edgeWord b e, parity_edgeWord b e⟩
  invFun y := prefixEdges b y.val
  left_inv := prefixEdges_edgeWord b
  right_inv y := Subtype.ext (edgeWord_prefixEdges b y.val y.property)

def allOn : Word (n + 1) := fun _ => 1

def localOutput (b : Bit) (x : Word (n + 1)) (w : Records n) : Word (n + 1) :=
  fun i => if x i = 1 then edgeWord b w.1 i else w.2 i

/-- Uniform independent edge and site bits, pushed through a deterministic map. -/
def push {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (y : B) : ℝ :=
  (∑ a, if f a = y then (1 : ℝ) else 0) / Fintype.card A

theorem push_nonneg {A B : Type*} [Fintype A] [DecidableEq B] (f : A → B) (y : B) :
    0 ≤ push f y := by
  unfold push
  exact div_nonneg (Finset.sum_nonneg fun a _ => by split <;> norm_num) (by positivity)

theorem sum_push {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] (f : A → B) : ∑ y, push f y = 1 := by
  unfold push
  rw [← Finset.sum_div, Finset.sum_comm]
  simp [Fintype.card_ne_zero]

theorem project_push {A B C : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    [DecidableEq C] (f : A → B) (g : B → C) (z : C) :
    ∑ y, (if g y = z then push f y else 0) = push (g ∘ f) z := by
  unfold push
  have h (y : B) :
      (if g y = z then (∑ a, if f a = y then (1 : ℝ) else 0) / Fintype.card A else 0) =
      (if g y = z then (∑ a, if f a = y then (1 : ℝ) else 0) else 0) / Fintype.card A := by
    split <;> simp_all
  simp_rw [h, ← Finset.sum_div]
  simp_rw [Finset.ite_sum_zero]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  change (∑ x, if g x = z then if f a = x then (1 : ℝ) else 0 else 0) = _
  calc
    _ = ∑ x, if f a = x then (if g x = z then (1 : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      split <;> split <;> rfl
    _ = _ := by rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]; rfl

private theorem push_affine_uniform {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Fintype A] [Fintype B] [DecidableEq B] (f : A →+ B) (hf : Function.Surjective f)
    (c y : B) : push (fun a => f a + c) y = (Fintype.card B : ℝ)⁻¹ := by
  have he (z : B) : push (fun a => f a + c) z = push (fun a => f a + c) y := by
    obtain ⟨a, ha⟩ := hf (z - y)
    unfold push
    congr 1
    rw [← Equiv.sum_comp (Equiv.addRight a) (fun v => if f v + c = z then (1 : ℝ) else 0)]
    change (∑ v, if f (v + a) + c = z then (1 : ℝ) else 0) = _
    simp only [map_add, ha]
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    apply propext
    constructor <;> intro h
    · calc
        f v + c = (f v + (z - y) + c) - (z - y) := by abel
        _ = y := by rw [h]; abel
    · calc
        f v + (z - y) + c = (f v + c) + (z - y) := by abel
        _ = z := by rw [h]; abel
  have h := sum_push (fun a => f a + c)
  simp_rw [he] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  exact eq_inv_of_mul_eq_one_right h

private def maskedLinear (x : Word (n + 1)) (s : Mask n) : Records n →+ Kept s where
  toFun w i := localOutput 0 x w i.val
  map_zero' := by
    funext i
    simp [localOutput, edgeWord, edgeAt, shift, Pi.single_apply]
  map_add' w z := by
    funext i
    have h (k : ℕ) : edgeAt (w.1 + z.1) k = edgeAt w.1 k + edgeAt z.1 k := by
      unfold edgeAt
      split <;> simp
    by_cases hi : x i.val = 1
    · simp [localOutput, hi, edgeWord, h, shift, Pi.single_apply]
      abel
    · simp [localOutput, hi]

private theorem maskedLinear_surjective (x : Word (n + 1)) (s : Mask n)
    (k : Fin (n + 1)) (hk : ¬ (k ∈ s ∧ x k = 1)) :
    Function.Surjective (maskedLinear x s) := by
  intro v
  let z : Word (n + 1) := fun i => if h : i ∈ s then v ⟨i,h⟩ else 0
  let y : Word (n + 1) := z - Pi.single k (parity z)
  have hy : parity y = 0 := by
    simp [y, parity, Finset.sum_sub_distrib, Pi.single_apply]
  refine ⟨(prefixEdges 0 y, z), ?_⟩
  funext i
  change localOutput 0 x (prefixEdges 0 y, z) i.val = _
  by_cases hi : x i.val = 1
  · have hik : i.val ≠ k := fun h => hk (h ▸ ⟨i.property, hi⟩)
    simp [localOutput, hi, edgeWord_prefixEdges _ _ hy, y, z, hik, i.property]
  · simp [localOutput, hi, z, i.property]

theorem mask_push_uniform (b : Bit) (x : Word (n + 1)) (s : Mask n) (v : Kept s)
    (h : ∃ k, ¬ (k ∈ s ∧ x k = 1)) :
    push (fun w : Records n => fun i : s => localOutput b x w i.val) v =
      (Fintype.card (Kept s) : ℝ)⁻¹ := by
  obtain ⟨k,hk⟩ := h
  let c : Kept s := fun i => if x i.val = 1 then shift b i.val else 0
  convert push_affine_uniform (maskedLinear x s) (maskedLinear_surjective x s k hk) c v using 2
  funext w i
  by_cases hi : x i.val = 1
  · simp [maskedLinear, localOutput, hi, edgeWord, shift, Pi.single_apply, c]
  · simp [maskedLinear, localOutput, hi, c]

def kernel (b : Bit) (x y : Word (n + 1)) : ℝ := push (localOutput b x) y

theorem kernel_marginal (b : Bit) (x : Word (n + 1)) (s : Mask n) (v : Kept s)
    (hs : s ≠ Finset.univ) :
    ∑ y : Word (n + 1), (if (fun i : s => y i.val) = v then kernel b x y else 0) =
      (Fintype.card (Kept s) : ℝ)⁻¹ := by
  unfold kernel
  rw [project_push]
  have hk : ∃ k, k ∉ s := by
    by_contra! h
    exact hs (Finset.eq_univ_of_forall h)
  obtain ⟨k,hk⟩ := hk
  exact mask_push_uniform b x s v ⟨k, fun h => hk h.1⟩

theorem card_word (n : ℕ) : Fintype.card (Word n) = 2 ^ n := by simp

theorem card_parity (b : Bit) :
    Fintype.card {y : Word (n + 1) // parity y = b} = 2 ^ n :=
  (Fintype.card_congr (edgeEquiv b)).symm.trans (card_word n)

theorem kernel_allOn (b : Bit) (y : Word (n + 1)) :
    kernel b allOn y = if parity y = b then (2 : ℝ) / 2 ^ (n + 1) else 0 := by
  have h (e : Word n) (r : Word (n + 1)) : localOutput b allOn (e, r) = edgeWord b e := by
    funext i
    simp [localOutput, allOn]
  simp only [kernel, push, Fintype.card_prod, Fintype.sum_prod_type, h,
    card_word, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  by_cases hp : parity y = b
  · have he (e : Word n) : edgeWord b e = y ↔ e = prefixEdges b y := by
      constructor
      · intro h
        rw [← h, prefixEdges_edgeWord]
      · rintro rfl
        exact edgeWord_prefixEdges b y hp
    simp_rw [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), hp, ite_eq_left, card_word,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_succ (2 : ℝ) n]
    field_simp
  · have he (e : Word n) : edgeWord b e ≠ y := fun h => hp (h ▸ parity_edgeWord b e)
    simp [he, hp]

private def univKept (n : ℕ) : Kept (Finset.univ : Mask n) ≃ Word (n + 1) where
  toFun v i := v ⟨i, Finset.mem_univ i⟩
  invFun y i := y i.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem kernel_inactive (b : Bit) {x : Word (n + 1)} (hx : x ≠ allOn) (y : Word (n + 1)) :
    kernel b x y = ((2 : ℝ) ^ (n + 1))⁻¹ := by
  have h : ∃ k, ¬ (k ∈ (Finset.univ : Mask n) ∧ x k = 1) := by
    by_contra! hh
    exact hx (funext fun k => (hh k).2)
  have hm := mask_push_uniform b x Finset.univ ((univKept n).symm y) h
  rw [Fintype.card_congr (univKept n), card_word, Nat.cast_pow, Nat.cast_ofNat] at hm
  convert hm using 1
  unfold kernel push
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  exact if_congr ((univKept n).symm.injective.eq_iff).symm rfl rfl

end

end D5.S3.Quantum.EnvironmentRecords.EdgePath
