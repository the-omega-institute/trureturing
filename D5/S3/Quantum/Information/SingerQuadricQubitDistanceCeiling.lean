/- GID: D5/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/SingerQuadricQubitDistanceCeiling
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: For every d >= 2 the Singer-quadric qubit code Q(2,d) has cross-correlation u = 1 and minimum distance 2. -/

/-
proof_shape: result: content.
escape_witness: exponent_exclusions (for r, s ≤ d, 3 * 2 ^ s is not congruent to 2 ^ r
  modulo 2 ^ (d + 1) - 1), used on the proof path of result through correlation_units and
  cross_correlation. The private theorems whose proof path contains it are content:
  inverse_power_sum_zero, correlation_units, cross_correlation, hx_ones, pair_centralizer,
  small_centralizer_zero, distance_lower_bound. Every other private theorem is bind-only and
  is used on the proof path of result.
admission_basis: open-problem-resolution (#13470; Proved)
Direct frozen dependencies: none; only pinned Mathlib is imported.
-/

import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.Circulant

set_option linter.style.longLine false

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.SingerQuadricQubitDistanceCeiling

open scoped BigOperators
open Matrix

abbrev K (d : ℕ) := GaloisField 2 (d + 1)

def n (d : ℕ) : ℕ := 2 ^ (d + 1) - 1

instance (d : ℕ) : NeZero (n d) := ⟨by
  dsimp [n]
  have h : 1 < 2 ^ (d + 1) := Nat.one_lt_pow (by omega) (by omega)
  omega⟩

def tr {d : ℕ} (x : K d) : ZMod 2 := Algebra.trace (ZMod 2) (K d) x

def tauH {d : ℕ} (α : K d) : Fin (n d) → ZMod 2 :=
  fun i => if tr (α ^ (i : ℕ)) = 0 then 1 else 0

def tauQ {d : ℕ} (α : K d) : Fin (n d) → ZMod 2 :=
  fun i => if tr (α ^ (3 * (i : ℕ))) = 0 then 1 else 0

def Hz {d : ℕ} (α : K d) := Matrix.circulant (tauH α)

def Hx {d : ℕ} (α : K d) := Matrix.circulant (tauQ α) * Matrix.circulant (tauH α)

def centralizer {d : ℕ} (α : K d) :=
  {v : (Fin (n d) → ZMod 2) × (Fin (n d) → ZMod 2) |
    Matrix.vecMul v.1 (Matrix.transpose (Hx α)) =
      Matrix.vecMul v.2 (Matrix.transpose (Hz α))}

def stabilizers {d : ℕ} (α : K d) :=
  {v : (Fin (n d) → ZMod 2) × (Fin (n d) → ZMod 2) |
    ∃ c, v = (Matrix.vecMul c (Hz α), Matrix.vecMul c (Hx α))}

def wt {d : ℕ} (v : (Fin (n d) → ZMod 2) × (Fin (n d) → ZMod 2)) : ℕ :=
  (Finset.univ.filter fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0).card

def claim : Prop := ∀ d : ℕ, 2 ≤ d → ∀ α : K d, orderOf α = n d →
  (Matrix.circulant (tauQ α)).mulVec (tauH α) = 1 ∧
  (∀ i j, i ≠ j →
    (Pi.single i 1 + Pi.single j 1, 0) ∈ centralizer α ∧
    (Pi.single i 1 + Pi.single j 1, 0) ∉ stabilizers α) ∧
  (∀ v ∈ centralizer α, v ∉ stabilizers α → 2 ≤ wt v)

local instance (d : ℕ) : DecidableEq (K d) := Classical.decEq _

local instance (d : ℕ) : Fintype (K d) := Fintype.ofFinite (K d)

private theorem arithmetic (d : ℕ) (hd : 2 ≤ d) :
    7 ≤ n d ∧ Fintype.card (K d) = 2 ^ (d + 1) ∧
      Fintype.card (K d)ˣ = n d := by
  have hp : 8 ≤ 2 ^ (d + 1) := by
    calc 8 = 2 ^ 3 := by norm_num
         _ ≤ 2 ^ (d + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hc : Fintype.card (K d) = 2 ^ (d + 1) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 (d + 1) (by omega)
  refine ⟨by dsimp [n]; omega, hc, ?_⟩
  rw [Fintype.card_units, hc]
  rfl

private theorem power_lt_n (d t : ℕ) (hd : 2 ≤ d) (ht : t < d + 1) :
    2 ^ t < n d := by
  have h := Nat.pow_le_pow_right (n := 2) (by omega : 1 ≤ 2) (by omega : t ≤ d)
  have hp := Nat.one_lt_pow (by omega : d ≠ 0) (by omega : 1 < 2)
  dsimp [n]
  rw [pow_succ]
  omega

private theorem exponent_exclusions (d : ℕ) (hd : 2 ≤ d) (r s : ℕ)
    (hr : r < d + 1) (hs : s < d + 1) :
    ¬ n d ∣ 2 ^ r ∧ ¬ n d ∣ 3 * 2 ^ s ∧
      ¬ n d ∣ 3 * 2 ^ s + (n d - 1) * 2 ^ r := by
  have hn := (arithmetic d hd).1
  have hm : 2 ^ (d + 1) = n d + 1 := by
    dsimp [n]
    have := Nat.one_le_pow (d + 1) 2 (by omega)
    omega
  have hp : (2 : ZMod (n d)) ^ (d + 1) = 1 := by
    change ((2 : ℕ) : ZMod (n d)) ^ (d + 1) = 1
    rw [← Nat.cast_pow, hm, Nat.cast_add, ZMod.natCast_self, Nat.cast_one, zero_add]
  have hcancel : (2 : ZMod (n d)) ^ s * 2 ^ (d + 1 - s) = 1 := by
    rw [← pow_add, Nat.add_sub_of_le (by omega), hp]
  have hthree : (3 : ZMod (n d)) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by omega : 0 < 3) (by omega : 3 < n d)
      ((ZMod.natCast_eq_zero_iff 3 (n d)).mp h)
  refine ⟨Nat.not_dvd_of_pos_of_lt (by positivity) (power_lt_n d r hd hr), ?_, ?_⟩
  · intro h
    have hz := (ZMod.natCast_eq_zero_iff (3 * 2 ^ s) (n d)).mpr h
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hz
    apply hthree
    calc (3 : ZMod (n d)) = (3 * 2 ^ s) * 2 ^ (d + 1 - s) := by rw [mul_assoc, hcancel, mul_one]
         _ = 0 := by rw [hz, zero_mul]
  · intro h
    have hnm : ((n d - 1 : ℕ) : ZMod (n d)) = -1 := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
    have hz := (ZMod.natCast_eq_zero_iff _ (n d)).mpr h
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hnm,
      neg_one_mul] at hz
    have he : (3 : ZMod (n d)) * 2 ^ s = 2 ^ r := sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz)
    have he' : (3 : ZMod (n d)) = 2 ^ ((r + (d + 1 - s)) % (d + 1)) := by
      calc (3 : ZMod (n d)) = (3 * 2 ^ s) * 2 ^ (d + 1 - s) := by
             rw [mul_assoc, hcancel, mul_one]
           _ = 2 ^ (r + (d + 1 - s)) := by rw [he, pow_add]
           _ = _ := pow_eq_pow_mod _ hp
    let t := (r + (d + 1 - s)) % (d + 1)
    have ht : t < d + 1 := Nat.mod_lt _ (by omega)
    have ht' := power_lt_n d t hd ht
    have heq : 3 = 2 ^ t := by
      have hh := (ZMod.natCast_eq_natCast_iff' 3 (2 ^ t) (n d)).mp
        (by simpa only [Nat.cast_ofNat, Nat.cast_pow] using he')
      simpa only [Nat.mod_eq_of_lt (by omega : 3 < n d), Nat.mod_eq_of_lt ht'] using hh
    rcases t with _ | _ | t
    · norm_num at heq
    · norm_num at heq
    · have hh : 4 ≤ 2 ^ (t + 2) := by
        calc 4 = 2 ^ 2 := by norm_num
             _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      omega

private theorem power_sum_zero (d e : ℕ) (hd : 2 ≤ d) (he : ¬ n d ∣ e) :
    ∑ x : (K d)ˣ, (x : K d) ^ e = 0 := by
  simpa only [(arithmetic d hd).2.1, if_neg (show ¬ 2 ^ (d + 1) - 1 ∣ e from he),
    Units.val_pow_eq_pow_val] using
    FiniteField.sum_pow_units (K d) e

private theorem trace_expansion (d : ℕ) (x : K d) :
    algebraMap (ZMod 2) (K d) (tr x) = ∑ i ∈ Finset.range (d + 1), x ^ (2 ^ i) := by
  simpa only [tr, GaloisField.finrank 2 (by omega : d + 1 ≠ 0),
    Nat.card_eq_fintype_card, ZMod.card] using
    FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) (K d) x

private theorem primitive_data (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) : α ≠ 0 ∧ α ^ n d = 1 := by
  have hzero : α ≠ 0 := by
    intro hz
    rw [hz, orderOf_zero] at hα
    have := (arithmetic d hd).1
    omega
  exact ⟨hzero, hα ▸ pow_orderOf_eq_one α⟩

private theorem primitive_bijective (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (hzero : α ≠ 0) :
    Function.Bijective (fun i : Fin (n d) =>
      Units.mk0 (α ^ (i : ℕ)) (pow_ne_zero _ hzero)) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, ?_⟩
  · intro i j hij
    have hh : α ^ (i : ℕ) = α ^ (j : ℕ) := congrArg Units.val hij
    have ho : IsOfFinOrder α := orderOf_pos_iff.mp (by rw [hα]; exact NeZero.pos _)
    have hh' := ho.pow_inj_mod.mp hh
    rw [hα, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hh'
    exact Fin.ext hh'
  · rw [Fintype.card_fin, (arithmetic d hd).2.2]

private theorem primitive_pow_add (d : ℕ) (α : K d) (hp : α ^ n d = 1)
    (i j : Fin (n d)) : α ^ ((i + j : Fin (n d)) : ℕ) = α ^ (i : ℕ) * α ^ (j : ℕ) := by
  rw [Fin.val_add, ← pow_eq_pow_mod _ hp, pow_add]

private theorem primitive_pow_sub (d : ℕ) (α : K d) (hzero : α ≠ 0)
    (hp : α ^ n d = 1) (i j : Fin (n d)) :
    α ^ ((i - j : Fin (n d)) : ℕ) = α ^ (i : ℕ) * (α ^ (j : ℕ)) ^ (n d - 1) := by
  apply mul_right_cancel₀ (pow_ne_zero (j : ℕ) hzero)
  rw [← primitive_pow_add d α hp, sub_add_cancel]
  rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel ((show 1 ≤ n d from NeZero.one_le)), ← pow_mul,
    mul_comm (j : ℕ), pow_mul, hp, one_pow, mul_one]

private theorem binary_indicator (t : ZMod 2) : (if t = 0 then 1 else 0) = 1 + t := by
  fin_cases t <;> decide

private theorem inverse_power_sum_zero (d r : ℕ) (hd : 2 ≤ d) (hr : r < d + 1) :
    ∑ x : (K d)ˣ, (x : K d) ^ ((n d - 1) * 2 ^ r) = 0 := by
  apply power_sum_zero d _ hd
  have hc : Nat.Coprime (n d) (n d - 1) := by
    rw [Nat.coprime_self_sub_right (show 1 ≤ n d from NeZero.one_le)]
    exact Nat.coprime_one_right _
  rw [hc.dvd_mul_left]
  exact (exponent_exclusions d hd r r hr hr).1

private theorem n_cast_one (d : ℕ) : (n d : K d) = 1 := by
  have hp : 1 ≤ 2 ^ (d + 1) := Nat.one_le_pow _ _ (by omega)
  have hc : (2 : K d) = 0 := CharP.cast_eq_zero (K d) 2
  have ht : (1 : K d) + 1 = 0 := by simpa only [one_add_one_eq_two] using hc
  have hm : -(1 : K d) = 1 := neg_eq_iff_add_eq_zero.mpr ht
  simp [n, Nat.cast_sub hp, hc, hm]

private theorem correlation_units (d : ℕ) (hd : 2 ≤ d) (b : K d) :
    ∑ x : (K d)ˣ, (1 + algebraMap (ZMod 2) (K d) (tr ((x : K d) ^ 3))) *
      (1 + algebraMap (ZMod 2) (K d) (tr (b * (x : K d) ^ (n d - 1)))) = 1 := by
  simp_rw [trace_expansion, mul_pow, ← pow_mul]
  have hq : ∑ x : (K d)ˣ, ∑ s ∈ Finset.range (d + 1),
      (x : K d) ^ (3 * 2 ^ s) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    exact power_sum_zero d _ hd (exponent_exclusions d hd s s
      (Finset.mem_range.mp hs) (Finset.mem_range.mp hs)).2.1
  have hh : ∑ x : (K d)ˣ, ∑ r ∈ Finset.range (d + 1),
      b ^ (2 ^ r) * (x : K d) ^ ((n d - 1) * 2 ^ r) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro r hr
    rw [← Finset.mul_sum, inverse_power_sum_zero d r hd (Finset.mem_range.mp hr), mul_zero]
  have hqh : ∑ x : (K d)ˣ,
      (∑ s ∈ Finset.range (d + 1), (x : K d) ^ (3 * 2 ^ s)) *
      (∑ r ∈ Finset.range (d + 1),
        b ^ (2 ^ r) * (x : K d) ^ ((n d - 1) * 2 ^ r)) = 0 := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro r hr
    have he := (exponent_exclusions d hd r s
      (Finset.mem_range.mp hr) (Finset.mem_range.mp hs)).2.2
    have ht (x : (K d)ˣ) :
        (x : K d) ^ (3 * 2 ^ s) *
          (b ^ (2 ^ r) * (x : K d) ^ ((n d - 1) * 2 ^ r)) =
        b ^ (2 ^ r) * (x : K d) ^ (3 * 2 ^ s + (n d - 1) * 2 ^ r) := by
      rw [pow_add]
      ring
    simp_rw [ht]
    rw [← Finset.mul_sum, power_sum_zero d _ hd he, mul_zero]
  simp only [add_mul, mul_add, one_mul, mul_one, Finset.sum_add_distrib]
  rw [hq, hh, hqh]
  simp only [Finset.sum_const, Finset.card_univ, (arithmetic d hd).2.2,
    nsmul_eq_mul, mul_one, n_cast_one, add_zero]

private theorem cross_correlation (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) : (Matrix.circulant (tauQ α)).mulVec (tauH α) = 1 := by
  obtain ⟨hzero, hp⟩ := primitive_data d hd α hα
  ext k
  change (∑ j : Fin (n d), tauQ α (k - j) * tauH α j) = 1
  rw [Fintype.sum_equiv (Equiv.subLeft k) _
    (fun i => tauQ α i * tauH α (k - i)) (by intro j; simp)]
  apply FaithfulSMul.algebraMap_injective (ZMod 2) (K d)
  simp only [map_sum, map_mul, tauQ, tauH, binary_indicator, map_add, map_one]
  calc
    (∑ i : Fin (n d),
      (1 + algebraMap (ZMod 2) (K d) (tr (α ^ (3 * (i : ℕ))))) *
      (1 + algebraMap (ZMod 2) (K d) (tr (α ^ ((k - i : Fin (n d)) : ℕ))))) =
      ∑ x : (K d)ˣ, (1 + algebraMap (ZMod 2) (K d) (tr ((x : K d) ^ 3))) *
        (1 + algebraMap (ZMod 2) (K d)
          (tr (α ^ (k : ℕ) * (x : K d) ^ (n d - 1)))) := by
      apply Fintype.sum_bijective _ (primitive_bijective d hd α hα hzero)
      intro i
      simp only [Units.val_mk0, primitive_pow_sub d α hzero hp, ← pow_mul]
      rw [Nat.mul_comm 3 (i : ℕ)]
    _ = 1 := correlation_units d hd _

private theorem hx_ones (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) : Hx α = fun _ _ => 1 := by
  change Matrix.circulant (tauQ α) * Matrix.circulant (tauH α) = _
  rw [Matrix.circulant_mul, show Matrix.circulant (tauQ α) *ᵥ tauH α = 1 from
    cross_correlation d hd α hα]
  rfl

private theorem binary_cases (t : ZMod 2) : t = 0 ∨ t = 1 := by
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem trace_fibers (d : ℕ) (hd : 2 ≤ d) (b : K d) (hb : b ≠ 0)
    (a : ZMod 2) : (Finset.univ.filter fun x : K d => tr (b * x) = a).card = 2 ^ d := by
  let f : K d →ₗ[ZMod 2] ZMod 2 :=
    (Algebra.trace (ZMod 2) (K d)).comp (LinearMap.mulLeft (ZMod 2) b)
  have hn : ∃ x : K d, f x ≠ 0 := by
    by_contra! hf
    apply hb
    apply (traceForm_nondegenerate (ZMod 2) (K d)).1 b
    intro x
    simpa only [Algebra.traceForm_apply, f, LinearMap.comp_apply, LinearMap.mulLeft_apply] using hf x
  have onto : Function.Surjective f := by
    intro y
    rcases binary_cases y with rfl | rfl
    · exact ⟨0, map_zero f⟩
    · obtain ⟨x, hx⟩ := hn
      exact ⟨x, (binary_cases (f x)).resolve_left hx⟩
  have equal (c : ZMod 2) :
      (Finset.univ.filter fun x : K d => f x = c).card =
      (Finset.univ.filter fun x : K d => f x = a).card :=
    AddMonoidHom.card_fiber_eq_of_mem_range f.toAddMonoidHom (onto c) (onto a)
  have total := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (K d))) (t := (Finset.univ : Finset (ZMod 2)))
    (f := f) (by simp)
  simp only [equal, Finset.sum_const, Finset.card_univ, smul_eq_mul, ZMod.card,
    (arithmetic d hd).2.1, pow_succ] at total
  change (Finset.univ.filter fun x : K d => f x = a).card = 2 ^ d
  omega

private theorem trace_unit_fibers (d : ℕ) (hd : 2 ≤ d) (b : K d) (hb : b ≠ 0)
    (a : ZMod 2) :
    (Finset.univ.filter fun x : (K d)ˣ => tr (b * (x : K d)) = a).card =
      if a = 0 then 2 ^ d - 1 else 2 ^ d := by
  have he : (Finset.univ.filter fun x : (K d)ˣ => tr (b * (x : K d)) = a).card =
      ((Finset.univ.filter fun x : K d => tr (b * x) = a).erase 0).card := by
    apply Finset.card_bij (fun (x : (K d)ˣ) _ => (x : K d))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Units.ne_zero x, hx⟩
    · intro x _ y _ h
      exact Units.val_injective h
    · intro x hx
      obtain ⟨hzero, hx⟩ := Finset.mem_erase.mp hx
      have htrace := (Finset.mem_filter.mp hx).2
      exact ⟨Units.mk0 x hzero, by simpa using htrace, rfl⟩
  rw [he]
  split_ifs with ha
  · rw [Finset.card_erase_of_mem (by simp [ha, tr]), trace_fibers d hd b hb]
  · have hnot : (0 : K d) ∉ (Finset.univ.filter fun x : K d => tr (b * x) = a) := by
      intro hx
      have hx' := (Finset.mem_filter.mp hx).2
      apply ha
      simpa only [mul_zero, tr, map_zero] using hx'.symm
    rw [Finset.erase_eq_of_notMem hnot, trace_fibers d hd b hb]

private theorem unit_inverse (d : ℕ) (hd : 2 ≤ d) (x : (K d)ˣ) :
    (x : K d) ^ (n d - 1) = ((x⁻¹ : (K d)ˣ) : K d) := by
  have hp : (x : K d) ^ n d = 1 := by
    have h : x ^ Fintype.card (K d)ˣ = 1 := pow_card_eq_one
    rw [(arithmetic d hd).2.2] at h
    exact congrArg Units.val h
  apply mul_right_cancel₀ (Units.ne_zero x)
  rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ n d from NeZero.one_le), hp]
  simp

private theorem coordinate_fibers (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (b : K d) (hb : b ≠ 0) (a : ZMod 2) :
    (Finset.univ.filter fun j : Fin (n d) =>
      tr (b * (α ^ (j : ℕ)) ^ (n d - 1)) = a).card =
        if a = 0 then 2 ^ d - 1 else 2 ^ d := by
  have hzero := (primitive_data d hd α hα).1
  let e := fun j : Fin (n d) => (Units.mk0 (α ^ (j : ℕ)) (pow_ne_zero _ hzero))⁻¹
  have he : Function.Bijective e :=
    (Equiv.inv (K d)ˣ).bijective.comp (primitive_bijective d hd α hα hzero)
  rw [← trace_unit_fibers d hd b hb a]
  simp only [Finset.card_filter]
  apply Fintype.sum_bijective e he
  intro j
  congr 1
  rw [show ((e j : (K d)ˣ) : K d) = (α ^ (j : ℕ)) ^ (n d - 1) from
    (unit_inverse d hd (Units.mk0 (α ^ (j : ℕ)) (pow_ne_zero _ hzero))).symm]

private theorem row_formula (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (c : Fin (n d) → ZMod 2) (j : Fin (n d)) :
    Matrix.vecMul c (Hz α) j = (∑ r, c r) +
      tr ((∑ r, algebraMap (ZMod 2) (K d) (c r) * α ^ (r : ℕ)) *
        (α ^ (j : ℕ)) ^ (n d - 1)) := by
  obtain ⟨hzero, hp⟩ := primitive_data d hd α hα
  simp only [Matrix.vecMul, dotProduct, Hz, Matrix.circulant_apply, tauH, binary_indicator,
    primitive_pow_sub d α hzero hp, mul_add, mul_one, Finset.sum_add_distrib]
  congr 1
  simp only [Finset.sum_mul, tr, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem binary_ne_zero (t : ZMod 2) : t ≠ 0 ↔ t = 1 := by
  rcases binary_cases t with rfl | rfl <;> simp

private theorem row_weights (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (c : Fin (n d) → ZMod 2) :
    let w := (Finset.univ.filter fun j => Matrix.vecMul c (Hz α) j ≠ 0).card
    w = 0 ∨ w = n d ∨ w = 2 ^ d ∨ w = 2 ^ d - 1 := by
  let a := ∑ r, c r
  let b := ∑ r, algebraMap (ZMod 2) (K d) (c r) * α ^ (r : ℕ)
  have hf (j : Fin (n d)) : Matrix.vecMul c (Hz α) j =
      a + tr (b * (α ^ (j : ℕ)) ^ (n d - 1)) := row_formula d hd α hα c j
  dsimp only
  simp only [hf]
  by_cases hb : b = 0
  · simp only [hb, zero_mul, tr, map_zero, add_zero]
    by_cases ha : a = 0
    · left
      simp [ha]
    · right; left
      simp [ha]
  · rcases binary_cases a with ha | ha
    · right; right; left
      simp only [ha, zero_add, binary_ne_zero]
      simpa using coordinate_fibers d hd α hα b hb 1
    · right; right; right
      simp only [ha, ← binary_indicator]
      have he : (Finset.univ.filter fun j : Fin (n d) =>
          (if tr (b * (α ^ (j : ℕ)) ^ (n d - 1)) = 0 then (1 : ZMod 2) else 0) ≠ 0) =
          Finset.univ.filter (fun j : Fin (n d) => tr (b * (α ^ (j : ℕ)) ^ (n d - 1)) = 0) := by
        ext j
        simp
      rw [he]
      simpa using coordinate_fibers d hd α hα b hb 0

private theorem pair_weight (d : ℕ) (i j : Fin (n d)) (hij : i ≠ j) :
    (Finset.univ.filter fun k => (Pi.single i 1 + Pi.single j 1 : Fin (n d) → ZMod 2) k ≠ 0).card = 2 := by
  have he : (Finset.univ.filter fun k =>
      (Pi.single i 1 + Pi.single j 1 : Fin (n d) → ZMod 2) k ≠ 0) = {i, j} := by
    ext k
    by_cases hki : k = i
    · subst k
      simp [hij, Pi.single_apply]
    · by_cases hkj : k = j
      · subst k
        simp [Ne.symm hij, Pi.single_apply]
      · simp [hki, hkj, Pi.single_apply]
  rw [he, Finset.card_pair hij]

private theorem pair_not_stabilizer (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (i j : Fin (n d)) (hij : i ≠ j) :
    (Pi.single i 1 + Pi.single j 1, 0) ∉ stabilizers α := by
  rintro ⟨c, hc⟩
  have hc' : Pi.single i 1 + Pi.single j 1 = Matrix.vecMul c (Hz α) := congrArg Prod.fst hc
  have hw := row_weights d hd α hα c
  rw [← hc', pair_weight d i j hij] at hw
  have hp : 4 ≤ 2 ^ d := by
    calc 4 = 2 ^ 2 := by norm_num
         _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
  have hn := (arithmetic d hd).1
  rcases hw with hw | hw | hw | hw <;> omega

private theorem pair_centralizer (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (i j : Fin (n d)) :
    (Pi.single i 1 + Pi.single j 1, 0) ∈ centralizer α := by
  change Matrix.vecMul (Pi.single i 1 + Pi.single j 1) (Hx α)ᵀ =
    Matrix.vecMul 0 (Hz α)ᵀ
  rw [hx_ones d hd α hα, Matrix.add_vecMul, Matrix.single_one_vecMul,
    Matrix.single_one_vecMul, Matrix.zero_vecMul]
  ext k
  change (1 : ZMod 2) + 1 = 0
  decide

private theorem tauH_weight (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) :
    (Finset.univ.filter fun i : Fin (n d) => tauH α i ≠ 0).card = 2 ^ d - 1 := by
  have hzero := (primitive_data d hd α hα).1
  rw [← show (Finset.univ.filter fun x : (K d)ˣ => tr ((x : K d)) = 0).card =
    2 ^ d - 1 from by simpa using
      trace_unit_fibers d hd 1 one_ne_zero 0]
  simp only [Finset.card_filter]
  apply Fintype.sum_bijective _ (primitive_bijective d hd α hα hzero)
  intro i
  by_cases hi : tr (α ^ (i : ℕ)) = 0 <;> simp [tauH, hi]

private theorem column_weight (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (j : Fin (n d)) :
    (Finset.univ.filter fun r : Fin (n d) => Hz α r j ≠ 0).card = 2 ^ d - 1 := by
  rw [← tauH_weight d hd α hα]
  simp only [Finset.card_filter]
  exact Fintype.sum_equiv (Equiv.subRight j) _ _ (fun _ => rfl)

private theorem column_nonconstant (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d) (j : Fin (n d)) (a : ZMod 2) :
    ¬ ∀ r : Fin (n d), Hz α r j = a := by
  intro hc
  have hw := column_weight d hd α hα j
  simp only [hc] at hw
  have hp : 4 ≤ 2 ^ d := by
    calc 4 = 2 ^ 2 := by norm_num
         _ ≤ 2 ^ d := Nat.pow_le_pow_right (by omega) hd
  rcases binary_cases a with rfl | rfl
  · simp at hw
    omega
  · have he : n d = 2 ^ d - 1 := by simpa using hw
    dsimp [n] at he
    rw [pow_succ] at he
    omega

private theorem small_centralizer_zero (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d)
    (v : (Fin (n d) → ZMod 2) × (Fin (n d) → ZMod 2))
    (hv : v ∈ centralizer α) (hw : wt v ≤ 1) : v = 0 := by
  obtain ⟨j, hj⟩ := Finset.card_le_one_iff_subset_singleton.mp hw
  have hz (i : Fin (n d)) (hij : i ≠ j) : v.1 i = 0 ∧ v.2 i = 0 := by
    have hnot : ¬ (v.1 i ≠ 0 ∨ v.2 i ≠ 0) := by
      intro hi
      have hmem : i ∈ Finset.univ.filter (fun i => v.1 i ≠ 0 ∨ v.2 i ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      exact hij (Finset.mem_singleton.mp (hj hmem))
    tauto
  have ha : v.1 = Pi.single j (v.1 j) := by
    ext i
    by_cases hij : i = j
    · subst i; simp
    · simp [hij, (hz i hij).1]
  have hb : v.2 = Pi.single j (v.2 j) := by
    ext i
    by_cases hij : i = j
    · subst i; simp
    · simp [hij, (hz i hij).2]
  have he (r : Fin (n d)) : v.1 j = v.2 j * Hz α r j := by
    have h := congrFun hv r
    rw [ha, hb, hx_ones d hd α hα, Matrix.single_vecMul, Matrix.single_vecMul] at h
    change v.1 j * 1 = v.2 j * Hz α r j at h
    simpa only [mul_one] using h
  have hbj : v.2 j = 0 := by
    rcases binary_cases (v.2 j) with hh | hh
    · exact hh
    · exact False.elim (column_nonconstant d hd α hα j (v.1 j)
        (fun r => by simpa only [hh, one_mul] using (he r).symm))
  have haj : v.1 j = 0 := by simpa only [hbj, zero_mul] using he j
  apply Prod.ext
  · change v.1 = 0
    simpa only [haj, Pi.single_zero] using ha
  · change v.2 = 0
    simpa only [hbj, Pi.single_zero] using hb

private theorem zero_stabilizer (d : ℕ) (α : K d) :
    (0 : (Fin (n d) → ZMod 2) × (Fin (n d) → ZMod 2)) ∈ stabilizers α := by
  refine ⟨0, ?_⟩
  rw [Matrix.zero_vecMul, Matrix.zero_vecMul]
  rfl

private theorem distance_lower_bound (d : ℕ) (hd : 2 ≤ d) (α : K d)
    (hα : orderOf α = n d)
    (v : (Fin (n d) → ZMod 2) × (Fin (n d) → ZMod 2))
    (hv : v ∈ centralizer α) (hs : v ∉ stabilizers α) : 2 ≤ wt v := by
  by_contra! h
  have hz := small_centralizer_zero d hd α hα v hv (by omega)
  exact hs (hz ▸ zero_stabilizer d α)

theorem result : claim := by
  intro d hd α hα
  refine ⟨cross_correlation d hd α hα, ?_, ?_⟩
  · intro i j hij
    exact ⟨pair_centralizer d hd α hα i j, pair_not_stabilizer d hd α hα i j hij⟩
  · intro v hv hs
    exact distance_lower_bound d hd α hα v hv hs

end D5.S3.Quantum.Information.SingerQuadricQubitDistanceCeiling
