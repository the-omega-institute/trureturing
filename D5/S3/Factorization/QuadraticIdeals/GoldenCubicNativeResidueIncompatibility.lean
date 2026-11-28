/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeResidueIncompatibility
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeResidueIncompatibility
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Exact native cubic clock residues forbid simultaneous prime-field residue maps. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclicOrder
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxRecDepth 8192

namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeResidueIncompatibility
open NumberField D5.S3.Factorization.QuadraticIdeals
open scoped NumberField

open D5.S0.Carrier D5.S1.Scale
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open Polynomial

/-- Time zero is native level one: L₁=4 and B₁=19. -/
def lucasState (n : ℕ) : ℤ := goldenLucas (3 ^ (n + 1))

def cycle13 : Fin 6 → ZMod 13 := ![4, 11, 12, 9, 2, 1]

def cycle73 : Fin 18 → ZMod 73 := ![4, 3, 36, 44, 52, 20, 30, 7, 72, 69, 70, 37, 29, 21, 53, 43, 66, 1]

def rootCount {m : ℕ} [NeZero m] (l : ZMod m) : ℕ := (Finset.univ.filter (fun x : ZMod m => equation l x = 0)).card

def moduloIndex (m : ℕ) (hm : 0 < m) (n : ℕ) : Fin m := ⟨n % m, Nat.mod_lt _ hm⟩

theorem cycle13_step : ∀ i : Fin 6, cycle13 (i + 1) = cycle13 i * (cycle13 i ^ 2 + 3) := by
  decide

theorem cycle73_step : ∀ i : Fin 18, cycle73 (i + 1) = cycle73 i * (cycle73 i ^ 2 + 3) := by
  decide

private theorem index_step (m : ℕ) [NeZero m] (hm : 1 < m) (n : ℕ) :
    moduloIndex m (by omega) (n + 1) = moduloIndex m (by omega) n + 1 := by
  apply Fin.ext
  change (n + 1) % m = (n % m + 1 % m) % m
  exact Nat.add_mod n 1 m

private theorem state_start : lucasState 0 = 4 := by
  norm_num [lucasState, goldenLucas, trace, phi, pow_succ]

private theorem state_step (n : ℕ) :
    lucasState (n + 1) = lucasState n * (lucasState n ^ 2 + 3) := by
  exact (golden_cubic_lucas_block (n + 1) (by omega)).2.2.2.2.2

theorem state_cycle13 (n : ℕ) :
    (lucasState n : ZMod 13) = cycle13 (moduloIndex 6 (by decide) n) := by
  induction n with
  | zero => rw [state_start]; decide
  | succ n ih =>
    rw [state_step, index_step 6 (by decide)]
    push_cast
    rw [ih, cycle13_step]

theorem state_cycle73 (n : ℕ) :
    (lucasState n : ZMod 73) = cycle73 (moduloIndex 18 (by decide) n) := by
  induction n with
  | zero => rw [state_start]; decide
  | succ n ih =>
    rw [state_step, index_step 18 (by decide)]
    push_cast
    rw [ih, cycle73_step]

/-- Exact finite root counts on the mod-13 cycle. -/
theorem rootCount_cycle13 :
    ∀ i : Fin 6, rootCount (cycle13 i) = if i.val % 3 = 0 then 3 else 0 := by
  decide

/-- Clock phase, measured from native level one, at which the mod-73
polynomial has three distinct roots. -/
def split73Phase (r : ℕ) : Prop := r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 7 ∨ r = 8

instance (r : ℕ) : Decidable (split73Phase r) := by unfold split73Phase; infer_instance

/-- Exact finite root counts on the mod-73 cycle. -/
theorem rootCount_cycle73 :
    ∀ i : Fin 18, rootCount (cycle73 i) = if split73Phase (i.val % 9) then 3 else 0 := by
  decide

theorem native_rootCount13 (n : ℕ) :
    rootCount (lucasState n : ZMod 13) = if n % 3 = 0 then 3 else 0 := by
  rw [state_cycle13, rootCount_cycle13]
  have h : (moduloIndex 6 (by decide) n).val % 3 = n % 3 := by
    change (n % 6) % 3 = n % 3
    omega
  rw [h]

theorem native_rootCount73 (n : ℕ) :
    rootCount (lucasState n : ZMod 73) = if split73Phase (n % 9) then 3 else 0 := by
  rw [state_cycle73, rootCount_cycle73]
  have h : (moduloIndex 18 (by decide) n).val % 9 = n % 9 := by
    change (n % 18) % 9 = n % 9
    omega
  rw [h]

/-- A stronger certificate than exclusion of simultaneous complete
splitting: if the mod-13 reduction has any root, the mod-73 reduction
has none. Thus no common native level has a root at both primes. -/
theorem no_simultaneous_roots (n : ℕ) :
    ¬ ((∃ x : ZMod 13, equation (lucasState n : ZMod 13) x = 0) ∧
       (∃ x : ZMod 73, equation (lucasState n : ZMod 73) x = 0)) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  have h13 : 0 < rootCount (lucasState n : ZMod 13) := Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have h73 : 0 < rootCount (lucasState n : ZMod 73) := Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
  have h3 : n % 3 = 0 := by
    by_contra h
    rw [native_rootCount13, ite_eq_right h] at h13
    omega
  have h9 : split73Phase (n % 9) := by
    by_contra h
    rw [native_rootCount73, ite_eq_right h] at h73
    omega
  unfold split73Phase at h9
  omega

theorem nonzero_blocks13_73 (n : ℕ) :
    ((lucasState n : ZMod 13) ^ 2 + 3 ≠ 0) ∧
    ((lucasState n : ZMod 73) ^ 2 + 3 ≠ 0) := by
  have h13 : ∀ i : Fin 6, cycle13 i ^ 2 + 3 ≠ 0 := by decide
  have h73 : ∀ i : Fin 18, cycle73 i ^ 2 + 3 ≠ 0 := by decide
  rw [state_cycle13, state_cycle73]
  exact ⟨h13 _, h73 _⟩

private theorem eval_cubic_equation {R : Type*} [CommRing R] (l x : R) :
    (cubic l).toPoly.eval x = equation l x := by
  simp [cubic, Cubic.toPoly, equation]
  ring

/-- Endpoint on the actual canonical polynomial reductions at every
positive native level, rather than just the two hard-coded cycles. -/
theorem no_native_simultaneous_polynomial_roots (j : ℕ) (hj : 1 ≤ j) :
    ¬ ((∃ x : ZMod 13,
          (cubic (goldenLucas (3 ^ j) : ZMod 13)).toPoly.eval x = 0) ∧
       (∃ x : ZMod 73,
          (cubic (goldenLucas (3 ^ j) : ZMod 73)).toPoly.eval x = 0)) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  simpa only [eval_cubic_equation, lucasState] using no_simultaneous_roots n

/-- No native field has a degree-one residue map at both primes. The
statement is on the actual ring of integers, not a putative order. -/
theorem no_native_pair_of_residue_maps (j : ℕ) (hj : 1 ≤ j) :
    let p := (cubic (goldenLucas (3 ^ j) : ℚ)).toPoly
    let K := p.SplittingField
    ¬ (Nonempty (𝓞 K →+* ZMod 13) ∧ Nonempty (𝓞 K →+* ZMod 73)) := by
  let l := goldenLucas (3 ^ j)
  let p := (cubic (l : ℚ)).toPoly
  let K := p.SplittingField
  change ¬ (Nonempty (𝓞 K →+* ZMod 13) ∧ Nonempty (𝓞 K →+* ZMod 73))
  intro hpair
  obtain ⟨⟨φ⟩, ⟨ψ⟩⟩ := hpair
  obtain ⟨x, S, b, hx, hSint, hspan, _, hb1, _, _⟩ := GoldenCubicNativeCyclicOrder.actual_order_discriminant j hj
  have hαint : IsIntegral ℤ x := by
    apply hSint
    change x ∈ S.toSubmodule
    rw [hspan, ← hb1]
    exact Submodule.subset_span ⟨1, rfl⟩
  let α : 𝓞 K := ⟨x, hαint⟩
  have hα : equation (l : 𝓞 K) α = 0 := by
    apply RingOfIntegers.coe_injective
    simp only [equation, map_add, map_sub, map_mul, map_pow, map_intCast, map_ofNat, map_zero]
    exact hx
  have hm {q : ℕ} (f : 𝓞 K →+* ZMod q) :
      equation (l : ZMod q) (f α) = 0 := by
    simpa only [equation, map_add, map_sub, map_mul, map_pow, map_intCast, map_ofNat, map_zero]
      using congrArg f hα
  obtain ⟨n, hn⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  apply no_simultaneous_roots n
  refine ⟨⟨φ α, ?_⟩, ⟨ψ α, ?_⟩⟩
  · simpa only [lucasState, ← hn] using hm φ
  · simpa only [lucasState, ← hn] using hm ψ


end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeResidueIncompatibility
