/- GID: D5/S1/Dynamics/PeriodicOrbits/FiniteRealization
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/FiniteRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite cyclic actions realize exactly the nonnegative divisible Mobius tables. -/

import D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Equiv.Defs

/-! # Exact realization of finite divisor tables by cyclic permutations. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.PeriodicOrbits.FiniteRealization

open Function
open D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
open D5.S1.Descent.FiniteSelfMapConjugacy (cycleLengthMultiplicity)

/-- The positive divisors of the chosen exponent; the type is empty when it is zero. -/
abbrev Divisor (M : ℕ) := {d : ℕ // d ∈ M.divisors}

instance {M : ℕ} (d : Divisor M) : NeZero d.val :=
  ⟨(Nat.pos_of_mem_divisors d.property).ne'⟩

/-- One finite cyclic component for each copy of each prescribed divisor length. -/
abbrev CycleCarrier (M : ℕ) (c : ℕ → ℕ) := Σ d : Divisor M, Fin (c d.val) × ZMod d.val

noncomputable instance (M : ℕ) (c : ℕ → ℕ) : Fintype (CycleCarrier M c) := by
  classical
  unfold CycleCarrier
  infer_instance

/-- Advance each cyclic component by one phase, preserving its divisor and copy index. -/
noncomputable def cyclePermutation (M : ℕ) (c : ℕ → ℕ) : Equiv.Perm (CycleCarrier M c) :=
  Equiv.sigmaCongrRight fun _d => Equiv.prodCongr (Equiv.refl _) (Equiv.addRight 1)

private theorem cycle_iterate (M : ℕ) (c : ℕ → ℕ) (n : ℕ) (d : Divisor M)
    (j : Fin (c d.val)) (z : ZMod d.val) :
    (cyclePermutation M c)^[n] ⟨d, j, z⟩ = ⟨d, j, z + (n : ZMod d.val)⟩ := by
  induction n with
  | zero => simp [id]
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    change (⟨d, j, z + (n : ZMod d.val) + 1⟩ : CycleCarrier M c) =
      ⟨d, j, z + ((n + 1 : ℕ) : ZMod d.val)⟩
    simp [Nat.cast_add, add_assoc]

private theorem cycle_fixed_iff (M : ℕ) (c : ℕ → ℕ) (n : ℕ) (x : CycleCarrier M c) :
    (cyclePermutation M c)^[n] x = x ↔ x.1.val ∣ n := by
  rcases x with ⟨d, j, z⟩
  rw [cycle_iterate]
  simp [ZMod.natCast_eq_zero_iff]

private theorem cycle_fixed_count (M : ℕ) (c : ℕ → ℕ) (n : ℕ) :
    fixedCount (cyclePermutation M c) n =
      ∑ d ∈ M.divisors, if d ∣ n then d * c d else 0 := by
  classical
  unfold fixedCount
  simp_rw [cycle_fixed_iff]
  rw [Finset.card_filter]
  change (∑ x : CycleCarrier M c, if x.1.val ∣ n then 1 else 0) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  calc
    _ = ∑ d : Divisor M, if d.val ∣ n then d.val * c d.val else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d.val ∣ n <;> simp [hd, Nat.mul_comm]
    _ = _ := (Finset.sum_subtype M.divisors (fun _ => Iff.rfl)
      (fun d => if d ∣ n then d * c d else 0)).symm

/-- Exact finite realization of a table indexed by the divisors of a positive exponent.
The value at zero and the values outside that divisor set are not prescribed. -/
theorem finite_realization_iff (a : ℕ → ℕ) {M : ℕ} (hM : 0 < M) :
    (∃ σ : Equiv.Perm (Fin (a M)), σ ^ M = 1 ∧
      ∀ d ∈ M.divisors, fixedCount σ d = a d) ↔
    ∀ d ∈ M.divisors, 0 ≤ delta a d ∧ (d : ℤ) ∣ delta a d := by
  classical
  constructor
  · rintro ⟨σ, hσ, htable⟩ d hd
    have hdpos := Nat.pos_of_mem_divisors hd
    have hdelta : delta a d = delta (fixedCount σ) d := by
      unfold delta
      apply Finset.sum_congr rfl
      intro p hp
      have hpd : p.2 ∣ d := ⟨p.1, by
        simpa [Nat.mul_comm] using (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩
      rw [htable p.2 (Nat.mem_divisors.mpr
        ⟨hpd.trans (Nat.mem_divisors.mp hd).1, hM.ne'⟩)]
    rw [hdelta, delta_fixed_count σ hdpos]
    exact ⟨mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _), dvd_mul_right _ _⟩
  · intro hdelta
    let c : ℕ → ℕ := fun d => (delta a d / (d : ℤ)).toNat
    have hcoeff (d : ℕ) (hd : d ∈ M.divisors) :
        (d : ℤ) * (c d : ℤ) = delta a d := by
      dsimp [c]
      rw [Int.toNat_of_nonneg (Int.ediv_nonneg (hdelta d hd).1 (Int.natCast_nonneg _))]
      exact Int.mul_ediv_cancel' (hdelta d hd).2
    have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
      (f := fun d => (d : ℤ) * (c d : ℤ)) (g := fun d => (a d : ℤ))
      {d : ℕ | d ∣ M} (fun _ _ h₁ h₂ => h₁.trans h₂)).mpr
      (fun d hd hdM => (hcoeff d (Nat.mem_divisors.mpr ⟨hdM, hM.ne'⟩)).symm)
    have hsum (d : ℕ) (hd : d ∈ M.divisors) :
        ∑ k ∈ d.divisors, k * c k = a d := by
      exact_mod_cast hinv d
        (Nat.pos_of_mem_divisors hd) (Nat.mem_divisors.mp hd).1
    have htable (d : ℕ) (hd : d ∈ M.divisors) :
        fixedCount (cyclePermutation M c) d = a d := by
      rw [cycle_fixed_count, ← Finset.sum_filter]
      have hf : M.divisors.filter (fun k => k ∣ d) = d.divisors := by
        ext k
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hkd⟩
          exact ⟨hkd, (Nat.pos_of_mem_divisors hd).ne'⟩
        · rintro ⟨hkd, _⟩
          exact ⟨⟨hkd.trans (Nat.mem_divisors.mp hd).1, hM.ne'⟩, hkd⟩
      rw [hf]
      exact hsum d hd
    have hcard : Fintype.card (CycleCarrier M c) = a M := by
      rw [← htable M (Nat.mem_divisors.mpr ⟨dvd_rfl, hM.ne'⟩)]
      unfold fixedCount
      have hall : ∀ x : CycleCarrier M c, (cyclePermutation M c)^[M] x = x :=
        fun x => (cycle_fixed_iff M c M x).mpr (Nat.mem_divisors.mp x.1.property).1
      simp [hall]
    let e : CycleCarrier M c ≃ Fin (a M) :=
      (Fintype.equivFin _).trans (finCongr hcard)
    let σ : Equiv.Perm (Fin (a M)) := e.permCongr (cyclePermutation M c)
    have hconj : ∀ x, e (cyclePermutation M c x) = σ (e x) := by
      intro x
      simp [σ, Equiv.permCongr]
    refine ⟨σ, ?_, ?_⟩
    · apply Equiv.ext
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      change σ^[M] (e x) = e x
      rw [← (show Semiconj e (cyclePermutation M c) σ from hconj).iterate_right M x]
      exact congrArg e ((cycle_fixed_iff M c M x).mpr (Nat.mem_divisors.mp x.1.property).1)
    · intro d hd
      rw [← htable d hd]
      unfold fixedCount
      symm
      apply Finset.card_equiv e
      intro x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← (show Semiconj e (cyclePermutation M c) σ from hconj).iterate_right d x,
        e.injective.eq_iff]

#print axioms finite_realization_iff

end D5.S1.Dynamics.PeriodicOrbits.FiniteRealization
