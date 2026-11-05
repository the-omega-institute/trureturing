/- GID: D5/S1/Dynamics/PeriodicOrbits/ProductClosure
   generality: G
   mirror-B: D5/B/S1/Dynamics/PeriodicOrbits/ProductClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Direct products multiply fixed-point tables and preserve finite Dold realizability. -/

import D5.S1.Dynamics.PeriodicOrbits.FiniteRealization
import Mathlib.Data.Fintype.EquivFin

/-! # Direct products of finite cyclic actions -/

set_option autoImplicit false

namespace D5.S1.Dynamics.PeriodicOrbits.ProductClosure

open D5.S1.Dynamics.PeriodicOrbits.OrbitCounting
open D5.S1.Dynamics.PeriodicOrbits.FiniteRealization

variable {X Y : Type*}

theorem fixed_count_prodMap (f : X → X) (g : Y → Y) [Fintype X] [Fintype Y]
    (n : ℕ) :
    fixedCount (Prod.map f g) n = fixedCount f n * fixedCount g n := by
  classical
  unfold fixedCount
  rw [← Fintype.card_subtype, ← Fintype.card_subtype, ← Fintype.card_subtype]
  let e :
      {x : X × Y // (Prod.map f g)^[n] x = x} ≃
        ({x : X // f^[n] x = x} × {y : Y // g^[n] y = y}) :=
    { toFun := fun z =>
        let hz : f^[n] z.1.1 = z.1.1 ∧ g^[n] z.1.2 = z.1.2 := by
          have hz' := z.2
          have hi := congrArg (fun h : (X × Y) → X × Y => h z.1)
            (Prod.map_iterate f g n)
          have hp := hi.symm.trans hz'
          change (f^[n] z.1.1, g^[n] z.1.2) = z.1 at hp
          exact Prod.ext_iff.mp hp
        ⟨⟨z.1.1, hz.1⟩, ⟨z.1.2, hz.2⟩⟩
      invFun := fun z =>
        ⟨(z.1.1, z.2.1), by
          have hi := congrArg (fun h : (X × Y) → X × Y => h (z.1.1, z.2.1))
            (Prod.map_iterate f g n)
          have hr : Prod.map (f^[n]) (g^[n]) (z.1.1, z.2.1) =
              (z.1.1, z.2.1) := by
            change (f^[n] z.1.1, g^[n] z.2.1) = (z.1.1, z.2.1)
            exact Prod.ext_iff.mpr ⟨z.1.2, z.2.2⟩
          exact hi.trans hr⟩
      left_inv := by
        intro z
        exact Subtype.ext rfl
      right_inv := by
        intro z
        exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl) }
  exact (Fintype.card_congr e).trans (Fintype.card_prod _ _)

/-! The Dold transform is closed under the pointwise product forced by a
direct product of finite actions. -/

theorem product_dold_nonneg_dvd (f : X → X) (g : Y → Y) [Fintype X] [Fintype Y]
    {n : ℕ} (hn : 0 < n) :
    0 ≤ delta (fun k => fixedCount f k * fixedCount g k) n ∧
      (n : ℤ) ∣ delta (fun k => fixedCount f k * fixedCount g k) n := by
  have hdelta := delta_fixed_count (Prod.map f g) hn
  have hEq :
      delta (fun k => fixedCount f k * fixedCount g k) n =
        delta (fixedCount (Prod.map f g)) n := by
    unfold delta
    apply Finset.sum_congr rfl
    intro p hp
    rw [fixed_count_prodMap]
  rw [hEq, hdelta]
  exact ⟨mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _), dvd_mul_right _ _⟩

theorem finite_table_product_dold (a b : ℕ → ℕ) {M : ℕ} (hM : 0 < M)
    (ha : ∃ σ : Equiv.Perm (Fin (a M)), σ ^ M = 1 ∧
      ∀ d ∈ M.divisors, fixedCount σ d = a d)
    (hb : ∃ τ : Equiv.Perm (Fin (b M)), τ ^ M = 1 ∧
      ∀ d ∈ M.divisors, fixedCount τ d = b d)
    {d : ℕ} (hd : d ∈ M.divisors) :
    0 ≤ delta (fun k => a k * b k) d ∧
      (d : ℤ) ∣ delta (fun k => a k * b k) d := by
  obtain ⟨σ, hσ, hσtable⟩ := ha
  obtain ⟨τ, hτ, hτtable⟩ := hb
  have hdold := product_dold_nonneg_dvd σ τ (Nat.pos_of_mem_divisors hd)
  have hEq :
      delta (fun k => fixedCount σ k * fixedCount τ k) d =
        delta (fun k => a k * b k) d := by
    unfold delta
    apply Finset.sum_congr rfl
    intro p hp
    have hpd : p.2 ∣ d := by
      exact ⟨p.1, by
        simpa [Nat.mul_comm] using (Nat.mem_divisorsAntidiagonal.mp hp).1.symm⟩
    have hpm : p.2 ∈ M.divisors := Nat.mem_divisors.mpr ⟨
      hpd.trans (Nat.mem_divisors.mp hd).1, hM.ne'⟩
    change (ArithmeticFunction.moebius p.1 : ℤ) *
        ((fixedCount σ p.2 * fixedCount τ p.2 : ℕ) : ℤ) =
      (ArithmeticFunction.moebius p.1 : ℤ) * ((a p.2 * b p.2 : ℕ) : ℤ)
    rw [hσtable p.2 hpm, hτtable p.2 hpm]
  rw [← hEq]
  exact hdold

#print axioms fixed_count_prodMap
#print axioms product_dold_nonneg_dvd
#print axioms finite_table_product_dold

end D5.S1.Dynamics.PeriodicOrbits.ProductClosure
