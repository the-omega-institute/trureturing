/- GID: D5/S3/CharacterSums/QuadraticPrimeCrossPeriod
   generality: I
   mirror-B: D5/B/S3/CharacterSums/QuadraticPrimeCrossPeriod
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Distinct odd prime Jacobi rows have zero complete correlation on the class three modulo eight, with a bounded interval remainder. -/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section

namespace D5.S3.CharacterSums.QuadraticPrimeCrossPeriod

/-- Product of the two Jacobi rows in their original orientation, restricted to one class. -/
def weight (p r n : ℕ) : ℤ :=
  if n % 8 = 3 then jacobiSym (p : ℤ) n * jacobiSym (r : ℤ) n else 0

/-- Correlation on the integers from A to A + L, excluding the right endpoint. -/
def corr (p r A L : ℕ) : ℤ := ∑ i ∈ Finset.range L, weight p r (A+i)

private def sign (p : ℕ) : ℤ := if p % 4 = 3 then -1 else 1

private theorem swap {p n : ℕ} (hp : p.Prime) (ho : p ≠ 2) (hn : n % 8 = 3) :
    jacobiSym (p : ℤ) n = sign p * jacobiSym (n : ℤ) p := by
  have h := jacobiSym.quadratic_reciprocity_if ((Nat.odd_iff.mp (hp.odd_of_ne_two ho)))
    (show n % 2 = 1 by omega)
  rw [← h]
  have h4 : n % 4 = 3 := by omega
  by_cases h3 : p % 4 = 3 <;> simp [h3,h4,sign]

private theorem fin_cast {t : ℕ} [NeZero t] (i : Fin t) : ZMod.finEquiv t i = (i.val : ZMod t) := by
  cases t with
  | zero => exact Fin.elim0 i
  | succ t => exact (Fin.cast_val_eq_self i).symm

private theorem full {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hd : p ≠ r) (A : ℕ) :
    corr p r A (8*(p*r)) = 0 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact r.Prime := ⟨hr⟩
  let T := 8*(p*r)
  have ht : 0 < T := Nat.mul_pos (by decide) (Nat.mul_pos hp.pos hr.pos)
  let _ : NeZero T := ⟨ht.ne'⟩
  have hc : Nat.Coprime 8 (p*r) := by
    simpa using ((hp.odd_of_ne_two hp2).mul (hr.odd_of_ne_two hr2)).coprime_two_left.pow_left 3
  let e : ZMod T ≃+* ZMod 8 × (ZMod p × ZMod r) :=
    (ZMod.chineseRemainder hc).trans
      ((RingEquiv.refl _).prodCongr (ZMod.chineseRemainder ((Nat.coprime_primes hp hr).2 hd)))
  let f : ZMod 8 × (ZMod p × ZMod r) → ℤ := fun x =>
    if x.1 = 3 then (sign p * quadraticChar (ZMod p) x.2.1) *
      (sign r * quadraticChar (ZMod r) x.2.2) else 0
  have hw (n : ℕ) : weight p r n = f (e n) := by
    rw [map_natCast]
    have h8 : ((n : ZMod 8) = 3) ↔ n % 8 = 3 := ZMod.natCast_eq_natCast_iff n 3 8
    by_cases h : n % 8 = 3
    · simp only [weight, h, ite_true, f, Prod.fst_natCast, Prod.snd_natCast, h8]
      rw [swap hp hp2 h, swap hr hr2 h, ← jacobiSym.legendreSym.to_jacobiSym,
        ← jacobiSym.legendreSym.to_jacobiSym]
      simp [legendreSym]
    · simp [weight, h, f, h8]
  have hz : ∑ x, f x = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro x _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hx : x = 3
    · have hχ := quadraticChar_sum_zero (F := ZMod r) (by rwa [ZMod.ringChar_zmod_n])
      simp only [f, hx, ite_true, ← mul_assoc, ← Finset.mul_sum, hχ, mul_zero]
    · simp [f,hx]
  let perm := ((ZMod.finEquiv T).toEquiv.trans (Equiv.addLeft (A : ZMod T))).trans e.toEquiv
  unfold corr
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin T, f (perm i) := by
      apply Finset.sum_congr rfl
      intro i _
      change weight p r (A+i.val) = f (e ((A : ZMod T) + ZMod.finEquiv T i))
      rw [hw, fin_cast, Nat.cast_add]
    _ = 0 := (perm.sum_comp f).trans hz

private theorem abs_weight (p r n : ℕ) : |weight p r n| ≤ 1 := by
  unfold weight
  split
  · rcases jacobiSym.trichotomy (p : ℤ) n with h|h|h <;>
      rcases jacobiSym.trichotomy (r : ℤ) n with g|g|g <;> simp [h,g]
  · simp

private theorem short (p r A L : ℕ) : |corr p r A L| ≤ (L : ℤ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simpa using (Finset.sum_le_card_nsmul (Finset.range L) (fun i => |weight p r (A+i)|) 1
    (fun i _ => abs_weight p r (A+i)))

/-- Complete periods cancel for distinct odd primes. On any interval only its remainder
contributes, while the diagonal is bounded by its interval length. -/
theorem quadratic_prime_cross_period (p r A L : ℕ) :
    (0 ≤ corr p p A L ∧ corr p p A L ≤ (L : ℤ)) ∧
    (p.Prime → r.Prime → p ≠ 2 → r ≠ 2 → p ≠ r →
      corr p r A (8*(p*r)) = 0 ∧ |corr p r A L| ≤ (L % (8*(p*r)) : ℕ)) := by
  have hn : 0 ≤ corr p p A L := by
    apply Finset.sum_nonneg
    intro i _
    unfold weight
    split
    · apply mul_self_nonneg
    · rfl
  refine ⟨⟨hn, (le_abs_self _).trans (short p p A L)⟩, ?_⟩
  intro hp hr hp2 hr2 hd
  let T := 8*(p*r)
  have hT (a : ℕ) := full hp hr hp2 hr2 hd a
  have mult (k : ℕ) : corr p r A (T*k) = 0 := by
    induction k with
    | zero => simp [corr]
    | succ k ih =>
      rw [Nat.mul_succ, corr, Finset.sum_range_add]
      change corr p r A (T*k) + _ = 0
      rw [ih, zero_add]
      simpa [corr, Nat.add_assoc] using hT (A+T*k)
  refine ⟨hT A, ?_⟩
  change |corr p r A L| ≤ ((L % T : ℕ) : ℤ)
  conv_lhs => rw [← Nat.div_add_mod L T, corr, Finset.sum_range_add]
  change |corr p r A (T*(L/T)) + _| ≤ _
  rw [mult, zero_add]
  simpa [corr,Nat.add_assoc] using short p r (A+T*(L/T)) (L%T)

end D5.S3.CharacterSums.QuadraticPrimeCrossPeriod
