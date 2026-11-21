/- GID: D5/S3/CharacterSums/AffineJacobiCorrelation
   generality: I
   mirror-B: D5/B/S3/CharacterSums/AffineJacobiCorrelation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two Jacobi rows along an affine progression have zero full-block correlation and an explicit remainder bound when their odd prime moduli are distinct and coprime to the stride. -/

import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section

namespace D5.S3.CharacterSums.AffineJacobiCorrelation

/-- Jacobi product sum for the progression indexed by the half-open interval [A,A+L). -/
def corr (b m p r A L : ℕ) : ℤ :=
  ∑ i ∈ Finset.range L, jacobiSym (p:ℤ) (b+m*(A+i)) * jacobiSym (r:ℤ) (b+m*(A+i))

private def sign (p : ℕ) : ℤ := if p % 4 = 3 then -1 else 1

private theorem swap {p n : ℕ} (hp : p.Prime) (ho : p ≠ 2) (hn : n % 4 = 3) :
    jacobiSym (p : ℤ) n = sign p * jacobiSym (n : ℤ) p := by
  rw [← jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp (hp.odd_of_ne_two ho))
    (show n % 2 = 1 by omega)]
  by_cases h3 : p % 4 = 3 <;> simp [h3,hn,sign]

private theorem fin_cast {t : ℕ} [NeZero t] (i : Fin t) : ZMod.finEquiv t i = (i.val : ZMod t) := by
  cases t with
  | zero => exact Fin.elim0 i
  | succ t => exact (Fin.cast_val_eq_self i).symm

private theorem full {b m p r : ℕ} (hb : b % 4 = 3) (hm : 4 ∣ m) (hp : p.Prime) (hr : r.Prime)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hd : p ≠ r) (hc : m.Coprime p) (hc' : m.Coprime r) (A : ℕ) :
    corr b m p r A (p*r) = 0 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact r.Prime := ⟨hr⟩
  let _ : NeZero (p*r) := ⟨(Nat.mul_pos hp.pos hr.pos).ne'⟩
  let e := ZMod.chineseRemainder ((Nat.coprime_primes hp hr).2 hd)
  let f : ZMod p × ZMod r → ℤ := fun x =>
    (sign p * quadraticChar (ZMod p) x.1) * (sign r * quadraticChar (ZMod r) x.2)
  have hw (n : ℕ) (hn : n % 4 = 3) :
      jacobiSym (p:ℤ) n * jacobiSym (r:ℤ) n = f (e n) := by
    rw [map_natCast,swap hp hp2 hn,swap hr hr2 hn, ← jacobiSym.legendreSym.to_jacobiSym,
      ← jacobiSym.legendreSym.to_jacobiSym]
    simp [f,legendreSym]
  have hz : ∑ x, f x = 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_eq_zero
    intro x _
    have hχ := quadraticChar_sum_zero (F := ZMod r) (by rwa [ZMod.ringChar_zmod_n])
    simp only [f, ← mul_assoc, ← Finset.mul_sum, hχ, mul_zero]
  let u := ((ZMod.isUnit_iff_coprime m (p*r)).2 (Nat.coprime_mul_iff_right.2 ⟨hc,hc'⟩)).unit
  have hu : (u : ZMod (p*r)) = m := IsUnit.unit_spec _
  let perm := (((((ZMod.finEquiv (p*r)).toEquiv.trans (Equiv.addLeft (A : ZMod (p*r)))).trans
    (Units.mulLeft u)).trans (Equiv.addLeft (b : ZMod (p*r)))).trans e.toEquiv)
  unfold corr
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : Fin (p*r), f (perm i) := by
      apply Finset.sum_congr rfl
      intro i _
      have h4 : (b+m*(A+i.val)) % 4 = 3 := by
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hm _), Nat.add_zero,
          Nat.mod_mod, hb]
      rw [hw _ h4]
      change f (e ((b+m*(A+i.val) : ℕ) : ZMod (p*r))) =
        f (e ((b : ZMod (p*r)) + (u : ZMod (p*r)) * ((A : ZMod (p*r)) + ZMod.finEquiv (p*r) i)))
      rw [hu, fin_cast, Nat.cast_add, Nat.cast_mul, Nat.cast_add]
    _ = 0 := (perm.sum_comp f).trans hz

private theorem short (b m p r A L : ℕ) : |corr b m p r A L| ≤ (L : ℤ) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _ ∈ Finset.range L, (1 : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      rcases jacobiSym.trichotomy (p:ℤ) (b+m*(A+i)) with h|h|h <;>
        rcases jacobiSym.trichotomy (r:ℤ) (b+m*(A+i)) with g|g|g <;> simp [h,g]
    _ = _ := by simp

/-- On each complete block the off-diagonal correlation vanishes. On an incomplete block
the absolute error is at most its remainder length. Every diagonal is bounded by its length. -/
theorem affine_jacobi_correlation (b m p r A L : ℕ) :
    (0 ≤ corr b m p p A L ∧ corr b m p p A L ≤ (L:ℤ)) ∧
    (b % 4 = 3 → 4 ∣ m → p.Prime → r.Prime → p ≠ 2 → r ≠ 2 → p ≠ r →
      m.Coprime p → m.Coprime r →
      corr b m p r A (p*r) = 0 ∧ |corr b m p r A L| ≤ (L % (p*r) : ℕ)) := by
  have hn : 0 ≤ corr b m p p A L := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  refine ⟨⟨hn,(le_abs_self _).trans (short ..)⟩, ?_⟩
  intro hb hm hp hr hp2 hr2 hd hc hc'
  let T := p*r
  have hT := full hb hm hp hr hp2 hr2 hd hc hc'
  have mult (k : ℕ) : corr b m p r A (T*k) = 0 := by
    induction k with
    | zero => simp [corr]
    | succ k ih =>
      rw [Nat.mul_succ, corr, Finset.sum_range_add]
      change corr b m p r A (T*k) + _ = 0
      rw [ih, zero_add]
      simpa [corr, Nat.add_assoc] using hT (A+T*k)
  refine ⟨hT A, ?_⟩
  change |corr b m p r A L| ≤ ((L % T : ℕ) : ℤ)
  conv_lhs => rw [← Nat.div_add_mod L T, corr, Finset.sum_range_add]
  change |corr b m p r A (T*(L/T)) + _| ≤ _
  rw [mult, zero_add]
  simpa [corr, Nat.add_assoc] using short b m p r (A+T*(L/T)) (L%T)

end D5.S3.CharacterSums.AffineJacobiCorrelation
