/- GID: D5/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees
   generality: G
   mirror-B: D5/B/S3/Combinatorics/NumericalSemigroup/IntegerFiberDegrees
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive integer fibers realize sufficiently large multiples of the degree order. -/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Eventual degrees for nonnegative integer fibers over a fixed ray. -/

open Finset

set_option autoImplicit false

namespace D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees

variable {I J : Type*}

/-- Degrees whose scaled right-hand side has a nonnegative integer solution. -/
def countedDegrees (A : (J → ℤ) →+ (I → ℤ)) (w : I → ℤ) : AddSubmonoid ℕ where
  carrier := {n | ∃ v : J → ℤ, (∀ j, 0 ≤ v j) ∧ A v = n • w}
  zero_mem' := ⟨0, fun _ => le_rfl, by simp⟩
  add_mem' := by
    rintro a b ⟨va, ha, hav⟩ ⟨vb, hb, hbv⟩
    exact ⟨va + vb, fun j => add_nonneg (ha j) (hb j), by rw [map_add, hav, hbv, add_nsmul]⟩

private theorem coprime_degrees (D : AddSubmonoid ℕ) (h b r : ℕ)
    (coprime : b.Coprime (r + 1)) (left : h * b ∈ D) (right : h * (r + 1) ∈ D)
    {t : ℕ} (ht : (b - 1) * r ≤ t) :
    h * t ∈ D := by
  obtain ⟨a, c, eq⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le b (r + 1) t
    (coprime.gcd_eq_one.symm ▸ one_dvd t)
    (by simpa [Nat.pred_eq_sub_one] using ht)
  have combination := D.add_mem (D.nsmul_mem left a) (D.nsmul_mem right c)
  have scaled : a * (h * b) + c * (h * (r + 1)) = h * t := by
    rw [← eq]
    ring
  simpa only [nsmul_eq_mul, Nat.cast_id, scaled] using combination

/-- A strictly positive integer solution lets a signed vector of primitive degree
produce two nonnegative vectors with consecutive normalized degrees. -/
theorem eventual_counts [Finite J] (A : (J → ℤ) →+ (I → ℤ)) (w : I → ℤ)
    (p : J → ℤ) (B : ℕ) (hB : 0 < B) (hp : ∀ j, 0 < p j) (hpA : A p = B • w) :
    let q : (I → ℤ) ⧸ A.range := QuotientAddGroup.mk w
    let h := addOrderOf q
    0 < h ∧ (∀ N ∈ countedDegrees A w, h ∣ N) ∧
      ∃ b : ℕ, B = h * b ∧ (∃ u : J → ℤ, A u = h • w) ∧
        ∀ u : J → ℤ, A u = h • w →
          letI : Fintype J := Fintype.ofFinite J
          let r := (1 + ∑ j, (u j).natAbs) * b
          0 < r ∧ h * r ∈ countedDegrees A w ∧ h * (r + 1) ∈ countedDegrees A w ∧
            ∀ t ≥ (b - 1) * r, h * t ∈ countedDegrees A w := by
  classical
  let _ : Fintype J := Fintype.ofFinite J
  let q : (I → ℤ) ⧸ A.range := QuotientAddGroup.mk w
  let h := addOrderOf q
  have range_iff (n : ℕ) : h ∣ n ↔ ∃ x : J → ℤ, A x = n • w := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    change n • (QuotientAddGroup.mk' A.range) w = 0 ↔ _
    rw [← (QuotientAddGroup.mk' A.range).map_nsmul]
    change QuotientAddGroup.mk (n • w) = (0 : (I → ℤ) ⧸ A.range) ↔ _
    rw [QuotientAddGroup.eq_zero_iff]
    exact AddMonoidHom.mem_range
  have dvdB := (range_iff B).mpr ⟨p, hpA⟩
  have hh : 0 < h := Nat.pos_of_dvd_of_pos dvdB hB
  obtain ⟨b, hb⟩ := dvdB
  refine ⟨hh, fun N ⟨v, _, hv⟩ => (range_iff N).mpr ⟨v, hv⟩,
    b, hb, (range_iff h).mp (dvd_refl h), ?_⟩
  intro u hu
  let k := 1 + ∑ j, (u j).natAbs
  have hk : 0 < k := by simp [k]
  have pos (j : J) : 0 ≤ (u + k • p) j := by
    have habs : (u j).natAbs ≤ k := by
      dsimp [k]
      have bound : (u j).natAbs ≤ ∑ i, (u i).natAbs :=
        Finset.single_le_sum (f := fun i => (u i).natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      exact bound.trans (Nat.le_add_left _ _)
    have hb : (-(u j) : ℤ) ≤ (k : ℤ) := calc
      _ ≤ |u j| := neg_le_abs _
      _ ≤ (k : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast habs
    have hk_le : (k : ℤ) ≤ (k : ℤ) * p j := by
      simpa using mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ p j by have := hp j; omega)
        (Int.natCast_nonneg k)
    change 0 ≤ u j + (k : ℤ) * p j
    linarith
  let r := k * b
  have hr : 0 < r := by
    have hbpos : 0 < b := by
      by_contra! hn
      have : b = 0 := by omega
      simp [this] at hb
      omega
    exact Nat.mul_pos hk hbpos
  have hleft : h * r = k * B := by rw [hb]; dsimp [r]; ring
  have left : h * r ∈ countedDegrees A w := by
    refine ⟨k • p, fun j => nsmul_nonneg (hp j).le k, ?_⟩
    rw [map_nsmul, hpA, smul_smul, hleft]
  have right : h * (r + 1) ∈ countedDegrees A w := by
    refine ⟨u + k • p, pos, ?_⟩
    rw [map_add, map_nsmul, hu, hpA, smul_smul, ← add_nsmul,
      Nat.mul_add, Nat.mul_one, hleft, add_comm]
  have base : h * b ∈ countedDegrees A w := ⟨p, fun j => (hp j).le, hb ▸ hpA⟩
  have coprime : b.Coprime (r + 1) := by
    have hcop := (Nat.coprime_add_mul_right_right b 1 k).mpr (Nat.coprime_one_right b)
    simpa only [r, Nat.add_comm] using hcop
  exact ⟨hr, left, right,
    fun t ht => coprime_degrees (countedDegrees A w) h b r coprime base right ht⟩

end D5.S3.Combinatorics.NumericalSemigroup.IntegerFiberDegrees
