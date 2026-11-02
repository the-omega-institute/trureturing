/- GID: D5/S3/Quantum/Fermionic/BcGhostBRSTHermitian
   generality: I
   mirror-B: D5/B/S3/Quantum/Fermionic/BcGhostBRSTHermitian
   mirror-E: none(waiver:algebraic-ghost-brst-hermitian)
   anchors: []
   utility: none
   digest: Original all-mode cubic ghost BRST adjoint on the signed occupation form. -/

import D5.S3.Quantum.Fermionic.BcGhostCubic
import D5.S3.Quantum.Fermionic.BcGhostHermitian

/-! Adjoint transposition of the original normally ordered cubic ghost charge
on the signed occupation pairing, including its exact CAR boundary terms. -/

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostFock
open D5.S3.Quantum.Fermionic.BcGhostHermitian
open private cubic_eq from D5.S3.Quantum.Fermionic.BcGhostCubic

noncomputable section
namespace D5.S3.Quantum.Fermionic.BcGhostBRST

/-- The unweighted boundary correction for the literal source ordering. -/
def cubicDefect (p q : ℤ) : ℂ :=
  if -1 ≤ p + q ∧ p + q ≤ 1 then
    (if p = 0 then 1 else 0) - (if q = 0 then 1 else 0)
  else 0

/-- Transposition of the exact native cubic against the signed occupation form.
The committed `cubic_eq` supplies all original ordering branches, including
their vanishing contractions; no replacement normal order is introduced.
The middle strip retains both CAR contractions explicitly. -/
theorem Hg_cubic (p q : ℤ) (x y : Fock) :
    Hg (cubic p q x) y = -Hg x (cubic (-p) (-q) y) +
      cubicDefect p q * Hg x (c 0 y) := by
  have htranspose : Hg (cubic p q x) y =
      Hg x ((if -p-q ≤ -2 then c (-q) * c (-p) * b (p+q)
        else b (p+q) * c (-q) * c (-p)) y) := by
    by_cases hk : -p-q ≤ -2
    · simp only [cubic_eq, ite_eq_left hk, Module.End.mul_apply]
      rw [Hg_b, Hg_c, Hg_c]
      rw [show -(-p-q) = p+q by omega]
    · simp only [cubic_eq, ite_eq_right hk, Module.End.mul_apply]
      rw [Hg_c, Hg_c, Hg_b]
      rw [show -(-p-q) = p+q by omega]
  have hcc := ghost_c_car (-q) (-p)
  have hswap : c (-q) * c (-p) = -(c (-p) * c (-q)) :=
    eq_neg_of_add_eq_zero_left hcc
  have hreverse :
      (if -p-q ≤ -2 then c (-q) * c (-p) * b (p+q)
        else b (p+q) * c (-q) * c (-p)) =
      -cubic (-p) (-q) + cubicDefect p q • c 0 := by
    by_cases hhi : -p-q ≤ -2
    · have hn : ¬ - -p - -q ≤ -2 := by omega
      have hm : ¬ (-1 ≤ p+q ∧ p+q ≤ 1) := by omega
      rw [ite_eq_left hhi, cubic_eq, ite_eq_right hn]
      simp only [neg_neg, sub_neg_eq_add, cubicDefect, ite_eq_right hm,
        zero_smul, add_zero]
      rw [hswap, neg_mul]
    · by_cases hlo : - -p - -q ≤ -2
      · have hm : ¬ (-1 ≤ p+q ∧ p+q ≤ 1) := by omega
        rw [ite_eq_right hhi, cubic_eq, ite_eq_left hlo]
        simp only [neg_neg, sub_neg_eq_add, cubicDefect, ite_eq_right hm,
          zero_smul, add_zero]
        calc
          b (p+q) * c (-q) * c (-p) =
              b (p+q) * (c (-q) * c (-p)) := mul_assoc _ _ _
          _ = -(b (p+q) * c (-p) * c (-q)) := by
            rw [hswap]
            simp only [mul_neg, ← mul_assoc]
      · have hm : -1 ≤ p+q ∧ p+q ≤ 1 := by omega
        have hbp := ghost_mixed_car (p+q) (-p)
        have hbq := ghost_mixed_car (p+q) (-q)
        have hp : p+q+ -q = 0 ↔ p = 0 := by omega
        have hq : p+q+ -p = 0 ↔ q = 0 := by omega
        rw [ite_eq_right hhi, cubic_eq, ite_eq_right hlo]
        simp only [neg_neg, sub_neg_eq_add, cubicDefect, ite_eq_left hm]
        calc
          b (p+q) * c (-q) * c (-p) =
              -(c (-p) * c (-q) * b (p+q)) +
                (b (p+q) * c (-q) + c (-q) * b (p+q)) * c (-p) -
                c (-q) * (b (p+q) * c (-p) + c (-p) * b (p+q)) +
                (c (-q) * c (-p) + c (-p) * c (-q)) * b (p+q) := by
            noncomm_ring
          _ = _ := by
            rw [hbq, hbp, hcc]
            simp only [hp, hq]
            by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0 <;>
              simp [hp0, hq0, sub_eq_add_neg]
  have hneg_right (z : Fock) : Hg x (-z) = -Hg x z := by
    simpa only [neg_one_smul, neg_one_mul] using Hg_smul_right (-1) x z
  rw [htranspose, hreverse]
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.smul_apply,
    Hg_add_right, hneg_right, Hg_smul_right]

/-- All weighted defects, each with its actual coefficient. -/
def cubicTermDefect (pq : ℤ × ℤ) : ℂ :=
  (if pq = (0, 1) then -(1/2 : ℂ) else 0) +
  (if pq = (1, 0) then -(1/2 : ℂ) else 0) +
  (if pq = (0, -1) then (1/2 : ℂ) else 0) +
  (if pq = (-1, 0) then (1/2 : ℂ) else 0)

/-- The native weight reverses the cubic sign; exactly four defects remain. -/
theorem Hg_cubicTerm (p q : ℤ) (x y : Fock) :
    Hg (cubicTerm (p, q) x) y = Hg x (cubicTerm (-p, -q) y) +
      cubicTermDefect (p, q) * Hg x (c 0 y) := by
  let a : ℂ := (1/2 : ℂ) * ((p-q : ℤ) : ℂ)
  have ha : star a = a := by
    change (starRingEnd ℂ) ((1/2 : ℂ) * ((p-q : ℤ) : ℂ)) = _
    rw [map_mul, map_div₀, map_one, map_ofNat, map_intCast]
  have hn : (1/2 : ℂ) * ((-p- -q : ℤ) : ℂ) = -a := by
    dsimp [a]
    push_cast
    ring
  have hd : a * cubicDefect p q = cubicTermDefect (p, q) := by
    dsimp [a]
    by_cases hp : p = 0
    · subst p
      by_cases hq : -1 ≤ q ∧ q ≤ 1
      · have hqlo := hq.1
        have hqhi := hq.2
        interval_cases q <;> norm_num [cubicDefect, cubicTermDefect]
      · have hqm : q ≠ -1 := by omega
        have hqz : q ≠ 0 := by omega
        have hqp : q ≠ 1 := by omega
        simp [cubicDefect, cubicTermDefect, hq, hqm, hqz, hqp]
    · by_cases hq : q = 0
      · subst q
        by_cases hm : -1 ≤ p ∧ p ≤ 1
        · have hplo := hm.1
          have hphi := hm.2
          interval_cases p <;> norm_num [cubicDefect, cubicTermDefect]
        · have hpm : p ≠ -1 := by omega
          have hpp : p ≠ 1 := by omega
          simp [cubicDefect, cubicTermDefect, hm, hp, hpm, hpp]
      · simp [cubicDefect, cubicTermDefect, hp, hq]
  simp only [cubicTerm, LinearMap.smul_apply, Hg_smul_left, Hg_smul_right]
  change star a * Hg (cubic p q x) y =
    ((1/2 : ℂ) * ((-p- -q : ℤ) : ℂ)) * Hg x (cubic (-p) (-q) y) +
      cubicTermDefect (p, q) * Hg x (c 0 y)
  rw [ha, Hg_cubic, hn, mul_add, ← mul_assoc, hd]
  ring

/-- Exact symmetry of the original pointwise-finite Qg on every Fock state.
Only finite sesquilinearity is used. The capture contains both action supports,
is closed under simultaneous mode negation, and contains all four defects. -/
theorem Hg_Qg (x y : Fock) : Hg (Qg x) y = Hg x (Qg y) := by
  classical
  let sx : Finset (ℤ × ℤ) := (cubicTerm_finite x).toFinset
  let sy : Finset (ℤ × ℤ) := (cubicTerm_finite y).toFinset
  let D : Finset (ℤ × ℤ) := {(0, 1), (1, 0), (0, -1), (-1, 0)}
  let U := sx ∪ sy ∪ D
  let negPair : ℤ × ℤ → ℤ × ℤ := fun pq => (-pq.1, -pq.2)
  let S := U ∪ U.image negPair
  have hnn (pq : ℤ × ℤ) : negPair (negPair pq) = pq := by
    rcases pq with ⟨p, q⟩
    simp [negPair]
  have hclosed : ∀ pq ∈ S, negPair pq ∈ S := by
    intro pq hpq
    change pq ∈ U ∪ U.image negPair at hpq
    change negPair pq ∈ U ∪ U.image negPair
    rcases Finset.mem_union.mp hpq with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨pq, h, rfl⟩)
    · rcases Finset.mem_image.mp h with ⟨r, hr, hrp⟩
      rw [← hrp, hnn]
      exact Finset.mem_union_left _ hr
  have hxS : Function.support (fun pq => cubicTerm pq x) ⊆
      (S : Set (ℤ × ℤ)) := by
    intro pq hpq
    have hx : pq ∈ sx := by
      simpa only [sx, Set.Finite.mem_toFinset] using hpq
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ hx))
  have hyS : Function.support (fun pq => cubicTerm pq y) ⊆
      (S : Set (ℤ × ℤ)) := by
    intro pq hpq
    have hy : pq ∈ sy := by
      simpa only [sy, Set.Finite.mem_toFinset] using hpq
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hy))
  have hQx : Qg x = ∑ pq ∈ S, cubicTerm pq x := by
    change (∑ᶠ pq : ℤ × ℤ, cubicTerm pq x) = ∑ pq ∈ S, cubicTerm pq x
    exact finsum_eq_finsetSum_of_support_subset _ hxS
  have hQy : Qg y = ∑ pq ∈ S, cubicTerm pq y := by
    change (∑ᶠ pq : ℤ × ℤ, cubicTerm pq y) = ∑ pq ∈ S, cubicTerm pq y
    exact finsum_eq_finsetSum_of_support_subset _ hyS
  let left : Fock →+ ℂ :=
    { toFun := fun z => Hg z y
      map_zero' := Hg_zero_left y
      map_add' := fun z w => Hg_add_left z w y }
  let right : Fock →+ ℂ :=
    { toFun := fun z => Hg x z
      map_zero' := Hg_zero_right x
      map_add' := fun z w => Hg_add_right x z w }
  have hreindex :
      (∑ pq ∈ S, Hg x (cubicTerm (negPair pq) y)) =
      ∑ pq ∈ S, Hg x (cubicTerm pq y) := by
    apply Finset.sum_bij (fun pq _ => negPair pq)
    · intro pq hpq
      exact hclosed pq hpq
    · intro a ha b hb hab
      calc
        a = negPair (negPair a) := (hnn a).symm
        _ = negPair (negPair b) := congrArg negPair hab
        _ = b := hnn b
    · intro pq hpq
      exact ⟨negPair pq, hclosed pq hpq, hnn pq⟩
    · intro pq hpq
      rfl
  have hdefects : (∑ pq ∈ S, cubicTermDefect pq) = 0 := by
    have h01 : (0, 1) ∈ S := by simp [S, U, D]
    have h10 : (1, 0) ∈ S := by simp [S, U, D]
    have h0m : (0, -1) ∈ S := by simp [S, U, D]
    have hm0 : (-1, 0) ∈ S := by simp [S, U, D]
    norm_num [cubicTermDefect, Finset.sum_add_distrib, h01, h10, h0m, hm0]
  have hcorrection :
      (∑ pq ∈ S, cubicTermDefect pq * Hg x (c 0 y)) = 0 := by
    rw [← Finset.sum_mul, hdefects, zero_mul]
  calc
    Hg (Qg x) y = ∑ pq ∈ S, Hg (cubicTerm pq x) y := by
      rw [hQx]
      exact map_sum left _ _
    _ = ∑ pq ∈ S, (Hg x (cubicTerm (negPair pq) y) +
          cubicTermDefect pq * Hg x (c 0 y)) := by
      apply Finset.sum_congr rfl
      rintro ⟨p, q⟩ hpq
      exact Hg_cubicTerm p q x y
    _ = (∑ pq ∈ S, Hg x (cubicTerm (negPair pq) y)) +
          (∑ pq ∈ S, cubicTermDefect pq * Hg x (c 0 y)) :=
      Finset.sum_add_distrib
    _ = ∑ pq ∈ S, Hg x (cubicTerm pq y) := by
      rw [hreindex, hcorrection, add_zero]
    _ = Hg x (Qg y) := by
      rw [hQy]
      exact (map_sum right _ _).symm

end D5.S3.Quantum.Fermionic.BcGhostBRST
