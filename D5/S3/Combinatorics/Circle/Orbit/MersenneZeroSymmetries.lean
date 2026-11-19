/- GID: D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries
   generality: I
   mirror-B: none(waiver:no-separate-boolean-mirror-claimed)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Logic.Equiv.Fin.Rotate, mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Gcd residue coordinates classify literal Mersenne zero-family symmetries. -/

import D5.S3.Combinatorics.Circle.Orbit.MersenneDifferenceZeroSubsets
import D5.S3.FiniteGroups.Partitions.UniformPartitionAutomorphisms
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-! Rotation-power orbits admit exact gcd-residue coordinates. Bezout constructs
a rotation exponent from equal residues. Both directions of literal zero-family
preservation reconstruct the orbit relation; conjugation by the residue chart
then identifies its complete symmetry group. No cyclic order inside an orbit
is observed. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.MersenneZeroSymmetries

open Equiv
open scoped BigOperators

private theorem finEquiv_apply {n : ℕ} [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => exact (Fin.cast_val_eq_self i).symm

private theorem rotation_conj {n : ℕ} [NeZero n] :
    (ZMod.finEquiv n).toEquiv.permCongrHom (finRotate n) =
      Equiv.addLeft (1 : ZMod n) := by
  ext x
  change ZMod.finEquiv n (finRotate n ((ZMod.finEquiv n).symm x)) = 1 + x
  rw [finRotate_apply, map_add, map_one, RingEquiv.apply_symm_apply, add_comm]

private theorem rotation_zpow {n : ℕ} [NeZero n] (a : ℕ) (z : ℤ) (i : Fin n) :
    ZMod.finEquiv n ((((finRotate n : Perm (Fin n)) ^ a) ^ z) i) =
      (z : ZMod n) * (a : ZMod n) + (i.val : ZMod n) := by
  let e := (ZMod.finEquiv n).toEquiv
  have hp : e.permCongrHom ((finRotate n : Perm (Fin n)) ^ a) =
      Equiv.addLeft (a : ZMod n) := by
    rw [map_pow, rotation_conj]
    simp
  calc
    _ = (e.permCongrHom (((finRotate n : Perm (Fin n)) ^ a) ^ z)) (e i) := by
      change _ = ZMod.finEquiv n
        (((((finRotate n : Perm (Fin n)) ^ a) ^ z)) (e.symm (e i)))
      rw [e.symm_apply_apply]
    _ = _ := by
      rw [map_zpow, hp]
      simp [e, finEquiv_apply, zsmul_eq_mul]

/-- Rotation-power orbits are exactly the residue classes modulo the gcd. -/
theorem sameCycle_iff_residue (n a : ℕ) (hn : 0 < n) (i j : Fin n) :
    ((finRotate n : Perm (Fin n)) ^ a).SameCycle i j ↔
      i.val % Nat.gcd n a = j.val % Nat.gcd n a := by
  let : NeZero n := ⟨ne_of_gt hn⟩
  constructor
  · rintro ⟨z, hz⟩
    have hm : z * a + (i.val : ℤ) ≡ (j.val : ℤ) [ZMOD n] := by
      apply (ZMod.intCast_eq_intCast_iff _ _ n).mp
      push_cast
      rw [← rotation_zpow a z i, hz, finEquiv_apply]
    have hgn : (Nat.gcd n a : ℤ) ∣ (n : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left n a)
    have hga : (Nat.gcd n a : ℤ) ∣ (a : ℤ) :=
      Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right n a)
    apply Nat.modEq_iff_dvd.mpr
    have hd := (hm.of_dvd hgn).dvd
    have ha := dvd_mul_of_dvd_right hga z
    convert dvd_add hd ha using 1 <;> ring
  · intro h
    obtain ⟨k, hk⟩ := Nat.modEq_iff_dvd.mp h
    have hb : (a : ℤ) * Nat.gcdA a n ≡ (Nat.gcd n a : ℤ) [ZMOD n] := by
      simpa only [Nat.gcd_comm] using Int.gcd_a_modEq a n
    have hm : (k * Nat.gcdA a n) * a + (i.val : ℤ) ≡ (j.val : ℤ) [ZMOD n] := by
      convert (hb.mul_left k).add_right (i.val : ℤ) using 1
      · ring
      · rw [mul_comm k]
        omega
    refine ⟨k * Nat.gcdA a n, ?_⟩
    apply (ZMod.finEquiv n).injective
    rw [rotation_zpow, finEquiv_apply]
    have he := (ZMod.intCast_eq_intCast_iff _ _ n).mpr hm
    push_cast at he
    simpa only [Int.cast_mul] using he

/-- Physical labels split into their gcd residue and quotient coordinates. -/
def residueChart (n a : ℕ) : Fin n ≃ Fin (Nat.gcd n a) × Fin (n / Nat.gcd n a) :=
  (finCongr (Nat.div_mul_cancel (Nat.gcd_dvd_left n a)).symm).trans
    (finProdFinEquiv.symm.trans (Equiv.prodComm _ _))

private theorem residueChart_fst (n a : ℕ) (i : Fin n) :
    ((residueChart n a i).1).val = i.val % Nat.gcd n a := rfl

/-- The chart identifies the rotation orbit relation with equality of block indices. -/
theorem sameCycle_iff_chart (n a : ℕ) (hn : 0 < n) (i j : Fin n) :
    ((finRotate n : Perm (Fin n)) ^ a).SameCycle i j ↔
      (residueChart n a i).1 = (residueChart n a j).1 := by
  rw [sameCycle_iff_residue n a hn, Fin.ext_iff]
  rw [residueChart_fst, residueChart_fst]

private theorem invariant_iff_saturated {X : Type*} [Finite X] [DecidableEq X]
    (rho : Perm X) (A : Finset X) :
    A.image rho = A ↔ ∀ x y, rho.SameCycle x y → (x ∈ A ↔ y ∈ A) := by
  constructor
  · intro hA
    have step : ∀ x, x ∈ A → rho x ∈ A := by
      intro x hx
      rw [← hA]
      exact Finset.mem_image_of_mem _ hx
    have along : ∀ x y, rho.SameCycle x y → x ∈ A → y ∈ A := by
      intro x y hxy hx
      obtain ⟨k, rfl⟩ := hxy.exists_nat_pow_eq
      clear hxy
      induction k with
      | zero => exact hx
      | succ k ih => simpa only [pow_succ', Perm.mul_apply] using step _ ih
    intro x y hxy
    exact ⟨along x y hxy, along y x hxy.symm⟩
  · intro hA
    ext y
    constructor
    · rintro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (hA x (rho x) (Perm.SameCycle.refl rho x).apply_right).mp hx
    · intro hy
      refine Finset.mem_image.mpr ⟨rho.symm y, ?_, rho.apply_symm_apply y⟩
      exact (hA (rho.symm y) y (by
        simpa only [rho.apply_symm_apply] using
          (Perm.SameCycle.refl rho (rho.symm y)).apply_right)).mpr hy

private theorem family_forward {X : Type*} [Finite X] [DecidableEq X]
    (rho q : Perm X)
    (hq : ∀ A : Finset X, (A.image q).image rho = A.image q ↔ A.image rho = A)
    (x y : X) (hxy : rho.SameCycle x y) : rho.SameCycle (q x) (q y) := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let C := Finset.univ.filter (rho.SameCycle (q x))
  have hC : C.image rho = C := by
    apply (invariant_iff_saturated rho C).mpr
    intro u v huv
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.trans huv, fun h => h.trans huv.symm⟩
  have hT : (C.image q.symm).image rho = C.image q.symm := by
    apply (hq (C.image q.symm)).mp
    simpa [Finset.image_image] using hC
  have hx : x ∈ C.image q.symm := by
    apply Finset.mem_image.mpr
    exact ⟨q x, by
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Perm.SameCycle.refl rho _, q.symm_apply_apply x⟩
  have hy := ((invariant_iff_saturated rho _).mp hT x y hxy).mp hx
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hy
  have he' : u = q y := (q.symm_apply_eq).mp he
  subst u
  exact (Finset.mem_filter.mp hu).2

private theorem family_iff_relation {X : Type*} [Finite X] [DecidableEq X]
    (rho q : Perm X) :
    (∀ A : Finset X, (A.image q).image rho = A.image q ↔ A.image rho = A) ↔
      ∀ x y, rho.SameCycle (q x) (q y) ↔ rho.SameCycle x y := by
  constructor
  · intro hq
    have hi : ∀ A : Finset X,
        (A.image q.symm).image rho = A.image q.symm ↔ A.image rho = A := by
      intro A
      simpa [Finset.image_image] using (hq (A.image q.symm)).symm
    intro x y
    exact ⟨fun h => by
      simpa only [q.symm_apply_apply] using family_forward rho q.symm hi _ _ h,
      family_forward rho q hq x y⟩
  · intro hq A
    rw [invariant_iff_saturated, invariant_iff_saturated]
    constructor
    · intro h x y hxy
      simpa only [Finset.mem_image, q.injective.eq_iff, exists_eq_right] using
        h (q x) (q y) ((hq x y).mpr hxy)
    · intro h x y hxy
      have hr : rho.SameCycle (q.symm x) (q.symm y) := by
        apply (hq _ _).mp
        simpa only [q.apply_symm_apply] using hxy
      simpa only [Finset.mem_image, ← q.eq_symm_apply, exists_eq_right] using
        h (q.symm x) (q.symm y) hr

/-- The permutations preserving and reflecting the literal integer-zero family. -/
def ZeroFamilyAut (n a : ℕ) : Subgroup (Perm (Fin n)) where
  carrier := {q | ∀ A : Finset (Fin n),
    (∑ i ∈ A.image q, SourceWidth.actualSource n (2 ^ a - 1) i) = 0 ↔
      (∑ i ∈ A, SourceWidth.actualSource n (2 ^ a - 1) i) = 0}
  one_mem' := by intro A; simp
  mul_mem' := by
    intro q r hq hr A
    simpa only [Finset.image_image, ← Perm.coe_mul] using
      (hq (A.image r)).trans (hr A)
  inv_mem' := by
    intro q hq A
    simpa [Finset.image_image] using (hq (A.image q.symm)).symm

/-- The literal zero family remembers precisely the rotation orbit partition. -/
theorem zeroFamilyAut_eq_orbitAut (n a : ℕ) (hn : 0 < n) :
    ZeroFamilyAut n a = D5.S3.FiniteGroups.SuccessorQuotient.relationAut
      (((finRotate n : Perm (Fin n)) ^ a).SameCycle) := by
  classical
  ext q
  change (∀ A : Finset (Fin n),
    (∑ i ∈ A.image q, SourceWidth.actualSource n (2 ^ a - 1) i) = 0 ↔
      (∑ i ∈ A, SourceWidth.actualSource n (2 ^ a - 1) i) = 0) ↔ _
  simp_rw [MersenneDifferenceZeroSubsets.actual_zero_iff_rotation n a hn]
  exact family_iff_relation _ q

private theorem chart_map (n a : ℕ) (hn : 0 < n) :
    (ZeroFamilyAut n a).map ((residueChart n a).permCongrHom :
      Perm (Fin n) →* Perm (Fin (Nat.gcd n a) × Fin (n / Nat.gcd n a))) =
        D5.S3.FiniteGroups.UniformPartitionAutomorphisms.Aut
          (Fin (Nat.gcd n a)) (Fin (n / Nat.gcd n a)) := by
  let e := residueChart n a
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [zeroFamilyAut_eq_orbitAut n a hn] at hp
    intro x y
    have h := hp (e.symm x) (e.symm y)
    simp_rw [sameCycle_iff_chart n a hn] at h
    change (e (p (e.symm x))).1 = (e (p (e.symm y))).1 ↔
      (e (e.symm x)).1 = (e (e.symm y)).1 at h
    change (e (p (e.symm x))).1 = (e (p (e.symm y))).1 ↔ x.1 = y.1
    simpa only [e.apply_symm_apply] using h
  · intro hq
    refine ⟨e.permCongrHom.symm q, ?_, e.permCongrHom.apply_symm_apply q⟩
    rw [zeroFamilyAut_eq_orbitAut n a hn]
    intro i j
    rw [sameCycle_iff_chart n a hn, sameCycle_iff_chart n a hn]
    change (e (e.symm (q (e i)))).1 = (e (e.symm (q (e j)))).1 ↔ _
    simpa only [e.apply_symm_apply] using hq (e i) (e j)

/-- Complete natural-index semidirect coordinates for the physical zero-family group. -/
noncomputable def zeroFamilyEquiv (n a : ℕ) (hn : 0 < n) :
    ZeroFamilyAut n a ≃*
      D5.S3.FiniteGroups.UniformPartitionAutomorphisms.Coordinates
        (Fin (Nat.gcd n a)) (Fin (n / Nat.gcd n a)) := by
  have hg : 0 < Nat.gcd n a := Nat.gcd_pos_of_pos_left a hn
  have hl : 0 < n / Nat.gcd n a :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left n a)) hg
  letI : NeZero (n / Nat.gcd n a) := ⟨ne_of_gt hl⟩
  exact (((residueChart n a).permCongrHom.subgroupMap (ZeroFamilyAut n a)).trans
    (MulEquiv.subgroupCongr (chart_map n a hn))).trans
      D5.S3.FiniteGroups.UniformPartitionAutomorphisms.automorphismEquiv

/-- Exact order of the complete literal zero-family symmetry group. -/
theorem card_zeroFamilyAut (n a : ℕ) (hn : 0 < n) :
    Nat.card (ZeroFamilyAut n a) =
      (n / Nat.gcd n a).factorial ^ Nat.gcd n a * (Nat.gcd n a).factorial := by
  have hg : 0 < Nat.gcd n a := Nat.gcd_pos_of_pos_left a hn
  have hl : 0 < n / Nat.gcd n a :=
    Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_left n a)) hg
  let : NeZero (n / Nat.gcd n a) := ⟨ne_of_gt hl⟩
  have he := (zeroFamilyEquiv n a hn).trans
    D5.S3.FiniteGroups.UniformPartitionAutomorphisms.automorphismEquiv.symm
  rw [Nat.card_congr he.toEquiv,
    D5.S3.FiniteGroups.UniformPartitionAutomorphisms.card_aut]
  simp

end D5.S3.Combinatorics.Circle.MersenneZeroSymmetries
