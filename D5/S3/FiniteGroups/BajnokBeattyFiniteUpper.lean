/- GID: D5/S3/FiniteGroups/BajnokBeattyFiniteUpper
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattyFiniteUpper
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Abstract finite noncyclic abelian upper bounds via the actual relation kernel. -/

import D5.S3.FiniteGroups.LeeSquareCompression
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Pi
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Prime.Defs

/-! Abstract finite noncyclic abelian upper bounds for signed Lee covers.

The integral quotient and diagonal bases are classical Smith normal form,
reused from Mathlib. No ordered divisibility chain is assumed: the divisor is
the gcd of the two nonzero diagonal coefficients. Expanding the bottom basis
proves divisibility in the original coordinates of the covering pair.

Mathematical source: Bajnok--Beatty, arXiv v1, upper direction of Conjecture 1.6.
Matching lower constructions and the literal maximum remain separate.
No current literature novelty or publication priority is claimed.

proof_shape: finite_noncyclic_upper_dichotomy: content.
escape_witness: the noncyclic Smith quotient forces a gcd at least two, and the
bottom-basis expansion puts the actual relation kernel inside c times Z^2 in
its original coordinates. The quotient equivalence identifies its index with
Nat.card G before the existing compression estimate is applied.
proof_shape: finite_noncyclic_upper_prime: content; consumer: finite_noncyclic_upper.
proof_shape: finite_noncyclic_upper_composite: content; consumer: finite_noncyclic_upper.
proof_shape: finite_noncyclic_upper: content.
The branch results use the same live kernel-divisor construction through the
dichotomy; prime and least-prime-factor arithmetic supplies the exact endpoints.
admission_basis: escape-witness.
The private coefficient map and kernel_common_divisor have actual consumers in
finite_noncyclic_upper_dichotomy; they are not stand-alone API wrappers.
-/

set_option autoImplicit false

namespace D5.S3.FiniteGroups.BajnokBeattyFiniteUpper

open NearSquareLatticeRigidity

private def coefficientMap {G : Type*} [AddCommGroup G] (a b : G) : Plane →+ G where
  toFun z := z 0 • a + z 1 • b
  map_zero' := by simp
  map_add' z w := by
    change (z 0 + w 0) • a + (z 1 + w 1) • b =
      (z 0 • a + z 1 • b) + (w 0 • a + w 1 • b)
    rw [add_zsmul, add_zsmul]
    abel

/-- A finite noncyclic quotient of the integral plane forces a nontrivial common
coordinate divisor of its actual kernel. The Smith bases need not be ordered. -/
theorem kernel_common_divisor {G : Type*} [AddCommGroup G] [Finite G]
    (hnoncyclic : ¬ IsAddCyclic G) (f : Plane →+ G)
    (hf : Function.Surjective f) :
    ∃ c : ℕ, 2 ≤ c ∧
      ∀ z ∈ f.toIntLinearMap.ker, (c : ℤ) ∣ z 0 ∧ (c : ℤ) ∣ z 1 := by
  classical
  let K := f.toIntLinearMap.ker
  let B : Module.Basis (Fin 2) ℤ Plane := Pi.basisFun ℤ (Fin 2)
  let eG : (Plane ⧸ K) ≃+ G :=
    (f.toIntLinearMap.quotKerEquivOfSurjective hf).toAddEquiv
  letI : Finite (Plane ⧸ K) := Finite.of_equiv G eG.symm.toEquiv
  have hrank : Module.finrank ℤ K = Module.finrank ℤ Plane :=
    (Submodule.finiteQuotient_iff K).mp inferInstance
  let α : Fin 2 → ℤ := Submodule.smithNormalFormCoeffs B hrank
  let m : ℕ := (α 0).natAbs
  let n : ℕ := (α 1).natAbs
  have hm : m ≠ 0 := Int.natAbs_ne_zero.mpr
    (Submodule.smithNormalFormCoeffs_ne_zero B hrank 0)
  have hn : n ≠ 0 := Int.natAbs_ne_zero.mpr
    (Submodule.smithNormalFormCoeffs_ne_zero B hrank 1)
  letI : NeZero m := ⟨hm⟩
  letI : NeZero n := ⟨hn⟩
  let eSNF : (Plane ⧸ K) ≃+ (∀ i : Fin 2, ZMod (α i).natAbs) :=
    K.quotientEquivPiZMod B hrank
  let eTwo : (∀ i : Fin 2, ZMod (α i).natAbs) ≃+ (ZMod m × ZMod n) :=
    (LinearEquiv.piFinTwo ℤ (fun i : Fin 2 => ZMod (α i).natAbs)).toAddEquiv
  let e : G ≃+ (ZMod m × ZMod n) := eG.symm.trans (eSNF.trans eTwo)
  have hnotcoprime : ¬ m.Coprime n := by
    intro hcoprime
    have hcyc : IsAddCyclic (ZMod m × ZMod n) :=
      AddGroup.isAddCyclic_prod_iff.mpr ⟨inferInstance, inferInstance,
        by simpa only [Nat.card_zmod] using hcoprime⟩
    exact hnoncyclic (e.isAddCyclic.mpr hcyc)
  let c : ℕ := Nat.gcd m n
  have hcpos : 0 < c := Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hm)
  have hcne : c ≠ 1 := by
    intro hc
    exact hnotcoprime (Nat.coprime_iff_gcd_eq_one.mpr hc)
  have hc : 2 ≤ c := by omega
  have hcoeff : ∀ j : Fin 2, (c : ℤ) ∣ α j := by
    intro j
    apply Int.natCast_dvd.mpr
    fin_cases j
    · exact Nat.gcd_dvd_left m n
    · exact Nat.gcd_dvd_right m n
  let D : Module.Basis (Fin 2) ℤ K := Submodule.smithNormalFormBotBasis B hrank
  let T : Module.Basis (Fin 2) ℤ Plane := Submodule.smithNormalFormTopBasis B hrank
  have hD (j : Fin 2) : (D j : Plane) = α j • T j :=
    Submodule.smithNormalFormBotBasis_def B hrank j
  refine ⟨c, hc, ?_⟩
  intro z hz
  have hcoord (i : Fin 2) : (c : ℤ) ∣ z i := by
    let w : K := ⟨z, hz⟩
    have hexp : D.repr w 0 * (D 0 : Plane) i +
        D.repr w 1 * (D 1 : Plane) i = z i := by
      have hw := D.sum_repr w
      rw [Fin.sum_univ_two] at hw
      exact congrArg (fun v : K => (v : Plane) i) hw
    rw [hD 0, hD 1] at hexp
    simp only [Pi.smul_apply, smul_eq_mul] at hexp
    rw [← hexp]
    exact (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (hcoeff 0) (T 0 i))
      (D.repr w 0)).add
      (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (hcoeff 1) (T 1 i))
        (D.repr w 1))
  exact ⟨hcoord 0, hcoord 1⟩

/-- The actual order of every finite noncyclic abelian Lee-covered group obeys
the lattice dichotomy, for the actual common divisor of the given pair's kernel. -/
theorem finite_noncyclic_upper_dichotomy {G : Type*} [AddCommGroup G] [Finite G]
    {s : ℕ} (hs : 3 ≤ s) (hnoncyclic : ¬ IsAddCyclic G) (a b : G)
    (hcover : ∀ g : G, ∃ x y : ℤ,
      |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) :
    ∃ c : ℕ, 2 ≤ c ∧
      ((Nat.card G : ℤ) ≤ 2 * (s : ℤ)^2 ∨
        (Odd (c : ℤ) ∧ (c : ℤ) ∣ 2 * (s : ℤ) + 1 ∧
          2 * (Nat.card G : ℤ) ≤ (2 * (s : ℤ) + 1)^2 - (c : ℤ)^2)) := by
  let f := coefficientMap a b
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨x, y, _, he⟩ := hcover g
    exact ⟨![x, y], he⟩
  let K := f.toIntLinearMap.ker
  obtain ⟨c, hc, hdiv⟩ := kernel_common_divisor hnoncyclic f hf
  have hLee : ∀ z : Plane, ∃ r : Plane,
      |r 0| + |r 1| ≤ (s : ℤ) ∧ z - r ∈ K := by
    intro z
    obtain ⟨x, y, hxy, he⟩ := hcover (f z)
    refine ⟨![x, y], hxy, ?_⟩
    change f (z - ![x, y]) = 0
    rw [map_sub]
    change f z - (x • a + y • b) = 0
    rw [he, sub_self]
  have hindex : K.toAddSubgroup.index = Nat.card G := by
    change Nat.card (Plane ⧸ K) = Nat.card G
    exact Nat.card_congr (f.toIntLinearMap.quotKerEquivOfSurjective hf).toEquiv
  refine ⟨c, hc, ?_⟩
  have h := LeeSquareCompression.lattice_upper_bound K (c := (c : ℤ))
    (s := (s : ℤ)) (by exact_mod_cast hc) (by exact_mod_cast hs) hdiv hLee
  simpa only [hindex] using h

/-- Prime case of the Bajnok--Beatty abstract finite-group upper bound. -/
theorem finite_noncyclic_upper_prime {G : Type*} [AddCommGroup G] [Finite G]
    {s : ℕ} (hs : 3 ≤ s) (hnoncyclic : ¬ IsAddCyclic G) (a b : G)
    (hcover : ∀ g : G, ∃ x y : ℤ,
      |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g)
    (hprime : Nat.Prime (2 * s + 1)) : Nat.card G ≤ 2 * s^2 := by
  obtain ⟨c, hc, hlow | ⟨_, hdvd, hhigh⟩⟩ :=
    finite_noncyclic_upper_dichotomy hs hnoncyclic a b hcover
  · exact_mod_cast hlow
  · have hdvdN : c ∣ 2 * s + 1 := by exact_mod_cast hdvd
    have heq : c = 2 * s + 1 := by
      rcases hprime.eq_one_or_self_of_dvd c hdvdN with h | h
      · omega
      · exact h
    have heqZ : (c : ℤ) = 2 * (s : ℤ) + 1 := by exact_mod_cast heq
    rw [heqZ, sub_self] at hhigh
    have hpos : 0 < (Nat.card G : ℤ) := by exact_mod_cast (Nat.card_pos (α := G))
    omega

/-- Composite case, with exactly the least-prime-factor square correction.
All arithmetic in this statement is in `ℕ`, including the displayed subtraction. -/
theorem finite_noncyclic_upper_composite {G : Type*} [AddCommGroup G] [Finite G]
    {s : ℕ} (hs : 3 ≤ s) (hnoncyclic : ¬ IsAddCyclic G) (a b : G)
    (hcover : ∀ g : G, ∃ x y : ℤ,
      |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g)
    (hnotprime : ¬ Nat.Prime (2 * s + 1)) :
    2 * Nat.card G ≤ (2 * s + 1)^2 - (Nat.minFac (2 * s + 1))^2 := by
  let p := Nat.minFac (2 * s + 1)
  have hpsq : p^2 ≤ 2 * s + 1 :=
    Nat.minFac_sq_le_self (by omega) hnotprime
  have hbase : 2 * s + 1 ≤ (2 * s + 1)^2 := by nlinarith
  have hsub : p^2 ≤ (2 * s + 1)^2 := hpsq.trans hbase
  obtain ⟨c, hc, hlow | ⟨_, hdvd, hhigh⟩⟩ :=
    finite_noncyclic_upper_dichotomy hs hnoncyclic a b hcover
  · have hlowN : Nat.card G ≤ 2 * s^2 := by exact_mod_cast hlow
    have hsum : 2 * Nat.card G + p^2 ≤ (2 * s + 1)^2 := by nlinarith
    change 2 * Nat.card G ≤ (2 * s + 1)^2 - p^2
    omega
  · have hdvdN : c ∣ 2 * s + 1 := by exact_mod_cast hdvd
    have hpc : p ≤ c := Nat.minFac_le_of_dvd hc hdvdN
    have hpcZ : (p : ℤ) ≤ (c : ℤ) := by exact_mod_cast hpc
    have hsumZ : 2 * (Nat.card G : ℤ) + (p : ℤ)^2 ≤
        (2 * (s : ℤ) + 1)^2 := by
      have hp0 : (0 : ℤ) ≤ p := by positivity
      have hsq : (p : ℤ)^2 ≤ (c : ℤ)^2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hpcZ)
          (show (0 : ℤ) ≤ (c : ℤ) + (p : ℤ) by omega)]
      nlinarith only [hhigh, hsq]
    have hsum : 2 * Nat.card G + p^2 ≤ (2 * s + 1)^2 := by exact_mod_cast hsumZ
    change 2 * Nat.card G ≤ (2 * s + 1)^2 - p^2
    omega

/-- Abstract upper bound for every finite noncyclic abelian group with a signed
two-generator Lee cover of radius `s ≥ 3`; no pair-distinctness assumption. -/
theorem finite_noncyclic_upper {G : Type*} [AddCommGroup G] [Finite G]
    {s : ℕ} (hs : 3 ≤ s) (hnoncyclic : ¬ IsAddCyclic G) (a b : G)
    (hcover : ∀ g : G, ∃ x y : ℤ,
      |x| + |y| ≤ (s : ℤ) ∧ x • a + y • b = g) :
    if Nat.Prime (2 * s + 1) then Nat.card G ≤ 2 * s^2
    else 2 * Nat.card G ≤ (2 * s + 1)^2 - (Nat.minFac (2 * s + 1))^2 := by
  classical
  by_cases hp : Nat.Prime (2 * s + 1)
  · rw [if_pos hp]
    exact finite_noncyclic_upper_prime hs hnoncyclic a b hcover hp
  · rw [if_neg hp]
    exact finite_noncyclic_upper_composite hs hnoncyclic a b hcover hp

end D5.S3.FiniteGroups.BajnokBeattyFiniteUpper
