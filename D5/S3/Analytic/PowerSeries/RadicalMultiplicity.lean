/- GID: D5/S3/Analytic/PowerSeries/RadicalMultiplicity
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Local multiplicity of finite polynomial radical sums. -/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0. Full license and NOTICE chain:
Library/Analysis/leanpool-differential-wronskian.md.
Required closure transplanted from LeanPool/lean-pool,
revision edbe5bd56f476cc2965564676b66199f281ab714,
LeanPool/MarkoffModP/BGS/Algebra/DifferentialWronskian.lean.
Retirement: replace this closure by direct imports when this repository's pinned
Mathlib contains an equivalent differential-field Wronskian criterion.
-/

namespace BGS.Algebra

noncomputable section

open scoped Matrix

variable {C L : Type*} [Field C] [Field L] [Algebra C L]

/-- The ordinary Wronskian matrix of a finite family with respect to a derivation. -/
private def derivationWronskian (D : Derivation C L L) {n : ℕ} (f : Fin n → L) :
    Matrix (Fin n) (Fin n) L :=
  fun i j ↦ (D.toLinearMap ^ (i : ℕ)) (f j)

private lemma derivation_iterate_succ (D : Derivation C L L) (n : ℕ) (x : L) :
    D ((D.toLinearMap ^ n) x) = (D.toLinearMap ^ (n + 1)) x := by
  rw [pow_succ', Module.End.mul_apply]
  rfl

/-- If every element killed by `D` comes from `C`, then a family linearly independent over
`C` has nonzero ordinary Wronskian. -/
private theorem derivationWronskian_det_ne_zero_of_linearIndependent
    (D : Derivation C L L)
    (constants : ∀ x : L, D x = 0 → ∃ c : C, algebraMap C L c = x) :
    ∀ (n : ℕ) (f : Fin n → L), LinearIndependent C f →
      (derivationWronskian D f).det ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro f hf
      simp
  | succ n ih =>
      intro f hf hdet
      let W : Matrix (Fin (n + 1)) (Fin (n + 1)) L := derivationWronskian D f
      have hWdet : W.det = 0 := by simpa [W] using hdet
      obtain ⟨a, ha_ne, haW⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hWdet
      obtain ⟨k, hak⟩ : ∃ k, a k ≠ 0 := by
        simpa [Function.ne_iff] using ha_ne
      let c : Fin (n + 1) → L := fun j ↦ (a k)⁻¹ * a j
      have hck : c k = 1 := by simp [c, hak]
      have hcW : W *ᵥ c = 0 := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
        calc
          ∑ j, W i j * c j = (a k)⁻¹ * ∑ j, W i j * a j := by
            simp only [c]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = 0 := by
            rw [show ∑ j, W i j * a j = 0 by
              simpa [Matrix.mulVec, dotProduct] using congr_fun haW i, mul_zero]
      have hc_relation (i : Fin (n + 1)) :
          ∑ j, (D.toLinearMap ^ (i : ℕ)) (f j) * c j = 0 := by
        simpa [W, derivationWronskian, Matrix.mulVec, dotProduct] using congr_fun hcW i
      have hDck : D (c k) = 0 := by simp [hck]
      let g : Fin n → L := fun j ↦ f (k.succAbove j)
      have hg : LinearIndependent C g :=
        hf.comp k.succAbove k.succAbove_right_injective
      have hWgdet : (derivationWronskian D g).det ≠ 0 := ih g hg
      let b : Fin n → L := fun j ↦ D (c (k.succAbove j))
      have hfull (i : Fin n) :
          ∑ j : Fin (n + 1),
              (D.toLinearMap ^ (i : ℕ)) (f j) * D (c j) = 0 := by
        have hderiv := congrArg D (hc_relation i.castSucc)
        have hnext := hc_relation i.succ
        simp only [map_zero, map_sum, D.leibniz, smul_eq_mul,
          derivation_iterate_succ] at hderiv
        have hindex (j : Fin (n + 1)) :
            (D.toLinearMap ^ (((i.castSucc : Fin (n + 1)) : ℕ) + 1)) (f j) =
              (D.toLinearMap ^ ((i.succ : Fin (n + 1)) : ℕ)) (f j) := by
          simp
        simp_rw [hindex] at hderiv
        have hnext' :
            ∑ j : Fin (n + 1),
                c j * (D.toLinearMap ^ ((i.succ : Fin (n + 1)) : ℕ)) (f j) = 0 := by
          simpa [mul_comm] using hnext
        rw [Finset.sum_add_distrib] at hderiv
        have hderiv' :
            (∑ j : Fin (n + 1), (D.toLinearMap ^ (i : ℕ)) (f j) * D (c j)) +
              ∑ j : Fin (n + 1),
                c j * (D.toLinearMap ^ ((i.succ : Fin (n + 1)) : ℕ)) (f j) = 0 := by
          simpa using hderiv
        linear_combination hderiv' - hnext'
      have hWgb : derivationWronskian D g *ᵥ b = 0 := by
        funext i
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, b, g,
          derivationWronskian]
        have hi := hfull i
        rw [Fin.sum_univ_succAbove (fun j : Fin (n + 1) ↦
          (D.toLinearMap ^ (i : ℕ)) (f j) * D (c j)) k] at hi
        simpa [hDck] using hi
      have hbzero : b = 0 := Matrix.eq_zero_of_mulVec_eq_zero hWgdet hWgb
      have hDc (j : Fin (n + 1)) : D (c j) = 0 := by
        by_cases hj : j = k
        · simpa [hj] using hDck
        · obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hj
          have := congr_fun hbzero r
          simpa [b, hr] using this
      choose coeff hcoeff using fun j ↦ constants (c j) (hDc j)
      have hcoeff_relation : ∑ j, coeff j • f j = 0 := by
        have hzero := hc_relation 0
        simpa [hcoeff, Algebra.smul_def, mul_comm] using hzero
      have hcoeff_zero : ∀ j, coeff j = 0 :=
        (Fintype.linearIndependent_iff.mp hf) coeff hcoeff_relation
      have : (1 : L) = 0 := by
        rw [← hck, ← hcoeff k, hcoeff_zero k, map_zero]
      exact one_ne_zero this

end

end BGS.Algebra

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Apache-2.0. Full license: Library/Analysis/tauceti-laurent-derivation.md.
Required closure from TauCetiProject/TauCeti at
93af5b549b7d9ed44291d6ceb093a8013dda00f8,
TauCeti/RingTheory/LaurentSeries/{Basic,Derivative}.lean.
The power-series compatibility proof uses the pinned derivative API directly.
Retirement: replace this closure by direct imports when this repository's pinned
Mathlib supplies Laurent derivative Leibniz and its bundled derivation.
-/

open scoped LaurentSeries PowerSeries

namespace CdsoRadical

open HahnSeries

private theorem coe_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) :
    ((PowerSeries.derivative f : R⟦X⟧) : R⸨X⸩) =
      LaurentSeries.derivative R (f : R⸨X⸩) := by
  ext i
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  rcases i with n | n
  · simp [PowerSeries.coeff_derivative, Ring.choose_one_right,
      show ¬(n : ℤ) < 0 by omega, show ¬(n : ℤ) + 1 < 0 by omega,
      show ((n : ℤ) + 1).natAbs = n + 1 by omega, nsmul_eq_mul]
  · rcases n with _ | n
    · simp [Ring.choose_one_right]
    · simp [show Int.negSucc (n + 1) + 1 < 0 by omega]

private theorem derivative_single_mul {R : Type*} [CommRing R]
    (m : ℤ) (c : R) (f : R⸨X⸩) :
    LaurentSeries.derivative R (single m c * f) =
      single (m - 1) (m * c) * f + single m c * LaurentSeries.derivative R f := by
  ext n
  simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    coeff_add, coeff_single_mul, Ring.choose_one_right]
  have h₁ : n - (m - 1) = n + 1 - m := by omega
  have h₂ : n - m + (1 : ℕ) = n + 1 - m := by omega
  simp only [h₁, h₂, ← zsmul_eq_mul, smul_mul_assoc, mul_smul_comm, ← add_zsmul]
  congr 1
  omega

private theorem derivative_single_mul_coe {R : Type*} [CommRing R]
    (m : ℤ) (c : R) (φ : R⟦X⟧) :
    LaurentSeries.derivative R (single m c * (φ : R⸨X⸩)) =
      single (m - 1) (m * c) * φ +
        single m c * ((PowerSeries.derivative φ : R⟦X⟧) : R⸨X⸩) := by
  rw [derivative_single_mul, ← coe_derivative]

private theorem derivative_mul {R : Type*} [CommRing R] (f g : R⸨X⸩) :
    LaurentSeries.derivative R (f * g) =
      LaurentSeries.derivative R f * g + f * LaurentSeries.derivative R g := by
  rw [← LaurentSeries.single_order_mul_powerSeriesPart f,
    ← LaurentSeries.single_order_mul_powerSeriesPart g]
  set a := f.order
  set b := g.order
  set φ := f.powerSeriesPart
  set ψ := g.powerSeriesPart
  have hab : (single (a + b) (1 : R) : R⸨X⸩) = single a 1 * single b 1 := by
    rw [single_mul_single, one_mul]
  have hfg : (single a (1 : R) * (φ : R⸨X⸩)) * (single b 1 * (ψ : R⸨X⸩)) =
      single (a + b) 1 * ((φ * ψ : R⟦X⟧) : R⸨X⸩) := by
    rw [PowerSeries.coe_mul, hab]
    ring
  have hd : (single (a + b - 1) (((a + b : ℤ) : R) * 1) : R⸨X⸩) =
      single (a - 1) ((a : R) * 1) * single b 1 +
        single a 1 * single (b - 1) ((b : R) * 1) := by
    rw [single_mul_single, single_mul_single, show a - 1 + b = a + b - 1 by ring,
      show a + (b - 1) = a + b - 1 by ring, ← single_add]
    push_cast
    ring_nf
  simp only [hfg, derivative_single_mul_coe]
  simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.coe_add, PowerSeries.coe_mul]
  rw [hd, hab]
  ring

private theorem algebraMap_mul_eq_smul {R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] (c : R) (f : LaurentSeries A) :
    algebraMap R (LaurentSeries A) c * f = c • f := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, algebraMap_smul]

private noncomputable def laurentD (R : Type*) [CommRing R] :
    Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun f := LaurentSeries.derivative R f
  map_add' f g := (LaurentSeries.derivative R).map_add f g
  map_smul' c f := by
    rw [Algebra.smul_def, algebraMap_mul_eq_smul]
    exact map_smul (LaurentSeries.derivative R) c f
  map_one_eq_zero' := by
    ext n
    suffices n + 1 = 0 → (n : R) + 1 = 0 by
      simpa [LaurentSeries.derivative_apply, coeff_one]
    intro h
    simpa using congrArg (fun i : ℤ ↦ (i : R)) h
  leibniz' f g := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    rw [derivative_mul]
    ring

private theorem laurentD_constants {R : Type*} [Field R] [CharZero R]
    (f : R⸨X⸩) (hf : laurentD R f = 0) :
    ∃ c : R, algebraMap R R⸨X⸩ c = f := by
  refine ⟨f.coeff 0, ?_⟩
  have hc (n : ℤ) : n • f.coeff n = 0 := by
    have := congrArg (fun g : R⸨X⸩ => g.coeff (n - 1)) hf
    simpa [laurentD, LaurentSeries.derivative_apply] using this
  have hs : f = single 0 (f.coeff 0) := by
    ext n
    by_cases hn : n = 0
    · simp [hn]
    · simpa [coeff_single_of_ne hn, hn] using hc n
  simpa [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply] using hs.symm


private def polyJet (p A : ℝ[X]) : ℕ → ℝ[X]
  | 0 => A
  | v + 1 => p * (polyJet p A v).derivative +
      Polynomial.C ((1 : ℝ) / 2 - v) * p.derivative * polyJet p A v

private theorem polyJet_degree (p A : ℝ[X]) {d : ℕ}
    (hp : p.natDegree ≤ 2) (hA : A.natDegree ≤ d) (v : ℕ) :
    (polyJet p A v).natDegree ≤ d + 2 * v := by
  induction v with
  | zero => simpa [polyJet] using hA
  | succ v ih =>
    simp only [polyJet]
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · have h := Polynomial.natDegree_mul_le p (polyJet p A v).derivative
      have h' := (Polynomial.natDegree_derivative_le (polyJet p A v)).trans (Nat.sub_le _ _)
      omega
    · have h := Polynomial.natDegree_mul_le
        (Polynomial.C ((1 : ℝ) / 2 - v) * p.derivative) (polyJet p A v)
      have h' := Polynomial.natDegree_C_mul_le ((1 : ℝ) / 2 - v) p.derivative
      have h'' := (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
      omega

private def polyLS : ℝ[X] →+* ℝ⸨X⸩ :=
  (HahnSeries.ofPowerSeries ℤ ℝ).comp Polynomial.coeToPowerSeries.ringHom

private theorem D_poly (p : ℝ[X]) : laurentD ℝ (polyLS p) = polyLS p.derivative := by
  change LaurentSeries.derivative ℝ ((p : ℝ⟦X⟧) : ℝ⸨X⸩) =
    ((p.derivative : ℝ⟦X⟧) : ℝ⸨X⸩)
  rw [← coe_derivative, PowerSeries.derivative_coe]

private theorem D_root (S : ℝ⸨X⸩) (p : ℝ[X])
    (hp : polyLS p ≠ 0) (hs : S ^ 2 = polyLS p) :
    laurentD ℝ S = (1 / 2 : ℝ⸨X⸩) * polyLS p.derivative * S / polyLS p := by
  have h := congrArg (laurentD ℝ) hs
  rw [Derivation.leibniz_pow, D_poly] at h
  simp only [pow_one, nsmul_eq_mul, smul_eq_mul] at h
  apply (eq_div_iff hp).2
  rw [← hs]
  linear_combination S / 2 * h

end CdsoRadical
