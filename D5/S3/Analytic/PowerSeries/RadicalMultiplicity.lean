/- GID: D5/S3/Analytic/PowerSeries/RadicalMultiplicity
   generality: G
   mirror-B: D5/B/S3/Analytic/PowerSeries/RadicalMultiplicity
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
Library/Analytic/leanpool-differential-wronskian.md.
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
Apache-2.0. Full license: Library/Analytic/tauceti-laurent-derivation.md.
Required closure from TauCetiProject/TauCeti at
93af5b549b7d9ed44291d6ceb093a8013dda00f8,
TauCeti/RingTheory/LaurentSeries/{Basic,Derivative}.lean.
The power-series compatibility proof uses the pinned derivative API directly.
Retirement: replace this closure by direct imports when this repository's pinned
Mathlib supplies Laurent derivative Leibniz and its bundled derivation.
-/

open scoped LaurentSeries PowerSeries

namespace CdsoRadical

open HahnSeries Polynomial
noncomputable section

private theorem coe_derivative {R : Type*} [CommRing R] (f : R⟦X⟧) :
    ((PowerSeries.derivative f : R⟦X⟧) : R⸨X⸩) =
      LaurentSeries.derivative R (f : R⸨X⸩) := by
  ext i
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  rcases i with n | n
  · simp [PowerSeries.coeff_derivative, Ring.choose_one_right,
      show ¬(n : ℤ) < 0 by omega, show ¬(n : ℤ) + 1 < 0 by omega,
      show ((n : ℤ) + 1).natAbs = n + 1 by omega, nsmul_eq_mul, mul_comm]
  · rcases n with _ | n
    · simp [Ring.choose_one_right]
    · simp [show Int.negSucc (n + 1) + 1 < 0 by omega]

private theorem derivative_single_mul {R : Type*} [CommRing R]
    (m : ℤ) (c : R) (f : R⸨X⸩) :
    LaurentSeries.derivative R (single m c * f) =
      single (m - 1) (m * c) * f + single m c * LaurentSeries.derivative R f := by
  ext n
  simp only [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    HahnSeries.coeff_add, coeff_single_mul, Ring.choose_one_right]
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

local instance laurentModule (R : Type*) [CommRing R] : Module R (LaurentSeries R) :=
  (inferInstance : Algebra R (LaurentSeries R)).toModule

local instance laurentCharZero (R : Type*) [Field R] [CharZero R] :
    CharZero (LaurentSeries R) := Algebra.charZero_of_charZero R (LaurentSeries R)

private noncomputable def laurentD (R : Type*) [CommRing R] :
    Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun f := LaurentSeries.derivative R f
  map_add' f g := by
    ext n
    simp [LaurentSeries.derivative_apply, smul_add]
  map_smul' c f := by
    change LaurentSeries.derivative R (algebraMap R (LaurentSeries R) c * f) =
      algebraMap R (LaurentSeries R) c * LaurentSeries.derivative R f
    rw [algebraMap_mul_eq_smul, algebraMap_mul_eq_smul]
    exact map_smul (LaurentSeries.derivative R) c f
  map_one_eq_zero' := by
    ext n
    suffices n + 1 = 0 → (n : R) + 1 = 0 by
      simpa [LaurentSeries.derivative_apply, HahnSeries.coeff_one]
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
    · have h := Polynomial.natDegree_mul_le (p := p) (q := (polyJet p A v).derivative)
      have h' := (Polynomial.natDegree_derivative_le (polyJet p A v)).trans (Nat.sub_le _ _)
      omega
    · have h := Polynomial.natDegree_mul_le
        (p := Polynomial.C ((1 : ℝ) / 2 - v) * p.derivative) (q := polyJet p A v)
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


private theorem D_jet (S : ℝ⸨X⸩) (p A : ℝ[X])
    (hp : polyLS p ≠ 0) (hs : S ^ 2 = polyLS p) (v : ℕ) :
    ((laurentD ℝ).toLinearMap ^ v) (polyLS A * S) =
      S * polyLS p ^ (-(v : ℤ)) * polyLS (polyJet p A v) := by
  induction v with
  | zero => simp [polyJet, mul_comm]
  | succ v ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change laurentD ℝ (S * polyLS p ^ (-(v : ℤ)) * polyLS (polyJet p A v)) = _
    rw [Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_zpow,
      D_root S p hp hs, D_poly, D_poly]
    simp only [polyJet, map_add, map_mul, smul_eq_mul]
    have hz : polyLS p ^ (-(v : ℤ)) =
        polyLS p ^ (-((v + 1 : ℕ) : ℤ)) * polyLS p := by
      calc
        _ = polyLS p ^ (-((v + 1 : ℕ) : ℤ) + 1) := by congr 1; omega
        _ = _ := by rw [zpow_add₀ hp, zpow_one]
    have hz' : polyLS p ^ (-(v : ℤ) - 1) =
        polyLS p ^ (-((v + 1 : ℕ) : ℤ)) := by congr 1; push_cast; ring
    rw [hz', hz]
    have hC (c : ℝ) : polyLS (Polynomial.C c) = algebraMap ℝ ℝ⸨X⸩ c := by
      simp [polyLS, Polynomial.coe_C, HahnSeries.algebraMap_apply',
        PowerSeries.algebraMap_apply]
    rw [hC]
    simp only [map_sub, map_div₀, map_one, map_ofNat, map_natCast, zsmul_eq_mul,
      Int.cast_neg, Int.cast_natCast]
    push_cast
    field_simp [hp]
    <;> ring

private def wronskianPS {n : ℕ} (f : Fin n → ℝ⟦X⟧) :
    Matrix (Fin n) (Fin n) ℝ⟦X⟧ :=
  fun i j => PowerSeries.derivative^[i.val] (f j)

private theorem iterate_coe (f : ℝ⟦X⟧) (v : ℕ) :
    ((laurentD ℝ).toLinearMap ^ v) (f : ℝ⸨X⸩) =
      ((PowerSeries.derivative^[v] f : ℝ⟦X⟧) : ℝ⸨X⸩) := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply']
    exact (coe_derivative _).symm

private theorem wronskianPS_ne_zero {n : ℕ} (f : Fin n → ℝ⟦X⟧)
    (hi : LinearIndependent ℝ (fun i => (f i : ℝ⸨X⸩))) :
    (wronskianPS f).det ≠ 0 := by
  have h := BGS.Algebra.derivationWronskian_det_ne_zero_of_linearIndependent
    (laurentD ℝ) (laurentD_constants) n _ hi
  have he : BGS.Algebra.derivationWronskian (laurentD ℝ)
      (fun i => (f i : ℝ⸨X⸩)) =
      (wronskianPS f).map (HahnSeries.ofPowerSeries ℤ ℝ) := by
    exact Matrix.ext fun i j => iterate_coe _ _
  rw [he] at h
  change Matrix.det ((HahnSeries.ofPowerSeries ℤ ℝ).mapMatrix (wronskianPS f)) ≠ 0 at h
  rw [← RingHom.map_det] at h
  exact fun hz => h (by rw [hz, map_zero])


private theorem detPoly_degree {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ[X])
    (d : ℕ) (hM : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.natDegree ≤ n * d := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  have hsign : (Equiv.Perm.sign σ • ∏ i, M (σ i) i).natDegree ≤
      (∏ i, M (σ i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · simp [h]
    · simp [h, Units.neg_smul, Polynomial.natDegree_neg]
  refine hsign.trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
  calc
    (∑ i, (M (σ i) i).natDegree) ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => hM _ _
    _ = n * d := by simp

private theorem column_order {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ⟦X⟧)
    (j : Fin n) (b : ℕ) (hM : ∀ i, (b : ℕ∞) ≤ (M i j).order) :
    (b : ℕ∞) ≤ M.det.order := by
  classical
  have hdiv : ∀ i, (PowerSeries.X : ℝ⟦X⟧) ^ b ∣ M i j := by
    intro i
    rw [PowerSeries.X_pow_dvd_iff]
    exact PowerSeries.nat_le_order_iff.mp (hM i)
  choose c hc using hdiv
  have he : M = M.updateCol j ((PowerSeries.X ^ b : ℝ⟦X⟧) • c) := by
    apply Matrix.ext
    intro i k
    by_cases hk : k = j
    · subst k
      simpa [Matrix.updateCol_apply, Pi.smul_apply, smul_eq_mul] using hc i
    · simp [Matrix.updateCol_apply, hk]
  have hd : (PowerSeries.X : ℝ⟦X⟧) ^ b ∣ M.det := by
    refine ⟨(M.updateCol j c).det, ?_⟩
    conv_lhs => rw [he]
    exact Matrix.det_updateCol_smul M j _ c
  exact PowerSeries.nat_le_order_iff.mpr (PowerSeries.X_pow_dvd_iff.mp hd)

private theorem polynomial_order_le (p : ℝ[X]) (hp : p ≠ 0) :
    (p : ℝ⟦X⟧).order ≤ (p.natDegree : ℕ∞) := by
  apply PowerSeries.order_le
  simpa only [Polynomial.coeff_coe, Polynomial.leadingCoeff] using
    (Polynomial.leadingCoeff_ne_zero.mpr hp)


private theorem jet_factorPS (S : ℝ⟦X⟧) (p A : ℝ[X])
    (hS0 : PowerSeries.constantCoeff S ≠ 0)
    (hs : S ^ 2 = (p : ℝ⟦X⟧)) (N v : ℕ) (hv : v ≤ N) :
    (p : ℝ⟦X⟧) ^ N * PowerSeries.derivative^[v] ((A : ℝ⟦X⟧) * S) =
      S * ((p ^ (N - v) * polyJet p A v : ℝ[X]) : ℝ⟦X⟧) := by
  have hS : S ≠ 0 := fun h => hS0 (by rw [h, map_zero])
  have hSL : (S : ℝ⸨X⸩) ≠ 0 :=
    (map_ne_zero_iff _ (HahnSeries.ofPowerSeries_injective)).mpr hS
  have hsL : (S : ℝ⸨X⸩) ^ 2 = polyLS p := by
    simpa [polyLS] using congrArg (HahnSeries.ofPowerSeries ℤ ℝ) hs
  have hp : polyLS p ≠ 0 := by rw [← hsL]; exact pow_ne_zero _ hSL
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℝ))
  simp only [map_mul, map_pow, Polynomial.coe_mul, Polynomial.coe_pow]
  rw [← iterate_coe, map_mul]
  change polyLS p ^ N * ((laurentD ℝ).toLinearMap ^ v) (polyLS A * (S : ℝ⸨X⸩)) = _
  rw [D_jet _ p A hp hsL, zpow_neg, zpow_natCast]
  change polyLS p ^ N * ((S : ℝ⸨X⸩) * (polyLS p ^ v)⁻¹ * polyLS (polyJet p A v)) =
    (S : ℝ⸨X⸩) * (polyLS p ^ (N - v) * polyLS (polyJet p A v))
  have he : polyLS p ^ N = polyLS p ^ v * polyLS p ^ (N - v) := by
    rw [← pow_add, Nat.add_sub_of_le hv]
  rw [he]
  field_simp [hp]
  <;> ring

private theorem wronskian_order_bound {n d : ℕ} (hn : 0 < n)
    (S : Fin n → ℝ⟦X⟧) (p A : Fin n → ℝ[X])
    (hS0 : ∀ j, PowerSeries.constantCoeff (S j) ≠ 0)
    (hs : ∀ j, S j ^ 2 = (p j : ℝ⟦X⟧))
    (hp : ∀ j, (p j).natDegree ≤ 2) (hA : ∀ j, (A j).natDegree ≤ d)
    (hi : LinearIndependent ℝ (fun j => (((A j : ℝ⟦X⟧) * S j) : ℝ⸨X⸩))) :
    (wronskianPS (fun j => (A j : ℝ⟦X⟧) * S j)).det.order ≤
      (n * (d + 2 * (n - 1)) : ℕ) := by
  classical
  let Q : Matrix (Fin n) (Fin n) ℝ[X] :=
    fun i j => p j ^ (n - 1 - i.val) * polyJet (p j) (A j) i.val
  let W := wronskianPS (fun j => (A j : ℝ⟦X⟧) * S j)
  have hQ (i j : Fin n) : (Q i j).natDegree ≤ d + 2 * (n - 1) := by
    have hiN : i.val ≤ n - 1 := by omega
    have h1 := Polynomial.natDegree_mul_le
      (p := p j ^ (n - 1 - i.val)) (q := polyJet (p j) (A j) i.val)
    have h2 := Polynomial.natDegree_pow_le_of_le (n - 1 - i.val) (hp j)
    have h3 := polyJet_degree (p j) (A j) (hp j) (hA j) i.val
    dsimp [Q]
    omega
  have he : (fun i j => (p j : ℝ⟦X⟧) ^ (n - 1) * W i j) =
      (fun i j => S j * ((Q i j : ℝ[X]) : ℝ⟦X⟧)) := by
    funext i j
    exact jet_factorPS (S j) (p j) (A j) (hS0 j) (hs j) (n - 1) i.val (by omega)
  have hdet := congrArg Matrix.det he
  change (Matrix.of (fun i j => (p j : ℝ⟦X⟧) ^ (n - 1) * W i j)).det =
    (Matrix.of (fun i j => S j * ((Q i j : ℝ[X]) : ℝ⟦X⟧))).det at hdet
  rw [Matrix.det_mul_row (fun j => (p j : ℝ⟦X⟧) ^ (n - 1)) W] at hdet
  have hscale := Matrix.det_mul_row S
    (fun (i j : Fin n) => ((Q i j : ℝ[X]) : ℝ⟦X⟧))
  rw [hscale] at hdet
  have hmap : Matrix.det (fun i j => ((Q i j : ℝ[X]) : ℝ⟦X⟧)) = (Q.det : ℝ⟦X⟧) := by
    exact (Polynomial.coeToPowerSeries.ringHom.map_det Q).symm
  rw [hmap] at hdet
  have hunitS : IsUnit (∏ j, S j) := by
    apply IsUnit.prod_iff.mpr
    intro j _
    exact PowerSeries.isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr (hS0 j))
  have hunitP : IsUnit (∏ j, (p j : ℝ⟦X⟧) ^ (n - 1)) := by
    apply IsUnit.prod_iff.mpr
    intro j _
    rw [← hs j]
    exact (PowerSeries.isUnit_iff_constantCoeff.mpr
      (isUnit_iff_ne_zero.mpr (hS0 j))).pow _ |>.pow _
  have hord := congrArg PowerSeries.order hdet
  simp only [PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit hunitP,
    PowerSeries.order_zero_of_isUnit hunitS, zero_add] at hord
  have hW : W.det ≠ 0 := wronskianPS_ne_zero _ (by simpa only [map_mul] using hi)
  have hQne : Q.det ≠ 0 := by
    intro hz
    have : (Q.det : ℝ⟦X⟧) = 0 := by simp [hz]
    have := hord.trans (congrArg PowerSeries.order this)
    exact hW (PowerSeries.order_eq_top.mp (by simpa using this))
  exact hord.trans_le ((polynomial_order_le _ hQne).trans (by
    exact_mod_cast detPoly_degree Q _ hQ))

private theorem jet_sum {n : ℕ} (f : Fin n → ℝ⟦X⟧) (c : Fin n → ℝ) (v : ℕ) :
    PowerSeries.derivative^[v] (∑ j, c j • f j) =
      ∑ j, c j • PowerSeries.derivative^[v] (f j) := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Derivation.map_smul, Function.iterate_succ_apply']

private theorem independent_sum_zero {n d : ℕ} (hn : 0 < n)
    (S : Fin n → ℝ⟦X⟧) (p A : Fin n → ℝ[X])
    (hS0 : ∀ j, PowerSeries.constantCoeff (S j) ≠ 0)
    (hs : ∀ j, S j ^ 2 = (p j : ℝ⟦X⟧))
    (hp : ∀ j, (p j).natDegree ≤ 2) (hA : ∀ j, (A j).natDegree ≤ d)
    (hi : LinearIndependent ℝ (fun j => (((A j : ℝ⟦X⟧) * S j) : ℝ⸨X⸩)))
    (c : Fin n → ℝ)
    (hcoeff : ∀ k ≤ n * (d + 2 * (n - 1)) + n - 1,
      PowerSeries.coeff k (∑ j, c j • ((A j : ℝ⟦X⟧) * S j)) = 0) :
    ∑ j, c j • ((A j : ℝ⟦X⟧) * S j) = 0 := by
  classical
  by_contra hz
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hz
  let f : Fin n → ℝ⟦X⟧ := fun j => (A j : ℝ⟦X⟧) * S j
  let Z := ∑ j, c j • f j
  let W := wronskianPS f
  let M := W.updateCol j (fun i => PowerSeries.derivative^[i.val] Z)
  have he : M.det = PowerSeries.C (c j) * W.det := by
    have hM : M = W.updateCol j (fun i => ∑ k, PowerSeries.C (c k) * W i k) := by
      apply Matrix.ext
      intro i k
      by_cases hk : k = j
      · subst k
        simpa [M, Matrix.updateCol_apply, Z, W, wronskianPS,
          PowerSeries.smul_eq_C_mul] using jet_sum f c i.val
      · simp [M, Matrix.updateCol_apply, hk]
    rw [hM]
    exact Matrix.det_updateCol_sum W j (fun k => PowerSeries.C (c k))
  let D := n * (d + 2 * (n - 1))
  have hcol (i : Fin n) : (D + 1 : ℕ) ≤ (M i j).order := by
    apply PowerSeries.nat_le_order_iff.mpr
    intro k hk
    simp only [M, Matrix.updateCol_apply, ite_true,
      PowerSeries.coeff_iterate_derivative]
    change (k+1).ascFactorial i.val * PowerSeries.coeff (k+i.val)
      (∑ j, c j • ((A j : ℝ⟦X⟧) * S j)) = 0
    rw [hcoeff (k + i.val) (by dsimp [D] at hk; omega), mul_zero]
  have hlow := column_order M j (D + 1) hcol
  have hunit : IsUnit (PowerSeries.C (c j) : ℝ⟦X⟧) :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simpa using isUnit_iff_ne_zero.mpr hj)
  rw [he, PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit hunit, zero_add] at hlow
  have hupp := wronskian_order_bound hn S p A hS0 hs hp hA hi
  have hbad := hlow.trans hupp
  have hbadNat : D + 1 ≤ D := by exact_mod_cast hbad
  omega

/-- A quadratic finite-jet cutoff for polynomial radical sums; the original family may be
linearly dependent and may contain identical or zero summands. -/
theorem sum_eq_zero_of_coeff_eq_zero {ι : Type*} [Fintype ι]
    (S : ι → ℝ⟦X⟧) (p A : ι → ℝ[X])
    (hS0 : ∀ j, PowerSeries.constantCoeff (S j) ≠ 0)
    (hs : ∀ j, S j ^ 2 = (p j : ℝ⟦X⟧))
    (hp : ∀ j, (p j).natDegree ≤ 2)
    (hA : ∀ j, (A j).natDegree ≤ Fintype.card ι)
    (hcoeff : ∀ k ≤ 3 * (Fintype.card ι) ^ 2,
      PowerSeries.coeff k (∑ j, (A j : ℝ⟦X⟧) * S j) = 0) :
    ∑ j, (A j : ℝ⟦X⟧) * S j = 0 := by
  classical
  let f : ι → ℝ⟦X⟧ := fun j => (A j : ℝ⟦X⟧) * S j
  obtain ⟨κ, a, ha, hspan, hi⟩ := exists_linearIndependent' ℝ f
  letI : Fintype κ := Fintype.ofInjective a ha
  let l := Fintype.card κ
  let e : κ ≃ Fin l := Fintype.equivFin κ
  let b : Fin l → ι := a ∘ e.symm
  have hb : Function.Injective b := ha.comp e.symm.injective
  have hl : l ≤ Fintype.card ι := Fintype.card_le_of_injective a ha
  have hrange : Set.range (f ∘ b) = Set.range (f ∘ a) := by
    exact e.symm.surjective.range_comp (f ∘ a)
  have hZ : (∑ j, f j) ∈ Submodule.span ℝ (Set.range (f ∘ b)) := by
    rw [hrange, hspan]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hZ
  by_cases hl0 : l = 0
  · simpa [hl0] using hc.symm
  have hi' : LinearIndependent ℝ (fun j : Fin l => (f (b j) : ℝ⸨X⸩)) := by
    have hli : LinearIndependent ℝ (f ∘ b) := hi.comp e.symm e.symm.injective
    apply Fintype.linearIndependent_iff.mpr
    intro r hr
    apply Fintype.linearIndependent_iff.mp hli r
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℝ))
    rw [map_sum, map_zero]
    convert hr using 1
    apply Finset.sum_congr rfl
    intro j _
    rw [PowerSeries.smul_eq_C_mul, map_mul]
    change (HahnSeries.ofPowerSeries ℤ ℝ) (PowerSeries.C (r j)) *
      (f (b j) : ℝ⸨X⸩) = algebraMap ℝ ℝ⸨X⸩ (r j) * (f (b j) : ℝ⸨X⸩)
    congr 1

  have hcut : l * (Fintype.card ι + 2 * (l - 1)) + l - 1 ≤
      3 * (Fintype.card ι) ^ 2 := by
    have hlpos : 0 < l := Nat.pos_of_ne_zero hl0
    have hsub : l - 1 + 1 = l := by omega
    have hmul := Nat.mul_le_mul_left (Fintype.card ι) hl
    have hsq := Nat.mul_self_le_mul_self hl
    have htrunc : l * (Fintype.card ι + 2 * (l-1)) + l - 1 ≤
        l * (Fintype.card ι + 2 * (l-1)) + l := Nat.sub_le _ _
    nlinarith
  have hz := independent_sum_zero (Nat.pos_of_ne_zero hl0)
    (S ∘ b) (p ∘ b) (A ∘ b)
    (fun j => hS0 (b j)) (fun j => hs (b j))
    (fun j => hp (b j)) (fun j => hA (b j))
    (by simpa only [f, Function.comp_apply, map_mul] using hi') c
    (fun k hk => by
      change PowerSeries.coeff k (∑ j, c j • (f ∘ b) j) = 0
      rw [hc]
      exact hcoeff k (hk.trans hcut))
  change (∑ j, c j • (f ∘ b) j) = 0 at hz
  rw [hc] at hz
  exact hz

end
end CdsoRadical
