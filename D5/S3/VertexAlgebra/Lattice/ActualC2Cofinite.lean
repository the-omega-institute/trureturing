/- GID: D5/S3/VertexAlgebra/Lattice/ActualC2Cofinite
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/ActualC2Cofinite
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-definite lattice actual C2 is finite-dimensional on the literal carrier quotient. -/

/-
Copyright (c) 2026 Fedor K. Popov. All rights reserved.
Released under Apache 2.0 license as described in the repository root LICENSE.
Authors: Fedor K. Popov
Modified source: the sector-ideal/Newton route is a source-faithful port of
VOA.Classification.COne.latticeVOAGen_c2Cofinite from Lean_VOA commit
013a799ca834a8a6b3afa8129e3e522025b3f45c.  The local carrier and actual-field
suppliers are retained from their local provenance; no external VOA stack is
vendored.
proof_shape: positive_definite_c2_cofinite: content
admission_basis: escape-witness
escape_witness: the live proof closes every charge sector by the actual C2 ideal,
reduces unbounded oscillator powers, and spans the full literal carrier by the
finite closed charge box.
escape-audit: unfinished; no source-faithful enrolled Reg template supplies the
required whole-family variation, sensitivity, and observational-dependence
evidence for this Prop-valued finite-dimensionality statement.
-/

import D5.S3.VertexAlgebra.Lattice.ActualC2
import D5.S3.VertexAlgebra.LatticeActualConformalState
import D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.RingTheory.MvPolynomial.Ideal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.ActualC2Cofinite

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration
open D5.S3.VertexAlgebra.LatticeActualConformalState
open D5.S3.VertexAlgebra.LatticeSugawaraConformal
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeAllStateField
open D5.S3.VertexAlgebra.LatticeActualStateFieldCalculus
open D5.S3.VertexAlgebra.LatticeAllStateReconstruction
open MvPolynomial Matrix
open scoped BigOperators VertexOperator

noncomputable section

open private ground ground_product creation_zero
  from D5.S3.VertexAlgebra.Lattice.NormFourFixedPeirce
open private left_minus_one_mem higher_product_mem
  from D5.S3.VertexAlgebra.Lattice.ActualC2
open private creation_derivation
  from D5.S3.VertexAlgebra.LatticeSugawaraConformal
open private bilinear_unit bilinear_sub_right
  from D5.S3.VertexAlgebra.LatticeFiniteNegativeGeneration

def sectorIdeal (D : LatticeData) (δ : Charge D) : Ideal (Oscillator D) where
  carrier := {p | Finsupp.single δ p ∈ ActualC2.C2 D}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change Finsupp.single δ (p + q) ∈ ActualC2.C2 D
    rw [Finsupp.single_add]
    exact (ActualC2.C2 D).add_mem hp hq
  smul_mem' := by
    intro p q hq
    change Finsupp.single δ (p * q) ∈ ActualC2.C2 D
    induction p using MvPolynomial.induction_on generalizing q with
    | C c =>
        have hC : (C c : Oscillator D) * q = c • q := by
          simp [Algebra.smul_def]
        rw [hC]
        simpa only [Finsupp.smul_single] using (ActualC2.C2 D).smul_mem c hq
    | add p q hp hq' =>
        simpa only [smul_eq_mul, add_mul, Finsupp.single_add] using
          (ActualC2.C2 D).add_mem (hp hq) (hq' hq)
    | mul_X p x hp =>
        obtain ⟨i, k⟩ := x
        cases k with
        | zero =>
          have hm := left_minus_one_mem D (currentState D i)
            (Finsupp.single δ (p • q)) (hp hq)
          have heq : mu D (currentState D i) (-1) (Finsupp.single δ (p • q)) =
              Finsupp.single δ (X (i, 0) * (p • q)) := by
            rw [mu, current_state_field, neutralField_ncoeff]
            simp [neutralMode, neutralPolynomialMode]
          rw [heq] at hm
          simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hm
        | succ k =>
          have hm := higher_product_mem D k (currentState D i)
            (Finsupp.single δ (p • q))
          have heq : mu D (currentState D i) (-((k : ℤ) + 2))
                (Finsupp.single δ (p • q)) =
              Finsupp.single δ (X (i, k + 1) * (p • q)) := by
            rw [mu, current_state_field, neutralField_ncoeff,
              neutralMode_single,
              show -((k : ℤ) + 2) = -((k + 1 : ℕ) : ℤ) - 1 by omega,
              neutralPolynomialMode_negative]
            simp [mul_assoc]
          rw [heq] at hm
          simpa only [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using hm

private theorem higher_var_mem (D : LatticeData) (δ : Charge D)
    (i : Fin D.rank) {k : ℕ} (hk : 1 ≤ k) :
    X (i, k) ∈ sectorIdeal D δ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have h := higher_product_mem D r (currentState D i)
    (Finsupp.single δ (1 : Oscillator D))
  have heq : mu D (currentState D i) (-((r : ℤ) + 2))
      (Finsupp.single δ (1 : Oscillator D)) =
      Finsupp.single δ (X (i, r + 1) * (1 : Oscillator D)) := by
    rw [mu, current_state_field, neutralField_ncoeff,
      neutralMode_single,
      show -((r : ℤ) + 2) = -((r + 1 : ℕ) : ℤ) - 1 by omega,
      neutralPolynomialMode_negative]
    simp
  rw [heq] at h
  change Finsupp.single δ (X (i, r + 1)) ∈ ActualC2.C2 D
  simpa using h

private theorem derivation_mem (D : LatticeData) (δ : Charge D)
    (p : Oscillator D) :
    oscillatorDerivation D p ∈ sectorIdeal D δ := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [oscillatorDerivation]
  | add p q hp hq =>
      simpa only [map_add] using (sectorIdeal D δ).add_mem hp hq
  | mul_X p x hp =>
      obtain ⟨i, k⟩ := x
      simp only [oscillatorDerivation, Derivation.leibniz, MvPolynomial.mkDerivation_X,
        smul_eq_mul, map_mul]
      apply (sectorIdeal D δ).add_mem
      · have hx := higher_var_mem D δ i (by omega : 1 ≤ k + 1)
        simpa [oscillatorDerivation, smul_eq_mul] using (sectorIdeal D δ).mul_mem_left p
          (Submodule.smul_of_tower_mem (sectorIdeal D δ) (k + 1 : ℂ) hx)
      · simpa [oscillatorDerivation, mul_comm] using (sectorIdeal D δ).mul_mem_left
          (X (i, k)) hp

private theorem ground_coeff_mem (D : LatticeData) (δ α : Charge D) (d : ℕ)
    (hd : 1 + bilinear D α α - bilinear D α δ ≤ (d : ℤ)) :
    creationCoeff D α d ∈ sectorIdeal D δ := by
  let n : ℤ := -(d : ℤ) - 1 - bilinear D α (δ - α)
  have hn : n ≤ -2 := by
    dsimp [n]
    rw [bilinear_sub_right]
    omega
  have h := higher_product_mem D ((-n - 2).toNat)
    (ground D α) (ground D (δ - α))
  have hto : ((-n - 2).toNat : ℤ) = -n - 2 :=
    Int.toNat_of_nonneg (by omega)
  have hmode : -(((-n - 2).toNat : ℤ) + 2) = n := by omega
  rw [hmode, ground_product] at h
  have he : epsilon D α (δ - α) ≠ 0 := by
    unfold epsilon paritySign
    split_ifs <;> norm_num
  have harg : -n - 1 - bilinear D α (δ - α) = (d : ℤ) := by
    dsimp [n]
    ring
  rw [harg, show α + (δ - α) = δ by abel] at h
  have h' := Submodule.smul_of_tower_mem (ActualC2.C2 D)
    (epsilon D α (δ - α))⁻¹ h
  change Finsupp.single δ (creationCoeff D α (d : ℤ)) ∈ ActualC2.C2 D
  simpa only [Finsupp.single_smul, smul_smul, inv_mul_cancel₀ he, one_smul] using h'

private theorem creation_power_sub_mem (D : LatticeData) (δ α : Charge D)
    (d : ℕ) :
    (chargePolynomial D α) ^ d - (d.factorial : ℂ) • creationCoeff D α d ∈
      sectorIdeal D δ := by
  induction d with
  | zero => simp [creation_zero]
  | succ d ih =>
      have hd := derivation_mem D δ (creationCoeff D α d)
      have hrec := creation_derivation D α (d : ℤ)
      have hmul := (sectorIdeal D δ).mul_mem_left (chargePolynomial D α) ih
      have hkey :
          (chargePolynomial D α) ^ (d + 1) - ((d + 1).factorial : ℂ) •
              creationCoeff D α ((d : ℤ) + 1) =
            chargePolynomial D α *
                ((chargePolynomial D α) ^ d - (d.factorial : ℂ) •
                  creationCoeff D α d) -
              (d.factorial : ℂ) • oscillatorDerivation D (creationCoeff D α d) := by
        have hrec' : oscillatorDerivation D (creationCoeff D α d) =
            ((d : ℂ) + 1) • creationCoeff D α ((d : ℤ) + 1) -
              chargePolynomial D α * creationCoeff D α d := by
          exact hrec
        rw [hrec']
        have hfac : ((d + 1).factorial : ℂ) =
            (d + 1 : ℂ) * (d.factorial : ℂ) := by
          rw [Nat.factorial_succ]
          norm_num
        rw [hfac]
        simp only [smul_sub, smul_add, smul_smul, Algebra.smul_def,
          Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        have hcoef :
            (algebraMap ℂ (Oscillator D))
                (((d : ℂ) + 1) * (d.factorial : ℂ)) =
              (algebraMap ℂ (Oscillator D)) (d.factorial : ℂ) *
                (algebraMap ℂ (Oscillator D)) ((d : ℂ) + 1) := by
          rw [map_mul]
          ring
        rw [hcoef]
        ring
      have hmem := (sectorIdeal D δ).sub_mem hmul
        ((Submodule.smul_of_tower_mem (sectorIdeal D δ) (d.factorial : ℂ)) hd)
      have hgoal := hkey ▸ hmem
      simpa only [Nat.cast_add, Nat.cast_one] using hgoal

private theorem creation_power_mem (D : LatticeData) (δ α : Charge D) (d : ℕ)
    (hd : 1 + bilinear D α α - bilinear D α δ ≤ (d : ℤ)) :
    (chargePolynomial D α) ^ d ∈ sectorIdeal D δ := by
  have h := (sectorIdeal D δ).add_mem (creation_power_sub_mem D δ α d)
    (Submodule.smul_of_tower_mem (sectorIdeal D δ) (d.factorial : ℂ)
      (ground_coeff_mem D δ α d hd))
  simpa only [sub_add_cancel] using h

private theorem isIntegral_of_pow_eq_zero {A : Type*} [CommRing A] [Algebra ℂ A]
    {x : A} {n : ℕ} (hx : x ^ n = 0) : IsIntegral ℂ x :=
  ⟨Polynomial.X ^ n, Polynomial.monic_X_pow n, by simp [hx]⟩

private instance quotient_algebra (D : LatticeData) (δ : Charge D) :
    Algebra ℂ (Oscillator D ⧸ sectorIdeal D δ) := Ideal.Quotient.algebra ℂ

private instance quotient_module (D : LatticeData) (δ : Charge D) :
    Module ℂ (Oscillator D ⧸ sectorIdeal D δ) := by
  letI : Algebra ℂ (Oscillator D ⧸ sectorIdeal D δ) := quotient_algebra D δ
  exact Algebra.toModule

private theorem isNilpotent_mk_X_zero (D : LatticeData) (hD : Matrix.PosDef
    (D.G.map (Int.cast : ℤ → ℝ))) (δ : Charge D) (i : Fin D.rank) :
    IsNilpotent (Ideal.Quotient.mk (sectorIdeal D δ) (X (i, 0))) := by
  rw [← mem_nilradical]
  let z : ℤ := 1 + bilinear D (unitCharge D i) (unitCharge D i) -
    bilinear D (unitCharge D i) δ
  let n : ℕ := z.toNat
  have hpow : (X (i, 0)) ^ n ∈ sectorIdeal D δ := by
    have hnorm : bilinear D (unitCharge D i) (unitCharge D i) = D.G i i := by
      simp [bilinear, unitCharge]
    have h := creation_power_mem D δ (unitCharge D i)
      n (by
        dsimp [n, z]
        exact Int.self_le_toNat z)
    simpa [chargePolynomial, unitCharge, hnorm, n, z] using h
  exact ⟨n, by
    change (Ideal.Quotient.mk (sectorIdeal D δ) (X (i, 0))) ^
      n = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hpow⟩

private theorem adjoin_mk_X_zero_eq_top (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (δ : Charge D) :
    Algebra.adjoin ℂ (Set.range fun i : Fin D.rank =>
      Ideal.Quotient.mkₐ ℂ (sectorIdeal D δ) (X (i, 0))) = ⊤ := by
  let J := sectorIdeal D δ
  let f := Ideal.Quotient.mkₐ ℂ J
  have hsurj : Function.Surjective f := Ideal.Quotient.mkₐ_surjective ℂ J
  rw [eq_top_iff]
  have htop : (⊤ : Subalgebra ℂ (Oscillator D ⧸ J)) =
      (Algebra.adjoin ℂ (Set.range (fun x : Index D => X x))).map f := by
    rw [MvPolynomial.adjoin_range_X, Algebra.map_top, (AlgHom.range_eq_top f).2 hsurj]
  rw [htop, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨_, ⟨⟨i, k⟩, rfl⟩, rfl⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst k; exact Algebra.subset_adjoin ⟨i, rfl⟩
  · have hz : f (X (i, k)) = 0 := by
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact higher_var_mem D δ i hk
    rw [SetLike.mem_coe, hz]
    exact Subalgebra.zero_mem _

set_option maxHeartbeats 800000 in
private theorem finite_quot_sector (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (δ : Charge D) :
    Module.Finite ℂ (Oscillator D ⧸ sectorIdeal D δ) := by
  letI : Algebra ℂ (Oscillator D ⧸ sectorIdeal D δ) := quotient_algebra D δ
  refine ⟨?_⟩
  have h := fg_adjoin_of_finite (R := ℂ)
    (Set.finite_range fun i : Fin D.rank =>
      Ideal.Quotient.mkₐ ℂ (sectorIdeal D δ) (X (i, 0))) (by
      rintro _ ⟨i, rfl⟩
      obtain ⟨n, hn⟩ := isNilpotent_mk_X_zero D hD δ i
      exact isIntegral_of_pow_eq_zero (n := n) (by simpa using hn))
  rwa [adjoin_mk_X_zero_eq_top D hD δ, Algebra.top_toSubmodule] at h

def sectorMap (D : LatticeData) (δ : Charge D) : Oscillator D →ₗ[ℂ]
    (Carrier D ⧸ ActualC2.C2 D) :=
  (ActualC2.C2 D).mkQ.comp (Finsupp.lsingle δ)

set_option maxHeartbeats 800000 in
private theorem range_sectorMap_fg (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (δ : Charge D) :
    (LinearMap.range (sectorMap D δ)).FG := by
  have hle : (sectorIdeal D δ).restrictScalars ℂ ≤ LinearMap.ker (sectorMap D δ) := by
    intro p hp
    change (ActualC2.C2 D).mkQ (Finsupp.single δ p) = 0
    exact (Submodule.Quotient.mk_eq_zero (ActualC2.C2 D)).2 hp
  let ψ := (sectorIdeal D δ).restrictScalars ℂ |>.liftQ (sectorMap D δ) hle
  let e : (Oscillator D ⧸ ((sectorIdeal D δ).restrictScalars ℂ)) ≃ₗ[ℂ]
      Oscillator D ⧸ sectorIdeal D δ :=
    Submodule.Quotient.restrictScalarsEquiv ℂ (sectorIdeal D δ)
  letI : Module.Finite ℂ (Oscillator D ⧸ sectorIdeal D δ) := finite_quot_sector D hD δ
  letI : Module.Finite ℂ (Oscillator D ⧸ ((sectorIdeal D δ).restrictScalars ℂ)) :=
    Module.Finite.equiv e.symm
  have hr : LinearMap.range (sectorMap D δ) = LinearMap.range ψ := by
    rw [← (sectorIdeal D δ).restrictScalars ℂ |>.liftQ_mkQ (sectorMap D δ) hle,
      LinearMap.range_comp_of_range_eq_top _
        (Submodule.range_mkQ ((sectorIdeal D δ).restrictScalars ℂ))]
  rw [hr, LinearMap.range_eq_map]
  exact (Module.Finite.fg_top).map ψ

def shortCharges (D : LatticeData) : Set (Charge D) :=
  {δ | ∀ i, |bilinear D (unitCharge D i) δ| ≤ D.G i i}

private theorem shortCharges_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    (shortCharges D).Finite := by
  let f : Charge D → (Fin D.rank → ℤ) :=
    fun δ i => bilinear D (unitCharge D i) δ
  have hf : Function.Injective f := by
    intro α β h
    by_contra hne
    have hpos := norm_positive D hD (α - β) (sub_ne_zero.mpr hne)
    have hz : ∀ i, bilinear D (unitCharge D i) (α - β) = 0 := by
      intro i
      rw [bilinear_sub_right]
      exact sub_eq_zero.mpr (congrFun h i)
    have hq : bilinear D (α - β) (α - β) = 0 := by
      simp only [bilinear, Pi.sub_apply]
      simp_rw [mul_assoc, ← Finset.mul_sum]
      have hz' : ∀ i, ∑ j, D.G i j * (α j - β j) = 0 := by
        simpa only [bilinear_unit, Pi.sub_apply] using hz
      simp [hz']
    omega
  let B : Set (Fin D.rank → ℤ) :=
    Set.univ.pi fun i => Set.Icc (-D.G i i) (D.G i i)
  have hB : B.Finite := Set.Finite.pi fun i => Set.finite_Icc _ _
  refine (hB.preimage hf.injOn).subset ?_
  intro δ hδ i hi
  exact Set.mem_Icc.mpr (abs_le.mp (hδ i))

private theorem sector_top_of_not_short (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    {δ : Charge D} (hδ : δ ∉ shortCharges D) :
    sectorIdeal D δ = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  simp only [shortCharges, Set.mem_setOf_eq, not_forall, not_le] at hδ
  obtain ⟨i, hi⟩ := hδ
  by_cases hpos : 0 < bilinear D (unitCharge D i) δ
  · have hpow := creation_power_mem D δ (unitCharge D i) 0 (by
      have hnorm : bilinear D (unitCharge D i) (unitCharge D i) = D.G i i := by
        simp [bilinear, unitCharge]
      have hi' : D.G i i < bilinear D (unitCharge D i) δ := by
        simpa [abs_of_pos hpos] using hi
      rw [hnorm]
      omega)
    simpa [creation_zero] using hpow
  · have hpow := creation_power_mem D δ (-unitCharge D i) 0 (by
      have hnorm : bilinear D (-unitCharge D i) (-unitCharge D i) = D.G i i := by
        simp [bilinear, bilinear_neg_left, bilinear_neg_right, unitCharge]
      have hi' : D.G i i < -bilinear D (unitCharge D i) δ := by
        simpa [abs_of_nonpos (le_of_not_gt hpos)] using hi
      rw [hnorm, bilinear_neg_left]
      omega)
    simpa [creation_zero, bilinear_neg_left] using hpow

theorem positive_definite_c2_cofinite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    FiniteDimensional ℂ (Carrier D ⧸ ActualC2.C2 D) := by
  classical
  haveI : Finite (shortCharges D) := (shortCharges_finite D hD).to_subtype
  let M : Submodule ℂ (Carrier D ⧸ ActualC2.C2 D) :=
    ⨆ δ : shortCharges D, LinearMap.range (sectorMap D δ.1)
  have hMfg : M.FG := Submodule.fg_iSup _ fun δ => range_sectorMap_fg D hD δ.1
  have hMtop : M = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨v, rfl⟩ := (ActualC2.C2 D).mkQ_surjective x
    have hv : v ∈ Submodule.span ℂ
        (Set.range (fun q : Charge D × Oscillator D => Finsupp.single q.1 q.2)) := by
      induction v using Finsupp.induction_linear with
      | zero => exact Submodule.zero_mem _
      | add f g hf hg => exact Submodule.add_mem _ hf hg
      | single a b => exact Submodule.subset_span ⟨(a, b), rfl⟩
    refine Submodule.span_induction (p := fun v _ =>
      (ActualC2.C2 D).mkQ v ∈ M) ?_ ?_ ?_ ?_ hv
    · rintro z ⟨⟨δ, p⟩, rfl⟩
      by_cases hδ : δ ∈ shortCharges D
      · exact Submodule.mem_iSup_of_mem (⟨δ, hδ⟩ : shortCharges D) ⟨p, rfl⟩
      · have hp : p ∈ sectorIdeal D δ := by
          rw [sector_top_of_not_short D hD hδ]
          trivial
        change (ActualC2.C2 D).mkQ (Finsupp.single δ p) ∈ M
        have hz : (ActualC2.C2 D).mkQ (Finsupp.single δ p) = 0 :=
          (Submodule.Quotient.mk_eq_zero (ActualC2.C2 D)).2 hp
        rw [hz]
        exact M.zero_mem
    · simp
    · intro x y _ _ hx hy
      simpa using M.add_mem hx hy
    · intro c x _ hx
      simpa using M.smul_mem c hx
  exact ⟨hMtop ▸ hMfg⟩

end
end D5.S3.VertexAlgebra.Lattice.ActualC2Cofinite

section AxiomAudit
#print axioms D5.S3.VertexAlgebra.Lattice.ActualC2Cofinite.positive_definite_c2_cofinite
end AxiomAudit
