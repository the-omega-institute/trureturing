/- GID: D5/S3/VertexAlgebra/LatticeThetaCharacter
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/LatticeThetaCharacter
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual finite-charge theta restrictions, signed occupation traces and the identity-ground character endpoint. -/

import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeChargeCoercivity
import D5.S3.VertexAlgebra.LatticeInvolution
import D5.S3.VertexAlgebra.LatticeHalfFockCharacter
import D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators
open Filter Topology
open Complex

namespace D5.S3.VertexAlgebra.LatticeThetaCharacter

open D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open D5.S3.VertexAlgebra.LatticeAllStateField
open D5.S3.VertexAlgebra.LatticePositiveEnergy
open D5.S3.VertexAlgebra.LatticeSugawaraCurrents
open D5.S3.VertexAlgebra.LatticeInvolution
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization
open D5.S3.VertexAlgebra.LatticeTwistedGroundRealization.SignQuotient
open D5.S3.VertexAlgebra.LatticeHalfFockCharacter
open D5.S3.VertexAlgebra.LatticeHalfFockGradedTrace
open D5.S3.Combinatorics.Partitions.AnalyticIntegerOccupation
open D5.S3.Combinatorics.Partitions.EtaOddOccupation

abbrev CutoffIndex (D : LatticeData) (C : Finset (Charge D)) (n : ℤ) :=
  {a : Label D // a.1 ∈ C ∧ energy D a = n}

abbrev IntegerFiber (D : LatticeData) (N : ℕ) :=
  {d : Exponent D // oscillatorEnergy d = N}

private def reflectedLabel (D : LatticeData) (a : Label D) : Label D := (-a.1, a.2)

private def occurrenceSign (D : LatticeData) (a : Label D) : ℂ :=
  (-1 : ℂ) ^ (occurrences D a.2).length

private def coefficientThetaAtom (D : LatticeData) (a : Label D) :
    ℂ →ₗ[ℂ] (Label D →₀ ℂ) :=
  { toFun := fun c =>
      Finsupp.single (reflectedLabel D a) (occurrenceSign D a * c)
    map_add' := by
      intro x y
      simp [mul_add]
    map_smul' := by
      intro c x
      simp [smul_eq_mul, mul_assoc, mul_comm] }

private def coefficientTheta (D : LatticeData) :
    (Label D →₀ ℂ) →ₗ[ℂ] (Label D →₀ ℂ) :=
  Finsupp.lsum ℂ (fun a => coefficientThetaAtom D a)

private theorem coefficientTheta_single (D : LatticeData) (a : Label D) (c : ℂ) :
    coefficientTheta D (Finsupp.single a c) =
      Finsupp.single (reflectedLabel D a) (occurrenceSign D a * c) := by
  simp [coefficientTheta, coefficientThetaAtom]

private theorem carrierCoeff_theta (D : LatticeData) :
    (carrierCoeffEquiv D).toLinearMap.comp (thetaLinear D) =
      (coefficientTheta D).comp (carrierCoeffEquiv D).toLinearMap := by
  apply LinearMap.ext
  intro v
  let f := carrierCoeffEquiv D v
  have hv : v = (carrierCoeffEquiv D).symm f := by simp [f]
  rw [hv]
  change carrierCoeffEquiv D (thetaLinear D ((carrierCoeffEquiv D).symm f)) = _
  rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [LinearMap.comp_apply]
  rw [show Finsupp.single a (f a) = f a • Finsupp.single a 1 by simp]
  simp only [map_smul]
  rw [show (carrierCoeffEquiv D).symm (Finsupp.single a 1) = carrierBasis D a by rfl]
  rw [show thetaLinear D (carrierBasis D a) =
      occurrenceSign D a • carrierBasis D (reflectedLabel D a) by
    change thetaLinear D (carrierBasis D a) = _
    rw [carrierBasis_apply, theta_single, sigma_monomial, carrierBasis_apply,
      ← Finsupp.smul_single]
    rfl]
  have coeff_basis (b : Label D) :
      carrierCoeffEquiv D (carrierBasis D b) = Finsupp.single b 1 := by
    change (carrierCoeffEquiv D) ((carrierCoeffEquiv D).symm (Finsupp.single b 1)) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [map_smul]
  rw [coeff_basis (reflectedLabel D a)]
  change f a • occurrenceSign D a • Finsupp.single (reflectedLabel D a) 1 =
    f a • coefficientTheta D (carrierCoeffEquiv D (carrierBasis D a))
  rw [coeff_basis a, coefficientTheta_single]
  simp [occurrenceSign, reflectedLabel, smul_eq_mul]

private theorem reflected_involutive (D : LatticeData) (a : Label D) :
    reflectedLabel D (reflectedLabel D a) = a := by
  simp [reflectedLabel]

private theorem reflected_energy (D : LatticeData) (a : Label D) :
    energy D (reflectedLabel D a) = energy D a := by
  simp [reflectedLabel, energy, chargeEnergy, bilinear]

private theorem coefficientTheta_supported (D : LatticeData) (S : Set (Label D))
    (hS : ∀ a, a ∈ S → reflectedLabel D a ∈ S)
    (f : Label D →₀ ℂ) (hf : f ∈ Finsupp.supported ℂ ℂ S) :
    coefficientTheta D f ∈ Finsupp.supported ℂ ℂ S := by
  rw [Finsupp.mem_supported'] at hf ⊢
  intro a ha
  rw [coefficientTheta, Finsupp.lsum_apply]
  unfold Finsupp.sum
  change (∑ x ∈ f.support, coefficientThetaAtom D x (f x)) a = 0
  rw [Finset.sum_apply']
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hxa : reflectedLabel D x = a
  · exfalso
    apply ha
    rw [← hxa]
    exact hS x (by
      have hx0 := Finsupp.mem_support_iff.mp hx
      by_contra hnot
      exact hx0 (hf x hnot))
  · simp [coefficientThetaAtom, hxa]

def chargeSupported (D : LatticeData) (C : Finset (Charge D)) :
    Submodule ℂ (Carrier D) :=
  (Finsupp.supported ℂ ℂ {a : Label D | a.1 ∈ C}).comap
    (carrierCoeffEquiv D).toLinearMap

def cutoffActualGrade (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (C : Finset (Charge D)) (n : ℤ) : Submodule ℂ (Carrier D) :=
  chargeSupported D C ⊓ (sugawaraMode D H 0).eigenspace (n : ℂ)

def signedThetaCoefficient (D : LatticeData) (N : ℕ) : ℂ :=
  letI : Finite {d : Exponent D // oscillatorEnergy d ≤ N} := oscillatorLeFinite D N
  letI : Finite (IntegerFiber D N) := by
    apply Finite.of_injective (fun d : IntegerFiber D N =>
      (⟨d.1, Nat.le_of_eq d.2⟩ : {d : Exponent D // oscillatorEnergy d ≤ N}))
    intro a b h
    exact Subtype.ext (congrArg (fun z => z.1) h)
  letI : Fintype (IntegerFiber D N) := Fintype.ofFinite _
  ∑ d : IntegerFiber D N, (-1 : ℂ) ^ (occurrences D d.1).length

private theorem integerFiber_finite (D : LatticeData) (N : ℕ) :
    Finite (IntegerFiber D N) := by
  letI : Finite {d : Exponent D // oscillatorEnergy d ≤ N} :=
    oscillatorLeFinite D N
  exact Finite.of_injective (fun d : IntegerFiber D N =>
    (⟨d.1, Nat.le_of_eq d.2⟩ :
      {d : Exponent D // oscillatorEnergy d ≤ N})) (by
    intro a b h
    exact Subtype.ext (congrArg (fun z => z.1) h))

noncomputable instance integerFiber_fintype (D : LatticeData) (N : ℕ) :
    Fintype (IntegerFiber D N) := by
  letI : Finite (IntegerFiber D N) := integerFiber_finite D N
  exact Fintype.ofFinite _

private def neutralCutoffEquiv (D : LatticeData) (N : ℕ) :
    CutoffIndex D ({0} : Finset (Charge D)) (N : ℤ) ≃ IntegerFiber D N :=
  { toFun := fun a => ⟨a.1.2, by
      have ha : a.1.1 = 0 := by simpa using a.2.1
      have he := a.2.2
      simpa [energy, ha, chargeEnergy_zero] using he⟩
    invFun := fun d => ⟨(0, d.1), by simp [energy, d.2]⟩
    left_inv := by
      intro a
      apply Subtype.ext
      apply Prod.ext
      · have ha : a.1.1 = 0 := by simpa using a.2.1
        exact ha.symm
      · rfl
    right_inv := by
      intro d
      apply Subtype.ext
      rfl }

private theorem chargeSupported_mem_iff (D : LatticeData)
    (C : Finset (Charge D)) (v : Carrier D) :
    v ∈ chargeSupported D C ↔
      ∀ a : Label D, a.1 ∉ C → carrierCoeffEquiv D v a = 0 := by
  change carrierCoeffEquiv D v ∈ Finsupp.supported ℂ ℂ _ ↔ _
  rw [Finsupp.mem_supported']
  rfl

private theorem cutoffActualGrade_eq_supported (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ) :
    cutoffActualGrade D H C n =
      (Finsupp.supported ℂ ℂ {a : Label D | a.1 ∈ C ∧ energy D a = n}).comap
        (carrierCoeffEquiv D).toLinearMap := by
  ext v
  constructor
  · intro hv
    change carrierCoeffEquiv D v ∈
      Finsupp.supported ℂ ℂ {a : Label D | a.1 ∈ C ∧ energy D a = n}
    rw [Finsupp.mem_supported']
    intro a ha
    by_cases hC : a.1 ∈ C
    · have hgrade : v ∈ grade D n := by
        rw [← actualL0_eigenspace_eq_grade D H hHG hGH n]
        exact hv.2
      have henergy : energy D a ≠ n := by
        intro he
        exact ha ⟨hC, he⟩
      exact (mem_grade_iff D n v).mp hgrade a henergy
    · exact (chargeSupported_mem_iff D C v).mp hv.1 a hC
  · intro hv
    change carrierCoeffEquiv D v ∈
      Finsupp.supported ℂ ℂ {a : Label D | a.1 ∈ C ∧ energy D a = n} at hv
    rw [Finsupp.mem_supported'] at hv
    have hsupport : ∀ a : Label D, a.1 ∉ C → carrierCoeffEquiv D v a = 0 := by
      intro a ha
      exact hv a (by intro h; exact ha h.1)
    have hgrade : v ∈ grade D n := by
      rw [mem_grade_iff]
      intro a ha
      exact hv a (by intro h; exact ha h.2)
    refine ⟨?_, ?_⟩
    · exact (chargeSupported_mem_iff D C v).mpr hsupport
    · rw [actualL0_eigenspace_eq_grade D H hHG hGH n]
      exact hgrade

private theorem theta_mem_cutoff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (hCsym : ∀ a, a ∈ C → -a ∈ C)
    (v : Carrier D) (hv : v ∈ cutoffActualGrade D H C n) :
    thetaLinear D v ∈ cutoffActualGrade D H C n := by
  rw [cutoffActualGrade_eq_supported D H hHG hGH C n]
  change carrierCoeffEquiv D (thetaLinear D v) ∈
    Finsupp.supported ℂ ℂ {a : Label D | a.1 ∈ C ∧ energy D a = n}
  rw [show carrierCoeffEquiv D (thetaLinear D v) =
      coefficientTheta D (carrierCoeffEquiv D v) by
        exact LinearMap.congr_fun (carrierCoeff_theta D) v]
  refine coefficientTheta_supported D
    {a : Label D | a.1 ∈ C ∧ energy D a = n} ?_ (carrierCoeffEquiv D v) ?_
  · intro a ha
    exact ⟨hCsym a.1 ha.1, by rw [reflected_energy D a]; exact ha.2⟩
  · rw [cutoffActualGrade_eq_supported D H hHG hGH C n] at hv
    exact hv


def cutoffCoeffEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ) :
    cutoffActualGrade D H C n ≃ₗ[ℂ] (CutoffIndex D C n →₀ ℂ) := by
  let S : Set (Label D) := {a : Label D | a.1 ∈ C ∧ energy D a = n}
  let e : cutoffActualGrade D H C n ≃ₗ[ℂ]
      (Finsupp.supported ℂ ℂ S).comap
        (carrierCoeffEquiv D).toLinearMap :=
    LinearEquiv.ofEq _ _ (cutoffActualGrade_eq_supported D H hHG hGH C n)
  let e' := (LinearEquiv.ofSubmodule' (carrierCoeffEquiv D)
    (Finsupp.supported ℂ ℂ S)).trans (Finsupp.supportedEquivFinsupp S)
  change cutoffActualGrade D H C n ≃ₗ[ℂ] (S →₀ ℂ)
  exact e.trans e'

private theorem cutoffCoeffEquiv_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (v : cutoffActualGrade D H C n) (i : CutoffIndex D C n) :
    cutoffCoeffEquiv D H hHG hGH C n v i = carrierCoeffEquiv D v.1 i.1 := by
  rfl

theorem cutoffIndex_finite (D : LatticeData) (C : Finset (Charge D)) (n : ℤ) :
    Finite (CutoffIndex D C n) := by
  classical
  letI : Fintype C := Fintype.ofFinite C
  letI (a : C) : Finite {d : Exponent D //
      oscillatorEnergy d = n - chargeEnergy D a.1} := by
    letI := oscillatorLeFinite D (n - chargeEnergy D a.1).toNat
    apply Finite.of_injective (fun d =>
      (⟨d.1, by
        have hnonneg : 0 ≤ n - chargeEnergy D a.1 := by
          have := d.2
          omega
        have hd : (oscillatorEnergy d.1 : ℤ) =
            n - chargeEnergy D a.1 := by
          exact_mod_cast d.2
        have hnat : oscillatorEnergy d.1 =
            (n - chargeEnergy D a.1).toNat := by
          have hto : ((n - chargeEnergy D a.1).toNat : ℤ) =
              n - chargeEnergy D a.1 := Int.toNat_of_nonneg hnonneg
          have hz : (oscillatorEnergy d.1 : ℤ) =
              ((n - chargeEnergy D a.1).toNat : ℤ) := hd.trans hto.symm
          exact_mod_cast hz
        exact hnat.le⟩ :
        {d : Exponent D // oscillatorEnergy d ≤ (n - chargeEnergy D a.1).toNat}))
    intro x y h
    exact Subtype.ext (congrArg (fun z => z.1) h)
  letI : Finite (Σ a : C, {d : Exponent D //
      oscillatorEnergy d = n - chargeEnergy D a.1}) := by infer_instance
  let f : CutoffIndex D C n →
      Σ a : C, {d : Exponent D //
        oscillatorEnergy d = n - chargeEnergy D a.1} := fun a =>
    ⟨⟨a.1.1, a.2.1⟩, a.1.2, by
      have h := a.2.2
      dsimp [energy] at h ⊢
      omega⟩
  exact Finite.of_injective f (by
    rintro ⟨⟨ac, ae⟩, ha⟩ ⟨⟨bc, be⟩, hb⟩ h
    have hh := h
    simp only [f, Sigma.mk.injEq] at hh
    rcases hh with ⟨hc, hde⟩
    cases hc
    apply Subtype.ext
    exact Prod.ext rfl (congrArg Subtype.val (eq_of_heq hde)))

def cutoffBasis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ) :
    Module.Basis (CutoffIndex D C n) ℂ (cutoffActualGrade D H C n) :=
  Module.Basis.ofRepr (cutoffCoeffEquiv D H hHG hGH C n)

theorem cutoffActualGrade_finiteDimensional (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ) :
    FiniteDimensional ℂ (cutoffActualGrade D H C n) := by
  letI : Finite (CutoffIndex D C n) := cutoffIndex_finite D C n
  exact Module.Finite.of_basis (cutoffBasis D H hHG hGH C n)

def thetaRestriction (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (hCsym : ∀ a, a ∈ C → -a ∈ C) :
    cutoffActualGrade D H C n →ₗ[ℂ] cutoffActualGrade D H C n :=
  ((thetaLinear D).domRestrict (cutoffActualGrade D H C n)).codRestrict
    (cutoffActualGrade D H C n)
    (fun v => theta_mem_cutoff D H hHG hGH C n hCsym v.1 v.2)

private theorem thetaRestriction_basis_apply (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (hCsym : ∀ a, a ∈ C → -a ∈ C)
    (i : CutoffIndex D C n) :
    thetaRestriction D H hHG hGH C n hCsym
        (cutoffBasis D H hHG hGH C n i) =
      ⟨thetaLinear D ((cutoffBasis D H hHG hGH C n i).1),
        theta_mem_cutoff D H hHG hGH C n hCsym _
          ((cutoffBasis D H hHG hGH C n i).property)⟩ := by
  rfl

def cutoffThetaTrace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (hCsym : ∀ a, a ∈ C → -a ∈ C) : ℂ := by
  letI : Finite (CutoffIndex D C n) := cutoffIndex_finite D C n
  letI : Fintype (CutoffIndex D C n) := Fintype.ofFinite _
  exact LinearMap.trace ℂ (cutoffActualGrade D H C n)
    (thetaRestriction D H hHG hGH C n hCsym)

def neutralThetaTrace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (N : ℕ) : ℂ :=
  cutoffThetaTrace D H hHG hGH ({0} : Finset (Charge D)) (N : ℤ) (by
    intro a ha
    simp only [Finset.mem_singleton] at ha
    simpa [ha])

private theorem cutoffBasis_carrierCoeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (i : CutoffIndex D C n) :
    carrierCoeffEquiv D ((cutoffBasis D H hHG hGH C n i :
      cutoffActualGrade D H C n)) = Finsupp.single i.1 1 := by
  have hrepr : cutoffCoeffEquiv D H hHG hGH C n
      (cutoffBasis D H hHG hGH C n i) = Finsupp.single i 1 := by
    change (cutoffBasis D H hHG hGH C n).repr
        (cutoffBasis D H hHG hGH C n i) = _
    exact (cutoffBasis D H hHG hGH C n).repr_self i
  apply Finsupp.ext
  intro a
  by_cases ha : a.1 ∈ C ∧ energy D a = n
  · rw [← cutoffCoeffEquiv_apply D H hHG hGH C n
        (cutoffBasis D H hHG hGH C n i) ⟨a, ha⟩]
    rw [hrepr]
    by_cases h : i.1 = a
    · subst a
      simp
    · have hsub : i ≠ ⟨a, ha⟩ := by
        intro heq
        exact h (congrArg Subtype.val heq)
      simp [Finsupp.single_apply, h, hsub]
  · have hm0 := (cutoffBasis D H hHG hGH C n i).property
    have hm1 := Eq.mp (congrArg
      (fun P : Submodule ℂ (Carrier D) =>
        (cutoffBasis D H hHG hGH C n i).1 ∈ P)
      (cutoffActualGrade_eq_supported D H hHG hGH C n)) hm0
    change carrierCoeffEquiv D (cutoffBasis D H hHG hGH C n i).1 ∈
      Finsupp.supported ℂ ℂ {a : Label D | a.1 ∈ C ∧ energy D a = n} at hm1
    have hm := hm1
    rw [Finsupp.mem_supported'] at hm
    rw [hm a ha]
    have hia : i.1 ≠ a := by
      intro heq
      apply ha
      simpa [heq] using i.2
    simp [hia]

theorem cutoff_theta_trace_neutral_sum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (n : ℤ)
    (hCsym : ∀ a, a ∈ C → -a ∈ C)
    [Fintype (CutoffIndex D C n)] :
    LinearMap.trace ℂ (cutoffActualGrade D H C n)
        (thetaRestriction D H hHG hGH C n hCsym) =
      ∑ i : CutoffIndex D C n,
        if i.1.1 = 0 then (-1 : ℂ) ^ (occurrences D i.1.2).length else 0 := by
  classical
  letI : Finite (CutoffIndex D C n) :=
    Fintype.finite (inferInstance : Fintype (CutoffIndex D C n))
  rw [LinearMap.trace_eq_matrix_trace ℂ (cutoffBasis D H hHG hGH C n)]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply]
  change (∑ i, (cutoffCoeffEquiv D H hHG hGH C n
      (thetaRestriction D H hHG hGH C n hCsym
        (cutoffBasis D H hHG hGH C n i))) i) = _
  have htheta (i : CutoffIndex D C n) :
      carrierCoeffEquiv D (thetaLinear D
          (cutoffBasis D H hHG hGH C n i).1) =
        coefficientTheta D (Finsupp.single i.1 1) := by
    rw [show carrierCoeffEquiv D (thetaLinear D
        (cutoffBasis D H hHG hGH C n i).1) =
        coefficientTheta D (carrierCoeffEquiv D
          (cutoffBasis D H hHG hGH C n i).1) by
      exact LinearMap.congr_fun (carrierCoeff_theta D) _]
    rw [cutoffBasis_carrierCoeff]
  simp_rw [cutoffCoeffEquiv_apply]
  simp_rw [thetaRestriction_basis_apply]
  simp_rw [htheta]
  simp_rw [coefficientTheta_single]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hzero : i.1.1 = 0
  · have href : reflectedLabel D i.1 = i.1 := by
      apply Prod.ext
      · ext j
        simp [reflectedLabel, hzero]
      · rfl
    simp [occurrenceSign, Finsupp.single_apply, hzero, href]
  · have href : reflectedLabel D i.1 ≠ i.1 := by
      intro heq
      apply hzero
      have hc := congrArg Prod.fst heq
      ext j
      have hj : -(i.1.1 j) = i.1.1 j := by
        simpa [reflectedLabel] using congrFun hc j
      simpa using (eq_zero_of_neg_eq hj)
    simp [occurrenceSign, Finsupp.single_apply, hzero, href]

theorem cutoff_actual_theta_trace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (C : Finset (Charge D)) (hCsym : ∀ a, a ∈ C → -a ∈ C) (n : ℤ) :
    cutoffThetaTrace D H hHG hGH C n hCsym =
      if (0 : Charge D) ∈ C then
        (if hn : 0 ≤ n then signedThetaCoefficient D n.toNat else 0)
      else 0 := by
  classical
  letI : Finite (CutoffIndex D C n) := cutoffIndex_finite D C n
  letI : Fintype (CutoffIndex D C n) := Fintype.ofFinite _
  unfold cutoffThetaTrace
  rw [cutoff_theta_trace_neutral_sum D H hHG hGH C n hCsym]
  by_cases hzero : (0 : Charge D) ∈ C
  · simp only [hzero, ↓reduceIte]
    by_cases hn : 0 ≤ n
    · simp only [hn, ↓reduceDIte]
      letI : Finite (IntegerFiber D n.toNat) := integerFiber_finite D n.toNat
      letI : Fintype (IntegerFiber D n.toNat) := Fintype.ofFinite _
      let e : IntegerFiber D n.toNat → CutoffIndex D C n := fun d =>
        ⟨(0, d.1), by
          refine ⟨hzero, ?_⟩
          have hd : (oscillatorEnergy d.1 : ℤ) = n := by
            have hd' : (oscillatorEnergy d.1 : ℤ) = (n.toNat : ℤ) := by
              exact_mod_cast d.2
            exact hd'.trans (Int.toNat_of_nonneg hn)
          simpa [energy] using hd⟩
      let t : Finset (CutoffIndex D C n) :=
        Finset.univ.filter (fun i => i.1.1 = 0)
      have ht :
          (∑ i : CutoffIndex D C n,
            if i.1.1 = 0 then (-1 : ℂ) ^ (occurrences D i.1.2).length else 0) =
            (∑ i ∈ t, (-1 : ℂ) ^ (occurrences D i.1.2).length) := by
        simp [t, Finset.sum_filter]
      have hsum :
          (∑ d : IntegerFiber D n.toNat,
              (-1 : ℂ) ^ (occurrences D d.1).length) =
            (∑ i ∈ t, (-1 : ℂ) ^ (occurrences D i.1.2).length) := by
        apply Finset.sum_bij (s := (Finset.univ : Finset (IntegerFiber D n.toNat)))
          (t := t) (fun d _ => e d)
        · intro d hd
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rfl⟩
        · intro d₁ hd₁ d₂ hd₂ h
          apply Subtype.ext
          exact congrArg (fun z => z.2) (congrArg Subtype.val h)
        · intro i hi
          have hz : i.1.1 = 0 := Finset.mem_filter.mp hi |>.2
          let d : IntegerFiber D n.toNat := ⟨i.1.2, by
            have he := i.2.2
            have he' : (oscillatorEnergy i.1.2 : ℤ) = n := by
              simpa [energy, hz, chargeEnergy_zero] using he
            have he'' : (oscillatorEnergy i.1.2 : ℤ) = (n.toNat : ℤ) :=
              he'.trans (Int.toNat_of_nonneg hn).symm
            exact_mod_cast he''⟩
          refine ⟨d, Finset.mem_univ _, ?_⟩
          apply Subtype.ext
          apply Prod.ext
          · exact hz.symm
          · rfl
        · intro d hd
          rfl
      exact ht.trans hsum.symm
    · simp [hn]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hz : i.1.1 = 0
      · have he := i.2.2
        have he' : (oscillatorEnergy i.1.2 : ℤ) = n := by
          simpa [energy, hz, chargeEnergy_zero] using he
        simp [hz]
        omega
      · simp [hz]
  · simp only [hzero, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hz : i.1.1 = 0
    · exact False.elim (hzero (by simpa [hz] using i.2.1))
    · simp [hz]

theorem neutral_actual_theta_trace (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (N : ℕ) :
    neutralThetaTrace D H hHG hGH N = signedThetaCoefficient D N := by
  classical
  unfold neutralThetaTrace
  rw [cutoff_actual_theta_trace D H hHG hGH {0} (by
    intro a ha
    simp only [Finset.mem_singleton] at ha
    simpa [ha]) (N : ℤ)]
  simp

private theorem integer_fiber_sum (D : LatticeData) (N : ℕ) (q : ℂ) :
    (∑' d : IntegerFiber D N, signedIntegerMonomial q d.1) =
      signedThetaCoefficient D N * q ^ N := by
  classical
  rw [tsum_fintype]
  rw [signedThetaCoefficient]
  simp only [signedIntegerMonomial, integerEnergy]
  simp_rw [show ∀ d : IntegerFiber D N,
      q ^ Finsupp.weight (fun x : (Fin D.rank × ℕ) => x.2 + 1) d.1 = q ^ N
    by intro d; change q ^ oscillatorEnergy d.1 = q ^ N; rw [d.2]]
  rw [← Finset.sum_mul]
  simp [occupationCount, occurrences]

theorem actual_theta_trace_series (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    {q : ℂ} (hq : ‖q‖ < 1) :
    (∀ N : ℕ, neutralThetaTrace D H hHG hGH N = signedThetaCoefficient D N) ∧
    Summable (fun N : ℕ => ‖signedThetaCoefficient D N * q ^ N‖) ∧
    HasSum (fun N : ℕ => signedThetaCoefficient D N * q ^ N)
      (∑' d : Exponent D, signedIntegerMonomial q d) := by
  classical
  have hsum := (summable_norm_signed_integer_occupations (Fin D.rank) hq).of_norm
  have hgroup := hsum.hasSum.tsum_fiberwise (integerEnergy (Fin D.rank))
  have hgroup' : HasSum (fun N : ℕ =>
      ∑' d : IntegerFiber D N, signedIntegerMonomial q d.1)
      (∑' d : Exponent D, signedIntegerMonomial q d) := by
    change HasSum (fun N : ℕ =>
      ∑' d : IntegerFiber D N, signedIntegerMonomial q d.1)
      (∑' d : Exponent D, signedIntegerMonomial q d)
    exact hgroup
  have hcoeff : HasSum (fun N : ℕ => signedThetaCoefficient D N * q ^ N)
      (∑' d : Exponent D, signedIntegerMonomial q d) :=
    hgroup'.congr_fun (fun N => by
      rw [integer_fiber_sum D N q])
  have hnormGroup : HasSum (fun N : ℕ =>
      ∑' d : IntegerFiber D N, ‖signedIntegerMonomial q d.1‖)
      (∑' d : Exponent D, ‖signedIntegerMonomial q d‖) := by
    have h := (summable_norm_signed_integer_occupations (Fin D.rank) hq).hasSum
    change HasSum (fun N : ℕ =>
      ∑' d : IntegerFiber D N, ‖signedIntegerMonomial q d.1‖)
      (∑' d : Exponent D, ‖signedIntegerMonomial q d‖)
    exact h.tsum_fiberwise (integerEnergy (Fin D.rank))
  have hnormCoeff : Summable
      (fun N : ℕ => ‖signedThetaCoefficient D N * q ^ N‖) := by
    refine (HasSum.summable hnormGroup).of_nonneg_of_le ?_ ?_
    · intro N
      exact norm_nonneg _
    · intro N
      have hle : ‖∑' d : IntegerFiber D N,
          signedIntegerMonomial q d.1‖ ≤
          ∑' d : IntegerFiber D N, ‖signedIntegerMonomial q d.1‖ := by
        simp only [tsum_fintype]
        exact norm_sum_le _ _
      rw [← integer_fiber_sum D N q]
      exact hle
  refine ⟨?_, ?_, ?_⟩
  · intro N
    exact neutral_actual_theta_trace D H hHG hGH N
  · exact hnormCoeff
  · exact hcoeff

/- The eta/S endpoint remains open until its proof terms are available. The
restriction above is the actual operator on the actual finite cutoff, with no
scalar or regularized proxy. -/

end D5.S3.VertexAlgebra.LatticeThetaCharacter
