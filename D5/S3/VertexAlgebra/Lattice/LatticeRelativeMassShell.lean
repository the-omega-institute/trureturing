/- GID: D5/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/LatticeRelativeMassShell
   mirror-E: none(waiver:algebraic-original-relative-mass-shell)
   anchors: []
   utility: none
   digest: The literal original fixed-momentum relative mass shell has a finite tensor basis and is preserved by the actual total BRST charge. -/

/- The fixed-momentum kinematic component on the ORIGINAL
`LatticeMatterGhostCoupling.State D = Carrier D ⊗ Fock`.  This module proves
the literal kernel/support/basis and finite-dimensional endpoints needed by
the relative shell.  It does not assert a no-ghost theorem or positivity.
-/

import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.Lattice.LatticeMatterGhostCoupling
import D5.S3.VertexAlgebra.Lattice.LatticeBRSTWard
import D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open scoped BigOperators TensorProduct

namespace D5.S3.VertexAlgebra.LatticeRelativeMassShell

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeMatterGhostCoupling
open LatticeSugawaraVirasoro
open D5.S3.VertexAlgebra.LatticeBRST
open D5.S3.Quantum.Fermionic.CountableOccupationFock
open D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy
  (relativeEnergy relativeEnergy_nonneg level level_cast L_zero_ket
    L_zero_coefficient RelativeLevel
    relative_level_coeff_iff relative_level_support)

noncomputable section

/-- Charge, original polynomial exponent, and original finite ghost occupation. -/
abbrev TensorLabel (D : LatticeData) := Label D × Finset ℕ

private def ghostBasis : Module.Basis (Finset ℕ) ℂ Fock :=
  Finsupp.basisSingleOne

/-- The tensor product of the ORIGINAL carrier monomials and occupation kets. -/
def tensorBasis (D : LatticeData) : Module.Basis (TensorLabel D) ℂ (State D) :=
  (carrierBasis D).tensorProduct ghostBasis

/-- Actual tensor coefficients, not a new representation of the state space. -/
def tensorCoeffEquiv (D : LatticeData) : State D ≃ₗ[ℂ] (TensorLabel D →₀ ℂ) :=
  (tensorBasis D).repr

def coeff (D : LatticeData) (x : State D) (i : TensorLabel D) : ℂ :=
  tensorCoeffEquiv D x i

@[simp] theorem tensorBasis_apply (D : LatticeData) (i : TensorLabel D) :
    tensorBasis D i =
      Finsupp.single i.1.1 (MvPolynomial.monomial i.1.2 1) ⊗ₜ[ℂ] ket i.2 := by
  rcases i with ⟨l, S⟩
  simp [tensorBasis, ghostBasis, carrierBasis_apply, ket]

@[simp] private theorem coeff_zero (D : LatticeData) (i : TensorLabel D) :
    coeff D 0 i = 0 := by
  change (tensorCoeffEquiv D 0) i = 0
  rw [(tensorCoeffEquiv D).map_zero]
  exact Finsupp.zero_apply

@[simp] private theorem coeff_add (D : LatticeData) (x y : State D)
    (i : TensorLabel D) : coeff D (x + y) i = coeff D x i + coeff D y i := by
  change (tensorCoeffEquiv D (x + y)) i =
    (tensorCoeffEquiv D x) i + (tensorCoeffEquiv D y) i
  rw [(tensorCoeffEquiv D).map_add]
  exact Finsupp.add_apply _ _ _

@[simp] private theorem coeff_smul (D : LatticeData) (z : ℂ) (x : State D)
    (i : TensorLabel D) : coeff D (z • x) i = z * coeff D x i := by
  change (tensorCoeffEquiv D (z • x)) i = z * (tensorCoeffEquiv D x) i
  rw [(tensorCoeffEquiv D).map_smul]
  rfl

/-- These coordinates are exactly the ORIGINAL charge-polynomial coefficients. -/
theorem coeff_tmul (D : LatticeData) (v : Carrier D) (w : Fock)
    (i : TensorLabel D) :
    coeff D (v ⊗ₜ[ℂ] w) i = carrierCoeffEquiv D v i.1 * w i.2 := by
  rcases i with ⟨l, S⟩
  change ((carrierBasis D).tensorProduct ghostBasis).repr (v ⊗ₜ[ℂ] w) (l,S) = _
  rw [Module.Basis.tensorProduct_repr_tmul_apply]
  change w S * carrierCoeffEquiv D v l = carrierCoeffEquiv D v l * w S
  exact mul_comm _ _

/-- In particular, the fixed charge below refers to the original Finsupp charge. -/
theorem coeff_tmul_original (D : LatticeData) (v : Carrier D) (w : Fock)
    (a : Charge D) (d : Exponent D) (S : Finset ℕ) :
    coeff D (v ⊗ₜ[ℂ] w) ((a,d),S) = (v a).coeff d * w S := by
  rw [coeff_tmul]
  rfl

private def ghostSlices (D : LatticeData) : State D ≃ₗ[ℂ] (Label D →₀ Fock) :=
  by
    classical
    exact TensorProduct.equivFinsuppOfBasisLeft (carrierBasis D)

private def ghostSlice (D : LatticeData) (l : Label D) : State D →ₗ[ℂ] Fock :=
  (Finsupp.lapply l).comp (ghostSlices D).toLinearMap

@[simp] private theorem ghostSlice_tmul (D : LatticeData) (l : Label D)
    (v : Carrier D) (w : Fock) :
    ghostSlice D l (v ⊗ₜ[ℂ] w) = carrierCoeffEquiv D v l • w := by
  classical
  change TensorProduct.equivFinsuppOfBasisLeft (carrierBasis D)
    (v ⊗ₜ[ℂ] w) l = _
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply (carrierBasis D) v w l

@[simp] private theorem ghostSlice_coeff (D : LatticeData) (l : Label D)
    (x : State D) (S : Finset ℕ) : ghostSlice D l x S = coeff D x (l,S) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      rw [ghostSlice_tmul, coeff_tmul]
      simp only [Finsupp.smul_apply, smul_eq_mul]
  | add x y hx hy =>
      simp only [map_add, Finsupp.add_apply, coeff_add, hx, hy]

private theorem ghostSlice_ghostB (D : LatticeData) (l : Label D) (x : State D) :
    ghostSlice D l (ghostB D 0 x) =
      D5.S3.Quantum.Fermionic.BcGhostFock.b 0 (ghostSlice D l x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v w => simp [ghostB]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Literal tensor b_0 kernel; no replacement relative subspace is postulated. -/
theorem ghostB_zero_iff (D : LatticeData) (x : State D) :
    ghostB D 0 x = 0 ↔
      ∀ i : TensorLabel D, 3 ∈ i.2 → coeff D x i = 0 := by
  constructor
  · intro hx i hi
    have hs : D5.S3.Quantum.Fermionic.BcGhostFock.b 0 (ghostSlice D i.1 x) = 0 := by
      rw [← ghostSlice_ghostB, hx, map_zero]
    simpa only [ghostSlice_coeff] using
      (D5.S3.Quantum.Fermionic.BcGhostQuartetCount.b0_eq_zero_iff_coefficients _).mp hs i.2 hi
  · intro hx
    apply (ghostSlices D).injective
    have hzero : ghostSlices D (0 : State D) = 0 := (ghostSlices D).map_zero
    rw [hzero]
    ext l S
    change ghostSlice D l (ghostB D 0 x) S = (0 : Fock) S
    rw [ghostSlice_ghostB]
    have hs : D5.S3.Quantum.Fermionic.BcGhostFock.b 0 (ghostSlice D l x) = 0 := by
      apply (D5.S3.Quantum.Fermionic.BcGhostQuartetCount.b0_eq_zero_iff_coefficients _).mpr
      intro T hT
      rw [ghostSlice_coeff]
      exact hx (l,T) hT
    rw [hs]

/-- Integer eigenvalue of the ACTUAL unshifted total zero mode. -/
def totalEnergy (D : LatticeData) (i : TensorLabel D) : ℤ :=
  energy D i.1 + D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.energy i.2

/-- The actual matter zero mode plus the actual ghost Virasoro zero mode. -/
/- The shell uses the exact accepted matter-plus-ghost zero mode.  This is
   only a name for the existing operator at index zero, never a replacement
   grading definition. -/
abbrev totalL0 (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) :
    Module.End ℂ (State D) := matterMode D H 0 + ghostVirasoro D 0

theorem totalL0_basis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (i : TensorLabel D) :
    totalL0 D H (tensorBasis D i) = (totalEnergy D i : ℂ) • tensorBasis D i := by
  have ht : tensorBasis D i = carrierBasis D i.1 ⊗ₜ[ℂ] ket i.2 := by
    rcases i with ⟨l,S⟩
    simp [tensorBasis, ghostBasis, ket]
  simp only [ht, totalL0, LinearMap.add_apply, matterMode, ghostVirasoro,
    TensorProduct.map_tmul, LinearMap.id_apply,
    actualL0_basis D H hHG hGH, L_zero_ket]
  change (energy D i.1 : ℂ) • (carrierBasis D i.1 ⊗ₜ[ℂ] ket i.2) +
    carrierBasis D i.1 ⊗ₜ[ℂ]
      ((D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.energy i.2 : ℂ) • ket i.2) = _
  rw [TensorProduct.tmul_smul, ← add_smul]
  simp only [totalEnergy, Int.cast_add]

/-- All-state diagonal formula, directly consuming both original coefficient formulas. -/
theorem totalL0_coeff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) (i : TensorLabel D) :
    coeff D (totalL0 D H x) i = (totalEnergy D i : ℂ) * coeff D x i := by
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
      simp only [totalL0, LinearMap.add_apply, matterMode, ghostVirasoro,
        TensorProduct.map_tmul, LinearMap.id_apply, coeff_add, coeff_tmul,
        actualL0_coeff D H hHG hGH, L_zero_coefficient, totalEnergy, Int.cast_add]
      ring
  | add x y hx hy =>
      simp only [map_add, coeff_add, hx, hy, mul_add]

theorem totalL0_zero_iff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (x : State D) :
    totalL0 D H x = 0 ↔
      ∀ i : TensorLabel D, coeff D x i ≠ 0 → totalEnergy D i = 0 := by
  constructor
  · intro hx i hi
    have hc := congrArg (fun y : State D => coeff D y i) hx
    rw [totalL0_coeff D H hHG hGH, coeff_zero] at hc
    have he : (totalEnergy D i : ℂ) = 0 := (mul_eq_zero.mp hc).resolve_right hi
    exact_mod_cast he
  · intro hx
    apply (tensorCoeffEquiv D).injective
    have hzero : tensorCoeffEquiv D (0 : State D) = 0 :=
      (tensorCoeffEquiv D).map_zero
    rw [hzero]
    ext i
    change coeff D (totalL0 D H x) i = 0
    rw [totalL0_coeff D H hHG hGH]
    by_cases hi : coeff D x i = 0
    · simp [hi]
    · rw [hx i hi]
      simp

/-- Fixed original charge-coefficient support; this imposes no oscillator cutoff. -/
def fixedMomentum (D : LatticeData) (a : Charge D) : Submodule ℂ (State D) :=
  (Finsupp.supported ℂ ℂ {i : TensorLabel D | i.1.1 = a}).comap
    (tensorCoeffEquiv D).toLinearMap

theorem mem_fixedMomentum_iff (D : LatticeData) (a : Charge D) (x : State D) :
    x ∈ fixedMomentum D a ↔
      ∀ i : TensorLabel D, i.1.1 ≠ a → coeff D x i = 0 := by
  change tensorCoeffEquiv D x ∈ Finsupp.supported ℂ ℂ _ ↔ _
  rw [Finsupp.mem_supported']
  rfl

private theorem summand_mem_fixedMomentum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D)
    (d : Exponent D) (S : Finset ℕ) (m : ℤ) :
    summand D H m (tensorBasis D ((a,d),S)) ∈ fixedMomentum D a := by
  apply (mem_fixedMomentum_iff D a _).mpr
  intro i hi
  rcases i with ⟨⟨q,e⟩,T⟩
  simp only [summand, tensorBasis_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [sugawaraMode_single_sector]
  rw [coeff_tmul_original]
  simp [hi]

private theorem ghostCharge_mem_fixedMomentum (D : LatticeData)
    (a : Charge D) (d : Exponent D) (S : Finset ℕ) :
    ghostCharge D (tensorBasis D ((a,d),S)) ∈ fixedMomentum D a := by
  apply (mem_fixedMomentum_iff D a _).mpr
  intro i hi
  rcases i with ⟨⟨q,e⟩,T⟩
  simp only [ghostCharge, tensorBasis_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [coeff_tmul_original]
  simp [hi]

theorem fixedMomentum_eq_span (D : LatticeData) (a : Charge D) :
    fixedMomentum D a =
      Submodule.span ℂ (tensorBasis D '' {i : TensorLabel D | i.1.1 = a}) := by
  ext x
  change tensorCoeffEquiv D x ∈ Finsupp.supported ℂ ℂ _ ↔ _
  rw [Finsupp.mem_supported]
  change ((tensorCoeffEquiv D x).support : Set (TensorLabel D)) ⊆
    {i : TensorLabel D | i.1.1 = a} ↔ _
  exact (tensorBasis D).mem_span_image.symm

private theorem T_mem_fixedMomentum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (a : Charge D) (d : Exponent D) (S : Finset ℕ) :
    T D H (tensorBasis D ((a,d),S)) ∈ fixedMomentum D a := by
  change (∑ᶠ m : ℤ, summand D H m (tensorBasis D ((a,d),S))) ∈
    fixedMomentum D a
  apply finsum_induction _ (fixedMomentum D a).zero_mem
    (fun _ _ => (fixedMomentum D a).add_mem)
  intro m
  exact summand_mem_fixedMomentum D H a d S m

theorem totalCharge_mem_fixedMomentum (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D)
    {x : State D} (hx : x ∈ fixedMomentum D a) :
    totalCharge D H x ∈ fixedMomentum D a := by
  rw [fixedMomentum_eq_span D a] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨i, hi, rfl⟩
      rcases i with ⟨⟨q,e⟩,S⟩
      have hqa : q = a := hi
      subst q
      apply (fixedMomentum D a).add_mem
      · exact T_mem_fixedMomentum D H a e S
      · exact ghostCharge_mem_fixedMomentum D a e S
  | zero => simpa using (fixedMomentum D a).zero_mem
  | add x y _ _ hx hy =>
      simpa only [map_add] using (fixedMomentum D a).add_mem hx hy
  | smul z x _ hx =>
      simpa only [map_smul] using (fixedMomentum D a).smul_mem z hx

/-- DEFINITION by fixed charge and the TWO LITERAL actual-operator kernels. -/
def relativeMassShell (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Charge D) :
    Submodule ℂ (State D) :=
  (fixedMomentum D a ⊓ LinearMap.ker (ghostB D 0)) ⊓ LinearMap.ker (totalL0 D H)

private theorem totalEnergy_eq_zero_iff (D : LatticeData) (a : Charge D)
    (i : TensorLabel D) (hi : i.1.1 = a) :
    totalEnergy D i = 0 ↔
      (oscillatorEnergy i.1.2 : ℤ) + relativeEnergy i.2 = 1 - chargeEnergy D a := by
  simp only [totalEnergy, energy,
    D5.S3.Quantum.Fermionic.BcGhostRelativeEnergy.relativeEnergy, hi]
  omega

/-- BOTH directions for arbitrary actual states, with an integer shell equation. -/
theorem mem_relativeMassShell_iff (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (x : State D) :
    x ∈ relativeMassShell D H a ↔
      ∀ i : TensorLabel D, coeff D x i ≠ 0 →
        i.1.1 = a ∧ 3 ∉ i.2 ∧
          (oscillatorEnergy i.1.2 : ℤ) + relativeEnergy i.2 = 1 - chargeEnergy D a := by
  constructor
  · rintro ⟨⟨ha,hb⟩,hL⟩ i hi
    have hcharge : i.1.1 = a := by
      by_contra hne
      exact hi ((mem_fixedMomentum_iff D a x).mp ha i hne)
    have hghost : 3 ∉ i.2 := by
      intro h3
      exact hi ((ghostB_zero_iff D x).mp hb i h3)
    have henergy := (totalL0_zero_iff D H hHG hGH x).mp hL i hi
    exact ⟨hcharge, hghost, (totalEnergy_eq_zero_iff D a i hcharge).mp henergy⟩
  · intro hx
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply (mem_fixedMomentum_iff D a x).mpr
      intro i hi
      by_contra hne
      exact hi (hx i hne).1
    · apply (ghostB_zero_iff D x).mpr
      intro i h3
      by_contra hne
      exact (hx i hne).2.1 h3
    · apply (totalL0_zero_iff D H hHG hGH x).mpr
      intro i hi
      exact (totalEnergy_eq_zero_iff D a i (hx i hi).1).mpr (hx i hi).2.2

/- The original total BRST charge preserves the literal fixed-momentum,
   b₀-kernel, total-L₀ kernel intersection.  The two kernel steps consume the
   native Ward and covariance identities at r = 0. -/
theorem totalCharge_mem_relativeMassShell (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) {x : State D} (hx : x ∈ relativeMassShell D H a) :
    totalCharge D H x ∈ relativeMassShell D H a := by
  rcases hx with ⟨⟨hfixed, hb⟩, hL⟩
  change ghostB D 0 x = 0 at hb
  change matterMode D H 0 x + ghostVirasoro D 0 x = 0 at hL
  have hL' : (matterMode D H 0 + ghostVirasoro D 0) x = 0 := by
    simpa only [LinearMap.add_apply] using hL
  refine ⟨⟨totalCharge_mem_fixedMomentum D H a hfixed, ?_⟩, ?_⟩
  · have hw := LinearMap.congr_fun (total_ward_b D H 0) x
    simp only [LinearMap.add_apply, Module.End.mul_apply] at hw
    change totalCharge D H (ghostB D 0 x) +
      ghostB D 0 (totalCharge D H x) =
      matterMode D H 0 x + ghostVirasoro D 0 x at hw
    rw [hb, map_zero, hL] at hw
    change ghostB D 0 (totalCharge D H x) = 0
    simpa using hw
  · have hc := LinearMap.congr_fun (total_covariance D H hHG hGH 0) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
    have hc' : totalCharge D H ((matterMode D H 0 + ghostVirasoro D 0) x) -
        (matterMode D H 0 + ghostVirasoro D 0) (totalCharge D H x) = 0 := by
      simpa using hc
    rw [hL', map_zero, zero_sub] at hc'
    change (matterMode D H 0 + ghostVirasoro D 0) (totalCharge D H x) = 0
    exact neg_eq_zero.mp hc'

/-- Exact allowed indices; finiteness is PROVED below, not part of this definition. -/
def allowedLabels (D : LatticeData) (a : Charge D) : Set (TensorLabel D) :=
  {i | i.1.1 = a ∧ 3 ∉ i.2 ∧
    (oscillatorEnergy i.1.2 : ℤ) + relativeEnergy i.2 = 1 - chargeEnergy D a}

abbrev ShellIndex (D : LatticeData) (a : Charge D) :=
  {i : TensorLabel D // i ∈ allowedLabels D a}

theorem relativeMassShell_eq_supported (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) :
    relativeMassShell D H a =
      (Finsupp.supported ℂ ℂ (allowedLabels D a)).comap
        (tensorCoeffEquiv D).toLinearMap := by
  ext x
  rw [mem_relativeMassShell_iff D H hHG hGH]
  change (∀ i, coeff D x i ≠ 0 → i ∈ allowedLabels D a) ↔
    tensorCoeffEquiv D x ∈ Finsupp.supported ℂ ℂ (allowedLabels D a)
  rw [Finsupp.mem_supported']
  constructor
  · intro hx i hi
    by_contra hne
    exact hi (hx i hne)
  · intro hx i hi
    by_contra hbad
    exact hi (hx i hbad)

/-- Spanning is obtained from the original tensor basis, after kernel identification. -/
theorem relativeMassShell_eq_span (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) :
    relativeMassShell D H a =
      Submodule.span ℂ (tensorBasis D '' allowedLabels D a) := by
  rw [relativeMassShell_eq_supported D H hHG hGH]
  ext x
  change ((tensorCoeffEquiv D x).support : Set (TensorLabel D)) ⊆ allowedLabels D a ↔ _
  exact (tensorBasis D).mem_span_image.symm

/-- Genuine coefficient equivalence on the actual kernel intersection. -/
def shellCoeffEquiv (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) :
    relativeMassShell D H a ≃ₗ[ℂ] (ShellIndex D a →₀ ℂ) :=
  (LinearEquiv.ofEq _ _ (relativeMassShell_eq_supported D H hHG hGH a)).trans
    ((LinearEquiv.ofSubmodule' (tensorCoeffEquiv D)
      (Finsupp.supported ℂ ℂ (allowedLabels D a))).trans
        (Finsupp.supportedEquivFinsupp (allowedLabels D a)))

def shellBasis (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) :
    Module.Basis (ShellIndex D a) ℂ (relativeMassShell D H a) :=
  Module.Basis.ofRepr (shellCoeffEquiv D H hHG hGH a)

/-- Its vectors really are the allowed ORIGINAL tensor basis vectors. -/
theorem shellBasis_coe (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (i : ShellIndex D a) :
    (shellBasis D H hHG hGH a i : State D) = tensorBasis D i.1 := by
  apply (tensorCoeffEquiv D).injective
  change tensorCoeffEquiv D ((tensorCoeffEquiv D).symm
    ((Finsupp.supportedEquivFinsupp (R := ℂ) (M := ℂ) (allowedLabels D a)).symm
      (Finsupp.single i 1) : TensorLabel D →₀ ℂ)) =
        (tensorBasis D).repr (tensorBasis D i.1)
  rw [LinearEquiv.apply_symm_apply, Module.Basis.repr_self]
  exact Finsupp.supportedEquivFinsupp_symm_single (allowedLabels D a) i 1

/-- The prescribed nonnegative cutoff, including the empty-space case. -/
def massShellCutoff (D : LatticeData) (a : Charge D) : ℕ :=
  (1 - chargeEnergy D a).toNat

theorem massShellCutoff_cast (D : LatticeData) (a : Charge D)
    (ha : chargeEnergy D a ≤ 1) :
    (massShellCutoff D a : ℤ) = 1 - chargeEnergy D a := by
  exact Int.toNat_of_nonneg (by omega)

private theorem allowed_charge_le_one (D : LatticeData) (a : Charge D)
    (i : TensorLabel D) (hi : i ∈ allowedLabels D a) : chargeEnergy D a ≤ 1 := by
  have hg := relativeEnergy_nonneg i.2
  have ho : (0 : ℤ) ≤ (oscillatorEnergy i.1.2 : ℤ) := by omega
  have he := hi.2.2
  omega

/-- This supplies the GENUINE RelativeLevel premise of the imported support lemma. -/
private theorem ket_relativeLevel (S : Finset ℕ) (h3 : 3 ∉ S) :
    RelativeLevel (level S) (ket S) := by
  apply (relative_level_coeff_iff (level S) (ket S)).mpr
  constructor
  · intro T hT
    have hST : S ≠ T := by
      rintro rfl
      exact h3 hT
    simp [ket, hST]
  · intro T hT
    by_cases hTS : T = S
    · subst T
      exact (level_cast S).symm
    · simp [ket, hTS, Ne.symm hTS] at hT

private theorem allowed_bounds (D : LatticeData) (a : Charge D)
    (i : TensorLabel D) (hi : i ∈ allowedLabels D a) :
    oscillatorEnergy i.1.2 ≤ massShellCutoff D a ∧
      i.2 ⊆ Finset.range (2 * massShellCutoff D a + 4) := by
  have hc := massShellCutoff_cast D a (allowed_charge_le_one D a i hi)
  have hg := relativeEnergy_nonneg i.2
  have he := hi.2.2
  have ho : oscillatorEnergy i.1.2 ≤ massShellCutoff D a := by omega
  have hlcast := level_cast i.2
  have hl : level i.2 ≤ massShellCutoff D a := by omega
  have hket := ket_relativeLevel i.2 hi.2.1
  have hs : i.2 ⊆ Finset.range (2 * level i.2 + 4) :=
    relative_level_support (level i.2) (ket i.2) hket i.2 (by simp [ket])
  refine ⟨ho, ?_⟩
  intro j hj
  have hj' := Finset.mem_range.mp (hs hj)
  exact Finset.mem_range.mpr (by omega)

/-- The actual mass-shell space VANISHES above charge energy one. -/
theorem relativeMassShell_eq_bot_of_one_lt (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (ha : 1 < chargeEnergy D a) :
    relativeMassShell D H a = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  rw [Submodule.mem_bot]
  apply (tensorCoeffEquiv D).injective
  have hzero : tensorCoeffEquiv D (0 : State D) = 0 :=
    (tensorCoeffEquiv D).map_zero
  rw [hzero]
  ext i
  change coeff D x i = 0
  by_contra hi
  have hallowed : i ∈ allowedLabels D a :=
    (mem_relativeMassShell_iff D H hHG hGH a x).mp hx i hi
  have hc := allowed_charge_le_one D a i hallowed
  omega

/-- Explicit support bounds on every nonzero ORIGINAL tensor coefficient. -/
theorem coefficient_support_bound (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) (x : State D) (hx : x ∈ relativeMassShell D H a)
    (i : TensorLabel D) (hi : coeff D x i ≠ 0) :
    i.1.1 = a ∧ oscillatorEnergy i.1.2 ≤ massShellCutoff D a ∧
      i.2 ⊆ Finset.range (2 * massShellCutoff D a + 4) := by
  have hallowed : i ∈ allowedLabels D a :=
    (mem_relativeMassShell_iff D H hHG hGH a x).mp hx i hi
  exact ⟨hallowed.1, allowed_bounds D a i hallowed⟩

/-- Finiteness is independent of H and of ANY sign condition on the Gram form.
The only oscillator finiteness input is oscillatorLeFinite D N.
The only ghost support input is relative_level_support with ket_relativeLevel.
-/
theorem shellIndex_finite (D : LatticeData) (a : Charge D) :
    Finite (ShellIndex D a) := by
  classical
  by_cases ha : chargeEnergy D a ≤ 1
  · letI := oscillatorLeFinite D (massShellCutoff D a)
    let B : Finset (Finset ℕ) :=
      (Finset.range (2 * massShellCutoff D a + 4)).powerset
    let encode (i : ShellIndex D a) :
        {d : Exponent D // oscillatorEnergy d ≤ massShellCutoff D a} ×
          {S : Finset ℕ // S ∈ B} :=
      (⟨i.1.1.2, (allowed_bounds D a i.1 i.2).1⟩,
       ⟨i.1.2, Finset.mem_powerset.mpr (allowed_bounds D a i.1 i.2).2⟩)
    have hinj : Function.Injective encode := by
      intro i j hij
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · exact i.2.1.trans j.2.1.symm
        · exact congrArg Subtype.val (congrArg Prod.fst hij)
      · exact congrArg Subtype.val (congrArg Prod.snd hij)
    exact Finite.of_injective encode hinj
  · haveI : IsEmpty (ShellIndex D a) :=
      ⟨fun i => ha (allowed_charge_le_one D a i.1 i.2)⟩
    infer_instance

/-- Genuine finite dimensionality of the literal kernel intersection, uniform
in all fixed charges, with only the actual two-sided inverse assumptions. -/
theorem relativeMassShell_finiteDimensional (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (hHG : H * gramComplex D = 1) (hGH : gramComplex D * H = 1)
    (a : Charge D) : FiniteDimensional ℂ (relativeMassShell D H a) := by
  letI := shellIndex_finite D a
  exact Module.Finite.of_basis (shellBasis D H hHG hGH a)

end
end D5.S3.VertexAlgebra.LatticeRelativeMassShell
