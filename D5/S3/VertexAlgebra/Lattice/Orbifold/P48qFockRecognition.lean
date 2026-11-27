/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFockRecognition
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Recognition of the P48q state from the native Weyl and charge relations. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qCyclicOscillator
import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedGroundRecognition
import OmegaBuild.Commands

/-!
Recognition of the P48q finite-support polynomial Fock representation for
the current and charge generators of Bakalov–Kac, arXiv:math/0402315v3,
§4.3. The target vacuum has the native moving-lattice character, and its
charge translates lie in the independent joint eigenspaces of the fixed
Cartan zero modes.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFockRecognition

open LatticeGeneratingFieldLocality (Charge)
open P48qMomentumEnergy (Fixed chargeVector fixedGram pairing_physicalMomentum physicalMomentum)
open P48qTwistedChargeAction (Momentum lattice g multiplier liftPhase movingExact U)
open P48qThirdTwistedField (Cartan Fock Mode State creator annihilatorDual fixedDualBases
  chargePhase U_ground)
open P48qTwistedHeisenberg (mode mode_zero_apply scale)
open P48qTwistedFockIrreducibility (chargeOperator chargeOperator_single
  fixedCartan_separates negative_mode_single positive_mode_single)
open ThirdEigenspacePairing (p48qForm)
open ThirdTwistedGroundRecognition (recognitionMap recognitionMap_single)
open MvPolynomial
open scoped BigOperators

noncomputable section

local notation "s" => ThirdTwistedChargeAction.chooseSection lattice g
local notation "N" => ThirdTwistedChargeAction.N lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "χ" => ThirdTwistedChargeAction.chi lattice g multiplier liftPhase movingExact
local notation "cre" i => mode (creator fixedDualBases i) (Int.negSucc i.2)
local notation "ann" i => mode (annihilatorDual fixedDualBases i) (Int.ofNat (i.2 + 1))

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- The target joint eigenspace with the native fixed Cartan weight at `p`. -/
def jointWeightSpace (Z : Fixed → Module.End ℂ M) (p : Momentum) : Submodule ℂ M :=
  ⨅ h : Fixed, (Z h).eigenspace (fixedGram h (physicalMomentum p))

/-- The native weights distinguish the momentum sectors in any target. -/
theorem jointWeightSpace_iSupIndep (Z : Fixed → Module.End ℂ M) :
    iSupIndep (jointWeightSpace Z) := by
  have hinj : Function.Injective (fun (p : Momentum) (h : Fixed) =>
      fixedGram h (physicalMomentum p)) := by
    intro p q heq
    by_contra hpq
    obtain ⟨h, hsep⟩ := fixedCartan_separates hpq
    exact hsep (congrFun heq h)
  exact (iSupIndep.iInf (fun h => (Z h).eigenspace)
    (fun h => (Z h).eigenspaces_iSupIndep)).comp hinj

private theorem fock_map_eq_of_one (A : Mode → Module.End ℂ M)
    {F G : Fock →ₗ[ℂ] M} (hF : ∀ i P, F (X i * P) = A i (F P))
    (hG : ∀ i P, G (X i * P) = A i (G P)) (hOne : F 1 = G 1) : F = G := by
  apply LinearMap.ext
  intro P
  induction P using MvPolynomial.induction_on with
  | C c =>
    rw [show C c = c • (1 : Fock) by rw [smul_eq_C_mul, mul_one], map_smul, map_smul, hOne]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
  | mul_X P i hP => rw [mul_comm P (X i), hF, hG, hP]

/-- A nonzero target vacuum with the native moving character generates the
native charge orbit of cyclic oscillator spaces. Independence separates their
finite sum, and irreducibility makes it the entire target. The positive
operators `B` have the physical frequency in their Weyl bracket. -/
private theorem recognize_irreducible_of_subspaces
    (A B : Mode → Module.End ℂ M) (T : Charge lattice → Module.End ℂ M) (w : M)
    (W : Momentum → Submodule ℂ M)
    (hA : ∀ i j, Commute (A i) (A j))
    (hWeyl : ∀ i j, ⁅B i, A j⁆ = if i = j then scale i.2 • 1 else 0)
    (hAT : ∀ i a, Commute (A i) (T a))
    (hBT : ∀ i a, Commute (B i) (T a))
    (hUnit : T 0 = LinearMap.id)
    (hMul : ∀ a b, (T a).comp (T b) = (multiplier.c a b : ℂ) • T (a + b))
    (hw : w ≠ 0) (hVac : ∀ i, B i w = 0)
    (hχ : ∀ m : ThirdTwistedChargeAction.Moving lattice g, T m.1 w = (χ m : ℂ) • w)
    (hWeight : ∀ p, T ((s).lift p) w ∈ W p)
    (hStable : ∀ p i x, x ∈ W p → A i x ∈ W p)
    (hIndep : iSupIndep W)
    (hIrred : ∀ S : Submodule ℂ M,
      (∀ i x, x ∈ S → A i x ∈ S) → (∀ i x, x ∈ S → B i x ∈ S) →
      (∀ a x, x ∈ S → T a x ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ e : State ≃ₗ[ℂ] M,
      (∀ p, e (Finsupp.single p 1) = T ((s).lift p) w) ∧
      (∀ p P, e (Finsupp.single p P) ∈ W p) ∧
      (∀ i : Mode, (A i).comp e.toLinearMap = e.toLinearMap.comp (cre i)) ∧
      (∀ i : Mode, (B i).comp e.toLinearMap = e.toLinearMap.comp (ann i)) ∧
      ∀ a, (T a).comp e.toLinearMap = e.toLinearMap.comp (chargeOperator a) := by
  classical
  let R := recognitionMap s T w
  let v (p : Momentum) := R (Finsupp.single p 1)
  have hv (p : Momentum) : v p = T ((s).lift p) w := by
    simp only [v, R, recognitionMap_single, one_smul]
  have hRinj : Function.Injective R :=
    ThirdTwistedGroundRecognition.recognitionMap_injective hUnit hMul hw hIndep hWeight
  have hv_ne (p : Momentum) : v p ≠ 0 := by
    intro hz
    have h := hRinj (hz.trans R.map_zero.symm)
    have hAt := congrArg (fun f : P48qTwistedChargeAction.Ground => f p) h
    exact one_ne_zero (by simpa only [Finsupp.single_eq_same, Finsupp.zero_apply] using hAt)
  have hTransport (a : Charge lattice) (p : Momentum) :
      T a (v p) = chargePhase a p • v (shift a p) := by
    have h : (T a).comp R = R.comp (U a) :=
      ThirdTwistedGroundRecognition.recognitionMap_intertwines hMul hχ a
    simpa only [v, R, LinearMap.comp_apply, U_ground, recognitionMap_single, one_smul]
      using DFunLike.congr_fun h (Finsupp.single p 1)
  have hScale (n : ℕ) : scale n ≠ 0 :=
    div_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) (by norm_num)
  let D (i : Mode) := (scale i.2)⁻¹ • B i
  have hNorm : ∀ i j, ⁅D i, A j⁆ = if i = j then 1 else 0 := by
    intro i j
    let c := (scale i.2)⁻¹
    calc
      ⁅D i, A j⁆ = c • ⁅B i, A j⁆ := by
        change (c • B i) * A j - A j * (c • B i) = c • (B i * A j - A j * B i)
        rw [smul_mul_assoc, mul_smul_comm, smul_sub]
      _ = _ := by
        rw [hWeyl]
        split_ifs <;> simp [c, smul_smul, hScale]
  have hVac' (p : Momentum) (i : Mode) : D i (v p) = 0 := by
    have h := DFunLike.congr_fun (hBT i ((s).lift p)).eq w
    change B i (T ((s).lift p) w) = T ((s).lift p) (B i w) at h
    simp only [D, LinearMap.smul_apply, hv, h, hVac, map_zero, smul_zero]
  choose F hFinj hFone hFX hFD using fun p =>
    P48qCyclicOscillator.exists_cyclic_intertwiner A D (v p) hA hNorm (hv_ne p) (hVac' p)
  have hFmem (p : Momentum) (P : Fock) : F p P ∈ W p := by
    induction P using MvPolynomial.induction_on with
    | C c =>
      rw [show C c = c • (1 : Fock) by rw [smul_eq_C_mul, mul_one], map_smul, hFone, hv]
      exact (W p).smul_mem c (hWeight p)
    | add P Q hP hQ => rw [map_add]; exact (W p).add_mem hP hQ
    | mul_X P i hP => rw [mul_comm P (X i), hFX]; exact hStable p i _ hP
  have hFT (a : Charge lattice) (p : Momentum) :
      (T a).comp (F p) = chargePhase a p • F (shift a p) := by
    apply fock_map_eq_of_one A
    · intro i P
      simp only [LinearMap.comp_apply, hFX]
      exact DFunLike.congr_fun (hAT i a).eq.symm (F p P)
    · intro i P
      simp only [LinearMap.smul_apply, hFX, map_smul]
    · simpa only [LinearMap.comp_apply, LinearMap.smul_apply, hFone] using hTransport a p
  let L : State →ₗ[ℂ] M := Finsupp.lsum ℂ F
  have hSingle (p : Momentum) (P : Fock) : L (Finsupp.single p P) = F p P :=
    Finsupp.lsum_single ℂ F p P
  have hCre (i : Mode) : (A i).comp L = L.comp (cre i) := by
    rcases i with ⟨j, n⟩
    apply Finsupp.lhom_ext
    intro p P
    simpa only [LinearMap.comp_apply, negative_mode_single, hSingle] using (hFX p (j, n) P).symm
  have hAnn (i : Mode) : (B i).comp L = L.comp (ann i) := by
    rcases i with ⟨j, n⟩
    apply Finsupp.lhom_ext
    intro p P
    simp only [LinearMap.comp_apply, positive_mode_single, map_smul, hSingle, hFD,
      D, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (hScale n), one_smul]
  have hCharge (a : Charge lattice) : (T a).comp L = L.comp (chargeOperator a) := by
    apply Finsupp.lhom_ext
    intro p P
    simpa only [LinearMap.comp_apply, chargeOperator_single, hSingle, map_smul,
      LinearMap.smul_apply] using DFunLike.congr_fun (hFT a p) P
  have hInj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).2
    intro u hu
    have hSum : ∑ p ∈ u.support, F p (u p) = 0 := hu
    have hComponent := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero W).mp hIndep
      u.support (fun p => F p (u p)) (fun p _ => hFmem p _) hSum
    apply Finsupp.ext
    intro p
    by_cases hp : p ∈ u.support
    · exact hFinj p ((hComponent p hp).trans (map_zero (F p)).symm)
    · exact Finsupp.notMem_support_iff.mp hp
  have hSurj : Function.Surjective L := by
    have invariant {Q : Module.End ℂ M} {q : Module.End ℂ State}
        (hQ : Q.comp L = L.comp q) (x : M) (hx : x ∈ L.range) : Q x ∈ L.range := by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨q y, (DFunLike.congr_fun hQ y).symm⟩
    rcases hIrred L.range (fun i => invariant (hCre i)) (fun i => invariant (hAnn i))
      (fun a => invariant (hCharge a)) with hBot | hTop
    · have hMem : v 0 ∈ L.range := ⟨Finsupp.single 0 1, (hSingle 0 1).trans (hFone 0)⟩
      rw [hBot, Submodule.mem_bot] at hMem
      exact (hv_ne 0 hMem).elim
    · exact LinearMap.range_eq_top.mp hTop
  refine ⟨LinearEquiv.ofBijective L ⟨hInj, hSurj⟩, ?_, ?_, hCre, hAnn, hCharge⟩
  · intro p
    exact (hSingle p 1).trans ((hFone p).trans (hv p))
  · intro p P
    change L (Finsupp.single p P) ∈ W p
    rw [hSingle]
    exact hFmem p P

/-- The fixed Cartan relations place each charge translate of the vacuum in
its native joint weight space. Recognition then intertwines the fixed Cartan
zero modes as well as the oscillator and charge operators. -/
theorem recognize_irreducible
    (A B : Mode → Module.End ℂ M) (T : Charge lattice → Module.End ℂ M)
    (Z : Fixed → Module.End ℂ M) (w : M)
    (hA : ∀ i j, Commute (A i) (A j))
    (hWeyl : ∀ i j, ⁅B i, A j⁆ = if i = j then scale i.2 • 1 else 0)
    (hAT : ∀ i a, Commute (A i) (T a))
    (hBT : ∀ i a, Commute (B i) (T a))
    (hUnit : T 0 = LinearMap.id)
    (hMul : ∀ a b, (T a).comp (T b) = (multiplier.c a b : ℂ) • T (a + b))
    (hw : w ≠ 0) (hVac : ∀ i, B i w = 0)
    (hχ : ∀ m : ThirdTwistedChargeAction.Moving lattice g, T m.1 w = (χ m : ℂ) • w)
    (hZero : ∀ h, Z h w = 0)
    (hZA : ∀ h i, Commute (Z h) (A i))
    (hZT : ∀ h a, (Z h).comp (T a) - (T a).comp (Z h) =
      (p48qForm (h : Cartan) (chargeVector (N a)) / 3) • T a)
    (hIrred : ∀ S : Submodule ℂ M,
      (∀ i x, x ∈ S → A i x ∈ S) → (∀ i x, x ∈ S → B i x ∈ S) →
      (∀ a x, x ∈ S → T a x ∈ S) → S = ⊥ ∨ S = ⊤) :
    ∃ e : State ≃ₗ[ℂ] M,
      (∀ p, e (Finsupp.single p 1) = T ((s).lift p) w) ∧
      (∀ p P, e (Finsupp.single p P) ∈ jointWeightSpace Z p) ∧
      (∀ i : Mode, (A i).comp e.toLinearMap = e.toLinearMap.comp (cre i)) ∧
      (∀ i : Mode, (B i).comp e.toLinearMap = e.toLinearMap.comp (ann i)) ∧
      (∀ a, (T a).comp e.toLinearMap = e.toLinearMap.comp (chargeOperator a)) ∧
      ∀ h, (Z h).comp e.toLinearMap = e.toLinearMap.comp (mode (h : Cartan) 0) := by
  have hWeight (p : Momentum) : T ((s).lift p) w ∈ jointWeightSpace Z p := by
    simp only [jointWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro h
    simpa only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      hZero h, map_zero, sub_zero, (s).right_inv p, ← pairing_physicalMomentum h p]
      using DFunLike.congr_fun (hZT h ((s).lift p)) w
  have hStable : ∀ p i x, x ∈ jointWeightSpace Z p → A i x ∈ jointWeightSpace Z p := by
    simp only [jointWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro p i x hx h
    calc
      Z h (A i x) = A i (Z h x) := DFunLike.congr_fun (hZA h i).eq x
      _ = _ := by rw [hx h, map_smul]
  obtain ⟨e, hGround, hMem, hCre, hAnn, hCharge⟩ :=
    recognize_irreducible_of_subspaces A B T w (jointWeightSpace Z) hA hWeyl hAT hBT
      hUnit hMul hw hVac hχ hWeight hStable (jointWeightSpace_iSupIndep Z) hIrred
  refine ⟨e, hGround, hMem, hCre, hAnn, hCharge, ?_⟩
  intro h
  have hMode : mode (h : Cartan) 0 = P48qFixedCurrentIterate.zeroMode h := by
    apply LinearMap.ext
    intro v
    apply Finsupp.ext
    intro p
    exact (mode_zero_apply (h : Cartan) v p).trans
      (P48qFixedCurrentIterate.zeroMode_apply h v p).symm
  apply Finsupp.lhom_ext
  intro p P
  have hp := hMem p P
  simp only [jointWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hp
  simpa only [LinearMap.comp_apply, hMode, P48qFixedCurrentIterate.zeroMode_single,
    map_smul, LinearEquiv.coe_toLinearMap] using hp h

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFockRecognition

#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFockRecognition.jointWeightSpace_iSupIndep
#print axioms D5.S3.VertexAlgebra.Lattice.Orbifold.P48qFockRecognition.recognize_irreducible
