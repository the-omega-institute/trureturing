/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedModeMorphisms
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTwistedModeMorphisms
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed physical mode morphisms on and between the original twisted Leech slices. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OriginalOrbifoldTwistedOscillatorAction
import D5.S3.VertexAlgebra.TwistedGround.MixedTranslation
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The native fixed-source mode commutant and the morphisms between opposite twisted slices. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedModeMorphisms

open ActualLeechHyperbolic (leechData leech_spec)
open LatticeInvolution (FixedCarrier)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open LatticeHalfFockChargedTensorCoefficients (groundRank)
open LatticeHalfFockGradedTrace (actualTensorL0 actualAmbientBasis actual_basis_eigenvalue
  actualTensorL0_repr oddWeight OddMonomial)
open LatticeTwistedGroundRealization (Half)
open LatticeHalfFockParityT (actualParity)
open LatticeHalfFockCorrectedField (correctedField)
open OriginalOrbifoldConformal (conformalVector)
open OriginalOrbifoldSectorModules (fixedParityY)
open OriginalOrbifoldTwistedGroundAction (PositiveTwisted groundEquiv twistedL0
  fixedZeroMode twisted_top_irreducible)
open OriginalOrbifoldTwistedOscillatorAction (positive_twisted_irreducible)
open Module.End (mem_eigenspace_iff)
open scoped BigOperators VertexOperator

open private basis_parity parity_repr from
  D5.S3.VertexAlgebra.TwistedGround.MixedTranslation

noncomputable section

local notation "hu" => And.left (And.right leech_spec)
local notation "Slice" => paritySpace leechData hu
local notation "Top" => OriginalOrbifoldTwistedGroundAction.Top
local notation "mode" => fun (s : ℂ) (a : FixedCarrier leechData) (n : ℤ) =>
  (fixedParityY leechData hu s a)[[n]]

/-- The linear maps intertwining each physical mode of every actual fixed source. -/
def fixedModeHom (s t : ℂ) : Submodule ℂ (Slice s →ₗ[ℂ] Slice t) where
  carrier := {f | ∀ a n v, f (mode s a n v) = mode t a n (f v)}
  zero_mem' := by
    intro a n v
    simp
  add_mem' hf hg := by
    intro a n v
    simpa only [LinearMap.add_apply, map_add] using congrArg₂ (· + ·) (hf a n v) (hg a n v)
  smul_mem' c f hf := by
    intro a n v
    simpa only [LinearMap.smul_apply, map_smul] using congrArg (c • ·) (hf a n v)

private theorem map_eigenvector {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (f : V →ₗ[ℂ] W)
    (A : Module.End ℂ V) (B : Module.End ℂ W) (v : V) (c : ℂ)
    (hc : f (A v) = B (f v)) (he : A v = c • v) : B (f v) = c • f v :=
  hc.symm.trans ((congrArg f he).trans (map_smul f c v))

set_option maxHeartbeats 1200000 in
-- Compare the projected parity subtype with the ambient tensor field.
/-- Physical mode `1` of the raw projected conformal field is the full tensor energy. -/
theorem fixedParity_conformal_mode_val (s : ℂ) (v : Slice s) :
    (mode s (conformalVector leechData hu).1 1 v).val = actualTensorL0 leechData hu v.val := by
  let H := HalfFockSpectralFiberSource.actualInverse leechData
  change (correctedField leechData hu (LatticeActualConformalState.omega leechData H)).coeff
    (-4) v.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega leechData hu _
    (HalfFockSpectralFiberSource.actualInverse_left leechData hu)]
  simp only [LatticeHalfFock.tensorStressField, HVertexOperator.coeff_of_coeff,
    LatticeHalfFock.stressCoeff, actualTensorL0, LatticeHalfFock.tensorL]
  rfl

set_option maxHeartbeats 1200000 in
-- The commutation equation is on the parity subtype inside the tensor space.
private theorem preserves_top (f : fixedModeHom 1 1) (v : PositiveTwisted) (hv : v ∈ Top) :
    f.val v ∈ Top := by
  change v ∈ twistedL0.eigenspace (3 / 2) at hv
  change f.val v ∈ twistedL0.eigenspace (3 / 2)
  have h : f.val (twistedL0 v) = twistedL0 (f.val v) :=
    f.property (conformalVector leechData hu).1 1 v
  exact (mem_eigenspace_iff (f := twistedL0)).mpr
    (map_eigenvector f.val twistedL0 twistedL0 v (3 / 2) h
      ((mem_eigenspace_iff (f := twistedL0)).mp hv))

private theorem top_ne_zero_vector : ∃ v : Top, v ≠ 0 := by
  refine ⟨groundEquiv 1, ?_⟩
  exact groundEquiv.map_ne_zero_iff.mpr one_ne_zero

set_option maxHeartbeats 1200000 in
-- The restriction compares endomorphisms on two nested subtypes.
private theorem top_scalar (f : fixedModeHom 1 1) :
    ∃ c : ℂ, ∀ v : Top, f.val v.val = c • v.val := by
  let F : Module.End ℂ Top := f.val.restrict (preserves_top f)
  let : FiniteDimensional ℂ Top := groundEquiv.finiteDimensional
  let : Nontrivial Top := by
    obtain ⟨v, hv⟩ := top_ne_zero_vector
    exact ⟨⟨v, 0, hv⟩⟩
  obtain ⟨c, hc⟩ := F.exists_eigenvalue
  have stable (a : FixedCarrier leechData) (h : ℤ)
      (ha : a.val ∈ LatticePositiveEnergy.grade leechData h) (v : Top)
      (hv : v ∈ F.eigenspace c) : fixedZeroMode a h ha v ∈ F.eigenspace c := by
    have hcomm : F (fixedZeroMode a h ha v) = fixedZeroMode a h ha (F v) :=
      Subtype.ext (f.property a (h - 1) v.val)
    exact (mem_eigenspace_iff (f := F)).mpr
      (map_eigenvector (fixedZeroMode a h ha) F F v c hcomm.symm
        ((mem_eigenspace_iff (f := F)).mp hv))
  have htop : F.eigenspace c = ⊤ := (twisted_top_irreducible _ stable).resolve_left hc
  refine ⟨c, fun v => ?_⟩
  have hv : v ∈ F.eigenspace c := htop.symm ▸ Submodule.mem_top
  exact congrArg (fun w : Top => w.val) ((mem_eigenspace_iff (f := F)).mp hv)

set_option maxHeartbeats 1200000 in
-- Evaluating the kernel and scalar identity uses the actual parity subtype.
/-- Every endomorphism commuting with all fixed physical modes has a unique scalar. -/
theorem positive_twisted_mode_end_eq_smul (f : fixedModeHom 1 1) :
    ∃! c : ℂ, f.val = c • (LinearMap.id : Module.End ℂ PositiveTwisted) := by
  obtain ⟨c, hc⟩ := top_scalar f
  obtain ⟨v₀, hv₀⟩ := top_ne_zero_vector
  have hv₀' : v₀.val ≠ 0 := fun h => hv₀ (Subtype.ext h)
  let K : Submodule ℂ PositiveTwisted :=
    LinearMap.ker (f.val - c • (LinearMap.id : Module.End ℂ PositiveTwisted))
  have mem_K (v : PositiveTwisted) : v ∈ K ↔ f.val v = c • v := by
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
  have stable (a : FixedCarrier leechData) (n : ℤ) (v : PositiveTwisted) (hv : v ∈ K) :
      mode 1 a n v ∈ K := by
    apply (mem_K _).mpr
    exact map_eigenvector (mode 1 a n) f.val f.val v c (f.property a n v).symm ((mem_K v).mp hv)
  have hvK : v₀.val ∈ K := (mem_K _).mpr (hc v₀)
  have K_ne_bot : K ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hvK
    exact hv₀' hvK
  have K_top : K = ⊤ := (positive_twisted_irreducible K stable).resolve_left K_ne_bot
  refine ⟨c, LinearMap.ext (fun v => (mem_K v).mp (K_top.symm ▸ Submodule.mem_top)), ?_⟩
  intro d hd
  apply smul_left_injective ℂ hv₀'
  exact (LinearMap.congr_fun hd v₀.val).symm.trans (hc v₀)

private theorem scalar_mem_fixedModeHom (c : ℂ) :
    c • (LinearMap.id : Module.End ℂ PositiveTwisted) ∈ fixedModeHom 1 1 := by
  intro a n v
  exact (map_smul (mode 1 a n) c v).symm

set_option maxHeartbeats 1200000 in
-- Compare the endomorphism and commutant carriers through their subtypes.
/-- The fixed-mode commutant is precisely the line through the identity. -/
theorem positive_twisted_mode_end_eq_span :
    fixedModeHom 1 1 = Submodule.span ℂ {(LinearMap.id : Module.End ℂ PositiveTwisted)} := by
  apply le_antisymm
  · intro f hf
    obtain ⟨c, hc, _⟩ := positive_twisted_mode_end_eq_smul ⟨f, hf⟩
    exact Submodule.mem_span_singleton.mpr ⟨c, hc.symm⟩
  · apply Submodule.span_le.mpr
    rintro f (rfl : f = LinearMap.id)
    change (LinearMap.id : Module.End ℂ PositiveTwisted) ∈ fixedModeHom 1 1
    simpa only [one_smul] using scalar_mem_fixedModeHom 1

set_option maxHeartbeats 1200000 in
-- The codomain is the subtype of linear maps on the actual parity slice.
/-- The linear identification sends each complex number to that scalar times the identity. -/
def positiveTwistedModeEndEquiv : ℂ ≃ₗ[ℂ] fixedModeHom 1 1 :=
  LinearEquiv.ofBijective
    ((LinearMap.toSpanSingleton ℂ (Module.End ℂ PositiveTwisted) LinearMap.id).codRestrict
      (fixedModeHom 1 1) scalar_mem_fixedModeHom) (by
        constructor
        · intro c d h
          obtain ⟨v, hv⟩ := top_ne_zero_vector
          have hv' : v.val ≠ 0 := fun he => hv (Subtype.ext he)
          exact smul_left_injective ℂ hv' (congrArg (fun f : fixedModeHom 1 1 => f.val v.val) h)
        · intro f
          obtain ⟨c, hc, _⟩ := positive_twisted_mode_end_eq_smul f
          refine ⟨c, Subtype.ext ?_⟩
          change c • (LinearMap.id : Module.End ℂ PositiveTwisted) = f.val
          exact hc.symm)

@[simp] theorem positiveTwistedModeEndEquiv_apply (c : ℂ) :
    (positiveTwistedModeEndEquiv c).val = c • (LinearMap.id : Module.End ℂ PositiveTwisted) := rfl

private abbrev conformalMode (s : ℂ) : Module.End ℂ (Slice s) :=
  mode s (conformalVector leechData hu).1 1

private abbrev EnergyLabel := OddMonomial leechData × Half (groundRank leechData hu)

private theorem support_parity {s : ℂ} (v : Slice s) (j : EnergyLabel)
    (hj : (actualAmbientBasis leechData hu).repr v.val j ≠ 0) :
    (-1 : ℂ) ^ oddWeight leechData j.1 = s := by
  have hp : actualParity leechData hu v.val = s • v.val := by
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] using v.property
  have h := congrArg (fun w => (actualAmbientBasis leechData hu).repr w j) hp
  rw [parity_repr] at h
  exact mul_right_cancel₀ hj (by simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using h)

/-- A nonzero eigenvector of the raw conformal mode has an actual oscillator grade
with the corresponding parity sign. Even grades give half-integral weights and
odd grades give integral weights. -/
theorem fixedParity_conformal_eigenweight (s μ : ℂ) (v : Slice s) (hv : v ≠ 0)
    (he : mode s (conformalVector leechData hu).1 1 v = μ • v) :
    ∃ N : ℕ, μ = 3 / 2 + (N : ℂ) / 2 ∧ (-1 : ℂ) ^ N = s := by
  let b := actualAmbientBasis leechData hu
  obtain ⟨j, hj⟩ : ∃ j, b.repr v.val j ≠ 0 := by
    by_contra! h
    exact hv (Subtype.ext (b.repr.map_eq_zero_iff.mp (Finsupp.ext h)))
  have ha : actualTensorL0 leechData hu v.val = μ • v.val :=
    (fixedParity_conformal_mode_val s v).symm.trans (congrArg Subtype.val he)
  have hc := congrArg (fun w => (actualAmbientBasis leechData hu).repr w j) ha
  rw [actualTensorL0_repr] at hc
  simp only [leech_spec.1, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  have hw := mul_right_cancel₀ hj hc
  exact ⟨oddWeight leechData j.1, by linear_combination -hw, support_parity v j hj⟩

/-- The actual finite energy decomposition kills every fixed-mode map between distinct
parity slices. In particular the two twisted Leech sectors have zero Hom in both directions. -/
theorem fixedModeHom_eq_bot_of_ne (s t : ℂ) (hst : s ≠ t) : fixedModeHom s t = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  intro f hf
  change ∀ a n v, f (mode s a n v) = mode t a n (f v) at hf
  rw [Submodule.mem_bot]
  apply LinearMap.ext
  intro v
  let b := actualAmbientBasis leechData hu
  let B := (b.repr v.val).support
  let w (j : B) : Slice s := ⟨b j.val, by
    have hs := support_parity v j.val (Finsupp.mem_support_iff.mp j.property)
    simpa only [paritySpace, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, hs] using
      basis_parity leechData hu j.val⟩
  have hv : (∑ j ∈ B.attach, b.repr v.val j.val • w j) = v := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ j ∈ B.attach, b.repr v.val j.val • b j.val) = v.val
    rw [Finset.sum_attach B (fun j => b.repr v.val j • b j)]
    exact b.linearCombination_repr v.val
  have hw (j : B) : f (w j) = 0 := by
    let N := oddWeight leechData j.val.1
    let μ : ℂ := 3 / 2 + (N : ℂ) / 2
    have he : conformalMode s (w j) = μ • w j := by
      apply Subtype.ext
      rw [fixedParity_conformal_mode_val]
      change actualTensorL0 leechData hu (b j.val) = μ • b j.val
      have hrank : (leechData.rank : ℂ) / 16 = 3 / 2 := by rw [leech_spec.1]; norm_num
      dsimp only [b, μ, N]
      simpa only [hrank, Prod.mk.eta] using actual_basis_eigenvalue leechData hu j.val.1 j.val.2
    have hc : conformalMode t (f (w j)) = μ • f (w j) :=
      map_eigenvector f (conformalMode s) (conformalMode t) (w j) μ
        (hf (conformalVector leechData hu).1 1 (w j)) he
    by_contra hn
    obtain ⟨M, hM, ht⟩ := fixedParity_conformal_eigenweight t μ (f (w j)) hn hc
    have hcast : (N : ℂ) = (M : ℂ) := by dsimp only [μ] at hM; linear_combination 2 * hM
    have hNM : N = M := Nat.cast_injective hcast
    have hs : (-1 : ℂ) ^ N = s := support_parity v j.val (Finsupp.mem_support_iff.mp j.property)
    rw [hNM] at hs
    exact hst (hs.symm.trans ht)
  rw [← hv, map_sum]
  simp only [map_smul, hw, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

#print axioms fixedModeHom
#print axioms fixedParity_conformal_mode_val
#print axioms positive_twisted_mode_end_eq_smul
#print axioms positive_twisted_mode_end_eq_span
#print axioms positiveTwistedModeEndEquiv
#print axioms positiveTwistedModeEndEquiv_apply
#print axioms fixedParity_conformal_eigenweight
#print axioms fixedModeHom_eq_bot_of_ne

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTwistedModeMorphisms
