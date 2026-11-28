/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/NativeFusion/P48qFiniteModularTrace
   generality: I
   mirror-B: none(waiver:no-B-plane-mirror-for-source-module)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Modular trace identities force twisted labels on the electric stabilizer. -/

import D5.S3.FiniteGroups.CosetActions.EtalePermutationTrace
import D5.S3.FiniteGroups.InducedCharacterFormula
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qHolomorphicExtensionObstruction
import Mathlib.Data.Matrix.Mul
import Mathlib.RepresentationTheory.Character
import OmegaBuild.Commands

/-!
Dong–Ren–Xu, *On Orbifold Theory*, [arXiv:1507.03306v2](https://arxiv.org/abs/1507.03306v2),
Sections 2.2 and 3, give the modular trace and fixed-point module context.
Here the common finite label space, modular coefficient identities, twisted
support and identification of the paired twining coefficients with the
electric algebra trace enter as hypotheses.
-/

compile_only_with_mathlib

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion

open scoped Matrix
open FiniteGroups.CosetActions.EtalePermutationTrace
  (exists_coset_trace_eq_fixedPoints_and_ne_zero)

local notation "coeffs(" b ")" => (fun i => ((b i : ℕ) : ℂ))

/-- On the subgroup supplied by the finite étale trace theorem, modular
covariance forces a twisted label with positive extension multiplicity. -/
theorem exists_coset_trace_and_positive_twisted_multiplicity
    {G A I : Type*} [Group G] [Finite G] [Fintype I]
    [CommRing A] [Nontrivial A] [Algebra ℂ A] [Module.Finite ℂ A] [Algebra.Etale ℂ A]
    (ρ : G →* (A ≃ₐ[ℂ] A))
    (hfixed : ∀ a : A, (∀ g : G, ρ g a = a) → ∃ z : ℂ, a = algebraMap ℂ A z)
    (b : I → ℕ) (S : Matrix I I ℂ)
    (hInvariant : coeffs(b) ᵥ* S = coeffs(b))
    (u v : G → I → ℂ) (c : G → ℂˣ) (twisted : G → Set I)
    (hCovariance : ∀ g, S *ᵥ u g = (c g : ℂ) • v g)
    (hTrace : ∀ g, coeffs(b) ⬝ᵥ u g = LinearMap.trace ℂ A (ρ g).toLinearMap)
    (hSupport : ∀ g i, i ∉ twisted g → v g i = 0) :
    ∃ K : Subgroup G, ∀ g : G,
      LinearMap.trace ℂ A (ρ g).toLinearMap = ({q : G ⧸ K | g • q = q}.ncard : ℂ) ∧
      (g ∈ K → ∃ i ∈ twisted g, 0 < b i) := by
  obtain ⟨K, hCoset⟩ := exists_coset_trace_eq_fixedPoints_and_ne_zero ρ hfixed
  refine ⟨K, fun g => ⟨(hCoset g).1, ?_⟩⟩
  intro hg
  have hTransport :
      (c g : ℂ) • (coeffs(b) ⬝ᵥ v g) = LinearMap.trace ℂ A (ρ g).toLinearMap := by
    rw [← dotProduct_smul, ← hCovariance g, Matrix.dotProduct_mulVec, hInvariant, hTrace g]
  have hPair : coeffs(b) ⬝ᵥ v g ≠ 0 := by
    intro hZero
    exact (hCoset g).2 hg (by simpa only [hZero, smul_zero] using hTransport.symm)
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hPair
  have hv : v g i ≠ 0 := right_ne_zero_of_mul hi
  have hb : b i ≠ 0 := fun h => hi (by simp [h])
  have hiTwisted : i ∈ twisted g := by
    by_contra hNotTwisted
    exact hv (hSupport g i hNotTwisted)
  exact ⟨i, hiTwisted, Nat.pos_of_ne_zero hb⟩

section ElectricCharacters

open scoped BigOperators
open CategoryTheory
open FiniteGroups.FiniteCharacterAlgebra.TauCeti (ClassFunction)
open FiniteGroups.InducedCharacterFormula.TauCeti (characterPairing_ind indClassFun_apply)

/-- The fixed-coset count is the value of the character induced from the
trivial character of the specified subgroup. -/
private theorem induced_trivial_apply_eq_fixed_cosets
    {G : Type*} [Group G] [Finite G] (K : Subgroup G) (g : G) :
    (FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind K
      (⟨fun _ => 1, fun _ _ => rfl⟩ : ClassFunction ℂ K)).1 g =
        ({q : G ⧸ K | g • q = q}.ncard : ℂ) := by
  classical
  rw [FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind_apply, indClassFun_apply]
  let : Fintype (G ⧸ K) := Fintype.ofFinite _
  have hfix (q : G ⧸ K) : q.out⁻¹ * g * q.out ∈ K ↔ g • q = q := by
    have hq : (QuotientGroup.mk q.out : G ⧸ K) = q := Quotient.out_eq' q
    have hgq : (QuotientGroup.mk (g * q.out) : G ⧸ K) = g • q :=
      congrArg (g • ·) hq
    calc
      _ ↔ (QuotientGroup.mk q.out : G ⧸ K) = QuotientGroup.mk (g * q.out) := by
        simpa only [mul_assoc] using
          (QuotientGroup.eq (s := K) (a := q.out) (b := g * q.out)).symm
      _ ↔ _ := by rw [hq, hgq, eq_comm]
  let fixed : Set (G ⧸ K) := {q | g • q = q}
  have hFinite : fixed.Finite := Set.toFinite _
  have hFilter : Finset.univ.filter (fun q : G ⧸ K => g • q = q) = hFinite.toFinset := by
    ext q
    simp [fixed]
  simp only [dite_eq_ite, hfix, Finset.sum_boole, hFilter]
  exact congrArg (fun n : ℕ => (n : ℂ)) (Set.ncard_eq_toFinset_card fixed hFinite).symm

/-- An irreducible coefficient of the electric algebra trace equals the
dimension of its fixed space for the subgroup that gives the coset trace. -/
theorem electric_multiplicity_eq_finrank_invariants
    {G A I : Type*} [Group G] [Finite G] [Fintype I]
    [CommRing A] [Algebra ℂ A] [Module.Finite ℂ A]
    (K : Subgroup G) (ρ : G →* (A ≃ₐ[ℂ] A))
    (R : I → FDRep ℂ G) [∀ i, Simple (R i)]
    (hDistinct : Pairwise fun i j => ¬ Nonempty (R i ≅ R j)) (b : I → ℕ)
    (hCoset : ∀ g : G,
      LinearMap.trace ℂ A (ρ g).toLinearMap = ({q : G ⧸ K | g • q = q}.ncard : ℂ))
    (hCharacter : ∀ g : G,
      LinearMap.trace ℂ A (ρ g).toLinearMap = ∑ i, (b i : ℂ) * (R i).character g)
    (j : I) : b j = Module.finrank ℂ (Representation.invariants ((R j).ρ.comp K.subtype)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hG
  let : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let trivial : ClassFunction ℂ K := ⟨fun _ => 1, fun _ _ => rfl⟩
  let induced := FiniteGroups.InducedCharacterFormula.TauCeti.ClassFunction.ind K trivial
  have hInduced (g : G) : induced.1 g = ∑ i, (b i : ℂ) * (R i).character g :=
    (induced_trivial_apply_eq_fixed_cosets K g).trans ((hCoset g).symm.trans (hCharacter g))
  have hOrthogonal (i : I) :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, (R i).character g * (R j).character g⁻¹ =
        if i = j then 1 else 0 := by
    rw [FDRep.char_orthonormal]
    by_cases hij : i = j
    · subst i
      simp [show Nonempty (R j ≅ R j) from ⟨Iso.refl _⟩]
    · simp [hij, hDistinct hij]
  have hCoefficient :
      (Nat.card G : ℂ)⁻¹ * (∑ g : G, induced.1 g * (R j).character g⁻¹) = (b j : ℂ) := by
    simp_rw [hInduced, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm, Finset.mul_sum]
    calc
      _ = ∑ i, (b i : ℂ) *
          ((Nat.card G : ℂ)⁻¹ * ∑ g : G, (R i).character g * (R j).character g⁻¹) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
        exact mul_left_comm _ _ _
      _ = _ := by
        simp_rw [hOrthogonal, mul_ite, mul_one, mul_zero]
        simp
  have hReciprocity := characterPairing_ind (S := K) (isUnit_iff_ne_zero.mpr hG)
    trivial (ClassFunction.ofCharacter (R j).ρ)
  change ClassFunction.characterPairing induced (ClassFunction.ofCharacter (R j).ρ) = _
    at hReciprocity
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply] at hReciprocity
  change (Nat.card G : ℂ)⁻¹ * (∑ g : G, induced.1 g * (R j).character g⁻¹) =
    (Nat.card K : ℂ)⁻¹ * (∑ k : K, 1 * (R j).character ((k⁻¹ : K) : G)) at hReciprocity
  rw [hCoefficient] at hReciprocity
  have hInverse : (∑ k : K, (R j).character ((k⁻¹ : K) : G)) =
      ∑ k : K, (R j).character (k : G) :=
    Fintype.sum_equiv (Equiv.inv K) _ _ fun _ => rfl
  simp only [one_mul, hInverse] at hReciprocity
  have hAverage :=
    Representation.card_inv_mul_sum_char_eq_finrank ((R j).ρ.comp K.subtype)
  exact Nat.cast_injective (hReciprocity.trans hAverage)

/-- A weighted character identity on a finite grade determines its fixed
dimension. If the target grade contains those electric dimensions and a
nonnegative remainder, its dimension bounds the fixed dimension. -/
theorem fixed_grade_finrank_le_of_electric_multiplicities
    {G I Wn : Type*} [Group G] [Finite G] [Fintype I]
    [AddCommGroup Wn] [Module ℂ Wn] [FiniteDimensional ℂ Wn]
    (K : Subgroup G) (R : I → FDRep ℂ G) (Vn : FDRep ℂ G) (b d : I → ℕ)
    (hMultiplicity : ∀ i,
      b i = Module.finrank ℂ (Representation.invariants ((R i).ρ.comp K.subtype)))
    (hGrade : ∀ g : G, Vn.character g = ∑ i, (d i : ℂ) * (R i).character g)
    (extra : ℕ) (hTarget : Module.finrank ℂ Wn = (∑ i, b i * d i) + extra) :
    Module.finrank ℂ (Representation.invariants (Vn.ρ.comp K.subtype)) = (∑ i, b i * d i) ∧
    Module.finrank ℂ (Representation.invariants (Vn.ρ.comp K.subtype)) ≤ Module.finrank ℂ Wn := by
  let : Fintype K := Fintype.ofFinite K
  let : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hAverage (V : FDRep ℂ G) :
      (Nat.card K : ℂ)⁻¹ * (∑ k : K, V.character (k : G)) =
        (Module.finrank ℂ (Representation.invariants (V.ρ.comp K.subtype)) : ℂ) :=
    Representation.card_inv_mul_sum_char_eq_finrank (V.ρ.comp K.subtype)
  have hDimension : Module.finrank ℂ (Representation.invariants (Vn.ρ.comp K.subtype)) =
      ∑ i, b i * d i := by
    apply Nat.cast_injective (R := ℂ)
    rw [← hAverage Vn]
    push_cast
    simp_rw [hGrade]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (d i : ℂ) * ((Nat.card K : ℂ)⁻¹ * ∑ k : K, (R i).character (k : G)) := by
        rw [← Finset.mul_sum]
        exact mul_left_comm _ _ _
      _ = _ := by rw [hAverage, ← hMultiplicity i, mul_comm]
  exact ⟨hDimension, by rw [hDimension, hTarget]; exact Nat.le_add_right _ _⟩

end ElectricCharacters

open ExtremalC48 (SL47)
open HalfFockSpectralFiberSource (actualInverse)
open LatticeActualConformalState (omega)
open LatticeGeneratingFieldLocality (Carrier Charge bilinear)
open LatticePositiveEnergy (grade)
open DiagonalCharacterConjugacy (PreservesModes)
open P48qFiniteActionObstruction (p48q_finite_action_obstruction)
open P48qHolomorphicExtensionObstruction (CubicSectorRealization)
open P48qOrderThreeSpectrumTransport (conformalZeroMode)
open P48qTwistedChargeAction (lattice)

universe w x

/-- With a grading-compatible realization of each occupied cubic label in
an integrally graded target, the electric stabilizer has two independent
fixed weight-two states in the P48q lattice carrier. -/
theorem p48q_fixed_quadratics_of_finite_modular_trace
    {G A I : Type*} [Group G] [Finite G] [Fintype I]
    [CommRing A] [Nontrivial A] [Algebra ℂ A] [Module.Finite ℂ A] [Algebra.Etale ℂ A]
    (ρ : G →* (A ≃ₐ[ℂ] A))
    (hfixed : ∀ a : A, (∀ g : G, ρ g a = a) → ∃ z : ℂ, a = algebraMap ℂ A z)
    (b : I → ℕ) (S : Matrix I I ℂ)
    (hInvariant : coeffs(b) ᵥ* S = coeffs(b))
    (u v : G → I → ℂ) (c : G → ℂˣ) (twisted : G → Set I)
    (hCovariance : ∀ g, S *ᵥ u g = (c g : ℂ) • v g)
    (hTrace : ∀ g, coeffs(b) ⬝ᵥ u g = LinearMap.trace ℂ A (ρ g).toLinearMap)
    (hSupport : ∀ g i, i ∉ twisted g → v g i = 0)
    (realization : Additive SL47 →+ AddAut (Charge lattice))
    (hFaithful : Function.Injective realization)
    (hIsometry : ∀ s : Additive SL47, ∀ a b,
      bilinear lattice (realization s a) (realization s b) = bilinear lattice a b)
    (hExhaustive : ∀ s : AddAut (Charge lattice),
      (∀ a b, bilinear lattice (s a) (s b) = bilinear lattice a b) → ∃ k, realization k = s)
    (U : G →* (Carrier lattice ≃ₗ[ℂ] Carrier lattice))
    (hU : Function.Injective U) (hMode : ∀ g, PreservesModes lattice (U g))
    (hOmega : ∀ g, U g (omega lattice (actualInverse lattice)) =
      omega lattice (actualInverse lattice))
    {W : Type x} [AddCommGroup W] [Module ℂ W] (L_W : Module.End ℂ W)
    (hGraded : (⨆ n : ℤ, L_W.eigenspace (n : ℂ)) = ⊤)
    (hRealizeCubic : ∀ g, orderOf g = 3 → ∀ i ∈ twisted g, 0 < b i →
      Nonempty (CubicSectorRealization.{w, x} (U g) L_W)) :
    ∃ K : Subgroup G,
      (∀ g : G,
        LinearMap.trace ℂ A (ρ g).toLinearMap = ({q : G ⧸ K | g • q = q}.ncard : ℂ)) ∧
      ∃ q : Fin 2 → Carrier lattice, (∀ i, q i ∈ grade lattice 2) ∧
        (∀ k : K, ∀ i, U k (q i) = q i) ∧ LinearIndependent ℂ q := by
  obtain ⟨K, hCoset⟩ := exists_coset_trace_and_positive_twisted_multiplicity
    ρ hfixed b S hInvariant u v c twisted hCovariance hTrace hSupport
  refine ⟨K, fun g => (hCoset g).1, ?_⟩
  obtain ⟨_, _, _, hDichotomy⟩ :=
    p48q_finite_action_obstruction.{w} realization hFaithful hIsometry hExhaustive
      (U.comp K.subtype) (hU.comp Subtype.val_injective) (fun k => hMode k) (fun k => hOmega k)
  rcases hDichotomy with hQuadratics | ⟨k, hOrder, _, hSpectrum⟩
  · exact hQuadratics
  · have hOrderG : orderOf (k : G) = 3 :=
      (orderOf_injective K.subtype Subtype.val_injective k).trans hOrder
    obtain ⟨i, hi, hb⟩ := (hCoset k).2 k.property
    obtain ⟨sector⟩ := hRealizeCubic k hOrderG i hi hb
    let _ := sector.spaceAdd
    let _ := sector.spaceModule
    let L : Module.End ℂ sector.branch :=
      LinearMap.restrict (conformalZeroMode sector.field) sector.stable
    have hNoEigenvalue (n : ℤ) : ¬ L.HasEigenvalue (n : ℂ) := by
      intro hEigenvalue
      obtain ⟨y, hy⟩ := hEigenvalue.exists_hasEigenvector
      have hyNe : (y : sector.space) ≠ 0 := fun h =>
        (Module.End.hasEigenvector_iff.mp hy).2 (Subtype.ext h)
      have hyEigen : conformalZeroMode sector.field (y : sector.space) =
          (n : ℂ) • (y : sector.space) := by
        simpa only [L, LinearMap.coe_restrict_apply, Submodule.coe_smul] using
          congrArg (fun z : sector.branch => (z : sector.space)) hy.apply_eq_smul
      exact (hSpectrum sector.space sector.field sector.fieldLaw sector.lower sector.lowerBound
        sector.finiteWeight (n : ℂ) y hyNe hyEigen).2.2 n rfl
    have hVanish := Omega.LinearAlgebra.eq_zero_of_injective_intertwiner_of_no_eigenvalue
      L L_W (fun n : ℤ => (n : ℂ)) hGraded hNoEigenvalue
      sector.inclusion sector.injective sector.intertwines
    obtain ⟨y, hy, hyNe⟩ := Submodule.exists_mem_ne_zero_of_ne_bot sector.nonzero
    exact (hyNe (congrArg (fun z : sector.branch => (z : sector.space)) (hVanish ⟨y, hy⟩))).elim

#print axioms exists_coset_trace_and_positive_twisted_multiplicity
#print axioms electric_multiplicity_eq_finrank_invariants
#print axioms fixed_grade_finrank_le_of_electric_multiplicities
#print axioms p48q_fixed_quadratics_of_finite_modular_trace

end D5.S3.VertexAlgebra.Lattice.Orbifold.NativeFusion
