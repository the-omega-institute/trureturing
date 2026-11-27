/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/GaloisDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/GaloisDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.GaloisDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/GaloisDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.General.LinearAlgebra.Base
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Profinite Galois groups, local fields, places, decomposition, inertia, Frobenius,
cyclotomic character. -/

noncomputable section

open NumberField Pointwise MulAction Units MulSemiringAction ValuationSubring SetLike


/-- A fixed algebraic closure of ℚ. -/
def Ω := AlgebraicClosure ℚ deriving Field, IsAlgClosed, CharZero

instance : Algebra.IsAlgebraic ℚ Ω := AlgebraicClosure.isAlgebraic ℚ

/-- The valuation subrings of Ω: its finite places, together with Ω itself (the trivial
valuation). -/
abbrev ClosurePlace := ValuationSubring Ω

/-- The element c of Γ is a complex conjugation: for some embedding j : Ω → ℂ, j(cx) is the
complex conjugate of j(x) for all x. -/
def IsComplexConj {Γ} [SMul Γ Ω] (c : Γ) := ∃ j : Ω →+* ℂ, ∀ x, j (c • x) = star (j x)

variable (O Γ : Type*) (K Ω : outParam Type*) [Group Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] (l : ℕ) [Fact l.Prime] [CommRing O] [Algebra ℤ_[l] O]

/-- The multiplicative group Ω^×, written additively; it is given the discrete topology. -/
abbrev DiscreteUnits := Additive Ωˣ

instance : TopologicalSpace (DiscreteUnits Ω) := ⊥

instance : DiscreteTopology (DiscreteUnits Ω) := ⟨rfl⟩

/-- The profinite group Γ acts on the Galois extension Ω/K as its Galois group, with open
stabilisers. -/
class IsProGalois [TopologicalSpace Γ] extends IsGaloisGroup Γ K Ω, IsGalois K Ω,
    IsTopologicalGroup Γ, CompactSpace Γ, TotallyDisconnectedSpace Γ where
  isOpen_stabilizer (x : Ω) : @IsOpen Γ _ (stabilizer Γ x)

/-- A place `A` of `Ω` is read as its valuation: `A x`. -/
instance : CoeFun (ValuationSubring Ω) (Ω → ·.ValueGroup) := ⟨(·.valuation)⟩

variable {Ω} (A : ValuationSubring Ω)

/-- The decomposition group of a valuation subring A of Ω: the elements of Γ mapping A onto
itself. -/
abbrev decompGroup := stabilizer Γ A

/-- For a valuation subring A of Ω and x in K, the value of the image of x in Ω under the
multiplicative valuation attached to A. -/
abbrev valuationVia x := A (algebraMap K Ω x)

/-- The valuation subring A ∩ K of K. -/
abbrev valRingBelow := (A.valuation.comap (algebraMap K Ω)).valuationSubring

/-- Γ = Gal(Ω/K) with Ω algebraically closed of characteristic 0 stabilises A, and A ∩ K is a
discrete valuation ring with finite residue field: K is a henselian local field. -/
class IsLocalGalois (A : outParam (ValuationSubring Ω)) [TopologicalSpace Γ] extends IsProGalois Γ K
  Ω, IsAlgClosed Ω, CharZero Ω where
  mem_decompGroup g : g ∈ decompGroup Γ A
  dvr : IsDiscreteValuationRing (valRingBelow K A)
  finite_residue : Finite (IsLocalRing.ResidueField (valRingBelow K A))

variable {Γ K} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The ℤ-linear representation of Γ on Ω^× (written additively) coming from the action of Γ on
the field Ω by ring automorphisms. -/
def unitsRep : Representation ℤ Γ (DiscreteUnits Ω) :=
  @.ofMulDistribMulAction Γ _ _ _ mulDistribMulActionRight

/-- σ stabilises A and σx ≡ x^q modulo the maximal ideal for all x in A; for q the residue order
of the base, an arithmetic Frobenius. -/
def IsFrob q σ := σ ∈ decompGroup Γ A ∧ ∀ x, A.valuation x ≤ 1 → A.valuation (σ • x - x ^ q) < 1

/-- The valuation subring A of Ω lies over the prime v of K: an integer of K is in the maximal
ideal of A exactly when it lies in v. -/
def IsPlaceOver := ∀ x : 𝓞 K, A.valuation (algebraMap K Ω x) < 1 ↔ x ∈ v.asIdeal

variable {A q} {σ τ g : Γ} {Γ' Ω'} [Group Γ'] [Field Ω'] [MulSemiringAction Γ' Ω'] {φ : Γ' → Γ}
  {j : Ω →+* Ω'} (e : ∀ g x, j (φ g • x) = g • j x) {A' s q'} (h : IsFrob A q σ)

lemma mem_decompGroup_iff : σ ∈ decompGroup Γ A ↔ ∀ x, σ • x ∈ A ↔ x ∈ A :=
  ext'_iff.trans mem_stabilizer_set

lemma smul_eq_comap : g • A = A.comap (toRingHom _ _ g⁻¹) := ext' (Set.preimage_smul_inv ..).symm

lemma conj_mem_decompGroup_smul : σ ∈ decompGroup Γ A →
  g * σ * g⁻¹ ∈ decompGroup Γ (g • A) := by simp_all [mul_smul]

lemma isEquiv_comap : (comap A' j).valuation.IsEquiv (A'.valuation.comap j) :=
    Valuation.isEquiv_of_val_le_one (by simp)

lemma val_comap_lt_one {x} : (comap A' j) x < 1 ↔ A' (j x) < 1 := isEquiv_comap.lt_one_iff_lt_one

attribute [local simp↓] IsFrob mem_decompGroup_iff mul_smul smul_sub val_comap_lt_one

lemma val_smul_lt_one (g : Γ) {x} : (g • A) (g • x) < 1 ↔ A x < 1 := by rw [smul_eq_comap]; simp

include e

lemma decompGroup.map : s ∈ decompGroup _ A' → φ s ∈ decompGroup Γ (A'.comap j) := by aesop

lemma IsFrob.map : IsFrob A' q s → IsFrob (A'.comap j) q (φ s) := by simp_all

omit e
include h

lemma IsFrob.conj g : IsFrob (g • A) q (g * σ * g⁻¹) := by rw [smul_eq_comap]; aesop

/-- If σ is a Frobenius at A for the exponent q, then στ is a Frobenius for qq' exactly when τ
is a Frobenius for q'. -/
lemma IsFrob.mul_iff : IsFrob A (q * q') (σ * τ) ↔ IsFrob A q' τ := (mul_mem_cancel_left h.1).and
  (forall₂_congr fun x _ ↦ .trans (by simp [pow_mul']; rfl) ((add_mem_cancel_right
  (H := A.nonunits) (h.2 (x ^ q') (by grind [pow_le_one']))).trans (h.1 ▸ val_smul_lt_one σ)))

lemma IsFrob.pow n : IsFrob A (q ^ n) (σ ^ n) := n.rec (by simp) (by grind [mul_iff, pow_succ])

variable (Γ A) in
/-- The inertia group of A: the σ in Γ stabilising the valuation subring A with σx − x in the
maximal ideal for every x in A. -/
def inertiaGroup : Subgroup Γ :=
  ⟨⟨⟨{σ | IsFrob A 1 σ}, (·.mul_iff.2)⟩, by simp⟩, (·.mul_iff.1 (by simp))⟩

lemma IsFrob.inv_mul : IsFrob A q τ → σ⁻¹ * τ ∈ inertiaGroup Γ A := h.mul_iff.1 ∘ by simp

variable (Ω)

/-- The ℓ-adic cyclotomic character Γ → ℤ_ℓ^× of a group Γ acting on the field Ω by ring
automorphisms. -/
def cycChar : Γ →* ℤ_[l]ˣ := (cyclotomicCharacter Ω l).comp (toRingAut ..)

/-- The ℓ-adic cyclotomic character of Γ composed with ℤ_ℓ^× → O^×, for a commutative
ℤ_ℓ-algebra O. -/
abbrev cycCharIn := (map (algebraMap _ O).1).comp (cycChar (Γ := Γ) Ω l)
