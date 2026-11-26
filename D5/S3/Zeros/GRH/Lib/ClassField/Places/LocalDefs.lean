/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/LocalDefs
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/LocalDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.LocalDefs. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/LocalDefs.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.GaloisCohomology.CyclicClass
import D5.S3.Zeros.GRH.Lib.General.Analysis.OstrowskiTaussky
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

Part of: Local class field theory: invariant of the Brauer group, Artin map, norms, tame symbol
(known result; see Lib.ClassField.Local.ArtinMapAtPlace).

Part of: Galois cohomology in degrees ≤ 2: Shapiro, Hilbert 90, Kummer, symbols, Herbrand quotient
(known result; see Lib.ClassField.GaloisCohomology.CyclicNorm).

This file: Definitions: uniformiser, order, cyclotomic character, local invariant, local Artin map,
chosen place. -/

noncomputable section

open NumberField Units Classical


variable {Γ K Ω} [Group Γ] [Field K] [Field Ω] [Algebra K Ω] [MulSemiringAction Γ Ω] (A :
  ValuationSubring Ω) [TopologicalSpace Γ]

/-- The element π of K is a uniformiser for A: an x in K has A-valuation below 1 exactly when
its valuation is at most that of π. -/
def IsUniformiser π := ∀ x, valuationVia K A x < 1 ↔ valuationVia K A x ≤ valuationVia K A π

/-- For a subgroup H of Γ, the intermediate field of Ω/K consisting of the elements fixed by H. -/
abbrev fixedFieldOf [IsProGalois Γ K Ω] (H : Subgroup Γ) : IntermediateField K Ω :=
  FixedPoints.intermediateField H

section

variable (Ω) [IsTopologicalGroup Γ] (χ : QZChar Γ)

/-- The cyclotomic character modulo N: the homomorphism Γ → (ℤ/N)^× giving the action of Γ on
the N-th roots of unity in Ω. -/
def cycCharMod N [NeZero N] [HasEnoughRootsOfUnity Ω N] := (modularCyclotomicCharacter
  Ω (HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N)).comp (MulSemiringAction.toRingAut Γ Ω)

/-- A continuous character χ : Γ → ℚ/ℤ as a group homomorphism to ℚ/ℤ written multiplicatively. -/
def QZChar.toHom := MonoidHom.mk' (Multiplicative.ofAdd <| χ.1 ·) χ.2.2

/-- The kernel of a continuous character χ : Γ → ℚ/ℤ, as a subgroup of Γ. -/
abbrev QZChar.ker := (toHom χ).ker

/-- The homomorphism induced by the continuous character χ on the topological abelianisation of
Γ, with values in ℚ/ℤ written multiplicatively. -/
def QZChar.abelianLift : TopologicalAbelianization Γ →* Multiplicative QZ := QuotientGroup.lift _
  (toHom χ) (closure_minimal (Abelianization.commutator_subset_ker _) ⟨χ.2.1.1 {0}ᶜ ⟨⟩⟩)

variable (Γ)

/-- The homomorphism from K^× to the Γ-invariants of Ω^× (both written additively) induced by
the map K → Ω. -/
def DiscreteUnits.ofBase [SMulCommClass Γ K Ω] : Additive Kˣ →+ (@unitsRep Γ Ω _ _ _).invariants :=
  .codRestrict (map (algebraMap K Ω)).toAdditive _ fun _ _ ↦ ext (smul_algebraMap ..)

variable (K) {Ω}

/-- The number of elements of the residue field of the valuation ring of K induced by A (zero if
infinite). -/
abbrev residueCard := Nat.card (IsLocalRing.ResidueField (valRingBelow K A))

/-- The order normalised on K: a chosen additive f : Ω^× → ℚ with n f(x) = a exactly when x^n
and π^a have equal valuation, for uniformisers π of K. -/
def ordRat := epsilon fun f : DiscreteUnits Ω →+ ℚ ↦ ∀ π : Kˣ, IsUniformiser A π.1 →
  ∀ x (n : ℕ) (a : ℤ), A.valuation x.toMul ^ n = valuationVia K A π ^ a ↔ n * f x = a

/-- Property of an additive b: ℚ/ℤ → H²(Γ, Ω^×): it is injective, and (χ, w) = n·b(χ(φ)) for
unramified χ, Frobenius φ and invariant w of integer order n. -/
def IsClassOfInv (b : QZ →+ H2 (@unitsRep Γ Ω _ _ _)) := (⇑b).Injective ∧ ∀ χ,
  (∀ g ∈ inertiaGroup Γ A, χ.1 g = 0) → ∀ φ, IsFrob A (residueCard K A) φ → ∀ w (n : ℤ),
  ordRat K A w.1 = n → cyclicClass _ χ w = n • b (χ.1 φ)

/-- A chosen additive map ℚ/ℤ → H²(Γ, Ω^×) with the property `IsClassOfInv`; for a local field it
sends r to the class of invariant r. -/
def classOfInv := epsilon (IsClassOfInv Γ K A)

/-- The homomorphism f : L^× → Γ^ab satisfies χ(f x) = −inv(δχ ∪ x) for all characters χ and all
x, inv the local invariant; for L = K, the local Artin map. -/
def IsLocalArtin {L} [Field L] [Algebra L Ω] [SMulCommClass Γ L Ω] (f :
  Lˣ →* TopologicalAbelianization Γ) := ∀ χ x, classOfInv Γ K A
  (QZChar.abelianLift χ (f x)).toAdd = -cyclicClass _ χ (DiscreteUnits.ofBase _ Ω (.ofMul x))

end

variable (Γ) [IsProGalois Γ K Ω] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The local Artin map at v: a chosen homomorphism from K_v^× to the abelianised decomposition
group of A with χ(Art x) = −inv(χ, x) for all χ and x ∈ K^×. -/
def localArtin := epsilon fun f : (v.adicCompletion K)ˣ →* _ ↦ IsLocalArtin (decompGroup Γ A)
  (fixedFieldOf (decompGroup Γ A)) A (f.comp (map (algebraMap K _).1))

/-- For a finite prime v of the number field K, a chosen valuation subring of Ω lying over v. -/
def placeOver [Algebra K _root_.Ω] : ClosurePlace := epsilon (IsPlaceOver · v)
