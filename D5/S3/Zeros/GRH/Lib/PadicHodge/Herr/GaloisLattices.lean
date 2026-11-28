/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Herr/GaloisLattices
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Herr/GaloisLattices
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Herr.GaloisLattices. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Herr/GaloisLattices.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Limit.HodgeTateProjectors
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Artin–Schreier–Witt resolution over the tilt (known result; see
Lib.PadicHodge.WachGamma.KisinModuleDefs).

Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius (known
result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

Set-up used by: Artin–Schreier–Witt resolution over the tilt. -/

noncomputable section

namespace Lift

variable {p} [ThePrime p] (O Γ : Type) [CommRing O] [Algebra ℤ_[p] O] [Group Γ]

/-- A finite free O-module, with compatible Z_p-module structure, together with an O-linear
representation of the group Γ on it. -/
structure GalLattice where
  (Carrier) [addCommGroup : AddCommGroup Carrier] [moduleO : Module O Carrier] [moduleZp :
    Module ℤ_[p] Carrier]
  [isScalarTower : IsScalarTower ℤ_[p] O Carrier] [free : Module.Free O Carrier] [module_finite :
    Module.Finite O Carrier]
  ρ : Representation O Γ Carrier

open Module Submodule GalLattice TensorProduct Polynomial AdjoinRoot

attribute [instance] GalLattice.addCommGroup moduleO moduleZp GalLattice.isScalarTower free
  module_finite

instance : CoeSort (GalLattice O Γ) Type := ⟨Carrier⟩

variable {O Γ} [OverGp Γ p] (F) (K : Γ → _ → Prop) (U : _ → Finset ℤ) (Y L : GalLattice O Γ)

/-- The twisted dual L^∨(1) = Hom_O(L, O(1)) of a lattice L, with Γ acting on O(1) through the
cyclotomic character. -/
abbrev GalLattice.tateDual := mk _ (L.ρ.linHom (actionRep O O χ))

/-- Y is admissible for periods fixed both near 1 and F-almost everywhere, has jumps in U(g) at
each embedding g, and Q kills (s, 0) whenever K(s, Q) and j(s) is in inertia. -/
def InClass := IsAdmissible Y.ρ (nearOne Γ ⊔ F) ∧ (∀ g u, jump Y.ρ g u ≠ 0 → u ∈ U g) ∧
  ∀ s Q, K s Q → IsWeilPair (toGp s) 0 → IsKilledBy Y.ρ s 0 Q

lemma InClass.isPotCrys (h : InClass F K U Y) : IsPotCrys Y.ρ := h.1.mono (by simp)

/-- The tensor product Y ⊗_O L of two lattices, with the diagonal action of Γ. -/
abbrev GalLattice.tensor := mk _ (Y.ρ.tprod L.ρ)

/-- A pairing of Y and L modulo p^m: an O-linear ψ: Y ⊗ L → O(1) with gψ − ψ = p^m c(g) for a
crystalline cocycle c, and a Z_p-linear f: O → Z_p. -/
structure Pairing where
  (m) (integralForm) (toZp : Dual ℤ_[p] O) (thirdClass : crysCocycles (Y.tensor L).tateDual.ρ)
  pow_smul_thirdClass g : p ^ m • thirdClass.1 g = ρ _ g integralForm - integralForm

variable {Y L} (P : Pairing Y L) [Free ℤ_[p] O]

/-- The Z_p-bilinear pairing Y × L → Z_p/p^m sending (y, l) to f(ψ(y ⊗ l)) modulo p^m, for the
form ψ and the functional f: O → Z_p of P. -/
def Pairing.modPairing := ((curry P.integralForm).restrictScalars₁₂ ℤ_[p] ℤ_[p]).compr₂ (Qₗ :=
  QuotSpan (p ^ P.m : ℤ_[p])) (mkQ _ ∘ₗ P.toZp)

/-- The cup product (g, h) ↦ b(a(g), g·c(h)), with b the `modPairing` of P and Z/p^m(1) ⊂ Q̄_p^×,
is the coboundary of a continuous cochain Γ → Q̄_p^×. -/
def Pairing.CupBounds [TopologicalSpace Γ] (a c : Γ → _) :=
  (fun q ↦ zmodPowToUnits _ (P.modPairing (a q.1) (L.ρ q.1 (c q.2)))) ∈ B2 (unitsRep.comp toGp)

attribute [-simp] nsmul_eq_mul
attribute [local simp] Pairing.CupBounds extensionRep Units.smul_def

/-- The O-module L^{⊥𝒬} of functions c: Γ → L whose cup product with every a in Z_f(Y) bounds
(`Lift.Pairing.CupBounds`), for all Y in 𝒬, m and pairings `Lift.Pairing` of Y and L. -/
def cupOrthogonal [TopologicalSpace Γ] (𝒬 : GalLattice O Γ → Prop) L :=
  Submodule.mk ⟨⟨{c | ∀ Y (P : Pairing Y L), 𝒬 Y → ∀ a ∈ crysCocycles Y.ρ,
  P.CupBounds a c}, by simp_all [← Pi.add_def, add_mem]⟩, by simp [← Pi.zero_def]⟩ fun (o : O) ↦
  (fun _ ↦ by simpa [Pairing.modPairing] using · · · · _ ∘ smul_mem _ o)

instance : Free ℤ_[p] L := .trans (S := O)

/-- The O-valued pairing ((λ, o), t) ↦ (p^m λ + oψ)(t) of Y ⊗ L with the extension of O by (Y ⊗
L)^∨(1) along the cocycle c of P. -/
def Pairing.thirdPairing := LinearMap.coprod (p ^ P.m • .id) (.toSpanSingleton O _ P.integralForm)

/-- The O-valued pairing β of Y ⊗ L with the extension of O by (Y ⊗ L)^∨(1) attached to P is
equivariant into the Tate twist: β(gx, gt) = χ(j(g))·β(x, t) for g in Γ, with χ the
cyclotomic character. -/
lemma Pairing.thirdPairing_equivariant g x t : P.thirdPairing (extensionRep (.toSpanSingleton _ _
  P.thirdClass) g x) (ρ _ g t) = χ g • P.thirdPairing x t := by simp [thirdPairing,
  smul_comm (p ^ _), P.pow_smul_thirdClass, -Representation.tprod_apply, smul_sub]; abel

lemma Pairing.modPairing_rho g y l : P.modPairing (Y.ρ g y) (L.ρ g l) =
  χ g • P.modPairing y l := by simpa [thirdPairing, nsmul_quot_eq_zero] using!
  congr((P.toZp $(P.thirdPairing_equivariant g (0, 1) (y ⊗ₜ l)) : QuotSpan (p ^ P.m : ℤ_[p])))

variable [Module.Finite ℤ_[p] O] [IsDomain O] {F K U K' U'} (h : InClass F K U Y) (h' :
  InClass F K' U' L)

instance : Module.Finite ℤ_[p] L := .trans O _
