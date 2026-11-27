/- GID: D5/S3/Zeros/GRH/Lib/GaloisRep/Main/LocalEmbedding
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/GaloisRep/Main/LocalEmbedding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.GaloisRep.Main.LocalEmbedding. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/GaloisRep/Main/LocalEmbedding.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.PadicDecomposition
import D5.S3.Zeros.GRH.Lib.PadicHodge.Crystalline.Defs
import D5.S3.Zeros.GRH.Lib.Weil.Unramified.SphericalHecke
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Local conditions: unramified or crystalline, finite type, killing polynomials, jumps.
Decomposition group versus local Galois group: Frobenius, inertia, cyclotomic character agree. -/

variable (ℓ) [ThePrime ℓ] (E m : Type) [Fintype m] [Field E] [Algebra E Ω]

/-- A homomorphism from Gal(Ω/E) to the invertible matrices over ℚ̄_ℓ with rows and columns
indexed by m; continuity is not part of the definition. -/
abbrev GalRep := Gal(Ω/E) →* GL m (PadicAlgCl ℓ)

/-- An embedding e : Ω → ℚ̄_ℓ inducing the place A, with a compatible open embedding j of the
decomposition group of A into Gal(ℚ̄_ℓ over ℚ_ℓ), as in `InducesPlace`. -/
class PadicPlaceEmbedding (A : ClosurePlace) (ℓ : outParam ℕ) [ThePrime ℓ] extends OverGp
  (decompGroup Gal(Ω/E) A) ℓ where (e) inducesPlace : InducesPlace E A e toGp

variable {ℓ E m} (r : GalRep ℓ E m) (A : ClosurePlace) [NumberField E] [PadicIso ℓ] (R : ℕ → ℕ →
  Prop) (J : (E →+* ℂ) → Multiset ℤ) (w : FinPlace E)

/-- The restriction of r to the decomposition group of A, acting on column vectors over ℚ̄_ℓ. -/
noncomputable abbrev decompRep := matrixRep (r.comp (decompGroup _ A).subtype)

/-- r is trivial on the inertia group of A if ℓ is a unit at A, and crystalline along every
embedding in Q̄_ℓ inducing A. -/
def IsGoodAt := (A.valuation ℓ = 1 → ∀ s ∈ inertiaGroup _ A, r s = 1) ∧
  ∀ [PadicPlaceEmbedding E A ℓ], IsCrystalline (decompRep r A)

/-- r is trivial on the inertia elements near 1 if ℓ is a unit at A, and potentially crystalline
along every embedding in Q̄_ℓ inducing A. -/
def IsFiniteTypeAt := (A.valuation ℓ = 1 → ∀ᶠ s in nhds 1, s ∈ inertiaGroup _ A → r s = 1) ∧
  ∀ [PadicPlaceEmbedding E A ℓ], IsPotCrys (decompRep r A)

/-- P kills s at A: P(r(s)) = 0 if ℓ is a unit at A, and `IsKilledBy` holds for every Weil
pair (s, k) along every embedding in ℚ̄_ℓ inducing A. -/
def PolyKillsAt s P := (A.valuation ℓ = 1 → Polynomial.aeval (r s).1 P = 0) ∧
  ∀ [L : PadicPlaceEmbedding ..] ⦃h k⦄, IsWeilPair (L.toGp ⟨s, h⟩) k →
  IsKilledBy (decompRep r A) ⟨s, h⟩ k P

/-- For each embedding inducing A above ℓ, each compatible τ: E → Q̄_ℓ and each integer u, R
relates the multiplicity of u in J(τ) to that as Hodge–Tate jump of r. -/
def JumpsRelAt := ∀ ⦃L : PadicPlaceEmbedding E A ℓ⦄ ⦃γ⦄ ⦃g : Gp ℓ⦄, (∀ x, γ x = ↑(g x)) → ∀ u,
  R ((J (.comp ιℓ.symm
  (.comp ↑g⁻¹ (L.e.comp (algebraMap ..)) : E →+* PadicAlgCl ℓ))).count u) (jump (decompRep r A) γ u)

/-- For each embedding inducing A above ℓ and each compatible τ: E → Q̄_ℓ, the Hodge–Tate jumps
of r, with multiplicity, are J(τ). -/
abbrev HasJumpsAt := JumpsRelAt r A Eq J

/-- Occurrence, as a relation between multiplicities: if m is nonzero, so is n. -/
abbrev OccursIn m n := m ≠ 0 → n ≠ 0

/-- At every A above w: r is unramified or crystalline, its jump multiplicities are related to J
by R, and P kills every geometric Frobenius. -/
def SphericalClause P := ∀ ⦃A⦄, IsPlaceOver A w → IsGoodAt r A ∧ JumpsRelAt r A R J ∧
  ∀ s, IsFrob A w.q s⁻¹ → PolyKillsAt r A s P

variable {ℓ : _} [ThePrime ℓ] {E : _} [Field E] [Algebra E Ω] {A : _} [h :
  PadicPlaceEmbedding E A ℓ]

/-- For s in the decomposition group of A and j = h.toGp, the map to Gal(ℚ̄_ℓ/ℚ_ℓ): j(s) induces
x ↦ x^q on the residue field of ℚ̄_ℓ if and only if s induces x ↦ x^q on that of A. -/
lemma PadicPlaceEmbedding.isFrob_iff {q s} : IsFrob (intQpBar ℓ) q (h.toGp s) ↔ IsFrob A q s.1 := by
  obtain @⟨_, e, ⟨⟨⟩, k⟩, -⟩ := h
  simpa [IsFrob, isLocalGalois_padic.4, val_comap_lt_one, ← k,
    ← mem_ball_zero_iff, -Metric.mem_ball, -AlgEquiv.smul_def] using
    ⟨by tauto, (isClosed_property (denseRange_emb_padicAlgCl e) (isClosed_imp (Valued.isOpen_integer
    (PadicAlgCl ℓ)) (IsUltrametricDist.isClosed_ball ..).preimage_of_continuous) ·)⟩

lemma PadicPlaceEmbedding.isWeilPair_zero_iff {s} : IsWeilPair (h.toGp s) 0 ↔
  s ∈ inertiaGroup _ A := _root_.isWeilPair_zero_iff.trans isFrob_iff

lemma PadicPlaceEmbedding.cyclotomicGp_eq_cycChar g : cyclotomicGp (h.toGp g) = cycChar Ω ℓ g.1 :=
  (cycChar_eq_of_equivariant ℓ (symm ∘' h.inducesPlace.1.2 g)).symm
