/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Characters/LocalCharacters
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Characters/LocalCharacters
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Characters.LocalCharacters. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Characters/LocalCharacters.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Global.Avatars
import D5.S3.Zeros.GRH.Lib.ClassField.HeckeL.AutCharLFunction
import D5.S3.Zeros.GRH.Lib.PadicHodge.Characters.UnramifiedPeriods
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Known result: Characters with finite image on inertia are potentially crystalline of weight 0.
This file treats only the potentially unramified case of the theorem on locally algebraic
characters, with the jumps and the action of Weil elements. The period is a solution of Lang's
equation for GL_1 in A_inf with coefficients, and no Lubin–Tate theory is used. Source: B. Conrad,
Lifting global representations with local properties (preprint 2011), Appendix B; J.-P. Serre,
Abelian l-adic representations (1968), III, Appendix.

This file: Local behaviour of l-adic avatars and of characters with finite inertia image. -/


open NumberField Matrix.GeneralLinearGroup Polynomial QuotientGroup AlgHeckeChar
variable {ℓ} [ThePrime ℓ] [PadicIso ℓ] {E} [Field E] [EmbeddedNumberField E] {A : ClosurePlace} {w :
  FinPlace E} {μ : Gal(Ω/E) →* (PadicAlgCl ℓ)ˣ} {m} [Fintype m]

lemma JumpsRelAt.congr {r : GalRep ℓ E m} {R J J'} (hA : IsPlaceOver A w) (h : JumpsRelAt r A R J)
    (h' : ∀ τ, inducedPrime τ = w → J τ = J' τ) : JumpsRelAt r A R J' := by
  refine fun a _ g k ↦ h' _ ?_ ▸ h k; ext
  simpa [hA.unique (a.inducesPlace.1.1 ▸ isPlaceOver_placeOfEmb _)]
    using congr($(norm_smul_Cp g⁻¹ (a.e _)) < 1)

/-- A continuous ℓ-adic character μ with finite image on inertia at A is of finite type at A
(potentially crystalline above ℓ), has the single jump 0, and X − μ(s) kills every s.

Known result: Characters with finite image on inertia are potentially crystalline of weight 0. -/
lemma isFiniteTypeAt_char [Unique m] (c : Continuous μ) (H :
  (μ '' inertiaGroup Gal(Ω/E) A).Finite) : let r := (scalar m).comp μ
  IsFiniteTypeAt r A ∧ HasJumpsAt r A (fun _ ↦ {0}) ∧ ∀ s, PolyKillsAt r A s (X - C (μ s).1) :=
  have I := ((H.sep (· ≠ 1)).isClosed.preimage c).compl_mem_nhds (by simp)
  have K [l : PadicPlaceEmbedding ..] := isPotCrys_of_unramified_char l.inducesPlace.2.1 (ν :=
    μ.domRestrict (decompGroup ..)) (c.comp continuous_subtype_val)
    (.mono (continuousAt_subtype_val I) (by aesop (add simp l.isWeilPair_zero_iff))) (by simp)
  ⟨⟨fun _ ↦ .mono I (by aesop), K.1⟩, by simp [JumpsRelAt, K, hasJumps_of_cyclotomicGp_zpow 0 _ _],
  fun _ ↦ ⟨by aesop, K.2.2 _ _⟩⟩

variable [IsTotallyComplex E] (θ : AlgHeckeChar E)

variable (w) in
/-- At each A over w the avatar of θ has finite type, jumps −n(ι⁻¹τ); each s of degree m ≤ 1 is
Art(x), ord x = m, with X − ιθ_w(x) killing s. -/
def AvatarCompatAt := ∀ ⦃A⦄, IsPlaceOver A w → let r := (scalar (Fin 1)).comp θ.avatar
  IsFiniteTypeAt r A ∧ HasJumpsAt r A ({-θ.1.2.toAdd ·}) ∧ ∀ s, ∀ m ≤ (1 : ℕ), ∀ h :
    IsFrob A (w.q ^ m) s⁻¹, ∃ x, Valued.v x.1 = .exp (-m) ∧ localArtin Gal(Ω/E) A w x =
    (⟨s, inv_mem h.1⟩ : decompGroup ..) ∧ PolyKillsAt r A s (X - C (ιℓ (θ.1.1 (locIdele w x))))

/-- If w ∤ ℓ and θ is unramified at w, the ℓ-adic avatar of θ at a geometric Frobenius at A over
w equals ι of the value of θ at the local idele of the chosen uniformiser at w. -/
lemma AlgHeckeChar.avatar_frob (hA : IsPlaceOver A w) (l : ↑ℓ ∉ w.1) (u :
  CharUnramifiedAt θ.1.1 w) {s} (hs : IsFrob A w.q s⁻¹) : (avatar θ s).1 =
  ιℓ (heckeCoeff θ.1.1 ∅ w) := (hA.exists_localArtin_eq hs 1).elim fun z e ↦ by simp [e,
  u.apply_locIdele_eq_zpow z, heckeCoeff, θ.avatar_localArtin hA (.inl l) e.2]

lemma AlgHeckeChar.eventually_avatar_frob : ∀ᶠ y in mostFrobenii E, (avatar θ y.frob).1 =
  ιℓ (heckeCoeff θ.1.1 ∅ y.w) := eventually_mostFrobenii ((eventually_unramified _ θ.2.1).and
  (finite_natCast_mem ℓ).compl_mem_cofinite) fun y ⟨a, b⟩ ↦ θ.avatar_frob y.isPlaceOver b a y.isFrob

/-- Local-global compatibility `AvatarCompatAt` holds at A over w for the ℓ-adic avatar of an
algebraic Hecke character θ of a totally complex E whose exponent n_σ vanishes for every σ
with ισ inducing w. -/
lemma avatarCompatAt_of_type_eq_zero (hk : ∀ σ, inducedPrime σ = w → θ.1.2.toAdd σ = 0) :
  AvatarCompatAt w θ := fun _ hA ↦ (isFiniteTypeAt_char (by fun_prop) (.of_surjOn (.map ιℓ ∘ kerLift
  _) (fun _ ⟨_, k, e⟩ ↦ (hA.exists_localArtin_eq (inv_mem k) 0).elim fun x ⟨a, h⟩ ↦
  ⟨_, ⟨_, locIdele_mem_idelesUnitOff a, rfl⟩, e ▸ Units.ext (θ.avatar_localArtin hA (.inr hk)
  h).symm⟩) (finite_quotient_image_of_isCompact θ.2.1 isCompact_idelesUnitOff_empty))).imp_right
  (.imp (·.congr hA (by grind)) fun p _ m _ h ↦
  (hA.exists_localArtin_eq h m).imp fun _ b ↦ by simp [*, ← θ.avatar_localArtin hA (.inr hk) b.2])

/-- If `AvatarCompatAt` holds at w and θ is unramified at w, then at every A over w its ℓ-adic
avatar is unramified (crystalline above ℓ), has jump −n(ι⁻¹τ) at τ, and X − ιθ_w(ϖ) kills
every geometric Frobenius. -/
lemma AvatarCompatAt.sphericalClause_of_unramified {θ} (H : AvatarCompatAt w θ) (h :
  CharUnramifiedAt θ.1.1 w) : SphericalClause ((scalar (Fin 1)).comp (avatar θ)) Eq
  ({-θ.1.2.toAdd ·}) w (X - C (ιℓ (heckeCoeff θ.1.1 ∅ w))) := by
  peel 2 H
  choose a b x e _ p using this
  simpa [isGoodAt_iff, *, heckeCoeff, h.apply_locIdele_eq_zpow (x ..)] using
    And.intro (p · 0 bot_le <| inv_mem ·) (p · 1)
