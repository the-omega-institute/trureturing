/- GID: D5/S3/Zeros/GRH/New/Selmer/LevelPlacesChosen
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Selmer/LevelPlacesChosen
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Selmer.LevelPlacesChosen. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Selmer/LevelPlacesChosen.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.GaloisRep.Main.AvatarCompatibility
import D5.S3.Zeros.GRH.New.Exchange.TriangleLevelExponent
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Also holds known results stated on this proof's data: ℓ-adic avatar of an algebraic Hecke character
and its local behaviour (known result; see Lib.GaloisRep.Main.AvatarCompatibility).

This file: Avatars of algebraic characters: conjugate duality, inertia action; names for Galois
group and places. Apt tuples sit at chosen places; distinct N-th roots of
unity in ℚ̄_ℓ are at least ‖N‖ apart. -/

open Matrix.GeneralLinearGroup Polynomial Units AlgHeckeChar WeilData AutChar.HasWeight
variable {P} (D : Data P) (ℓ) [ThePrime ℓ]

/-- An embedding `E → ℚ(μ_cond) ⊆ ℚ̄`, fixed once and for all. -/
noncomputable instance : UnramCMField D.E :=
  {((cycloField _).val.comp P.toCycloField).toAlgebra with}

lemma Data.algebraMap_mem_cycloField x : algebraMap D.E Ω x ∈ cycloField D.cycloConductor :=
  Subtype.prop _

/-- The absolute Galois group of the field E of the data D: automorphisms of an algebraic
closure of E fixing E. -/
abbrev AbsGal := Gal(Ω/D.E)

/-- The set of finite places of E above one of the two primes g₀, g₁ of the data. -/
def placesAboveG := {v : FinPlace D.E | ∃ i, ↑(D.g i) ∈ v.1}

/-- The finite set of places of E that divide ℓgN, where g = g₀g₁ and N is the level of the
data. -/
noncomputable def badPlaces := (finite_natCast_mem (K := D.E) (ℓ * (D.gProd * D.N))).toFinset

@[grind .] lemma placesDividing_union_subset_badPlaces w : w ∈ placesDividing _ ℓ ∪ placesAboveG D →
  w ∈ badPlaces D ℓ := by
  simp_all [badPlaces, placesAboveG, placesDividing, Data.gProd, w.2.mul_mem_iff_mem_or_mem, or_imp]

variable {D ℓ}

@[simp, grind =] lemma star_mem_placesAboveG {v} : star v ∈ placesAboveG D ↔
  v ∈ placesAboveG D := by simp [placesAboveG]

/-- If x ≠ y are N-th roots of unity in ℚ̄_ℓ, then ‖N‖ ≤ ‖x − y‖. -/
lemma norm_natCast_le_norm_sub_of_pow_eq_one {x y : PadicAlgCl ℓ} {N : ℕ} : x ^ N = 1 → y ^ N = 1 →
  x ≠ y → ‖(N : PadicAlgCl ℓ)‖ ≤ ‖x - y‖ := by grind [=_ valuation_intQpBar_le_iff,
  eq_of_pow_eq_one_of_val_sub_lt]

@[fun_prop] lemma continuous_cycInv : Continuous (cycInv ℓ D.E (PadicAlgCl ℓ)) :=
  continuous_coe_inv.comp continuous_cycCharIn

lemma cycInv_eq_of_isFrob (x : FrobeniusDatum D.E) (h : ↑ℓ ∉ x.w.1) :
  cycInv ℓ _ (PadicAlgCl ℓ) x.frob = x.w.q := by
  simp_all [cycInv, ← map_inv, x.isFrob.cycChar_eq ℓ, x.isPlaceOver.valuation_natCast_eq_one_iff]

variable [PadicIso ℓ] {a : AutChar D.E} {e ψ} (h : a.HasWeight e ψ) (k j : ℤ)

/-- The ℓ-adic avatar, through ι, of the base change to E of ϑ⁻¹: a character of the absolute
Galois group of E with values in ℚ̄_ℓ. -/
noncomputable def Data.TameChar.invAvatar (ϑ : D.TameChar) : AbsGal D →* PadicAlgCl ℓ :=
  (coeHom _).comp (ϑ.hasWeight.inv.toAlgebraic 0 0).avatar

/-- The ℓ-adic avatar μ of the algebraic character bc(a)·υ^{−k}·|·|^{j−k/2} satisfies μ(g^c)
μ(g) = cyc(g)^{2j−k} for all g. -/
lemma avatar_conjGal_mul : ∀ g, let μ := (h.toAlgebraic k j).avatar
  μ (conjGal g) * μ g = cycCharIn _ Ω ℓ g ^ (2 * j - k) := (dense_of_mostFrobenii
  (eventually_mostFrobenii (eventually_notMem_star_notMem ℓ h.1.toFinset) fun x _ ↦ by
  obtain _ := upsilon_atUnif_mul_star (star x.w), x.isFrob, x.isFrob.conjPlace_conjGal,
    @h.atUnif_star
  simp_all [← val_inj, avatar_frob _ x.isPlaceOver, avatar_frob _ x.isPlaceOver.conjPlace_star,
    charUnramifiedAt_toAlgebraic, congr(ψ $(star_star x.w) = 1)]
  simp [toAlgebraic, HeckeChar.atUnif, heckeCoeff] at *
  simp [*, field, sq, ← mul_zpow, ← map_mul, ← Complex.ofReal_mul, ← cycInv_eq_of_isFrob,
    cycInv])).induction (fun _ ↦ id) (by apply isClosed_eq <;> fun_prop)

/-- Let w be split, A a place over w, and the tame part ψ of a trivial at w̄. Then inertia at A
acts on the avatar of bc(a)·υ^{−k}·|·|^{j−k/2} through the tame character given by the label
of ψ_w. -/
lemma isLabelledAt_avatar {w A f} (b : ψ (star w) = 1) (c :
  w.IsSplit) : let T := faithfulChar (ResField w); IsLabelledAt A T f (PolyKillsAt ((scalar
    (Fin 1)).comp (h.toAlgebraic k j).avatar) A) (X - C (charName T (ψ w)).1) := fun s y hy ↦ by
  choose x a b H using
    (avatarCompatAt_of_stablyUnram (h.toAlgebraic k j) hy.1).2.2 s 0 bot_le (inv_mem hy.2.2.1)
  simpa [*, hy.pow_apply_charName _ a b, toAlgebraic, baseChange_finPart_locIdele,
    charUnramifiedAt_upsilon ..] using H

lemma isChosen_chosenPlace {P} {D : Data P} {ϑ L} (h : L = D.levelPlaces ϑ) i :
  D.IsChosen (L.chosenPlace i) ∧ ϑ.ψ (L.chosenPlace i) = 1 ∧
  L.chosenPlace i ∈ placesAboveG D := by rcases L, h with ⟨⟨⟩, ⟨⟩⟩; grind [Data.chosen,
  placesAboveG, → D.levelNorm_mem_and_notMem_of_mem_Q, Data.IsChosen, ϑ.5]
