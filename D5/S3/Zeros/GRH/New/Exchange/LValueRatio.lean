/- GID: D5/S3/Zeros/GRH/New/Exchange/LValueRatio
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Exchange/LValueRatio
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Exchange.LValueRatio. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Exchange/LValueRatio.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Seesaw.IndexTypes
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: records of the data and parameters of this proof, names for its objects.

Set-up for this proof: general results applied to the objects of this proof.

This file: Finitely many pairs (character, integer), from finiteness of tame Hecke characters.
Powers of tame characters, m-fold twists, characters of the chain. Ratio of twisted to untwisted
Hecke L-value; the trivial twist. -/

variable {P : Parameters} {D : Data P}

/-- Pairs are finitely many. -/
instance Data.finite_pair : Finite (@Pair P D) := .of_injective (β := Set.Iic (fun _ ↦ ⌊_⌋₊) ×
  Set.Icc 1 _ × AutChar.tameChars D.finite_isChosen.toFinset) (fun p ↦
  ⟨⟨_, id (Nat.le_floor <| p.9 ·)⟩, ⟨_, p.7⟩, (_, _),
  id ⟨by simpa [Set.apply_rangeSplitting Pair.c] using p.hasWeight.mul (Set.rangeSplitting
  Pair.c ⟨_, p, rfl⟩).hasWeight.inv, by simp_all [Pair.ψ_eq_one]⟩⟩) (by rintro ⟨⟩ ⟨⟩; aesop)

/-- For a tame character ϑ and a natural number n, the tame character ϑⁿ, with the same set Q
and tame part ψⁿ. -/
noncomputable def Data.TameChar.pow ϑ n :=
  @mk P D (toAutChar ϑ ^ n) _ (ϑ.ψ ^ n) (mod_cast ϑ.hasWeight.zpow n) (by simp_all [ϑ.5]) ϑ.6 ϑ.7

/-- An m-fold twist: a twist ϑ whose tame part has ψ_wⁿ non-trivial for all w in Q and 1 ≤ n ≤
m. -/
structure Data.MFoldTwist (D :
  Data P) extends D.Twist where pow_ne_one : ∀ n ∈ D.LiftIndex, ∀ w ∈ Q, ψ w ^ n ≠ 1

/-- For a tame character ϑ and a natural number j, the character μ_j⁰ϑ^j of U(1)(𝔸), used for
lift j of a chain; μ_j⁰ = `Data.μ₀` j. -/
noncomputable abbrev Data.chainChar (D : Data P) ϑ j := D.liftChar (.pow ϑ j) j

noncomputable instance Data.instOneTws (D : Data P) : One D.MFoldTwist := ⟨1, nofun⟩

instance Data.instCoeTwsTwist (D : Data P) : Coe D.MFoldTwist D.Twist := ⟨MFoldTwist.toTwist⟩

/-- For an m-fold twist ϑ and 1 ≤ n ≤ m, the power ϑⁿ as a twist. -/
noncomputable def Data.MFoldTwist.powTwist ϑ (n : LiftIndex D) :=
  Twist.mk (ϑ.pow n) (@pow_ne_one P D ϑ n n.2)

lemma Data.twist_one_spec : ((1 : D.Twist).toAutChar = 1 ∧ (1 : D.MFoldTwist).1 = 1) ∧
  (1 : D.Twist).Q = ∅ := by tauto

/-- The ratio |L(z, (νϑ^s)⁻¹)| / |L(z, ν⁻¹)|, Euler factors removed at the chosen places above g in
both, and at Q in the numerator. -/
noncomputable def Data.Pair.ratio (p : D.Pair) (ϑ : D.TameChar) (s : ℤˣ := 1) := (‖(p.ν *
  ϑ.toAutChar ^ s.1)⁻¹.L ({w | D.IsChosen w} ∪ ϑ.Q) p.z‖ / ‖p.ν⁻¹.L {w | D.IsChosen w} p.z‖ : ℂ)
