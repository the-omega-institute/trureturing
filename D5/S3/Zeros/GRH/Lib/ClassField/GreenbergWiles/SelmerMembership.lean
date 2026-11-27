/- GID: D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SelmerMembership
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/SelmerMembership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.GreenbergWiles.SelmerMembership. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/GreenbergWiles/SelmerMembership.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.Cyclotomic.Stickelberger.GaussSums
import D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles.SelmerRelations
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Greenberg–Wiles formula, as a lower bound for the dual side (known result; see
Lib.ClassField.GreenbergWiles.GreenbergWilesBound).

Set-up used by: Greenberg–Wiles formula, as a lower bound for the dual side.

This file: Membership in Selmer groups of cocycles; dropping conditions and places where
unramified. -/


open Matrix.Module
variable {E : Type} {Λ n B} [Field E] [EmbeddedNumberField E] [CommRing Λ] [Fintype n]
  [AddCommGroup B] [Module Λ B] {ρ : Gal(Ω/E) → Matrix n n Λ} {S T L K c}

lemma mem_selmerModule_iff : c ∈ selmerModule ρ S L B ↔ (∀ g h, c (g * h) = c g + ρ g • c h) ∧
  (∀ g ∈ inertiaAbove Sᶜ, c g = 0) ∧ c ∈ obeying L B ∧ IsLocallyConstant
  c := by simp [selmerModule, obeying, ↓iInf_union, ← mem_obeying_cocycleRels]; tauto

/-- A member c of the Selmer module for (S, L) lies in that for (T, K) if K ⊆ L and c vanishes
on inertia at all places of S outside T. -/
lemma selmerModule_mono (k : c ∈ selmerModule ρ S L B) (l : K ⊆ L) (h : ∀ v ∈ S \ T,
  ∀ g ∈ inertiaAbove {v}, c g = 0 := by simp) :
  c ∈ selmerModule ρ T K B := by simp_all [mem_selmerModule_iff, obeying, inertiaAbove]; grind
