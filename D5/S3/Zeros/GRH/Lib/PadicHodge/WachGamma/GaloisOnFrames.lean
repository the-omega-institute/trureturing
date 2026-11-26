/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/GaloisOnFrames
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/WachGamma/GaloisOnFrames
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.WachGamma.GaloisOnFrames. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/WachGamma/GaloisOnFrames.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.WachKisin.FrameTheorem
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Kisin modules: Galois action trivial modulo the variable, Hodge–Tate weights read off
(known result; see Lib.PadicHodge.WachGamma.Letters).

This file: Galois stability of the Kisin lattice; congruence step towards triviality modulo the
variable. -/

variable {p} [ThePrime p] [Γ : GroupOverGp p] {k : Lift.KummerChart Γ} {O} {L :
  Lift.KummerChart.JumpLattice O} {x μ g} (hg : ∀ h ∈ k.Γ', g * h * g⁻¹ ∈ k.Γ')

namespace Lift.KummerChart.JumpLattice

lemma pow_smul_gal_sub_mem_span_of_dvd {g : Gp p} {d m x} (o : ∀ {y}, y ∈ k.bicommutant →
  d ∣ g • y - y) : (∃ s ∈ k.bicommutant, k.E.1 ^ m • x = algebraMap _ BdR s) → k.E.1 ^ (2 * m) •
  (g • x - x) ∈ BPlus ∙ algebraMap _ _ d := fun ⟨s, f, e⟩ ↦ Submodule.mem_span_singleton.2 (by
  obtain ⟨_, ⟨v, _⟩, ⟨r, _⟩, t, _⟩ := congr(g • $e), pow_dvd_pow_of_dvd (k.associated_smul_E g).dvd'
    m, o (k.ainfToBPlus_mem_bicommutant (k.E ^ m)), o f
  apply_fun algebraMap _ BdR at *
  use v • (k.E.1 ^ m • t - r * s)
  simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, pow_mul'] at *
  grind)

include hg

lemma conjForm_mem_forms (h : μ ∈ L.forms) : conjForm μ g ∈ L.forms := fun t s ↦ by
  simpa [mul_smul, inv_smul_eq_iff] using h (L.ρ g t) ⟨_, hg _ s.2⟩

/-- If g in Γ satisfies gΓ'g⁻¹ ⊂ Γ', then g maps the module `Lift.KummerChart.JumpLattice.kisinAinf`
of L into itself. -/
lemma smul_mem_kisinAinf : x ∈ kisinAinf → FrobGroup.inr g • x ∈ L.kisinAinf :=
  .imp (fun ⟨_, ⟨n, rfl⟩, s⟩ ↦ mem_saturateBy_of_smul (by simp [associated_smul_tau.pow_pow.dvd])
  ⟨n, rfl⟩ (le_saturateBy (frobGroup_smul_smul .. ▸ smul_mem_ainfLattice _ s))) fun h n _ e ↦ by
  simpa [smul_smul, ((FrobGroup.phi_mul_comm _).pow_left _).eq] using
    smul_mem_hodgeFil (toGp g) (h n _ (conjForm_mem_forms hg e))
