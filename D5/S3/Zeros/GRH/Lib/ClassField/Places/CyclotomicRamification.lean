/- GID: D5/S3/Zeros/GRH/Lib/ClassField/Places/CyclotomicRamification
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/ClassField/Places/CyclotomicRamification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.ClassField.Places.CyclotomicRamification. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/ClassField/Places/CyclotomicRamification.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.ClassField.Places.FrobeniusOnRoots
import D5.S3.Zeros.GRH.Lib.ClassField.Places.TameInertia
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Hilbert ramification theory for infinite Galois extensions; ideles and ideal classes
(known result; see Lib.ClassField.Places.LocalFrobenius).

This file: Cyclotomic p-power tower of Q_p is totally ramified; inertia hits each cyclotomic
value. -/

variable {p} [ThePrime p] (a : ℕ)

/-- Let S ⊆ G_p be closed and a a natural number. If each primitive p^{k+1}-th root of unity ζ,
k ≥ 0, is sent to ζ^a by some element of S, then some g in S has cyclotomic character a. -/
lemma exists_cyclotomicGp_eq_of_isClosed {S} (hS : IsClosed S) (H : ∀ k ζ,
  IsPrimitiveRoot ζ (p ^ (k + 1)) → ∃ g ∈ S, g ζ =
  ζ ^ a) : ∃ g ∈ S, (cyclotomicGp g).1 = a := (Metric.mem_of_closed' ((Units.continuous_val.comp
  (continuous_cycChar p)).isClosedMap _ hS)).2 (@PadicInt.exists_pow_neg_lt p _ · · |>.rec fun k h ↦
  (H k _ HasEnoughRootsOfUnity.prim.choose_spec).rec fun g e ↦ ⟨_, by tauto, h.trans_le' (by
    erw [dist_eq_norm', PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton,
      pow_dvd_cycChar_sub_iff, cycCharMod_eq_of_dvd ⟨p,
      rfl⟩ (cycCharMod_eq_of_isPrimitiveRoot HasEnoughRootsOfUnity.prim.choose_spec e.2)])⟩)

/-- Every natural number a prime to p is the value of the cyclotomic character at some element
of the inertia group of G_p; that is, ℚ_p(μ_{p^∞}) is totally ramified. -/
lemma exists_inertia_cyclotomicGp_eq (c : p.Coprime a) : ∃ g ∈ inertiaGroup _ (intQpBar p),
  (cyclotomicGp g).1 = a := exists_cyclotomicGp_eq_of_isClosed a isClosed_inertiaGroup fun s ξ
  h ↦ by apply (exists_inertia_smul_eq_of_orbit_subset (x := ξ - 1) isUniformiser_ell
  (h.card_primitiveRoots ▸ Finset.card_image_le) _ _ (Finset.mem_image_of_mem (· - 1) (a := ξ ^ a)
  _)).imp <;> simp [← map_pow, le_antisymm_iff, valuation_intQpBar_le_iff, norm_zeta_sub_one_pow h,
  h.map_of_injective, AlgEquiv.injective, NeZero.pos, h.pow_of_coprime, c.symm.pow_right]
