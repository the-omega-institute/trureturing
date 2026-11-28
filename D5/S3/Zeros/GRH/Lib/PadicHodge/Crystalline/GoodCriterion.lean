/- GID: D5/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/GoodCriterion
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/Lib/PadicHodge/Crystalline/GoodCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module Lib.PadicHodge.Crystalline.GoodCriterion. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Lib/PadicHodge/Crystalline/GoodCriterion.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.Lib.PadicHodge.Limit.LocalLimit
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Potentially crystalline representations, Hodge–Tate weights, Weil–Deligne Frobenius
(known result; see Lib.PadicHodge.Crystalline.RegularityFrobenius).

This file: Potentially crystalline with inertia acting trivially on D_pcris implies crystalline.
Crystalline iff potentially crystalline with trivial inertia action; a multiple of a killing
polynomial kills. -/

open Submodule Subgroup IsIntegral Module.End NonarchimedeanGroup

/-- Let j have open image in G_p and T be potentially crystalline. If every s in Γ with j(s) in
inertia fixes each element of D_pcris(T), the elements of B⊗T fixed near 1, then T is
crystalline. -/
lemma IsPotCrys.isCrystalline_of_inertia_fixes {p} [ThePrime p] {Γ R T} [Group Γ] [CommRing R]
  [AddCommGroup T] [Module R T] [Algebra ℤ_[p] R] [Module ℤ_[p] T] [IsScalarTower ℤ_[p] R T] [𝒥 :
  OverGp Γ p] {ρ : Representation R Γ T} (h : IsPotCrys ρ) (hI : ∀ s, IsWeilPair (toGp s) 0 →
  linearFrob ρ s 0 = 1) : IsCrystalline ρ := eq_top_mono (span_le.2 fun y a ↦ by
  let ⟨V, W⟩ := is_nonarchimedean _ (nhds_one_le_map_nearOne Γ (Filter.image_mem_map a))
  let U := id (OpenSubgroup.mk (inertiaGroup _ (intQpBar p) ⊔ V.1) (isOpen_mono le_sup_right V.2))
  choose c hf _ hE _ using Lift.exists_kummer_chart _ (𝒥 := ⟨_, ⟨U.1.range_subtype ▸ U.2⟩⟩)
  refine (span_subset_span ..) (mem_span_fixed (L := (isField_of_isIntegral_of_isField' (S :=
    integralClosure ℚ_[p] Bcris) (Field.toIsField ℚ_[p])).toField) 𝒥.toGp (.tprod (actionRep _ Bcris
    toGp) (overZp _)) (fun _ _ _ ↦ tensorAction_smul ..) (fun g m ↦ ?_) fun s n ↦
    U.1.range_subtype.le (c.chart_isChartOf s ⟨fun a ↦ by
    simpa using injective_BPlus_Bcris ((smul_algebraMap_eq_algebraMap_smul ..).symm.trans congr($(
                  n ⟨⟨_, (of_finite ℤ_[p] a).algebraMap.algebraMap.tower_top⟩, fun u ↦
      Subtype.ext ((smul_algebraMap_eq_algebraMap_smul ..).trans
      (congrArg _ ((hf u).1 a)))⟩).1)), by simp [← sub_eq_of_eq_add (hE _).1, c.theta_E, U]⟩))
  let ⟨i, k, _, v, e⟩ := mem_sup_of_normal_left (hs := ⟨fun _ h g ↦
    isLocalGalois_padic.4 g ▸ h.conj g⟩).1 m
  obtain ⟨t, w, rfl⟩ := W v
  erw [← div_mul_cancel g t, map_mul, mul_apply, w, ← linearFrob_apply h, hI] <;>
    simp [isWeilPair_zero_iff, ← e, k, a]) h

variable {ℓ E m A} [ThePrime ℓ] [Field E] [EmbeddedNumberField E] [Fintype m] {r : GalRep ℓ E m}

/-- Let A be a place not above ℓ, r finite on inertia at A, and s an inertia element killed by
P. Then p(r(s)) = 0 for every polynomial p vanishing at all roots of P. -/
lemma IsFiniteTypeAt.aeval_eq_zero_of_roots (h : IsFiniteTypeAt r A) (hA : A ℓ = 1) {s} (hs :
  s ∈ inertiaGroup _ A) {P} (hP : PolyKillsAt r A s P) p : (∀ x, P.IsRoot x → p.IsRoot x) →
  Polynomial.aeval (r s).1 p = 0 := map_eq_zero_of_roots _ (by simpa [pow_mem hs, Units.ext_iff]
  using! ((mapClusterPt_one_atTop_pow s).frequently (h.1 hA)).forall_exists_of_atTop 1) (hP.1 hA)

lemma PolyKillsAt.of_dvd {s P Q} : PolyKillsAt r A s P → P ∣ Q → PolyKillsAt r A s Q := by
  grind -linarith [PolyKillsAt, IsKilledBy, Polynomial.eval₂_mul_noncomm,
    commute_coefEnd_linearFrob, dvd_def]

/-- At a place A above a finite place w, r is unramified (crystalline above ℓ) exactly when it
is of finite type and X − 1 kills every element of inertia. -/
lemma isGoodAt_iff : IsGoodAt r A ↔ IsFiniteTypeAt r A ∧ ∀ s ∈ inertiaGroup _ A,
  PolyKillsAt r A s (Polynomial.X - 1) := ⟨fun ⟨h, g⟩ ↦
  ⟨⟨by aesop, g.isPotCrys⟩, fun s i ↦ ⟨by aesop, fun t ↦ by simp_all [← (ℓ.pow_right_inj Fact.out).1
  (t.eq_pow_of_isFrob (PadicPlaceEmbedding.isWeilPair_zero_iff.2 i)), IsKilledBy,
  IsCrystalline.isPotCrys, IsCrystalline.linearFrob_eq_one]⟩⟩, fun ⟨h, g⟩ ↦
  ⟨by simp_all [PolyKillsAt], h.2.isCrystalline_of_inertia_fixes fun s t ↦ by simpa using
  ((g _ (PadicPlaceEmbedding.isWeilPair_zero_iff.1 t)).2 t).2⟩⟩
