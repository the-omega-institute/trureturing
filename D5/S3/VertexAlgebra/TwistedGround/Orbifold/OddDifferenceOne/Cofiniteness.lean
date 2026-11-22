/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/Cofiniteness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/OddDifferenceOne/Cofiniteness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded strict mode words give C2-cofiniteness of the Leech extension. -/

import D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOne.ActualLeech
import D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechRelativeOddAction

/-! C₂-cofiniteness of the relative odd quotient and of the assembled Leech extension. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2

open ActualLeechHyperbolic (leechData leech_spec)
open HalfFock.LatticeHalfFockParityField (paritySpace)
open OddDifferenceOne (leech_odd_difference_one)
open OddDifferenceOneSpanning (Homogeneous Word strictSpan wordMap)
open private act lettersIn increasing wordMap_cons sorted_truncate tail_cutoff from
  D5.S3.VertexAlgebra.TwistedGround.Orbifold.OddDifferenceOneSpanning

local notation "uΛ" => And.left (And.right leech_spec)
local notation "Odd" => paritySpace leechData uΛ (-1)
local notation "C₂" => relativeOddC2 leechData uΛ

set_option maxHeartbeats 600000 in
-- Elaborating the finite word enumeration through the actual quotient maps needs extra heartbeats.
/-- The actual negative twisted relative quotient and the intrinsic C₂ quotient of
the assembled Leech extension are both finite dimensional over ℂ. -/
theorem leech_c2_cofinite :
    FiniteDimensional ℂ LeechRelativeOddQuotient ∧
    FiniteDimensional ℂ LeechExtensionQuotient := by
  classical
  have odd_finite : FiniteDimensional ℂ LeechRelativeOddQuotient := by
    by_cases hseed : ∃ u : Odd, u ≠ 0
    swap
    · have : Subsingleton Odd := ⟨fun x y =>
        (not_ne_iff.mp (fun hx => hseed ⟨x, hx⟩)).trans
          (not_ne_iff.mp (fun hy => hseed ⟨y, hy⟩)).symm⟩
      exact FiniteDimensional.of_surjective (C₂).mkQ (C₂).mkQ_surjective
    obtain ⟨u, hu⟩ := hseed
    obtain ⟨X, hspan, _⟩ := leech_odd_difference_one u hu
    obtain ⟨L, hL⟩ := tail_cutoff X u
    let I := Finset.Ico (-1 : ℤ) L
    let Letter := (↥X × ↥I)
    let Code := Σ k : Fin (I.card + 1), Fin k.val → Letter
    let decode (c : Code) : Word leechData :=
      List.ofFn fun i => ((c.2 i).1.val, (c.2 i).2.val)
    let q := (C₂).mkQ
    let read (c : Code) := q (wordMap (decode c) u)
    let G : Set LeechRelativeOddQuotient := insert 0 (Set.range read)
    let S : Set Odd := {v | ∃ t : Word leechData,
      lettersIn X t ∧ increasing t ∧ v = wordMap t u}
    have hG : (q '' S) ⊆ G := by
      rintro _ ⟨_, ⟨t, hx, ht, rfl⟩, rfl⟩
      by_cases hhigh : ∃ a ∈ t, L ≤ a.2
      · have hz := sorted_truncate X u L hL t (ht.imp fun h => le_of_lt h) hx hhigh
        rw [hz, map_zero]
        exact Set.mem_insert _ _
      by_cases hlow : ∃ a ∈ t, a.2 ≤ -2
      · obtain ⟨a, ha, haLow⟩ := hlow
        cases t with
        | nil => simp at ha
        | cons b t =>
          have hb : b.2 ≤ -2 := by
            rcases List.mem_cons.mp ha with rfl | ha
            · exact haLow
            · exact (le_of_lt ((List.pairwise_cons.mp ht).1 a ha)).trans haLow
          have hz : q (wordMap (b :: t) u) = 0 := by
            rw [wordMap_cons]
            exact (Submodule.Quotient.mk_eq_zero C₂).mpr
              (fixed_odd_mode_mem_relativeOddC2 leechData uΛ b.1.state (wordMap t u) hb)
          rw [hz]
          exact Set.mem_insert _ _
      have hindex (a : Homogeneous leechData × ℤ) (ha : a ∈ t) : a.2 ∈ I := by
        apply Finset.mem_Ico.mpr
        have hlo : ¬ a.2 ≤ -2 := fun h => hlow ⟨a, ha, h⟩
        exact ⟨by omega, lt_of_not_ge (fun h => hhigh ⟨a, ha, h⟩)⟩
      have hdistinct : (t.map Prod.snd).Pairwise (· < ·) := List.pairwise_map.mpr ht
      have hsubset : (t.map Prod.snd).toFinset ⊆ I := by
        intro j hj
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
        exact hindex a ha
      have hlength : t.length ≤ I.card := by
        simpa only [List.toFinset_card_of_nodup hdistinct.nodup, List.length_map]
          using Finset.card_le_card hsubset
      let code : Code := ⟨⟨t.length, Nat.lt_succ_of_le hlength⟩, fun i =>
        (⟨(t.get i).1, hx _ (List.get_mem t i)⟩, ⟨(t.get i).2, hindex _ (List.get_mem t i)⟩)⟩
      have hdecode : decode code = t := List.ofFn_get t
      refine Set.mem_insert_of_mem _ ⟨code, ?_⟩
      change q (wordMap (decode code) u) = q (wordMap t u)
      rw [hdecode]
    have hqspan : Submodule.span ℂ (q '' S) = ⊤ := by
      rw [← Submodule.map_span, show Submodule.span ℂ S = ⊤ from hspan,
        Submodule.map_top, Submodule.range_mkQ]
    have hle : Submodule.span ℂ (q '' S) ≤ Submodule.span ℂ G := Submodule.span_mono hG
    rw [hqspan] at hle
    have hfg : (Submodule.span ℂ G).FG := Submodule.fg_span ((Set.finite_range read).insert 0)
    rw [top_unique hle] at hfg
    exact Module.Finite.of_fg_top hfg
  exact ⟨odd_finite, leech_extension_c2_cofinite_of_relative_odd_finite odd_finite⟩

#print axioms leech_c2_cofinite

end D5.S3.VertexAlgebra.TwistedGround.Orbifold.ActualLeechExtensionC2
