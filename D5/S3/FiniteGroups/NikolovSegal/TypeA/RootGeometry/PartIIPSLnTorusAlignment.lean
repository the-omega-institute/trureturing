/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIIPSLnTorusAlignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnTorusAlignment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-! Actual all-rank projective torus alignment. The whole central-quotient
preimage is averaged, following the accepted PartIIPSL3TorusAlignment proof.
No projective automorphism lift is assumed or constructed. -/
namespace NikolovSegal.PSLnTorusAlignment
open Matrix
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
open NikolovSegal.PSLnNormalizer
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F
local notation "Q" => ProjectiveSpecialLinearGroup (Fin n) F
local notation "π" => QuotientGroup.mk' (Subgroup.center G)

/-- The actual quotient image of the literal determinant-one diagonal torus. -/
def projectiveDiagonalTorus (n : ℕ) (F : Type u) [Field F] :
    Subgroup (ProjectiveSpecialLinearGroup (Fin n) F) :=
  (diagonalTorus n F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))

theorem center_le_torus : (π).ker ≤ diagonalTorus n F := by
  intro g hg
  have hc : g ∈ Subgroup.center G := (QuotientGroup.eq_one_iff g).mp hg
  obtain ⟨z, _, hs⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  apply diagonal_of_eq g (fun _ => z)
  exact hs.symm

/-- Actual index arithmetic proves the full torus-image preimage has the
original SL torus order. It retains every scalar in the actual center. -/
theorem card_torus_image_preimage [Fintype F] (beta : MulAut Q) :
    Nat.card (((projectiveDiagonalTorus n F).map beta.toMonoidHom).comap π) =
      Nat.card (diagonalTorus n F) := by
  let W := ((projectiveDiagonalTorus n F).map beta.toMonoidHom).comap π
  have hi : W.index = (diagonalTorus n F).index := by
    dsimp only [W]
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
    have hb : ((projectiveDiagonalTorus n F).map beta.toMonoidHom).index =
        (projectiveDiagonalTorus n F).index := Subgroup.index_map_equiv _ beta
    rw [hb]
    exact Subgroup.index_map_eq _ (QuotientGroup.mk'_surjective _) center_le_torus
  apply (mul_left_inj' (diagonalTorus n F).index_ne_zero_of_finite).mp
  calc
    Nat.card W * (diagonalTorus n F).index = Nat.card W * W.index := by rw [hi]
    _ = Nat.card G := W.card_mul_index
    _ = Nat.card (diagonalTorus n F) * (diagonalTorus n F).index :=
      (diagonalTorus n F).card_mul_index.symm

theorem projective_torus_le_normalizer : projectiveDiagonalTorus n F ≤
    Subgroup.normalizer (projectiveUplus n F : Set Q) := by
  rintro g ⟨t, ht, rfl⟩
  exact (quotient_mem_normalizer_iff_upper t).mpr (diagonalTorus_le_Borel ht)

/-- A further actual projective inner correction preserves U and aligns T
by averaging its whole SL preimage, without lifting the automorphism. -/
theorem U_preserving_torus_alignment [Fintype F] (beta : MulAut Q)
    (hU : (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F) :
    ∃ u : G, u ∈ Uplus n F ∧
      (projectiveUplus n F).map (MulAut.conj (π u)⁻¹ * beta).toMonoidHom = projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map (MulAut.conj (π u)⁻¹ * beta).toMonoidHom = projectiveDiagonalTorus n F := by
  classical
  let W := ((projectiveDiagonalTorus n F).map beta.toMonoidHom).comap π
  letI : Fintype W := Fintype.ofFinite _
  have ht : ∀ w : W, Upper (w : G) := by
    intro w
    have hm : π w.val ∈ (Subgroup.normalizer (projectiveUplus n F : Set Q)).map beta.toMonoidHom :=
      (Subgroup.map_mono (projective_torus_le_normalizer (n := n) (F := F))) w.property
    rw [Subgroup.map_equiv_normalizer_eq, hU] at hm
    exact (quotient_mem_normalizer_iff_upper w.val).mp hm
  have hc : (Fintype.card W : F) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, card_torus_image_preimage beta]
    exact card_torus_cast_ne_zero
  obtain ⟨u, hu, hd⟩ := upper_finite_subgroup_diagonal_alignment W ht hc
  let delta := MulAut.conj (π u)⁻¹ * beta
  have hV : (projectiveUplus n F).map delta.toMonoidHom = projectiveUplus n F := by
    change (projectiveUplus n F).map ((MulAut.conj (π u)⁻¹).toMonoidHom.comp beta.toMonoidHom) = _
    rw [← Subgroup.map_map, hU]
    have hum : π u ∈ projectiveUplus n F := Subgroup.mem_map_of_mem π hu
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.le_normalizer ((projectiveUplus n F).inv_mem hum))
  have hle : (projectiveDiagonalTorus n F).map delta.toMonoidHom ≤ projectiveDiagonalTorus n F := by
    rintro g ⟨z, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) (beta (π t))
    have hwW : w ∈ W := by
      change π w ∈ (projectiveDiagonalTorus n F).map beta.toMonoidHom
      rw [hw]
      exact Subgroup.mem_map_of_mem beta.toMonoidHom (Subgroup.mem_map_of_mem π ht)
    have hdiag : u⁻¹*w*u ∈ diagonalTorus n F := diagonal_of_eq _ _ (hd ⟨w, hwW⟩)
    refine ⟨u⁻¹*w*u, hdiag, ?_⟩
    change π (u⁻¹*w*u) = (MulAut.conj (π u)⁻¹ * beta) (π t)
    simp only [map_mul, map_inv, hw, MulAut.mul_apply, MulAut.conj_inv_apply]
  have hT : (projectiveDiagonalTorus n F).map delta.toMonoidHom = projectiveDiagonalTorus n F := by
    apply Subgroup.eq_of_le_of_card_ge hle
    exact (Nat.card_congr ((projectiveDiagonalTorus n F).equivMapOfInjective
      delta.toMonoidHom delta.injective).toEquiv).le
  exact ⟨u, hu, hV, hT⟩

variable [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p]
include p

/-- One genuine projective inner correction, before all targets, preserves
actual full projective U and T in every rank and characteristic. -/
theorem psl_inner_U_T_correction (n : ℕ) (alpha : MulAut (ProjectiveSpecialLinearGroup (Fin n) F)) :
    ∃ c : ProjectiveSpecialLinearGroup (Fin n) F,
      let beta := MulAut.conj c * alpha
      let B := (Borel n F).map (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F)))
      (projectiveUplus n F).map beta.toMonoidHom = projectiveUplus n F ∧
      (projectiveDiagonalTorus n F).map beta.toMonoidHom = projectiveDiagonalTorus n F ∧
      B.map beta.toMonoidHom = B ∧
      (∀ g, beta g ∈ projectiveUplus n F ↔ g ∈ projectiveUplus n F) ∧
      (∀ g, beta g ∈ projectiveDiagonalTorus n F ↔ g ∈ projectiveDiagonalTorus n F) ∧
      (∀ g, beta g ∈ B ↔ g ∈ B) := by
  obtain ⟨c, hU, _, _, _⟩ := InnerUNormalization.psl_inner_U_Borel_correction p n alpha
  obtain ⟨u, _, hV, hT⟩ := U_preserving_torus_alignment (MulAut.conj c * alpha) hU
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
  let delta := MulAut.conj (q u)⁻¹ * (MulAut.conj c * alpha)
  let B := (Borel n F).map q
  have hB : B.map delta.toMonoidHom = B := by
    dsimp only [B, q]
    rw [← projective_normalizer_eq_map_Borel, Subgroup.map_equiv_normalizer_eq, hV]
  have hi : ∀ H : Subgroup (ProjectiveSpecialLinearGroup (Fin n) F),
      H.map delta.toMonoidHom = H → ∀ g, delta g ∈ H ↔ g ∈ H := by
    intro H h g
    have hm := Subgroup.mem_map_iff_mem (f := delta.toMonoidHom) (K := H) (x := g) delta.injective
    rwa [h] at hm
  have he : MulAut.conj ((q u)⁻¹*c) * alpha = delta := by rw [map_mul, mul_assoc]
  refine ⟨(q u)⁻¹*c, ?_⟩
  dsimp only
  rw [he]
  exact ⟨hV, hT, hB, hi _ hV, hi _ hT, hi _ hB⟩

end NikolovSegal.PSLnTorusAlignment
