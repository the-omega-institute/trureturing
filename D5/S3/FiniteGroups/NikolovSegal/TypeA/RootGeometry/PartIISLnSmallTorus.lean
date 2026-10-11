/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallTorus
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnSmallTorus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnBareFullGroupClassification
import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIIPSLnBareFullGroupClassification
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnSmallField
open Matrix NikolovSegal.SLnRootAction
open NikolovSegal.SLnNormalizer NikolovSegal.SLnTorusAlignment
universe u
variable {F : Type u} [Field F] {n : ℕ}
local notation "G" => SpecialLinearGroup (Fin n) F

private theorem spare_coordinate (hn : 4 < n) (i j a b : Fin n) :
    ∃ k : Fin n, k ≠ i ∧ k ≠ j ∧ k ≠ a ∧ k ≠ b := by
  classical
  have hex : ∃ k : Fin n, k ∉ ({i,j,a,b}:Finset (Fin n)) := by
    by_contra h
    have hs : (Finset.univ : Finset (Fin n)) ⊆ {i,j,a,b} := by
      intro k _
      by_contra hk
      exact h ⟨k,hk⟩
    have hc := Finset.card_le_card hs
    have hf : ({i,j,a,b}:Finset (Fin n)).card ≤ 4 := Finset.card_le_four
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    omega
  obtain ⟨k,hk⟩ := hex
  exact ⟨k,by simpa using hk⟩

private theorem nontrivial_unit [Fintype F] (hF : 2 < Fintype.card F) :
    ∃ x : Fˣ, (x:F) ≠ 1 := by
  classical
  have he : ∃ x : Fˣ, x^1 ≠ 1 := exists_pow_ne_one_of_isCyclic (by decide)
    (by rw [Nat.card_eq_fintype_card,Fintype.card_units]; omega)
  obtain ⟨x,hx⟩ := he
  exact ⟨x,fun he => hx (by simpa only [pow_one] using Units.ext he)⟩

/-- Actual determinant-one character-kernel separation with a spare coordinate.
Unlike the three-coordinate argument, this works for F3 and F4 in EVERY rank>=5. -/
theorem torusKernel_separates [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (r s : PositiveIndex n) (hsr : s ≠ r) :
    ∃ d ∈ torusKernel (F := F) r, d.val s.val.1 s.val.1 ≠ d.val s.val.2 s.val.2 := by
  classical
  obtain ⟨k,hki,hkj,hka,hkb⟩ := spare_coordinate hn r.val.1 r.val.2 s.val.1 s.val.2
  obtain ⟨x,hx⟩ := nontrivial_unit hF
  have hab := ne_of_lt s.property
  have outside : (s.val.1 ≠ r.val.1 ∧ s.val.1 ≠ r.val.2) ∨
      (s.val.2 ≠ r.val.1 ∧ s.val.2 ≠ r.val.2) := by
    by_contra h
    have hbad : (s.val.1=r.val.1 ∨ s.val.1=r.val.2) ∧
        (s.val.2=r.val.1 ∨ s.val.2=r.val.2) := by tauto
    rcases hbad with ⟨ha,hb⟩
    rcases ha with ha|ha <;> rcases hb with hb|hb
    · exact hab (ha.trans hb.symm)
    · exact hsr (Subtype.ext (Prod.ext ha hb))
    · have hs := s.property; rw [ha,hb] at hs; exact lt_asymm hs r.property
    · exact hab (ha.trans hb.symm)
  rcases outside with ⟨hai,haj⟩|⟨hbi,hbj⟩
  · let d := SpecialLinearGroup.diag2n hka.symm (x:F) x.ne_zero
    have hd : d ∈ diagonalTorus n F := diagonal_of_eq _ _ rfl
    refine ⟨d,(mem_torusKernel_iff r d).mpr ⟨hd,?_⟩,?_⟩
    · simp [d,SpecialLinearGroup.diag2n_coe,hai.symm,haj.symm,hki.symm,hkj.symm]
    · simpa [d,SpecialLinearGroup.diag2n_coe,hab,hab.symm,hkb.symm,hka.symm] using hx
  · let d := SpecialLinearGroup.diag2n hkb.symm (x:F) x.ne_zero
    have hd : d ∈ diagonalTorus n F := diagonal_of_eq _ _ rfl
    refine ⟨d,(mem_torusKernel_iff r d).mpr ⟨hd,?_⟩,?_⟩
    · simp [d,SpecialLinearGroup.diag2n_coe,hbi.symm,hbj.symm,hki.symm,hkj.symm]
    · simpa [d,SpecialLinearGroup.diag2n_coe,hab,hab.symm,hka.symm,hkb.symm] using (Ne.symm hx)

/- The entrywise recognition proof is adapted at its genuinely changed separation
boundary; the accepted carrier, character and matrix equations are reused. -/
theorem fixed_torusKernel_iff [Fintype F] (hn : 4 < n) (hF : 2 < Fintype.card F)
    (r : PositiveIndex n) (g : G) (hg : g ∈ Uplus n F) :
    (∀ d ∈ torusKernel r, d*g = g*d) ↔ g ∈ rootSubgroup (F := F) r := by
  classical
  constructor
  · intro h
    have hz : ∀ i j : Fin n, i < j → (i,j) ≠ r.val → g.val i j = 0 := by
      intro i j hij hne
      let s : PositiveIndex n := ⟨(i,j), hij⟩
      have hsr : s ≠ r := fun he => hne (congrArg Subtype.val he)
      obtain ⟨d,hd,hsep⟩ := torusKernel_separates hn hF r s hsr
      have hc := (diagonal_commutes_iff d g ((mem_torusKernel_iff r d).mp hd).1).mp (h d hd) i j
      exact (mul_eq_zero.mp hc).resolve_left (sub_ne_zero.mpr hsep)
    refine ⟨g.val r.val.1 r.val.2, ?_⟩
    apply Subtype.ext
    ext i j
    change (1 + Matrix.single r.val.1 r.val.2 (g.val r.val.1 r.val.2) : Matrix (Fin n) (Fin n) F) i j = g.val i j
    by_cases he : i = j
    · subst j
      have hs : ¬(r.val.1=i ∧ r.val.2=i) := by
        rintro ⟨ha,hb⟩
        exact (ne_of_lt r.property) (ha.trans hb.symm)
      simp [Matrix.single_apply, hs, hg.2 i]
    · by_cases hij : i < j
      · by_cases hr : (i,j) = r.val
        · have hi : i = r.val.1 := congrArg Prod.fst hr
          have hj : j = r.val.2 := congrArg Prod.snd hr
          simp [Matrix.single_apply, Matrix.one_apply, hi, hj, ne_of_lt r.property]
        · rw [hz i j hij hr]
          have hs : ¬(r.val.1=i ∧ r.val.2=j) := by
            rintro ⟨ha,hb⟩
            exact hr (Prod.ext ha.symm hb.symm)
          simp [Matrix.single_apply, Matrix.one_apply, he, hs]
      · have hji : j.val < i.val := by
          have hne : i.val ≠ j.val := fun h => he (Fin.ext h)
          omega
        rw [hg.1 i j hji]
        have hr : ¬ (i = r.val.1 ∧ j = r.val.2) := by rintro ⟨rfl,rfl⟩; exact hij r.property
        have hs : ¬(r.val.1=i ∧ r.val.2=j) := by
          rintro ⟨ha,hb⟩
          exact hr ⟨ha.symm,hb.symm⟩
        simp [Matrix.single_apply, Matrix.one_apply, he, hs]
  · rintro ⟨t,rfl⟩ d hd
    apply (diagonal_commutes_iff d _ ((mem_torusKernel_iff r d).mp hd).1).mpr
    intro i j
    have hdiag := ((mem_torusKernel_iff r d).mp hd).2
    change (d.val i i-d.val j j)*(1 + Matrix.single r.val.1 r.val.2 t : Matrix (Fin n) (Fin n) F) i j = 0
    by_cases he : i = j
    · subst j; simp
    · by_cases hr : i = r.val.1 ∧ j = r.val.2
      · rcases hr with ⟨rfl,rfl⟩; simp [hdiag]
      · have hs : ¬(r.val.1=i ∧ r.val.2=j) := by
          rintro ⟨ha,hb⟩
          exact hr ⟨ha.symm,hb.symm⟩
        simp [Matrix.single_apply, Matrix.one_apply, he, hs]

end NikolovSegal.SLnSmallField
