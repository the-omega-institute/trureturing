/- GID: D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every actual factor exceeds the fixed factorial cutoff. -/

import D5.S3.FiniteGroups.NikolovSegal.MinimalNormalConjugacy
import D5.S3.FiniteGroups.NikolovSegal.SimpleSectionsOfProducts
import D5.S3.FiniteGroups.NikolovSegal.Alpha

set_option autoImplicit false
namespace NikolovSegal
universe u v w
variable {G : Type u} [Group G]

/-- Every section of a commutative group is commutative, including sections
formed from arbitrary subgroups. -/
theorem commutative_section {A : Type v} [Group A] [IsMulCommutative G]
    (h : Involves A G) : IsMulCommutative A := by
  obtain ⟨H, f, hf⟩ := h
  constructor
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := hf a
  obtain ⟨y, rfl⟩ := hf b
  rw [← map_mul, ← map_mul]
  apply congrArg f
  apply Subtype.ext
  exact mul_comm' (x : G) (y : G)

/-- Large alternating-section degree forces noncommutativity. -/
theorem noncommutative_of_large_alpha [Finite G] {k : ℕ} (hk : 4 ≤ k)
    (hα : ¬alpha G ≤ k) : ¬IsMulCommutative G := by
  intro hc
  let := hc
  have ha := commutative_section (alpha_spec (G := G)).1
  have hsmall := alternatingGroup.isMulCommutative_iff_card_le_three.mp ha
  simp only [Nat.card_fin] at hsmall
  exact hα (hsmall.trans (by omega))

/-- The elementary structure part of Proposition 3, Case 1, with the paper's
actual uniform cutoff. Every factor, not just one or their average, has order
larger than C. C and k are fixed before the arbitrary finite ambient group. -/
theorem large_minimal_normal_structure [Finite G]
    (N : Subgroup G)
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (C k : ℕ) (hk : 4 ≤ k) (hfac : 2 * C < k.factorial)
    (hα : ¬alpha N ≤ k) :
    _root_.commutator N = ⊤ ∧ Subgroup.center N = ⊥ ∧
      (∀ M : MinimalNormalFactor N,
        IsSimpleGroup M.val ∧ ¬IsMulCommutative M.val ∧ C < Nat.card M.val) ∧
      Nonempty ((∀ M : MinimalNormalFactor N, M.val) ≃* N) := by
  let := hN.prop.1
  have hna := noncommutative_of_large_alpha hk hα
  obtain ⟨hp, hz, hsimple, he⟩ := minimal_normal_nonabelian_direct_product N hN hna
  obtain ⟨e⟩ := he
  have hn : 5 ≤ alpha N := by omega
  let : IsSimpleGroup (alternatingGroup (Fin (alpha N))) :=
    alternatingGroup.isSimpleGroup (by simpa using hn)
  have hsec := involves_of_injective e.symm.toMonoidHom e.symm.injective
      (alpha_spec (G := N)).1
  obtain ⟨L, hL⟩ := simple_involves_pi_factor (MinimalNormalFactor N)
      (fun M => M.val) hsec
  have hcard : Nat.card (alternatingGroup (Fin (alpha N))) ≤ Nat.card L.val :=
    Nat.le_of_dvd Nat.card_pos (involves_card_dvd hL)
  have hfactorial : k.factorial ≤ (alpha N).factorial := Nat.factorial_le (by omega)
  let : Nontrivial (Fin (alpha N)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have halt := two_mul_nat_card_alternatingGroup (α := Fin (alpha N))
  simp only [Nat.card_perm, Nat.card_fin] at halt
  have hlarge : C < Nat.card L.val := by omega
  refine ⟨hp, hz, ?_, ⟨e⟩⟩
  intro M
  obtain ⟨em⟩ := minimal_normal_factors_isomorphic N hN hna M L
  have heq : Nat.card M.val = Nat.card L.val := Nat.card_congr em.toEquiv
  exact ⟨(hsimple M).1, (hsimple M).2, heq ▸ hlarge⟩

/-- The central quotient in the exact form needed by the large semisimple
absorption theorem. All factor size and simplicity hypotheses are proved here. -/
theorem large_minimal_normal_proposition2_data [Finite G]
    (N : Subgroup G)
    (hN : Minimal (fun K : Subgroup G => K.Normal ∧ K ≠ ⊥) N)
    (C k : ℕ) (hk : 4 ≤ k) (hfac : 2 * C < k.factorial)
    (hα : ¬alpha N ≤ k) :
    _root_.commutator N = ⊤ ∧
      (∀ M : MinimalNormalFactor N,
        IsSimpleGroup M.val ∧ ¬IsMulCommutative M.val ∧ C < Nat.card M.val) ∧
      Nonempty ((N ⧸ Subgroup.center N) ≃* (∀ M : MinimalNormalFactor N, M.val)) := by
  obtain ⟨hp, hz, hf, ⟨e⟩⟩ := large_minimal_normal_structure N hN C k hk hfac hα
  exact ⟨hp, hf, ⟨(QuotientGroup.quotientMulEquivOfEq hz).trans
    (QuotientGroup.quotientBot.trans e.symm)⟩⟩

end NikolovSegal
