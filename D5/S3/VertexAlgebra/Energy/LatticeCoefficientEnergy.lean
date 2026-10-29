/- GID: D5/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Energy/LatticeCoefficientEnergy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Inverse-free energy support of the original all-state lattice fields. -/

import D5.S3.VertexAlgebra.Sewing.CanonicalOccupation
import D5.S3.VertexAlgebra.LatticeEnergyGrading
import D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

/-!
The finite coefficient recurrences preserve signed energy for arbitrary original
lattice data, including singular Gram matrices. This is a grading of the original
state-field map, independently of constructing a Sugawara zero mode.

proof_shape: actual_mode_grade: content
admission_basis: escape-witness
escape_witness: Input-occupation and descendant-word induction prove off-energy
vanishing of the literal matrix coefficient, using both normal-product branches.
The all-state endpoint consumes this support invariant on the full carrier basis.
utility is none: the result is an unrestricted algebraic support theorem, not a
finite certified instance, bounded enumeration, checker or numerical reduction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeCoefficientEnergy

open LatticeGeneratingFieldLocality LatticeAllStateField LatticeFiniteNegativeGeneration
open LatticePositiveEnergy LatticeSectorIntertwiner CanonicalOccupationSewing MvPolynomial
open scoped BigOperators VertexOperator

open private wordMap wordCoeff wordMap_nil wordCoeff_nil_add_single wordCoeff_cons
  from D5.S3.VertexAlgebra.Sewing.CanonicalOccupationRow
open private canonical_monomial_word from D5.S3.VertexAlgebra.Sewing.CanonicalOccupation

noncomputable section

private theorem level_add_single (D : LatticeData) (d : Occ D) (x : Index D) :
    level D (d + Finsupp.single x 1) = level D d + (x.2 + 1) := by
  simp [level, oscillatorEnergy, map_add, Finsupp.weight_single]

private theorem level_sub_single (D : LatticeData) (d : Occ D) (x : Index D)
    (hx : d x ≠ 0) :
    level D (d - Finsupp.single x 1) + (x.2 + 1) = level D d :=
  Finsupp.weight_sub_single_add hx

private theorem nil_zero_input (D : LatticeData) (α β : Charge D)
    (m : ℤ) (e : Occ D)
    (he : (level D e : ℤ) ≠ -m - 1 - bilinear D α β) :
    wordCoeff D α β [] m e 0 = 0 := by
  classical
  have hc : LatticeActualProductKernel.convolution D α (-m - 1 - bilinear D α β) 1 =
      creationCoeff D α (-m - 1 - bilinear D α β) := by
    simpa using LatticeActualProductKernel.convolution_monomial D α
      (-m - 1 - bilinear D α β) 0 (1 : Oscillator D)
  have hh : wordCoeff D α β [] m e 0 =
      epsilon D α β * (creationCoeff D α (-m - 1 - bilinear D α β)).coeff e := by
    simp [wordCoeff, b, wordMap_nil, translatedPolynomial, hc]
  rw [hh]
  by_cases ht : -m - 1 - bilinear D α β < 0
  · simp [creationCoeff, ht]
  · have hn : Finsupp.weight (fun x : Index D => x.2 + 1) e ≠
        (-m - 1 - bilinear D α β).toNat := by
      change level D e ≠ _
      omega
    rw [((actual_creation_coefficient_transport D α α).1 _).coeff_eq_zero e hn,
      mul_zero]

private theorem nil_off_energy (D : LatticeData) (α β : Charge D)
    (d : Occ D) : ∀ (m : ℤ) (e : Occ D),
    (level D e : ℤ) ≠ (level D d : ℤ) - m - 1 - bilinear D α β →
      wordCoeff D α β [] m e d = 0 := by
  classical
  suffices h : ∀ n : ℕ, ∀ d : Occ D, d.degree = n → ∀ (m : ℤ) (e : Occ D),
      (level D e : ℤ) ≠ (level D d : ℤ) - m - 1 - bilinear D α β →
        wordCoeff D α β [] m e d = 0 from h d.degree d rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro d hd m e he
    by_cases hz : d = 0
    · subst d
      apply nil_zero_input D α β m e
      simpa [level, oscillatorEnergy] using he
    · obtain ⟨x, hx⟩ : ∃ x : Index D, d x ≠ 0 := by
        by_contra h
        push Not at h
        exact hz (Finsupp.ext h)
      let d' := d - Finsupp.single x 1
      have hadd : d' + Finsupp.single x 1 = d := Finsupp.sub_add_single_one_cancel hx
      have hdeg : d'.degree + 1 = d.degree := by
        rw [← hadd, map_add, Finsupp.degree_single]
      have hi := ih d'.degree (by omega) d' rfl
      have hlev := level_add_single D d' x
      rw [hadd] at hlev
      rw [← hadd, wordCoeff_nil_add_single]
      have hleft : (if x ∈ e.support then
          wordCoeff D α β [] m (e - Finsupp.single x 1) d' else 0) = 0 := by
        split_ifs with hx'
        · have hl := level_sub_single D e x (Finsupp.mem_support_iff.mp hx')
          apply hi m _
          omega
        · rfl
      rw [hleft, hi (m - (x.2 + 1 : ℕ)) e (by omega)]
      simp

/-- Output occupation precedes input occupation in the literal coefficient. -/
private theorem word_off_energy (D : LatticeData) (α β : Charge D)
    (ω : List (Index D)) : ∀ (m : ℤ) (e d : Occ D),
    (level D e : ℤ) ≠ (level D d : ℤ) +
      (ω.map (fun x => (x.2 + 1 : ℤ))).sum - m - 1 - bilinear D α β →
      wordCoeff D α β ω m e d = 0 := by
  classical
  induction ω with
  | nil =>
    intro m e d h
    exact nil_off_energy D α β d m e (by simpa using h)
  | cons x ω ih =>
    intro m e d he
    simp only [List.map_cons, List.sum_cons] at he
    rw [wordCoeff_cons]
    have hfirst : (∑ j ∈ Finset.range (level D e),
        ((j + x.2).choose x.2 : ℂ) *
          if (x.1, j + x.2) ∈ e.support then
            wordCoeff D α β ω (m + j) (e - Finsupp.single (x.1, j + x.2) 1) d
          else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      split_ifs with hx
      · have hl := level_sub_single D e (x.1, j + x.2)
          (Finsupp.mem_support_iff.mp hx)
        rw [ih (m + j) _ d (by dsimp only [Prod.snd] at hl; omega), mul_zero]
      · exact mul_zero _
    rw [hfirst, zero_add]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hlt : j < x.2
    · simp [hlt]
    · rw [ite_eq_right hlt]
      by_cases heq : j = x.2
      · rw [ite_eq_left heq, ih (m - j - 1) e d (by omega)]
        simp
      · rw [ite_eq_right heq]
        have hsum : (∑ a : Fin D.rank, (D.G x.1 a : ℂ) *
            (d (a, j - x.2 - 1) : ℂ) *
              wordCoeff D α β ω (m - j - 1) e
                (d - Finsupp.single (a, j - x.2 - 1) 1)) = 0 := by
          apply Finset.sum_eq_zero
          intro a ha
          by_cases hz : d (a, j - x.2 - 1) = 0
          · simp [hz]
          · have hl := level_sub_single D d (a, j - x.2 - 1) hz
            rw [ih (m - j - 1) e _ (by dsimp only [Prod.snd] at hl; omega), mul_zero]
        rw [hsum]
        simp

private theorem canonical_off_energy (D : LatticeData) (α β : Charge D)
    (U W T : Occ D) (q : ℤ)
    (h : (level D T : ℤ) ≠ (level D U : ℤ) + (level D W : ℤ) -
      q - 1 - bilinear D α β) :
    (canonical D α β (b D U) q (b D W)).coeff T = 0 := by
  rw [canonical_monomial_word]
  change wordCoeff D α β (occurrences D U) q T W = 0
  have hw : ((occurrences D U).map (fun x => (x.2 + 1 : ℤ))).sum =
      (level D U : ℤ) := by
    have hn := LatticeHalfFockFiniteCorrection.wordWeight_occurrences D U
    change ((occurrences D U).map (fun x => x.2 + 1)).sum = level D U at hn
    have hc := congrArg (fun n : ℕ => (n : ℤ)) hn
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def, Nat.cast_add,
      Nat.cast_one] using hc
  apply word_off_energy
  rw [hw]
  omega

private theorem charge_energy_add (D : LatticeData) (α β : Charge D) :
    chargeEnergy D (α + β) = chargeEnergy D α + chargeEnergy D β + bilinear D α β := by
  have h := two_chargeEnergy D (α + β)
  have ha := two_chargeEnergy D α
  have hb := two_chargeEnergy D β
  rw [LatticeActualGeneratorLocality.bilinear_add_right,
    bilinear_symmetric D (α + β) α,
    LatticeActualGeneratorLocality.bilinear_add_right,
    bilinear_symmetric D (α + β) β,
    LatticeActualGeneratorLocality.bilinear_add_right,
    bilinear_symmetric D β α] at h
  omega

private theorem basis_mode_grade (D : LatticeData) (u v : Label D) (q : ℤ) :
    ((Y D (carrierBasis D u))[[q]]) (carrierBasis D v) ∈
      grade D (energy D u + energy D v - q - 1) := by
  classical
  rw [carrierBasis_apply, carrierBasis_apply]
  change ((Y D (inclusion D u.1 (b D u.2)))[[q]]) (inclusion D v.1 (b D v.2)) ∈ _
  rw [← inclusion_canonical D u.1 v.1 (b D u.2) (b D v.2) q, mem_grade_iff]
  intro t ht
  change ((Finsupp.single (u.1 + v.1)
    (canonical D u.1 v.1 (b D u.2) q (b D v.2))) t.1).coeff t.2 = 0
  by_cases hc : u.1 + v.1 = t.1
  · rw [Finsupp.single_apply, ite_eq_left hc]
    apply canonical_off_energy
    have hcharge := charge_energy_add D u.1 v.1
    simp only [energy] at ht
    rw [← hc] at ht
    simp only [level]
    omega
  · simp [hc]

/-- Every signed mode of the original full state-field map preserves energy.
No Gram inverse or positivity assumption is used, including at rank zero. -/
theorem actual_mode_grade (D : LatticeData) (m n q : ℤ) (a b : Carrier D)
    (ha : a ∈ grade D m) (hb : b ∈ grade D n) :
    ((Y D a)[[q]]) b ∈ grade D (m + n - q - 1) := by
  classical
  rw [grade_eq_span] at ha hb
  induction ha using Submodule.span_induction generalizing b with
  | mem x hx =>
    obtain ⟨u, hu, rfl⟩ := hx
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      change energy D u = m at hu
      change energy D v = n at hv
      simpa only [hu, hv] using basis_mode_grade D u v q
    | zero => simp
    | add x y hx hy ihx ihy =>
      simpa only [map_add] using (grade D (m + n - q - 1)).add_mem ihx ihy
    | smul c x hx ih =>
      simpa only [map_smul] using (grade D (m + n - q - 1)).smul_mem c ih
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [map_add, Pi.add_apply, LinearMap.add_apply] using
      (grade D (m + n - q - 1)).add_mem (ihx b hb) (ihy b hb)
  | smul c x hx ih =>
    simpa only [map_smul, Pi.smul_apply, LinearMap.smul_apply] using
      (grade D (m + n - q - 1)).smul_mem c (ih b hb)

#print axioms actual_mode_grade

end
end D5.S3.VertexAlgebra.LatticeCoefficientEnergy
