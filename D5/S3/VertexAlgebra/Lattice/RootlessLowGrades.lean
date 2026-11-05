/- GID: D5/S3/VertexAlgebra/Lattice/RootlessLowGrades
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/RootlessLowGrades
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constructive rootless lattice low-energy bases and actual Sugawara spectrum. -/

import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.NatCard
import Mathlib.Tactic

/-!
Actual positive definite even lattices of arbitrary natural rank, including zero.
The oscillator proof removes occupied occurrences and distinguishes a mode-two
singleton from an unordered pair of mode-one colours, including repetitions.
Rootlessness excludes charged states below energy two; the norm-four shell
is finite by the existing charge sublevel theorem, with no count premise.
The resulting basis reindexes the existing all-charge gradeBasis and transports
to the literal inverse-Gram Sugawara operator using actualL0_eigenspace_eq_grade.
Mathlib's symmetric-power cardinality theorem retains its Apache-2.0 license
and original authorship. Lattice construction context: Bakalov--Kac,
math/0402315v1, section 4.1; no Monster or Leech shell count is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.Lattice.RootlessLowGrades

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeSugawaraCurrents

abbrev OscillatorFiber (D : LatticeData) (n : ℕ) :=
  {d : Exponent D // oscillatorEnergy d = n}

abbrev NormFour (D : LatticeData) :=
  {a : Charge D // bilinear D a a = 4}

private theorem oscillator_add (D : LatticeData) (d e : Exponent D) :
    oscillatorEnergy (d + e) = oscillatorEnergy d + oscillatorEnergy e :=
  map_add (Finsupp.weight (fun x : Index D => x.2 + 1)) d e

private theorem oscillator_single (D : LatticeData) (x : Index D) (m : ℕ) :
    oscillatorEnergy (Finsupp.single x m : Exponent D) = m * (x.2 + 1) := by
  simp [oscillatorEnergy, Finsupp.weight_single]

/-- Removing an actual occupied oscillator proves the entire degree-one
classification, including the empty-colour case. -/
theorem oscillator_one_iff (D : LatticeData) (d : Exponent D) :
    oscillatorEnergy d = 1 ↔
      ∃ i : Fin D.rank, d = Finsupp.single (i, 0) 1 := by
  classical
  constructor
  · intro hd
    have hd0 : d ≠ 0 := by
      intro h
      simp [h, oscillatorEnergy] at hd
    obtain ⟨⟨i, k⟩, hx⟩ := Finsupp.support_nonempty_iff.mpr hd0
    have hx' : d (i, k) ≠ 0 := Finsupp.mem_support_iff.mp hx
    have hw : oscillatorEnergy (d - Finsupp.single (i, k) 1) + (k + 1) =
        oscillatorEnergy d :=
      Finsupp.weight_sub_single_add (w := fun x : Index D => x.2 + 1) hx'
    have hk : k = 0 := by omega
    subst k
    have hz : d - Finsupp.single (i, 0) 1 = 0 :=
      (oscillatorEnergy_eq_zero_iff D _).mp (by omega)
    have hr := Finsupp.sub_add_single_one_cancel hx'
    rw [hz, zero_add] at hr
    exact ⟨i, hr.symm⟩
  · rintro ⟨i, rfl⟩
    simp [oscillator_single]

/-- A bijection with literal degree-one oscillator monomials. -/
def oscillatorOneEquiv (D : LatticeData) :
    OscillatorFiber D 1 ≃ Fin D.rank := by
  classical
  let f : Fin D.rank → OscillatorFiber D 1 := fun i =>
    ⟨Finsupp.single (i, 0) 1, by simp [oscillator_single]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      have hs : Finsupp.single (i, 0) (1 : ℕ) = Finsupp.single (j, 0) 1 :=
        congrArg Subtype.val h
      exact congrArg Prod.fst ((Finsupp.single_left_inj (by decide)).mp hs)
    · intro d
      obtain ⟨i, hi⟩ := (oscillator_one_iff D d.1).mp d.2
      exact ⟨i, Subtype.ext hi.symm⟩
  exact (Equiv.ofBijective f hf).symm

/-- Exhaustive degree-two classification derived from the weight, rather
than assumed as a dimension or a partition formula. -/
theorem oscillator_two_classification (D : LatticeData) (d : Exponent D)
    (hd : oscillatorEnergy d = 2) :
    (∃ i : Fin D.rank, d = Finsupp.single (i, 1) 1) ∨
    (∃ i j : Fin D.rank,
      d = Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1) := by
  classical
  have hd0 : d ≠ 0 := by
    intro h
    simp [h, oscillatorEnergy] at hd
  obtain ⟨⟨i, k⟩, hx⟩ := Finsupp.support_nonempty_iff.mpr hd0
  have hx' : d (i, k) ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hw : oscillatorEnergy (d - Finsupp.single (i, k) 1) + (k + 1) =
      oscillatorEnergy d :=
    Finsupp.weight_sub_single_add (w := fun x : Index D => x.2 + 1) hx'
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl
  · have he : oscillatorEnergy (d - Finsupp.single (i, 0) 1) = 1 := by omega
    obtain ⟨j, hj⟩ := (oscillator_one_iff D _).mp he
    have hr := Finsupp.sub_add_single_one_cancel hx'
    rw [hj] at hr
    exact Or.inr ⟨j, i, hr.symm⟩
  · have he : oscillatorEnergy (d - Finsupp.single (i, 1) 1) = 0 := by omega
    have hz := (oscillatorEnergy_eq_zero_iff D _).mp he
    have hr := Finsupp.sub_add_single_one_cancel hx'
    rw [hz, zero_add] at hr
    exact Or.inl ⟨i, hr.symm⟩

/-- The actual exponent vector of a two-multiset of mode-one colours. -/
def pairOccupation (D : LatticeData) (s : Sym (Fin D.rank) 2) : Exponent D :=
  ((s : Multiset (Fin D.rank)).map (fun i => (i, 0) : Fin D.rank → Index D)).toFinsupp

private theorem pairOccupation_pair (D : LatticeData) (i j : Fin D.rank) :
    pairOccupation D (⟨{i, j}, by simp⟩ : Sym (Fin D.rank) 2) =
      Finsupp.single (i, 0) 1 + Finsupp.single (j, 0) 1 := by
  classical
  ext x
  simp [pairOccupation, Multiset.count_cons, Multiset.count_singleton,
    Finsupp.single_apply, eq_comm, Nat.add_comm]

private theorem pairOccupation_energy (D : LatticeData) (s : Sym (Fin D.rank) 2) :
    oscillatorEnergy (pairOccupation D s) = 2 := by
  rcases s with ⟨s, hs⟩
  obtain ⟨i, j, rfl⟩ := Multiset.card_eq_two.mp hs
  rw [pairOccupation_pair, oscillator_add, oscillator_single, oscillator_single]
  norm_num

private theorem pairOccupation_injective (D : LatticeData) :
    Function.Injective (pairOccupation D) := by
  intro s t h
  apply Sym.ext
  apply Multiset.map_injective
    (show Function.Injective (fun i : Fin D.rank => ((i, 0) : Index D)) from
      fun i j hij => congrArg Prod.fst hij)
  have hm := congrArg (fun d : Exponent D => d.toMultiset) h
  simpa only [pairOccupation, Multiset.toFinsupp_toMultiset] using hm

private theorem pairOccupation_mode_two (D : LatticeData)
    (s : Sym (Fin D.rank) 2) (i : Fin D.rank) :
    pairOccupation D s (i, 1) = 0 := by
  classical
  rcases s with ⟨s, hs⟩
  obtain ⟨j, k, rfl⟩ := Multiset.card_eq_two.mp hs
  rw [pairOccupation_pair]
  simp [Finsupp.single_apply]

/-- The forward construction from the two genuinely different oscillator
configurations to the exact energy-two fiber. -/
def oscillatorTwoDecode (D : LatticeData) :
    Fin D.rank ⊕ Sym (Fin D.rank) 2 → OscillatorFiber D 2
  | Sum.inl i => ⟨Finsupp.single (i, 1) 1, by simp [oscillator_single]⟩
  | Sum.inr s => ⟨pairOccupation D s, pairOccupation_energy D s⟩

private theorem oscillatorTwoDecode_bijective (D : LatticeData) :
    Function.Bijective (oscillatorTwoDecode D) := by
  classical
  constructor
  · intro x y h
    cases x with
    | inl i =>
      cases y with
      | inl j =>
        have hs : Finsupp.single (i, 1) (1 : ℕ) = Finsupp.single (j, 1) 1 :=
          congrArg Subtype.val h
        have hij : i = j :=
          congrArg Prod.fst ((Finsupp.single_left_inj (by decide)).mp hs)
        exact congrArg Sum.inl hij
      | inr s =>
        have hs : Finsupp.single (i, 1) (1 : ℕ) = pairOccupation D s :=
          congrArg Subtype.val h
        have hv := congrArg (fun d : Exponent D => d (i, 1)) hs
        have hf : (1 : ℕ) = 0 := by simpa [pairOccupation_mode_two] using hv
        exact False.elim (Nat.one_ne_zero hf)
    | inr s =>
      cases y with
      | inl i =>
        have hs : Finsupp.single (i, 1) (1 : ℕ) = pairOccupation D s :=
          (congrArg Subtype.val h).symm
        have hv := congrArg (fun d : Exponent D => d (i, 1)) hs
        have hf : (1 : ℕ) = 0 := by simpa [pairOccupation_mode_two] using hv
        exact False.elim (Nat.one_ne_zero hf)
      | inr t =>
        exact congrArg Sum.inr
          (pairOccupation_injective D (congrArg Subtype.val h))
  · intro d
    rcases oscillator_two_classification D d.1 d.2 with ⟨i, hi⟩ | ⟨i, j, hij⟩
    · exact ⟨Sum.inl i, Subtype.ext hi.symm⟩
    · refine ⟨Sum.inr (⟨{i, j}, by simp⟩ : Sym (Fin D.rank) 2), ?_⟩
      apply Subtype.ext
      change pairOccupation D (⟨{i, j}, by simp⟩ : Sym (Fin D.rank) 2) = d.1
      rw [pairOccupation_pair]
      exact hij.symm

/-- A finite, actual exponent-vector bijection, with repeated mode-one
colours handled by Sym rather than by ordered pairs with duplication. -/
def oscillatorTwoEquiv (D : LatticeData) :
    OscillatorFiber D 2 ≃ Fin D.rank ⊕ Sym (Fin D.rank) 2 :=
  (Equiv.ofBijective (oscillatorTwoDecode D)
    (oscillatorTwoDecode_bijective D)).symm

private theorem card_two_multisets (D : LatticeData) :
    Nat.card (Sym (Fin D.rank) 2) = Nat.choose (D.rank + 1) 2 := by
  have hn : Nat.card (Fin D.rank) + 2 - 1 = D.rank + 1 := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  exact (Sym.natCard_sym_eq_choose (Fin D.rank) 2).trans
    (congrArg (fun n : ℕ => Nat.choose n 2) hn)

/-- General neutral oscillator count; no specialization to rank 24. -/
theorem neutral_energy_two_card (D : LatticeData) :
    Nat.card (OscillatorFiber D 2) = D.rank + Nat.choose (D.rank + 1) 2 := by
  rw [Nat.card_congr (oscillatorTwoEquiv D), Nat.card_sum, card_two_multisets]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Evenness gives integral half-norm. Positive definiteness and absence of
norm-two charges therefore force a nonzero charge to cost at least two. -/
theorem chargeEnergy_gap (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2)
    (a : Charge D) (ha : a ≠ 0) : 2 ≤ chargeEnergy D a := by
  have hnonneg := chargeEnergy_nonneg D hD a
  have hzero : chargeEnergy D a ≠ 0 :=
    fun h => ha ((chargeEnergy_eq_zero_iff D hD a).mp h)
  have hone : chargeEnergy D a ≠ 1 := by
    intro h
    have ht := two_chargeEnergy D a
    exact hroot a (by omega)
  omega

private theorem chargeEnergy_two_iff (D : LatticeData) (a : Charge D) :
    chargeEnergy D a = 2 ↔ bilinear D a a = 4 := by
  have ht := two_chargeEnergy D a
  omega

/-- The norm-four charges are actual integral charges in a finite derived
ellipsoid, not an assumed finite classification. -/
theorem normFour_finite (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) : Finite (NormFour D) := by
  have hs : Set.Finite {a : Charge D | bilinear D a a = 4} :=
    (chargeSublevel_finite D hD 2).subset (by
      intro a ha
      have hc := (chargeEnergy_two_iff D a).mpr ha
      change chargeEnergy D a ≤ (2 : ℤ)
      omega)
  exact hs.to_subtype

theorem energy_one_iff (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (x : Label D) :
    energy D x = 1 ↔ x.1 = 0 ∧ oscillatorEnergy x.2 = 1 := by
  constructor
  · intro hx
    have he : chargeEnergy D x.1 + (oscillatorEnergy x.2 : ℤ) = 1 := hx
    have ha : x.1 = 0 := by
      by_contra h
      have hg := chargeEnergy_gap D hD hroot x.1 h
      omega
    have hc : chargeEnergy D x.1 = 0 := by simp [ha]
    exact ⟨ha, by omega⟩
  · rintro ⟨ha, hd⟩
    simp [energy, ha, hd]

/-- Charge/oscillator exclusion at total energy two, proved from positivity,
integrality, and rootlessness alone. -/
theorem energy_two_iff (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) (x : Label D) :
    energy D x = 2 ↔
      (x.1 = 0 ∧ oscillatorEnergy x.2 = 2) ∨
      (bilinear D x.1 x.1 = 4 ∧ x.2 = 0) := by
  constructor
  · intro hx
    have he : chargeEnergy D x.1 + (oscillatorEnergy x.2 : ℤ) = 2 := hx
    by_cases ha : x.1 = 0
    · have hc : chargeEnergy D x.1 = 0 := by simp [ha]
      exact Or.inl ⟨ha, by omega⟩
    · have hg := chargeEnergy_gap D hD hroot x.1 ha
      have hc : chargeEnergy D x.1 = 2 := by omega
      have hd : oscillatorEnergy x.2 = 0 := by omega
      exact Or.inr ⟨(chargeEnergy_two_iff D x.1).mp hc,
        (oscillatorEnergy_eq_zero_iff D _).mp hd⟩
  · rintro (⟨ha, hd⟩ | ⟨ha, hd⟩)
    · simp [energy, ha, hd]
    · have hc := (chargeEnergy_two_iff D x.1).mpr ha
      simp [energy, hc, hd, oscillatorEnergy]

def energyZeroEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) :
    EnergyFiber D 0 ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(0, 0), (energy_eq_zero_iff D hD _).mpr rfl⟩
  left_inv x := Subtype.ext ((energy_eq_zero_iff D hD x.1).mp x.2).symm
  right_inv x := by cases x; rfl

private def energyOneNeutralEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    EnergyFiber D 1 ≃ OscillatorFiber D 1 where
  toFun x := ⟨x.1.2, ((energy_one_iff D hD hroot x.1).mp x.2).2⟩
  invFun d := ⟨(0, d.1), by simp [energy, d.2]⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext (((energy_one_iff D hD hroot x.1).mp x.2).1).symm rfl
  right_inv d := Subtype.ext rfl

def energyOneEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    EnergyFiber D 1 ≃ Fin D.rank :=
  (energyOneNeutralEquiv D hD hroot).trans (oscillatorOneEquiv D)

/-- Actual all-charge monomial labels, with no oscillator at the norm-four
charged ground states and no nonzero charge in the oscillator summand. -/
def energyTwoDecode (D : LatticeData) :
    OscillatorFiber D 2 ⊕ NormFour D → EnergyFiber D 2
  | Sum.inl d => ⟨(0, d.1), by simp [energy, d.2]⟩
  | Sum.inr a => ⟨(a.1, 0), by
      have hc := (chargeEnergy_two_iff D a.1).mpr a.2
      simp [energy, hc, oscillatorEnergy]⟩

private theorem energyTwoDecode_bijective (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Function.Bijective (energyTwoDecode D) := by
  constructor
  · intro x y h
    cases x with
    | inl d =>
      cases y with
      | inl e =>
        apply congrArg Sum.inl
        exact Subtype.ext (congrArg (fun z : EnergyFiber D 2 => z.1.2) h)
      | inr a =>
        have hd : d.1 = 0 := congrArg (fun z : EnergyFiber D 2 => z.1.2) h
        have hf := d.2
        simp [hd, oscillatorEnergy] at hf
    | inr a =>
      cases y with
      | inl d =>
        have hd : d.1 = 0 :=
          (congrArg (fun z : EnergyFiber D 2 => z.1.2) h).symm
        have hf := d.2
        simp [hd, oscillatorEnergy] at hf
      | inr b =>
        apply congrArg Sum.inr
        exact Subtype.ext (congrArg (fun z : EnergyFiber D 2 => z.1.1) h)
  · intro x
    rcases (energy_two_iff D hD hroot x.1).mp x.2 with ⟨ha, hd⟩ | ⟨ha, hd⟩
    · refine ⟨Sum.inl ⟨x.1.2, hd⟩, ?_⟩
      apply Subtype.ext
      exact Prod.ext ha.symm rfl
    · refine ⟨Sum.inr ⟨x.1.1, ha⟩, ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl hd.symm

def energyTwoEquiv (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    EnergyFiber D 2 ≃ OscillatorFiber D 2 ⊕ NormFour D :=
  (Equiv.ofBijective (energyTwoDecode D)
    (energyTwoDecode_bijective D hD hroot)).symm

def energyTwoConfigurations (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    EnergyFiber D 2 ≃ (Fin D.rank ⊕ Sym (Fin D.rank) 2) ⊕ NormFour D :=
  (energyTwoEquiv D hD hroot).trans
    (Equiv.sumCongr (oscillatorTwoEquiv D) (Equiv.refl _))

/-- Reindex the existing actual-carrier grade basis by the proved
configurations. No replacement carrier or dimension axiom is introduced. -/
def gradeTwoBasis (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.Basis ((Fin D.rank ⊕ Sym (Fin D.rank) 2) ⊕ NormFour D) ℂ (grade D 2) :=
  (gradeBasis D 2).reindex (energyTwoConfigurations D hD hroot)

theorem grade_two_finrank (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    Module.finrank ℂ (grade D 2) =
      D.rank + Nat.choose (D.rank + 1) 2 + Nat.card (NormFour D) := by
  haveI : Finite (NormFour D) := normFour_finite D hD
  rw [Module.finrank_eq_nat_card_basis (gradeTwoBasis D hD hroot), Nat.card_sum]
  rw [← Nat.card_congr (oscillatorTwoEquiv D), neutral_energy_two_card]

/-- The actual canonical inverse-Gram Sugawara operator. The only premises
are positive definiteness and rootlessness of the supplied even LatticeData.
Finiteness is proved for all signed integer eigenspaces, and the first three
finranks use the preceding genuine finite label bijections. -/
theorem actual_rootless_low_spectrum (D : LatticeData)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (hroot : ∀ a : Charge D, bilinear D a a ≠ 2) :
    (∀ n : ℤ, FiniteDimensional ℂ
      ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace (n : ℂ))) ∧
    Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 0) = 1 ∧
    Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 1) = D.rank ∧
    Module.finrank ℂ ((sugawaraMode D (gramComplex D)⁻¹ 0).eigenspace 2) =
      D.rank + Nat.choose (D.rank + 1) 2 + Nat.card (NormFour D) := by
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists D hD
  have hH : (gramComplex D)⁻¹ = H := Matrix.inv_eq_left_inv hHG
  rw [hH]
  have hfinite (n : ℤ) :
      FiniteDimensional ℂ ((sugawaraMode D H 0).eigenspace (n : ℂ)) := by
    rw [actualL0_eigenspace_eq_grade D H hHG hGH n]
    exact grade_finiteDimensional D hD n
  have hcard (n : ℤ) :
      Module.finrank ℂ ((sugawaraMode D H 0).eigenspace (n : ℂ)) =
        Nat.card (EnergyFiber D n) := by
    rw [actualL0_eigenspace_eq_grade D H hHG hGH n]
    exact Module.finrank_eq_nat_card_basis (gradeBasis D n)
  refine ⟨hfinite, ?_, ?_, ?_⟩
  · have hc : Nat.card (EnergyFiber D 0) = 1 := by
      rw [Nat.card_congr (energyZeroEquiv D hD)]
      simp
    have h := (hcard 0).trans hc
    rw [Int.cast_zero] at h
    exact h
  · have hc : Nat.card (EnergyFiber D 1) = D.rank := by
      rw [Nat.card_congr (energyOneEquiv D hD hroot)]
      simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    have h := (hcard 1).trans hc
    rw [Int.cast_one] at h
    exact h
  · change Module.finrank ℂ ((sugawaraMode D H 0).eigenspace ((2 : ℤ) : ℂ)) = _
    rw [actualL0_eigenspace_eq_grade D H hHG hGH 2]
    exact grade_two_finrank D hD hroot

#print axioms oscillator_two_classification
#print axioms oscillatorTwoEquiv
#print axioms normFour_finite
#print axioms energyTwoConfigurations
#print axioms grade_two_finrank
#print axioms actual_rootless_low_spectrum

end D5.S3.VertexAlgebra.Lattice.RootlessLowGrades
