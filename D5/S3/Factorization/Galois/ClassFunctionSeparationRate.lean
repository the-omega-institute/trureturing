/- GID: D5/S3/Factorization/Galois/ClassFunctionSeparationRate
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/ClassFunctionSeparationRate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Class-function success is a conjugacy-class count; degeneracies are explicit. -/
/- Library-search audit trail (2026-08-25):
   * Object-name searches for `ClassFunctionSeparationRate` and the declaration names below
     found no repository hit.
   * Pinned Mathlib has no bundled class-function type, but supplies `ConjClasses`,
     `ConjClasses.mem_carrier_iff_mk_eq`, and `Finset.card_eq_sum_card_fiberwise`.
   * Digest searches for finite-group success, disagreement rates, and class counts found no
     equivalent D5 theorem.
   * The Galois and splitting directories contain Frobenius-class observers, but no rate count.
   * `DistanceProfile` counts generic disagreements; it has no conjugacy-class decomposition.
   * Vocabulary variants `class function`, `conjugacy invariant`, `separation density`, and
     `distinguishing probability` found no equivalent declaration.
   * Chebotarev and Frobenius-density source searches have zero pinned-Mathlib and D5 hits.
     Therefore this module proves only the finite counting half, not prime-ideal transfer. -/

import Mathlib.GroupTheory.ClassEquation
import Mathlib.Data.Fintype.Perm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Factorization.Galois.ClassFunctionSeparationRate

/-- A target is a class function when it is constant on conjugate elements. -/
def IsConjugacyInvariantTarget {G S : Type*} [Monoid G] (target : G -> S) : Prop :=
  forall {sigma tau : G}, IsConj sigma tau -> target sigma = target tau

/-- A target pair is conjugacy invariant when each of its two readings is a class function. -/
def AreConjugacyInvariantTargets {G S : Type*} [Monoid G]
    (first second : G -> S) : Prop :=
  IsConjugacyInvariantTarget first ∧ IsConjugacyInvariantTarget second

/-- The finite event on which two targets give different readings. -/
noncomputable def separationSet {G S : Type*} [Fintype G]
    (first second : G -> S) : Finset G := by
  classical
  exact Finset.univ.filter fun sigma => first sigma ≠ second sigma

/-- The exact uniform success rate for distinguishing two targets on a finite carrier. -/
noncomputable def finiteGroupSuccessRate {G S : Type*} [Fintype G]
    (first second : G -> S) : Rat :=
  (separationSet first second).card / Fintype.card G

/-- A conjugacy class is separating when it contains a successful group element. -/
def conjugacyClassSeparates {G S : Type*} [Monoid G] (first second : G -> S)
    (conjClass : ConjClasses G) : Prop :=
  exists sigma, sigma ∈ conjClass.carrier ∧ first sigma ≠ second sigma

/-- The conjugacy classes on which the two targets differ. -/
noncomputable def separatingConjugacyClasses {G S : Type*} [Monoid G] [Fintype G]
    (first second : G -> S) : Finset (ConjClasses G) := by
  classical
  exact Finset.univ.filter fun conjClass =>
    conjugacyClassSeparates first second conjClass

/-- The number of successful elements, computed by summing whole conjugacy classes. -/
noncomputable def conjugacyClassSeparationCount {G S : Type*} [Monoid G] [Fintype G]
    (first second : G -> S) : Nat := by
  classical
  exact ∑ conjClass ∈ separatingConjugacyClasses first second,
    conjClass.carrier.toFinset.card

/-- For class-function targets, the separation event is constant on conjugacy classes. -/
theorem separation_set_membership_is_conjugacy_invariant
    {G S : Type*} [Monoid G] [Fintype G] {first second : G -> S}
    (hinvariant : AreConjugacyInvariantTargets first second) {sigma tau : G}
    (hconj : IsConj sigma tau) :
    sigma ∈ separationSet first second <-> tau ∈ separationSet first second := by
  simp only [separationSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hinvariant.1 hconj, hinvariant.2 hconj]

#print axioms separation_set_membership_is_conjugacy_invariant

private theorem separation_card_eq_conjugacy_class_count
    {G S : Type*} [Monoid G] [Fintype G] {first second : G -> S}
    (hinvariant : AreConjugacyInvariantTargets first second) :
    (separationSet first second).card = conjugacyClassSeparationCount first second := by
  classical
  have classwise :
      forall conjClass : ConjClasses G,
        conjugacyClassSeparates first second conjClass ->
          forall {sigma : G}, ConjClasses.mk sigma = conjClass ->
            first sigma ≠ second sigma := by
    intro conjClass hclass sigma hsigma
    obtain ⟨witness, hwitness, hseparates⟩ := hclass
    have hwitnessClass : ConjClasses.mk witness = conjClass :=
      ConjClasses.mem_carrier_iff_mk_eq.mp hwitness
    have hconj : IsConj sigma witness :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (hsigma.trans hwitnessClass.symm)
    intro heq
    apply hseparates
    exact (hinvariant.1 hconj).symm.trans (heq.trans (hinvariant.2 hconj))
  calc
    (separationSet first second).card =
        ∑ conjClass ∈ (Finset.univ : Finset (ConjClasses G)),
          ((separationSet first second).filter fun sigma =>
            ConjClasses.mk sigma = conjClass).card := by
      apply Finset.card_eq_sum_card_fiberwise
      intro sigma hsigma
      simp
    _ = ∑ conjClass ∈ (Finset.univ : Finset (ConjClasses G)),
        if conjugacyClassSeparates first second conjClass then
          conjClass.carrier.toFinset.card else 0 := by
      apply Finset.sum_congr rfl
      intro conjClass hclass
      by_cases hseparates : conjugacyClassSeparates first second conjClass
      · rw [if_pos hseparates]
        congr 1
        ext sigma
        simp only [Finset.mem_filter, separationSet, Finset.mem_univ, true_and,
          Set.mem_toFinset, ConjClasses.mem_carrier_iff_mk_eq]
        constructor
        · exact fun hsigma => hsigma.2
        · intro hsigma
          exact ⟨classwise conjClass hseparates hsigma, hsigma⟩
      · rw [if_neg hseparates]
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro sigma hsigma hsigmaClass
        apply hseparates
        refine ⟨sigma, ?_, ?_⟩
        · exact ConjClasses.mem_carrier_iff_mk_eq.mpr hsigmaClass
        · simpa [separationSet] using hsigma
    _ = conjugacyClassSeparationCount first second := by
      rw [conjugacyClassSeparationCount, separatingConjugacyClasses, Finset.sum_filter]

/-- The uniform finite-group success rate is computable by conjugacy-class cardinalities. -/
theorem finite_group_success_rate_eq_conjugacy_class_count
    {G S : Type*} [Monoid G] [Fintype G] {first second : G -> S}
    (hinvariant : AreConjugacyInvariantTargets first second) :
    finiteGroupSuccessRate first second =
      (conjugacyClassSeparationCount first second : Rat) / Fintype.card G := by
  rw [finiteGroupSuccessRate, separation_card_eq_conjugacy_class_count hinvariant]

#print axioms finite_group_success_rate_eq_conjugacy_class_count

/-- On an empty finite carrier, the totalized rational rate is zero. -/
theorem empty_carrier_has_zero_success_rate {S : Type*} (first second : Fin 0 -> S) :
    finiteGroupSuccessRate first second = 0 := by
  simp [finiteGroupSuccessRate, separationSet]

#print axioms empty_carrier_has_zero_success_rate

/-- A monoid carrier cannot itself be empty because it contains one. -/
theorem monoid_carrier_is_nonempty {G : Type*} [Monoid G] : Nonempty G :=
  ⟨1⟩

#print axioms monoid_carrier_is_nonempty

/-- Identical targets have zero distinguishing success on every finite carrier. -/
theorem identical_targets_have_zero_success_rate
    {G S : Type*} [Fintype G] (target : G -> S) :
    finiteGroupSuccessRate target target = 0 := by
  simp [finiteGroupSuccessRate, separationSet]

#print axioms identical_targets_have_zero_success_rate

/-- Distinct constant targets on the trivial group have full success rate. -/
theorem trivial_group_distinct_targets_have_full_success_rate :
    finiteGroupSuccessRate (fun _ : Unit => true) (fun _ : Unit => false) = 1 := by
  norm_num [finiteGroupSuccessRate, separationSet]

#print axioms trivial_group_distinct_targets_have_full_success_rate

/-- Without conjugacy invariance, a target can separate two conjugate permutations unevenly. -/
theorem conjugacy_invariance_is_necessary :
    let target : Equiv.Perm (Fin 3) -> Fin 3 := fun sigma => sigma 0
    let constant : Equiv.Perm (Fin 3) -> Fin 3 := fun _ => 0
    IsConjugacyInvariantTarget constant ∧
      ¬AreConjugacyInvariantTargets target constant ∧
    exists sigma tau : Equiv.Perm (Fin 3), IsConj sigma tau ∧
      sigma ∈ separationSet target constant ∧ tau ∉ separationSet target constant := by
  dsimp only
  let sigma : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let conjugator : Equiv.Perm (Fin 3) := Equiv.swap 0 2
  let tau := conjugator * sigma * conjugator⁻¹
  have hconj : IsConj sigma tau := isConj_iff.mpr ⟨conjugator, rfl⟩
  have hconstant : IsConjugacyInvariantTarget
      (fun _ : Equiv.Perm (Fin 3) => (0 : Fin 3)) := by
    intro first second hfirstSecond
    rfl
  have hsigma : sigma ∈ separationSet (fun p => p 0) (fun _ => 0) := by
    simp [separationSet, sigma]
  have htau : tau ∉ separationSet (fun p => p 0) (fun _ => 0) := by
    simp [separationSet, tau, conjugator, sigma, Equiv.swap_apply_def]
  refine ⟨hconstant, ?_, sigma, tau, hconj, hsigma, htau⟩
  intro hinvariant
  exact htau
    ((separation_set_membership_is_conjugacy_invariant hinvariant hconj).mp hsigma)

#print axioms conjugacy_invariance_is_necessary

end D5.S3.Factorization.Galois.ClassFunctionSeparationRate
