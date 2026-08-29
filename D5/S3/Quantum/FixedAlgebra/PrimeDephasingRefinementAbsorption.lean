/- GID: D5/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption
   generality: G
   mirror-B: D5/B/S3/Quantum/FixedAlgebra/PrimeDephasingRefinementAbsorption
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Record-channel dephasings commute and absorb under profile-set refinement. -/

/- Library-search audit trail (2026-08-29):
   * Repository shape searches found `recordChannel` and its fixed-block theorem, but no
     refinement-composition theorem; both canonical declarations are reused below.
   * `QuantumChannels.Pinching.pinching_idempotent` and
     `FiniteRecordPinchingIdempotence.finite_record_pinching_idempotent` cover only S = T.
   * Searches in Quantum/Measurement, Quantum/FixedAlgebra, EnvironmentRecords,
     Quantum/Completion, and the pinned Mathlib tree found no refinement absorption law.
   * Loogle returned zero exact matches for `Function.comp ?f ?f = ?f`; the LeanSearch
     endpoint returned no result body, so no claim is made for that service. -/

import D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.FixedAlgebra.PrimeDephasingRefinementAbsorption

open D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

/-- The observed prime-exponent profile of an address, restricted to the finite index set S. -/
def restrictedPrimeProfile {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin d -> Prime -> Value) (i : Fin d) :
    {p : Prime // p ∈ S} -> Value :=
  fun p => valuation i p.1

/-- The least address carrying the same restricted profile as the given address. -/
noncomputable def profileClassRepresentative {d : Nat} {Profile : Type*}
    (classOf : Fin d -> Profile) (i : Fin d) : Fin d := by
  classical
  have nonempty : (Finset.univ.filter fun j => classOf j = classOf i).Nonempty :=
    ⟨i, by simp⟩
  exact (Finset.univ.filter fun j => classOf j = classOf i).min' nonempty

/-- A canonical orthogonal environment record for the fibers of an observed profile. -/
noncomputable def orthogonalProfileRecord {d : Nat} {Profile : Type*}
    (classOf : Fin d -> Profile) : Fin d -> Fin d -> ℂ :=
  fun i a => if a = profileClassRepresentative classOf i then 1 else 0

/-- The finite-prime dephasing channel, realized by the repository's canonical record channel. -/
noncomputable def primeDephasing {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin d -> Prime -> Value) :
    Matrix (Fin d) (Fin d) ℂ -> Matrix (Fin d) (Fin d) ℂ :=
  recordChannel (orthogonalProfileRecord (restrictedPrimeProfile S valuation))

private theorem profile_class_representative_class {d : Nat} {Profile : Type*}
    (classOf : Fin d -> Profile) (i : Fin d) :
    classOf (profileClassRepresentative classOf i) = classOf i := by
  classical
  have nonempty : (Finset.univ.filter fun j => classOf j = classOf i).Nonempty :=
    ⟨i, by simp⟩
  exact (Finset.mem_filter.mp (Finset.min'_mem _ nonempty)).2

private theorem profile_class_representative_eq_iff {d : Nat} {Profile : Type*}
    (classOf : Fin d -> Profile) (i j : Fin d) :
    profileClassRepresentative classOf i = profileClassRepresentative classOf j ↔
      classOf i = classOf j := by
  constructor
  · intro h
    rw [← profile_class_representative_class classOf i,
      ← profile_class_representative_class classOf j, h]
  · intro h
    classical
    simp [profileClassRepresentative, h]

private theorem record_gram_orthogonal_profile_record_of_eq
    {d : Nat} {Profile : Type*} (classOf : Fin d -> Profile) (i j : Fin d)
    (hClass : classOf i = classOf j) :
    recordGram (orthogonalProfileRecord classOf) i j = 1 := by
  classical
  have hRepresentative :=
    (profile_class_representative_eq_iff classOf i j).mpr hClass
  simp [recordGram, orthogonalProfileRecord, hRepresentative]

private theorem record_gram_orthogonal_profile_record_of_ne
    {d : Nat} {Profile : Type*} (classOf : Fin d -> Profile) (i j : Fin d)
    (hClass : classOf i ≠ classOf j) :
    recordGram (orthogonalProfileRecord classOf) i j = 0 := by
  classical
  have hRepresentative :
      profileClassRepresentative classOf i ≠ profileClassRepresentative classOf j :=
    fun h => hClass ((profile_class_representative_eq_iff classOf i j).mp h)
  simp [recordGram, orthogonalProfileRecord, Ne.symm hRepresentative]

private theorem prime_dephasing_apply_of_eq
    {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin d -> Prime -> Value)
    (rho : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d)
    (hProfile : restrictedPrimeProfile S valuation i =
      restrictedPrimeProfile S valuation j) :
    primeDephasing S valuation rho i j = rho i j := by
  change recordGram
      (orthogonalProfileRecord (restrictedPrimeProfile S valuation)) i j * rho i j = rho i j
  rw [record_gram_orthogonal_profile_record_of_eq _ _ _ hProfile]
  exact one_mul _

private theorem prime_dephasing_apply_of_ne
    {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin d -> Prime -> Value)
    (rho : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d)
    (hProfile : restrictedPrimeProfile S valuation i ≠
      restrictedPrimeProfile S valuation j) :
    primeDephasing S valuation rho i j = 0 := by
  change recordGram
      (orthogonalProfileRecord (restrictedPrimeProfile S valuation)) i j * rho i j = 0
  rw [record_gram_orthogonal_profile_record_of_ne _ _ _ hProfile]
  exact zero_mul _

private theorem restricted_prime_profile_eq_of_subset
    {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    {S T : Finset Prime} (valuation : Fin d -> Prime -> Value) (hST : S ⊆ T)
    {i j : Fin d}
    (hT : restrictedPrimeProfile T valuation i = restrictedPrimeProfile T valuation j) :
    restrictedPrimeProfile S valuation i = restrictedPrimeProfile S valuation j := by
  funext p
  exact congrFun hT ⟨p.1, hST p.2⟩

/-- A finer finite-prime observation commutes with and absorbs a coarser dephasing. -/
theorem prime_dephasing_refinement_absorption
    {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    {S T : Finset Prime} (valuation : Fin d -> Prime -> Value) (hST : S ⊆ T) :
    Function.comp (primeDephasing T valuation) (primeDephasing S valuation) =
        Function.comp (primeDephasing S valuation) (primeDephasing T valuation) ∧
      Function.comp (primeDephasing T valuation) (primeDephasing S valuation) =
        primeDephasing T valuation ∧
      Function.comp (primeDephasing S valuation) (primeDephasing T valuation) =
        primeDephasing T valuation := by
  have leftAbsorption :
      Function.comp (primeDephasing T valuation) (primeDephasing S valuation) =
        primeDephasing T valuation := by
    funext rho
    ext i j
    simp only [Function.comp_apply]
    by_cases hT :
        restrictedPrimeProfile T valuation i = restrictedPrimeProfile T valuation j
    · have hS := restricted_prime_profile_eq_of_subset valuation hST hT
      rw [prime_dephasing_apply_of_eq T valuation _ i j hT,
        prime_dephasing_apply_of_eq S valuation rho i j hS,
        prime_dephasing_apply_of_eq T valuation rho i j hT]
    · rw [prime_dephasing_apply_of_ne T valuation _ i j hT,
        prime_dephasing_apply_of_ne T valuation rho i j hT]
  have rightAbsorption :
      Function.comp (primeDephasing S valuation) (primeDephasing T valuation) =
        primeDephasing T valuation := by
    funext rho
    ext i j
    simp only [Function.comp_apply]
    by_cases hT :
        restrictedPrimeProfile T valuation i = restrictedPrimeProfile T valuation j
    · have hS := restricted_prime_profile_eq_of_subset valuation hST hT
      rw [prime_dephasing_apply_of_eq S valuation _ i j hS,
        prime_dephasing_apply_of_eq T valuation rho i j hT]
    · by_cases hS :
          restrictedPrimeProfile S valuation i = restrictedPrimeProfile S valuation j
      · rw [prime_dephasing_apply_of_eq S valuation _ i j hS,
          prime_dephasing_apply_of_ne T valuation rho i j hT]
      · rw [prime_dephasing_apply_of_ne S valuation _ i j hS,
          prime_dephasing_apply_of_ne T valuation rho i j hT]
  exact ⟨leftAbsorption.trans rightAbsorption.symm, leftAbsorption, rightAbsorption⟩

#print axioms prime_dephasing_refinement_absorption

/-- Taking S = T in refinement absorption gives idempotence of every prime dephasing. -/
theorem prime_dephasing_idempotent
    {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin d -> Prime -> Value) :
    Function.comp (primeDephasing S valuation) (primeDephasing S valuation) =
      primeDephasing S valuation :=
  (prime_dephasing_refinement_absorption valuation (Finset.Subset.rfl)).2.1

#print axioms prime_dephasing_idempotent

/-- Observing the empty prime set leaves every matrix unchanged. -/
theorem prime_dephasing_empty
    {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    (valuation : Fin d -> Prime -> Value) :
    primeDephasing (∅ : Finset Prime) valuation = id := by
  funext rho
  ext i j
  exact prime_dephasing_apply_of_eq _ _ _ _ _ (Subsingleton.elim _ _)

#print axioms prime_dephasing_empty

/-- The full finite index set absorbs dephasing by every subset. -/
theorem prime_dephasing_univ_absorption
    {d : Nat} {Prime Value : Type*} [Fintype Prime] [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin d -> Prime -> Value) :
    Function.comp (primeDephasing Finset.univ valuation) (primeDephasing S valuation) =
        Function.comp (primeDephasing S valuation) (primeDephasing Finset.univ valuation) ∧
      Function.comp (primeDephasing Finset.univ valuation) (primeDephasing S valuation) =
        primeDephasing Finset.univ valuation ∧
      Function.comp (primeDephasing S valuation) (primeDephasing Finset.univ valuation) =
        primeDephasing Finset.univ valuation :=
  prime_dephasing_refinement_absorption valuation (Finset.subset_univ S)

#print axioms prime_dephasing_univ_absorption

/- Degenerate-input audit: empty address spaces, singleton address spaces, empty index types,
   constant and zero profiles, and an identity address profile. -/
example {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin 0 -> Prime -> Value) :
    primeDephasing S valuation = id := by
  funext rho
  exact Subsingleton.elim _ _

example {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (valuation : Fin 1 -> Prime -> Value) :
    primeDephasing S valuation = id := by
  funext rho
  ext i j
  fin_cases i
  fin_cases j
  exact prime_dephasing_apply_of_eq _ _ _ _ _ rfl

example {d : Nat} {Value : Type*} (valuation : Fin d -> Empty -> Value) :
    primeDephasing (∅ : Finset Empty) valuation = id :=
  prime_dephasing_empty valuation

example {d : Nat} {Prime Value : Type*} [DecidableEq Prime]
    (S : Finset Prime) (constantProfile : Prime -> Value) :
    primeDephasing S (fun (_ : Fin d) => constantProfile) = id := by
  funext rho
  ext i j
  exact prime_dephasing_apply_of_eq _ _ _ _ _ rfl

example {d : Nat} {Prime : Type*} [DecidableEq Prime]
    (S : Finset Prime) :
    primeDephasing S (fun (_ : Fin d) (_ : Prime) => (0 : Nat)) = id := by
  funext rho
  ext i j
  exact prime_dephasing_apply_of_eq _ _ _ _ _ rfl

example {d : Nat} :
    primeDephasing ({()} : Finset Unit) (fun (i : Fin d) (_ : Unit) => i) =
      fun rho : Matrix (Fin d) (Fin d) ℂ => Matrix.diagonal fun i => rho i i := by
  funext rho
  ext i j
  by_cases hij : i = j
  · subst j
    rw [prime_dephasing_apply_of_eq _ _ _ i i rfl]
    simp
  · have hProfile :
        restrictedPrimeProfile ({()} : Finset Unit) (fun k (_ : Unit) => k) i ≠
          restrictedPrimeProfile ({()} : Finset Unit) (fun k (_ : Unit) => k) j := by
      intro h
      have hEntry := congrFun h ⟨(), by simp⟩
      exact hij hEntry
    rw [prime_dephasing_apply_of_ne _ _ _ i j hProfile]
    simp [hij]

/-- Without S ⊆ T, the finer-first absorption conclusion can fail on a two-address system. -/
theorem refinement_subset_is_necessary :
    let S : Finset Bool := {true}
    let T : Finset Bool := ∅
    let valuation : Fin 2 -> Bool -> Fin 2 := fun i _ => i
    ¬ S ⊆ T ∧
      Function.comp (primeDephasing T valuation) (primeDephasing S valuation) ≠
        primeDephasing T valuation := by
  dsimp only
  constructor
  · simp
  · intro hFunctions
    let rho : Matrix (Fin 2) (Fin 2) ℂ := fun _ _ => 1
    have hEntry := congrArg
      (fun channel : Matrix (Fin 2) (Fin 2) ℂ -> Matrix (Fin 2) (Fin 2) ℂ =>
        channel rho (0 : Fin 2) (1 : Fin 2)) hFunctions
    have hS :
        restrictedPrimeProfile ({true} : Finset Bool) (fun i (_ : Bool) => i)
            (0 : Fin 2) ≠
          restrictedPrimeProfile ({true} : Finset Bool) (fun i (_ : Bool) => i)
            (1 : Fin 2) := by
      intro h
      have hAtTrue := congrFun h ⟨true, by simp⟩
      change (0 : Fin 2) = 1 at hAtTrue
      exact Fin.zero_ne_one hAtTrue
    have hT :
        restrictedPrimeProfile (∅ : Finset Bool) (fun i (_ : Bool) => i) (0 : Fin 2) =
          restrictedPrimeProfile (∅ : Finset Bool) (fun i (_ : Bool) => i) (1 : Fin 2) :=
      Subsingleton.elim _ _
    simp only [Function.comp_apply] at hEntry
    rw [prime_dephasing_apply_of_eq _ _ _ _ _ hT,
      prime_dephasing_apply_of_ne _ _ _ _ _ hS,
      prime_dephasing_apply_of_eq _ _ _ _ _ hT] at hEntry
    change (0 : ℂ) = 1 at hEntry
    exact zero_ne_one hEntry

#print axioms refinement_subset_is_necessary

end D5.S3.Quantum.FixedAlgebra.PrimeDephasingRefinementAbsorption
