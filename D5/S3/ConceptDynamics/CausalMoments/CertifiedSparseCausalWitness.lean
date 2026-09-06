/- GID: D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S0/Certificates/RationalMomentReplay]
   digest: Support-restricted rational Caratheodory witnesses give complete elimination certificates; accepted traces return original-carrier probability laws preserving all causal LP rows, objectives, and primal-dual endpoint witnesses. -/

import D5.S0.Certificates.RationalMomentReplay
import D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw

/- The S0 checker is executable and data-only. Classical selection is confined
   to the existence theorem here. Restricting the Caratheodory input carrier to
   the current positive support ensures that no new causal atom is introduced.
   Completeness of the certificate language is distinct from a verified solver
   that discovers null vectors or computes a Caratheodory representation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.ConceptDynamics.CausalMoments.CertifiedSparseCausalWitness

open scoped BigOperators
open D5.S0.Certificates.RationalFarkas
open D5.S0.Certificates.LinearObjectiveDual
open D5.S0.Certificates.RationalMomentElimination
open D5.S0.Certificates.RationalMomentReplay
open D5.S3.ConceptDynamics.PartialIdentification.CanonicalResponseSignature
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSupportReduction
open D5.S3.ConceptDynamics.CausalMoments.FiniteMomentSparseLaw

/-- Rational moment reduction can be restricted to atoms that already have
positive mass. It preserves all nominated moments without creating any atom. -/
theorem exists_supported_moment_replacement {n d : Nat}
    (law : FiniteResponseLaw (Fin n)) (feature : Fin n → Fin d → ℚ) :
    ∃ sparse : FiniteResponseLaw (Fin n),
      activeAtoms sparse.mass ⊆ activeAtoms law.mass ∧
      (activeAtoms sparse.mass).card ≤ d + 1 ∧
      ∀ j, linearObjective (fun i => feature i j) sparse.mass =
        linearObjective (fun i => feature i j) law.mass := by
  classical
  let S := activeAtoms law.mass
  have restrict_sum : ∀ f : Fin n → ℚ,
      (∑ i : S, law.mass i.1 * f i.1) = ∑ i, law.mass i * f i := by
    intro f
    calc
      (∑ i : S, law.mass i.1 * f i.1) = ∑ i ∈ S, law.mass i * f i := by
        simp only [Finset.univ_eq_attach]
        exact Finset.sum_attach S (fun i => law.mass i * f i)
      _ = ∑ i, law.mass i * f i := by
        change (∑ i ∈ Finset.univ.filter (fun i => law.mass i ≠ 0), law.mass i * f i) = _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases zero : law.mass i = 0 <;> simp [zero]
  let restricted : FiniteResponseLaw S := {
    mass := fun i => law.mass i.1
    nonnegative := fun i => law.nonnegative i.1
    total := by simpa only [mul_one, law.total] using restrict_sum (fun _ => 1) }
  obtain ⟨compression⟩ := exists_momentCompression restricted (fun i : S => feature i.1)
  let generator : compression.profiles → Fin n := fun profile => (compression.sourceAtom profile).1
  let sparse := pushforwardResponseLaw compression.latentLaw generator
  have support_image : activeAtoms sparse.mass ⊆ Finset.univ.image generator := by
    intro i hi
    by_contra outside
    have misses : ∀ profile, generator profile ≠ i := by
      intro profile equal
      exact outside (Finset.mem_image.mpr ⟨profile, Finset.mem_univ _, equal⟩)
    have zero : sparse.mass i = 0 := by
      change (∑ profile, if generator profile = i then compression.latentLaw.mass profile else 0) = 0
      simp [misses]
    exact (Finset.mem_filter.mp hi).2 zero
  refine ⟨sparse, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨profile, _, equal⟩ := Finset.mem_image.mp (support_image hi)
    rw [← equal]
    exact (compression.sourceAtom profile).2
  · calc
      (activeAtoms sparse.mass).card ≤ (Finset.univ.image generator).card :=
        Finset.card_le_card support_image
      _ ≤ (Finset.univ : Finset compression.profiles).card := Finset.card_image_le
      _ = compression.profiles.card := by simp
      _ ≤ d + 1 := by simpa only [Fintype.card_fin] using compression.card_le
  · intro j
    change linearObjective (fun i => feature i j)
      (pushforwardResponseLaw compression.latentLaw generator).mass = _
    rw [pushforward_linearObjective]
    calc
      linearObjective (fun profile => feature (generator profile) j) compression.latentLaw.mass =
          ∑ i : S, law.mass i.1 * feature i.1 j := by
        simpa [linearObjective, generator, restricted, mul_comm] using compression.coordinate_eq j
      _ = linearObjective (fun i => feature i j) law.mass := by
        simpa only [linearObjective, mul_comm] using restrict_sum (fun i => feature i j)

/-- Every finite rational probability vector has an accepted sparse certificate.
Existentially zero or one step suffices: after finding a supported replacement,
its difference from the initial law is a checked direction with pivot ratio one.
This does not compute that replacement or give a one-step search algorithm. -/
theorem exists_accepted_moment_certificate {n d : Nat}
    (law : FiniteResponseLaw (Fin n)) (feature : Fin n → Fin d → ℚ) :
    ∃ (result : Fin n → ℚ) (steps : List (EliminationStep n)),
      checkCompression feature law.mass steps = some result ∧ steps.length ≤ 1 := by
  classical
  have initial_ok : (∀ i, 0 ≤ law.mass i) ∧ (∑ i, law.mass i) = 1 :=
    ⟨law.nonnegative, law.total⟩
  by_cases already_small : (activeAtoms law.mass).card ≤ d + 1
  · refine ⟨law.mass, [], ?_, by simp⟩
    simp only [checkCompression, if_pos initial_ok, replaySteps, if_pos already_small]
  · obtain ⟨sparse, contained, small, moments⟩ := exists_supported_moment_replacement law feature
    have missing : ∃ p, p ∈ activeAtoms law.mass ∧ p ∉ activeAtoms sparse.mass := by
      by_contra no_missing
      have subset : activeAtoms law.mass ⊆ activeAtoms sparse.mass := by
        intro p hp
        by_contra hout
        exact no_missing ⟨p, hp, hout⟩
      exact already_small ((Finset.card_le_card subset).trans small)
    obtain ⟨pivot, pivot_in, pivot_out⟩ := missing
    have pivot_positive : 0 < law.mass pivot :=
      lt_of_le_of_ne (law.nonnegative pivot) (Ne.symm (Finset.mem_filter.mp pivot_in).2)
    have sparse_pivot_zero : sparse.mass pivot = 0 := by
      by_contra nonzero
      exact pivot_out (Finset.mem_filter.mpr ⟨Finset.mem_univ _, nonzero⟩)
    have inactive : ∀ i, law.mass i = 0 → sparse.mass i = 0 := by
      intro i zero
      by_contra nonzero
      have member := contained (Finset.mem_filter.mpr ⟨Finset.mem_univ _, nonzero⟩)
      exact (Finset.mem_filter.mp member).2 zero
    let step : EliminationStep n := {
      direction := fun i => law.mass i - sparse.mass i
      pivot := pivot }
    have valid : ValidStep feature law.mass step := by
      refine ⟨law.nonnegative, pivot_positive, ?_, ?_, ?_, ?_, ?_⟩
      · change 0 < law.mass pivot - sparse.mass pivot
        simpa only [sparse_pivot_zero, sub_zero] using pivot_positive
      · intro i zero
        change law.mass i - sparse.mass i = 0
        rw [zero, inactive i zero, sub_self]
      · change (∑ i, (law.mass i - sparse.mass i)) = 0
        rw [Finset.sum_sub_distrib, law.total, sparse.total, sub_self]
      · intro j
        change linearObjective (fun i => feature i j) (fun i => law.mass i - sparse.mass i) = 0
        calc
          _ = linearObjective (fun i => feature i j) law.mass -
              linearObjective (fun i => feature i j) sparse.mass := by
            simp only [linearObjective, mul_sub, Finset.sum_sub_distrib]
          _ = 0 := by rw [moments j, sub_self]
      · intro i _
        change law.mass pivot * (law.mass i - sparse.mass i) ≤
          law.mass i * (law.mass pivot - sparse.mass pivot)
        rw [sparse_pivot_zero, sub_zero]
        nlinarith [mul_nonneg pivot_positive.le (sparse.nonnegative i)]
    have update : eliminate law.mass step = sparse.mass := by
      funext i
      change law.mass i - (law.mass pivot / (law.mass pivot - sparse.mass pivot)) *
        (law.mass i - sparse.mass i) = sparse.mass i
      rw [sparse_pivot_zero, sub_zero, div_self (ne_of_gt pivot_positive), one_mul]
      ring
    have checked := (checkStep_eq_true_iff feature law.mass step).mpr valid
    refine ⟨sparse.mass, [step], ?_, by simp⟩
    simp only [checkCompression, if_pos initial_ok, replaySteps, if_pos checked, update, if_pos small]

/-- Fin-indexed array adapter: coordinate zero is the query; successor
coordinates are the original data rows. Normalization is checked separately. -/
def rowQueryArray {n m : Nat} (A : Fin m → Fin n → ℚ) (query : Fin n → ℚ) :
    Fin n → Fin (m + 1) → ℚ :=
  fun i j => Fin.cases (query i) (fun c => A c i) j

/-- An accepted certificate returns a normalized probability law on the original
carrier preserving every original LP row and the exact original objective. -/
theorem checked_causal_problem_witness {n m : Nat}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (query : Fin n → ℚ)
    (law : FiniteResponseLaw (Fin n)) (result : Fin n → ℚ)
    (steps : List (EliminationStep n)) (feasible : LinearFeasible A b law.mass)
    (accepted : checkCompression (rowQueryArray A query) law.mass steps = some result) :
    ∃ sparse : FiniteResponseLaw (Fin n), sparse.mass = result ∧
      activeAtoms sparse.mass ⊆ activeAtoms law.mass ∧
      (activeAtoms sparse.mass).card ≤ m + 2 ∧
      LinearFeasible A b sparse.mass ∧
      linearObjective query sparse.mass = linearObjective query law.mass := by
  obtain ⟨hn, ht, hm, hs, hc, _⟩ :=
    checkCompression_sound (rowQueryArray A query) law.mass result steps accepted
  let sparse : FiniteResponseLaw (Fin n) := ⟨result, hn, ht⟩
  refine ⟨sparse, rfl, hs, ?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hc
  · intro c
    have row_eq : linearObjective (A c) result = linearObjective (A c) law.mass := by
      simpa only [rowQueryArray, Fin.cases_succ] using hm c.succ
    change linearObjective (A c) result ≤ b c
    rw [row_eq]
    exact feasible c
  · simpa only [rowQueryArray, Fin.cases_zero] using hm 0

/-- A prior lower dual certificate remains usable with the checked sparse
attaining law. Sparse replay does not modify the original inequality system. -/
theorem checked_lower_endpoint_witness {n m : Nat}
    (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ) (query : Fin n → ℚ) (lower : ℚ)
    (dual : LowerBoundCertificate A b query lower)
    (law : FiniteResponseLaw (Fin n)) (feasible : LinearFeasible A b law.mass)
    (attains : linearObjective query law.mass = lower)
    (result : Fin n → ℚ) (steps : List (EliminationStep n))
    (accepted : checkCompression (rowQueryArray A query) law.mass steps = some result) :
    IsExactLowerBound A b query lower ∧
      ∃ sparse : FiniteResponseLaw (Fin n), sparse.mass = result ∧
        (activeAtoms sparse.mass).card ≤ m + 2 ∧
        LinearFeasible A b sparse.mass ∧ linearObjective query sparse.mass = lower := by
  obtain ⟨sparse, mass_eq, _, small, sparse_feasible, query_eq⟩ :=
    checked_causal_problem_witness A b query law result steps feasible accepted
  have sparse_attains := query_eq.trans attains
  have witness : PrimalWitness A b query lower := ⟨sparse.mass, sparse_feasible, sparse_attains⟩
  exact ⟨exact_lower_bound_of_certificate_and_witness A b query lower dual witness,
    sparse, mass_eq, small, sparse_feasible, sparse_attains⟩

#print axioms exists_supported_moment_replacement
#print axioms exists_accepted_moment_certificate
#print axioms checked_causal_problem_witness
#print axioms checked_lower_endpoint_witness

end D5.S3.ConceptDynamics.CausalMoments.CertifiedSparseCausalWitness
