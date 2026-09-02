/- GID: D5/S0/Certificates/FiniteBranchAtlas
   generality: G
   mirror-B: D5/B/S0/Certificates/FiniteBranchAtlas
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Exhaustive refutations of every branch in a finite covering atlas exclude all admissible candidates. -/

import D5.S0.Certificates.FiniteExhaustion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.FiniteBranchAtlas

open D5.S0.Certificates.FiniteExhaustion

universe u v

/-- A finite branch atlas covers every candidate by at least one Boolean branch predicate. -/
structure Atlas (Candidate : Type u) (Branch : Type v)
    [Fintype Candidate] [Fintype Branch] where
  inBranch : Candidate → Branch → Bool
  covers : ∀ candidate, ∃ branch, inBranch candidate branch = true

/-- The finite predicate searching for an admissible candidate inside one branch. -/
def branchWitnessPredicate
    {Candidate : Type u} {Branch : Type v}
    [Fintype Candidate] [Fintype Branch]
    (atlas : Atlas Candidate Branch) (admissible : Candidate → Bool)
    (branch : Branch) : Candidate → Bool :=
  fun candidate => atlas.inBranch candidate branch && admissible candidate

/-- Exhaustively certify that one branch contains no admissible candidate. -/
def branchEmptyCheck
    {Candidate : Type u} {Branch : Type v}
    [Fintype Candidate] [Fintype Branch]
    (atlas : Atlas Candidate Branch) (admissible : Candidate → Bool)
    (branch : Branch) : Bool :=
  exhaustiveUnsatCheck (branchWitnessPredicate atlas admissible branch)

/-- If every branch of a covering finite atlas is exhaustively refuted, no admissible candidate exists. -/
theorem no_admissible_of_all_branch_checks
    {Candidate : Type u} {Branch : Type v}
    [Fintype Candidate] [Fintype Branch]
    (atlas : Atlas Candidate Branch) (admissible : Candidate → Bool)
    (checks : ∀ branch, branchEmptyCheck atlas admissible branch = true) :
    ¬ ∃ candidate, admissible candidate = true := by
  rintro ⟨candidate, hCandidate⟩
  obtain ⟨branch, hBranch⟩ := atlas.covers candidate
  have checked :
      exhaustiveUnsatCheck (branchWitnessPredicate atlas admissible branch) = true := by
    simpa [branchEmptyCheck] using checks branch
  have noWitness :
      ¬ ∃ x, branchWitnessPredicate atlas admissible branch x = true :=
    unsatisfiable_of_exhaustive_check checked
  apply noWitness
  refine ⟨candidate, ?_⟩
  simp [branchWitnessPredicate, hBranch, hCandidate]

/-- A single surviving admissible candidate forces at least one atlas branch check to fail. -/
theorem exists_failed_branch_check_of_admissible
    {Candidate : Type u} {Branch : Type v}
    [Fintype Candidate] [Fintype Branch]
    (atlas : Atlas Candidate Branch) (admissible : Candidate → Bool)
    (candidate : Candidate) (hCandidate : admissible candidate = true) :
    ∃ branch, branchEmptyCheck atlas admissible branch = false := by
  obtain ⟨branch, hBranch⟩ := atlas.covers candidate
  refine ⟨branch, ?_⟩
  have hnot :
      ¬ ∀ x, branchWitnessPredicate atlas admissible branch x = false := by
    intro h
    have hc := h candidate
    simp [branchWitnessPredicate, hBranch, hCandidate] at hc
  unfold branchEmptyCheck exhaustiveUnsatCheck
  exact decide_eq_false hnot

#print axioms no_admissible_of_all_branch_checks
#print axioms exists_failed_branch_check_of_admissible

end D5.S0.Certificates.FiniteBranchAtlas
