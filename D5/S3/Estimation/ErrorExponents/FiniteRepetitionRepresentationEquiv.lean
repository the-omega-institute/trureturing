/- GID: D5/S3/Estimation/ErrorExponents/FiniteRepetitionRepresentationEquiv
   generality: G
   mirror-B: D5/B/S3/Estimation/ErrorExponents/FiniteRepetitionRepresentationEquiv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Recursive IidSpace samples, product masses, distances, affinities, and decision risks transport exactly to the canonical Fin-indexed finite-suite representation. -/

import D5.S3.RenyiDivergence.PowerAdditivity
import D5.S3.Entropy.NamingWindow.GreenClassWindowHellinger
import D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
import D5.S3.TotalVariation.Metric
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite repetition representation equivalence

The repository has two established finite-product encodings. `IidSpace ι n` is
the recursive right-associated product used by Renyi and arbitrary-test
results. `Fin n -> ι` is the tuple encoding used by `windowLaw` and the
operational finite-suite Bayes-risk owner.

This module proves that the carriers are equivalent using Mathlib's canonical
`Fin.consEquiv`, then proves that the two product masses agree pointwise under
that equivalence. Total variation and Bhattacharyya affinity therefore agree
exactly after reindexing. Decision finsets, their complements, and equal-prior
risk also transport exactly.

No third repetition representation or second Bayes-risk primitive is
introduced. The two existing interfaces are now related by an explicit
change of coordinates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.ErrorExponents.FiniteRepetitionRepresentationEquiv

open D5.S3.RenyiDivergence
open D5.S3.Entropy.NamingWindow.GreenClassWindowEntropy
open D5.S3.Estimation.ErrorExponents.FiniteSuiteErrorSqueeze
open D5.S3.TotalVariation.Pinsker
open D5.S3.TotalVariation.Bhattacharyya
open scoped BigOperators

universe u

/-- Canonical equivalence between the recursive iid carrier and an `n`-tuple.
The successor step is exactly Mathlib's `Fin.consEquiv`. -/
noncomputable def iidSpaceFinEquiv (ι : Type u) :
    (n : ℕ) -> IidSpace ι n ≃ (Fin n -> ι)
  | 0 =>
      { toFun := fun _ i => Fin.elim0 i
        invFun := fun _ => PUnit.unit
        left_inv := fun z => Subsingleton.elim _ _
        right_inv := fun f => funext fun i => Fin.elim0 i }
  | n + 1 =>
      (Equiv.prodCongr (Equiv.refl ι) (iidSpaceFinEquiv ι n)).trans
        (Fin.consEquiv (fun _ : Fin (n + 1) => ι))

@[simp]
theorem iid_space_fin_equiv_succ_zero
    (ι : Type u) (n : ℕ) (head : ι) (tail : IidSpace ι n) :
    iidSpaceFinEquiv ι (n + 1) (head, tail) 0 = head := by
  simp [iidSpaceFinEquiv]

@[simp]
theorem iid_space_fin_equiv_succ_succ
    (ι : Type u) (n : ℕ) (head : ι) (tail : IidSpace ι n) (i : Fin n) :
    iidSpaceFinEquiv ι (n + 1) (head, tail) i.succ =
      iidSpaceFinEquiv ι n tail i := by
  simp [iidSpaceFinEquiv]

/-- Under the canonical carrier equivalence, the recursive iid mass is exactly
the repository's `windowLaw` product of identical coordinate laws. -/
theorem iid_power_eq_windowLaw
    {ι : Type u} (p : ι -> ℝ) :
    ∀ (n : ℕ) (z : IidSpace ι n),
      iidPower p n z =
        windowLaw (fun _ : Fin n => p) (iidSpaceFinEquiv ι n z) := by
  intro n
  induction n with
  | zero =>
      intro z
      have hz : z = PUnit.unit := Subsingleton.elim _ _
      subst z
      simp [iidPower, windowLaw, iidSpaceFinEquiv]
  | succ n ih =>
      rintro ⟨head, tail⟩
      rw [iidPower, windowLaw, Fin.prod_univ_succ,
        iid_space_fin_equiv_succ_zero]
      calc
        p head * iidPower p n tail =
            p head * windowLaw (fun _ : Fin n => p)
              (iidSpaceFinEquiv ι n tail) := by rw [ih tail]
        _ = p head *
            ∏ i : Fin n,
              p (iidSpaceFinEquiv ι (n + 1) (head, tail) i.succ) := by
          congr 1
          unfold windowLaw
          apply Finset.prod_congr rfl
          intro i hi
          rw [iid_space_fin_equiv_succ_succ]

/-- Total variation is invariant under the exact change from recursive iid
samples to `Fin n` tuples. -/
theorem total_variation_iidPower_eq_windowLaw
    {ι : Type u} [Fintype ι]
    (p q : ι -> ℝ) (n : ℕ) :
    totalVariation (iidPower p n) (iidPower q n) =
      totalVariation
        (windowLaw (fun _ : Fin n => p))
        (windowLaw (fun _ : Fin n => q)) := by
  classical
  let e := iidSpaceFinEquiv ι n
  unfold totalVariation
  congr 1
  calc
    (∑ z : IidSpace ι n, |iidPower p n z - iidPower q n z|) =
        ∑ z : IidSpace ι n,
          |windowLaw (fun _ : Fin n => p) (e z) -
            windowLaw (fun _ : Fin n => q) (e z)| := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [iid_power_eq_windowLaw p n z, iid_power_eq_windowLaw q n z]
      rfl
    _ = ∑ u : Fin n -> ι,
          |windowLaw (fun _ : Fin n => p) u -
            windowLaw (fun _ : Fin n => q) u| := by
      exact e.sum_comp
        (fun u : Fin n -> ι =>
          |windowLaw (fun _ : Fin n => p) u -
            windowLaw (fun _ : Fin n => q) u|)

/-- Bhattacharyya affinity is invariant under the same carrier-and-law
reindexing. -/
theorem bhattacharyya_iidPower_eq_windowLaw
    {ι : Type u} [Fintype ι]
    (p q : ι -> ℝ) (n : ℕ) :
    bhattacharyya (iidPower p n) (iidPower q n) =
      bhattacharyya
        (windowLaw (fun _ : Fin n => p))
        (windowLaw (fun _ : Fin n => q)) := by
  classical
  let e := iidSpaceFinEquiv ι n
  unfold bhattacharyya
  calc
    (∑ z : IidSpace ι n,
        Real.sqrt (iidPower p n z * iidPower q n z)) =
      ∑ z : IidSpace ι n,
        Real.sqrt
          (windowLaw (fun _ : Fin n => p) (e z) *
            windowLaw (fun _ : Fin n => q) (e z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [iid_power_eq_windowLaw p n z, iid_power_eq_windowLaw q n z]
      rfl
    _ = ∑ u : Fin n -> ι,
        Real.sqrt
          (windowLaw (fun _ : Fin n => p) u *
            windowLaw (fun _ : Fin n => q) u) := by
      exact e.sum_comp
        (fun u : Fin n -> ι =>
          Real.sqrt
            (windowLaw (fun _ : Fin n => p) u *
              windowLaw (fun _ : Fin n => q) u))

/-- Transport a recursive iid decision event to the canonical finite-suite
carrier. This is just the `Finset` action of the carrier equivalence. -/
noncomputable def iidDecisionToFin
    (ι : Type u) (n : ℕ) :
    Finset (IidSpace ι n) -> Finset (Fin n -> ι) :=
  (iidSpaceFinEquiv ι n).finsetCongr

@[simp]
theorem mem_iidDecisionToFin
    {ι : Type u} (n : ℕ) (decision : Finset (IidSpace ι n))
    (u : Fin n -> ι) :
    u ∈ iidDecisionToFin ι n decision ↔
      (iidSpaceFinEquiv ι n).symm u ∈ decision := by
  simp [iidDecisionToFin, Equiv.finsetCongr_apply]

/-- Complementing a decision event commutes with the carrier equivalence. -/
theorem iidDecisionToFin_compl
    {ι : Type u} [Fintype ι]
    (n : ℕ) (decision : Finset (IidSpace ι n)) :
    iidDecisionToFin ι n decisionᶜ =
      (iidDecisionToFin ι n decision)ᶜ := by
  classical
  ext u
  simp [mem_iidDecisionToFin]

/-- The mass assigned to a decision event is unchanged when both the event and
the repeated law are transported to the `Fin n` representation. -/
theorem iid_decision_mass_eq_windowLaw
    {ι : Type u} [Fintype ι]
    (p : ι -> ℝ) (n : ℕ) (decision : Finset (IidSpace ι n)) :
    (∑ z ∈ decision, iidPower p n z) =
      ∑ u ∈ iidDecisionToFin ι n decision,
        windowLaw (fun _ : Fin n => p) u := by
  classical
  let e := iidSpaceFinEquiv ι n
  change (∑ z ∈ decision, iidPower p n z) =
    ∑ u ∈ decision.map e.toEmbedding,
      windowLaw (fun _ : Fin n => p) u
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro z hz
  rw [iid_power_eq_windowLaw p n z]
  rfl

/-- Equal-prior decision risk is exactly representation invariant. This is the
operational bridge between arbitrary recursive iid tests and the finite-suite
coordinates used by `finiteSuiteOptimalError`. -/
theorem iid_equal_prior_error_eq_windowLaw
    {ι : Type u} [Fintype ι]
    (p q : ι -> ℝ) (n : ℕ) (decision : Finset (IidSpace ι n)) :
    equalPriorError (iidPower p n) (iidPower q n) decision =
      equalPriorError
        (windowLaw (fun _ : Fin n => p))
        (windowLaw (fun _ : Fin n => q))
        (iidDecisionToFin ι n decision) := by
  unfold equalPriorError
  rw [iid_decision_mass_eq_windowLaw p n decision,
    iid_decision_mass_eq_windowLaw q n decisionᶜ,
    iidDecisionToFin_compl]

#print axioms iid_space_fin_equiv_succ_zero
#print axioms iid_space_fin_equiv_succ_succ
#print axioms iid_power_eq_windowLaw
#print axioms total_variation_iidPower_eq_windowLaw
#print axioms bhattacharyya_iidPower_eq_windowLaw
#print axioms mem_iidDecisionToFin
#print axioms iidDecisionToFin_compl
#print axioms iid_decision_mass_eq_windowLaw
#print axioms iid_equal_prior_error_eq_windowLaw

end D5.S3.Estimation.ErrorExponents.FiniteRepetitionRepresentationEquiv
