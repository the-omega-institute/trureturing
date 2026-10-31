/- GID: D5/S3/Quantum/Information/MarginalCalculus
   generality: G
   mirror-B: D5/B/S3/Quantum/Information/MarginalCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Composition and basis independence of actual finite density marginals. -/

import D5.S3.Quantum.Information.StrongSubadditivity

set_option autoImplicit false

open scoped BigOperators
open D5.S3.Quantum.Divergence.QuantumRelativeEntropyDefectComposition
open D5.S3.Quantum.Divergence.VonNeumannEntropyPinching
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Information.StrongSubadditivity

namespace D5.S3.Quantum.Information.MarginalCalculus

variable {N K R S T K' R' : Type*}
  [Fintype N] [DecidableEq N] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype K'] [DecidableEq K']
  [Fintype R'] [DecidableEq R']

/-- Keep K and trace R, using an explicit tensor-coordinate equivalence. -/
noncomputable def reduceState (e : (K × R) ≃ N) (rho : DensityState N) : DensityState K :=
  marginalRight (relabelState e rho)

theorem relabelState_comp (e : K ≃ N) (f : S ≃ K) (rho : DensityState N) :
    relabelState f (relabelState e rho) = relabelState (f.trans e) rho := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  rfl

theorem reduceState_entry (e : (K × R) ≃ N) (rho : DensityState N) (i j : K) :
    CStarMatrix.ofMatrix.symm (reduceState e rho).1 i j =
      ∑ r, CStarMatrix.ofMatrix.symm rho.1 (e (i, r)) (e (j, r)) := rfl

/-- A change of traced basis has no effect; a change of kept basis only relabels the result. -/
theorem reduceState_reindex (e : (K × R) ≃ N) (k : K' ≃ K) (r : R' ≃ R)
    (rho : DensityState N) :
    reduceState ((k.prodCongr r).trans e) rho = relabelState k (reduceState e rho) := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext i j
  simp only [relabelState_matrix, reduceState_entry]
  change (∑ x : R', CStarMatrix.ofMatrix.symm rho.1 (e (k i, r x)) (e (k j, r x))) =
    ∑ y : R, CStarMatrix.ofMatrix.symm rho.1 (e (k i, y)) (e (k j, y))
  exact r.sum_comp (fun y : R =>
    CStarMatrix.ofMatrix.symm rho.1 (e (k i, y)) (e (k j, y)))

theorem entropy_reduceState_reindex (e : (K × R) ≃ N) (k : K' ≃ K) (r : R' ≃ R)
    (rho : DensityState N) :
    vonNeumannEntropy (reduceState ((k.prodCongr r).trans e) rho) =
      vonNeumannEntropy (reduceState e rho) := by
  rw [reduceState_reindex, entropy_relabelState]

theorem entropy_reduceState_congr (f : (K' × R') ≃ N) (e : (K × R) ≃ N)
    (k : K' ≃ K) (r : R' ≃ R) (rho : DensityState N)
    (h : ∀ q, f q = e (k q.1, r q.2)) :
    vonNeumannEntropy (reduceState f rho) = vonNeumannEntropy (reduceState e rho) := by
  have he : f = (k.prodCongr r).trans e := Equiv.ext h
  rw [he, entropy_reduceState_reindex]

theorem reduceState_congr (f : (K' × R') ≃ N) (e : (K × R) ≃ N)
    (k : K' ≃ K) (r : R' ≃ R) (rho : DensityState N)
    (h : ∀ q, f q = e (k q.1, r q.2)) :
    reduceState f rho = relabelState k (reduceState e rho) := by
  have he : f = (k.prodCongr r).trans e := Equiv.ext h
  rw [he, reduceState_reindex]

/-- Two actual traces compose to the trace over the product of the discarded registers. -/
theorem reduceState_compose (e : (K × R) ≃ N) (f : (S × T) ≃ K)
    (rho : DensityState N) :
    reduceState f (reduceState e rho) =
      reduceState (((Equiv.prodAssoc S T R).symm.trans
        (f.prodCongr (Equiv.refl R))).trans e) rho := by
  apply Subtype.ext
  apply CStarMatrix.ofMatrix.symm.injective
  ext i j
  change (∑ t : T, ∑ r : R,
    CStarMatrix.ofMatrix.symm rho.1 (e (f (i, t), r)) (e (f (j, t), r))) =
      ∑ tr : T × R, CStarMatrix.ofMatrix.symm rho.1
        (e (f (i, tr.1), tr.2)) (e (f (j, tr.1), tr.2))
  exact (Fintype.sum_prod_type (fun tr : T × R => CStarMatrix.ofMatrix.symm rho.1
    (e (f (i, tr.1), tr.2)) (e (f (j, tr.1), tr.2)))).symm

/-- Regroup X,Y,Z into one tensor product, retaining the middle register for SSA. -/
def centerSplit : (S × (K × R)) ≃ (K × (S × R)) where
  toFun q := (q.2.1, (q.1, q.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv := by rintro ⟨s, k, r⟩; rfl
  right_inv := by rintro ⟨k, s, r⟩; rfl

/-- SSA after an arbitrary genuine tensor-coordinate partition of the same state. -/
theorem ssa_partition (e : (K × (S × R)) ≃ N) (rho : DensityState N) :
    vonNeumannEntropy rho +
      vonNeumannEntropy (reduceState (centerSplit.trans e) rho) ≤
    vonNeumannEntropy (reduceState ((Equiv.prodAssoc K S R).trans e) rho) +
      vonNeumannEntropy (reduceState ((Equiv.prodComm (S × R) K).trans e) rho) := by
  have h := strong_subadditivity (relabelState e rho)
  have hmid : marginalRight (marginalLeft (relabelState e rho)) =
      reduceState (centerSplit.trans e) rho := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    ext i j
    change (∑ r : R, ∑ k : K, CStarMatrix.ofMatrix.symm rho.1
      (e (k, (i, r))) (e (k, (j, r)))) =
      ∑ kr : K × R, CStarMatrix.ofMatrix.symm rho.1
        (e (kr.1, (i, kr.2))) (e (kr.1, (j, kr.2)))
    rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  have hleft : marginalRight (relabelState (Equiv.prodAssoc K S R)
      (relabelState e rho)) =
      reduceState ((Equiv.prodAssoc K S R).trans e) rho := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    rfl
  have hright : marginalLeft (relabelState e rho) =
      reduceState ((Equiv.prodComm (S × R) K).trans e) rho := by
    apply Subtype.ext
    apply CStarMatrix.ofMatrix.symm.injective
    rfl
  rwa [entropy_relabelState, hmid, hleft, hright] at h

end D5.S3.Quantum.Information.MarginalCalculus
