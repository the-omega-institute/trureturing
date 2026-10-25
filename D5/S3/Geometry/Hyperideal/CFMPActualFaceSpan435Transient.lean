/- Temporary exact application, not prospective canonical D5 source.
   UNCOMPILED. The source owner must first review and apply the adjacent
   proposed-mlocal-exposure.patch in an authorized validation checkout.
   No geometric bridge is an input to this example. -/

import D5.S3.Geometry.Hyperideal.ActualCornerTransport
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Setoid.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
open D5.S3.Geometry.Hyperideal.ActualCornerTransport

example {T K : Type*} [Fintype T]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] (q : Pairing T) :
    {h : Occurrence T → K | ∀ e : GlobalEdge q, M q h e = 0} =
      (Submodule.span K (Set.range (fun i : Slot T =>
        (localLift i : Occurrence T → K) - localLift (J q i))) :
          Set (Occurrence T → K)) := by
  classical
  let U : Occurrence T → Occurrence T → K := fun o => Pi.single o 1
  let L : Slot T → Occurrence T → K := fun i => localLift i - localLift (J q i)
  let W : Submodule K (Occurrence T → K) := Submodule.span K (Set.range L)
  let μ : (Occurrence T → K) →ₗ[K] (GlobalEdge q → K) :=
    FunOnFinite.linearMap K K (P q)
  have μ_apply (a : Occurrence T → K) (e : GlobalEdge q) : μ a e = M q a e := by
    change FunOnFinite.linearMap K K (P q) a e = M q a e
    simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter, M]

  -- Consume the exact original local mlocal proof through its proposed exposure.
  -- No proof of mform, edge_labels, mlocal, or zeroM is repeated here.
  have transport_zero (i : Slot T) : μ (L i) = 0 := by
    rw [show L i = (localLift i : Occurrence T → K) - localLift (J q i) from rfl,
      map_sub]
    ext e
    simp only [Pi.sub_apply, Pi.zero_apply, μ_apply]
    exact sub_eq_zero.mpr
      (D5.S3.Geometry.Hyperideal.ActualCornerTransport.mlocal q i e).symm
  have W_le : W ≤ LinearMap.ker μ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact transport_zero i

  -- Three-slot coefficient inversion is normalization, not an escape witness.
  have one_face (x : Corner T) (r : Fin 3) :
      (localLift (x, r) : Occurrence T → K) -
        ∑ s : Fin 3, localLift (x, s) = U (edge (x, r)) := by
    funext o
    simp only [Pi.sub_apply, Finset.sum_apply]
    fin_cases r <;>
      simp [localLift, U, edge, Fin.sum_univ_succ, Pi.single_apply, eq_comm] <;>
      split_ifs <;> ring
  have target_sum (x : Corner T) :
      (∑ s : Fin 3, (localLift (J q (x, s)) : Occurrence T → K)) =
        ∑ s : Fin 3, localLift (q.p x, s) := by
    exact (q.sigma x).sum_comp (fun s => (localLift (q.p x, s) : Occurrence T → K))
  have inversion (i : Slot T) :
      L i - ∑ s : Fin 3, L (i.1, s) = U (edge i) - U (edge (J q i)) := by
    calc
      L i - ∑ s : Fin 3, L (i.1, s) =
          ((localLift i : Occurrence T → K) - ∑ s : Fin 3, localLift (i.1, s)) -
            (localLift (J q i) - ∑ s : Fin 3, localLift (J q (i.1, s))) := by
        funext o
        simp only [L, Pi.sub_apply, Finset.sum_apply, Finset.sum_sub_distrib]
        ring
      _ = U (edge i) - U (edge (J q i)) := by
        rw [target_sum]
        change
          ((localLift (i.1, i.2) : Occurrence T → K) -
              ∑ s : Fin 3, localLift (i.1, s)) -
            (localLift (q.p i.1, q.sigma i.1 i.2) -
              ∑ s : Fin 3, localLift (q.p i.1, s)) = _
        simp only [one_face]
  have generator_mem (i : Slot T) : U (edge i) - U (edge (J q i)) ∈ W := by
    rw [← inversion]
    exact W.sub_mem
      (Submodule.subset_span (Set.mem_range_self i))
      (W.sum_mem (fun s _ => Submodule.subset_span (Set.mem_range_self (i.1, s))))

  -- Equality of coordinate classes modulo W is already an equivalence relation.
  -- Use the pinned closure theorem; do not implement an EqvGen induction.
  let π : (Occurrence T → K) →ₗ[K] ((Occurrence T → K) ⧸ W) := W.mkQ
  let coordinateSetoid : Setoid (Occurrence T) := Setoid.ker (fun o => π (U o))
  have generator_eq : ∀ o z, edgeRel q o z → coordinateSetoid o z := by
    rintro o z ⟨i, rfl, rfl⟩
    change π (U (edge i)) = π (U (edge (J q i)))
    exact (Submodule.Quotient.eq W).mpr (generator_mem i)
  have closure : Relation.EqvGen.setoid (edgeRel q) ≤ coordinateSetoid :=
    Setoid.eqvGen_le generator_eq
  let v : GlobalEdge q → ((Occurrence T → K) ⧸ W) :=
    Quotient.lift (fun o => π (U o)) (fun _ _ h => closure h)
  have descend (o : Occurrence T) : v (P q o) = π (U o) := rfl

  -- Finite basis expansion followed by existing fiberwise summation.
  -- Quotient.lift avoids any representative choice or nonempty-type assumption.
  have reconstruction (h : Occurrence T → K) :
      π h = ∑ e : GlobalEdge q, M q h e • v e := by
    calc
      π h = π (∑ o : Occurrence T, Pi.single o (h o)) :=
        congrArg π (Finset.univ_sum_single h).symm
      _ = ∑ o : Occurrence T, h o • π (U o) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro o _
        have single_scale : Pi.single o (h o) = h o • U o := by
          simpa only [U, smul_eq_mul, mul_one] using (Pi.single_smul' o (h o) (1 : K))
        rw [single_scale, map_smul]
      _ = ∑ o : Occurrence T, h o • v (P q o) := by simp_rw [descend]
      _ = ∑ e : GlobalEdge q,
          ∑ o ∈ (Finset.univ : Finset (Occurrence T)) with P q o = e,
            h o • v (P q o) :=
        (Finset.sum_fiberwise Finset.univ (P q) (fun o => h o • v (P q o))).symm
      _ = ∑ e : GlobalEdge q,
          ∑ o ∈ (Finset.univ : Finset (Occurrence T)) with P q o = e,
            h o • v e := by
        apply Finset.sum_congr rfl
        intro e _
        apply Finset.sum_congr rfl
        intro o ho
        rw [(Finset.mem_filter.mp ho).2]
      _ = ∑ e : GlobalEdge q, M q h e • v e := by
        simp only [← Finset.sum_smul, Finset.sum_filter, M]

  ext h
  change (∀ e : GlobalEdge q, M q h e = 0) ↔ h ∈ W
  constructor
  · intro hM
    apply (Submodule.Quotient.mk_eq_zero W).mp
    change π h = 0
    rw [reconstruction]
    simp [hM]
  · intro hW e
    have hz : μ h = 0 := W_le hW
    simpa only [μ_apply, Pi.zero_apply] using congrFun hz e
