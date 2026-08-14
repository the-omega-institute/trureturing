/- GID: D5/S1/Dynamics/UniversalSolenoid
   generality: I
   mirror-B: D5/B/S1/Dynamics/UniversalSolenoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The universal solenoid carries its visible projection and dense real flow. -/

import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Algebra.Group.Basic

namespace D5.S1.Dynamics

/-- The universal one-dimensional solenoid, indexed by the divisibility
system of positive integers. -/
abbrev UniversalSolenoid :=
  {theta : ℕ+ → AddCircle (1 : ℝ) //
    ∀ m n : ℕ+, n.1 • theta ⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ = theta m}

namespace UniversalSolenoid

instance : Zero UniversalSolenoid :=
  ⟨⟨fun _ => 0, by intro m n; simp⟩⟩

instance : Add UniversalSolenoid :=
  ⟨fun theta eta => ⟨theta.1 + eta.1, by
    intro m n
    change n.1 • (theta.1 _ + eta.1 _) = theta.1 m + eta.1 m
    rw [nsmul_add, theta.2 m n, eta.2 m n]⟩⟩

instance : Neg UniversalSolenoid :=
  ⟨fun theta => ⟨-theta.1, by
    intro m n
    change n.1 • (-theta.1 _) = -theta.1 m
    rw [smul_neg, theta.2 m n]⟩⟩

instance : AddCommGroup UniversalSolenoid where
  add := (· + ·)
  add_assoc _ _ _ := Subtype.ext (add_assoc _ _ _)
  zero := 0
  zero_add _ := Subtype.ext (zero_add _)
  add_zero _ := Subtype.ext (add_zero _)
  neg := Neg.neg
  neg_add_cancel _ := Subtype.ext (neg_add_cancel _)
  add_comm _ _ := Subtype.ext (add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : TopologicalSpace UniversalSolenoid :=
  TopologicalSpace.induced Subtype.val inferInstance

instance : ContinuousAdd UniversalSolenoid :=
  ⟨continuous_induced_rng.mpr <|
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd))⟩

instance : ContinuousNeg UniversalSolenoid :=
  ⟨continuous_induced_rng.mpr continuous_subtype_val.neg⟩

instance : IsTopologicalAddGroup UniversalSolenoid where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

/-- The visible phase is the coordinate at index one. -/
def projection : UniversalSolenoid →+ AddCircle (1 : ℝ) where
  toFun theta := theta.1 ⟨1, Nat.zero_lt_one⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem continuous_projection : Continuous projection :=
  show Continuous (fun theta : UniversalSolenoid => theta.1 ⟨1, Nat.zero_lt_one⟩) from
    (continuous_apply (show ℕ+ from ⟨1, Nat.zero_lt_one⟩)).comp continuous_subtype_val

/-- The real flow maps `t` to the compatible family represented by `t / m`
in the coordinate of index `m`. -/
noncomputable def realFlow (t : ℝ) : UniversalSolenoid :=
  ⟨fun m => ((t / m.1 : ℝ) : AddCircle (1 : ℝ)), by
    intro m n
    rw [← AddCircle.coe_nsmul]
    apply congrArg (fun x : ℝ => (x : AddCircle (1 : ℝ)))
    change n.1 • (t / ((m.1 * n.1 : ℕ) : ℝ)) = t / m.1
    rw [nsmul_eq_mul]
    push_cast
    field_simp [Nat.ne_of_gt m.2, Nat.ne_of_gt n.2]⟩

theorem realFlow_zero : realFlow 0 = 0 := by
  apply Subtype.ext
  funext m
  change (((0 : ℝ) / m.1 : ℝ) : AddCircle (1 : ℝ)) = 0
  simp

theorem realFlow_add (s t : ℝ) : realFlow (s + t) = realFlow s + realFlow t := by
  apply Subtype.ext
  funext m
  change (((s + t) / m.1 : ℝ) : AddCircle (1 : ℝ)) =
    ((s / m.1 : ℝ) : AddCircle (1 : ℝ)) + ((t / m.1 : ℝ) : AddCircle (1 : ℝ))
  rw [← AddCircle.coe_add]
  congr 1
  ring

/-- The real flow as an additive homomorphism. -/
noncomputable def realFlowHom : ℝ →+ UniversalSolenoid where
  toFun := realFlow
  map_zero' := realFlow_zero
  map_add' := realFlow_add

theorem continuous_realFlow : Continuous realFlow := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro m
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_id.div_const (m.1 : ℝ))

@[simp] theorem projection_realFlow (t : ℝ) :
    projection (realFlow t) = (t : AddCircle (1 : ℝ)) := by
  change ((t / (1 : ℕ) : ℝ) : AddCircle (1 : ℝ)) = _
  norm_num

theorem projection_surjective : Function.Surjective projection := by
  intro theta
  refine QuotientAddGroup.induction_on theta ?_
  intro t
  exact ⟨realFlow t, projection_realFlow t⟩

private def commonIndex (indices : Finset ℕ+) : ℕ+ :=
  ⟨indices.prod (fun m => m.1), Finset.prod_pos fun m _ => m.2⟩

private theorem divides_commonIndex {indices : Finset ℕ+} {m : ℕ+}
    (hm : m ∈ indices) : m.1 ∣ (commonIndex indices).1 := by
  exact Finset.dvd_prod_of_mem (fun k : ℕ+ => k.1) hm

private theorem exists_realFlow_eq_on_finset (theta : UniversalSolenoid)
    (indices : Finset ℕ+) :
    ∃ t : ℝ, ∀ m ∈ indices, (realFlow t).1 m = theta.1 m := by
  let M := commonIndex indices
  rcases (QuotientAddGroup.mk'_surjective (AddSubgroup.zmultiples (1 : ℝ)))
      (theta.1 M) with ⟨x, hx⟩
  refine ⟨M.1 * x, ?_⟩
  intro m hm
  rcases divides_commonIndex hm with ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra hkzero
    have : k = 0 := Nat.eq_zero_of_not_pos hkzero
    subst k
    simp only [mul_zero] at hk
    exact (Nat.ne_of_gt M.2) hk
  let n : ℕ+ := ⟨k, hkpos⟩
  have hmn : (⟨m.1 * n.1, Nat.mul_pos m.2 n.2⟩ : ℕ+) = M := by
    apply Subtype.ext
    exact hk.symm
  calc
    (realFlow (M.1 * x)).1 m =
        n.1 • (x : AddCircle (1 : ℝ)) := by
      rw [← AddCircle.coe_nsmul]
      apply congrArg (fun y : ℝ => (y : AddCircle (1 : ℝ)))
      change M.1 * x / m.1 = k • x
      rw [nsmul_eq_mul]
      rw [show (M.1 : ℝ) = (m.1 : ℝ) * k by exact_mod_cast hk]
      field_simp [Nat.ne_of_gt m.2]
    _ = n.1 • theta.1 M := congrArg (n.1 • ·) hx
    _ = theta.1 m := by
      rw [← hmn]
      exact theta.2 m n

theorem denseRange_realFlow : DenseRange realFlow := by
  rw [DenseRange]
  intro theta
  rw [mem_closure_iff_nhds']
  intro neighborhood hneighborhood
  change neighborhood ∈ @nhds UniversalSolenoid
    (TopologicalSpace.induced Subtype.val
      (inferInstance : TopologicalSpace (ℕ+ → AddCircle (1 : ℝ)))) theta at hneighborhood
  rw [mem_nhds_induced] at hneighborhood
  rcases hneighborhood with ⟨ambient, hambient, hsubset⟩
  classical
  simp only [nhds_pi, Filter.mem_pi'] at hambient
  rcases hambient with ⟨indices, coordinateSets, htheta, hcoordinateSets⟩
  rcases exists_realFlow_eq_on_finset theta indices with ⟨t, ht⟩
  refine ⟨⟨realFlow t, ⟨t, rfl⟩⟩, hsubset ?_⟩
  apply hcoordinateSets
  intro m hm
  rw [ht m hm]
  exact mem_of_mem_nhds (htheta m)

instance : PreconnectedSpace UniversalSolenoid :=
  DenseRange.preconnectedSpace denseRange_realFlow continuous_realFlow

instance : ConnectedSpace UniversalSolenoid := ⟨⟨0⟩⟩

end UniversalSolenoid

end D5.S1.Dynamics
