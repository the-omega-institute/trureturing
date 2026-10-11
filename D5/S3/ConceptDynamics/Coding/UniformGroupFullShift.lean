/- GID: D5/S3/ConceptDynamics/Coding/UniformGroupFullShift
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/UniformGroupFullShift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform group-ring endpoints have explicit equivariant full-shift coordinates. -/

import D5.S3.ConceptDynamics.Coding.OrderedGroupChainHistories
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.Notation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Coding.UniformGroupFullShift

open scoped BigOperators
open D5.S3.ConceptDynamics.Coding.CountedGroupOverlap
open D5.S3.ConceptDynamics.Coding.CountedGroupChainPaths
open D5.S3.ConceptDynamics.Coding.OrderedGroupChainHistories
open D5.S3.ConceptDynamics.Coding.FiniteWindowTableCriterion
open D5.S3.ConceptDynamics.Coding.EssentialWordRealization
open D5.S3.ConceptDynamics.Coding.FixedBlockRigidity

universe u
variable {H : Type u} [Group H] [Fintype H] [LinearOrder H]

noncomputable def uH : MonoidAlgebra ℕ H := ∑ h : H, MonoidAlgebra.single h 1

theorem uH_coeff (g : H) : (uH (H := H)).coeff g = 1 := by
  classical
  simp [uH, MonoidAlgebra.coeff_sum, Finsupp.sum_apply]

noncomputable def uniformEndpoint (n b : ℕ) : GroupMat H n n := fun _ _ => b • uH (H := H)

theorem uniformEndpoint_coeff (n b : ℕ) (i j : Fin n) (g : H) :
    ((uniformEndpoint (H := H) n b) i j).coeff g = b := by
  classical
  change (b • uH (H := H)).coeff g = b
  change b • (uH (H := H)).coeff g = b
  rw [uH_coeff]
  simp

noncomputable def numberEquiv (n b : ℕ) (i j : Fin n) (g : H) :
    Fin ((uniformEndpoint (H := H) n b i j).coeff g) ≃ Fin b :=
  (Fin.castOrderIso (uniformEndpoint_coeff (H := H) n b i j g)).toEquiv

theorem numberEquiv_roundtrip_heq (n b : ℕ) (i i' j j' : Fin n) (g g' : H)
    (hi : i = i') (hj : j = j') (hg : g = g')
    (x : Fin ((uniformEndpoint (H := H) n b i j).coeff g)) :
    HEq ((numberEquiv (H := H) n b i' j' g').symm
      ((numberEquiv (H := H) n b i j g) x)) x := by
  cases hi
  cases hj
  cases hg
  simp

abbrev FullSymbol (H : Type u) (n b : ℕ) := Fin n × H × Fin b
abbrev FullShift (H : Type u) (n b : ℕ) := ℤ → FullSymbol H n b

def fullShift {n b : ℕ} (x : FullShift H n b) : FullShift H n b := fun i => x (i + 1)

def fullGroupAction {n b : ℕ} (h : H) (x : FullShift H n b) : FullShift H n b :=
  fun i => ((x i).1, (h * (x i).2.1, (x i).2.2))

noncomputable def fullshiftForward (n b : ℕ) (z : History (expandedGraph (uniformEndpoint (H := H) n b))) :
    FullShift H n b :=
  fun i => ((z.val i).1.source, ((z.val i).2,
    numberEquiv (H := H) n b _ _ _ (z.val i).1.number)
    )

noncomputable def fullshiftInverse (n b : ℕ) (x : FullShift H n b) :
    History (expandedGraph (uniformEndpoint (H := H) n b)) :=
  ⟨fun i =>
      (⟨(x i).1, (x (i + 1)).1, (x i).2.1⁻¹ * (x (i + 1)).2.1,
        (numberEquiv (H := H) n b _ _ _).symm (x i).2.2⟩,
        (x i).2.1), by
    intro i
    apply Prod.ext
    · rfl
    · simp [expandedGraph, mul_assoc]⟩

theorem fullshift_inverse_forward (n b : ℕ) (x : FullShift H n b) :
    fullshiftForward (H := H) n b (fullshiftInverse (H := H) n b x) = x := by
  apply funext
  intro i
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [fullshiftForward, fullshiftInverse]
    · simp [fullshiftForward, fullshiftInverse, numberEquiv]

theorem fullshift_forward_inverse
    (n b : ℕ)
    (z : History (expandedGraph (uniformEndpoint (H := H) n b))) :
    fullshiftInverse (H := H) n b (fullshiftForward (H := H) n b z) = z := by
  apply Subtype.ext
  funext i
  cases hzi : z.val i with
  | mk e k =>
    cases e with
    | mk s t g c =>
      have h := z.property i
      rw [hzi] at h
      have hs' := congrArg (fun p : Fin n × H => p.1) h
      have hs'' : t = (z.val (i + 1)).1.source := by
        simpa only [expandedGraph] using hs'
      have hk' := congrArg (fun p : Fin n × H => p.2) h
      have hk'' : k * g = (z.val (i + 1)).2 := by
        simpa only [expandedGraph] using hk'
      have hsrc : (z.val i).1.source = s := congrArg (fun p : Edge (uniformEndpoint (H := H) n b) × H => p.1.source) hzi
      have htgt : (z.val i).1.target = t := congrArg (fun p : Edge (uniformEndpoint (H := H) n b) × H => p.1.target) hzi
      have hlab : (z.val i).1.label = g := congrArg (fun p : Edge (uniformEndpoint (H := H) n b) × H => p.1.label) hzi
      have hnum : (z.val i).1.number.val = c.val := congrArg
        (fun p : Edge (uniformEndpoint (H := H) n b) × H => p.1.number.val) hzi
      have hgroup : (z.val i).2 = k := congrArg
        (fun p : Edge (uniformEndpoint (H := H) n b) × H => p.2) hzi
      dsimp [fullshiftInverse, fullshiftForward]
      apply Prod.ext
      · apply (Edge.mk.injEq _ _ _ _ _ _ _ _).mpr
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact hsrc
        · exact hs''.symm
        · calc
            (z.val i).2⁻¹ * (z.val (i + 1)).2 = (z.val i).2⁻¹ * (k * g) := by rw [hk'']
            _ = g := by rw [hgroup]; simp
        · have hedge := congrArg
              (fun p : Edge (uniformEndpoint (H := H) n b) × H => p.1) hzi
          have hparts := (Edge.mk.injEq _ _ _ _ _ _ _ _).mp hedge
          have hnext : (z.val i).1.target = (z.val (i + 1)).1.source :=
            htgt.trans hs''
          have hlabel : (z.val i).2⁻¹ * (z.val (i + 1)).2 = (z.val i).1.label := by
            calc
              (z.val i).2⁻¹ * (z.val (i + 1)).2 = (z.val i).2⁻¹ * (k * g) := by rw [hk'']
              _ = g := by rw [hgroup]; simp
              _ = (z.val i).1.label := hlab.symm
          exact (numberEquiv_roundtrip_heq (H := H) n b
            (z.val i).1.source (z.val i).1.source
            (z.val i).1.target (z.val (i + 1)).1.source
            (z.val i).1.label ((z.val i).2⁻¹ * (z.val (i + 1)).2)
            rfl hnext hlabel.symm (z.val i).1.number).trans hparts.2.2.2
      · exact hgroup

section Topology
variable [TopologicalSpace H] [IsTopologicalGroup H] [DiscreteTopology H]

noncomputable def fullshiftHomeomorph (n b : ℕ) :
    History (expandedGraph (uniformEndpoint (H := H) n b)) ≃ₜ FullShift H n b where
  toEquiv := { toFun := fullshiftForward (H := H) n b
               invFun := fullshiftInverse (H := H) n b
               left_inv := fullshift_forward_inverse (H := H) n b
               right_inv := fullshift_inverse_forward (H := H) n b }
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (continuous_of_discreteTopology :
      Continuous (fun p : Edge (uniformEndpoint (H := H) n b) × H =>
        (p.1.source, (p.2, Fin.cast (uniformEndpoint_coeff (H := H) n b _ _ _) p.1.number)))).comp
      ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    let hcoord : Continuous (fun x : FullShift H n b => (x i, x (i + 1))) :=
      (continuous_apply i).prodMk (continuous_apply (i + 1))
    exact (continuous_of_discreteTopology :
      Continuous (fun p : FullSymbol H n b × FullSymbol H n b =>
        ((⟨p.1.1, p.2.1, p.1.2.1⁻¹ * p.2.2.1,
          (numberEquiv (H := H) n b _ _ _).symm p.1.2.2⟩,
          p.1.2.1) : Edge (uniformEndpoint (H := H) n b) × H))).comp hcoord

noncomputable def chain_fullshift_homeomorph {n m L : ℕ}
    {b : ℕ} {A : GroupMat H n n} {c : Chain H A (uniformEndpoint (H := H) m b) L} :
    History (expandedGraph A) ≃ₜ FullShift H m b :=
  (chainHistoryHomeomorph c).trans (fullshiftHomeomorph (H := H) m b)

theorem chain_fullshift_forward_window {n m L : ℕ}
    {b : ℕ} {A : GroupMat H n n} {c : Chain H A (uniformEndpoint (H := H) m b) L}
    (z w : History (expandedGraph A)) (i : ℤ)
    (h : ∀ t : ℤ, i ≤ t → t ≤ i + (L : ℤ) → z.val t = w.val t) :
    (chain_fullshift_homeomorph (c := c) z) i = (chain_fullshift_homeomorph (c := c) w) i := by
  have hz := chain_forward_window c z w i h
  change fullshiftForward (H := H) m b (chainHistoryHomeomorph c z) i =
    fullshiftForward (H := H) m b (chainHistoryHomeomorph c w) i
  exact congrArg (fun p : Edge (uniformEndpoint (H := H) m b) × H =>
    (p.1.source, (p.2, numberEquiv (H := H) m b _ _ _ p.1.number))) hz

theorem chain_fullshift_inverse_window {n m L : ℕ}
    {b : ℕ} {A : GroupMat H n n} {c : Chain H A (uniformEndpoint (H := H) m b) L}
    (z w : FullShift H m b) (i : ℤ)
    (h : ∀ t : ℤ, i - (L : ℤ) ≤ t → t ≤ i + 1 → z t = w t) :
    ((chain_fullshift_homeomorph (c := c)).symm z).val i =
      ((chain_fullshift_homeomorph (c := c)).symm w).val i := by
  have hin : ∀ t : ℤ, i - (L : ℤ) ≤ t → t ≤ i →
      ((fullshiftHomeomorph (H := H) m b).symm z).val t =
        ((fullshiftHomeomorph (H := H) m b).symm w).val t := by
    intro t ht0 ht1
    have heq : (fullshiftInverse (H := H) m b z).val t =
        (fullshiftInverse (H := H) m b w).val t := by
      have hp : (z t, z (t + 1)) = (w t, w (t + 1)) := by
        exact Prod.ext (h t (by omega) (by omega))
          (h (t + 1) (by omega) (by omega))
      exact congrArg (fun p : FullSymbol H m b × FullSymbol H m b =>
        ((⟨p.1.1, p.2.1, p.1.2.1⁻¹ * p.2.2.1,
          (numberEquiv (H := H) m b _ _ _).symm p.1.2.2⟩ :
            Edge (uniformEndpoint (H := H) m b)), p.1.2.1))
        hp
    simpa [fullshiftHomeomorph] using heq
  exact chain_inverse_window c _ _ i (by
    intro t ht0 ht1
    exact hin t ht0 ht1)

theorem chain_fullshift_time (n m L : ℕ)
    {b : ℕ} {A : GroupMat H n n} {c : Chain H A (uniformEndpoint (H := H) m b) L}
    (z : History (expandedGraph A)) :
    chain_fullshift_homeomorph (c := c) (FiniteWindowTableCriterion.shift _ z) =
      fullShift (chain_fullshift_homeomorph (c := c) z) := by
  exact congrArg (fullshiftForward (H := H) m b) (chain_history_time c z)

theorem chain_fullshift_group (n m L : ℕ)
    {b : ℕ} {A : GroupMat H n n} {c : Chain H A (uniformEndpoint (H := H) m b) L}
    (h : H) (z : History (expandedGraph A)) :
    chain_fullshift_homeomorph (c := c) (groupHistory _ h z) =
      fullGroupAction h (chain_fullshift_homeomorph (c := c) z) := by
  exact congrArg (fullshiftForward (H := H) m b) ((chain_history_group c h).1 z)

/-- Both directions of the actual endpoint coordinates, at their exact windows. -/
structure CoordinateLaws {n : ℕ} (A : GroupMat H n n) (m b L : ℕ)
    (F : History (expandedGraph A) ≃ₜ FullShift H m b) : Prop where
  time : ∀ z, F (FiniteWindowTableCriterion.shift _ z) = fullShift (F z)
  inverseTime : ∀ x, F.symm (fullShift x) = FiniteWindowTableCriterion.shift _ (F.symm x)
  group : ∀ h z, F (groupHistory _ h z) = fullGroupAction h (F z)
  inverseGroup : ∀ h x, F.symm (fullGroupAction h x) = groupHistory _ h (F.symm x)
  forwardWindow : ∀ z w i, (∀ t : ℤ, i ≤ t → t ≤ i + (L : ℤ) → z.val t = w.val t) →
    F z i = F w i
  inverseWindow : ∀ z w i, (∀ t : ℤ, i - (L : ℤ) ≤ t → t ≤ i + 1 → z t = w t) →
    (F.symm z).val i = (F.symm w).val i

theorem chain_coordinate_laws {n m L b : ℕ} {A : GroupMat H n n}
    (c : Chain H A (uniformEndpoint (H := H) m b) L) :
    CoordinateLaws A m b L (chain_fullshift_homeomorph (c := c)) := by
  constructor
  · exact chain_fullshift_time n m L
  · intro x
    apply (chain_fullshift_homeomorph (c := c)).injective
    simpa using (chain_fullshift_time n m L (c := c)
      ((chain_fullshift_homeomorph (c := c)).symm x)).symm
  · exact chain_fullshift_group n m L
  · intro h x
    apply (chain_fullshift_homeomorph (c := c)).injective
    simpa using (chain_fullshift_group n m L (c := c) h
      ((chain_fullshift_homeomorph (c := c)).symm x)).symm
  · exact chain_fullshift_forward_window
  · exact chain_fullshift_inverse_window

end Topology

/-- The superdiagonal entries in the consecutive literal Jordan blocks. -/
def jordanActive : List ℕ → ℕ → ℕ → Bool
  | [], _, _ => false
  | a :: as, i, j => if i < a then decide (i + 1 = j ∧ j < a)
      else if a ≤ j then jordanActive as (i - a) (j - a) else false

/-- Natural coefficients of the literal q³nJu + q(q1-u)Nparts. -/
noncomputable def partitionMatrix (n : ℕ) (parts : List ℕ) : GroupMat H n n :=
  fun i j => MonoidAlgebra.ofCoeff (Finsupp.equivFunOnFinite.symm fun g =>
    if jordanActive parts i.val j.val then
      if g = 1 then Fintype.card H ^ 3 * n + Fintype.card H * (Fintype.card H - 1)
      else Fintype.card H ^ 3 * n - Fintype.card H
    else Fintype.card H ^ 3 * n)

private theorem partition_coeff (n : ℕ) (parts : List ℕ) (i j : Fin n) (g : H) :
    (partitionMatrix (H := H) n parts i j).coeff g =
      if jordanActive parts i.val j.val then
        if g = 1 then Fintype.card H ^ 3 * n + Fintype.card H * (Fintype.card H - 1)
        else Fintype.card H ^ 3 * n - Fintype.card H
      else Fintype.card H ^ 3 * n := by
  classical
  simp [partitionMatrix]

private theorem jordan_ones (n i j : ℕ) : jordanActive (List.replicate n 1) i j = false := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, jordanActive]
    split
    · simp only [decide_eq_false_iff_not]
      omega
    · split <;> simp_all

private theorem partition_endpoint (n : ℕ) :
    partitionMatrix (H := H) n (List.replicate n 1) =
      uniformEndpoint (H := H) n (Fintype.card H ^ 3 * n) := by
  ext i j g
  rw [partition_coeff, jordan_ones, uniformEndpoint_coeff]
  rfl

private theorem partition_positive {n : ℕ} (hn : 0 < n)
    (hq : 2 ≤ Fintype.card H)
    (parts : List ℕ) (i j : Fin n) (g : H) :
    0 < (partitionMatrix (H := H) n parts i j).coeff g := by
  let q := Fintype.card H
  have hqpos : 0 < q := by dsimp [q]; omega
  have hq2 : q < q ^ 2 := by dsimp [q]; nlinarith
  have hq3 : q ^ 2 ≤ q ^ 3 := by
    calc
      q ^ 2 ≤ q ^ 2 * q := Nat.le_mul_of_pos_right _ hqpos
      _ = q ^ 3 := by ring
  have hb : q < q ^ 3 * n :=
    lt_of_lt_of_le (lt_of_lt_of_le hq2 hq3) (Nat.le_mul_of_pos_right _ hn)
  rw [partition_coeff]
  split
  · split
    · exact lt_of_lt_of_le (Nat.mul_pos (pow_pos hqpos _) hn) (Nat.le_add_right _ _)
    · exact Nat.sub_pos_of_lt hb
  · exact Nat.mul_pos (pow_pos hqpos _) hn

theorem positive_essential {n : ℕ} (A : GroupMat H n n)
    (hp : ∀ i, 0 < (A i i).coeff 1) : Essential (expandedGraph A) := by
  classical
  letI := Classical.decEq H
  constructor
  · intro v
    exact ⟨(⟨v.1, v.1, 1, ⟨0, hp _⟩⟩, v.2), rfl⟩
  · intro v
    exact ⟨(⟨v.1, v.1, 1, ⟨0, hp _⟩⟩, v.2), by simp [expandedGraph]⟩

/-- The block diagonal of literal nilpotent Jordan blocks, padded by zeros.
Each block has ones precisely on its upper superdiagonal. -/
def jordanBlocks : List ℕ → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | a :: parts, i, j =>
      if i < a ∧ j < a then if i + 1 = j then 1 else 0
      else if a ≤ i ∧ a ≤ j then jordanBlocks parts (i - a) (j - a) else 0

private theorem jordan_correspondence (parts : List ℕ) (i j : ℕ) :
    (if jordanActive parts i j then 1 else 0 : ℕ) = jordanBlocks parts i j := by
  induction parts generalizing i j with
  | nil => rfl
  | cons a parts ih =>
    by_cases hi : i < a
    · by_cases hj : j < a
      · simp [jordanActive, jordanBlocks, hi, hj]
      · simp [jordanActive, jordanBlocks, hi, hj]
    · have hia : a ≤ i := by omega
      by_cases hj : a ≤ j
      · simp [jordanActive, jordanBlocks, hi, hia, hj, not_lt.mpr hj, ih]
      · simp [jordanActive, jordanBlocks, hi, hia, hj]

/-- Coefficients in the integer group ring, with the original signed perturbation. -/
noncomputable def partitionSource (n : ℕ) (parts : List ℕ) :
    Matrix (Fin n) (Fin n) (MonoidAlgebra ℤ H) :=
  fun i j => (Fintype.card H ^ 3 * n : ℕ) •
      (∑ g : H, MonoidAlgebra.single g (1 : ℤ)) +
    jordanBlocks parts i.val j.val • ((Fintype.card H : ℕ) •
        ((Fintype.card H : ℕ) • (1 : MonoidAlgebra ℤ H) -
          ∑ g : H, MonoidAlgebra.single g (1 : ℤ)))

private theorem partition_source_coeff {n : ℕ} (hn : 0 < n)
    (hq : 2 ≤ Fintype.card H) (parts : List ℕ) (i j : Fin n) (g : H) :
    ((partitionMatrix (H := H) n parts i j).coeff g : ℤ) =
      (partitionSource (H := H) n parts i j).coeff g := by
  have hb : Fintype.card H ≤ Fintype.card H ^ 3 * n := by
    have hqpos : 0 < Fintype.card H := by omega
    have hq2 : Fintype.card H ≤ Fintype.card H ^ 2 := by nlinarith
    calc
      Fintype.card H ≤ Fintype.card H ^ 2 := hq2
      _ ≤ Fintype.card H ^ 2 * Fintype.card H := Nat.le_mul_of_pos_right _ hqpos
      _ = Fintype.card H ^ 3 := by ring
      _ ≤ Fintype.card H ^ 3 * n := Nat.le_mul_of_pos_right _ hn
  classical
  have hz (g : H) : (∑ h : H, MonoidAlgebra.single h (1 : ℤ)).coeff g = 1 := by
    simp [MonoidAlgebra.coeff_sum, Finsupp.sum_apply]
  rw [partition_coeff]
  unfold partitionSource
  rw [← jordan_correspondence]
  by_cases ha : jordanActive parts i.val j.val
  · simp only [ha, if_true, one_nsmul, MonoidAlgebra.coeff_add,
      MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_smul,
      Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, hz,
      MonoidAlgebra.one_def, MonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hg : g = 1
    · simp [hg, Nat.cast_sub (by omega : 1 ≤ Fintype.card H)]
    · simp [hg, eq_comm, Nat.cast_sub hb, sub_eq_add_neg]
  · simp only [if_neg ha, zero_nsmul, add_zero]
    change ((Fintype.card H ^ 3 * n : ℕ) : ℤ) =
      (Fintype.card H ^ 3 * n : ℕ) • (∑ h : H, MonoidAlgebra.single h (1 : ℤ)).coeff g
    rw [hz]
    simp

private theorem partition_essential {n : ℕ} (hn : 0 < n)
    (hq : 2 ≤ Fintype.card H) (parts : List ℕ) :
    Essential (expandedGraph (partitionMatrix (H := H) n parts)) :=
  positive_essential _ (fun i => partition_positive hn hq parts i i 1)

section PartitionCoordinates
variable [TopologicalSpace H] [DiscreteTopology H] [IsTopologicalGroup H]

/-- The chain premise is supplied; the literal endpoint is discharged here. -/
noncomputable def partitionFullShift {n L : ℕ} (parts : List ℕ)
    (c : Chain H (partitionMatrix (H := H) n parts)
      (partitionMatrix (H := H) n (List.replicate n 1)) L) :
    History (expandedGraph (partitionMatrix (H := H) n parts)) ≃ₜ
      FullShift H n (Fintype.card H ^ 3 * n) := by
  rw [partition_endpoint (H := H) n] at c
  have c' : Chain H (partitionMatrix (H := H) n parts)
      (uniformEndpoint (H := H) n (Fintype.card H ^ 3 * n)) L := c
  exact chain_fullshift_homeomorph (c := c')
/-- Literal source coefficients, essentiality, alphabet and both window laws.
The sole chain premise is the supplied source chain. -/
theorem partition_coordinates {n L : ℕ} (hn : 0 < n) (hq : 2 ≤ Fintype.card H)
    (parts : List ℕ)
    (c : Chain H (partitionMatrix (H := H) n parts)
      (partitionMatrix (H := H) n (List.replicate n 1)) L) :
    (∀ i j g, ((partitionMatrix (H := H) n parts i j).coeff g : ℤ) =
      (partitionSource (H := H) n parts i j).coeff g) ∧
    (∀ i j g, 0 < (partitionMatrix (H := H) n parts i j).coeff g) ∧
    Essential (expandedGraph (partitionMatrix (H := H) n parts)) ∧
    Fintype.card (FullSymbol H n (Fintype.card H ^ 3 * n)) = Fintype.card H ^ 4 * n ^ 2 ∧
    CoordinateLaws (partitionMatrix (H := H) n parts) n (Fintype.card H ^ 3 * n) L
      (partitionFullShift parts c) := by
  refine ⟨partition_source_coeff hn hq parts, partition_positive hn hq parts,
    partition_essential hn hq parts, ?_, ?_⟩
  · simp only [FullSymbol, Fintype.card_prod, Fintype.card_fin]
    ring
  · unfold partitionFullShift
    exact chain_coordinate_laws _

end PartitionCoordinates



end D5.S3.ConceptDynamics.Coding.UniformGroupFullShift
