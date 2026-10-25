import D5.S3.Geometry.Hyperideal.LengthGramSideTrace
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open scoped BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace

namespace CFMPOriginalBoundaryEdge229Transient

-- Temporary exact application of the original twenty exterior triangle tuples.
-- No new retained declaration or geometric cancellation is asserted.
def labels : Fin 20 → Fin 3 → Fin 4 × Fin 4 :=
  ![![(0, 1), (0, 2), (0, 3)], ![(1, 0), (1, 2), (1, 3)], ![(2, 0), (2, 1), (2, 3)], ![(3, 0), (3, 1), (3, 2)], ![(1, 2), (2, 1), (2, 3)], ![(1, 2), (2, 3), (3, 2)], ![(1, 2), (3, 2), (3, 1)], ![(1, 2), (3, 1), (1, 3)], ![(0, 2), (2, 0), (2, 3)], ![(0, 2), (2, 3), (3, 2)], ![(0, 2), (3, 2), (3, 0)], ![(0, 2), (3, 0), (0, 3)], ![(0, 1), (1, 0), (1, 3)], ![(0, 1), (1, 3), (3, 1)], ![(0, 1), (3, 1), (3, 0)], ![(0, 1), (3, 0), (0, 3)], ![(0, 1), (1, 0), (1, 2)], ![(0, 1), (1, 2), (2, 1)], ![(0, 1), (2, 1), (2, 0)], ![(0, 1), (2, 0), (0, 2)]]

theorem labels_realize (l : Fin 6 → ℝ) (n : Fin 20) (j : Fin 3) :
    endpoint l (labels n j).1 (labels n j).2 = vertices l n j.succ := by
  fin_cases n <;> fin_cases j <;> rfl

theorem labels_distinct : ∀ n : Fin 20, ∀ j : Fin 3,
    (labels n j).1 ≠ (labels n j).2 := by decide

def startIndex : Fin 3 → Fin 3 := ![0, 0, 1]
def endIndex : Fin 3 → Fin 3 := ![2, 1, 2]

def startVertex (l : Fin 6 → ℝ) (o : Fin 20 × Fin 3) : V :=
  vertices l o.1 (startIndex o.2).succ

def endVertex (l : Fin 6 → ℝ) (o : Fin 20 × Fin 3) : V :=
  vertices l o.1 (endIndex o.2).succ

def pairs : Fin 30 → (Fin 20 × Fin 3) × (Fin 20 × Fin 3) :=
  ![((0, 1), (19, 0)), ((0, 0), (15, 0)), ((12, 1), (16, 1)), ((16, 0), (17, 1)), ((12, 0), (13, 1)), ((18, 0), (19, 1)), ((17, 0), (18, 1)), ((14, 0), (15, 1)), ((13, 0), (14, 1)), ((0, 2), (11, 0)), ((8, 1), (19, 2)), ((8, 0), (9, 1)), ((10, 0), (11, 1)), ((9, 0), (10, 1)), ((11, 2), (15, 2)), ((1, 1), (16, 2)), ((1, 0), (12, 2)), ((1, 2), (7, 0)), ((4, 1), (17, 2)), ((4, 0), (5, 1)), ((6, 0), (7, 1)), ((5, 0), (6, 1)), ((7, 2), (13, 2)), ((2, 1), (18, 2)), ((2, 0), (8, 2)), ((2, 2), (4, 2)), ((5, 2), (9, 2)), ((3, 1), (14, 2)), ((3, 0), (10, 2)), ((3, 2), (6, 2))]

def swapped : Fin 30 → Bool :=
  ![false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, true, true, false, false, false, true, true, true]

def occurrence (p : Fin 30 × Bool) : Fin 20 × Fin 3 :=
  if p.2 then (pairs p.1).2 else (pairs p.1).1

theorem occurrence_bijective : Function.Bijective occurrence := by decide

theorem paired_endpoints (l : Fin 6 → ℝ) (p : Fin 30) :
    startVertex l (pairs p).1 =
      (if swapped p then endVertex l (pairs p).2 else startVertex l (pairs p).2) ∧
    endVertex l (pairs p).1 =
      (if swapped p then startVertex l (pairs p).2 else endVertex l (pairs p).2) := by
  let f : Fin 4 × Fin 4 → V := fun a => endpoint l a.1 a.2
  have hs (o : Fin 20 × Fin 3) :
      startVertex l o = f (labels o.1 (startIndex o.2)) :=
    (labels_realize l o.1 (startIndex o.2)).symm
  have he (o : Fin 20 × Fin 3) :
      endVertex l o = f (labels o.1 (endIndex o.2)) :=
    (labels_realize l o.1 (endIndex o.2)).symm
  have hp :
      labels (pairs p).1.1 (startIndex (pairs p).1.2) =
        (if swapped p then labels (pairs p).2.1 (endIndex (pairs p).2.2)
         else labels (pairs p).2.1 (startIndex (pairs p).2.2)) ∧
      labels (pairs p).1.1 (endIndex (pairs p).1.2) =
        (if swapped p then labels (pairs p).2.1 (startIndex (pairs p).2.2)
         else labels (pairs p).2.1 (endIndex (pairs p).2.2)) := by
    fin_cases p <;> exact ⟨rfl, rfl⟩
  cases hswap : swapped p
  · simp [hswap] at hp ⊢
    exact ⟨(hs _).trans ((congrArg f hp.1).trans (hs _).symm),
      (he _).trans ((congrArg f hp.2).trans (he _).symm)⟩
  · simp [hswap] at hp ⊢
    exact ⟨(hs _).trans ((congrArg f hp.1).trans (he _).symm),
      (he _).trans ((congrArg f hp.2).trans (hs _).symm)⟩

def diagonal : Fin 12 → Fin 30 := ![3, 4, 5, 6, 7, 8, 11, 12, 13, 19, 20, 21]
def truncation : Fin 12 → Fin 30 := ![0, 1, 9, 15, 16, 17, 23, 24, 25, 27, 28, 29]
def physical : Fin 6 → Fin 30 := ![2, 10, 14, 26, 22, 18]

def classified : Fin 12 ⊕ (Fin 12 ⊕ Fin 6) → Fin 30
  | Sum.inl d => diagonal d
  | Sum.inr (Sum.inl t) => truncation t
  | Sum.inr (Sum.inr q) => physical q

theorem classified_bijective : Function.Bijective classified := by decide

theorem diagonal_same_facet (d : Fin 12) :
    facet (pairs (diagonal d)).1.1 = facet (pairs (diagonal d)).2.1 := by
  fin_cases d <;> decide

def lengthLabels : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (2,3), (1,3), (1,2)]

def sideLabels : Fin 6 → Fin 4 × Fin 4 :=
  ![(2,3), (1,3), (1,2), (0,1), (0,2), (0,3)]

theorem physical_supports (q : Fin 6) :
    facet (pairs (physical q)).1.1 = Sum.inl (sideLabels q).1 ∧
    facet (pairs (physical q)).2.1 = Sum.inl (sideLabels q).2 := by
  fin_cases q <;> decide

def physicalReversed : Fin 6 → Bool := ![false, false, true, false, true, false]

theorem physical_endpoints (l : Fin 6 → ℝ) (q : Fin 6) :
    startVertex l (pairs (physical q)).1 =
      (if physicalReversed q then endpoint l (lengthLabels q).2 (lengthLabels q).1
       else endpoint l (lengthLabels q).1 (lengthLabels q).2) ∧
    endVertex l (pairs (physical q)).1 =
      (if physicalReversed q then endpoint l (lengthLabels q).1 (lengthLabels q).2
       else endpoint l (lengthLabels q).2 (lengthLabels q).1) := by
  fin_cases q <;> exact ⟨rfl, rfl⟩

theorem truncation_supports (t : Fin 12) :
    (∃ i k : Fin 4, i ≠ k ∧
      facet (pairs (truncation t)).1.1 = Sum.inr i ∧
      facet (pairs (truncation t)).2.1 = Sum.inl k) ∨
    (∃ i k : Fin 4, i ≠ k ∧
      facet (pairs (truncation t)).2.1 = Sum.inr i ∧
      facet (pairs (truncation t)).1.1 = Sum.inl k) := by
  fin_cases t <;> decide

theorem sum_pairs {A : Type*} [AddCommMonoid A] (F : Fin 20 → Fin 3 → A) :
    ∑ n, ∑ e, F n e =
      ∑ p : Fin 30, (F (pairs p).1.1 (pairs p).1.2 +
        F (pairs p).2.1 (pairs p).2.2) := by
  let e := Equiv.ofBijective occurrence occurrence_bijective
  calc
    _ = ∑ t : Fin 20 × Fin 3, F t.1 t.2 := (Fintype.sum_prod_type _).symm
    _ = ∑ t : Fin 30 × Bool, F (e t).1 (e t).2 := (Equiv.sum_comp e _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      simp [e, occurrence, Fintype.sum_bool, add_comm]

theorem sum_classified {A : Type*} [AddCommMonoid A] (H : Fin 30 → A) :
    ∑ p : Fin 30, H p =
      (∑ d : Fin 12, H (diagonal d)) +
      ((∑ t : Fin 12, H (truncation t)) + (∑ q : Fin 6, H (physical q))) := by
  let e := Equiv.ofBijective classified classified_bijective
  calc
    _ = ∑ x : Fin 12 ⊕ (Fin 12 ⊕ Fin 6), H (e x) := (Equiv.sum_comp e H).symm
    _ = _ := by
      change (∑ x : Fin 12 ⊕ (Fin 12 ⊕ Fin 6), H (classified x)) = _
      simp only [Fintype.sum_sum_type, classified]

-- Pure finite regrouping: the geometric cancellation hypotheses remain obligations.
theorem boundary_sum_reduce (F : Fin 20 → Fin 3 → ℝ) (C : Fin 6 → ℝ)
    (hdiag : ∀ d : Fin 12,
      F (pairs (diagonal d)).1.1 (pairs (diagonal d)).1.2 +
        F (pairs (diagonal d)).2.1 (pairs (diagonal d)).2.2 = 0)
    (htrunc : ∀ t : Fin 12,
      F (pairs (truncation t)).1.1 (pairs (truncation t)).1.2 +
        F (pairs (truncation t)).2.1 (pairs (truncation t)).2.2 = 0)
    (hphysical : ∀ q : Fin 6,
      F (pairs (physical q)).1.1 (pairs (physical q)).1.2 +
        F (pairs (physical q)).2.1 (pairs (physical q)).2.2 = C q) :
    ∑ n : Fin 20, ∑ e : Fin 3, F n e = ∑ q : Fin 6, C q := by
  rw [sum_pairs, sum_classified]
  simp_rw [hdiag, htrunc, hphysical]
  simp

def otherIndex : Fin 3 → Fin 3 := ![1, 2, 0]
def startLabel (o : Fin 20 × Fin 3) : Fin 4 × Fin 4 := labels o.1 (startIndex o.2)
def endLabel (o : Fin 20 × Fin 3) : Fin 4 × Fin 4 := labels o.1 (endIndex o.2)
def otherLabel (o : Fin 20 × Fin 3) : Fin 4 × Fin 4 := labels o.1 (otherIndex o.2)

-- The strict third-vertex sign follows from the existing endpoint support theorem.
theorem adjacent_support_incidence : ∀ p : Fin 30,
    facet (pairs p).1.1 ≠ facet (pairs p).2.1 →
    (incident (facet (pairs p).2.1) (startLabel (pairs p).1).1 (startLabel (pairs p).1).2 ∧
     incident (facet (pairs p).2.1) (endLabel (pairs p).1).1 (endLabel (pairs p).1).2 ∧
     ¬incident (facet (pairs p).2.1) (otherLabel (pairs p).1).1 (otherLabel (pairs p).1).2) ∧
    (incident (facet (pairs p).1.1) (startLabel (pairs p).2).1 (startLabel (pairs p).2).2 ∧
     incident (facet (pairs p).1.1) (endLabel (pairs p).2).1 (endLabel (pairs p).2).2 ∧
     ¬incident (facet (pairs p).1.1) (otherLabel (pairs p).2).1 (otherLabel (pairs p).2).2) := by
  decide

end CFMPOriginalBoundaryEdge229Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPOriginalBoundaryEdge229Transient.labels_realize,
      ``CFMPOriginalBoundaryEdge229Transient.labels_distinct,
      ``CFMPOriginalBoundaryEdge229Transient.occurrence_bijective,
      ``CFMPOriginalBoundaryEdge229Transient.paired_endpoints,
      ``CFMPOriginalBoundaryEdge229Transient.classified_bijective,
      ``CFMPOriginalBoundaryEdge229Transient.diagonal_same_facet,
      ``CFMPOriginalBoundaryEdge229Transient.physical_supports,
      ``CFMPOriginalBoundaryEdge229Transient.physical_endpoints,
      ``CFMPOriginalBoundaryEdge229Transient.truncation_supports,
      ``CFMPOriginalBoundaryEdge229Transient.adjacent_support_incidence,
      ``CFMPOriginalBoundaryEdge229Transient.sum_pairs,
      ``CFMPOriginalBoundaryEdge229Transient.sum_classified,
      ``CFMPOriginalBoundaryEdge229Transient.boundary_sum_reduce] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP229 target absent from checked environment: {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP229 disallowed axiom {ax} in {name}"
    Lean.logInfo m!"CFMP229 CHECKED {name} axioms={axioms}"

