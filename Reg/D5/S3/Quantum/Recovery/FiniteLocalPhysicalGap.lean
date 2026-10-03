import D5.S3.Quantum.Recovery.FiniteLocalPhysicalGap
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
open D5.S3.Quantum.Recovery.FiniteLocalSharedLabelRecovery
open D5.S3.Quantum.Recovery.FiniteLocalPhysicalGap
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalPhysicalGap

abbrev signature : Signature where
  Params := ℝ
  State _ := D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.State
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ r z => VInfinity r z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2),
    (∀ (Y : Type) (P : ActualProtocol Y) (accept : Y → Prop)
      (feedback : Y → Matrix.unitaryGroup (Fin 5) ℂ) (p : ℝ), 0 ≤ p →
      (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
        acceptedMap P r accept feedback X = (p : ℂ) • X) →
      p ≤ 4*VInfinity r origin ∧ p ≤ U r-H r^3/(49152*kappa r) ∧ p ≤ 1 ∧
      (∀ q : ℝ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
          acceptedMap P r accept feedback X = (q : ℂ) • X) ↔
        (∀ (F : Type) [Fintype F] [DecidableEq F]
          (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
          referenceAcceptedMap P r accept feedback F X = (q : ℂ) • X))) ∧
    (0 ∈ physicalSuccess r ∧ BddAbove (physicalSuccess r) ∧
      IsLUB (physicalSuccess r) (eta_fin r)) ∧
    (0 ≤ eta_fin r ∧ eta_fin r ≤ 4*VInfinity r origin ∧
      eta_fin r ≤ U r-H r^3/(49152*kappa r) ∧
      4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
      U r-H r^3/(49152*kappa r) < U r) ∧
    (∀ z, VInfinity r z = treeValue r z) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r) ∧
    H r^3/(196608*kappa r) ≤ psi r origin

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2),
    (∀ (Y : Type) (P : ActualProtocol Y) (accept : Y → Prop)
      (feedback : Y → Matrix.unitaryGroup (Fin 5) ℂ) (p : ℝ), 0 ≤ p →
      (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
        acceptedMap P r accept feedback X = (p : ℂ) • X) →
      p ≤ 4*VInfinity r origin ∧ p ≤ U r-H r^3/(49152*kappa r) ∧ p ≤ 1 ∧
      (∀ q : ℝ,
        (∀ X : Matrix (Fin 5) (Fin 5) ℂ,
          acceptedMap P r accept feedback X = (q : ℂ) • X) ↔
        (∀ (F : Type) [Fintype F] [DecidableEq F]
          (X : Matrix (F × Fin 5) (F × Fin 5) ℂ),
          referenceAcceptedMap P r accept feedback F X = (q : ℂ) • X))) ∧
    (0 ∈ physicalSuccess r ∧ BddAbove (physicalSuccess r) ∧
      IsLUB (physicalSuccess r) (eta_fin r)) ∧
    (0 ≤ eta_fin r ∧ eta_fin r ≤ 4*VInfinity r origin ∧
      eta_fin r ≤ U r-H r^3/(49152*kappa r) ∧
      4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
      U r-H r^3/(49152*kappa r) < U r) ∧
    (∀ z, R.readout () r z = treeValue r z) ∧
    SeparatelyConcave (VInfinity r) ∧
    (∀ z, 0 ≤ VInfinity r z ∧ VInfinity r z ≤ fSEP r z ∧
      0 ≤ psi r z ∧ psi r z ≤ fSEP r z) ∧
    (∀ z, ((z.1 : Bloch),(z.2 : Bloch)) ∈ K_s r →
      VInfinity r z = h r ∧ psi r z = 0) ∧
    (∀ n : Ball, ‖(n : Bloch)‖ = 1 → VInfinity r (n,n) = 0 ∧ psi r (n,n) = 0) ∧
    SeparatelyConvex (psi r) ∧
    H r^3/(196608*kappa r) ≤ psi r origin

theorem actual_law : arena.Law actual := full_source_finite_recovery_gap

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  have he := (bad 1 (by norm_num) (by norm_num) (by norm_num)).2.2.2.1 origin
  have hv := (source_bellman_finite_tree_identity 1 (by norm_num)
    (by norm_num) (by norm_num)).2.2.2.2.2.1 origin
  change -1 = treeValue 1 origin at he
  rw [← hv.1] at he
  linarith [hv.2.1]

def registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    obtain ⟨⟨a,b⟩,hab⟩ := (all_r_flat_geometry 1 (by norm_num)
      (by norm_num) (by norm_num)).2.2.2.1
    let x : Ball := ⟨a,by
      simpa only [Metric.mem_closedBall,dist_zero_right,hab.1] using (le_rfl : (1 : ℝ) ≤ 1)⟩
    let y : Ball := ⟨b,by
      simpa only [Metric.mem_closedBall,dist_zero_right,hab.2.1] using (le_rfl : (1 : ℝ) ≤ 1)⟩
    have ha := source_bellman_finite_tree_identity 1 (by norm_num) (by norm_num) (by norm_num)
    have hflat := ha.2.2.2.2.2.2.2.2.2.1 (x,y) hab
    have hdiag := ha.2.2.2.2.2.2.2.2.2.2.1 x hab.1
    refine ⟨(1 : ℝ),(x,y),(x,x),?_⟩
    change VInfinity 1 (x,y) ≠ VInfinity 1 (x,x)
    rw [hflat.1,hdiag.1]
    unfold h kappa
    positivity

register_information_theorem full_source_finite_recovery_gap in arena
  readout via (realize signature (fun _ r z => VInfinity r z) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.FiniteLocalPhysicalGap
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","arg","arg","arg",
        "fn","arg","body","fn","arg"]
      stateBinder := 4 }] })
  escape continues (open)

end Reg.D5.S3.Quantum.Recovery.FiniteLocalPhysicalGap
