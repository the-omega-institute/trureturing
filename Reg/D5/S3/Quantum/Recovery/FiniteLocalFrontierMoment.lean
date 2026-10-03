import D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment
abbrev BT := D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree

abbrev signature : Signature where
  Params := (z : State) × BT z
  State p := p.2.Leaves → Bool
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ p m => failureDefect p.2 m) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def sourceStatement : Prop := ∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2) (z : State) (T : BT z)
    (mark : T.Leaves → Bool)
    (accepted : ∀ l, mark l = true →
      (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s r),
    (0 ≤ failureDefect T mark ∧
    g r * successMass T mark + failureDefect T mark = d z ∧
    (z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      T.expect (fun l => polarMoment (T.endpoint l)) - Z r ≥
        H r - (2*Z r/g r)*failureDefect T mark) ∧
    (∀ cut : T.Cut,
      failureDefect T mark = ∑ v, cut.mass v *
        failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))) ∧
    (∀ cut : T.Cut,
      T.expect (fun l => polarMoment (T.endpoint l)) ≤
        ∑ v, cut.mass v * (polarMoment (cut.branch v).1 +
          (2-‖((cut.branch v).1.1 : Bloch)‖^2-‖((cut.branch v).1.2 : Bloch)‖^2)/2)) ∧
    (∀ (epsilon tau : ℝ), 0 < epsilon → 0 ≤ tau → ∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon ∨
        (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r-(2*Z r/g r)*failureDefect T mark ≤
        tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon) ∧
    (∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon r ∨
        (epsilon r < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark ≤
        frontierMass cut r (epsilon r) (tau r) ∧
      (epsilon r/2)*frontierMass cut r (epsilon r) (tau r) ≤ failureDefect T mark ∧
      H r^3/65536 ≤ failureDefect T mark)) ∧
    4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
    U r-H r^3/(49152*kappa r) < U r ∧
    H r^3/(196608*kappa r) ≤ psi r origin

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2) (z : State) (T : BT z)
    (mark : T.Leaves → Bool)
    (accepted : ∀ l, mark l = true →
      (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s r),
    (0 ≤ R.readout () ⟨z,T⟩ mark ∧
    g r * successMass T mark + failureDefect T mark = d z ∧
    (z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      T.expect (fun l => polarMoment (T.endpoint l)) - Z r ≥
        H r - (2*Z r/g r)*failureDefect T mark) ∧
    (∀ cut : T.Cut,
      failureDefect T mark = ∑ v, cut.mass v *
        failureDefect (cut.branch v).2 (fun l => mark (cut.include v l))) ∧
    (∀ cut : T.Cut,
      T.expect (fun l => polarMoment (T.endpoint l)) ≤
        ∑ v, cut.mass v * (polarMoment (cut.branch v).1 +
          (2-‖((cut.branch v).1.1 : Bloch)‖^2-‖((cut.branch v).1.2 : Bloch)‖^2)/2)) ∧
    (∀ (epsilon tau : ℝ), 0 < epsilon → 0 ≤ tau → ∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon ∨
        (epsilon < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r-(2*Z r/g r)*failureDefect T mark ≤
        tau+frontierMass cut r epsilon tau+8*epsilon+failureDefect T mark/epsilon) ∧
    (∀ cut : T.Cut,
      (∀ v, 0 < cut.mass v → d (cut.branch v).1 = epsilon r ∨
        (epsilon r < d (cut.branch v).1 ∧ (cut.branch v).2.depth = 0)) →
      z = (⟨0,by simp⟩,⟨0,by simp⟩) →
      H r/2-(2*Z r/g r+1/epsilon r)*failureDefect T mark ≤
        frontierMass cut r (epsilon r) (tau r) ∧
      (epsilon r/2)*frontierMass cut r (epsilon r) (tau r) ≤ failureDefect T mark ∧
      H r^3/65536 ≤ failureDefect T mark)) ∧
    4*VInfinity r origin ≤ U r-H r^3/(49152*kappa r) ∧
    U r-H r^3/(49152*kappa r) < U r ∧
    H r^3/(196608*kappa r) ≤ psi r origin

theorem actual_law : arena.Law actual := same_tree_stopped_moment_certificate

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  let zero : Ball := ⟨0,by simp⟩
  let z : State := (zero,zero)
  let T : BT z := .stop z
  have acc : ∀ l : T.Leaves, (fun _ => false) l = true →
      (((T.endpoint l).1 : Bloch),((T.endpoint l).2 : Bloch)) ∈ K_s 1 := by simp
  have hn := (bad 1 (by norm_num) (by norm_num) (by norm_num) z T (fun _ => false) acc).1.1
  change 0 ≤ (-1 : ℝ) at hn
  linarith

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
    let zero : Ball := ⟨0,by simp⟩
    let z : State := (zero,zero)
    let T : BT z := .stop z
    refine ⟨⟨z,T⟩,(fun _ => false),(fun _ => true),?_⟩
    change failureDefect T (fun _ => false) ≠ failureDefect T (fun _ => true)
    norm_num [failureDefect,T,D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.expect,D5.S3.Quantum.Recovery.FiniteLocalBellmanEnvelope.Tree.endpoint,d,defect,z,zero]

register_information_theorem same_tree_stopped_moment_certificate in arena
  readout via (realize signature (fun _ p m => failureDefect p.2 m) (fun e => nomatch e))
  realizes registration
  escape from source ({
    owner := `D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment
    coordinates := #[4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 6 }] })
  escape continues (open)

end Reg.D5.S3.Quantum.Recovery.FiniteLocalFrontierMoment
