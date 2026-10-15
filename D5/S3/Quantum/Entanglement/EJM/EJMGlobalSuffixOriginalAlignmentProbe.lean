/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentProbe
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentProbe
   mirror-E: none(waiver:actual-original-subtree-kernel-probe)
   anchors: []
   utility: none
   digest: An exact 17-node actual suffix is transported to its original fuel-indexed DAG nodes without changing any cache or partial event. -/

/- Prepared diagnostic; this source is not accepted until canonical kernel
compilation succeeds. It handles the already accepted first 17-node subtree,
not the complete 2497 suffix and not the full original global refutation. -/

import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock0

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentProbe
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 6 ∧ left = 2480 ∧ right = 94965) ∨
  (fuel = 5 ∧ left = 2481 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 2482 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 2483 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 2484 ∧ right = 93663) ∨
  (fuel = 4 ∧ left = 2485 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2486 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2487 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2488 ∧ right = 93169) ∨
  (fuel = 3 ∧ left = 2489 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2490 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2491 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2492 ∧ right = 92687) ∨
  (fuel = 2 ∧ left = 2493 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2494 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2495 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2496 ∧ right = 0)

private theorem alignment (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related (fuel + 1) left right) :
    StepRelated (Related fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 5 := by omega
    subst fuel left right
    have leftShape : pilotNodes 6 2480 = .split (15 : Fin 20) ![2481,2482,2483,2484] := by
      change (.split (15 : Fin 20)
        (fun a => ⟨(5463707142665775 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl
    have rightShape : EJMGlobalDAGData.nodes 6 94965 =
        .split (15 : Fin 20) ![2894,2894,2894,93663] := by
      change (.split (15 : Fin 20)
        (fun a => ⟨(EJMGlobalDAGData.shapeWord 2804 /
          2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
          Nat.mod_lt _ (by decide)⟩) :
          Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, rightShape]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 2484 = .split (16 : Fin 20) ![2485,2486,2487,2488] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(5472505383696048 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    have rightShape : EJMGlobalDAGData.nodes 5 93663 =
        .split (16 : Fin 20) ![493,493,493,93169] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(EJMGlobalDAGData.shapeWord 1502 /
          2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
          Nat.mod_lt _ (by decide)⟩) :
          Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, rightShape]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 2488 = .split (17 : Fin 20) ![2489,2490,2491,2492] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(5481303624726321 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    have rightShape : EJMGlobalDAGData.nodes 4 93169 =
        .split (17 : Fin 20) ![494,494,494,92687] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(EJMGlobalDAGData.shapeWord 1008 /
          2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
          Nat.mod_lt _ (by decide)⟩) :
          Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, rightShape]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2492 = .split (18 : Fin 20) ![2493,2494,2495,2496] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(5490101865756594 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    have rightShape : EJMGlobalDAGData.nodes 3 92687 =
        .split (18 : Fin 20) ![495,495,495,0] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(EJMGlobalDAGData.shapeWord 526 /
          2 ^ (21 * a.val) % 2 ^ 21) % EJMGlobalDAGData.Size,
          Nat.mod_lt _ (by decide)⟩) :
          Node EJMGlobalDAGData.Size (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, rightShape]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related 1) .bound .bound
    exact .bound

private theorem original_subtree_2480 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 94965 cache2480 partial2480 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related alignment
    6 2480 94965 cache2480 partial2480 (by unfold Related; decide +kernel)
    EJMGlobalSuffixProbeBlock0.receipt2480

#print axioms alignment
#print axioms original_subtree_2480

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentProbe
