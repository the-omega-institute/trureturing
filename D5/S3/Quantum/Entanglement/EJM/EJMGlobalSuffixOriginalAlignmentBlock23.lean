/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock23
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock23
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock23
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock2
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock23
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related1003 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 1003 ∧ right = 113698) ∨
  (fuel = 3 ∧ left = 1004 ∧ right = 1950) ∨
  (fuel = 3 ∧ left = 1005 ∧ right = 113693) ∨
  (fuel = 2 ∧ left = 1006 ∧ right = 1951) ∨
  (fuel = 2 ∧ left = 1007 ∧ right = 101524) ∨
  (fuel = 1 ∧ left = 1008 ∧ right = 1952) ∨
  (fuel = 1 ∧ left = 1009 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1010 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1011 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1012 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1013 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1014 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1015 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1016 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1017 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1018 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1019 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1020 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1021 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1022 ∧ right = 113682) ∨
  (fuel = 2 ∧ left = 1023 ∧ right = 113681) ∨
  (fuel = 1 ∧ left = 1024 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1025 ∧ right = 4831) ∨
  (fuel = 1 ∧ left = 1026 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1027 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1028 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1029 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1030 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1031 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1032 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1033 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1034 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1035 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1036 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1037 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1038 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1039 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1040 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1041 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1042 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 1043 ∧ right = 113682) ∨
  (fuel = 2 ∧ left = 1044 ∧ right = 113681) ∨
  (fuel = 1 ∧ left = 1045 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1046 ∧ right = 4831) ∨
  (fuel = 1 ∧ left = 1047 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1048 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1049 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1050 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1051 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1052 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1053 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1054 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1055 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1056 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1057 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1058 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 1059 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 1060 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 1061 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1062 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 1063 ∧ right = 0)

private theorem alignment1003 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related1003 (fuel + 1) left right) :
    StepRelated (Related1003 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 1003 = .split (17 : Fin 20) ![1004,1005,1022,1043] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2294130069372305 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_4_113698]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related1003 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1005 = .split (18 : Fin 20) ![1006,1007,1012,1017] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2236950096281042 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_3_113693]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related1003 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1007 = .split (19 : Fin 20) ![1008,1009,1010,1011] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2223754883268115 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_101524]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1012 = .split (19 : Fin 20) ![1013,1014,1015,1016] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2234752684555955 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1017 = .split (19 : Fin 20) ![1018,1019,1020,1021] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2245750485843795 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1022 = .split (18 : Fin 20) ![1023,1028,1033,1038] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2283140861689842 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113682]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1023 = .split (19 : Fin 20) ![1024,1025,1026,1027] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2258947847389203 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113681]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1028 = .split (19 : Fin 20) ![1029,1030,1031,1032] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2269945648677043 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1033 = .split (19 : Fin 20) ![1034,1035,1036,1037] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2280943449964883 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1038 = .split (19 : Fin 20) ![1039,1040,1041,1042] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2291941251252723 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 1043 = .split (18 : Fin 20) ![1044,1049,1054,1059] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2329331627098770 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113682]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1044 = .split (19 : Fin 20) ![1045,1046,1047,1048] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2305138612798131 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113681]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1049 = .split (19 : Fin 20) ![1050,1051,1052,1053] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2316136414085971 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1054 = .split (19 : Fin 20) ![1055,1056,1057,1058] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2327134215373811 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 1059 = .split (19 : Fin 20) ![1060,1061,1062,1063] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2338132016661651 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related1003 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related1003 0) .bound .bound
    exact .bound

theorem originalReceipt1003 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 113698 cache1003 partial1003 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related1003 alignment1003
    4 1003 113698 cache1003 partial1003 (by unfold Related1003; decide +kernel)
    EJMGlobalSuffixProbeBlock23.receipt1003

#print axioms originalReceipt1003

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock23
