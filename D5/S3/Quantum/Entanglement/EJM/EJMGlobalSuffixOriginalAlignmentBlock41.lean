/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock41
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock41
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock41
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock41
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related137 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 137 ∧ right = 161434) ∨
  (fuel = 3 ∧ left = 138 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 139 ∧ right = 113677) ∨
  (fuel = 2 ∧ left = 140 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 141 ∧ right = 92212) ∨
  (fuel = 1 ∧ left = 142 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 143 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 144 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 145 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 146 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 147 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 148 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 149 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 150 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 151 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 152 ∧ right = 108651) ∨
  (fuel = 2 ∧ left = 153 ∧ right = 92399) ∨
  (fuel = 1 ∧ left = 154 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 155 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 156 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 157 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 158 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 159 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 160 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 161 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 162 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 163 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 164 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 165 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 166 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 167 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 168 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 169 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 170 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 171 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 172 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 173 ∧ right = 108651) ∨
  (fuel = 2 ∧ left = 174 ∧ right = 92399) ∨
  (fuel = 1 ∧ left = 175 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 176 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 177 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 178 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 179 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 180 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 181 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 182 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 183 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 184 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 185 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 186 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 187 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 188 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 189 ∧ right = 92282) ∨
  (fuel = 1 ∧ left = 190 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 191 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 192 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 193 ∧ right = 0)

private theorem alignment137 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related137 (fuel + 1) left right) :
    StepRelated (Related137 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 137 = .split (17 : Fin 20) ![138,139,152,173] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(380512645812561 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_4_161434]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related137 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 139 = .split (18 : Fin 20) ![140,141,146,147] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(323334820204946 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113677]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related137 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 141 = .split (19 : Fin 20) ![142,143,144,145] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(318935700214227 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92212]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related137 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 147 = .split (19 : Fin 20) ![148,149,150,151] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(332133061759635 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 152 = .split (18 : Fin 20) ![153,158,163,168] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(369523437605682 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_108651]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 153 = .split (19 : Fin 20) ![154,155,156,157] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(345330423305043 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92399]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 158 = .split (19 : Fin 20) ![159,160,161,162] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(356328224592883 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 163 = .split (19 : Fin 20) ![164,165,166,167] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(367326025880723 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 168 = .split (19 : Fin 20) ![169,170,171,172] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(378323827168563 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 173 = .split (18 : Fin 20) ![174,179,184,189] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(415714203014610 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_108651]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 174 = .split (19 : Fin 20) ![175,176,177,178] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(391521188713971 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92399]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 179 = .split (19 : Fin 20) ![180,181,182,183] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(402518990001811 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 184 = .split (19 : Fin 20) ![185,186,187,188] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(413516791289651 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 189 = .split (19 : Fin 20) ![190,191,192,193] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(424514592577491 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92282]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related137 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related137 0) .bound .bound
    exact .bound

theorem originalReceipt137 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161434 cache137 partial137 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related137 alignment137
    4 137 161434 cache137 partial137 (by unfold Related137; decide +kernel)
    EJMGlobalSuffixProbeBlock41.receipt137

#print axioms originalReceipt137

private def Related136 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 136 ∧ right = 493)

private theorem alignment136 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related136 (fuel + 1) left right) :
    StepRelated (Related136 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related136 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt136 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache136 partial136 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related136 alignment136
    4 136 493 cache136 partial136 (by unfold Related136; decide +kernel)
    EJMGlobalSuffixProbeBlock41.receipt136

#print axioms originalReceipt136

private def Related135 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 135 ∧ right = 493)

private theorem alignment135 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related135 (fuel + 1) left right) :
    StepRelated (Related135 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 3 := by omega
  subst fuel left right
  change StepRelated (Related135 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
  exact .symmetry _

theorem originalReceipt135 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 493 cache135 partial135 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related135 alignment135
    4 135 493 cache135 partial135 (by unfold Related135; decide +kernel)
    EJMGlobalSuffixProbeBlock41.receipt135

#print axioms originalReceipt135

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock41
