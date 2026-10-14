/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock40
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock40
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock40
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock40
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related194 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 4 ∧ left = 194 ∧ right = 161435) ∨
  (fuel = 3 ∧ left = 195 ∧ right = 1950) ∨
  (fuel = 3 ∧ left = 196 ∧ right = 113680) ∨
  (fuel = 2 ∧ left = 197 ∧ right = 1951) ∨
  (fuel = 2 ∧ left = 198 ∧ right = 101524) ∨
  (fuel = 1 ∧ left = 199 ∧ right = 1952) ∨
  (fuel = 1 ∧ left = 200 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 201 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 202 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 203 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 204 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 205 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 206 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 207 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 208 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 209 ∧ right = 113682) ∨
  (fuel = 2 ∧ left = 210 ∧ right = 113681) ∨
  (fuel = 1 ∧ left = 211 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 212 ∧ right = 4831) ∨
  (fuel = 1 ∧ left = 213 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 214 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 215 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 216 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 217 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 218 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 219 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 220 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 221 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 222 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 223 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 224 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 225 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 226 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 227 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 228 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 229 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 230 ∧ right = 113682) ∨
  (fuel = 2 ∧ left = 231 ∧ right = 113681) ∨
  (fuel = 1 ∧ left = 232 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 233 ∧ right = 4831) ∨
  (fuel = 1 ∧ left = 234 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 235 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 236 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 237 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 238 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 239 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 240 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 241 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 242 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 243 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 244 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 245 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 246 ∧ right = 113505) ∨
  (fuel = 1 ∧ left = 247 ∧ right = 4830) ∨
  (fuel = 1 ∧ left = 248 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 249 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 250 ∧ right = 0)

private theorem alignment194 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related194 (fuel + 1) left right) :
    StepRelated (Related194 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 194 = .split (17 : Fin 20) ![195,196,209,230] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(505887580493937 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_4_161435]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related194 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 196 = .split (18 : Fin 20) ![197,198,203,204] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(448709754886322 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113680]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related194 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 198 = .split (19 : Fin 20) ![199,200,201,202] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(444310634895603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_101524]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 97 11))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related194 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 204 = .split (19 : Fin 20) ![205,206,207,208] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(457507996441011 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 209 = .split (18 : Fin 20) ![210,215,220,225] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(494898372287058 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113682]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 210 = .split (19 : Fin 20) ![211,212,213,214] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(470705357986419 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113681]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 215 = .split (19 : Fin 20) ![216,217,218,219] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(481703159274259 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 220 = .split (19 : Fin 20) ![221,222,223,224] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(492700960562099 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 225 = .split (19 : Fin 20) ![226,227,228,229] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(503698761849939 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 230 = .split (18 : Fin 20) ![231,236,241,246] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(541089137695986 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_3_113682]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 231 = .split (19 : Fin 20) ![232,233,234,235] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(516896123395347 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113681]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 10))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 236 = .split (19 : Fin 20) ![237,238,239,240] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(527893924683187 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 241 = .split (19 : Fin 20) ![242,243,244,245] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(538891725971027 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 246 = .split (19 : Fin 20) ![247,248,249,250] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(549889527258867 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_113505]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related194 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 241 9))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related194 0) .bound .bound
    exact .bound

theorem originalReceipt194 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 161435 cache194 partial194 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related194 alignment194
    4 194 161435 cache194 partial194 (by unfold Related194; decide +kernel)
    EJMGlobalSuffixProbeBlock40.receipt194

#print axioms originalReceipt194

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock40
