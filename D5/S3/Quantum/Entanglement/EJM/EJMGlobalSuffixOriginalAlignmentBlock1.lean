/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock1
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixOriginalAlignmentBlock1
   mirror-E: none(waiver:actual-original-suffix-helper)
   anchors: []
   utility: none
   digest: Checked finite simulation transports full frontier subtrees to the original DAG, preserving actual caches and partial events. -/

/- Prepared exact suffix alignment; compilation is still required. Every
cache, partial event, symmetry and gap is the original actual expression.
This is not acceptance of the complete original global certificate. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalDAGData
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock0
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock1
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock10
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock11
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock2
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock4
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock5
import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixAlignmentShapesBlock6
import D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 65536
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock1
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay (check)
open D5.S0.Certificates.FiniteCachedSymmetryDAGSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale)

private def Related2249 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 6 ∧ left = 2249 ∧ right = 161531) ∨
  (fuel = 5 ∧ left = 2250 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 2251 ∧ right = 2894) ∨
  (fuel = 5 ∧ left = 2252 ∧ right = 161530) ∨
  (fuel = 4 ∧ left = 2253 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2254 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2255 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2256 ∧ right = 161529) ∨
  (fuel = 3 ∧ left = 2257 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2258 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2259 ∧ right = 95262) ∨
  (fuel = 2 ∧ left = 2260 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2261 ∧ right = 92212) ∨
  (fuel = 1 ∧ left = 2262 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2263 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2264 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2265 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2266 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 2267 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2268 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2269 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2270 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2271 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 2272 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2273 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2274 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2275 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 2276 ∧ right = 93931) ∨
  (fuel = 2 ∧ left = 2277 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 2278 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2279 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2280 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2281 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2282 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2283 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2284 ∧ right = 0) ∨
  (fuel = 5 ∧ left = 2285 ∧ right = 129699) ∨
  (fuel = 4 ∧ left = 2286 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2287 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2288 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2289 ∧ right = 129050) ∨
  (fuel = 3 ∧ left = 2290 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2291 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2292 ∧ right = 92553) ∨
  (fuel = 2 ∧ left = 2293 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2294 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2295 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2296 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 2297 ∧ right = 129049) ∨
  (fuel = 2 ∧ left = 2298 ∧ right = 94132) ∨
  (fuel = 1 ∧ left = 2299 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2300 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2301 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 2302 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2303 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2304 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2305 ∧ right = 0)

private theorem alignment2249 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related2249 (fuel + 1) left right) :
    StepRelated (Related2249 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 5 := by omega
    subst fuel left right
    have leftShape : pilotNodes 6 2249 = .split (15 : Fin 20) ![2250,2251,2252,2285] := by
      change (.split (15 : Fin 20)
        (fun a => ⟨(5025977467345231 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (15 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_6_161531]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related2249 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    change StepRelated (Related2249 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 2252 = .split (16 : Fin 20) ![2253,2254,2255,2256] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4962207403940272 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_5_161530]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2249 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2249 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2249 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 2256 = .split (17 : Fin 20) ![2257,2258,2259,2276] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(5006190017059377 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_4_161529]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2249 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2249 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2259 = .split (18 : Fin 20) ![2260,2261,2266,2271] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4995198659271314 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_3_95262]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2261 = .split (19 : Fin 20) ![2262,2263,2264,2265] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4982003446258387 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92212]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2266 = .split (19 : Fin 20) ![2267,2268,2269,2270] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4993001247546227 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2271 = .split (19 : Fin 20) ![2272,2273,2274,2275] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(5003999048834067 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2276 = .split (18 : Fin 20) ![2277,2282,2283,2284] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(5023795091152050 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_3_93931]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2277 = .split (19 : Fin 20) ![2278,2279,2280,2281] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(5017196410379475 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 2285 = .split (16 : Fin 20) ![2286,2287,2288,2289] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(5034792892440016 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_5_129699]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2249 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2249 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2249 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 2289 = .split (17 : Fin 20) ![2290,2291,2292,2297] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(5052387226492497 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_4_129050]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2249 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2249 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2292 = .split (18 : Fin 20) ![2293,2294,2295,2296] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(5050189814242994 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_92553]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2297 = .split (18 : Fin 20) ![2298,2303,2304,2305] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(5069985856560978 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_3_129049]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2298 = .split (19 : Fin 20) ![2299,2300,2301,2302] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(5063387175788403 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock6.shape_2_94132]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2249 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2249 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2249 1) .bound .bound
    exact .bound

theorem originalReceipt2249 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 6 161531 cache2249 partial2249 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related2249 alignment2249
    6 2249 161531 cache2249 partial2249 (by unfold Related2249; decide +kernel)
    EJMGlobalSuffixProbeBlock1.receipt2249

#print axioms originalReceipt2249

private def Related2204 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 2204 ∧ right = 161527) ∨
  (fuel = 4 ∧ left = 2205 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2206 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2207 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2208 ∧ right = 161526) ∨
  (fuel = 3 ∧ left = 2209 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2210 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2211 ∧ right = 161465) ∨
  (fuel = 2 ∧ left = 2212 ∧ right = 92336) ∨
  (fuel = 1 ∧ left = 2213 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2214 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2215 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2216 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2217 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 2218 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2219 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2220 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2221 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2222 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 2223 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2224 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2225 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2226 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2227 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 2228 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2229 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2230 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2231 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 2232 ∧ right = 161525) ∨
  (fuel = 2 ∧ left = 2233 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 2234 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2235 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2236 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2237 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2238 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 2239 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2240 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2241 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2242 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2243 ∧ right = 94133) ∨
  (fuel = 1 ∧ left = 2244 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2245 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2246 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2247 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2248 ∧ right = 0)

private theorem alignment2204 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related2204 (fuel + 1) left right) :
    StepRelated (Related2204 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 2204 = .split (16 : Fin 20) ![2205,2206,2207,2208] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4856628511577008 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_5_161527]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2204 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2204 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2204 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 2208 = .split (17 : Fin 20) ![2209,2210,2211,2232] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4909407217718321 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_4_161526]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2204 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2204 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2211 = .split (18 : Fin 20) ![2212,2217,2222,2227] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4898418007938194 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_161465]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2212 = .split (19 : Fin 20) ![2213,2214,2215,2216] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4874224993637555 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92336]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2217 = .split (19 : Fin 20) ![2218,2219,2220,2221] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4885222794925395 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2222 = .split (19 : Fin 20) ![2223,2224,2225,2226] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4896220596213235 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2227 = .split (19 : Fin 20) ![2228,2229,2230,2231] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4907218397501075 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2232 = .split (18 : Fin 20) ![2233,2238,2243,2248] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4944608773347122 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_3_161525]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2233 = .split (19 : Fin 20) ![2234,2235,2236,2237] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4920415759046483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2238 = .split (19 : Fin 20) ![2239,2240,2241,2242] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4931413560334323 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2243 = .split (19 : Fin 20) ![2244,2245,2246,2247] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4942411361622163 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_2_94133]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2204 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2204 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2204 1) .bound .bound
    exact .bound

theorem originalReceipt2204 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 161527 cache2204 partial2204 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related2204 alignment2204
    5 2204 161527 cache2204 partial2204 (by unfold Related2204; decide +kernel)
    EJMGlobalSuffixProbeBlock1.receipt2204

#print axioms originalReceipt2204

private def Related2163 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 2163 ∧ right = 161524) ∨
  (fuel = 4 ∧ left = 2164 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2165 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2166 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2167 ∧ right = 161523) ∨
  (fuel = 3 ∧ left = 2168 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2169 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2170 ∧ right = 108675) ∨
  (fuel = 2 ∧ left = 2171 ∧ right = 92212) ∨
  (fuel = 1 ∧ left = 2172 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2173 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2174 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2175 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2176 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 2177 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2178 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2179 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2180 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2181 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 2182 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2183 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2184 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2185 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2186 ∧ right = 92170) ∨
  (fuel = 1 ∧ left = 2187 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2188 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2189 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2190 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 2191 ∧ right = 105973) ∨
  (fuel = 2 ∧ left = 2192 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 2193 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2194 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2195 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2196 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2197 ∧ right = 92278) ∨
  (fuel = 1 ∧ left = 2198 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2199 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2200 ∧ right = 2898) ∨
  (fuel = 1 ∧ left = 2201 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2202 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2203 ∧ right = 0)

private theorem alignment2163 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related2163 (fuel + 1) left right) :
    StepRelated (Related2163 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 2163 = .split (16 : Fin 20) ![2164,2165,2166,2167] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4766446541016720 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_5_161524]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2163 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2163 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2163 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 2167 = .split (17 : Fin 20) ![2168,2169,2170,2191] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4819225247158033 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock11.shape_4_161523]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2163 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2163 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2170 = .split (18 : Fin 20) ![2171,2176,2181,2186] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4808236037377906 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_108675]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2171 = .split (19 : Fin 20) ![2172,2173,2174,2175] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4784043023077267 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92212]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2176 = .split (19 : Fin 20) ![2177,2178,2179,2180] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4795040824365107 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2181 = .split (19 : Fin 20) ![2182,2183,2184,2185] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4806038625652947 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2186 = .split (19 : Fin 20) ![2187,2188,2189,2190] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4817036426940787 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92170]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2191 = .split (18 : Fin 20) ![2192,2197,2202,2203] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4845630709764626 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock5.shape_3_105973]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2192 = .split (19 : Fin 20) ![2193,2194,2195,2196] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4830233788486195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2197 = .split (19 : Fin 20) ![2198,2199,2200,2201] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4841231589774035 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock0.shape_2_92278]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2163 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 17))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2163 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2163 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2163 1) .bound .bound
    exact .bound

theorem originalReceipt2163 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 161524 cache2163 partial2163 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related2163 alignment2163
    5 2163 161524 cache2163 partial2163 (by unfold Related2163; decide +kernel)
    EJMGlobalSuffixProbeBlock1.receipt2163

#print axioms originalReceipt2163

private def Related2162 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 2162 ∧ right = 2894)

private theorem alignment2162 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related2162 (fuel + 1) left right) :
    StepRelated (Related2162 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related2162 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt2162 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache2162 partial2162 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related2162 alignment2162
    5 2162 2894 cache2162 partial2162 (by unfold Related2162; decide +kernel)
    EJMGlobalSuffixProbeBlock1.receipt2162

#print axioms originalReceipt2162

private def Related2161 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 2161 ∧ right = 2894)

private theorem alignment2161 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related2161 (fuel + 1) left right) :
    StepRelated (Related2161 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with ⟨hf, hl, hr⟩
  have amount : fuel = 4 := by omega
  subst fuel left right
  change StepRelated (Related2161 4) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 144 13))
  exact .symmetry _

theorem originalReceipt2161 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 2894 cache2161 partial2161 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related2161 alignment2161
    5 2161 2894 cache2161 partial2161 (by unfold Related2161; decide +kernel)
    EJMGlobalSuffixProbeBlock1.receipt2161

#print axioms originalReceipt2161

private def Related2130 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) : Prop :=
  (fuel = 5 ∧ left = 2130 ∧ right = 161520) ∨
  (fuel = 4 ∧ left = 2131 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2132 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2133 ∧ right = 493) ∨
  (fuel = 4 ∧ left = 2134 ∧ right = 161519) ∨
  (fuel = 3 ∧ left = 2135 ∧ right = 494) ∨
  (fuel = 3 ∧ left = 2136 ∧ right = 94691) ∨
  (fuel = 2 ∧ left = 2137 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2138 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2139 ∧ right = 495) ∨
  (fuel = 2 ∧ left = 2140 ∧ right = 92336) ∨
  (fuel = 1 ∧ left = 2141 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2142 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2143 ∧ right = 496) ∨
  (fuel = 1 ∧ left = 2144 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 2145 ∧ right = 108737) ∨
  (fuel = 2 ∧ left = 2146 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2147 ∧ right = 92399) ∨
  (fuel = 1 ∧ left = 2148 ∧ right = 3374) ∨
  (fuel = 1 ∧ left = 2149 ∧ right = 3375) ∨
  (fuel = 1 ∧ left = 2150 ∧ right = 0) ∨
  (fuel = 1 ∧ left = 2151 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2152 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2153 ∧ right = 0) ∨
  (fuel = 3 ∧ left = 2154 ∧ right = 92176) ∨
  (fuel = 2 ∧ left = 2155 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2156 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2157 ∧ right = 0) ∨
  (fuel = 2 ∧ left = 2158 ∧ right = 0)

private theorem alignment2130 (fuel : ℕ) (left : Fin 2497)
    (right : Fin EJMGlobalDAGData.Size) (related : Related2130 (fuel + 1) left right) :
    StepRelated (Related2130 fuel) (pilotNodes (fuel + 1) left)
      (EJMGlobalDAGData.nodes (fuel + 1) right) := by
  rcases related with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 4 := by omega
    subst fuel left right
    have leftShape : pilotNodes 5 2130 = .split (16 : Fin 20) ![2131,2132,2133,2134] := by
      change (.split (16 : Fin 20)
        (fun a => ⟨(4693861052516976 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (16 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock10.shape_5_161520]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2130 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2130 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2130 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    change StepRelated (Related2130 3) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 12))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 3 := by omega
    subst fuel left right
    have leftShape : pilotNodes 4 2134 = .split (17 : Fin 20) ![2135,2136,2145,2154] := by
      change (.split (17 : Fin 20)
        (fun a => ⟨(4737847960603377 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock10.shape_4_161519]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2130 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    change StepRelated (Related2130 2) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2136 = .split (18 : Fin 20) ![2137,2138,2139,2140] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4707058414062386 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock4.shape_3_94691]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2130 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2140 = .split (19 : Fin 20) ![2141,2142,2143,2144] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4715856655092659 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92336]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2130 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 24 15))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2145 = .split (18 : Fin 20) ![2146,2147,2152,2153] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4735652696886354 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock10.shape_3_108737]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2130 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    have leftShape : pilotNodes 2 2147 = .split (19 : Fin 20) ![2148,2149,2150,2151] := by
      change (.split (19 : Fin 20)
        (fun a => ⟨(4731253576895635 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock1.shape_2_92399]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2130 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 13))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14)) (.symmetry (EJMGlobalScoreSymmetry.cutOfTag 168 14))
    exact .symmetry _
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 0 := by omega
    subst fuel left right
    change StepRelated (Related2130 0) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 2 := by omega
    subst fuel left right
    have leftShape : pilotNodes 3 2154 = .split (18 : Fin 20) ![2155,2156,2157,2158] := by
      change (.split (18 : Fin 20)
        (fun a => ⟨(4746650498698610 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl
    rw [leftShape, EJMGlobalSuffixAlignmentShapesBlock2.shape_3_92176]
    apply StepRelated.split
    intro a
    fin_cases a <;> unfold Related2130 <;> decide +kernel
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) .bound .bound
    exact .bound
  · rcases h with ⟨hf, hl, hr⟩
    have amount : fuel = 1 := by omega
    subst fuel left right
    change StepRelated (Related2130 1) .bound .bound
    exact .bound

theorem originalReceipt2130 :
    check EJMGlobalDAGData.nodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 161520 cache2130 partial2130 = true := by
  exact checked_simulation pilotNodes EJMGlobalDAGData.nodes step lower
    EJMGlobalScoreSymmetry.dominates scale Related2130 alignment2130
    5 2130 161520 cache2130 partial2130 (by unfold Related2130; decide +kernel)
    EJMGlobalSuffixProbeBlock1.receipt2130

#print axioms originalReceipt2130

end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixOriginalAlignmentBlock1
