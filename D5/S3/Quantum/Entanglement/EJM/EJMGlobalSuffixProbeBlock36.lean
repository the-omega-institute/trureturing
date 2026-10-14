/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock36
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock36
   mirror-E: none(waiver:actual-global-cover-kernel-probe)
   anchors: []
   utility: none
   digest: Exact full subtree leaf receipts and every four-child split are assembled without changing their actual contexts. -/

/- Same complete existing-cover suffix. This is computational staging of the
original actual cache/partial expressions and all four branches. Native input
is untrusted. Only canonical kernel compilation earns each receipt. These
receipts close this exact suffix, not the complete global refutation. -/

import D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option linter.style.longLine false

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock36
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache407 : Cache :=
  step cache406 ⟨17, by decide⟩ 0
private def partial407 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 0)

private def cache408 : Cache :=
  step cache406 ⟨17, by decide⟩ 1
private def partial408 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 1)

private def cache409 : Cache :=
  step cache408 ⟨18, by decide⟩ 0
private def partial409 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 0)

private def cache410 : Cache :=
  step cache408 ⟨18, by decide⟩ 1
private def partial410 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 1)

private def cache411 : Cache :=
  step cache410 ⟨19, by decide⟩ 0
private def partial411 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 0)

private def cache412 : Cache :=
  step cache410 ⟨19, by decide⟩ 1
private def partial412 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 1)

private def cache413 : Cache :=
  step cache410 ⟨19, by decide⟩ 2
private def partial413 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 2)

private def cache414 : Cache :=
  step cache410 ⟨19, by decide⟩ 3
private def partial414 : Partial (Fin 20) (Fin 4) :=
  Function.update partial410 ⟨19, by decide⟩ (some 3)

private def cache415 : Cache :=
  step cache408 ⟨18, by decide⟩ 2
private def partial415 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 2)

private def cache416 : Cache :=
  step cache415 ⟨19, by decide⟩ 0
private def partial416 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 0)

private def cache417 : Cache :=
  step cache415 ⟨19, by decide⟩ 1
private def partial417 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 1)

private def cache418 : Cache :=
  step cache415 ⟨19, by decide⟩ 2
private def partial418 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 2)

private def cache419 : Cache :=
  step cache415 ⟨19, by decide⟩ 3
private def partial419 : Partial (Fin 20) (Fin 4) :=
  Function.update partial415 ⟨19, by decide⟩ (some 3)

private def cache420 : Cache :=
  step cache408 ⟨18, by decide⟩ 3
private def partial420 : Partial (Fin 20) (Fin 4) :=
  Function.update partial408 ⟨18, by decide⟩ (some 3)

private def cache421 : Cache :=
  step cache420 ⟨19, by decide⟩ 0
private def partial421 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 0)

private def cache422 : Cache :=
  step cache420 ⟨19, by decide⟩ 1
private def partial422 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 1)

private def cache423 : Cache :=
  step cache420 ⟨19, by decide⟩ 2
private def partial423 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 2)

private def cache424 : Cache :=
  step cache420 ⟨19, by decide⟩ 3
private def partial424 : Partial (Fin 20) (Fin 4) :=
  Function.update partial420 ⟨19, by decide⟩ (some 3)

private def cache425 : Cache :=
  step cache406 ⟨17, by decide⟩ 2
private def partial425 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 2)

private def cache426 : Cache :=
  step cache425 ⟨18, by decide⟩ 0
private def partial426 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 0)

private def cache427 : Cache :=
  step cache425 ⟨18, by decide⟩ 1
private def partial427 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 1)

private def cache428 : Cache :=
  step cache425 ⟨18, by decide⟩ 2
private def partial428 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 2)

private def cache429 : Cache :=
  step cache425 ⟨18, by decide⟩ 3
private def partial429 : Partial (Fin 20) (Fin 4) :=
  Function.update partial425 ⟨18, by decide⟩ (some 3)

private def cache430 : Cache :=
  step cache406 ⟨17, by decide⟩ 3
private def partial430 : Partial (Fin 20) (Fin 4) :=
  Function.update partial406 ⟨17, by decide⟩ (some 3)

private def cache431 : Cache :=
  step cache430 ⟨18, by decide⟩ 0
private def partial431 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 0)

private def cache432 : Cache :=
  step cache430 ⟨18, by decide⟩ 1
private def partial432 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 1)

private def cache433 : Cache :=
  step cache432 ⟨19, by decide⟩ 0
private def partial433 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 0)

private def cache434 : Cache :=
  step cache432 ⟨19, by decide⟩ 1
private def partial434 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 1)

private def cache435 : Cache :=
  step cache432 ⟨19, by decide⟩ 2
private def partial435 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 2)

private def cache436 : Cache :=
  step cache432 ⟨19, by decide⟩ 3
private def partial436 : Partial (Fin 20) (Fin 4) :=
  Function.update partial432 ⟨19, by decide⟩ (some 3)

private def cache437 : Cache :=
  step cache430 ⟨18, by decide⟩ 2
private def partial437 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 2)

private def cache438 : Cache :=
  step cache437 ⟨19, by decide⟩ 0
private def partial438 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 0)

private def cache439 : Cache :=
  step cache437 ⟨19, by decide⟩ 1
private def partial439 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 1)

private def cache440 : Cache :=
  step cache437 ⟨19, by decide⟩ 2
private def partial440 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 2)

private def cache441 : Cache :=
  step cache437 ⟨19, by decide⟩ 3
private def partial441 : Partial (Fin 20) (Fin 4) :=
  Function.update partial437 ⟨19, by decide⟩ (some 3)

private def cache442 : Cache :=
  step cache430 ⟨18, by decide⟩ 3
private def partial442 : Partial (Fin 20) (Fin 4) :=
  Function.update partial430 ⟨18, by decide⟩ (some 3)

private def cache443 : Cache :=
  step cache442 ⟨19, by decide⟩ 0
private def partial443 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 0)

private def cache444 : Cache :=
  step cache442 ⟨19, by decide⟩ 1
private def partial444 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 1)

private def cache445 : Cache :=
  step cache442 ⟨19, by decide⟩ 2
private def partial445 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 2)

private def cache446 : Cache :=
  step cache442 ⟨19, by decide⟩ 3
private def partial446 : Partial (Fin 20) (Fin 4) :=
  Function.update partial442 ⟨19, by decide⟩ (some 3)

private theorem receipt446 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨446, by decide⟩ cache446 partial446 = true := by
  decide +kernel

private theorem receipt445 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨445, by decide⟩ cache445 partial445 = true := by
  decide +kernel

private theorem receipt444 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨444, by decide⟩ cache444 partial444 = true := by
  decide +kernel

private theorem receipt443 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨443, by decide⟩ cache443 partial443 = true := by
  decide +kernel

private theorem receipt442 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨442, by decide⟩ cache442 partial442 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![443,444,445,446])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(981003337742195 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt443
  · exact receipt444
  · exact receipt445
  · exact receipt446

private theorem receipt441 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨441, by decide⟩ cache441 partial441 = true := by
  decide +kernel

private theorem receipt440 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨440, by decide⟩ cache440 partial440 = true := by
  decide +kernel

private theorem receipt439 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨439, by decide⟩ cache439 partial439 = true := by
  decide +kernel

private theorem receipt438 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨438, by decide⟩ cache438 partial438 = true := by
  decide +kernel

private theorem receipt437 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨437, by decide⟩ cache437 partial437 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![438,439,440,441])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(970005536454355 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt438
  · exact receipt439
  · exact receipt440
  · exact receipt441

private theorem receipt436 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨436, by decide⟩ cache436 partial436 = true := by
  decide +kernel

private theorem receipt435 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨435, by decide⟩ cache435 partial435 = true := by
  decide +kernel

private theorem receipt434 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨434, by decide⟩ cache434 partial434 = true := by
  decide +kernel

private theorem receipt433 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨433, by decide⟩ cache433 partial433 = true := by
  decide +kernel

private theorem receipt432 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨432, by decide⟩ cache432 partial432 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![433,434,435,436])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(959007735166515 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt433
  · exact receipt434
  · exact receipt435
  · exact receipt436

private theorem receipt431 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨431, by decide⟩ cache431 partial431 = true := by
  decide +kernel

private theorem receipt430 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨430, by decide⟩ cache430 partial430 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![431,432,437,442])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(972202948179442 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt431
  · exact receipt432
  · exact receipt437
  · exact receipt442

private theorem receipt429 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨429, by decide⟩ cache429 partial429 = true := by
  decide +kernel

private theorem receipt428 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨428, by decide⟩ cache428 partial428 = true := by
  decide +kernel

private theorem receipt427 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨427, by decide⟩ cache427 partial427 = true := by
  decide +kernel

private theorem receipt426 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨426, by decide⟩ cache426 partial426 = true := by
  decide +kernel

private theorem receipt425 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨425, by decide⟩ cache425 partial425 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![426,427,428,429])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(943610813363538 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt426
  · exact receipt427
  · exact receipt428
  · exact receipt429

private theorem receipt424 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨424, by decide⟩ cache424 partial424 = true := by
  decide +kernel

private theorem receipt423 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨423, by decide⟩ cache423 partial423 = true := by
  decide +kernel

private theorem receipt422 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨422, by decide⟩ cache422 partial422 = true := by
  decide +kernel

private theorem receipt421 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨421, by decide⟩ cache421 partial421 = true := by
  decide +kernel

private theorem receipt420 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨420, by decide⟩ cache420 partial420 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![421,422,423,424])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(932613012075699 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt421
  · exact receipt422
  · exact receipt423
  · exact receipt424

private theorem receipt419 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨419, by decide⟩ cache419 partial419 = true := by
  decide +kernel

private theorem receipt418 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨418, by decide⟩ cache418 partial418 = true := by
  decide +kernel

private theorem receipt417 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨417, by decide⟩ cache417 partial417 = true := by
  decide +kernel

private theorem receipt416 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨416, by decide⟩ cache416 partial416 = true := by
  decide +kernel

private theorem receipt415 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨415, by decide⟩ cache415 partial415 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![416,417,418,419])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(921615210787859 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt416
  · exact receipt417
  · exact receipt418
  · exact receipt419

private theorem receipt414 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨414, by decide⟩ cache414 partial414 = true := by
  decide +kernel

private theorem receipt413 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨413, by decide⟩ cache413 partial413 = true := by
  decide +kernel

private theorem receipt412 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨412, by decide⟩ cache412 partial412 = true := by
  decide +kernel

private theorem receipt411 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨411, by decide⟩ cache411 partial411 = true := by
  decide +kernel

private theorem receipt410 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨410, by decide⟩ cache410 partial410 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![411,412,413,414])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(910617409500019 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt411
  · exact receipt412
  · exact receipt413
  · exact receipt414

private theorem receipt409 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨409, by decide⟩ cache409 partial409 = true := by
  decide +kernel

private theorem receipt408 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨408, by decide⟩ cache408 partial408 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![409,410,415,420])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(923812622512946 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt409
  · exact receipt410
  · exact receipt415
  · exact receipt420

private theorem receipt407 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨407, by decide⟩ cache407 partial407 = true := by
  decide +kernel

theorem receipt406 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨406, by decide⟩ cache406 partial406 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![407,408,425,430])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(945808223515377 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt407
  · exact receipt408
  · exact receipt425
  · exact receipt430


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock36
