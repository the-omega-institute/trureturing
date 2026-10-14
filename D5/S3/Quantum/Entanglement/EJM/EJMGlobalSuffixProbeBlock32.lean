/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock32
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock32
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock32
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache573 : Cache :=
  step cache572 ⟨17, by decide⟩ 0
private def partial573 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 0)

private def cache574 : Cache :=
  step cache572 ⟨17, by decide⟩ 1
private def partial574 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 1)

private def cache575 : Cache :=
  step cache574 ⟨18, by decide⟩ 0
private def partial575 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 0)

private def cache576 : Cache :=
  step cache574 ⟨18, by decide⟩ 1
private def partial576 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 1)

private def cache577 : Cache :=
  step cache576 ⟨19, by decide⟩ 0
private def partial577 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 0)

private def cache578 : Cache :=
  step cache576 ⟨19, by decide⟩ 1
private def partial578 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 1)

private def cache579 : Cache :=
  step cache576 ⟨19, by decide⟩ 2
private def partial579 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 2)

private def cache580 : Cache :=
  step cache576 ⟨19, by decide⟩ 3
private def partial580 : Partial (Fin 20) (Fin 4) :=
  Function.update partial576 ⟨19, by decide⟩ (some 3)

private def cache581 : Cache :=
  step cache574 ⟨18, by decide⟩ 2
private def partial581 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 2)

private def cache582 : Cache :=
  step cache581 ⟨19, by decide⟩ 0
private def partial582 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 0)

private def cache583 : Cache :=
  step cache581 ⟨19, by decide⟩ 1
private def partial583 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 1)

private def cache584 : Cache :=
  step cache581 ⟨19, by decide⟩ 2
private def partial584 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 2)

private def cache585 : Cache :=
  step cache581 ⟨19, by decide⟩ 3
private def partial585 : Partial (Fin 20) (Fin 4) :=
  Function.update partial581 ⟨19, by decide⟩ (some 3)

private def cache586 : Cache :=
  step cache574 ⟨18, by decide⟩ 3
private def partial586 : Partial (Fin 20) (Fin 4) :=
  Function.update partial574 ⟨18, by decide⟩ (some 3)

private def cache587 : Cache :=
  step cache586 ⟨19, by decide⟩ 0
private def partial587 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 0)

private def cache588 : Cache :=
  step cache586 ⟨19, by decide⟩ 1
private def partial588 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 1)

private def cache589 : Cache :=
  step cache586 ⟨19, by decide⟩ 2
private def partial589 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 2)

private def cache590 : Cache :=
  step cache586 ⟨19, by decide⟩ 3
private def partial590 : Partial (Fin 20) (Fin 4) :=
  Function.update partial586 ⟨19, by decide⟩ (some 3)

private def cache591 : Cache :=
  step cache572 ⟨17, by decide⟩ 2
private def partial591 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 2)

private def cache592 : Cache :=
  step cache591 ⟨18, by decide⟩ 0
private def partial592 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 0)

private def cache593 : Cache :=
  step cache591 ⟨18, by decide⟩ 1
private def partial593 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 1)

private def cache594 : Cache :=
  step cache593 ⟨19, by decide⟩ 0
private def partial594 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 0)

private def cache595 : Cache :=
  step cache593 ⟨19, by decide⟩ 1
private def partial595 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 1)

private def cache596 : Cache :=
  step cache593 ⟨19, by decide⟩ 2
private def partial596 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 2)

private def cache597 : Cache :=
  step cache593 ⟨19, by decide⟩ 3
private def partial597 : Partial (Fin 20) (Fin 4) :=
  Function.update partial593 ⟨19, by decide⟩ (some 3)

private def cache598 : Cache :=
  step cache591 ⟨18, by decide⟩ 2
private def partial598 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 2)

private def cache599 : Cache :=
  step cache591 ⟨18, by decide⟩ 3
private def partial599 : Partial (Fin 20) (Fin 4) :=
  Function.update partial591 ⟨18, by decide⟩ (some 3)

private def cache600 : Cache :=
  step cache599 ⟨19, by decide⟩ 0
private def partial600 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 0)

private def cache601 : Cache :=
  step cache599 ⟨19, by decide⟩ 1
private def partial601 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 1)

private def cache602 : Cache :=
  step cache599 ⟨19, by decide⟩ 2
private def partial602 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 2)

private def cache603 : Cache :=
  step cache599 ⟨19, by decide⟩ 3
private def partial603 : Partial (Fin 20) (Fin 4) :=
  Function.update partial599 ⟨19, by decide⟩ (some 3)

private def cache604 : Cache :=
  step cache572 ⟨17, by decide⟩ 3
private def partial604 : Partial (Fin 20) (Fin 4) :=
  Function.update partial572 ⟨17, by decide⟩ (some 3)

private def cache605 : Cache :=
  step cache604 ⟨18, by decide⟩ 0
private def partial605 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 0)

private def cache606 : Cache :=
  step cache605 ⟨19, by decide⟩ 0
private def partial606 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 0)

private def cache607 : Cache :=
  step cache605 ⟨19, by decide⟩ 1
private def partial607 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 1)

private def cache608 : Cache :=
  step cache605 ⟨19, by decide⟩ 2
private def partial608 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 2)

private def cache609 : Cache :=
  step cache605 ⟨19, by decide⟩ 3
private def partial609 : Partial (Fin 20) (Fin 4) :=
  Function.update partial605 ⟨19, by decide⟩ (some 3)

private def cache610 : Cache :=
  step cache604 ⟨18, by decide⟩ 1
private def partial610 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 1)

private def cache611 : Cache :=
  step cache610 ⟨19, by decide⟩ 0
private def partial611 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 0)

private def cache612 : Cache :=
  step cache610 ⟨19, by decide⟩ 1
private def partial612 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 1)

private def cache613 : Cache :=
  step cache610 ⟨19, by decide⟩ 2
private def partial613 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 2)

private def cache614 : Cache :=
  step cache610 ⟨19, by decide⟩ 3
private def partial614 : Partial (Fin 20) (Fin 4) :=
  Function.update partial610 ⟨19, by decide⟩ (some 3)

private def cache615 : Cache :=
  step cache604 ⟨18, by decide⟩ 2
private def partial615 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 2)

private def cache616 : Cache :=
  step cache615 ⟨19, by decide⟩ 0
private def partial616 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 0)

private def cache617 : Cache :=
  step cache615 ⟨19, by decide⟩ 1
private def partial617 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 1)

private def cache618 : Cache :=
  step cache615 ⟨19, by decide⟩ 2
private def partial618 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 2)

private def cache619 : Cache :=
  step cache615 ⟨19, by decide⟩ 3
private def partial619 : Partial (Fin 20) (Fin 4) :=
  Function.update partial615 ⟨19, by decide⟩ (some 3)

private def cache620 : Cache :=
  step cache604 ⟨18, by decide⟩ 3
private def partial620 : Partial (Fin 20) (Fin 4) :=
  Function.update partial604 ⟨18, by decide⟩ (some 3)

private def cache621 : Cache :=
  step cache620 ⟨19, by decide⟩ 0
private def partial621 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 0)

private def cache622 : Cache :=
  step cache620 ⟨19, by decide⟩ 1
private def partial622 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 1)

private def cache623 : Cache :=
  step cache620 ⟨19, by decide⟩ 2
private def partial623 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 2)

private def cache624 : Cache :=
  step cache620 ⟨19, by decide⟩ 3
private def partial624 : Partial (Fin 20) (Fin 4) :=
  Function.update partial620 ⟨19, by decide⟩ (some 3)

theorem receipt626 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨626, by decide⟩ cache626 partial626 = true := by
  decide +kernel

private theorem receipt624 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨624, by decide⟩ cache624 partial624 = true := by
  decide +kernel

private theorem receipt623 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨623, by decide⟩ cache623 partial623 = true := by
  decide +kernel

private theorem receipt622 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨622, by decide⟩ cache622 partial622 = true := by
  decide +kernel

private theorem receipt621 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨621, by decide⟩ cache621 partial621 = true := by
  decide +kernel

private theorem receipt620 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨620, by decide⟩ cache620 partial620 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![621,622,623,624])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1372525063589299 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt621
  · exact receipt622
  · exact receipt623
  · exact receipt624

private theorem receipt619 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨619, by decide⟩ cache619 partial619 = true := by
  decide +kernel

private theorem receipt618 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨618, by decide⟩ cache618 partial618 = true := by
  decide +kernel

private theorem receipt617 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨617, by decide⟩ cache617 partial617 = true := by
  decide +kernel

private theorem receipt616 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨616, by decide⟩ cache616 partial616 = true := by
  decide +kernel

private theorem receipt615 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨615, by decide⟩ cache615 partial615 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![616,617,618,619])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1361527262301459 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt616
  · exact receipt617
  · exact receipt618
  · exact receipt619

private theorem receipt614 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨614, by decide⟩ cache614 partial614 = true := by
  decide +kernel

private theorem receipt613 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨613, by decide⟩ cache613 partial613 = true := by
  decide +kernel

private theorem receipt612 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨612, by decide⟩ cache612 partial612 = true := by
  decide +kernel

private theorem receipt611 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨611, by decide⟩ cache611 partial611 = true := by
  decide +kernel

private theorem receipt610 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨610, by decide⟩ cache610 partial610 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![611,612,613,614])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1350529461013619 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt611
  · exact receipt612
  · exact receipt613
  · exact receipt614

private theorem receipt609 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨609, by decide⟩ cache609 partial609 = true := by
  decide +kernel

private theorem receipt608 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨608, by decide⟩ cache608 partial608 = true := by
  decide +kernel

private theorem receipt607 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨607, by decide⟩ cache607 partial607 = true := by
  decide +kernel

private theorem receipt606 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨606, by decide⟩ cache606 partial606 = true := by
  decide +kernel

private theorem receipt605 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨605, by decide⟩ cache605 partial605 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![606,607,608,609])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1339531659725779 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt606
  · exact receipt607
  · exact receipt608
  · exact receipt609

private theorem receipt604 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨604, by decide⟩ cache604 partial604 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![605,610,615,620])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1363724674026418 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt605
  · exact receipt610
  · exact receipt615
  · exact receipt620

private theorem receipt603 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨603, by decide⟩ cache603 partial603 = true := by
  decide +kernel

private theorem receipt602 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨602, by decide⟩ cache602 partial602 = true := by
  decide +kernel

private theorem receipt601 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨601, by decide⟩ cache601 partial601 = true := by
  decide +kernel

private theorem receipt600 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨600, by decide⟩ cache600 partial600 = true := by
  decide +kernel

private theorem receipt599 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨599, by decide⟩ cache599 partial599 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![600,601,602,603])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1326334298180371 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt600
  · exact receipt601
  · exact receipt602
  · exact receipt603

private theorem receipt598 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨598, by decide⟩ cache598 partial598 = true := by
  decide +kernel

private theorem receipt597 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨597, by decide⟩ cache597 partial597 = true := by
  decide +kernel

private theorem receipt596 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨596, by decide⟩ cache596 partial596 = true := by
  decide +kernel

private theorem receipt595 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨595, by decide⟩ cache595 partial595 = true := by
  decide +kernel

private theorem receipt594 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨594, by decide⟩ cache594 partial594 = true := by
  decide +kernel

private theorem receipt593 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨593, by decide⟩ cache593 partial593 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![594,595,596,597])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1313136936634963 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt594
  · exact receipt595
  · exact receipt596
  · exact receipt597

private theorem receipt592 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨592, by decide⟩ cache592 partial592 = true := by
  decide +kernel

private theorem receipt591 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨591, by decide⟩ cache591 partial591 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![592,593,598,599])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1317536056625682 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt592
  · exact receipt593
  · exact receipt598
  · exact receipt599

private theorem receipt590 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨590, by decide⟩ cache590 partial590 = true := by
  decide +kernel

private theorem receipt589 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨589, by decide⟩ cache589 partial589 = true := by
  decide +kernel

private theorem receipt588 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨588, by decide⟩ cache588 partial588 = true := by
  decide +kernel

private theorem receipt587 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨587, by decide⟩ cache587 partial587 = true := by
  decide +kernel

private theorem receipt586 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨586, by decide⟩ cache586 partial586 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![587,588,589,590])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1297740014831987 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt587
  · exact receipt588
  · exact receipt589
  · exact receipt590

private theorem receipt585 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨585, by decide⟩ cache585 partial585 = true := by
  decide +kernel

private theorem receipt584 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨584, by decide⟩ cache584 partial584 = true := by
  decide +kernel

private theorem receipt583 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨583, by decide⟩ cache583 partial583 = true := by
  decide +kernel

private theorem receipt582 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨582, by decide⟩ cache582 partial582 = true := by
  decide +kernel

private theorem receipt581 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨581, by decide⟩ cache581 partial581 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![582,583,584,585])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1286742213544147 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt582
  · exact receipt583
  · exact receipt584
  · exact receipt585

private theorem receipt580 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨580, by decide⟩ cache580 partial580 = true := by
  decide +kernel

private theorem receipt579 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨579, by decide⟩ cache579 partial579 = true := by
  decide +kernel

private theorem receipt578 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨578, by decide⟩ cache578 partial578 = true := by
  decide +kernel

private theorem receipt577 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨577, by decide⟩ cache577 partial577 = true := by
  decide +kernel

private theorem receipt576 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨576, by decide⟩ cache576 partial576 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![577,578,579,580])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(1275744412256307 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt577
  · exact receipt578
  · exact receipt579
  · exact receipt580

private theorem receipt575 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨575, by decide⟩ cache575 partial575 = true := by
  decide +kernel

private theorem receipt574 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨574, by decide⟩ cache574 partial574 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![575,576,581,586])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(1288939625269234 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt575
  · exact receipt576
  · exact receipt581
  · exact receipt586

private theorem receipt573 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨573, by decide⟩ cache573 partial573 = true := by
  decide +kernel

theorem receipt572 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨572, by decide⟩ cache572 partial572 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![573,574,591,604])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(1328527412316081 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt573
  · exact receipt574
  · exact receipt591
  · exact receipt604


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock32
