/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock43
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock43
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock43
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache13 : Cache :=
  step cache12 ⟨17, by decide⟩ 0
private def partial13 : Partial (Fin 20) (Fin 4) :=
  Function.update partial12 ⟨17, by decide⟩ (some 0)

private def cache14 : Cache :=
  step cache12 ⟨17, by decide⟩ 1
private def partial14 : Partial (Fin 20) (Fin 4) :=
  Function.update partial12 ⟨17, by decide⟩ (some 1)

private def cache15 : Cache :=
  step cache14 ⟨18, by decide⟩ 0
private def partial15 : Partial (Fin 20) (Fin 4) :=
  Function.update partial14 ⟨18, by decide⟩ (some 0)

private def cache16 : Cache :=
  step cache14 ⟨18, by decide⟩ 1
private def partial16 : Partial (Fin 20) (Fin 4) :=
  Function.update partial14 ⟨18, by decide⟩ (some 1)

private def cache17 : Cache :=
  step cache16 ⟨19, by decide⟩ 0
private def partial17 : Partial (Fin 20) (Fin 4) :=
  Function.update partial16 ⟨19, by decide⟩ (some 0)

private def cache18 : Cache :=
  step cache16 ⟨19, by decide⟩ 1
private def partial18 : Partial (Fin 20) (Fin 4) :=
  Function.update partial16 ⟨19, by decide⟩ (some 1)

private def cache19 : Cache :=
  step cache16 ⟨19, by decide⟩ 2
private def partial19 : Partial (Fin 20) (Fin 4) :=
  Function.update partial16 ⟨19, by decide⟩ (some 2)

private def cache20 : Cache :=
  step cache16 ⟨19, by decide⟩ 3
private def partial20 : Partial (Fin 20) (Fin 4) :=
  Function.update partial16 ⟨19, by decide⟩ (some 3)

private def cache21 : Cache :=
  step cache14 ⟨18, by decide⟩ 2
private def partial21 : Partial (Fin 20) (Fin 4) :=
  Function.update partial14 ⟨18, by decide⟩ (some 2)

private def cache22 : Cache :=
  step cache21 ⟨19, by decide⟩ 0
private def partial22 : Partial (Fin 20) (Fin 4) :=
  Function.update partial21 ⟨19, by decide⟩ (some 0)

private def cache23 : Cache :=
  step cache21 ⟨19, by decide⟩ 1
private def partial23 : Partial (Fin 20) (Fin 4) :=
  Function.update partial21 ⟨19, by decide⟩ (some 1)

private def cache24 : Cache :=
  step cache21 ⟨19, by decide⟩ 2
private def partial24 : Partial (Fin 20) (Fin 4) :=
  Function.update partial21 ⟨19, by decide⟩ (some 2)

private def cache25 : Cache :=
  step cache21 ⟨19, by decide⟩ 3
private def partial25 : Partial (Fin 20) (Fin 4) :=
  Function.update partial21 ⟨19, by decide⟩ (some 3)

private def cache26 : Cache :=
  step cache14 ⟨18, by decide⟩ 3
private def partial26 : Partial (Fin 20) (Fin 4) :=
  Function.update partial14 ⟨18, by decide⟩ (some 3)

private def cache27 : Cache :=
  step cache26 ⟨19, by decide⟩ 0
private def partial27 : Partial (Fin 20) (Fin 4) :=
  Function.update partial26 ⟨19, by decide⟩ (some 0)

private def cache28 : Cache :=
  step cache26 ⟨19, by decide⟩ 1
private def partial28 : Partial (Fin 20) (Fin 4) :=
  Function.update partial26 ⟨19, by decide⟩ (some 1)

private def cache29 : Cache :=
  step cache26 ⟨19, by decide⟩ 2
private def partial29 : Partial (Fin 20) (Fin 4) :=
  Function.update partial26 ⟨19, by decide⟩ (some 2)

private def cache30 : Cache :=
  step cache26 ⟨19, by decide⟩ 3
private def partial30 : Partial (Fin 20) (Fin 4) :=
  Function.update partial26 ⟨19, by decide⟩ (some 3)

private def cache31 : Cache :=
  step cache12 ⟨17, by decide⟩ 2
private def partial31 : Partial (Fin 20) (Fin 4) :=
  Function.update partial12 ⟨17, by decide⟩ (some 2)

private def cache32 : Cache :=
  step cache31 ⟨18, by decide⟩ 0
private def partial32 : Partial (Fin 20) (Fin 4) :=
  Function.update partial31 ⟨18, by decide⟩ (some 0)

private def cache33 : Cache :=
  step cache32 ⟨19, by decide⟩ 0
private def partial33 : Partial (Fin 20) (Fin 4) :=
  Function.update partial32 ⟨19, by decide⟩ (some 0)

private def cache34 : Cache :=
  step cache32 ⟨19, by decide⟩ 1
private def partial34 : Partial (Fin 20) (Fin 4) :=
  Function.update partial32 ⟨19, by decide⟩ (some 1)

private def cache35 : Cache :=
  step cache32 ⟨19, by decide⟩ 2
private def partial35 : Partial (Fin 20) (Fin 4) :=
  Function.update partial32 ⟨19, by decide⟩ (some 2)

private def cache36 : Cache :=
  step cache32 ⟨19, by decide⟩ 3
private def partial36 : Partial (Fin 20) (Fin 4) :=
  Function.update partial32 ⟨19, by decide⟩ (some 3)

private def cache37 : Cache :=
  step cache31 ⟨18, by decide⟩ 1
private def partial37 : Partial (Fin 20) (Fin 4) :=
  Function.update partial31 ⟨18, by decide⟩ (some 1)

private def cache38 : Cache :=
  step cache37 ⟨19, by decide⟩ 0
private def partial38 : Partial (Fin 20) (Fin 4) :=
  Function.update partial37 ⟨19, by decide⟩ (some 0)

private def cache39 : Cache :=
  step cache37 ⟨19, by decide⟩ 1
private def partial39 : Partial (Fin 20) (Fin 4) :=
  Function.update partial37 ⟨19, by decide⟩ (some 1)

private def cache40 : Cache :=
  step cache37 ⟨19, by decide⟩ 2
private def partial40 : Partial (Fin 20) (Fin 4) :=
  Function.update partial37 ⟨19, by decide⟩ (some 2)

private def cache41 : Cache :=
  step cache37 ⟨19, by decide⟩ 3
private def partial41 : Partial (Fin 20) (Fin 4) :=
  Function.update partial37 ⟨19, by decide⟩ (some 3)

private def cache42 : Cache :=
  step cache31 ⟨18, by decide⟩ 2
private def partial42 : Partial (Fin 20) (Fin 4) :=
  Function.update partial31 ⟨18, by decide⟩ (some 2)

private def cache43 : Cache :=
  step cache42 ⟨19, by decide⟩ 0
private def partial43 : Partial (Fin 20) (Fin 4) :=
  Function.update partial42 ⟨19, by decide⟩ (some 0)

private def cache44 : Cache :=
  step cache42 ⟨19, by decide⟩ 1
private def partial44 : Partial (Fin 20) (Fin 4) :=
  Function.update partial42 ⟨19, by decide⟩ (some 1)

private def cache45 : Cache :=
  step cache42 ⟨19, by decide⟩ 2
private def partial45 : Partial (Fin 20) (Fin 4) :=
  Function.update partial42 ⟨19, by decide⟩ (some 2)

private def cache46 : Cache :=
  step cache42 ⟨19, by decide⟩ 3
private def partial46 : Partial (Fin 20) (Fin 4) :=
  Function.update partial42 ⟨19, by decide⟩ (some 3)

private def cache47 : Cache :=
  step cache31 ⟨18, by decide⟩ 3
private def partial47 : Partial (Fin 20) (Fin 4) :=
  Function.update partial31 ⟨18, by decide⟩ (some 3)

private def cache48 : Cache :=
  step cache47 ⟨19, by decide⟩ 0
private def partial48 : Partial (Fin 20) (Fin 4) :=
  Function.update partial47 ⟨19, by decide⟩ (some 0)

private def cache49 : Cache :=
  step cache47 ⟨19, by decide⟩ 1
private def partial49 : Partial (Fin 20) (Fin 4) :=
  Function.update partial47 ⟨19, by decide⟩ (some 1)

private def cache50 : Cache :=
  step cache47 ⟨19, by decide⟩ 2
private def partial50 : Partial (Fin 20) (Fin 4) :=
  Function.update partial47 ⟨19, by decide⟩ (some 2)

private def cache51 : Cache :=
  step cache47 ⟨19, by decide⟩ 3
private def partial51 : Partial (Fin 20) (Fin 4) :=
  Function.update partial47 ⟨19, by decide⟩ (some 3)

private def cache52 : Cache :=
  step cache12 ⟨17, by decide⟩ 3
private def partial52 : Partial (Fin 20) (Fin 4) :=
  Function.update partial12 ⟨17, by decide⟩ (some 3)

private def cache53 : Cache :=
  step cache52 ⟨18, by decide⟩ 0
private def partial53 : Partial (Fin 20) (Fin 4) :=
  Function.update partial52 ⟨18, by decide⟩ (some 0)

private def cache54 : Cache :=
  step cache53 ⟨19, by decide⟩ 0
private def partial54 : Partial (Fin 20) (Fin 4) :=
  Function.update partial53 ⟨19, by decide⟩ (some 0)

private def cache55 : Cache :=
  step cache53 ⟨19, by decide⟩ 1
private def partial55 : Partial (Fin 20) (Fin 4) :=
  Function.update partial53 ⟨19, by decide⟩ (some 1)

private def cache56 : Cache :=
  step cache53 ⟨19, by decide⟩ 2
private def partial56 : Partial (Fin 20) (Fin 4) :=
  Function.update partial53 ⟨19, by decide⟩ (some 2)

private def cache57 : Cache :=
  step cache53 ⟨19, by decide⟩ 3
private def partial57 : Partial (Fin 20) (Fin 4) :=
  Function.update partial53 ⟨19, by decide⟩ (some 3)

private def cache58 : Cache :=
  step cache52 ⟨18, by decide⟩ 1
private def partial58 : Partial (Fin 20) (Fin 4) :=
  Function.update partial52 ⟨18, by decide⟩ (some 1)

private def cache59 : Cache :=
  step cache58 ⟨19, by decide⟩ 0
private def partial59 : Partial (Fin 20) (Fin 4) :=
  Function.update partial58 ⟨19, by decide⟩ (some 0)

private def cache60 : Cache :=
  step cache58 ⟨19, by decide⟩ 1
private def partial60 : Partial (Fin 20) (Fin 4) :=
  Function.update partial58 ⟨19, by decide⟩ (some 1)

private def cache61 : Cache :=
  step cache58 ⟨19, by decide⟩ 2
private def partial61 : Partial (Fin 20) (Fin 4) :=
  Function.update partial58 ⟨19, by decide⟩ (some 2)

private def cache62 : Cache :=
  step cache58 ⟨19, by decide⟩ 3
private def partial62 : Partial (Fin 20) (Fin 4) :=
  Function.update partial58 ⟨19, by decide⟩ (some 3)

private def cache63 : Cache :=
  step cache52 ⟨18, by decide⟩ 2
private def partial63 : Partial (Fin 20) (Fin 4) :=
  Function.update partial52 ⟨18, by decide⟩ (some 2)

private def cache64 : Cache :=
  step cache63 ⟨19, by decide⟩ 0
private def partial64 : Partial (Fin 20) (Fin 4) :=
  Function.update partial63 ⟨19, by decide⟩ (some 0)

private def cache65 : Cache :=
  step cache63 ⟨19, by decide⟩ 1
private def partial65 : Partial (Fin 20) (Fin 4) :=
  Function.update partial63 ⟨19, by decide⟩ (some 1)

private def cache66 : Cache :=
  step cache63 ⟨19, by decide⟩ 2
private def partial66 : Partial (Fin 20) (Fin 4) :=
  Function.update partial63 ⟨19, by decide⟩ (some 2)

private def cache67 : Cache :=
  step cache63 ⟨19, by decide⟩ 3
private def partial67 : Partial (Fin 20) (Fin 4) :=
  Function.update partial63 ⟨19, by decide⟩ (some 3)

private def cache68 : Cache :=
  step cache52 ⟨18, by decide⟩ 3
private def partial68 : Partial (Fin 20) (Fin 4) :=
  Function.update partial52 ⟨18, by decide⟩ (some 3)

private def cache69 : Cache :=
  step cache68 ⟨19, by decide⟩ 0
private def partial69 : Partial (Fin 20) (Fin 4) :=
  Function.update partial68 ⟨19, by decide⟩ (some 0)

private def cache70 : Cache :=
  step cache68 ⟨19, by decide⟩ 1
private def partial70 : Partial (Fin 20) (Fin 4) :=
  Function.update partial68 ⟨19, by decide⟩ (some 1)

private def cache71 : Cache :=
  step cache68 ⟨19, by decide⟩ 2
private def partial71 : Partial (Fin 20) (Fin 4) :=
  Function.update partial68 ⟨19, by decide⟩ (some 2)

private def cache72 : Cache :=
  step cache68 ⟨19, by decide⟩ 3
private def partial72 : Partial (Fin 20) (Fin 4) :=
  Function.update partial68 ⟨19, by decide⟩ (some 3)

private theorem receipt72 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨72, by decide⟩ cache72 partial72 = true := by
  decide +kernel

private theorem receipt71 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨71, by decide⟩ cache71 partial71 = true := by
  decide +kernel

private theorem receipt70 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨70, by decide⟩ cache70 partial70 = true := by
  decide +kernel

private theorem receipt69 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨69, by decide⟩ cache69 partial69 = true := by
  decide +kernel

private theorem receipt68 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨68, by decide⟩ cache68 partial68 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![69,70,71,72])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(158367801411763 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt69
  · exact receipt70
  · exact receipt71
  · exact receipt72

private theorem receipt67 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨67, by decide⟩ cache67 partial67 = true := by
  decide +kernel

private theorem receipt66 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨66, by decide⟩ cache66 partial66 = true := by
  decide +kernel

private theorem receipt65 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨65, by decide⟩ cache65 partial65 = true := by
  decide +kernel

private theorem receipt64 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨64, by decide⟩ cache64 partial64 = true := by
  decide +kernel

private theorem receipt63 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨63, by decide⟩ cache63 partial63 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![64,65,66,67])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(147370000123923 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt64
  · exact receipt65
  · exact receipt66
  · exact receipt67

private theorem receipt62 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨62, by decide⟩ cache62 partial62 = true := by
  decide +kernel

private theorem receipt61 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨61, by decide⟩ cache61 partial61 = true := by
  decide +kernel

private theorem receipt60 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨60, by decide⟩ cache60 partial60 = true := by
  decide +kernel

private theorem receipt59 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨59, by decide⟩ cache59 partial59 = true := by
  decide +kernel

private theorem receipt58 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨58, by decide⟩ cache58 partial58 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![59,60,61,62])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(136372198836083 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt59
  · exact receipt60
  · exact receipt61
  · exact receipt62

private theorem receipt57 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨57, by decide⟩ cache57 partial57 = true := by
  decide +kernel

private theorem receipt56 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨56, by decide⟩ cache56 partial56 = true := by
  decide +kernel

private theorem receipt55 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨55, by decide⟩ cache55 partial55 = true := by
  decide +kernel

private theorem receipt54 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨54, by decide⟩ cache54 partial54 = true := by
  decide +kernel

private theorem receipt53 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨53, by decide⟩ cache53 partial53 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![54,55,56,57])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(125374397548243 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt54
  · exact receipt55
  · exact receipt56
  · exact receipt57

private theorem receipt52 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨52, by decide⟩ cache52 partial52 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![53,58,63,68])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(149567411848882 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt53
  · exact receipt58
  · exact receipt63
  · exact receipt68

private theorem receipt51 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨51, by decide⟩ cache51 partial51 = true := by
  decide +kernel

private theorem receipt50 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨50, by decide⟩ cache50 partial50 = true := by
  decide +kernel

private theorem receipt49 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨49, by decide⟩ cache49 partial49 = true := by
  decide +kernel

private theorem receipt48 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨48, by decide⟩ cache48 partial48 = true := by
  decide +kernel

private theorem receipt47 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨47, by decide⟩ cache47 partial47 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![48,49,50,51])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(112177036002835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt48
  · exact receipt49
  · exact receipt50
  · exact receipt51

private theorem receipt46 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨46, by decide⟩ cache46 partial46 = true := by
  decide +kernel

private theorem receipt45 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨45, by decide⟩ cache45 partial45 = true := by
  decide +kernel

private theorem receipt44 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨44, by decide⟩ cache44 partial44 = true := by
  decide +kernel

private theorem receipt43 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨43, by decide⟩ cache43 partial43 = true := by
  decide +kernel

private theorem receipt42 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨42, by decide⟩ cache42 partial42 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![43,44,45,46])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(101179234714995 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt43
  · exact receipt44
  · exact receipt45
  · exact receipt46

private theorem receipt41 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨41, by decide⟩ cache41 partial41 = true := by
  decide +kernel

private theorem receipt40 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨40, by decide⟩ cache40 partial40 = true := by
  decide +kernel

private theorem receipt39 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨39, by decide⟩ cache39 partial39 = true := by
  decide +kernel

private theorem receipt38 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨38, by decide⟩ cache38 partial38 = true := by
  decide +kernel

private theorem receipt37 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨37, by decide⟩ cache37 partial37 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![38,39,40,41])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(90181433427155 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt38
  · exact receipt39
  · exact receipt40
  · exact receipt41

private theorem receipt36 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨36, by decide⟩ cache36 partial36 = true := by
  decide +kernel

private theorem receipt35 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨35, by decide⟩ cache35 partial35 = true := by
  decide +kernel

private theorem receipt34 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨34, by decide⟩ cache34 partial34 = true := by
  decide +kernel

private theorem receipt33 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨33, by decide⟩ cache33 partial33 = true := by
  decide +kernel

private theorem receipt32 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨32, by decide⟩ cache32 partial32 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![33,34,35,36])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(79183632139315 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt33
  · exact receipt34
  · exact receipt35
  · exact receipt36

private theorem receipt31 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨31, by decide⟩ cache31 partial31 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![32,37,42,47])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(103376646439954 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt32
  · exact receipt37
  · exact receipt42
  · exact receipt47

private theorem receipt30 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨30, by decide⟩ cache30 partial30 = true := by
  decide +kernel

private theorem receipt29 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨29, by decide⟩ cache29 partial29 = true := by
  decide +kernel

private theorem receipt28 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨28, by decide⟩ cache28 partial28 = true := by
  decide +kernel

private theorem receipt27 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨27, by decide⟩ cache27 partial27 = true := by
  decide +kernel

private theorem receipt26 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨26, by decide⟩ cache26 partial26 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![27,28,29,30])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(65986270593907 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt27
  · exact receipt28
  · exact receipt29
  · exact receipt30

private theorem receipt25 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨25, by decide⟩ cache25 partial25 = true := by
  decide +kernel

private theorem receipt24 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨24, by decide⟩ cache24 partial24 = true := by
  decide +kernel

private theorem receipt23 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨23, by decide⟩ cache23 partial23 = true := by
  decide +kernel

private theorem receipt22 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨22, by decide⟩ cache22 partial22 = true := by
  decide +kernel

private theorem receipt21 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨21, by decide⟩ cache21 partial21 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![22,23,24,25])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(54988469306067 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt22
  · exact receipt23
  · exact receipt24
  · exact receipt25

private theorem receipt20 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨20, by decide⟩ cache20 partial20 = true := by
  decide +kernel

private theorem receipt19 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨19, by decide⟩ cache19 partial19 = true := by
  decide +kernel

private theorem receipt18 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨18, by decide⟩ cache18 partial18 = true := by
  decide +kernel

private theorem receipt17 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨17, by decide⟩ cache17 partial17 = true := by
  decide +kernel

private theorem receipt16 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨16, by decide⟩ cache16 partial16 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![17,18,19,20])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(43990668018227 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt17
  · exact receipt18
  · exact receipt19
  · exact receipt20

private theorem receipt15 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨15, by decide⟩ cache15 partial15 = true := by
  decide +kernel

private theorem receipt14 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨14, by decide⟩ cache14 partial14 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![15,16,21,26])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(57185881031154 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt15
  · exact receipt16
  · exact receipt21
  · exact receipt26

private theorem receipt13 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨13, by decide⟩ cache13 partial13 = true := by
  decide +kernel

theorem receipt12 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨12, by decide⟩ cache12 partial12 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![13,14,31,52])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(114365854122417 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt13
  · exact receipt14
  · exact receipt31
  · exact receipt52

theorem receipt11 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨11, by decide⟩ cache11 partial11 = true := by
  decide +kernel

theorem receipt10 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨10, by decide⟩ cache10 partial10 = true := by
  decide +kernel

theorem receipt8 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨8, by decide⟩ cache8 partial8 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock43
