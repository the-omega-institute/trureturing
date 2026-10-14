/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock42
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock42
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock42
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache74 : Cache :=
  step cache73 ⟨17, by decide⟩ 0
private def partial74 : Partial (Fin 20) (Fin 4) :=
  Function.update partial73 ⟨17, by decide⟩ (some 0)

private def cache75 : Cache :=
  step cache73 ⟨17, by decide⟩ 1
private def partial75 : Partial (Fin 20) (Fin 4) :=
  Function.update partial73 ⟨17, by decide⟩ (some 1)

private def cache76 : Cache :=
  step cache75 ⟨18, by decide⟩ 0
private def partial76 : Partial (Fin 20) (Fin 4) :=
  Function.update partial75 ⟨18, by decide⟩ (some 0)

private def cache77 : Cache :=
  step cache75 ⟨18, by decide⟩ 1
private def partial77 : Partial (Fin 20) (Fin 4) :=
  Function.update partial75 ⟨18, by decide⟩ (some 1)

private def cache78 : Cache :=
  step cache77 ⟨19, by decide⟩ 0
private def partial78 : Partial (Fin 20) (Fin 4) :=
  Function.update partial77 ⟨19, by decide⟩ (some 0)

private def cache79 : Cache :=
  step cache77 ⟨19, by decide⟩ 1
private def partial79 : Partial (Fin 20) (Fin 4) :=
  Function.update partial77 ⟨19, by decide⟩ (some 1)

private def cache80 : Cache :=
  step cache77 ⟨19, by decide⟩ 2
private def partial80 : Partial (Fin 20) (Fin 4) :=
  Function.update partial77 ⟨19, by decide⟩ (some 2)

private def cache81 : Cache :=
  step cache77 ⟨19, by decide⟩ 3
private def partial81 : Partial (Fin 20) (Fin 4) :=
  Function.update partial77 ⟨19, by decide⟩ (some 3)

private def cache82 : Cache :=
  step cache75 ⟨18, by decide⟩ 2
private def partial82 : Partial (Fin 20) (Fin 4) :=
  Function.update partial75 ⟨18, by decide⟩ (some 2)

private def cache83 : Cache :=
  step cache82 ⟨19, by decide⟩ 0
private def partial83 : Partial (Fin 20) (Fin 4) :=
  Function.update partial82 ⟨19, by decide⟩ (some 0)

private def cache84 : Cache :=
  step cache82 ⟨19, by decide⟩ 1
private def partial84 : Partial (Fin 20) (Fin 4) :=
  Function.update partial82 ⟨19, by decide⟩ (some 1)

private def cache85 : Cache :=
  step cache82 ⟨19, by decide⟩ 2
private def partial85 : Partial (Fin 20) (Fin 4) :=
  Function.update partial82 ⟨19, by decide⟩ (some 2)

private def cache86 : Cache :=
  step cache82 ⟨19, by decide⟩ 3
private def partial86 : Partial (Fin 20) (Fin 4) :=
  Function.update partial82 ⟨19, by decide⟩ (some 3)

private def cache87 : Cache :=
  step cache75 ⟨18, by decide⟩ 3
private def partial87 : Partial (Fin 20) (Fin 4) :=
  Function.update partial75 ⟨18, by decide⟩ (some 3)

private def cache88 : Cache :=
  step cache87 ⟨19, by decide⟩ 0
private def partial88 : Partial (Fin 20) (Fin 4) :=
  Function.update partial87 ⟨19, by decide⟩ (some 0)

private def cache89 : Cache :=
  step cache87 ⟨19, by decide⟩ 1
private def partial89 : Partial (Fin 20) (Fin 4) :=
  Function.update partial87 ⟨19, by decide⟩ (some 1)

private def cache90 : Cache :=
  step cache87 ⟨19, by decide⟩ 2
private def partial90 : Partial (Fin 20) (Fin 4) :=
  Function.update partial87 ⟨19, by decide⟩ (some 2)

private def cache91 : Cache :=
  step cache87 ⟨19, by decide⟩ 3
private def partial91 : Partial (Fin 20) (Fin 4) :=
  Function.update partial87 ⟨19, by decide⟩ (some 3)

private def cache92 : Cache :=
  step cache73 ⟨17, by decide⟩ 2
private def partial92 : Partial (Fin 20) (Fin 4) :=
  Function.update partial73 ⟨17, by decide⟩ (some 2)

private def cache93 : Cache :=
  step cache92 ⟨18, by decide⟩ 0
private def partial93 : Partial (Fin 20) (Fin 4) :=
  Function.update partial92 ⟨18, by decide⟩ (some 0)

private def cache94 : Cache :=
  step cache93 ⟨19, by decide⟩ 0
private def partial94 : Partial (Fin 20) (Fin 4) :=
  Function.update partial93 ⟨19, by decide⟩ (some 0)

private def cache95 : Cache :=
  step cache93 ⟨19, by decide⟩ 1
private def partial95 : Partial (Fin 20) (Fin 4) :=
  Function.update partial93 ⟨19, by decide⟩ (some 1)

private def cache96 : Cache :=
  step cache93 ⟨19, by decide⟩ 2
private def partial96 : Partial (Fin 20) (Fin 4) :=
  Function.update partial93 ⟨19, by decide⟩ (some 2)

private def cache97 : Cache :=
  step cache93 ⟨19, by decide⟩ 3
private def partial97 : Partial (Fin 20) (Fin 4) :=
  Function.update partial93 ⟨19, by decide⟩ (some 3)

private def cache98 : Cache :=
  step cache92 ⟨18, by decide⟩ 1
private def partial98 : Partial (Fin 20) (Fin 4) :=
  Function.update partial92 ⟨18, by decide⟩ (some 1)

private def cache99 : Cache :=
  step cache98 ⟨19, by decide⟩ 0
private def partial99 : Partial (Fin 20) (Fin 4) :=
  Function.update partial98 ⟨19, by decide⟩ (some 0)

private def cache100 : Cache :=
  step cache98 ⟨19, by decide⟩ 1
private def partial100 : Partial (Fin 20) (Fin 4) :=
  Function.update partial98 ⟨19, by decide⟩ (some 1)

private def cache101 : Cache :=
  step cache98 ⟨19, by decide⟩ 2
private def partial101 : Partial (Fin 20) (Fin 4) :=
  Function.update partial98 ⟨19, by decide⟩ (some 2)

private def cache102 : Cache :=
  step cache98 ⟨19, by decide⟩ 3
private def partial102 : Partial (Fin 20) (Fin 4) :=
  Function.update partial98 ⟨19, by decide⟩ (some 3)

private def cache103 : Cache :=
  step cache92 ⟨18, by decide⟩ 2
private def partial103 : Partial (Fin 20) (Fin 4) :=
  Function.update partial92 ⟨18, by decide⟩ (some 2)

private def cache104 : Cache :=
  step cache103 ⟨19, by decide⟩ 0
private def partial104 : Partial (Fin 20) (Fin 4) :=
  Function.update partial103 ⟨19, by decide⟩ (some 0)

private def cache105 : Cache :=
  step cache103 ⟨19, by decide⟩ 1
private def partial105 : Partial (Fin 20) (Fin 4) :=
  Function.update partial103 ⟨19, by decide⟩ (some 1)

private def cache106 : Cache :=
  step cache103 ⟨19, by decide⟩ 2
private def partial106 : Partial (Fin 20) (Fin 4) :=
  Function.update partial103 ⟨19, by decide⟩ (some 2)

private def cache107 : Cache :=
  step cache103 ⟨19, by decide⟩ 3
private def partial107 : Partial (Fin 20) (Fin 4) :=
  Function.update partial103 ⟨19, by decide⟩ (some 3)

private def cache108 : Cache :=
  step cache92 ⟨18, by decide⟩ 3
private def partial108 : Partial (Fin 20) (Fin 4) :=
  Function.update partial92 ⟨18, by decide⟩ (some 3)

private def cache109 : Cache :=
  step cache108 ⟨19, by decide⟩ 0
private def partial109 : Partial (Fin 20) (Fin 4) :=
  Function.update partial108 ⟨19, by decide⟩ (some 0)

private def cache110 : Cache :=
  step cache108 ⟨19, by decide⟩ 1
private def partial110 : Partial (Fin 20) (Fin 4) :=
  Function.update partial108 ⟨19, by decide⟩ (some 1)

private def cache111 : Cache :=
  step cache108 ⟨19, by decide⟩ 2
private def partial111 : Partial (Fin 20) (Fin 4) :=
  Function.update partial108 ⟨19, by decide⟩ (some 2)

private def cache112 : Cache :=
  step cache108 ⟨19, by decide⟩ 3
private def partial112 : Partial (Fin 20) (Fin 4) :=
  Function.update partial108 ⟨19, by decide⟩ (some 3)

private def cache113 : Cache :=
  step cache73 ⟨17, by decide⟩ 3
private def partial113 : Partial (Fin 20) (Fin 4) :=
  Function.update partial73 ⟨17, by decide⟩ (some 3)

private def cache114 : Cache :=
  step cache113 ⟨18, by decide⟩ 0
private def partial114 : Partial (Fin 20) (Fin 4) :=
  Function.update partial113 ⟨18, by decide⟩ (some 0)

private def cache115 : Cache :=
  step cache114 ⟨19, by decide⟩ 0
private def partial115 : Partial (Fin 20) (Fin 4) :=
  Function.update partial114 ⟨19, by decide⟩ (some 0)

private def cache116 : Cache :=
  step cache114 ⟨19, by decide⟩ 1
private def partial116 : Partial (Fin 20) (Fin 4) :=
  Function.update partial114 ⟨19, by decide⟩ (some 1)

private def cache117 : Cache :=
  step cache114 ⟨19, by decide⟩ 2
private def partial117 : Partial (Fin 20) (Fin 4) :=
  Function.update partial114 ⟨19, by decide⟩ (some 2)

private def cache118 : Cache :=
  step cache114 ⟨19, by decide⟩ 3
private def partial118 : Partial (Fin 20) (Fin 4) :=
  Function.update partial114 ⟨19, by decide⟩ (some 3)

private def cache119 : Cache :=
  step cache113 ⟨18, by decide⟩ 1
private def partial119 : Partial (Fin 20) (Fin 4) :=
  Function.update partial113 ⟨18, by decide⟩ (some 1)

private def cache120 : Cache :=
  step cache119 ⟨19, by decide⟩ 0
private def partial120 : Partial (Fin 20) (Fin 4) :=
  Function.update partial119 ⟨19, by decide⟩ (some 0)

private def cache121 : Cache :=
  step cache119 ⟨19, by decide⟩ 1
private def partial121 : Partial (Fin 20) (Fin 4) :=
  Function.update partial119 ⟨19, by decide⟩ (some 1)

private def cache122 : Cache :=
  step cache119 ⟨19, by decide⟩ 2
private def partial122 : Partial (Fin 20) (Fin 4) :=
  Function.update partial119 ⟨19, by decide⟩ (some 2)

private def cache123 : Cache :=
  step cache119 ⟨19, by decide⟩ 3
private def partial123 : Partial (Fin 20) (Fin 4) :=
  Function.update partial119 ⟨19, by decide⟩ (some 3)

private def cache124 : Cache :=
  step cache113 ⟨18, by decide⟩ 2
private def partial124 : Partial (Fin 20) (Fin 4) :=
  Function.update partial113 ⟨18, by decide⟩ (some 2)

private def cache125 : Cache :=
  step cache124 ⟨19, by decide⟩ 0
private def partial125 : Partial (Fin 20) (Fin 4) :=
  Function.update partial124 ⟨19, by decide⟩ (some 0)

private def cache126 : Cache :=
  step cache124 ⟨19, by decide⟩ 1
private def partial126 : Partial (Fin 20) (Fin 4) :=
  Function.update partial124 ⟨19, by decide⟩ (some 1)

private def cache127 : Cache :=
  step cache124 ⟨19, by decide⟩ 2
private def partial127 : Partial (Fin 20) (Fin 4) :=
  Function.update partial124 ⟨19, by decide⟩ (some 2)

private def cache128 : Cache :=
  step cache124 ⟨19, by decide⟩ 3
private def partial128 : Partial (Fin 20) (Fin 4) :=
  Function.update partial124 ⟨19, by decide⟩ (some 3)

private def cache129 : Cache :=
  step cache113 ⟨18, by decide⟩ 3
private def partial129 : Partial (Fin 20) (Fin 4) :=
  Function.update partial113 ⟨18, by decide⟩ (some 3)

private def cache130 : Cache :=
  step cache129 ⟨19, by decide⟩ 0
private def partial130 : Partial (Fin 20) (Fin 4) :=
  Function.update partial129 ⟨19, by decide⟩ (some 0)

private def cache131 : Cache :=
  step cache129 ⟨19, by decide⟩ 1
private def partial131 : Partial (Fin 20) (Fin 4) :=
  Function.update partial129 ⟨19, by decide⟩ (some 1)

private def cache132 : Cache :=
  step cache129 ⟨19, by decide⟩ 2
private def partial132 : Partial (Fin 20) (Fin 4) :=
  Function.update partial129 ⟨19, by decide⟩ (some 2)

private def cache133 : Cache :=
  step cache129 ⟨19, by decide⟩ 3
private def partial133 : Partial (Fin 20) (Fin 4) :=
  Function.update partial129 ⟨19, by decide⟩ (some 3)

private theorem receipt133 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨133, by decide⟩ cache133 partial133 = true := by
  decide +kernel

private theorem receipt132 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨132, by decide⟩ cache132 partial132 = true := by
  decide +kernel

private theorem receipt131 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨131, by decide⟩ cache131 partial131 = true := by
  decide +kernel

private theorem receipt130 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨130, by decide⟩ cache130 partial130 = true := by
  decide +kernel

private theorem receipt129 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨129, by decide⟩ cache129 partial129 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![130,131,132,133])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(292540977123411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt130
  · exact receipt131
  · exact receipt132
  · exact receipt133

private theorem receipt128 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨128, by decide⟩ cache128 partial128 = true := by
  decide +kernel

private theorem receipt127 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨127, by decide⟩ cache127 partial127 = true := by
  decide +kernel

private theorem receipt126 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨126, by decide⟩ cache126 partial126 = true := by
  decide +kernel

private theorem receipt125 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨125, by decide⟩ cache125 partial125 = true := by
  decide +kernel

private theorem receipt124 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨124, by decide⟩ cache124 partial124 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![125,126,127,128])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(281543175835571 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt125
  · exact receipt126
  · exact receipt127
  · exact receipt128

private theorem receipt123 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨123, by decide⟩ cache123 partial123 = true := by
  decide +kernel

private theorem receipt122 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨122, by decide⟩ cache122 partial122 = true := by
  decide +kernel

private theorem receipt121 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨121, by decide⟩ cache121 partial121 = true := by
  decide +kernel

private theorem receipt120 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨120, by decide⟩ cache120 partial120 = true := by
  decide +kernel

private theorem receipt119 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨119, by decide⟩ cache119 partial119 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![120,121,122,123])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(270545374547731 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt120
  · exact receipt121
  · exact receipt122
  · exact receipt123

private theorem receipt118 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨118, by decide⟩ cache118 partial118 = true := by
  decide +kernel

private theorem receipt117 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨117, by decide⟩ cache117 partial117 = true := by
  decide +kernel

private theorem receipt116 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨116, by decide⟩ cache116 partial116 = true := by
  decide +kernel

private theorem receipt115 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨115, by decide⟩ cache115 partial115 = true := by
  decide +kernel

private theorem receipt114 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨114, by decide⟩ cache114 partial114 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![115,116,117,118])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(259547573259891 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt115
  · exact receipt116
  · exact receipt117
  · exact receipt118

private theorem receipt113 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨113, by decide⟩ cache113 partial113 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![114,119,124,129])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(283740587560530 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt114
  · exact receipt119
  · exact receipt124
  · exact receipt129

private theorem receipt112 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨112, by decide⟩ cache112 partial112 = true := by
  decide +kernel

private theorem receipt111 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨111, by decide⟩ cache111 partial111 = true := by
  decide +kernel

private theorem receipt110 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨110, by decide⟩ cache110 partial110 = true := by
  decide +kernel

private theorem receipt109 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨109, by decide⟩ cache109 partial109 = true := by
  decide +kernel

private theorem receipt108 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨108, by decide⟩ cache108 partial108 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![109,110,111,112])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(246350211714483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt109
  · exact receipt110
  · exact receipt111
  · exact receipt112

private theorem receipt107 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨107, by decide⟩ cache107 partial107 = true := by
  decide +kernel

private theorem receipt106 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨106, by decide⟩ cache106 partial106 = true := by
  decide +kernel

private theorem receipt105 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨105, by decide⟩ cache105 partial105 = true := by
  decide +kernel

private theorem receipt104 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨104, by decide⟩ cache104 partial104 = true := by
  decide +kernel

private theorem receipt103 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨103, by decide⟩ cache103 partial103 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![104,105,106,107])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(235352410426643 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt104
  · exact receipt105
  · exact receipt106
  · exact receipt107

private theorem receipt102 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨102, by decide⟩ cache102 partial102 = true := by
  decide +kernel

private theorem receipt101 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨101, by decide⟩ cache101 partial101 = true := by
  decide +kernel

private theorem receipt100 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨100, by decide⟩ cache100 partial100 = true := by
  decide +kernel

private theorem receipt99 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨99, by decide⟩ cache99 partial99 = true := by
  decide +kernel

private theorem receipt98 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨98, by decide⟩ cache98 partial98 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![99,100,101,102])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(224354609138803 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt99
  · exact receipt100
  · exact receipt101
  · exact receipt102

private theorem receipt97 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨97, by decide⟩ cache97 partial97 = true := by
  decide +kernel

private theorem receipt96 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨96, by decide⟩ cache96 partial96 = true := by
  decide +kernel

private theorem receipt95 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨95, by decide⟩ cache95 partial95 = true := by
  decide +kernel

private theorem receipt94 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨94, by decide⟩ cache94 partial94 = true := by
  decide +kernel

private theorem receipt93 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨93, by decide⟩ cache93 partial93 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![94,95,96,97])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(213356807850963 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt94
  · exact receipt95
  · exact receipt96
  · exact receipt97

private theorem receipt92 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨92, by decide⟩ cache92 partial92 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![93,98,103,108])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(237549822151602 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt93
  · exact receipt98
  · exact receipt103
  · exact receipt108

private theorem receipt91 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨91, by decide⟩ cache91 partial91 = true := by
  decide +kernel

private theorem receipt90 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨90, by decide⟩ cache90 partial90 = true := by
  decide +kernel

private theorem receipt89 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨89, by decide⟩ cache89 partial89 = true := by
  decide +kernel

private theorem receipt88 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨88, by decide⟩ cache88 partial88 = true := by
  decide +kernel

private theorem receipt87 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨87, by decide⟩ cache87 partial87 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![88,89,90,91])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(200159446305555 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt88
  · exact receipt89
  · exact receipt90
  · exact receipt91

private theorem receipt86 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨86, by decide⟩ cache86 partial86 = true := by
  decide +kernel

private theorem receipt85 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨85, by decide⟩ cache85 partial85 = true := by
  decide +kernel

private theorem receipt84 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨84, by decide⟩ cache84 partial84 = true := by
  decide +kernel

private theorem receipt83 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨83, by decide⟩ cache83 partial83 = true := by
  decide +kernel

private theorem receipt82 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨82, by decide⟩ cache82 partial82 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![83,84,85,86])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(189161645017715 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt83
  · exact receipt84
  · exact receipt85
  · exact receipt86

private theorem receipt81 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨81, by decide⟩ cache81 partial81 = true := by
  decide +kernel

private theorem receipt80 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨80, by decide⟩ cache80 partial80 = true := by
  decide +kernel

private theorem receipt79 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨79, by decide⟩ cache79 partial79 = true := by
  decide +kernel

private theorem receipt78 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨78, by decide⟩ cache78 partial78 = true := by
  decide +kernel

private theorem receipt77 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨77, by decide⟩ cache77 partial77 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![78,79,80,81])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(178163843729875 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt78
  · exact receipt79
  · exact receipt80
  · exact receipt81

private theorem receipt76 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨76, by decide⟩ cache76 partial76 = true := by
  decide +kernel

private theorem receipt75 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨75, by decide⟩ cache75 partial75 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![76,77,82,87])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(191359056742802 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt76
  · exact receipt77
  · exact receipt82
  · exact receipt87

private theorem receipt74 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨74, by decide⟩ cache74 partial74 = true := by
  decide +kernel

theorem receipt73 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨73, by decide⟩ cache73 partial73 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![74,75,92,113])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(248539029834065 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt74
  · exact receipt75
  · exact receipt92
  · exact receipt113


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock42
