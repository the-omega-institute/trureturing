/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock21
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock21
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock21
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1092 : Cache :=
  step cache1091 ⟨17, by decide⟩ 0
private def partial1092 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1091 ⟨17, by decide⟩ (some 0)

private def cache1093 : Cache :=
  step cache1091 ⟨17, by decide⟩ 1
private def partial1093 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1091 ⟨17, by decide⟩ (some 1)

private def cache1094 : Cache :=
  step cache1093 ⟨18, by decide⟩ 0
private def partial1094 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1093 ⟨18, by decide⟩ (some 0)

private def cache1095 : Cache :=
  step cache1093 ⟨18, by decide⟩ 1
private def partial1095 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1093 ⟨18, by decide⟩ (some 1)

private def cache1096 : Cache :=
  step cache1095 ⟨19, by decide⟩ 0
private def partial1096 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1095 ⟨19, by decide⟩ (some 0)

private def cache1097 : Cache :=
  step cache1095 ⟨19, by decide⟩ 1
private def partial1097 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1095 ⟨19, by decide⟩ (some 1)

private def cache1098 : Cache :=
  step cache1095 ⟨19, by decide⟩ 2
private def partial1098 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1095 ⟨19, by decide⟩ (some 2)

private def cache1099 : Cache :=
  step cache1095 ⟨19, by decide⟩ 3
private def partial1099 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1095 ⟨19, by decide⟩ (some 3)

private def cache1100 : Cache :=
  step cache1093 ⟨18, by decide⟩ 2
private def partial1100 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1093 ⟨18, by decide⟩ (some 2)

private def cache1101 : Cache :=
  step cache1093 ⟨18, by decide⟩ 3
private def partial1101 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1093 ⟨18, by decide⟩ (some 3)

private def cache1102 : Cache :=
  step cache1091 ⟨17, by decide⟩ 2
private def partial1102 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1091 ⟨17, by decide⟩ (some 2)

private def cache1103 : Cache :=
  step cache1102 ⟨18, by decide⟩ 0
private def partial1103 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1102 ⟨18, by decide⟩ (some 0)

private def cache1104 : Cache :=
  step cache1103 ⟨19, by decide⟩ 0
private def partial1104 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1103 ⟨19, by decide⟩ (some 0)

private def cache1105 : Cache :=
  step cache1103 ⟨19, by decide⟩ 1
private def partial1105 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1103 ⟨19, by decide⟩ (some 1)

private def cache1106 : Cache :=
  step cache1103 ⟨19, by decide⟩ 2
private def partial1106 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1103 ⟨19, by decide⟩ (some 2)

private def cache1107 : Cache :=
  step cache1103 ⟨19, by decide⟩ 3
private def partial1107 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1103 ⟨19, by decide⟩ (some 3)

private def cache1108 : Cache :=
  step cache1102 ⟨18, by decide⟩ 1
private def partial1108 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1102 ⟨18, by decide⟩ (some 1)

private def cache1109 : Cache :=
  step cache1108 ⟨19, by decide⟩ 0
private def partial1109 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1108 ⟨19, by decide⟩ (some 0)

private def cache1110 : Cache :=
  step cache1108 ⟨19, by decide⟩ 1
private def partial1110 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1108 ⟨19, by decide⟩ (some 1)

private def cache1111 : Cache :=
  step cache1108 ⟨19, by decide⟩ 2
private def partial1111 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1108 ⟨19, by decide⟩ (some 2)

private def cache1112 : Cache :=
  step cache1108 ⟨19, by decide⟩ 3
private def partial1112 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1108 ⟨19, by decide⟩ (some 3)

private def cache1113 : Cache :=
  step cache1102 ⟨18, by decide⟩ 2
private def partial1113 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1102 ⟨18, by decide⟩ (some 2)

private def cache1114 : Cache :=
  step cache1113 ⟨19, by decide⟩ 0
private def partial1114 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1113 ⟨19, by decide⟩ (some 0)

private def cache1115 : Cache :=
  step cache1113 ⟨19, by decide⟩ 1
private def partial1115 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1113 ⟨19, by decide⟩ (some 1)

private def cache1116 : Cache :=
  step cache1113 ⟨19, by decide⟩ 2
private def partial1116 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1113 ⟨19, by decide⟩ (some 2)

private def cache1117 : Cache :=
  step cache1113 ⟨19, by decide⟩ 3
private def partial1117 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1113 ⟨19, by decide⟩ (some 3)

private def cache1118 : Cache :=
  step cache1102 ⟨18, by decide⟩ 3
private def partial1118 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1102 ⟨18, by decide⟩ (some 3)

private def cache1119 : Cache :=
  step cache1118 ⟨19, by decide⟩ 0
private def partial1119 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1118 ⟨19, by decide⟩ (some 0)

private def cache1120 : Cache :=
  step cache1118 ⟨19, by decide⟩ 1
private def partial1120 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1118 ⟨19, by decide⟩ (some 1)

private def cache1121 : Cache :=
  step cache1118 ⟨19, by decide⟩ 2
private def partial1121 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1118 ⟨19, by decide⟩ (some 2)

private def cache1122 : Cache :=
  step cache1118 ⟨19, by decide⟩ 3
private def partial1122 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1118 ⟨19, by decide⟩ (some 3)

private def cache1123 : Cache :=
  step cache1091 ⟨17, by decide⟩ 3
private def partial1123 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1091 ⟨17, by decide⟩ (some 3)

private def cache1124 : Cache :=
  step cache1123 ⟨18, by decide⟩ 0
private def partial1124 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1123 ⟨18, by decide⟩ (some 0)

private def cache1125 : Cache :=
  step cache1124 ⟨19, by decide⟩ 0
private def partial1125 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1124 ⟨19, by decide⟩ (some 0)

private def cache1126 : Cache :=
  step cache1124 ⟨19, by decide⟩ 1
private def partial1126 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1124 ⟨19, by decide⟩ (some 1)

private def cache1127 : Cache :=
  step cache1124 ⟨19, by decide⟩ 2
private def partial1127 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1124 ⟨19, by decide⟩ (some 2)

private def cache1128 : Cache :=
  step cache1124 ⟨19, by decide⟩ 3
private def partial1128 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1124 ⟨19, by decide⟩ (some 3)

private def cache1129 : Cache :=
  step cache1123 ⟨18, by decide⟩ 1
private def partial1129 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1123 ⟨18, by decide⟩ (some 1)

private def cache1130 : Cache :=
  step cache1129 ⟨19, by decide⟩ 0
private def partial1130 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1129 ⟨19, by decide⟩ (some 0)

private def cache1131 : Cache :=
  step cache1129 ⟨19, by decide⟩ 1
private def partial1131 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1129 ⟨19, by decide⟩ (some 1)

private def cache1132 : Cache :=
  step cache1129 ⟨19, by decide⟩ 2
private def partial1132 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1129 ⟨19, by decide⟩ (some 2)

private def cache1133 : Cache :=
  step cache1129 ⟨19, by decide⟩ 3
private def partial1133 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1129 ⟨19, by decide⟩ (some 3)

private def cache1134 : Cache :=
  step cache1123 ⟨18, by decide⟩ 2
private def partial1134 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1123 ⟨18, by decide⟩ (some 2)

private def cache1135 : Cache :=
  step cache1123 ⟨18, by decide⟩ 3
private def partial1135 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1123 ⟨18, by decide⟩ (some 3)

private theorem receipt1135 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1135, by decide⟩ cache1135 partial1135 = true := by
  decide +kernel

private theorem receipt1134 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1134, by decide⟩ cache1134 partial1134 = true := by
  decide +kernel

private theorem receipt1133 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1133, by decide⟩ cache1133 partial1133 = true := by
  decide +kernel

private theorem receipt1132 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1132, by decide⟩ cache1132 partial1132 = true := by
  decide +kernel

private theorem receipt1131 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1131, by decide⟩ cache1131 partial1131 = true := by
  decide +kernel

private theorem receipt1130 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1130, by decide⟩ cache1130 partial1130 = true := by
  decide +kernel

private theorem receipt1129 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1129, by decide⟩ cache1129 partial1129 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1130,1131,1132,1133])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2492101234691411 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1130
  · exact receipt1131
  · exact receipt1132
  · exact receipt1133

private theorem receipt1128 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1128, by decide⟩ cache1128 partial1128 = true := by
  decide +kernel

private theorem receipt1127 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1127, by decide⟩ cache1127 partial1127 = true := by
  decide +kernel

private theorem receipt1126 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1126, by decide⟩ cache1126 partial1126 = true := by
  decide +kernel

private theorem receipt1125 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1125, by decide⟩ cache1125 partial1125 = true := by
  decide +kernel

private theorem receipt1124 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1124, by decide⟩ cache1124 partial1124 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1125,1126,1127,1128])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2481103433403571 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1125
  · exact receipt1126
  · exact receipt1127
  · exact receipt1128

private theorem receipt1123 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1123, by decide⟩ cache1123 partial1123 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1124,1129,1134,1135])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2496500354682002 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1124
  · exact receipt1129
  · exact receipt1134
  · exact receipt1135

private theorem receipt1122 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1122, by decide⟩ cache1122 partial1122 = true := by
  decide +kernel

private theorem receipt1121 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1121, by decide⟩ cache1121 partial1121 = true := by
  decide +kernel

private theorem receipt1120 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1120, by decide⟩ cache1120 partial1120 = true := by
  decide +kernel

private theorem receipt1119 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1119, by decide⟩ cache1119 partial1119 = true := by
  decide +kernel

private theorem receipt1118 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1118, by decide⟩ cache1118 partial1118 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1119,1120,1121,1122])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2467906071858163 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1119
  · exact receipt1120
  · exact receipt1121
  · exact receipt1122

private theorem receipt1117 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1117, by decide⟩ cache1117 partial1117 = true := by
  decide +kernel

private theorem receipt1116 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1116, by decide⟩ cache1116 partial1116 = true := by
  decide +kernel

private theorem receipt1115 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1115, by decide⟩ cache1115 partial1115 = true := by
  decide +kernel

private theorem receipt1114 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1114, by decide⟩ cache1114 partial1114 = true := by
  decide +kernel

private theorem receipt1113 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1113, by decide⟩ cache1113 partial1113 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1114,1115,1116,1117])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2456908270570323 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1114
  · exact receipt1115
  · exact receipt1116
  · exact receipt1117

private theorem receipt1112 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1112, by decide⟩ cache1112 partial1112 = true := by
  decide +kernel

private theorem receipt1111 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1111, by decide⟩ cache1111 partial1111 = true := by
  decide +kernel

private theorem receipt1110 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1110, by decide⟩ cache1110 partial1110 = true := by
  decide +kernel

private theorem receipt1109 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1109, by decide⟩ cache1109 partial1109 = true := by
  decide +kernel

private theorem receipt1108 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1108, by decide⟩ cache1108 partial1108 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1109,1110,1111,1112])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2445910469282483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1109
  · exact receipt1110
  · exact receipt1111
  · exact receipt1112

private theorem receipt1107 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1107, by decide⟩ cache1107 partial1107 = true := by
  decide +kernel

private theorem receipt1106 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1106, by decide⟩ cache1106 partial1106 = true := by
  decide +kernel

private theorem receipt1105 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1105, by decide⟩ cache1105 partial1105 = true := by
  decide +kernel

private theorem receipt1104 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1104, by decide⟩ cache1104 partial1104 = true := by
  decide +kernel

private theorem receipt1103 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1103, by decide⟩ cache1103 partial1103 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1104,1105,1106,1107])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2434912667994643 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1104
  · exact receipt1105
  · exact receipt1106
  · exact receipt1107

private theorem receipt1102 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1102, by decide⟩ cache1102 partial1102 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1103,1108,1113,1118])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2459105682295282 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1103
  · exact receipt1108
  · exact receipt1113
  · exact receipt1118

private theorem receipt1101 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1101, by decide⟩ cache1101 partial1101 = true := by
  decide +kernel

private theorem receipt1100 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1100, by decide⟩ cache1100 partial1100 = true := by
  decide +kernel

private theorem receipt1099 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1099, by decide⟩ cache1099 partial1099 = true := by
  decide +kernel

private theorem receipt1098 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1098, by decide⟩ cache1098 partial1098 = true := by
  decide +kernel

private theorem receipt1097 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1097, by decide⟩ cache1097 partial1097 = true := by
  decide +kernel

private theorem receipt1096 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1096, by decide⟩ cache1096 partial1096 = true := by
  decide +kernel

private theorem receipt1095 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1095, by decide⟩ cache1095 partial1095 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1096,1097,1098,1099])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2417316185934099 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1096
  · exact receipt1097
  · exact receipt1098
  · exact receipt1099

private theorem receipt1094 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1094, by decide⟩ cache1094 partial1094 = true := by
  decide +kernel

private theorem receipt1093 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1093, by decide⟩ cache1093 partial1093 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1094,1095,1100,1101])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2421715305924818 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1094
  · exact receipt1095
  · exact receipt1100
  · exact receipt1101

private theorem receipt1092 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1092, by decide⟩ cache1092 partial1092 = true := by
  decide +kernel

theorem receipt1091 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1091, by decide⟩ cache1091 partial1091 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1092,1093,1102,1123])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2470094891026577 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1092
  · exact receipt1093
  · exact receipt1102
  · exact receipt1123


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock21
