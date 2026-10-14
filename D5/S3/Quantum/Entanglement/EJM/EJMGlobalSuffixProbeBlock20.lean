/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock20
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock20
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock20
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache1140 : Cache :=
  step cache1139 ⟨17, by decide⟩ 0
private def partial1140 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1139 ⟨17, by decide⟩ (some 0)

private def cache1141 : Cache :=
  step cache1139 ⟨17, by decide⟩ 1
private def partial1141 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1139 ⟨17, by decide⟩ (some 1)

private def cache1142 : Cache :=
  step cache1139 ⟨17, by decide⟩ 2
private def partial1142 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1139 ⟨17, by decide⟩ (some 2)

private def cache1143 : Cache :=
  step cache1142 ⟨18, by decide⟩ 0
private def partial1143 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1142 ⟨18, by decide⟩ (some 0)

private def cache1144 : Cache :=
  step cache1142 ⟨18, by decide⟩ 1
private def partial1144 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1142 ⟨18, by decide⟩ (some 1)

private def cache1145 : Cache :=
  step cache1144 ⟨19, by decide⟩ 0
private def partial1145 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1144 ⟨19, by decide⟩ (some 0)

private def cache1146 : Cache :=
  step cache1144 ⟨19, by decide⟩ 1
private def partial1146 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1144 ⟨19, by decide⟩ (some 1)

private def cache1147 : Cache :=
  step cache1144 ⟨19, by decide⟩ 2
private def partial1147 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1144 ⟨19, by decide⟩ (some 2)

private def cache1148 : Cache :=
  step cache1144 ⟨19, by decide⟩ 3
private def partial1148 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1144 ⟨19, by decide⟩ (some 3)

private def cache1149 : Cache :=
  step cache1142 ⟨18, by decide⟩ 2
private def partial1149 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1142 ⟨18, by decide⟩ (some 2)

private def cache1150 : Cache :=
  step cache1142 ⟨18, by decide⟩ 3
private def partial1150 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1142 ⟨18, by decide⟩ (some 3)

private def cache1151 : Cache :=
  step cache1150 ⟨19, by decide⟩ 0
private def partial1151 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1150 ⟨19, by decide⟩ (some 0)

private def cache1152 : Cache :=
  step cache1150 ⟨19, by decide⟩ 1
private def partial1152 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1150 ⟨19, by decide⟩ (some 1)

private def cache1153 : Cache :=
  step cache1150 ⟨19, by decide⟩ 2
private def partial1153 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1150 ⟨19, by decide⟩ (some 2)

private def cache1154 : Cache :=
  step cache1150 ⟨19, by decide⟩ 3
private def partial1154 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1150 ⟨19, by decide⟩ (some 3)

private def cache1155 : Cache :=
  step cache1139 ⟨17, by decide⟩ 3
private def partial1155 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1139 ⟨17, by decide⟩ (some 3)

private def cache1156 : Cache :=
  step cache1155 ⟨18, by decide⟩ 0
private def partial1156 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1155 ⟨18, by decide⟩ (some 0)

private def cache1157 : Cache :=
  step cache1156 ⟨19, by decide⟩ 0
private def partial1157 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1156 ⟨19, by decide⟩ (some 0)

private def cache1158 : Cache :=
  step cache1156 ⟨19, by decide⟩ 1
private def partial1158 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1156 ⟨19, by decide⟩ (some 1)

private def cache1159 : Cache :=
  step cache1156 ⟨19, by decide⟩ 2
private def partial1159 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1156 ⟨19, by decide⟩ (some 2)

private def cache1160 : Cache :=
  step cache1156 ⟨19, by decide⟩ 3
private def partial1160 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1156 ⟨19, by decide⟩ (some 3)

private def cache1161 : Cache :=
  step cache1155 ⟨18, by decide⟩ 1
private def partial1161 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1155 ⟨18, by decide⟩ (some 1)

private def cache1162 : Cache :=
  step cache1161 ⟨19, by decide⟩ 0
private def partial1162 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1161 ⟨19, by decide⟩ (some 0)

private def cache1163 : Cache :=
  step cache1161 ⟨19, by decide⟩ 1
private def partial1163 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1161 ⟨19, by decide⟩ (some 1)

private def cache1164 : Cache :=
  step cache1161 ⟨19, by decide⟩ 2
private def partial1164 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1161 ⟨19, by decide⟩ (some 2)

private def cache1165 : Cache :=
  step cache1161 ⟨19, by decide⟩ 3
private def partial1165 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1161 ⟨19, by decide⟩ (some 3)

private def cache1166 : Cache :=
  step cache1155 ⟨18, by decide⟩ 2
private def partial1166 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1155 ⟨18, by decide⟩ (some 2)

private def cache1167 : Cache :=
  step cache1155 ⟨18, by decide⟩ 3
private def partial1167 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1155 ⟨18, by decide⟩ (some 3)

private theorem receipt1167 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1167, by decide⟩ cache1167 partial1167 = true := by
  decide +kernel

private theorem receipt1166 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1166, by decide⟩ cache1166 partial1166 = true := by
  decide +kernel

private theorem receipt1165 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1165, by decide⟩ cache1165 partial1165 = true := by
  decide +kernel

private theorem receipt1164 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1164, by decide⟩ cache1164 partial1164 = true := by
  decide +kernel

private theorem receipt1163 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1163, by decide⟩ cache1163 partial1163 = true := by
  decide +kernel

private theorem receipt1162 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1162, by decide⟩ cache1162 partial1162 = true := by
  decide +kernel

private theorem receipt1161 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1161, by decide⟩ cache1161 partial1161 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1162,1163,1164,1165])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2562487162933587 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1162
  · exact receipt1163
  · exact receipt1164
  · exact receipt1165

private theorem receipt1160 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1160, by decide⟩ cache1160 partial1160 = true := by
  decide +kernel

private theorem receipt1159 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1159, by decide⟩ cache1159 partial1159 = true := by
  decide +kernel

private theorem receipt1158 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1158, by decide⟩ cache1158 partial1158 = true := by
  decide +kernel

private theorem receipt1157 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1157, by decide⟩ cache1157 partial1157 = true := by
  decide +kernel

private theorem receipt1156 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1156, by decide⟩ cache1156 partial1156 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1157,1158,1159,1160])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2551489361645747 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1157
  · exact receipt1158
  · exact receipt1159
  · exact receipt1160

private theorem receipt1155 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1155, by decide⟩ cache1155 partial1155 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1156,1161,1166,1167])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2566886282924178 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1156
  · exact receipt1161
  · exact receipt1166
  · exact receipt1167

private theorem receipt1154 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1154, by decide⟩ cache1154 partial1154 = true := by
  decide +kernel

private theorem receipt1153 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1153, by decide⟩ cache1153 partial1153 = true := by
  decide +kernel

private theorem receipt1152 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1152, by decide⟩ cache1152 partial1152 = true := by
  decide +kernel

private theorem receipt1151 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1151, by decide⟩ cache1151 partial1151 = true := by
  decide +kernel

private theorem receipt1150 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1150, by decide⟩ cache1150 partial1150 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1151,1152,1153,1154])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2538292000100339 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1151
  · exact receipt1152
  · exact receipt1153
  · exact receipt1154

private theorem receipt1149 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1149, by decide⟩ cache1149 partial1149 = true := by
  decide +kernel

private theorem receipt1148 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1148, by decide⟩ cache1148 partial1148 = true := by
  decide +kernel

private theorem receipt1147 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1147, by decide⟩ cache1147 partial1147 = true := by
  decide +kernel

private theorem receipt1146 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1146, by decide⟩ cache1146 partial1146 = true := by
  decide +kernel

private theorem receipt1145 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1145, by decide⟩ cache1145 partial1145 = true := by
  decide +kernel

private theorem receipt1144 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1144, by decide⟩ cache1144 partial1144 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1145,1146,1147,1148])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2525094638554931 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1145
  · exact receipt1146
  · exact receipt1147
  · exact receipt1148

private theorem receipt1143 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1143, by decide⟩ cache1143 partial1143 = true := by
  decide +kernel

private theorem receipt1142 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1142, by decide⟩ cache1142 partial1142 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1143,1144,1149,1150])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2529493758545650 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1143
  · exact receipt1144
  · exact receipt1149
  · exact receipt1150

private theorem receipt1141 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1141, by decide⟩ cache1141 partial1141 = true := by
  decide +kernel

private theorem receipt1140 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1140, by decide⟩ cache1140 partial1140 = true := by
  decide +kernel

theorem receipt1139 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1139, by decide⟩ cache1139 partial1139 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1140,1141,1142,1155])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2540485116333713 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1140
  · exact receipt1141
  · exact receipt1142
  · exact receipt1155

theorem receipt1138 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1138, by decide⟩ cache1138 partial1138 = true := by
  decide +kernel

theorem receipt1137 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1137, by decide⟩ cache1137 partial1137 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock20
