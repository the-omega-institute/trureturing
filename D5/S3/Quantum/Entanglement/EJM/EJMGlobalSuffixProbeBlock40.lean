/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock40
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock40
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock40
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache195 : Cache :=
  step cache194 ⟨17, by decide⟩ 0
private def partial195 : Partial (Fin 20) (Fin 4) :=
  Function.update partial194 ⟨17, by decide⟩ (some 0)

private def cache196 : Cache :=
  step cache194 ⟨17, by decide⟩ 1
private def partial196 : Partial (Fin 20) (Fin 4) :=
  Function.update partial194 ⟨17, by decide⟩ (some 1)

private def cache197 : Cache :=
  step cache196 ⟨18, by decide⟩ 0
private def partial197 : Partial (Fin 20) (Fin 4) :=
  Function.update partial196 ⟨18, by decide⟩ (some 0)

private def cache198 : Cache :=
  step cache196 ⟨18, by decide⟩ 1
private def partial198 : Partial (Fin 20) (Fin 4) :=
  Function.update partial196 ⟨18, by decide⟩ (some 1)

private def cache199 : Cache :=
  step cache198 ⟨19, by decide⟩ 0
private def partial199 : Partial (Fin 20) (Fin 4) :=
  Function.update partial198 ⟨19, by decide⟩ (some 0)

private def cache200 : Cache :=
  step cache198 ⟨19, by decide⟩ 1
private def partial200 : Partial (Fin 20) (Fin 4) :=
  Function.update partial198 ⟨19, by decide⟩ (some 1)

private def cache201 : Cache :=
  step cache198 ⟨19, by decide⟩ 2
private def partial201 : Partial (Fin 20) (Fin 4) :=
  Function.update partial198 ⟨19, by decide⟩ (some 2)

private def cache202 : Cache :=
  step cache198 ⟨19, by decide⟩ 3
private def partial202 : Partial (Fin 20) (Fin 4) :=
  Function.update partial198 ⟨19, by decide⟩ (some 3)

private def cache203 : Cache :=
  step cache196 ⟨18, by decide⟩ 2
private def partial203 : Partial (Fin 20) (Fin 4) :=
  Function.update partial196 ⟨18, by decide⟩ (some 2)

private def cache204 : Cache :=
  step cache196 ⟨18, by decide⟩ 3
private def partial204 : Partial (Fin 20) (Fin 4) :=
  Function.update partial196 ⟨18, by decide⟩ (some 3)

private def cache205 : Cache :=
  step cache204 ⟨19, by decide⟩ 0
private def partial205 : Partial (Fin 20) (Fin 4) :=
  Function.update partial204 ⟨19, by decide⟩ (some 0)

private def cache206 : Cache :=
  step cache204 ⟨19, by decide⟩ 1
private def partial206 : Partial (Fin 20) (Fin 4) :=
  Function.update partial204 ⟨19, by decide⟩ (some 1)

private def cache207 : Cache :=
  step cache204 ⟨19, by decide⟩ 2
private def partial207 : Partial (Fin 20) (Fin 4) :=
  Function.update partial204 ⟨19, by decide⟩ (some 2)

private def cache208 : Cache :=
  step cache204 ⟨19, by decide⟩ 3
private def partial208 : Partial (Fin 20) (Fin 4) :=
  Function.update partial204 ⟨19, by decide⟩ (some 3)

private def cache209 : Cache :=
  step cache194 ⟨17, by decide⟩ 2
private def partial209 : Partial (Fin 20) (Fin 4) :=
  Function.update partial194 ⟨17, by decide⟩ (some 2)

private def cache210 : Cache :=
  step cache209 ⟨18, by decide⟩ 0
private def partial210 : Partial (Fin 20) (Fin 4) :=
  Function.update partial209 ⟨18, by decide⟩ (some 0)

private def cache211 : Cache :=
  step cache210 ⟨19, by decide⟩ 0
private def partial211 : Partial (Fin 20) (Fin 4) :=
  Function.update partial210 ⟨19, by decide⟩ (some 0)

private def cache212 : Cache :=
  step cache210 ⟨19, by decide⟩ 1
private def partial212 : Partial (Fin 20) (Fin 4) :=
  Function.update partial210 ⟨19, by decide⟩ (some 1)

private def cache213 : Cache :=
  step cache210 ⟨19, by decide⟩ 2
private def partial213 : Partial (Fin 20) (Fin 4) :=
  Function.update partial210 ⟨19, by decide⟩ (some 2)

private def cache214 : Cache :=
  step cache210 ⟨19, by decide⟩ 3
private def partial214 : Partial (Fin 20) (Fin 4) :=
  Function.update partial210 ⟨19, by decide⟩ (some 3)

private def cache215 : Cache :=
  step cache209 ⟨18, by decide⟩ 1
private def partial215 : Partial (Fin 20) (Fin 4) :=
  Function.update partial209 ⟨18, by decide⟩ (some 1)

private def cache216 : Cache :=
  step cache215 ⟨19, by decide⟩ 0
private def partial216 : Partial (Fin 20) (Fin 4) :=
  Function.update partial215 ⟨19, by decide⟩ (some 0)

private def cache217 : Cache :=
  step cache215 ⟨19, by decide⟩ 1
private def partial217 : Partial (Fin 20) (Fin 4) :=
  Function.update partial215 ⟨19, by decide⟩ (some 1)

private def cache218 : Cache :=
  step cache215 ⟨19, by decide⟩ 2
private def partial218 : Partial (Fin 20) (Fin 4) :=
  Function.update partial215 ⟨19, by decide⟩ (some 2)

private def cache219 : Cache :=
  step cache215 ⟨19, by decide⟩ 3
private def partial219 : Partial (Fin 20) (Fin 4) :=
  Function.update partial215 ⟨19, by decide⟩ (some 3)

private def cache220 : Cache :=
  step cache209 ⟨18, by decide⟩ 2
private def partial220 : Partial (Fin 20) (Fin 4) :=
  Function.update partial209 ⟨18, by decide⟩ (some 2)

private def cache221 : Cache :=
  step cache220 ⟨19, by decide⟩ 0
private def partial221 : Partial (Fin 20) (Fin 4) :=
  Function.update partial220 ⟨19, by decide⟩ (some 0)

private def cache222 : Cache :=
  step cache220 ⟨19, by decide⟩ 1
private def partial222 : Partial (Fin 20) (Fin 4) :=
  Function.update partial220 ⟨19, by decide⟩ (some 1)

private def cache223 : Cache :=
  step cache220 ⟨19, by decide⟩ 2
private def partial223 : Partial (Fin 20) (Fin 4) :=
  Function.update partial220 ⟨19, by decide⟩ (some 2)

private def cache224 : Cache :=
  step cache220 ⟨19, by decide⟩ 3
private def partial224 : Partial (Fin 20) (Fin 4) :=
  Function.update partial220 ⟨19, by decide⟩ (some 3)

private def cache225 : Cache :=
  step cache209 ⟨18, by decide⟩ 3
private def partial225 : Partial (Fin 20) (Fin 4) :=
  Function.update partial209 ⟨18, by decide⟩ (some 3)

private def cache226 : Cache :=
  step cache225 ⟨19, by decide⟩ 0
private def partial226 : Partial (Fin 20) (Fin 4) :=
  Function.update partial225 ⟨19, by decide⟩ (some 0)

private def cache227 : Cache :=
  step cache225 ⟨19, by decide⟩ 1
private def partial227 : Partial (Fin 20) (Fin 4) :=
  Function.update partial225 ⟨19, by decide⟩ (some 1)

private def cache228 : Cache :=
  step cache225 ⟨19, by decide⟩ 2
private def partial228 : Partial (Fin 20) (Fin 4) :=
  Function.update partial225 ⟨19, by decide⟩ (some 2)

private def cache229 : Cache :=
  step cache225 ⟨19, by decide⟩ 3
private def partial229 : Partial (Fin 20) (Fin 4) :=
  Function.update partial225 ⟨19, by decide⟩ (some 3)

private def cache230 : Cache :=
  step cache194 ⟨17, by decide⟩ 3
private def partial230 : Partial (Fin 20) (Fin 4) :=
  Function.update partial194 ⟨17, by decide⟩ (some 3)

private def cache231 : Cache :=
  step cache230 ⟨18, by decide⟩ 0
private def partial231 : Partial (Fin 20) (Fin 4) :=
  Function.update partial230 ⟨18, by decide⟩ (some 0)

private def cache232 : Cache :=
  step cache231 ⟨19, by decide⟩ 0
private def partial232 : Partial (Fin 20) (Fin 4) :=
  Function.update partial231 ⟨19, by decide⟩ (some 0)

private def cache233 : Cache :=
  step cache231 ⟨19, by decide⟩ 1
private def partial233 : Partial (Fin 20) (Fin 4) :=
  Function.update partial231 ⟨19, by decide⟩ (some 1)

private def cache234 : Cache :=
  step cache231 ⟨19, by decide⟩ 2
private def partial234 : Partial (Fin 20) (Fin 4) :=
  Function.update partial231 ⟨19, by decide⟩ (some 2)

private def cache235 : Cache :=
  step cache231 ⟨19, by decide⟩ 3
private def partial235 : Partial (Fin 20) (Fin 4) :=
  Function.update partial231 ⟨19, by decide⟩ (some 3)

private def cache236 : Cache :=
  step cache230 ⟨18, by decide⟩ 1
private def partial236 : Partial (Fin 20) (Fin 4) :=
  Function.update partial230 ⟨18, by decide⟩ (some 1)

private def cache237 : Cache :=
  step cache236 ⟨19, by decide⟩ 0
private def partial237 : Partial (Fin 20) (Fin 4) :=
  Function.update partial236 ⟨19, by decide⟩ (some 0)

private def cache238 : Cache :=
  step cache236 ⟨19, by decide⟩ 1
private def partial238 : Partial (Fin 20) (Fin 4) :=
  Function.update partial236 ⟨19, by decide⟩ (some 1)

private def cache239 : Cache :=
  step cache236 ⟨19, by decide⟩ 2
private def partial239 : Partial (Fin 20) (Fin 4) :=
  Function.update partial236 ⟨19, by decide⟩ (some 2)

private def cache240 : Cache :=
  step cache236 ⟨19, by decide⟩ 3
private def partial240 : Partial (Fin 20) (Fin 4) :=
  Function.update partial236 ⟨19, by decide⟩ (some 3)

private def cache241 : Cache :=
  step cache230 ⟨18, by decide⟩ 2
private def partial241 : Partial (Fin 20) (Fin 4) :=
  Function.update partial230 ⟨18, by decide⟩ (some 2)

private def cache242 : Cache :=
  step cache241 ⟨19, by decide⟩ 0
private def partial242 : Partial (Fin 20) (Fin 4) :=
  Function.update partial241 ⟨19, by decide⟩ (some 0)

private def cache243 : Cache :=
  step cache241 ⟨19, by decide⟩ 1
private def partial243 : Partial (Fin 20) (Fin 4) :=
  Function.update partial241 ⟨19, by decide⟩ (some 1)

private def cache244 : Cache :=
  step cache241 ⟨19, by decide⟩ 2
private def partial244 : Partial (Fin 20) (Fin 4) :=
  Function.update partial241 ⟨19, by decide⟩ (some 2)

private def cache245 : Cache :=
  step cache241 ⟨19, by decide⟩ 3
private def partial245 : Partial (Fin 20) (Fin 4) :=
  Function.update partial241 ⟨19, by decide⟩ (some 3)

private def cache246 : Cache :=
  step cache230 ⟨18, by decide⟩ 3
private def partial246 : Partial (Fin 20) (Fin 4) :=
  Function.update partial230 ⟨18, by decide⟩ (some 3)

private def cache247 : Cache :=
  step cache246 ⟨19, by decide⟩ 0
private def partial247 : Partial (Fin 20) (Fin 4) :=
  Function.update partial246 ⟨19, by decide⟩ (some 0)

private def cache248 : Cache :=
  step cache246 ⟨19, by decide⟩ 1
private def partial248 : Partial (Fin 20) (Fin 4) :=
  Function.update partial246 ⟨19, by decide⟩ (some 1)

private def cache249 : Cache :=
  step cache246 ⟨19, by decide⟩ 2
private def partial249 : Partial (Fin 20) (Fin 4) :=
  Function.update partial246 ⟨19, by decide⟩ (some 2)

private def cache250 : Cache :=
  step cache246 ⟨19, by decide⟩ 3
private def partial250 : Partial (Fin 20) (Fin 4) :=
  Function.update partial246 ⟨19, by decide⟩ (some 3)

private theorem receipt250 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨250, by decide⟩ cache250 partial250 = true := by
  decide +kernel

private theorem receipt249 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨249, by decide⟩ cache249 partial249 = true := by
  decide +kernel

private theorem receipt248 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨248, by decide⟩ cache248 partial248 = true := by
  decide +kernel

private theorem receipt247 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨247, by decide⟩ cache247 partial247 = true := by
  decide +kernel

private theorem receipt246 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨246, by decide⟩ cache246 partial246 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![247,248,249,250])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(549889527258867 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt247
  · exact receipt248
  · exact receipt249
  · exact receipt250

private theorem receipt245 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨245, by decide⟩ cache245 partial245 = true := by
  decide +kernel

private theorem receipt244 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨244, by decide⟩ cache244 partial244 = true := by
  decide +kernel

private theorem receipt243 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨243, by decide⟩ cache243 partial243 = true := by
  decide +kernel

private theorem receipt242 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨242, by decide⟩ cache242 partial242 = true := by
  decide +kernel

private theorem receipt241 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨241, by decide⟩ cache241 partial241 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![242,243,244,245])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(538891725971027 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt242
  · exact receipt243
  · exact receipt244
  · exact receipt245

private theorem receipt240 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨240, by decide⟩ cache240 partial240 = true := by
  decide +kernel

private theorem receipt239 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨239, by decide⟩ cache239 partial239 = true := by
  decide +kernel

private theorem receipt238 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨238, by decide⟩ cache238 partial238 = true := by
  decide +kernel

private theorem receipt237 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨237, by decide⟩ cache237 partial237 = true := by
  decide +kernel

private theorem receipt236 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨236, by decide⟩ cache236 partial236 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![237,238,239,240])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(527893924683187 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt237
  · exact receipt238
  · exact receipt239
  · exact receipt240

private theorem receipt235 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨235, by decide⟩ cache235 partial235 = true := by
  decide +kernel

private theorem receipt234 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨234, by decide⟩ cache234 partial234 = true := by
  decide +kernel

private theorem receipt233 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨233, by decide⟩ cache233 partial233 = true := by
  decide +kernel

private theorem receipt232 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨232, by decide⟩ cache232 partial232 = true := by
  decide +kernel

private theorem receipt231 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨231, by decide⟩ cache231 partial231 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![232,233,234,235])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(516896123395347 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt232
  · exact receipt233
  · exact receipt234
  · exact receipt235

private theorem receipt230 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨230, by decide⟩ cache230 partial230 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![231,236,241,246])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(541089137695986 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt231
  · exact receipt236
  · exact receipt241
  · exact receipt246

private theorem receipt229 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨229, by decide⟩ cache229 partial229 = true := by
  decide +kernel

private theorem receipt228 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨228, by decide⟩ cache228 partial228 = true := by
  decide +kernel

private theorem receipt227 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨227, by decide⟩ cache227 partial227 = true := by
  decide +kernel

private theorem receipt226 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨226, by decide⟩ cache226 partial226 = true := by
  decide +kernel

private theorem receipt225 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨225, by decide⟩ cache225 partial225 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![226,227,228,229])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(503698761849939 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt226
  · exact receipt227
  · exact receipt228
  · exact receipt229

private theorem receipt224 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨224, by decide⟩ cache224 partial224 = true := by
  decide +kernel

private theorem receipt223 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨223, by decide⟩ cache223 partial223 = true := by
  decide +kernel

private theorem receipt222 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨222, by decide⟩ cache222 partial222 = true := by
  decide +kernel

private theorem receipt221 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨221, by decide⟩ cache221 partial221 = true := by
  decide +kernel

private theorem receipt220 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨220, by decide⟩ cache220 partial220 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![221,222,223,224])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(492700960562099 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt221
  · exact receipt222
  · exact receipt223
  · exact receipt224

private theorem receipt219 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨219, by decide⟩ cache219 partial219 = true := by
  decide +kernel

private theorem receipt218 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨218, by decide⟩ cache218 partial218 = true := by
  decide +kernel

private theorem receipt217 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨217, by decide⟩ cache217 partial217 = true := by
  decide +kernel

private theorem receipt216 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨216, by decide⟩ cache216 partial216 = true := by
  decide +kernel

private theorem receipt215 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨215, by decide⟩ cache215 partial215 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![216,217,218,219])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(481703159274259 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt216
  · exact receipt217
  · exact receipt218
  · exact receipt219

private theorem receipt214 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨214, by decide⟩ cache214 partial214 = true := by
  decide +kernel

private theorem receipt213 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨213, by decide⟩ cache213 partial213 = true := by
  decide +kernel

private theorem receipt212 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨212, by decide⟩ cache212 partial212 = true := by
  decide +kernel

private theorem receipt211 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨211, by decide⟩ cache211 partial211 = true := by
  decide +kernel

private theorem receipt210 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨210, by decide⟩ cache210 partial210 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![211,212,213,214])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(470705357986419 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt211
  · exact receipt212
  · exact receipt213
  · exact receipt214

private theorem receipt209 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨209, by decide⟩ cache209 partial209 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![210,215,220,225])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(494898372287058 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt210
  · exact receipt215
  · exact receipt220
  · exact receipt225

private theorem receipt208 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨208, by decide⟩ cache208 partial208 = true := by
  decide +kernel

private theorem receipt207 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨207, by decide⟩ cache207 partial207 = true := by
  decide +kernel

private theorem receipt206 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨206, by decide⟩ cache206 partial206 = true := by
  decide +kernel

private theorem receipt205 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨205, by decide⟩ cache205 partial205 = true := by
  decide +kernel

private theorem receipt204 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨204, by decide⟩ cache204 partial204 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![205,206,207,208])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(457507996441011 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt205
  · exact receipt206
  · exact receipt207
  · exact receipt208

private theorem receipt203 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨203, by decide⟩ cache203 partial203 = true := by
  decide +kernel

private theorem receipt202 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨202, by decide⟩ cache202 partial202 = true := by
  decide +kernel

private theorem receipt201 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨201, by decide⟩ cache201 partial201 = true := by
  decide +kernel

private theorem receipt200 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨200, by decide⟩ cache200 partial200 = true := by
  decide +kernel

private theorem receipt199 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨199, by decide⟩ cache199 partial199 = true := by
  decide +kernel

private theorem receipt198 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨198, by decide⟩ cache198 partial198 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![199,200,201,202])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(444310634895603 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt199
  · exact receipt200
  · exact receipt201
  · exact receipt202

private theorem receipt197 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨197, by decide⟩ cache197 partial197 = true := by
  decide +kernel

private theorem receipt196 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨196, by decide⟩ cache196 partial196 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![197,198,203,204])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(448709754886322 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt197
  · exact receipt198
  · exact receipt203
  · exact receipt204

private theorem receipt195 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨195, by decide⟩ cache195 partial195 = true := by
  decide +kernel

theorem receipt194 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨194, by decide⟩ cache194 partial194 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![195,196,209,230])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(505887580493937 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt195
  · exact receipt196
  · exact receipt209
  · exact receipt230


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock40
