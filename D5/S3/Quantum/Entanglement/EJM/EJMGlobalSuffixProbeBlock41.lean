/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock41
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock41
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock41
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)
open D5.S0.Certificates.FiniteSymmetryDAGReplay (Node)
open D5.S0.Certificates.FiniteCachedSymmetryDAGReplay
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (scale RawTree)
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeData

private def cache138 : Cache :=
  step cache137 ⟨17, by decide⟩ 0
private def partial138 : Partial (Fin 20) (Fin 4) :=
  Function.update partial137 ⟨17, by decide⟩ (some 0)

private def cache139 : Cache :=
  step cache137 ⟨17, by decide⟩ 1
private def partial139 : Partial (Fin 20) (Fin 4) :=
  Function.update partial137 ⟨17, by decide⟩ (some 1)

private def cache140 : Cache :=
  step cache139 ⟨18, by decide⟩ 0
private def partial140 : Partial (Fin 20) (Fin 4) :=
  Function.update partial139 ⟨18, by decide⟩ (some 0)

private def cache141 : Cache :=
  step cache139 ⟨18, by decide⟩ 1
private def partial141 : Partial (Fin 20) (Fin 4) :=
  Function.update partial139 ⟨18, by decide⟩ (some 1)

private def cache142 : Cache :=
  step cache141 ⟨19, by decide⟩ 0
private def partial142 : Partial (Fin 20) (Fin 4) :=
  Function.update partial141 ⟨19, by decide⟩ (some 0)

private def cache143 : Cache :=
  step cache141 ⟨19, by decide⟩ 1
private def partial143 : Partial (Fin 20) (Fin 4) :=
  Function.update partial141 ⟨19, by decide⟩ (some 1)

private def cache144 : Cache :=
  step cache141 ⟨19, by decide⟩ 2
private def partial144 : Partial (Fin 20) (Fin 4) :=
  Function.update partial141 ⟨19, by decide⟩ (some 2)

private def cache145 : Cache :=
  step cache141 ⟨19, by decide⟩ 3
private def partial145 : Partial (Fin 20) (Fin 4) :=
  Function.update partial141 ⟨19, by decide⟩ (some 3)

private def cache146 : Cache :=
  step cache139 ⟨18, by decide⟩ 2
private def partial146 : Partial (Fin 20) (Fin 4) :=
  Function.update partial139 ⟨18, by decide⟩ (some 2)

private def cache147 : Cache :=
  step cache139 ⟨18, by decide⟩ 3
private def partial147 : Partial (Fin 20) (Fin 4) :=
  Function.update partial139 ⟨18, by decide⟩ (some 3)

private def cache148 : Cache :=
  step cache147 ⟨19, by decide⟩ 0
private def partial148 : Partial (Fin 20) (Fin 4) :=
  Function.update partial147 ⟨19, by decide⟩ (some 0)

private def cache149 : Cache :=
  step cache147 ⟨19, by decide⟩ 1
private def partial149 : Partial (Fin 20) (Fin 4) :=
  Function.update partial147 ⟨19, by decide⟩ (some 1)

private def cache150 : Cache :=
  step cache147 ⟨19, by decide⟩ 2
private def partial150 : Partial (Fin 20) (Fin 4) :=
  Function.update partial147 ⟨19, by decide⟩ (some 2)

private def cache151 : Cache :=
  step cache147 ⟨19, by decide⟩ 3
private def partial151 : Partial (Fin 20) (Fin 4) :=
  Function.update partial147 ⟨19, by decide⟩ (some 3)

private def cache152 : Cache :=
  step cache137 ⟨17, by decide⟩ 2
private def partial152 : Partial (Fin 20) (Fin 4) :=
  Function.update partial137 ⟨17, by decide⟩ (some 2)

private def cache153 : Cache :=
  step cache152 ⟨18, by decide⟩ 0
private def partial153 : Partial (Fin 20) (Fin 4) :=
  Function.update partial152 ⟨18, by decide⟩ (some 0)

private def cache154 : Cache :=
  step cache153 ⟨19, by decide⟩ 0
private def partial154 : Partial (Fin 20) (Fin 4) :=
  Function.update partial153 ⟨19, by decide⟩ (some 0)

private def cache155 : Cache :=
  step cache153 ⟨19, by decide⟩ 1
private def partial155 : Partial (Fin 20) (Fin 4) :=
  Function.update partial153 ⟨19, by decide⟩ (some 1)

private def cache156 : Cache :=
  step cache153 ⟨19, by decide⟩ 2
private def partial156 : Partial (Fin 20) (Fin 4) :=
  Function.update partial153 ⟨19, by decide⟩ (some 2)

private def cache157 : Cache :=
  step cache153 ⟨19, by decide⟩ 3
private def partial157 : Partial (Fin 20) (Fin 4) :=
  Function.update partial153 ⟨19, by decide⟩ (some 3)

private def cache158 : Cache :=
  step cache152 ⟨18, by decide⟩ 1
private def partial158 : Partial (Fin 20) (Fin 4) :=
  Function.update partial152 ⟨18, by decide⟩ (some 1)

private def cache159 : Cache :=
  step cache158 ⟨19, by decide⟩ 0
private def partial159 : Partial (Fin 20) (Fin 4) :=
  Function.update partial158 ⟨19, by decide⟩ (some 0)

private def cache160 : Cache :=
  step cache158 ⟨19, by decide⟩ 1
private def partial160 : Partial (Fin 20) (Fin 4) :=
  Function.update partial158 ⟨19, by decide⟩ (some 1)

private def cache161 : Cache :=
  step cache158 ⟨19, by decide⟩ 2
private def partial161 : Partial (Fin 20) (Fin 4) :=
  Function.update partial158 ⟨19, by decide⟩ (some 2)

private def cache162 : Cache :=
  step cache158 ⟨19, by decide⟩ 3
private def partial162 : Partial (Fin 20) (Fin 4) :=
  Function.update partial158 ⟨19, by decide⟩ (some 3)

private def cache163 : Cache :=
  step cache152 ⟨18, by decide⟩ 2
private def partial163 : Partial (Fin 20) (Fin 4) :=
  Function.update partial152 ⟨18, by decide⟩ (some 2)

private def cache164 : Cache :=
  step cache163 ⟨19, by decide⟩ 0
private def partial164 : Partial (Fin 20) (Fin 4) :=
  Function.update partial163 ⟨19, by decide⟩ (some 0)

private def cache165 : Cache :=
  step cache163 ⟨19, by decide⟩ 1
private def partial165 : Partial (Fin 20) (Fin 4) :=
  Function.update partial163 ⟨19, by decide⟩ (some 1)

private def cache166 : Cache :=
  step cache163 ⟨19, by decide⟩ 2
private def partial166 : Partial (Fin 20) (Fin 4) :=
  Function.update partial163 ⟨19, by decide⟩ (some 2)

private def cache167 : Cache :=
  step cache163 ⟨19, by decide⟩ 3
private def partial167 : Partial (Fin 20) (Fin 4) :=
  Function.update partial163 ⟨19, by decide⟩ (some 3)

private def cache168 : Cache :=
  step cache152 ⟨18, by decide⟩ 3
private def partial168 : Partial (Fin 20) (Fin 4) :=
  Function.update partial152 ⟨18, by decide⟩ (some 3)

private def cache169 : Cache :=
  step cache168 ⟨19, by decide⟩ 0
private def partial169 : Partial (Fin 20) (Fin 4) :=
  Function.update partial168 ⟨19, by decide⟩ (some 0)

private def cache170 : Cache :=
  step cache168 ⟨19, by decide⟩ 1
private def partial170 : Partial (Fin 20) (Fin 4) :=
  Function.update partial168 ⟨19, by decide⟩ (some 1)

private def cache171 : Cache :=
  step cache168 ⟨19, by decide⟩ 2
private def partial171 : Partial (Fin 20) (Fin 4) :=
  Function.update partial168 ⟨19, by decide⟩ (some 2)

private def cache172 : Cache :=
  step cache168 ⟨19, by decide⟩ 3
private def partial172 : Partial (Fin 20) (Fin 4) :=
  Function.update partial168 ⟨19, by decide⟩ (some 3)

private def cache173 : Cache :=
  step cache137 ⟨17, by decide⟩ 3
private def partial173 : Partial (Fin 20) (Fin 4) :=
  Function.update partial137 ⟨17, by decide⟩ (some 3)

private def cache174 : Cache :=
  step cache173 ⟨18, by decide⟩ 0
private def partial174 : Partial (Fin 20) (Fin 4) :=
  Function.update partial173 ⟨18, by decide⟩ (some 0)

private def cache175 : Cache :=
  step cache174 ⟨19, by decide⟩ 0
private def partial175 : Partial (Fin 20) (Fin 4) :=
  Function.update partial174 ⟨19, by decide⟩ (some 0)

private def cache176 : Cache :=
  step cache174 ⟨19, by decide⟩ 1
private def partial176 : Partial (Fin 20) (Fin 4) :=
  Function.update partial174 ⟨19, by decide⟩ (some 1)

private def cache177 : Cache :=
  step cache174 ⟨19, by decide⟩ 2
private def partial177 : Partial (Fin 20) (Fin 4) :=
  Function.update partial174 ⟨19, by decide⟩ (some 2)

private def cache178 : Cache :=
  step cache174 ⟨19, by decide⟩ 3
private def partial178 : Partial (Fin 20) (Fin 4) :=
  Function.update partial174 ⟨19, by decide⟩ (some 3)

private def cache179 : Cache :=
  step cache173 ⟨18, by decide⟩ 1
private def partial179 : Partial (Fin 20) (Fin 4) :=
  Function.update partial173 ⟨18, by decide⟩ (some 1)

private def cache180 : Cache :=
  step cache179 ⟨19, by decide⟩ 0
private def partial180 : Partial (Fin 20) (Fin 4) :=
  Function.update partial179 ⟨19, by decide⟩ (some 0)

private def cache181 : Cache :=
  step cache179 ⟨19, by decide⟩ 1
private def partial181 : Partial (Fin 20) (Fin 4) :=
  Function.update partial179 ⟨19, by decide⟩ (some 1)

private def cache182 : Cache :=
  step cache179 ⟨19, by decide⟩ 2
private def partial182 : Partial (Fin 20) (Fin 4) :=
  Function.update partial179 ⟨19, by decide⟩ (some 2)

private def cache183 : Cache :=
  step cache179 ⟨19, by decide⟩ 3
private def partial183 : Partial (Fin 20) (Fin 4) :=
  Function.update partial179 ⟨19, by decide⟩ (some 3)

private def cache184 : Cache :=
  step cache173 ⟨18, by decide⟩ 2
private def partial184 : Partial (Fin 20) (Fin 4) :=
  Function.update partial173 ⟨18, by decide⟩ (some 2)

private def cache185 : Cache :=
  step cache184 ⟨19, by decide⟩ 0
private def partial185 : Partial (Fin 20) (Fin 4) :=
  Function.update partial184 ⟨19, by decide⟩ (some 0)

private def cache186 : Cache :=
  step cache184 ⟨19, by decide⟩ 1
private def partial186 : Partial (Fin 20) (Fin 4) :=
  Function.update partial184 ⟨19, by decide⟩ (some 1)

private def cache187 : Cache :=
  step cache184 ⟨19, by decide⟩ 2
private def partial187 : Partial (Fin 20) (Fin 4) :=
  Function.update partial184 ⟨19, by decide⟩ (some 2)

private def cache188 : Cache :=
  step cache184 ⟨19, by decide⟩ 3
private def partial188 : Partial (Fin 20) (Fin 4) :=
  Function.update partial184 ⟨19, by decide⟩ (some 3)

private def cache189 : Cache :=
  step cache173 ⟨18, by decide⟩ 3
private def partial189 : Partial (Fin 20) (Fin 4) :=
  Function.update partial173 ⟨18, by decide⟩ (some 3)

private def cache190 : Cache :=
  step cache189 ⟨19, by decide⟩ 0
private def partial190 : Partial (Fin 20) (Fin 4) :=
  Function.update partial189 ⟨19, by decide⟩ (some 0)

private def cache191 : Cache :=
  step cache189 ⟨19, by decide⟩ 1
private def partial191 : Partial (Fin 20) (Fin 4) :=
  Function.update partial189 ⟨19, by decide⟩ (some 1)

private def cache192 : Cache :=
  step cache189 ⟨19, by decide⟩ 2
private def partial192 : Partial (Fin 20) (Fin 4) :=
  Function.update partial189 ⟨19, by decide⟩ (some 2)

private def cache193 : Cache :=
  step cache189 ⟨19, by decide⟩ 3
private def partial193 : Partial (Fin 20) (Fin 4) :=
  Function.update partial189 ⟨19, by decide⟩ (some 3)

private theorem receipt193 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨193, by decide⟩ cache193 partial193 = true := by
  decide +kernel

private theorem receipt192 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨192, by decide⟩ cache192 partial192 = true := by
  decide +kernel

private theorem receipt191 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨191, by decide⟩ cache191 partial191 = true := by
  decide +kernel

private theorem receipt190 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨190, by decide⟩ cache190 partial190 = true := by
  decide +kernel

private theorem receipt189 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨189, by decide⟩ cache189 partial189 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![190,191,192,193])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(424514592577491 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt190
  · exact receipt191
  · exact receipt192
  · exact receipt193

private theorem receipt188 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨188, by decide⟩ cache188 partial188 = true := by
  decide +kernel

private theorem receipt187 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨187, by decide⟩ cache187 partial187 = true := by
  decide +kernel

private theorem receipt186 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨186, by decide⟩ cache186 partial186 = true := by
  decide +kernel

private theorem receipt185 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨185, by decide⟩ cache185 partial185 = true := by
  decide +kernel

private theorem receipt184 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨184, by decide⟩ cache184 partial184 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![185,186,187,188])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(413516791289651 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt185
  · exact receipt186
  · exact receipt187
  · exact receipt188

private theorem receipt183 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨183, by decide⟩ cache183 partial183 = true := by
  decide +kernel

private theorem receipt182 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨182, by decide⟩ cache182 partial182 = true := by
  decide +kernel

private theorem receipt181 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨181, by decide⟩ cache181 partial181 = true := by
  decide +kernel

private theorem receipt180 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨180, by decide⟩ cache180 partial180 = true := by
  decide +kernel

private theorem receipt179 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨179, by decide⟩ cache179 partial179 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![180,181,182,183])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(402518990001811 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt180
  · exact receipt181
  · exact receipt182
  · exact receipt183

private theorem receipt178 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨178, by decide⟩ cache178 partial178 = true := by
  decide +kernel

private theorem receipt177 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨177, by decide⟩ cache177 partial177 = true := by
  decide +kernel

private theorem receipt176 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨176, by decide⟩ cache176 partial176 = true := by
  decide +kernel

private theorem receipt175 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨175, by decide⟩ cache175 partial175 = true := by
  decide +kernel

private theorem receipt174 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨174, by decide⟩ cache174 partial174 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![175,176,177,178])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(391521188713971 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt175
  · exact receipt176
  · exact receipt177
  · exact receipt178

private theorem receipt173 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨173, by decide⟩ cache173 partial173 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![174,179,184,189])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(415714203014610 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt174
  · exact receipt179
  · exact receipt184
  · exact receipt189

private theorem receipt172 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨172, by decide⟩ cache172 partial172 = true := by
  decide +kernel

private theorem receipt171 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨171, by decide⟩ cache171 partial171 = true := by
  decide +kernel

private theorem receipt170 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨170, by decide⟩ cache170 partial170 = true := by
  decide +kernel

private theorem receipt169 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨169, by decide⟩ cache169 partial169 = true := by
  decide +kernel

private theorem receipt168 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨168, by decide⟩ cache168 partial168 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![169,170,171,172])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(378323827168563 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt169
  · exact receipt170
  · exact receipt171
  · exact receipt172

private theorem receipt167 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨167, by decide⟩ cache167 partial167 = true := by
  decide +kernel

private theorem receipt166 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨166, by decide⟩ cache166 partial166 = true := by
  decide +kernel

private theorem receipt165 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨165, by decide⟩ cache165 partial165 = true := by
  decide +kernel

private theorem receipt164 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨164, by decide⟩ cache164 partial164 = true := by
  decide +kernel

private theorem receipt163 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨163, by decide⟩ cache163 partial163 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![164,165,166,167])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(367326025880723 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt164
  · exact receipt165
  · exact receipt166
  · exact receipt167

private theorem receipt162 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨162, by decide⟩ cache162 partial162 = true := by
  decide +kernel

private theorem receipt161 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨161, by decide⟩ cache161 partial161 = true := by
  decide +kernel

private theorem receipt160 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨160, by decide⟩ cache160 partial160 = true := by
  decide +kernel

private theorem receipt159 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨159, by decide⟩ cache159 partial159 = true := by
  decide +kernel

private theorem receipt158 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨158, by decide⟩ cache158 partial158 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![159,160,161,162])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(356328224592883 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt159
  · exact receipt160
  · exact receipt161
  · exact receipt162

private theorem receipt157 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨157, by decide⟩ cache157 partial157 = true := by
  decide +kernel

private theorem receipt156 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨156, by decide⟩ cache156 partial156 = true := by
  decide +kernel

private theorem receipt155 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨155, by decide⟩ cache155 partial155 = true := by
  decide +kernel

private theorem receipt154 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨154, by decide⟩ cache154 partial154 = true := by
  decide +kernel

private theorem receipt153 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨153, by decide⟩ cache153 partial153 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![154,155,156,157])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(345330423305043 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt154
  · exact receipt155
  · exact receipt156
  · exact receipt157

private theorem receipt152 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨152, by decide⟩ cache152 partial152 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![153,158,163,168])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(369523437605682 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt153
  · exact receipt158
  · exact receipt163
  · exact receipt168

private theorem receipt151 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨151, by decide⟩ cache151 partial151 = true := by
  decide +kernel

private theorem receipt150 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨150, by decide⟩ cache150 partial150 = true := by
  decide +kernel

private theorem receipt149 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨149, by decide⟩ cache149 partial149 = true := by
  decide +kernel

private theorem receipt148 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨148, by decide⟩ cache148 partial148 = true := by
  decide +kernel

private theorem receipt147 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨147, by decide⟩ cache147 partial147 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![148,149,150,151])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(332133061759635 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt148
  · exact receipt149
  · exact receipt150
  · exact receipt151

private theorem receipt146 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨146, by decide⟩ cache146 partial146 = true := by
  decide +kernel

private theorem receipt145 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨145, by decide⟩ cache145 partial145 = true := by
  decide +kernel

private theorem receipt144 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨144, by decide⟩ cache144 partial144 = true := by
  decide +kernel

private theorem receipt143 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨143, by decide⟩ cache143 partial143 = true := by
  decide +kernel

private theorem receipt142 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨142, by decide⟩ cache142 partial142 = true := by
  decide +kernel

private theorem receipt141 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨141, by decide⟩ cache141 partial141 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![142,143,144,145])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(318935700214227 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt142
  · exact receipt143
  · exact receipt144
  · exact receipt145

private theorem receipt140 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨140, by decide⟩ cache140 partial140 = true := by
  decide +kernel

private theorem receipt139 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨139, by decide⟩ cache139 partial139 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![140,141,146,147])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(323334820204946 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt140
  · exact receipt141
  · exact receipt146
  · exact receipt147

private theorem receipt138 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨138, by decide⟩ cache138 partial138 = true := by
  decide +kernel

theorem receipt137 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨137, by decide⟩ cache137 partial137 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![138,139,152,173])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(380512645812561 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt138
  · exact receipt139
  · exact receipt152
  · exact receipt173

theorem receipt136 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨136, by decide⟩ cache136 partial136 = true := by
  decide +kernel

theorem receipt135 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨135, by decide⟩ cache135 partial135 = true := by
  decide +kernel


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock41
