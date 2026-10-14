/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock13
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock13
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock13
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

theorem receipt252 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨252, by decide⟩ cache252 partial252 = true := by
  decide +kernel

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


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock13
