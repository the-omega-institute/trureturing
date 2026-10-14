/- GID: D5/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock7
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMGlobalSuffixProbeBlock7
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

namespace D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock7
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

private def cache1169 : Cache :=
  step cache1168 ⟨17, by decide⟩ 0
private def partial1169 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1168 ⟨17, by decide⟩ (some 0)

private def cache1170 : Cache :=
  step cache1168 ⟨17, by decide⟩ 1
private def partial1170 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1168 ⟨17, by decide⟩ (some 1)

private def cache1171 : Cache :=
  step cache1170 ⟨18, by decide⟩ 0
private def partial1171 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1170 ⟨18, by decide⟩ (some 0)

private def cache1172 : Cache :=
  step cache1170 ⟨18, by decide⟩ 1
private def partial1172 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1170 ⟨18, by decide⟩ (some 1)

private def cache1173 : Cache :=
  step cache1172 ⟨19, by decide⟩ 0
private def partial1173 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1172 ⟨19, by decide⟩ (some 0)

private def cache1174 : Cache :=
  step cache1172 ⟨19, by decide⟩ 1
private def partial1174 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1172 ⟨19, by decide⟩ (some 1)

private def cache1175 : Cache :=
  step cache1172 ⟨19, by decide⟩ 2
private def partial1175 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1172 ⟨19, by decide⟩ (some 2)

private def cache1176 : Cache :=
  step cache1172 ⟨19, by decide⟩ 3
private def partial1176 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1172 ⟨19, by decide⟩ (some 3)

private def cache1177 : Cache :=
  step cache1170 ⟨18, by decide⟩ 2
private def partial1177 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1170 ⟨18, by decide⟩ (some 2)

private def cache1178 : Cache :=
  step cache1170 ⟨18, by decide⟩ 3
private def partial1178 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1170 ⟨18, by decide⟩ (some 3)

private def cache1179 : Cache :=
  step cache1168 ⟨17, by decide⟩ 2
private def partial1179 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1168 ⟨17, by decide⟩ (some 2)

private def cache1180 : Cache :=
  step cache1179 ⟨18, by decide⟩ 0
private def partial1180 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1179 ⟨18, by decide⟩ (some 0)

private def cache1181 : Cache :=
  step cache1180 ⟨19, by decide⟩ 0
private def partial1181 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1180 ⟨19, by decide⟩ (some 0)

private def cache1182 : Cache :=
  step cache1180 ⟨19, by decide⟩ 1
private def partial1182 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1180 ⟨19, by decide⟩ (some 1)

private def cache1183 : Cache :=
  step cache1180 ⟨19, by decide⟩ 2
private def partial1183 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1180 ⟨19, by decide⟩ (some 2)

private def cache1184 : Cache :=
  step cache1180 ⟨19, by decide⟩ 3
private def partial1184 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1180 ⟨19, by decide⟩ (some 3)

private def cache1185 : Cache :=
  step cache1179 ⟨18, by decide⟩ 1
private def partial1185 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1179 ⟨18, by decide⟩ (some 1)

private def cache1186 : Cache :=
  step cache1185 ⟨19, by decide⟩ 0
private def partial1186 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1185 ⟨19, by decide⟩ (some 0)

private def cache1187 : Cache :=
  step cache1185 ⟨19, by decide⟩ 1
private def partial1187 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1185 ⟨19, by decide⟩ (some 1)

private def cache1188 : Cache :=
  step cache1185 ⟨19, by decide⟩ 2
private def partial1188 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1185 ⟨19, by decide⟩ (some 2)

private def cache1189 : Cache :=
  step cache1185 ⟨19, by decide⟩ 3
private def partial1189 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1185 ⟨19, by decide⟩ (some 3)

private def cache1190 : Cache :=
  step cache1179 ⟨18, by decide⟩ 2
private def partial1190 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1179 ⟨18, by decide⟩ (some 2)

private def cache1191 : Cache :=
  step cache1179 ⟨18, by decide⟩ 3
private def partial1191 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1179 ⟨18, by decide⟩ (some 3)

private def cache1192 : Cache :=
  step cache1191 ⟨19, by decide⟩ 0
private def partial1192 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1191 ⟨19, by decide⟩ (some 0)

private def cache1193 : Cache :=
  step cache1191 ⟨19, by decide⟩ 1
private def partial1193 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1191 ⟨19, by decide⟩ (some 1)

private def cache1194 : Cache :=
  step cache1191 ⟨19, by decide⟩ 2
private def partial1194 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1191 ⟨19, by decide⟩ (some 2)

private def cache1195 : Cache :=
  step cache1191 ⟨19, by decide⟩ 3
private def partial1195 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1191 ⟨19, by decide⟩ (some 3)

private def cache1196 : Cache :=
  step cache1168 ⟨17, by decide⟩ 3
private def partial1196 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1168 ⟨17, by decide⟩ (some 3)

private def cache1197 : Cache :=
  step cache1196 ⟨18, by decide⟩ 0
private def partial1197 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1196 ⟨18, by decide⟩ (some 0)

private def cache1198 : Cache :=
  step cache1197 ⟨19, by decide⟩ 0
private def partial1198 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1197 ⟨19, by decide⟩ (some 0)

private def cache1199 : Cache :=
  step cache1197 ⟨19, by decide⟩ 1
private def partial1199 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1197 ⟨19, by decide⟩ (some 1)

private def cache1200 : Cache :=
  step cache1197 ⟨19, by decide⟩ 2
private def partial1200 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1197 ⟨19, by decide⟩ (some 2)

private def cache1201 : Cache :=
  step cache1197 ⟨19, by decide⟩ 3
private def partial1201 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1197 ⟨19, by decide⟩ (some 3)

private def cache1202 : Cache :=
  step cache1196 ⟨18, by decide⟩ 1
private def partial1202 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1196 ⟨18, by decide⟩ (some 1)

private def cache1203 : Cache :=
  step cache1202 ⟨19, by decide⟩ 0
private def partial1203 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1202 ⟨19, by decide⟩ (some 0)

private def cache1204 : Cache :=
  step cache1202 ⟨19, by decide⟩ 1
private def partial1204 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1202 ⟨19, by decide⟩ (some 1)

private def cache1205 : Cache :=
  step cache1202 ⟨19, by decide⟩ 2
private def partial1205 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1202 ⟨19, by decide⟩ (some 2)

private def cache1206 : Cache :=
  step cache1202 ⟨19, by decide⟩ 3
private def partial1206 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1202 ⟨19, by decide⟩ (some 3)

private def cache1207 : Cache :=
  step cache1196 ⟨18, by decide⟩ 2
private def partial1207 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1196 ⟨18, by decide⟩ (some 2)

private def cache1208 : Cache :=
  step cache1196 ⟨18, by decide⟩ 3
private def partial1208 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1196 ⟨18, by decide⟩ (some 3)

private def cache1216 : Cache :=
  step cache1215 ⟨17, by decide⟩ 0
private def partial1216 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1215 ⟨17, by decide⟩ (some 0)

private def cache1217 : Cache :=
  step cache1215 ⟨17, by decide⟩ 1
private def partial1217 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1215 ⟨17, by decide⟩ (some 1)

private def cache1218 : Cache :=
  step cache1215 ⟨17, by decide⟩ 2
private def partial1218 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1215 ⟨17, by decide⟩ (some 2)

private def cache1219 : Cache :=
  step cache1218 ⟨18, by decide⟩ 0
private def partial1219 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1218 ⟨18, by decide⟩ (some 0)

private def cache1220 : Cache :=
  step cache1218 ⟨18, by decide⟩ 1
private def partial1220 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1218 ⟨18, by decide⟩ (some 1)

private def cache1221 : Cache :=
  step cache1218 ⟨18, by decide⟩ 2
private def partial1221 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1218 ⟨18, by decide⟩ (some 2)

private def cache1222 : Cache :=
  step cache1221 ⟨19, by decide⟩ 0
private def partial1222 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1221 ⟨19, by decide⟩ (some 0)

private def cache1223 : Cache :=
  step cache1221 ⟨19, by decide⟩ 1
private def partial1223 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1221 ⟨19, by decide⟩ (some 1)

private def cache1224 : Cache :=
  step cache1221 ⟨19, by decide⟩ 2
private def partial1224 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1221 ⟨19, by decide⟩ (some 2)

private def cache1225 : Cache :=
  step cache1221 ⟨19, by decide⟩ 3
private def partial1225 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1221 ⟨19, by decide⟩ (some 3)

private def cache1226 : Cache :=
  step cache1218 ⟨18, by decide⟩ 3
private def partial1226 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1218 ⟨18, by decide⟩ (some 3)

private def cache1227 : Cache :=
  step cache1215 ⟨17, by decide⟩ 3
private def partial1227 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1215 ⟨17, by decide⟩ (some 3)

private def cache1228 : Cache :=
  step cache1227 ⟨18, by decide⟩ 0
private def partial1228 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1227 ⟨18, by decide⟩ (some 0)

private def cache1229 : Cache :=
  step cache1228 ⟨19, by decide⟩ 0
private def partial1229 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1228 ⟨19, by decide⟩ (some 0)

private def cache1230 : Cache :=
  step cache1228 ⟨19, by decide⟩ 1
private def partial1230 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1228 ⟨19, by decide⟩ (some 1)

private def cache1231 : Cache :=
  step cache1228 ⟨19, by decide⟩ 2
private def partial1231 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1228 ⟨19, by decide⟩ (some 2)

private def cache1232 : Cache :=
  step cache1228 ⟨19, by decide⟩ 3
private def partial1232 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1228 ⟨19, by decide⟩ (some 3)

private def cache1233 : Cache :=
  step cache1227 ⟨18, by decide⟩ 1
private def partial1233 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1227 ⟨18, by decide⟩ (some 1)

private def cache1234 : Cache :=
  step cache1233 ⟨19, by decide⟩ 0
private def partial1234 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1233 ⟨19, by decide⟩ (some 0)

private def cache1235 : Cache :=
  step cache1233 ⟨19, by decide⟩ 1
private def partial1235 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1233 ⟨19, by decide⟩ (some 1)

private def cache1236 : Cache :=
  step cache1233 ⟨19, by decide⟩ 2
private def partial1236 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1233 ⟨19, by decide⟩ (some 2)

private def cache1237 : Cache :=
  step cache1233 ⟨19, by decide⟩ 3
private def partial1237 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1233 ⟨19, by decide⟩ (some 3)

private def cache1238 : Cache :=
  step cache1227 ⟨18, by decide⟩ 2
private def partial1238 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1227 ⟨18, by decide⟩ (some 2)

private def cache1239 : Cache :=
  step cache1227 ⟨18, by decide⟩ 3
private def partial1239 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1227 ⟨18, by decide⟩ (some 3)

private def cache1241 : Cache :=
  step cache1240 ⟨17, by decide⟩ 0
private def partial1241 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 0)

private def cache1242 : Cache :=
  step cache1240 ⟨17, by decide⟩ 1
private def partial1242 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 1)

private def cache1243 : Cache :=
  step cache1242 ⟨18, by decide⟩ 0
private def partial1243 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 0)

private def cache1244 : Cache :=
  step cache1242 ⟨18, by decide⟩ 1
private def partial1244 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 1)

private def cache1245 : Cache :=
  step cache1244 ⟨19, by decide⟩ 0
private def partial1245 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 0)

private def cache1246 : Cache :=
  step cache1244 ⟨19, by decide⟩ 1
private def partial1246 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 1)

private def cache1247 : Cache :=
  step cache1244 ⟨19, by decide⟩ 2
private def partial1247 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 2)

private def cache1248 : Cache :=
  step cache1244 ⟨19, by decide⟩ 3
private def partial1248 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1244 ⟨19, by decide⟩ (some 3)

private def cache1249 : Cache :=
  step cache1242 ⟨18, by decide⟩ 2
private def partial1249 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 2)

private def cache1250 : Cache :=
  step cache1242 ⟨18, by decide⟩ 3
private def partial1250 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1242 ⟨18, by decide⟩ (some 3)

private def cache1251 : Cache :=
  step cache1250 ⟨19, by decide⟩ 0
private def partial1251 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 0)

private def cache1252 : Cache :=
  step cache1250 ⟨19, by decide⟩ 1
private def partial1252 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 1)

private def cache1253 : Cache :=
  step cache1250 ⟨19, by decide⟩ 2
private def partial1253 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 2)

private def cache1254 : Cache :=
  step cache1250 ⟨19, by decide⟩ 3
private def partial1254 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1250 ⟨19, by decide⟩ (some 3)

private def cache1255 : Cache :=
  step cache1240 ⟨17, by decide⟩ 2
private def partial1255 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 2)

private def cache1256 : Cache :=
  step cache1255 ⟨18, by decide⟩ 0
private def partial1256 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 0)

private def cache1257 : Cache :=
  step cache1256 ⟨19, by decide⟩ 0
private def partial1257 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 0)

private def cache1258 : Cache :=
  step cache1256 ⟨19, by decide⟩ 1
private def partial1258 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 1)

private def cache1259 : Cache :=
  step cache1256 ⟨19, by decide⟩ 2
private def partial1259 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 2)

private def cache1260 : Cache :=
  step cache1256 ⟨19, by decide⟩ 3
private def partial1260 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1256 ⟨19, by decide⟩ (some 3)

private def cache1261 : Cache :=
  step cache1255 ⟨18, by decide⟩ 1
private def partial1261 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 1)

private def cache1262 : Cache :=
  step cache1261 ⟨19, by decide⟩ 0
private def partial1262 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 0)

private def cache1263 : Cache :=
  step cache1261 ⟨19, by decide⟩ 1
private def partial1263 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 1)

private def cache1264 : Cache :=
  step cache1261 ⟨19, by decide⟩ 2
private def partial1264 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 2)

private def cache1265 : Cache :=
  step cache1261 ⟨19, by decide⟩ 3
private def partial1265 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1261 ⟨19, by decide⟩ (some 3)

private def cache1266 : Cache :=
  step cache1255 ⟨18, by decide⟩ 2
private def partial1266 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 2)

private def cache1267 : Cache :=
  step cache1266 ⟨19, by decide⟩ 0
private def partial1267 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 0)

private def cache1268 : Cache :=
  step cache1266 ⟨19, by decide⟩ 1
private def partial1268 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 1)

private def cache1269 : Cache :=
  step cache1266 ⟨19, by decide⟩ 2
private def partial1269 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 2)

private def cache1270 : Cache :=
  step cache1266 ⟨19, by decide⟩ 3
private def partial1270 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1266 ⟨19, by decide⟩ (some 3)

private def cache1271 : Cache :=
  step cache1255 ⟨18, by decide⟩ 3
private def partial1271 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1255 ⟨18, by decide⟩ (some 3)

private def cache1272 : Cache :=
  step cache1271 ⟨19, by decide⟩ 0
private def partial1272 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 0)

private def cache1273 : Cache :=
  step cache1271 ⟨19, by decide⟩ 1
private def partial1273 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 1)

private def cache1274 : Cache :=
  step cache1271 ⟨19, by decide⟩ 2
private def partial1274 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 2)

private def cache1275 : Cache :=
  step cache1271 ⟨19, by decide⟩ 3
private def partial1275 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1271 ⟨19, by decide⟩ (some 3)

private def cache1276 : Cache :=
  step cache1240 ⟨17, by decide⟩ 3
private def partial1276 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1240 ⟨17, by decide⟩ (some 3)

private def cache1277 : Cache :=
  step cache1276 ⟨18, by decide⟩ 0
private def partial1277 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 0)

private def cache1278 : Cache :=
  step cache1277 ⟨19, by decide⟩ 0
private def partial1278 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 0)

private def cache1279 : Cache :=
  step cache1277 ⟨19, by decide⟩ 1
private def partial1279 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 1)

private def cache1280 : Cache :=
  step cache1277 ⟨19, by decide⟩ 2
private def partial1280 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 2)

private def cache1281 : Cache :=
  step cache1277 ⟨19, by decide⟩ 3
private def partial1281 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1277 ⟨19, by decide⟩ (some 3)

private def cache1282 : Cache :=
  step cache1276 ⟨18, by decide⟩ 1
private def partial1282 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 1)

private def cache1283 : Cache :=
  step cache1282 ⟨19, by decide⟩ 0
private def partial1283 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 0)

private def cache1284 : Cache :=
  step cache1282 ⟨19, by decide⟩ 1
private def partial1284 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 1)

private def cache1285 : Cache :=
  step cache1282 ⟨19, by decide⟩ 2
private def partial1285 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 2)

private def cache1286 : Cache :=
  step cache1282 ⟨19, by decide⟩ 3
private def partial1286 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1282 ⟨19, by decide⟩ (some 3)

private def cache1287 : Cache :=
  step cache1276 ⟨18, by decide⟩ 2
private def partial1287 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 2)

private def cache1288 : Cache :=
  step cache1276 ⟨18, by decide⟩ 3
private def partial1288 : Partial (Fin 20) (Fin 4) :=
  Function.update partial1276 ⟨18, by decide⟩ (some 3)

private theorem receipt1288 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1288, by decide⟩ cache1288 partial1288 = true := by
  decide +kernel

private theorem receipt1287 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1287, by decide⟩ cache1287 partial1287 = true := by
  decide +kernel

private theorem receipt1286 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1286, by decide⟩ cache1286 partial1286 = true := by
  decide +kernel

private theorem receipt1285 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1285, by decide⟩ cache1285 partial1285 = true := by
  decide +kernel

private theorem receipt1284 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1284, by decide⟩ cache1284 partial1284 = true := by
  decide +kernel

private theorem receipt1283 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1283, by decide⟩ cache1283 partial1283 = true := by
  decide +kernel

private theorem receipt1282 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1282, by decide⟩ cache1282 partial1282 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1283,1284,1285,1286])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2828633954099315 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1283
  · exact receipt1284
  · exact receipt1285
  · exact receipt1286

private theorem receipt1281 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1281, by decide⟩ cache1281 partial1281 = true := by
  decide +kernel

private theorem receipt1280 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1280, by decide⟩ cache1280 partial1280 = true := by
  decide +kernel

#print axioms receipt1280

private theorem receipt1279 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1279, by decide⟩ cache1279 partial1279 = true := by
  decide +kernel

private theorem receipt1278 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1278, by decide⟩ cache1278 partial1278 = true := by
  decide +kernel

private theorem receipt1277 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1277, by decide⟩ cache1277 partial1277 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1278,1279,1280,1281])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2817636152811475 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1278
  · exact receipt1279
  · exact receipt1280
  · exact receipt1281

private theorem receipt1276 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1276, by decide⟩ cache1276 partial1276 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1277,1282,1287,1288])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2833033074089906 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1277
  · exact receipt1282
  · exact receipt1287
  · exact receipt1288

private theorem receipt1275 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1275, by decide⟩ cache1275 partial1275 = true := by
  decide +kernel

private theorem receipt1274 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1274, by decide⟩ cache1274 partial1274 = true := by
  decide +kernel

private theorem receipt1273 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1273, by decide⟩ cache1273 partial1273 = true := by
  decide +kernel

private theorem receipt1272 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1272, by decide⟩ cache1272 partial1272 = true := by
  decide +kernel

private theorem receipt1271 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1271, by decide⟩ cache1271 partial1271 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1272,1273,1274,1275])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2804438791266067 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1272
  · exact receipt1273
  · exact receipt1274
  · exact receipt1275

private theorem receipt1270 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1270, by decide⟩ cache1270 partial1270 = true := by
  decide +kernel

private theorem receipt1269 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1269, by decide⟩ cache1269 partial1269 = true := by
  decide +kernel

private theorem receipt1268 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1268, by decide⟩ cache1268 partial1268 = true := by
  decide +kernel

private theorem receipt1267 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1267, by decide⟩ cache1267 partial1267 = true := by
  decide +kernel

private theorem receipt1266 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1266, by decide⟩ cache1266 partial1266 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1267,1268,1269,1270])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2793440989978227 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1267
  · exact receipt1268
  · exact receipt1269
  · exact receipt1270

private theorem receipt1265 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1265, by decide⟩ cache1265 partial1265 = true := by
  decide +kernel

private theorem receipt1264 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1264, by decide⟩ cache1264 partial1264 = true := by
  decide +kernel

private theorem receipt1263 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1263, by decide⟩ cache1263 partial1263 = true := by
  decide +kernel

private theorem receipt1262 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1262, by decide⟩ cache1262 partial1262 = true := by
  decide +kernel

private theorem receipt1261 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1261, by decide⟩ cache1261 partial1261 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1262,1263,1264,1265])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2782443188690387 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1262
  · exact receipt1263
  · exact receipt1264
  · exact receipt1265

private theorem receipt1260 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1260, by decide⟩ cache1260 partial1260 = true := by
  decide +kernel

private theorem receipt1259 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1259, by decide⟩ cache1259 partial1259 = true := by
  decide +kernel

private theorem receipt1258 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1258, by decide⟩ cache1258 partial1258 = true := by
  decide +kernel

private theorem receipt1257 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1257, by decide⟩ cache1257 partial1257 = true := by
  decide +kernel

private theorem receipt1256 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1256, by decide⟩ cache1256 partial1256 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1257,1258,1259,1260])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2771445387402547 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1257
  · exact receipt1258
  · exact receipt1259
  · exact receipt1260

private theorem receipt1255 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1255, by decide⟩ cache1255 partial1255 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1256,1261,1266,1271])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2795638401703186 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1256
  · exact receipt1261
  · exact receipt1266
  · exact receipt1271

private theorem receipt1254 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1254, by decide⟩ cache1254 partial1254 = true := by
  decide +kernel

private theorem receipt1253 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1253, by decide⟩ cache1253 partial1253 = true := by
  decide +kernel

private theorem receipt1252 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1252, by decide⟩ cache1252 partial1252 = true := by
  decide +kernel

private theorem receipt1251 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1251, by decide⟩ cache1251 partial1251 = true := by
  decide +kernel

private theorem receipt1250 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1250, by decide⟩ cache1250 partial1250 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1251,1252,1253,1254])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2758248025857139 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1251
  · exact receipt1252
  · exact receipt1253
  · exact receipt1254

private theorem receipt1249 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1249, by decide⟩ cache1249 partial1249 = true := by
  decide +kernel

private theorem receipt1248 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1248, by decide⟩ cache1248 partial1248 = true := by
  decide +kernel

private theorem receipt1247 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1247, by decide⟩ cache1247 partial1247 = true := by
  decide +kernel

private theorem receipt1246 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1246, by decide⟩ cache1246 partial1246 = true := by
  decide +kernel

private theorem receipt1245 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1245, by decide⟩ cache1245 partial1245 = true := by
  decide +kernel

private theorem receipt1244 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1244, by decide⟩ cache1244 partial1244 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1245,1246,1247,1248])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2745050664311731 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1245
  · exact receipt1246
  · exact receipt1247
  · exact receipt1248

private theorem receipt1243 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1243, by decide⟩ cache1243 partial1243 = true := by
  decide +kernel

private theorem receipt1242 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1242, by decide⟩ cache1242 partial1242 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1243,1244,1249,1250])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2749449784302450 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1243
  · exact receipt1244
  · exact receipt1249
  · exact receipt1250

private theorem receipt1241 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1241, by decide⟩ cache1241 partial1241 = true := by
  decide +kernel

theorem receipt1240 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1240, by decide⟩ cache1240 partial1240 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1241,1242,1255,1276])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2806627609910065 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1241
  · exact receipt1242
  · exact receipt1255
  · exact receipt1276

private theorem receipt1239 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1239, by decide⟩ cache1239 partial1239 = true := by
  decide +kernel

private theorem receipt1238 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1238, by decide⟩ cache1238 partial1238 = true := by
  decide +kernel

private theorem receipt1237 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1237, by decide⟩ cache1237 partial1237 = true := by
  decide +kernel

private theorem receipt1236 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1236, by decide⟩ cache1236 partial1236 = true := by
  decide +kernel

private theorem receipt1235 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1235, by decide⟩ cache1235 partial1235 = true := by
  decide +kernel

private theorem receipt1234 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1234, by decide⟩ cache1234 partial1234 = true := by
  decide +kernel

private theorem receipt1233 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1233, by decide⟩ cache1233 partial1233 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1234,1235,1236,1237])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2720855501478483 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1234
  · exact receipt1235
  · exact receipt1236
  · exact receipt1237

private theorem receipt1232 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1232, by decide⟩ cache1232 partial1232 = true := by
  decide +kernel

private theorem receipt1231 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1231, by decide⟩ cache1231 partial1231 = true := by
  decide +kernel

private theorem receipt1230 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1230, by decide⟩ cache1230 partial1230 = true := by
  decide +kernel

private theorem receipt1229 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1229, by decide⟩ cache1229 partial1229 = true := by
  decide +kernel

private theorem receipt1228 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1228, by decide⟩ cache1228 partial1228 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1229,1230,1231,1232])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2709857700190643 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1229
  · exact receipt1230
  · exact receipt1231
  · exact receipt1232

private theorem receipt1227 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1227, by decide⟩ cache1227 partial1227 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1228,1233,1238,1239])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2725254621469074 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1228
  · exact receipt1233
  · exact receipt1238
  · exact receipt1239

private theorem receipt1226 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1226, by decide⟩ cache1226 partial1226 = true := by
  decide +kernel

private theorem receipt1225 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1225, by decide⟩ cache1225 partial1225 = true := by
  decide +kernel

private theorem receipt1224 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1224, by decide⟩ cache1224 partial1224 = true := by
  decide +kernel

private theorem receipt1223 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1223, by decide⟩ cache1223 partial1223 = true := by
  decide +kernel

private theorem receipt1222 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1222, by decide⟩ cache1222 partial1222 = true := by
  decide +kernel

private theorem receipt1221 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1221, by decide⟩ cache1221 partial1221 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1222,1223,1224,1225])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2694460778387667 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1222
  · exact receipt1223
  · exact receipt1224
  · exact receipt1225

private theorem receipt1220 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1220, by decide⟩ cache1220 partial1220 = true := by
  decide +kernel

private theorem receipt1219 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1219, by decide⟩ cache1219 partial1219 = true := by
  decide +kernel

private theorem receipt1218 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1218, by decide⟩ cache1218 partial1218 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1219,1220,1221,1226])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2696658190637170 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1219
  · exact receipt1220
  · exact receipt1221
  · exact receipt1226

private theorem receipt1217 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1217, by decide⟩ cache1217 partial1217 = true := by
  decide +kernel

private theorem receipt1216 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1216, by decide⟩ cache1216 partial1216 = true := by
  decide +kernel

theorem receipt1215 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1215, by decide⟩ cache1215 partial1215 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1216,1217,1218,1227])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2698855602886673 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1216
  · exact receipt1217
  · exact receipt1218
  · exact receipt1227

theorem receipt1214 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1214, by decide⟩ cache1214 partial1214 = true := by
  decide +kernel

theorem receipt1213 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1213, by decide⟩ cache1213 partial1213 = true := by
  decide +kernel

theorem receipt1211 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1211, by decide⟩ cache1211 partial1211 = true := by
  decide +kernel

theorem receipt1210 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 5 ⟨1210, by decide⟩ cache1210 partial1210 = true := by
  decide +kernel

private theorem receipt1208 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1208, by decide⟩ cache1208 partial1208 = true := by
  decide +kernel

private theorem receipt1207 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1207, by decide⟩ cache1207 partial1207 = true := by
  decide +kernel

private theorem receipt1206 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1206, by decide⟩ cache1206 partial1206 = true := by
  decide +kernel

private theorem receipt1205 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1205, by decide⟩ cache1205 partial1205 = true := by
  decide +kernel

private theorem receipt1204 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1204, by decide⟩ cache1204 partial1204 = true := by
  decide +kernel

private theorem receipt1203 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1203, by decide⟩ cache1203 partial1203 = true := by
  decide +kernel

private theorem receipt1202 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1202, by decide⟩ cache1202 partial1202 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1203,1204,1205,1206])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2652669133493875 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1203
  · exact receipt1204
  · exact receipt1205
  · exact receipt1206

private theorem receipt1201 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1201, by decide⟩ cache1201 partial1201 = true := by
  decide +kernel

private theorem receipt1200 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1200, by decide⟩ cache1200 partial1200 = true := by
  decide +kernel

private theorem receipt1199 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1199, by decide⟩ cache1199 partial1199 = true := by
  decide +kernel

private theorem receipt1198 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1198, by decide⟩ cache1198 partial1198 = true := by
  decide +kernel

private theorem receipt1197 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1197, by decide⟩ cache1197 partial1197 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1198,1199,1200,1201])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2641671332206035 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1198
  · exact receipt1199
  · exact receipt1200
  · exact receipt1201

private theorem receipt1196 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1196, by decide⟩ cache1196 partial1196 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1197,1202,1207,1208])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2657068253484466 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1197
  · exact receipt1202
  · exact receipt1207
  · exact receipt1208

private theorem receipt1195 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1195, by decide⟩ cache1195 partial1195 = true := by
  decide +kernel

private theorem receipt1194 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1194, by decide⟩ cache1194 partial1194 = true := by
  decide +kernel

private theorem receipt1193 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1193, by decide⟩ cache1193 partial1193 = true := by
  decide +kernel

private theorem receipt1192 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1192, by decide⟩ cache1192 partial1192 = true := by
  decide +kernel

private theorem receipt1191 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1191, by decide⟩ cache1191 partial1191 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1192,1193,1194,1195])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2628473970660627 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1192
  · exact receipt1193
  · exact receipt1194
  · exact receipt1195

private theorem receipt1190 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1190, by decide⟩ cache1190 partial1190 = true := by
  decide +kernel

private theorem receipt1189 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1189, by decide⟩ cache1189 partial1189 = true := by
  decide +kernel

private theorem receipt1188 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1188, by decide⟩ cache1188 partial1188 = true := by
  decide +kernel

private theorem receipt1187 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1187, by decide⟩ cache1187 partial1187 = true := by
  decide +kernel

private theorem receipt1186 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1186, by decide⟩ cache1186 partial1186 = true := by
  decide +kernel

private theorem receipt1185 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1185, by decide⟩ cache1185 partial1185 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1186,1187,1188,1189])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2615276609115219 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1186
  · exact receipt1187
  · exact receipt1188
  · exact receipt1189

private theorem receipt1184 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1184, by decide⟩ cache1184 partial1184 = true := by
  decide +kernel

private theorem receipt1183 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1183, by decide⟩ cache1183 partial1183 = true := by
  decide +kernel

private theorem receipt1182 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1182, by decide⟩ cache1182 partial1182 = true := by
  decide +kernel

private theorem receipt1181 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1181, by decide⟩ cache1181 partial1181 = true := by
  decide +kernel

private theorem receipt1180 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1180, by decide⟩ cache1180 partial1180 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1181,1182,1183,1184])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2604278807827379 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1181
  · exact receipt1182
  · exact receipt1183
  · exact receipt1184

private theorem receipt1179 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1179, by decide⟩ cache1179 partial1179 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1180,1185,1190,1191])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2619675729105810 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1180
  · exact receipt1185
  · exact receipt1190
  · exact receipt1191

private theorem receipt1178 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1178, by decide⟩ cache1178 partial1178 = true := by
  decide +kernel

private theorem receipt1177 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1177, by decide⟩ cache1177 partial1177 = true := by
  decide +kernel

private theorem receipt1176 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1176, by decide⟩ cache1176 partial1176 = true := by
  decide +kernel

private theorem receipt1175 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1175, by decide⟩ cache1175 partial1175 = true := by
  decide +kernel

private theorem receipt1174 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1174, by decide⟩ cache1174 partial1174 = true := by
  decide +kernel

private theorem receipt1173 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 1 ⟨1173, by decide⟩ cache1173 partial1173 = true := by
  decide +kernel

private theorem receipt1172 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1172, by decide⟩ cache1172 partial1172 = true := by
  apply actual_split (i := (19 : Fin 20))
    (children := ![1173,1174,1175,1176])
    (by
      change (.split (19 : Fin 20)
        (fun a => ⟨(2586682325766835 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (19 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1173
  · exact receipt1174
  · exact receipt1175
  · exact receipt1176

private theorem receipt1171 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 2 ⟨1171, by decide⟩ cache1171 partial1171 = true := by
  decide +kernel

private theorem receipt1170 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1170, by decide⟩ cache1170 partial1170 = true := by
  apply actual_split (i := (18 : Fin 20))
    (children := ![1171,1172,1177,1178])
    (by
      change (.split (18 : Fin 20)
        (fun a => ⟨(2591081445757554 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (18 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1171
  · exact receipt1172
  · exact receipt1177
  · exact receipt1178

private theorem receipt1169 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 3 ⟨1169, by decide⟩ cache1169 partial1169 = true := by
  decide +kernel

theorem receipt1168 :
    check pilotNodes step lower EJMGlobalScoreSymmetry.dominates
      scale 4 ⟨1168, by decide⟩ cache1168 partial1168 = true := by
  apply actual_split (i := (17 : Fin 20))
    (children := ![1169,1170,1179,1196])
    (by
      change (.split (17 : Fin 20)
        (fun a => ⟨(2630664937837105 / 2 ^ (5 + 12 * a.val) % 4096) % 2497,
          Nat.mod_lt _ (by decide)⟩) :
          Node 2497 (Fin 20) (Fin 4) EJMGlobalScoreSymmetry.Cut) = _
      apply congrArg (Node.split (17 : Fin 20))
      funext a
      fin_cases a <;> rfl)
  intro a
  fin_cases a
  · exact receipt1169
  · exact receipt1170
  · exact receipt1179
  · exact receipt1196

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


end D5.S3.Quantum.Entanglement.EJM.EJMGlobalSuffixProbeBlock7
