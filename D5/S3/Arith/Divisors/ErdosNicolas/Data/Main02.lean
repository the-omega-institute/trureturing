/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main02
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main02.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts00

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main02

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![2, 2, 0, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![3, 7, 1, 2, 1, 1, 1]

private def n1014 : MainTree := .leaf (mainRankLeaf 2 ![2, 2, 0, 0, 0, 0, 0])
private def n1015 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 0, 0, 0, 0])
private def n1013 : MainTree := .split 1 2 n1014 n1015
private def n1017 : MainTree := .leaf (mainFullLeaf ![3, 2, 0, 0, 0, 0, 0])
private def n1018 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 0, 0, 0, 0])
private def n1016 : MainTree := .split 1 2 n1017 n1018
private def n1012 : MainTree := .split 0 2 n1013 n1016
private def n1020 : MainTree := .leaf (mainRankLeaf 1 ![2, 3, 0, 0, 0, 0, 1])
private def n1022 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 0, 0, 0, 1])
private def n1023 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 0, 0, 0, 1])
private def n1021 : MainTree := .split 1 2 n1022 n1023
private def n1019 : MainTree := .split 0 2 n1020 n1021
private def n1011 : MainTree := .split 6 0 n1012 n1019
private def n1027 : MainTree := .leaf (mainGapLeaf ![2, 2, 0, 0, 0, 1, 0])
private def n1028 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 0, 0, 1, 0])
private def n1026 : MainTree := .split 1 2 n1027 n1028
private def n1030 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 0, 0, 1, 0])
private def n1031 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 0, 0, 1, 0])
private def n1029 : MainTree := .split 1 2 n1030 n1031
private def n1025 : MainTree := .split 0 2 n1026 n1029
private def n1033 : MainTree := .leaf (mainRankLeaf 1 ![2, 3, 0, 0, 0, 1, 1])
private def n1034 : MainTree := .leaf (mainRankLeaf 1 ![3, 3, 0, 0, 0, 1, 1])
private def n1032 : MainTree := .split 0 2 n1033 n1034
private def n1024 : MainTree := .split 6 0 n1025 n1032
private def n1010 : MainTree := .split 5 0 n1011 n1024
private def n1039 : MainTree := .leaf (mainGapLeaf ![2, 2, 0, 0, 1, 0, 0])
private def n1040 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 0, 1, 0, 0])
private def n1038 : MainTree := .split 1 2 n1039 n1040
private def n1042 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 0, 1, 0, 0])
private def n1043 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 0, 1, 0, 0])
private def n1041 : MainTree := .split 1 2 n1042 n1043
private def n1037 : MainTree := .split 0 2 n1038 n1041
private def n1045 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 0, 1, 0, 1])
private def n1046 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 0, 1, 0, 1])
private def n1044 : MainTree := .split 0 2 n1045 n1046
private def n1036 : MainTree := .split 6 0 n1037 n1044
private def n1049 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 0, 1, 1, 0])
private def n1050 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 0, 1, 1, 0])
private def n1048 : MainTree := .split 0 2 n1049 n1050
private def n1052 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 0, 1, 1, 1])
private def n1053 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 0, 1, 1, 1])
private def n1051 : MainTree := .split 0 2 n1052 n1053
private def n1047 : MainTree := .split 6 0 n1048 n1051
private def n1035 : MainTree := .split 5 0 n1036 n1047
private def n1009 : MainTree := .split 4 0 n1010 n1035
private def n1059 : MainTree := .leaf (mainFullLeaf ![2, 2, 1, 0, 0, 0, 0])
private def n1060 : MainTree := .leaf (mainFullLeaf ![2, 3, 1, 0, 0, 0, 0])
private def n1058 : MainTree := .split 1 2 n1059 n1060
private def n1062 : MainTree := .leaf (mainFullLeaf ![3, 2, 1, 0, 0, 0, 0])
private def n1063 : MainTree := .leaf (mainFullLeaf ![3, 3, 1, 0, 0, 0, 0])
private def n1061 : MainTree := .split 1 2 n1062 n1063
private def n1057 : MainTree := .split 0 2 n1058 n1061
private def n1066 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 0, 0, 0, 1])
private def n1067 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 0, 0, 0, 1])
private def n1065 : MainTree := .split 1 2 n1066 n1067
private def n1069 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 0, 0, 0, 1])
private def n1070 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 0, 0, 0, 1])
private def n1068 : MainTree := .split 1 2 n1069 n1070
private def n1064 : MainTree := .split 0 2 n1065 n1068
private def n1056 : MainTree := .split 6 0 n1057 n1064
private def n1074 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 0, 0, 1, 0])
private def n1075 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 0, 0, 1, 0])
private def n1073 : MainTree := .split 1 2 n1074 n1075
private def n1077 : MainTree := .leaf (mainRankLeaf 2 ![3, 2, 1, 0, 0, 1, 0])
private def n1078 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 0, 0, 1, 0])
private def n1076 : MainTree := .split 1 2 n1077 n1078
private def n1072 : MainTree := .split 0 2 n1073 n1076
private def n1080 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 0, 0, 1, 1])
private def n1082 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 0, 0, 1, 1])
private def n1083 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 0, 0, 1, 1])
private def n1081 : MainTree := .split 1 2 n1082 n1083
private def n1079 : MainTree := .split 0 2 n1080 n1081
private def n1071 : MainTree := .split 6 0 n1072 n1079
private def n1055 : MainTree := .split 5 0 n1056 n1071
private def n1088 : MainTree := .leaf (mainFullLeaf ![2, 2, 1, 0, 1, 0, 0])
private def n1089 : MainTree := .leaf (mainRankLeaf 2 ![2, 3, 1, 0, 1, 0, 0])
private def n1087 : MainTree := .split 1 2 n1088 n1089
private def n1091 : MainTree := .leaf (mainFullLeaf ![3, 2, 1, 0, 1, 0, 0])
private def n1092 : MainTree := .leaf (mainRankLeaf 2 ![3, 3, 1, 0, 1, 0, 0])
private def n1090 : MainTree := .split 1 2 n1091 n1092
private def n1086 : MainTree := .split 0 2 n1087 n1090
private def n1095 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 0, 1, 0, 1])
private def n1096 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 0, 1, 0, 1])
private def n1094 : MainTree := .split 1 2 n1095 n1096
private def n1098 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 0, 1, 0, 1])
private def n1099 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 0, 1, 0, 1])
private def n1097 : MainTree := .split 1 2 n1098 n1099
private def n1093 : MainTree := .split 0 2 n1094 n1097
private def n1085 : MainTree := .split 6 0 n1086 n1093
private def n1103 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 0, 1, 1, 0])
private def n1104 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 0, 1, 1, 0])
private def n1102 : MainTree := .split 1 2 n1103 n1104
private def n1106 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 0, 1, 1, 0])
private def n1107 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 0, 1, 1, 0])
private def n1105 : MainTree := .split 1 2 n1106 n1107
private def n1101 : MainTree := .split 0 2 n1102 n1105
private def n1109 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 0, 1, 1, 1])
private def n1110 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 0, 1, 1, 1])
private def n1108 : MainTree := .split 0 2 n1109 n1110
private def n1100 : MainTree := .split 6 0 n1101 n1108
private def n1084 : MainTree := .split 5 0 n1085 n1100
private def n1054 : MainTree := .split 4 0 n1055 n1084
private def n1008 : MainTree := .split 2 0 n1009 n1054
private def n1117 : MainTree := .leaf (mainGapLeaf ![2, 5, 0, 0, 0, 0, 0])
private def n1118 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 0, 0, 0, 0])
private def n1116 : MainTree := .split 0 2 n1117 n1118
private def n1119 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 0, 0, 0])
private def n1115 : MainTree := .split 1 5 n1116 n1119
private def n1120 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 0, 0, 1])
private def n1114 : MainTree := .split 6 0 n1115 n1120
private def n1124 : MainTree := .leaf (mainGapLeaf ![2, 5, 0, 0, 0, 1, 0])
private def n1125 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 0, 0, 1, 0])
private def n1123 : MainTree := .split 0 2 n1124 n1125
private def n1126 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 0, 1, 0])
private def n1122 : MainTree := .split 1 5 n1123 n1126
private def n1127 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 0, 1, 1])
private def n1121 : MainTree := .split 6 0 n1122 n1127
private def n1113 : MainTree := .split 5 0 n1114 n1121
private def n1131 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 0, 1, 0, 0])
private def n1132 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 1, 0, 0])
private def n1130 : MainTree := .split 1 5 n1131 n1132
private def n1133 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 1, 0, 1])
private def n1129 : MainTree := .split 6 0 n1130 n1133
private def n1135 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 1, 1, 0])
private def n1136 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 0, 1, 1, 1])
private def n1134 : MainTree := .split 6 0 n1135 n1136
private def n1128 : MainTree := .split 5 0 n1129 n1134
private def n1112 : MainTree := .split 4 0 n1113 n1128
private def n1142 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 0, 0, 0, 0])
private def n1143 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 0, 0, 0, 0])
private def n1141 : MainTree := .split 0 2 n1142 n1143
private def n1144 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 0, 0, 0])
private def n1140 : MainTree := .split 1 5 n1141 n1144
private def n1147 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 0, 0, 0, 1])
private def n1148 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 0, 0, 0, 1])
private def n1146 : MainTree := .split 0 2 n1147 n1148
private def n1149 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 0, 0, 1])
private def n1145 : MainTree := .split 1 5 n1146 n1149
private def n1139 : MainTree := .split 6 0 n1140 n1145
private def n1153 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 0, 0, 1, 0])
private def n1154 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 0, 0, 1, 0])
private def n1152 : MainTree := .split 0 2 n1153 n1154
private def n1155 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 0, 1, 0])
private def n1151 : MainTree := .split 1 5 n1152 n1155
private def n1156 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 0, 1, 1])
private def n1150 : MainTree := .split 6 0 n1151 n1156
private def n1138 : MainTree := .split 5 0 n1139 n1150
private def n1161 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 0, 1, 0, 0])
private def n1162 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 0, 1, 0, 0])
private def n1160 : MainTree := .split 0 2 n1161 n1162
private def n1163 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 1, 0, 0])
private def n1159 : MainTree := .split 1 5 n1160 n1163
private def n1165 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 0, 1, 0, 1])
private def n1166 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 1, 0, 1])
private def n1164 : MainTree := .split 1 5 n1165 n1166
private def n1158 : MainTree := .split 6 0 n1159 n1164
private def n1170 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 0, 1, 1, 0])
private def n1171 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 0, 1, 1, 0])
private def n1169 : MainTree := .split 0 2 n1170 n1171
private def n1172 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 1, 1, 0])
private def n1168 : MainTree := .split 1 5 n1169 n1172
private def n1173 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 0, 1, 1, 1])
private def n1167 : MainTree := .split 6 0 n1168 n1173
private def n1157 : MainTree := .split 5 0 n1158 n1167
private def n1137 : MainTree := .split 4 0 n1138 n1157
private def n1111 : MainTree := .split 2 0 n1112 n1137
private def n1007 : MainTree := .split 1 3 n1008 n1111
private def n1182 : MainTree := .leaf (mainGapLeaf ![2, 2, 0, 1, 0, 0, 0])
private def n1183 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 1, 0, 0, 0])
private def n1181 : MainTree := .split 1 2 n1182 n1183
private def n1185 : MainTree := .leaf (mainFullLeaf ![3, 2, 0, 1, 0, 0, 0])
private def n1186 : MainTree := .leaf (mainRankLeaf 2 ![3, 3, 0, 1, 0, 0, 0])
private def n1184 : MainTree := .split 1 2 n1185 n1186
private def n1180 : MainTree := .split 0 2 n1181 n1184
private def n1188 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 2, 0, 0, 0])
private def n1190 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 2, 0, 0, 0])
private def n1191 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 0, 0, 0])
private def n1189 : MainTree := .split 1 2 n1190 n1191
private def n1187 : MainTree := .split 0 2 n1188 n1189
private def n1179 : MainTree := .split 3 1 n1180 n1187
private def n1195 : MainTree := .leaf (mainGapLeaf ![2, 2, 0, 1, 0, 0, 1])
private def n1196 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 1, 0, 0, 1])
private def n1194 : MainTree := .split 1 2 n1195 n1196
private def n1198 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 1, 0, 0, 1])
private def n1199 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 1, 0, 0, 1])
private def n1197 : MainTree := .split 1 2 n1198 n1199
private def n1193 : MainTree := .split 0 2 n1194 n1197
private def n1201 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 2, 0, 0, 1])
private def n1202 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 0, 0, 1])
private def n1200 : MainTree := .split 0 2 n1201 n1202
private def n1192 : MainTree := .split 3 1 n1193 n1200
private def n1178 : MainTree := .split 6 0 n1179 n1192
private def n1207 : MainTree := .leaf (mainGapLeaf ![2, 2, 0, 1, 0, 1, 0])
private def n1208 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 1, 0, 1, 0])
private def n1206 : MainTree := .split 1 2 n1207 n1208
private def n1210 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 1, 0, 1, 0])
private def n1211 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 1, 0, 1, 0])
private def n1209 : MainTree := .split 1 2 n1210 n1211
private def n1205 : MainTree := .split 0 2 n1206 n1209
private def n1213 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 2, 0, 1, 0])
private def n1214 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 0, 1, 0])
private def n1212 : MainTree := .split 0 2 n1213 n1214
private def n1204 : MainTree := .split 3 1 n1205 n1212
private def n1217 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 1, 0, 1, 1])
private def n1218 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 1, 0, 1, 1])
private def n1216 : MainTree := .split 0 2 n1217 n1218
private def n1220 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 2, 0, 1, 1])
private def n1221 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 0, 1, 1])
private def n1219 : MainTree := .split 0 2 n1220 n1221
private def n1215 : MainTree := .split 3 1 n1216 n1219
private def n1203 : MainTree := .split 6 0 n1204 n1215
private def n1177 : MainTree := .split 5 0 n1178 n1203
private def n1227 : MainTree := .leaf (mainGapLeaf ![2, 2, 0, 1, 1, 0, 0])
private def n1228 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 1, 1, 0, 0])
private def n1226 : MainTree := .split 1 2 n1227 n1228
private def n1230 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 1, 1, 0, 0])
private def n1231 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 1, 1, 0, 0])
private def n1229 : MainTree := .split 1 2 n1230 n1231
private def n1225 : MainTree := .split 0 2 n1226 n1229
private def n1233 : MainTree := .leaf (mainRankLeaf 1 ![2, 3, 0, 2, 1, 0, 0])
private def n1235 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 2, 1, 0, 0])
private def n1236 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 1, 0, 0])
private def n1234 : MainTree := .split 1 2 n1235 n1236
private def n1232 : MainTree := .split 0 2 n1233 n1234
private def n1224 : MainTree := .split 3 1 n1225 n1232
private def n1239 : MainTree := .leaf (mainRankLeaf 1 ![2, 3, 0, 1, 1, 0, 1])
private def n1240 : MainTree := .leaf (mainRankLeaf 1 ![3, 3, 0, 1, 1, 0, 1])
private def n1238 : MainTree := .split 0 2 n1239 n1240
private def n1242 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 2, 1, 0, 1])
private def n1243 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 1, 0, 1])
private def n1241 : MainTree := .split 0 2 n1242 n1243
private def n1237 : MainTree := .split 3 1 n1238 n1241
private def n1223 : MainTree := .split 6 0 n1224 n1237
private def n1248 : MainTree := .leaf (mainGapLeaf ![2, 2, 0, 1, 1, 1, 0])
private def n1249 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 1, 1, 1, 0])
private def n1247 : MainTree := .split 1 2 n1248 n1249
private def n1251 : MainTree := .leaf (mainGapLeaf ![3, 2, 0, 1, 1, 1, 0])
private def n1252 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 1, 1, 1, 0])
private def n1250 : MainTree := .split 1 2 n1251 n1252
private def n1246 : MainTree := .split 0 2 n1247 n1250
private def n1254 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 2, 1, 1, 0])
private def n1255 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 1, 1, 0])
private def n1253 : MainTree := .split 0 2 n1254 n1255
private def n1245 : MainTree := .split 3 1 n1246 n1253
private def n1258 : MainTree := .leaf (mainGapLeaf ![2, 3, 0, 1, 1, 1, 1])
private def n1259 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 1, 1, 1, 1])
private def n1257 : MainTree := .split 0 2 n1258 n1259
private def n1260 : MainTree := .leaf (mainGapLeaf ![3, 3, 0, 2, 1, 1, 1])
private def n1256 : MainTree := .split 3 1 n1257 n1260
private def n1244 : MainTree := .split 6 0 n1245 n1256
private def n1222 : MainTree := .split 5 0 n1223 n1244
private def n1176 : MainTree := .split 4 0 n1177 n1222
private def n1267 : MainTree := .leaf (mainFullLeaf ![2, 2, 1, 1, 0, 0, 0])
private def n1268 : MainTree := .leaf (mainFullLeaf ![2, 3, 1, 1, 0, 0, 0])
private def n1266 : MainTree := .split 1 2 n1267 n1268
private def n1270 : MainTree := .leaf (mainFullLeaf ![3, 2, 1, 1, 0, 0, 0])
private def n1271 : MainTree := .leaf (mainFullLeaf ![3, 3, 1, 1, 0, 0, 0])
private def n1269 : MainTree := .split 1 2 n1270 n1271
private def n1265 : MainTree := .split 0 2 n1266 n1269
private def n1274 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 2, 0, 0, 0])
private def n1275 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 0, 0, 0])
private def n1273 : MainTree := .split 1 2 n1274 n1275
private def n1277 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 2, 0, 0, 0])
private def n1278 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 0, 0, 0])
private def n1276 : MainTree := .split 1 2 n1277 n1278
private def n1272 : MainTree := .split 0 2 n1273 n1276
private def n1264 : MainTree := .split 3 1 n1265 n1272
private def n1282 : MainTree := .leaf (mainRankLeaf 2 ![2, 2, 1, 1, 0, 0, 1])
private def n1283 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 1, 0, 0, 1])
private def n1281 : MainTree := .split 1 2 n1282 n1283
private def n1285 : MainTree := .leaf (mainRankLeaf 2 ![3, 2, 1, 1, 0, 0, 1])
private def n1286 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 1, 0, 0, 1])
private def n1284 : MainTree := .split 1 2 n1285 n1286
private def n1280 : MainTree := .split 0 2 n1281 n1284
private def n1288 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 0, 0, 1])
private def n1290 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 2, 0, 0, 1])
private def n1291 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 0, 0, 1])
private def n1289 : MainTree := .split 1 2 n1290 n1291
private def n1287 : MainTree := .split 0 2 n1288 n1289
private def n1279 : MainTree := .split 3 1 n1280 n1287
private def n1263 : MainTree := .split 6 0 n1264 n1279
private def n1296 : MainTree := .leaf (mainRankLeaf 2 ![2, 2, 1, 1, 0, 1, 0])
private def n1297 : MainTree := .leaf (mainRankLeaf 2 ![2, 3, 1, 1, 0, 1, 0])
private def n1295 : MainTree := .split 1 2 n1296 n1297
private def n1299 : MainTree := .leaf (mainFullLeaf ![3, 2, 1, 1, 0, 1, 0])
private def n1300 : MainTree := .leaf (mainRankLeaf 2 ![3, 3, 1, 1, 0, 1, 0])
private def n1298 : MainTree := .split 1 2 n1299 n1300
private def n1294 : MainTree := .split 0 2 n1295 n1298
private def n1303 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 2, 0, 1, 0])
private def n1304 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 0, 1, 0])
private def n1302 : MainTree := .split 1 2 n1303 n1304
private def n1306 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 2, 0, 1, 0])
private def n1307 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 0, 1, 0])
private def n1305 : MainTree := .split 1 2 n1306 n1307
private def n1301 : MainTree := .split 0 2 n1302 n1305
private def n1293 : MainTree := .split 3 1 n1294 n1301
private def n1311 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 1, 0, 1, 1])
private def n1312 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 1, 0, 1, 1])
private def n1310 : MainTree := .split 1 2 n1311 n1312
private def n1314 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 1, 0, 1, 1])
private def n1315 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 1, 0, 1, 1])
private def n1313 : MainTree := .split 1 2 n1314 n1315
private def n1309 : MainTree := .split 0 2 n1310 n1313
private def n1317 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 0, 1, 1])
private def n1318 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 0, 1, 1])
private def n1316 : MainTree := .split 0 2 n1317 n1318
private def n1308 : MainTree := .split 3 1 n1309 n1316
private def n1292 : MainTree := .split 6 0 n1293 n1308
private def n1262 : MainTree := .split 5 0 n1263 n1292
private def n1324 : MainTree := .leaf (mainFullLeaf ![2, 2, 1, 1, 1, 0, 0])
private def n1325 : MainTree := .leaf (mainRankLeaf 2 ![2, 3, 1, 1, 1, 0, 0])
private def n1323 : MainTree := .split 1 2 n1324 n1325
private def n1327 : MainTree := .leaf (mainFullLeaf ![3, 2, 1, 1, 1, 0, 0])
private def n1328 : MainTree := .leaf (mainRankLeaf 2 ![3, 3, 1, 1, 1, 0, 0])
private def n1326 : MainTree := .split 1 2 n1327 n1328
private def n1322 : MainTree := .split 0 2 n1323 n1326
private def n1331 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 2, 1, 0, 0])
private def n1332 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 1, 0, 0])
private def n1330 : MainTree := .split 1 2 n1331 n1332
private def n1334 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 2, 1, 0, 0])
private def n1335 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 1, 0, 0])
private def n1333 : MainTree := .split 1 2 n1334 n1335
private def n1329 : MainTree := .split 0 2 n1330 n1333
private def n1321 : MainTree := .split 3 1 n1322 n1329
private def n1339 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 1, 1, 0, 1])
private def n1340 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 1, 1, 0, 1])
private def n1338 : MainTree := .split 1 2 n1339 n1340
private def n1342 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 1, 1, 0, 1])
private def n1343 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 1, 1, 0, 1])
private def n1341 : MainTree := .split 1 2 n1342 n1343
private def n1337 : MainTree := .split 0 2 n1338 n1341
private def n1345 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 1, 0, 1])
private def n1346 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 1, 0, 1])
private def n1344 : MainTree := .split 0 2 n1345 n1346
private def n1336 : MainTree := .split 3 1 n1337 n1344
private def n1320 : MainTree := .split 6 0 n1321 n1336
private def n1351 : MainTree := .leaf (mainGapLeaf ![2, 2, 1, 1, 1, 1, 0])
private def n1352 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 1, 1, 1, 0])
private def n1350 : MainTree := .split 1 2 n1351 n1352
private def n1354 : MainTree := .leaf (mainGapLeaf ![3, 2, 1, 1, 1, 1, 0])
private def n1355 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 1, 1, 1, 0])
private def n1353 : MainTree := .split 1 2 n1354 n1355
private def n1349 : MainTree := .split 0 2 n1350 n1353
private def n1357 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 1, 1, 0])
private def n1358 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 1, 1, 0])
private def n1356 : MainTree := .split 0 2 n1357 n1358
private def n1348 : MainTree := .split 3 1 n1349 n1356
private def n1361 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 1, 1, 1, 1])
private def n1362 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 1, 1, 1, 1])
private def n1360 : MainTree := .split 0 2 n1361 n1362
private def n1364 : MainTree := .leaf (mainGapLeaf ![2, 3, 1, 2, 1, 1, 1])
private def n1365 : MainTree := .leaf (mainGapLeaf ![3, 3, 1, 2, 1, 1, 1])
private def n1363 : MainTree := .split 0 2 n1364 n1365
private def n1359 : MainTree := .split 3 1 n1360 n1363
private def n1347 : MainTree := .split 6 0 n1348 n1359
private def n1319 : MainTree := .split 5 0 n1320 n1347
private def n1261 : MainTree := .split 4 0 n1262 n1319
private def n1175 : MainTree := .split 2 0 n1176 n1261
private def n1373 : MainTree := .leaf (mainGapLeaf ![2, 5, 0, 1, 0, 0, 0])
private def n1374 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 1, 0, 0, 0])
private def n1372 : MainTree := .split 0 2 n1373 n1374
private def n1375 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 2, 0, 0, 0])
private def n1371 : MainTree := .split 3 1 n1372 n1375
private def n1377 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 1, 0, 0, 0])
private def n1378 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 2, 0, 0, 0])
private def n1376 : MainTree := .split 3 1 n1377 n1378
private def n1370 : MainTree := .split 1 5 n1371 n1376
private def n1381 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 1, 0, 0, 1])
private def n1382 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 2, 0, 0, 1])
private def n1380 : MainTree := .split 3 1 n1381 n1382
private def n1383 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 2, 0, 0, 1])
private def n1379 : MainTree := .split 1 5 n1380 n1383
private def n1369 : MainTree := .split 6 0 n1370 n1379
private def n1388 : MainTree := .leaf (mainGapLeaf ![2, 5, 0, 1, 0, 1, 0])
private def n1389 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 1, 0, 1, 0])
private def n1387 : MainTree := .split 0 2 n1388 n1389
private def n1390 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 2, 0, 1, 0])
private def n1386 : MainTree := .split 3 1 n1387 n1390
private def n1391 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 2, 0, 1, 0])
private def n1385 : MainTree := .split 1 5 n1386 n1391
private def n1394 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 1, 0, 1, 1])
private def n1395 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 2, 0, 1, 1])
private def n1393 : MainTree := .split 3 1 n1394 n1395
private def n1396 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 2, 0, 1, 1])
private def n1392 : MainTree := .split 1 5 n1393 n1396
private def n1384 : MainTree := .split 6 0 n1385 n1392
private def n1368 : MainTree := .split 5 0 n1369 n1384
private def n1402 : MainTree := .leaf (mainGapLeaf ![2, 5, 0, 1, 1, 0, 0])
private def n1403 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 1, 1, 0, 0])
private def n1401 : MainTree := .split 0 2 n1402 n1403
private def n1404 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 2, 1, 0, 0])
private def n1400 : MainTree := .split 3 1 n1401 n1404
private def n1406 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 1, 1, 0, 0])
private def n1407 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 2, 1, 0, 0])
private def n1405 : MainTree := .split 3 1 n1406 n1407
private def n1399 : MainTree := .split 1 5 n1400 n1405
private def n1410 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 1, 1, 0, 1])
private def n1411 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 2, 1, 0, 1])
private def n1409 : MainTree := .split 3 1 n1410 n1411
private def n1412 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 2, 1, 0, 1])
private def n1408 : MainTree := .split 1 5 n1409 n1412
private def n1398 : MainTree := .split 6 0 n1399 n1408
private def n1416 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 1, 1, 1, 0])
private def n1417 : MainTree := .leaf (mainGapLeaf ![3, 5, 0, 2, 1, 1, 0])
private def n1415 : MainTree := .split 3 1 n1416 n1417
private def n1418 : MainTree := .leaf (mainGapLeaf ![3, 7, 0, 2, 1, 1, 0])
private def n1414 : MainTree := .split 1 5 n1415 n1418
private def n1419 : MainTree :=
  .leaf (.rankIndexed 1 768 RankReadouts00.rankReadout1419)
private def n1413 : MainTree := .split 6 0 n1414 n1419
private def n1397 : MainTree := .split 5 0 n1398 n1413
private def n1367 : MainTree := .split 4 0 n1368 n1397
private def n1427 : MainTree := .leaf (mainRankLeaf 2 ![2, 4, 1, 1, 0, 0, 0])
private def n1428 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 1, 0, 0, 0])
private def n1426 : MainTree := .split 1 4 n1427 n1428
private def n1430 : MainTree := .leaf (mainRankLeaf 2 ![3, 4, 1, 1, 0, 0, 0])
private def n1431 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 0, 0, 0])
private def n1429 : MainTree := .split 1 4 n1430 n1431
private def n1425 : MainTree := .split 0 2 n1426 n1429
private def n1433 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 2, 0, 0, 0])
private def n1434 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 0, 0, 0])
private def n1432 : MainTree := .split 0 2 n1433 n1434
private def n1424 : MainTree := .split 3 1 n1425 n1432
private def n1437 : MainTree := .leaf (mainGapLeaf ![2, 7, 1, 1, 0, 0, 0])
private def n1438 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 1, 0, 0, 0])
private def n1436 : MainTree := .split 0 2 n1437 n1438
private def n1439 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 2, 0, 0, 0])
private def n1435 : MainTree := .split 3 1 n1436 n1439
private def n1423 : MainTree := .split 1 5 n1424 n1435
private def n1443 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 1, 0, 0, 1])
private def n1444 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 0, 0, 1])
private def n1442 : MainTree := .split 0 2 n1443 n1444
private def n1445 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 0, 0, 1])
private def n1441 : MainTree := .split 3 1 n1442 n1445
private def n1447 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 1, 0, 0, 1])
private def n1448 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 2, 0, 0, 1])
private def n1446 : MainTree := .split 3 1 n1447 n1448
private def n1440 : MainTree := .split 1 5 n1441 n1446
private def n1422 : MainTree := .split 6 0 n1423 n1440
private def n1453 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 1, 0, 1, 0])
private def n1454 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 0, 1, 0])
private def n1452 : MainTree := .split 0 2 n1453 n1454
private def n1455 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 0, 1, 0])
private def n1451 : MainTree := .split 3 1 n1452 n1455
private def n1457 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 1, 0, 1, 0])
private def n1458 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 2, 0, 1, 0])
private def n1456 : MainTree := .split 3 1 n1457 n1458
private def n1450 : MainTree := .split 1 5 n1451 n1456
private def n1461 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 0, 1, 1])
private def n1462 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 0, 1, 1])
private def n1460 : MainTree := .split 3 1 n1461 n1462
private def n1463 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 2, 0, 1, 1])
private def n1459 : MainTree := .split 1 5 n1460 n1463
private def n1449 : MainTree := .split 6 0 n1450 n1459
private def n1421 : MainTree := .split 5 0 n1422 n1449
private def n1469 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 1, 1, 0, 0])
private def n1470 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 1, 0, 0])
private def n1468 : MainTree := .split 0 2 n1469 n1470
private def n1472 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 2, 1, 0, 0])
private def n1473 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 1, 0, 0])
private def n1471 : MainTree := .split 0 2 n1472 n1473
private def n1467 : MainTree := .split 3 1 n1468 n1471
private def n1475 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 1, 1, 0, 0])
private def n1476 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 2, 1, 0, 0])
private def n1474 : MainTree := .split 3 1 n1475 n1476
private def n1466 : MainTree := .split 1 5 n1467 n1474
private def n1480 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 1, 1, 0, 1])
private def n1481 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 1, 0, 1])
private def n1479 : MainTree := .split 0 2 n1480 n1481
private def n1482 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 1, 0, 1])
private def n1478 : MainTree := .split 3 1 n1479 n1482
private def n1483 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 2, 1, 0, 1])
private def n1477 : MainTree := .split 1 5 n1478 n1483
private def n1465 : MainTree := .split 6 0 n1466 n1477
private def n1488 : MainTree := .leaf (mainGapLeaf ![2, 5, 1, 1, 1, 1, 0])
private def n1489 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 1, 1, 0])
private def n1487 : MainTree := .split 0 2 n1488 n1489
private def n1490 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 1, 1, 0])
private def n1486 : MainTree := .split 3 1 n1487 n1490
private def n1491 : MainTree :=
  .leaf (.rankIndexed 1 768 RankReadouts00.rankReadout1491)
private def n1485 : MainTree := .split 1 5 n1486 n1491
private def n1494 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 1, 1, 1, 1])
private def n1495 : MainTree := .leaf (mainGapLeaf ![3, 5, 1, 2, 1, 1, 1])
private def n1493 : MainTree := .split 3 1 n1494 n1495
private def n1496 : MainTree := .leaf (mainGapLeaf ![3, 7, 1, 2, 1, 1, 1])
private def n1492 : MainTree := .split 1 5 n1493 n1496
private def n1484 : MainTree := .split 6 0 n1485 n1492
private def n1464 : MainTree := .split 5 0 n1465 n1484
private def n1420 : MainTree := .split 4 0 n1421 n1464
private def n1366 : MainTree := .split 2 0 n1367 n1420
private def n1174 : MainTree := .split 1 3 n1175 n1366
private def n1006 : MainTree := .split 3 0 n1007 n1174

private theorem c1009 : C ![2, 2, 0, 0, 0, 0, 0] ![3, 3, 0, 0, 1, 1, 1] n1009 := by
  decide +kernel

private theorem c1055 : C ![2, 2, 1, 0, 0, 0, 0] ![3, 3, 1, 0, 0, 1, 1] n1055 := by
  decide +kernel

private theorem c1084 : C ![2, 2, 1, 0, 1, 0, 0] ![3, 3, 1, 0, 1, 1, 1] n1084 := by
  decide +kernel

private theorem c1054 : C ![2, 2, 1, 0, 0, 0, 0] ![3, 3, 1, 0, 1, 1, 1] n1054 := by
  exact checkExponentBoxTree_join c1055 c1084 (by decide +kernel)

private theorem c1008 : C ![2, 2, 0, 0, 0, 0, 0] ![3, 3, 1, 0, 1, 1, 1] n1008 := by
  exact checkExponentBoxTree_join c1009 c1054 (by decide +kernel)

private theorem c1112 : C ![2, 4, 0, 0, 0, 0, 0] ![3, 7, 0, 0, 1, 1, 1] n1112 := by
  decide +kernel

private theorem c1138 : C ![2, 4, 1, 0, 0, 0, 0] ![3, 7, 1, 0, 0, 1, 1] n1138 := by
  decide +kernel

private theorem c1157 : C ![2, 4, 1, 0, 1, 0, 0] ![3, 7, 1, 0, 1, 1, 1] n1157 := by
  decide +kernel

private theorem c1137 : C ![2, 4, 1, 0, 0, 0, 0] ![3, 7, 1, 0, 1, 1, 1] n1137 := by
  exact checkExponentBoxTree_join c1138 c1157 (by decide +kernel)

private theorem c1111 : C ![2, 4, 0, 0, 0, 0, 0] ![3, 7, 1, 0, 1, 1, 1] n1111 := by
  exact checkExponentBoxTree_join c1112 c1137 (by decide +kernel)

private theorem c1007 : C ![2, 2, 0, 0, 0, 0, 0] ![3, 7, 1, 0, 1, 1, 1] n1007 := by
  exact checkExponentBoxTree_join c1008 c1111 (by decide +kernel)

private theorem c1177 : C ![2, 2, 0, 1, 0, 0, 0] ![3, 3, 0, 2, 0, 1, 1] n1177 := by
  decide +kernel

private theorem c1223 : C ![2, 2, 0, 1, 1, 0, 0] ![3, 3, 0, 2, 1, 0, 1] n1223 := by
  decide +kernel

private theorem c1244 : C ![2, 2, 0, 1, 1, 1, 0] ![3, 3, 0, 2, 1, 1, 1] n1244 := by
  decide +kernel

private theorem c1222 : C ![2, 2, 0, 1, 1, 0, 0] ![3, 3, 0, 2, 1, 1, 1] n1222 := by
  exact checkExponentBoxTree_join c1223 c1244 (by decide +kernel)

private theorem c1176 : C ![2, 2, 0, 1, 0, 0, 0] ![3, 3, 0, 2, 1, 1, 1] n1176 := by
  exact checkExponentBoxTree_join c1177 c1222 (by decide +kernel)

private theorem c1263 : C ![2, 2, 1, 1, 0, 0, 0] ![3, 3, 1, 2, 0, 0, 1] n1263 := by
  decide +kernel

private theorem c1293 : C ![2, 2, 1, 1, 0, 1, 0] ![3, 3, 1, 2, 0, 1, 0] n1293 := by
  decide +kernel

private theorem c1308 : C ![2, 2, 1, 1, 0, 1, 1] ![3, 3, 1, 2, 0, 1, 1] n1308 := by
  decide +kernel

private theorem c1292 : C ![2, 2, 1, 1, 0, 1, 0] ![3, 3, 1, 2, 0, 1, 1] n1292 := by
  exact checkExponentBoxTree_join c1293 c1308 (by decide +kernel)

private theorem c1262 : C ![2, 2, 1, 1, 0, 0, 0] ![3, 3, 1, 2, 0, 1, 1] n1262 := by
  exact checkExponentBoxTree_join c1263 c1292 (by decide +kernel)

private theorem c1321 : C ![2, 2, 1, 1, 1, 0, 0] ![3, 3, 1, 2, 1, 0, 0] n1321 := by
  decide +kernel

private theorem c1336 : C ![2, 2, 1, 1, 1, 0, 1] ![3, 3, 1, 2, 1, 0, 1] n1336 := by
  decide +kernel

private theorem c1320 : C ![2, 2, 1, 1, 1, 0, 0] ![3, 3, 1, 2, 1, 0, 1] n1320 := by
  exact checkExponentBoxTree_join c1321 c1336 (by decide +kernel)

private theorem c1348 : C ![2, 2, 1, 1, 1, 1, 0] ![3, 3, 1, 2, 1, 1, 0] n1348 := by
  decide +kernel

private theorem c1360 : C ![2, 2, 1, 1, 1, 1, 1] ![3, 3, 1, 1, 1, 1, 1] n1360 := by
  decide +kernel

private theorem c1363 : C ![2, 2, 1, 2, 1, 1, 1] ![3, 3, 1, 2, 1, 1, 1] n1363 := by
  decide +kernel

private theorem c1359 : C ![2, 2, 1, 1, 1, 1, 1] ![3, 3, 1, 2, 1, 1, 1] n1359 := by
  exact checkExponentBoxTree_join c1360 c1363 (by decide +kernel)

private theorem c1347 : C ![2, 2, 1, 1, 1, 1, 0] ![3, 3, 1, 2, 1, 1, 1] n1347 := by
  exact checkExponentBoxTree_join c1348 c1359 (by decide +kernel)

private theorem c1319 : C ![2, 2, 1, 1, 1, 0, 0] ![3, 3, 1, 2, 1, 1, 1] n1319 := by
  exact checkExponentBoxTree_join c1320 c1347 (by decide +kernel)

private theorem c1261 : C ![2, 2, 1, 1, 0, 0, 0] ![3, 3, 1, 2, 1, 1, 1] n1261 := by
  exact checkExponentBoxTree_join c1262 c1319 (by decide +kernel)

private theorem c1175 : C ![2, 2, 0, 1, 0, 0, 0] ![3, 3, 1, 2, 1, 1, 1] n1175 := by
  exact checkExponentBoxTree_join c1176 c1261 (by decide +kernel)

private theorem c1369 : C ![2, 4, 0, 1, 0, 0, 0] ![3, 7, 0, 2, 0, 0, 1] n1369 := by
  decide +kernel

private theorem c1384 : C ![2, 4, 0, 1, 0, 1, 0] ![3, 7, 0, 2, 0, 1, 1] n1384 := by
  decide +kernel

private theorem c1368 : C ![2, 4, 0, 1, 0, 0, 0] ![3, 7, 0, 2, 0, 1, 1] n1368 := by
  exact checkExponentBoxTree_join c1369 c1384 (by decide +kernel)

private theorem c1398 : C ![2, 4, 0, 1, 1, 0, 0] ![3, 7, 0, 2, 1, 0, 1] n1398 := by
  decide +kernel

private theorem c1414 : C ![2, 4, 0, 1, 1, 1, 0] ![3, 7, 0, 2, 1, 1, 0] n1414 := by
  decide +kernel

private theorem c1419 : C ![2, 4, 0, 1, 1, 1, 1] ![3, 7, 0, 2, 1, 1, 1] n1419 := by
  decide +kernel

private theorem c1413 : C ![2, 4, 0, 1, 1, 1, 0] ![3, 7, 0, 2, 1, 1, 1] n1413 := by
  exact checkExponentBoxTree_join c1414 c1419 (by decide +kernel)

private theorem c1397 : C ![2, 4, 0, 1, 1, 0, 0] ![3, 7, 0, 2, 1, 1, 1] n1397 := by
  exact checkExponentBoxTree_join c1398 c1413 (by decide +kernel)

private theorem c1367 : C ![2, 4, 0, 1, 0, 0, 0] ![3, 7, 0, 2, 1, 1, 1] n1367 := by
  exact checkExponentBoxTree_join c1368 c1397 (by decide +kernel)

private theorem c1423 : C ![2, 4, 1, 1, 0, 0, 0] ![3, 7, 1, 2, 0, 0, 0] n1423 := by
  decide +kernel

private theorem c1440 : C ![2, 4, 1, 1, 0, 0, 1] ![3, 7, 1, 2, 0, 0, 1] n1440 := by
  decide +kernel

private theorem c1422 : C ![2, 4, 1, 1, 0, 0, 0] ![3, 7, 1, 2, 0, 0, 1] n1422 := by
  exact checkExponentBoxTree_join c1423 c1440 (by decide +kernel)

private theorem c1450 : C ![2, 4, 1, 1, 0, 1, 0] ![3, 7, 1, 2, 0, 1, 0] n1450 := by
  decide +kernel

private theorem c1460 : C ![2, 4, 1, 1, 0, 1, 1] ![3, 5, 1, 2, 0, 1, 1] n1460 := by
  decide +kernel

private theorem c1463 : C ![2, 6, 1, 1, 0, 1, 1] ![3, 7, 1, 2, 0, 1, 1] n1463 := by
  decide +kernel

private theorem c1459 : C ![2, 4, 1, 1, 0, 1, 1] ![3, 7, 1, 2, 0, 1, 1] n1459 := by
  exact checkExponentBoxTree_join c1460 c1463 (by decide +kernel)

private theorem c1449 : C ![2, 4, 1, 1, 0, 1, 0] ![3, 7, 1, 2, 0, 1, 1] n1449 := by
  exact checkExponentBoxTree_join c1450 c1459 (by decide +kernel)

private theorem c1421 : C ![2, 4, 1, 1, 0, 0, 0] ![3, 7, 1, 2, 0, 1, 1] n1421 := by
  exact checkExponentBoxTree_join c1422 c1449 (by decide +kernel)

private theorem c1466 : C ![2, 4, 1, 1, 1, 0, 0] ![3, 7, 1, 2, 1, 0, 0] n1466 := by
  decide +kernel

private theorem c1478 : C ![2, 4, 1, 1, 1, 0, 1] ![3, 5, 1, 2, 1, 0, 1] n1478 := by
  decide +kernel

private theorem c1483 : C ![2, 6, 1, 1, 1, 0, 1] ![3, 7, 1, 2, 1, 0, 1] n1483 := by
  decide +kernel

private theorem c1477 : C ![2, 4, 1, 1, 1, 0, 1] ![3, 7, 1, 2, 1, 0, 1] n1477 := by
  exact checkExponentBoxTree_join c1478 c1483 (by decide +kernel)

private theorem c1465 : C ![2, 4, 1, 1, 1, 0, 0] ![3, 7, 1, 2, 1, 0, 1] n1465 := by
  exact checkExponentBoxTree_join c1466 c1477 (by decide +kernel)

private theorem c1486 : C ![2, 4, 1, 1, 1, 1, 0] ![3, 5, 1, 2, 1, 1, 0] n1486 := by
  decide +kernel

private theorem c1491 : C ![2, 6, 1, 1, 1, 1, 0] ![3, 7, 1, 2, 1, 1, 0] n1491 := by
  decide +kernel

private theorem c1485 : C ![2, 4, 1, 1, 1, 1, 0] ![3, 7, 1, 2, 1, 1, 0] n1485 := by
  exact checkExponentBoxTree_join c1486 c1491 (by decide +kernel)

private theorem c1494 : C ![2, 4, 1, 1, 1, 1, 1] ![3, 5, 1, 1, 1, 1, 1] n1494 := by
  decide +kernel

private theorem c1495 : C ![2, 4, 1, 2, 1, 1, 1] ![3, 5, 1, 2, 1, 1, 1] n1495 := by
  decide +kernel

private theorem c1493 : C ![2, 4, 1, 1, 1, 1, 1] ![3, 5, 1, 2, 1, 1, 1] n1493 := by
  exact checkExponentBoxTree_join c1494 c1495 (by decide +kernel)

private theorem c1496 : C ![2, 6, 1, 1, 1, 1, 1] ![3, 7, 1, 2, 1, 1, 1] n1496 := by
  decide +kernel

private theorem c1492 : C ![2, 4, 1, 1, 1, 1, 1] ![3, 7, 1, 2, 1, 1, 1] n1492 := by
  exact checkExponentBoxTree_join c1493 c1496 (by decide +kernel)

private theorem c1484 : C ![2, 4, 1, 1, 1, 1, 0] ![3, 7, 1, 2, 1, 1, 1] n1484 := by
  exact checkExponentBoxTree_join c1485 c1492 (by decide +kernel)

private theorem c1464 : C ![2, 4, 1, 1, 1, 0, 0] ![3, 7, 1, 2, 1, 1, 1] n1464 := by
  exact checkExponentBoxTree_join c1465 c1484 (by decide +kernel)

private theorem c1420 : C ![2, 4, 1, 1, 0, 0, 0] ![3, 7, 1, 2, 1, 1, 1] n1420 := by
  exact checkExponentBoxTree_join c1421 c1464 (by decide +kernel)

private theorem c1366 : C ![2, 4, 0, 1, 0, 0, 0] ![3, 7, 1, 2, 1, 1, 1] n1366 := by
  exact checkExponentBoxTree_join c1367 c1420 (by decide +kernel)

private theorem c1174 : C ![2, 2, 0, 1, 0, 0, 0] ![3, 7, 1, 2, 1, 1, 1] n1174 := by
  exact checkExponentBoxTree_join c1175 c1366 (by decide +kernel)

private theorem c1006 : C ![2, 2, 0, 0, 0, 0, 0] ![3, 7, 1, 2, 1, 1, 1] n1006 := by
  exact checkExponentBoxTree_join c1007 c1174 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n1006

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c1006

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main02
