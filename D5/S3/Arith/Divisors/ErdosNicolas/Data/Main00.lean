/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main00
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main00.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts00

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main00

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![0, 0, 0, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![3, 1, 3, 2, 1, 1, 1]

private def n9 : MainTree := .leaf (mainGapLeaf ![0, 0, 0, 0, 0, 1, 1])
private def n10 : MainTree := .leaf (mainGapLeaf ![0, 0, 0, 0, 1, 1, 1])
private def n8 : MainTree := .split 4 0 n9 n10
private def n12 : MainTree := .leaf (mainGapLeaf ![0, 0, 1, 0, 0, 1, 1])
private def n13 : MainTree := .leaf (mainGapLeaf ![0, 0, 1, 0, 1, 1, 1])
private def n11 : MainTree := .split 4 0 n12 n13
private def n7 : MainTree := .split 2 0 n8 n11
private def n16 : MainTree := .leaf (mainGapLeaf ![0, 1, 0, 0, 0, 1, 1])
private def n17 : MainTree := .leaf (mainRankLeaf 1 ![0, 1, 0, 0, 1, 1, 1])
private def n15 : MainTree := .split 4 0 n16 n17
private def n20 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 0, 0, 0, 1])
private def n21 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 0, 0, 1, 1])
private def n19 : MainTree := .split 5 0 n20 n21
private def n23 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 0, 1, 0, 1])
private def n24 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 0, 1, 1, 1])
private def n22 : MainTree := .split 5 0 n23 n24
private def n18 : MainTree := .split 4 0 n19 n22
private def n14 : MainTree := .split 2 0 n15 n18
private def n6 : MainTree := .split 1 0 n7 n14
private def n29 : MainTree := .leaf (mainGapLeaf ![1, 0, 0, 0, 0, 0, 1])
private def n30 : MainTree := .leaf (mainGapLeaf ![1, 0, 0, 0, 0, 1, 1])
private def n28 : MainTree := .split 5 0 n29 n30
private def n32 : MainTree := .leaf (mainGapLeaf ![1, 0, 0, 0, 1, 0, 1])
private def n33 : MainTree := .leaf (mainGapLeaf ![1, 0, 0, 0, 1, 1, 1])
private def n31 : MainTree := .split 5 0 n32 n33
private def n27 : MainTree := .split 4 0 n28 n31
private def n36 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 0, 0, 0, 1])
private def n37 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 0, 0, 1, 1])
private def n35 : MainTree := .split 5 0 n36 n37
private def n39 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 0, 1, 0, 1])
private def n40 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 0, 1, 1, 1])
private def n38 : MainTree := .split 5 0 n39 n40
private def n34 : MainTree := .split 4 0 n35 n38
private def n26 : MainTree := .split 2 0 n27 n34
private def n45 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 0, 0, 0, 0])
private def n46 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 0, 0, 0, 1])
private def n44 : MainTree := .split 6 0 n45 n46
private def n47 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 0, 0, 1, 1])
private def n43 : MainTree := .split 5 0 n44 n47
private def n50 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 0, 1, 0, 0])
private def n51 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 0, 1, 0, 1])
private def n49 : MainTree := .split 6 0 n50 n51
private def n52 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 0, 1, 1, 1])
private def n48 : MainTree := .split 5 0 n49 n52
private def n42 : MainTree := .split 4 0 n43 n48
private def n56 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 0, 0, 0])
private def n57 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 0, 0, 1])
private def n55 : MainTree := .split 6 0 n56 n57
private def n59 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 0, 1, 0])
private def n60 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 0, 1, 1])
private def n58 : MainTree := .split 6 0 n59 n60
private def n54 : MainTree := .split 5 0 n55 n58
private def n63 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 1, 0, 0])
private def n64 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 1, 0, 1])
private def n62 : MainTree := .split 6 0 n63 n64
private def n66 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 1, 1, 0])
private def n67 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 0, 1, 1, 1])
private def n65 : MainTree := .split 6 0 n66 n67
private def n61 : MainTree := .split 5 0 n62 n65
private def n53 : MainTree := .split 4 0 n54 n61
private def n41 : MainTree := .split 2 0 n42 n53
private def n25 : MainTree := .split 1 0 n26 n41
private def n5 : MainTree := .split 0 0 n6 n25
private def n72 : MainTree := .leaf (mainGapLeaf ![0, 0, 0, 2, 0, 1, 1])
private def n73 : MainTree := .leaf (mainGapLeaf ![0, 0, 0, 2, 1, 1, 1])
private def n71 : MainTree := .split 4 0 n72 n73
private def n76 : MainTree := .leaf (mainGapLeaf ![0, 0, 1, 2, 0, 0, 1])
private def n77 : MainTree := .leaf (mainGapLeaf ![0, 0, 1, 2, 0, 1, 1])
private def n75 : MainTree := .split 5 0 n76 n77
private def n79 : MainTree := .leaf (mainGapLeaf ![0, 0, 1, 2, 1, 0, 1])
private def n80 : MainTree := .leaf (mainGapLeaf ![0, 0, 1, 2, 1, 1, 1])
private def n78 : MainTree := .split 5 0 n79 n80
private def n74 : MainTree := .split 4 0 n75 n78
private def n70 : MainTree := .split 2 0 n71 n74
private def n84 : MainTree := .leaf (mainGapLeaf ![0, 1, 0, 2, 0, 0, 1])
private def n85 : MainTree := .leaf (mainGapLeaf ![0, 1, 0, 2, 0, 1, 1])
private def n83 : MainTree := .split 5 0 n84 n85
private def n87 : MainTree := .leaf (mainGapLeaf ![0, 1, 0, 2, 1, 0, 1])
private def n88 : MainTree := .leaf (mainGapLeaf ![0, 1, 0, 2, 1, 1, 1])
private def n86 : MainTree := .split 5 0 n87 n88
private def n82 : MainTree := .split 4 0 n83 n86
private def n92 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 2, 0, 0, 0])
private def n93 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 2, 0, 0, 1])
private def n91 : MainTree := .split 6 0 n92 n93
private def n94 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 2, 0, 1, 1])
private def n90 : MainTree := .split 5 0 n91 n94
private def n96 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 2, 1, 0, 1])
private def n97 : MainTree := .leaf (mainGapLeaf ![0, 1, 1, 2, 1, 1, 1])
private def n95 : MainTree := .split 5 0 n96 n97
private def n89 : MainTree := .split 4 0 n90 n95
private def n81 : MainTree := .split 2 0 n82 n89
private def n69 : MainTree := .split 1 0 n70 n81
private def n102 : MainTree := .leaf (mainGapLeaf ![1, 0, 0, 2, 0, 0, 1])
private def n103 : MainTree := .leaf (mainRankLeaf 1 ![1, 0, 0, 2, 0, 1, 1])
private def n101 : MainTree := .split 5 0 n102 n103
private def n105 : MainTree := .leaf (mainGapLeaf ![1, 0, 0, 2, 1, 0, 1])
private def n106 : MainTree := .leaf (mainGapLeaf ![1, 0, 0, 2, 1, 1, 1])
private def n104 : MainTree := .split 5 0 n105 n106
private def n100 : MainTree := .split 4 0 n101 n104
private def n110 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 2, 0, 0, 0])
private def n111 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 2, 0, 0, 1])
private def n109 : MainTree := .split 6 0 n110 n111
private def n113 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 2, 0, 1, 0])
private def n114 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 2, 0, 1, 1])
private def n112 : MainTree := .split 6 0 n113 n114
private def n108 : MainTree := .split 5 0 n109 n112
private def n117 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 2, 1, 0, 0])
private def n118 : MainTree := .leaf (mainGapLeaf ![1, 0, 1, 2, 1, 0, 1])
private def n116 : MainTree := .split 6 0 n117 n118
private def n119 : MainTree := .leaf (mainRankLeaf 1 ![1, 0, 1, 2, 1, 1, 1])
private def n115 : MainTree := .split 5 0 n116 n119
private def n107 : MainTree := .split 4 0 n108 n115
private def n99 : MainTree := .split 2 0 n100 n107
private def n125 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 1, 0, 0, 0])
private def n126 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 0, 0, 0])
private def n124 : MainTree := .split 3 1 n125 n126
private def n127 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 0, 0, 1])
private def n123 : MainTree := .split 6 0 n124 n127
private def n129 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 0, 1, 0])
private def n130 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 0, 1, 1])
private def n128 : MainTree := .split 6 0 n129 n130
private def n122 : MainTree := .split 5 0 n123 n128
private def n133 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 1, 0, 0])
private def n134 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 1, 0, 1])
private def n132 : MainTree := .split 6 0 n133 n134
private def n136 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 1, 1, 0])
private def n137 : MainTree := .leaf (mainGapLeaf ![1, 1, 0, 2, 1, 1, 1])
private def n135 : MainTree := .split 6 0 n136 n137
private def n131 : MainTree := .split 5 0 n132 n135
private def n121 : MainTree := .split 4 0 n122 n131
private def n142 : MainTree := .leaf (mainRankLeaf 2 ![1, 1, 1, 1, 0, 0, 0])
private def n143 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 2, 0, 0, 0])
private def n141 : MainTree := .split 3 1 n142 n143
private def n144 : MainTree := .leaf (mainRankLeaf 1 ![1, 1, 1, 2, 0, 0, 1])
private def n140 : MainTree := .split 6 0 n141 n144
private def n146 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 2, 0, 1, 0])
private def n147 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 2, 0, 1, 1])
private def n145 : MainTree := .split 6 0 n146 n147
private def n139 : MainTree := .split 5 0 n140 n145
private def n151 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 1, 1, 0, 0])
private def n152 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 2, 1, 0, 0])
private def n150 : MainTree := .split 3 1 n151 n152
private def n153 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 2, 1, 0, 1])
private def n149 : MainTree := .split 6 0 n150 n153
private def n155 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 2, 1, 1, 0])
private def n156 : MainTree := .leaf (mainGapLeaf ![1, 1, 1, 2, 1, 1, 1])
private def n154 : MainTree := .split 6 0 n155 n156
private def n148 : MainTree := .split 5 0 n149 n154
private def n138 : MainTree := .split 4 0 n139 n148
private def n120 : MainTree := .split 2 0 n121 n138
private def n98 : MainTree := .split 1 0 n99 n120
private def n68 : MainTree := .split 0 0 n69 n98
private def n4 : MainTree := .split 3 0 n5 n68
private def n161 : MainTree := .leaf (mainGapLeaf ![0, 0, 3, 0, 0, 1, 1])
private def n162 : MainTree := .leaf (mainGapLeaf ![0, 0, 3, 0, 1, 1, 1])
private def n160 : MainTree := .split 4 0 n161 n162
private def n165 : MainTree := .leaf (mainGapLeaf ![0, 1, 3, 0, 0, 0, 1])
private def n166 : MainTree := .leaf (mainGapLeaf ![0, 1, 3, 0, 0, 1, 1])
private def n164 : MainTree := .split 5 0 n165 n166
private def n168 : MainTree := .leaf (mainGapLeaf ![0, 1, 3, 0, 1, 0, 1])
private def n169 : MainTree := .leaf (mainGapLeaf ![0, 1, 3, 0, 1, 1, 1])
private def n167 : MainTree := .split 5 0 n168 n169
private def n163 : MainTree := .split 4 0 n164 n167
private def n159 : MainTree := .split 1 0 n160 n163
private def n173 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 0, 0, 0, 1])
private def n174 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 0, 0, 1, 1])
private def n172 : MainTree := .split 5 0 n173 n174
private def n176 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 0, 1, 0, 1])
private def n177 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 0, 1, 1, 1])
private def n175 : MainTree := .split 5 0 n176 n177
private def n171 : MainTree := .split 4 0 n172 n175
private def n181 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 0, 0, 0])
private def n182 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 0, 0, 1])
private def n180 : MainTree := .split 6 0 n181 n182
private def n184 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 0, 1, 0])
private def n185 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 0, 1, 1])
private def n183 : MainTree := .split 6 0 n184 n185
private def n179 : MainTree := .split 5 0 n180 n183
private def n188 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 1, 0, 0])
private def n189 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 1, 0, 1])
private def n187 : MainTree := .split 6 0 n188 n189
private def n191 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 1, 1, 0])
private def n192 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 0, 1, 1, 1])
private def n190 : MainTree := .split 6 0 n191 n192
private def n186 : MainTree := .split 5 0 n187 n190
private def n178 : MainTree := .split 4 0 n179 n186
private def n170 : MainTree := .split 1 0 n171 n178
private def n158 : MainTree := .split 0 0 n159 n170
private def n197 : MainTree := .leaf (mainGapLeaf ![0, 0, 3, 2, 0, 0, 1])
private def n198 : MainTree := .leaf (mainGapLeaf ![0, 0, 3, 2, 0, 1, 1])
private def n196 : MainTree := .split 5 0 n197 n198
private def n199 : MainTree := .leaf (mainGapLeaf ![0, 0, 3, 2, 1, 1, 1])
private def n195 : MainTree := .split 4 0 n196 n199
private def n202 : MainTree := .leaf (mainRankLeaf 1 ![0, 1, 3, 2, 0, 0, 1])
private def n203 : MainTree := .leaf (mainGapLeaf ![0, 1, 3, 2, 0, 1, 1])
private def n201 : MainTree := .split 5 0 n202 n203
private def n205 : MainTree := .leaf (mainGapLeaf ![0, 1, 3, 2, 1, 0, 1])
private def n206 : MainTree := .leaf (mainGapLeaf ![0, 1, 3, 2, 1, 1, 1])
private def n204 : MainTree := .split 5 0 n205 n206
private def n200 : MainTree := .split 4 0 n201 n204
private def n194 : MainTree := .split 1 0 n195 n200
private def n211 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 2, 0, 0, 0])
private def n212 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 2, 0, 0, 1])
private def n210 : MainTree := .split 6 0 n211 n212
private def n214 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 2, 0, 1, 0])
private def n215 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 2, 0, 1, 1])
private def n213 : MainTree := .split 6 0 n214 n215
private def n209 : MainTree := .split 5 0 n210 n213
private def n218 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 2, 1, 0, 0])
private def n219 : MainTree := .leaf (mainGapLeaf ![1, 0, 3, 2, 1, 0, 1])
private def n217 : MainTree := .split 6 0 n218 n219
private def n220 : MainTree := .leaf (mainRankLeaf 1 ![1, 0, 3, 2, 1, 1, 1])
private def n216 : MainTree := .split 5 0 n217 n220
private def n208 : MainTree := .split 4 0 n209 n216
private def n225 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 1, 0, 0, 0])
private def n226 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 2, 0, 0, 0])
private def n224 : MainTree := .split 3 1 n225 n226
private def n227 : MainTree := .leaf (mainRankLeaf 1 ![1, 1, 3, 2, 0, 0, 1])
private def n223 : MainTree := .split 6 0 n224 n227
private def n229 : MainTree := .leaf (mainRankLeaf 1 ![1, 1, 3, 2, 0, 1, 0])
private def n230 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 2, 0, 1, 1])
private def n228 : MainTree := .split 6 0 n229 n230
private def n222 : MainTree := .split 5 0 n223 n228
private def n234 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 1, 1, 0, 0])
private def n235 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 2, 1, 0, 0])
private def n233 : MainTree := .split 3 1 n234 n235
private def n236 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 2, 1, 0, 1])
private def n232 : MainTree := .split 6 0 n233 n236
private def n238 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 2, 1, 1, 0])
private def n239 : MainTree := .leaf (mainGapLeaf ![1, 1, 3, 2, 1, 1, 1])
private def n237 : MainTree := .split 6 0 n238 n239
private def n231 : MainTree := .split 5 0 n232 n237
private def n221 : MainTree := .split 4 0 n222 n231
private def n207 : MainTree := .split 1 0 n208 n221
private def n193 : MainTree := .split 0 0 n194 n207
private def n157 : MainTree := .split 3 0 n158 n193
private def n3 : MainTree := .split 2 1 n4 n157
private def n247 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 0, 0, 0, 0])
private def n248 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 0, 0, 0, 1])
private def n246 : MainTree := .split 6 0 n247 n248
private def n249 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 0, 0, 1, 1])
private def n245 : MainTree := .split 5 0 n246 n249
private def n252 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 0, 1, 0, 0])
private def n253 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 0, 1, 0, 1])
private def n251 : MainTree := .split 6 0 n252 n253
private def n254 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 0, 1, 1, 1])
private def n250 : MainTree := .split 5 0 n251 n254
private def n244 : MainTree := .split 4 0 n245 n250
private def n259 : MainTree := .leaf (mainGapLeaf ![2, 0, 1, 0, 0, 0, 0])
private def n260 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 0, 0, 0])
private def n258 : MainTree := .split 0 2 n259 n260
private def n261 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 0, 0, 1])
private def n257 : MainTree := .split 6 0 n258 n261
private def n263 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 0, 1, 0])
private def n264 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 0, 1, 1])
private def n262 : MainTree := .split 6 0 n263 n264
private def n256 : MainTree := .split 5 0 n257 n262
private def n268 : MainTree := .leaf (mainGapLeaf ![2, 0, 1, 0, 1, 0, 0])
private def n269 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 1, 0, 0])
private def n267 : MainTree := .split 0 2 n268 n269
private def n270 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 1, 0, 1])
private def n266 : MainTree := .split 6 0 n267 n270
private def n272 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 1, 1, 0])
private def n273 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 0, 1, 1, 1])
private def n271 : MainTree := .split 6 0 n272 n273
private def n265 : MainTree := .split 5 0 n266 n271
private def n255 : MainTree := .split 4 0 n256 n265
private def n243 : MainTree := .split 2 0 n244 n255
private def n279 : MainTree := .leaf (mainFullLeaf ![2, 1, 0, 0, 0, 0, 0])
private def n280 : MainTree := .leaf (mainFullLeaf ![3, 1, 0, 0, 0, 0, 0])
private def n278 : MainTree := .split 0 2 n279 n280
private def n281 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 0, 0, 0, 1])
private def n277 : MainTree := .split 6 0 n278 n281
private def n284 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 0, 0, 1, 0])
private def n285 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 0, 0, 1, 0])
private def n283 : MainTree := .split 0 2 n284 n285
private def n286 : MainTree := .leaf (mainRankLeaf 1 ![3, 1, 0, 0, 0, 1, 1])
private def n282 : MainTree := .split 6 0 n283 n286
private def n276 : MainTree := .split 5 0 n277 n282
private def n290 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 0, 1, 0, 0])
private def n291 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 0, 1, 0, 0])
private def n289 : MainTree := .split 0 2 n290 n291
private def n292 : MainTree := .leaf (mainRankLeaf 1 ![3, 1, 0, 0, 1, 0, 1])
private def n288 : MainTree := .split 6 0 n289 n292
private def n295 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 0, 1, 1, 0])
private def n296 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 0, 1, 1, 0])
private def n294 : MainTree := .split 0 2 n295 n296
private def n297 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 0, 1, 1, 1])
private def n293 : MainTree := .split 6 0 n294 n297
private def n287 : MainTree := .split 5 0 n288 n293
private def n275 : MainTree := .split 4 0 n276 n287
private def n302 : MainTree := .leaf (mainFullLeaf ![2, 1, 1, 0, 0, 0, 0])
private def n303 : MainTree := .leaf (mainFullLeaf ![3, 1, 1, 0, 0, 0, 0])
private def n301 : MainTree := .split 0 2 n302 n303
private def n305 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 0, 0, 0, 1])
private def n306 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 0, 0, 0, 1])
private def n304 : MainTree := .split 0 2 n305 n306
private def n300 : MainTree := .split 6 0 n301 n304
private def n309 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 0, 0, 1, 0])
private def n310 : MainTree := .leaf (mainRankLeaf 2 ![3, 1, 1, 0, 0, 1, 0])
private def n308 : MainTree := .split 0 2 n309 n310
private def n312 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 0, 0, 1, 1])
private def n313 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 0, 0, 1, 1])
private def n311 : MainTree := .split 0 2 n312 n313
private def n307 : MainTree := .split 6 0 n308 n311
private def n299 : MainTree := .split 5 0 n300 n307
private def n317 : MainTree := .leaf (mainRankLeaf 2 ![2, 1, 1, 0, 1, 0, 0])
private def n318 : MainTree := .leaf (mainFullLeaf ![3, 1, 1, 0, 1, 0, 0])
private def n316 : MainTree := .split 0 2 n317 n318
private def n320 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 0, 1, 0, 1])
private def n321 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 0, 1, 0, 1])
private def n319 : MainTree := .split 0 2 n320 n321
private def n315 : MainTree := .split 6 0 n316 n319
private def n324 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 0, 1, 1, 0])
private def n325 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 0, 1, 1, 0])
private def n323 : MainTree := .split 0 2 n324 n325
private def n327 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 0, 1, 1, 1])
private def n328 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 0, 1, 1, 1])
private def n326 : MainTree := .split 0 2 n327 n328
private def n322 : MainTree := .split 6 0 n323 n326
private def n314 : MainTree := .split 5 0 n315 n322
private def n298 : MainTree := .split 4 0 n299 n314
private def n274 : MainTree := .split 2 0 n275 n298
private def n242 : MainTree := .split 1 0 n243 n274
private def n336 : MainTree := .leaf (mainGapLeaf ![2, 0, 0, 1, 0, 0, 0])
private def n337 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 1, 0, 0, 0])
private def n335 : MainTree := .split 0 2 n336 n337
private def n338 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 2, 0, 0, 0])
private def n334 : MainTree := .split 3 1 n335 n338
private def n339 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 2, 0, 0, 1])
private def n333 : MainTree := .split 6 0 n334 n339
private def n342 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 0, 1, 0, 1, 0])
private def n343 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 2, 0, 1, 0])
private def n341 : MainTree := .split 3 1 n342 n343
private def n344 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 2, 0, 1, 1])
private def n340 : MainTree := .split 6 0 n341 n344
private def n332 : MainTree := .split 5 0 n333 n340
private def n347 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 2, 1, 0, 0])
private def n348 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 2, 1, 0, 1])
private def n346 : MainTree := .split 6 0 n347 n348
private def n350 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 0, 2, 1, 1, 0])
private def n351 : MainTree := .leaf (mainGapLeaf ![3, 0, 0, 2, 1, 1, 1])
private def n349 : MainTree := .split 6 0 n350 n351
private def n345 : MainTree := .split 5 0 n346 n349
private def n331 : MainTree := .split 4 0 n332 n345
private def n357 : MainTree := .leaf (mainGapLeaf ![2, 0, 1, 1, 0, 0, 0])
private def n358 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 1, 0, 0, 0])
private def n356 : MainTree := .split 0 2 n357 n358
private def n359 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 2, 0, 0, 0])
private def n355 : MainTree := .split 3 1 n356 n359
private def n361 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 1, 1, 0, 0, 1])
private def n362 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 2, 0, 0, 1])
private def n360 : MainTree := .split 3 1 n361 n362
private def n354 : MainTree := .split 6 0 n355 n360
private def n365 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 1, 0, 1, 0])
private def n366 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 2, 0, 1, 0])
private def n364 : MainTree := .split 3 1 n365 n366
private def n367 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 2, 0, 1, 1])
private def n363 : MainTree := .split 6 0 n364 n367
private def n353 : MainTree := .split 5 0 n354 n363
private def n372 : MainTree := .leaf (mainGapLeaf ![2, 0, 1, 1, 1, 0, 0])
private def n373 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 1, 1, 0, 0])
private def n371 : MainTree := .split 0 2 n372 n373
private def n374 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 2, 1, 0, 0])
private def n370 : MainTree := .split 3 1 n371 n374
private def n375 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 1, 2, 1, 0, 1])
private def n369 : MainTree := .split 6 0 n370 n375
private def n378 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 1, 1, 1, 0])
private def n379 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 2, 1, 1, 0])
private def n377 : MainTree := .split 3 1 n378 n379
private def n380 : MainTree := .leaf (mainGapLeaf ![3, 0, 1, 2, 1, 1, 1])
private def n376 : MainTree := .split 6 0 n377 n380
private def n368 : MainTree := .split 5 0 n369 n376
private def n352 : MainTree := .split 4 0 n353 n368
private def n330 : MainTree := .split 2 0 n331 n352
private def n387 : MainTree := .leaf (mainRankLeaf 2 ![2, 1, 0, 1, 0, 0, 0])
private def n388 : MainTree := .leaf (mainFullLeaf ![3, 1, 0, 1, 0, 0, 0])
private def n386 : MainTree := .split 0 2 n387 n388
private def n390 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 2, 0, 0, 0])
private def n391 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 0, 0, 0])
private def n389 : MainTree := .split 0 2 n390 n391
private def n385 : MainTree := .split 3 1 n386 n389
private def n394 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 1, 0, 0, 1])
private def n395 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 1, 0, 0, 1])
private def n393 : MainTree := .split 0 2 n394 n395
private def n396 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 0, 0, 1])
private def n392 : MainTree := .split 3 1 n393 n396
private def n384 : MainTree := .split 6 0 n385 n392
private def n400 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 1, 0, 1, 0])
private def n401 : MainTree := .leaf (mainRankLeaf 2 ![3, 1, 0, 1, 0, 1, 0])
private def n399 : MainTree := .split 0 2 n400 n401
private def n403 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 2, 0, 1, 0])
private def n404 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 0, 1, 0])
private def n402 : MainTree := .split 0 2 n403 n404
private def n398 : MainTree := .split 3 1 n399 n402
private def n406 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 1, 0, 1, 1])
private def n407 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 0, 1, 1])
private def n405 : MainTree := .split 3 1 n406 n407
private def n397 : MainTree := .split 6 0 n398 n405
private def n383 : MainTree := .split 5 0 n384 n397
private def n412 : MainTree := .leaf (mainRankLeaf 1 ![2, 1, 0, 1, 1, 0, 0])
private def n413 : MainTree := .leaf (mainRankLeaf 2 ![3, 1, 0, 1, 1, 0, 0])
private def n411 : MainTree := .split 0 2 n412 n413
private def n415 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 2, 1, 0, 0])
private def n416 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 1, 0, 0])
private def n414 : MainTree := .split 0 2 n415 n416
private def n410 : MainTree := .split 3 1 n411 n414
private def n419 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 1, 1, 0, 1])
private def n420 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 1, 1, 0, 1])
private def n418 : MainTree := .split 0 2 n419 n420
private def n421 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 1, 0, 1])
private def n417 : MainTree := .split 3 1 n418 n421
private def n409 : MainTree := .split 6 0 n410 n417
private def n425 : MainTree := .leaf (mainGapLeaf ![2, 1, 0, 1, 1, 1, 0])
private def n426 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 1, 1, 1, 0])
private def n424 : MainTree := .split 0 2 n425 n426
private def n427 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 1, 1, 0])
private def n423 : MainTree := .split 3 1 n424 n427
private def n429 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 1, 1, 1, 1])
private def n430 : MainTree := .leaf (mainGapLeaf ![3, 1, 0, 2, 1, 1, 1])
private def n428 : MainTree := .split 3 1 n429 n430
private def n422 : MainTree := .split 6 0 n423 n428
private def n408 : MainTree := .split 5 0 n409 n422
private def n382 : MainTree := .split 4 0 n383 n408
private def n436 : MainTree := .leaf (mainFullLeaf ![2, 1, 1, 1, 0, 0, 0])
private def n437 : MainTree := .leaf (mainFullLeaf ![3, 1, 1, 1, 0, 0, 0])
private def n435 : MainTree := .split 0 2 n436 n437
private def n439 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 2, 0, 0, 0])
private def n440 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 0, 0, 0])
private def n438 : MainTree := .split 0 2 n439 n440
private def n434 : MainTree := .split 3 1 n435 n438
private def n443 : MainTree := .leaf (mainRankLeaf 2 ![2, 1, 1, 1, 0, 0, 1])
private def n444 : MainTree := .leaf (mainRankLeaf 2 ![3, 1, 1, 1, 0, 0, 1])
private def n442 : MainTree := .split 0 2 n443 n444
private def n446 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 2, 0, 0, 1])
private def n447 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 0, 0, 1])
private def n445 : MainTree := .split 0 2 n446 n447
private def n441 : MainTree := .split 3 1 n442 n445
private def n433 : MainTree := .split 6 0 n434 n441
private def n451 : MainTree := .leaf (mainRankLeaf 2 ![2, 1, 1, 1, 0, 1, 0])
private def n452 : MainTree := .leaf (mainRankLeaf 2 ![3, 1, 1, 1, 0, 1, 0])
private def n450 : MainTree := .split 0 2 n451 n452
private def n454 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 2, 0, 1, 0])
private def n455 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 0, 1, 0])
private def n453 : MainTree := .split 0 2 n454 n455
private def n449 : MainTree := .split 3 1 n450 n453
private def n458 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 1, 0, 1, 1])
private def n459 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 1, 0, 1, 1])
private def n457 : MainTree := .split 0 2 n458 n459
private def n460 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 0, 1, 1])
private def n456 : MainTree := .split 3 1 n457 n460
private def n448 : MainTree := .split 6 0 n449 n456
private def n432 : MainTree := .split 5 0 n433 n448
private def n465 : MainTree := .leaf (mainRankLeaf 2 ![2, 1, 1, 1, 1, 0, 0])
private def n466 : MainTree := .leaf (mainFullLeaf ![3, 1, 1, 1, 1, 0, 0])
private def n464 : MainTree := .split 0 2 n465 n466
private def n468 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 2, 1, 0, 0])
private def n469 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 1, 0, 0])
private def n467 : MainTree := .split 0 2 n468 n469
private def n463 : MainTree := .split 3 1 n464 n467
private def n472 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 1, 1, 0, 1])
private def n473 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 1, 1, 0, 1])
private def n471 : MainTree := .split 0 2 n472 n473
private def n474 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 1, 0, 1])
private def n470 : MainTree := .split 3 1 n471 n474
private def n462 : MainTree := .split 6 0 n463 n470
private def n478 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 1, 1, 1, 0])
private def n479 : MainTree := .leaf (mainRankLeaf 2 ![3, 1, 1, 1, 1, 1, 0])
private def n477 : MainTree := .split 0 2 n478 n479
private def n481 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 2, 1, 1, 0])
private def n482 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 1, 1, 0])
private def n480 : MainTree := .split 0 2 n481 n482
private def n476 : MainTree := .split 3 1 n477 n480
private def n485 : MainTree := .leaf (mainGapLeaf ![2, 1, 1, 1, 1, 1, 1])
private def n486 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 1, 1, 1, 1])
private def n484 : MainTree := .split 0 2 n485 n486
private def n487 : MainTree := .leaf (mainGapLeaf ![3, 1, 1, 2, 1, 1, 1])
private def n483 : MainTree := .split 3 1 n484 n487
private def n475 : MainTree := .split 6 0 n476 n483
private def n461 : MainTree := .split 5 0 n462 n475
private def n431 : MainTree := .split 4 0 n432 n461
private def n381 : MainTree := .split 2 0 n382 n431
private def n329 : MainTree := .split 1 0 n330 n381
private def n241 : MainTree := .split 3 0 n242 n329
private def n494 : MainTree := .leaf (mainGapLeaf ![2, 0, 3, 0, 0, 0, 0])
private def n495 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 0, 0, 0, 0])
private def n493 : MainTree := .split 0 2 n494 n495
private def n496 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 0, 0, 0, 1])
private def n492 : MainTree := .split 6 0 n493 n496
private def n498 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 3, 0, 0, 1, 0])
private def n499 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 0, 0, 1, 1])
private def n497 : MainTree := .split 6 0 n498 n499
private def n491 : MainTree := .split 5 0 n492 n497
private def n502 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 3, 0, 1, 0, 0])
private def n503 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 0, 1, 0, 1])
private def n501 : MainTree := .split 6 0 n502 n503
private def n505 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 0, 1, 1, 0])
private def n506 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 0, 1, 1, 1])
private def n504 : MainTree := .split 6 0 n505 n506
private def n500 : MainTree := .split 5 0 n501 n504
private def n490 : MainTree := .split 4 0 n491 n500
private def n512 : MainTree := .leaf (mainGapLeaf ![2, 1, 2, 0, 0, 0, 0])
private def n513 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 0, 0, 0, 0])
private def n511 : MainTree := .split 2 2 n512 n513
private def n515 : MainTree := .leaf (mainRankLeaf 2 ![3, 1, 2, 0, 0, 0, 0])
private def n516 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 0, 0, 0, 0])
private def n514 : MainTree := .split 2 2 n515 n516
private def n510 : MainTree := .split 0 2 n511 n514
private def n518 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 0, 0, 0, 1])
private def n519 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 0, 0, 0, 1])
private def n517 : MainTree := .split 0 2 n518 n519
private def n509 : MainTree := .split 6 0 n510 n517
private def n522 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 0, 0, 1, 0])
private def n524 : MainTree := .leaf (mainGapLeaf ![3, 1, 2, 0, 0, 1, 0])
private def n525 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 0, 0, 1, 0])
private def n523 : MainTree := .split 2 2 n524 n525
private def n521 : MainTree := .split 0 2 n522 n523
private def n527 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 0, 0, 1, 1])
private def n528 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 0, 0, 1, 1])
private def n526 : MainTree := .split 0 2 n527 n528
private def n520 : MainTree := .split 6 0 n521 n526
private def n508 : MainTree := .split 5 0 n509 n520
private def n532 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 0, 1, 0, 0])
private def n533 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 0, 1, 0, 0])
private def n531 : MainTree := .split 0 2 n532 n533
private def n535 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 0, 1, 0, 1])
private def n536 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 0, 1, 0, 1])
private def n534 : MainTree := .split 0 2 n535 n536
private def n530 : MainTree := .split 6 0 n531 n534
private def n539 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 0, 1, 1, 0])
private def n540 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 0, 1, 1, 0])
private def n538 : MainTree := .split 0 2 n539 n540
private def n541 : MainTree := .leaf (mainRankLeaf 1 ![3, 1, 3, 0, 1, 1, 1])
private def n537 : MainTree := .split 6 0 n538 n541
private def n529 : MainTree := .split 5 0 n530 n537
private def n507 : MainTree := .split 4 0 n508 n529
private def n489 : MainTree := .split 1 0 n490 n507
private def n548 : MainTree := .leaf (mainGapLeaf ![2, 0, 3, 1, 0, 0, 0])
private def n549 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 1, 0, 0, 0])
private def n547 : MainTree := .split 0 2 n548 n549
private def n550 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 3, 2, 0, 0, 0])
private def n546 : MainTree := .split 3 1 n547 n550
private def n552 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 1, 0, 0, 1])
private def n553 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 2, 0, 0, 1])
private def n551 : MainTree := .split 3 1 n552 n553
private def n545 : MainTree := .split 6 0 n546 n551
private def n556 : MainTree := .leaf (mainRankLeaf 1 ![3, 0, 3, 1, 0, 1, 0])
private def n557 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 2, 0, 1, 0])
private def n555 : MainTree := .split 3 1 n556 n557
private def n558 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 2, 0, 1, 1])
private def n554 : MainTree := .split 6 0 n555 n558
private def n544 : MainTree := .split 5 0 n545 n554
private def n562 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 1, 1, 0, 0])
private def n563 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 2, 1, 0, 0])
private def n561 : MainTree := .split 3 1 n562 n563
private def n564 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 2, 1, 0, 1])
private def n560 : MainTree := .split 6 0 n561 n564
private def n567 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 1, 1, 1, 0])
private def n568 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 2, 1, 1, 0])
private def n566 : MainTree := .split 3 1 n567 n568
private def n569 : MainTree := .leaf (mainGapLeaf ![3, 0, 3, 2, 1, 1, 1])
private def n565 : MainTree := .split 6 0 n566 n569
private def n559 : MainTree := .split 5 0 n560 n565
private def n543 : MainTree := .split 4 0 n544 n559
private def n576 : MainTree := .leaf (mainRankLeaf 2 ![2, 1, 2, 1, 0, 0, 0])
private def n577 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 1, 0, 0, 0])
private def n575 : MainTree := .split 2 2 n576 n577
private def n579 : MainTree := .leaf (mainFullLeaf ![3, 1, 2, 1, 0, 0, 0])
private def n580 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 1, 0, 0, 0])
private def n578 : MainTree := .split 2 2 n579 n580
private def n574 : MainTree := .split 0 2 n575 n578
private def n582 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 2, 0, 0, 0])
private def n583 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 0, 0, 0])
private def n581 : MainTree := .split 0 2 n582 n583
private def n573 : MainTree := .split 3 1 n574 n581
private def n586 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 1, 0, 0, 1])
private def n587 : MainTree := .leaf (mainRankLeaf 1 ![3, 1, 3, 1, 0, 0, 1])
private def n585 : MainTree := .split 0 2 n586 n587
private def n589 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 2, 0, 0, 1])
private def n590 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 0, 0, 1])
private def n588 : MainTree := .split 0 2 n589 n590
private def n584 : MainTree := .split 3 1 n585 n588
private def n572 : MainTree := .split 6 0 n573 n584
private def n594 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 1, 0, 1, 0])
private def n596 : MainTree := .leaf (mainGapLeaf ![3, 1, 2, 1, 0, 1, 0])
private def n597 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 1, 0, 1, 0])
private def n595 : MainTree := .split 2 2 n596 n597
private def n593 : MainTree := .split 0 2 n594 n595
private def n599 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 2, 0, 1, 0])
private def n600 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 0, 1, 0])
private def n598 : MainTree := .split 0 2 n599 n600
private def n592 : MainTree := .split 3 1 n593 n598
private def n603 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 1, 0, 1, 1])
private def n604 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 1, 0, 1, 1])
private def n602 : MainTree := .split 0 2 n603 n604
private def n605 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 0, 1, 1])
private def n601 : MainTree := .split 3 1 n602 n605
private def n591 : MainTree := .split 6 0 n592 n601
private def n571 : MainTree := .split 5 0 n572 n591
private def n610 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 1, 1, 0, 0])
private def n612 : MainTree := .leaf (mainGapLeaf ![3, 1, 2, 1, 1, 0, 0])
private def n613 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 1, 1, 0, 0])
private def n611 : MainTree := .split 2 2 n612 n613
private def n609 : MainTree := .split 0 2 n610 n611
private def n615 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 2, 1, 0, 0])
private def n616 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 1, 0, 0])
private def n614 : MainTree := .split 0 2 n615 n616
private def n608 : MainTree := .split 3 1 n609 n614
private def n619 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 1, 1, 0, 1])
private def n620 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 1, 1, 0, 1])
private def n618 : MainTree := .split 0 2 n619 n620
private def n621 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 1, 0, 1])
private def n617 : MainTree := .split 3 1 n618 n621
private def n607 : MainTree := .split 6 0 n608 n617
private def n625 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 1, 1, 1, 0])
private def n626 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 1, 1, 1, 0])
private def n624 : MainTree := .split 0 2 n625 n626
private def n628 : MainTree := .leaf (mainGapLeaf ![2, 1, 3, 2, 1, 1, 0])
private def n629 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 1, 1, 0])
private def n627 : MainTree := .split 0 2 n628 n629
private def n623 : MainTree := .split 3 1 n624 n627
private def n631 : MainTree :=
  .leaf (.rankIndexed 1 512 RankReadouts00.rankReadout631)
private def n632 : MainTree := .leaf (mainGapLeaf ![3, 1, 3, 2, 1, 1, 1])
private def n630 : MainTree := .split 3 1 n631 n632
private def n622 : MainTree := .split 6 0 n623 n630
private def n606 : MainTree := .split 5 0 n607 n622
private def n570 : MainTree := .split 4 0 n571 n606
private def n542 : MainTree := .split 1 0 n543 n570
private def n488 : MainTree := .split 3 0 n489 n542
private def n240 : MainTree := .split 2 1 n241 n488
private def n2 : MainTree := .split 0 1 n3 n240

private theorem c5 : C ![0, 0, 0, 0, 0, 0, 0] ![1, 1, 1, 0, 1, 1, 1] n5 := by
  decide +kernel

private theorem c68 : C ![0, 0, 0, 1, 0, 0, 0] ![1, 1, 1, 2, 1, 1, 1] n68 := by
  decide +kernel

private theorem c4 : C ![0, 0, 0, 0, 0, 0, 0] ![1, 1, 1, 2, 1, 1, 1] n4 := by
  exact checkExponentBoxTree_join c5 c68 (by decide +kernel)

private theorem c158 : C ![0, 0, 2, 0, 0, 0, 0] ![1, 1, 3, 0, 1, 1, 1] n158 := by
  decide +kernel

private theorem c194 : C ![0, 0, 2, 1, 0, 0, 0] ![0, 1, 3, 2, 1, 1, 1] n194 := by
  decide +kernel

private theorem c208 : C ![1, 0, 2, 1, 0, 0, 0] ![1, 0, 3, 2, 1, 1, 1] n208 := by
  decide +kernel

private theorem c221 : C ![1, 1, 2, 1, 0, 0, 0] ![1, 1, 3, 2, 1, 1, 1] n221 := by
  decide +kernel

private theorem c207 : C ![1, 0, 2, 1, 0, 0, 0] ![1, 1, 3, 2, 1, 1, 1] n207 := by
  exact checkExponentBoxTree_join c208 c221 (by decide +kernel)

private theorem c193 : C ![0, 0, 2, 1, 0, 0, 0] ![1, 1, 3, 2, 1, 1, 1] n193 := by
  exact checkExponentBoxTree_join c194 c207 (by decide +kernel)

private theorem c157 : C ![0, 0, 2, 0, 0, 0, 0] ![1, 1, 3, 2, 1, 1, 1] n157 := by
  exact checkExponentBoxTree_join c158 c193 (by decide +kernel)

private theorem c3 : C ![0, 0, 0, 0, 0, 0, 0] ![1, 1, 3, 2, 1, 1, 1] n3 := by
  exact checkExponentBoxTree_join c4 c157 (by decide +kernel)

private theorem c242 : C ![2, 0, 0, 0, 0, 0, 0] ![3, 1, 1, 0, 1, 1, 1] n242 := by
  decide +kernel

private theorem c330 : C ![2, 0, 0, 1, 0, 0, 0] ![3, 0, 1, 2, 1, 1, 1] n330 := by
  decide +kernel

private theorem c382 : C ![2, 1, 0, 1, 0, 0, 0] ![3, 1, 0, 2, 1, 1, 1] n382 := by
  decide +kernel

private theorem c432 : C ![2, 1, 1, 1, 0, 0, 0] ![3, 1, 1, 2, 0, 1, 1] n432 := by
  decide +kernel

private theorem c462 : C ![2, 1, 1, 1, 1, 0, 0] ![3, 1, 1, 2, 1, 0, 1] n462 := by
  decide +kernel

private theorem c475 : C ![2, 1, 1, 1, 1, 1, 0] ![3, 1, 1, 2, 1, 1, 1] n475 := by
  decide +kernel

private theorem c461 : C ![2, 1, 1, 1, 1, 0, 0] ![3, 1, 1, 2, 1, 1, 1] n461 := by
  exact checkExponentBoxTree_join c462 c475 (by decide +kernel)

private theorem c431 : C ![2, 1, 1, 1, 0, 0, 0] ![3, 1, 1, 2, 1, 1, 1] n431 := by
  exact checkExponentBoxTree_join c432 c461 (by decide +kernel)

private theorem c381 : C ![2, 1, 0, 1, 0, 0, 0] ![3, 1, 1, 2, 1, 1, 1] n381 := by
  exact checkExponentBoxTree_join c382 c431 (by decide +kernel)

private theorem c329 : C ![2, 0, 0, 1, 0, 0, 0] ![3, 1, 1, 2, 1, 1, 1] n329 := by
  exact checkExponentBoxTree_join c330 c381 (by decide +kernel)

private theorem c241 : C ![2, 0, 0, 0, 0, 0, 0] ![3, 1, 1, 2, 1, 1, 1] n241 := by
  exact checkExponentBoxTree_join c242 c329 (by decide +kernel)

private theorem c489 : C ![2, 0, 2, 0, 0, 0, 0] ![3, 1, 3, 0, 1, 1, 1] n489 := by
  decide +kernel

private theorem c543 : C ![2, 0, 2, 1, 0, 0, 0] ![3, 0, 3, 2, 1, 1, 1] n543 := by
  decide +kernel

private theorem c572 : C ![2, 1, 2, 1, 0, 0, 0] ![3, 1, 3, 2, 0, 0, 1] n572 := by
  decide +kernel

private theorem c591 : C ![2, 1, 2, 1, 0, 1, 0] ![3, 1, 3, 2, 0, 1, 1] n591 := by
  decide +kernel

private theorem c571 : C ![2, 1, 2, 1, 0, 0, 0] ![3, 1, 3, 2, 0, 1, 1] n571 := by
  exact checkExponentBoxTree_join c572 c591 (by decide +kernel)

private theorem c607 : C ![2, 1, 2, 1, 1, 0, 0] ![3, 1, 3, 2, 1, 0, 1] n607 := by
  decide +kernel

private theorem c623 : C ![2, 1, 2, 1, 1, 1, 0] ![3, 1, 3, 2, 1, 1, 0] n623 := by
  decide +kernel

private theorem c630 : C ![2, 1, 2, 1, 1, 1, 1] ![3, 1, 3, 2, 1, 1, 1] n630 := by
  decide +kernel

private theorem c622 : C ![2, 1, 2, 1, 1, 1, 0] ![3, 1, 3, 2, 1, 1, 1] n622 := by
  exact checkExponentBoxTree_join c623 c630 (by decide +kernel)

private theorem c606 : C ![2, 1, 2, 1, 1, 0, 0] ![3, 1, 3, 2, 1, 1, 1] n606 := by
  exact checkExponentBoxTree_join c607 c622 (by decide +kernel)

private theorem c570 : C ![2, 1, 2, 1, 0, 0, 0] ![3, 1, 3, 2, 1, 1, 1] n570 := by
  exact checkExponentBoxTree_join c571 c606 (by decide +kernel)

private theorem c542 : C ![2, 0, 2, 1, 0, 0, 0] ![3, 1, 3, 2, 1, 1, 1] n542 := by
  exact checkExponentBoxTree_join c543 c570 (by decide +kernel)

private theorem c488 : C ![2, 0, 2, 0, 0, 0, 0] ![3, 1, 3, 2, 1, 1, 1] n488 := by
  exact checkExponentBoxTree_join c489 c542 (by decide +kernel)

private theorem c240 : C ![2, 0, 0, 0, 0, 0, 0] ![3, 1, 3, 2, 1, 1, 1] n240 := by
  exact checkExponentBoxTree_join c241 c488 (by decide +kernel)

private theorem c2 : C ![0, 0, 0, 0, 0, 0, 0] ![3, 1, 3, 2, 1, 1, 1] n2 := by
  exact checkExponentBoxTree_join c3 c240 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n2

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c2

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main00
