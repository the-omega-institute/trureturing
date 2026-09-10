/- GID: D5/S3/Quantum/Tomography/RealXCheckedOriginSector
   generality: I
   mirror-B: D5/B/S3/Quantum/Tomography/RealXCheckedOriginSector
   mirror-E: none(waiver:partial-domain-kernel-integration-instance)
   anchors: []
   digest: A concrete complete 237-node rational forest excludes all six-residual near-zeros on the all-positive origin sector of radius one-fifth. -/

import D5.S0.Certificates.CheckedRationalBoxCover
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/- This is a numeric integration instance for the cover proof, not a larger
   Hadamard exclusion neighborhood. The phase domain is [-1/5,1/5]^5 in ONE
   signed Cayley chart. The full 32-chart phase cube is not certified here.
   All local annotations are proposed by annotate and then independently
   verified by RationalIntervalExpression.check inside checkForest.
   The split forest is complete on the stated sector. It uses no contractions,
   no trusted result file, no assumed local inequalities, and no sampled root
   catalogue. Real semantics is connected to the actual H0 matrix below.
-/

open scoped BigOperators Matrix
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Tomography.RealXCheckedOriginSector

open Matrix
open D5.S0.Certificates.RationalIntervalExpression
open D5.S0.Certificates.CheckedRationalBoxCover

private def annotate {n : ℕ} (box : Fin n → ℚ × ℚ) : Expr n → Expr n
  | .input i _ _ => .input i (box i).1 (box i).2
  | .const q _ _ => .const q q q
  | .add _ _ a b =>
    let x := annotate box a
    let y := annotate box b
    .add ((bounds x).1 + (bounds y).1) ((bounds x).2 + (bounds y).2) x y
  | .neg _ _ a =>
    let x := annotate box a
    .neg (-(bounds x).2) (-(bounds x).1) x
  | .mul _ _ a b =>
    let x := annotate box a
    let y := annotate box b
    let p := (bounds x).1 * (bounds y).1
    let q := (bounds x).1 * (bounds y).2
    let r := (bounds x).2 * (bounds y).1
    let s := (bounds x).2 * (bounds y).2
    .mul (min (min p q) (min r s)) (max (max p q) (max r s)) x y
  | .square _ _ a =>
    let x := annotate box a
    let l := (bounds x).1
    let u := (bounds x).2
    .square (if l ≤ 0 ∧ 0 ≤ u then 0 else min (l ^ 2) (u ^ 2))
      (max (l ^ 2) (u ^ 2)) x
  | .inv _ _ a =>
    let x := annotate box a
    .inv (1 / (bounds x).2) (1 / (bounds x).1) x

private def residualData : List (Expr 6) :=
  let e0 : Expr 6 := .const (0 : ℚ) 0 0
  let e1 : Expr 6 := .const (-3 / 5 : ℚ) 0 0
  let e2 : Expr 6 := .const (1 : ℚ) 0 0
  let e3 : Expr 6 := .mul 0 0 e1 e2
  let e4 : Expr 6 := .const (-4 / 5 : ℚ) 0 0
  let e5 : Expr 6 := .mul 0 0 e4 e0
  let e6 : Expr 6 := .neg 0 0 e5
  let e7 : Expr 6 := .add 0 0 e3 e6
  let e8 : Expr 6 := .add 0 0 e0 e7
  let e9 : Expr 6 := .input 1 0 0
  let e10 : Expr 6 := .square 0 0 e9
  let e11 : Expr 6 := .neg 0 0 e10
  let e12 : Expr 6 := .add 0 0 e2 e11
  let e13 : Expr 6 := .add 0 0 e2 e10
  let e14 : Expr 6 := .inv 0 0 e13
  let e15 : Expr 6 := .mul 0 0 e12 e14
  let e16 : Expr 6 := .mul 0 0 e2 e15
  let e17 : Expr 6 := .const (2 : ℚ) 0 0
  let e18 : Expr 6 := .mul 0 0 e17 e9
  let e19 : Expr 6 := .mul 0 0 e18 e14
  let e20 : Expr 6 := .mul 0 0 e0 e19
  let e21 : Expr 6 := .neg 0 0 e20
  let e22 : Expr 6 := .add 0 0 e16 e21
  let e23 : Expr 6 := .add 0 0 e8 e22
  let e24 : Expr 6 := .input 2 0 0
  let e25 : Expr 6 := .square 0 0 e24
  let e26 : Expr 6 := .neg 0 0 e25
  let e27 : Expr 6 := .add 0 0 e2 e26
  let e28 : Expr 6 := .add 0 0 e2 e25
  let e29 : Expr 6 := .inv 0 0 e28
  let e30 : Expr 6 := .mul 0 0 e27 e29
  let e31 : Expr 6 := .mul 0 0 e2 e30
  let e32 : Expr 6 := .mul 0 0 e17 e24
  let e33 : Expr 6 := .mul 0 0 e32 e29
  let e34 : Expr 6 := .mul 0 0 e0 e33
  let e35 : Expr 6 := .neg 0 0 e34
  let e36 : Expr 6 := .add 0 0 e31 e35
  let e37 : Expr 6 := .add 0 0 e23 e36
  let e38 : Expr 6 := .const (-2 / 5 : ℚ) 0 0
  let e39 : Expr 6 := .input 3 0 0
  let e40 : Expr 6 := .square 0 0 e39
  let e41 : Expr 6 := .neg 0 0 e40
  let e42 : Expr 6 := .add 0 0 e2 e41
  let e43 : Expr 6 := .add 0 0 e2 e40
  let e44 : Expr 6 := .inv 0 0 e43
  let e45 : Expr 6 := .mul 0 0 e42 e44
  let e46 : Expr 6 := .mul 0 0 e38 e45
  let e47 : Expr 6 := .input 0 0 0
  let e48 : Expr 6 := .const (1 / 5 : ℚ) 0 0
  let e49 : Expr 6 := .mul 0 0 e47 e48
  let e50 : Expr 6 := .mul 0 0 e17 e39
  let e51 : Expr 6 := .mul 0 0 e50 e44
  let e52 : Expr 6 := .mul 0 0 e49 e51
  let e53 : Expr 6 := .neg 0 0 e52
  let e54 : Expr 6 := .add 0 0 e46 e53
  let e55 : Expr 6 := .add 0 0 e37 e54
  let e56 : Expr 6 := .input 4 0 0
  let e57 : Expr 6 := .square 0 0 e56
  let e58 : Expr 6 := .neg 0 0 e57
  let e59 : Expr 6 := .add 0 0 e2 e58
  let e60 : Expr 6 := .add 0 0 e2 e57
  let e61 : Expr 6 := .inv 0 0 e60
  let e62 : Expr 6 := .mul 0 0 e59 e61
  let e63 : Expr 6 := .mul 0 0 e2 e62
  let e64 : Expr 6 := .mul 0 0 e17 e56
  let e65 : Expr 6 := .mul 0 0 e64 e61
  let e66 : Expr 6 := .mul 0 0 e0 e65
  let e67 : Expr 6 := .neg 0 0 e66
  let e68 : Expr 6 := .add 0 0 e63 e67
  let e69 : Expr 6 := .add 0 0 e55 e68
  let e70 : Expr 6 := .input 5 0 0
  let e71 : Expr 6 := .square 0 0 e70
  let e72 : Expr 6 := .neg 0 0 e71
  let e73 : Expr 6 := .add 0 0 e2 e72
  let e74 : Expr 6 := .add 0 0 e2 e71
  let e75 : Expr 6 := .inv 0 0 e74
  let e76 : Expr 6 := .mul 0 0 e73 e75
  let e77 : Expr 6 := .mul 0 0 e2 e76
  let e78 : Expr 6 := .mul 0 0 e17 e70
  let e79 : Expr 6 := .mul 0 0 e78 e75
  let e80 : Expr 6 := .mul 0 0 e0 e79
  let e81 : Expr 6 := .neg 0 0 e80
  let e82 : Expr 6 := .add 0 0 e77 e81
  let e83 : Expr 6 := .add 0 0 e69 e82
  let e84 : Expr 6 := .square 0 0 e83
  let e85 : Expr 6 := .mul 0 0 e1 e0
  let e86 : Expr 6 := .mul 0 0 e4 e2
  let e87 : Expr 6 := .add 0 0 e85 e86
  let e88 : Expr 6 := .add 0 0 e0 e87
  let e89 : Expr 6 := .mul 0 0 e2 e19
  let e90 : Expr 6 := .mul 0 0 e0 e15
  let e91 : Expr 6 := .add 0 0 e89 e90
  let e92 : Expr 6 := .add 0 0 e88 e91
  let e93 : Expr 6 := .mul 0 0 e2 e33
  let e94 : Expr 6 := .mul 0 0 e0 e30
  let e95 : Expr 6 := .add 0 0 e93 e94
  let e96 : Expr 6 := .add 0 0 e92 e95
  let e97 : Expr 6 := .mul 0 0 e38 e51
  let e98 : Expr 6 := .mul 0 0 e49 e45
  let e99 : Expr 6 := .add 0 0 e97 e98
  let e100 : Expr 6 := .add 0 0 e96 e99
  let e101 : Expr 6 := .mul 0 0 e2 e65
  let e102 : Expr 6 := .mul 0 0 e0 e62
  let e103 : Expr 6 := .add 0 0 e101 e102
  let e104 : Expr 6 := .add 0 0 e100 e103
  let e105 : Expr 6 := .mul 0 0 e2 e79
  let e106 : Expr 6 := .mul 0 0 e0 e76
  let e107 : Expr 6 := .add 0 0 e105 e106
  let e108 : Expr 6 := .add 0 0 e104 e107
  let e109 : Expr 6 := .square 0 0 e108
  let e110 : Expr 6 := .add 0 0 e84 e109
  let e111 : Expr 6 := .const (6 : ℚ) 0 0
  let e112 : Expr 6 := .neg 0 0 e111
  let e113 : Expr 6 := .add 0 0 e110 e112
  let e114 : Expr 6 := .mul 0 0 e2 e2
  let e115 : Expr 6 := .mul 0 0 e0 e0
  let e116 : Expr 6 := .neg 0 0 e115
  let e117 : Expr 6 := .add 0 0 e114 e116
  let e118 : Expr 6 := .add 0 0 e0 e117
  let e119 : Expr 6 := .mul 0 0 e1 e15
  let e120 : Expr 6 := .mul 0 0 e4 e19
  let e121 : Expr 6 := .neg 0 0 e120
  let e122 : Expr 6 := .add 0 0 e119 e121
  let e123 : Expr 6 := .add 0 0 e118 e122
  let e124 : Expr 6 := .add 0 0 e123 e36
  let e125 : Expr 6 := .mul 0 0 e2 e45
  let e126 : Expr 6 := .mul 0 0 e0 e51
  let e127 : Expr 6 := .neg 0 0 e126
  let e128 : Expr 6 := .add 0 0 e125 e127
  let e129 : Expr 6 := .add 0 0 e124 e128
  let e130 : Expr 6 := .mul 0 0 e38 e62
  let e131 : Expr 6 := .mul 0 0 e49 e65
  let e132 : Expr 6 := .neg 0 0 e131
  let e133 : Expr 6 := .add 0 0 e130 e132
  let e134 : Expr 6 := .add 0 0 e129 e133
  let e135 : Expr 6 := .add 0 0 e134 e82
  let e136 : Expr 6 := .square 0 0 e135
  let e137 : Expr 6 := .mul 0 0 e2 e0
  let e138 : Expr 6 := .mul 0 0 e0 e2
  let e139 : Expr 6 := .add 0 0 e137 e138
  let e140 : Expr 6 := .add 0 0 e0 e139
  let e141 : Expr 6 := .mul 0 0 e1 e19
  let e142 : Expr 6 := .mul 0 0 e4 e15
  let e143 : Expr 6 := .add 0 0 e141 e142
  let e144 : Expr 6 := .add 0 0 e140 e143
  let e145 : Expr 6 := .add 0 0 e144 e95
  let e146 : Expr 6 := .mul 0 0 e2 e51
  let e147 : Expr 6 := .mul 0 0 e0 e45
  let e148 : Expr 6 := .add 0 0 e146 e147
  let e149 : Expr 6 := .add 0 0 e145 e148
  let e150 : Expr 6 := .mul 0 0 e38 e65
  let e151 : Expr 6 := .mul 0 0 e49 e62
  let e152 : Expr 6 := .add 0 0 e150 e151
  let e153 : Expr 6 := .add 0 0 e149 e152
  let e154 : Expr 6 := .add 0 0 e153 e107
  let e155 : Expr 6 := .square 0 0 e154
  let e156 : Expr 6 := .add 0 0 e136 e155
  let e157 : Expr 6 := .add 0 0 e156 e112
  let e158 : Expr 6 := .add 0 0 e118 e22
  let e159 : Expr 6 := .mul 0 0 e1 e30
  let e160 : Expr 6 := .mul 0 0 e4 e33
  let e161 : Expr 6 := .neg 0 0 e160
  let e162 : Expr 6 := .add 0 0 e159 e161
  let e163 : Expr 6 := .add 0 0 e158 e162
  let e164 : Expr 6 := .add 0 0 e163 e128
  let e165 : Expr 6 := .add 0 0 e164 e68
  let e166 : Expr 6 := .mul 0 0 e38 e76
  let e167 : Expr 6 := .mul 0 0 e49 e79
  let e168 : Expr 6 := .neg 0 0 e167
  let e169 : Expr 6 := .add 0 0 e166 e168
  let e170 : Expr 6 := .add 0 0 e165 e169
  let e171 : Expr 6 := .square 0 0 e170
  let e172 : Expr 6 := .add 0 0 e140 e91
  let e173 : Expr 6 := .mul 0 0 e1 e33
  let e174 : Expr 6 := .mul 0 0 e4 e30
  let e175 : Expr 6 := .add 0 0 e173 e174
  let e176 : Expr 6 := .add 0 0 e172 e175
  let e177 : Expr 6 := .add 0 0 e176 e148
  let e178 : Expr 6 := .add 0 0 e177 e103
  let e179 : Expr 6 := .mul 0 0 e38 e79
  let e180 : Expr 6 := .mul 0 0 e49 e76
  let e181 : Expr 6 := .add 0 0 e179 e180
  let e182 : Expr 6 := .add 0 0 e178 e181
  let e183 : Expr 6 := .square 0 0 e182
  let e184 : Expr 6 := .add 0 0 e171 e183
  let e185 : Expr 6 := .add 0 0 e184 e112
  let e186 : Expr 6 := .mul 0 0 e38 e2
  let e187 : Expr 6 := .neg 0 0 e49
  let e188 : Expr 6 := .mul 0 0 e187 e0
  let e189 : Expr 6 := .neg 0 0 e188
  let e190 : Expr 6 := .add 0 0 e186 e189
  let e191 : Expr 6 := .add 0 0 e0 e190
  let e192 : Expr 6 := .add 0 0 e191 e22
  let e193 : Expr 6 := .add 0 0 e192 e36
  let e194 : Expr 6 := .const (3 / 5 : ℚ) 0 0
  let e195 : Expr 6 := .mul 0 0 e194 e45
  let e196 : Expr 6 := .mul 0 0 e4 e51
  let e197 : Expr 6 := .neg 0 0 e196
  let e198 : Expr 6 := .add 0 0 e195 e197
  let e199 : Expr 6 := .add 0 0 e193 e198
  let e200 : Expr 6 := .const (-1 : ℚ) 0 0
  let e201 : Expr 6 := .mul 0 0 e200 e62
  let e202 : Expr 6 := .add 0 0 e201 e67
  let e203 : Expr 6 := .add 0 0 e199 e202
  let e204 : Expr 6 := .mul 0 0 e200 e76
  let e205 : Expr 6 := .add 0 0 e204 e81
  let e206 : Expr 6 := .add 0 0 e203 e205
  let e207 : Expr 6 := .square 0 0 e206
  let e208 : Expr 6 := .mul 0 0 e38 e0
  let e209 : Expr 6 := .mul 0 0 e187 e2
  let e210 : Expr 6 := .add 0 0 e208 e209
  let e211 : Expr 6 := .add 0 0 e0 e210
  let e212 : Expr 6 := .add 0 0 e211 e91
  let e213 : Expr 6 := .add 0 0 e212 e95
  let e214 : Expr 6 := .mul 0 0 e194 e51
  let e215 : Expr 6 := .mul 0 0 e4 e45
  let e216 : Expr 6 := .add 0 0 e214 e215
  let e217 : Expr 6 := .add 0 0 e213 e216
  let e218 : Expr 6 := .mul 0 0 e200 e65
  let e219 : Expr 6 := .add 0 0 e218 e102
  let e220 : Expr 6 := .add 0 0 e217 e219
  let e221 : Expr 6 := .mul 0 0 e200 e79
  let e222 : Expr 6 := .add 0 0 e221 e106
  let e223 : Expr 6 := .add 0 0 e220 e222
  let e224 : Expr 6 := .square 0 0 e223
  let e225 : Expr 6 := .add 0 0 e207 e224
  let e226 : Expr 6 := .add 0 0 e225 e112
  let e227 : Expr 6 := .mul 0 0 e38 e15
  let e228 : Expr 6 := .mul 0 0 e187 e19
  let e229 : Expr 6 := .neg 0 0 e228
  let e230 : Expr 6 := .add 0 0 e227 e229
  let e231 : Expr 6 := .add 0 0 e118 e230
  let e232 : Expr 6 := .add 0 0 e231 e36
  let e233 : Expr 6 := .mul 0 0 e200 e45
  let e234 : Expr 6 := .add 0 0 e233 e127
  let e235 : Expr 6 := .add 0 0 e232 e234
  let e236 : Expr 6 := .mul 0 0 e194 e62
  let e237 : Expr 6 := .mul 0 0 e4 e65
  let e238 : Expr 6 := .neg 0 0 e237
  let e239 : Expr 6 := .add 0 0 e236 e238
  let e240 : Expr 6 := .add 0 0 e235 e239
  let e241 : Expr 6 := .add 0 0 e240 e205
  let e242 : Expr 6 := .square 0 0 e241
  let e243 : Expr 6 := .mul 0 0 e38 e19
  let e244 : Expr 6 := .mul 0 0 e187 e15
  let e245 : Expr 6 := .add 0 0 e243 e244
  let e246 : Expr 6 := .add 0 0 e140 e245
  let e247 : Expr 6 := .add 0 0 e246 e95
  let e248 : Expr 6 := .mul 0 0 e200 e51
  let e249 : Expr 6 := .add 0 0 e248 e147
  let e250 : Expr 6 := .add 0 0 e247 e249
  let e251 : Expr 6 := .mul 0 0 e194 e65
  let e252 : Expr 6 := .mul 0 0 e4 e62
  let e253 : Expr 6 := .add 0 0 e251 e252
  let e254 : Expr 6 := .add 0 0 e250 e253
  let e255 : Expr 6 := .add 0 0 e254 e222
  let e256 : Expr 6 := .square 0 0 e255
  let e257 : Expr 6 := .add 0 0 e242 e256
  let e258 : Expr 6 := .add 0 0 e257 e112
  let e259 : Expr 6 := .mul 0 0 e38 e30
  let e260 : Expr 6 := .mul 0 0 e187 e33
  let e261 : Expr 6 := .neg 0 0 e260
  let e262 : Expr 6 := .add 0 0 e259 e261
  let e263 : Expr 6 := .add 0 0 e158 e262
  let e264 : Expr 6 := .add 0 0 e263 e234
  let e265 : Expr 6 := .add 0 0 e264 e202
  let e266 : Expr 6 := .mul 0 0 e194 e76
  let e267 : Expr 6 := .mul 0 0 e4 e79
  let e268 : Expr 6 := .neg 0 0 e267
  let e269 : Expr 6 := .add 0 0 e266 e268
  let e270 : Expr 6 := .add 0 0 e265 e269
  let e271 : Expr 6 := .square 0 0 e270
  let e272 : Expr 6 := .mul 0 0 e38 e33
  let e273 : Expr 6 := .mul 0 0 e187 e30
  let e274 : Expr 6 := .add 0 0 e272 e273
  let e275 : Expr 6 := .add 0 0 e172 e274
  let e276 : Expr 6 := .add 0 0 e275 e249
  let e277 : Expr 6 := .add 0 0 e276 e219
  let e278 : Expr 6 := .mul 0 0 e194 e79
  let e279 : Expr 6 := .mul 0 0 e4 e76
  let e280 : Expr 6 := .add 0 0 e278 e279
  let e281 : Expr 6 := .add 0 0 e277 e280
  let e282 : Expr 6 := .square 0 0 e281
  let e283 : Expr 6 := .add 0 0 e271 e282
  let e284 : Expr 6 := .add 0 0 e283 e112
  [e113, e157, e185, e226, e258, e284]

private def residual (a : Fin 6) : Expr 6 := residualData.getD a.val (.const 0 0 0)

private def rootBox : Fin 6 → ℚ × ℚ :=
  Fin.cases ((5038595261767 / 1099511627776 : ℚ), (629824407721 / 137438953472 : ℚ)) (fun _ ↦ (-1 / 5, 1 / 5))

private def pathBox : ℕ → ℕ → Fin 6 → ℚ × ℚ
  | 0, _ => rootBox
  | d + 1, w =>
    let parent := pathBox d (w / 2)
    fun j ↦ if j.val = d % 5 + 1 then
      let p := parent j
      let cut := (p.1 + p.2) / 2
      if w % 2 = 0 then (p.1, cut) else (cut, p.2)
    else parent j

private def paths : List (ℕ × ℕ) :=
  [(3, 0), (6, 8), (6, 9), (5, 4), (6, 10), (6, 11), (5, 5), (4, 2), (7, 24), (7, 25), (6, 12), (6, 13), (5, 6), (8, 56), (12, 912), (12, 913), (11, 456), (11, 457), (10, 228), (12, 916), (13, 1834), (14, 3670), (15, 7342), (15, 7343), (14, 3671), (13, 1835), (12, 917), (11, 458), (11, 459), (10, 229), (9, 114), (12, 920), (12, 921), (11, 460), (13, 1844), (14, 3690), (14, 3691), (13, 1845), (12, 922), (12, 923), (11, 461), (10, 230), (13, 1848), (17, 29584), (17, 29585), (16, 14792), (17, 29586), (18, 59174), (18, 59175), (17, 29587), (16, 14793), (15, 7396), (15, 7397), (14, 3698), (14, 3699), (13, 1849), (12, 924), (13, 1850), (15, 7404), (16, 14810), (17, 29622), (18, 59246), (18, 59247), (17, 29623), (16, 14811), (15, 7405), (14, 3702), (15, 7406), (15, 7407), (14, 3703), (13, 1851), (12, 925), (11, 462), (13, 1852), (14, 3706), (16, 14828), (17, 29658), (18, 59318), (18, 59319), (17, 29659), (16, 14829), (15, 7414), (15, 7415), (14, 3707), (13, 1853), (12, 926), (13, 1854), (15, 7420), (15, 7421), (14, 3710), (15, 7422), (16, 14846), (17, 29694), (18, 59390), (19, 118782), (19, 118783), (18, 59391), (17, 29695), (16, 14847), (15, 7423), (14, 3711), (13, 1855), (12, 927), (11, 463), (10, 231), (9, 115), (8, 57), (7, 28), (8, 58), (10, 236), (13, 1896), (13, 1897), (12, 948), (12, 949), (11, 474), (11, 475), (10, 237), (9, 118), (10, 238), (13, 1912), (14, 3826), (14, 3827), (13, 1913), (12, 956), (12, 957), (11, 478), (13, 1916), (14, 3834), (14, 3835), (13, 1917), (12, 958), (12, 959), (11, 479), (10, 239), (9, 119), (8, 59), (7, 29), (6, 14), (8, 60), (10, 244), (10, 245), (9, 122), (13, 1968), (13, 1969), (12, 984), (12, 985), (11, 492), (11, 493), (10, 246), (13, 1976), (14, 3954), (15, 7910), (15, 7911), (14, 3955), (13, 1977), (12, 988), (13, 1978), (14, 3958), (15, 7918), (15, 7919), (14, 3959), (13, 1979), (12, 989), (11, 494), (11, 495), (10, 247), (9, 123), (8, 61), (7, 30), (8, 62), (9, 126), (10, 254), (13, 2040), (13, 2041), (12, 1020), (12, 1021), (11, 510), (11, 511), (10, 255), (9, 127), (8, 63), (7, 31), (6, 15), (5, 7), (4, 3), (3, 1), (2, 0), (3, 2), (5, 12), (6, 26), (6, 27), (5, 13), (4, 6), (5, 14), (8, 120), (9, 242), (9, 243), (8, 121), (7, 60), (7, 61), (6, 30), (6, 31), (5, 15), (4, 7), (3, 3), (2, 1), (1, 0), (3, 4), (4, 10), (6, 44), (6, 45), (5, 22), (8, 184), (9, 370), (10, 742), (10, 743), (9, 371), (8, 185), (7, 92), (7, 93), (6, 46), (6, 47), (5, 23), (4, 11), (3, 5), (2, 2), (3, 6), (4, 14), (5, 30), (6, 62), (6, 63), (5, 31), (4, 15), (3, 7), (2, 3), (1, 1), (0, 0)]

private def boxes (i : Fin 237) : Fin 6 → ℚ × ℚ :=
  let p := paths.getD i.val (0, 0)
  pathBox p.1 p.2

/- Codes below are untrusted compact syntax, not acceptance bits. Every
   decoded node is checked by checkForest, including both child boxes. -/
private def stepCodes : List ℕ :=
  [0, 1, 1, 2857, 1, 1, 7141, 8561, 2, 2, 12854, 2,
   15709, 0, 0, 0, 21422, 0, 24277, 5, 0, 0, 0, 5,
   32849, 34264, 35679, 37094, 5, 39985, 41357, 4, 4, 45698, 0, 0,
   4, 51412, 52827, 0, 55694, 57085, 3, 3, 3, 62834, 3, 0,
   0, 68547, 69962, 71377, 3, 74261, 3, 77116, 78471, 0, 4, 3,
   3, 0, 0, 88539, 89954, 91369, 92789, 4, 3, 97109, 98524, 99891,
   101306, 0, 5, 3, 3, 0, 0, 111387, 112802, 114217, 3, 117101,
   118480, 119895, 0, 0, 5, 125669, 4, 3, 3, 0, 0, 0,
   135664, 137079, 138494, 139909, 141329, 142744, 144147, 145562, 146905, 148145, 149500, 150819,
   0, 0, 0, 0, 158511, 0, 161366, 0, 164221, 165617, 4, 0,
   4, 4, 172792, 174207, 4, 177074, 0, 0, 4, 182788, 184203, 4,
   187070, 188461, 189845, 191260, 192627, 194042, 0, 0, 5, 199925, 0, 0,
   204207, 0, 207062, 0, 209917, 0, 5, 5, 5, 217061, 218476, 219891,
   0, 0, 0, 5, 227057, 228472, 229887, 231302, 5, 234193, 235529, 236908,
   238311, 0, 0, 0, 0, 0, 247047, 0, 249902, 0, 252757, 254153,
   255568, 256983, 258398, 259633, 260309, 261700, 263079, 0, 2, 1, 1, 271321,
   272741, 2, 0, 2, 4, 279892, 281307, 2, 284174, 2, 287029, 288413,
   289828, 291219, 292634, 0, 1, 2, 1, 299881, 0, 1, 1, 5,
   307025, 308440, 309855, 1, 312734, 1, 315589, 316961, 318364, 319779, 0, 1,
   2, 2, 1, 328441, 329861, 331276, 332691, 334106, 335413]

private def index237 (n : ℕ) : Fin 237 :=
  ⟨n % 237, Nat.mod_lt _ (by decide)⟩

private def steps (i : Fin 237) : Step 6 6 0 237 :=
  let code := stepCodes.getD i.val 0
  if h : code < 6 then
    let a : Fin 6 := ⟨code, h⟩
    .excluded a (annotate (boxes i) (residual a))
  else
    let data := code - 6
    let k : Fin 6 := ⟨data % 6, Nat.mod_lt _ (by decide)⟩
    let left := index237 (data / 6)
    let right := index237 (data / (6 * 237))
    let cut := ((boxes i k).1 + (boxes i k).2) / 2
    .split k cut left right

private def targets : Fin 0 → Fin 6 → ℚ × ℚ := fun i ↦ Fin.elim0 i

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem sector_checked :
    checkForest boxes targets residual (1 / 64) steps = true := by
  decide +kernel

private def seedMatrix (s : ℝ) : Matrix (Fin 6) (Fin 6) ℂ := fun i j ↦
  if i.val < 3 then
    if j.val < 3 then
      if i = j then ⟨-3 / 5, 4 / 5⟩ else 1
    else
      if i.val + 3 = j.val then ⟨-2 / 5, s / 5⟩ else 1
  else
    if j.val < 3 then
      if i.val = j.val + 3 then ⟨-2 / 5, -s / 5⟩ else 1
    else
      if i = j then ⟨3 / 5, 4 / 5⟩ else -1

private abbrev phase (t : ℝ) : ℂ :=
  ⟨(1 - t ^ 2) / (1 + t ^ 2), 2 * t / (1 + t ^ 2)⟩

set_option maxRecDepth 8192 in
private theorem residual_value (s : ℝ) (t : Fin 5 → ℝ) (a : Fin 6) :
    value (Fin.cases s t) (residual a) =
      Complex.normSq (((seedMatrix s)ᴴ *ᵥ
        (Fin.cases (1 : ℂ) (fun i ↦ phase (t i)))) a) - 6 := by
  fin_cases a <;>
    norm_num [residual, residualData, value, seedMatrix, phase,
      Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Complex.normSq_apply, Complex.star_def,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      div_eq_mul_inv] <;>
    dsimp [Fin.cases, Fin.induction, Fin.induction.go] <;> ring

/-- Every point of the stated five-dimensional signed-Cayley sector violates
at least one of the six residual bands of the actual Q(i,sqrt(21)) seed.
The 237-node forest checks all 119 exclusion leaves and 118 closed splits.
No mathematical enclosure or finite-cover premise is supplied by the caller.

This is a concrete traversal integration theorem on a proper subregion of one
chart. It does not imply whole-space root coverage or four-MUB nonexistence.
Kernel acceptance requires actually compiling this file and its dependencies. -/
theorem no_common_unbiased_sublevel_in_checked_origin_sector
    (t : Fin 5 → ℝ)
    (ht : ∀ i, -(1 / 5 : ℝ) ≤ t i ∧ t i ≤ (1 / 5 : ℝ)) :
    let H : Matrix (Fin 6) (Fin 6) ℂ := fun i j ↦
      if i.val < 3 then
        if j.val < 3 then
          if i = j then ⟨-3 / 5, 4 / 5⟩ else 1
        else
          if i.val + 3 = j.val then ⟨-2 / 5, Real.sqrt 21 / 5⟩ else 1
      else
        if j.val < 3 then
          if i.val = j.val + 3 then ⟨-2 / 5, -Real.sqrt 21 / 5⟩ else 1
        else
          if i = j then ⟨3 / 5, 4 / 5⟩ else -1
    let u : Fin 6 → ℂ := Fin.cases 1 (fun i ↦
      ⟨(1 - t i ^ 2) / (1 + t i ^ 2), 2 * t i / (1 + t i ^ 2)⟩)
    ¬ ∀ a, |Complex.normSq ((Hᴴ *ᵥ u) a) - 6| ≤ (1 / 64 : ℝ) := by
  change ¬ ∀ a, |Complex.normSq (((seedMatrix (Real.sqrt 21))ᴴ *ᵥ
    Fin.cases (1 : ℂ) (fun i ↦ phase (t i))) a) - 6| ≤ (1 / 64 : ℝ)
  intro hsmall
  have hs :
      (5038595261767 / 1099511627776 : ℝ) ≤ Real.sqrt 21 ∧
        Real.sqrt 21 ≤ (629824407721 / 137438953472 : ℝ) := by
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
    have hn := Real.sqrt_nonneg (21 : ℝ)
    constructor <;> nlinarith
  have hx : ∀ j : Fin 6,
      ((boxes 236 j).1 : ℝ) ≤ Fin.cases (Real.sqrt 21) t j ∧
        Fin.cases (Real.sqrt 21) t j ≤ ((boxes 236 j).2 : ℝ) := by
    have hroot (j : Fin 6) : boxes 236 j = rootBox j := by rfl
    intro j
    rw [hroot]
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · change ((5038595261767 / 1099511627776 : ℚ) : ℝ) ≤ Real.sqrt 21 ∧
        Real.sqrt 21 ≤ ((629824407721 / 137438953472 : ℚ) : ℝ)
      norm_num
      exact hs
    · change (((-1 / 5 : ℚ) : ℝ) ≤ t k ∧ t k ≤ ((1 / 5 : ℚ) : ℝ))
      norm_num
      exact ht k
  have hr : ∀ a, |value (Fin.cases (Real.sqrt 21) t) (residual a)| ≤
      ((1 / 64 : ℚ) : ℝ) := by
    intro a
    rw [residual_value]
    norm_num
    exact hsmall a
  obtain ⟨k, _⟩ := checked_forest_covers_sublevel boxes targets residual
    (1 / 64) steps sector_checked 236 (Fin.cases (Real.sqrt 21) t) hx hr
  exact Fin.elim0 k

#print axioms no_common_unbiased_sublevel_in_checked_origin_sector

end D5.S3.Quantum.Tomography.RealXCheckedOriginSector
