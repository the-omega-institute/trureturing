/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main13
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main13.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main13

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![4, 2, 2, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![8, 7, 3, 0, 1, 1, 1]

private def n3138 : MainTree := .leaf (mainRankLeaf 2 ![4, 2, 2, 0, 0, 0, 0])
private def n3139 : MainTree := .leaf (mainRankLeaf 2 ![5, 2, 2, 0, 0, 0, 0])
private def n3137 : MainTree := .split 0 4 n3138 n3139
private def n3140 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 0, 0, 0])
private def n3136 : MainTree := .split 2 2 n3137 n3140
private def n3143 : MainTree := .leaf (mainGapLeaf ![4, 3, 2, 0, 0, 0, 0])
private def n3144 : MainTree := .leaf (mainGapLeaf ![5, 3, 2, 0, 0, 0, 0])
private def n3142 : MainTree := .split 0 4 n3143 n3144
private def n3145 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 0, 0, 0])
private def n3141 : MainTree := .split 2 2 n3142 n3145
private def n3135 : MainTree := .split 1 2 n3136 n3141
private def n3148 : MainTree := .leaf (mainGapLeaf ![8, 2, 2, 0, 0, 0, 0])
private def n3149 : MainTree := .leaf (mainGapLeaf ![8, 2, 3, 0, 0, 0, 0])
private def n3147 : MainTree := .split 2 2 n3148 n3149
private def n3150 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 0, 0, 0])
private def n3146 : MainTree := .split 1 2 n3147 n3150
private def n3134 : MainTree := .split 0 5 n3135 n3146
private def n3154 : MainTree := .leaf (mainGapLeaf ![5, 2, 2, 0, 0, 0, 1])
private def n3155 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 0, 0, 1])
private def n3153 : MainTree := .split 2 2 n3154 n3155
private def n3156 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 0, 0, 1])
private def n3152 : MainTree := .split 1 2 n3153 n3156
private def n3158 : MainTree := .leaf (mainGapLeaf ![8, 2, 3, 0, 0, 0, 1])
private def n3159 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 0, 0, 1])
private def n3157 : MainTree := .split 1 2 n3158 n3159
private def n3151 : MainTree := .split 0 5 n3152 n3157
private def n3133 : MainTree := .split 6 0 n3134 n3151
private def n3165 : MainTree := .leaf (mainGapLeaf ![4, 2, 2, 0, 0, 1, 0])
private def n3166 : MainTree := .leaf (mainGapLeaf ![5, 2, 2, 0, 0, 1, 0])
private def n3164 : MainTree := .split 0 4 n3165 n3166
private def n3167 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 0, 1, 0])
private def n3163 : MainTree := .split 2 2 n3164 n3167
private def n3168 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 0, 1, 0])
private def n3162 : MainTree := .split 1 2 n3163 n3168
private def n3170 : MainTree := .leaf (mainGapLeaf ![8, 2, 3, 0, 0, 1, 0])
private def n3171 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 0, 1, 0])
private def n3169 : MainTree := .split 1 2 n3170 n3171
private def n3161 : MainTree := .split 0 5 n3162 n3169
private def n3174 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 0, 1, 1])
private def n3175 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 0, 1, 1])
private def n3173 : MainTree := .split 1 2 n3174 n3175
private def n3176 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 0, 1, 1])
private def n3172 : MainTree := .split 0 5 n3173 n3176
private def n3160 : MainTree := .split 6 0 n3161 n3172
private def n3132 : MainTree := .split 5 0 n3133 n3160
private def n3183 : MainTree := .leaf (mainGapLeaf ![4, 2, 2, 0, 1, 0, 0])
private def n3184 : MainTree := .leaf (mainGapLeaf ![5, 2, 2, 0, 1, 0, 0])
private def n3182 : MainTree := .split 0 4 n3183 n3184
private def n3185 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 1, 0, 0])
private def n3181 : MainTree := .split 2 2 n3182 n3185
private def n3188 : MainTree := .leaf (mainGapLeaf ![4, 3, 2, 0, 1, 0, 0])
private def n3189 : MainTree := .leaf (mainGapLeaf ![5, 3, 2, 0, 1, 0, 0])
private def n3187 : MainTree := .split 0 4 n3188 n3189
private def n3190 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 1, 0, 0])
private def n3186 : MainTree := .split 2 2 n3187 n3190
private def n3180 : MainTree := .split 1 2 n3181 n3186
private def n3192 : MainTree := .leaf (mainGapLeaf ![8, 2, 3, 0, 1, 0, 0])
private def n3193 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 1, 0, 0])
private def n3191 : MainTree := .split 1 2 n3192 n3193
private def n3179 : MainTree := .split 0 5 n3180 n3191
private def n3196 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 1, 0, 1])
private def n3197 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 1, 0, 1])
private def n3195 : MainTree := .split 1 2 n3196 n3197
private def n3198 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 1, 0, 1])
private def n3194 : MainTree := .split 0 5 n3195 n3198
private def n3178 : MainTree := .split 6 0 n3179 n3194
private def n3202 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 1, 1, 0])
private def n3203 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 1, 1, 0])
private def n3201 : MainTree := .split 1 2 n3202 n3203
private def n3205 : MainTree := .leaf (mainGapLeaf ![8, 2, 3, 0, 1, 1, 0])
private def n3206 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 1, 1, 0])
private def n3204 : MainTree := .split 1 2 n3205 n3206
private def n3200 : MainTree := .split 0 5 n3201 n3204
private def n3209 : MainTree := .leaf (mainGapLeaf ![5, 2, 3, 0, 1, 1, 1])
private def n3210 : MainTree := .leaf (mainGapLeaf ![5, 3, 3, 0, 1, 1, 1])
private def n3208 : MainTree := .split 1 2 n3209 n3210
private def n3211 : MainTree := .leaf (mainGapLeaf ![8, 3, 3, 0, 1, 1, 1])
private def n3207 : MainTree := .split 0 5 n3208 n3211
private def n3199 : MainTree := .split 6 0 n3200 n3207
private def n3177 : MainTree := .split 5 0 n3178 n3199
private def n3131 : MainTree := .split 4 0 n3132 n3177
private def n3219 : MainTree := .leaf (mainGapLeaf ![4, 5, 2, 0, 0, 0, 0])
private def n3220 : MainTree := .leaf (mainGapLeaf ![5, 5, 2, 0, 0, 0, 0])
private def n3218 : MainTree := .split 0 4 n3219 n3220
private def n3221 : MainTree := .leaf (mainGapLeaf ![5, 5, 3, 0, 0, 0, 0])
private def n3217 : MainTree := .split 2 2 n3218 n3221
private def n3222 : MainTree := .leaf (mainGapLeaf ![5, 7, 3, 0, 0, 0, 0])
private def n3216 : MainTree := .split 1 5 n3217 n3222
private def n3223 : MainTree := .leaf (mainGapLeaf ![8, 7, 3, 0, 0, 0, 0])
private def n3215 : MainTree := .split 0 5 n3216 n3223
private def n3225 : MainTree := .leaf (mainGapLeaf ![5, 7, 3, 0, 0, 0, 1])
private def n3226 : MainTree := .leaf (mainGapLeaf ![8, 7, 3, 0, 0, 0, 1])
private def n3224 : MainTree := .split 0 5 n3225 n3226
private def n3214 : MainTree := .split 6 0 n3215 n3224
private def n3230 : MainTree := .leaf (mainGapLeaf ![5, 5, 3, 0, 0, 1, 0])
private def n3231 : MainTree := .leaf (mainGapLeaf ![5, 7, 3, 0, 0, 1, 0])
private def n3229 : MainTree := .split 1 5 n3230 n3231
private def n3232 : MainTree := .leaf (mainGapLeaf ![8, 7, 3, 0, 0, 1, 0])
private def n3228 : MainTree := .split 0 5 n3229 n3232
private def n3233 : MainTree := .leaf (mainGapLeaf ![8, 7, 3, 0, 0, 1, 1])
private def n3227 : MainTree := .split 6 0 n3228 n3233
private def n3213 : MainTree := .split 5 0 n3214 n3227
private def n3239 : MainTree := .leaf (mainGapLeaf ![5, 5, 2, 0, 1, 0, 0])
private def n3240 : MainTree := .leaf (mainGapLeaf ![5, 5, 3, 0, 1, 0, 0])
private def n3238 : MainTree := .split 2 2 n3239 n3240
private def n3241 : MainTree := .leaf (mainGapLeaf ![5, 7, 3, 0, 1, 0, 0])
private def n3237 : MainTree := .split 1 5 n3238 n3241
private def n3242 : MainTree := .leaf (mainGapLeaf ![8, 7, 3, 0, 1, 0, 0])
private def n3236 : MainTree := .split 0 5 n3237 n3242
private def n3243 : MainTree := .leaf (mainGapLeaf ![8, 7, 3, 0, 1, 0, 1])
private def n3235 : MainTree := .split 6 0 n3236 n3243
private def n3246 : MainTree := .leaf (mainGapLeaf ![5, 7, 3, 0, 1, 1, 0])
private def n3247 : MainTree := .leaf (mainGapLeaf ![8, 7, 3, 0, 1, 1, 0])
private def n3245 : MainTree := .split 0 5 n3246 n3247
private def d3248 : List ℕ := [
    0x308022240101024500128060102010320104208140001400028002220004108040300120008200020100000,
    0x4210c26030212121004452014830400908040812203034020112400a60022800c160202021110420048204,
    0x5000320c36040222131014402a62000524840410902c18050822204113044000630106822410a700018328,
    0x12a72003810534850406220912c01228060832214123006454010601440116832420a8000291180a0428142,
    0x33016404a64020602511450126842430a12921804c1a052824206115010330c460026011502321088410244,
    0x40c56012611160203442118851034422a8200491382050c044800e60416230907002322c112380708422241,
    0x5223410a843026414a74030605812500b21460136852408240a22931814c0322a062834200d161250084203,
    0x4570213452101a28861044432a14923830506c1c054810e70426208101c40917012332c212480046808031,
    0x10b3140e070146802e01962418250a32909041804324c1323a072844210d26135018430350c06a660226211,
    0x64820e80436202d18111c5092700a422342c3125801461316220544410071a853036424a840069406158225,
    0x3610c845001628440360c16a76032631107814580202b23462111a3887105440a242a24933840516c0522c0,
    0x16950625832508c20b4141e080156812e11972428260a0a103c42919051814334c2324a006682805154220d,
    0x3c074830e46212d01328121c6093701a432352c08a41268024623106572215454103a1072a863046434a015,
    0x11638450370c26a86008942641117824512b33472121a48804e8100396441a252a3490b043850506326c152,
    0x5140722e066822e21982438204d70a1a113c5292900c461824344c3325a016615164230d0744610271c8550,
    0x362a442362c18a51278034633109816582204b25464113a2073a87305640c244a11526960635842518c30b,
    0x58814e1397442a262a0c105c44900f1b053860516336c2524c008684807140e56222d11338131c0e8709470,
    0x4326a026625108574240d17456105a1272c865021648460380c36a0351895265112783450ac22b43482131a,
    0x2153697060d045852508301e28c40b6141723e076832e31948214d80a0332a123c6293901c471834354c0aa,
    0x41c0471e88095701363a452372c28a6128800a944643119826514b35474123a3074a806e8300596641c254a,
    0x41a68824e2398443a206d72a1c115c54910f2b00e463870526346c35201d5c018617150e66232d094213481,
    0x3663510b818584250d06b27466115a2273c87503165840e270346a13501b2896266113784451ac32b534092,
    0x55862518311e38c50b7142724e00a686809142e41958224d1333a133c7294900562c481844364c1aa5327a0,
    0x62382c38a0557121a95465312983650cc24b45484133a4075a816e1597642c264a3150e107c46980602f1d0,
    0x25c64920f3b01e473880536356c0ca45211d6c028627160e0a576242d19431358151c07a1472e86702364a4,
    0x794166841e280356a23511b3897260f07114785450a303e2ac42b63419251a78834e3394a216d82a0532c1,
    0xb42334a143c0678295901563c454374c2aa6328a00c94664510171b828560d16b37476125a3274c808e850,
    0x6a826e2598643c208d74a4151e117c56912f2d065872528321e48c60b81437203d5e01a619152e51968234d,
    0x86252d08b29441368161c17a2473e87703365a472348a15581203b2a96466313984651cc34b5540b243a507,
    0x2920c661a8880b144e4395a226d1533c135c74930f4b00762e483846366c1ca55221d7c038637170e0d81a5,
    0xec70d26b47486135a4275c818e1795167842e266a33509c21b48982604f1f08115786451a313e3ac52b734,
    0x13d6e02a629162e0c561978244d1b43335a153c09a1676902564c464384c3aa0757321c95665511172b8385,
    0xc305e2cc44b6541b253a6077a836e3594c218d84a5150732e127c66922f3d075882538331e58c0ea70b472,
    0x48647180e0371d82a562d18b39451378171c27a3474e80ae8700994366a482358a25513b3a9746731498565,
    0x4ac62b83439205d1c671a1b154e5396a236d0d42534c145c08784940f5b01763e456376c2ca65231d8c00e9,
    0x6512173b84851ec80d36b5740d245a5276c828e2796168843e20ad76a43519c31b58914f2f06787452a323e,
    0x80b57223d7e03a639172e0f81c571988254d0ab2b44336a163c19a2677903565c47434aa17583205b2c9666,
    0x1c315e3cc54b7542b20e663a7078a80d146e45901f5c228d6151733e137c76932f4d009685848341e68c1ea,
    0x1e95865711372d83a572d28b49461388181c37a4475e81ae1995367a468a3550bc23b4a984606f831598665,
    0x33e5ac72b49215d2c681a2b164e0e56397a246d1d43535c155c0ba18750f6b02764e466386c3ca09575241d,
    0x7513174b85850e307e2ec46b6741d255a6277c838e3797164e21ad86a53509329c41b68924f3f07788453a3,
    0x67233d8e04a649182e0571f82c581964d1ab3b45337a173c29a3670ce8900b94566c48435aa27515b3c9766,
    0x25e4cc64b8543b207d1e673a8071d156e55911f6c238d0f47152734e147c0a786942f5d019658351e78c2ea,
    0x7b2e96866712373d84a582d38b5940f271347a5476e82ae2996368a40cd78a4551bc33b5a916f6987652c3,
    0x4a343e6ac82b59225d3c63b174e1e57398a256d0cb2d44536c165c1ba28760f7b03765e47634ca19585251d,
    0x8514175b86851e317e3ec56b7742d265a7278c80f148e47981603f5e22ad63519339c51b78934f4f00b6878,
    0x88c3ea0b577243d5a65911572f83c574d2ab4b46338a183c39a4671ce1b95567c46aa3750dc25b4c986608f,
    0x26f7988653c335e5cc74b4b217d2e683a2d166e65921f7c248d1f48153735e157c0da1a752f6d029668361e,
    0x8635ca29561d17b3e97867713374d85a509e48b6941f281357a6477e83ae3997361cd88a5550b32bc43b6a9,
    0x88944f5f01b65a353e7ac69235d4c64b184e0772e583966d1cb3d45537c175c2ba3870ee70f8b00d94766e4,
    0x7aa4751dc35b5c918f5176b87852e327e4ec66b8743d209d75a8271f158e57913f6e23ad73529349c0c761b,
    0x67c1da2a762f7d039678371e4ea1b587253d09b6a66912573f84c584d3ab5b473349a5672ce2b96568c40ed,
    0x49983605f2cd6551b33bc53b7a936f0d68984c345e6cc84b5b227d3e63d176e75931f8c258d0eb2f44736e1,
    0x8c185c3ba4871ee80f1d95767e46ca3950fc71d27b4e98860af8714375d86a519e58b7942f267a7478e84ae,
    0x2f168e67923f7e24ad83539359c0fa1c771b54f6f02b66a363e8ac0d579245d5c65b11773e576d2cb4d4653,
    0x4f85c50be4ab6b483359a6673ce3b97561ed8aa5750d32dc45b6c928f6177b88853e337e5ec76b4d219d85a,
    0x6b237d4e64d186e09785941f68d1eb3f45737e177c2da3a772f8d00f949688381e5ea2b563d19b7a6791357,
    0x81d37b5e91af5376d87a529e68b8943f20bd77a8475ae59915f3cd7552b34bc0e763b8a946f1d65c355e7cc,
    0x1fa2c781b64f7f03b67a373e1d589255d0bb6c66b12774e586d3cb5d47534ba5872ee2d96768e47ca4951fc,
    0x7674ce4b985607f2ed6751d33dc55b7c938f0f67178b84e347e6ec86b5d229d3f178e77933f8e25ad49369c,
    0x5e65d119751f78d2eb4f46738e187c3da4a782f1f95966ea3b573d29b8a60cf8914575f86c51be5ab7b469a,
    0x2fc47b6e92af6377d88a539e78b4f21bd87a6ae69925f4cd8553b35bc1e773b56f2d66c365e8cc0f57b247d,
    0x6ad59379c2fa3c774f8f04b68a383e2d565d1bb7c67b13775e50de4cb6d48535ba6873ee3d97768ca5950f3,
    0x7c52be6ab8b40dd79a8675ce5b917f3ed7752d34dc65b8c948f1f68175e357e7ec6d239d4f188e0b787943f,
    0x2e783b66f3d67c375e1f58b257d0db6e66d129761f88d3eb5f47734da5a72f96967ea4b583d39b1cf5576f8,
    0x4776e51de5cb7d46ba7874ee4d987609f6951f33fc57b7e93af7378d849e88b5f22bd7ae79935f5cd4b36bc,
    0x27f4ed8753d35dc75b58f2f66e367e8ec7d249d5f11b753f7ad69389c3fa4c784f5b63d575d2bb8c60ef8b1,
    0x85e2f567d1db7e67d13970fe71f4eb6f48735da6a73f97968ea5b549b2cf6577f88c53be7ab1dd89a6ce6b9,
    0x6cb8d40fd7ba8875ee5d919f7952f34fc67b8e94af83759e6f23bd8ae0d789945f6cd5b37bc3e776f4d68c3,
    0x7ce7b937f5ed4d36dc85b68f3f67e377e8d259d0fb6f12b763f8ad7934fa5c76b64d585d3bb1ef5777e52de,
    0x7cd6b38bc4e786f5d63f577d2db8e68d14971fe81f5eb7f46da7a74f98960bf6b559b3cf7578f84be8ab2dd,
    0x7f13b773f8935fa6c77b65d54bb2ef6778e53de7cb1fd8ba6ee6d929f8953f35fc77b5af69e7f24bd1d755f,
    0x87d3db5972fe6eb8f47da8a75f91bf7b569b4cf8575be3dd8ce0f78b947f6ed5d37dc78f4f68e387e69d1fb,
    0x83f6fa7c78b60df6d55bb3ef7774de8cb2fd7ee7d939f4f36fc87b6af79e8f25bd2d765f8cd7b35e76d64f5,
    0x3d775f8b36e77d65f54db6973fe7eb8da6f92bf8b579b5cf6be4dd1f757f7ed6d38dc88f5f679d2fb8f14b7,
    0x89b6cf7be5dd2f767f8ed7d36f689d3fb5b77fa8c71df7d56bb4ef8775de3fd8ee8d949f5f37fc7af89e6bd,
    0x77f8d37f64fb6b78fa2df8d57bb5ef6de4fd59f6f38fc8af7bd4d785f7e78d60ff6f55db7974fe8eb7f93bf,
    0x5bf8cf7dd4f787f8f65fb7b73df8bb6ef7de5fd69f7f38bd5d78e71ff7f56db8975fe8f94bf7cf8be6dd3f7,
    0x4ff8fe7bf6f77fb5df8ef7fd89f7d73ff8db7fe6bf8dd5f76fb8b74df7ef8de6fd79f8f36d72ff8f57db6fe,
    0x8ff7ff8df6ff8f77df5ff8bf7f78fb6df8fd8d7]
private def a3248 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![8, 7, 3, 0, 1, 1, 1])
    4096 29 2304 d3248
private def n3248 : MainTree := .leaf (mainGapLeafOfDivisors ![8, 7, 3, 0, 1, 1, 1] a3248)
private def n3244 : MainTree := .split 6 0 n3245 n3248
private def n3234 : MainTree := .split 5 0 n3235 n3244
private def n3212 : MainTree := .split 4 0 n3213 n3234
private def n3130 : MainTree := .split 1 3 n3131 n3212

private theorem c3133 : C ![4, 2, 2, 0, 0, 0, 0] ![8, 3, 3, 0, 0, 0, 1] n3133 := by
  decide +kernel

private theorem c3161 : C ![4, 2, 2, 0, 0, 1, 0] ![8, 3, 3, 0, 0, 1, 0] n3161 := by
  decide +kernel

private theorem c3172 : C ![4, 2, 2, 0, 0, 1, 1] ![8, 3, 3, 0, 0, 1, 1] n3172 := by
  decide +kernel

private theorem c3160 : C ![4, 2, 2, 0, 0, 1, 0] ![8, 3, 3, 0, 0, 1, 1] n3160 := by
  exact checkExponentBoxTree_join c3161 c3172 (by decide +kernel)

private theorem c3132 : C ![4, 2, 2, 0, 0, 0, 0] ![8, 3, 3, 0, 0, 1, 1] n3132 := by
  exact checkExponentBoxTree_join c3133 c3160 (by decide +kernel)

private theorem c3179 : C ![4, 2, 2, 0, 1, 0, 0] ![8, 3, 3, 0, 1, 0, 0] n3179 := by
  decide +kernel

private theorem c3194 : C ![4, 2, 2, 0, 1, 0, 1] ![8, 3, 3, 0, 1, 0, 1] n3194 := by
  decide +kernel

private theorem c3178 : C ![4, 2, 2, 0, 1, 0, 0] ![8, 3, 3, 0, 1, 0, 1] n3178 := by
  exact checkExponentBoxTree_join c3179 c3194 (by decide +kernel)

private theorem c3200 : C ![4, 2, 2, 0, 1, 1, 0] ![8, 3, 3, 0, 1, 1, 0] n3200 := by
  decide +kernel

private theorem c3208 : C ![4, 2, 2, 0, 1, 1, 1] ![5, 3, 3, 0, 1, 1, 1] n3208 := by
  decide +kernel

private theorem c3211 : C ![6, 2, 2, 0, 1, 1, 1] ![8, 3, 3, 0, 1, 1, 1] n3211 := by
  decide +kernel

private theorem c3207 : C ![4, 2, 2, 0, 1, 1, 1] ![8, 3, 3, 0, 1, 1, 1] n3207 := by
  exact checkExponentBoxTree_join c3208 c3211 (by decide +kernel)

private theorem c3199 : C ![4, 2, 2, 0, 1, 1, 0] ![8, 3, 3, 0, 1, 1, 1] n3199 := by
  exact checkExponentBoxTree_join c3200 c3207 (by decide +kernel)

private theorem c3177 : C ![4, 2, 2, 0, 1, 0, 0] ![8, 3, 3, 0, 1, 1, 1] n3177 := by
  exact checkExponentBoxTree_join c3178 c3199 (by decide +kernel)

private theorem c3131 : C ![4, 2, 2, 0, 0, 0, 0] ![8, 3, 3, 0, 1, 1, 1] n3131 := by
  exact checkExponentBoxTree_join c3132 c3177 (by decide +kernel)

private theorem c3214 : C ![4, 4, 2, 0, 0, 0, 0] ![8, 7, 3, 0, 0, 0, 1] n3214 := by
  decide +kernel

private theorem c3228 : C ![4, 4, 2, 0, 0, 1, 0] ![8, 7, 3, 0, 0, 1, 0] n3228 := by
  decide +kernel

private theorem c3233 : C ![4, 4, 2, 0, 0, 1, 1] ![8, 7, 3, 0, 0, 1, 1] n3233 := by
  decide +kernel

private theorem c3227 : C ![4, 4, 2, 0, 0, 1, 0] ![8, 7, 3, 0, 0, 1, 1] n3227 := by
  exact checkExponentBoxTree_join c3228 c3233 (by decide +kernel)

private theorem c3213 : C ![4, 4, 2, 0, 0, 0, 0] ![8, 7, 3, 0, 0, 1, 1] n3213 := by
  exact checkExponentBoxTree_join c3214 c3227 (by decide +kernel)

private theorem c3236 : C ![4, 4, 2, 0, 1, 0, 0] ![8, 7, 3, 0, 1, 0, 0] n3236 := by
  decide +kernel

private theorem c3243 : C ![4, 4, 2, 0, 1, 0, 1] ![8, 7, 3, 0, 1, 0, 1] n3243 := by
  decide +kernel

private theorem c3235 : C ![4, 4, 2, 0, 1, 0, 0] ![8, 7, 3, 0, 1, 0, 1] n3235 := by
  exact checkExponentBoxTree_join c3236 c3243 (by decide +kernel)

private theorem c3246 : C ![4, 4, 2, 0, 1, 1, 0] ![5, 7, 3, 0, 1, 1, 0] n3246 := by
  decide +kernel

private theorem c3247 : C ![6, 4, 2, 0, 1, 1, 0] ![8, 7, 3, 0, 1, 1, 0] n3247 := by
  decide +kernel

private theorem c3245 : C ![4, 4, 2, 0, 1, 1, 0] ![8, 7, 3, 0, 1, 1, 0] n3245 := by
  exact checkExponentBoxTree_join c3246 c3247 (by decide +kernel)

private theorem c3248 : C ![4, 4, 2, 0, 1, 1, 1] ![8, 7, 3, 0, 1, 1, 1] n3248 := by
  decide +kernel

private theorem c3244 : C ![4, 4, 2, 0, 1, 1, 0] ![8, 7, 3, 0, 1, 1, 1] n3244 := by
  exact checkExponentBoxTree_join c3245 c3248 (by decide +kernel)

private theorem c3234 : C ![4, 4, 2, 0, 1, 0, 0] ![8, 7, 3, 0, 1, 1, 1] n3234 := by
  exact checkExponentBoxTree_join c3235 c3244 (by decide +kernel)

private theorem c3212 : C ![4, 4, 2, 0, 0, 0, 0] ![8, 7, 3, 0, 1, 1, 1] n3212 := by
  exact checkExponentBoxTree_join c3213 c3234 (by decide +kernel)

private theorem c3130 : C ![4, 2, 2, 0, 0, 0, 0] ![8, 7, 3, 0, 1, 1, 1] n3130 := by
  exact checkExponentBoxTree_join c3131 c3212 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n3130

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c3130

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main13
