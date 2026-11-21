/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/Main05
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Main05.chunk_checked
   digest: Exact numerical and binary coverage certificate for the main exponent box. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts01
import D5.S3.Arith.Divisors.ErdosNicolas.Data.RankReadouts00

/-! Opaque numerical subproofs bound temporary kernel reduction memory. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

namespace D5.S3.Arith.ErdosNicolas.Data.Main05

private abbrev C (lo hi : Fin 7 → ℕ) (tree : MainTree) : Prop :=
  checkExponentBoxTree mainScale boxPrimes lo hi tree = true

/-- Lower exponents at this subtree root. -/
def lo : Fin 7 → ℕ := ![4, 0, 2, 0, 0, 0, 0]

/-- Upper exponents at the same root. -/
def hi : Fin 7 → ℕ := ![17, 1, 3, 2, 1, 1, 1]

private def n2207 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 0, 0, 0, 0])
private def n2208 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 0, 0, 0, 1])
private def n2206 : MainTree := .split 6 0 n2207 n2208
private def n2210 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 3, 0, 0, 1, 0])
private def n2211 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 0, 0, 1, 1])
private def n2209 : MainTree := .split 6 0 n2210 n2211
private def n2205 : MainTree := .split 5 0 n2206 n2209
private def n2214 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 0, 1, 0, 0])
private def n2215 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 0, 1, 0, 1])
private def n2213 : MainTree := .split 6 0 n2214 n2215
private def n2217 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 0, 1, 1, 0])
private def n2218 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 0, 1, 1, 1])
private def n2216 : MainTree := .split 6 0 n2217 n2218
private def n2212 : MainTree := .split 5 0 n2213 n2216
private def n2204 : MainTree := .split 4 0 n2205 n2212
private def n2225 : MainTree := .leaf (mainRankLeaf 2 ![4, 1, 2, 0, 0, 0, 0])
private def n2226 : MainTree := .leaf (mainRankLeaf 2 ![5, 1, 2, 0, 0, 0, 0])
private def n2224 : MainTree := .split 0 4 n2225 n2226
private def n2227 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 0, 0, 0, 0])
private def n2223 : MainTree := .split 2 2 n2224 n2227
private def n2229 : MainTree := .leaf (mainGapLeaf ![8, 1, 2, 0, 0, 0, 0])
private def n2230 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 0, 0, 0, 0])
private def n2228 : MainTree := .split 2 2 n2229 n2230
private def n2222 : MainTree := .split 0 5 n2223 n2228
private def n2233 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 0, 0, 0, 1])
private def n2234 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 0, 0, 0, 1])
private def n2232 : MainTree := .split 2 2 n2233 n2234
private def n2235 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 0, 0, 0, 1])
private def n2231 : MainTree := .split 0 5 n2232 n2235
private def n2221 : MainTree := .split 6 0 n2222 n2231
private def n2240 : MainTree := .leaf (mainGapLeaf ![4, 1, 2, 0, 0, 1, 0])
private def n2241 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 0, 0, 1, 0])
private def n2239 : MainTree := .split 0 4 n2240 n2241
private def n2242 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 0, 0, 1, 0])
private def n2238 : MainTree := .split 2 2 n2239 n2242
private def n2243 : MainTree := .leaf (mainRankLeaf 1 ![8, 1, 3, 0, 0, 1, 0])
private def n2237 : MainTree := .split 0 5 n2238 n2243
private def n2245 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 0, 0, 1, 1])
private def n2246 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 0, 0, 1, 1])
private def n2244 : MainTree := .split 0 5 n2245 n2246
private def n2236 : MainTree := .split 6 0 n2237 n2244
private def n2220 : MainTree := .split 5 0 n2221 n2236
private def n2252 : MainTree := .leaf (mainGapLeaf ![4, 1, 2, 0, 1, 0, 0])
private def n2253 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 0, 1, 0, 0])
private def n2251 : MainTree := .split 0 4 n2252 n2253
private def n2254 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 0, 1, 0, 0])
private def n2250 : MainTree := .split 2 2 n2251 n2254
private def n2255 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 0, 1, 0, 0])
private def n2249 : MainTree := .split 0 5 n2250 n2255
private def n2257 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 0, 1, 0, 1])
private def n2258 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 0, 1, 0, 1])
private def n2256 : MainTree := .split 0 5 n2257 n2258
private def n2248 : MainTree := .split 6 0 n2249 n2256
private def n2261 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 0, 1, 1, 0])
private def n2262 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 0, 1, 1, 0])
private def n2260 : MainTree := .split 0 5 n2261 n2262
private def n2263 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 0, 1, 1, 1])
private def n2259 : MainTree := .split 6 0 n2260 n2263
private def n2247 : MainTree := .split 5 0 n2248 n2259
private def n2219 : MainTree := .split 4 0 n2220 n2247
private def n2203 : MainTree := .split 1 0 n2204 n2219
private def n2270 : MainTree := .leaf (mainGapLeaf ![5, 0, 3, 1, 0, 0, 0])
private def n2271 : MainTree := .leaf (mainGapLeaf ![5, 0, 3, 2, 0, 0, 0])
private def n2269 : MainTree := .split 3 1 n2270 n2271
private def n2272 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 2, 0, 0, 0])
private def n2268 : MainTree := .split 0 5 n2269 n2272
private def n2274 : MainTree := .leaf (mainGapLeaf ![5, 0, 3, 2, 0, 0, 1])
private def n2275 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 2, 0, 0, 1])
private def n2273 : MainTree := .split 0 5 n2274 n2275
private def n2267 : MainTree := .split 6 0 n2268 n2273
private def n2278 : MainTree := .leaf (mainGapLeaf ![5, 0, 3, 2, 0, 1, 0])
private def n2279 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 2, 0, 1, 0])
private def n2277 : MainTree := .split 0 5 n2278 n2279
private def n2280 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 3, 2, 0, 1, 1])
private def n2276 : MainTree := .split 6 0 n2277 n2280
private def n2266 : MainTree := .split 5 0 n2267 n2276
private def n2285 : MainTree := .leaf (mainGapLeaf ![5, 0, 3, 1, 1, 0, 0])
private def n2286 : MainTree := .leaf (mainGapLeaf ![5, 0, 3, 2, 1, 0, 0])
private def n2284 : MainTree := .split 3 1 n2285 n2286
private def n2287 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 3, 2, 1, 0, 0])
private def n2283 : MainTree := .split 0 5 n2284 n2287
private def n2288 : MainTree := .leaf (mainRankLeaf 1 ![8, 0, 3, 2, 1, 0, 1])
private def n2282 : MainTree := .split 6 0 n2283 n2288
private def n2291 : MainTree := .leaf (mainGapLeaf ![5, 0, 3, 2, 1, 1, 0])
private def n2292 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 2, 1, 1, 0])
private def n2290 : MainTree := .split 0 5 n2291 n2292
private def n2293 : MainTree := .leaf (mainGapLeaf ![8, 0, 3, 2, 1, 1, 1])
private def n2289 : MainTree := .split 6 0 n2290 n2293
private def n2281 : MainTree := .split 5 0 n2282 n2289
private def n2265 : MainTree := .split 4 0 n2266 n2281
private def n2301 : MainTree := .leaf (mainRankLeaf 2 ![4, 1, 2, 1, 0, 0, 0])
private def n2302 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 1, 0, 0, 0])
private def n2300 : MainTree := .split 0 4 n2301 n2302
private def n2303 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 1, 0, 0, 0])
private def n2299 : MainTree := .split 2 2 n2300 n2303
private def n2306 : MainTree := .leaf (mainGapLeaf ![4, 1, 2, 2, 0, 0, 0])
private def n2307 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 2, 0, 0, 0])
private def n2305 : MainTree := .split 0 4 n2306 n2307
private def n2308 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 2, 0, 0, 0])
private def n2304 : MainTree := .split 2 2 n2305 n2308
private def n2298 : MainTree := .split 3 1 n2299 n2304
private def n2310 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 1, 0, 0, 0])
private def n2311 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 2, 0, 0, 0])
private def n2309 : MainTree := .split 3 1 n2310 n2311
private def n2297 : MainTree := .split 0 5 n2298 n2309
private def n2316 : MainTree := .leaf (mainGapLeaf ![4, 1, 2, 1, 0, 0, 1])
private def n2317 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 1, 0, 0, 1])
private def n2315 : MainTree := .split 0 4 n2316 n2317
private def n2318 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 1, 0, 0, 1])
private def n2314 : MainTree := .split 2 2 n2315 n2318
private def n2319 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 2, 0, 0, 1])
private def n2313 : MainTree := .split 3 1 n2314 n2319
private def n2321 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 1, 0, 0, 1])
private def n2322 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 2, 0, 0, 1])
private def n2320 : MainTree := .split 3 1 n2321 n2322
private def n2312 : MainTree := .split 0 5 n2313 n2320
private def n2296 : MainTree := .split 6 0 n2297 n2312
private def n2328 : MainTree := .leaf (mainGapLeaf ![4, 1, 2, 1, 0, 1, 0])
private def n2329 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 1, 0, 1, 0])
private def n2327 : MainTree := .split 0 4 n2328 n2329
private def n2330 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 1, 0, 1, 0])
private def n2326 : MainTree := .split 2 2 n2327 n2330
private def n2331 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 2, 0, 1, 0])
private def n2325 : MainTree := .split 3 1 n2326 n2331
private def n2333 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 1, 0, 1, 0])
private def n2334 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 2, 0, 1, 0])
private def n2332 : MainTree := .split 3 1 n2333 n2334
private def n2324 : MainTree := .split 0 5 n2325 n2332
private def n2337 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 1, 0, 1, 1])
private def n2338 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 2, 0, 1, 1])
private def n2336 : MainTree := .split 3 1 n2337 n2338
private def n2339 : MainTree :=
  .leaf (.rankIndexed 1 864 RankReadouts00.rankReadout2339)
private def n2335 : MainTree := .split 0 5 n2336 n2339
private def n2323 : MainTree := .split 6 0 n2324 n2335
private def n2295 : MainTree := .split 5 0 n2296 n2323
private def n2346 : MainTree := .leaf (mainGapLeaf ![4, 1, 2, 1, 1, 0, 0])
private def n2347 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 1, 1, 0, 0])
private def n2345 : MainTree := .split 0 4 n2346 n2347
private def n2348 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 1, 1, 0, 0])
private def n2344 : MainTree := .split 2 2 n2345 n2348
private def n2349 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 2, 1, 0, 0])
private def n2343 : MainTree := .split 3 1 n2344 n2349
private def n2352 : MainTree := .leaf (mainGapLeaf ![8, 1, 2, 1, 1, 0, 0])
private def n2353 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 1, 1, 0, 0])
private def n2351 : MainTree := .split 2 2 n2352 n2353
private def n2354 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 2, 1, 0, 0])
private def n2350 : MainTree := .split 3 1 n2351 n2354
private def n2342 : MainTree := .split 0 5 n2343 n2350
private def n2357 : MainTree := .leaf (mainRankLeaf 1 ![5, 1, 3, 1, 1, 0, 1])
private def n2358 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 2, 1, 0, 1])
private def n2356 : MainTree := .split 3 1 n2357 n2358
private def n2359 : MainTree :=
  .leaf (.rankIndexed 1 864 RankReadouts00.rankReadout2359)
private def n2355 : MainTree := .split 0 5 n2356 n2359
private def n2341 : MainTree := .split 6 0 n2342 n2355
private def n2364 : MainTree := .leaf (mainGapLeaf ![5, 1, 2, 1, 1, 1, 0])
private def n2365 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 1, 1, 1, 0])
private def n2363 : MainTree := .split 2 2 n2364 n2365
private def n2366 : MainTree := .leaf (mainGapLeaf ![5, 1, 3, 2, 1, 1, 0])
private def n2362 : MainTree := .split 3 1 n2363 n2366
private def n2368 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 1, 1, 1, 0])
private def n2369 : MainTree := .leaf (mainGapLeaf ![8, 1, 3, 2, 1, 1, 0])
private def n2367 : MainTree := .split 3 1 n2368 n2369
private def n2361 : MainTree := .split 0 5 n2362 n2367
private def n2371 : MainTree :=
  .leaf (.rankIndexed 1 1152 RankReadouts00.rankReadout2371)
private def d2372 : List ℕ := [
    0x3084a12c062040304323c02706206103054031034198002c003c0c8004780020d84800209001830018060000,
    0x90ae004b081b8201211213603421000a488064f4318244030480e03024900d4803f09200e1820c23c008360,
    0x50de06486c79000cce140604785381900f5380028ca6080e06caa80f8f60f10cc2a01c0031a04827906d540,
    0x784a8598250274092d00a818a62834bc41f0665b413c0652615118c4204c0632600681a980aa43358003c908,
    0x3f83caac0126c4931680213e061832b201e84a9e08146c82612d1393903a21c18925808a440c34b819818a00,
    0x9f09240e9ec1c5520c1b1c0a049878ac00232084a3617e0c40fd0e4cc05a0c288849407894c8437096614063,
    0x6333a091abc01a6cb0c0911a5089860407203855808448c495f001b3687aa408d48485618d1f901ca20d4092,
    0x1baab0d160810290dee1103cc6c5c00d1a845521084a0e92c1e82ba01669114245290c286f1e9a889e026082,
    0xe3389e610000f140d0b70288c181d1e594036d3a2aaa826503f0499c8861ed2b919cd21341520796e039309,
    0x9c24289a570055241bd0cb4c81b974305072821e519e5538103eb38218509ec82cb5078dbe0b019a9c8a8992,
    0x2136916c0299342b1bc98e8101b5942121f99e0993c933adb05026206c50581c9c3a0a9938c403238083da14,
    0x1d99a151c3c2e0635992114a409898da2918700550c7a20986180350d6811e30fa54b580cdb346d58052a13e,
    0x6634012893b5a8096d09ca3e98c0548eaaa10e8c5b240b04b9d43c51f2b224509c4bcda49ebf806673101499,
    0x6287f8e4e647303a6ad16c872231274c825afa1690233787ca44a5d85858033b221ec805e1d5c02ca41b309a,
    0x12cd8e7e23049afc968b121cc7c73154c5005a8c3854ba022990cf01ea4ad6201590c6e9b2e2013296dfa42a,
    0x72839730a8a5685a4d56101133e925be423007cf746890a6e5c454a2b8c7a148523fb2e079a8c585564099ac,
    0x298c3ac40423db2a1c90e34f8acaa488663a1467622024ef88db2c19078704a8d66a1098ad3f1089701889fb,
    0x10ad0115247229a40a53e1b606d4f5b84170356a327a84a138acb1b9693a9ea2be01ea262c1a9c3424d164f9,
    0xa515153cc4809b82841a1c7bd3a4892bdaf06cda6382c3234d361568476f03b2f061a106593917a469958e0c,
    0x3cf2885a27670350caa99682012c3ace64352c4826807a2aee2a1a5694dd114a6a07c526dd30b9487606faae,
    0x7b75d0175aa928df8590cf693461349535d80f6dc873418f3b2410255b5a2291a3678dcb049467ba446d62e0,
    0x9c79f09b3b079a406b94519242913337128b00175307076751054a1ce09d555c442f06570307f67539487219,
    0xdeba5950fe4139e9e5d6453067db75e8c0a2899cd0821a50d6e02d93d6a4e937dc702c539c0c88464d96216,
    0x4c6ff21903740d274e8e6c740a9eb117466d10701a154ad34085935b4cb6ab882b3882ba48b7ba2899605434,
    0x4709549fbfab4a7396cc9bc682b47766aaa90f8b918f812172ec329426eb07ee79266b32471c26db8a050d12,
    0x667332812537d8b5813da33ed1c2469c1c642ae88d522c8c9a1885a40b301d53c71f6a516556113ccd5b5d04,
    0xaa30eeea08e64a166654f425eea5f51be59322f1209d6b097e176a82c4fe6e41cd406e7076d5ecd2a4a1e971,
    0xa9ca0a168562c374991cbc9e43dd6355d02ea4630367c4426d1a3f6a02b558b5903967d73339ac623ad4216e,
    0x376d51c56212bcfd615dc45f0c54ffcbaccaa39ccd5b2da6bb0a08d9fc8c927cc9239a61f4ad38d86f4f9b8c,
    0x35b8784bb529fa8c5f9d8c08d70989cac72c39f31ab6a615354096b0ab7470908b448f9a7891a58b60235487,
    0x516ad62d1ab6888bb08cfbd28539f2919b156d0f7c699542f13f389a965760c31f0a73b9114b9d10a3561c5c,
    0x952e4e9627d567133070876853b48b221d24f8ebe5b236ee1b0e8ba1aed46904272b6bd022cb6b82e55eb650,
    0x94d6c4ed385c802e6955474f70522504f43d2d675e84770f555fd7a69d1670da2d4dc536df2f261f624219dc,
    0x7be44ed72e2af22d9a6b83a389b4abc12b7a1dd78cb3c9841b413d3ad9158d3b76be1835a0a2b22ba44a5ae4,
    0x82378273a1b768416bb6818ab259a5b75a349ae022ee07f6ed074a53b392b3a2afa535a8be33e89382d0ecd8,
    0x16703a8caed65c8373f3b279f92481a9cad314ef60a667adce861478056b4eb2e19478f05ae724ef118bd197,
    0x38d24f160a5a2c99e1b6b0802baceaa0b74959b38a9a88a5e6f56076773528510f5bd5d417dab8f1255bfe3a,
    0x988eb87fe7b59d5954cb6fbd38a851a3c7fd4256ed9893e74f373a2c725da06c43bb8cb50bcd2cfa4ddd8d73,
    0xa27ab0b33fd86773103cc2cdaa59d0d632eacde8323a4af347505a75b71d0e2e3615f456ab40b86a17aed32b,
    0x52ab2e3262613ed6a82a39d54feeca5ca39ee7b1a8efcd74e2aac3f2e6176675d975afb966c7291e70dae629,
    0xc4ad6617ea92c6bf25f5c973b962afa938c48da66d03d38fb56bd923ef1c719a86aa6596eb3270b73da60bab,
    0x44d2f679e8c58f609ab461c468d5fbdc65f4c5ec8e677374d14296fbab85847ccb9ea47b4d3ebb091b8dfb8e,
    0xb031ac5f355717490afc1ab8abe65de54d14a3e2f1afbf18567fa3323b63b4cc6d95ce369954f5070702bdd3,
    0x9579105ed2e4ff13a0ccef446ef2bf6898bb87da9d225ed63423dc395ae5f292b7a62d1b09a25d2cf9c8ddb6,
    0xa5b5ba26df2c1ed0e6e117d26b9abedb370f9085dc16a42bd65be86774f5f28c5bbe8d1517e9529f62eda9de,
    0x76d93483e83adb15dbbdf180cb96539dbced9069597e82b12ef221f9b5a15dcd7b69f47937eb8b7ebcceee4e,
    0xc7b9ce2397b9ad785dad778f525e8deb480abbd07e4bceaa7ab597dbdccfe874d9b5eb8e3e63e16f47609de2,
    0xc5b45e1beb198ce96b3a9bbd68fa6ad0bd48b7ecd479c7703eef32fcfeecd4ededc5c29e86eb2807670ebba6,
    0xcb8a5e3350747765b50c75c6f4eaab85fbb7315d7acf6bd8ad1eeae7ff73acce6f7474f0bbddd9a7a8a3b1c7,
    0x97fa3b2cc63bf88df4ed93a6ca1eebcf7b0d19713b5bd56bfacadcb73f96a9cccfd3cfbe39b5dd5a59ee6cc3,
    0xb6f9185fd25836efb2ae8b8bf7e6c7cafa6707513e8db06d5e935c75f795a9adfac2e47f4dd858dee3e0f2fd,
    0x2ff7966dc7ea3fae727d6fbe737573e4382f79b43bbbbebae8efe45a5f13e6f3bdaff48f5e2f7ca77d9a3e97,
    0x6bfabee7e5ea7ba8e3bcc747fa96cdd3ebbf8bf59d9d74f35f5347bd6aa7ef7d0fb3d1f71fde376fada03e77,
    0xd7f7ff2fd3fd4f67f5bc7fbcfaee6febdbef91ddfebea4f95efdc1fd1f7f69bd875ff96eff69fcbb19ecbd3b]
private def a2372 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![8, 1, 3, 2, 1, 1, 1])
    2048 32 1728 d2372
private def n2372 : MainTree := .leaf (mainGapLeafOfDivisors ![8, 1, 3, 2, 1, 1, 1] a2372)
private def n2370 : MainTree := .split 0 5 n2371 n2372
private def n2360 : MainTree := .split 6 0 n2361 n2370
private def n2340 : MainTree := .split 5 0 n2341 n2360
private def n2294 : MainTree := .split 4 0 n2295 n2340
private def n2264 : MainTree := .split 1 0 n2265 n2294
private def n2202 : MainTree := .split 3 0 n2203 n2264
private def n2377 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 0, 0, 0, 1])
private def n2378 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 0, 0, 1, 1])
private def n2376 : MainTree := .split 5 0 n2377 n2378
private def n2380 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 0, 1, 0, 1])
private def n2381 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 0, 1, 1, 1])
private def n2379 : MainTree := .split 5 0 n2380 n2381
private def n2375 : MainTree := .split 4 0 n2376 n2379
private def n2385 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 0, 0, 0, 0])
private def n2386 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 0, 0, 0, 1])
private def n2384 : MainTree := .split 6 0 n2385 n2386
private def n2388 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 0, 0, 1, 0])
private def n2389 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 0, 0, 1, 1])
private def n2387 : MainTree := .split 6 0 n2388 n2389
private def n2383 : MainTree := .split 5 0 n2384 n2387
private def n2392 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 0, 1, 0, 0])
private def n2393 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 0, 1, 0, 1])
private def n2391 : MainTree := .split 6 0 n2392 n2393
private def n2394 : MainTree :=
  .leaf (.rankIndexed 1 1152 RankReadouts00.rankReadout2394)
private def n2390 : MainTree := .split 5 0 n2391 n2394
private def n2382 : MainTree := .split 4 0 n2383 n2390
private def n2374 : MainTree := .split 1 0 n2375 n2382
private def n2399 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 2, 0, 0, 0])
private def n2400 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 2, 0, 0, 1])
private def n2398 : MainTree := .split 6 0 n2399 n2400
private def n2401 : MainTree :=
  .leaf (.rankIndexed 1 864 RankReadouts00.rankReadout2401)
private def n2397 : MainTree := .split 5 0 n2398 n2401
private def n2404 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 2, 1, 0, 0])
private def n2405 : MainTree := .leaf (mainGapLeaf ![17, 0, 3, 2, 1, 0, 1])
private def n2403 : MainTree := .split 6 0 n2404 n2405
private def n2406 : MainTree :=
  .leaf (.rankIndexed 1 1728 RankReadouts01.rankReadout2406)
private def n2402 : MainTree := .split 5 0 n2403 n2406
private def n2396 : MainTree := .split 4 0 n2397 n2402
private def n2410 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 2, 0, 0, 0])
private def n2411 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 2, 0, 0, 1])
private def n2409 : MainTree := .split 6 0 n2410 n2411
private def n2413 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 2, 0, 1, 0])
private def d2414 : List ℕ := [
    0x621e0041b01284b0190100c27804e0c40c4060a8034198004c003c0c80087806c2400104800c1800c030000,
    0x2a87b0790a80703409086e540090ae005308100910911b01a10800601a3d0c60920901c06080e4803f0920c2,
    0x18c0d43e0cd36806926152210260980363023398003d108050de0653c800c501821e24e06403e4e01980e06d,
    0x4280cc3d2ac0146c8b40111f06404b1e10984b9b009d1c81d10e0c502491031819200788a899825027968054,
    0x3e003c7b241158639e00fd2883502527c24a1c9520c30501e4b00094846c4fc1881fccc05a04424c2546e12d,
    0x8248c440d93801a55121104c960f415e00ee408a0a430c3d49e04231a9d0498da6181243521204072038958,
    0x3dab5079858274db0548ca0729c8402281a26e00f2500de559508252187ba1015d3484d0552dc07461469304,
    0x4086508533c134794281326c8284c18e827288064b0207e9c4432b802c920df0677e05d00e9043cc554ce0a2,
    0x48c6d4fe01b2049359a153170669e6109254265690e00aca2098a1806e1f9580cf36cc044296c02a93a401bd,
    0x4c87d0b50137383e9228b0324f10809e3290138cca80252d884fad11ccc602a87655087863c500587503e964,
    0xf65895680b7286cc8c1fa8585a4c50f96645005b2e808c6453c0971bcc402692f42cd84729cc0eaaba7021d,
    0x54a0a4881f2848585219a815c7e5701897843fd989466f02d46b30808a9f893cb01188d06e9c454c8541525c,
    0x3927a8acb92340459a40a63e2b607b85c27cdc05698f4ecf04a2a2c1aac3825d404fab10112543941cdfe15a,
    0x3d3088afb9134cf608a9366d02956f187a203b14a13d448c1821a75114af06d9c261a1adfa2132f00852d48c,
    0x21a7bd6b4210b4695461356dc2aed02dd076c90412b445434e2e1ba60a224b825290870551a0804e4392cb40,
    0x508d9851ad51d4c702c93b444db465c544e676040aba9d88a5251b97e4800bb01f75041928b382ae2f0cf3d0,
    0x978869b28e93a0aca722216069a04396e57205dd02499046fdf8a068705d4cb3c820acf8f3d70298bd02919d,
    0x8a40b9301d60ff020b32b17306dc8e1fe8605b527b369022e902aec32af3885e0067a26dc20e262814545133,
    0x3aa7da1416573c91ee81ac6a82c8feae478c40d9a94a6f82e4cda8279a4ae5a2d34703858d057a98a2555219,
    0xcc0e747dbe4284dd058aea3274713d3c52928c18904fa88a05b1ac81ce7398c877800aa67121f8a20b533498,
    0x530505bd0b7b58ba5850474f32c8472c046c37e341c6622fe10b97c4bd240e6aaf72d3848d2656987d61716b,
    0x6135093fcb111ab1a7c2354ad220e2bfe54f8c10602b7684492eb4484c58dca9aa7b8464fdae285a62e8a333,
    0x2f4b1411bac4ab238e5bfd2b7110d13d4222d28f9d7c5b50942f1a9520dc857da45c2f0d9414745cde46bc60,
    0x685234f5d74726be0d0bda22f831a4b6a14eb66890ee6401754b13f990899b8c584ee7715f4f045ac3dfb541,
    0x34ea39ec937980da6d12dfa223b59355852aada742258bcc1f4826c117050b92bd749218e1bf54150f0bca5b,
    0xaa0a35b7c56b4276992883818ad67722b8ba6ee522028685c5d5253bb8cea428be412bc1e910fc08d0611b88,
    0x4d5270ecabb7453b525dd47e6d6100c3a2ef9b1d4bca20ece6b914e7002f57b19fa50a19e8cb85ae8f18f05b,
    0xcc8e8641be840ebba1c997a40f270133fae2535c35b85eac5829d4850b2f9b3acc1d71d0e931d80939911c55,
    0x66ea71bf0bbb60bb5e7cb6c028e9c28e38d8c56a728b97a86e82262928746052b3c78e6a7291e4d2d421916f,
    0x8c951941cb55953f11cb1b80553555e348a60bddc26193475e04c2a2cee66e91ae7c0475ab1ffb10b9a18d18,
    0x2fcb25d849239f00671c484ced3a4c9f7b010a73139fba26b5f36186aadd859da85cb479e3b2c2973511937d,
    0x4bf7a1a3491af0e5d7e3de237841a6c2fa2d9854d3e5287331badae5d74753dd645853d118c6a627a71fd545,
    0x7186ae9a2927bb312d32e3a2acaaae2996f718ad6b0bd292cc47c185833e91bc6991471dfce3241d100bebb6,
    0xaa8a46653738b5694ef3298213c917c61a872a163bae9f295ef04897ff8c506c46cf0ed5eb113c10d16bf427,
    0x44f1674926e9407760b2bfc90e9a78dd87eed721f17bce0eb647d765f5114d1d2c7ab839a5d7d5b77119105f,
    0x94d0561b173cd0e96ef4877d882eca2f287b49303343aeae2ade2f97b730b06b6ba263be3c321ab4a5e64cea,
    0xb190d7373abbbacef1238217f6d178d2a7a72eb02a3e7131c2a928f98368e8432781d5655be409d317f48a6d,
    0xa459b5e5d7329f361c0dba5ef4a6a5287972b3a8023d8ecc7f54406aa38e22bbbc93c76e06cefbacd6a52a03,
    0x5df48701d6870f1badcb17d415265facda0d1d64b1d380b8fa73c4c4d77d1a949db09999d1dd57d5871acc3b,
    0x6ff19ad8e9896f0727f23b8db53f1b3baa0a98ef64958178f5cde847c447f0a351b150ce8d66553cfa6685b2,
    0x4671974f547958b2f2a3b29fb79201e358959f1dcc9bb050aee99afa70f870d357b136a973d1965d5814ecd6,
    0xacab0f264f58d7a75fdc422ff9d1d8dea9275e97f449a61849a7d81cc7721f3ccec32dded4d1f65b59a6acf6,
    0x8c7a56554199f778a45e3341f66220e7a76f7a705347af2e3ae02fda6cf7e63611a2f1f2af29b99b6bf4b41a,
    0x94477e08e4a9e7769af4a9b219c9d7de1c5111e976797af826bfb8db8d4d6ab29398b69e8632bd6904aaee44,
    0xab790a75e934df7e250c17c939a9d3dd97dd881aed9687f49b38d779b96f97dd2dc1f1eae2b23d5955665c5b,
    0xa048fe38eaaaa78e9df509be103f20e8894f63a1be69bbefb713595b6cbce92e07ad8e2e395bdd4930e85479,
    0xc3b48eb54d9b77a8aa5acfcb14063bea980f8e62768077b7da4fd86baf4f30f35bb1b9be6d6257076d695cbb,
    0x7777b69d6857c7856c5d1bac4a7e68db3d3507ab4e508dfa8683dee92f8fe26e86beb859a9d85ccf731f5cd2,
    0xacf93a7be9f95b9573b3b3bcb8b225d32cfb60ee5539c376ad97eb8ac335e33e9995d0772b4ffbcd8dece67e,
    0xb2578f15599cf782dc7dc1a6f31e8747dd6d57f23697bf906f26d9a8879d6f5d7bb84bfe98e138fd727584cf,
    0xcd6fbf10d97a4f5ba6edbfd4d9723deadbf528f25ddbc44d7ec8e739bd8a697dc7d5d55e86eb5827917464ab,
    0xca5a8f2cc4fd037dec3dcea7b87f5e4dbcb540f55e3bd04efef8d3ed1363f13db7adb1cf52d0bbe590f455f9,
    0xbfb66ee1c7fd637fb27e77c5b4cee5eb2d732bf2bde7c5d6773fd3bd7558f4dc1fca367af7e87c2f73669d6b,
    0xd7f97f47dffd678bf5dd9fca773f5ee5bd074ff5f5f3d175bf53e5dbf788e6fe5ed5fa36c9e2ba1fadf23e8e]
private def a2414 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![17, 1, 3, 2, 0, 1, 1])
    2048 32 1728 d2414
private def n2414 : MainTree := .leaf (mainGapLeafOfDivisors ![17, 1, 3, 2, 0, 1, 1] a2414)
private def n2412 : MainTree := .split 6 0 n2413 n2414
private def n2408 : MainTree := .split 5 0 n2409 n2412
private def n2417 : MainTree := .leaf (mainGapLeaf ![17, 1, 3, 2, 1, 0, 0])
private def d2418 : List ℕ := [
    0xf0020d80c21284b0080610647804e0c403054031034198004c003c0c83c00106c2400104800c1800c030000,
    0x3d8198540381a0484792a0048570029840dc100488d80d08409100d1e8630030480e0304492401f849007031,
    0xf8334da09e49831884098260068c09526000f4420143781941b1e419c280789381909c0019820381b4aa03e,
    0x558498b40111f00ccc807a3c2028d904c6c0274720744383144b24425c064801513304a0092d00a818c1a9e2,
    0xd4848563c01fa5106a27c24a03c7b2a431c0a03c960012128d89f83101c9980b41861104aa421b84b50a0fe,
    0x3801a455211074960f40d2720450918a41eaa889e02631a9d0af007618124c30203901c4ac0421267c06d241,
    0xcedb0548393cc201140d137028879a50274a84650254e44321015d3484d00f2dc30a1bcab3040827b8440d9,
    0x3ca33cdb0506c8285270e82728806490a4e22695c248264fc0ba18303a410aab0207e670431ed02cb50df058,
    0xeccd10f0b818ef308489948c3814413143006c811535606698092a10ab48b60150ad200dea0406e6503f33c,
    0x48a4bd0b0b078840557148332a009496a026b447d3180aaaa0c9450058750f187d2c8138dab6213e7f07324d,
    0x24f0b0b48f954c500152e83229e03d9620166cd8804d3f4d84c50e56647303a8b69c08742326412e7d06f39c,
    0x966a0fc8225c0624e5073662569bc0b5610114f94b01188d1218dd3882b90abc21fe970a32ad1ace513f118,
    0x5b036ce105c0d684db80ad4b4f04f51457248b06a916a809f4532c41ee9509f3fc54a63c14a76221090b0b0e,
    0x6d0295295101d8a515193d44809c8727584457d5e1a661a4d9fa2de2f061c10c8c39256583043340229a41f1,
    0x2ed6800fadd20cc90abab433d171829ef112b58b805a908705b70ab4100ed2c8826807a5150d37226e9ec115,
    0x6da65a2a33e3b079c40cec452148dcb66146800753a84a2ce09da2217832d39bd021aaea10a4a34afc946135,
    0x79c42d3409b572389d02495144cdf8a1a8705d5e41055655c0a62f4606675420872dc05d6ac8237ec702ca06,
    0x256b4e1816d63415e40aaa40b148172ec32a75b0007f67a599c21b7628144ff4bc6ca93c74b363a02ea72221,
    0x3fab90739ce0eecd67121f6f82e5333cd3ed2d1cf23848e386a6289164865e31034c052a042b173066d4111c,
    0xa38f155794972c8c08d5445030b8b5ac81f6c64a1400552ba8c9c5105a9ea4c1d5850595895d009e6b1aa363,
    0x5806aa343117f07ed7117c316cce481cd6f42de70b0a08e9965908e6987d51b6601bee74e33e442edd058a5e,
    0x38adcb180af418ed1e1a5d68851d170d772b5093fbdc232b1a16a56a28ff94c2a72836b015ae92249e613163,
    0x8889ddea11157d5f212b0f352fd94817ab4808d70c8e396ca0adb7934518184b4a3e72c446ada9f08d42f488,
    0x6925c96cc86386c802ea0a990dc62c25b684770f5b939e08b5ed117a82da853ac5a243b9d625552c4fdfea26,
    0x6755614a8be9d0895e969021e9b20a42357ae90d3a8e26efd6d12df8785e59348d56d5d22f2f860e6870608b,
    0x5ec67e2ea86948b5e1a17163d7702dc856de8262b2f03b581041b419dc8adc41bb7b280a6036975494e888ed,
    0x6ce807360eb7527499cce6446e005ea6aa50f465c2bb7448f125bf3aa0a361d177b42f2883b25ae453a062b5,
    0x814aceb894d7356e17a91ea90a161916f5991d241b1d80881d771978ab8099fc9c3b2e1a76b16ba814e5f358,
    0xba46ba363156ac7fe5eae6a08cde4a1d16fd8f05dce579e9a65b35047599071ba1a9ca2df421b87298a903c9,
    0xc682ce8f3b878e984a5c09464e66a32837c0475655888634618dc02538aae29db005ebb64d1d7c030a8b3b85,
    0x932b0ac04298d4c4ee89ad7f5861aa97eb50b96491cf65935271b7d8c899da71f796b989cfcfc472f9aa6b76,
    0x46f986451c77cb8c9074cc6eaed92fd1d68d591cbcf4462f7b4e11ba8b0bd64d16760a68a1c01b5cbae2427b,
    0xab8a66235ad7ada5089d7e83109d609ab8d2a49fcda65c7100beb2abd1246bc37b8c4bf185cb3c2023da6cfa,
    0x8c3839a5ca85b73e5915e00bf22665373c628362d67876a77b043459e48bdc6534a86f76622c775c95e8abff,
    0x6b8dae89e701deeb6ad2979d489e22e924dd4b1eac1657f5f5d35c47ef55148c3e2f769647b29aed0417d1a3,
    0xb470f69232781cadebac5fb78be65360d86c5ceef47890ec8505cc95e516703343940775c56489e3761edcc2,
    0x93c76f02cef71375a3835a407307373aba10ceeacb82c802fe74d2a7a7a4536cba82a8fb343a5aa4a3df6594,
    0x973999d1d0047afab54551c710ee913bc7975cca7c0db74bdea528794ab3ac64358ecc7eeec06c4915eda2f1,
    0xb150cd66d1a8eaa7a02db25df132fa60393b611c3c6e62f7565fe1c6b341b36c963a78fa6c4e77029ae94b52,
    0xb54b9e82b2ebd92566b37fc7b19b424b7c28d467f23bccb53df4e369a0ee931d218175a1cddb97c5a808fd49,
    0x99cddf1ad1fcf8ee6b34f6467a7a9c5477c2b2ec4bb2a3300eb029d8956c74c49bb0507215dd335f1b70d357,
    0x7635794ddaf893a5a9841a58760635dc87f78662117fb537aa49b2daf53557f465c24d3e56654cc73f6f23e7,
    0xb4f10595de98255e631dc05fb2ab08cfbbc51f245e3341f3373d3b7c14d1eb2b8ec993d69b3dfd3b31a8be74,
    0x64778665e288b79e6511dfc1392a79b8dbb54d5af4c5ce4ebe866b4abb91223d2e7afa56bfc19b8d55949d98,
    0x8e576661e206bb42b38d5bc8537275e934df4b60be6a74f715f76acaab65a1fd26aef046df2fbc1f2a6c847a,
    0x70790695e889774091fe69d5554df6e3ab2aefa92c0fad96f7524a7b1d0deefc79c4d6d979df8c0f285c5e49,
    0xccf405f5ea99a58e691e8077b5aaddea2a7952d67d8d8ef01f12c4eb6b7da4fd86baf1c70f35bcdf426f84da,
    0xbcd8de68e7e7775a72853a7c7a86c5d1bac4a7ed9c4dd357d60f5858df7330ed07bdd25f1fcd9d0d859a9e58,
    0x8fd79667e2ccfb59f274f7d3f4e73b3b3d7158625d32d3360e0edcac37672d5b2fbdb35e33e8595d8572b4ff,
    0xb832aec95e38fb8ab3ddfcc16e3f26d3798f43b3aeb6abf91b4bd318377275859a8877aebddc25ff84e56e55,
    0x9bba2b2e66b7dfab6cbd27add6ff535918f78a6fd4a3c9776f1135fce74375acdec8b4bf465c7d5d55eccc13,
    0xd035af296a3a7baf227df7b0f73b0fdf19b7a272d503d578ef413bfadb4fb52d8fc4f6defcc73c4342ef9643,
    0xd1dac6cddc38ff8b6ff64fcefae699dcbd6567657e57bcf8bb3fe51a77aeab1e9b83f736cf5efd0f85f2ccd3,
    0xd7f97f47dffd678bf5dd9fca7af6e7e5bd074ff5f5f3d17976b7ea7bf788e6fe8dcbdabec9e2bbfb43f5be47]
private def a2418 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![17, 1, 3, 2, 1, 0, 1])
    2048 32 1728 d2418
private def n2418 : MainTree := .leaf (mainGapLeafOfDivisors ![17, 1, 3, 2, 1, 0, 1] a2418)
private def n2416 : MainTree := .split 6 0 n2417 n2418
private def d2420 : List ℕ := [
    0x106c0610942580c4080323c027062061030540310341986001e0640023c00106c2400104800c1800c030000,
    0x1500e0018d01e41b5500242b8610370402423603421000a4887a18c12201824070124035200fc24803860878,
    0x4985446310813018c9801a06a54866b00108050de0363c8338501812703201ea700ca6080e15407c7b078866,
    0x1f030cc807a12a028d904c25ad807207443825808a4425c0cc801e13304a04e8125a0150629e20f86d04f019,
    0x28835024a7c1ec1c55218e05024cb02410947e0c40fd0e4cc05a04424a03d210dc4283f83caac0126c493168,
    0x2ba349c811414861437aa227809820a742bc36586069422618101c82b0108919f01b43d435212158635e0007,
    0x14460c0ea502745546503f4e4430f6c200ce6909a0a903cb701c9561a2c10f70881e6701508aa04a0e92c1e8,
    0x440c0485085134ae00aa4837a4c9f80372e8410f28cf604670430a102cb50df058272db064a713cc201141b8,
    0x1c01554421820478c3eab03346d49509f5a45b12685690031d021942121f99e09936c14098b6403693874153,
    0x500d84b50e51f4c603aaa843a64a2802c12e750b224509c4bdb11fc1cc4043b33443c2e0ccbcc25204d68a46,
    0x4f0589218dd6207e90a98a1fecc8e62ad16d380231274c87d0b48de7383e50b0b0322f103daae016520d984d,
    0x6109f4f94b01183dd1a1c454a2b8c7829784970a31611ace5025a7e2307e6161890e6cc55314016a0a974045,
    0x458c348b54014c61d620214a87249f3fc2b210d3b1103e30906db0e0d66a1098ad044b81e09ca28a569bc0d5,
    0x578698e09367e82ad6f03b2f0966461e91a6e45831a022a229a40a55b07082e2a327adc013a5a4ea7a8afb92,
    0x2e09442d484276db865a084e6434413408428a8d29ba7b04d5b401f5ba94a880ec2aea511230521c7bc44c22,
    0x1d4ea082b384442f18199d7a021d5d0175aa928df8597e4a31b6976b40418f3b24102ad11499e8b86e451ad6,
    0xfecf5595702986dd7a051508d94b724f1d32098e20644265a2a10b67c26cec2b99d8924291337e2d9900175,
    0xc0059923b841c2c51449fe97886481b363a0ac45d4e4336f3895a685a65b4713a00af205452054350e0cabc8,
    0x633531548b232714416bc64c0754a54082cae6027a82238d8cfec301cec683bb3555487c5cc5205cbb1e69d6,
    0x16f385750474ca9ea4c1f585037dceb12ba06b10bb54162b91e29ce55e5267137c4cca04fb4b42d6e787da38,
    0x4fe4665908e6990b51b66038ca9df21416e80ad74a5ea389e4b1b96460c448d5443f70b8c5ac8666734a1400,
    0x5c295a8a1cb7fc56d4c379b58c24891f3962236132c046a6aa341c57f02bd7117c786976481476f435dcab0a,
    0x650e4d169a28c045ea0b4a14eb156d4f84aa17a4413f7fadcb1820c4eeed088b4484a8b9879a9a84f7163023,
    0x34ef689bbf56d4b7cbcd121dceb246a9644cc1e221a17a822da4abeaf8b64e185d7eca41b897ab4896e471eb,
    0x41368a1e326106d055b574457178ddaf87b3831b49724a744476c86640a55054c844b16087b423b908d5ecf0,
    0xc08aee7724b710fcd46a029805ded0baa20ec959d55856a2fa7419f8baf4b4826c5af050b8ba40b72154736f,
    0x906c76a820787465e2abca67e766b914e8193b57b05350cd9e522018683add4b1ebb8ce5118bd8acbc1e89da,
    0x9cabb9e7a69c05271c30e3742c5aea28b97c86dac439cd8f24e92b3ae2536733805ea9aa942859705bdd123c,
    0x6a10c51d66463753955be88a60bd76a62a4075f00c0a2cee15cd5b862a47aa41ff97b0c9663378e8746020bb,
    0x39f0094e4e36fb6c133c9a3ef2d61539f473748d746ca9ad5859ae678f41130c94297025bf63c732a0c8ecb6,
    0x9a88c63211ba8ad3a17ac9cc53f1f3143802ddb1a2eba3c9eddc4998528c989dd135b519f035559562172d18,
    0xd38fe57197da2cec248a9a6f76b985c4896623da6ac2b008df30c6a38ef95fd6186ea5fad425fa3b24996397,
    0x76acaaf4345af08be312fca86f77082c79f495e8ac8a7fea671920e9996b5db11368d09eb22c19e86ae34bde,
    0x57f5f67938c7ef4d148cc42f7695d748f653572231a38c2f5b4a34bafcb6e0c4f90bf22549373c62836d3440,
    0x90f71190d544173261f459686776bb4109e2be9ede0e6d72a2898ef75ac8af029799489e22c5acf0f54ef608,
    0x9d2bc9e9e914db81a50415715921d2dd851f309ae5a387b9c193d5a56f5d67545f5f3a493752cc1b058b9ba6,
    0x5ef4a943ca59750d51f66863f776a93ec8af65178d243b7816074ef7136f2532039830d9d5dde6771e2ac8bf,
    0xa952fdacaceb199b63b1d380d39f12381b689ae94c9e972e8d1edd68e1545ad43bcdcf2e8457329f035c1640,
    0x7d387283263a4325a05e3e737362dc91fa92d4a19acdccd4023abead510171c2efa44ef301c9d70f6e98bdd5,
    0x53b8da685b177526e15d68ba66be36be2d40d5ec52e7a0b46a4aa9e6ff8f6d944c96f7d1a8d844779963754f,
    0x65b5826ac4a8cba61a7d8283998e7ebe7c34ddf1adaaa3eee5975ec9ac8ce33547d08f870a2cbb133fa8cc03,
    0xbd4d1eb2d7a9eabf9efe9dc252b28be547637914dcceb5f1273e5665876067b46bd3cfee9c6192ff6a5d9493,
    0xcf4f5f4ae0aaff065c764ca6ca4e635a78839d195de9abd5e631afdd2d4c308c1a9f722ee463341f336213b7,
    0xce5432bbeb48239117dd2ec1f2a6e3323bc355a65c5bb319e4efe098253cdc6dc0a6b2aa62bafbc51f2aec47,
    0x8f2fbb565965e749b03ca1717926df5d9986d76c86718f556e75e28d269be96ca282f929d3dc5bb5555af43f,
    0xad975e38ea46b763b37d09c4ce0f20db6a572eefc23fcd31caa9bedc416568552581f90a6e5bd94f0df355df,
    0xa0f25f1fcd989d7d9a9d86ccf405f5ea9c3d8e691bbdbe136addd4bd10b3ec6d028efaaa03e25c756d5df49f,
    0x9af19f42e9ac2b07a7fdccc6f345dddeead3a19f1ea1c2d62e8de5853f34ad9c4dd017d6b55858dfa8a9e61d,
    0xd70bfe9961395b956e55e599f6733ed679efa7e9ccaecacecef35618979fb4cd8383b9429d61bb56cbef6d62,
    0xaaf666876b682791ae0cabbc71f75859acf782dc7e4db854de63e758fd57f16697a6306f275c98879daf5d7b,
    0xd4d88685e439bb7eb35befd5b88acbd279bd6ff465918f7abb14ca3c9776dafd92ce74375ae2ac8b4befe5c7,
    0xcb373a69e81ad7a8e9ee5a89fa0afbd87a7d87ef8cdbd1340f55e3b77f7cab6e8ad4b63f2e627b6f7e6b7473,
    0xc8f7fb58d9bb871ff5962dc9f9df5ce2ea6772eceeba95f95ef3d9ecff9469dd63d3707f295cdbdfaf343e17,
    0xd7f97f47dffd678bf5dd9fca7af6e7ebecb7a0e9fdf3d17976b7ea7cbd7ef11cdfd1babf47593c577f687eb7]
private def a2420 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![17, 1, 3, 2, 1, 1, 0])
    2048 32 1728 d2420
private def n2420 : MainTree := .leaf (mainGapLeafOfDivisors ![17, 1, 3, 2, 1, 1, 0] a2420)
private def d2421 : List ℕ := [
    0x620200c10643c01381880c20302a00c40681980013000780c80021e00040d82400081200181800600c0000,
    0x2421211b00d042000a2440191e831812200c0900e018112401a4801f824801c1820610f0010360184128258,
    0x1e127019007a4e00050ca3040380d92a807c3d81e20cc1500700061a02411e40da5400482b80093080dc080,
    0xf819936813c0324982a218c2101300c626003406a3012a419a6000791080283780c906c3c800319c140302,
    0x36409825a6c01391c80e843818912c0224880c325c0660312003c22a133025013a0245a00a80c518a0693c4,
    0xe466016818508824a01e1294841b82594280631fc0f255801236224c2d00211f01860653200f412a3c1014,
    0xd442415831a7801f900e2881a80924f824901d1ec0e254818331c0501260f12c00114820943613f03101fa,
    0xde1e954427804c0823194e81232bc00d1b26180910d242230c0403900e12b00842461253e001b1b41ea481,
    0x723090dd2ac1a26080812433dc1101e61b13800d154215442104a0744b03d02ba00b1a472022824514830a,
    0x3cc1000074501a137014430603a1e54a00db2742aa54119407e0494e42183da8402b90ce34826815203c5b8,
    0xcb2647e006e2e83050392083ca19e2a960407d33810c1423d902c5a81e337c0b00cd2726d81511920714e2,
    0x2120fc6781323c919d36c0a02626c803614130349c1d02a627144019160207b2144e110a13457002a49037a,
    0xc751026143003506b2043c60fa2a556019b33436a60125413e1095a42d802949a0ac90037918e40806d328,
    0xf92c848a09c25e3696c413d3f80331cc2024990ec6682a343c17018d3327982112520261315a248c1c00aa,
    0x2013c355c01629036609a3315002516c213b2d40255a11ca1f46300a90ea55043a18b3248a005812e3a83c5,
    0x6c13141fe1c96643980e955a16c9c043908c24e4c812d3e82d20231bc7381f248925d42c1600673227880f6,
    0x24d3f28582d13120e61f166254c28016a1870545d008a3214f00f512b2c40154861ba36562009925b3f442a,
    0x24b3e496011801f1ee4684851b938854a15c31e4290527841fd4b80f328c2c25590131ac7280963634fc230,
    0x1273e28481b62c148361c0950d635042615a3f10445c03117821fb3940e566128a2b46f01691aa6100894fa,
    0x3d42be00f2897244581a961a09322ca804f914c30e5880421ed4a83920e327c7f82b254908631d0514ec220,
    0x3d21a62b172260c08534022a24711469014a3e15b01b51eb3840b80d554627a4256e004e15931b4b44ea781,
    0x27944804d60a08321c3de4e91128442bd5781b334c3826190d326c7e81564235bc0762f030d0414b2918391,
    0x754e621a4b11046803d18422bb4541a572134a3747b022926a6d003e1495ba30b4a4a201d80df2ae528545,
    0x20c3ce6481022ad5684521a333c8b83726091463dd1115ac2e01e74a20b49082763815436dc15519641004b,
    0x17819560607f33a4e57a010e2193db57402e5aa84149437e0b20cf3497e45182696da1532ecb4003d5b9073,
    0x2164e367c1363b03cd1015729d84514920a42663717e26cc1454002ea30703b1d475020a4a16702752ab444,
    0x564ae029819f36e5e86050a233950810d6ca1432dc02d49e5a91d290437d6380b127340c4426d919332c8a8,
    0x2152564d010b1355a62da57102b1c47400ae49190237b5142657e140a43487006f2e932a7900fe20967a3cb,
    0x6791332cc48e7081c236d6280a15122633fc9784326c903720649d1d166c3a02a75621749c833644160379c,
    0x2382556c613f3fa5a58601ce2d949b6340ad0ee66a90155443e17218f4098a405c5d832979a2133acc000fd,
    0x1f647048d1c16320aba985115521643264318a205a78c2054c03aa3c70fb2948102ca56173009e33536b504,
    0x42e6a86c51623f95c81cd78a20339c0ed55e6692929c443d6f81713334cc5027992533ec9682d60275a373c,
    0x6310eb28480016e5519c243b5d408e3258a10594ca4f493012f3a93ea8501be2c973a48b624ba009d35825f,
    0x5d23234bca384f27890f72c655d01729172c46036762209b234a883f65016c385c2d53165901cb1f566639a,
    0x16d1ae72a9c161408d4fe23224f4c996411c6983e985a2d346ccc01bd7391f338c54e7c828242d6e8056161,
    0x4f196211a84c2c558046a4871bb3548d038a6217f015e3f542b5c42f83157861ff4ba66592028e39955b6f4,
    0xa844fd7b82313f358c0465c28593134aca283960e76637fc2b653054d2816f216bb580555d161208b2243e6,
    0x4694aa0bc91027e3897fa54b6e4c6015d41831f0534ee7687852224b968828d84a2c345c1ad61e729097352,
    0x454b65c178391c3953d665028b2b572645a6f11ab3448c022e611a824fb69414e3e596111958a5b49f01ef,
    0x2b344c60e8880873424ed7a81162216923e357caf85b28491b738661d0ba0d73517ec5204276e215b2f4b48,
    0x8462bf57a7259e034e45961b7b422d26e7eaa816d414d5be2f230f589043a241dc7584a991a39352c27d7f9,
    0xc181156916d214b2e44a65b1a221da90c3856400b952a54727b41499044a6e104f8b021e4b54eb6843b83d5,
    0x51c26d6de7e9157412b445bd8780772f14b364c1066829193d356cae84561a77238bc3765f060d3417b222b,
    0x1d964a674ab02af52956a17c9d033e4498ba60b7a4d2021d4d83df1135ae8288452e25797480b634d90a383,
    0x7a221b3b4c081055766818439dc45549671034b3757e651a7b126b4049802ee6d1b4203f5bb75420e4a5a21,
    0xa633d8b937350c6ce9481474025ad8681d62e17524a363cbb80b56729092774466dd17a1974118ac5e04e7,
    0x49590637f63a0b37e5aa040e5196db8742ed32e8aab4179420d67e3b23cf649103ae429c8185699da4535ec,
    0xcd81d575179220b3a4566671ae229a9cc4457001795ea60733b4d4a5050a7a110f9702de57502f5ab744478,
    0x32d79e8a92174d2c0467d9381373b157370c1c67429d949362cba80a55162677e397c4366b06cd4018722eb,
    0x70a734b7036f5e962a0a323ca903fe50997a6cb8642dd59849f1d366e8e89053a263980817640d9ca4435dc,
    0xcc81c56367410af903a9c5155567d040b4358a605e5da87132b4c4a403ae791c020ff67b8142ce565ae1299,
    0x4335cc78ea082074c266d9282963a18125636fcc781757329c933750679d23a2574d196c6a05a78622db474,
    0x1738a5b6005d4ce5d979b9343ad3ee96ac018542cd73e47248f7091c3ba435c8d8629a9a5136ac1663fd979,
    0x464626731ba209f35aa8c5057c02396aa6c73fb594b105ca8611cfa3039e6350ef66b8045385559c643f6fa,
    0xcc473d9f81f74716337cc286802a995536ecc681655d63278a305ba3c4f677078d4c19323ab2958118522cb,
    0x6ea1632fcb504be5c9a3a78b92439d65855f29372e9a89c54626f98c82364cda8a50369c3ed85e9692d7592,
    0xb5c5d561689008f4cb4f596611e69a9313eb584b0046e851cc21bf73b8d438e625ba13597ca7f4c3042f6a9,
    0x58272d9e83564618d26237bcd382357f2a893f75c685d2fa317591a2c76066792239b5342856f680116f9c3,
    0x85b9f446d4aea2acc191438d7fe53254f7c9283c6441c9986e9b5a0575d376c2264bda394f368c84eac82c7,
    0xb4c5c58802f976a7874bb654bd068a92128faf045e6f51af72b8c45f8615a864ff7ba233965c2011d58e699,
    0x3468c2b596137acd282256963e796311bafc5b683084d5819f246b0be3558d191238b5246e67f1c6215f41a,
    0x84b9e445d71861f3537eea68a855227b99882f658db4a0475c375c4ad91ea293976527fdab82b75316f388c,
    0xa261de75a9f14ab644bc00bd52e91127f7fb99444e6e5c6141988a8b4cf04ef7697aa2233bcc1057e689afa,
    0x6e387c2f58b2b494b768691d3ba3d7651aec8207279e245b5f43457b68c122fa83c1c6956d695014f58b5b5,
    0x44d8be5f260f889343d244dca587a9c1a11769382c2e657daf95b374c90eb883876420bb7edaa8416521992,
    0x57b714c9074a9e134fbb051e7b526f7eb9846b86d5b465bf87a2f3a25ce01dd64e75991bab452d56eaea9d4,
    0x2e57564a7a231dbbbc6768f090d641ab252b17e4159919d244b5e47a68b1d2221f4dac0c6859403b982a847,
    0x4138aeb28b455e2879a483b664dc0a10768381c56d9deae94577128bdb783775f17b394c406982c196d386c,
    0x704c8017d5ee9d133f8bba5450e7a5d214d994a9745af82986a2e347ccd063e749bba0b790baa451d7d86df,
    0x5777469dd47a497711bac8e07e7aa251b6b44058769812efb43cdc755796a1020f64b675ae629e81aab156b,
    0x94940359cb18869cda1d77538ec3a663dbb967380c9cec4844770217b8adb684d65e1a527a393c3b5972c09,
    0xaa140fc705de87532f8aba44778795c0667f93a3b3ae529d70e8199dbb745ed62ebaa0a7a9450d97e6b26cf,
    0xae329bc7c7369b09cd701b725eb23e4d5a51a9250b6a48669712df59accc745a004798ea90763b7d4d5080a,
    0xc056a2939b0847670dcca1c77438dc62da9eba95177d297dc384376b1873a0c4c6a42cd979392c3a5816567,
    0xd4023d6aea913ff97bb145ce865599a0aa3466f8e992a3a353c6fe809c7a1779cbb645dd89879f4d396ebe8,
    0x806a9d53a5577d1c6c9a08a7b6205f5db7744c5936a413afc03815856ad02cf70b735ba635e8dab7162b7c4,
    0xa094c365cbd89292978139ac4666fdc797338cca8ed085077c223b96dc285966a1b128639fc475a32cc9637,
    0xb614cfd3069e9353ef96bb04838855cc673f9fa473ba535d7ce8d9a9bc346ad6eec6a167b545cda3e77278f,
    0x8d6627ba335bd3c7f6a70a8d7c1c326ab2fe595b11b525cb764926a3139f65a805ac05399aa9c76fb8948ca,
    0x85f593a2eca8cc57629f9bc85367cd28780399c6edb5ec695d7892a3dcf84f7771933acc586b028539ec465,
    0x41e99ac316eb8842fd76eb514bfa3bbd468e925659acaaf472f9a99ea4635fc7be8c9d3a237a8bc2469d958,
    0x923abc535af26f78c6b5d5fa617891d2ca60967c2211f69b8345859f6b0146fcc38d5916b9038f7cb7f5c66,
    0xd2a227c1468dafe83284fac958371cc989e93578d3a6c5267bdd397f398cb4e5c78822fba2dce8656761bd2,
    0x71a8c5b805f9a6aa877bb95498ac2158f75e9f54afa2bbc48f89157ffaba533c6541d88e999b5bcf476d7ae,
    0x5b78319f3b8c646bc20bf913aac5259966e7c6341b8b6b30b4d881cf276b3be655bd1c1268b8249e6af145f,
    0xa69aaa5236bc87e9892f7b4bce475da1891f653aeed68822ab9c885f688d3478c3a5c7adc1ed29697952afd,
    0x8f4645ab6bc152f9959d6c5044f88b8b5d264dea5acf17ab9443bd82ec1157fafbc9474e9e5719b8abb47ef,
    0x993b2c5e687d8b3a4cc0e6879423bbaed716821c929e3b7c5f5bb27b7986c1d6ba6d7951b20a27ce21df75b,
    0x81eab556faebc849b89d58bfb7a5f3d254dd94ea59c1b82d86e2e7cd474dbbe8f290fb896437dcd58aa9417,
    0xa567a7d234db976bf0c0d94182b47e715c91cd274b8e4aa6bb151f7da985c406b9b2ab4787ba14a4ace164f,
    0xc0b81dad89df713bae8e2b79d486b694d407983b1c86dcde757a12bbd6778f1ab3c4c706c8217f9d3b6c5e5,
    0xa55a96d1050f94b97559eb1a86ba0447d8eecd163fbbbd5480eaa57d9c4ac748afb29b6a5e377c93ea493b7,
    0x973b0ccce747a0247bbad7d68e1d52aa3c3c6b5c72877a46cdd77a797a11be0ae729f81b9b4705b76c815ef,
    0xb7562fbabd44a78a9597fc3a6b359da0eb19cdb8ed92e3a780dc7e9b29cfc4970389cb694d7a53bec6a693d,
    0xc2c6a5b1686759ba36cb0ccda018eb53e7d5d5180b9a4b66c715df89aa45d00779beac0793bad4b0a70f8de,
    0x83c9feb09477ccb8ddb98a9f7d3c6e9a2c39776a0d4c7a43bdc92d817ad2c7d7379b1b73d0c7c6d4223fa93,
    0x35f8dba747c5c36d416afb15b565cfa0ba3565ebda92bac453d9ae6ffc7b8ceb65899d0ad3496fbe9c2a6a3,
    0xa8fd097c395cc29597b13cac7669fda33bcc807ac253bc6d8969a1b63cfc775d32937b0683a857ad1ca0ba7,
    0xd3169f95ab05839caacc79fbb94bca7cf99ec356efc6bb38b55a3fcfa77365dacebd99ad9ee4678cdd3ea72,
    0x836acd587b03c9c9ed8d7b92d3d7f7a71c338862ffb53cec765bd692765baf6d70ac19ab5fe8958cba64c26,
    0x68facbaf571ec9a9ebb845fda6e7bfd3b98ec25959a2fca9cea7638fcabebc953799dc58b5f893d2ea62cf9,
    0xbd3d6c826abdaf3c8c8c7b825fbd2d956a61c238359f7bc68fa917b91d60c6741f99bb34885cf676fbd5c16,
    0xa1abc58f9d6aabbc54c8a88fa5ecf57afd2bbf8c15aff83371db8ec99a6daae52798db32b4f883a1cce9657,
    0x953b228f6b8d647bc3d5caad997c528b7b31cf39463bfc13825c969e771bbb6b81a6b6be95598bb24ce675f,
    0xa5bbf494582fc95cd674fb8bbb57ded5aaabc446bdb2e87fa4ece5a19aefd698239bcb7ec895f7a5dd18c1f,
    0xd59b2db6e5e7a4dbf2c0f943adc717c938e6b7dbb3d4c987c426bba16b21ce38f5ab7c869ba9d7c51d274df,
    0x47fcd38e5d56aa77dbc76c41b2b77ea15a4bbe481fadac859b9b7bd14d4a94fb1e86fcb8cd5bbf8f37ddc4e,
    0xc7589eb6bd0477dbee93fb0ead9baf8e3a7cc3ed496b7b1dcdfa13be29b6c4d707c83b6da57d12977bf1a06,
    0xb0dcb2ccfa03b9c7d7d539a6c3dc73a47d0277bad6be19b5b77d46a7aa97d1159fb1bcb4a058efd5580fc4b,
    0xcb1ac653f9a5b6789bd36d01beb83ead5b0bca48dfb9ad45a79c3ba0fbde92fd78c7f9b389dd0ebedc2e6a7,
    0xbdbd74ac59af8cfd0bd3595ec2b83dcae9ffbceb99c6f9a3b3ccfe777bddad3ca2a76d0d7c7d43c2db17a37,
    0xc5ab39cfbacfc9e9efd3fa7395dcadcee767bcdd72ac3c5c897a66cfdd33b0783bb96ca1a75c37b3ab5765f,
    0x8fdd6eabfc8ec59d2fa63bfc837c9db93d62b36887cedbd7af7d71b865ffa65c2795bcab8feb95bcbd6499f,
    0xd1abf9b8fd5eaafb33a1dd6d827c8db83d1c957b26bc78fbc56d61b35cf7bfac1771fc9bb85a6f98fa1eceb,
    0x7dfd5bc45b2fa4fade9bdb7fd4ed19b23cbc8f7d5dc53bf6947c97bb7c466bfb25ce7a1bd6b9bec55c8ba5f,
    0xd13cb6a07d57c77d0677fbe5adba7ed15d4bb1fcb9c4fb6fbf3add8e7d4dc43a17be6c879bbd16bf5cbacd7,
    0xd3783fca5b9bb3ebdfd79d0fc2fcb3b9d9a7d03ad7ca6d47a7bcb5d7a89fd05befb0fb9ea7dc3fbe3d7c9b7,
    0xc8fd1ebfdd63b37b878ffd65c5bbfec9fcefd73c5da67b97d66b3bd7595fcafbcfc5eb3dcffca3a77d76ac7,
    0xc5fd77b3fca7d7bb9fd7dcb7d07a7fd7ebe7d17cbbadfd4fcbdbf7c479bfd1bcbed5fd1db27c57bfba1fd6f,
    0xd7fcbfd1fbffd67]
private def a2421 : List ℕ :=
  certificateIndexedDivisors (exponentFactors boxPrimes ![17, 1, 3, 2, 1, 1, 1])
    4096 29 3456 d2421
private def n2421 : MainTree := .leaf (mainGapLeafOfDivisors ![17, 1, 3, 2, 1, 1, 1] a2421)
private def n2419 : MainTree := .split 6 0 n2420 n2421
private def n2415 : MainTree := .split 5 0 n2416 n2419
private def n2407 : MainTree := .split 4 0 n2408 n2415
private def n2395 : MainTree := .split 1 0 n2396 n2407
private def n2373 : MainTree := .split 3 0 n2374 n2395
private def n2201 : MainTree := .split 0 8 n2202 n2373

private theorem c2204 : C ![4, 0, 2, 0, 0, 0, 0] ![8, 0, 3, 0, 1, 1, 1] n2204 := by
  decide +kernel

private theorem c2220 : C ![4, 1, 2, 0, 0, 0, 0] ![8, 1, 3, 0, 0, 1, 1] n2220 := by
  decide +kernel

private theorem c2248 : C ![4, 1, 2, 0, 1, 0, 0] ![8, 1, 3, 0, 1, 0, 1] n2248 := by
  decide +kernel

private theorem c2259 : C ![4, 1, 2, 0, 1, 1, 0] ![8, 1, 3, 0, 1, 1, 1] n2259 := by
  decide +kernel

private theorem c2247 : C ![4, 1, 2, 0, 1, 0, 0] ![8, 1, 3, 0, 1, 1, 1] n2247 := by
  exact checkExponentBoxTree_join c2248 c2259 (by decide +kernel)

private theorem c2219 : C ![4, 1, 2, 0, 0, 0, 0] ![8, 1, 3, 0, 1, 1, 1] n2219 := by
  exact checkExponentBoxTree_join c2220 c2247 (by decide +kernel)

private theorem c2203 : C ![4, 0, 2, 0, 0, 0, 0] ![8, 1, 3, 0, 1, 1, 1] n2203 := by
  exact checkExponentBoxTree_join c2204 c2219 (by decide +kernel)

private theorem c2266 : C ![4, 0, 2, 1, 0, 0, 0] ![8, 0, 3, 2, 0, 1, 1] n2266 := by
  decide +kernel

private theorem c2282 : C ![4, 0, 2, 1, 1, 0, 0] ![8, 0, 3, 2, 1, 0, 1] n2282 := by
  decide +kernel

private theorem c2289 : C ![4, 0, 2, 1, 1, 1, 0] ![8, 0, 3, 2, 1, 1, 1] n2289 := by
  decide +kernel

private theorem c2281 : C ![4, 0, 2, 1, 1, 0, 0] ![8, 0, 3, 2, 1, 1, 1] n2281 := by
  exact checkExponentBoxTree_join c2282 c2289 (by decide +kernel)

private theorem c2265 : C ![4, 0, 2, 1, 0, 0, 0] ![8, 0, 3, 2, 1, 1, 1] n2265 := by
  exact checkExponentBoxTree_join c2266 c2281 (by decide +kernel)

private theorem c2297 : C ![4, 1, 2, 1, 0, 0, 0] ![8, 1, 3, 2, 0, 0, 0] n2297 := by
  decide +kernel

private theorem c2312 : C ![4, 1, 2, 1, 0, 0, 1] ![8, 1, 3, 2, 0, 0, 1] n2312 := by
  decide +kernel

private theorem c2296 : C ![4, 1, 2, 1, 0, 0, 0] ![8, 1, 3, 2, 0, 0, 1] n2296 := by
  exact checkExponentBoxTree_join c2297 c2312 (by decide +kernel)

private theorem c2324 : C ![4, 1, 2, 1, 0, 1, 0] ![8, 1, 3, 2, 0, 1, 0] n2324 := by
  decide +kernel

private theorem c2336 : C ![4, 1, 2, 1, 0, 1, 1] ![5, 1, 3, 2, 0, 1, 1] n2336 := by
  decide +kernel

private theorem c2339 : C ![6, 1, 2, 1, 0, 1, 1] ![8, 1, 3, 2, 0, 1, 1] n2339 := by
  decide +kernel

private theorem c2335 : C ![4, 1, 2, 1, 0, 1, 1] ![8, 1, 3, 2, 0, 1, 1] n2335 := by
  exact checkExponentBoxTree_join c2336 c2339 (by decide +kernel)

private theorem c2323 : C ![4, 1, 2, 1, 0, 1, 0] ![8, 1, 3, 2, 0, 1, 1] n2323 := by
  exact checkExponentBoxTree_join c2324 c2335 (by decide +kernel)

private theorem c2295 : C ![4, 1, 2, 1, 0, 0, 0] ![8, 1, 3, 2, 0, 1, 1] n2295 := by
  exact checkExponentBoxTree_join c2296 c2323 (by decide +kernel)

private theorem c2342 : C ![4, 1, 2, 1, 1, 0, 0] ![8, 1, 3, 2, 1, 0, 0] n2342 := by
  decide +kernel

private theorem c2356 : C ![4, 1, 2, 1, 1, 0, 1] ![5, 1, 3, 2, 1, 0, 1] n2356 := by
  decide +kernel

private theorem c2359 : C ![6, 1, 2, 1, 1, 0, 1] ![8, 1, 3, 2, 1, 0, 1] n2359 := by
  decide +kernel

private theorem c2355 : C ![4, 1, 2, 1, 1, 0, 1] ![8, 1, 3, 2, 1, 0, 1] n2355 := by
  exact checkExponentBoxTree_join c2356 c2359 (by decide +kernel)

private theorem c2341 : C ![4, 1, 2, 1, 1, 0, 0] ![8, 1, 3, 2, 1, 0, 1] n2341 := by
  exact checkExponentBoxTree_join c2342 c2355 (by decide +kernel)

private theorem c2362 : C ![4, 1, 2, 1, 1, 1, 0] ![5, 1, 3, 2, 1, 1, 0] n2362 := by
  decide +kernel

private theorem c2367 : C ![6, 1, 2, 1, 1, 1, 0] ![8, 1, 3, 2, 1, 1, 0] n2367 := by
  decide +kernel

private theorem c2361 : C ![4, 1, 2, 1, 1, 1, 0] ![8, 1, 3, 2, 1, 1, 0] n2361 := by
  exact checkExponentBoxTree_join c2362 c2367 (by decide +kernel)

private theorem c2371 : C ![4, 1, 2, 1, 1, 1, 1] ![5, 1, 3, 2, 1, 1, 1] n2371 := by
  decide +kernel

private theorem c2372 : C ![6, 1, 2, 1, 1, 1, 1] ![8, 1, 3, 2, 1, 1, 1] n2372 := by
  decide +kernel

private theorem c2370 : C ![4, 1, 2, 1, 1, 1, 1] ![8, 1, 3, 2, 1, 1, 1] n2370 := by
  exact checkExponentBoxTree_join c2371 c2372 (by decide +kernel)

private theorem c2360 : C ![4, 1, 2, 1, 1, 1, 0] ![8, 1, 3, 2, 1, 1, 1] n2360 := by
  exact checkExponentBoxTree_join c2361 c2370 (by decide +kernel)

private theorem c2340 : C ![4, 1, 2, 1, 1, 0, 0] ![8, 1, 3, 2, 1, 1, 1] n2340 := by
  exact checkExponentBoxTree_join c2341 c2360 (by decide +kernel)

private theorem c2294 : C ![4, 1, 2, 1, 0, 0, 0] ![8, 1, 3, 2, 1, 1, 1] n2294 := by
  exact checkExponentBoxTree_join c2295 c2340 (by decide +kernel)

private theorem c2264 : C ![4, 0, 2, 1, 0, 0, 0] ![8, 1, 3, 2, 1, 1, 1] n2264 := by
  exact checkExponentBoxTree_join c2265 c2294 (by decide +kernel)

private theorem c2202 : C ![4, 0, 2, 0, 0, 0, 0] ![8, 1, 3, 2, 1, 1, 1] n2202 := by
  exact checkExponentBoxTree_join c2203 c2264 (by decide +kernel)

private theorem c2375 : C ![9, 0, 2, 0, 0, 0, 0] ![17, 0, 3, 0, 1, 1, 1] n2375 := by
  decide +kernel

private theorem c2383 : C ![9, 1, 2, 0, 0, 0, 0] ![17, 1, 3, 0, 0, 1, 1] n2383 := by
  decide +kernel

private theorem c2391 : C ![9, 1, 2, 0, 1, 0, 0] ![17, 1, 3, 0, 1, 0, 1] n2391 := by
  decide +kernel

private theorem c2394 : C ![9, 1, 2, 0, 1, 1, 0] ![17, 1, 3, 0, 1, 1, 1] n2394 := by
  decide +kernel

private theorem c2390 : C ![9, 1, 2, 0, 1, 0, 0] ![17, 1, 3, 0, 1, 1, 1] n2390 := by
  exact checkExponentBoxTree_join c2391 c2394 (by decide +kernel)

private theorem c2382 : C ![9, 1, 2, 0, 0, 0, 0] ![17, 1, 3, 0, 1, 1, 1] n2382 := by
  exact checkExponentBoxTree_join c2383 c2390 (by decide +kernel)

private theorem c2374 : C ![9, 0, 2, 0, 0, 0, 0] ![17, 1, 3, 0, 1, 1, 1] n2374 := by
  exact checkExponentBoxTree_join c2375 c2382 (by decide +kernel)

private theorem c2398 : C ![9, 0, 2, 1, 0, 0, 0] ![17, 0, 3, 2, 0, 0, 1] n2398 := by
  decide +kernel

private theorem c2401 : C ![9, 0, 2, 1, 0, 1, 0] ![17, 0, 3, 2, 0, 1, 1] n2401 := by
  decide +kernel

private theorem c2397 : C ![9, 0, 2, 1, 0, 0, 0] ![17, 0, 3, 2, 0, 1, 1] n2397 := by
  exact checkExponentBoxTree_join c2398 c2401 (by decide +kernel)

private theorem c2403 : C ![9, 0, 2, 1, 1, 0, 0] ![17, 0, 3, 2, 1, 0, 1] n2403 := by
  decide +kernel

private theorem c2406 : C ![9, 0, 2, 1, 1, 1, 0] ![17, 0, 3, 2, 1, 1, 1] n2406 := by
  decide +kernel

private theorem c2402 : C ![9, 0, 2, 1, 1, 0, 0] ![17, 0, 3, 2, 1, 1, 1] n2402 := by
  exact checkExponentBoxTree_join c2403 c2406 (by decide +kernel)

private theorem c2396 : C ![9, 0, 2, 1, 0, 0, 0] ![17, 0, 3, 2, 1, 1, 1] n2396 := by
  exact checkExponentBoxTree_join c2397 c2402 (by decide +kernel)

private theorem c2409 : C ![9, 1, 2, 1, 0, 0, 0] ![17, 1, 3, 2, 0, 0, 1] n2409 := by
  decide +kernel

private theorem c2413 : C ![9, 1, 2, 1, 0, 1, 0] ![17, 1, 3, 2, 0, 1, 0] n2413 := by
  decide +kernel

private theorem c2414 : C ![9, 1, 2, 1, 0, 1, 1] ![17, 1, 3, 2, 0, 1, 1] n2414 := by
  decide +kernel

private theorem c2412 : C ![9, 1, 2, 1, 0, 1, 0] ![17, 1, 3, 2, 0, 1, 1] n2412 := by
  exact checkExponentBoxTree_join c2413 c2414 (by decide +kernel)

private theorem c2408 : C ![9, 1, 2, 1, 0, 0, 0] ![17, 1, 3, 2, 0, 1, 1] n2408 := by
  exact checkExponentBoxTree_join c2409 c2412 (by decide +kernel)

private theorem c2417 : C ![9, 1, 2, 1, 1, 0, 0] ![17, 1, 3, 2, 1, 0, 0] n2417 := by
  decide +kernel

private theorem c2418 : C ![9, 1, 2, 1, 1, 0, 1] ![17, 1, 3, 2, 1, 0, 1] n2418 := by
  decide +kernel

private theorem c2416 : C ![9, 1, 2, 1, 1, 0, 0] ![17, 1, 3, 2, 1, 0, 1] n2416 := by
  exact checkExponentBoxTree_join c2417 c2418 (by decide +kernel)

private theorem c2420 : C ![9, 1, 2, 1, 1, 1, 0] ![17, 1, 3, 2, 1, 1, 0] n2420 := by
  decide +kernel

private theorem c2421 : C ![9, 1, 2, 1, 1, 1, 1] ![17, 1, 3, 2, 1, 1, 1] n2421 := by
  decide +kernel

private theorem c2419 : C ![9, 1, 2, 1, 1, 1, 0] ![17, 1, 3, 2, 1, 1, 1] n2419 := by
  exact checkExponentBoxTree_join c2420 c2421 (by decide +kernel)

private theorem c2415 : C ![9, 1, 2, 1, 1, 0, 0] ![17, 1, 3, 2, 1, 1, 1] n2415 := by
  exact checkExponentBoxTree_join c2416 c2419 (by decide +kernel)

private theorem c2407 : C ![9, 1, 2, 1, 0, 0, 0] ![17, 1, 3, 2, 1, 1, 1] n2407 := by
  exact checkExponentBoxTree_join c2408 c2415 (by decide +kernel)

private theorem c2395 : C ![9, 0, 2, 1, 0, 0, 0] ![17, 1, 3, 2, 1, 1, 1] n2395 := by
  exact checkExponentBoxTree_join c2396 c2407 (by decide +kernel)

private theorem c2373 : C ![9, 0, 2, 0, 0, 0, 0] ![17, 1, 3, 2, 1, 1, 1] n2373 := by
  exact checkExponentBoxTree_join c2374 c2395 (by decide +kernel)

private theorem c2201 : C ![4, 0, 2, 0, 0, 0, 0] ![17, 1, 3, 2, 1, 1, 1] n2201 := by
  exact checkExponentBoxTree_join c2202 c2373 (by decide +kernel)

/-- The complete binary certificate at this subtree root. -/
def certificate : MainTree := n2201

theorem chunk_checked :
    checkExponentBoxTree mainScale boxPrimes lo hi certificate = true := c2201

#print axioms chunk_checked

end D5.S3.Arith.ErdosNicolas.Data.Main05
