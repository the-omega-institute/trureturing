# Rational batch declaration shapes

Current assessment of unchanged mathematical HEAD: `a20d0c3328a3c6f085105e6aeeab091449af819e`

Historical report input HEAD: `9e1af55f012e7a4337886fce2cafdedf23f7e9a2`

Raw Lean report: `sha256:7884fdbd82489e2c2f3531c4a0687e03b255f4cf89d28787c05a8970fcfc6fc2`

All 90 included declarations are listed: **49 bind-only theorems, 1 content refutation, 22 definitions, 1 structure and 17 generated companions**. The 12 excluded report helpers are identified in [declaration-audit.json](declaration-audit.json). Twenty-two former content rows are corrected. Definitions and generated companions are separate from theorem proof shape.

The **Captured internal D5** column counts historical value/type constants within the row's module after local auxiliary expansion. The **Captured external D5** column counts observed direct outside-module D5 constants from value/type; it omits prerequisites reached only through local helpers. Both columns omit Mathlib and Lean-core constants. The exact historical producer implementation is `ASSUMED-UNVERIFIED`; its raw source label does not establish uniform expansion. Capture covers **87/90** rows: `Fraction._sizeOf_inst`, `Fraction._sizeOf_1` and `Fraction.mk._flat_ctor` remain `missing`, with null audit arrays, not zero dependencies. These counts do not certify reduced proof liveness or admission. Exact semantic owners, source clauses and directed uses are recorded separately in the audit.

The six rows affected by external helper omissions are `RichRational.integerEmbedding`, `RichRational.add`, `RichRational.div`, `RichRational.mul`, `RationalQuotient.rationalSection` and `IntegerExactDivision.half`. Concrete examples are the omitted guard owners `GeneratedProduct.q_product` and `ComplementFibers.balancedSection_rightInverse`; [report.md](report.md) gives their existing declaration IDs and helper paths. The authored owner/use accounting supplies these dependencies separately, including `mul → add → q_product`; the historical arrays and counts remain unchanged.

| Module | Declaration | Kind | Proof shape | Captured internal D5 | Captured external D5 | Statement ID |
|---|---|---|---|---:|---:|---|
| `RichRational` | `add_readout` | `theorem` | `bind-only` | 6 | 10 | `sha256:a144430dfa4126b6400a689d9fa83b6dd22b699039fb2ef674bc8213ee5084d3` |
| `RichRational` | `div_readout` | `theorem` | `bind-only` | 6 | 8 | `sha256:d2f7755eb749cad22c81aeb406949590c3c5c84361843f9a805283c6ae6d3b88` |
| `RichRational` | `inv_readout` | `theorem` | `bind-only` | 6 | 1 | `sha256:d174ed21eac272bcbe6893ae78dc52120e496dd577702d6b293a3f2082145d31` |
| `RichRational` | `mul_readout` | `theorem` | `bind-only` | 5 | 7 | `sha256:72ef1821b4e62ddf95a2a852b2ee7488731c5493e869274460d406ce984f4290` |
| `RichRational` | `neg_readout` | `theorem` | `bind-only` | 5 | 8 | `sha256:2622604afe65ea4fc08a750b6ae6d26d679f2975336f38d71a9ae6a3638d7d2a` |
| `RichRational` | `InverseGuard` | `def` | `definition` | 2 | 1 | `sha256:ff444e383bd056e866404daa1c89cb08a9caaed838a685a14e193061c3746923` |
| `RichRational` | `kernelSetoid` | `def` | `definition` | 2 | 0 | `sha256:5af59fef6179cf74d2cdce4829388d3e5e7a0ee26f1819aa66000a8e7033f6b7` |
| `RichRational` | `DivisionGuard` | `def` | `definition` | 2 | 1 | `sha256:cae58b51a8bad1f8ff7f73bae49eb80084098d59965353ab4642f5a7df58d280` |
| `RichRational` | `CrossEquivalent` | `def` | `definition` | 3 | 1 | `sha256:655c407ece3941ca875c263fe3a6fee9cafdcba75e949f0aa5e3b3e69028798b` |
| `RichRational` | `integerEmbedding` | `def` | `definition` | 2 | 2 | `sha256:568d01f7a4fc4e3202bd415f340743f3955704e637ce9f34180cf4ecb096d350` |
| `RichRational` | `kernel_iff_cross` | `theorem` | `bind-only` | 5 | 0 | `sha256:a5b6f44d66eab3370edf86c482eb6992f95f1e48cda05c71074d9d5e3c89cee7` |
| `RichRational` | `cross_equivalence` | `theorem` | `bind-only` | 4 | 0 | `sha256:445d11f750157d062927a79568f60e35a5afdda4002b25f4dbd7cebdb5231d15` |
| `RichRational` | `cross_iff_readout` | `theorem` | `bind-only` | 6 | 1 | `sha256:b1072db88d5feccab4ada45bbdad302709b42298706ee54a5df88fbebb4a1503` |
| `RichRational` | `inverse_guard_iff` | `theorem` | `bind-only` | 6 | 1 | `sha256:ddc1460afa5a75f8cddded1ac091cc62deaae2970ce7674b6fb6ff473e947f9f` |
| `RichRational` | `division_guard_iff` | `theorem` | `bind-only` | 4 | 0 | `sha256:eaa92be8fdae6e0b9032283d09d455efec19093f20d702806eb01135c5644a9d` |
| `RichRational` | `inverse_guard_congr` | `theorem` | `bind-only` | 6 | 0 | `sha256:7abcc16f70b3e0ad40fa1df16ef5322df4210f2ed3b804568b322021a3ecba97` |
| `RichRational` | `division_guard_congr` | `theorem` | `bind-only` | 4 | 0 | `sha256:575a2e7161869fb21cbf4ee0ba0270e87015fe47c2e2d70de609e003657d62bd` |
| `RichRational` | `denominator_cast_ne_zero` | `theorem` | `bind-only` | 3 | 1 | `sha256:4a33aa5569e4e128c15e540c410259aae29428a2cc9776e7703f617e8626b07e` |
| `RichRational` | `integerEmbedding_readout` | `theorem` | `bind-only` | 2 | 4 | `sha256:ab7b7d131a9f2742a336560fdc51851e759a83472d3b274ee6a041186f6ea43e` |
| `RichRational` | `integerEmbedding_retains` | `theorem` | `bind-only` | 2 | 1 | `sha256:359537299b5fd46cb0330242a9d50871c03c4d30f888e4704ef26266b2bfe015` |
| `RichRational` | `add` | `def` | `definition` | 5 | 2 | `sha256:87722315fa270eb93317f7b4531f4334fffaf750256a9e29990859234691b739` |
| `RichRational` | `div` | `def` | `definition` | 6 | 1 | `sha256:7d3b42390d62a126234df6bb8f6e30493e659dfb662b6ea10b1acf1a61dec579` |
| `RichRational` | `inv` | `def` | `definition` | 5 | 0 | `sha256:086e7f50b9d00253f1a8f3958f8ac652139b245968360310e33beac054c0c490` |
| `RichRational` | `mul` | `def` | `definition` | 6 | 1 | `sha256:be22f452e70266674e1bba7d8811fa51d44b8f58e589ba0bcf4341b1cda1ab67` |
| `RichRational` | `neg` | `def` | `definition` | 5 | 1 | `sha256:825deadf8c22651a53de83c39c8907b8f4661bca4b2cac19b2d1fbf0c1d94101` |
| `RichRational` | `readout` | `def` | `definition` | 3 | 1 | `sha256:3ff788f4190d660e90a94c2d5d194588de53870ce6a3ea71d67ef198ac199f47` |
| `RichRational` | `Fraction` | `inductive` | `structure` | 0 | 0 | `sha256:03da01de8e834ef8a418a44b4a754df0db1a438fdc830f2bbbc2441c0cd55d82` |
| `RichRational` | `add_congr` | `theorem` | `bind-only` | 6 | 0 | `sha256:610faef1318d6963e415290e1f80e5603b86ad891f1a149e91697095d859e08c` |
| `RichRational` | `div_congr` | `theorem` | `bind-only` | 7 | 0 | `sha256:a7a30aabbd467cdc081c72627d4719930becd4f76517408ab84e9d5f4f11c8aa` |
| `RichRational` | `inv_congr` | `theorem` | `bind-only` | 7 | 0 | `sha256:fec0b2f55a2f83e8f9dc6271498b4581039de986dda13261cab792645aaeff70` |
| `RichRational` | `mul_congr` | `theorem` | `bind-only` | 6 | 0 | `sha256:4fe164b3f187e5f4d9e62538ee66000a3c1e544e6c00a4d3d134e0356b90cefb` |
| `RichRational` | `neg_congr` | `theorem` | `bind-only` | 6 | 0 | `sha256:e728f6f3c5340964cc7497feaa860aafdb778bfe38fe12769a8312a30b8cc793` |
| `RichRational` | `Fraction.denominator` | `def` | `generated` | 1 | 1 | `sha256:2dc165e989b0024bd05ad7c421f7b4d40ef0e5e1dc81c93a9e94e06de157ef9e` |
| `RichRational` | `Fraction.noConfusion` | `def` | `generated` | 3 | 2 | `sha256:7b7ec5a80ec27c841dfbc7886a8b35878bd326b774350f6efb77596027fe25aa` |
| `RichRational` | `Fraction._sizeOf_inst` | `def` | `generated` | missing | missing | `sha256:a6ba3d1bdd2902ed2c3c39a292611dfc2ecd2daa3589b9ba2b9a2c4b6557360f` |
| `RichRational` | `Fraction.noConfusionType` | `def` | `generated` | 2 | 2 | `sha256:dec0715b2aebcf4997f90cbe2f45dad584860b138c01086cbc500063e9129a91` |
| `RichRational` | `Fraction.denominator_ne_zero` | `theorem` | `generated` | 2 | 1 | `sha256:99e184302166e97a8e035648a50c796d866bff3719806afb1b778d4a6a378442` |
| `RichRational` | `Fraction.mk` | `constructor` | `generated` | 1 | 2 | `sha256:4582468246d3ef248b85dc70d5a172d1db82d0f53e206459181aac2333e267aa` |
| `RichRational` | `Fraction.rec` | `recursor` | `generated` | 2 | 2 | `sha256:9112fb19a408634be14409288cd289ea86fcb16f1a141a44cdac81241d621c35` |
| `RichRational` | `Fraction.recOn` | `def` | `generated` | 3 | 2 | `sha256:b865849580c79b665d832febb78add8d8c8a0213813fe4e02362fd2b42c073ed` |
| `RichRational` | `Fraction.casesOn` | `def` | `generated` | 3 | 2 | `sha256:66c3eaa67f75a6e130e81320d7651cb190403094408c2c4b8e49365859d3eb46` |
| `RichRational` | `Fraction.ctorIdx` | `def` | `generated` | 1 | 0 | `sha256:1d574fe981d12f440ca82481fa5b096394fbaeb7ce97a3772c8caaaf86e60cbd` |
| `RichRational` | `Fraction._sizeOf_1` | `def` | `generated` | missing | missing | `sha256:1bc845d5b444f2faeda6a8bf61cd44075b7b37558877626ab4afb4877d6afc50` |
| `RichRational` | `Fraction.numerator` | `def` | `generated` | 1 | 1 | `sha256:863058d1069d36ba26956bfaaf3dbf50571e8772d78fe6f4b2b1606ecc185d71` |
| `RichRational` | `Fraction.mk._flat_ctor` | `def` | `generated` | missing | missing | `sha256:d9490eb7a82747135e7178de7f93c7933005969ff4f5a3327af57d0d5b0ea2db` |
| `RichRational` | `Fraction.mk.noConfusion` | `def` | `generated` | 3 | 2 | `sha256:1c7e83c480f748a1f235c7bfc860aa9c95cd247e0fc2f58e8d2f6a5b1c2d7240` |
| `RichRational` | `Fraction.mk.sizeOf_spec` | `theorem` | `generated` | 3 | 2 | `sha256:cd68110a12ccc870811fcaa5eae80801ab568890a93b4fda2f1176420d6b48fa` |
| `RichRational` | `Fraction.mk.inj` | `theorem` | `generated` | 3 | 2 | `sha256:cdafd0143f2a071f3666b0c1cbe49f57ea89d9b4049b1e2c421f8527b019085c` |
| `RichRational` | `Fraction.mk.injEq` | `theorem` | `generated` | 3 | 2 | `sha256:c508293a830ea85e494d82cd6b8331f30792710f37686c4039ba48b5711254e5` |
| `RationalQuotient` | `class_eq_iff` | `theorem` | `bind-only` | 3 | 4 | `sha256:d2768ffb40a6ee326b0ce9544d92ba2f10791bc2e640ae96fc98a4065d1149a1` |
| `RationalQuotient` | `quotientField` | `def` | `definition` | 2 | 0 | `sha256:6dfd179f9acaff39788a98f87d1fd2d01a48f37d01ea71bc24c0857f86216480` |
| `RationalQuotient` | `rationalSection` | `def` | `definition` | 0 | 3 | `sha256:688afe77446cf5ee48e53b4a07a69e0d44fea85948d9b6296071b8ed65cbe48f` |
| `RationalQuotient` | `quotient_readout` | `theorem` | `bind-only` | 3 | 2 | `sha256:44f1b42ca3fb463224a17475873c04643685744484282032e653614cb9269a7d` |
| `RationalQuotient` | `rationalSection_zero` | `theorem` | `bind-only` | 1 | 3 | `sha256:d9b0622e4967de1c548a13ad936d7dd81bf1ee4cc9268e8dddad94574bc3cc8f` |
| `RationalQuotient` | `rational_field_equiv` | `def` | `definition` | 3 | 0 | `sha256:59b3c9e1d2b7a1ebeac8c9ff700bc17e2b684fdc6be569c85f61700ef6bd2775` |
| `RationalQuotient` | `quotient_inverse_domain` | `theorem` | `bind-only` | 4 | 4 | `sha256:6390ef09b6d704cc0ff609e1acce95fd323cbaef0e0efe3550a66c22d4cad333` |
| `RationalQuotient` | `rationalSection_reduced` | `theorem` | `bind-only` | 1 | 5 | `sha256:e59c6210b854fbb00e478503a279d72d996707726d19488030f25afd9221d7dd` |
| `RationalQuotient` | `rational_quotient_equiv` | `def` | `definition` | 3 | 2 | `sha256:1ffa8368e9e80db99412a95999efd2a847416d4725862d276af16a906856be36` |
| `RationalQuotient` | `quotient_division_domain` | `theorem` | `bind-only` | 4 | 2 | `sha256:575fb9234f13d23c38bbf5bb11d89d2df7db8fdee5fbe2795315004a5bd4043f` |
| `RationalQuotient` | `rationalSection_injective` | `theorem` | `bind-only` | 2 | 2 | `sha256:4516a31ee2492f52f2f5c364bfb9c32fa9c6726369396b5bad36b04f422140c5` |
| `RationalQuotient` | `reduced_coordinates_unique` | `theorem` | `bind-only` | 0 | 0 | `sha256:ea02bdb957b41f85c71136c6ff952a90cc28a3f8d714c6b7a841e6c584c730be` |
| `RationalQuotient` | `rationalSection_rightInverse` | `theorem` | `bind-only` | 1 | 5 | `sha256:d4be8a7cc83899f47d03a6c795d230af3f92cd29f529c007f51c52d44cab269a` |
| `RationalQuotient` | `classOf` | `def` | `definition` | 1 | 2 | `sha256:d969658ef2e80bf7f59eda42f95068734d4e972d6c91db8defd7e8ad61308f0f` |
| `RationalQuotient` | `Rational` | `def` | `definition` | 0 | 2 | `sha256:fb474b7a103412fdb29d978dba54321886549f9b496e80197e8ab8ad68721a4e` |
| `RationalQuotient` | `class_add` | `theorem` | `bind-only` | 4 | 3 | `sha256:d3f05cf47152f256ec0b445e62a8bb439a088301101216c9386a29fbc71bb6c7` |
| `RationalQuotient` | `class_div` | `theorem` | `bind-only` | 4 | 4 | `sha256:ce068da87926c783242da34efb1ce61eed7b02b05b43629deac1d6c9333eefe5` |
| `RationalQuotient` | `class_inv` | `theorem` | `bind-only` | 4 | 4 | `sha256:be6133f3608965982bc0c2b9e38949c951eff9111513d212fc83e6bcde63fd19` |
| `RationalQuotient` | `class_mul` | `theorem` | `bind-only` | 4 | 3 | `sha256:81706e06396690127a93662fb5bb96bad9f9dc0f49ebf8eea046b091f3f584df` |
| `RationalQuotient` | `class_neg` | `theorem` | `bind-only` | 4 | 3 | `sha256:7d8fddfb176572a380f176f7e04d15d920397e9797616f23346b46682a6d0b13` |
| `IntegerExactDivision` | `ExactGuard` | `def` | `definition` | 0 | 2 | `sha256:01f5879b11b99eb9372718d03736b63edf1c6f46f07da26aac444253a864296a` |
| `IntegerExactDivision` | `exactDivide` | `def` | `definition` | 2 | 2 | `sha256:9daa826a317541c66db54668ef643c41c6fa1715485c90f901883e25127423c9` |
| `IntegerExactDivision` | `exactQuotient` | `def` | `definition` | 2 | 2 | `sha256:0266e9f6b7431600327ec6defc2d6ad1ef0e694bb6468ccb092ba0eba0222f87` |
| `IntegerExactDivision` | `exactDivide_congr` | `theorem` | `bind-only` | 5 | 3 | `sha256:db260752bd8b75775594ea20d88ab5aa8a2872033d28dc34d05c61f998f2b967` |
| `IntegerExactDivision` | `exact_guard_congr` | `theorem` | `bind-only` | 1 | 2 | `sha256:d8df0094c298e549696722cffa3e4d203b01d3169e5286a142f2b85344e104f0` |
| `IntegerExactDivision` | `exactDivide_by_one` | `theorem` | `bind-only` | 1 | 4 | `sha256:8501746d6413d9434088e025c11a2c51e1481c7a0b6fa34621e191ed5fe5db6c` |
| `IntegerExactDivision` | `exactQuotient_spec` | `theorem` | `bind-only` | 3 | 2 | `sha256:46d6022b6330db22c84f0000439c0238c46b8a8c2ad1ddec59e65895ad753e35` |
| `IntegerExactDivision` | `exactDivide_literal` | `theorem` | `bind-only` | 4 | 8 | `sha256:228cfef4c800a3d13650113c7ed15eff309117ae6e399f418c31bfed682fead4` |
| `IntegerExactDivision` | `exactDivide_readout` | `theorem` | `bind-only` | 3 | 3 | `sha256:ba18cef9f5ddad7f3e2aa70cb080fd2da9c026830c7726becd64d22d7a42ecef` |
| `IntegerExactDivision` | `exactQuotient_unique` | `theorem` | `bind-only` | 3 | 2 | `sha256:41eed45acafeb698fa88b862e989b9ce3de50143af17773b33350d814169289a` |
| `IntegerExactDivision` | `fraction_exactDivide` | `theorem` | `bind-only` | 6 | 5 | `sha256:af4393b1b9591697d0cc8d73e658e9173d6d0225d11bebfd39305adb5931be0e` |
| `IntegerExactDivision` | `quotient_exactDivide` | `theorem` | `bind-only` | 3 | 11 | `sha256:a1536abf95fe19d1b26489a92d91ecc196cfc4727f386525eddd0858302df241` |
| `IntegerExactDivision` | `fraction_eq_integer_iff` | `theorem` | `bind-only` | 0 | 7 | `sha256:30205f4505a68e724f587608343a0e5b51e09ac3ada580c5e49b2ab66af8451f` |
| `IntegerExactDivision` | `exact_guard_fraction_congr` | `theorem` | `bind-only` | 2 | 6 | `sha256:e5279f7c24b0557793294ceb0ecc343c591f88fe6e4d3fdbc2f95b9aea64df8e` |
| `IntegerExactDivision` | `division_domains_equal_claim` | `def` | `definition` | 1 | 3 | `sha256:47f0d7e2afc08cb461f7ffa9ab45f07f2bb250a81e9f50ee8797e6ac74b78ecf` |
| `IntegerExactDivision` | `exact_quotient_exists_unique` | `theorem` | `bind-only` | 1 | 2 | `sha256:d53a0498182f2e39237dcb066bae2c662fba3cb9d64ef010019fdd4124caa626` |
| `IntegerExactDivision` | `exact_guard_iff_integer_value` | `theorem` | `bind-only` | 4 | 6 | `sha256:9f10e7dfc359528802b9bd5cad6e1aeef7452a599d2d9824c2fcc5e7133ef4d6` |
| `IntegerExactDivision` | `section_loses_product_history` | `theorem` | `bind-only` | 0 | 24 | `sha256:5a8a616664b3d5bcad1ad82c5b49b97eed433d87f027da3b12c999e1700aa3ad` |
| `IntegerExactDivision` | `division_domains_equal_refuted` | `theorem` | `content` | 3 | 8 | `sha256:fde68f201f90c5998b0fff44590e1f271093dbf10c441d5f5cce997fcd962fb1` |
| `IntegerExactDivision` | `exactDivide_loses_product_history` | `theorem` | `bind-only` | 6 | 5 | `sha256:0fbbffd63ccdb681cdcb77205cf9f4434dc3746b1ed82b4ce29b6280072225cd` |
| `IntegerExactDivision` | `half` | `def` | `definition` | 0 | 3 | `sha256:47745b7570753d4fe8197f25fe00cc1603d2d5fdfed3211c9e6e487913218ecc` |

The sole content row is `division_domains_equal_refuted`: the live half obstruction establishes the closed negation. Its certified-instance/refutes utility is separate from historical escape preregistration, which is not certified here. The general archive-loss rows use frozen readout/cardinality formulas and normalization, so receive no escape credit.

Necessary Rat/Setoid/field, exact-quotient and archive API wrappers use `rule-11-upstream-wrapper`; their source obligations and exact owners are row-specific in the audit. Definitional projection companions receive no independent admission credit. No row uses `structural-consequence` as a basis, and no historical future consumer is promoted to a live use.

This corrected implementation assessment is not a review approval, a new Freeze/coverage receipt or overall CSA completion. Historical source/report/Freeze identities and raw captured edges remain unchanged.
