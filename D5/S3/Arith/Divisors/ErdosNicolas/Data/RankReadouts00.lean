/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/RankReadouts00
   generality: I
   mirror-B: none(waiver:certificate-payload-without-standalone-claim)
   mirror-E: none(waiver:pure-mathematics-no-experimental-evidence-claim)
   anchors: []
   utility: none
   digest: Balanced packed readout directories for complete indexed rank certificates. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Data.MainSupport

/-! The consuming main-box checks validate every generated divisor in sorted order. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Arith.ErdosNicolas.Data.RankReadouts00

private def b631_3 : PackedIndexTree := .leaf
  0x4058812a8620290220a8208c8c8108308122342108210701084888004a088015000890c00218010801010000
private def b631_5 : PackedIndexTree := .leaf
  0x2c1124c01c51b141d01480a8a142479054a1231c0068c60688921874012942c609832005610234861030c098
private def b631_6 : PackedIndexTree := .leaf
  0x780330622a919468c9346610966069079423086b1c169070e0858512551116a08b850cb021b3024257122451
private def b631_4 : PackedIndexTree := .node 1 b631_5 b631_6
private def b631_2 : PackedIndexTree := .node 1 b631_3 b631_4
private def b631_9 : PackedIndexTree := .leaf
  0x7501b2230a64b9866284e494a745441db0316242b4c4d40c70c650f60c9524e3c20b8a0b326519121d51458c
private def b631_10 : PackedIndexTree := .leaf
  0x23744e103c65b82aa2a4f49ca2b0c6d1d1473885895e6468b3835c51a42e419748171cb86152d49d40d0b4c3
private def b631_8 : PackedIndexTree := .node 1 b631_9 b631_10
private def b631_12 : PackedIndexTree := .leaf
  0x1c90f991292eb8aae2c4dacb1f41d21c4db12b22b9a1336671c6d094ec8b245e709df014c5b92555a36a8678
private def b631_13 : PackedIndexTree := .leaf
  0x29597dc951a7275698bd31ccdf106e599523a9ab3b83534fc81d991c616ce549b32cd511cd2b5c37c436c21e
private def b631_11 : PackedIndexTree := .node 1 b631_12 b631_13
private def b631_7 : PackedIndexTree := .node 2 b631_8 b631_11
private def b631_1 : PackedIndexTree := .node 3 b631_2 b631_7
private def b631_16 : PackedIndexTree := .leaf
  0xd9d3d607ec4c774a6a6f585e1cb1e4dd932baaa69dd93c71617a74a5d83aaaa8f69da335e31be14f3ca0e3c
private def b631_18 : PackedIndexTree := .leaf
  0x5a4f48f71fd05bcd8db7973473e699ca33b574e3b711725f9da91a96ed8baeac8dcdf88f176e5875e49697aa
private def b631_19 : PackedIndexTree := .leaf
  0x35e6de93abea1f6356e6c4f5e9cf1df96559fa8ed9d27fc55d175ab6fd93a3ce8ecd9e6efc8573cd2f2caeb6
private def b631_17 : PackedIndexTree := .node 1 b631_18 b631_19
private def b631_15 : PackedIndexTree := .node 1 b631_16 b631_17
private def b631_22 : PackedIndexTree := .leaf
  0x19ef29f798f7bb2b7755f6cf5bd63fc72d1f29fbdb935df3cb337b33e5c6dcbcd6b7ba7cf983e73aeaaf786e
private def b631_23 : PackedIndexTree := .leaf
  0x7b8f7f56fcf8fba7b5fd85fcfb6aecfce7fcc7ee6bdd58deddd7bafeb5a5f5f49dd7fcd9dda9fae768ef6bdb
private def b631_21 : PackedIndexTree := .node 1 b631_22 b631_23
private def b631_25 : PackedIndexTree := .leaf
  0x4ffee7fb7fed7ffdbbebffcefdbdec7fdfbebde5fbbbf79f7a6f9bbeebfbe7efaceeaff6cedfd67cffce7ab7
private def b631_26 : PackedIndexTree := .leaf
  0x1ffbfefdffef
private def b631_24 : PackedIndexTree := .node 1 b631_25 b631_26
private def b631_20 : PackedIndexTree := .node 2 b631_21 b631_24
private def b631_14 : PackedIndexTree := .node 3 b631_15 b631_20
private def b631_0 : PackedIndexTree := .node 7 b631_1 b631_14

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout631 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![3, 1, 3, 1, 1, 1, 1])
    512 39 b631_0

private def b977_4 : PackedIndexTree := .leaf
  0x1a07901a3201ca80616c010361e818820604647e1206083061068900011e18800804660c0021e00606060000
private def b977_5 : PackedIndexTree := .leaf
  0x2421b0f000e009107a4a005628386647c630c1840700193866a48120093099c201e13119002a58065e203090
private def b977_3 : PackedIndexTree := .node 1 b977_4 b977_5
private def b977_7 : PackedIndexTree := .leaf
  0x14261f9371a87b12108a7060cd0198317e824aa0a861469489b87f03238241491f0618341aab81e5c80a189
private def b977_9 : PackedIndexTree := .leaf
  0xc98600e970925001da85a294050799b104494329a4366282201e7a6a23315018db204a60086a4368656d1ea
private def b977_10 : PackedIndexTree := .leaf
  0x2c0674814e9d0315918524a128743e00b9653c8219e9304c20ad078d30034c624592101a196884421e506d94
private def b977_8 : PackedIndexTree := .node 1 b977_9 b977_10
private def b977_6 : PackedIndexTree := .node 1 b977_7 b977_8
private def b977_2 : PackedIndexTree := .node 2 b977_3 b977_6
private def b977_13 : PackedIndexTree := .leaf
  0x27862c6e0e6bc3c87d732020b2b02c18d91a111c4f44a9c001e044e43aa219b3a07e924494b18e30e120f072
private def b977_15 : PackedIndexTree := .leaf
  0x274aa8aa61cd4560351aeb96ea687f9c90a6ac2b0e290c6d499bc3c5f228036806ba391689147b729f44a42a
private def b977_16 : PackedIndexTree := .leaf
  0x1ed08ea69c4d15522019db605a6426ae87ed48094deaa4a96a8587b9236e672270d27f4336b0e18c125099f1
private def b977_14 : PackedIndexTree := .node 1 b977_15 b977_16
private def b977_12 : PackedIndexTree := .node 1 b977_13 b977_14
private def b977_18 : PackedIndexTree := .leaf
  0x1427601fa8ccd87151948526cd0004c9698544a95a636e2a9505422ad86d5eb054ce26552375a98b26223110
private def b977_20 : PackedIndexTree := .leaf
  0x20a2e1959384e866d23f13203e5d24e0c50442a41a321a51146d4429e74d095658cb86844b21a597a292250c
private def b977_21 : PackedIndexTree := .leaf
  0xea8564b12c754b9c43e53d0fa09a32c267cec5c24d13483b45d24c68031d9385876106c43ea5b2153e75109
private def b977_19 : PackedIndexTree := .node 1 b977_20 b977_21
private def b977_17 : PackedIndexTree := .node 1 b977_18 b977_19
private def b977_11 : PackedIndexTree := .node 3 b977_12 b977_17
private def b977_1 : PackedIndexTree := .node 5 b977_2 b977_11
private def b977_25 : PackedIndexTree := .leaf
  0x2473d5f64adc19e8a48143bafa893a56c8e07f7392d0ba7cac8b263e135803d1ccf6b05c28193b7468aad0b4
private def b977_26 : PackedIndexTree := .leaf
  0x1276f5f39d8d62855a0debb396345a66a72d187d42bab8ae9e55c1bebd6f8f39b0a2bc1cd80c2d39ab12c56a
private def b977_24 : PackedIndexTree := .node 1 b977_25 b977_26
private def b977_28 : PackedIndexTree := .leaf
  0x2dc449ef9cc9d34d56889ad99a31ba914528279d6ab2acd589159169bb27a69bb1ff532ad2b5ae38e32172e0
private def b977_30 : PackedIndexTree := .leaf
  0x5522d0eb65da33e1e54ecc40a2d98c8d519dc446a75565615a21b69b7410179949bba549a60df6ae2e23859
private def b977_31 : PackedIndexTree := .leaf
  0x17421ed57590b4d6842e99786c453fac997d0d83943766922f21d94c53b59364049751446a52ca69e2b5e255
private def b977_29 : PackedIndexTree := .node 1 b977_30 b977_31
private def b977_27 : PackedIndexTree := .node 1 b977_28 b977_29
private def b977_23 : PackedIndexTree := .node 2 b977_24 b977_27
private def b977_34 : PackedIndexTree := .leaf
  0x1620fe8db0ced8f17174eb62da8185d641dec5718fbbe13f7560ba38ee2e57293c4fb4cfd4ce8283443b1a91
private def b977_36 : PackedIndexTree := .leaf
  0xe78d96bb911a7de7b2955eafd6d9ba39bc9cf4702f9f6b32cd613ddc329af481e8bad4b53ad6e8e92f7167e
private def b977_37 : PackedIndexTree := .leaf
  0x267bad1552e9a8945bb789fbb54da71af8cc5d45ae19dcd78995b8d66bbb94e466af2bd5d17ae26fe6d28ef1
private def b977_35 : PackedIndexTree := .node 1 b977_36 b977_37
private def b977_33 : PackedIndexTree := .node 1 b977_34 b977_35
private def b977_39 : PackedIndexTree := .leaf
  0x2932f576b5d37a1847a56cb5e50f76cbe87ecd40d47776965ea5715edb416cea662f5f08fb75de44d5788d06
private def b977_41 : PackedIndexTree := .leaf
  0x11b57e6fbcd1db98a7bd56f8ed1e9fd638f6f6adcb7595c7be68f3be3e5ce8359ac75d6fa75e852ecffbf20f
private def b977_42 : PackedIndexTree := .leaf
  0x2ff5fe9fb9d1fbde3f59efbbf577a1efe2fe975eecf5f5df41e9b5fadfa751789eef53e9e17ee38dee5
private def b977_40 : PackedIndexTree := .node 1 b977_41 b977_42
private def b977_38 : PackedIndexTree := .node 1 b977_39 b977_40
private def b977_32 : PackedIndexTree := .node 3 b977_33 b977_38
private def b977_22 : PackedIndexTree := .node 5 b977_23 b977_32
private def b977_0 : PackedIndexTree := .node 11 b977_1 b977_22

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout977 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![1, 3, 3, 2, 1, 1, 1])
    1024 35 b977_0

private def b1419_4 : PackedIndexTree := .leaf
  0x270604dc0e2484218206410610e0069b03041c6204830a58310203c00132002660040c240020d86001830000
private def b1419_5 : PackedIndexTree := .leaf
  0x78324f209003a21993d1901400532a604819a330310a0069059c3e0090c9c8908d90d0d002a44680603680c
private def b1419_3 : PackedIndexTree := .node 1 b1419_4 b1419_5
private def b1419_7 : PackedIndexTree := .leaf
  0x1b1431a861868074e2052784e1896c8e4124c31001e965b4941103158a0844a7825a630f1130e831822971b8
private def b1419_9 : PackedIndexTree := .leaf
  0xd29c5cc9a2464a0dd688d40e462039f8926726910919183400de0443a9d1d061490928e14283c06ea004a4c
private def b1419_10 : PackedIndexTree := .leaf
  0x1e8674a8989943e522150ce0ceb80aa647252490dc0678800d4d13e82c02e9091550685ca3f06136c5803436
private def b1419_8 : PackedIndexTree := .node 1 b1419_9 b1419_10
private def b1419_6 : PackedIndexTree := .node 1 b1419_7 b1419_8
private def b1419_2 : PackedIndexTree := .node 2 b1419_3 b1419_6
private def b1419_13 : PackedIndexTree := .leaf
  0x79638f31c025138eaa25e4a025e500f5645ba3b0511e8cb09a109868a6f1211f19b460cd3d9920a45201e8c
private def b1419_15 : PackedIndexTree := .leaf
  0x2006d6519e9ac4453a1b18b3984bb40429f1e14f25b7618d6d8989484d3a51231c4408ea897568951b978914
private def b1419_16 : PackedIndexTree := .leaf
  0x102a84137f298936765610d6a5d261d041a49238c150fa289e6a2751392524e6cd303950e6a8411a81fa9016
private def b1419_14 : PackedIndexTree := .node 1 b1419_15 b1419_16
private def b1419_12 : PackedIndexTree := .node 1 b1419_13 b1419_14
private def b1419_18 : PackedIndexTree := .leaf
  0xd53f863ba05a03e947e5549cdf0695ce2c26a195014a8df170d60eec09d66c745fa4b09192da642c880f466
private def b1419_20 : PackedIndexTree := .leaf
  0x19f470812a9963ec2d15a91ae9ec544ac999cb520fd499c2164820dcd3af02e861cd9a69291dc44a552211a3
private def b1419_21 : PackedIndexTree := .leaf
  0x2821f519508f71d1933b853b628da11e9849442a663655be48ca01547e468cfae42b852b09968e5c125705ea
private def b1419_19 : PackedIndexTree := .node 1 b1419_20 b1419_21
private def b1419_17 : PackedIndexTree := .node 1 b1419_18 b1419_19
private def b1419_11 : PackedIndexTree := .node 3 b1419_12 b1419_17
private def b1419_1 : PackedIndexTree := .node 5 b1419_2 b1419_11
private def b1419_25 : PackedIndexTree := .leaf
  0x1e3581154f9da63c712684f3aed411a3079681aaa5f771415a89c959bb3b5161ec7209eac8456ca2e086f5e6
private def b1419_26 : PackedIndexTree := .leaf
  0x2018a95c9edad7593b2e06d2593239ed110e2cb227da993d766026dd34266536b9131146eaa6d2811699567e
private def b1419_24 : PackedIndexTree := .node 1 b1419_25 b1419_26
private def b1419_28 : PackedIndexTree := .leaf
  0x5e7f699b0a777d1592d26e74d054b8932283fb1229a8e20755fea689593d315690f231ab4186bbc2a505e9c
private def b1419_30 : PackedIndexTree := .leaf
  0x14a3fee916ee0a56be555f1869cf530b19adc64ac5d218d7b06ea8726da59fb5e12d559f269c892c86740eec
private def b1419_31 : PackedIndexTree := .leaf
  0x171a19eb475462ad9728857b72bb8e1ed85ab22b6675257249ca470d1e20ebd0beb486574a4dc57b953214ae
private def b1419_29 : PackedIndexTree := .node 1 b1419_30 b1419_31
private def b1419_27 : PackedIndexTree := .node 1 b1419_28 b1419_29
private def b1419_23 : PackedIndexTree := .node 2 b1419_24 b1419_27
private def b1419_34 : PackedIndexTree := .leaf
  0x16245c73be2adb596d8263279d64a0dde50c75278efb6634a16ae84d455ba0a6fca11fd1b1da15ac6daa3e0c
private def b1419_36 : PackedIndexTree := .leaf
  0x8e8b6c9bcaa78929e80d35579af2e86fbd2d38162eb2a7f5853f2f1db4d89bb5447b3231aaddd8196b27657
private def b1419_37 : PackedIndexTree := .leaf
  0x1f3538b3bb45fb92c37d61e2d66f5e92f22ec5bba217fd7ca6df656c8d2d907bc69db1a2b5762275cb925d33
private def b1419_35 : PackedIndexTree := .node 1 b1419_36 b1419_37
private def b1419_33 : PackedIndexTree := .node 1 b1419_34 b1419_35
private def b1419_39 : PackedIndexTree := .leaf
  0x236a1d4728edd8e617ace0e5cca547eb5b79758e9ef2bd4b29ae1afe3cada1b5357671c87bae1db8a975e557
private def b1419_41 : PackedIndexTree := .leaf
  0x17e23ef38969f57cbbbd62fb2e262f537b36f681d632faf9b5ece8cd6577c9f8d6faabd6f82d661defcb6e0d
private def b1419_42 : PackedIndexTree := .leaf
  0x2ff8fee75fe27bdcbfb3efb59efd8defe83edf8eca78f6b75dee38f94fb961f5eeefb997d7dcb7b1e23
private def b1419_40 : PackedIndexTree := .node 1 b1419_41 b1419_42
private def b1419_38 : PackedIndexTree := .node 1 b1419_39 b1419_40
private def b1419_32 : PackedIndexTree := .node 3 b1419_33 b1419_38
private def b1419_22 : PackedIndexTree := .node 5 b1419_23 b1419_32
private def b1419_0 : PackedIndexTree := .node 11 b1419_1 b1419_22

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout1419 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![3, 7, 0, 2, 1, 1, 1])
    1024 35 b1419_0

private def b1491_4 : PackedIndexTree := .leaf
  0x108604080f1823724c065b00401a39184120c1960c20718c3c024310016600233030900043600c6001830000
private def b1491_5 : PackedIndexTree := .leaf
  0x25c09920664c60800364054668cd3d2640c4ce7202890432320053f24267060364069c0d03680d0d1a49100e
private def b1491_3 : PackedIndexTree := .node 1 b1491_4 b1491_5
private def b1491_7 : PackedIndexTree := .leaf
  0x1b2920e50490c6167c124e67804096586128e030e50075149698d6d0141e0f10798ea20e83c9880944c315bc
private def b1491_9 : PackedIndexTree := .leaf
  0x1a5349cc0b0909140f4243669aa0025009190a6803d60c64375d402a4d9d03e351386c4de044389381b6a06c
private def b1491_10 : PackedIndexTree := .leaf
  0xcf724f60a45099833325c0211ca980fd0aa434919da50ca184073f9947e0589c59e344623e0db9a0354b272
private def b1491_8 : PackedIndexTree := .node 1 b1491_9 b1491_10
private def b1491_6 : PackedIndexTree := .node 1 b1491_7 b1491_8
private def b1491_2 : PackedIndexTree := .node 2 b1491_3 b1491_6
private def b1491_13 : PackedIndexTree := .leaf
  0x4d5128a6f4ea790442a25d628274844e31dbe952b80851897991489b81559b1f0f57b02299592a30563b150
private def b1491_15 : PackedIndexTree := .leaf
  0x1871a27e12ce17609c945e29e11510a5b4f1b5ab0e2054799481f459ac8418f1c2896d8e90587a440f362680
private def b1491_16 : PackedIndexTree := .leaf
  0x3f35539198df75a6cb403993d309d9a93593a7406d6cc9492413436040ea7d6aaa41b9045a24a39de143841
private def b1491_14 : PackedIndexTree := .node 1 b1491_15 b1491_16
private def b1491_12 : PackedIndexTree := .node 1 b1491_13 b1491_14
private def b1491_18 : PackedIndexTree := .leaf
  0x273550d3736c43e82d2466a0dd2e7122869c88a85ce4042e24a474a10b686981955ca89d502d027f05c9d5a2
private def b1491_20 : PackedIndexTree := .leaf
  0x1527a08572cac9842b4961c14a9532dc2af086472623fd957e5261659f2029618cf97c0b49a5967ea904b45a
private def b1491_21 : PackedIndexTree := .leaf
  0x1e6464462aa5f501236e6b01f57495aba7b42346a1464c74a35ba15ced5447e3ddeea12e8146675228e704ee
private def b1491_19 : PackedIndexTree := .node 1 b1491_20 b1491_21
private def b1491_17 : PackedIndexTree := .node 1 b1491_18 b1491_19
private def b1491_11 : PackedIndexTree := .node 3 b1491_12 b1491_17
private def b1491_1 : PackedIndexTree := .node 5 b1491_2 b1491_11
private def b1491_25 : PackedIndexTree := .leaf
  0x1176b6114f8716dc98ab8171ed11822816ba12aa1451ca8b5b0eb796dc448452a58ba084f519dc6fca0956b9
private def b1491_26 : PackedIndexTree := .leaf
  0x1ab232a57486f4156925a4b43e06a70699fd60a99d94196a8009d78e7910d3d8d06aab4e376ad427a534d27a
private def b1491_24 : PackedIndexTree := .node 1 b1491_25 b1491_26
private def b1491_28 : PackedIndexTree := .leaf
  0x22ab015d22aa340dfdbd12a175a3a6867579f475cb89b6d17f93117a77560d74edd1b20959bad28143b4ca2c
private def b1491_30 : PackedIndexTree := .leaf
  0x2975e2be7c51e860b565dfba445b55482b14fb7caec2da6b532924bdc58a556225cf2c2c60bc934a620a65c6
private def b1491_31 : PackedIndexTree := .leaf
  0x1bbac87f5da0c7be85ba61652476a3d703bd537a6e02b686baa1d14d4a70ca4af5ea21d1d2ba6349e1ead081
private def b1491_29 : PackedIndexTree := .node 1 b1491_30 b1491_31
private def b1491_27 : PackedIndexTree := .node 1 b1491_28 b1491_29
private def b1491_23 : PackedIndexTree := .node 2 b1491_24 b1491_27
private def b1491_34 : PackedIndexTree := .leaf
  0x1368c1af84ea91cd6d26add44e0aa0d64aa9477756e285e7b78472ad418e2b177ad85d4a295ebb46e1550875
private def b1491_36 : PackedIndexTree := .leaf
  0x22d5688d74eca25e2481e9d8b96123aa741d6b806f8a7a351ad6276cbcb560227d359ed3f8dacc266afb5a09
private def b1491_37 : PackedIndexTree := .leaf
  0xb75369355ee42c6c7bba21539c78aec122cb2bd52b88a9b5f2c257df52e5ffbd85f566c97daf02ea6fb4d33
private def b1491_35 : PackedIndexTree := .node 1 b1491_36 b1491_37
private def b1491_33 : PackedIndexTree := .node 1 b1491_34 b1491_35
private def b1491_39 : PackedIndexTree := .leaf
  0x2d928d438eab3b6977836171dd71b860ea1eeb52d72295ebb88af8f21fad57929abf47e19ad8835e9f3bb61a
private def b1491_41 : PackedIndexTree := .leaf
  0x17e7def12ed5bb2ef28962f23ef989a9f58cbd80efa8decd2fad74de31b389b82e32596ab5befcb7e39599df
private def b1491_42 : PackedIndexTree := .leaf
  0x2ff8fee75fef389efb2fecf8cefd59efe8eedb83d73b8e3d29e3eadd7b86ee5bbd4fb98b388d7db0ef7
private def b1491_40 : PackedIndexTree := .node 1 b1491_41 b1491_42
private def b1491_38 : PackedIndexTree := .node 1 b1491_39 b1491_40
private def b1491_32 : PackedIndexTree := .node 3 b1491_33 b1491_38
private def b1491_22 : PackedIndexTree := .node 5 b1491_23 b1491_32
private def b1491_0 : PackedIndexTree := .node 11 b1491_1 b1491_22

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout1491 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![3, 7, 1, 2, 1, 1, 0])
    1024 35 b1491_0

private def b1726_5 : PackedIndexTree := .leaf
  0x930189e0020302190fc308240608184e03081a18c2400021e0c40026c0010cc0c0900020f0018600180c0000
private def b1726_7 : PackedIndexTree := .leaf
  0x840202411e1660310c800a4b12100cb683c403048540340c04f201a190de24401c540c08309b0020361821e8
private def b1726_8 : PackedIndexTree := .leaf
  0xb40801b0cb0488c403d12800a629ec0383333a03e3623183050807000cc82409386c8669240489f00246119c
private def b1726_6 : PackedIndexTree := .node 1 b1726_7 b1726_8
private def b1726_4 : PackedIndexTree := .node 1 b1726_5 b1726_6
private def b1726_10 : PackedIndexTree := .leaf
  0x61556034922370c64fe0321c138986241720490f81869400d0352b89c8c683cbc83900a0c4a420d83c001b1c
private def b1726_12 : PackedIndexTree := .leaf
  0xca6d0f54380282624d1f9a90d206e1a8612f08f61210449c0c18d093819818b809c2f12481fa048aa054185
private def b1726_13 : PackedIndexTree := .leaf
  0x22250655446f46906cc28450c144448a03c7a551338199264a80636f86c809260918f0688021548dc06d306
private def b1726_11 : PackedIndexTree := .node 1 b1726_12 b1726_13
private def b1726_9 : PackedIndexTree := .node 1 b1726_10 b1726_11
private def b1726_3 : PackedIndexTree := .node 3 b1726_4 b1726_9
private def b1726_16 : PackedIndexTree := .leaf
  0x4b4212431083ca06d9a36ab7065064a186f203a6425c65024a44940a84075b62a1344fc181a500a0798d8d00
private def b1726_18 : PackedIndexTree := .leaf
  0x1f13e805b244b36a1d4485278820cf3698452e12604c104b40f19309f8035990c6122649f0040a82686124f0
private def b1726_19 : PackedIndexTree := .leaf
  0xfc92424b982593e4c70c37b92a10903c0e4b00cecec842c8ab8081906f409d1d06cccc46299142892825074
private def b1726_17 : PackedIndexTree := .node 1 b1726_18 b1726_19
private def b1726_15 : PackedIndexTree := .node 1 b1726_16 b1726_17
private def b1726_21 : PackedIndexTree := .leaf
  0x79873101450058d8d580b031b2c923211625580388f425470003b21b48f6902139074a21b299b1d12d275314
private def b1726_23 : PackedIndexTree := .leaf
  0x6c806a82ba6a0392734b12d09158887b728f28e51f42520a93c18b948f6437528072af1c40f263d3a6d107d
private def b1726_24 : PackedIndexTree := .leaf
  0x6a1adc22b937502272b1b4d1250ff3c939346014aac15838987243ab81b5c91263783c4f944063a282d0ca2
private def b1726_22 : PackedIndexTree := .node 1 b1726_23 b1726_24
private def b1726_20 : PackedIndexTree := .node 1 b1726_21 b1726_22
private def b1726_14 : PackedIndexTree := .node 3 b1726_15 b1726_20
private def b1726_2 : PackedIndexTree := .node 6 b1726_3 b1726_14
private def b1726_28 : PackedIndexTree := .leaf
  0xa109c84e0d293c7f6a6033698e0ae81ac1c338e1823061af19c8c9224a098f8a74554d00551871a9284ac55a
private def b1726_30 : PackedIndexTree := .leaf
  0x2a8880339b67030e80b4d04c8269743c59227eca4514a94095a53741bcaa4549aa7f0c2c2c5593dc48cdcc3c
private def b1726_31 : PackedIndexTree := .leaf
  0xa090e40ab3a19d6204cc9b7d0549bf549692374d4c2c4589884648e786440f6d12046a999e2716e570068c9d
private def b1726_29 : PackedIndexTree := .node 1 b1726_30 b1726_31
private def b1726_27 : PackedIndexTree := .node 1 b1726_28 b1726_29
private def b1726_33 : PackedIndexTree := .leaf
  0x4a4149be9b32013328101365825930db0761234a2546a22a94d33711b6fd2154c0454c1d2a054114b60da9eb
private def b1726_35 : PackedIndexTree := .leaf
  0x12a65865be44351a0225456f6b20d2cca9e897a14a296555e044c8b218508ec01f6dca8d9cdbc19afc90e151
private def b1726_36 : PackedIndexTree := .leaf
  0x2653f807cc94baca6d6093758f890614108550d4836d34709a5e3f19e4219288515a8e80851e7268cda80dba
private def b1726_34 : PackedIndexTree := .node 1 b1726_35 b1726_36
private def b1726_32 : PackedIndexTree := .node 1 b1726_33 b1726_34
private def b1726_26 : PackedIndexTree := .node 3 b1726_27 b1726_32
private def b1726_39 : PackedIndexTree := .leaf
  0xed4c020ac41f5095934f14b75d2d508575521dea13e3a84250545866adac5c5b932b2e92704e4335a1690fc
private def b1726_41 : PackedIndexTree := .leaf
  0xb52ea65513d07c825462c26b067c764ee8472e4b824dae413441b9c5a2f48e91319faccd400c73272b10b3e1
private def b1726_42 : PackedIndexTree := .leaf
  0x8213b591da6ae2819e893b3a31529028a6cead05a0ea96c8558b24bac812c3ab9a25d7a0e20f99f712192bde
private def b1726_40 : PackedIndexTree := .node 1 b1726_41 b1726_42
private def b1726_38 : PackedIndexTree := .node 1 b1726_39 b1726_40
private def b1726_44 : PackedIndexTree := .leaf
  0x512e2aec0e996b3acb623862a1fde71ce7324b62902e4f8ac85918f7bb2a509960a595881e8737183d9609c2
private def b1726_46 : PackedIndexTree := .leaf
  0x40747228d5205ad48732b11632ce0016a48ec4dcb5611ea7d8959c18889e8525a594cf6d02d2aaa80ed5f354
private def b1726_47 : PackedIndexTree := .leaf
  0x72b259e59cb2307d68d02b55cd1057279b91294ae55e0df4a55e9be7123ce064429b0c7d360a2b46bc1e69cd
private def b1726_45 : PackedIndexTree := .node 1 b1726_46 b1726_47
private def b1726_43 : PackedIndexTree := .node 1 b1726_44 b1726_45
private def b1726_37 : PackedIndexTree := .node 3 b1726_38 b1726_43
private def b1726_25 : PackedIndexTree := .node 6 b1726_26 b1726_37
private def b1726_1 : PackedIndexTree := .node 12 b1726_2 b1726_25
private def b1726_52 : PackedIndexTree := .leaf
  0x8648c98785cabae4d7012737a7ce86276882d086b59014328cad03770d5455db51ba8396054e78688d0b4a6a
private def b1726_54 : PackedIndexTree := .leaf
  0x556d06e20ab1aafe9121590b556dc29bb87d35204d0a13c9a5763b892a7fca654e69d46556dd215a6b871bfc
private def b1726_55 : PackedIndexTree := .leaf
  0x87acfa84a73b197084e8d393efb0ab2228e1535a6b83ba26b6692668628c6c02ea78f24c8a14aa2c09d3ab76
private def b1726_53 : PackedIndexTree := .node 1 b1726_54 b1726_55
private def b1726_51 : PackedIndexTree := .node 1 b1726_52 b1726_53
private def b1726_57 : PackedIndexTree := .leaf
  0x442b68db904a0d0ec0bcd14cb62ada09b768ba5f5149a2b52da5a986ea37cd5c2e9888b9fc88e0b2b70891ef
private def b1726_59 : PackedIndexTree := .leaf
  0x43cfa4a9c6ca70dfd6610299d0b516b2e4c75f2d908d76523ca31dc22344e302a767adcdfb5c19845552b056
private def b1726_60 : PackedIndexTree := .leaf
  0xa06cb44bbe6b62ec4a2c6a08d51d4a2ca34efd67b42b9828acbc255af415445ba421cb64ed5056776f867d89
private def b1726_58 : PackedIndexTree := .node 1 b1726_59 b1726_60
private def b1726_56 : PackedIndexTree := .node 1 b1726_57 b1726_58
private def b1726_50 : PackedIndexTree := .node 3 b1726_51 b1726_56
private def b1726_63 : PackedIndexTree := .leaf
  0x8a3f964ccb8313d52fb2bb5cebabc90d41c50cecc5c524dbc5e5bd97cfcd0ea53ad814d6b3a226d7c080ccd
private def b1726_65 : PackedIndexTree := .leaf
  0x95cf8d06d32086b19ae291bc109e5ecf32e95d843ad57ac759d090b26b1699ba841756eccbbe54374d234d6a
private def b1726_66 : PackedIndexTree := .leaf
  0x82912993d75b56ead7c3d527e75505d2451d165ad0ee1732ecb924f09ee7ab4ad3bd83f499cff898a0ad6bad
private def b1726_64 : PackedIndexTree := .node 1 b1726_65 b1726_66
private def b1726_62 : PackedIndexTree := .node 1 b1726_63 b1726_64
private def b1726_68 : PackedIndexTree := .leaf
  0x2c54b81fa8d71cb0dacddc1db04a77a3c2e35cdcebd33a715a912b616ca0656a172c95983bd3158b7a8e30fb
private def b1726_70 : PackedIndexTree := .leaf
  0x38711a6e41114d69d7a2078ab559ab521516ad6ed0b51d72de0216e474c5eb2b9b25f7a4e2a7e893661efcab
private def b1726_71 : PackedIndexTree := .leaf
  0x14b29caf52b8f15555fb5571703aeccda2da9b91caf279e73c8e51e8a60bd3eab3b982ce01161a5b58dc68f7
private def b1726_69 : PackedIndexTree := .node 1 b1726_70 b1726_71
private def b1726_67 : PackedIndexTree := .node 1 b1726_68 b1726_69
private def b1726_61 : PackedIndexTree := .node 3 b1726_62 b1726_67
private def b1726_49 : PackedIndexTree := .node 6 b1726_50 b1726_61
private def b1726_75 : PackedIndexTree := .leaf
  0x2ba17aafae237f036874439b29b6c90a3778bc68ed536a775873c3646d004b5b975c8468fbc4568c9eeca5ca
private def b1726_77 : PackedIndexTree := .leaf
  0xb041748b2e1a1a9dda1dc61af6451315b8e8e1eeacd68170d51aa6bb08bb9dd49729c4668daaf68a2bdff5c9
private def b1726_78 : PackedIndexTree := .leaf
  0x5d6454a5d178c8a69bbdc598cfed1285b5bd7e21fcd5a176384faed7dcee4a6c72a9ed3d4e5d335eff619a33
private def b1726_76 : PackedIndexTree := .node 1 b1726_77 b1726_78
private def b1726_74 : PackedIndexTree := .node 1 b1726_75 b1726_76
private def b1726_80 : PackedIndexTree := .leaf
  0xb176d5dabeb8dd4e96729985f3151797cafc23d6e9de2271899fd8db86fb4aba23a791c4834d34cf6d9db581
private def b1726_82 : PackedIndexTree := .leaf
  0x21e76e2f0beb7e87e36d6ea72b36f910399f07197d7db66ecca39dd52d185fbcc32f495c2bba65b77d082d07
private def b1726_83 : PackedIndexTree := .leaf
  0x1ff13a0cdaf75ebf107c5d6bca4ef10bd97e5dab6ad77464def8a867cf4da3584752ab2ef241a9ee5e6bdba5
private def b1726_81 : PackedIndexTree := .node 1 b1726_82 b1726_83
private def b1726_79 : PackedIndexTree := .node 1 b1726_80 b1726_81
private def b1726_73 : PackedIndexTree := .node 3 b1726_74 b1726_79
private def b1726_86 : PackedIndexTree := .leaf
  0x5f349547b5bbbc3bd1f17373f7b626a83b392bcb353358ed760b5e12eb5dd7d3d73af49a2da851774d6b5dee
private def b1726_88 : PackedIndexTree := .leaf
  0x8f555dabddb80a5bd1d91e4ff73acc963a5f1f1c7ddd9bd04d1eaf68af48d5b8b780c596b3deb38f05625d9a
private def b1726_89 : PackedIndexTree := .leaf
  0x5c77f287d9377b1daebc3746f6197291b68f656e595f8f303e6da6f77cbcc8ed1fb9b00d734479bb65853af5
private def b1726_87 : PackedIndexTree := .node 1 b1726_88 b1726_89
private def b1726_85 : PackedIndexTree := .node 1 b1726_86 b1726_87
private def b1726_91 : PackedIndexTree := .leaf
  0x8c74f6fb107b6eede32a9b98e5f96fdf9b1efbe9f47353b60c8bc66b8e89e3adfa9af61577bbb29ea79ff85f
private def b1726_93 : PackedIndexTree := .leaf
  0x82ebee93def89f6797eb5fbc65dd43d37bcb06d7f45f17f5bef9c1d52f798bdba7beb1be9dacf83c5f6bf9df
private def b1726_94 : PackedIndexTree := .leaf
  0xbff1fecfaffbcf07efb97fa7f19efda9fbfb1dec3dfe77eb9ecbc7b23f73e3ecdf5ef01ecdc7ebbe8fece967
private def b1726_92 : PackedIndexTree := .node 1 b1726_93 b1726_94
private def b1726_90 : PackedIndexTree := .node 1 b1726_91 b1726_92
private def b1726_84 : PackedIndexTree := .node 3 b1726_85 b1726_90
private def b1726_72 : PackedIndexTree := .node 6 b1726_73 b1726_84
private def b1726_48 : PackedIndexTree := .node 12 b1726_49 b1726_72
private def b1726_0 : PackedIndexTree := .node 24 b1726_1 b1726_48

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout1726 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![3, 3, 3, 2, 1, 1, 1])
    2048 32 b1726_0

private def b1758_4 : PackedIndexTree := .leaf
  0x13e6c8d84849c010362a9b606550020ae488482440c7201a498c00789200538258306c0022a0064801824000
private def b1758_5 : PackedIndexTree := .leaf
  0xb06f12407c4a24d56039ca3c1392d01c4a04e25cc2049ce0c568081b14b09400cc64e8602a4247809801c32
private def b1758_3 : PackedIndexTree := .node 1 b1758_4 b1758_5
private def b1758_7 : PackedIndexTree := .leaf
  0x1e24c89a42151024cc0d140199b42bcda0a923798492780d60038725442b1b806cde49d522880a1e0c10f1f8
private def b1758_8 : PackedIndexTree := .leaf
  0x612d9c24a8256605078499570c4051d00ccf64fd6a2e8226ccd94b85427610014c87513c0dc622ad6e099b7
private def b1758_6 : PackedIndexTree := .node 1 b1758_7 b1758_8
private def b1758_2 : PackedIndexTree := .node 2 b1758_3 b1758_6
private def b1758_11 : PackedIndexTree := .leaf
  0x1ba2d628074e04a5ec5504f2907a30c136183e73dfa528b25a5be084e41312d255580407e730c73c8424edfe
private def b1758_12 : PackedIndexTree := .leaf
  0x1e437d344285a54ca38580b1e4ce769420f4687e4b15d0dc0b1bd495e812ca04395703d823483a72cf15186c
private def b1758_10 : PackedIndexTree := .node 1 b1758_11 b1758_12
private def b1758_14 : PackedIndexTree := .leaf
  0x9b4255e05884748cd0d4f8506045b0672f1b536d300ad9e159e727e12588ca605d60e4fc191452b5700a1b9
private def b1758_15 : PackedIndexTree := .leaf
  0x40745fc3dd4c1c96b700bb8b8233992f7c95a15480844c9630f4111d54f60018cb85bdc409d9a3a85278d33
private def b1758_13 : PackedIndexTree := .node 1 b1758_14 b1758_15
private def b1758_9 : PackedIndexTree := .node 2 b1758_10 b1758_13
private def b1758_1 : PackedIndexTree := .node 4 b1758_2 b1758_9
private def b1758_19 : PackedIndexTree := .leaf
  0x1760b9bf7a8e5135105661c045841fcd4734f3520431b9ff2de2a5e8e270d2b665ee144a64507c574c505588
private def b1758_20 : PackedIndexTree := .leaf
  0xa18510f5908a60dd834c3b3f947829721b5bb8a4e14d9a44305c7b555296181ecd061ddc0fd021a9fb52cb3
private def b1758_18 : PackedIndexTree := .node 1 b1758_19 b1758_20
private def b1758_22 : PackedIndexTree := .leaf
  0x16332d8e119d7808fd1957171a340a59c3b1e54d50b5805b21a1733d923e9db50e061a4be5d4dd0b5a0161e9
private def b1758_23 : PackedIndexTree := .leaf
  0x18d3d4451c2012e62c5f1c566df03ac534595f888176288574cf9538748156d2f6303a13167df415d1a20a13
private def b1758_21 : PackedIndexTree := .node 1 b1758_22 b1758_23
private def b1758_17 : PackedIndexTree := .node 2 b1758_18 b1758_21
private def b1758_26 : PackedIndexTree := .leaf
  0x21d614d5401498306f8ad7b38da6179ef29e1a4547d625de105047f54d5e0737062f39daa449f356e1e204d6
private def b1758_27 : PackedIndexTree := .leaf
  0x232685f61651c855656408b764ff82d738d8ee4dda54345d22219345947760840c6b5de3a0bda27ad115988c
private def b1758_25 : PackedIndexTree := .node 1 b1758_26 b1758_27
private def b1758_29 : PackedIndexTree := .leaf
  0x718b57d6a1f145e2362d0653c758c4e96b1f58811b20d8f11e035f9c78d59d3b5185862421d933ec7681cbf
private def b1758_31 : PackedIndexTree := .leaf
  0x2251de336b9f7475918dcef89889656098eda347967235018363869c5f86d9677d055e63c6ad1323a1f35e0e
private def b1758_32 : PackedIndexTree := .leaf
  0x8fdaf89d1f8e5978f48f83da941e3e6b6215fd19
private def b1758_30 : PackedIndexTree := .node 1 b1758_31 b1758_32
private def b1758_28 : PackedIndexTree := .node 1 b1758_29 b1758_30
private def b1758_24 : PackedIndexTree := .node 2 b1758_25 b1758_28
private def b1758_16 : PackedIndexTree := .node 4 b1758_17 b1758_24
private def b1758_0 : PackedIndexTree := .node 8 b1758_1 b1758_16

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout1758 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![3, 5, 3, 2, 0, 1, 0])
    1024 35 b1758_0

private def b2339_4 : PackedIndexTree := .leaf
  0xfc490c20c478021b02512c0c810185e0270c41881854034330016003c190023c06c480042400c3003018000
private def b2339_6 : PackedIndexTree := .leaf
  0xc80fa701981c1b5547b0f22a038341211baa00915c0158410122244d81a2100180d3d18c248481c0c103a40
private def b2339_7 : PackedIndexTree := .leaf
  0x19401e2545984a09eb4054318351f0cd6d01a93152420984c036604cec003d210146f06579003281823c538
private def b2339_5 : PackedIndexTree := .node 1 b2339_6 b2339_7
private def b2339_3 : PackedIndexTree := .node 1 b2339_4 b2339_5
private def b2339_9 : PackedIndexTree := .leaf
  0x9909b17e1883fb302d044498953712d850331eaac029b25a0113e190259e11312e274e41d21c3141291063
private def b2339_11 : PackedIndexTree := .leaf
  0xa4618f54f0426367424cdac30491aa12081c81c5587c00f3da412b18e3f5443504a9f1251caa430c281e560
private def b2339_12 : PackedIndexTree := .leaf
  0x808a0d16e01e9406f55aa10950c7b95d691342aadc0e98534b0410523220d970069a8a1109a587a15e01d14
private def b2339_10 : PackedIndexTree := .node 1 b2339_11 b2339_12
private def b2339_8 : PackedIndexTree := .node 1 b2339_9 b2339_10
private def b2339_2 : PackedIndexTree := .node 3 b2339_3 b2339_8
private def b2339_15 : PackedIndexTree := .leaf
  0x9a794504c8a160ce84e620327020fe7121ab805a486f8675d01d411e65559c289edb50f31613a2a4ca0e672
private def b2339_17 : PackedIndexTree := .leaf
  0x164919b57f01b40a4dcd1532e19a4252a266d238056a2131860371fab033db6c04855b015939bd8119442b3c
private def b2339_18 : PackedIndexTree := .leaf
  0x4d4be16395cc1d6ae876647d16a04cfa914b06490178d4813999a012927ed139b1815476aa21e31c2c7507d
private def b2339_16 : PackedIndexTree := .node 1 b2339_17 b2339_18
private def b2339_14 : PackedIndexTree := .node 1 b2339_15 b2339_16
private def b2339_20 : PackedIndexTree := .leaf
  0x1462d4d6c20459f92723234375c4a9a150aa5c1ed62ab40b6cd187e969628f9cc9402dae8119919e09737b10
private def b2339_22 : PackedIndexTree := .leaf
  0x348299f1b60f71713e2b58f9d9458b0d5c384b9f6c408a547287356aa50a5107c96190da82b9f9b81893ff31
private def b2339_23 : PackedIndexTree := .leaf
  0x20809d0e967407a55f699154d8a5b79873b2944f624c18439d48aaf0db70b0d1ae135e021969c97a95968116
private def b2339_21 : PackedIndexTree := .node 1 b2339_22 b2339_23
private def b2339_19 : PackedIndexTree := .node 1 b2339_20 b2339_21
private def b2339_13 : PackedIndexTree := .node 3 b2339_14 b2339_19
private def b2339_1 : PackedIndexTree := .node 6 b2339_2 b2339_13
private def b2339_27 : PackedIndexTree := .leaf
  0x2ba8a64a6e6005d81f41a51ce1572f19e435efb585a6968c4d4abb743bc9082ad22a34dbac14895c252706a3
private def b2339_29 : PackedIndexTree := .leaf
  0x21a3a5d0aca21c0e6821d6eae417925bf8197565905cf9e7532f41499da10a3b54eac70594ee2232e7376081
private def b2339_30 : PackedIndexTree := .leaf
  0x19ba092bb4e383871a15e89aaa190ba607587f59ab16dd1c7f96d93f362ea05bb19542f3d26ce2c5051a2933
private def b2339_28 : PackedIndexTree := .node 1 b2339_29 b2339_30
private def b2339_26 : PackedIndexTree := .node 1 b2339_27 b2339_28
private def b2339_32 : PackedIndexTree := .leaf
  0x1f55acfb508b1ba9939e9498c31213e81b20e773b191dea987c2d999d57d96591dacd50b27f6e440f35528b9
private def b2339_34 : PackedIndexTree := .leaf
  0x1c5a9e0c0ad129774458daa465fbb898bcce98504b7ba70a11e7923ac08d8df71b1185d7c979cdabd1a9974c
private def b2339_35 : PackedIndexTree := .leaf
  0x5da593f89a77772be8b70f5eac508e5572d5b68911d29f3b685e6a6902bee1ca1478b8d7c267f236c68d656
private def b2339_33 : PackedIndexTree := .node 1 b2339_34 b2339_35
private def b2339_31 : PackedIndexTree := .node 1 b2339_32 b2339_33
private def b2339_25 : PackedIndexTree := .node 3 b2339_26 b2339_31
private def b2339_38 : PackedIndexTree := .leaf
  0x253ce8be826f043f4169e8e4dedf3b726a56b6897079b08b5cabd70e0a5e65bd09ebbe1a145f4929ed93bb20
private def b2339_40 : PackedIndexTree := .leaf
  0x31614e85b30eb74b1d88e6a766bb92f588057741f39538bdbd99fa1ad78f31e16e8d76b2520eb58adbb80971
private def b2339_41 : PackedIndexTree := .leaf
  0x2ca8e71baac2f985d759dae477567fee6cde9c2eeed8e8e3c568b86e62746b347a69d416f81eee65f3f536f5
private def b2339_39 : PackedIndexTree := .node 1 b2339_40 b2339_41
private def b2339_37 : PackedIndexTree := .node 1 b2339_38 b2339_39
private def b2339_44 : PackedIndexTree := .leaf
  0x32aa670b23ec18ddc78397d97f46bf11bd369a50eeb9eec28c7135fac973e67d39f76b7552cee5cb14b8ca83
private def b2339_45 : PackedIndexTree := .leaf
  0x327ade6d5ce0bbcb43be4efc869789e6e776bfd717bbe9a3d2edbc885fa45deca62fb1e5783513d15aba4ae3
private def b2339_43 : PackedIndexTree := .node 1 b2339_44 b2339_45
private def b2339_47 : PackedIndexTree := .leaf
  0x34fcb633b2dafd5ee7cba9d8ee6347f51a7aefc5ecd74e6bd4b5953ef7a1ece8f71f76f5a80f3b2fef18fa8f
private def b2339_48 : PackedIndexTree := .leaf
  0xd7effcbe9fd4ecfd6e3fbce6fd76fbc8ddfd7a93cae0fd1efda6ec35fefe
private def b2339_46 : PackedIndexTree := .node 1 b2339_47 b2339_48
private def b2339_42 : PackedIndexTree := .node 2 b2339_43 b2339_46
private def b2339_36 : PackedIndexTree := .node 3 b2339_37 b2339_42
private def b2339_24 : PackedIndexTree := .node 6 b2339_25 b2339_36
private def b2339_0 : PackedIndexTree := .node 12 b2339_1 b2339_24

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout2339 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![8, 1, 3, 2, 0, 1, 1])
    1024 35 b2339_0

private def b2359_4 : PackedIndexTree := .leaf
  0x124038311e0086c0c22512c040610c9e0270c40615018834330016003c190f00086c480042400c3003018000
private def b2359_6 : PackedIndexTree := .leaf
  0x36081c1b5540f9ec198a80e0d0484f2a8024570056106e100913606884122034f4630061207030492900fc
private def b2359_7 : PackedIndexTree := .leaf
  0x1516612804ad0150630d5e21f0cd6d09e930c6420984c01a60552c003d210146f0650d9e4338a03c53832270
private def b2359_5 : PackedIndexTree := .node 1 b2359_6 b2359_7
private def b2359_3 : PackedIndexTree := .node 1 b2359_4 b2359_5
private def b2359_9 : PackedIndexTree := .leaf
  0x1f862072cc0b430c44256423712d850feab1265a0113e0336407a7840a6c84c274e41d21c314969112e06500
private def b2359_11 : PackedIndexTree := .leaf
  0x266367457807c304961820720715604224df036a411aa122b0fd510d49f12503cf6a918e0a07958009129b1
private def b2359_12 : PackedIndexTree := .leaf
  0xf39413aa84ca096724315d6913407adc6146f55b04105ee220d9700692aa110ea587a0d245123290f5a893c
private def b2359_10 : PackedIndexTree := .node 1 b2359_11 b2359_12
private def b2359_8 : PackedIndexTree := .node 1 b2359_9 b2359_10
private def b2359_2 : PackedIndexTree := .node 3 b2359_3 b2359_8
private def b2359_15 : PackedIndexTree := .leaf
  0xa1938e84e6203250a9c49aae2484c97460c1d41155c083f670867b416b51be160672a439798808a0d16e0a2
private def b2359_17 : PackedIndexTree := .leaf
  0x24d1db34878b831d0926646382884c61806d0254eb066b014a885b496c054566f6040dd941fb3c794cf6d850
private def b2359_18 : PackedIndexTree := .leaf
  0xb687446990977d0de9152f858b0406ae52199a01295a813b44fac6055aa1920b1d478c7d5904e6d49f7f0e6
private def b2359_16 : PackedIndexTree := .node 1 b2359_17 b2359_18
private def b2359_14 : PackedIndexTree := .node 1 b2359_15 b2359_16
private def b2359_20 : PackedIndexTree := .leaf
  0x8c8d243375c42ba153fe5c51aad35a7e461275a4f9a99400aae8646781ed6202db3c404d7e98a3973273075
private def b2359_22 : PackedIndexTree := .leaf
  0x2132b65a7a9458b0d545a7d29ac43de544faa563c299d9105870e12da87e422b818972873cc55a2d708115f2
private def b2359_23 : PackedIndexTree := .leaf
  0xd36e915296523b294a8d3d8902743a7557ebc69b0d4dade5e187085c95670610da022b487c6d836dc21706b
private def b2359_21 : PackedIndexTree := .node 1 b2359_22 b2359_23
private def b2359_19 : PackedIndexTree := .node 1 b2359_20 b2359_21
private def b2359_13 : PackedIndexTree := .node 3 b2359_14 b2359_19
private def b2359_1 : PackedIndexTree := .node 6 b2359_2 b2359_13
private def b2359_27 : PackedIndexTree := .leaf
  0x3384ee222f0cb9cd0daea4a6968c4d57607edd41b2455eb467b057bc89b5970169c12ae080ee5920b407a62a
private def b2359_29 : PackedIndexTree := .leaf
  0x9bae4e29268a4ce1a5d505ac94cbd3036768421d6e05ed56ff1c1660665b3e761e720629149b928e003aa51
private def b2359_30 : PackedIndexTree := .leaf
  0xb2865039814aac59ba091c4aed35b71a15eaa8142ebb1957587fcf5666df14145fe93ce9cd9d02ea2142e68
private def b2359_28 : PackedIndexTree := .node 1 b2359_29 b2359_30
private def b2359_26 : PackedIndexTree := .node 1 b2359_27 b2359_28
private def b2359_32 : PackedIndexTree := .leaf
  0x2af5263046a815aec83ef1950aa9ba9930b67a75565c484f6b3547f6e439dce1df3587cb9999f68e24738689
private def b2359_34 : PackedIndexTree := .leaf
  0xd79fd19b1a56a62a75042bba5129e563b01aac45fbb897c62f33734b7c28479948ed31f58d8df71a172c65e
private def b2359_35 : PackedIndexTree := .leaf
  0x11729ec53ba55a593f89a77446bec3da9a417a08ee172f2856da2c274a7cc8db6a35179c52be0c9774451e2e
private def b2359_33 : PackedIndexTree := .node 1 b2359_34 b2359_35
private def b2359_31 : PackedIndexTree := .node 1 b2359_32 b2359_33
private def b2359_25 : PackedIndexTree := .node 3 b2359_26 b2359_31
private def b2359_38 : PackedIndexTree := .leaf
  0x22b6ee0294cedcea952fa2543e6caf5a7a3937b7d79c9ab6be3076848bd2572b65c3c805d82a5bd09dc7ae2d
private def b2359_40 : PackedIndexTree := .leaf
  0x2ee65f3f7671614f58804eb74b3988cbd9aabb8f24ba357741f2553ab5bd99fa1ad75c71e16e09bc1da20f41
private def b2359_41 : PackedIndexTree := .leaf
  0x232a0d1db2b1ba72ab0beed75d676bb15d59ffb9b37744bb9a7508e8e3a2e1b98ab3536f547a855beccc7607
private def b2359_39 : PackedIndexTree := .node 1 b2359_40 b2359_41
private def b2359_37 : PackedIndexTree := .node 1 b2359_38 b2359_39
private def b2359_44 : PackedIndexTree := .leaf
  0x292b8d7dcaafcc2c8fd363771e0e97f468c51bb269a50eeb9eec2c4dadd557eb95cfcb267d39f78e4b39854b
private def b2359_45 : PackedIndexTree := .leaf
  0x28fc9eb7be573c860bbcb437775c3be9789e6eafe915ef29be9a3d2edbc885f835ded162fb1e57a6513b05ab
private def b2359_43 : PackedIndexTree := .node 1 b2359_44 b2359_45
private def b2359_47 : PackedIndexTree := .leaf
  0x2fed3e33b2e9d6bf57b9f2ed463b98d1fb369ebbf17d65d39af528f54fbde87b3b1fbc5dbd6a03cecbf9b63e
private def b2359_48 : PackedIndexTree := .leaf
  0xd7effcbe9fd4ecfd6e3fbcf5d9befbc8ddfd7a93caefd83f47a6ec35ff2d
private def b2359_46 : PackedIndexTree := .node 1 b2359_47 b2359_48
private def b2359_42 : PackedIndexTree := .node 2 b2359_43 b2359_46
private def b2359_36 : PackedIndexTree := .node 3 b2359_37 b2359_42
private def b2359_24 : PackedIndexTree := .node 6 b2359_25 b2359_36
private def b2359_0 : PackedIndexTree := .node 12 b2359_1 b2359_24

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout2359 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![8, 1, 3, 2, 1, 0, 1])
    1024 35 b2359_0

private def b2371_5 : PackedIndexTree := .leaf
  0x3084a12c062040304323c02706206103054031034198002c003c0c8004780020d84800209001830018060000
private def b2371_6 : PackedIndexTree := .leaf
  0x1b41215c009610370402422426c0684200149100c9e8630488060901c06049201a3f09200e1820c23c008360
private def b2371_4 : PackedIndexTree := .node 1 b2371_5 b2371_6
private def b2371_8 : PackedIndexTree := .leaf
  0x3341e4840286f0324363c8006670a03023c29c0c807a00a329820381b2aa03e3d83c4330a807000c681209e4
private def b2371_9 : PackedIndexTree := .leaf
  0x4430d2e066062801e12a16609409d024150314c50697883e0ccb682780c95118c4204c0632600681a980aa4
private def b2371_7 : PackedIndexTree := .node 1 b2371_8 b2371_9
private def b2371_3 : PackedIndexTree := .node 2 b2371_4 b2371_7
private def b2371_12 : PackedIndexTree := .leaf
  0x1109280f129370966140633f83c809362498b40109f030c195900f4254f040a3641309689c9c81d10e0c492c
private def b2371_13 : PackedIndexTree := .leaf
  0x7c006cda1ea1a9090ac31a3f2039441a81249240e9ec1c460d8e05024c3c560011128d85f83103f4390b4185
private def b2371_11 : PackedIndexTree := .node 1 b2371_12 b2371_13
private def b2371_15 : PackedIndexTree := .leaf
  0x8421283a3d057402cd222848a521850de3d29e02608263248d5e00d36424469422618101c80e156021123125
private def b2371_17 : PackedIndexTree := .leaf
  0x288c181d1e51b69d1551940fc1250c3da572339a42682a40f0393091baab0d1081486f70881e6362e0068954
private def b2371_18 : PackedIndexTree := .leaf
  0x54de865a640dcba182839410f28cf2a90face0861427b20b0f1b7c160335391513241c5e610000f140d0b70
private def b2371_16 : PackedIndexTree := .node 1 b2371_17 b2371_18
private def b2371_14 : PackedIndexTree := .node 1 b2371_15 b2371_16
private def b2371_10 : PackedIndexTree := .node 2 b2371_11 b2371_14
private def b2371_2 : PackedIndexTree := .node 4 b2371_3 b2371_10
private def b2371_22 : PackedIndexTree := .leaf
  0x6d49509f1095b00a45637931d02036b284243f0993c933adb05026206c505819d054c9c6201910f685085134
private def b2371_23 : PackedIndexTree := .leaf
  0x5902712f36927afe0199cc4043b151c3c2e0635992114a4098989c015431d30c3006a1ad023c61f4a94cdb34
private def b2371_21 : PackedIndexTree := .node 1 b2371_22 b2371_23
private def b2371_25 : PackedIndexTree := .leaf
  0x466f0f925d85858033b221ec805e1816520d984d3314a24ed6a0253947d0548ea87462d9205825cea1e28f9
private def b2371_26 : PackedIndexTree := .leaf
  0x5a2c48731f15005a8c3854114c847a92b588054dd36513296dfa42a6287f8e4b981d25b21c88c49c4b5f42d2
private def b2371_24 : PackedIndexTree := .node 1 b2371_25 b2371_26
private def b2371_20 : PackedIndexTree := .node 2 b2371_21 b2371_24
private def b2371_29 : PackedIndexTree := .leaf
  0x6227edca0e5514ad0b49aa11292df211803e7ba341b97105718f4290a47f479a8c58404cd60966c68c126bf2
private def b2371_30 : PackedIndexTree := .leaf
  0x636f515f00f513160d4893458531870423dae4871a7c5642198e85144049df11b65822546b35084c569f8844
private def b2371_28 : PackedIndexTree := .node 1 b2371_29 b2371_30
private def b2371_32 : PackedIndexTree := .leaf
  0x57a6cda63821a69b0ab4230ecbc186841722f48d32b110ad0115247228529f09b53d6e105c0d54f509427159
private def b2371_34 : PackedIndexTree := .leaf
  0x3ce2d13b3812aa65a0804b0ea868823d1577150d2b4a6e88a53503e292c2cec0df55c9e62404d106871ef112
private def b2371_35 : PackedIndexTree := .leaf
  0x4eaaae2217832a1fd9d10e432f6c1737e16433da4a692a6bb01e873418f38812ad8a468d9e37228cf7488ae0
private def b2371_33 : PackedIndexTree := .node 1 b2371_34 b2371_35
private def b2371_31 : PackedIndexTree := .node 1 b2371_32 b2371_33
private def b2371_27 : PackedIndexTree := .node 2 b2371_28 b2371_31
private def b2371_19 : PackedIndexTree := .node 4 b2371_20 b2371_27
private def b2371_1 : PackedIndexTree := .node 9 b2371_2 b2371_19
private def b2371_40 : PackedIndexTree := .leaf
  0x33edb85133921a50d6e02d3a4df458a73819108c9b2c42c4d9d83cd203144522666e2516002ea60e0ecea20a
private def b2371_41 : PackedIndexTree := .leaf
  0x6da28531bfc8640dd031d1740a9cba3368828552b10b26ab68159c415cded32c0a8681bd74b2a1fc825e5a98
private def b2371_39 : PackedIndexTree := .node 1 b2371_40 b2371_41
private def b2371_43 : PackedIndexTree := .leaf
  0x64d0c42d205754f1c7da945942799ab6b4709549fbfa39cb64568ee87c5c8c7c090b8ca509bac1fa4cd661c2
private def b2371_44 : PackedIndexTree := .leaf
  0x8762399285925eea5f51be592275ac25f85c589fc9cd406e7076a9287a5c599a537d8b58139f68e070455964
private def b2371_42 : PackedIndexTree := .node 1 b2371_43 b2371_44
private def b2371_38 : PackedIndexTree := .node 2 b2371_39 b2371_42
private def b2371_47 : PackedIndexTree := .leaf
  0x11a8c92791c7d2b4e361bd3e6e314142d0ac585918f758c05d48c606ce26d1a3f65aac58e59f57343ad4216e
private def b2371_48 : PackedIndexTree := .leaf
  0x35a25da92317e611989b961cead94096b0aa22d123e6234b16351bb6a8e28af3f5856be18a9ff51ce64b69ae
private def b2371_46 : PackedIndexTree := .node 1 b2371_47 b2371_48
private def b2371_50 : PackedIndexTree := .leaf
  0x70c2e86bb5184e56d7a04572af5945ab58b46ada222e29cf948c9ef8d22f13f3892bb0618f853444a3561c5c
private def b2371_52 : PackedIndexTree := .leaf
  0x296b90ed3851729ee0a44a09e879dc3d557ed3a2ca2d4dc5357930f086771c9a7d56713043b4222c885f19b7
private def b2371_53 : PackedIndexTree := .leaf
  0x696dd535c045dc0fd071d955e5f19f44943af7c89ae216cd35c1a6d2af0483baf120cf4e2b1a76ecd0515915
private def b2371_51 : PackedIndexTree := .node 1 b2371_52 b2371_53
private def b2371_49 : PackedIndexTree := .node 1 b2371_50 b2371_51
private def b2371_45 : PackedIndexTree := .node 2 b2371_46 b2371_49
private def b2371_37 : PackedIndexTree := .node 4 b2371_38 b2371_45
private def b2371_57 : PackedIndexTree := .leaf
  0x21eb7817c786fe2ce072ed65c835d93cf206a72298a667adcca3c023acb845aa7788c5e8cbc11436ed082c55
private def b2371_58 : PackedIndexTree := .leaf
  0x656eb87face532dbc51a3c7fcb74e9ba22ed03621b2d42e4ddd89c614a99e1b4015d675505ba4535114bcb3b
private def b2371_56 : PackedIndexTree := .node 1 b2371_57 b2371_58
private def b2371_60 : PackedIndexTree := .leaf
  0x6b48e5fd9cf73c3be1f9730baeb5f72cd8e470dae1667fb0cd03a967425d59ba3a4aeb6e3a1c515f02e1a85e
private def b2371_61 : PackedIndexTree := .leaf
  0x5f4c5dcda852de23c8f3eb8dc6fdc735985e58d7e39d5271891b3ed5ae7de38a862cac9c2dbab52ab2e3209f
private def b2371_59 : PackedIndexTree := .node 1 b2371_60 b2371_61
private def b2371_55 : PackedIndexTree := .node 2 b2371_56 b2371_59
private def b2371_64 : PackedIndexTree := .leaf
  0x6a6bd823b9756ed1912be72371ac5f35571657e0d2f951f178d7a3323b1b5c6a8383815d132c76ad1851abf7
private def b2371_65 : PackedIndexTree := .leaf
  0x3b65fa0ac4b43eee5a7a6f5e677626b4322eb99c38bb82cbd5dd3d78b6d151794f3bc2f53fc4e83288dde45d
private def b2371_63 : PackedIndexTree := .node 1 b2371_64 b2371_65
private def b2371_67 : PackedIndexTree := .leaf
  0x5368f96fc7981ecbdd9a9d14f00cebba688e5eddac7a80abbd07a9e2facfd71c7c16f04ddb1078aedde032e5
private def b2371_69 : PackedIndexTree := .leaf
  0x23f1bdc7c1e5fb18d1ba878cad6d7f39f7df1cdae96752f1991dc750beebd67b5e47affdd19778ec71e1bba5
private def b2371_70 : PackedIndexTree := .leaf
  0x8feefe0faff8ced7e3ba3f74f1ed4fc7d76f01cbfc7e5cf05ddd9df89eef57bb4717f06ddf45f83a89dabafb
private def b2371_68 : PackedIndexTree := .node 1 b2371_69 b2371_70
private def b2371_66 : PackedIndexTree := .node 1 b2371_67 b2371_68
private def b2371_62 : PackedIndexTree := .node 2 b2371_63 b2371_66
private def b2371_54 : PackedIndexTree := .node 4 b2371_55 b2371_62
private def b2371_36 : PackedIndexTree := .node 9 b2371_37 b2371_54
private def b2371_0 : PackedIndexTree := .node 18 b2371_1 b2371_36

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout2371 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![5, 1, 3, 2, 1, 1, 1])
    2048 32 b2371_0

private def b2394_5 : PackedIndexTree := .leaf
  0x150030410210a0480420c8044104121400d0108080e008822000900050008500040903003000810008020000
private def b2394_6 : PackedIndexTree := .leaf
  0x142340151a000a4102482c29028838006182290251c00303a0260c20c2240b00c40124203103010219005180
private def b2394_4 : PackedIndexTree := .node 1 b2394_5 b2394_6
private def b2394_8 : PackedIndexTree := .leaf
  0x1305a0218cc04c044a10e12201a8f003808a5104486c024620710b008c050808e41148001485825000c46102
private def b2394_9 : PackedIndexTree := .leaf
  0x646a00688321819828982068484a80aa4401e04280e308324118ac0a4720910f010c0942a14124832920069
private def b2394_7 : PackedIndexTree := .node 1 b2394_8 b2394_9
private def b2394_3 : PackedIndexTree := .node 2 b2394_4 b2394_7
private def b2394_12 : PackedIndexTree := .leaf
  0x14c244e10742c2068c80ea4c02e06284e388070848631d8249040312c44c063065016250c0964214a00548d8
private def b2394_13 : PackedIndexTree := .leaf
  0x1f04144720405a170a48a32583492407134401cb810614a12c6a1c105c064d214a5803a48c0723d01346194c
private def b2394_11 : PackedIndexTree := .node 1 b2394_12 b2394_13
private def b2394_15 : PackedIndexTree := .leaf
  0x8e6c00a9461ca22c8a2010dc164f218a078c00949581648a046816206630730d14040ac5a1a10b4740952a0
private def b2394_17 : PackedIndexTree := .leaf
  0x4d033413856286730931114841ac7a1e11348401c96a5c04e0a28ce4881b40989c31238cb61125102c4f103a
private def b2394_18 : PackedIndexTree := .leaf
  0x30a439420ad0a6370e48362466b0a92c81e28883d0873e0154c3125196551208ae132890e507c6805a4cc0f2
private def b2394_16 : PackedIndexTree := .node 1 b2394_17 b2394_18
private def b2394_14 : PackedIndexTree := .node 1 b2394_15 b2394_16
private def b2394_10 : PackedIndexTree := .node 2 b2394_11 b2394_14
private def b2394_2 : PackedIndexTree := .node 4 b2394_3 b2394_10
private def b2394_22 : PackedIndexTree := .leaf
  0x328a04770d94c8828198bc7006a4ec132550434338963068301a9662a2a085593444236928079354c8007978
private def b2394_23 : PackedIndexTree := .leaf
  0x2e89848d2901727a9b004f3707140e94e5883b44991c4121d8b19ec324c2098a6217431d1809538c5940f10b
private def b2394_21 : PackedIndexTree := .node 1 b2394_22 b2394_23
private def b2394_25 : PackedIndexTree := .leaf
  0x20e9c06aa0605e6942f14b3a8b0497119548928398fc7807a50c1725d0534538d63869303a81b34c645610eb
private def b2394_26 : PackedIndexTree := .leaf
  0x16a16cf31d107cc08959b4542569680f9454e80479f840a174c730425a34cae24916c68d161d26905c5510fa
private def b2394_24 : PackedIndexTree := .node 1 b2394_25 b2394_26
private def b2394_20 : PackedIndexTree := .node 2 b2394_21 b2394_24
private def b2394_29 : PackedIndexTree := .leaf
  0x7106c57113a28eac08aa460de7944f18b4280f58096e2b2b91450b327900114a58364ca00b98d1ce45901a8c
private def b2394_30 : PackedIndexTree := .leaf
  0x2ac90d660f51368990887e6845acfa2e1334c409ca6a7c033d1c24513a739a216d226671448f63c69b10903b
private def b2394_28 : PackedIndexTree := .node 1 b2394_29 b2394_30
private def b2394_32 : PackedIndexTree := .leaf
  0x5589483dbc83e2c88bd1875e0555430af44a378e5a540fad04d7199648b287997c8809a54c1f26d015ce6927
private def b2394_34 : PackedIndexTree := .leaf
  0x41a59ccb2836184d46da664a22f9c11ab468c84ed3502f2aaa1010f4f0a146ea0e06ee10d69533b8b249b223
private def b2394_35 : PackedIndexTree := .leaf
  0x2ec98d7629217702118b6237471d9801f32ab1877a6523c82d4a0bd7027b8ecb646144ccde2a95b08c9d4097
private def b2394_33 : PackedIndexTree := .node 1 b2394_34 b2394_35
private def b2394_31 : PackedIndexTree := .node 1 b2394_32 b2394_33
private def b2394_27 : PackedIndexTree := .node 2 b2394_28 b2394_31
private def b2394_19 : PackedIndexTree := .node 4 b2394_20 b2394_27
private def b2394_1 : PackedIndexTree := .node 9 b2394_2 b2394_19
private def b2394_40 : PackedIndexTree := .leaf
  0x7d035d269a73acb0da6175236a99488fe7847ad3a361434e40dcaea8c053d5c2c523a9383bbc43da64d0e309
private def b2394_41 : PackedIndexTree := .leaf
  0x4b8d24db2a3658b487dc484e2e88fd2076e017ceab0625ea94af24b5a83f5e0a2e432e91a51733f8ba58c272
private def b2394_39 : PackedIndexTree := .node 1 b2394_40 b2394_41
private def b2394_43 : PackedIndexTree := .leaf
  0x6b0aca1411751a79d0b03f606e30da95b5ccb449f402456ad1d0a5a7a07e59518f5f0c14aea8e16f011169d3
private def b2394_44 : PackedIndexTree := .leaf
  0x8889b509a9c7127d971b6c6244ed58be247491dd809f42ad18b7ae533ca2d8a13d8029b92cbe47146cd1e329
private def b2394_42 : PackedIndexTree := .node 1 b2394_43 b2394_44
private def b2394_38 : PackedIndexTree := .node 2 b2394_39 b2394_42
private def b2394_47 : PackedIndexTree := .leaf
  0x3e69f1b4b985e51a0abacd44e9583fb437987d4cdb266225fa2126b5e8f854d410472da8e7b3868a675670f7
private def b2394_48 : PackedIndexTree := .leaf
  0x70a7758713755a94d6e3c946cc8dd63522f6bc61127a50efc06fa5570c6bd929de596d50bec4155ca66123ca
private def b2394_46 : PackedIndexTree := .node 1 b2394_47 b2394_48
private def b2394_50 : PackedIndexTree := .leaf
  0x7286f5772d98c902919abc752f619919761a99d4b0bf7070311a9db6ccd44df2ab6690856d4504f2ea907b78
private def b2394_52 : PackedIndexTree := .leaf
  0x6e91858d2b97d493ddc3c543ad38bbaed526c7204a766c6fb1c91bb6631895d2c786047d4abc63ded950f30b
private def b2394_53 : PackedIndexTree := .leaf
  0x60f1c0afad580c8bdd2a5e696f50feb2e63312939afc7d3061b91d769aa9d6b0ff7871313aa1b74ce44ff2eb
private def b2394_51 : PackedIndexTree := .node 1 b2394_52 b2394_53
private def b2394_49 : PackedIndexTree := .node 1 b2394_50 b2394_51
private def b2394_45 : PackedIndexTree := .node 2 b2394_46 b2394_49
private def b2394_37 : PackedIndexTree := .node 4 b2394_38 b2394_45
private def b2394_57 : PackedIndexTree := .leaf
  0x71ab9d8b13f806ad52dbe67a28f995bb46b4be61528f7f10152eb8e36ecb569b5c892ad9d1c2c7a47edb8afa
private def b2394_58 : PackedIndexTree := .leaf
  0x88aa75e71f76dac4dce2f67c71b20923b762ce9a399f62b11937be553ce2e0a23d6dcd6559b3c853161d9217
private def b2394_56 : PackedIndexTree := .node 1 b2394_57 b2394_58
private def b2394_60 : PackedIndexTree := .leaf
  0x3bed5557c255bcf2e2a27d75ce6579b7c8d2fc92bbcd64ed58bfc435eaa6e134114fcdadfa39a6731a967c38
private def b2394_61 : PackedIndexTree := .leaf
  0x666ef21929781ad9dcb1bf66ab6e3345157ceae1a3da6f2c3e3c2dd81c8ddd6b537b8cda11c524f6fc5bd387
private def b2394_59 : PackedIndexTree := .node 1 b2394_60 b2394_61
private def b2394_55 : PackedIndexTree := .node 2 b2394_56 b2394_59
private def b2394_64 : PackedIndexTree := .leaf
  0x74ef58ffb75636bf9f5c74834ee5a7b1d89c9ddf6b93838dda31abb862ee9e3a1f72abbe32b1e816af5f73d9
private def b2394_65 : PackedIndexTree := .leaf
  0x82c8fddab5b67d0ae2d3f971ed755bc2d7a7171db2fb8e2fea03a5f7aacbdaf44b5fb0ba0cb737f91c96bc4d
private def b2394_63 : PackedIndexTree := .node 1 b2394_64 b2394_65
private def b2394_67 : PackedIndexTree := .leaf
  0x6fafce3e35784f1593fbf5736dfa35c3979ee757bc6d826fd99dc3a88ea7e0ab6f73ccf6374597670f18bbe7
private def b2394_69 : PackedIndexTree := .leaf
  0x5ff1d60dbfe89f075bbc76776c7df7c1e77b0cdcbc6757f0d5edbbe8f303deeb378a70d9bdc7a5bf155d7bde
private def b2394_70 : PackedIndexTree := .leaf
  0x8ff0fe2fbff8ef07ddfc378f6f7e3ec576ff1f9fbc3b73f1be1ec1767f16e1f45d76efedafc2f8bcff639bd7
private def b2394_68 : PackedIndexTree := .node 1 b2394_69 b2394_70
private def b2394_66 : PackedIndexTree := .node 1 b2394_67 b2394_68
private def b2394_62 : PackedIndexTree := .node 2 b2394_63 b2394_66
private def b2394_54 : PackedIndexTree := .node 4 b2394_55 b2394_62
private def b2394_36 : PackedIndexTree := .node 9 b2394_37 b2394_54
private def b2394_0 : PackedIndexTree := .node 18 b2394_1 b2394_36

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout2394 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![17, 1, 3, 0, 1, 1, 1])
    2048 32 b2394_0

private def b2401_4 : PackedIndexTree := .leaf
  0x5310921e0380180d330401840e48094188480209c040313c0640c8181b001300340083c24004030600c000
private def b2401_6 : PackedIndexTree := .leaf
  0x441941249033064f2360981984c1b41a4b0a03046e60054050353d003308a81a0360703d3f0702443e54024
private def b2401_7 : PackedIndexTree := .leaf
  0xcd1e98c0e8201050003d21339e02d07425442550630a04902522420c82587c2744a5700a044d03c49e6c084
private def b2401_5 : PackedIndexTree := .node 1 b2401_6 b2401_7
private def b2401_3 : PackedIndexTree := .node 1 b2401_4 b2401_5
private def b2401_9 : PackedIndexTree := .leaf
  0x164a037074f6370fd2a9bc1a8501c41e4c03f544253fa10390a43147261093160790e552099383e007318ac
private def b2401_11 : PackedIndexTree := .leaf
  0x1981195819c2c135264301b4b4da7b09a200a1139601bd81154154ba40450d43d4a26d0c3220a91a58215968
private def b2401_12 : PackedIndexTree := .leaf
  0x18825c5c1f5560a93c12d5d02d0a870ca2c0d11f99027db12144557a705110404d25349e43ccb8364996c886
private def b2401_10 : PackedIndexTree := .node 1 b2401_11 b2401_12
private def b2401_8 : PackedIndexTree := .node 1 b2401_9 b2401_10
private def b2401_2 : PackedIndexTree := .node 3 b2401_3 b2401_8
private def b2401_15 : PackedIndexTree := .leaf
  0x5a5b07b6343b0853a930fa381012b9c033de12d47563aa05d0224d0435542940a1448ce8424c9788b672076
private def b2401_17 : PackedIndexTree := .leaf
  0x27c4a91007d31379f03fe11394a56fad06905259073614594ca4454d1809d393e612399f8299b831c8c2b586
private def b2401_18 : PackedIndexTree := .leaf
  0x241454d57bb0075082650a36d48958a7460d4815d6905d29909168a0d67a0f72f0dd6d88a670ab6f46b1456a
private def b2401_16 : PackedIndexTree := .node 1 b2401_17 b2401_18
private def b2401_14 : PackedIndexTree := .node 1 b2401_15 b2401_16
private def b2401_20 : PackedIndexTree := .leaf
  0xb964aa46cd7821d9911d599c82d51a5841a1849cec435e62e9cc36ded26c8166aac5682e5004f5850e8812f
private def b2401_22 : PackedIndexTree := .leaf
  0x176a2136921574702b4f6163a9fc42e1d32cb172adc6285e5c07f6453e9415f9c5454161ecc2042c9c434de5
private def b2401_23 : PackedIndexTree := .leaf
  0x13b934fb385fac31ba239a02bdc15ba8063ea15d4234d64e8d0e27d103854e970ad478da82ddc91dd89a885d
private def b2401_21 : PackedIndexTree := .node 1 b2401_22 b2401_23
private def b2401_19 : PackedIndexTree := .node 1 b2401_20 b2401_21
private def b2401_13 : PackedIndexTree := .node 3 b2401_14 b2401_19
private def b2401_1 : PackedIndexTree := .node 6 b2401_2 b2401_13
private def b2401_27 : PackedIndexTree := .leaf
  0x19eac1bfb45a514d659fa6444a244ce45465f2c1213760e77e4a76e6d2235a6ae1669e1875305b5b64646a2c
private def b2401_29 : PackedIndexTree := .leaf
  0x1639d54988b3490e0845e2935de9c08bd75ae865aa86dd7c22d9d9d94a9716b9f52b4462acf1ea2f9d037df1
private def b2401_30 : PackedIndexTree := .leaf
  0x3323b606c61c6b61e76b0bb736a65ea8c66ead56c2f5065a868ee8010f885ceb81efc05d520d95aba9450a54
private def b2401_28 : PackedIndexTree := .node 1 b2401_29 b2401_30
private def b2401_26 : PackedIndexTree := .node 1 b2401_27 b2401_28
private def b2401_32 : PackedIndexTree := .leaf
  0x2d66aabc72edd62c5f5c68a9291e8c13f945fec421fcc6052cdc5b7ac45ca8464ea55e6529ce3851e5941e19
private def b2401_34 : PackedIndexTree := .leaf
  0x2ba9e94e9816fa062ed024f8d4e37d70ebd1a2ad1c3b55a9a0aa39a177a25379251d8db487db0885ddc3adfd
private def b2401_35 : PackedIndexTree := .leaf
  0x25e9fe6544e25cfb2474ae47cf05766b2b4e9869eb959e795366689b3891e0c46e2dc19dabb1fbc35bb23da1
private def b2401_33 : PackedIndexTree := .node 1 b2401_34 b2401_35
private def b2401_31 : PackedIndexTree := .node 1 b2401_32 b2401_33
private def b2401_25 : PackedIndexTree := .node 3 b2401_26 b2401_31
private def b2401_38 : PackedIndexTree := .leaf
  0x255d5202c5223cd609b8b03b21d7ba597aa57da5a569de3c52e5dcda0ac722bcf5eb2fdd1baaaa5fa9067eb1
private def b2401_40 : PackedIndexTree := .leaf
  0x2858cb4494e39c4b33be207c65c7b65adb1a86a9e6c5ee8d8eb4c96e1b3be01c6ada6bac073ee1a3aafa5543
private def b2401_41 : PackedIndexTree := .leaf
  0x30fbd5a3ad662a0e69d0b288df497df09776f6adad7a71abaf66aa2e4b47e31d2b0a77af07ff11afadfb1573
private def b2401_39 : PackedIndexTree := .node 1 b2401_40 b2401_41
private def b2401_37 : PackedIndexTree := .node 1 b2401_38 b2401_39
private def b2401_44 : PackedIndexTree := .leaf
  0x17fa463ed425fc7b3fc95d3b9692ace99d626789f3983726b9b07b31dbbb69aaee7b53e61cea0ec822fd06ee
private def b2401_45 : PackedIndexTree := .leaf
  0x313be6c7a1e6dd1b2c8ef4dbeb1bb6dafb066ea3f4ed5603c56c2b8ec9a5e578f756c5b37bf20bc76cabaeab
private def b2401_43 : PackedIndexTree := .node 1 b2401_44 b2401_45
private def b2401_47 : PackedIndexTree := .leaf
  0x351bfb1fa4f52d6727b9ecda6f5acee0fc86cebbe63c8b43ca6f7ade9dd726bcab4bc2ddfbc69eafe33d16f2
private def b2401_48 : PackedIndexTree := .leaf
  0xd7f2fbff53d6ecfc8f5dcae9fd7af3d1f2dbee6fcbb4fb0f57c5efdb2e3f
private def b2401_46 : PackedIndexTree := .node 1 b2401_47 b2401_48
private def b2401_42 : PackedIndexTree := .node 2 b2401_43 b2401_46
private def b2401_36 : PackedIndexTree := .node 3 b2401_37 b2401_42
private def b2401_24 : PackedIndexTree := .node 6 b2401_25 b2401_36
private def b2401_0 : PackedIndexTree := .node 12 b2401_1 b2401_24

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout2401 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![17, 0, 3, 2, 0, 1, 1])
    1024 35 b2401_0

end D5.S3.Arith.ErdosNicolas.Data.RankReadouts00
