/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Data/RankReadouts02
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

namespace D5.S3.Arith.ErdosNicolas.Data.RankReadouts02

private def b3419_5 : PackedIndexTree := .leaf
  0x8c601b0da48c6c0040c1780378c10480189600d1861e00058001e184660630304800086c00630006060000
private def b3419_7 : PackedIndexTree := .leaf
  0x6606212084ea803c80925e006c08e40201b2630623d81ec01ccd06060c091380c83032001919e4844200c8cc
private def b3419_8 : PackedIndexTree := .leaf
  0x348371f824860243b0001f3643480507863c30c1e3c2510380cca4c309260251b601c31d2d12078c0c47201c
private def b3419_6 : PackedIndexTree := .node 1 b3419_7 b3419_8
private def b3419_4 : PackedIndexTree := .node 1 b3419_5 b3419_6
private def b3419_10 : PackedIndexTree := .leaf
  0x39c0986fa723243289c3de3061247e482068d20069a04b219986244ab042815276036338c3b1a3c12181c0f1
private def b3419_12 : PackedIndexTree := .leaf
  0x2902066a6000ac64933cc6098601b9ca1d4088483361b6639238547b4a82a30f83629900499c960189843c1
private def b3419_13 : PackedIndexTree := .leaf
  0x934131b060604a6e0082710fcc9064a5cae0488213c8902a38198e633ecc92918a3f1279218502126f2a10f4
private def b3419_11 : PackedIndexTree := .node 1 b3419_12 b3419_13
private def b3419_9 : PackedIndexTree := .node 1 b3419_10 b3419_11
private def b3419_3 : PackedIndexTree := .node 3 b3419_4 b3419_9
private def b3419_16 : PackedIndexTree := .leaf
  0x494ae2af3032207253e6020426d06a4c80f4635900c57b279a4603e7883dd451aa1c4541fb19b49c18583914
private def b3419_18 : PackedIndexTree := .leaf
  0x242f1cea55a2180b2100e54f00746833127cf90c4b1cc6013cf11029100e85454169c3cc099a64be1b1f9312
private def b3419_19 : PackedIndexTree := .leaf
  0x7af0ce80285122599e0e14e8652c413a49a169f0185932a9825d4c1fd210dbb4a4d403cd121096c96c3430e
private def b3419_17 : PackedIndexTree := .node 1 b3419_18 b3419_19
private def b3419_15 : PackedIndexTree := .node 1 b3419_16 b3419_17
private def b3419_22 : PackedIndexTree := .leaf
  0x1246959c0dd320fc4ff4a4492159ee10f54470aa40fa2d1806071b31a69980587963e4b2593d20c8c29bc61e
private def b3419_23 : PackedIndexTree := .leaf
  0x61a46a502450a5565b310bc180acdf54402c9dc4240a65433d312d0aecc6c943ce3c321d4a61a072730764e0
private def b3419_21 : PackedIndexTree := .node 1 b3419_22 b3419_23
private def b3419_25 : PackedIndexTree := .leaf
  0x4e6e9144ce4e6200c9b261964e5ef9ecae5248920447950e07ec835200d4743492acff0d0b344a9920339fa
private def b3419_26 : PackedIndexTree := .leaf
  0x7218d82abdb3d1238202a115d51daa0f95186b2d01524ca1c9fc19d4a12c55f063ac8c248b49c39ed8941608
private def b3419_24 : PackedIndexTree := .node 1 b3419_25 b3419_26
private def b3419_20 : PackedIndexTree := .node 2 b3419_21 b3419_24
private def b3419_14 : PackedIndexTree := .node 3 b3419_15 b3419_20
private def b3419_2 : PackedIndexTree := .node 6 b3419_3 b3419_14
private def b3419_30 : PackedIndexTree := .leaf
  0x2a6a204a16978984373f462849d5d3cd3b558182912c33098e58eb4fd810118911accdca24ca7d41f0c7b22
private def b3419_32 : PackedIndexTree := .leaf
  0x79275aae02e51e272113421ce9e97458e66650129be63167e64faacc64146a91e420922a7c0aa37b50da80f5
private def b3419_33 : PackedIndexTree := .leaf
  0x49e171f145022b26d5404da9c401b096ec0f050dcb4c4d80473007f424c94994b84ba1a9885716fc48f12043
private def b3419_31 : PackedIndexTree := .node 1 b3419_32 b3419_33
private def b3419_29 : PackedIndexTree := .node 1 b3419_30 b3419_31
private def b3419_36 : PackedIndexTree := .leaf
  0x36a355344c95ac1eebe32125d2d1ea1e76f52354d62007ef14e94e6516260d5b3e1c6544cb3f740962a5513c
private def b3419_37 : PackedIndexTree := .leaf
  0x1523b9a795c9c50084a1a7674ea32706d7e680189ca64961615cd5f6d8447092a438952adc16a4fb80c45410
private def b3419_35 : PackedIndexTree := .node 1 b3419_36 b3419_37
private def b3419_39 : PackedIndexTree := .leaf
  0xa20756adb6821b838169c08428ba6a27910d031960d127eb49f29f2af0c74953d0c630f8f1903912a5b0e03b
private def b3419_40 : PackedIndexTree := .leaf
  0xc7816df09eeae9250232a71690eaa6b5a1ff215495a669656135bfe3468452b4b758992834d6a3f8c3c8e4a2
private def b3419_38 : PackedIndexTree := .node 1 b3419_39 b3419_40
private def b3419_34 : PackedIndexTree := .node 2 b3419_35 b3419_38
private def b3419_28 : PackedIndexTree := .node 3 b3419_29 b3419_34
private def b3419_43 : PackedIndexTree := .leaf
  0xe8fea3412d966b01e9865accc2c8c379c3f0b0e8b6450982814e7812e8a99e94a9a09d441195651625cb13b
private def b3419_45 : PackedIndexTree := .leaf
  0x5dc24eca33928d331f61913fee4a52ab2c7015dee9ea9213f9518b0387525ab0fb2d26ba07a1cb45308aa267
private def b3419_46 : PackedIndexTree := .leaf
  0x1586fea2b5202f99842c0b430cae5f2630e0b458b5777084a7152bc79e772b15d052b86c5142839a3b5404e1
private def b3419_44 : PackedIndexTree := .node 1 b3419_45 b3419_46
private def b3419_42 : PackedIndexTree := .node 1 b3419_43 b3419_44
private def b3419_49 : PackedIndexTree := .leaf
  0x3b10e67629113d091a20e92aeba9fea0ab20cd4a12557d19262b1fb237285576340a7550833672e93eb06c1a
private def b3419_50 : PackedIndexTree := .leaf
  0x6e445e4eaaaaa16f9b19705078260b1bb4529ba67adccc4206c121464e4d25d5283db5cdc049324b89822bcb
private def b3419_48 : PackedIndexTree := .node 1 b3419_49 b3419_50
private def b3419_52 : PackedIndexTree := .leaf
  0x7ad8de221e96f923d4e622083a4057b552c53a14689a35ad02d0bae2a795039bf940d632562510bcafe29565
private def b3419_53 : PackedIndexTree := .leaf
  0xdefd5013159514595d9dbac2db889e1438d09d1a5ba9b45b13fe051190486b945996b61f587dafcc8c98391
private def b3419_51 : PackedIndexTree := .node 1 b3419_52 b3419_53
private def b3419_47 : PackedIndexTree := .node 2 b3419_48 b3419_51
private def b3419_41 : PackedIndexTree := .node 3 b3419_42 b3419_47
private def b3419_27 : PackedIndexTree := .node 7 b3419_28 b3419_41
private def b3419_1 : PackedIndexTree := .node 13 b3419_2 b3419_27
private def b3419_58 : PackedIndexTree := .leaf
  0x65d63dce141c84b51f39f4af57a156e33175102a99e520b22d4c4f91576b1a895e9c9010d4a177552f565650
private def b3419_60 : PackedIndexTree := .leaf
  0x2b49b6006618dc84c99cb958d93035d6c622479bfd12c4b0c8ebd5d6d584017e7e13b08d183439ac9ec442e9
private def b3419_61 : PackedIndexTree := .leaf
  0x5e99e84cd9a458cfca64d232e816c5b989564f71f05d7c67c228c96a08aa45b43ca9ed708096f82a88ad434d
private def b3419_59 : PackedIndexTree := .node 1 b3419_60 b3419_61
private def b3419_57 : PackedIndexTree := .node 1 b3419_58 b3419_59
private def b3419_63 : PackedIndexTree := .leaf
  0x54a2c8e2d4b6b16e4b5e6c1170450f5a49889a43b2d78d55f5c512f96ab09ead68bacded4de2185c74d434e7
private def b3419_65 : PackedIndexTree := .leaf
  0x3bd0fee94f252f8745242a1de57671af0806256cb33b290ea5f764f8b8805ca4a75698e82cea86da5ea80613
private def b3419_66 : PackedIndexTree := .leaf
  0x8b15acfe91d946ac288d56b88da4bb4fcc1f070e0a2f9aab8b3408781a86996cc0a5cb4cf9d7970c4af163d1
private def b3419_64 : PackedIndexTree := .node 1 b3419_65 b3419_66
private def b3419_62 : PackedIndexTree := .node 1 b3419_63 b3419_64
private def b3419_56 : PackedIndexTree := .node 3 b3419_57 b3419_62
private def b3419_69 : PackedIndexTree := .leaf
  0xb08ca49b397a558f6251efaeae0a4ae2808fa585ac3b6b73b9498a068d69dda159cb4bb1ffa0cb2495d62e4b
private def b3419_71 : PackedIndexTree := .leaf
  0x43b68dd84c32ab9583abfb4111a65751c583152b3b742330b51d5c06ca5c942e0b8319e51594b9a2b7b32083
private def b3419_72 : PackedIndexTree := .leaf
  0xd0828e14a36b793714088e5df655d114799ab69f6d80bdce4d59e3988c7ae48a9e9ffa4858db26ae592751af
private def b3419_70 : PackedIndexTree := .node 1 b3419_71 b3419_72
private def b3419_68 : PackedIndexTree := .node 1 b3419_69 b3419_70
private def b3419_75 : PackedIndexTree := .leaf
  0x55f8d45e442aaa41cbacfb8362b6d73532c101b33c74432eb25faccca41c58bb85a318ad5e9ddac6dc2e8e16
private def b3419_76 : PackedIndexTree := .leaf
  0xb068549acbb5914a6b75dc70345313c343b33b57d68013f095193459b0bad05d9173c50f223e93ed15ef550a
private def b3419_74 : PackedIndexTree := .node 1 b3419_75 b3419_76
private def b3419_78 : PackedIndexTree := .leaf
  0xcf826ece34129cebf2ac6240f635cd4adc8017f574536e7419558b8aa2d7adf971ce505d125aa4deb7731c70
private def b3419_79 : PackedIndexTree := .leaf
  0xb94dbcbe502c2a71d1adbb9b65b73708d826882635345b31b2bfb8c262f5e22dd86faa7711c30d2258e74af6
private def b3419_77 : PackedIndexTree := .node 1 b3419_78 b3419_79
private def b3419_73 : PackedIndexTree := .node 2 b3419_74 b3419_77
private def b3419_67 : PackedIndexTree := .node 3 b3419_68 b3419_73
private def b3419_55 : PackedIndexTree := .node 6 b3419_56 b3419_67
private def b3419_83 : PackedIndexTree := .leaf
  0x73b4c321ad53eb5edc45e9c5da705dc41ba93d14c8a6b5aee8afce55e5016cc3ab5979462f203952ada8beaa
private def b3419_85 : PackedIndexTree := .leaf
  0x16f0f5aecf04476a5db15bcb90050746fa44b1f26c5aada47e89c33b8cdacbc61183d9fd18cd75c99a844b2f
private def b3419_86 : PackedIndexTree := .leaf
  0x98b9603bc6b71747961d696ed75f4542f47970943af5cf766d1694d9a6b82c35f47334b31fc4c3e325e82e98
private def b3419_84 : PackedIndexTree := .node 1 b3419_85 b3419_86
private def b3419_82 : PackedIndexTree := .node 1 b3419_83 b3419_84
private def b3419_89 : PackedIndexTree := .leaf
  0x3bf74e79e8614b0ad1c4de5e365dd21497df176f839556b8ee246a92f74074a0b3b68d64b366d8f487ed2bb2
private def b3419_90 : PackedIndexTree := .leaf
  0x142d1ddae5b5da836c9ba0c8dad22cdeca18ac45f557b8a5de7ec1db60b8f34c764373056752fbc4e1e8d62d
private def b3419_88 : PackedIndexTree := .node 1 b3419_89 b3419_90
private def b3419_92 : PackedIndexTree := .leaf
  0x76395e3220995f477584556eb4211ddc12e79d20ca26a74b7f32c72b0a4de95c4bbbce0f14c36d2f3bd7e682
private def b3419_93 : PackedIndexTree := .leaf
  0x75ab3729c60a33ab2e63712fd85f42a37b7b3773808f7474d96dd8171d7bf51447bb4a7f49db32cb3ad7c59e
private def b3419_91 : PackedIndexTree := .node 1 b3419_92 b3419_93
private def b3419_87 : PackedIndexTree := .node 2 b3419_88 b3419_91
private def b3419_81 : PackedIndexTree := .node 3 b3419_82 b3419_87
private def b3419_96 : PackedIndexTree := .leaf
  0xb56ee32f471a48b26b7ddda2b0d6e42fbd028ce6cae6bf4e7e996453ef7ae85e9e17b10e7b5af77858603c75
private def b3419_98 : PackedIndexTree := .leaf
  0xb965f681db6cdf1f110cc7a6b1b5c6d20bb3a3218a3e5ef9f6ce94f8c77d9cde4189dabe83e9a172d7f39a25
private def b3419_99 : PackedIndexTree := .leaf
  0x5fcedf2ea0fa47ada2dd0eb8e5e60fae5cd71e298de47138bf4edd59eba2053bbb5e7665d36ba8bf7c95beab
private def b3419_97 : PackedIndexTree := .node 1 b3419_98 b3419_99
private def b3419_95 : PackedIndexTree := .node 1 b3419_96 b3419_97
private def b3419_102 : PackedIndexTree := .leaf
  0xb9da1d1ccdf74b4e2f8ea4893a56da9678f6ecf2cc66a3fac9bbe8b47b70f3b53c5c361efad2d89b7834ccf1
private def b3419_103 : PackedIndexTree := .leaf
  0xd4776f472f9b3f196fc6b1a139d513d3b8e749aefc375fba0efe3a1c8fad6f6d0dd402fed8bbe8eeb3ef1d1b
private def b3419_101 : PackedIndexTree := .node 1 b3419_102 b3419_103
private def b3419_105 : PackedIndexTree := .leaf
  0xbe7a9adbc7da43a351fd3ebef13f4dbb9cbf4975c5c95cf7ee99de6d3f3dddeebc8c3ab6e697fce31fa9bb8f
private def b3419_106 : PackedIndexTree := .leaf
  0xd7f7ff53d3fd7379f5ec7fd1f7e693dfdd42eff5f5cfa73a9633eb3cef4f6f0affbfdade87c79bcba25d3ebb
private def b3419_104 : PackedIndexTree := .node 1 b3419_105 b3419_106
private def b3419_100 : PackedIndexTree := .node 2 b3419_101 b3419_104
private def b3419_94 : PackedIndexTree := .node 3 b3419_95 b3419_100
private def b3419_80 : PackedIndexTree := .node 7 b3419_81 b3419_94
private def b3419_54 : PackedIndexTree := .node 13 b3419_55 b3419_80
private def b3419_0 : PackedIndexTree := .node 27 b3419_1 b3419_54

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout3419 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![8, 7, 3, 2, 0, 0, 1])
    2048 32 b3419_0

private def b3436_5 : PackedIndexTree := .leaf
  0x2a8db0192a0020486d015c488240910187200d1261800032001e1240049c0960606c0010a800c4800c090000
private def b3436_7 : PackedIndexTree := .leaf
  0xa18a422d0080d88a8a582517400318c01a9d06048c2a4121e01304820383227c6c86c1210312700225806c
private def b3436_8 : PackedIndexTree := .leaf
  0x24a6083c5a4006fc0b04824e2de12403e1284995601c25ae50f05ac4e4184b40389c0941b089c25c6101239c
private def b3436_6 : PackedIndexTree := .node 1 b3436_7 b3436_8
private def b3436_4 : PackedIndexTree := .node 1 b3436_5 b3436_6
private def b3436_10 : PackedIndexTree := .leaf
  0x199261b415e368151233cc06a2489e24d9680698007072460544158c00dc01b4813789381eaa4288050784bc
private def b3436_12 : PackedIndexTree := .leaf
  0x3212c950ba80229e0370c492055ad0adc098db8aebc44c84d1085dc48aa884881233048c34510032a02d1391
private def b3436_13 : PackedIndexTree := .leaf
  0x3624c95c2433100a318139740024334b13d96e24427e0dab50ba0446cd3b0aa9b24b8db4545d40664ea1000a
private def b3436_11 : PackedIndexTree := .node 1 b3436_12 b3436_13
private def b3436_9 : PackedIndexTree := .node 1 b3436_10 b3436_11
private def b3436_3 : PackedIndexTree := .node 3 b3436_4 b3436_9
private def b3436_16 : PackedIndexTree := .leaf
  0x4b55002492a561748103c11f932098b9831c790425b001e9d9fe0651845b24727d9c8e112a04a660d94503c2
private def b3436_18 : PackedIndexTree := .leaf
  0x82d8d5409e2903d12ccc025261ae88266181f2d439e00e635fa2942c921b062755a4df06084291a720a9898
private def b3436_19 : PackedIndexTree := .leaf
  0xbd09465c2ae13a079821a425e1d1cb51c30a094f128cb5ce746c60494818dba16a8a00ea429c09c4b45293d8
private def b3436_17 : PackedIndexTree := .node 1 b3436_18 b3436_19
private def b3436_15 : PackedIndexTree := .node 1 b3436_16 b3436_17
private def b3436_22 : PackedIndexTree := .leaf
  0x1e46725f12755b451da01d5081ead33951a0fca4e1e12c56b574273370161bd6602d2929e803912c50270a1c
private def b3436_23 : PackedIndexTree := .leaf
  0x3f1710c18c8928a2ab80792b5695706020a0fc5b94f82c320de41be4d0851bc8b4bc09241faa628d0b04a816
private def b3436_21 : PackedIndexTree := .node 1 b3436_22 b3436_23
private def b3436_25 : PackedIndexTree := .leaf
  0x2f126944b6a9e0564db260c021599e371159761e703737a4fa122c449e6525b63c54a515813ac02a3c4394bd
private def b3436_26 : PackedIndexTree := .leaf
  0x78c99aa61b50aa4d9092bcbbc91c163cd2118d26a09327ae90cd06a96a7c2895bc036c05414080e2e4d6c0ce
private def b3436_24 : PackedIndexTree := .node 1 b3436_25 b3436_26
private def b3436_20 : PackedIndexTree := .node 2 b3436_21 b3436_24
private def b3436_14 : PackedIndexTree := .node 3 b3436_15 b3436_20
private def b3436_2 : PackedIndexTree := .node 6 b3436_3 b3436_14
private def b3436_30 : PackedIndexTree := .leaf
  0x3257758c2a33d0222da3aad2004ccca7a8001a463170a2324b0c281b473a16f38819a1399a4993a8da4af8a4
private def b3436_32 : PackedIndexTree := .leaf
  0x753228726104f21bd6b3802ed17062846922732771575ba97aa23e409adbd5a0aabacf14802658453309aa11
private def b3436_33 : PackedIndexTree := .leaf
  0x664f7022b6714453276a28be86cc7c25d988ae85498abaa0a98863227620210ba20174a0c8cb37f07b94c5ba
private def b3436_31 : PackedIndexTree := .node 1 b3436_32 b3436_33
private def b3436_29 : PackedIndexTree := .node 1 b3436_30 b3436_31
private def b3436_36 : PackedIndexTree := .leaf
  0x9944cd5cb9aa40624149e65218c4435b2742373043fe95019cf696e8a96e57a4894fe71273386cd8b54baa56
private def b3436_37 : PackedIndexTree := .leaf
  0x2cd6c57660e4ee171feb7ecc94106196d91ef50e509a9ca881c2d42bd895425b315650e050822786c207f1a8
private def b3436_35 : PackedIndexTree := .node 1 b3436_36 b3436_37
private def b3436_39 : PackedIndexTree := .leaf
  0x392aa8a54301323d92d9a0a8330895e4856374e8c30e7700847e87e9936a90239931e351fb4a052d5f0f2885
private def b3436_40 : PackedIndexTree := .leaf
  0xb9061c13b0d51d5d20a07db52e7d720dac0d299faa956ed14a7e16590e7093660d690b4d0c37d171791ed043
private def b3436_38 : PackedIndexTree := .node 1 b3436_39 b3436_40
private def b3436_34 : PackedIndexTree := .node 2 b3436_35 b3436_38
private def b3436_28 : PackedIndexTree := .node 3 b3436_29 b3436_34
private def b3436_43 : PackedIndexTree := .leaf
  0x94b989ba96b161145e903bab0704a14e3850879645ea4a6f665d114c80aa44f94960cec0d30f50ed304fe51e
private def b3436_45 : PackedIndexTree := .leaf
  0x33d7a5924b955e7d28b5c076da700fb0534aa1a0607572e348be51d93d890f1a8db5f3d1750d93758142d340
private def b3436_46 : PackedIndexTree := .leaf
  0x5c4e32340d10a4fcd9c49d3b13e8b1ae97949aaa81b90b2859bdac0cc22daf124b7a24331c42e9b025ca0a1d
private def b3436_44 : PackedIndexTree := .node 1 b3436_45 b3436_46
private def b3436_42 : PackedIndexTree := .node 1 b3436_43 b3436_44
private def b3436_49 : PackedIndexTree := .leaf
  0x84d3416321516a65af0b1cc7ca9ca388c85aebb4a017a683cccecbf8087eae30caa2aed64b572c38a143dda7
private def b3436_50 : PackedIndexTree := .leaf
  0xc29028399f95b45ea305c5193255459d0ae33c8ade785c298b01d4867cfa028b7315d3e6ed2347926fc82269
private def b3436_48 : PackedIndexTree := .node 1 b3436_49 b3436_50
private def b3436_52 : PackedIndexTree := .leaf
  0x9e28b2a75f836e9842bb3d57d11056dd905cf3d8a10ac6d3589fc2558ae9a9619596e7c94e63db7cc0dd68e8
private def b3436_53 : PackedIndexTree := .leaf
  0x115356db69274a66c704029581aec41f12e544e2c5bd5f186941c099d4e2b382d919e5e59b49b7c0759b58a6
private def b3436_51 : PackedIndexTree := .node 1 b3436_52 b3436_53
private def b3436_47 : PackedIndexTree := .node 2 b3436_48 b3436_51
private def b3436_41 : PackedIndexTree := .node 3 b3436_42 b3436_47
private def b3436_27 : PackedIndexTree := .node 7 b3436_28 b3436_41
private def b3436_1 : PackedIndexTree := .node 13 b3436_2 b3436_27
private def b3436_58 : PackedIndexTree := .leaf
  0xc32d5274adf448e26a35f07cc13d9a9d556d0f052bc720499cd654d99c4df2a21357b77e9231a05a424f5635
private def b3436_60 : PackedIndexTree := .leaf
  0xbaec49de10110508e66a08a5464d8cbfa535600f4889b6aead786911cd8493dc017059a22f50818e5c6499ce
private def b3436_61 : PackedIndexTree := .leaf
  0x8ad6ee802f6916394e36116999b96bb812ee2f22ebde08f590e694e9df0d1155f61f497ea2be598d9315a8ab
private def b3436_59 : PackedIndexTree := .node 1 b3436_60 b3436_61
private def b3436_57 : PackedIndexTree := .node 1 b3436_58 b3436_59
private def b3436_63 : PackedIndexTree := .leaf
  0x2319121d0a329a8a5851aabea3e662abb40148ae618bd500ad88a92c675e20c08174637a94e0a954fe4f7a99
private def b3436_65 : PackedIndexTree := .leaf
  0x9455fb141e752221ed9aee8e83770485e7fed1254e66a0c5be2aaf57ad570e2ce7444e1d6666dbdc95d99bdd
private def b3436_66 : PackedIndexTree := .leaf
  0x6ff9945d505bccf54e59108653704da2134550ef6b28c94ace1cd1a775a8011b091fe6a665c1040ce6c6b521
private def b3436_64 : PackedIndexTree := .node 1 b3436_65 b3436_66
private def b3436_62 : PackedIndexTree := .node 1 b3436_63 b3436_64
private def b3436_56 : PackedIndexTree := .node 3 b3436_57 b3436_62
private def b3436_69 : PackedIndexTree := .leaf
  0x34330cff649b9546587bb9aed8820b07fb568157346c1aafde50a973b95f67f167d08bb53760faa8d282ea1a
private def b3436_71 : PackedIndexTree := .leaf
  0xcf8b946de0768529df637716514e7ea38ab470d36b49854b290c8b9bcaf6d90116c84aaca5c31765a629c0f7
private def b3436_72 : PackedIndexTree := .leaf
  0xc75368a1c2943eb26f5d3064d2ec8a9f6c8370b4f30776269c7640e0ef650fe97ea3f192e4e2651f5d60acf6
private def b3436_70 : PackedIndexTree := .node 1 b3436_71 b3436_72
private def b3436_68 : PackedIndexTree := .node 1 b3436_69 b3436_70
private def b3436_75 : PackedIndexTree := .leaf
  0xa2f705dbafcd3b87943c0d71d9d2350d32facea4f9dac4b3d575a30aa57f0dd85b682b0b31c48162f4c87559
private def b3436_76 : PackedIndexTree := .leaf
  0x8d3529f50536727667dc4046cf2c8326baa334b2c2175822def1b1e21b8e44742f9b3a5a9b19f64b01ac61f5
private def b3436_74 : PackedIndexTree := .node 1 b3436_75 b3436_76
private def b3436_78 : PackedIndexTree := .leaf
  0x20b09e68ac74194b8cbeb463aa7b1fd8411aebf4a8eaa6b85a029fb8c571e860cb92e74ab9e1d6b19e971b8d
private def b3436_79 : PackedIndexTree := .leaf
  0x95d628f9a9d8b56fd7d0e9c2b02da86725b65ee30be2ad074679a2ecf37e931d4967efa72844615f76d1ab16
private def b3436_77 : PackedIndexTree := .node 1 b3436_78 b3436_79
private def b3436_73 : PackedIndexTree := .node 2 b3436_74 b3436_77
private def b3436_67 : PackedIndexTree := .node 3 b3436_68 b3436_73
private def b3436_55 : PackedIndexTree := .node 6 b3436_56 b3436_67
private def b3436_83 : PackedIndexTree := .leaf
  0xc37581ab4eb44ce2f38df266ef84eb91c87c29d169aea9f7e72b2bf88b49b5602f62a42f1bcd7838e9c7152d
private def b3436_85 : PackedIndexTree := .leaf
  0xbe2f9d9664e56f0f5df6a42066b667a0acab4958dd82c587ac45db75e5a4e3c0e18072b6c4e6aa145ce2caf9
private def b3436_86 : PackedIndexTree := .leaf
  0x405936e76aa626ef6bd41a10682695c707f6a6ec0d02d10bc473e1369ce0f348be8bf426b31cf6ab0d912d47
private def b3436_84 : PackedIndexTree := .node 1 b3436_85 b3436_86
private def b3436_82 : PackedIndexTree := .node 1 b3436_83 b3436_84
private def b3436_89 : PackedIndexTree := .leaf
  0xd538a949d79833a023b0dfc16d1a55c57a02bdd1e55e38ed356766f17af7c8d565c8c53e1aa2bbef4f07dcc7
private def b3436_90 : PackedIndexTree := .leaf
  0x94677abfe29d0cbbe3ad560bed1733d07898f5c8955d9bc88d66def65446722c3bd44c2cd5c12b3080691dcd
private def b3436_88 : PackedIndexTree := .node 1 b3436_89 b3436_90
private def b3436_92 : PackedIndexTree := .leaf
  0x5cf1b5f71dd9fe8eb42a6faaad2f2e21b17779d911118673774d53a346ca725d90a36eef50e2282281e370d7
private def b3436_93 : PackedIndexTree := .leaf
  0xc4f5b27ba32cfb7f9a1bed8942cd1cd5b856b2e996b864245f21bb3d323ba9cd963ff19ae5d77c4305dae67e
private def b3436_91 : PackedIndexTree := .node 1 b3436_92 b3436_93
private def b3436_87 : PackedIndexTree := .node 2 b3436_88 b3436_91
private def b3436_81 : PackedIndexTree := .node 3 b3436_82 b3436_87
private def b3436_96 : PackedIndexTree := .leaf
  0x5fb87dad38fceb1ad9d9db8848c6a9dfdcb4b0e24eb021f8ee6dd3164f638fbdc35fda7c76c0fb2b9d8bfc65
private def b3436_98 : PackedIndexTree := .leaf
  0xd6aa7ec2e8c1d785da9463a1b5a8e9b59cf752df5e528828dc83cd341d9675b31fb0c23f4bd378f901ec6d0e
private def b3436_99 : PackedIndexTree := .leaf
  0x65c4761fea635f95ece527d5b8ba0ec7a1c72bec5c5b5f7589a8e737c647ab4a2fbf794623eae62f07906d2f
private def b3436_97 : PackedIndexTree := .node 1 b3436_98 b3436_99
private def b3436_95 : PackedIndexTree := .node 1 b3436_96 b3436_97
private def b3436_102 : PackedIndexTree := .leaf
  0x40773f55d7b837a0a38d0347da25a78bfacf0de9f32dc9eeff52a0b8e560f16e8a5e71e735d0bac2d5d13df3
private def b3436_103 : PackedIndexTree := .leaf
  0x647a6e9dd91c46d7a379dfd0f55f2f44d22737d95d92d4704ecce2bd031dda3c4e47b57d67ebc23791e9ed9a
private def b3436_101 : PackedIndexTree := .node 1 b3436_102 b3436_103
private def b3436_105 : PackedIndexTree := .leaf
  0xca683f5bd87d1d1f687b5b88796f58c7eb1ebff3bd6d4677fe25eb2a67ae477d978cf5b9aee7f7de8ef2eeba
private def b3436_106 : PackedIndexTree := .leaf
  0xd7f67f47c7fd675bf5db5fcbf64e27ebdb37a0d1febea7f1cf45b2fd4f67717c7bac647ecf6af83fa35a9d6b
private def b3436_104 : PackedIndexTree := .node 1 b3436_105 b3436_106
private def b3436_100 : PackedIndexTree := .node 2 b3436_101 b3436_104
private def b3436_94 : PackedIndexTree := .node 3 b3436_95 b3436_100
private def b3436_80 : PackedIndexTree := .node 7 b3436_81 b3436_94
private def b3436_54 : PackedIndexTree := .node 13 b3436_55 b3436_80
private def b3436_0 : PackedIndexTree := .node 27 b3436_1 b3436_54

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout3436 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![5, 5, 3, 2, 0, 1, 1])
    2048 32 b3436_0

private def b3530_6 : PackedIndexTree := .leaf
  0x100323c00fc1840900c10182700c203418c12030003c0c40011b00020cc0602400040f000c1800300c0000
private def b3530_8 : PackedIndexTree := .leaf
  0x3f000512c2421b430c0f10060482a00d00f200d4800641bc24400e1501810d800833006c1820f424c0311e0
private def b3530_9 : PackedIndexTree := .leaf
  0x1ec30201c27403e3cc1b10c610803836000319009c1b20cd54012402427c0613040ce2100402411980620c8
private def b3530_7 : PackedIndexTree := .node 1 b3530_8 b3530_9
private def b3530_5 : PackedIndexTree := .node 1 b3530_6 b3530_7
private def b3530_12 : PackedIndexTree := .leaf
  0xf84200c325001a03515c27218d6001e40e401433c1210360783c418e2d010030125812218803d4b00940c5
private def b3530_13 : PackedIndexTree := .leaf
  0x48406824e3900331c03c13181e22480fd0125701540541852ac3c20910dc3340fe01948c0702711861c8092
private def b3530_11 : PackedIndexTree := .node 1 b3530_12 b3530_13
private def b3530_15 : PackedIndexTree := .leaf
  0x54c0091303312462881521b806d4e01833100da0f521c00a33204c24d6c02a41a406e0d43fc1e10f6011138
private def b3530_16 : PackedIndexTree := .leaf
  0x12830e0284500f328048104a0653d82a23081bd0d263021411404424536c00f48215119c0660a83f41be0d9
private def b3530_14 : PackedIndexTree := .node 1 b3530_15 b3530_16
private def b3530_10 : PackedIndexTree := .node 2 b3530_11 b3530_14
private def b3530_4 : PackedIndexTree := .node 3 b3530_5 b3530_10
private def b3530_20 : PackedIndexTree := .leaf
  0x21227812d0425a02430843d019a1b52dc0ca3f210c30d78036400726412e1940494bc0a02a11b60d11f8544
private def b3530_21 : PackedIndexTree := .leaf
  0x27d1926f02d41d409e10430542c0cf54221125c1260260411684b409827e19906360c0c91f03f1306020348
private def b3530_19 : PackedIndexTree := .node 1 b3530_20 b3530_21
private def b3530_23 : PackedIndexTree := .leaf
  0x3241ee25410901e57c0391603612761912b86041e83ce09d0e85101b334054110a12502503a49836207c3c8
private def b3530_24 : PackedIndexTree := .leaf
  0x2b04b107a3c60950e04082d23381ed10266030301d14449007425a27539c18a03f4b21cc3cd0968404240c7
private def b3530_22 : PackedIndexTree := .node 1 b3530_23 b3530_24
private def b3530_18 : PackedIndexTree := .node 2 b3530_19 b3530_22
private def b3530_27 : PackedIndexTree := .leaf
  0x48833d2527b039403729415e1c40793c54ec18f6022d131c1e60e610122801657415833e0582591236cc189
private def b3530_28 : PackedIndexTree := .leaf
  0xde63c0f92204213360502513786c401b2a848e15d1a80725d02730b44006011ca1e50e50fa55801542213c
private def b3530_26 : PackedIndexTree := .node 1 b3530_27 b3530_28
private def b3530_30 : PackedIndexTree := .leaf
  0xac3f82ad1c27203c30dd20455013431a33545c24a0ff57228c48d1560569000714e41873e42ae3141c9093
private def b3530_31 : PackedIndexTree := .leaf
  0x6924f6c23913dc2a61a61c12e80d66342183fe1183191e378c24937001357113a4861551a005506a4c8392
private def b3530_29 : PackedIndexTree := .node 1 b3530_30 b3530_31
private def b3530_25 : PackedIndexTree := .node 2 b3530_26 b3530_29
private def b3530_17 : PackedIndexTree := .node 4 b3530_18 b3530_25
private def b3530_3 : PackedIndexTree := .node 7 b3530_4 b3530_17
private def b3530_35 : PackedIndexTree := .leaf
  0x33304d1744c06c10a428a2a51a51ba06f6180d54e21fc5483fd31287002c4540f735421e28413948504e5ac
private def b3530_37 : PackedIndexTree := .leaf
  0x1310465a42474a436e0883d428915319e6fc1b92e04e10aa3f61103114387840db36854e21d00b268132690
private def b3530_38 : PackedIndexTree := .leaf
  0x11512a02a58804545216c4b836d2827e048319d0672c46101f43da0a93f551c30a1bf63234c54d2161169c0
private def b3530_36 : PackedIndexTree := .node 1 b3530_37 b3530_38
private def b3530_34 : PackedIndexTree := .node 1 b3530_35 b3530_36
private def b3530_41 : PackedIndexTree := .leaf
  0x12930f02978245149c3660802662813a81966f404b2d84be1d83d90a22a384c3094300d36311fa546215260
private def b3530_42 : PackedIndexTree := .leaf
  0x2258078116434a36526527a12f6d81955a22bc6084bd0863d29300a10ec5141b74142de3441f954510e66c
private def b3530_40 : PackedIndexTree := .node 1 b3530_41 b3530_42
private def b3530_44 : PackedIndexTree := .leaf
  0x14849434921325e7bc2793a00435a116a4b61d00853d109a4f884419b42860e2dd0cb3281f27503f310d234
private def b3530_45 : PackedIndexTree := .leaf
  0x5c54325d1273846d00272b449a1694b507e5dc3ca09927f6f240c60d2d61d6a801f110666430756402142e
private def b3530_43 : PackedIndexTree := .node 1 b3530_44 b3530_45
private def b3530_39 : PackedIndexTree := .node 2 b3530_40 b3530_43
private def b3530_33 : PackedIndexTree := .node 3 b3530_34 b3530_39
private def b3530_49 : PackedIndexTree := .leaf
  0x39857e03b29849916236390c07d3c94f01936f12ba6062d53201d51ea09f0ea64810551222c57842d3428a0
private def b3530_50 : PackedIndexTree := .leaf
  0x4929f01611ac0765d42774d439e0b84042b96051ce72c1e93cf0e984251155c4261403263414682567b410b
private def b3530_48 : PackedIndexTree := .node 1 b3530_49 b3530_50
private def b3530_52 : PackedIndexTree := .leaf
  0x25b4e86ce39d18b3e82b28104b31cd0972f40e264084122440a42532533a1ef79825566237c6c801f57d146
private def b3530_53 : PackedIndexTree := .leaf
  0xb402b11c672407b3c76240e14ee2085544092d331e87c33946010366122a57629014549115a05a5b8904075
private def b3530_51 : PackedIndexTree := .node 1 b3530_52 b3530_53
private def b3530_47 : PackedIndexTree := .node 2 b3530_48 b3530_51
private def b3530_56 : PackedIndexTree := .leaf
  0x6384ed0b640296011c60331d1e74447900e737455a22901757513e69c48a15933f0597b24cc6cd3960b0296
private def b3530_57 : PackedIndexTree := .leaf
  0x3168741cb45863e0fb3585592224239cc13d4890525b02537b137a6c63953e02952aa15f1aa7081c55d22ec
private def b3530_55 : PackedIndexTree := .node 1 b3530_56 b3530_57
private def b3530_59 : PackedIndexTree := .leaf
  0x552ab022126c13669433759405145e1784c43796c528e7ec2a948f1a99020735d161c4e62003e60b5401528
private def b3530_60 : PackedIndexTree := .leaf
  0x45d24b4a83728d008c57328d1573b41a27000579012e44ca4e53e50ae3fa2af85831572243c7880df63d206
private def b3530_58 : PackedIndexTree := .node 1 b3530_59 b3530_60
private def b3530_54 : PackedIndexTree := .node 2 b3530_55 b3530_58
private def b3530_46 : PackedIndexTree := .node 4 b3530_47 b3530_54
private def b3530_32 : PackedIndexTree := .node 7 b3530_33 b3530_46
private def b3530_2 : PackedIndexTree := .node 15 b3530_3 b3530_32
private def b3530_65 : PackedIndexTree := .leaf
  0x4876e41a15ae06b2c86144c93933de93c0ad3f95201c37212ea63635020555121a11a6789c413531b5a878e
private def b3530_67 : PackedIndexTree := .leaf
  0x3dd0a62a75048501a743461a2e90d76351fe75c54a2193ff11987202e58c78d456170356c003712867e413b
private def b3530_68 : PackedIndexTree := .leaf
  0x4e3a8c1fd54911267031387102d43a7864554a035536a21f26a7c82856923ac6f804f5ad1764c2a201dc6c3
private def b3530_66 : PackedIndexTree := .node 1 b3530_67 b3530_68
private def b3530_64 : PackedIndexTree := .node 1 b3530_65 b3530_66
private def b3530_71 : PackedIndexTree := .leaf
  0x58443978534e8ac36954f2699c21336916dc5a62c04a61754c108a5e83d69340a528b5186fe1bb4186192e2
private def b3530_72 : PackedIndexTree := .leaf
  0x3a458a0475a54a516e4ba36f9180893d57e24fc84819f6fd2c6612b702e132c1f67540ab3f765411151e238
private def b3530_70 : PackedIndexTree := .node 1 b3530_71 b3530_72
private def b3530_74 : PackedIndexTree := .leaf
  0x2837e13aa6f64102c56112da1da738a841f53db66884e51d30b56843299014c63334d2174742627c01179c1
private def b3530_75 : PackedIndexTree := .leaf
  0x9320a30ee64c84d516230416cc04313468a41fb5477a426166e12b3886d402b58945349e9fc16d4b90825e0
private def b3530_73 : PackedIndexTree := .node 1 b3530_74 b3530_75
private def b3530_69 : PackedIndexTree := .node 2 b3530_70 b3530_73
private def b3530_63 : PackedIndexTree := .node 3 b3530_64 b3530_69
private def b3530_79 : PackedIndexTree := .leaf
  0x34575246c7b810f66d236582ae029c78349d1663675c49100812674f46da3a91976f52be81c60a2d94bf1d9
private def b3530_80 : PackedIndexTree := .leaf
  0x9f416534b5d87be27b4d86d93a20bc5a3b4c2bd6091d27300873d39310ed4fa84651556041542a2df32a888
private def b3530_78 : PackedIndexTree := .node 1 b3530_79 b3530_80
private def b3530_82 : PackedIndexTree := .leaf
  0x81416b4b77141d15de09b2f86444f984540e96c42960f329a821f375179c66638056623502358114a6a8496
private def b3530_83 : PackedIndexTree := .leaf
  0x2d75343228801d7a8146464a10766556522e57a42f9d81494958a205e5bc90825f7bd3866d2c303a13ec2b6
private def b3530_81 : PackedIndexTree := .node 1 b3530_82 b3530_83
private def b3530_77 : PackedIndexTree := .node 2 b3530_78 b3530_81
private def b3530_86 : PackedIndexTree := .leaf
  0x22d5791426a03438a105d46a7b64d03856d139a29a7f8b442b549b72890e07f5dd3cb6284f2a5020c6f340d
private def b3530_87 : PackedIndexTree := .leaf
  0x6ca39957f2999f21631ae70c90d5d62f04d64f10ba4069642bb60786432172e1eb4487940eb64951355eabc
private def b3530_85 : PackedIndexTree := .node 1 b3530_86 b3530_87
private def b3530_89 : PackedIndexTree := .leaf
  0x39f3ea9480b940581252c8781cf72d2f6642ba035c84355d2264276849d01413275b479a4692577b537e8dc
private def b3530_90 : PackedIndexTree := .leaf
  0x768556ab422540b69887e33b59879946217c663c0c37d6c92927f01474939f11ad5ba9060775d56204d54ea
private def b3530_88 : PackedIndexTree := .node 1 b3530_89 b3530_90
private def b3530_84 : PackedIndexTree := .node 2 b3530_85 b3530_88
private def b3530_76 : PackedIndexTree := .node 4 b3530_77 b3530_84
private def b3530_62 : PackedIndexTree := .node 7 b3530_63 b3530_76
private def b3530_94 : PackedIndexTree := .leaf
  0x8d422b5777d429169e15b3b870405b5b99054cea2c4e96cf3e90b2b422b381185c7264406262f50e364120a
private def b3530_96 : PackedIndexTree := .leaf
  0x5f43e29400b1297b4152470a1c77256252ee63a4efa9820955596211e67c9c831f87d446792cf04614ac376
private def b3530_97 : PackedIndexTree := .leaf
  0x2027600b740396111d52a87659044579145a35a8b8c0437555b7e89ce13f69d48b6e85b2b102cc7b34cd397
private def b3530_95 : PackedIndexTree := .node 1 b3530_96 b3530_97
private def b3530_93 : PackedIndexTree := .node 1 b3530_94 b3530_95
private def b3530_100 : PackedIndexTree := .leaf
  0x359ab222326e7cc9cd6963b05960535b117a4c6a2437b6c79243e17ee2ab5088541ab7095d361eb7c2ed639
private def b3530_101 : PackedIndexTree := .leaf
  0x4c58d208e5ec93828f7ed3b6702c6041c90361d2e64e7744a902013e767485a52931787543e99c78a45963f
private def b3530_99 : PackedIndexTree := .node 1 b3530_100 b3530_101
private def b3530_103 : PackedIndexTree := .leaf
  0x75893e0af3fb65885952223c723ccc43d7893528b0207553ab126d67a9c61376956e05955aa45f4aaa08179
private def b3530_104 : PackedIndexTree := .leaf
  0x21b4787c411b6799c558eaec5a978f4a9172c023738d191c08d7e65006e63b51a37012ca828616b742e54cb
private def b3530_102 : PackedIndexTree := .node 1 b3530_103 b3530_104
private def b3530_98 : PackedIndexTree := .node 2 b3530_99 b3530_102
private def b3530_92 : PackedIndexTree := .node 3 b3530_93 b3530_98
private def b3530_108 : PackedIndexTree := .leaf
  0xc015e47ca2877e56e53ae6fa5afb582c9615a221de73ca883df93d50685252156c4369942eb63789435175e
private def b3530_109 : PackedIndexTree := .leaf
  0x9360a765050585151a41a978cc443561b8a8a8e1ff75d54b7a8672bd038c87302f58d4576b44a2a00171357
private def b3530_107 : PackedIndexTree := .node 1 b3530_108 b3530_109
private def b3530_111 : PackedIndexTree := .leaf
  0x47065611367123a586ae443b7879e44a18ae36b5c891426b7c96936dec3c3ad6f92c28201774c3a211dd5ea
private def b3530_112 : PackedIndexTree := .leaf
  0x7c2d204dc9c36dd3a65a7804b502c14a773491a08b5e93d79354fea5c84a5196ff419b722e332e88ca8d756
private def b3530_110 : PackedIndexTree := .node 1 b3530_111 b3530_112
private def b3530_106 : PackedIndexTree := .node 2 b3530_107 b3530_110
private def b3530_115 : PackedIndexTree := .leaf
  0x2fc7e34fd8494129702c7613b7132d73aa861f77557a065566a51f56aac823958599214e6ac9f834f8ad476
private def b3530_116 : PackedIndexTree := .leaf
  0xbac66984f569232cc24339919dc14d8a65c07a64752637c138a8e86d6c343a558b8189fe16f4bb7189195e2
private def b3530_114 : PackedIndexTree := .node 1 b3530_115 b3530_116
private def b3530_118 : PackedIndexTree := .leaf
  0x66fc183896d5ae229e7fcb4849f9fd5c69120835e162c4f6a543ab6f795441181e2db5388841db739a8564e
private def b3530_119 : PackedIndexTree := .leaf
  0x4f56db0be968b4e2bf81d60b868732c9044c9330ef64d517774562ac0231417cc16a488a3478a57a546e7ba
private def b3530_117 : PackedIndexTree := .node 1 b3530_118 b3530_119
private def b3530_113 : PackedIndexTree := .node 2 b3530_114 b3530_117
private def b3530_105 : PackedIndexTree := .node 4 b3530_106 b3530_113
private def b3530_91 : PackedIndexTree := .node 7 b3530_92 b3530_105
private def b3530_61 : PackedIndexTree := .node 15 b3530_62 b3530_91
private def b3530_1 : PackedIndexTree := .node 30 b3530_2 b3530_61
private def b3530_125 : PackedIndexTree := .leaf
  0x847aa456196e42b6889d432b88975379ecfc46d7b93828e0237583ae129d6aa9f61677105c59115da4daa38
private def b3530_127 : PackedIndexTree := .leaf
  0x3815677f49da14b6a94979f55beb1c90a5d97bf4d9c323a33ee94c0bdb4d8165307161d37312fa646ba44fb
private def b3530_128 : PackedIndexTree := .leaf
  0xc313ed7fab462b781586071572a5df62ab882f9645a5220e76cab840f96d53688259ca8379d4666678c4c10
private def b3530_126 : PackedIndexTree := .node 1 b3530_127 b3530_128
private def b3530_124 : PackedIndexTree := .node 1 b3530_125 b3530_126
private def b3530_131 : PackedIndexTree := .leaf
  0x20d96668086653532388144a9a8796cf446564b8d8abe22f57b7d89d96a23bc8a305f5bd9094d2a303876d3
private def b3530_132 : PackedIndexTree := .leaf
  0x55fabd6869d21436a16ec5b6b1446b7b7a144d18de39b5f894429b7f9b4570ec6c72990f6292f24f3a51a9c
private def b3530_130 : PackedIndexTree := .node 1 b3530_131 b3530_132
private def b3530_134 : PackedIndexTree := .leaf
  0x9287f2d5050c9f31af70d5d7834622b802f14d776494a0bb40796586552e87a72fcd8449795ba235e8bcc08
private def b3530_135 : PackedIndexTree := .leaf
  0x3eb94981385e52d8794429a02f7643ba135d76aab62277d06859d169a59aaf85b579b17ea28c0e37f8dd6cb
private def b3530_133 : PackedIndexTree := .node 1 b3530_134 b3530_135
private def b3530_129 : PackedIndexTree := .node 2 b3530_130 b3530_133
private def b3530_123 : PackedIndexTree := .node 3 b3530_124 b3530_129
private def b3530_139 : PackedIndexTree := .leaf
  0xab567ebdc9ca69987f599cf24634aea0c17dc0d8d65f07d62937f13ba706c645bb907b64621a2e4eb748a94
private def b3530_140 : PackedIndexTree := .leaf
  0x7ea69f6eac483b9705b122ce82cb784cfa2d5f69420b365cb4385d526727984cd04416278b4a9a20b769557
private def b3530_138 : PackedIndexTree := .node 1 b3530_139 b3530_140
private def b3530_142 : PackedIndexTree := .leaf
  0x50aa6885652570b998b7e2ef63b898a9976247c96311f67d9c9592af0447793cf14ad8bac063778d59207d5
private def b3530_143 : PackedIndexTree := .leaf
  0x676bd452b877ad459199e45b6b8a0435b8b9c057ced2c7e99cf6e93b25b3b11b5c2cda267409265f53e3941
private def b3530_141 : PackedIndexTree := .node 1 b3530_142 b3530_143
private def b3530_137 : PackedIndexTree := .node 2 b3530_138 b3530_141
private def b3530_146 : PackedIndexTree := .leaf
  0x7cd6978f46e2c403b1597824a0a17b4c7a259255ee93a7ef509855c6241e97ccc861fb7d746a922037617ac
private def b3530_147 : PackedIndexTree := .leaf
  0x939502a603b7703c6141d82ab762e7890745a9175a65abb867585b23eae8cce43f99d78b9e88b25ccab326f
private def b3530_145 : PackedIndexTree := .node 1 b3530_146 b3530_147
private def b3530_149 : PackedIndexTree := .leaf
  0x93f65952356eacc23dccd9966b08963538b147a7c6d2467b9c7c246e1aee5ab808b544aba098d391e08f5ed
private def b3530_150 : PackedIndexTree := .leaf
  0x4797c5bd238e8ecc3858faed6b6a0217371cc0391d5e67e7a445016e7974b5a2cb829617b7573ec9ca8a759
private def b3530_148 : PackedIndexTree := .node 1 b3530_149 b3530_150
private def b3530_144 : PackedIndexTree := .node 2 b3530_145 b3530_148
private def b3530_136 : PackedIndexTree := .node 4 b3530_137 b3530_144
private def b3530_122 : PackedIndexTree := .node 7 b3530_123 b3530_136
private def b3530_154 : PackedIndexTree := .leaf
  0x5e57cba58c3e3af6fb958b5982253ca231df73da89652bb050785356d97acc64379959e08958aa75f7aad08
private def b3530_156 : PackedIndexTree := .leaf
  0x5eb937b94651a5e51b778ac441b979cc588e8a9a8f7a9472673bd1c1c38dae68009e66b54a3a015cab28916
private def b3530_157 : PackedIndexTree := .leaf
  0x7579b47a2d004716578e4aca23b587ae59e56ae9fa8af5c9915d224dea3c6dfc3d806b522c382186c736c94
private def b3530_155 : PackedIndexTree := .node 1 b3530_156 b3530_157
private def b3530_153 : PackedIndexTree := .node 1 b3530_154 b3530_155
private def b3530_160 : PackedIndexTree := .leaf
  0x9f95c2b204777c3d214dd8eac363a7950805b5181a71ac7873591b2feba84ffa5d84baa897268cb7332f88d
private def b3530_161 : PackedIndexTree := .leaf
  0xb4a8199ff7195e362eb8c2fda5677095641397153a88673ba87ce47a1bae66b8c8c1456bac99939de14f6ad
private def b3530_159 : PackedIndexTree := .node 1 b3530_160 b3530_161
private def b3530_163 : PackedIndexTree := .leaf
  0x81f86a539885c9244e9accf864fbad776ac22337dccc39dd6a68a7b045c17a7a34c1a38b8e96d7c357fed5c
private def b3530_164 : PackedIndexTree := .leaf
  0xac168abe89d66a588bb18cfe46f7bba18c198e25fcae329f7fdb49712c705c791362da3a4f7a55aa095596a
private def b3530_162 : PackedIndexTree := .node 1 b3530_163 b3530_164
private def b3530_158 : PackedIndexTree := .node 2 b3530_159 b3530_162
private def b3530_152 : PackedIndexTree := .node 3 b3530_153 b3530_158
private def b3530_168 : PackedIndexTree := .leaf
  0x8e192c7f6d546ab9f7c54711b1e5db838b844dba3994e0bf969b4f869532733c91cdc44dba68c0aa6775563
private def b3530_169 : PackedIndexTree := .leaf
  0xb68a3274cc333ef94d817a748625317179a4b8a2fb647ba5aa576eaba96f6899d559eafc79fcfd8c6c12383
private def b3530_167 : PackedIndexTree := .node 1 b3530_168 b3530_169
private def b3530_171 : PackedIndexTree := .leaf
  0xcd462bb89a53a9e20f76dab9682be053788359d9aacf6467a108c5c118da7dad387f59db3bec685bfb1d90b
private def b3530_172 : PackedIndexTree := .leaf
  0x867af4cda44b9a9797cf58bec0a8d9abf7d96a36eec4c3bdb16830a164d3a315fa9467fbb47861c6e72b988
private def b3530_170 : PackedIndexTree := .node 1 b3530_171 b3530_172
private def b3530_166 : PackedIndexTree := .node 2 b3530_167 b3530_170
private def b3530_175 : PackedIndexTree := .leaf
  0x7d2d306879d36edafa5b7b15b60a15a2a8df92a5f9945d5250ea6c70fc6d836b822f389ca9d766967bc4681
private def b3530_176 : PackedIndexTree := .leaf
  0xa29c0f9295f27f3d5150dc66980b66835623b8174aca8a9676594bbd852f87bad8cd99a26bcba335f8bdc09
private def b3530_174 : PackedIndexTree := .node 1 b3530_175 b3530_176
private def b3530_178 : PackedIndexTree := .leaf
  0x707c65b6582eb7aa2f749a9565ebbc85f986cd24439a19ec8b676bab7d147d1bde69b8f8c4459baf9a0e17f
private def b3530_179 : PackedIndexTree := .leaf
  0x65da6a527ad0985cd199a89a8b5a9b47ed2867fbdd9cbc28af280ccf34afa0d8d7b349225f17d7a64c4a3bb
private def b3530_177 : PackedIndexTree := .node 1 b3530_178 b3530_179
private def b3530_173 : PackedIndexTree := .node 2 b3530_174 b3530_177
private def b3530_165 : PackedIndexTree := .node 4 b3530_166 b3530_173
private def b3530_151 : PackedIndexTree := .node 7 b3530_152 b3530_165
private def b3530_121 : PackedIndexTree := .node 15 b3530_122 b3530_151
private def b3530_184 : PackedIndexTree := .leaf
  0x8997637aed0c47dbd68f0ad6593af16baa068bbc07921d2e7eba486ebc49b13b5e2cf82db79742ca05f7943
private def b3530_186 : PackedIndexTree := .leaf
  0xc20ad5aea99f9ea6b9a055ceb2c7cfd2d8f6c423b395cb5d826a27c84741927bb450ba6985797ecca999b7f
private def b3530_187 : PackedIndexTree := .leaf
  0x5cdd26a40c268f56e3c4180ad68b56825a0bc985ef93bb98a6277cc6341f97dcc9892747a937adbba677bd5
private def b3530_185 : PackedIndexTree := .node 1 b3530_186 b3530_187
private def b3530_183 : PackedIndexTree := .node 1 b3530_184 b3530_185
private def b3530_190 : PackedIndexTree := .leaf
  0x8eec3aaef809b5571ec7c91fa46503a61aac97682bb77891c9e75b9b8d0465bbb9ace23fae9ccf9e96b28b3
private def b3530_191 : PackedIndexTree := .leaf
  0x71db2a5e7b90a45a5a95a975b5b53e73fc9da8bce8bb28cc56facd997bf49e26b1897b24d0a47b7c7d25c25
private def b3530_189 : PackedIndexTree := .node 1 b3530_190 b3530_191
private def b3530_193 : PackedIndexTree := .leaf
  0xa59c3f95982386e53dc969b0b96653bb177aac697bcc79e18abb087abd09bd3c1e38f8edc39802d606b7a03
private def b3530_194 : PackedIndexTree := .leaf
  0x86dc7a737c95ce0b95baaa5faaa779ac568ebec88f9b6d02473a1cc1d8e6ae7d448019e7c745cbb29917a3e
private def b3530_192 : PackedIndexTree := .node 1 b3530_193 b3530_194
private def b3530_188 : PackedIndexTree := .node 2 b3530_189 b3530_192
private def b3530_182 : PackedIndexTree := .node 3 b3530_183 b3530_188
private def b3530_198 : PackedIndexTree := .leaf
  0xc79b8e2ffba9aa977297368db00ce69b57a3d018cac168e5acbd586af9fbc58b2283cd234dfa3d952807b53
private def b3530_199 : PackedIndexTree := .leaf
  0xa57cb4aa2771957be453b887ce59aecfabaf8c9c157ded3c9dfb065c3b21b6ca368ebc37951d5e81ba7871b
private def b3530_197 : PackedIndexTree := .node 1 b3530_198 b3530_199
private def b3530_201 : PackedIndexTree := .leaf
  0xaa196bbc886bc93cde44f9adcf98c2777ac37ddbea6a7c50b05b1aa1aa35c1b5fe7ffd5db4bc7298c62fb8d
private def b3530_202 : PackedIndexTree := .leaf
  0xcac94fa76533adccdd9a6ba78c1aa7d3468bbe99d7afeb19cffa198e392e5fdd56a70c56713c7183ab86a3b
private def b3530_200 : PackedIndexTree := .node 1 b3530_201 b3530_202
private def b3530_196 : PackedIndexTree := .node 2 b3530_197 b3530_200
private def b3530_205 : PackedIndexTree := .leaf
  0x74dbc0a7586398acd69a5b8b76fabbd18be28fc59fafda128c7c1392dd3a7f7d55c55c6ab1fb6a839b8574e
private def b3530_206 : PackedIndexTree := .leaf
  0x831a17ca45fb947a6ec6f989cd589ea9fbc6683be1c2caf69abcf7a118dbb387dbd39c4e3bfc69b69832a33
private def b3530_204 : PackedIndexTree := .node 1 b3530_205 b3530_206
private def b3530_208 : PackedIndexTree := .leaf
  0xb61a2bc8892bd5350fa6d982837b8389dcaa767d10bc5bdaadaaf5cdb6be8bfc0bd32a4c6efc4db17d74b62
private def b3530_209 : PackedIndexTree := .leaf
  0xc2a8f9c4580ed6ca0fb365f3b9ca66c67981b6774bca9a97bbebd9ad99a39ee6bdb30d167d3d318fac46afb
private def b3530_207 : PackedIndexTree := .node 1 b3530_208 b3530_209
private def b3530_203 : PackedIndexTree := .node 2 b3530_204 b3530_207
private def b3530_195 : PackedIndexTree := .node 4 b3530_196 b3530_203
private def b3530_181 : PackedIndexTree := .node 7 b3530_182 b3530_195
private def b3530_213 : PackedIndexTree := .leaf
  0xbf889bd0e47fd29c298f2af380dc80b35923a4aa65c4b82fb7bca29bc65fbbdad2987cd39ed8b7d15d2abdf
private def b3530_215 : PackedIndexTree := .leaf
  0xc9ab9abb577e97fccbb0c7afd0dbd7c228f1ad7d646bba07b2ed2fa4995eb5fc86743ca1cecbb6a6bad199b
private def b3530_216 : PackedIndexTree := .leaf
  0xa41c2780bd69b57c7ec99b99a63aae77dbf08939bad06bbbc21aebd489eb5cfb2da428f7c4395dd6a827c85
private def b3530_214 : PackedIndexTree := .node 1 b3530_215 b3530_216
private def b3530_212 : PackedIndexTree := .node 1 b3530_213 b3530_214
private def b3530_219 : PackedIndexTree := .leaf
  0xbb38cdd40bf59e3b0ab25d0b8efc3bd62a7c71fc7db92a47aad977c9fcea9b9d058ceacfbf66b3c5cb26d27
private def b3530_220 : PackedIndexTree := .leaf
  0xd5ac5ac7583ea3fbcc86fc97ce29b1b9777bac7beeb09a1ec1fd46803d61c76b2bb91a5bcb895b53fce99b2
private def b3530_218 : PackedIndexTree := .node 1 b3530_219 b3530_220
private def b3530_222 : PackedIndexTree := .leaf
  0xcb6773d1cbe6b01ce78cbc17d3ed59c59b23b6e83dcb0953a7ac7bce1babaab68fbedb029b7d03a1d8e7d45
private def b3530_223 : PackedIndexTree := .leaf
  0xcdf8c3d36bebc51b1bd78a1b5ffa72c7398dcb5aa3bcabe59afcfbb3c7dfd3dc52b07b6da37d5fa7998eb8f
private def b3530_221 : PackedIndexTree := .node 1 b3530_222 b3530_223
private def b3530_217 : PackedIndexTree := .node 2 b3530_218 b3530_221
private def b3530_211 : PackedIndexTree := .node 3 b3530_212 b3530_217
private def b3530_227 : PackedIndexTree := .leaf
  0xbe3c2e8fdd70a13b3ad3bc6bb6b74fcadbc2a77add9a7d1ad358feaffc8c92fd57a71c5783bb87caebc9ade
private def b3530_228 : PackedIndexTree := .leaf
  0xcabd11bdbadb6bfb32d33a4dd75b63c8aca5a6fbfc89fd12bc7c2daf7b39a4ec4fd76833ca6bc198bcd7d19
private def b3530_226 : PackedIndexTree := .node 1 b3530_227 b3530_228
private def b3530_230 : PackedIndexTree := .leaf
  0x8f3d66c81a4bca3cee9bdad3bfad2bc2b80fd6dc82b37b9da679bebbfd4c9efb31d178fbc47d6ec89b9e983
private def b3530_231 : PackedIndexTree := .leaf
  0xc5db27a7ec7faafbf19bbd07d49c5ea43d6bc9bb9b77fbf2b0dc23d4ad65b2fcbc95fc87cedbb7bf9b0ed0f
private def b3530_229 : PackedIndexTree := .node 1 b3530_230 b3530_231
private def b3530_225 : PackedIndexTree := .node 2 b3530_226 b3530_229
private def b3530_234 : PackedIndexTree := .leaf
  0xb6fcb1a7bd1eb03d5bc5b83fcb2bcdce3befd7ca1fd47c77cb9bce9b3d41b0bd63a7db93cbaceb8cfd42bf7
private def b3530_235 : PackedIndexTree := .leaf
  0xd13a4fd77ca7bfec2fd71b3bbc3d1b8ffd72c8dcafadfd37d79c8ea73bcbb3dc53d7a98fcb7d1dbe7b3ed3f
private def b3530_233 : PackedIndexTree := .node 1 b3530_234 b3530_235
private def b3530_237 : PackedIndexTree := .leaf
  0xc8fd7bb3fd1fcb3d7dbcfd7ecbbd43a7fc5fbf3d4bcbdb0fd67cbecefbfbc839bfd4dd6fb9fd4eb33c8bbfd
private def b3530_238 : PackedIndexTree := .leaf
  0xd7fcbfd4fbffd73
private def b3530_236 : PackedIndexTree := .node 1 b3530_237 b3530_238
private def b3530_232 : PackedIndexTree := .node 2 b3530_233 b3530_236
private def b3530_224 : PackedIndexTree := .node 4 b3530_225 b3530_232
private def b3530_210 : PackedIndexTree := .node 7 b3530_211 b3530_224
private def b3530_180 : PackedIndexTree := .node 15 b3530_181 b3530_210
private def b3530_120 : PackedIndexTree := .node 30 b3530_121 b3530_180
private def b3530_0 : PackedIndexTree := .node 60 b3530_1 b3530_120

/-- Exact packed readout for this complete sorted upper-corner divisor sequence. -/
def rankReadout3530 : ℕ → ℕ :=
  indexedPackedReadout (exponentFactors boxPrimes ![17, 3, 3, 2, 1, 1, 0])
    4096 29 b3530_0

end D5.S3.Arith.ErdosNicolas.Data.RankReadouts02
