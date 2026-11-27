import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover00

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap00Box : Box := ![(1, 6 / 5), (0, 63 / 100), (0, 1 / 2), (0, 1 / 2)]

private def cap000Box : Box := ![(1, 6 / 5), (0, 63 / 200), (0, 1 / 2), (0, 1 / 2)]

private def cap0000Box : Box := ![(1, 6 / 5), (0, 63 / 200), (0, 1 / 4), (0, 1 / 2)]

private def cap0000Tree : Option PackedTree := decode 8 0xf5247523f4cf74cef4fdf4fd74cb74cad7b757b6d7625761d790d790575dd75d5e9fbe9fae996e995e9a7e9a6e990e98faf21af20aebbaebaaeceaecdaeb5aeb4a6bdbabdb6bb12bb0ebb3abb36bad6bad25a265a225796579257ba57b65762575e8ea47ea45e99de99be9a6e9a5e98fe98e9688968695e495e295ed95ec95d795d6ae2e9a7e9a6e990e98fe935e934e926e925aeceaecdaeb5aeb4ae5fae5eae52ae51b5d9d5d9b5d6b5d695cbf5cbd5ca55ca32bdd2bdb2bb12baf2b192b172afb2af9474d374d2f4c7f4c7749a74997492f491caf6caf64aebcaeb4ac5cac4cabe4abd57d321d31fd25bd259d24dd24bd233d2315d6b5d695cb15caf5ca55ca35c915c8f6bad6bad2b962b95eb94ab946b922b91e5762575e5612560e55f655f255c655c28e98fe98ee92ce92be925e923e918e91795d795d695839582957c957a9570956fad19689968895e595e495ee95ed95d895d788c088bf883188308839883888248823b1181117f106310611073107110491047019f019d00bb00b900c500c300a1009f44b444b434af24af14af6caf64aebcaeb40674066402e402d4030c0304027c0275714af74af6caec4aebcac64ac5cabecabe441cc41c44124411c3f643f5c3f0c3f05883988388824882387ec87eb87e187e0806280618050804f801d801c800e800da257b657b2575e575a562e562655f255ea01860182013e013a0072006a0036002eb95d895d795849583957d957c957195708050804f80158014800e800d80058004b2baf2bad2b072b052af92af52ae12adf009f009d00290027001b0017000900075a23a917a66fa66fa637a697a63ba63ba6325a1a578a578a575657b2575a575a5752f4cdf499f4c6f49274c77495f4c674914af14ac54aeacabdcaeb4ac14aea4abcd7174d2f495f4c774917499748bf491f48acaf64ac14aeb4abccac4cab7cabd4ab6de98ee922e92be916e923e915e917e91495d695799582956e957a956d956f956ca8cb434ac54af14abdcaf64ac14aeb4abcc066400dc02d400640304009c027400558a57b2560a575a55e6562655be55ea55b60182004e013a002a006a000e002e0006caeb4abccac14ab74abd4ab6cab7cab6402740054009c0014005c000c001c0005443

private theorem cap0000Accepted : Accepted table cap0000Box cap0000Tree := by
  decide +kernel

private def cap0001Box : Box := ![(1, 6 / 5), (0, 63 / 200), (1 / 4, 1 / 2), (0, 1 / 2)]

private def cap00010Box : Box := ![(1, 6 / 5), (0, 63 / 200), (1 / 4, 1 / 2), (0, 1 / 4)]

private def cap00010Tree : Option PackedTree := decode 5 0x33a91fa677a917a66fa69ba63fa697a63a5a2257925a1a578a57b6575e57b2575ac6a74d374c7f4d2f4c7749a7492f4997491caf6caebcaf64aeb4ac5cabe4ac4cabd58d192d112bc92d0d2bc52bdb2baf2bd92bad019d00b9019900b500c3009f00c1009d635257b6575e57b2575a562e55f2562655ea0186013e0182013a00720036006a002ec688

private theorem cap00010Accepted : Accepted table cap00010Box cap00010Tree := by
  decide +kernel

private def cap00011Box : Box := ![(1, 6 / 5), (0, 63 / 200), (1 / 4, 1 / 2), (1 / 4, 1 / 2)]

private def cap000110Box : Box := ![(1, 11 / 10), (0, 63 / 200), (1 / 4, 1 / 2), (1 / 4, 1 / 2)]

private def cap000110Tree : Option PackedTree := decode 5 0x32d752d512d512d4f2c1f2bfd2bfd2bfb11e111bf11bf11bd10b1108f108f108d623c2237e237e237a2162211e211e211a03f203ae03ae03aa01d601b201b201ae896a8968996a7968895fe95ee95fd95ed88df88c088de88bf8847883988468838b11bf118111bd117f108f1073108d107101d7019f01d5019d00d900c500d700c34396a896a79689968895fe95fd95ee95ed88df88de88c088bf8847884688398838b11bf11bd1181117f108f108d1073107101d701d5019f019d00d900d700c500c344b53cb444b444b434afecaf6caf6caf640754067406740664035c030c030c03056a583e57fa57fa57f6565e564a564a56462162211e211e211a1fde1fca1fca1fc6c42c4423c423c42343fbc3f943f943f8c03ac03640364035c0144011c011c011512bfd2bdd2bfb2bdb2b252b192b232b17108f1073108d10710fe50fd90fe30fd76211e20e6211a20e21fca1fb21fc61fae01b2018a01ae0186008e0076008a0072872bfd2bfb2bdd2bdb2b252b232b192b17108f108d107310710fe50fe30fd90fd76211e211a20e620e21fca1fc61fb21fae01b201ae018a0186008e008a00760072895fd95ed95ed95ec9591958b958b9589806b8061806180608022801c801c801aad1

private theorem cap000110Accepted : Accepted table cap000110Box cap000110Tree := by
  decide +kernel

private def cap000111Box : Box := ![(11 / 10, 6 / 5), (0, 63 / 200), (1 / 4, 1 / 2), (1 / 4, 1 / 2)]

private def cap000111Tree : Option PackedTree := decode 6 0xf54a753ef53ef53e7510750775077506d7dad7d057d057cfd7a2d799d799d7995ea20ea0eea0eea0de9cae9b8e9b8e9b7af45af33af33af32aef1aedfaedfaedea6bed6be82be82be7ebd16bccebccebcca5aea5aa25aa25a9e598a59425942593ed7a2d799d799d7995778d76fd76fd76f4b314b284b284b27cb07caff4aff4afed23a9f7a923a9f3a91fa83ba7efa837a7eabe82bdbabe7ebdb6bccebc86bccabc82f50774fdf506f4fd74dc74d3f4dbf4d35799d790d7995790576fd767576f5766d35f415edd5f3f5edb5e675e435e655e412d512d132d4f2d112ca12c7f2c9f2c7d6bccebc86bccabc82bb7ebb3abb7abb36594258fe593e58fa57fa57ba57f657b690fa9f7a9f3a923a91fa83ba837a7efa7eabe82be7ebdbabdb6bccebccabc86bc82f5077506f4fdf4fd74dc74dbf4d3f4d35799d7995790d790576fd76f57675766d35f415f3f5edd5edb5e675e655e435e412d512d4f2d132d112ca12c9f2c7f2c7d6bccebccabc86bc82bb7ebb7abb3abb365942593e58fe58fa57fa57f657ba57b691d4f9d48fd48fd48bd36fd34dd34dd34b5f3f5edb5edb5ed55dbd5d9b5d9b5d996be7ebdb6bdb6bdaabb7abb36bb36bb325a9e5a225a225a1a57f657b657b657b286ba72ba6e3a6e3a6dfa5eba5afa5afa5aabbc6bb7ebb7ebb7aba8aba4eba4eba4af4bd74b5f4b5f4b574a3749f749f749ed7515749d749d7495738573457345733d35de35dbf5dbf5dbd5ce15cd15cd15ccf2c1f2bfd2bfd2bfb2b2f2b252b252b23474dc74d3f4dbf4d374b5f4af74b574aed76fd767576f5766d749d74357495742de96be95ee96ae95de93ee935e93de934ae93ae86ae92ae85ae68ae5fae67ae5ea6bb7ebb3abb7abb36b9a2b97eb99eb97a57fa57ba57f657b6564a56325646562e87d371d36fd34fd34dd2d7d2d5d2bdd2bb5dbf5dbd5d9d5d9b5d275d255d0d5d0b7a5afa5aba57ba577a4fba4f7a4d7a4d2ba4eba4aba1aba16b9a2b99eb97eb97a9aedfaedeaeceaecdae68ae67ae5fae5e95fe95fd95ee95ed95929591958c958ba3a6dfa69ba69ba697a4f7a4d3a4d3a4cabb7abb36bb36bb32b99eb97ab97ab976d76f5766d766d7665733d72f572f572ecafecaf6caf6caf64ac8cac5cac5cac4d0d1

private theorem cap000111Accepted : Accepted table cap000111Box cap000111Tree := by
  decide +kernel

private def cap00011Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap000110Tree <*> cap000111Tree

private theorem cap00011Accepted : Accepted table cap00011Box cap00011Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap00011Box 0 (midpoint cap00011Box 0) = cap000110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap000110Accepted
  · have h : rightBox cap00011Box 0 (midpoint cap00011Box 0) = cap000111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap000111Accepted

private def cap0001Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap00010Tree <*> cap00011Tree

private theorem cap0001Accepted : Accepted table cap0001Box cap0001Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap0001Box 3 (midpoint cap0001Box 3) = cap00010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap00010Accepted
  · have h : rightBox cap0001Box 3 (midpoint cap0001Box 3) = cap00011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap00011Accepted

private def cap000Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap0000Tree <*> cap0001Tree

private theorem cap000Accepted : Accepted table cap000Box cap000Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap000Box 2 (midpoint cap000Box 2) = cap0000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0000Accepted
  · have h : rightBox cap000Box 2 (midpoint cap000Box 2) = cap0001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0001Accepted

private def cap001Box : Box := ![(1, 6 / 5), (63 / 200, 63 / 100), (0, 1 / 2), (0, 1 / 2)]

private def cap001Tree : Option PackedTree := decode 10 0xced32eb2dec2aeb26ec5beb27ec1eeb25b1c4b03cb118b034b132b035b10fb033b11963896079623160696265606b621f606730cd2e532fd52e4130012e432fc32e3f6222488c9110e2ec5beb27eb27eb14eb42eb15eb15eb13b132b035b035b023b04fb024b024b022bd685d62bd62bd627d529d4fbd4fbd4f9609f6049604960455f6b5f415f415f3f4d899581ad81ad811d827d812581258114c004b90cb90cb874b9d4b884b884b86db04fb024b024b022afb5afa0afa0af9f973a97109710970d96ba96a896a896a7a47593f529f58a7528f58af5297589f528581ad7bcd811d7bbd81257bc581157bb5eb15ea52eb13ea50ea7dea48ea7cea47b024af78b022af76afa0af6eaf9faf6da6c0d6bde6c08ebddec092bde2c08abdda5c865a565c3a5a4a5c425a525c365a46d81257bc581157bb57d057b757cfd7b6cb884b4a4b86cb48cb544b44cb53cb44521ceb15eb13ea52ea50ea7dea7cea48ea47b024b022af78af76afa0af9faf6eaf6da65812581157bc57bb57d057cfd7b757b6cb884b86cb4a4b48cb544b53cb44cb445227589f52875287523753e7523f523f522d81157bb57bb57b5d7cfd7b6d7b6d7b55360475eef5eef5ed95f3f5edb5edb5ed52e1d2d252d252d0f2d4f2d112d112d0d43464c334b94cb94cb87cc004b90cb90cb874518c4a3c4a3c497c4ecc49f449f449753228c6251e251e24be276624fa24fa24ba07ae04f204f2049606aa04ce04ce04929125ca65a5a5c3e5a4e5c865a565c3a5a4a251e233624be232624fa233224ba232299128f119b125f1193127d1199125d1191027901b7024b01af026701b5024901ad48714c004b90cb90cb874b5d4b544b544b53c4ecc49f449f44974478446fc46fc46f589d9893e893e892e88f088df88df88de81aa81338133812480fc80eb80eb80eaa25c865a565c3a5a4a5aa25a265a9e5a2224fa233224ba2322237e2302237a22fec49f446644974464446fc460446f445fc099c06d4092406b4075c067c075406750e5c865c3a5a565a4a5aa25a9e5a265a2224fa24ba23322322237e237a230222fec49f449744664464446fc46f4460445fc099c092406d406b4075c0754067c067512e1d2d252d252d0f2d4f2d112d112d0d125d11911191117d11bd117f117f117b624ba2322232222fa237a22fe22fe22f60492035a035a033603aa033a033a033286889149d4a1d33fd48dd339d48fd33bd48bd3375eed5d8b5ed75d835edb5d875ed55d814d7bbd76357b6576157b6d761d7b557604b494af3cb43caf1cb444af24b434af1511a32292d252bcf2d0f2bc72d112bc92d0d2bc511911067117d105f117f1061117b105d6232220ce22fa20be22fe20c222f620ba035a017e0336016e033a01720332016a88d10e2

private theorem cap001Accepted : Accepted table cap001Box cap001Tree := by
  decide +kernel

def cap00Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap000Tree <*> cap001Tree

theorem cap00Accepted : Accepted table cap00Box cap00Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap00Box 1 (midpoint cap00Box 1) = cap000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap000Accepted
  · have h : rightBox cap00Box 1 (midpoint cap00Box 1) = cap001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap001Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover00
