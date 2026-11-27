import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover27

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap111011110100Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (3 / 4, 7 / 8)]

private def cap1110111101000Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap11101111010000Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap111011110100000Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 819 / 1600), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap111011110100000Tree : Option PackedTree := decode 6 0x38f258f218f0f8f0b8e098e078dff8dfd75ad75a97599759574ef74ed74e574e371e1f1e171def1de71bff1bfb1be71bdeeb32eb2aeb0aeb02e9cae9c6e9b6e9b2ac704c703c6f9c6f7c6adc6acc6a2c6a1ba77ba76ba6dba6cba42ba41ba3aba39a6eb5aeb52eb0aeb02e9dee9dae9b6e9b2c8e2c8dec88ec88ac702c6fec6eec6eadd3bdd3b5d36dd365d215d20dd1d5d1cd8e058dfd8ddd8dd58bed8be58b958b8d231e431e3f1de71de31c0f1c0b1bdf1bdaeb52eb4eeb02eafee9dae9d6e9b2e9aee381e381637be37b63566355e350e3505d3b5d3add365d35dd20dd205d1cdd1c5375a975a77581757f7483748174737471646f646d6445644362f962f762e362e143c77bc779c770c76ec6f9c6f7c6f2c6f0bac2bac0bab8bab6ba6dba6cba68ba67b8ee18edd8ec98ec58de58de18dd78dd37571756d755b755774d174cf74c774c55637ce37be375e374e3516350e3496348dd36dd365d31dd315d1d5d1cdd195d18d375857581755d755774db74d974c774c564476445641d641b637763756367636440013ae9b6e9b2e98ee98ae8eae8e6e8cae8c6c6eec6eac6cec6cac5cac5c6c59ec59a918ef38ef18ec58ec38def8ded8dd38dd17581757f7557755574d974d774c574c371bdf1bdb1ba71ba31a871a831a471a42e9b2e9aee98ae986e8e6e8e2e8c6e8c29bac0babfbaabbaaaba39ba38ba31ba30b222b221b20db20cb171b170b166b165a1a

private theorem cap111011110100000Accepted : Accepted table cap111011110100000Box cap111011110100000Tree := by
  decide +kernel

private def cap111011110100001Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101000010Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (3 / 4, 13 / 16)]

private def cap1110111101000010Tree : Option PackedTree := decode 6 0xe449e44964436442e4076406e4026401ddd0ddd05dcaddca5d995d98dd945d93dc892c891c885c884c80dc80cc803c802bba0bb9fbb94bb93bb31bb30bb27bb26af221b221721e721e32013200f1fe71fe2ee56ee52ee26ee22eca2ec9eec76ec72e442e442643c643be401e40163fc63fbddca5dc9ddc45dc3dd93dd935d8e5d8dd6b203b20372013200f1def1deb1dc31dbeeccaecc6eca2ec9eeb0aeb06eae2eadee406e4066401e40163bd63bce3b7e3b75d98dd985d93dd935d60dd605d5bdd5b57900990078ff38ff18ee18edf8ec98ec77651764f763b76397571756f755b75597200f200b1fe31fdf1dbf1dbb1d8f1d8aec9eec9aec72ec6eeadeeadaeab2eaaeb46ee86ee82ee56ee52eccaecc6eca2ec9ecc62cc5ecc2ecc2aca9aca96ca72ca6eddd05dcfddca5dc9dd98dd985d93dd93598bd98b59855984d952d952594dd94d57772b77277713770f7651764d763b76376617661365ff65fd653965356525652355d995d985d945d935d615d605d5c5d5b59535952594e594d5911d911590cd90c5bb28bb26bb1dbb1bbab8bab6baadbaabb29cb29ab292b291b219b218b20eb20da88c891c890c877c876c80cc80bc7f7c7f6bb9fbb9ebb87bb86bb30bb2fbb1bbb1ab901990178fef8fed8ef38ef18ec58ec37661765f763776357581757f755775554ddcfddcf5dc3ddc35d985d97dd8ddd8d598b598ad97f597ed9525951d948d9485bb30bb2fbb1bbb1abac0babfbaabbaaab2a4b2a3b291b290b222b221b20db20ca43

private theorem cap1110111101000010Accepted : Accepted table cap1110111101000010Box cap1110111101000010Tree := by
  decide +kernel

private def cap1110111101000011Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101000011Tree : Option PackedTree := decode 6 0xe457e4576450e4506411e411640ce40c5ddcdddc5dd6ddd65da3dda35d9edd9e5c8aec8adc8a0c89fc822c821c818c817bbb8bbb7bbacbbabbb46bb45bb3cbb3baf22872283224f224b20672063203b2036eeb6eeb2ee86ee82ecf6ecf2eccaecc6e450644fe4496448e40c640be406e4065dd65dd5ddd05dcfdd9e5d9ddd98dd9856b208f208b206720631e4b1e471e1f1e1aed1eed1aecf6ecf2eb5aeb56eb32eb2ee4116410e40c640be3c8e3c863c363c2dda35da2dd9e5d9ddd6add6a5d65dd655790339031901d901b8f0f8f0d8ef78ef5767b767976657663759975977585758372063205f203720331e1b1e171deb1de6ecf2eceeecc6ecc2eb2eeb2aeb06eb02b46eee6eee2eeb6eeb2ed1eed1aecf6ecf2ccc6ccc2cc92cc8ecaeacae6cac2cabedddc5ddbddd65dd5dda35da2dd9e5d9dd9985997d991d991595cd95c5957d95757775b775977437741767b767976657663664966476631662f6561655f654d654b6eeb2eeaeee82ee7eecf2eceeecc6ecc2cc8ecc8acc5ecc5acabecabaca96ca92b5768f768b767b767775ad75a975997595657565716561655d6471646f645d645b6ecf6eceeeccaecc2eb32eb2aeb0aeb02cac2cabaca9aca92c8bac8b6c88ec88aa2322b722af227f227b20872083205f205aeedeeedaeeaeeeaaed16ed12eceeeceae44fe44f6448e448640be40b64066405ddd5ddd55dcfddcf5d9ddd9d5d985d97d590439041901990178f218f1f8ef38ef1768b76897661765f75a975a77581757f4dddbdddb5dcfddcf5da2dda25d985d97d997d997598b598ad95c595bd9525951dbb45bb44bb30bb2fbad4bad3bac0babfb2b8b2b7b2a4b2a3b237b236b222b221a43

private theorem cap1110111101000011Accepted : Accepted table cap1110111101000011Box cap1110111101000011Tree := by
  decide +kernel

private def cap111011110100001Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101000010Tree <*> cap1110111101000011Tree

private theorem cap111011110100001Accepted : Accepted table cap111011110100001Box cap111011110100001Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110100001Box 2 (midpoint cap111011110100001Box 2) = cap1110111101000010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101000010Accepted
  · have h : rightBox cap111011110100001Box 2 (midpoint cap111011110100001Box 2) = cap1110111101000011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101000011Accepted

private def cap11101111010000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110100000Tree <*> cap111011110100001Tree

private theorem cap11101111010000Accepted : Accepted table cap11101111010000Box cap11101111010000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111010000Box 1 (midpoint cap11101111010000Box 1) = cap111011110100000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100000Accepted
  · have h : rightBox cap11101111010000Box 1 (midpoint cap11101111010000Box 1) = cap111011110100001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100001Accepted

private def cap11101111010001Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap111011110100010Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap111011110100010Tree : Option PackedTree := decode 7 0xf6df76def6d8f6d87692f692768ef68e6b02eb026afd6afceac9eac96ac5eac55edbdedbbedb0edafed24ed23ed1ced1bd604d603d5f9d5f8d592d591d58ad589afb6c7b6c3b693b68fb477b473b453b44f57eb57e757bb57b7562f562b560b5606f6d876d7f6d1f6d1768e768df689f6896afceafc6af6eaf5eac56ac4eac0eac056bb497b48fb477b46fb2e7b2e3b2cfb2cb564f5647562f562754f754f354e354def68ef68df68a76897659f65976557654eac5eac4eac16ac06a9c6a9bea996a98d475817580f57eb57e3564f5647562f56271e4b1e431e1f1e171c131c0f1bff1bfaeafd6afc6af7eaf5eac5eac4eac16ac063c3e3c2e3bde3bce37fe37f637ce37b90004e5ab27ab23ab05ab01aa7baa79aa65aa638e098e078df38def8d5b8d598d458d4348edbbedb9edafedaded23ed22ed1bed1ad603d601d5f8d5f6d591d590d589d588bdb5fdb5bdb45db41da37da35da25da23abf1abedabd7abd3ab13ab11ab01aaff57691f69176897688f65c765bf654f6546ac8eac86ac06abfea9e6a9dea98ea9853ac07ac03abd9abd3ab23ab21ab01aaff8f218f1f8ef38ef18e078e058def8dec40011b56475643560355ff54f354ef54c754c31c0f1c0b1bdf1bdb1ab31aaf1a871a8290fb693b68fb663b65fb453b44fb42fb42b57bb57b757875783560b560755e755e2f6d1f6d176cbf6cb7689f68976857684eaf6eaf5eaf06aefeac0eac06abc6abbd7db31db2fdb17db15da17da15da05da03abc3abc1aba9aba7aaf3aaf1aadfaadd7b65fb65bb62bb627b42bb427b407b3ff5783577f574f574b55e355df55bb55b6b5da29da25da17da13d955d953d947d945ab05ab01aaf3aaefaa65aa63aa59aa577b42fb427b40bb3ffb28fb28bb26bb26755e755df55bf55b754b354af5497548ea3abddabdbabc3abc1ab05ab03aaf3aaf18ef78ef58ee18edf8df38df18de58de3757b757af5783577f5607560355e355df1deb1de71dbf1dbb1be31bdf1bc71bc2bd5e1d5e0d5d4d5d3d579d578d56fd56ec770c76fc764c763c6f2c6f1c6ebc6eababc1abbfaba7aba5aaf1aaefaaddaadb8edf8edd8ec78ec58de38de18dd58dd35ad582d580d579d577d532d531d52cd52bc6f9c6f7c6f2c6f0c6a2c6a1c69cc69bbaaf3aaefaadfaadbaa59aa57aa4baa478de58de18dd78dd38d398d378d258d23511db45db41db2ddb29da25da23da13da11abd7abd3abbfabbbab01aaffaaefaaed7b65bb653b627b623b427b423b3ffb3fb577f5777574b574755df55db55b755b2aed12ed11ed00ecfeeca9eca8ec99ec98d580d57fd56dd56cd531d530d523d52220008c757b357a7574b5747560355ff55b755b31de71de31d8b1d871bdf1bdb1ba71ba2000236ac06abfeab6eab66a98ea986a91ea91637be37b6374e3746350e3506348e348521a

private theorem cap111011110100010Accepted : Accepted table cap111011110100010Box cap111011110100010Tree := by
  decide +kernel

private def cap111011110100011Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101000110Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (3 / 4, 13 / 16)]

private def cap1110111101000110Tree : Option PackedTree := decode 7 0x3ddd7ddd5ddb7ddb5dc8ddc8bdc73dc71bff3bff1bfe5bfe3bf87bf85bf7bbf7977fe77fe37fcb7fc77f0f7f0b7ef77ef35c1b5c175bdf5bdb59df59db59af59aa8eeeaeee8eedaeed9ee45ee44ee38ee37d705d704d6f6d6f5d676d675d66ad669afbb6fbb6bbb37bb33b8ebb8e3b8bbb8b75bdf5bdb5bab5ba759af59ab597f597820027776d776cf7667765f71c771bf716f7166b7b6b7aeb74eb746b356b34eb2f6b2ed6bb91bb917b8e7b8e3b693b68fb663b65f7f0f7f0b7ef77ef37ebb7eb77eab7ea6efe1efe16fdeefde6fd76fd6efd56fd4eb3beb3b6b35eb356af76af6eaf0eaf051dc8bdc89dc71dc6fdb47db45db2fdb2dacedacebacd5acd3abdbabd7abc1abbf5f71d771c77177716f6cc76cbf6c5f6c56b35eb356b2feb2f6af0eaf06aea6ae9c0004eee38ee37ee2dee2ced97ed96ed8aed89d66ad669d65ed65dd5e0d5dfd5d3d5d2ad1d707d705d6f7d6f6d677d676d66bd66ac893c892c886c885c80ec80dc804c80380009dae0bae09adedadebacedacebacd5acd391259123910b9109901b9019900790055eb7beb7b6b756b74eb35eb356b2feb2f64436442e43ce43c64026401e3fce3fc5d6f6d6f5d6e9d6e8d66ad669d65ed65dc885c884c878c877c803c802c7f8c7f7ad6b3beb3b6b35eb356af76af6eaf0eaf064076406e4026401e3bde3bd63b863b7dd676d675d66ad669d5edd5ebd5e0d5dfc80dc80cc803c802c77ac779c76fc76eaf59af59ab597f597b578757835753574f2013200f1fe71fe31dc31dbf1d931d8eeb356b34eb2f6b2eeaf06aefeae9eae96401e40163fc63fbe3b7e3b763b1e3b15688eee8eee7eed9eed8ee44ee43ee37ee36d704d703d6f5d6f4d675d674d669d668bddcfddcdddb1ddafdc87dc85dc6ddc6bae07ae05ade9ade7ace9ace7acd1accf5f76cf76bf765f764f71bf71af7167715eb7aeb79eb746b73eb34eb33eb2eeb2e55dc89dc87dc6fdc6ddb45db43db2ddb2bacebace9acd3acd1abd7abd5abbfabbd7b90fb90bb8dbb8d7b687b683b657b65359d359cf59a3599f57ab57a7577b5776bee37ee35ee2cee2bed96ed94ed89ed88d669d667d65dd65cd5dfd5ddd5d2d5d1a8eb826b816b7aeb79eb3aeb39eb34eb33e448e44864426441e4066405e4016400dd6f5d6f3d6e8d6e7d669d667d65dd65cc884c883c877c876c802c801c7f7c7f6ab59d759cf59a7599f57af57a7577f57772033202f200b20071de71de31dbb1db6eb34eb33eb2eeb2e6aefeaeeeae96ae8e4016400e3fbe3fb63b763b6e3b163b0d443

private theorem cap1110111101000110Accepted : Accepted table cap1110111101000110Box cap1110111101000110Tree := by
  decide +kernel

private def cap1110111101000111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (3 / 4, 13 / 16)]

private def cap11101111010001110Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (3 / 4, 25 / 32)]

private def cap11101111010001110Tree : Option PackedTree := decode 5 0x3de13de11ddf1ddefdcbbdcb9dca3dca1ae43ae41ae27ae25ad1dad1bad05ad037bc23bc1fbbdfbbdbb973b96fb943b93f5c835c7f5c4b5c475a375a335a075a02beef8eef7eee8eee7ee51ee50ee44ee43d713d712d704d703d682d681d675d674bddefddedddcfddcddca1dc9fdc87dc85ae25ae23ae07ae05ad03ad01ace9ace75aee5dee5cee51ee50edbbedbaedafedaed68ed68dd682d681d603d602d5f8d5f7bdcb9dcb7dca1dc9fdb75db73db5ddb5bad1bad19ad03ad01ac05ac03abefabed5f728f72877227721f6d7f6d776d176d0eb416b40eb3aeb3a6afc6afbeaf5eaf55ee50ee4fee43ee42edaeedadeda1eda0d681d680d674d673d5f7d5f6d5ead5e9ad1d721d71fd713d711d68ed68cd682d680c8adc8abc89fc89ec821c820c817c816bae27ae23ae09ae05ad05ad01acebace7913f913d91239121902f902d9019901756b476b466b416b406b01eb00eafc6afb6410e410640be40b63c863c7e3c2e3c25d682d680d675d673d5f8d5f6d5ebd5e9c817c816c80cc80bc785c784c779c778a88

private theorem cap11101111010001110Accepted : Accepted table cap11101111010001110Box cap11101111010001110Tree := by
  decide +kernel

private def cap11101111010001111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (25 / 32, 13 / 16)]

private def cap11101111010001111Tree : Option PackedTree := decode 7 0x3de17de15ddf5ddf3dd37dd35dd2fdd2dc01bc019c003c001bfcfbfcdbfc7bfc57ba6fba6bba5fba5bb97fb97bb94fb94b7f9f7f9b7f8f7f8b7f3f7f3b7f277f229e00ee00ce002e000dfcfdfcedfc9dfc8d723d722d715d714d690d68fd684d683a0009c3bc2bbc27bbe7bbe3b97bb977b94bb9478033802f80037fff7f3b7f377f237f1ef0067005f0006fffefe76fe6efe46fe3eb916b90eb8a6b89eb47eb476b41eb4150fbbebbbe7bbafbbabba5fba5bba4fba4b800780037fe77fe37f8f7f8b7f7f7f7af74bf74b7749f7497729f72977237722eff1eff16fefefef6fe4efe46fe1efe153c005c001bff3bff1bf93bf91bf87bf85ae2bae29ae0dae0bad09ad07acefaced000138777cf77c7775777477297728f722f72270006fffeffc6ffbefe46fe3efe16fe0de000dfffdff8dff7dfc8dfc7dfc2dfc1d714d713d705d704d683d682d676d675a1aee5fee5eee53ee52edbeedbdedb1edb0dfcfdfcedfc9dfc8dfb6dfb5dfb2dfb1bbf9fbf9dbf93bf91bf6dbf6bbf65bf63ad21ad1fad09ad07ac0bac09abf5abf34772f772ef7297728f6def6ddf6d876d7eb47eb476b41eb416b026b01eafceafc57dca7dca5dc8ddc8bdb63db61db49db47bf93bf91bf87bf85bf65bf63bf5dbf5b77f277f237f0f7f0b7ecb7ec77ebb7eb75a135a0f59df59db57eb57e757bb57b68ee52ee51ee45ee44edb0edafeda3eda2d683d682d676d675d5f9d5f8d5edd5ebad1d723d722d715d714d690d68fd684d683cf45cf44cf3ecf3dcf29cf28cf24cf23b9e8b9e899e7d9e7b9e539e519e499e47915f915d91439141904790459033903146b916b90eb8a6b89eb47eb476b41eb4164576456e450644fe4116410e40c640bd7ae2bae29ae0dae0bad09ad07acefaced9e7d9e7b9e719e6f9e499e479e3f9e3d73cfb3cf73ce33cdf3c933c8f3c7f3c7b22872283224f224b20672063203b20368d714d713d705d704d683d682d676d675c8a0c89fc892c891c818c817c80dc80cad6b486b47eb426b41eb02eb026afd6afce411e411640ce40c63c963c8e3c3e3c35d68fd68ed683d682d604d603d5f9d5f8c822c821c818c817c791c790c786c785af5a135a0f59df59db57eb57e757bb57b720672063203b20371e1f1e1b1def1deaeb41eb416b3b6b3aeafceafc6af6eaf5e40c640be406e40663c363c2e3bd63bcd688

private theorem cap11101111010001111Accepted : Accepted table cap11101111010001111Box cap11101111010001111Tree := by
  decide +kernel

private def cap1110111101000111Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111010001110Tree <*> cap11101111010001111Tree

private theorem cap1110111101000111Accepted : Accepted table cap1110111101000111Box cap1110111101000111Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111101000111Box 3 (midpoint cap1110111101000111Box 3) = cap11101111010001110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010001110Accepted
  · have h : rightBox cap1110111101000111Box 3 (midpoint cap1110111101000111Box 3) = cap11101111010001111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010001111Accepted

private def cap111011110100011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101000110Tree <*> cap1110111101000111Tree

private theorem cap111011110100011Accepted : Accepted table cap111011110100011Box cap111011110100011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110100011Box 2 (midpoint cap111011110100011Box 2) = cap1110111101000110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101000110Accepted
  · have h : rightBox cap111011110100011Box 2 (midpoint cap111011110100011Box 2) = cap1110111101000111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101000111Accepted

private def cap11101111010001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110100010Tree <*> cap111011110100011Tree

private theorem cap11101111010001Accepted : Accepted table cap11101111010001Box cap11101111010001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111010001Box 1 (midpoint cap11101111010001Box 1) = cap111011110100010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100010Accepted
  · have h : rightBox cap11101111010001Box 1 (midpoint cap11101111010001Box 1) = cap111011110100011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100011Accepted

private def cap1110111101000Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111010000Tree <*> cap11101111010001Tree

private theorem cap1110111101000Accepted : Accepted table cap1110111101000Box cap1110111101000Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111101000Box 0 (midpoint cap1110111101000Box 0) = cap11101111010000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010000Accepted
  · have h : rightBox cap1110111101000Box 0 (midpoint cap1110111101000Box 0) = cap11101111010001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010001Accepted

private def cap1110111101001Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (13 / 16, 7 / 8)]

private def cap11101111010010Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (13 / 16, 7 / 8)]

private def cap111011110100100Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 819 / 1600), (5 / 8, 11 / 16), (13 / 16, 7 / 8)]

private def cap111011110100100Tree : Option PackedTree := decode 6 0x38f2d8f298f178f138e0d8e0b8e038e0175b575b175a1759d74f374f174e974e771e2f1e271dff1df71c071c031bf31beeeb42eb3aeb1aeb12e9d2e9cee9bee9baac706c705c6fcc6fbc6afc6aec6a4c6a3ba79ba78ba6fba6eba44ba43ba3cba3ba6eb6aeb62eb1aeb12e9e6e9e2e9bee9bac8eac8e6c89ec896c70ac706c6f6c6f2dd3cdd3c5d37dd375d225d21dd1e5d1dd8e158e0d8ded8de58bfd8bf58ba58b9d231e531e4b1e271e1f1c171c131c031bfeeb62eb5aeb3aeb32e9e2e9dee9cee9cae3c4e3c3e3bee3bde380637fe37de37cdd675d665d625d615d39dd395d375d36d58e0b8e098df78df38d5d8d5b8d478d4574f174ef74dd74db74877485747774754dd6c5d6b5d625d615d3c5d3bdd375d36d91cd91c5912d911d8e0d8e058de58dddba78ba77ba6eba6dba43ba42ba3bba3ab1c1b1c0b1bcb1bbb17eb17db173b172a43c77fc77dc774c772c6fcc6fbc6f5c6f4bac6bac4babcbababa6fba6eba6aba69b8ee98ee58ed18ecd8deb8de98ddd8ddb757975757565756174d574d374cb74c95637e637de3776376e3526351e34ae34a5d37dd375d32dd325d1e5d1ddd1a5d19d3758d75897579757574df74dd74d574d3644f644b643b6437637b6379637363716eaf2eaeaeacaeac2e9aae9a6e996e992c876c86ec84ec842c6e6c6e2c6d6c6d2aba6fba6eba65ba64ba3cba3bba34ba33b1bdb1bcb1b5b1b4b174b173b169b168a463bee3bde3b963b8637de37ce37a63795d625d615d5d5d5c5d375d36dd34dd345c772c770c766c764c6f4c6f2c6edc6ebbababab8bab0baadba69ba68ba64ba63ab1bef1be71bb71baf1a8f1a8b1a531a4ae9bae9b6e992e98ee8eee8eae8cee8ca9bac4bac2bababab8ba6eba6dba69ba68b225b223b21bb219b1bcb1bbb1b8b1b7b757575717561755b74d374d174c974c7643764336421641d6371636f6369636755d375d36dd325d31dd1ddd1d5d19dd1958de58ddd8da58d9d8b9d8b958b458b3d21a

private theorem cap111011110100100Accepted : Accepted table cap111011110100100Box cap111011110100100Tree := by
  decide +kernel

private def cap111011110100101Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (5 / 8, 11 / 16), (13 / 16, 7 / 8)]

private def cap1110111101001010Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (13 / 16, 7 / 8)]

private def cap11101111010010100Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (13 / 16, 27 / 32)]

private def cap11101111010010100Tree : Option PackedTree := decode 6 0x3912b91299111910f9021901f900d900b8105810380fb80f980e380e180db80d97020b020701f701f301c701c301b701b2ee8eee8aee5eee5aecd2ecceecaaeca68c894c893c887c886c80fc80ec805c804c081c080c07cc07bc070c06fc06cc06bb8103810180f980f780e180df80d980d777457743772d772b766776657653765143c888c887c87bc87ac806c805c7fbc7fabb97bb96bb8cbb8bbb2abb29bb1fbb1eb910f910d90f590f3900b90098ff58ff3772d772b7717771376537651763d763b5ac810c80fc806c805c77dc77cc772c771bb34bb33bb2abb29bac4bac3bababab9b901f901d900b90098ef98ef78ee38ee1766776657653765175877585757375715e4036402e3fde3fd63b963b8e3b363b2dd955d94dd8fdd8f5d5d5d5cdd585d57dc805c804c7fac7f9c771c770c765c764bb29bb28bb1ebb1dbab9bab8baafbaadad1bba3bba2bb97bb96bb34bb33bb2abb29b31ab319b30db30cb2a8b2a7b29eb29db77457743772d772b76677665765376516633663166196617654f654d653b65395ddcbddcb5dc65dc5dd955d94dd8fdd8f5986d9865980d980594f594ed94a5949dbb96bb95bb8bbb89bb29bb28bb1ebb1db30cb30bb300b2ffb29db29cb293b292ad5d9a5d99dd955d94dd625d61dd5d5d5cd9545953d94f594ed912d912590dd90d5bb33bb32bb29bb28bac3bac2bab9bab8b2a7b2a6b29db29cb224b223b21ab219aeecaaeca6ec7eec7aeaeaeae6eac2eabeca7aca76ca52ca4ec86ec86ac842c83edd94dd945d8f5d8edd5cdd5c5d57dd56d94ed94e5949d949590d590cd907d9075688

private theorem cap11101111010010100Accepted : Accepted table cap11101111010010100Box cap11101111010010100Tree := by
  decide +kernel

private def cap11101111010010101Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (27 / 32, 7 / 8)]

private def cap11101111010010101Tree : Option PackedTree := decode 6 0xe44c644be4456444e4096408e4046403ddd2ddd25dccddcc5d9b5d9add965d95a0004ec896c895c889c888c811c810c807c806c083c082c07ec07dc072c071c06ec06db8107810580fd80fb80e580e380dd80db774977477731772f766b76697657765543c88ac889c87dc87cc808c807c7fdc7fcbb99bb98bb8ebb8dbb2cbb2bbb22bb21b9113911190f990f7900f900d8ff98ff77731772f771b7719765776557643763f5ac812c811c808c807c77fc77ec774c773bb36bb35bb2cbb2bbac6bac5babcbabbb90239021900f900d8efd8efb8ee78ee5766b766976577655758b7589757775755e4046403e3fee3fe63ba63b9e3b463b3dd965d95dd915d90dd5e5d5ddd595d58dc807c806c7fcc7fbc773c772c767c766bb2bbb2abb21bb1fbabbbababab1bab0ad1bba5bba4bb99bb98bb36bb35bb2cbb2bb31cb31bb30fb30eb2aab2a9b2a0b29fb774977477731772f766b76697657765566376635661d661b65536551653f653d5ddccddcc5dc75dc6dd965d95dd915d90d987d9875981d9815950594fd94b594adbb98bb97bb8dbb8cbb2bbb2abb21bb1fb30eb30db302b301b29fb29eb295b294ad5d9b5d9add965d95dd635d62dd5e5d5dd9555954d950594fd913d913590ed90e5bb35bb34bb2bbb2abac5bac4babbbabab2a9b2a8b29fb29eb226b225b21cb21baeecb2ecaeec8aec86eaf2eaeeeacaeac6ca82ca7eca5aca56c876c872c84ec84add95dd955d90dd8fdd5ddd5d5d58dd58594fd94f594ad94a590e590dd90959085688

private theorem cap11101111010010101Accepted : Accepted table cap11101111010010101Box cap11101111010010101Tree := by
  decide +kernel

private def cap1110111101001010Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111010010100Tree <*> cap11101111010010101Tree

private theorem cap1110111101001010Accepted : Accepted table cap1110111101001010Box cap1110111101001010Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111101001010Box 3 (midpoint cap1110111101001010Box 3) = cap11101111010010100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010010100Accepted
  · have h : rightBox cap1110111101001010Box 3 (midpoint cap1110111101001010Box 3) = cap11101111010010101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010010101Accepted

private def cap1110111101001011Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (13 / 16, 7 / 8)]

private def cap11101111010010110Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (13 / 16, 27 / 32)]

private def cap11101111010010110Tree : Option PackedTree := decode 6 0xe45964586451e4516412e412640de40d60476046e0446043e03ce03c603ae03a5c08ec08dc088c087c079c078c075c074bbbbbbbabbafbbaebb49bb48bb3fbb3ea322c322bf228b22872093208f206b206702370233021f021b01e301df01d301cee046e0466043e043603c603be03a6039dddd5ddcddd75dd6dda45da3dd9f5d9ed0f228f228b22572253206f206b2043203f0223021f020b020701d701d301c701c2e0446043e0416040e03ae03a6038e0385dd7ddd75dd1ddd15d9fdd9f5d9a5d99d1914591439129912790359033901f901d810f810d8103810180e980e780e180df7021f021b0207020301d301cf01c301beeebaeeb6ee8aee86ecfaecf6ecceecca86b20972093206f206b1e531e4f1e271e22ed26ed22ecfeecfaeb62eb5eeb3aeb36e4126411e40d640ce3c9e3c963c463c3dda45da3dd9f5d9edd6bdd6b5d66dd6657903790359021901f8f138f118efb8ef9767f767d76697667759d759b758975877206b2067203f203b1e231e1f1df31deeecfaecf6ecceeccaeb36eb32eb0eeb0ab46eeeeeeeaeebeeebaed26ed22ecfeecfacccecccacc9acc96caf2caeecacacac6dddd5ddcddd75dd6dda45da3dd9f5d9ed9995998d992d992595dd95d5958d95857775f775d77477745767f767d76697667664d664b66356633656565636551654f6eebaeeb6ee8aee86ecfaecf6ecceeccacc96cc92cc66cc62cac6cac2ca9eca9ab57693768f767f767b75b175ad759d75996579657565656561647364716461645d6ecfeecfaecd2ecceeb3aeb36eb12eb0ecacacac6caa2ca9ec8c2c8bec896c892dd9f5d9edd99dd995d66dd665d61dd615958d9585953d9535917d91759125911d688

private theorem cap11101111010010110Accepted : Accepted table cap11101111010010110Box cap11101111010010110Tree := by
  decide +kernel

private def cap11101111010010111Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (27 / 32, 7 / 8)]

private def cap11101111010010111Tree : Option PackedTree := decode 6 0xe45ae45a6452e4526413e413640ee40e5ddeddde5dd8ddd85da5dda55da0dda05c8b4c8b2c8a4c8a3c826c825c81cc81bc08fc08ec089c088c07ac079c076c075b811f811d8113811180f580f380ed80eb777977777761775f769576937681767f43c8a5c8a4c898c897c81dc81cc812c811bbb1bbb0bba5bba4bb41bb40bb36bb3510009d91499147912d912b9039903790239021811381118107810580ed80eb80e580e3702270223020f020b01db01d701cb01c6eec2eebeee92ee8eed02ecfeecd6ecd286b209f209b207720731e5b1e571e2f1e2aed2eed2aed06ed02eb6aeb66eb42eb3ee4136412e40e640de3cae3ca63c563c4dda55da4dda05d9fdd6cdd6c5d67dd6757903b9039902590238f178f158eff8efd76837681766d766b75a1759f758d758b72073206f204720431e2b1e271dfb1df6ed02ecfeecd6ecd2eb3eeb3aeb16eb12b46eef6eef2eec6eec2ed2eed2aed06ed02ccd6ccd2cca2cc9ecafacaf6cad2caceddde5dddddd85dd7dda55da4dda05d9fd99a5999d993d993595ed95e5959d9595777637761774b774976837681766d766b6651664f6639663765696567655565536eec2eebeee92ee8eed02ecfeecd6ecd2cc9ecc9acc6ecc6acacecacacaa6caa2b5769776937683767f75b575b175a1759d657d65796569656564756473646564616ed06ed02ecdaecd6eb42eb3eeb1aeb16cad2cacecaaacaa6c8cac8c6c89ec89adda05d9fdd9add9a5d67dd675d62dd625959d9595954d9545918d91859135912d688

private theorem cap11101111010010111Accepted : Accepted table cap11101111010010111Box cap11101111010010111Tree := by
  decide +kernel

private def cap1110111101001011Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111010010110Tree <*> cap11101111010010111Tree

private theorem cap1110111101001011Accepted : Accepted table cap1110111101001011Box cap1110111101001011Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111101001011Box 3 (midpoint cap1110111101001011Box 3) = cap11101111010010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010010110Accepted
  · have h : rightBox cap1110111101001011Box 3 (midpoint cap1110111101001011Box 3) = cap11101111010010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010010111Accepted

private def cap111011110100101Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101001010Tree <*> cap1110111101001011Tree

private theorem cap111011110100101Accepted : Accepted table cap111011110100101Box cap111011110100101Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110100101Box 2 (midpoint cap111011110100101Box 2) = cap1110111101001010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101001010Accepted
  · have h : rightBox cap111011110100101Box 2 (midpoint cap111011110100101Box 2) = cap1110111101001011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101001011Accepted

private def cap11101111010010Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110100100Tree <*> cap111011110100101Tree

private theorem cap11101111010010Accepted : Accepted table cap11101111010010Box cap11101111010010Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111010010Box 1 (midpoint cap11101111010010Box 1) = cap111011110100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100100Accepted
  · have h : rightBox cap11101111010010Box 1 (midpoint cap11101111010010Box 1) = cap111011110100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100101Accepted

private def cap11101111010011Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (13 / 16, 7 / 8)]

private def cap111011110100110Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (5 / 8, 11 / 16), (13 / 16, 7 / 8)]

private def cap1110111101001100Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (5 / 8, 21 / 32), (13 / 16, 7 / 8)]

private def cap1110111101001100Tree : Option PackedTree := decode 6 0xf6d476d3f6ce76cdf68c768bf687f6876af9eaf96af36af2eac36ac2eabeeabe5eda7eda6ed9bed9aed17ed16ed0eed0dd5f2d5f1d5e5d5e3d585d584d57cd57bafb673b66fb63fb63bb43fb43bb41bb417579b5797576b576755f755f355d355cef6cdf6cd76c776c6f6877686f682f6826af2eaf1eaeceaebeabe6abdeab9eab8d6bb463b45bb43fb437b2b7b2b3b297b293561b561355f755ef54d354cf54bb54b6f687f686f68376827652f652764e764deabeeabdeaba6ab8ea976a96ea946a9354757cf57c7579b5793561b561355f755ef1dff1df71dd31dcb1bf31bef1bd71bd0400276af36af26aed6aec6abeeabdeaba6ab8e3ba63b963b463b3637ae37a63776376a8004e5ab0dab09aae9aae5aa69aa67aa51aa4d8df98df78ddd8ddb8d498d478d2b8d282001388eda6eda5ed9aed99ed16ed15ed0ded0cd5f1d5f0d5e3d5e2d584d583d57bd57abdb4bdb49db33db31da2bda29da19da17abe1abddabc5abc3ab07ab05aaf5aaf35f6cd76ccf6c6f6c67686f68676827681eaf1eaf16aebeaeb6abdeabd6ab8eab85ed99ed98ed8ced8bed0ced0bed03ed02d5e2d5e1d5d6d5d4d57ad579d570d56fad768b768a7686f685f656765576527651eac26ac16abdeabcea99ea996a96ea965ed0ded0bed04ed02eca4eca3ec9bec9ad57bd579d571d56fd52dd52cd526d525a8eaf8eaf86af1eaf16ac26ac1eabdeabd63bee3be63b963b8e37de37d637a6379dd5f0d5eed5e2d5e1d583d582d57ad579c77cc77bc771c770c6fac6f9c6f3c6f2af578f578b575f575b55ef55eb55c755c31dcb1dc71d9b1d971bd31bcf1bb71bb2eaf16af0eaeb6aea6abd6abceab86ab7e3b8e3b863b2e3b26379e37963766375d6b5613560b55ef55e754cf54cb54b754b31bef1be71bd31bcb1a8f1a8b1a771a72eabdeabceab8eab7ea96ea966a936a92e37a63796376e375e34ee34e634a63495443

private theorem cap1110111101001100Accepted : Accepted table cap1110111101001100Box cap1110111101001100Tree := by
  decide +kernel

private def cap1110111101001101Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (21 / 32, 11 / 16), (13 / 16, 7 / 8)]

private def cap1110111101001101Tree : Option PackedTree := decode 6 0xf6e176e076daf6d9f6947693f690768feb04eb03eaff6afe6acb6acaeac76ac6dedb5edb3eda8eda6ed20ed1fed18ed16d5fed5fcd5f3d5f1d58ed58dd586d584abb4a3b49fb463b45bb2efb2ebb2b7b2b3565b5657561b561354ff54fb54d354ce9d609d607d5fed5fcd596d595d58ed58dc796c794c78bc789c706c705c701c700babfdabf9abe7abe3ab1dab1bab0dab098f178f138eff8efb8e038e018df98df756acb6acaeac36ac26a9fea9f6a9a6a99e3836382e37e637de357e35763526351d23b703b6ffb6cfb6cbb49fb49bb47fb47b581f581b57f357ef5657565356375632f6dff6df76d976d8f6937692f68f768eeb036b02eafdeafd6aca6ac9eac66ac5d7db67db65db4ddb4bda3fda3dda2dda2babf9abf7abe3abe1ab1bab19ab09ab077b6cbb6c7b697b693b47bb477b457b45357ef57eb57c357bb5633562f560f560ab5da4fda4bda3fda3bd975d973d969d967ab2bab27ab1bab17aa7daa7baa73aa717b47fb477b45bb453b2d3b2cfb2b3b2ab5637562f5613560b54e754e354cf54caa3ac0fac0babf9abf5ab2bab27ab1bab178f298f258f138f0f8e0b8e098e018dff757f357eb57c757bf5637562f5613560b1e271e1f1df71def1c031bff1bef1be4400272d595d593d584d582d53ed53dd533d532c705c704c6fbc6f9c6aec6adc6a3c6a2a43

private theorem cap1110111101001101Accepted : Accepted table cap1110111101001101Box cap1110111101001101Tree := by
  decide +kernel

private def cap111011110100110Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101001100Tree <*> cap1110111101001101Tree

private theorem cap111011110100110Accepted : Accepted table cap111011110100110Box cap111011110100110Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110100110Box 2 (midpoint cap111011110100110Box 2) = cap1110111101001100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101001100Accepted
  · have h : rightBox cap111011110100110Box 2 (midpoint cap111011110100110Box 2) = cap1110111101001101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101001101Accepted

private def cap111011110100111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (5 / 8, 11 / 16), (13 / 16, 7 / 8)]

private def cap1110111101001110Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (13 / 16, 7 / 8)]

private def cap11101111010011100Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (13 / 16, 27 / 32)]

private def cap11101111010011100Tree : Option PackedTree := decode 6 0x3dddddddbddbdddb9dc91dc8fdc79dc77bff9bff7bfe9bfe7bf8bbf89bf7fbf7c80813b7ff37fef7fd37fcf7f177f137eff7efb5c275c235beb5be359eb59e359b759b1000270eeedeeebeedceedbee47ee46ee3bee39dffbdff9dff3dff2dfc4dfc3dfbedfbd80809dbff7bff3bfe7bfe5bf89bf87bf7dbf7bae11ae0dadf1adefacf1acefacd9acd70001383eedeeedceed0eecfee3cee3bee30ee2fdff4dff3dff0dfefdfbfdfbedfbbdfbabbfe9bfe7bfe1bfdfbf7fbf7dbf77bf75adf5adf1add9add7acdbacd9acc3acc14776e776df767f766f71df71cf717f7176ff9eff96ff7eff76fdf6fdeefdd6fdcddff3dff2dfefdfeedfbedfbddfbadfb9d6f8d6f7d6ebd6ead66cd66bd660d65fa1aee48ee47ee3cee3beda6eda5ed9aed99dfc5dfc4dfbfdfbedfb0dfafdfacdfabbbf8bbf89bf7fbf7dbf61bf5fbf59bf57acf5acf1acdbacd9abe3abe1abc7abc547723f723771df71cf6d2f6d276ccf6cc6fe26fe1efdf6fdeefd7efd76fd5efd55dfc4dfc3dfbedfbddfafdfaedfabdfaad678d677d66cd66bd5f0d5eed5e2d5e1a1f71e771df7187717f6cd76ccf6c6f6c66fdfefdf6fddefdd6fd66fd5efd46fd3ddfbfdfbedfbbdfbadfacdfabdfa8dfa7d66dd66cd661d660d5e3d5e2d5d7d5d6a3b8efb8e7b8bfb8bbb667b663b633b62f7efb7ef77eeb7ee77eaf7eab7e9f7e9aefdf6fdeefdd6fdcefd5efd56fd3efd36b366b35eb306b2feaf16af0eaeb6aea50d1d709d708d6fad6f8d67ad678d66dd66ccf3acf39cf34cf33cf21cf20cf1ccf1bb9e759e739e699e679e439e419e399e37912b91299111910f9021901f900d900b46b846b836b7c6b7beb3c6b3beb366b35e79ce79c6799e7996790678fe78de78d5cf39cf38cf33cf32cf20cf1fcf1bcf1ac894c893c887c886c80fc80ec805c804a1eb7deb7ceb766b75eb36eb366b30eb3064446443e43de43d64036402e3fde3fd60004ed6f9d6f7d6ebd6ead66cd66bd660d65fc887c886c87ac879c805c804c7fac7f980009cd6b3d6b3ceb36eb366af8eaf86af1eaf164086407e4036402e3bee3be63b963b8a0004ed679d677d66cd66bd5f0d5eed5e2d5e1c80fc80ec805c804c77cc77bc771c77080009cf59b759b359875983578f578b575f575b201b20171fef1feb1dcb1dc71d9b1d96eb366b35eb306b2feaf16af0eaeb6aea6402e40263fd63fce3b8e3b863b2e3b25688

private theorem cap11101111010011100Accepted : Accepted table cap11101111010011100Box cap11101111010011100Tree := by
  decide +kernel

private def cap11101111010011101Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (5 / 8, 21 / 32), (27 / 32, 7 / 8)]

private def cap11101111010011101Tree : Option PackedTree := decode 6 0x3dde1dddfddc3ddc1dc97dc95dc7ddc7bae19ae17adfbadf9acf9acf7acdfacdc00813bbbbfbbbbbb83bb7bb92bb923b8f7b8f37ff77ff37fd77fd37f1b7f177f037efeeffeeffe6ffaeffa6fe36fe2efe06fdfeb856b84eb7e6b7d6b3deb3d6b376b36d0fbb87bb83bb4bbb47b8fbb8f7b8cbb8c75bf75bf35bbb5bb759bf59bb598f598af770776ff768f768771ef71e7718f7186b7e6b7deb76eb766b376b36eb316b30a0204e6bb92fb92bb8fbb8f7b6a3b69fb673b66f59f359ef59bf59bb57cf57cb579b5796f7257724f71ef71e76d3f6d376cdf6cd6b3deb3d6b376b36eaf96af8eaf2eaf1a0004e7dc7ddc7bdc65dc63db39db37db1fdb1dacdfacddacc7acc5abcdabcbabb5abb37b8f7b8f3b8c7b8c3b66fb66bb63bb63759bb59b7598b59875797578f5767575eb475c335c2f5bf75bf359f359ef59bf59bb2263225f222b2227204b20472023201d010276b856b84eb7e6b7d6b3deb3d6b376b36e79de79d679ae79a67916790e78ee78e5cf3bcf3acf35cf34cf22cf21cf1dcf1cc896c895c889c888c811c810c807c806a1eb7eeb7e6b776b76eb37eb376b31eb3164456444e43ee43e64046403e3fee3fe5d6fcd6fbd6edd6ecd66ed66dd662d661c889c888c87cc87bc807c806c7fcc7fb40009cd6b3e6b3deb37eb376af9eaf96af36af2e4096408e4046403e3bfe3bf63ba63b9dd67bd67ad66ed66dd5f2d5f1d5e5d5e3c811c810c807c806c77ec77dc773c772af59bf59bb598f598b579b5797576b57672023201f1ff71ff31dd31dcf1da31d9eeb376b36eb316b30eaf2eaf1eaeceaebe403e40363fe63fde3b9e3b963b3e3b35688

private theorem cap11101111010011101Accepted : Accepted table cap11101111010011101Box cap11101111010011101Tree := by
  decide +kernel

private def cap1110111101001110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111010011100Tree <*> cap11101111010011101Tree

private theorem cap1110111101001110Accepted : Accepted table cap1110111101001110Box cap1110111101001110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111101001110Box 3 (midpoint cap1110111101001110Box 3) = cap11101111010011100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010011100Accepted
  · have h : rightBox cap1110111101001110Box 3 (midpoint cap1110111101001110Box 3) = cap11101111010011101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010011101Accepted

private def cap1110111101001111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (13 / 16, 7 / 8)]

private def cap11101111010011110Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (13 / 16, 27 / 32)]

private def cap111011110100111100Box : Box := ![(47 / 40, 19 / 16), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (13 / 16, 27 / 32)]

private def cap111011110100111100Tree : Option PackedTree := decode 5 0x3ae4bae49ae31ae2fad25ad23ad0dad0b9e8f9e8d9e819e7f9e579e559e4d9e4a20013b3d1f3d1b3d033cff3caf3cab3c9b3c9722cb22c3228f228b20972093206f206a8d724d723d717d715d691d690d685d684cf46cf45cf3fcf3ecf2acf29cf25cf2420009d9e8d9e8b9e7f9e7d9e559e539e4b9e499161915f91459143904990479035903343d718d717d709d708d686d685d67ad678cf40cf3fcf3acf39cf26cf25cf21cf2040009d9e819e7f9e759e739e4d9e4b9e439e4191479145912b9129903790359021901f46b8beb8aeb846b836b42eb426b3c6b3be79fe79f679ce79c6792e7926790678fc0004ecf3fcf3ecf39cf38cf25cf24cf20cf1fc8a2c8a1c894c893c81ac819c80fc80ea1ad692d691d686d685d607d606d5fcd5fbc825c824c81bc81ac794c793c789c788bad23ad21ad0bad09ac0dac0babf7abf590499047903590338f278f258f118f0f5eb436b42eb3d6b3ceafe6afdeaf8eaf8640de40d64086407e3c4e3c463bee3be08004ed685d684d679d677d5fbd5fad5f0d5eec81ac819c80fc80ec788c787c77cc77b20009cd1

private theorem cap111011110100111100Accepted : Accepted table cap111011110100111100Box cap111011110100111100Tree := by
  decide +kernel

private def cap111011110100111101Box : Box := ![(19 / 16, 6 / 5), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (13 / 16, 27 / 32)]

private def cap111011110100111101Tree : Option PackedTree := decode 6 0x3de1bde19ddf9ddf7dd3bdd39dd33dd31c023c01fc009c007bfd3bfd1bfcbbfc97ba77ba73ba67ba63b987b983b957b9537fa77fa37f977f937f477f437f2f7f2a9e011e00fe004e003dfe9dfe8dfe5dfe4d725d724d718d716d6ccd6cbd6c9d6c8bbfd3bfd1bfcbbfc9bfa3bfa1bf97bf95ad99ad97ad93ad91ad25ad23ad0dad0b48ef0cef0beefbeefaee9cee9bee98ee97e00fe00de003e001dfe8dfe7dfe4dfe3bdd39dd37dd31dd2fdcc1dcbfdca9dca7bfd1bfcfbfc9bfc7bfa1bf9fbf95bf934f007f006f001f000eff46ff3eff26ff1eb926b91eb8b6b8aeb65eb656b646b63ddfe8dfe7dfe4dfe3dfd0dfcfdfcadfc9d6cbd6cad6c8d6c7d691d690d685d684a43eefceefbeeeeeeecee99ee98ee95ee94e004e003dffcdffadfe5dfe4dfe1dfe0bdd33dd31dd2bdd29dcabdca9dc91dc8fbfcbbfc9bfc3bfc1bf97bf95bf8bbf894f0027001effe6ffd6ff2eff26ff0eff06b8c6b8b6b84eb846b64eb646b636b62ddfe5dfe4dfe1dfe0dfcbdfcadfc5dfc4d6c9d6c8d6c6d6c5d686d685d67ad678a4777df77d77767775f74c774bf74a7749f001f000effd6ffceff26ff1eff06fefdee98ee97ee94ee93ee54ee53ee47ee46dfe4dfe3dfe0dfdfdfcadfc9dfc4dfc3a7800f80077feb7fe77f937f8f7f837f7f5c5b5c575c235c1b5b235b1f5b175b12eff26ff1eff06fefefe56fe4efe26fe1eb646b63eb62eb626b42eb426b3c6b3bd21aee61ee60ee55ee54edc0edbfedb3edb2dfd1dfd0dfcbdfcadfb8dfb7dfb4dfb3bbfa3bfa1bf97bf95bf71bf6fbf69bf67ad25ad23ad0dad0bac0fac0dabf9abf747730772ff72a7729f6dff6df76d976d8efe86fe7efe56fe4efdbefdb6fd9efd95dfd0dfcfdfcadfc9dfb7dfb6dfb3dfb2d691d690d685d684d606d605d5fbd5faa1f72af72a77247723f6d9f6d976d376d2efe5efe56fe2efe26fda6fd9efd86fd7ddfcbdfcadfc5dfc4dfb4dfb3dfb0dfafd686d685d67ad678d5fcd5fbd5f1d5f0a3b953b94fb91fb91bb6cbb6c7b697b6937f2b7f277f137f0f7ecf7ecb7ebf7ebaefe56fe4efe26fe1efd9efd96fd7efd76b42eb426b3c6b3beafdeafd6af86af750d1

private theorem cap111011110100111101Accepted : Accepted table cap111011110100111101Box cap111011110100111101Tree := by
  decide +kernel

private def cap11101111010011110Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111011110100111100Tree <*> cap111011110100111101Tree

private theorem cap11101111010011110Accepted : Accepted table cap11101111010011110Box cap11101111010011110Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11101111010011110Box 0 (midpoint cap11101111010011110Box 0) = cap111011110100111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100111100Accepted
  · have h : rightBox cap11101111010011110Box 0 (midpoint cap11101111010011110Box 0) = cap111011110100111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100111101Accepted

private def cap11101111010011111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (21 / 32, 11 / 16), (27 / 32, 7 / 8)]

private def cap11101111010011111Tree : Option PackedTree := decode 6 0x3de1fde1dddffddfddcc7dcc5dcafdcadae4fae4dae37ae35ad2bad29ad11ad0e00213bbc3bbc37bbfbbbf7b98bb987b95bb957804b8047801b80177f4b7f477f337f2c4042770097008f0037002efe96fe8efe66fe5eb936b92eb8ceb8c6b4a6b496b43eb4308004e0fbbffbbfbbbc3bbbfb95fb95bb92fb92b5c6f5c6b5c335c2f5a235a1f59f359ec01427777f777ef777f777772b772af725772470037002effeeffe6fe66fe5efe36fe2a0204ee006e005dffddffcdfccdfcbdfc6dfc5d719d718d70ad709d687d686d67bd67a40009c1aee63ee62ee57ee56edc2edc1edb5edb4d695d694d688d687d609d608d5fed5fdbdcc5dcc3dcaddcabdb83db81db69db67ad29ad25ad0fad0dac11ac0fabfbabf95f72bf72b7725f72576daf6da76d476d3eb446b43eb3e6b3deaff6afeeaf9eaf95ee56ee55ee4aee49edb4edb3eda7eda6d687d686d67bd67ad5fdd5fcd5f2d5f110009cd1d727d726d71bd71ad695d694d688d687c8b5c8b4c8a5c8a4c827c826c81dc81c10009dae4dae4bae33ae31ad29ad25ad0fad0d9e919e8f9e839e819e599e579e4f9e4d73d233d1f3d073d033cb33caf3c9f3c9b22d322cb2293228f209b20972073206e87ae37ae35ae19ae17ad11ad0facf9acf7914b91499131912f903b903990259022a0213b5c675c635c2b5c275a1f5a1b59ef59eb3d073d033cef3ceb3c9f3c9b3c8b3c86e7a0e7a0679de79d6793e79367916790e4526451e44b644ae40e640de408e40850d6b4aeb4a6b446b43eb04eb046aff6afee413e413640ee40e63cb63cae3c5e3c55d694d692d687d686d608d607d5fdd5fcc826c825c81cc81bc795c794c78ac789af5a235a1f59f359ef57fb57f757cf57cb20772073204b20471e2f1e2b1dff1dfaeb43eb436b3deb3d6afeeafe6af96af8e40e640de408e40863c563c4e3bf63bed688

private theorem cap11101111010011111Accepted : Accepted table cap11101111010011111Box cap11101111010011111Tree := by
  decide +kernel

private def cap1110111101001111Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111010011110Tree <*> cap11101111010011111Tree

private theorem cap1110111101001111Accepted : Accepted table cap1110111101001111Box cap1110111101001111Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111101001111Box 3 (midpoint cap1110111101001111Box 3) = cap11101111010011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010011110Accepted
  · have h : rightBox cap1110111101001111Box 3 (midpoint cap1110111101001111Box 3) = cap11101111010011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010011111Accepted

private def cap111011110100111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101001110Tree <*> cap1110111101001111Tree

private theorem cap111011110100111Accepted : Accepted table cap111011110100111Box cap111011110100111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110100111Box 2 (midpoint cap111011110100111Box 2) = cap1110111101001110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101001110Accepted
  · have h : rightBox cap111011110100111Box 2 (midpoint cap111011110100111Box 2) = cap1110111101001111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101001111Accepted

private def cap11101111010011Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110100110Tree <*> cap111011110100111Tree

private theorem cap11101111010011Accepted : Accepted table cap11101111010011Box cap11101111010011Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111010011Box 1 (midpoint cap11101111010011Box 1) = cap111011110100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100110Accepted
  · have h : rightBox cap11101111010011Box 1 (midpoint cap11101111010011Box 1) = cap111011110100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110100111Accepted

private def cap1110111101001Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111010010Tree <*> cap11101111010011Tree

private theorem cap1110111101001Accepted : Accepted table cap1110111101001Box cap1110111101001Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111101001Box 0 (midpoint cap1110111101001Box 0) = cap11101111010010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010010Accepted
  · have h : rightBox cap1110111101001Box 0 (midpoint cap1110111101001Box 0) = cap11101111010011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010011Accepted

def cap111011110100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111101000Tree <*> cap1110111101001Tree

theorem cap111011110100Accepted : Accepted table cap111011110100Box cap111011110100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011110100Box 3 (midpoint cap111011110100Box 3) = cap1110111101000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101000Accepted
  · have h : rightBox cap111011110100Box 3 (midpoint cap111011110100Box 3) = cap1110111101001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101001Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover27
