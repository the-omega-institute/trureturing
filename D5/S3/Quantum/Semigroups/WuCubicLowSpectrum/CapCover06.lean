import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover06

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap110Box : Box := ![(1, 6 / 5), (0, 63 / 200), (1 / 2, 1), (1 / 2, 1)]

private def cap1100Box : Box := ![(1, 6 / 5), (0, 63 / 200), (1 / 2, 3 / 4), (1 / 2, 1)]

private def cap11000Box : Box := ![(1, 6 / 5), (0, 63 / 200), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap110000Box : Box := ![(1, 11 / 10), (0, 63 / 200), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap1100000Box : Box := ![(1, 11 / 10), (0, 63 / 400), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap1100000Tree : Option PackedTree := decode 5 0xcb13cb10cb10cb0fcad04acecacecace44364434c434c433c40043fec3fec3fe5886c886988698867880087fd87fd87fc808480818081807f8031802e802e802da25886584e587e5846573e571e5736571621a62172219e216a20822072207e206ecae7cae3cae6cae2cacecacccace4acc4410440e440fc40dc3fec3fcc3fe43fc5310d310b910cf10b510411039103f1037010300f100ff00ed0097008f0095008d620822072207e206e1ff61fe61ff21fe2012e011e012a011a00ba00aa00b600a690e5886587e584e5846573e5736571e571621a6219e2172216a2082207e2072206ecae7cae6cae3cae2cacecace4acccacc4410440fc40e440dc3fec3fe43fcc3fc5310d310cf10b910b51041103f10391037010300ff00f100ed00970095008f008d62082207e2072206e1ff61ff21fe61fe2012e012a011e011a00ba00b600aa00a6912c3f2c232c232c1f2b9b2b8b2b8b2b8710cf10b510b510b1103f1037103710356573657165716570e567256625662565e207e206e206e206a1ff21fe21fe21fde98867885a885a885887fc87f887f887f7807f807680768075802d802980298028a1a

private theorem cap1100000Accepted : Accepted table cap1100000Box cap1100000Tree := by
  decide +kernel

private def cap1100001Box : Box := ![(1, 11 / 10), (63 / 400, 63 / 200), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap1100001Tree : Option PackedTree := decode 7 0x32db12da72da72da52d012cf72cf72cf5121b12111211120f116f11651165116365b4e5b365b4a5b3259ee59d659ea59d22422240a241e240622ca22b222c622aeb96d396d296cd96cc967b967a96759674890889078902890188b288b188ac88abb2da52d992d992d972cf52ce92ce92ce7120f12031203120111631157115711555a9680967596759673962796219621961f88b788ac88ac88aa886c886988698867a62436240a2422240622de22b222ca22ae0466043a0452043603220302031602fec4844480c481448044594455c4564455408a4086c08740864062c05fc060405f55116f11591159115510d910d310d310cf019101810181017d01090103010300ff4892d992d8b2d972d892ce92cdb2ce72cd9120311f5120111f31157114911551147635259d2599659ce59925882584a587e584622ae227622aa227221a2216e219e216aa32240623ce240223ca22ae227622aa2272043603fe043203fa02fe02c602fa02c2a91157113b1155113910d110b710cf10b5017f0163017d0161010100ef00ff00ed510e5b365b325b1a5b1659d659d259ba59b6240a240623ee23ea22b222ae22962292cb664b65cb62cb624b3a4b39cb36cb364480c480447d447cc455c45544524451d72d8d2d8b2d7d2d7b2cdd2cdb2ccd2ccb11f711f511e911e7114b1149113d113b65b165b125af65af259b659b25996599223ea23e623ce23ca2292228e22762272b52ceb2ce72cdd2cd92c432c3f2c352c3111591155114b114710d310cf10c710c3659ba59b6599a5996586a5866584e584a22962292227a2276218e218a2172216ecb36cb364b32cb324b0ccb0c4b094b08c4524451c44ec44e44314430c42dc42d568c4814480c47dc47d44564455c452c45240874086c083c0834060405fc05cc05c58901890088fa88f988ab88aa88a488a3810d810c8106810580bf80be80b880b7ae23ee23ea23d223ce22962292227a2276041e041a040203fe02e602e202ca02c6c47d447cc479c47944524451c44ec44e40834082c07fc07f405c405bc058c05856a22b222aa2296228e21a6219e218e2186030202fa02e602de020601fe01f201eec452c451c44f444e4431c430c42e442d405cc05bc0594058403e403dc03c403b5444b65cb5e4b624b5dcb39cb324b364b31c4804479447cc478c455444e4451c44dd96c496bb96bc96ba966c96639664966288f988f188f288f088a3889b889c889aaa59ce599259b2598e587e58465862584222aa2272228e226e219e216a21862166cb364b31cb324b314b0c4b084b08cb07c451c44dc44e444d4430c42cc42d442c546240223ca23ca23c222aa22722272226a043203fa03fa03f202fa02c202c202bec455444e444e444d4433c42d442d442c405f405840584057c03fc03b403b403ad21a

private theorem cap1100001Accepted : Accepted table cap1100001Box cap1100001Tree := by
  decide +kernel

private def cap110000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap1100000Tree <*> cap1100001Tree

private theorem cap110000Accepted : Accepted table cap110000Box cap110000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap110000Box 1 (midpoint cap110000Box 1) = cap1100000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100000Accepted
  · have h : rightBox cap110000Box 1 (midpoint cap110000Box 1) = cap1100001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100001Accepted

private def cap110001Box : Box := ![(11 / 10, 6 / 5), (0, 63 / 200), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap1100010Box : Box := ![(11 / 10, 6 / 5), (0, 63 / 400), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap1100010Tree : Option PackedTree := decode 6 0xf4f1f4eef4eef4edf4c574c3f4c3f4c2d78557825782578157595757d757d756de98ae987e987e985e94fe94ce94ce94baeb2aeafaeafaeadae79ae76ae76ae75a6bc2abc12bc12bc0abacababebabebab6589e58865886587e574a573e573e5736d7595757d757d756d73cd73b573b573acae94ae7cae7cae6cad04acecacecace52274ee74e6f4edf4e674c374bef4c2f4be5781d77a57815779d7575752d756d75255d30fd2fdd30bd2f9d299d291d297d28f5d5f5d4d5d5b5d495ced5ce55ceb5ce34caf03aef4af02aef3aeaeaea5aeadaea496209612961f961195ce95c695cd95c5aababeba9abab6ba92b9dab9cab9d6b9c6573e571e57365716567656665672566290fa777a76fa75ba753a61fa617a60fa60abc12bc0abbf6bbeebabebab6baaebaaaf4eb74ea74e774e674c1f4c174bf74be577ed77dd77ad779d755d7555753575255d30fd30bd2fdd2f9d299d297d291d28f5d5f5d5b5d4d5d495ced5ceb5ce55ce34d7825781577ed77dd757d756d755d7554b10cb0fcb0d4b0c4ae7cae6cae5cae55aefdaefbaef5aef3aeabaeaaaea6aea4961a96189613961195cb95ca95c795c5aababebab6ba9aba92b9dab9d6b9cab9c6573e5736571e5716567656725666566291d3b7d399d3a9d397d30bd2f9d305d2f75e055de75df75de55d5b5d495d555d477a753a72fa733a72ba60ba5efa5f3a5eabbeebbcabbcebbc6baaaba8eba92ba8aae985e97ce97ce97ae94be947e947e946aeadaea4aea4aea2ae75ae71ae71ae70a6bc0abbcebbcebbc6bab6ba92ba92ba8a587e58465846583e573657165716570ed756d75257525751573ad738d738d7384ae6cae2cae2cae1cace4acc4acc4acbd21a

private theorem cap1100010Accepted : Accepted table cap1100010Box cap1100010Tree := by
  decide +kernel

private def cap1100011Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap11000110Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 5 / 8), (1 / 2, 3 / 4)]

private def cap110001100Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 5 / 8), (1 / 2, 5 / 8)]

private def cap110001100Tree : Option PackedTree := decode 5 0x3d55bd545d545d543d463d455d455d4535f955f875f875f855ead5e9f5e9f5e9d7aa8baa5baa87aa57a8aba88ba8a7a886bf0ebedebf0abedabd3ebd1ebd3abd1abeaa2eaa1ea96ea95ea2aea29ea22ea21afc3afc2afb7afb6af4faf4eaf47af46bd543d52bd52bd529d453d443d443d4415f855f6d5f6d5f6b5e9d5e8d5e8d5e8b5aea31ea2aea2aea29e9dbe9d4e9d4e9d3af56af4faf4faf4eaf02aefbaefbaefabd455d445d453d443d3a9d399d3a7d3975e9f5e8f5e9d5e8d5df75de75df55de55f5157514f5117510f4ea74e9f4e674e5d7a7d7a757a3d7a3577dd77d5779d7795ea29ea21ea21ea20e9d3e9cbe9cbe9caaf4eaf46af46af45aefaaef2aef2aef1ad1afcaafc3afc3afc2af56af4faf4faf4e96cb96c496c496c39673966c966c966bb5f875f6f5f855f6d5e9f5e8f5e9d5e8d2d892d792d872d772cd92cc92cd72cc75d7e1d7e157dbd7db57a7d7a757a3d7a34b624b61cb5e4b5dcb364b35cb324b31dafc2afb6afb6afb5af4eaf46af46af4596c396bb96bb96ba966b966396639662ad57ab57a3d7a7d7a357815779d77dd7794b39cb324b364b31cb0fcb08cb0c4b085af4faf46af47af45aefbaef2aef3aef1966c966396649662961896109611960fa88

private theorem cap110001100Accepted : Accepted table cap110001100Box cap110001100Tree := by
  decide +kernel

private def cap110001101Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap110001101Tree : Option PackedTree := decode 7 0x3d55fd55dd549d547d4cbd4c9d4c3d4c18991898f897b897989158913890d890b7a997a993a987a983a8cfa8cba8b3a8af122b1227121b121711cb11c711b311ae9c4c8c4c7c4bdc4bcc472c471c46cc46bafccafcbafc5afc4af58af57af51af50a3aabbaab7aa8faa8ba8cba8c7a8afa8ab131f131b12f312ef11c711c311af11aae263e263625e625de238e2386235e23557e5d7e557e257e1d7abd7ab57a857a7d0faa93aa8faa63aa5fa987a983a977a97312f712f312c712c3121b1217120b1206f530f530752ef52e75167515f5127511e2436242e2416240e2366235e2336232d3897b897989638961890d890b890589035f8b5f895f735f715f0f5f0d5f075f057121b1217120b120711b311af119b1196be1ebe1abe0ebe0abd46bd42bd26bd2291d547d545d52fd52dd457d455d447d445897989778961895f88d788d588cb88c9712f312ef12c312bf11af11ab11971192bf12bf0ebee2bedebd42bd3ebd22bd1e86ba8cfa8cba8b3a8afa777a773a75ba756bd62bd5ebd46bd42bc12bc0ebbf6bbf2f5197518f515f51574ee74edf4eaf4ea57abd7ab57a857a7d781d781577e577dd7d459d457d449d447d3add3abd39dd39b5ea35ea15e935e915dfb5df95deb5de97a8afa8aba88fa88ba757a753a737a732bd42bd3ebd22bd1ebbf2bbeebbd2bbceb46bf32bf2ebf16bf12bd62bd5ebd46bd428316831282fa82f6826682628252824ed062d062505f505ed04cd04c504a5049cb66cb664b634b62cb3acb3a4b374b36d15f975f955f895f875eaf5ead5ea15e9f2d992d972d8b2d892ce92ce72cdb2cd95d7e2d7e257dcd7dc57a8d7a857a4d7a4505f505ed05bd05b504a5049d0475046da0bea0bda0b7a0b6a094a093a08ea08d96c696c596be96bd966e966d96669665a2bf12bf0ebee2bedebd42bd3ebd22bd1e82f682f282da82d6824e824a82368232d05ed05e505b505ad049d0495046d0464b62cb624b5ecb5e4b36cb364b32cb3250d57ac57abd7a8d7a857825781d77ed77e4b3acb3a4b374b36cb10cb104b0d4b0cdaf57af56af50af4faf03af02aefcaefb96749673966d966c9620961f96199618aebd46bd42bd26bd22bbf6bbf2bbd6bbd259ba59b6599a5996586a5866584e584ad7a857a7d7a457a3d77e577dd77a5779cb36cb364b32cb324b0ccb0c4b094b08d688

private theorem cap110001101Accepted : Accepted table cap110001101Box cap110001101Tree := by
  decide +kernel

private def cap11000110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap110001100Tree <*> cap110001101Tree

private theorem cap11000110Accepted : Accepted table cap11000110Box cap11000110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11000110Box 3 (midpoint cap11000110Box 3) = cap110001100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110001100Accepted
  · have h : rightBox cap11000110Box 3 (midpoint cap11000110Box 3) = cap110001101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110001101Accepted

private def cap11000111Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (5 / 8, 3 / 4), (1 / 2, 3 / 4)]

private def cap11000111Tree : Option PackedTree := decode 7 0xf55d755af55af55a751f751cf51cf51c57ebd7e957e957e8d7b1d7af57af57aedeab5eaafeab4eaaeea39ea33ea38ea32c4cec4c8c4cdc4c7c477c472c476c471b899d8991899b898f88ef88e588ed88e35fa55f995fa35f975ebd5eb15ebb5eaf43eab5eab4eaafeaaeea39ea38ea33ea32c4cec4cdc4c8c4c7c477c476c472c471b899d899b8991898f88ef88ed88e588e35fa55fa35f995f975ebd5ebb5eb15eaf4755a755775577556f51c751975197518d7e8d7e5d7e5d7e557aed7abd7abd7ab56ba8fba8cfa8e7a8cba78fa777a787a772bd8ebd62bd7abd5ebc2abc12bc22bc0ef51cf5197519f518f4f0f4ee74eef4edd7af57abd7ac57ab57845781d7825781546bf5ebf4abf4abf46bd8ebd7abd7abd765b625b4e5b4e5b4a5a0259ee59ee59ead7e957e657e8d7e5d7af57ac57aed7abcb69cb66cb694b664b3dcb3acb3d4b3a575fa55fa35f995f975ebd5ebb5eb15eaf2da72da52d9b2d992cf72cf52ceb2ce96bf46bf2ebf2ebf2abd76bd5ebd5ebd5a5b4a5b325b325b2e59ea59d259d259ceb55ec75eb15ebd5eaf5e155e095e115e072d012ceb2cf72ce92c4f2c432c4b2c416bd7abd5ebd62bd5abc22bc0ebc12bc0a59ee59d259d659ce589658825886587ea2275577551f556f55175197515f518f5156263e25e6263625de238e235e23862355c4c7c4bcc4c6c4bbc471c46bc470c46aafcbafc4afcaafc3af57af50af56af4fa2353a8cba8afa8c7a8aba773a757a76fa752bd5ebd42bd5abd3ebc0ebbf2bc0abbeec68cafcbafc4afcaafc3af57af50af56af4f96cc96c596cb96c49674966d9673966cb1a95eaf5ea15ead5e9f5e075df95e055df72ce92cdb2ce72cd92c412c332c3f2c3163443

private theorem cap11000111Accepted : Accepted table cap11000111Box cap11000111Tree := by
  decide +kernel

private def cap1100011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11000110Tree <*> cap11000111Tree

private theorem cap1100011Accepted : Accepted table cap1100011Box cap1100011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1100011Box 2 (midpoint cap1100011Box 2) = cap11000110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11000110Accepted
  · have h : rightBox cap1100011Box 2 (midpoint cap1100011Box 2) = cap11000111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11000111Accepted

private def cap110001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap1100010Tree <*> cap1100011Tree

private theorem cap110001Accepted : Accepted table cap110001Box cap110001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap110001Box 1 (midpoint cap110001Box 1) = cap1100010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100010Accepted
  · have h : rightBox cap110001Box 1 (midpoint cap110001Box 1) = cap1100011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100011Accepted

private def cap11000Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap110000Tree <*> cap110001Tree

private theorem cap11000Accepted : Accepted table cap11000Box cap11000Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11000Box 0 (midpoint cap11000Box 0) = cap110000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110000Accepted
  · have h : rightBox cap11000Box 0 (midpoint cap11000Box 0) = cap110001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110001Accepted

private def cap11001Box : Box := ![(1, 6 / 5), (0, 63 / 200), (1 / 2, 3 / 4), (3 / 4, 1)]

private def cap110010Box : Box := ![(1, 11 / 10), (0, 63 / 200), (1 / 2, 3 / 4), (3 / 4, 1)]

private def cap1100100Box : Box := ![(1, 11 / 10), (0, 63 / 400), (1 / 2, 3 / 4), (3 / 4, 1)]

private def cap1100100Tree : Option PackedTree := decode 5 0x32c552c532c492c472b452b432b3f2b3d10dd10db10d710d5100510030fff0ffd621ba21b621ae21aa200a20061ffe1ffa021a0216020e020a00ce00ca00c200be8962996279623962195a195a0959e959d886d886c886a88698801880087fe87fdb10db10d910d510d3100310010ffd0ffb010b01090105010300650063005f005d43962496239617961595d195d095c995c8886b886a8860885e88228821881e881db2ba32ba12b932b912b3f2b3d2b372b3510451043103d103b0fff0ffd0ff70ff54c435c4354430442f44114410c40f440ec041c041403d403cc026c0264024c024588228821881e881d87ff87fe87fb87fa804d804c804980488030802f802c802ba44b11cb10cb0acb09cae84ae7cae44ae3c4354434c42f442e4410c410440ec40e595d095cf95c895c7959e959d959a959988218820881d881c87fe87fd87fa87f9a621aa21a6217a21722086208220762072020a020601e601e20132012e0122011ec410c410440ec40e43ff43fec3fd43fcc0264025c0244023c017c0174015c015521a

private theorem cap1100100Accepted : Accepted table cap1100100Box cap1100100Tree := by
  decide +kernel

private def cap1100101Box : Box := ![(1, 11 / 10), (63 / 400, 63 / 200), (1 / 2, 3 / 4), (3 / 4, 1)]

private def cap11001010Box : Box := ![(1, 11 / 10), (63 / 400, 63 / 200), (1 / 2, 5 / 8), (3 / 4, 1)]

private def cap11001010Tree : Option PackedTree := decode 7 0x32da32da12d952d932cf32cf12ce52ce3120d120b11ff11fd1161115f1153115165b425b3e5b265b2259e259de59c659c22416241223fa23f622be22ba22a2229eb96ca96c996c296c196729671966a966988ff88fe88f888f788a988a888a288a1b2d932d912d832d812ce32ce12cd32cd11cfd1cfb1cf11cef1cbb1cb91cb31cb1639fa39f639e239de397639723966396223fa23f623de23da22a2229e2286228286a59e659de59ca59c25892588e587a587222c222ba22a6229e21ae21aa219a2196cb394b384b354b344b0f4b0e4b0bcb0ac454c453c451445044334432c430442f546241a241623fe23fa22c222be22a622a2044a0446042e042a0312030e02f602f2c482c482447f447ec457c45744544453c088c08840854084c061c061405e405dd711ff11fd11f111ef11531151114511430217021502090207017b0179016d016b623fa23f623de23da22a2229e22862282042a0426040e040a02f202ee02d602d2b51161115d1153114f10d710d510cd10cb01890185017b01770107010500fd00fb622a6229e228a2282219a21962182217a02f602ee02da02d201fa01f601ea01e6a225b3e5b3a5b225b1e59de59da59c259be2412240e23f623f222ba22b6229e229acb674b66cb63cb634b3b4b3acb37cb374481c481447e447dc456c45644534452d72d912d8f2d812d7f2ce12cdf2cd12ccf1cfb1cf91cef1ced1cb91cb71cb11caf639f639f239de39da3972396e3962395e23f623f223da23d6229e229a2282227e896c796c696bf96be966f966e966796668e7c8e7b8e768e758e5b8e5a8e578e56b1cf91cf71ced1ceb1cb71cb51caf1cad11f911f711eb11e9114d114b113f113d4352cef2ceb2ce12cdd2c472c432c392c35115d1159114f114b10d510d310cb10c7659c259be59a2599e5872586e58565852229e229a2282227e21962192217a2176cb37cb374b33cb334b0dcb0d4b0a4b09c4534452c44fc44f44324431c42ec42e568c4824481c47ec47e44574456c453c45340884087c084c08440614060c05dc05d58903890288fc88fb88ad88ac88a688a5810f810e8108810780c180c080ba80b9ae23f623f223da23d6229e229a2282227e04260422040a040602ee02ea02d202cec47e447dc47ac47a44534452c44fc44f40844083c080c080405d405cc059c05956a22ba22b2229e229621aa21a62196218e030a030202ee02e6020a020601f601f2c453c452c450444f4432c431c42f442e405dc05cc05a4059403ec03e403cc03c5443

private theorem cap11001010Accepted : Accepted table cap11001010Box cap11001010Tree := by
  decide +kernel

private def cap11001011Box : Box := ![(1, 11 / 10), (63 / 400, 63 / 200), (5 / 8, 3 / 4), (3 / 4, 1)]

private def cap11001011Tree : Option PackedTree := decode 6 0x32db92db52daf2dab2d072d052cff2cfb1223121f1219121511751173116d116965b5e5b5a5b465b4259fe59fa59e659e22432242e241a241622da22d622c222becb6b4b6acb684b67cb3f4b3ecb3c4b3bc485c4854482c482445ac45a4457c45756a5a0e5a0a59e659de58aa58a65892588e22ea22e622c222ba21ba21b621ae21aa98911890f890c890a88ba88b988b688b4811d811b8118811680cb80ca80c780c6b12191215120d1209116d11691161115d0231022d02250221018f018d018901855445d445cc458445744374436c435c4354065c0654062406140434042c041c0415225b6a5b625b565b4e5a0a5a0259f659ee243e2436242a242222e622de22d222cacb6acb6a4b67cb674b3ecb3e4b3bcb3b44854484c4824481c45a4459c4574456d96d496d396ce96cd967c967b96769675890989088903890288b388b288ad88acad4b414b404b3bcb3acb14cb13cb11cb10c45cc45bc45744564436c43644354434d3121f121b121512111173116f1169116502370233022d022901950191018d018b6242a24222412240a22d222ca22ba22b2045a04520442043a031a0316030a0302a88b988b788ae88ac886d886c886a886980ca80c880c280c08085808480828081a43

private theorem cap11001011Accepted : Accepted table cap11001011Box cap11001011Tree := by
  decide +kernel

private def cap1100101Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11001010Tree <*> cap11001011Tree

private theorem cap1100101Accepted : Accepted table cap1100101Box cap1100101Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1100101Box 2 (midpoint cap1100101Box 2) = cap11001010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11001010Accepted
  · have h : rightBox cap1100101Box 2 (midpoint cap1100101Box 2) = cap11001011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11001011Accepted

private def cap110010Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap1100100Tree <*> cap1100101Tree

private theorem cap110010Accepted : Accepted table cap110010Box cap110010Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap110010Box 1 (midpoint cap110010Box 1) = cap1100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100100Accepted
  · have h : rightBox cap110010Box 1 (midpoint cap110010Box 1) = cap1100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100101Accepted

private def cap110011Box : Box := ![(11 / 10, 6 / 5), (0, 63 / 200), (1 / 2, 3 / 4), (3 / 4, 1)]

private def cap1100110Box : Box := ![(11 / 10, 6 / 5), (0, 63 / 400), (1 / 2, 3 / 4), (3 / 4, 1)]

private def cap1100110Tree : Option PackedTree := decode 6 0x3d3cdd3cbd3c1d3bfd2a3d2a1d29dd29b5e1b5e195e0f5e0d5cf75cf55cf15cef6bc36bc32bc1ebc1ab9eeb9eab9e2b9de58aa58a65892588e568a5686567e567a8e9e5e9e3e9dfe9dde98be98ae988e987af0caf0aaf06af04aeb3aeb2aeb0aeafbd317d315d311d30fd2a1d29fd29bd2995d675d655d615d5f5cf55cf35cef5ced4d7865785578357825759d75957585757cb14cb13cb11cb10cae9cae94ae84ae7daeb3aeb2aeb0aeafae7aae79ae77ae7695d395d295d095cf95a195a0959e959da43e9e0e9dfe9d2e9d0e989e988e981e980af07af06aef9aef7aeb1aeb0aea9aea8bd313d311d303d301d29dd29bd295d2935d635d615d535d515cf15cef5ce95ce74d783d783577cd77bd758d7585754d7544b124b11cb0bcb0acae8cae84ae4cae45aeb1aeb0aea9aea8ae78ae77ae74ae7395d195d095c995c8959f959e959b959aa474eff4eef4ec74eb74c474c3f4c274c1d7835782577fd77ed7585757d7565755de9d8e9d6e9d0e9cee984e983e980e97eaeffaefdaef7aef5aeacaeabaea8aea6aba623a61fa603a5fba537a533a527a522bac2babebaa2ba9ab9deb9dab9ceb9ca9af06af04aeffaefdaeb0aeafaeacaeab96239621961c961a95d095cf95cc95cbb5dff5dfb5def5deb5d595d575d515d4d2c392c352c2b2c272b992b972b912b8f557585757d7545753573bd73b5739d7394ae84ae7cae44ae3cacf4acecacd4accd21a

private theorem cap1100110Accepted : Accepted table cap1100110Box cap1100110Tree := by
  decide +kernel

private def cap1100111Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 3 / 4), (3 / 4, 1)]

private def cap11001110Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 5 / 8), (3 / 4, 1)]

private def cap110011100Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 5 / 8), (3 / 4, 7 / 8)]

private def cap110011100Tree : Option PackedTree := decode 7 0xf558f55875537552f51af51a75177516e2656264e25fe25f623a6239e2376236dc4cac4c9c4bfc4bec474c473c46ec46dafceafcdafc7afc6af5aaf59af53af52a3aac3aabfaa97aa93a99ba997a98ba9871327132312fb12f7122f122b121f121af5337532f5317530f51a7519f516f5166245e2456243e2436239e2396236e2365389938991897d897b88e788e588db88d95f9b5f995f8d5f8b5eb35eb15ea55ea343eaa6eaa5ea9aea99ea63ea62ea5fea5ec4bfc4bec4b3c4b2c488c487c484c483bd4c7d4c5d4bfd4bdd45dd45bd44dd44b8911890f8909890788dd88db88d188cf4e25fe25f6259e25962446243e2426241d7e3d7e357de57dd57c4d7c457c2d7c25c488c487c484c483c46ec46dc468c467af89af88af85af84af53af52af4baf4aa47552f552754cf54c75317530f52f752ee25f625ee2596258e243e2436241e2415ea62ea61ea5eea5dea2dea2cea25ea24c487c486c483c482c46dc46cc467c466a712fb12f712cb12c7121f121b120f120abf1abf16beeabee6be22be1ebe12be0ee243e2436241e2416236e2366233e23357c457c3d7c257c1d7a957a8d7a557a4d21aea35ea34ea2eea2de9dfe9dee9d8e9d7af5aaf59af53af52af06af05aeffaefebd469d467d45bd459d3bdd3bbd3afd3ad5eb35eb15ea55ea35e0b5e095dfd5dfb5f5177516f5137512f4ec74ebf4e874e7d7a9d7a957a5d7a5577fd77f577bd77b5ea2dea2cea25ea24e9d7e9d6e9cfe9ceaf52af51af4aaf49aefeaefdaef6aef5ad1afceafcdafc7afc6af5aaf59af53af52a0c7a0c6a0c0a0bfa09ba09aa096a095b418f418d4181417f41374135412d412b2d9f2d9d2d912d8f2cef2ced2ce12cdf457e6d7e657e357e2d7acd7ac57a957a8d0635062d05fd05f504d504cd04ad04a5a0c6a0c5a0bfa0bea09aa099a095a09496ce96cd96c796c696769675966f966ea1d7e3d7e357de57ddd7a9d7a957a5d7a55060505fd05cd05c504b504ad048504788002ea0c0a0bfa0b9a0b8a096a095a090a08f96c896c796c096bf9670966f96689667a2bf1abf16beeebee6bd4abd46bd2abd2682fe82fa82e282de82568252823e823880017505fd05f505c505bd04ad04a5047d0474b63cb634b5fcb5f4b37cb374b33cb3350d57ad57acd7a9d7a957835782d77fd77f4b3bcb3b4b384b37cb11cb114b0e4b0ddaf59af58af52af51af05af04aefeaefd96769675966f966e96229621961b961aaebd4ebd4abd2ebd2abbfebbfabbdebbda59c259be59a2599e5872586e58565852d7a957a8d7a557a4d77f577ed77b577acb37cb374b33cb334b0dcb0d4b0a4b09d688

private theorem cap110011100Accepted : Accepted table cap110011100Box cap110011100Tree := by
  decide +kernel

private def cap110011101Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (1 / 2, 5 / 8), (7 / 8, 1)]

private def cap110011101Tree : Option PackedTree := decode 6 0xf559f55975547553f51bf51b75187517d7e857e7d7e4d7e457ae57add7aad7aa5eab2eab1eaa7eaa6ea36ea35ea2fea2ec4cbc4cac4c0c4bfc475c474c46fc46eb899789958981897f88eb88e988df88dd5f9f5f9d5f915f8f5eb75eb55ea95ea743eaa8eaa7ea9cea9bea30ea2fea28ea27afc9afc8afbeafbdaf55af54af4daf4cbd54fd54dd537d535d45fd45dd44fd44d8981897f8969896788df88dd88d388d17130312ff12d312cf11bf11bb11a711a2bf22bf1ebef6bef2bd52bd4ebd32bd2e86ba8dfa8d7a8c3a8bba783a77fa76ba762bd72bd6abd56bd4ebc1ebc1abc06bbfef5187517f5147513f4ed74ecf4e974e8d7aad7aa57a6d7a65780d780577cd77c5ea2fea2eea27ea26e9d9e9d8e9d1e9d0af54af53af4caf4baf00aeffaef8aef7ad1afd0afcfafc9afc8af5caf5baf55af5496d196d096ca96c99679967896729671b5f9f5f9d5f915f8f5eb75eb55ea95ea72da12d9f2d932d912cf12cef2ce32ce15d7e4d7e457df57ded7aad7aa57a6d7a64b654b64cb614b60cb394b38cb354b34dafc8afc7afbdafbcaf54af53af4caf4ba0c1a0c0a0baa0b9a097a096a091a090b4183418141754173412f412d412341212d932d912d832d812ce32ce12cd32cd14355eb95eb55eab5ea75e0f5e0d5e035dff2cf32cef2ce52ce12c492c472c3d2c396bd56bd52bd36bd32bc06bc02bbe6bbe259ca59c659aa59a6587a5876585e585ad7aa57a9d7a657a5d780577fd77c577bcb38cb384b34cb344b0ecb0e4b0b4b0ad688

private theorem cap110011101Accepted : Accepted table cap110011101Box cap110011101Tree := by
  decide +kernel

private def cap11001110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap110011100Tree <*> cap110011101Tree

private theorem cap11001110Accepted : Accepted table cap11001110Box cap11001110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11001110Box 3 (midpoint cap11001110Box 3) = cap110011100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110011100Accepted
  · have h : rightBox cap11001110Box 3 (midpoint cap11001110Box 3) = cap110011101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110011101Accepted

private def cap11001111Box : Box := ![(11 / 10, 6 / 5), (63 / 400, 63 / 200), (5 / 8, 3 / 4), (3 / 4, 1)]

private def cap11001111Tree : Option PackedTree := decode 7 0x3d57dd579d573d56fd483d481d47bd4775fb75fb35fad5fa95ecd5ecb5ec55ec17aae7aae3aacfaacba8f7a8f3a8dfa8dabf5abf56bf42bf3ebd8abd86bd72bd6ef55c755bf5597558f51e751df51b751ad7ead7ea57e7d7e757b0d7b057add7ad56ba907a903a8dfa8d7a79ba797a783a77ebd9abd96bd72bd6abc36bc32bc1ebc1a9afdbafd9afd6afd4af66af65af62af6096dc96da96d796d596839682967f967db5fad5fab5fa15f9f5ec55ec35eb95eb72daf2dad2da32da12cff2cfd2cf32cf16bf56bf52bf3ebf3abd86bd82bd6ebd6a5b5a5b565b425b3e59fa59f659e259deb55ecd5ecb5eb95eb55e1b5e195e0f5e0d2d072d052cf32cef2c552c532c492c4748eabceabbeab7eab6ea40ea3fea3bea3aafd9afd8afd4afd3af65af64af60af5fbd577d575d56dd56bd47fd47dd475d4735fb15faf5fa75fa55ec95ec75ebf5ebd5f55bf55b7558f558751df51d751af51a57ea57e9d7e757e6d7b057afd7ad57acdeab6eab5eab0eaafea3aea39ea34ea33c4cfc4cec4c9c4c8c478c477c473c472b899f899d8993899188f188ef88e788e55fa75fa55f9b5f995ebf5ebd5eb35eb1435d481d47dd477d473d3cbd3c7d3c5d3c35ecb5ec75ec15ebd5e195e155e135e117a8efa8e7a8d7a8cfa78ba787a77fa776bd82bd7abd6abd62bc26bc22bc1abc12a35fb35faf5fa95fa55ecb5ec75ec15ebd2db52db12dab2da72d052d012cfb2cf76bf52bf4ebf3abf36bd82bd7ebd6abd665b565b525b3e5b3a59f659f259de59dad7e9d7e957e6d7e657afd7af57acd7ac4b6a4b69cb674b66cb3e4b3dcb3b4b3ad6abd96bd8ebd82bd7abc32bc2abc26bc225a0a5a0259f659ee58a6589e589a5896d7b057af57ad57ac5784d784578357824b3ecb3dcb3bcb3acb134b12cb11cb10d443

private theorem cap11001111Accepted : Accepted table cap11001111Box cap11001111Tree := by
  decide +kernel

private def cap1100111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11001110Tree <*> cap11001111Tree

private theorem cap1100111Accepted : Accepted table cap1100111Box cap1100111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1100111Box 2 (midpoint cap1100111Box 2) = cap11001110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11001110Accepted
  · have h : rightBox cap1100111Box 2 (midpoint cap1100111Box 2) = cap11001111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11001111Accepted

private def cap110011Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap1100110Tree <*> cap1100111Tree

private theorem cap110011Accepted : Accepted table cap110011Box cap110011Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap110011Box 1 (midpoint cap110011Box 1) = cap1100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100110Accepted
  · have h : rightBox cap110011Box 1 (midpoint cap110011Box 1) = cap1100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100111Accepted

private def cap11001Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap110010Tree <*> cap110011Tree

private theorem cap11001Accepted : Accepted table cap11001Box cap11001Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11001Box 0 (midpoint cap11001Box 0) = cap110010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110010Accepted
  · have h : rightBox cap11001Box 0 (midpoint cap11001Box 0) = cap110011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110011Accepted

private def cap1100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11000Tree <*> cap11001Tree

private theorem cap1100Accepted : Accepted table cap1100Box cap1100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1100Box 3 (midpoint cap1100Box 3) = cap11000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11000Accepted
  · have h : rightBox cap1100Box 3 (midpoint cap1100Box 3) = cap11001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11001Accepted

private def cap1101Box : Box := ![(1, 6 / 5), (0, 63 / 200), (3 / 4, 1), (1 / 2, 1)]

private def cap11010Box : Box := ![(1, 6 / 5), (0, 63 / 200), (3 / 4, 1), (1 / 2, 3 / 4)]

private def cap11010Tree : Option PackedTree := decode 9 0xc9d577d56dd575d56bd47fd475d47dd4735fb15fa75faf5fa55ec95ebf5ec75ebd6353a8ffa8d3a8fba8cfa793a77ba78fa776bd92bd66bd8ebd62bc2ebc16bc2abc12a32bf62bf4ebf5ebf4abd92bd7ebd8ebd7a5b665b525b625b4e5a0659f25a0259eec6a57b257acd7b1d7ac5785d782d78557824b40cb3b4b404b3acb144b114b13cb10d4446a74f2f4eff4f1f4eef4c5f4c474c574c3d7865783578557825759d75857595757de98be988e98ae987e950e94de94fe94caeb3aeb0aeb2aeafae7aae77ae79ae76a6bc32bc1abc2abc12bacebac2bacababe58a6588e589e5886574e5742574a573ed759d75857595757d73d573bd73cd73b4ae9cae84ae94ae7cad0cacf4ad04aced22346496d996d496d896d39681967c9680967b890e8909890d890888b888b388b788b2b1a9682967796809675962996239627962188b988ae88b788ac886d886a886c8869a644874481c486c481445c4456c45bc456408d4087c08cc0874064c060c0644060551173115d116f115910db10d510d910d30195018501910181010b010501090103488d4962996239627962195a1959e95a0959d886d886a886c8869880187fe880087fdb10db10d510d910d310030ffd10010ffb010b0105010901030065005f0063005d44688

private theorem cap11010Accepted : Accepted table cap11010Box cap11010Tree := by
  decide +kernel

private def cap11011Box : Box := ![(1, 6 / 5), (0, 63 / 200), (3 / 4, 1), (3 / 4, 1)]

private def cap110110Box : Box := ![(1, 11 / 10), (0, 63 / 200), (3 / 4, 1), (3 / 4, 1)]

private def cap110110Tree : Option PackedTree := decode 6 0x32dc72dc52dc52dc12c5b2c592c592c570247024502450241011301110111010f65b8a5b725b825b6a5a165a0e5a125a0a245a24462452243e22f222ea22ee22e6cb42cb41cb424b414b164b154b15cb14c45e445d445dc45cc43844374437c436d3122d12231229121f10e110dd10df10db0245023b024102370111010d010f010b4396e296e096dc96da9685968496839682891689148911890f88bc88bb88ba88b9b2d0b2d092d072d052c592c572c552c53117911771175117310e110df10dd10db4c48b448a4488c487c4384437c4374436c0914090408ec08dc0444043c0434042d12dc12db52db52db12d092d052d052d011229121f121f121b117711731173116f65a125a0a5a0a5a0258ae58a658a6589e22ee22e622e622de21be21b621b621b298914890f890f890d886f886d886d886c8120811b811b81198087808580858084a1a962d962c962c962b95a595a495a495a380898088808880878036803580358034b2c592c552c572c532b492b452b472b430111010d010f010b006b0067006900655cb164b15cb154b14cad24ad1cad14ad0c0444043c0434042c01ac01a4019c0195962b96299629962795a395a195a195a080878085808580848034803280328031ad1

private theorem cap110110Accepted : Accepted table cap110110Box cap110110Tree := by
  decide +kernel

private def cap110111Box : Box := ![(11 / 10, 6 / 5), (0, 63 / 200), (3 / 4, 1), (3 / 4, 1)]

private def cap110111Tree : Option PackedTree := decode 7 0xf5637562f562f561f4f4f4f474f474f3cb71cb714b714b704b16cb164b164b15deac5eabeeac3eabcea44ea41ea43ea40afe2afdbafe0afd9af69af66af68af65bd489d483d487d481d3d1d3cdd3cfd3cb5ed35ecd5ed15ecb5e1f5e1b5e1d5e194d7f157edd7f057ecd7b4d7b357b457b2cb714b6e4b704b6d4b42cb41cb424b415af69af66af68af65af0faf0daf0eaf0c9685968396849682962c962a962b9629a43eac5eac3eabeeabcea44ea43ea41ea40afe2afe0afdbafd9af69af68af66af65bd489d487d483d481d3d1d3cfd3cdd3cb5ed35ed15ecd5ecb5e1f5e1d5e1b5e194d7f157f057edd7ecd7b4d7b457b357b2cb714b704b6e4b6d4b42cb424b41cb415af69af68af66af65af0faf0eaf0daf0c9685968496839682962c962b962a9629a47561f55e7560755df521f5207521751fd7f057ecd7eed7ec57b457b2d7b3d7b25eac0eabbeabceabaea42ea3fea40ea3eafddafd8afd9afd7af67af64af65af63aba90fa903a903a8fba79fa797a797a78ebda2bd96bd96bd8ebc3abc32bc32bc2a9afe0afd9afd9afd7af68af65af65af6396e096da96da96d89684968296829680b5ed15ecb5ecb5ec75e1d5e195e195e152d092d052d052d012c572c532c532c4f486ba7a7a7a3a7a3a79fa553a54fa54fa54a58b658b258b258ae569656925692568ef4f474f374f3f4f2f4a9f4a8f4a974a84b164b154b15cb14cad24ad14ad1cad0d7d3d1d3cfd3cdd3cbd2a7d2a5d2a3d2a12c592c572c552c532b492b472b452b437a79fa797a797a78fa54ba543a543a53ebc3abc32bc32bc2ab9f2b9eab9eab9e6d787578657865785573e573d573d573ccb15cb14cb14cb13cad1cad0cad0cad050d1

private theorem cap110111Accepted : Accepted table cap110111Box cap110111Tree := by
  decide +kernel

private def cap11011Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap110110Tree <*> cap110111Tree

private theorem cap11011Accepted : Accepted table cap11011Box cap11011Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11011Box 0 (midpoint cap11011Box 0) = cap110110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110110Accepted
  · have h : rightBox cap11011Box 0 (midpoint cap11011Box 0) = cap110111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap110111Accepted

private def cap1101Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11010Tree <*> cap11011Tree

private theorem cap1101Accepted : Accepted table cap1101Box cap1101Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1101Box 3 (midpoint cap1101Box 3) = cap11010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11010Accepted
  · have h : rightBox cap1101Box 3 (midpoint cap1101Box 3) = cap11011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11011Accepted

def cap110Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1100Tree <*> cap1101Tree

theorem cap110Accepted : Accepted table cap110Box cap110Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap110Box 2 (midpoint cap110Box 2) = cap1100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1100Accepted
  · have h : rightBox cap110Box 2 (midpoint cap110Box 2) = cap1101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover06
