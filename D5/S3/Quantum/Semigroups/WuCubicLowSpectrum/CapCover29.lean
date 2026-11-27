import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover29

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap1110111101100Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap11101111011000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap111011110110000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101100000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (5 / 8, 21 / 32), (3 / 4, 13 / 16)]

private def cap1110111101100000Tree : Option PackedTree := decode 6 0x394a994a7948f948d92cf92cd92b992b779f179ef79d779d5788d788b787778757294f294b291b2917259b2597256f256af3def3daf3aaf3a6f116f112f0eaf0e6bca47ca45ca3bca3ac95cc95ac951c94fbcebbce9bce0bcdfbc3bbc39bc31bc2fab259f259b2573256f224f224b221b2216f11af116f0eef0eaee86ee82ee56ee52e4b364b2e4ade4ad64496448e442e4425e22de225e1d5e1cddd05dcfddca5dc9d792b992b792a392a1910d910b90f390f17877787578637861772b7729771377117256f256b2543253f2217221321e321def0eaf0e6f0c2f0beee52ee4eee22ee1eb46f3e2f3daf3aef3a6f11af112f0eef0e6d1aad1a2d172d16ecf16cf0ecee6cedede75de74de705e6fde1dde1cde18de17da2e5a2dda28da2859dcd9dbd9d759d6d5788d788b7877787577437741772b7729678b6789677367716631662f661766156f116f112f0eaf0e6ee82ee7eee52ee4ecf12cf0ecee2cedecc5ecc5acc2acc26bbc3bbc39bc31bc2fbb95bb93bb89bb87b3b9b3b7b3aeb3adb30bb309b2ffb2fea88ca52ca51ca3aca39c965c964c94fc94ebcf6bcf5bcdfbcdebc44bc43bc2fbc2eb92cb92c9929f929d9123912190ef90ed78897887785f785d773f773d770f770d4de7b5e7ade6fde6f5e225e21de17de175a345a33da285a27d9e1d9e159d6d9d65bc44bc43bc2fbc2ebb9fbb9ebb87bb86b3c3b3c2b3adb3acb316b315b2feb2fda43

private theorem cap1110111101100000Accepted : Accepted table cap1110111101100000Box cap1110111101100000Tree := by
  decide +kernel

private def cap1110111101100001Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101100001Tree : Option PackedTree := decode 7 0x394eb94e994c394c19309930792e792e5825f825d824782458189818781798177704bf04bb048f048b0313030f02f302eef44ef44af416f412f17ef17af14af1468ca74ca73ca60ca5fc983c982c972c971bd12bd11bd04bd03bc5ebc5dbc51bc50af298729832953294f25cf25cb259f259af416f412f3e2f3def14af146f11af116e530652fe529e52964b964b8e4b364b2de825e81de7bde7b5e28de285e22de2256b2613260f25cf25cb22bf22bb228722830313030f02f302ef0233022f021b0216e0626061e05e605de0466045e0436042de2fde2f5e295e28dddcdddc5dd6ddd6519307930592e592e3915d915b9141913f78bd78bb78a378a17771776f775977575e4b9e4b964b3e4b36450e4506449e4495e295e28de235e22ddd6ddd65dd0ddd05c972c971c966c965c8a0c89fc892c891bc51bc50bc45bc44bbacbbabbba0bb9fad1bd13bd12bd05bd04bc5fbc5ebc52bc51b486b485b478b477b3dfb3deb3d2b3d1b7a257a237a097a0778bd78bb78a378a1690b690968ef68ed67bd67bb67a367a15de82de825e7c5e7bde295e28de235e22da3c5a3bda355a34d9e959e8d9e2d9e25bd04bd03bcf7bcf6bc51bc50bc45bc44b477b476b469b468b3d1b3d0b3c4b3c3ad5e2fde2f5e295e28dddcdddc5dd6ddd659efd9ef59e959e8d998d99859925991dbc5ebc5dbc51bc50bbb8bbb7bbacbbabb3deb3ddb3d1b3d0b330b32fb323b322aef14af146f11af116eeb6eeb2ee86ee82cf4acf46cf16cf12cc92cc8ecc62cc5ede28de285e22de225dd65dd5ddd05dcfd9e8d9e859e259e1d991d991598bd98b5688ca73ca71ca5fca5ec982c980c971c970bd11bd10bd03bd02bc5dbc5cbc50bc4fb94bf94bd94a594a392e392e192cb92c97a077a0579ed79eb78a1789f78897887564c164c064b8e4b86456e455e44fe44f5e2ede2e5e285e27dddbdddb5dd5ddd55c971c970c965c964c89fc89ec891c890bc50bc4fbc44bc43bbabbbaabb9fbb9ea8de88de885e7b5e7ade2ede2e5e225e21da425a41da345a33d9eed9ee59e1d9e15bc5dbc5cbc44bc43bbb7bbb6bb9fbb9eb3ddb3dcb3c3b3c2b32fb32eb316b315a43

private theorem cap1110111101100001Accepted : Accepted table cap1110111101100001Box cap1110111101100001Tree := by
  decide +kernel

private def cap111011110110000Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101100000Tree <*> cap1110111101100001Tree

private theorem cap111011110110000Accepted : Accepted table cap111011110110000Box cap111011110110000Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110110000Box 2 (midpoint cap111011110110000Box 2) = cap1110111101100000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101100000Accepted
  · have h : rightBox cap111011110110000Box 2 (midpoint cap111011110110000Box 2) = cap1110111101100001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101100001Accepted

private def cap111011110110001Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap111011110110001Tree : Option PackedTree := decode 8 0xe6b366b2e6ac66abe5e065dfe5da65d9dfb6dfb65fb05fafdf0c5f0bdf05df055cd65cd64cd57cd56cbbfcbbecbb3cbb2bf6cbf6bbf5fbf5ebe17be16be0abe09af3563355b3533352f2ed32ecb2ea32e9afd82fd7afd52fd4ef82ef826f7fef7f6acbc0cbbfcbb4cbb3ca75ca74ca61ca60c1fac1f9c1f2c1f1c12fc12ec123c122b83f583f383e583e3825f825d824782457c317c2f7c177c157a277a257a0b7a09465dfe5df65d9e5d9653a6539e530652fdf0bdf0b5f055f04de895e88de825e81d7976997679751974f94c394c194a994a77c177c157bff7bfd7a0b7a0979f179ef72ecf2ecb2e9f2e9b2983297f294f294af82af826f7faf7f6f412f40ef3def3dab46fdb6fdb2fd82fd7ef862f85ef82ef82ada76da72da3ada36d5e6d5e2d5b2d5aedfb65fb5dfafdfaf5f0bdf0b5f055f04db4e5b4ddb46db465abc5abbdab5dab5577ec17ebd7ea97ea77c177c137bff7bfb6d1d6d196d036d016ad96ad56ac16abd55f0c5f0bdf05df055e89de895e82de825abcdabc5ab65ab5da435a42da3c5a3bdbe17be16be0abe09bd12bd11bd04bd03b578b577b56bb56ab485b484b477b476aef82ef82af7fef7faf416f412f3e2f3ded5b2d5aed582d57ed1e2d1ded1aad1a6df055f04deff5efede825e81de7bde7b5ab5dab55aafdaaf5a3bda3b5a34da345688cd64cd63cd4bcd4acbbecbbdcba6cba5bf6bbf6abf53bf52be16be15bdfdbdfcb977d977b974d974b94e794e394a594a37c2d7c2b7bfb7bf97a237a2179ed79eb4dfb5dfb55fa9dfa95f0b5f0adefedefe5b4ddb4d5b405b3fdabbdabb5aaf5aaedbe16be15bdfdbdfcbd11bd10bcf6bcf5b577b576b55eb55db484b483b468b467a43cd4ccd4bcd23cd22cba8cba6cb97cb96bf54bf53bf45bf44bdffbdfdbdecbdebb9751974d973b973994a994a5948f948b7bff7bfb7be97be779f179ed79d779d372e772e732e5f2e5b291f291728ef28eaf7d2f7cef7b2f7aef3aef3a6f382f37ea37ea97ea77e8b7e897bff7bfb7bd97bd76d036d016cdd6cdb6ac16abd6a976a956f7fef7f6f7d2f7cef3e2f3daf3aef3a6d582d57ad552d54ed1aad1a2d172d16edefa5ef9def65ef5de75de74de705e6fdaaa5aa9daa5daa55a2e5a2dda28da2854466a5e6a566916690e5296528e51d651cdfa9dfa95fa25fa1de7b5e7ade6fde6f5bf53bf52bf44bf43bcf6bcf5bcdfbcdeb680b67fb66db66cb468b467b450b44fa1a

private theorem cap111011110110001Accepted : Accepted table cap111011110110001Box cap111011110110001Tree := by
  decide +kernel

private def cap11101111011000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110110000Tree <*> cap111011110110001Tree

private theorem cap11101111011000Accepted : Accepted table cap11101111011000Box cap11101111011000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111011000Box 1 (midpoint cap11101111011000Box 1) = cap111011110110000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110110000Accepted
  · have h : rightBox cap11101111011000Box 1 (midpoint cap11101111011000Box 1) = cap111011110110001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110110001Accepted

private def cap11101111011001Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap111011110110010Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101100100Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (5 / 8, 21 / 32), (3 / 4, 13 / 16)]

private def cap1110111101100100Tree : Option PackedTree := decode 7 0xf88a7889f8847883f7f0f7eff7ea77e9ec706c6fec6aec6a6be9ebe96be36be2840046f113f112f107f106efdfefdeefd3efd2d8dfd8ded8d4d8d3d7d2d7d1d7c5d7c4afc423c41fc3f3c3efbf53bf4fbf2bbf2763576353632763235f1b5f175eef5eeaf883f883787df87d77e9f7e977e4f7e46c6a6c69ec646c63ebe2ebe26bdd6bdcd6bbf83bf7fbf53bf4fbbafbbabbb6fbb6b81978193817b81777fe77fe37fcb7fc6f032f032702f702eeffceffc6ff96ff8ebe9ebe96be36be2eb836b82eb7beb7b51dfbfdfbddfa7dfa5ddd5ddd1ddb5ddb3afa5afa3af8baf89ae0bae09adedadeb5f7ea77e9f7e577e4f76df76d7766f7666be36be2ebddebdd6b7beb7b6b756b74defd3efd2efc9efc8eedaeed9eecceecbd7c5d7c4d7bad7b9d6f6d6f5d6e9d6e8ad1d8e0d8dfd8d5d8d4d7d3d7d2d7c6d7c5ca54ca53ca47ca46c967c966c95cc95bbb1bfb1bdb1a9b1a7afa5afa3af8baf8994a794a5948d948b92cd92cb92b792b55ec6aec69ec64ec63ebe36be26bddebdce523e522e51de51d64ae64ad64a8e4a7d5afa7afa5af8daf8bae0fae0badefaded92cf92cd92b992b791279125910d910a10013b5f4b5f475f175f135c175c135bdb5bd7259b2597256f256b224b224722172212bd7c6d7c5d7bbd7bad6f7d6f6d6ead6e9c95cc95bc951c950c886c885c879c878baf8baf89af75af73adedadebadd3add192b792b592a1929f910b910990f190ef5a23c44bc447c41bc417bf7bbf73bf4bbf47637b6377634f634b5f475f3f5f135f0ef8837882f87d787cf7e977e8f7e477e3ec69ec696c63ec636be26be1ebdcebdc55dfbddfb9dfa5dfa3ddd3ddcdddb3ddafafa3af9faf89af87ae09ae05adebade610011bbf4bbf47bf23bf1fbb67bb5fbb2fbb275f135f0f5ee75ee35bd75bcf5ba35b9ea3b1bdb1bbb18fb18dafa3af9faf73af7194a594a39475947392cb92c9929f929d75f475f3f5f135f0f5c135c0b5bd75bcf25972593256b2567224722432213220eebe26be1ebdcebdc6b7aeb79eb746b73e4ad64ace4a7e4a764426441e43be43b5443

private theorem cap1110111101100100Accepted : Accepted table cap1110111101100100Box cap1110111101100100Tree := by
  decide +kernel

private def cap1110111101100101Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (3 / 4, 13 / 16)]

private def cap11101111011001010Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (3 / 4, 25 / 32)]

private def cap11101111011001010Tree : Option PackedTree := decode 5 0xf8997898f890788ff7ff77fef7f5f7f56c7eec7e6c75ec756bf76bf6ebeeebee5f131f130f11ff11eeffdeffcefeaefe9d8fcd8fbd8ead8e9d7edd7ecd7dcd7dbafc483c47bc44bc447bfb3bfa7bf7bbf7363af63a7637b63775f775f6f5f475f3c200232effeeffdefebefeaef09ef08eef8eef7d7eed7edd7ddd7dcd721d720d713d712bdffbdff9dfd5dfd3de11de0fddefddedafdbafd9afb9afb7ae41ae3fae25ae235f7f5f7f577ef77eef77c777bf7747773ebeeebee6be8ebe86b89eb896b826b81defeaefe9efddefdceef7eef6eee7eee6d7dcd7dbd7d0d7cfd712d711d703d702ad1d8fdd8fbd8ebd8e9d7eed7ecd7ddd7dbca73ca71ca5fca5ec982c980c971c970bb1d7b1d3b1bdb1bbafbbafb7afa3af9f94bf94bd94a594a392e392e192cb92c956bf76bf66beeebedeb90eb8feb89eb88e4c164c064b8e4b86456e455e44fe44f5d7ddd7dbd7d1d7cfd713d711d704d702c971c970c965c964c89fc89ec891c890a88

private theorem cap11101111011001010Accepted : Accepted table cap11101111011001010Box cap11101111011001010Tree := by
  decide +kernel

private def cap11101111011001011Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (25 / 32, 13 / 16)]

private def cap111011110110010110Box : Box := ![(47 / 40, 19 / 16), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (25 / 32, 13 / 16)]

private def cap111011110110010110Tree : Option PackedTree := decode 6 0x3b1ffb1fdb1dbb1d9b0e1b0dfb0cdb0cba05ba059a041a03f9faf9fad9f9b9f99761c361bf619b61975fc35fbf5f7f5f7b3f5f3f5b3f373f333e4b3e473e173e129d02dd02cd020d01fcf92cf91cf85cf84ca75ca74ca61ca60c984c983c973c972a363fb63f763b363af5fbf5fbb5f7b5f7729d329cf2983297f260f260b25cb25c6bd8edd8ecd8e0d8dfd7dfd7ded7d3d7d2d020d01fd019d018cf85cf84cf7ecf7dba041a03fa033a0319f0b9f099efd9efb94c394c194a994a792e792e592cf92cd46c766c75ec6fec6f6bef6beeebe96be8e530652fe529e52964b964b8e4b364b2d6b5fc35fbf5f7f5f7b5df75df35dd75dd33e4b3e473e173e133d9f3d9b3d8b3d86ebbeebbe6bbaebba6b91eb916b8aeb8a67b3e7b367b167b0e7a2e7a2679f679ed39f259f239f0b9f099e8b9e899e7d9e7b9309930792e792e5915f915d9143914146bf7ebf76bef6beeeb916b90eb8a6b89e4c1e4c164b964b8e4576456e450644fd7afbfafbdafa7afa5ae2bae29ae0dae0b9f0b9f099efd9efb9e7d9e7b9e719e6f73e173e133dfb3df73cfb3cf73ce33cdf25cf25cb259f259b22872283224f224a8d7ded7ddd7d2d7d1d714d713d705d704c972c971c966c965c8a0c89fc892c891ad1

private theorem cap111011110110010110Accepted : Accepted table cap111011110110010110Box cap111011110110010110Tree := by
  decide +kernel

private def cap111011110110010111Box : Box := ![(19 / 16, 6 / 5), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (25 / 32, 13 / 16)]

private def cap111011110110010111Tree : Option PackedTree := decode 7 0xf89a7899f8917890f8457844783ef83e70a4f0a4709e709df06c706bf066706584004ef089f088f083f082f000efffeff7eff6e0d8e0d7e0d2e0d1e079e078e073e072be107e105e0fbe0f9dfefdfeddfdfdfdbc1a5c1a3c199c197c0e7c0e5c0d9c0d751e149e148e13ce13be0d8e0d7e0cce0cbd8ffd8fed8edd8ecd870d86fd866d865bc1b1c1afc199c197c0f3c0f1c0d9c0d7b0e1b0dfb0cdb0cbafe1afdfafbfafbd48f133f132f121f120efffeffeefedefebe148e147e13be13ae078e077e06be06abc291c28fc277c275c0f1c0efc0d7c0d5b1fdb1fbb1d9b1d7afdfafddafbdafbb43f122f121f114f113f07df07cf078f077e13ce13be135e134e0cce0cbe0c7e0c6be0fbe0f9e0f1e0efdfdfdfdbdfc1dfbfc199c197c18fc18dc0d9c0d7c0cbc0c94f09e709df09af09a70367035f032f0326c76ec766c706c6febefebef6be9ebe951e243e241e227e225dfdddfd7dfbfdfbdb1d9b1d7b1bfb1bdafbdafbbafa5afa2100119af000efffeff7eff6ef7def7cef78ef77e079e078e073e072e040e03fe03be03abdfefdfeddfdfdfdbdef1deefdee5dee3c0e7c0e5c0d9c0d7c077c075c06dc06b577bf77be77b977b8f785f785777d777cf020701ff01b701af006f0067000f00040004e3c0f3c0f1c0d9c0d7c081c07fc06dc06bafe1afdfafbfafbdaefbaef9aeebaee97810380ff80db80d780378033800780035df75df35dd75dd35c8f5c8b5c575c5291dfffdffddfdbdfd7de15de13ddf3ddf1c0f1c0efc0d7c0d5c019c017c001bfff781e381df81af81ab8033802f80037fff5fbf5fbb5f7b5f775c8b5c875c535c4e87dfdfdfdbdfc1dfbfdee5dee3dedbded9c0d9c0d7c0cbc0c9c06dc06bc063c0617bdcbbdc7bdb7bdb3bbebbbe7bbafbbab80db80d780c780c3800780037fe77fe29e06ce06be065e064e002e000dff9dff8d7dfd7ded7d3d7d2d715d714d706d70508009c3bfb7bfafbf7fbf7bbbe7bbe3bbabbba381af81ab8193818f80037fff7fe37fdef035f03570327031f0006fffeffc6ffbebef6beeebe96be8eb8a6b89eb82eb8250d1

private theorem cap111011110110010111Accepted : Accepted table cap111011110110010111Box cap111011110110010111Tree := by
  decide +kernel

private def cap11101111011001011Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111011110110010110Tree <*> cap111011110110010111Tree

private theorem cap11101111011001011Accepted : Accepted table cap11101111011001011Box cap11101111011001011Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11101111011001011Box 0 (midpoint cap11101111011001011Box 0) = cap111011110110010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110110010110Accepted
  · have h : rightBox cap11101111011001011Box 0 (midpoint cap11101111011001011Box 0) = cap111011110110010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110110010111Accepted

private def cap1110111101100101Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111011001010Tree <*> cap11101111011001011Tree

private theorem cap1110111101100101Accepted : Accepted table cap1110111101100101Box cap1110111101100101Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111101100101Box 3 (midpoint cap1110111101100101Box 3) = cap11101111011001010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111011001010Accepted
  · have h : rightBox cap1110111101100101Box 3 (midpoint cap1110111101100101Box 3) = cap11101111011001011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111011001011Accepted

private def cap111011110110010Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101100100Tree <*> cap1110111101100101Tree

private theorem cap111011110110010Accepted : Accepted table cap111011110110010Box cap111011110110010Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110110010Box 2 (midpoint cap111011110110010Box 2) = cap1110111101100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101100100Accepted
  · have h : rightBox cap111011110110010Box 2 (midpoint cap111011110110010Box 2) = cap1110111101100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101100101Accepted

private def cap111011110110011Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (5 / 8, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101100110Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (5 / 8, 21 / 32), (3 / 4, 13 / 16)]

private def cap1110111101100110Tree : Option PackedTree := decode 5 0x3eb27eb25ea01e9ffe59de599e57de57bb925b923b86bb869b4b9b4b5b499b4977cb3bcb33cb13cb0fc453c44bc423c41b6973696b694b69476383637b6357634ef9627961f95f795ef8847883787e787d6d296d28ed266d25ec6aec69ec64ec63d47724b724770d770d36973696b6933692f3533352f348f348b2ea32e9b2e5f2e5aed2e6d2d6d296d28ec706c6f6c6aec69e5d465d365cee5ce652a65296523e522dda52da51da4cda4bd8d5d8d3d8c9d8c7cb9dcb9ccb97cb96ca47ca45ca3bca3aa88f592f591f4fff4fef2ccf2cbf2bdf2bcdc91dc90dc34dc33da5ada59da4bda4abe599e597e57be579e225e223e1f5e1f3b4b5b4b3b497b495b1bdb1bbb18fb18d4ee48ee486e1a6e19ed2d6d2ced25ed2566a5e6a566916690e5d365d2e5cb65cadda5ada59da4bda4ad8ded8ddd8c7d8c6cba6cba5cb96cb95ca52ca51ca3aca39a43

private theorem cap1110111101100110Accepted : Accepted table cap1110111101100110Box cap1110111101100110Tree := by
  decide +kernel

private def cap1110111101100111Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (21 / 32, 11 / 16), (3 / 4, 13 / 16)]

private def cap1110111101100111Tree : Option PackedTree := decode 8 0x3eb59eb57eb3feb3de5cde5cbe5b3e5b1b953b951b93bb939b4e9b4e7b4cfb4cd7d6afd6abd67bd677cb97cb93cb63cb5f72a3729f7273726f69cf69cb699b6996bf59ff59df593f592f2d9f2d7f2cef2ccdc9ddc9bdc92dc91da67da65da5cda5aabcb9bcb97cb67cb63c83fc83bc817c8138a4f8a4b8a2f8a2b8773876f874b8746f907f9077902f902789a7899f8917890f0ee70edf0e970e8f0a4f0a4709e709dd3c527c525c517c515c3b9c3b7c3a5c3a3b4e9b4e7b4cfb4cdb379b377b365b36378773876f874b87478527852384f384ef66f366ef66cb66c763ff63fb63b763b291e5cbe5c9e5b1e5afe267e265e243e241b4e7b4e5b4cdb4cbb1fdb1fbb1d9b1d75f96cf96c79677966f8917890f88a7889ed33ed336d2e6d2dec76ec766c706c6fdf2d8f2d7f2cdf2ccf121f120f113f112da66da65da5bda5ad8ecd8ebd8dfd8dead1dca9dca8dc9ddc9cda74da73da67da66cd66cd65cd58cd57cbc0cbbfcbb4cbb3bb951b94fb939b937b4e7b4e5b4cdb4cb9acb9ac99aaf9aad977f977d976797655ee4eee4dee496e48ed33ed32ed2e6d2d66ac66ab66a666a5e5da65d965d465d355b4e9b4e7b4cfb4cdb1ffb1fdb1dbb1d9a249a247a239a237a05ba059a041a03f74493448f4473446f40b740b34083407f2f032eff2ed32ecf29d729d3298729828da73da72da66da65d8fed8fdd8ecd8ebcbbfcbbecbb3cbb2ca74ca73ca60ca5faf699f699b6973696f63b763b36383637f2ed32ecf2ea32e9f298729832953294eed336d32ed2ded2d6c766c75ec6fec6f65d9e5d965d3e5d36530652fe529e5295688f5aaf5a9f592f591f2e4f2e2f2ccf2cbdca7dca6dc91dc90da72da70da5ada59be5c9e5c5e5afe5ade265e261e241e23db4e5b4e1b4cbb4c9b1fbb1f7b1d7b1d37cb5fcb5bcb33cb2fc483c47bc44bc44769976993696b696763af63a7637b6376a3b94fb94db923b921b4e5b4e1b4b5b4b39ac99ac79a979a95977d977b974d974b769cb69c36997699363f763ef63af63a72efb2ef72ecb2ec729cf29c7297f297aed32ed326d2d6d2cec75ec74ec6f6c6ee5d965d8e5d365d2e52fe52f65296528d443

private theorem cap1110111101100111Accepted : Accepted table cap1110111101100111Box cap1110111101100111Tree := by
  decide +kernel

private def cap111011110110011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101100110Tree <*> cap1110111101100111Tree

private theorem cap111011110110011Accepted : Accepted table cap111011110110011Box cap111011110110011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110110011Box 2 (midpoint cap111011110110011Box 2) = cap1110111101100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101100110Accepted
  · have h : rightBox cap111011110110011Box 2 (midpoint cap111011110110011Box 2) = cap1110111101100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101100111Accepted

private def cap11101111011001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110110010Tree <*> cap111011110110011Tree

private theorem cap11101111011001Accepted : Accepted table cap11101111011001Box cap11101111011001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111011001Box 1 (midpoint cap11101111011001Box 1) = cap111011110110010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110110010Accepted
  · have h : rightBox cap11101111011001Box 1 (midpoint cap11101111011001Box 1) = cap111011110110011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110110011Accepted

def cap1110111101100Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111011000Tree <*> cap11101111011001Tree

theorem cap1110111101100Accepted : Accepted table cap1110111101100Box cap1110111101100Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111101100Box 0 (midpoint cap1110111101100Box 0) = cap11101111011000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111011000Accepted
  · have h : rightBox cap1110111101100Box 0 (midpoint cap1110111101100Box 0) = cap11101111011001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111011001Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover29
