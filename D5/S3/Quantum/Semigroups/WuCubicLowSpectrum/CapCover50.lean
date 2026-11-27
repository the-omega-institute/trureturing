import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover50

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap1111111000Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (3 / 4, 7 / 8)]

private def cap11111110000Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 441 / 800), (3 / 4, 7 / 8), (3 / 4, 7 / 8)]

private def cap111111100000Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 441 / 800), (3 / 4, 13 / 16), (3 / 4, 7 / 8)]

private def cap111111100000Tree : Option PackedTree := decode 7 0xd9b7d9b759b459b3d92f592ed92c592bd1e8d1e851e551e4d1795178d1765175db36eb36db367b366b25db25cb257b256a3d0a3cfa3c9a3c8a2f1a2f0a2eba2eaaecda2cd9ecd82cd7ec962c95ec942c93ea58aa586a56ea56aa25aa256a246a242d4b154b0d4add4ad544b544ad448d44851e551e4d1e151e0d1765175d1725171d166cf66cd66bf66bd64af64ad649f649d52c352c152b552b3512b51295121511f6a586a582a56aa566a256a252a242a23e8f268f228f068f028bae8baa8b8e8b8a86ac97ac972c962c95ac672c66ac662c65a8bca8bc28bb28baa895a8952894a8946d92c592b5928592758cc58cb58c8d8c7d17651755172517151295128d126d125d468f468f3e8f2a8f228bca8bc28bb28baa663a6632661e66166376636e635e6356d1e551e4d1e151e0d1765175d1725171ccc3ccc34cbf4cbecc6bcc6b4c67cc675a3c9a3c8a3c1a3c0a2eba2eaa2e3a2e299869985997d997c98d698d598ce98cdad5179517851725171512b512a5126d125cc6ecc6dcc67cc66cc2ecc2e4c2ccc2c522cdb6cd9acd9acd96c972c95ac95ac9568f3e8f228f228f1e8bc28baa8baa8ba6d9b359af59b2d9aed92b5927592ad926d4b054acd4afd4ac544a5447d449d4475a960a959a95fa958a894a88fa893a88ea3c8a3c0a3c7a3bfa2eaa2e2a2e9a2e1a1d9b359b2d9af59aed92b592ad9275926d4b054afd4acd4ac544a5449d447d4475a960a95fa959a958a894a893a88fa88ea3c8a3c7a3c0a3bfa2eaa2e9a2e2a2e1a2cd96cd76cd76cd72c956c936c936c9328f1e8efe8efe8efa8ba68b868b868b82b564b9649d64ad649b6335631f632d631d45e145c545d545c344a9449744a344956c95ac936c93ac932c65ac63ac63ec6368baa8b868b8a8b828946892a892e8926a3479f47914791478f45e145d545d545d33319330b330b330931b731ab31ab31a968f228f028f1e8efe8baa8b8a8ba68b86661665f2661265ee6356633663526332ba3c8a3c7a3c0a3bfa2eaa2e9a2e2a2e199859984997c997b98d598d498cd98ccb478f477f477f477d45d345c345c345c1330932f732f732f531a93199319931975aa2f0a2e2a2e2a2e0a254a24ba24ba24998db98cd98cd98cb985c985898589856a43

private theorem cap111111100000Accepted : Accepted table cap111111100000Box cap111111100000Tree := by
  decide +kernel

private def cap111111100001Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 441 / 800), (13 / 16, 7 / 8), (3 / 4, 7 / 8)]

private def cap111111100001Tree : Option PackedTree := decode 6 0xd9bbd9b7d9b7d9b6d931592f592f592e51ecd1e8d1e8d1e7d17ad179517951785b262b25eb25eb25cb19fb19cb19cb19aa2f5a2f2a2f2a2f0a259a256a256a254a68f668f468f468f3e8bd68bca8bca8bc26656663a663a6632638263766376636ed17ad17951795178512cd12b512b512a4c704c6ecc6ecc6dcc304c2ecc2ecc2e52259b759b3d9b6d9b3592ed92bd92e592b51e851e4d1e7d1e45178d175d178517558d4b25db24fb25cb24eb19bb190b19ab18fa2f1a2e3a2f0a2e2a255a24ca254a24ba8ca3d0a3c9a3cfa3c8a2f1a2eba2f0a2ea998d9986998c998598dc98d698db98d5b1aa2f2a2e4a2f0a2e2a256a24da254a24b98dd98cf98db98cd985d9859985c9858a43

private theorem cap111111100001Accepted : Accepted table cap111111100001Box cap111111100001Tree := by
  decide +kernel

private def cap11111110000Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111111100000Tree <*> cap111111100001Tree

private theorem cap11111110000Accepted : Accepted table cap11111110000Box cap11111110000Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11111110000Box 2 (midpoint cap11111110000Box 2) = cap111111100000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100000Accepted
  · have h : rightBox cap11111110000Box 2 (midpoint cap11111110000Box 2) = cap111111100001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100001Accepted

private def cap11111110001Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 7 / 8), (3 / 4, 7 / 8)]

private def cap111111100010Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (3 / 4, 7 / 8)]

private def cap1111111000100Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (3 / 4, 13 / 16)]

private def cap11111110001000Box : Box := ![(11 / 10, 9 / 8), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (3 / 4, 13 / 16)]

private def cap11111110001000Tree : Option PackedTree := decode 6 0xd350d3485348534752e652de52de52dd4fd54fce4fce4fcdcf85cf7f4f7f4f7eda5cca5bca5bca5baa507a500a500a4fe9f0b9efe9efe9efd9e709e699e699e68a67eaa7e727e727e6e79c279a679a679a26f226ef26ef26eee6a3e6a226a226a1e8a690a679a68ea677a5bca5a6a5baa5a49f9c9f879f9b9f869efe9ee99efd9ee8b4b794b4d4b754b494a0149d549fd49d13dfd3dd33dfb3dd13cd33cad3cd13cab4cfce4fc3cfcdcfc34f7f4f74cf7ecf744dde4dd3cdddcdd34d924d87cd91cd8759efe9ee99efd9ee89e699e569e689e559b249b0f9b239b0e9a889a7a9a879a79a43a690a68ea679a677a5bca5baa5a6a5a49f9c9f9b9f879f869efe9efd9ee99ee8b4b794b754b4d4b494a0149fd49d549d13dfd3dfb3dd33dd13cd33cd13cad3cab4cfce4fcdcfc3cfc34f7f4f7ecf74cf744dde4dddcdd3cdd34d924d91cd87cd8759efe9efd9ee99ee89e699e689e569e559b249b239b0f9b0e9a889a879a7a9a79a45347533bd33bd33b527f527452745273cfcdcfc34fc34fc2cf344f2acf2acf2a59f9b9f869f869f859e689e559e559e549bbb9ba69ba69ba59a879a799a799a78a1aa507a500a500a4fea3cfa3c8a3c8a3c79a8f9a889a889a87998c998599859984b4a0149d549fd49d147914781478f477f3cd33cad3cd13cab3ad93acb3ad73ac9679a6795a79a2795675b2759675ae75926a2269ea6a1e69e6661665f2661265ee874a0149fd49d549d14791478f4781477f3cd33cd13cad3cab3ad93ad73acb3ac9679a679a2795a795675b275ae759675926a226a1e69ea69e66616661265f265ee8a4fea4e8a4e8a4e7a3c7a3bfa3bfa3be9a879a799a799a789984997b997b997aad1

private theorem cap11111110001000Accepted : Accepted table cap11111110001000Box cap11111110001000Tree := by
  decide +kernel

private def cap11111110001001Box : Box := ![(9 / 8, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (3 / 4, 13 / 16)]

private def cap111111100010010Box : Box := ![(9 / 8, 23 / 20), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (3 / 4, 13 / 16)]

private def cap111111100010010Tree : Option PackedTree := decode 6 0x369d969b969b969b566db66cd66cd66cb553155195519551552cb52c152c152bf6aa62aa32aa32aa2aa596a582a582a57e941e9402940293fa8f3e8f228f228f1e8969b7698769b56985683d6819683b6817551754e9551554e753e953cb53e753c955a0fda06da0eda05d9b359af59b2d9aed4fad4f354f9d4f254b054acd4afd4ac53551954eb551554e753eb53cd53e753c94a0149d549fd49d148c948b348c748b16a7d6a79aa7cea792a582a566a57ea56291929166918e91628f228f028f1e8efe90ed372d36ad34ad342d07ed076d05ed056aa32aa2aaa0aaa02a7d6a7cea7bea7bada695a685a625a615a0bda0ada06da05d5415540553ad539d4f7d4f754f354f255683f683b681b681766cd66cb66bd66bb53eb53e753cd53c952c152bf52b352b14d5465545553ad539d4fad4f9d4f354f25280527f5275527452325231d22cd22c5a9f5a9f3a9e6a9e4a960a95fa959a958a464a463a459a458a3c8a3c7a3c0a3bfa45a6d5a615a615a60d9b2d9aed9aed9ae55455539d539d53954afd4ac54ac54abdaa8aaa73aa73aa72a95fa958a958a957a4fea4e8a4e8a4e7a3c7a3bfa3bfa3bea1a

private theorem cap111111100010010Accepted : Accepted table cap111111100010010Box cap111111100010010Tree := by
  decide +kernel

private def cap111111100010011Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 13 / 16), (3 / 4, 13 / 16)]

private def cap111111100010011Tree : Option PackedTree := decode 7 0x36e656e576e576e556bf16be36be36be158e158d358d358d156d556c756c756c56dcaedc7edcaadc7ad7c6d79ed7c2d79ab1a6b17eb1a2b17aad8ead66ad8aad62bb72bb72ab71fb71eb5f1b5f0b5e7b5e6ac69ac68ac5fac5eab63ab62ab59ab58b6e556e3d6e3d6e3b6be16bcd6bcd6bcb58d158bd58bd58bb56c556b156b156af5ab5f8b5e7b5e7b5e5b4ecb4dcb4dcb4daab6aab59ab59ab57aa98aa8caa8caa8aa6b1c2b17eb1a6b17aadaaad66ad8ead629a869a429a6a9a3e973296f2971696eed634d62f562fd62ed5b1d5ac55acd5abd34d5347d348534752e2d2ddd2de52dd5556d556b356b356af55315519551955154b994b794b794b754a0f4a014a0149fd4896e3d6df36e3b6df16bcd6b976bcb6b9558bd588358bb588156b1568356af568154b5e6b5cbb5e5b5cab4dbb4c3b4dab4c2ab58ab41ab57ab40aa8baa74aa8aaa73a8cac5eac41ac5dac40ab58ab41ab57ab40a68fa678a68ea677a5bba5a5a5baa5a4aa55ac55a0d5abd5a05545d53a55455539d2ddd2d2d2dd52d2527fd274d27f52745443b71fb71eb714b713b5e7b5e6b5dcb5dbac5fac5eac54ac53ab59ab58ab4eab4db6e3d6e3b6e276e256bcd6bcb6bb76bb558bd58bb58a758a556b156af569b56995db8a5b89db7d5b7cdaee5aeddae65ae5d62a5629d6215620d5a755a6d5a155a0db713b712b6f9b6f8b5dbb5dab5cbb5caac53ac52ac41ac40ab4dab4cab41ab40ad5af3daf2daee5aed5a6e5a6d5a695a6855acd5abd5a755a655465545554155405b5dcb5dbb5ccb5cbb4d2b4d1b4c4b4c3ab4eab4dab42ab41aa82aa81aa75aa74b6bb76bb56b976b9569a369a169876985569b5699568356815503550154e954e75a358bf58bb58a958a556b356af569d56994d214d1d4d0b4d094b794b754b634b616b152b14ab10ab102ad3aad32ad0aad029a169a1299e699de96c696c2969a9692aab59ab57ab4eab4caa8caa8aaa82aa80a5bca5baa5b1a5b0a500a4fea4f6a4f5b569d5699568556815505550154eb54e74b634b614b4d4b4949ed49eb49d549d15116e3b6df16df16def6bcb6b956b956b9358bb58815881587f56af56815681567f6d796d72ad72ad726d36ad30ad30ad306ad5ead02ad02acfeaa2aa9cea9cea9ca9ac5dac40ac40ac3faa8aaa73aa73aa72a68ea677a677a676a4fea4e8a4e8a4e7a1a

private theorem cap111111100010011Accepted : Accepted table cap111111100010011Box cap111111100010011Tree := by
  decide +kernel

private def cap11111110001001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111100010010Tree <*> cap111111100010011Tree

private theorem cap11111110001001Accepted : Accepted table cap11111110001001Box cap11111110001001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110001001Box 1 (midpoint cap11111110001001Box 1) = cap111111100010010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010010Accepted
  · have h : rightBox cap11111110001001Box 1 (midpoint cap11111110001001Box 1) = cap111111100010011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010011Accepted

private def cap1111111000100Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11111110001000Tree <*> cap11111110001001Tree

private theorem cap1111111000100Accepted : Accepted table cap1111111000100Box cap1111111000100Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1111111000100Box 0 (midpoint cap1111111000100Box 0) = cap11111110001000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110001000Accepted
  · have h : rightBox cap1111111000100Box 0 (midpoint cap1111111000100Box 0) = cap11111110001001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110001001Accepted

private def cap1111111000101Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap11111110001010Box : Box := ![(11 / 10, 9 / 8), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap111111100010100Box : Box := ![(11 / 10, 9 / 8), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap111111100010100Tree : Option PackedTree := decode 5 0x34a134a114a054a0347a347a1479547933ce53ce33cd73cd53ae73ae53add3adb679ca79c679ae79aa75ce75ca75ba75b66a466a426a2a6a26663a6636661e661a8a508a507a501a500a3d0a3cfa3c9a3c89e719e709e6a9e699d729d719d6d9d6cb3ce33ce13cd53cd33ae53ae33adb3ad93521351f35133511331b3319330d330b43a502a501a4eea4eca466a465a45da45b9e6b9e6a9e5a9e589dea9de99de59de4b48cd48cb48bb48b747954793478547833bd53bd33bcb3bc93add3adb3acf3acd4cf35cf354f2d4f2c4ef54ef4cef2cef24d454d44cd3ecd3dcd05cd054d034d02d9dea9de99de59de49d6e9d6d9d679d669a0b9a0a9a069a0599879986997e997da45280d280527652755232d232522dd22ccf354f34cf2c4f2b4ef4cef44ef24ef1da465a464a45ba459a3c9a3c8a3c1a3c09de99de89de49de39d6d9d6c9d669d65a679aa79a67962795a77a677a27792778e6a266a2269ee69ea682a682668166812cef4cef44ef24ef1ceb6ceb64eb34eb2cd054d04cd02cd024cc34cc2ccbeccbe521a

private theorem cap111111100010100Accepted : Accepted table cap111111100010100Box cap111111100010100Tree := by
  decide +kernel

private def cap111111100010101Box : Box := ![(11 / 10, 9 / 8), (189 / 320, 63 / 100), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap1111111000101010Box : Box := ![(11 / 10, 9 / 8), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (13 / 16, 7 / 8)]

private def cap1111111000101010Tree : Option PackedTree := decode 7 0xd34a5349d344d34452e052dfd2dad2da4fd04fcfcfcb4fcacf814f80cf7c4f7bda693a692a688a687a5bfa5bea5b4a5b39f9f9f9e9f959f949f019f009ef79ef6ae9a269a2299f699f296d696d296aa96a681e681e281ce81ca806a80668052804ed03cd03c5039d039500d500cd00a5009cfcb4fcacfc5cfc54f7c4f7bcf76cf76514d114d0f4cf94cf74b694b674b534b5140f140ef40e540e34033403140274025681e281de81ca81c680668062804e804a7e567e527e2a7e267bde7bda7bb27bae86a970296fa96d696ce940a940693ea93e27c0a7c027be27bda79ae79aa7992798ad2dad2da52d552d4d27d527cd2775276cf7c4f7bcf76cf764f324f31cf2d4f2cda5b4a5b3a5a9a5a8a4f9a4f8a4eda4ec9ef79ef69eec9eeb9e639e629e599e58ad19fa09f9f9f969f959f029f019ef89ef79bbf9bbe9bb69bb59b279b269b1e9b1db3f3f3f3d3f2b3f293e033e013def3ded377d377b376b3769364d364b363b36395cfcb4fcacfc5cfc54f7c4f7bcf76cf764e2fce2f4e2d4e2cce104e0fce0dce0d59c5f9c5e9c5a9c599c209c1f9c1b9c1a9bb69bb59bab9baa9b1e9b1d9b139b12a27e567e527e2a7e267bde7bda7bb27bae6ed66ed26eaa6ea66c766c726c4a6c46b53e053e013df13ded3cd73cd53cc93cc5364f364b363d363935153513350b350967be27bda7bb67bae7992798a796a79626c7a6c726c4e6c466a166a1269f669eea229a4a9a469a1e9a1a96fa96f696ce96ca7e7a7e767e527e4e7c027bfe7bda7bd6d348d34853435342d2ded2de52d952d8cfcecfce4fc9cfc94f7fcf7f4f7acf7a574d0f4d0d4cf74cf54b674b654b514b4f3f293f273f133f113ded3deb3dd73dd569a1a9a1699ea99e696ca96c6969e969a7e4e7e4a7e227e1e7bd67bd27baa7ba6b54b7d4b794b674b634a034a0149f149ed3e013dfd3ded3de93cd53cd33cc53cc3696ce96c696a2969a93e293da93b293aa7bda7bd27bae7ba6798a79867962795aa33f3d3f393f293f253e013dfd3ded3de9377b377937693765364b36493639363567e527e4e7e267e227bda7bd67bae7baa6ed26ece6ea66ea26c726c6e6c466c42cfc9cfc94fc44fc3cf7acf7a4f754f74cdd9cdd94dd44dd3cd8dcd8d4d884d87d6a7c027bfa7bda7bd279aa79a6798a79866c966c926c726c6a6a266a226a126a0ecf7b4f7a4f75cf74cf314f30cf2c4f2b4d8e4d8d4d88cd87cd424d41cd3dcd3d5443

private theorem cap1111111000101010Accepted : Accepted table cap1111111000101010Box cap1111111000101010Tree := by
  decide +kernel

private def cap1111111000101011Box : Box := ![(11 / 10, 9 / 8), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (13 / 16, 7 / 8)]

private def cap1111111000101011Tree : Option PackedTree := decode 5 0xd3525351d34f534e52e7d2e752e4d2e3cfd6cfd64fd44fd3cf874f86cf84cf845a69ea69ca694a692a5c9a5c7a5c0a5be9fa89fa79fa09f9e9f099f089f029f00aa973e973a970296fa94269422940a94067c3a7c367c0a7c0279ca79c679ae79aa99fad9fac9fa89fa79f0e9f0d9f099f089bca9bc99bc69bc59b319b309b2d9b2cb3f513f4f3f413f3d3e133e113e053e01378d378b377f377b365b3659364f364b54f874f86cf814f804f394f38cf35cf354d98cd984d93cd92cd48cd484d454d44d229a8e9a869a729a6a973a9732971e97167eb27eaa7e9e7e9a7c367c2e7c227c1ed34e534d5349534852e3d2e2d2df52de4fd3cfd34fcf4fce4f844f83cf804f7f554b9d4b994b7d4b794a114a0f4a034a013e1b3e173e013dfd3ce33ce13cd53cd34cfd64fd54fcf4fce4f86cf85cf804f7f4de4cde44ddecdde4d984d97cd92cd9259f0d9f0b9f009efe9e719e709e6a9e699b309b2f9b259b249a909a8f9a899a88a43

private theorem cap1111111000101011Accepted : Accepted table cap1111111000101011Box cap1111111000101011Tree := by
  decide +kernel

private def cap111111100010101Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1111111000101010Tree <*> cap1111111000101011Tree

private theorem cap111111100010101Accepted : Accepted table cap111111100010101Box cap111111100010101Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111111100010101Box 2 (midpoint cap111111100010101Box 2) = cap1111111000101010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000101010Accepted
  · have h : rightBox cap111111100010101Box 2 (midpoint cap111111100010101Box 2) = cap1111111000101011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000101011Accepted

private def cap11111110001010Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111100010100Tree <*> cap111111100010101Tree

private theorem cap11111110001010Accepted : Accepted table cap11111110001010Box cap11111110001010Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110001010Box 1 (midpoint cap11111110001010Box 1) = cap111111100010100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010100Accepted
  · have h : rightBox cap11111110001010Box 1 (midpoint cap11111110001010Box 1) = cap111111100010101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010101Accepted

private def cap11111110001011Box : Box := ![(9 / 8, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap111111100010110Box : Box := ![(9 / 8, 23 / 20), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap111111100010110Tree : Option PackedTree := decode 6 0x369df69dd69c169bd684b684968436841553755355521551d53f753f553ef53ed6d096d092d086d082cdbecdbacda2cd9ea7eea7eaa7dea7daa59ea59aa58aa5869aa9baa9aaa90aa8ea967a966a962a961a509a508a502a501a3d1a3d0a3caa3c9a2d3bad3b2d37ad372d092d08ed082d07eaa6aaa62aa3aaa32a7eaa7e6a7daa7d6da125a11da105a0fd9b759b6d9b3d9b354fd54fcd4fb54fad4b354b2d4b0d4b05355355531551d551952cd52cb52c352c14a114a0f4a034a0147a1479f4793479143b4e0b4deb4d6b4d4b421b420b41bb419aa90aa8eaa86aa84a9f7a9f6a9f1a9f0b69ad69a96993698f683768336823681f550d550954f354ef53e353e153d553d02000795a10da105a08da07d9b459b3d9b059afd4fbd4fb54f554f454b154b0d4add4ad535521551d550d550953ef53ed53e353e14a054a0349f549f148cd48cb48c548c36aa1aaa12a9e6a9dea7c6a7c2a7aaa7a293ea93e293ba93b2918a91869176916eaa9f7a9f6a9eaa9e8a962a961a95ba95aa466a465a45da45ba3caa3c9a3c2a3c1a45a6f5a6e5a6a5a695a105a0fda0cda0bd54755465542554154fb54fad4f854f7db4d4b4d2b4c7b4c4b419b417b40fb40daa84aa82aa77aa75a9f0a9efa9e8a9e620003cad082d07ed03ed036cd9ecd9acd7ecd7aa7daa7d6a7a2a79aa586a582a56aa5669aa8eaa8caa84aa82a9f6a9f5a9f0a9efa501a500a4f8a4f6a465a464a461a460b5509550554ef54eb53e153df53d153cd49f149ed49d949d548c348c148b748b3554fb54fad4f454f354b0d4b054ad54acd232d232522dd22cd1e4d1e451e0d1e0521a

private theorem cap111111100010110Accepted : Accepted table cap111111100010110Box cap111111100010110Tree := by
  decide +kernel

private def cap111111100010111Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap1111111000101110Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (13 / 16, 7 / 8)]

private def cap11111110001011100Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (13 / 16, 27 / 32)]

private def cap11111110001011100Tree : Option PackedTree := decode 8 0x36e436e416e2d6e2b6ccb6cc96cbf6cbd5c7f5c7d5c715c6f5ba55ba35b9b5b996d996d992d97ed97ad7a6d7a2d77ad776b74ab746b736b732b5d6b5d2b5bab5b69ae3fae3eae38ae37ad75ad74ad6ead6dac61ac60ac56ac55ab5bab5aab50ab4fa2dc82dc7edc56dc52d7a2d79ed776d772b8fab8f6b8deb8dab5d2b5ceb5b6b5b2d71f571ed71bd71b56ba56b9d6b6d6b65630562fd62ad62a55ad55acd5a7d5a750edc5adc56dc32dc2ad97ed97ad95ed956b8e2b8deb8c2b8beb736b732b71ab716db865b855b7f5b7ddb2bdb2adb26db25d7185717d713d71356e356e2d6df56ded56cbf6cbd6c9b6c976bbd6bbb6b9d6b9b5b9b5b995b7d5b7b5add5adb5acd5acb4d71c571bd713d71356e6d6e656df56ded62b562ad6225621d5dd55dcd5d855d7dadcdadccadbeadbdad6ead6dad66ad65abbaabb9abb0abafab50ab4fab44ab43a45b8adb8a5b7e5b7d5aeedaee5ae6dae6571bd71b57135712d6b6d6b656b2d6b210001eae37ae36ae26ae25ad6dad6cad65ad64ac55ac54ac43ac42ab4fab4eab43ab42a1ab5e9b5e8b5deb5ddb4deb4ddb4d4b4d3ab5bab5aab50ab4faa8eaa8daa84aa83b6bd16bcf6bbb6bb969bb69b969a769a556b556b3569f569d551b5519550755055daef5aeedae75ae6da6a5a69da635a62d6b756b6d6b356b2d676d67656745673dad6ead6dad66ad65acedacecace8ace7ab50ab4fab44ab43aa84aa83aa77aa76a2d776d772d736d732d34ed34ad316d312ad3ead3aad0ead0aaa0eaa0aa9daa9d6b46b186b182b15ab156ad6ead6aad42ad3e9f969f929f7e9f7a9d5e9d5a9d469d42d3f2d3f253efd3ef53abd3ab53a8d3a853495348d343d34352df52ded2d9d2d95158c158bf58ab58a956b556b3569f569d4d234d214d0d4d0b4b7b4b794b654b635d62b562ad622d621d5a855a7d5a255a1d3efd3ef53ec53ebd3a8d3a853a553a490001ea7dfa7dea7d8a7d7a751a750a74aa749a687a686a67ba67aa5b3a5b2a5a8a5a7a2b156b152b10eb10aad3ead3aad0ead0a9a1a9a1699ea99e696ca96c6969e969ab556b756b356a1569d551d5519550955054b7d4b794b674b634a034a0149f149ed6ad42ad3ead12ad0eaa12aa0ea9dea9da96ce96ca96a2969e93e293de93b293aed5a7d5a755a1d5a15541d541553b553ad2d952d8d2d3d2d3527bd27b5275d2755688

private theorem cap11111110001011100Accepted : Accepted table cap11111110001011100Box cap11111110001011100Tree := by
  decide +kernel

private def cap11111110001011101Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (27 / 32, 7 / 8)]

private def cap111111100010111010Box : Box := ![(9 / 8, 91 / 80), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (27 / 32, 7 / 8)]

private def cap111111100010111010Tree : Option PackedTree := decode 6 0xd631d631562c562bd5aed5ae55a955a8d3f3d3f353f0d3f053acd3ac53a9d3a95a7e7a7e6a7e1a7e0a759a758a753a752a694a693a689a688a5c0a5bfa5b5a5b4a2b18ab186b15eb15aad72ad6ead46ad429f9a9f969f829f7e9d629d5e9d4a9d46d3f353f2d3f053efd3ac53abd3a953a8d349d34953445343d2dfd2df52da52d9d0eb162b15eb11eb11aaef2aeeeaecaaec69f869f829f6a9f669e5e9e5a9e4a9e46d5de55ddd5d955d8d5a955a8d5a355a2d3cbd3cb53c953c8d3a9d3a953a653a5d34fc34fc14fb54fb34f2f4f2d4f254f234d134d114cfb4cf94c054c034bfb4bf969e5e9e5a9e4a9e469d4e9d4a9d329d2e980a980697f697f296d696d296aa96a69158af58ad588d588957775775576357614fc14fbf4fb34fb14f2d4f2b4f234f216aeeeaeeaaec6aec2ad46ad42ad16ad129e5a9e569e469e429d4a9d469d2e9d2a9a7e0a7dfa7d9a7d8a796a795a791a790a688a687a67ca67ba601a600a5fca5fbb4f2d4f2b4f234f214ea54ea34e974e954c034c014bf94bf74b694b674b534b51486aad76ad6ead4aad42aa42aa3aaa1aaa12970296fa96d696ce940a940693ea93e2d5a955a8d5a355a2d5435542d53cd53c52dad2da52d552d4d27d527cd2775276dab51ab50ab45ab44aa85aa84aa78aa77a5b4a5b3a5a9a5a8a4f9a4f8a4eda4ecad1

private theorem cap111111100010111010Accepted : Accepted table cap111111100010111010Box cap111111100010111010Tree := by
  decide +kernel

private def cap111111100010111011Box : Box := ![(91 / 80, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (27 / 32, 7 / 8)]

private def cap111111100010111011Tree : Option PackedTree := decode 8 0x36e476e456e316e2f6ccf6ccd6cc36cc15c835c815c755c735ba95ba75b9f5b9d6d99ed99ad986d982d7aed7aad782d77eb752b74eb73eb73ab5deb5dab5c2b5be9ae41ae40ae3aae39add4add3adcfadceac63ac62ac58ac57abc0abbfabbcabbbb5ba95ba75b9f5b9d5aef5aed5ae15adf5781577f5779577756bb56b956a556a348b722b721b717b716b666b665b660b65fae40ae3fae39ae38add3add2adceadcdb6ccd6ccb6cc16cbf6bd56bd36bbf6bbd5ba75ba55b9d5b9b5aed5aeb5adf5add4d720571fd71cd71c56e9d6e956e756e6d6315630d62bd62b55dfd5df55ddd5dd5add3add2adceadcdad76ad75ad6fad6eabbfabbeabbbabbaab5cab5bab51ab50a43b718b717b710b70eb661b660b65bb659ae3aae39ae34ae32adcfadceadcaadc8b6e216e1f6e056e036cb76cb56ca36ca15c695c675c575c555b955b935b855b836dc3edc3adc06dc02d96ad966d942d93eb8ceb8cab8aab8a6b726b722b706b702b56cc36cc16ca36c9f6bc16bbf6ba16b9f5b9f5b9d5b855b815ae15adf5ad15acf4d71d571cd71a571956e7d6e756e556e4562c562bd6285627d5de55ddd5dbd5db5ae34ae32ae2bae29adcaadc8adc2adc0ac50ac4fac47ac46abb7abb6abb2abb1aab73eb73ab70ab702b5c2b5beb5a2b59eaef2aeeeaecaaec6ad4aad46ad1aad16916e2f6e2d6e1d6e196cc16cbf6cb36caf5c735c715c655c615b9d5b9b5b915b8d6dc3adc36dc02dbfed966d962d93ed93ab8cab8c6b8a6b8a2b722b71eb702b6fedb86db865b7fdb7f5b2c5b2bdb275b26d718d71857145713d6e3d6e356dfd6df56ad982d97ed93ed936d77ed77ad73ed73ab73ab736b702b6fab5beb5bab59eb59a9ae39ae38ae32ae30adceadcdadc8adc6ac57ac56ac4fac4eabbbabbaabb6abb5b5c655c615c535c4f5b915b8d5b815b7d589f589d588d5889576d576b57635761556e756e6d6e056df56b7d6b756b3d6b355ddd5dd55d8d5d855a8d5a855a2d5a2521ab5ebb5eab5e0b5dfb4e0b4dfb4d6b4d5ab5dab5cab52ab51aa90aa8faa86aa85b6bd56bd36bbf6bbd69bf69bd69ab69a956b956b756a356a1551f551d550b55095daf05aefdae85ae7da6b5a6ada64da6456b856b7d6b456b3d677d67756755674dad70ad6fad68ad67acefaceeaceaace9ab52ab51ab46ab45aa86aa85aa79aa78a2d77ed77ad73ed73ad356d352d322d31ab5beb5bab59eb59ab3bab3b6b3a6b3a2d6b7d6b756b3d6b356775676d674d67455a8d5a855a2d5a25542d542553c553bd0d1

private theorem cap111111100010111011Accepted : Accepted table cap111111100010111011Box cap111111100010111011Tree := by
  decide +kernel

private def cap11111110001011101Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111111100010111010Tree <*> cap111111100010111011Tree

private theorem cap11111110001011101Accepted : Accepted table cap11111110001011101Box cap11111110001011101Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11111110001011101Box 0 (midpoint cap11111110001011101Box 0) = cap111111100010111010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010111010Accepted
  · have h : rightBox cap11111110001011101Box 0 (midpoint cap11111110001011101Box 0) = cap111111100010111011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010111011Accepted

private def cap1111111000101110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11111110001011100Tree <*> cap11111110001011101Tree

private theorem cap1111111000101110Accepted : Accepted table cap1111111000101110Box cap1111111000101110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1111111000101110Box 3 (midpoint cap1111111000101110Box 3) = cap11111110001011100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110001011100Accepted
  · have h : rightBox cap1111111000101110Box 3 (midpoint cap1111111000101110Box 3) = cap11111110001011101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110001011101Accepted

private def cap1111111000101111Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (13 / 16, 7 / 8)]

private def cap1111111000101111Tree : Option PackedTree := decode 7 0xdb9b5b9adb97db975afe5afddafadafa563a5639d636d63655b755b6d5b3d5b35b735b734b72eb72db5fbb5fab5f4b5f3ac73ac72ac6cac6bab6dab6cab66ab65aedcbedcbadc8edc8ad7d6d7d2d7aed7aab91ab916b906b902b5f2b5eeb5deb5dad7235722d720d72056be56bdd6bbd6bb5636d6365631d63155b3d5b355aed5ae516e5d6e5b6e456e436be96be76bd56bd35c8b5c895c815c7f5af75af55aed5aeb6b916b912b902b8feb5eeb5eab5dab5d6b1b2b1aeb18ab186ad9aad96ad72ad6e86ad7f2d7ead7d6d7ced3bed3bad3aad3a2adbaadb2ad9ead96aa6eaa6aaa5eaa5adafadaf9daf5daf4da755a745a705a6f55b3d5b2d5aed5add54bd54b55485547546b1d2b1cab1b6b1aeadbaadb2ad9ead969a929a8e9a7a9a72973e973a9726971ed636d6365631d63155b3d5b355aed5ae534f534ed34a5349d2e4d2e452e052dfdac6cac6bac62ac61ab66ab65ab5cab5ba69da69ca693a692a5c8a5c7a5bfa5bead55b755b655aed5add54dd54d5548554752e7d2e752e052df5284d28452815280d22dcd2dccedcb6dcb2d7ead7e6d7ced7cab1cab1c6b1aeb1aaadb2adaead96ad92db99db995b965b95dafcdafc5af95af8d638d63856355634d5b5d5b555b255b1d76e5b6e596e436e416be76be56bd36bd15c895c875c7f5c7d5af55af35aeb5ae96b912b90eb8feb8fab5eab5e6b5d6b5d2b1aeb1aab186b182ad96ad92ad6ead6a8b72cb72bb720b71fb5f2b5f1b5e8b5e7ac6aac69ac60ac5fab64ab63ab5aab59ad5afd5afc5af9daf8da775a765a745a7355b655b555b2d5b1d54d554c554b554adb5f3b5f1b5e9b5e7b4e8b4e6b4deb4dcab65ab63ab5bab59aa96aa95aa8eaa8ca8d63956385635d634d5b655b555b2d5b1d351d350d34e534d52e752e652e3d2e2dac6bac6aac61ac60ab65ab64ab5bab5aa69ca69ba692a691a5c7a5c6a5bea5bdb58d558d358c158bf56c956c756b556b34d374d354d234d214b8d4b8b4b7b4b795aab6cab6aab5bab59aa9aaa98aa8eaa8ca5cea5cca5bea5bca508a507a501a500a43

private theorem cap1111111000101111Accepted : Accepted table cap1111111000101111Box cap1111111000101111Tree := by
  decide +kernel

private def cap111111100010111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1111111000101110Tree <*> cap1111111000101111Tree

private theorem cap111111100010111Accepted : Accepted table cap111111100010111Box cap111111100010111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111111100010111Box 2 (midpoint cap111111100010111Box 2) = cap1111111000101110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000101110Accepted
  · have h : rightBox cap111111100010111Box 2 (midpoint cap111111100010111Box 2) = cap1111111000101111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000101111Accepted

private def cap11111110001011Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111100010110Tree <*> cap111111100010111Tree

private theorem cap11111110001011Accepted : Accepted table cap11111110001011Box cap11111110001011Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110001011Box 1 (midpoint cap11111110001011Box 1) = cap111111100010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010110Accepted
  · have h : rightBox cap11111110001011Box 1 (midpoint cap11111110001011Box 1) = cap111111100010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010111Accepted

private def cap1111111000101Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11111110001010Tree <*> cap11111110001011Tree

private theorem cap1111111000101Accepted : Accepted table cap1111111000101Box cap1111111000101Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1111111000101Box 0 (midpoint cap1111111000101Box 0) = cap11111110001010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110001010Accepted
  · have h : rightBox cap1111111000101Box 0 (midpoint cap1111111000101Box 0) = cap11111110001011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110001011Accepted

private def cap111111100010Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1111111000100Tree <*> cap1111111000101Tree

private theorem cap111111100010Accepted : Accepted table cap111111100010Box cap111111100010Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111111100010Box 3 (midpoint cap111111100010Box 3) = cap1111111000100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000100Accepted
  · have h : rightBox cap111111100010Box 3 (midpoint cap111111100010Box 3) = cap1111111000101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000101Accepted

private def cap111111100011Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (3 / 4, 7 / 8)]

private def cap1111111000110Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (3 / 4, 13 / 16)]

private def cap1111111000110Tree : Option PackedTree := decode 9 0x325b99db965b995b95dafcdaf95afc5af8d638d63556385634d5b5d5b255b555b1d8d4b5f9b5e8b5f8b5e7b4edb4ddb4ecb4dcab6bab5aab6aab59aa99aa8daa98aa8ca8cac71ac60ac70ac5fab6bab5aab6aab59a6a2a691a6a1a690a5cda5bda5cca5bcaaadb2ad6eadaaad66aa6aaa3aaa62aa32973a96fa973296f294229406941e9402911a969dd69bd69d969b9684968416847683f5535551d5531551953f553ed53f353eb6d092d082d08ed07ecdbacd9ecdb6cd9aa7eaa7daa7e6a7d6a59aa586a596a5829aa9aaa8eaa98aa8ca966a961a965a960a508a501a507a500a3d0a3c9a3cfa3c8a23464a6a2a691a6a1a690a5cda5bda5cca5bc9fab9f9d9faa9f9c9f0c9eff9f0b9efeaa973a96fa973296f294229406941e94027c367c027c2e7bfa79c679aa79c279a699fac9f9e9faa9f9c9f0d9f009f0b9efe9bc99bbd9bc89bbc9b309b259b2f9b24b3e1b3e013e173dfd3ce33cd53ce13cd33661364b365f364935213513351f3511488d4a508a501a507a500a3d0a3c9a3cfa3c89e719e6a9e709e699d729d6d9d719d6cb3ce33cd53ce13cd33ae53adb3ae33ad935213513351f3511331b330d3319330b44688

private theorem cap1111111000110Accepted : Accepted table cap1111111000110Box cap1111111000110Tree := by
  decide +kernel

private def cap1111111000111Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (13 / 16, 7 / 8)]

private def cap1111111000111Tree : Option PackedTree := decode 7 0xdba25b9fdb9fdb9eda7d5a7ada7ada7a563e563cd63cd63c5551d5505550554fdac7cac79ac79ac78aaa3aaa0aaa0aa9fa6afa6aaa6aaa6a9a514a50fa50fa50ea2dcfedcdadcf6dcd2d80ed7f2d806d7eab1e6b1d2b1e2b1caadcaadbaadc6adb2db01dafe5b00dafd5a7ada77da7a5a7755b955b755b8d5b65550554dd54fd54d5358f358e958f158e556e556dd56e356d94d554d494d534d474ba74b9f4ba54b9d6adcaadbaadc6adb2aa82aa6eaa7eaa6a974e973e974a973a943e9426943a942290edcfedcf6dcdadcd2d80ed806d7f2d7eab1e6b1e2b1d2b1caadcaadc6adbaadb2db01db00dafe5afd5a7ada7a5a77da7755b955b8d5b755b65550554fd54dd54d5358f358f158e958e556e556e356dd56d94d554d534d494d474ba74ba54b9f4b9d6adcaadc6adbaadb2aa82aa7eaa6eaa6a974e974a973e973a943e943a94269422916e7b6e696e696e656c036bf56bf56bf158f158e558e558e156e356d956d956d56d806d7ead7ead7e2d3d2d3bad3bad3b2adc6adb2adb2adaaaa7eaa6aaa6aaa629ac78ac72ac72ac70ab71ab6cab6cab6aa6a9a6a3a6a3a6a1a5d2a5cea5cea5ccb56e356d956d956d5553f5535553555314ba54b9d4b9d4b994a1d4a114a114a0f486ad3ead3d6d3d6d3d2cddecdd2cdd2cdce9452943e943e943a8f668f5a8f5a8f56da7ada77da7a5a7759ba59b7d9b9d9b75287d284d287528451eb51e8d1ead1e85769eb69e969df69dd66e966e766df66dd4a1f4a1d4a134a1147ad47ab47a347a16d3d2d3bad3bad3b2cdcecdbacdbacdb6943a94229422941e8f568f428f428f3eb469abe9aaa9aaa9aa69452943e943e943a6f566f426f426f3e6a726a5e6a5e6a5ad35553525354d351d287d284d28752844fd94fd6cfd8cfd64f3bcf394f3b4f38d9fb29fad9fb19fac9e779e729e769e719bd09bca9bcf9bc99a979a919a969a90a1d3555354d3525351d287d2875284d2844fd94fd8cfd6cfd64f3bcf3b4f394f38d9fb29fb19fad9fac9e779e769e729e719bd09bcf9bca9bc99a979a969a919a90a29aa69a8e9a8e9a86943a94229422941e7ec67eb27eb27eaa79da79c679c679c2cfd8cfd64fd64fd54f3b4f38cf38cf384de7cde4cde4cde44d4b4d484d484d47d0d528a5287d287d28751ecd1eb51eb51eacd4e4d4bcd4bcd4b4ccaccc9ccc9ccc95a50fa509a50ea508a3d6a3d1a3d5a3d09a979a919a969a909993998e9992998dae943e943a942694228f5a8f568f468f426a5e6a5a6a466a42664e664a663a6636d287528452845283d1ead1e851e851e7cd4b4d484d484d47ccc94cc6ccc6ccc65688

private theorem cap1111111000111Accepted : Accepted table cap1111111000111Box cap1111111000111Tree := by
  decide +kernel

private def cap111111100011Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1111111000110Tree <*> cap1111111000111Tree

private theorem cap111111100011Accepted : Accepted table cap111111100011Box cap111111100011Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111111100011Box 3 (midpoint cap111111100011Box 3) = cap1111111000110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000110Accepted
  · have h : rightBox cap111111100011Box 3 (midpoint cap111111100011Box 3) = cap1111111000111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111000111Accepted

private def cap11111110001Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111111100010Tree <*> cap111111100011Tree

private theorem cap11111110001Accepted : Accepted table cap11111110001Box cap11111110001Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11111110001Box 2 (midpoint cap11111110001Box 2) = cap111111100010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100010Accepted
  · have h : rightBox cap11111110001Box 2 (midpoint cap11111110001Box 2) = cap111111100011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100011Accepted

def cap1111111000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11111110000Tree <*> cap11111110001Tree

theorem cap1111111000Accepted : Accepted table cap1111111000Box cap1111111000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1111111000Box 1 (midpoint cap1111111000Box 1) = cap11111110000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110000Accepted
  · have h : rightBox cap1111111000Box 1 (midpoint cap1111111000Box 1) = cap11111110001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110001Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover50
