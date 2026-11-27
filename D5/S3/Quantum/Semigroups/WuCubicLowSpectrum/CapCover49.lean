import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover49

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap1111110Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 4, 1), (3 / 4, 1)]

private def cap11111100Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 4, 7 / 8), (3 / 4, 1)]

private def cap111111000Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 4, 7 / 8), (3 / 4, 7 / 8)]

private def cap111111000Tree : Option PackedTree := decode 7 0x3d9b5d9afd9afd9abd735d72fd72fd72d8da18d9b8d9b8d978b458b418b418b3f71b431b371b371b2f168b16831683167ec67ec672c672c66ac26ec262c262c25e8ecd7ecccecd5eccaec1dec1aec1cec18c6cdc6c2c6cbc6c0c621c61dc620c61bbd83bd835d839d831d72fd727d72dd7258c438c3b8c418c378b418b398b3f8b374e366e3616365e3606310e30ee310630dd8ce58c8d8cd58c7d88758855886d884dc621c61dc620c61bc5a0c59cc59fc59bb10eb10ab10db109b098b094b097b093a43ecd7ecd5eccceccaec1dec1cec1aec18c6cdc6cbc6c2c6c0c621c620c61dc61bbd83bd839d835d831d72fd72dd727d7258c438c418c3b8c378b418b3f8b398b374e366e365e36163606310e310630ee30dd8ce58cd58c8d8c7d8875886d8855884dc621c620c61dc61bc5a0c59fc59cc59bb10eb10db10ab109b098b097b094b093a4766af66576657664760e760c760c760b6365e3606360635f6310630de30de30cdec1cec18ec18ec16eb96eb92eb92eb90c620c61bc61bc619c59fc59bc59bc599a71b2f1b031b031afb1883186f186f1866c66ac63ec63ec636c436c426c426c41ee310630de30de30ce2cfe2cde2cde2ccd886d884d884d883d84bd849d849d849521aeb9aeb97eb97eb96eac3eac0eac0eabfb09bb098b098b097afe0afddafddafdcbd72fd727d72dd725d581d579d57fd57761316129612f61275fbb5fb35fb95fb15f5cbf5cb75c9f5c97560755ff55e755dd84c584bd84a5849d7eed7ee57ecd7ec5eb96eb92eb92eb90eabfeabbeabbeabab097b093b093b092afdcafd8afd8afd7ad1b19fb19cb19cb19ab09bb098b098b0979860985d985d985c9779977697769775b633963236335631f621d6215621b621344ad449b44a9449743a3439b43a143996c43ac42ac436c426c262c252c25ec24e8746873687428732858e857e858a857a9a256a24da254a24ba163a15fa162a15e985d9859985c98589776977297759771a1d8ce58cd58c8d8c7d8875886d8855884d12b512a5126d125d0e8d0e850e6d0e65b10eb10db10ab109b098b097b094b093a1d1a1d0a1cda1cca163a162a15fa15ea6895a89528936892e858e858a857e857a61766172616661625dda5dd65dca5dc68b19ab18fb18fb18db10db109b109b107a254a24ba24ba249a1d0a1cca1cca1cab621b62136213620f612f61276127612543a143994399439542c542bd42bd42bb4d12a5125d125d124d0b150af50af50aecc2e4c2c4c2c4c2b4bbacbb8cbb8cbb850d584dd84c584c584bd7f057eed7eed7ee4bbccbbb4bbb4bbacb704b6f4b6f4b6edb098b094b097b093afddafd9afdcafd8977697729775977196de96da96dd96d9aec262c25ec252c24ebf76bf72bf66bf625dda5dd65dca5dc65b7a5b765b6a5b66d84bd849d849d84957ee57ec57ec57ebcbbacbb8cbb8cbb84b6ecb6ccb6ccb6c5688

private theorem cap111111000Accepted : Accepted table cap111111000Box cap111111000Tree := by
  decide +kernel

private def cap111111001Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap111111001Tree : Option PackedTree := decode 6 0xf66e766df66cf66c75ce75cdf5ccf5cc58d0d8d058cf58ced84ed84e584d584cdecdbecdaecd8ecd7eb9beb9aeb98eb97b1a0b19fb19db19cb09cb09bb099b098afb367b363b33fb33bae67ae63ae57ae52c67ac676c652c64ec26ac266c25ac256f66c766bf667766675cc75cbf5ca75c9e3676366e362636162d0e2d062cee2ce5c6cec6cdc6c4c6c2c5a1c5a0c59dc59cb19db19cb193b191b099b098b095b094a1aeb9ceb9aeb99eb97eac5eac3eac2eac0b09db09bb09ab098afe2afe0afdfafddbd733d731d72bd729d585d583d57dd57b61356133612d612b5fbf5fbd5fb75fb57ae63ae5fae53ae4fab07ab03aaf7aaf2c266c262c256c252bf7abf76bf6abf66b46c686c682c67ac676c276c272c26ac266618a6186617e617a5dee5dea5de25dded8d058cfd8ced8ce584e584dd84cd84c4c30cc304c2f4c2ecbbd4bbccbbbcbbb57633d633b6329632761356133612d612b30bf30bd30b730b52ef12eef2ee92ee76c676c672c64ec646c266c262c256c252895e895a893e89368592858e8582857ed12bd12b5127d126d0b250b1d0b050afcc2f4c2ecc2d4c2ccbbbcbbb4bb9cbb950d584ed84dd84d584c57f157f057efd7eecbbdcbbccbbc4bbb4b714b704b6fcb6f5b09ab098b096b094afdfafddafdbafd9977897769774977296df96de96dc96daa88

private theorem cap111111001Accepted : Accepted table cap111111001Box cap111111001Tree := by
  decide +kernel

private def cap11111100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap111111000Tree <*> cap111111001Tree

private theorem cap11111100Accepted : Accepted table cap11111100Box cap11111100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11111100Box 3 (midpoint cap11111100Box 3) = cap111111000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111000Accepted
  · have h : rightBox cap11111100Box 3 (midpoint cap11111100Box 3) = cap111111001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111001Accepted

private def cap11111101Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (7 / 8, 1), (3 / 4, 1)]

private def cap11111101Tree : Option PackedTree := decode 6 0xf66ff66e766f766df5cf75ce75cef5cdd8d258d0d8d1d8d0584fd84ed84f584e5ecdeecdbecdcecdaeb9deb9beb9ceb9ab1a3b1a0b1a1b19fb09eb09cb09db09babae7bae73ae73ae6bab1bab17ab17ab0ec27ec276c276c26ebf8ebf8abf8abf829b1a4b1a1b1a3b1a0b09fb09db09eb09c9865986298649861977d977b977c977ab634763416343633f613d6139613b613730c930c330c530c12ef92ef52ef72ef35584fd84ed84ed84dd7f1d7f157f157f04bbecbbdcbbdcbbccb71cb714b714b70522766df66c766d766bf5cdf5cc75cd75cbd8d058ced8cfd8ce584e584cd84dd84c58d4eb9beb98eb9aeb97eac4eac1eac3eac0b09cb099b09bb098afe1afdeafe0afddb1a32c682c676c67ec672c272c266c26ec2626186617a618261765dea5dde5de65ddac6a584e584ad84dd84a57f0d7ed57f057eccbbd4bb9cbbccbb94b70cb6dcb704b6d5443

private theorem cap11111101Accepted : Accepted table cap11111101Box cap11111101Tree := by
  decide +kernel

def cap1111110Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11111100Tree <*> cap11111101Tree

theorem cap1111110Accepted : Accepted table cap1111110Box cap1111110Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1111110Box 2 (midpoint cap1111110Box 2) = cap11111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111100Accepted
  · have h : rightBox cap1111110Box 2 (midpoint cap1111110Box 2) = cap11111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover49
