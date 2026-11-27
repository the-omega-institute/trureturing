import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover58

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap1111111001101111Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (13 / 16, 7 / 8)]

private def cap11111110011011110Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (13 / 16, 27 / 32)]

private def cap111111100110111100Box : Box := ![(47 / 40, 19 / 16), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (13 / 16, 27 / 32)]

private def cap111111100110111100Tree : Option PackedTree := decode 8 0x3bb2fbb2dbb21bb1db863b861b859b855a6e9a6e7a6dfa6dda507a505a4fda4fb770c770c370b370ab6cff6cfb6ce36cdf4a0f4a0b49fb49f7470346ff46ef46ea9d374d373d36fd36ed1c0d1bfd1bbd1bace2dce2cce26ce25cc74cc73cc6dcc6ca3765b7657763b763370c370bf70ab70a34dcf4dcb4dbb4db74a0b4a0749f749f2ee186e17ee156e146d9f6d9eed9bed9b69416940e93ee93e68dfe8df68dd68dcd3a6e7a6e5a6dda6dba37fa37da375a3739c599c579c4b9c4998e798e598d998d743dd90dd8edd87dd85dc2cdc2adc23dc21d36fd36ed368d366d27ed27dd277d275bbb0fbb0dbaf3baf1b847b845b831b82fa6d1a6cfa6bda6bba4efa4eda4dba4d97761b761775e375df708b7087705f705b4d9f4d9b4d774d7349db49d749b349aeb5b859b855b831b82db671b66fb655b651a4fda4fba4dba4d7a377a375a369a3674e9b7e9b769b469b3693f693ee93be93ae7136712e710e710668de68d668b668add368d366d35ed35cd277d275d26dd26bce21ce20ce16ce13cd16cd15cd0fcd0dab49fb49f749b749af46ef46eb46d346cf346f346b343f343731b731b33193318e91bb1dbb19bb0bbb07b855b851b843b83fa6dda6dba6cda6c9a4fba4f9a4eba4e777617761375df75db70877083705b70574d9b4d974d734d6f49d749d349af49aaeec26ec1eebb6ebaee106e0fee0aee0a69b2e9b269ade9ad693a6939e9356934d6b70ab70a3705b70536cdf6cdb6ca36c9b49f749f349af49a746eb46e746cf46ca9d36ed36dd366d364d27dd27cd275d273ce25ce24ce20ce1fcd1acd19cd15cd14ba6cda6c9a6b9a6b5a4eba4e7a4d7a4d39c419c3f9c279c239a2b9a299a1b9a175693ee93e6935e934e8dd68dce8d9e8d9668d668ce686e685e6366635e631e631521adb3fdb3edb38db37d999d998d993d992cc74cc73cc6dcc6ccafdcafccaf7caf6bb67db67bb66fb66db331b32fb325b32398e798e598d998d795f995f795ed95eb5ed9c6d9bed956d946cc9ecc96cc4ecc468dde8dd68da68d9e84c684be8496848dd1bbd1bad1b4d1b3d098d097d092d091cc6dcc6ccc64cc63caf7caf6caeccaeba36cdf6cdb6ca36c9b664b66476623661f46eb46e746cf46cb425f425b42474242e8dd68dce8d9e8d9684be84b6848e84866366635e631e631657b657ae575e57550d1

private theorem cap111111100110111100Accepted : Accepted table cap111111100110111100Box cap111111100110111100Tree := by
  decide +kernel

private def cap111111100110111101Box : Box := ![(19 / 16, 6 / 5), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (13 / 16, 27 / 32)]

private def cap1111111001101111010Box : Box := ![(19 / 16, 6 / 5), (189 / 320, 1953 / 3200), (25 / 32, 13 / 16), (13 / 16, 27 / 32)]

private def cap1111111001101111010Tree : Option PackedTree := decode 5 0x3e76de76be75fe75de3bde3bbe3b1e3afb67fb67db671b66fb333b331b327b3257ced7ced3cebbceb7c777c773c75fc75b6cfb6cf76cdf6cdb6663665f664b6646bf3aff3aef3a1f39ff2a1f2a0f29cf29be349e348e33de33be271e270e26ce26bbe543e541e539e537e3b1e3afe39be399c4e3c4e1c4d9c4d7c39fc39dc393c3914f1a4f1a4719ef19df0e7f0e770e4f0e46d9c6d9bed956d946cc9ecc96cc4ecc451e75de75be73fe73be541e53fe537e535c691c68fc677c673c4e1c4dfc4d7c4d57ca83ca7fca6fca6bc75fc75bc733c72f89c389bf89af89ab873b87378723871e9e348e347e33be339e1cee1cde1c8e1c7db37db36db28db26d992d991d988d987a1a

private theorem cap1111111001101111010Accepted : Accepted table cap1111111001101111010Box cap1111111001101111010Tree := by
  decide +kernel

private def cap1111111001101111011Box : Box := ![(19 / 16, 6 / 5), (1953 / 3200, 63 / 100), (25 / 32, 13 / 16), (13 / 16, 27 / 32)]

private def cap11111110011011110110Box : Box := ![(19 / 16, 6 / 5), (1953 / 3200, 63 / 100), (25 / 32, 51 / 64), (13 / 16, 27 / 32)]

private def cap11111110011011110110Tree : Option PackedTree := decode 7 0x3ed6fed6ded5ded5be9e1e9dfe9cfe9cdcbbdcbbbcbabcba9c8d9c8d7c8c7c8c57dadbdad7dab7dab3d3bfd3bbd39bd397977797739753974f91af91ab918b9186bf6aef6adf69ff69ef4e7f4e6f4ddf4dce8dde8dce8d6e8d5e7b8e7b7e7b1e7b0bd1bbd1b9d1add1abcf71cf6fcf63cf61cbabcba9cb95cb91c8c7c8c5c8b3c8b147b56fb567b4f7b4efa737a72fa6e7a6d746e746df46af46a73dbf3db73d873d7880016e8dce8dbe8d5e8d4e7b7e7b6e7b0e7afe5d4e5d3e5c8e5c7e462e461e458e457a1af4f0f4eef4e7f4e5f3aff3aef3aaf3a9e46ce46ae463e461e349e348e344e343be9cfe9cbe9bbe9b7e755e753e743e73fc8c7c8c3c8b3c8afc689c687c67bc6762000591e5dee5dde5d5e5d4e46ce46be463e462dd90dd8fdd87dd86dc2cdc2bdc23dc22bcbbbcbb9cba9cba7c8d7c8d5c8c5c8c3bb1fbb1dbb0dbb0bb857b855b845b8435f2eaf2ea72e572e4f231f231722cf22c6ec3eec36ebceebc6e11ee116e0c6e0b880016e5d4e5d3e5c8e5c7e462e461e458e457dfa5dfa4dfa0df9fdecadec9dec5dec4bbf4bbf49bf41bf3fbd95bd93bd8bbd89bb0dbb0bbaf1baefb845b843b82fb82d435c8d9c8d5c8c7c8c3c693c691c689c687b859b855b847b843b671b66fb667b6657918f91879167915f8d138d0f8cf78cef708f70877063705b6ccf6ccb6cab6ca2a23dad7dad3dab3daafd3bbd3b7d397d3939773976f974f974b91ab91a791879182fb5a7b59fb55fb557a76fa767a727a71f2edf2ed72e972e8f234f2347230722fd7ed59ed57ed3bed37e9cbe9c9e9b5e9b3d1b7d1b5d1a9d1a7cf6dcf6bcf5fcf5c60005ba36fa36ba353a34f9edb9ed79ebf9ebb974f974b971f971791879183915f915a8f6abf6aaf69bf699f4e4f4e3f4d9f4d7e8dae8d9e8d3e8d2e7b5e7b4e7aee7ad20002dd1b5d1b3d1a7d1a5cf6bcf69cf5dcf5bcba5cba3cb8bcb89c8c1c8bfc8adc8ab435e9dde9d9e9cbe9c7e75de75be753e751c8d5c8d1c8c3c8bfc691c68fc687c6857d397d38fd36fd363cea7cea3ce7fce779187917f915f91578d0f8d0b8cef8ce4c000b23cbb9cbb7cba7cba5c8d5c8d3c8c3c8c1bb1dbb1bbb0bbb09b855b853b843b8417976f976b974b974791a791a39183917f763776337613760f70a770a37083707ebe5d3e5d2e5c7e5c5e461e460e457e456dfa4dfa3df9fdf9edec9dec8dec4dec3bbf49bf47bf3fbf3dbd93bd91bd89bd87bb0bbb09baefbaedb843b841b82db82b472e972e8f2e372e27230722ff22b722aeec26ec1eebb6ebaee106e0fee0aee0a1000166b91ab91a39187917f8d238d1f8d0f8d0b70ab70a37087707f6cdf6cdb6ccb6cc6f230f22ff22bf22af1a1f1a1719df19cee10ee0fee0b6e0a6d996d98ed946d935443

private theorem cap11111110011011110110Accepted : Accepted table cap11111110011011110110Box cap11111110011011110110Tree := by
  decide +kernel

private def cap11111110011011110111Box : Box := ![(19 / 16, 6 / 5), (1953 / 3200, 63 / 100), (51 / 64, 13 / 16), (13 / 16, 27 / 32)]

private def cap11111110011011110111Tree : Option PackedTree := decode 5 0x3ed85ed83ed7ded7be9f3e9f1e9ebe9e9cbcfcbcdcbc7cbc5c8ebc8e9c8e3c8e17dafbdaf7dadfdad7d3d7d3d3d3c3d3bb978f978b977b977391c791c391b391aaaf4f9f4f8f4f0f4eef3b6f3b5f3aff3aee475e474e46ce46ae34ee34de349e348a7979f979b977b977391d791d391b391ab765f765b7643763b70c770c370b370aaf23af23a7236723571a771a6f1a4f1a46e18ee186e166e156d9fed9f6d9c6d9bd23db07daffdaf7daf3d3e3d3dbd3d3d3cf979b9793978b978791d391cb91c391befb5efb5e7b5afb59fa7a7a79fa777a7672f172f0f2ee72ed72387237f235723455e9f1e9ede9dde9d9e76be769e75de75bc8e9c8e5c8d5c8d1c69bc699c691c68f4f2f372f272ee72ed723a7239723572346ecb6ecaeec76ec66e186e17ee156e145e474e472e46ae468e34de34ce348e347dc30dc2fdc2adc28db3edb3ddb37db36a43

private theorem cap11111110011011110111Accepted : Accepted table cap11111110011011110111Box cap11111110011011110111Tree := by
  decide +kernel

private def cap1111111001101111011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11111110011011110110Tree <*> cap11111110011011110111Tree

private theorem cap1111111001101111011Accepted : Accepted table cap1111111001101111011Box cap1111111001101111011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1111111001101111011Box 2 (midpoint cap1111111001101111011Box 2) = cap11111110011011110110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011011110110Accepted
  · have h : rightBox cap1111111001101111011Box 2 (midpoint cap1111111001101111011Box 2) = cap11111110011011110111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011011110111Accepted

private def cap111111100110111101Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap1111111001101111010Tree <*> cap1111111001101111011Tree

private theorem cap111111100110111101Accepted : Accepted table cap111111100110111101Box cap111111100110111101Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap111111100110111101Box 1 (midpoint cap111111100110111101Box 1) = cap1111111001101111010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001101111010Accepted
  · have h : rightBox cap111111100110111101Box 1 (midpoint cap111111100110111101Box 1) = cap1111111001101111011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001101111011Accepted

private def cap11111110011011110Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111111100110111100Tree <*> cap111111100110111101Tree

private theorem cap11111110011011110Accepted : Accepted table cap11111110011011110Box cap11111110011011110Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11111110011011110Box 0 (midpoint cap11111110011011110Box 0) = cap111111100110111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100110111100Accepted
  · have h : rightBox cap11111110011011110Box 0 (midpoint cap11111110011011110Box 0) = cap111111100110111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100110111101Accepted

private def cap11111110011011111Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (27 / 32, 7 / 8)]

private def cap111111100110111110Box : Box := ![(47 / 40, 19 / 16), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (27 / 32, 7 / 8)]

private def cap111111100110111110Tree : Option PackedTree := decode 8 0xeecceecc6ec96ec8eda0eda06d9d6d9ce717e71767146713e63b663ae637e6375dd98dd97dd91dd90db40db3fdb39db38d375d374d370d36fd1c1d1c0d1bcd1bbba6eba6e9a6e1a6dfa383a381a379a3779c5d9c5b9c4f9c4d98eb98e998dd98db43dd92dd91dd7cdd7bdc2edc2ddc1bdc1ad371d370d361d360d280d27fd270d26fbb85db85bb837b835b675b673b659b657a501a4ffa4e1a4dfa37ba379a36da36b4e9b8e9b869b0e9b06940693fe9386937e7146713e70ce70c668ee68e66896688dd280d27fd270d26fd1bdd1bcd1b6d1b5cd1dcd1ccd12cd11cc6fcc6ecc66cc65a46ec8eec86ec4eec3ee16ee166e12ee11e9b869b7e9b569b4693fe93f693ce93bddd89dd88dd7bdd7adc25dc24dc1adc19d36ad369d360d35fd279d278d26fd26ebbb11bb0fbaf5baf3b849b847b833b831a6d3a6d1a6bfa6bda4f1a4efa4dda4db5adc2ddc2cdc1adc18db39db38db2bdb2ad27fd27ed26fd26dd1bcd1bbd1b5d1b4a74dc34dbf4dab4da349ff49fb49e749df389f389b388b38873473346f345f345ae9b569b469b069af693ce93be937e936e7116710e70c670b668be68b6688e687d5a4ffa4fda4dfa4dba379a377a36ba3699a399a379a239a1f98dd98db98cb98c9486b6d076cff6ceb6ce3666f66676657664f31db31d331bf31b72bfb2bf72be72bdeed9d6d9ced966d95eccaecca6cc5ecc56637e63766336632e57ce57c65776576ddb39db38db2bdb2ad994d993d98ad989cc6ecc6dcc65cc64caf8caf7caedcaecad1

private theorem cap111111100110111110Accepted : Accepted table cap111111100110111110Box cap111111100110111110Tree := by
  decide +kernel

private def cap111111100110111111Box : Box := ![(19 / 16, 6 / 5), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (27 / 32, 7 / 8)]

private def cap111111100110111111Tree : Option PackedTree := decode 8 0x3ed89ed87ed73ed71e771e76fe763e761bb33bb31bb25bb23b683b681b675b6737db0fdb0bdae3dadfd3ebd3e7d3c7d3c397a3979f977f977b91db91d791b791b2fa7d7a7cfa78fa7879dbf9db79d879d7f23b723af236f23671a7f1a771a571a4d3cbd1cbcfcbbfcbbdc8edc8ebc8dbc8d9bb31bb2fbb23bb21b865b863b85bb859791db91d791b791b38d3f8d3b8d2b8d2770cb70c770b770b36d036cff6ce76ce290fdae7dae3da8bda87d3cbd3c7d383d37f9783977f9737973391bb91b79173916efa797a78fa707a6ff9d8f9d879d1f9d172377236f22e722df1a5f1a5719ff19f53cbc1cbbfcb9bcb99c8ddc8dbc8b9c8b7bb25bb23baf9baf7b85db85bb837b835791bb91b79173916f8d2f8d2b8cff8cfb70bb70b7706f706b6ceb6ce76cb36cae91ed71ed6fed61ed5de9e3e9e1e9d3e9cfcbbfcbbdcbafcbabc8dbc8d9c8cbc8c77dac3dabfda87da83d3a7d3a3d37fd37b975f975b9733972f91979193916f916afb57fb577b507b4ffa747a73fa6f7a6ef2eb72eaf2e5f2e572327231f22d722cd6bd3c7d3c3d37fd377cec3cebfce8bce8791b791b3916f91678d2b8d278cfb8cf69e5dfe5dee5d7e5d5e46de46ce465e463dd91dd90dd89dd87dc2ddc2cdc25dc23bcbafcbadcb99cb97c8cbc8c9c8b7c8b5bb13bb11baf7baf5b84bb849b835b8337975b9757972f972b9193918f916b91677623761f75eb75e77093708f70677062b5c8dbc8d9c8b7c8b3c695c693c67dc67bb85bb859b835b831b673b671b657b655486bcee3cedfcec7cec3c783c77fc76bc7676d076d036ceb6ce7666f666b66576652f9dbf9db79d879d7f8eff8ef78ecf8ec6da06d9fed9ced9c6ccd6cccecca6cc9d7e763e761e747e745e3b5e3b3e39fe39db675b673b659b657b32bb329b317b3157cec3cebfce8bce87c767c763c73bc7378d2b8d278cfb8cf78743873f872b8726f1a571a4f19f719ef0e870e7f0e570e4ed9ced9c6d95ed956cca6cc9ecc56cc4d0d1

private theorem cap111111100110111111Accepted : Accepted table cap111111100110111111Box cap111111100110111111Tree := by
  decide +kernel

private def cap11111110011011111Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111111100110111110Tree <*> cap111111100110111111Tree

private theorem cap11111110011011111Accepted : Accepted table cap11111110011011111Box cap11111110011011111Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11111110011011111Box 0 (midpoint cap11111110011011111Box 0) = cap111111100110111110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100110111110Accepted
  · have h : rightBox cap11111110011011111Box 0 (midpoint cap11111110011011111Box 0) = cap111111100110111111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100110111111Accepted

def cap1111111001101111Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11111110011011110Tree <*> cap11111110011011111Tree

theorem cap1111111001101111Accepted : Accepted table cap1111111001101111Box cap1111111001101111Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1111111001101111Box 3 (midpoint cap1111111001101111Box 3) = cap11111110011011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011011110Accepted
  · have h : rightBox cap1111111001101111Box 3 (midpoint cap1111111001101111Box 3) = cap11111110011011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011011111Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover58
