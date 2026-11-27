import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover47

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap11110Box : Box := ![(1, 6 / 5), (63 / 200, 63 / 100), (3 / 4, 1), (1 / 2, 3 / 4)]

private def cap111100Box : Box := ![(1, 11 / 10), (63 / 200, 63 / 100), (3 / 4, 1), (1 / 2, 3 / 4)]

private def cap111100Tree : Option PackedTree := decode 12 0x3249ba69b8c9ba59b8b9a799a639a789a62924692309245922f9152914291519141b1a934f334c734f134c532f732e532f532e322a5228522a32283210520f3210320f163464923490c4922c90bc8a94896c8a8c896462746144626c613c5c145b645c0c5b5d52454a44b6454644b2420a41c2420641be2e0a2db22e062dae2bc62b7e2bc22b7aa223524cbdccb94cbd4cb8cc664c61cc65cc614841483cc840c83c480147fcc800c7fc58d498cc98ba98cb98b9985798469856984590028ff090018fef8f9a8f8a8f998f89a8c908290709081906f90028ff090018fef8af18adf8af08ade8a8d8a7b8a8c8a7aaa480147f84800c7f7c7cd47c547ccc7c4c546c53dc546453d4511450a4510c509d44468c9189d1851189b184f170516d9170316d70d0f0ce30d0d0ce10c090be70c070be5548b828b6c8b818b6b8af18adf8af08ade860485f3860385f28595858485948583a8c3444339434343384302c2fa4301c2f9419bc194419b4193c16b4163c16ac1635860585f4860385f2859685858594858382d682c782d582c6827e826f827d826ea446a48af18adf8af08ade8a8d8a7b8a8c8a7a85958584859485838547853685468535aa2a3a29f22a3229ea288e28562886284e152214de151a14d613be139e13ba139a985968585859485838548853785468535827e826f827d826e8235822982348228b0a910a6f0a8d0a6b09df09cf09dd09cd046b04530469045103bd03b303bb03b1488d111a926162611e615a61165f765f465f6e5f3e3e6e3e2e3e663e263cca3cb63cc63cb2cbeecbe8cbedcbe7cbb8cbb64bb84bb5c7994796c798c7964770476dc76fc76d531f371f171f331f131e651e5b1e631e591447142b14431427137d1373137b137163cca3cb63cc63cb23b823b6e3b7e3b6a26fa26e626f626e225ee25da25ea25d6911a92ee32ed92ee12ed72db32da92db12da712f712ed12f512eb121d1213121b121163464511c50ac510c509c4bdc4bb44bd44bac277c273c2774273423b4238c23ac238584ef84e784ee84e6847684718475847081de81d981dd81d88166816181658160a235225ee25da25ea25d6243a242624362422059a058605960582046a045604660452c6888d1

private theorem cap111100Accepted : Accepted table cap111100Box cap111100Tree := by
  decide +kernel

private def cap111101Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 63 / 100), (3 / 4, 1), (1 / 2, 3 / 4)]

private def cap1111010Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 4, 1), (1 / 2, 3 / 4)]

private def cap1111010Tree : Option PackedTree := decode 11 0x324ecc9ecc1ecc8ecc0ec17ec11ec16ec10c6bfc6b7c6bec6b6c61ac614c619c613b1a9d82fd811d82dd80fd723d70fd721d70d8c358c178c338c158b358b218b338b1f5198d7f8d6f8d7d8d6d8c358c298c338c27631d630d631b630b62116205620f62036358c378c198c338c158b378b238b338b1f621361f5620f61f16127611d6125611b488d4eb92eb88eb90eb86eb12eb0eeb11eb0dc59bc591c599c58fc525c521c524c520bd625d61dd623d61bd577d56dd575d56b8a4b8a438a498a4189a9899f89a7899d4e2cde2c8e2cce2c7e26a6267e269e2675849d84758495846d7ec57e9d7ebd7e9511a3258c758be58c6d8bdd884587cd883d87c5125511c5124d11bd0e5d0ded0e550de55621361f5620f61f16127611d6125611b4399437d4395437942bd42b342bb42b14ca24aa238a249a237a1cba1bda1caa1bc985798469856984597dc97d097db97cfaa873286fa872a86f2857a8566857685625f765f465f6e5f3e5dc65db25dc25dae911a96127611d6125611b5fb15fa75faf5fa542bd42b342bb42b141a3419941a141976857a856685768562834683328342832e5dc65db25dc25dae5b665b525b625b4e88d111a

private theorem cap1111010Accepted : Accepted table cap1111010Box cap1111010Tree := by
  decide +kernel

private def cap1111011Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (3 / 4, 1), (1 / 2, 3 / 4)]

private def cap11110110Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (1 / 2, 3 / 4)]

private def cap111101100Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (1 / 2, 5 / 8)]

private def cap111101100Tree : Option PackedTree := decode 1 0xc

private theorem cap111101100Accepted : Accepted table cap111101100Box cap111101100Tree := by
  decide +kernel

private def cap111101101Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (5 / 8, 3 / 4)]

private def cap1111011010Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (5 / 8, 3 / 4)]

private def cap1111011010Tree : Option PackedTree := decode 10 0x325b7c5b61db7bdb615ae55ace5ae4dacdd6205607d61fd60755a05590559fd58fdb5cab59cb5c9b59bb4c2b4a8b4c1b4a7ab40ab20ab3fab1faa73aa59aa72aa58a6b102b03eb0feb03aa9cea966a9caa96299de995a99da995693a29342939e933e88d4b4c2b4a8b4c1b4a7b40bb3f5b40ab3f4aa73aa59aa72aa58a9e4a9cea9e3a9cdb681767eb681567e966bb668f66b9668d53c9539d53c7539b52b1528d52af528b4d539d52cd539552c54ac54a354abd4a2d27452685273d267d1dfd1d7d1df51d7511a3299de995a99da995693a29342939e933e7e1a7dae7e167daa795678fe795278facfc34fb5cfc2cfb54f2acf1fcf2a4f1f4dd34dc64dd2cdc5cd3ccd31cd3c4d31511a949d149a349cf499f477f475f477d475d34f334c734f134c532f732e532f532e280005a34446a4b35db347b35cb346b24db244b24cb243a958a946a957a945a88ea887a88da886b52b1528d52af528b511d510f511b510d477f475f477d475d45c345b145c145af446a5926d92259265921d8c758c358c6d8c2d170d16c5170516bd12551215124d120d8d19477f475f477d475d45c345b145c145af32f732e532f532e3319931873197318563528b868b628b828b5e892a890a892689066332630e632e630a615e613e615a613ac6888d1

private theorem cap1111011010Accepted : Accepted table cap1111011010Box cap1111011010Tree := by
  decide +kernel

private def cap1111011011Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (5 / 8, 3 / 4)]

private def cap1111011011Tree : Option PackedTree := decode 11 0x324f618f5ccf617f5cbf35cf313f35bf312dd14dcc9dd13dcc8daeedaa7daeddaa6aa79ae7989f9adf98978d2f8b578d278b4ed776d53ed76ed536cb46c986cb3ec97d466e8a6e64ee89ee646d776d53ed76ed5366e866c766e7e6c6e617e5f6e61765f65536bbb6a9f6bb76a9b65a364c3659f64bf30bf2fb730bb2fb32b432a872b3f2a82a2235278d2f8b578d278b4f82878167827f815ecb46c986cb3ec97ec1dec0e6c1d6c0dd53c143c0b3c13fc0afbcfbbc9bbcf7bc9760ef607360eb606f5d4b5ceb5d475ce6a3365a364c3659f64bf60ef607360eb606f2b432a872b3f2a8326f3269326ef268ea9b077b039b075b037aea5ae75aea3ae73937993499377934791c1919191bf918f5111a3266e866c766e7e6c6e617e5f6e61765f65fe8dfc9dfe85fc95f3cdf215f3c5f20d5330bf2fb730bb2fb32b432a872b3f2a82f9e6f90af9e2f906f566f4e6f562f4e2a37fa57f297fa17f257cf57c877cf17c836df16d876def6d856b956b396b936b376f9eaf90ef9e2f906f56af4eaf562f4e2d72ad672d726d66ed30ad2a2d306d29e911a932b432a872b3f2a8326f3269326ef268ef566f4e6f562f4e2f232f1d6f22ef1d2a9937993499377934791c1919191bf918f791978eb791778e977cf77a377cd77a151bd5abd3abd58bd38bc8dbc76bc8bbc74b4c2b4a8b4c1b4a7b40bb3f5b40ab3f4b791b78ed791778e977d177a577cd77a1681767eb681567e966bb668f66b9668d488d111a92779f7793779ef792f7437739f742f7396ba96b9d6ba8eb9ceb5c6b52eb5beb5255dd0fdce9dd0bdce5dbc1dba5dbbfdba3ad73ad4dad6fad49ac47ac2fac45ac2d4cd752d73ad751d739d6b8d6a5d6b7d6a4c8e0c8c8c8dfc8c7c846c835c845c834ab5ae75a9b5adf5a93588f585f588b585b211f20db211720d31eb71e931eb31e8e911a9dbc1dba5dbbfdba3d993d983d991d981ac47ac2fac45ac2daa93aa87aa91aa857588f585f588b585b5527550f5523550b1eb71e931eb31e8f1aff1adf1afb1ada88d1991c3919391bf918f908f906d908b906977d177a577cd77a176cf76b376cd76b17211f20db211720d31eb71e931eb31e8eed9eed66ed9aed62ebaeeb92ebaaeb8e9bbe8bbd2bbe6bbd0baebbae4baeabae3b35db347b35cb346b24db244b24cb243a23531eb71e931eb31e8f1aff1adf1afb1adac936c912c932c90ec63ac61ac636c616c6888d1

private theorem cap1111011011Accepted : Accepted table cap1111011011Box cap1111011011Tree := by
  decide +kernel

private def cap111101101Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap1111011010Tree <*> cap1111011011Tree

private theorem cap111101101Accepted : Accepted table cap111101101Box cap111101101Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap111101101Box 0 (midpoint cap111101101Box 0) = cap1111011010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111011010Accepted
  · have h : rightBox cap111101101Box 0 (midpoint cap111101101Box 0) = cap1111011011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111011011Accepted

private def cap11110110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap111101100Tree <*> cap111101101Tree

private theorem cap11110110Accepted : Accepted table cap11110110Box cap11110110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11110110Box 3 (midpoint cap11110110Box 3) = cap111101100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111101100Accepted
  · have h : rightBox cap11110110Box 3 (midpoint cap11110110Box 3) = cap111101101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111101101Accepted

private def cap11110111Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (7 / 8, 1), (1 / 2, 3 / 4)]

private def cap11110111Tree : Option PackedTree := decode 1 0xc

private theorem cap11110111Accepted : Accepted table cap11110111Box cap11110111Tree := by
  decide +kernel

private def cap1111011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11110110Tree <*> cap11110111Tree

private theorem cap1111011Accepted : Accepted table cap1111011Box cap1111011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1111011Box 2 (midpoint cap1111011Box 2) = cap11110110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11110110Accepted
  · have h : rightBox cap1111011Box 2 (midpoint cap1111011Box 2) = cap11110111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11110111Accepted

private def cap111101Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap1111010Tree <*> cap1111011Tree

private theorem cap111101Accepted : Accepted table cap111101Box cap111101Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap111101Box 1 (midpoint cap111101Box 1) = cap1111010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111010Accepted
  · have h : rightBox cap111101Box 1 (midpoint cap111101Box 1) = cap1111011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111011Accepted

def cap11110Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111100Tree <*> cap111101Tree

theorem cap11110Accepted : Accepted table cap11110Box cap11110Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11110Box 0 (midpoint cap11110Box 0) = cap111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111100Accepted
  · have h : rightBox cap11110Box 0 (midpoint cap11110Box 0) = cap111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover47
