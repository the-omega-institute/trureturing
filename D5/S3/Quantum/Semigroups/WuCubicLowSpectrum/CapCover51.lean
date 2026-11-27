import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover51

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap11111110010Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (3 / 4, 7 / 8), (3 / 4, 7 / 8)]

private def cap111111100100Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (3 / 4, 13 / 16), (3 / 4, 7 / 8)]

private def cap1111111001000Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (3 / 4, 13 / 16), (3 / 4, 13 / 16)]

private def cap1111111001000Tree : Option PackedTree := decode 7 0xf7adf7aa77aa77a976f6f6f476f476f3ebb56bb2ebb2ebb1eb16eb14eb14eb145d76ad765d765d763d62dd629d629d628c8fbc8f4c8f4c8f2c7bcc7b6c7b6c7b5a3bd53bd0bbd4bbcffba3fba27ba3bba1f5d975d575d8f5d4f5b075aef5b035ae50000b7747f744f7477743f6f476f0f6f3f6f06b60eb5deb606b5ceb14eb126b146b11d3aecbaeabaec7aea7ad83ad77ad81ad7391e991c791e591c3909b90919099908f75b075aef5b035ae758a7589358a3588f213721232133211f1edb1ebb1ed71eb690fbd53bd4bbd0bbcffba3fba3bba27ba1f5d975d8f5d575d4f5b075b035aef5ae48000b7747f7477744f743f6f476f3f6f0f6f06b60eb606b5deb5ceb14eb146b126b11d3aecbaec7aeabaea7ad83ad81ad77ad7391e991e591c791c3909b90999091908f75b075b035aef5ae758a758a35893588f213721332123211f1edb1ed71ebb1eb691dea5de7fde7fde7bdd1ddd0fdd0fdd0baec7aea7aea7aea3ad81ad73ad73ad6f7ba3bba1fba1fba17b79fb783b783b77f5b035ae75ae75adf58a3588f588f588a9d763d753d753d751d6c0d6b9d6b9d6b7c8f2c8e1c8e1c8dfc84cc847c847c845bad81ad73ad73ad6fac51ac47ac47ac459099908f908f908b8f6b8f5b8f5b8f59486bb7b7b7a3b7a3b79fb357b347b347b3431ef31edb1edb1ed71b2f1b1f1b1f1b1af6f476f0f6f3f6f07668f66576687664e3db63d763dae3d6e363e3606363635fd7dbd1dbcfdbc3dbc1d9a3d9a1d995d9938f6d8f6b8f5d8f5b8d8f8d8d8d818d7f7b79fb783b783b77fb343b327b327b3231ed71eb71eb71eb31b1b1aff1aff1afab4723ef23d323d323cb1ef31edb1edb1ed6cdb6cd9acd9acd96c972c95ac95ac956e47a6471e4796470e426e42464266423ddfc5df55dfb5df45db6ddb45db65db3dc84dc848c84cc847c7b6c7aec7b5c7adbb6dbb68bb6cbb67baf1baecbaf0baeba6efe2efaaefdaefa2ebc6ebb2ebc2ebaecd9acd7acd96cd76c95ac93ac956c9368791e991e591c791c3909b90999091908f77f177ed77d577d176db76d976d176cf7213721332123211f1edb1ed71ebb1eb6edb6edb2eda2ed9eebc6ebc2ebb2ebae9bbf8bbf6bbeabbe8baf1baf0baecbaebb366b365b35eb35db256b255b24eb24da323cb23872387237f1ed71eb71eb71eb2efdaefa2efa2ef9aebc2ebaeebaeebaaddfb5df45df45df35d785d75dd75dd7559b2d9aed9aed9ae592ad926d926d92650d63de63db63db63dae365e363e363e363592e592b592b592ad8cd58cb58cb58cadc7b6c7aec7b5c7adc6c7c6c0c6c6c6bfb256b24eb255b24db196b18fb195b18eaf1edb1ed71ebb1eb71b1f1b1b1b031afec95ac956c93ac936c65ac656c63ec63ae3dae3d6e3d6e3d66363635fe35fe35f592ad926d926d92658cad8c758c758c6d688

private theorem cap1111111001000Accepted : Accepted table cap1111111001000Box cap1111111001000Tree := by
  decide +kernel

private def cap1111111001001Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap1111111001001Tree : Option PackedTree := decode 7 0x3debbdeb9deaddeabdbdfdbdddbd5dbd391fb91f991ed91eb8f7d8f7b8f718f6f7bd73bd6fbd57bd53b7bbb7b7b7a7b7a35daf5dab5d9b5d9758bb58b758ab58a6ebb5ebb56bb36bb2eb176b16eb156b14e47e647de47ae47a63dee3de63dbe3db50fbd5bbd57bd1bbd13ba47ba43ba33ba2f5d9f5d9b5d675d5f5b0f5b0b5afb5af6f748f74877467745f6f576f4f6f1f6f16b61eb616b5f6b5eeb15eb156b136b12d3aecfaecdaeb3aeafad87ad85ad7dad7b91ed91eb91cf91cb909f909d9095909375b0f5b0b5afb5af758af58ab589b5897213f213b212b21271ee31edf1ec31ebe91deabdea9de89de85dd21dd1fdd17dd13aecdaecbaeafaeabad85ad83ad7bad7620005bba43ba3fba2fba27b7a7b7a3b78bb7875b0b5b075af75aef58ab58a7589758929d766d765d757d755d6c2d6c1d6bdd6bbc8f5c8f4c8e5c8e3c84ec84dc849c848bad85ad83ad7bad77ac55ac53ac4bac49909d909b909390918f6f8f6d8f5f8f5d486bb7bfb7b7b7abb7a3b35fb357b34fb3471efb1ef31ee31edb1b371b2f1b271b1ef6f576f4f6f1f6f17669f66976667665e3dc63dbe3d863d7e364e36463616360dede9ede8ede2ede1ecd2ecd1eccbeccac7b7c7b6c7afc7aec6c8c6c7c6c1c6c0ad1c8fdc8fcc8f6c8f5c7bec7bdc7b8c7b7b36fb36eb368b367b25eb25db258b257b91f991f791eb91e98f7b8f798f6f8f6d66dd66db66cf66cd64bb64b964af64ad5e47b647ae473e472e3dc63dbe3d863d7ddfd5dfcddf75df65d79dd795d775d76dbbfabbf9bbeebbecbaf3baf2baeebaedb368b367b360b35fb258b257b250b24fa323d723d32397238f213b213721272122efe6efe2efb2efaaedbaedb6eda6eda2e4276426e424e42463dbe3db63d7e3d75db75db6ddb4ddb45d795d78dd76dd765377f377f177d977d575e575e375db75d966cf66cd66bf66bd64af64ad649f649d4358f7d8f798f718f6d8d9b8d978d938d8f64bd64b964b164ad633963356331632d71ee31edf1ec31ebf1b271b231b0b1b06c962c95ec942c93ec662c65ec646c642e3dbe3db63d7e3d763646363e360e360592bd92b5927d92758cbd8cb58c858c7d688

private theorem cap1111111001001Accepted : Accepted table cap1111111001001Box cap1111111001001Tree := by
  decide +kernel

private def cap111111100100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1111111001000Tree <*> cap1111111001001Tree

private theorem cap111111100100Accepted : Accepted table cap111111100100Box cap111111100100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111111100100Box 3 (midpoint cap111111100100Box 3) = cap1111111001000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001000Accepted
  · have h : rightBox cap111111100100Box 3 (midpoint cap111111100100Box 3) = cap1111111001001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001001Accepted

private def cap111111100101Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (13 / 16, 7 / 8), (3 / 4, 7 / 8)]

private def cap111111100101Tree : Option PackedTree := decode 7 0x3decbdebbdec5deb9dbebdbdfdbe9dbdd920b91fb920591f98f898f7d8f878f7b7bd8bbd87bd77bd73b7d3b7cfb7bfb7bb240b240723f723f31f0f1f0b1efb1ef6f7b0f7ae77ae77adf6f9f6f776f776f6e480e47e647e647de3e163dee3dee3de56bb7d7b7bfb7bfb7b7b36bb35fb35fb3571f131efb1efb1ef31b431b371b371b2e9c905c8fdc902c8fcc7c4c7bec7c3c7bdb377b36fb374b36eb262b25eb261b25db920591f991fb91f78f878f7b8f7d8f7966e966dd66df66db64c364bb64bd64b9563e263df63df63de63686366e366e365d931592f592f592e58cfd8ce58ce58cd52277ae77aaf7adf7aa76f776f4f6f6f6f46bb5ebb36bb56bb2eb176b156b16eb14dd76bd766d76ad765d62ed62ad62dd629c8fcc8f5c8fbc8f4c7bdc7b7c7bcc7b6a2353b7bbb7a7b7b7b7a3b35bb34bb357b3471ef71edf1ef31edb1b331b231b2f1b1ec68cc8fcc8f5c8fbc8f4c7bdc7b7c7bcc7b6b36eb367b36db366b25db257b25cb256b1a98f7b8f6f8f798f6d8d998d918d978d8f64bb64af64b964ad6337632f6335632d63443

private theorem cap111111100101Accepted : Accepted table cap111111100101Box cap111111100101Tree := by
  decide +kernel

def cap11111110010Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111111100100Tree <*> cap111111100101Tree

theorem cap11111110010Accepted : Accepted table cap11111110010Box cap11111110010Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11111110010Box 2 (midpoint cap11111110010Box 2) = cap111111100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100100Accepted
  · have h : rightBox cap11111110010Box 2 (midpoint cap11111110010Box 2) = cap111111100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover51
