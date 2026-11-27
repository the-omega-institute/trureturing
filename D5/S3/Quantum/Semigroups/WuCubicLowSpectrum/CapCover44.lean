import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover44

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap11101111110Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 3 / 4), (7 / 8, 1)]

private def cap111011111100Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (7 / 8, 1)]

private def cap1110111111000Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap11101111110000Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111100000Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 819 / 1600), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111100000Tree : Option PackedTree := decode 5 0xe3cc63cbe3c0e3c06358e35863536352d91e591dd9155914d8c0d8c058bb58ba80084ec797c796c780c77fc707c706c6fdc6fcbadbbadabac7bac6ba7aba79ba70ba6fb8e0f8e0d8dfb8df98d618d5f8d4b8d4974f574f374e174df748b7489747b74794dd6ddd6d5d63dd635d3d5d3cdd385d37d91dd91d59145913d8e1d8e158df58dedba7aba79ba70ba6fba45ba44ba3dba3cb1c3b1c2b1beb1bdb180b17fb175b174a43c781c780c76ac769c6a6c6a5c698c697bac8bac7bab4bab3ba3eba3dba36ba35b7591758f75697567747d747b746d746b64556451642b642962ed62eb62d762d5463c063bfe3b4e3b4637ee37e6377e3775d63dd635d59dd595d385d37dd335d32dc6fdc6fcc6efc6eec6a5c6a4c697c695ba70ba6fba66ba65ba3dba3cba35ba34a6eb1eeb1aeaceeacae9c2e9bee99ae996c8a2c89ec852c84ec6fac6f6c6dac6d6dd385d37dd335d32dd1edd1e5d1add1a58df58ded8db58dad8bad8ba58b558b4d21a

private theorem cap111011111100000Accepted : Accepted table cap111011111100000Box cap111011111100000Tree := by
  decide +kernel

private def cap111011111100001Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111100001Tree : Option PackedTree := decode 7 0x39171916f9137913590559053902b90297783777f7751774f769d769b76737671720ab20a7205720531e631e5f1e071e02ed3aed36ece6ece2eb72eb6eeb22eb1e9bbc1bbbfbba8bba7bb4ebb4dbb39bb38b338b337b31fb31eb2c1b2c0b2adb2acb769d769b7673767175b975b77591758f65836581655b6559647964776455645148c8b7c8b6c8a7c8a6c829c828c81fc81ebbbfbbbebbb3bbb2bb4dbb4cbb43bb42b916d916b914d914b9051904f903d903b777d777b7765776376997697768576835e453e453644d644ce40fe40f640a6409ddd9ddd95dd3ddd35da1dda15d9c5d9bdc8a6c8a5c899c898c81ec81dc813c812bbb2bbb1bba6bba5bb42bb41bb37bb36ad6414e413e40fe40ee3cbe3cb63c663c5dda6dda5dda1dda0dd6ddd6d5d68dd685c81fc81dc814c812c78cc78bc780c77fbb43bb41bb38bb36bad1bad0bac7bac6a8dddfdddf5dd9ddd95da6dda65da1dda1599bd99b59955994d960595fd95b595adbbbebbbdbbb2bbb1bb4cbb4bbb42bb41b336b335b329b328b2bfb2beb2b5b2b4aeeeceeecaee9eee9aed0eed0aece2ecdeccaacca6cc7acc76cadacad6cab2caaeddd95dd8ddd35dd2dda15da0dd9bdd9b5994d994598ed98e595ad95a5955d95556aed36ed2eed0eed06eb6eeb6aeb46eb42cb02cafacadacad2c8eec8eac8cec8cadda1dda0dd9c5d9b5d68dd685d63dd63595b595a595659555919d91959145913d443c89bc89ac880c87fc815c814c800c7ffbba8bba7bb91bb90bb39bb38bb25bb24b902b902990018fff8f038f018ed58ed376737671764b76497591758f756975674ddd45dd3ddc8ddc85d9cdd9c5d92dd92598fd98f59835982d956d956594cd94c5bb39bb38bb25bb24bac8bac7bab4bab3b2adb2acb299b298b22ab228b215b214a4644d644ce4466445e40a6409e4056404ddd3ddd35dcdddcd5d9c5d9bdd975d96dc899c898c88bc88ac813c812c809c808bba6bba5bb9abb99bb37bb36bb2dbb2caf2233222f21ff21fb202b20271fff1ffaee6eee6aee42ee3eecbaecb6ec92ec8ee445e445643f643ee404e40463ff63feddcd5dccddc7ddc75d96dd965d91dd9156b2053204b202b20231e031dff1dd71dd2ece2ecdaecbaecb2eb1eeb1aeaf6eaf2e405640463ffe3fee3bae3ba63b4e3b45d975d965d925d915d5edd5e5d59dd59546ee9eee9aee6eee6aece2ecdeecbaecb6cc7acc76cc46cc42cab2caaeca8aca86ddd35dd2ddcd5dccdd9bdd9b5d96dd96598ed98e59885987d955d9555950d95057773777357721771f765d765b7649764766236621660b6609654565436531652f6ee6aee66ee3eee3aecb6ecb2ec8eec8acc42cc3ecc12cc0eca86ca82ca5eca5ab57671766d765d7659758f758d757b757965596555654565416451644f643d643b6ecbaecb2ec92ec8aeaf6eaf2eaceeacaca8aca82ca62ca5ac87ac876c852c84ea21a

private theorem cap111011111100001Accepted : Accepted table cap111011111100001Box cap111011111100001Tree := by
  decide +kernel

private def cap11101111110000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011111100000Tree <*> cap111011111100001Tree

private theorem cap11101111110000Accepted : Accepted table cap11101111110000Box cap11101111110000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111110000Box 1 (midpoint cap11101111110000Box 1) = cap111011111100000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111100000Accepted
  · have h : rightBox cap11101111110000Box 1 (midpoint cap11101111110000Box 1) = cap111011111100001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111100001Accepted

private def cap11101111110001Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111100010Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111100010Tree : Option PackedTree := decode 5 0xf6e276e1f6d576d4f65ef65e7657f65763cc63cbe3c0e3c06358e35863536352dedc3edc2eda9eda8ed29ed28ed19ed18d60ad609d5f4d5f3d597d596d587d586bda53da51da33da31d979d977d95dd95bab2fab2dab0fab0daa81aa7faa6baa694eb056b04eafa6af9eacbeacb6ac3eac363cbe3cb63c063bfe383e383637ee37e5d597d596d587d586d540d53fd535d534c707c706c6fdc6fcc6b0c6afc6a5c6a4a43edaaeda9ed91ed90ecafecaeec9fec9ed5f5d5f4d5dcd5dbd536d535d52ad529babebabe9abb9abb7aa6daa6baa55aa538f038f018ed58ed38d4d8d4b8d318d2f476d4f6d476c876c7f68cf68c7683f6836afa6af9eaedeaed6ac3eac36abaeaba5ed19ed18ed07ed06ecaeecadec9eec9cd587d586d575d574d535d534d529d528a757d357cf576f576b561f561b55d755d31e031dff1da71da31bf71bf31bbf1bbaeac3eac36abaeaba6a9aea9a6a94ea94637ee37e6377e3776352e352634be34ad21a

private theorem cap111011111100010Accepted : Accepted table cap111011111100010Box cap111011111100010Tree := by
  decide +kernel

private def cap111011111100011Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111100011Tree : Option PackedTree := decode 7 0xf7897788f779f77977337732f7277726eb956b94eb87eb876b4c6b4beb3feb3f5ee66ee65ee4eee4dedc4edc3edaaeda9d698d697d67fd67ed60bd60ad5f5d5f4a75cab5ca75c3f5c3b5a635a5f59ff59fb22e322df226f226b20ab20a720572052eb4c6b4beb3feb3f6b05eb056afaeafa64156414e40ae40a63cc63cbe3c0e3c0523bc47bc43bc07bc03b997b993b967b9635ca75ca35c775c735a5f5a5b5a2b5a26f7887787f780777ff7327731f72c772beb946b93eb8e6b8deb4b6b4aeb44eb4457de03de01dde5dde3dcb3dcb1dc9bdc99ae3bae39ae1dae1bad15ad13acfdacfb7bc03bbffbbc7bbc3b963b95fb933b92f5c735c6f5c375c335a275a2359f759f2b5dccbdcc7dcb3dcafdb87db85db6ddb6bad2fad2bad15ad11ac15ac13abffabfd7b967b95fb937b92fb6dbb6d7b6a7b6a35a2b5a2359fb59f357ff57fb57d357cea3ae53ae51ae3bae39ad2fad2dad15ad13916f916d914f914d90539051903f903d75ca35c9f5c735c6f5a5b5a575a275a2322db22d7229b229720a3209f207b2076bd71dd71cd70ed70dd68ad689d67ed67dc8a7c8a6c89ac899c81fc81ec814c813bae39ae37ae1bae19ad13ad11acfbacf9914d914b91339131903d903b902790255ad697d695d68ad688d60ad609d5ffd5fec829c827c81fc81dc797c796c78cc78bbad15ad11acfdacf9abffabfdabe9abe7903f903b902990258f198f178f018eff510fbbcfbbcbbb53bb4fb93bb937b8d3b8cf5c3f5c3b5bc75bc359ff59fb599b5996f7277726f71a7719f6d576d4f6c8f6c86b3feb3f6b336b32eafaeafa6aee6aedd3ae1fae1dade3ade1acffacfdaccdaccb91379135910190ff902b902990018fff759ff59fb599b599757d757d35773576f2057205320031fff1e071e031dab1da691dde5dde3ddc7ddc5dc9bdc99dc81dc7fae1dae1bae01adffacfdacfbace3ace17bbc7bbc3bb8bbb87b933b92fb8ffb8fb5c375c335bff5bf759f759f359c359bebeee3eee1eed3eed2ee40ee3eee33ee32d700d6fed6f0d6eed671d66fd665d66300409cbb937b92fb903b8fbb6a7b6a3b677b67359fb59f359c759bf57d357cf579f579af720771f7719f71976cef6ce76c876c7eb38eb37eb32eb31eaf3eaf36aedeaed5475c3b5c375c035bff59fb59f759c759c3226b22672233222f2053204f202b2026eb86eb866b7feb7eeb3eeb3e6b386b37e44ce44c6445e4456409e4096404e40457ae01adffade1addface3ace1accbacc99119911790ff90fd901590138fff8ffd75bff5bf75bbf5bbb59c359bf5993598f222f222b21fb21f7202720231ffb1ff6b5acfdacf9ace3acdfabe9abe7abcfabcd90299025901590118f018eff8eeb8ee9759c759bf5997598f579f579b576f576b202b20231fff1ff71dd71dd31da71da2a21a

private theorem cap111011111100011Accepted : Accepted table cap111011111100011Box cap111011111100011Tree := by
  decide +kernel

private def cap11101111110001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011111100010Tree <*> cap111011111100011Tree

private theorem cap11101111110001Accepted : Accepted table cap11101111110001Box cap11101111110001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111110001Box 1 (midpoint cap11101111110001Box 1) = cap111011111100010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111100010Accepted
  · have h : rightBox cap11101111110001Box 1 (midpoint cap11101111110001Box 1) = cap111011111100011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111100011Accepted

private def cap1110111111000Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111110000Tree <*> cap11101111110001Tree

private theorem cap1110111111000Accepted : Accepted table cap1110111111000Box cap1110111111000Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111111000Box 0 (midpoint cap1110111111000Box 0) = cap11101111110000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111110000Accepted
  · have h : rightBox cap1110111111000Box 0 (midpoint cap1110111111000Box 0) = cap11101111110001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111110001Accepted

private def cap1110111111001Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (15 / 16, 1)]

private def cap1110111111001Tree : Option PackedTree := decode 6 0xf78a7789f77af77a76e376e2f6d676d5e45d645ce44ee44e63cd63cce3c1e3c15ef13ef12eef4eef3edc5edc4edabedaac8b9c8b8c89cc89bc799c798c782c781afbbd7bbd3bb5bbb57b6b3b6afb64fb64b22772273220b22071e0f1e0b1db31daef77a7779f76af76a76d5f6d576c976c8e44e644de440e44063c163c0e3b5e3b556bb71bb713b6b3b6abb2fbb2f7b2c7b2bf1e6b1e631e0f1e071ad31ac71aa31a9af6d676d5f6c9f6c97658f6587650f65063c1e3c163b663b5e3546353e34d634cdedabedaaed92ed91ecb0ecafeca0ec9fc782c781c76bc76ac6a7c6a6c699c698ad1c8bac8b9c89dc89cc79ac799c783c782b33ab339b321b320b23eb23db22cb22bb91739171913991378f338f318f058f03778577837753775175bb75b9759375916ef0aef06eea6eea2eb76eb72eb26eb22cce6cce2cc82cc7ec8f6c8f2c8aec8aa87913b9139910591038f078f058ed98ed7664366416611660f64596457642f642d72273226f220722031e0b1e071daf1daaeea6eea2ee4aee46eb26eb22ead6ead2ddd4ddd45dc95dc8dd64dd645d5add5a5990598fd983d9835915d915590b590ad0d63cd63cce3c1e3c1635a6359e3546353d91f591ed9165915d8c1d8c158bc58bbdc799c798c782c781c6b3c6b1c6a7c6a6b23db23cb22bb22ab182b181b177b176af1e0f1e0b1db31daf1aa31a9f1a6b1a66c8b2c8aec85ec85ac5e2c5dec5b6c5b2e3c163c0e3b5e3b56353e353634ce34c5915d915590b590ad8bbd8bb58b658b5d688

private theorem cap1110111111001Accepted : Accepted table cap1110111111001Box cap1110111111001Tree := by
  decide +kernel

private def cap111011111100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111111000Tree <*> cap1110111111001Tree

private theorem cap111011111100Accepted : Accepted table cap111011111100Box cap111011111100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011111100Box 3 (midpoint cap111011111100Box 3) = cap1110111111000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111000Accepted
  · have h : rightBox cap111011111100Box 3 (midpoint cap111011111100Box 3) = cap1110111111001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111001Accepted

private def cap111011111101Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (7 / 8, 1)]

private def cap1110111111010Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (7 / 8, 15 / 16)]

private def cap11101111110100Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (7 / 8, 15 / 16)]

private def cap11101111110100Tree : Option PackedTree := decode 7 0xe474e47464696468e3d963d8e3d4e3d459b159b0d9a8d9a859295928d924d92400084ec8e8c8e7c8d1c8cfc84bc84ac83dc83cbbefbbeebbdabbd8bb6bbb6abb60bb5fb90979095907b90798f638f618f518f4f76d776d576c176bf75df75dd75d175cf4ddf7ddf75ded5dec5db5ddb55db05dafd9b0d9b059a7d9a6d96c596bd967d9675bb6bbb6abb60bb5fbaefbaeebae8bae7b2d8b2d7b2cfb2ceb251b250b248b247a43c8d2c8d1c8b8c8b7c7a9c7a8c798c797bbdbbbdabbc1bbc0bae9bae8badcbadb00109d77b777b57783777f76c376c1769d769b66a3669f6671666f65a1659f658365816ed86ed82ed3aed36eba6eba2eb72eb6ecb42cb3ecb06cb02c926c922c8f2c8ee9191a3919f918b9187907b90799067906577b577b1779b779776c176bf76af76ad72317230f22df22d720cf20cb20a7209eef36ef2eeefeeef6ed5eed5aed36ed2eac83dc83cc829c827c7a8c7a7c797c796bb60bb5fbb4dbb4bbae8bae7badbbadaa6ef6aef62ef36ef2eed82ed7eed5eed5acd3ecd36cd0ecd06cb3ecb3acb26cb22dde6dde5dddfdddeddabddab5da6dda5d9a1d9a0d99bd99ad964d9645960595f5576c176bf769b769775d175cf75b775b5659f659d6581657d6491648f64776475486b1ecb1ec71ea71ea31b131b0f1af31aeec94ac946c926c922c64ec64ac62ec62ae3d8e3d863d463d3e361e361635de35d5928d92859245923d8c958c8d8c558c4d78f538f518f318f2f8d798d778d638d616493649164796477631763156303630171ea31e9f1e5f1e5b1aef1aeb1ac31abeeba2eb9eeb6eeb6ae92ee92ae916e912dd745d73dd6ddd6d5d25dd255d22dd2259245923d91dd91d58c558c4d8c058bfd0d1

private theorem cap11101111110100Accepted : Accepted table cap11101111110100Box cap11101111110100Tree := by
  decide +kernel

private def cap11101111110101Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (7 / 8, 15 / 16)]

private def cap11101111110101Tree : Option PackedTree := decode 7 0x3de91de8fde61de5fdbcbdbc9dbb3dbb191d391d191a591a38f658f638f538f517bd1fbd1bbcbfbcb7ba37ba33b9efb9eb5d6b5d675d135d0b5aff5afb5ab75ab2f746f746773df73d76f276f1f6ec76ebeb5feb5f6b56eb566b13eb136b0eeb0e53aeb5aeb3ae89ae85ad7fad7dad5bad5991d191cf91a3919f90979095907b907975aff5afb5ab75ab3589f589b58775873212f212b20f720f31ec71ec31ea31e9e90fbcc3bcbfbc4bbc47b767b763b713b70f5d175d135cab5ca7587b5877582f582aeba2eba26b956b94eb0f6b0eeb05eb0564696468e45c645be3d4e3d463cc63cbd1de5fde5bde47de43dcf7dcf5dce1dcdfae89ae85ae6fae6bad5bad59ad45ad437bc8fbc87bc47bc3fb9c3b9bfb997b98f5cdf5cd75ca75c9f5a8b5a875a5f5a56aee7bee7aee65ee63edd8edd7edc3edc2d6add6acd697d695d61dd61cd60ad609a75d135d0b5cdf5cd75ab75ab35a8b5a872347233f2317230f20f720f320cf20caeb9beb9aeb94eb93eb516b50eb4beb4ae462e461e45be45ae419e4196414e413d5ad5bad59ad2fad2bac3bac39ac15ac13907b90799053904f8f518f4f8f2f8f2d486bb797b793b767b763b33bb337b31bb3171ecb1ec71ea71ea31b131b0f1af31aeef6f276f1f6ec76ebf666f6667662f66263d8e3d863d463d3e361e361635de35d57dbb3dbb1db89db87d98dd98bd97bd9798f538f518f318f2f8d798d778d638d617b763b75fb70fb70bb317b313b2f3b2ef58775873582b5827551f551b550354feeb0eeb0e6b056b04eaa3eaa36aa06a9fe3d463d3e3cbe3cb635de35d63586357d0d1

private theorem cap11101111110101Accepted : Accepted table cap11101111110101Box cap11101111110101Tree := by
  decide +kernel

private def cap1110111111010Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111110100Tree <*> cap11101111110101Tree

private theorem cap1110111111010Accepted : Accepted table cap1110111111010Box cap1110111111010Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111111010Box 0 (midpoint cap1110111111010Box 0) = cap11101111110100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111110100Accepted
  · have h : rightBox cap1110111111010Box 0 (midpoint cap1110111111010Box 0) = cap11101111110101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111110101Accepted

private def cap1110111111011Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (15 / 16, 1)]

private def cap1110111111011Tree : Option PackedTree := decode 5 0xf7a577a47799779876f376f2f6edf6ece475e474e46a646963da63d963d5e3d4def32ef31ef14ef13eddbeddaedc6edc5c8d4c8d3c8bac8b9c7abc7aac79ac799bde63de61de27de25dbb5dbb3db8bdb8991a791a5917391718f558f538f338f315aede6ede5eddbedd9eccfecceecc7ecc6c7b4c7b2c7abc7a9c6c5c6c4c6bdc6bcbdbb7dbb3db8ddb89d98fd98dd97dd97b8f578f538f358f318d7b8d798d698d6351c8ebc8eac8d4c8d3c7b4c7b3c7abc7aab364b363b353b352b254b253b24bb24ab91d591d391a791a58f678f658f558f5366c766c566a566a364a764a5649564935e46a6469e45d645ce3d5e3d563cd63ccd9a9d9a9599d599cd925d925591f591edc8d3c8d2c8b9c8b8c7aac7a9c799c798b352b351b339b338b24ab249b23db23cad63da63d963d5e3d4e362e362635ee35e592a59295925d924d8ca58c9d8c658c5dc7abc7a9c79ac798c6bdc6bcc6b4c6b1b24bb249b23eb23cb18cb18bb183b181a88

private theorem cap1110111111011Accepted : Accepted table cap1110111111011Box cap1110111111011Tree := by
  decide +kernel

private def cap111011111101Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111111010Tree <*> cap1110111111011Tree

private theorem cap111011111101Accepted : Accepted table cap111011111101Box cap111011111101Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011111101Box 3 (midpoint cap111011111101Box 3) = cap1110111111010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111010Accepted
  · have h : rightBox cap111011111101Box 3 (midpoint cap111011111101Box 3) = cap1110111111011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111011Accepted

def cap11101111110Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111011111100Tree <*> cap111011111101Tree

theorem cap11101111110Accepted : Accepted table cap11101111110Box cap11101111110Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11101111110Box 2 (midpoint cap11101111110Box 2) = cap111011111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111100Accepted
  · have h : rightBox cap11101111110Box 2 (midpoint cap11101111110Box 2) = cap111011111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover44
