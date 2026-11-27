import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover59

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap111111100111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (3 / 4, 7 / 8)]

private def cap1111111001110Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (3 / 4, 13 / 16)]

private def cap1111111001110Tree : Option PackedTree := decode 12 0xc93db03dad3daffdacfd3dfd3b7d3dbd3b39797976f9793976b91cf91a791cb91a2af4f8f4eef4f6f4ecf3b5f3aef3b4f3ade474e46ae472e468e34de348e34ce347a7979b97739793976b91d391ab91cb91a3765b763b7657763370c370ab70bf70a2f23a72357239723471a6f1a471a671a3ee186e156e17ee146d9f6d9bed9eed9b522353ced7cebbced3ceb7c777c75fc773c75b6cfb6cdf6cf76cdb6663664b665f6646c68cdd96dd8edd95dd8cdc30dc2adc2fdc28d373d36ed372d36dd282d27dd281d27cbb861b855b85fb851b67db66fb67bb66da505a4fba503a4f9a37fa375a37da3734e9b9e9b769b969b6e8dfe8dd68df68dce7166712e715e7126639e63666396635d11a9b67db66fb67bb66db331b325b32fb32398e798d998e598d795f995ed95f795eb634446a4f1ddf1d7f1dcf1d6f073f06ff072f06ed998d992d997d991d85dd859d85cd858b1af074f069f072f067ef5cef55ef5bef54d85ed853d85cd851d76bd766d76ad765a66ccc6cc46ccbecc3ec2eec296c2e6c28e57e6575e57de57564ee64e9e4ede4e955b0bdb0a7b0b9b0a3aed7aecdaed5aecb93bb93a993b793a591f991eb91f791e9488d19338b3389738af389331cf31b331cb31af0f3f0f2b0f3b0f2709fb09e709f709e2e1e7e1e561e761e4e13f613ce13ee13c600c6008e00be0085f59df565f595f55d11a998e798d998e598d795f995ed95f795eb7d677d597d657d577b057af97b037af76346600c6008e00be0085f59df565f595f55db99db965b995b95dafcdaf95afc5af8d8d4beb3beacbeb2beabbd82bd7cbd81bd7bb5f9b5f2b5f8b5f1b4edb4e7b4ecb4e6b1a22352657e6575e57de57564ee64e9e4ede4e95ec15eb95ec0deb8de555e515e54de50d593bb93a993b793a591f991eb91f791e9795779477953794377fd77f377fb77f14dec1deb9dec0deb8de55de51de54de50da775a6f5a765a6e5a125a105a11da0fdbcabbca3bca9bca1bbfebbf9bbfdbbf8b424b420b423b41fb36eb367b36db366a44688

private theorem cap1111111001110Accepted : Accepted table cap1111111001110Box cap1111111001110Tree := by
  decide +kernel

private def cap1111111001111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (13 / 16, 7 / 8)]

private def cap11111110011110Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (13 / 16, 7 / 8)]

private def cap11111110011110Tree : Option PackedTree := decode 8 0xe71fe71d671d671c65856582e582e5826013e012601260115ec5dec45ec45ec3dc027c024c024c022bd8bbd88bd88bd87b744b73fb73fb73db4fab4f5b4f5b4f4a2671ce71b671c671ae63f663de63ee63d6011e0106011600fdf5f5f5ddf5edf5d58d663fe63b663ee63a6582e57f6582657edf5fdf5b5f5edf5a5ec45ec25ec3dec1d33008f006b008b0066fafafad6faf6fad2dcfadcd6dcf6dcd2d80ad7eed806d7eaabebfbeb6bebdbeb4bd88bd84bd87bd83b603b5fcb601b5fab4f5b4efb4f4b4eea43ce3ace38ce37ce35cc7fcc7dcc7ccc7ac024c022c021c01fbebfbebdbebcbebab9c6f9c6d9c5f9c5d98f998f798ed98eb80438041803780357d797d777d6d7d6b738db38d738bb38b731ef31eb31d731d30083007f006b0066faeefaeafad6fad2b598ff98fb98ed98e9960b960995fd95fb7d7f7d7b7d6d7d697b117b0f7b097b074e01260116010e00fdf5fdf5edf5e5f5d5b9fdb9edb9e5b9ddb01db00db005affdc021c01fc01bc019bebcbebabeb6beb4b73cb73bb736b734b600b5ffb5fcb5faaafafefaf6fadafad2f622f61ef612f60ed80ed806d7f2d7ead3d6d3d2d3bed3ba919c719c6b9c6b9c6998fb98f598f598f38045803f803f803d7d7b7d757d757d73738d738b738d338b331eb31d331e731cf007f0067007b0062faeafad2fae6facebce35ce34ce2dce2ccc7acc79cc74cc73c01fc01ec019c018bebabeb9beb4beb3b9c699c599c599c5798f398e798e798e5803d80318031802f7d737d677d677d655acc7dcc74cc74cc72cb04cafdcafdcafbbebdbeb4beb4beb2bd87bd83bd83bd81a7008b0067007f0062faf6fad2faeafacedcf6dcd2dceedcced806d7ead7fed7e6e00fe00c600ce00bdf5d5f59df5a5f595b9ddb99db9a5b995affdafcdafd5afc557d7b7d697d697d657b0f7b077b077b036c036bf56bf56bf169e969dd69dd69d9486b2c2b2c172c172c132417240b240b2406d3ead3d6d3d6d3d2cddecdd2cdd2cdcee582e57f6582657ee481647ee480e47e5a7ada77da7a5a7759ba59b7d9b9d9b757960b960995fd95fb9205920391fb91f969eb69e969df69dd66e966e766df66dd72c132bf72bf72bef240723f323f323eef61ef60ef60ef606f006effaeffaeff6dec3dec1dec1dec0de00ddff5dff5dfeda7a5a775a775a7659b9d9b759b759b6d0d1

private theorem cap11111110011110Accepted : Accepted table cap11111110011110Box cap11111110011110Tree := by
  decide +kernel

private def cap11111110011111Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (13 / 16, 7 / 8)]

private def cap111111100111110Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (13 / 16, 7 / 8), (13 / 16, 7 / 8)]

private def cap111111100111110Tree : Option PackedTree := decode 5 0x3e3d7e3cfe3cfe3cddecbdec5dec5dec39615960b960b9609920b9205920592037c79fc783c79bc77bbd8bbd77bd87bd736683666f667f66675dbf5db35dbb5daeecd06ccdeccfecccebb7ebb66bb76bb5e582e57f6582657ee481647ee480e47e50fc79fc79bc783c77bbd8bbd87bd77bd736683667f666f66675dbf5dbb5db35daeecd06ccfeccdecccebb7ebb76bb66bb5e582e582657f657ee4816480e47ee47e51e3cde3bde3bde3b9e0ede0e9e0e9e0e5b33fb333b333b32fb0c1b0bdb0bdb0b97c1dbc1d3c1d3c1cbbd87bd73bd73bd6f6183617b617b61735dbb5daf5daf5daa9d99fd999d999d997d76ed76bd76bd76acb04cafdcafdcafbc901c8fcc8fcc8fba1a

private theorem cap111111100111110Accepted : Accepted table cap111111100111110Box cap111111100111110Tree := by
  decide +kernel

private def cap111111100111111Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (13 / 16, 7 / 8), (13 / 16, 7 / 8)]

private def cap111111100111111Tree : Option PackedTree := decode 8 0x3eda7ed9fed9fed9be787e783e783e77fbb4bbb45bb45bb41b699b695b695b6917cf0fcf07cf07ceffc7afc79fc79fc79b6d336d2b6d2b6d23668f66836683667e9dda5dda2dda2dda0d9a3d9a0d9a0d99fce3fce3ace3ace38cb0acb05cb05cb04a27b677b65fb66fb6579e079def9dff9de6ed0eecf6ed06eceeda4eda36da46da2d8d79e0f9dc79dff9db78f3f8f078f378ef6da56da0eda46d9fecd06ccdeccfecccd337687767b768376776d276d1b6d236d1738e738db38e338d731fb31ef31f731eac6b6d2b6d076d236cff6683666f667f666731ff31db31f731d32c172bfb2c132bf690fdb3fdb37db33db2bcf07ceffcefbcef3768b7683767f76776d2b6d236d1f6d16fb667b65fb627b61f9df79def9dc79dbeecfeecf6ecceecc6da3eda36da0eda05f6cbf6caf6c3f6c2f3bdf3bcf3b7f3b6dd9edd9ddd98dd97db46db45db40db3fad79e0f9dff9dc79db78f3f8f378f078ef6da56da46da0ed9fecd06ccfeccdecccd3bb45bb41bb3fbb3bb695b691b68fb68b9c759c719c6f9c6b98ff98fb98f998f57767f767b766776636d1f6d1b6d076d0338df38db38bf38bb31f331ef31db31d6eecf6eceeecc6ecbeda36da2eda06d9fe71b671ae7176716e63de63d663ae63a56b6d2b6d236d076cff6683667f666f666731ff31f731db31d32c172c132bfb2bf691ed9bed95ed95ed93e77fe779e779e777bb41bb3bbb3bbb39b691b68bb68bb6897db2bdb0bdb27db07cef3cedbceefced797ab979f97a7979b8d478d3b8d438d36f2f572f3f2f4f2f371a8f1a771a871a6eeceeecbeece6ecb6da2ed9feda26d9f50fdb2bdb27db0bdb07cef3ceefcedbced797ab97a7979f979b8d478d438d3b8d36f2f572f4f2f3f2f371a8f1a871a771a6eeceeece6ecbeecb6da2eda26d9fed9f51ed93ed83ed83ed7fe777e76be76be769cbd3cbcdcbcdcbc9c6a1c69bc69bc699797a7979b979b97938d438d378d378d337673765b765b76576d136cfb6cfb6cf686bceffcedbcef3ced7c79bc77bc797c7776d236cff6d176cfb667f6667667b6662f9de79daf9db79da78f2f8eef8ef78ee6da2ed9f6d9fed9eeccf6ccc6ccceccbd4776837677767776736d236d176d176d1338e338d738d738d331f731eb31eb31e6eeceeecbeece6ecb6da2ed9feda26d9f671ae716e71a6716663d663a663ce639d7bb3bbb39bb2fbb2db68bb689b67fb67d9c6b9c699c5b9c5998f598f398e998e777673765b765b76576d136cfb6cfb6cf738d338b338b338af31e731cf31cf31cab5b691b67fb68bb67db33fb333b33db33198fb98e998f598e7960995fb960795f976d176cfb6cff6cf7667b66636667665f31eb31cf31d331cb2c0f2bf32bf72beea21a

private theorem cap111111100111111Accepted : Accepted table cap111111100111111Box cap111111100111111Tree := by
  decide +kernel

private def cap11111110011111Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111100111110Tree <*> cap111111100111111Tree

private theorem cap11111110011111Accepted : Accepted table cap11111110011111Box cap11111110011111Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110011111Box 1 (midpoint cap11111110011111Box 1) = cap111111100111110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100111110Accepted
  · have h : rightBox cap11111110011111Box 1 (midpoint cap11111110011111Box 1) = cap111111100111111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111100111111Accepted

private def cap1111111001111Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11111110011110Tree <*> cap11111110011111Tree

private theorem cap1111111001111Accepted : Accepted table cap1111111001111Box cap1111111001111Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1111111001111Box 0 (midpoint cap1111111001111Box 0) = cap11111110011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011110Accepted
  · have h : rightBox cap1111111001111Box 0 (midpoint cap1111111001111Box 0) = cap11111110011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011111Accepted

def cap111111100111Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1111111001110Tree <*> cap1111111001111Tree

theorem cap111111100111Accepted : Accepted table cap111111100111Box cap111111100111Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111111100111Box 3 (midpoint cap111111100111Box 3) = cap1111111001110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001110Accepted
  · have h : rightBox cap111111100111Box 3 (midpoint cap111111100111Box 3) = cap1111111001111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001111Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover59
