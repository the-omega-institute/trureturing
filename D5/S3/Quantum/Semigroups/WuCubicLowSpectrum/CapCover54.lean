import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover54

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap111111100110110Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (13 / 16, 7 / 8)]

private def cap1111111001101100Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (3 / 4, 25 / 32), (13 / 16, 7 / 8)]

private def cap11111110011011000Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (3 / 4, 25 / 32), (13 / 16, 27 / 32)]

private def cap11111110011011000Tree : Option PackedTree := decode 7 0x3e39be399e389e387e0d3e0d1e0c3e0c1c393c391c383c381c18bc189c17fc17d787278723870787038317831382ff82fb66276623660365ff614f614b612f612a8f1ccf1cbf1c3f1c2f068f067f060f05fe1c8e1c7e1c0e1bfe0c4e0c3e0bee0bdbc391c38fc381c37fc189c187c17dc17bb311b30fb2ffb2fdb0a5b0a3b095b09343f1c4f1c3f1aef1acf0e5f0e4f0dff0dee1c1e1c0e1afe1ade12ee12de128e127be1cbe1c9e1bfe1bde0c3e0c1e0abe0a9c25dc25bc251c24fc17fc17dc171c16f4f0e0f0e070d7f0d6f0977096f0947093ecc06cbfecb86cb6ec5cec5c6c5a6c59de12ee12de128e127e0bfe0bee0b8e0b7d8b9d8b8d8b4d8b3d84bd84ad840d83fa478e1f8e178d678d578727871f86f786ef0e070dff0d6f0d5f096f0967093f093080016f0e4f0e3f0def0ddf060f05ff054f053e12de12ce127e126e0bee0bde0b7e0b6a7870386ff86b786af84b784b3849f849b65ff65fb65b765af62e362df62cf62caf096f0967093f093705f705ef05bf05b6c5c6c5bec59ec596c256c24ec1fec1f521af069f067f061f05fef55ef54ef50ef4ed853d851d84bd849d766d765d761d75fbe0c3e0c1e0abe0a9dea1de9fde89de87b097b095b081b07faec3aec1aeafaead7c183c17fc153c14fbd3fbd3bbd0fbd07612b612760ff60fb5d835d7f5d5b5d56b4766276623660365ff614f614b612f612b2bb32baf2b8f2b8b2753274f2733272eecc46cc3ecbfecbf6c296c28ec256c24e575e57565716570e4e9e4e964e5e4e557b301b2ffb2e1b2ddb097b095b081b07fa115a113a0ffa0fb9f8d9f8b9f819f7e20007b422b422741ff41f73f1b3f173f033eff2b8f2b8b2b572b532733272f270727028d97fd97ed96ed96bd84ad849d83fd83ed089d088d07dd07bcfc5cfc4cfbfcfbe20003da113a111a0fba0f79f8b9f899f7f9f7d95c595c395a995a7939793959381937f435b0a7b0a3b097b093aecdaecbaec3aebf93a993a59399939591eb91e991e191dd7612f612b610360ff5d875d835d5f5d5b2733272f2707270323c323bf23972392ec256c24ec1fec1f6bb06bafebab6baae4e5e4e564e064dfe477e47764726471d688

private theorem cap11111110011011000Accepted : Accepted table cap11111110011011000Box cap11111110011011000Tree := by
  decide +kernel

private def cap11111110011011001Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (3 / 4, 25 / 32), (27 / 32, 7 / 8)]

private def cap11111110011011001Tree : Option PackedTree := decode 6 0x3e39fe39de38de38be0d7e0d5e0c7e0c5b317b315b305b303b0abb0a9b09bb0997c73bc737c717c713c1abc1a7c18bc187662b6627660766036153614f6133612ebf1c6f1c5f1b1f1b0f063f062f058f057d982d981d972d971d84dd84cd842d841be38be389e361e35de0c5e0c3e0afe0abc385c383c363c35fc181c17fc173c1717870b870786c786bf830382ff82e782e36607660365c765c36133612f6107610286bc1afc1a7c18fc187bd5bbd57bd47bd436157614f6137612f5d9f5d9b5d8b5d86f831f830f82c782b77a8f7a877a377a26c26ec25ec216c206bb16bb0ebacebab88001e47662f662b660b660761576153613761332bbb2bb72b972b93275b2757273b2736ecc56cc4ecc0ecc06c2a6c29ec266c25e576e57665726571e4eae4ea64e6e4e657b305b303b2e5b2e3b09bb099b085b08395cb95c995b195af939d939b9387938576607660365c765c36133612f61076103422f422b420341ff3f1f3f1b3f073f02e845e8456840683fe7e3e7e367e0e7e065726571e56be56ae4e6e4e664e164e0d0d6c2aec29ec26ec25ebb3ebb36bb16bb0e4eb64ea64e764e6647b647ae478e4785d84dd84bd842d840d762d761d759d757c9cec9ccc9c3c9c1c8f1c8f0c8e7c8e5a88

private theorem cap11111110011011001Accepted : Accepted table cap11111110011011001Box cap11111110011011001Tree := by
  decide +kernel

private def cap1111111001101100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11111110011011000Tree <*> cap11111110011011001Tree

private theorem cap1111111001101100Accepted : Accepted table cap1111111001101100Box cap1111111001101100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1111111001101100Box 3 (midpoint cap1111111001101100Box 3) = cap11111110011011000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011011000Accepted
  · have h : rightBox cap1111111001101100Box 3 (midpoint cap1111111001101100Box 3) = cap11111110011011001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110011011001Accepted

private def cap1111111001101101Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (25 / 32, 13 / 16), (13 / 16, 7 / 8)]

private def cap1111111001101101Tree : Option PackedTree := decode 6 0xf8f078ef78ed78ec783af83a7838f8386ccdeccceccaecc9ec2fec2f6c2dec2d5f1daf1d8f1cff1cdf071f070f06bf069d995d993d98bd989d85bd85ad855d853abc1d7c1d3c1afc1a7bd77bd73bd5bbd57617f617b6157614f5db35daf5d9f5d9a9d99bd999d995d993d85fd85ed85bd85acafecafdcaf9caf7c9dec9ddc9dac9d9bb32bb327b317b313b0b7b0b5b0abb0a795f395ef95dd95d993b593b393ad93a956c2fec2f6c2aec29ebb66bb5ebb3ebb364ef64eee4eb64ea647ee47e647b647ad23c77bc773c763c75bc1d3c1cbc1c3c1bb6667665f664f6647617b6173616b6162f8ec78ebf8e6f8e678387837f834f8346cc9ecc96cc4ecc46c2d6c2cec29ec295f1d7f1d6f1ccf1cbf06ff06ef068f067d992d991d988d987d859d858d852d851ad783a78397834f833f7ae77adf7aaf7aa6c2f6c2e6c29ec28ebb5ebb56bb36bb2d3b333b32fb327b323b0bdb0b9b0b5b0b195fb95f795ef95eb93bb93b793b393b17664f66476627661f616b6163614f61472bdf2bd72bb32bab276727632753274aad85ed85cd853d851d76bd76ad766d765c9ddc9dbc9d4c9d2c8fcc8fbc8f5c8f4a43

private theorem cap1111111001101101Accepted : Accepted table cap1111111001101101Box cap1111111001101101Tree := by
  decide +kernel

def cap111111100110110Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1111111001101100Tree <*> cap1111111001101101Tree

theorem cap111111100110110Accepted : Accepted table cap111111100110110Box cap111111100110110Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111111100110110Box 2 (midpoint cap111111100110110Box 2) = cap1111111001101100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001101100Accepted
  · have h : rightBox cap111111100110110Box 2 (midpoint cap111111100110110Box 2) = cap1111111001101101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111001101101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover54
