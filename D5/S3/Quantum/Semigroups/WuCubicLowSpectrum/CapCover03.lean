import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover03

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap01110Box : Box := ![(1, 6 / 5), (63 / 200, 63 / 100), (1 / 4, 1 / 2), (1 / 2, 3 / 4)]

private def cap011100Box : Box := ![(1, 11 / 10), (63 / 200, 63 / 100), (1 / 4, 1 / 2), (1 / 2, 3 / 4)]

private def cap0111000Box : Box := ![(1, 11 / 10), (63 / 200, 189 / 400), (1 / 4, 1 / 2), (1 / 2, 3 / 4)]

private def cap01110000Box : Box := ![(1, 11 / 10), (63 / 200, 189 / 400), (1 / 4, 3 / 8), (1 / 2, 3 / 4)]

private def cap01110000Tree : Option PackedTree := decode 6 0xc9714971396a296a196ac96ab969a96998934893388d988d888e388e288d188d0b2e272e252d432d412d572d552d332d311267126511b111af11c511c311a1119f5c46449a4499c46cc46c4471c4714468c46840954094c072c0724077c077406f406ed8933893288d888d788e288e188d088cf8129812880e480e380ee80ed80dd80dcae2224b894b884b504b4fcb554b544b4c4b4bc4994498446bc46b4470c46fc467c467588c8932893088cb88ca88e188df88c188c08128812680d980d880ed80eb80d080cfa43

private theorem cap01110000Accepted : Accepted table cap01110000Box cap01110000Tree := by
  decide +kernel

private def cap01110001Box : Box := ![(1, 11 / 10), (63 / 200, 189 / 400), (3 / 8, 1 / 2), (1 / 2, 3 / 4)]

private def cap01110001Tree : Option PackedTree := decode 7 0x3300930072fcb2fc92e7d2e7b2e632e611e9f1e9d1e6d1e6b1d7d1d7b1d691d6763d3e3d3a3cda3cd63afa3af63ad23ace2776277227162712256a2566253a253689803980297e497e3973d973c9730972f89dc89db89c489c389598958894d894cae5f965f925c965c925cc65cc25c525c4e3cda3cd63aba3ab63ad23ace3a8e3a8ac79b479ac7574756c75a4759c751c75144e2c4e244a144a0c4a744a6c49a4499d12fc92fc72e492e472e612e5f2e272e251389138712831281129b1299126712655a973e973d9731973096be96bd96b596b48ebe8ebd8eb48eb38e758e748e6f8e6eb1d7d1d7b1d691d671ceb1ce91cdf1cdd12b512b3129d129b11e911e711d711d544b9ecb9e4b984b97cb5ecb5e4b5a4b59c4acc4ac44a6c4a64479c47944754474d72e632e612e292e272d6b2d692d592d571d691d671d471d451cdf1cdd1cd31cd163ad23ace3a8e3a8a39be39ba39a639a2253a253624d224ce23ae23aa238e238a89730972f9713971296b496b396ab96aa894d894c8933893288ea88e988e288e1ad189dd89dc89c589c4895a8959894e894d81ae81ad81978196814c814b81438142b13b913b71389138712b312b1129b1299035b0359032d032b02970295028502835c4e2c4e244a144a0c4a744a6c49a4499c0cbc0cb409bc09b40a1c0a140954094d89c489c389418940894d894c8933893281968195813681358142814181298128ad44ad44acc4a744a6c47a4479c475c47540a640a5c0a1c0a14080407fc07bc07b589598958894d894c88f388f288ea88e9814b814a8142814180ff80fe80f680f5ae253a253624d224ce23ae23aa238e238a050e050a04aa04a603de03da03be03bac4a6c4a64499c49944754474c4714470c0a140a0c094c094407b407ac0774076d6889802980097e397e1973c973a972f972d89db89d989c389c189588956894c894bb2fc72fc32e472e432e5f2e5b2e252e21138713831281127d129912971265126154b9e4b9d4b97cb96cb5e4b5d4b59cb58c4ac44ab44a644a5c47944784474c4745972f972d9712971096b396b196aa96a8894c894b8932893088e988e888e188dfa8c4edc4ecc4e1c4e0c4ac44ab44a644a5c0d640d540cac0ca40a540a440a0c0a0589c389c18940893e894c894b8932893081958194813581338141814081288126aa2562255a2532252e23ca23c223a623a2052a05220506050203fa03f203d603d2c4a644a5c49944984474c4744470c46fc0a0c0a040944093407ac07a4076c075d443

private theorem cap01110001Accepted : Accepted table cap01110001Box cap01110001Tree := by
  decide +kernel

private def cap0111000Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap01110000Tree <*> cap01110001Tree

private theorem cap0111000Accepted : Accepted table cap0111000Box cap0111000Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap0111000Box 2 (midpoint cap0111000Box 2) = cap01110000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap01110000Accepted
  · have h : rightBox cap0111000Box 2 (midpoint cap0111000Box 2) = cap01110001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap01110001Accepted

private def cap0111001Box : Box := ![(1, 11 / 10), (189 / 400, 63 / 100), (1 / 4, 1 / 2), (1 / 2, 3 / 4)]

private def cap0111001Tree : Option PackedTree := decode 9 0xc930d330d12fdb2fd9300930072fcb2fc91f4f1f4d1e791e771e9f1e9d1e6d1e6b4c7d947d8c79fc79f47a7c7a7479b479ac51f451ec4e844e7c4eec4ee44e2c4e25130e930e72fe12fdf300730052fc92fc7147b1479139f139d13b913b7138913875c46451f451ec4e844e7c4eec4ee44e2c4e242814280c255c255425ac25a4251c25158502850184ab84aa84b584b484a384a281f781f681a181a081ae81ad81978196a228f628f2273e273a2772276e2712270e07da07d60682067e06b606b2065a0656b888930e730e52fdf2fdd300530032fc72fc514791477139d139b13b713b513871385661ca619a5fba5faa600660025f8a5f8628ee28c62736272a276a2766270a2706b88c8a3c8a3189ce89ca89db89d989c389c181f581eb819f819c81ac81aa81958194b110e2

private theorem cap0111001Accepted : Accepted table cap0111001Box cap0111001Tree := by
  decide +kernel

private def cap011100Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap0111000Tree <*> cap0111001Tree

private theorem cap011100Accepted : Accepted table cap011100Box cap011100Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap011100Box 1 (midpoint cap011100Box 1) = cap0111000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0111000Accepted
  · have h : rightBox cap011100Box 1 (midpoint cap011100Box 1) = cap0111001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0111001Accepted

private def cap011101Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 63 / 100), (1 / 4, 1 / 2), (1 / 2, 3 / 4)]

private def cap0111010Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (1 / 4, 1 / 2), (1 / 2, 3 / 4)]

private def cap01110100Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (1 / 4, 3 / 8), (1 / 2, 3 / 4)]

private def cap01110100Tree : Option PackedTree := decode 7 0x33ac67ac63a9dfa9dbaa0baa07a9afa9ab14a3149f125f125b12771273123b1236e2946293e24be24b624ee24e62476246d8145813d7cd57ccd7d257d1d7c757c6d1d631d62fd4edd4ebd503d4ffd4d5d4d38a4f8a4d892d892b89398937891b89197149f149b125b12571273126f12371232c09ec09abe66be62be8ebe8abe36be32871196051604f5f355f335f495f475f1d5f1b420542034147414541534151413b41396840a8406828e828a82a682a2827682725c525c4e5a8a5a865ab25aae5a6a5a668b027b026af99af98afa3afa2af8daf8c9713971296a196a096ab96aa96999698ae222758bf58b753af53a753ff53f7534f53458135812d7cc57cbd7d157d0d7c657c5deb16eb15ea74ea73ea7eea7dea68ea67b025b024af97af96afa1afa0af8baf8aae232c09ac092be62be5abe8abe82be32be2a5c4a5c425a825a7e5aaa5aa25a625a5ec443

private theorem cap01110100Accepted : Accepted table cap01110100Box cap01110100Tree := by
  decide +kernel

private def cap01110101Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 8, 1 / 2), (1 / 2, 3 / 4)]

private def cap011101010Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 8, 1 / 2), (1 / 2, 5 / 8)]

private def cap011101010Tree : Option PackedTree := decode 6 0x3d8bbd8b9d841d83fd689d687d667d6658cb18caf8c478c458a9b8a998a7b8a7971963195f188f188b1537153314f714f2c4d2c4cec446c442c146c142c102c0fe8ec5cec5bec1fec1eeb43eb42eb32eb31b133b132b110b10fb050b04fb03fb03eafb083b07faca7aca3accfaccbac5fac5ac446c442c0dec0dac102c0fec09ac096f60ff60f75947593f5997598f58b758ad8885887d81b581ad81fd81f5812d81256bad13ad0faccfaccbaa5baa57aa27aa231537153314f714f312bf12bb128f128ae2a6e2a6629ee29e6257e2576251e2515828d8285820581fd7dbd7db57d5d7d551d687d685d665d663d52bd529d511d50f60a1609f607f607d5f6d5f6b5f555f535f599f599758bf58b7544f544753ff53f5820581fd8135812d7d5d7d557d157d0deb32eb31eb16eb15ea88ea87ea7eea7db03fb03eb025b024afaaafa9afa1afa0ad1b134b133b111b110b051b050b040b03f9802980197e397e2973c973b972f972eb626762656221621f60a1609f607f607d300330012fc52fc32e772e752e5d2e5b5d888d888581bd81b5820581fd8135812cbf1cbf14b91cb914b97cb974b894b88db110b10fb036b035b03fb03eb025b02497e297e197229721972e972d97119710ad5828d8285820581fd7dbd7db57d5d7d54b9e4b9dcb97cb974b5e4b5dcb59cb595b050b04fb03fb03eafb6afb5afaaafa9973b973a972e972d96bb96ba96b296b1aec102c0fec09ac096beaebeaabe8abe865cbe5cba5c4a5c465ace5aca5aaa5aa6d81fd81f5812d81257d557d4d7d0d7d04b974b96cb88cb884b594b58cb54cb545688

private theorem cap011101010Accepted : Accepted table cap011101010Box cap011101010Tree := by
  decide +kernel

private def cap011101011Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (3 / 8, 1 / 2), (5 / 8, 3 / 4)]

private def cap0111010110Box : Box := ![(11 / 10, 23 / 20), (63 / 200, 189 / 400), (3 / 8, 1 / 2), (5 / 8, 3 / 4)]

private def cap0111010110Tree : Option PackedTree := decode 6 0x3626d626b62276225617561736155615343e343e143a943a742f942f742dd42db6c2eac2e6c2aac2a6c14ec14ac10ac10685f285ee85ba85b6848a84868452844e9a1f1a1f0a1d4a1d3a17ca17ba16ea16d9804980397e597e49794979397879786b42f942f742dd42db42454243422942272f292f272f0f2f0d2e7d2e7b2e632e6148b135b134b112b111b052b051b041b040a1f0a1efa1d3a1d2a121a120a113a112b43e143df43a743a54243424142274225300730052fc92fc72e7b2e792e612e5f43b113b112b039b038b0aab0a9b02eb02da1d4a1d3a10fa10ea16ea16da108a107b61556153605d605b608560836051604f42dd42db4211420f42294227420542034d0ea50e9d087d08750b750b6d0845083cbf2cbf24b92cb924bc3cbc34b8d4b8cda16ea16da108a107a114a113a102a10197879786971a97199731973097149713a458895888d81c581bd820d8205813d81350e9d0e950875086d089d0895080d0805a1d3a1d2a10ea10da113a112a101a10097e497e3972497239730972f97139712a1ab053b052b042b041aff9aff8afebafeaa122a121a114a113a0e3a0e2a0d9a0d8b5ff35ff15fd75fd55f735f715f5b5f5941c741c541b341b1416f416d4161415f4d0915090d08a5089d071d071506cd06c4b9f4b9ecb98cb984b79cb794b74cb745a0e3a0e2a0d9a0d8a0b7a0b6a0b0a0af96f396f296e996e896be96bd96b596b4a458295828d820d82057dc57dbd7d657d5d090d0905089d089505b505ad057d0575a121a120a113a112a0b6a0b5a0afa0ae973d973c9730972f96bd96bc96b496b3a1d8215820d8145813d7f5d7f557f2d7f2508a5089d0815080d06cd06c506a5069dafebafeaafe5afe4afadafacafa4afa3a0d9a0d8a0d4a0d3a0b0a0afa0a9a0a8a68452844e840a840682c282be82a682a25cc65cc25c525c4e5ad65ad25ab25aae8b041b040b027b026afacafabafa3afa29730972f9713971296b496b396ab96aaad1

private theorem cap0111010110Accepted : Accepted table cap0111010110Box cap0111010110Tree := by
  decide +kernel

private def cap0111010111Box : Box := ![(23 / 20, 6 / 5), (63 / 200, 189 / 400), (3 / 8, 1 / 2), (5 / 8, 3 / 4)]

private def cap01110101110Box : Box := ![(23 / 20, 6 / 5), (63 / 200, 63 / 160), (3 / 8, 1 / 2), (5 / 8, 3 / 4)]

private def cap01110101110Tree : Option PackedTree := decode 6 0xf5a3f5a2f59df59d756ff56ef56b756ae2a862a762a2e2a2627862776273e2735eb3beb3aeb35eb34ead6ead5ead1ead0c545c544c53fc53ec4e7c4e6c4e1c4e0abab7fab77ab5bab57aa63aa5faa47aa4313c313bb139f139b12c712c312af12aaf56b756af568f5687548f5487545f5456273e2736270e2706255e2556252e2525471543153b1517151313c313bb139f139ac14ec14ac122c11ebfe6bfe2bfc6bfc2e2a2e2a2629fe29f6273e2736270e27058245823d8215820d7f8d7f857f5d7f55589e189dd89c389c189638961894b89495ff35ff15fd75fd55f735f715f5b5f5948eb45eb44eb34eb33eaddeadcead0eacfc54ec54dc53ec53dc4eec4edc4e0c4dfbd5bbd5b9d5a1d59fd52fd52dd515d51389dd89db89c189bf8961895f894989474e2a762a6e29f629ee2776276e270626fd8295828d820d82057fc57fbd7f557f4dc4eec4edc4e0c4dfc4b0c4afc4a4c4a3aff8aff7afeaafe9afb8afb7afacafaba43eb35eb34eb19eb18ead1ead0eac8eac7c53fc53ec528c527c4e1c4e0c4d8c4d7bd5a3d5a1d591d58fd517d515d505d50389c389c189b189af894b8949893b89394e29fe29f62946293e270e270626c626bd8215820d8145813d7f5d7f557f2d7f25c4e1c4e0c4d8c4d7c4a5c4a4c49dc49cafebafeaafe5afe4afadafacafa4afa3a4759a7599f58c758bf5457544f540f53fe29f629ee293e29362526251e24e624ddc53ec53dc527c526c4a4c4a3c49cc49bb041b040b027b026afacafabafa3afa2a1a

private theorem cap01110101110Accepted : Accepted table cap01110101110Box cap01110101110Tree := by
  decide +kernel

private def cap01110101111Box : Box := ![(23 / 20, 6 / 5), (63 / 160, 189 / 400), (3 / 8, 1 / 2), (5 / 8, 3 / 4)]

private def cap01110101111Tree : Option PackedTree := decode 6 0x3d8c1d8bdd895d893d785d781d76fd76d8cb78cb38c8d8c8b8b8d8b898b778b7410003bb12bb127b08bb087aedfaedbaebfaebb191b19171897189316ef16eb16cf16caaebc2ebc0ebb7ebb6eb47eb45eb3beb3ac5c6c5c4c5bbc5bac550c54ec545c54480001dd76fd76dd75fd75dd677d675d66bd6698b778b758b678b658a8b8a898a7f8a7d51c65bc659c646c645c5c6c5c4c5bbc5bab136b135b121b120b0bab0b9b0b0b0afb8c8d8c8b8c4b8c498b778b758b678b6562436241622762256161615f61556153562e362e262dde2dd62a862a762a2e2a2585d585cd8585857d829d82958245823dc5bbc5bac5b3c5b2c545c544c53fc53eb0b0b0afb0aab0a9b048b047b042b041a88ec5eec5dec21ec20ebc0ebbfebaeebadc659c658c624c623c5c4c5c3c5b2c5b1bd781d77fd75dd75bd68bd689d669d6678b898b878b658b638a9d8a9b8a7d8a7b4e32ce32c63126311e2e262e1e2d962d8d89ad89a58895888d85cd85c5854d8545c5c4c5c3c5b2c5b1c54ec54dc53ec53db0b9b0b8b0a9b0a8b052b051b041b040a43ec22ec21eba7eba6ebafebaeeba0eb9fc625c624c5abc5aac5b3c5b2c5a4c5a3b175d7f5d77590758ff59af59a758cf58c62d9e2d96297e297629fe29f62946293d38c4b8c498a6d8a6b8b678b658a5f8a5d622762256073607161556153605d605b716cf16cb14bf14bb14ff14fb14a3149ec2aac2a6c0bac0b6c10ac106c0a2c09e91d843d841d655d653d75dd75bd63fd63d8c498c478a6b8a698b658b638a5d8a5b7aebbaeb7ac7fac7bacd3accfac63ac5f16cb16c714bb14b714fb14f7149f149a9c624c623c535c534c53ec53dc527c526b112b111b038b037b041b040b027b026a1a

private theorem cap01110101111Accepted : Accepted table cap01110101111Box cap01110101111Tree := by
  decide +kernel

private def cap0111010111Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap01110101110Tree <*> cap01110101111Tree

private theorem cap0111010111Accepted : Accepted table cap0111010111Box cap0111010111Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap0111010111Box 1 (midpoint cap0111010111Box 1) = cap01110101110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap01110101110Accepted
  · have h : rightBox cap0111010111Box 1 (midpoint cap0111010111Box 1) = cap01110101111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap01110101111Accepted

private def cap011101011Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap0111010110Tree <*> cap0111010111Tree

private theorem cap011101011Accepted : Accepted table cap011101011Box cap011101011Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap011101011Box 0 (midpoint cap011101011Box 0) = cap0111010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0111010110Accepted
  · have h : rightBox cap011101011Box 0 (midpoint cap011101011Box 0) = cap0111010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0111010111Accepted

private def cap01110101Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap011101010Tree <*> cap011101011Tree

private theorem cap01110101Accepted : Accepted table cap01110101Box cap01110101Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap01110101Box 3 (midpoint cap01110101Box 3) = cap011101010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap011101010Accepted
  · have h : rightBox cap01110101Box 3 (midpoint cap01110101Box 3) = cap011101011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap011101011Accepted

private def cap0111010Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap01110100Tree <*> cap01110101Tree

private theorem cap0111010Accepted : Accepted table cap0111010Box cap0111010Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap0111010Box 2 (midpoint cap0111010Box 2) = cap01110100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap01110100Accepted
  · have h : rightBox cap0111010Box 2 (midpoint cap0111010Box 2) = cap01110101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap01110101Accepted

private def cap0111011Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (1 / 4, 1 / 2), (1 / 2, 3 / 4)]

private def cap0111011Tree : Option PackedTree := decode 10 0xc9da6fda6bd8a7d8a5d8c1d8bdd895d8938e258e218c9f8c9d8cb78cb38c8d8c8b62331c4b1c43193f193b196f1967191b1916c722c71ec4aac4a6c4dac4d6c486c482c444ed35ed34ec2dec2cec5eec5dec21ec20c710c70fc62fc62ec659c658c624c623a663886387e317e317632ce32c63126311d8e3d8e3588dd88d589ad89a58895888d21c464b1c8b1c7b12ab129b136b135b121b120a270a26fa1e7a1e6a1f1a1f0a1dea1ddb11944e144df43b543b343e343e143a943a730d330d12fdb2fd9300930072fcb2fc948b1d3b1d2b11eb11db135b134b112b111a27aa279a1dca1dba1f0a1efa1d3a1d2b44f544f343b943b743e143df43a743a530e930e72fe12fdf300730052fc92fc7438889da81da7fd85fd85dd8bbd8b9d841d83f8e398e378c638c618cb18caf8c478c4571c731c6f18c718c31963195f188f188ac74ac746c476c472c4d2c4cec446c4428ed3fed32ec2eec2aec5cec5bec1fec1eb1d1b1c4b11cb118b133b132b110b10fae232c74ac746c476c472c4d2c4cec446c44261ce61ca5fbe5fba600a60065f8e5f8ad8e8d8e2588e588c5899d89958885887cc394c334bf74bf54c00cc004bf14bf0d7110e2

private theorem cap0111011Accepted : Accepted table cap0111011Box cap0111011Tree := by
  decide +kernel

private def cap011101Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap0111010Tree <*> cap0111011Tree

private theorem cap011101Accepted : Accepted table cap011101Box cap011101Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap011101Box 1 (midpoint cap011101Box 1) = cap0111010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0111010Accepted
  · have h : rightBox cap011101Box 1 (midpoint cap011101Box 1) = cap0111011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap0111011Accepted

def cap01110Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap011100Tree <*> cap011101Tree

theorem cap01110Accepted : Accepted table cap01110Box cap01110Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap01110Box 0 (midpoint cap01110Box 0) = cap011100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap011100Accepted
  · have h : rightBox cap01110Box 0 (midpoint cap01110Box 0) = cap011101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap011101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover03
