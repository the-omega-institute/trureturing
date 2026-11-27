import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover08

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap1110010Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap11100100Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (1 / 2, 5 / 8), (1 / 2, 3 / 4)]

private def cap111001000Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (1 / 2, 5 / 8), (1 / 2, 5 / 8)]

private def cap111001000Tree : Option PackedTree := decode 6 0x3d929d8e7d8e7d8e5d6e1d6b3d6b3d6b18d198ce18ce18cdf8af18ac58ac58ac371a3319c319c319bf15e3158b158b1586c58ac52ec52ec52ac1e6c196c196c1928ec73ec5dec72ec5ceb59eb44eb58eb43c670c658c66fc657c562c54dc561c54cb8ce18cb18cdf8caf8ac58a9b8ac38a99629762696295626760cb60a360c960a143ec73ec72ec5dec5ceb59eb58eb44eb43c670c66fc658c657c562c561c54dc54cb8ce18cdf8cb18caf8ac58ac38a9b8a99629762956269626760cb60c960a360a147639762e762e762df5ac75a1f5a1f5a158a55899d899d8995832582858285827d6badc3ad67ad67ad63aab7aa8baa8baa8715e3158b158b1587131b12ef12ef12eae2bc62b162b162b0e263625de25de25d583cd832d832d83257e557e1d7e1d7e151d6b3d689d6b1d687d545d52dd543d52b8ac58a9b8ac38a998977895f8975895d7158b15371587153312ef12bf12eb12bac196c146c192c142bf0ebedebf0abeda87d6b3d6b1d689d687d545d543d52dd52b8ac58ac38a9b8a9989778975895f895d7158b15871537153312ef12eb12bf12bac196c192c146c142bf0ebf0abedebeda8eb58eb43eb43eb42eaa1ea95ea95ea94b064b050b050b04fafc2afb6afb6afb5ad1b162b14bb14bb14ab079b065b065b064982d981898189817975f974e974e974db629762696295626760cb60a360c960a130313005302f30032e9d2e792e9b2e775d8a5d8a5589a5899d832d8325828d8284c0c4c0bcc014c00cba74ba6cb9e4b9ddb14ab133b133b132b064b050b050b04f9817980198019800974d973b973b973aad583cd832d832d83257e557e1d7e1d7e14bafcba74ba74ba6cb65cb624b624b61db065b051b064b050afc3afb7afc2afb6974e973c974d973b96c496bc96c396bbaec196c192c146c142bf0ebf0abedebeda5d3a5d365cf25cee5b125b0e5af25aeed832582858285827d7e157db57db57dacba6cb9dcb9dcb9d4b61cb5dcb5dcb5d5688

private theorem cap111001000Accepted : Accepted table cap111001000Box cap111001000Tree := by
  decide +kernel

private def cap111001001Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap1110010010Box : Box := ![(11 / 10, 23 / 20), (63 / 200, 189 / 400), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100100100Box : Box := ![(11 / 10, 23 / 20), (63 / 200, 63 / 160), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100100100Tree : Option PackedTree := decode 5 0x360f960f560d160cd6033603160136011428f428b4269426741ef41ed41db41d96c066c062c026c022bf32bf2ebf16bf1283de83da83b683b28316831282fa82f69a147a145a134a133a0f7a0f6a0eda0ec976197609750974f9706970596fd96fcb41ef41ed41db41d9418b4189417d417b2e0d2e0b2dfb2df92d9b2d992d8d2d8b48b07ab079b066b065afcbafcaafc4afc3a145a144a133a132a0c4a0c3a0bda0bcb428b42894267426541894187417b41792ec12ebf2e9f2e9d2d992d972d8b2d8943b068b066b053b052b009b008aff9aff8a134a133a122a121a0eda0eca0e3a0e2b601360115ff35ff15f8b5f895f735f7141db41d941c741c5417d417b416f416d4d09a5099d0915090d076d0765071d0714ba84ba7cb9f4b9ecb7ecb7e4b79cb795a0eda0eca0e3a0e2a0bea0bda0b7a0b696fd96fc96f396f296c696c596be96bda458335832d8295828d7e257e1d7dc57dbd099d0995090d090505ed05e505b505ada133a132a121a120a0bda0bca0b6a0b5974f974e973d973c96c596c496bd96bca1a

private theorem cap11100100100Accepted : Accepted table cap11100100100Box cap11100100100Tree := by
  decide +kernel

private def cap11100100101Box : Box := ![(11 / 10, 23 / 20), (63 / 160, 189 / 400), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100100101Tree : Option PackedTree := decode 7 0xd8b2d8b258acd8ac58725871d86cd86c5110d110510a5109d0d450d3d0ce50cddb164b163b158b157b0e3b0e2b0d8b0d7a220a21fa213a212a1a7a1a6a19ba19aaec566c562c53ac536c366c362c33ec33a8852884e881e881a8672866e86468642d8ac58abd8a6d8a6586c586bd8675866d109d10951035102d0cdd0cd50c850c7d6ac392c38ac366c35ec1f2c1eac1cac1c286a2869a8672866a851e851684f684f2d86cd86bd867d866d83958385834583350ce50cd50c8d0c7d09ed09e509a5099d468886887e8852884a86a2869a8672866a60c260ba6092608e5ef25eea5ec65ec2d10a51095103d102d0ce50cd50c8d0c7cc124c11cc0d4c0ccbd8cbd84bd3cbd3554351434d4323431f428f428b426942672f792f752f4f2f4d2ec32ec12ea12e9f48b163b162b14cb14bb0e2b0e1b0cdb0cca21fa21ea205a204a1a6a1a5a18fa18eb61c561c3619b619960f560f360cd60cb434d434b431f431d428b4289426742654d10fd10f5102d10250a2d0a25099d0994c174c16cc0ccc0c4bb04bafcba7cba750ec53ac532c506c4fec33ec336c312c30a881e881687ee87ea8646863e86168612d8a0d89fd89b589ad8625861585d585cd0fdd0fd50f8d0f850c2d0c250be50bdd5619f619b6189618560d160cd60bb60b74323431f430b430942694267425742556c312c30ac2eac2e6c176c16ec14ec14a8616861285f285ee84ae84aa848a8486a3440f440b43f743f54323431f430b430930353033301d301b2f4f2f4d2f3b2f39687ee87ea87c687c28616861285f285ee603a60366012600e5e765e725e525e4eaa191a18fa17ca17ba134a133a122a12197a797a6979497939750974f973e973da458a658a5d89ad89a58335832d8295828d102d10250f850f7d099d0995090d0905a205a204a1f0a1efa133a132a121a1209819981898039802974f974e973d973ca1a

private theorem cap11100100101Accepted : Accepted table cap11100100101Box cap11100100101Tree := by
  decide +kernel

private def cap1110010010Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11100100100Tree <*> cap11100100101Tree

private theorem cap1110010010Accepted : Accepted table cap1110010010Box cap1110010010Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110010010Box 1 (midpoint cap1110010010Box 1) = cap11100100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100100100Accepted
  · have h : rightBox cap1110010010Box 1 (midpoint cap1110010010Box 1) = cap11100100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100100101Accepted

private def cap1110010011Box : Box := ![(23 / 20, 6 / 5), (63 / 200, 189 / 400), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100100110Box : Box := ![(23 / 20, 6 / 5), (63 / 200, 63 / 160), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100100110Tree : Option PackedTree := decode 7 0xf5ba75b975b4f5b37580f57ff57c757b62be62bd62b8e2b7e28a62896285e284900046eb68eb67eb5deb5ceaf8eaf7eaf0eaefc571c570c566c565c50bc50ac502c501bd6cfd6cdd6b9d6b7d5efd5edd5dfd5dd8ae18adf8acb8ac98a158a138a038a015aeb01eaffeaf8eaf6eaafeaaeeaaaeaa9c514c512c50bc509c4c8c4c7c4c3c4c2bd5f1d5edd5e1d5ddd555d553d549d5478a178a138a058a0189878985897b897951c57cc57ac571c56fc514c512c50bc509b07cb07ab072b070b019b018b011b010b8ae38adf8acd8ac98a178a138a058a0160e560e160d160cd60236021601360115628a62896281628062646263e25ee25e580cd80c5804d80457e657e5d7e2d7e2523adcbadc3ad6fad67abffabfbabbbabb715eb15e31593158b144b1447140313fef57ff57f75777576f5577556f551f55162896288e280627fe263e263625e625dd38af58af18ac98ac58a258a238a0189ff60f560f360cd60cb6031602f6011600f7144b1447140313ff131f131b12f312eec062c05ec022c01ebf2ebf2abf12bf0e90fad77ad73ad47ad43abc3abbfab9fab9b159b1597156b1567140b140713e713e2f5ae75adf5a875a7f577f57775737572e2b2e2b262ace2ac6280e280627c627bd7d6a3d6a1d68fd68dd5cfd5cdd5bfd5bd8ab58ab38aa18a9f89f389f189e189df7ad43ad3fad1bad17ab9bab97ab7bab7715671563153f153b13e313df13bf13bab5d5e1d5ddd5cfd5cbd549d547d53dd53b8a058a0189f389ef897b8979896f896d7ab9fab97ab7fab77aa7baa77aa63aa5f13e713df13c313bb12df12db12c712c2a38acd8ac98ab58ab18a058a0189f389ef60d160cd60bb60b760136011600360017156b15631543153b13e713df13c313bac176c16ec14ec14ac006c002bfe6bfe2ac502c500c4f0c4eec4bdc4bcc4b1c4b0b009b008aff9aff8afc5afc4afb9afb8a475adf5acf5a2f5a275777576f56ef56e62b262b162a762a6e280627fe2776276deaeeeaedeaddeadceaa3eaa2ea97ea96c500c4ffc4eec4edc4bcc4bbc4b0c4afa71593158b153b1537140313ff13bb13b6c19ac196c14ac146c022c01ebfe2bfdee280627fe2776276e25e625de2586257d8045803d7fc57fbd7e257e1d7dc57dbd21a

private theorem cap11100100110Accepted : Accepted table cap11100100110Box cap11100100110Tree := by
  decide +kernel

private def cap11100100111Box : Box := ![(23 / 20, 6 / 5), (63 / 160, 189 / 400), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap111001001110Box : Box := ![(23 / 20, 6 / 5), (63 / 160, 189 / 400), (1 / 2, 9 / 16), (5 / 8, 3 / 4)]

private def cap111001001110Tree : Option PackedTree := decode 6 0x3d8efd8edd8d5d8d3d7b7d7b5d79bd7998ce98ce78ccb8cc98bbb8bb98ba18b9f7b1dbb1d7b1a7b1a3af6baf63af33af2f19cf19cb1993198f1773176f173f173abec6aec69ec60ec5febcdebccebc3ebc1c665c664c65bc65ac5d0c5cfc5c6c5c5bd8d3d8d1d8bfd8bdd799d797d783d7818cc98cc78cb58cb38b9f8b9d8b8b8b895aebdbebdaebcdebcceb5deb5ceb51eb50c5ddc5dcc5d0c5cfc566c565c55ac559bd7b5d7b1d799d797d6b9d6b7d6a1d69f8bb98bb78b9f8b9d8acb8ac98ab38ab15f5e6f5e675e1f5e0f5a8f5a875a3f5a362e862e7e2e362e2e2ad62ace2a862a7debccebcbebc1ebc0eb50eb4feb46eb45c5cfc5cec5c5c5c4c559c558c54fc54ead1c674c673c665c664c5ddc5dcc5d0c5cfb14eb14db141b140b0cfb0ceb0c4b0c3b8ce78ce58cc98cc78bb98bb78b9f8b9d629b62996281627f619d619b618761855e332e331e32de32ce2e8e2e762e362e258a0d89fd89b589ad8625861585d585c84003e58bbb8bb98ba18b9f8acd8acb8ab58ab3619f619d6189618760d160cf60bb60b971773176f173f173b1597159315671562c33ac336c30ec30ac19ec19ac172c16ebc5d1c5cec5c6c5c4c55ac558c550c54eb0c4b0c2b0bab0b9b05db05bb053b05280007c88ec75ec73ec5eec5debd9ebd6ebc0ebbfc672c670c659c658c5dbc5d9c5c4c5c308005dd7b3d7add781d77fd6b7d6b3d68bd6898bb78bb38b898b878ac98ac58a9d8a9b0000b8e3396338632ce32c62ede2ece2e262e1d8a658a5d89ad89a5866d866585cd85c5c5dbc5d9c5c4c5c3c564c562c54ec54db0cdb0ccb0b9b0b8b066b065b052b051a43

private theorem cap111001001110Accepted : Accepted table cap111001001110Box cap111001001110Tree := by
  decide +kernel

private def cap111001001111Box : Box := ![(23 / 20, 6 / 5), (63 / 160, 189 / 400), (9 / 16, 5 / 8), (5 / 8, 3 / 4)]

private def cap111001001111Tree : Option PackedTree := decode 7 0x3d931d92fd90dd90bd7e7d7e3d7cdd7cbaa45aa43aa2baa29a9a9a9a7a99ba9997548b5487545754535353534f533753331a431a3f1a0319ff17d717d317a717a28ec97ec96ec85ec84ebf1ebf0ebe5ebe4c68fc68ec67fc67ec5f4c5f3c5e8c5e7afb21bb217b1dfb1dbaf9baf97af6faf6b545754535427542353375333531b5316ea8aea8a6a84ea846a66ea666a636a62e340633fe33a6339e2f4e2f462eee2ee51d90bd909d8edd8ebd7cbd7c9d7b5d7b18cff8cfd8ce78ce58bd18bcf8bb98bb75aebf3ebf1ebe6ebe5eb74eb73eb68eb67c5f5c5f4c5e9c5e8c57cc57bc571c570bd7e3d7e1d7cbd7c9d6e7d6e5d6cfd6cd8be98be78bd18bcf8af78af58ae18adf5f5f375f2f5edf5ed75b475b3f5aef5ae62f4e2f462eee2ee62b8e2b862b362b2debe5ebe4ebdaebd8eb67eb66eb5ceb5bc5e8c5e7c5dcc5dbc570c56fc565c564ad1c690c68fc680c67fc5f5c5f4c5e9c5e8b165b164b159b158b0e4b0e3b0d9b0d8b8d1f8d1d8cff8cfd8be98be78bd18bcf62c962c762b162af61c761c561b161af5e340633fe33a6339e2f4e2f462eee2ee58acd8ac58a758a6d86cd86c5867d8675c67fc67ec673c672c5e8c5e7c5dcc5dbb158b157b14db14cb0d8b0d7b0ceb0cdad62fae2fa62f4e2f462be62bde2b8e2b858725871d86cd86c583e583dd8395838dc5f4c5f3c5e8c5e7c57bc57ac570c56fb0e3b0e2b0d8b0d7b07bb07ab071b070af17a717a31777177315c715c3159b1596c366c362c33ec33ac1cac1c6c1a2c19ee2f462f3e2ee62ede2b862b7e2b2e2b2586c586bd8675866d838d8385833d8335688ec96ec94ec84ec83ebf0ebeeebe4ebe3c68ec68cc67ec67dc5f3c5f1c5e7c5e6bd909d907d8ebd8e7d7c9d7c7d7b1d7ad8cfd8cfb8ce58ce18bcf8bcd8bb78bb3575f875f775f275f1f5b975b875b375b2e2f9e2f8e2f3e2f362bd62bc62b7e2b75ebe4ebe3ebd8ebd6eb66eb65eb5beb59c5e7c5e6c5dbc5d9c56fc56ec564c562a8e34763466339633862f9e2f8e2ede2ecd8b1d8b158a658a5d8715870d866d8665c5f3c5f1c5dbc5d9c57ac578c564c562b0e2b0e1b0cdb0ccb07ab079b066b065a43

private theorem cap111001001111Accepted : Accepted table cap111001001111Box cap111001001111Tree := by
  decide +kernel

private def cap11100100111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111001001110Tree <*> cap111001001111Tree

private theorem cap11100100111Accepted : Accepted table cap11100100111Box cap11100100111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11100100111Box 2 (midpoint cap11100100111Box 2) = cap111001001110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001001110Accepted
  · have h : rightBox cap11100100111Box 2 (midpoint cap11100100111Box 2) = cap111001001111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001001111Accepted

private def cap1110010011Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11100100110Tree <*> cap11100100111Tree

private theorem cap1110010011Accepted : Accepted table cap1110010011Box cap1110010011Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110010011Box 1 (midpoint cap1110010011Box 1) = cap11100100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100100110Accepted
  · have h : rightBox cap1110010011Box 1 (midpoint cap1110010011Box 1) = cap11100100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100100111Accepted

private def cap111001001Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap1110010010Tree <*> cap1110010011Tree

private theorem cap111001001Accepted : Accepted table cap111001001Box cap111001001Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap111001001Box 0 (midpoint cap111001001Box 0) = cap1110010010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110010010Accepted
  · have h : rightBox cap111001001Box 0 (midpoint cap111001001Box 0) = cap1110010011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110010011Accepted

private def cap11100100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap111001000Tree <*> cap111001001Tree

private theorem cap11100100Accepted : Accepted table cap11100100Box cap11100100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11100100Box 3 (midpoint cap11100100Box 3) = cap111001000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001000Accepted
  · have h : rightBox cap11100100Box 3 (midpoint cap11100100Box 3) = cap111001001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001001Accepted

private def cap11100101Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (5 / 8, 3 / 4), (1 / 2, 3 / 4)]

private def cap111001010Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (5 / 8, 3 / 4), (1 / 2, 5 / 8)]

private def cap111001010Tree : Option PackedTree := decode 8 0xc9d92bd8e9d929d8e7d7dfd7afd7ddd7ad8d1b8ce38d198ce18be58bb58be38bb354ebefebd7ebeeebd6eb71eb5aeb70eb59c5f2c5dac5f1c5d9c579c563c578c562a8e34763396346633862f9e2ede2f8e2ecd8b1d8a658b158a5d8715866d870d8665c5f3c5dbc5f1c5d9c57ac564c578c562b0e2b0cdb0e1b0ccb07ab066b079b065a446a75b975adf5b875acf57ff577757f7576e2bd62b262bc62b1628962806288e27fdeaffeaeeeafeeaedeaaeeaa3eaadeaa2c512c500c511c4ffc4c7c4bcc4c6c4bba715eb159315e3158b144b1403144713fec1eac19ac1e6c196c062c022c05ec01ee28962806288e27fe263e25e6263625dd80c5804580bd803d7e5d7e257e557e1d2234658b1d8a658b158a5d8715866d870d866510fd102d10f510250d350c7d0d2d0c75b0e2b0cdb0e1b0ccb07ab066b079b065a1a6a18fa1a5a18ea145a133a144a132a6887e8816887a8812851684ce851284ca60ba606660b660625d825d3e5d7e5d3a88d4b07ab066b079b065afcbafc4afcaafc3a145a133a144a132a0c4a0bda0c3a0bcb428b4267428942654189417b418741792ec12e9f2ebf2e9d2d992d8b2d972d8944688

private theorem cap111001010Accepted : Accepted table cap111001010Box cap111001010Tree := by
  decide +kernel

private def cap111001011Box : Box := ![(11 / 10, 6 / 5), (63 / 200, 189 / 400), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap1110010110Box : Box := ![(11 / 10, 23 / 20), (63 / 200, 189 / 400), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap1110010110Tree : Option PackedTree := decode 8 0xd8c6d8bdd8c2d8bd5883d87c5880d87bd124d11bd120d11b50e550de50e250dddb185b17ab17bb179b101b0f7b0f8b0f6a241a236a237a235a1c4a1bba1bca1baaac41ec3e2c3e2c3dac24ac236c236c22e872a86f286f286ea857685628562855a9a249a237a237a235a1caa1bca1bca1ba985698459845984397db97cf97cf97cdb439543794379437542bb42b142b142ad2fb72f9f2f9f2f9b2ee12ed72ed72ed548962f562c962f362c761ef61c761ed61c5446d4441446b443f4377434f4375434d54b0f7b0e3b0f6b0e2b08cb07bb08bb07aa1bba1a7a1baa1a6a157a146a156a145a8ca236a220a235a21fa1bba1a7a1baa1a69844982f9843982e97ce97bb97cd97baaa86f286a286ea869a8562851e855a85165f3e5ef25f365eea5dae5d865daa5d8290ec5eec5e6c5c2c5bac3e2c3dac3bac3b288de88d688b288aa86f286ea86ca86c2d8b858b7d8b2d8b258775876d8725871d1165115d110d11050d950d8d0d450d3db16fb16eb164b163b0edb0ecb0e3b0e2a22ba22aa220a21fa1b1a1b0a1a7a1a6ad587c587b587758765846d845d842d84250de50dd50d950d850ac50ab50a850a7db0eeb0ecb0e4b0e2b085b084b07cb07aa1b2a1b0a1a8a1a6a150a14fa147a145a8d11bd11ad116511550de50dd50d950d84c22cc21cc1d4c1ccbe7cbe6cbe2cbe25a22ca22aa221a21fa1b2a1b0a1a8a1a6983a98399830982e97c597c497bc97baaa86f286ea86a2869a8562855a851e85165f3e5f365ef25eea5dae5daa5d865d829162f362c762c762c561ed61c561c561c3446b443f443f443d4375434d434d434b6c3dac38ac38ac386c22ec1eac1eac1e686ea869a869a8696855a8516851685129a235a21fa21fa21ea156a145a145a1449843982e982e982d976a97609760975fa1ab092b08db08db08bafd7afd2afd2afd1a15da158a158a156a0d0a0cba0cba0cab42bb42b142b142ad41a14197419741952ee12ed72ed72ed52db12da72da72da545846d83e5845d83d580f580cd80ed80c50ac50a3d0ab50a2d07e507bd07dd07b5b01eb019b01db018afd2afccafd1afcba0fca0f7a0fba0f6a0cba0c5a0caa0c4a68562851e855a8516832e8316832a83125dae5d865daa5d825b4e5b365b4a5b3287611b611760f960f5603d603b6033603142b142ad428f428b41f941f741ef41ed6c07ac076c066c062bf4abf46bf32bf2e83f283ee83de83da832e832a831683129a158a156a147a145a0cba0caa0c5a0c4976b976a9761976096d396d296cd96cca2c22ec1eac1eac1e6bf46bf2ebf2ebf2a855a851685168512832a83128312830ed0ab50a2d0a2d0a25065506250625061cbb54bb04bb04bafcb694b664b664b65d0d1

private theorem cap1110010110Accepted : Accepted table cap1110010110Box cap1110010110Tree := by
  decide +kernel

private def cap1110010111Box : Box := ![(23 / 20, 6 / 5), (63 / 200, 189 / 400), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap11100101110Box : Box := ![(23 / 20, 6 / 5), (63 / 200, 63 / 160), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap11100101110Tree : Option PackedTree := decode 6 0x3d721d70dd70dd709d623d61bd61bd6178b338b1f8b1f8b1b8a498a418a418a3d7ac47ac37ac37ac2faaebaad7aad7aad3149314831483147b134f133b133b13369c599c58fc58fc58dc4d3c4cec4cec4cdb092b08db08db08bafd7afd2afd2afd1a275c2f5b9f5c275b9758675807585f57fe2c762bde2c6e2bd628fe289e28f628955d61bd603d617d5ffd56bd55fd569d55d8a418a298a3d8a25899d8991899b898f4e2c7e2be62c6e2bd6290628a628f62895846d83e5845d83d580f580cd80ed80c5c520c514c51ec512c4cec4c8c4cdc4c7b01eb019b01db018afd2afccafd1afcba43eb86eb84eb7eeb7ceb0deb0beb08eb07c58fc58dc587c585c520c51ec51bc51abd6fdd6f9d6e9d6e5d611d60fd603d5ff8b0f8b0b8af98af58a378a358a298a2557586f585f580f57ff55af55a7557f5576290628f628a628962676266e2646263d38b1f8b1b8af98af58a418a3d8a298a25611b611760f960f5603d603b6033603171483147b1453144b133b13371323131ec07ac076c066c062bf4abf46bf32bf2e91d709d6e5d6e5d6e1d617d5ffd5ffd5fd8b1b8af58af58af18a3d8a258a258a237ac2fabffabffabfbaad3aabbaabbaab7147b144b144b14471337131f131f131a9c58dc57ac57ac578c4cdc4c7c4c7c4c6b08bb07ab07ab079afd1afcbafcbafcaa1a

private theorem cap11100101110Accepted : Accepted table cap11100101110Box cap11100101110Tree := by
  decide +kernel

private def cap11100101111Box : Box := ![(23 / 20, 6 / 5), (63 / 160, 189 / 400), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap111001011110Box : Box := ![(23 / 20, 6 / 5), (63 / 160, 189 / 400), (5 / 8, 11 / 16), (5 / 8, 3 / 4)]

private def cap111001011110Tree : Option PackedTree := decode 7 0x3d96fd96dd951d94fd80fd80dd7fbd7f9aa77aa75aa61aa5fa9c3a9c1a9b7a9b5754ef54eb54c354bf53875383536f536b1aaf1aab1a831a7f182b1827180317fe8ecb6ecb5eca7eca6ec06ec05ebfcebfbc6aac6a9c69fc69ec609c608c5ffc5feafb2a3b29fb263b25faff7aff3afcfafc754c354bf548b5487536f536b5353534eea986a97ea916a90ea6dea6d6a6a6a69e350634fe3486347e30062ffe2fae2fa51d94fd94dd92fd92dd7f9d7f7d7e3d7e18d3f8d3d8d1f8d1d8bff8bfd8be98be75aec07ec06ebfdebfceb86eb85eb7eeb7dc60ac609c600c5ffc58fc58ec587c586bd80dd80bd7f9d7f7d70bd709d6fbd6f98c138c118bff8bfd8b1d8b1b8b0d8b0b5f5fef5fe75f9f5f8f5bf75bef5ba75b9e30062ffe2fae2fa62c3e2c362be62bddebfcebfbebf1ebf0eb7deb7ceb73eb72c5ffc5fec5f4c5f3c586c585c57bc57aad1c6abc6aac6a0c69fc60ac609c600c5ffb17bb17ab170b16fb0f8b0f7b0eeb0edb8d558d538d3f8d3d8c138c118bff8bfd62f562f362df62dd61ef61ed61db61d95e350634fe3486347e30062ffe2fae2fa58b858b7d8b2d8b258775876d8725871dc69fc69ec68fc68ec5ffc5fec5f4c5f3b16fb16eb164b163b0edb0ecb0e3b0e2ad63056304630062ff62c7e2c6e2c3e2c2d87c587b587758765846d845d842d8425c600c5fec5f6c5f3c587c585c57cc57ab0eeb0ecb0e4b0e2b085b084b07cb07a20008c88ecb5ec96eca6ec95ec05ebf0ebfbebefc6a9c68ec69ec68dc608c5f3c5fec5f2bd94dd92bd92dd929d7f7d7dfd7e1d7dd8d3d8d1b8d1d8d198bfd8be58be78be357602f5f875fdf5f7f5c275b975be75b8e30462f9e2ff62f962c6e2bd62c2e2bcdebfbebefebf0ebeeeb7ceb71eb72eb70c5fec5f2c5f3c5f1c585c579c57ac578a8e354e34763476346630462f9e2f9e2f8d8bcd8b1d8b1d8b1587b587158715870dc608c5f3c5f3c5f1c58dc57ac57ac578b0f6b0e2b0e2b0e1b08bb07ab07ab079a43

private theorem cap111001011110Accepted : Accepted table cap111001011110Box cap111001011110Tree := by
  decide +kernel

private def cap111001011111Box : Box := ![(23 / 20, 6 / 5), (63 / 160, 189 / 400), (11 / 16, 3 / 4), (5 / 8, 3 / 4)]

private def cap111001011111Tree : Option PackedTree := decode 6 0x3d991d981d981d97fd82dd821d821d81f8d7d8d6d8d6d8d6b8c338c278c278c257b303b2dfb2ffb2dbb043b01fb03fb01b1adb1aaf1ad71aab184f182b184b1826becc0ecbfecb7ecb6ec10ec0fec07ec06c6b6c6b5c6abc6aac613c612c60ac609bd97fd96dd96dd96bd81fd80dd80dd80b8d6b8d558d558d538c258c138c138c115aec16ec07ec10ec06eb90eb86eb8deb85c619c60ac613c609c599c58fc596c58ebd821d80dd80fd80bd71bd70bd70dd7098c278c138c158c118b2d8b1d8b1f8b1b51c6bec6b6c6b6c6b5c619c613c613c612b18db185b185b184b107b101b101b100b8d6d8d578d6b8d558c278c158c258c13630b62f7630962f5620361f1620161ef5e35b635ae355e3556309e30963056304d8c2d8c258bdd8bd5880d880587c587bdc6b5c6aac6aac6a9c612c609c609c608b184b17ab17ab179b100b0f7b0f7b0f6ad630ce3056305630462cce2c7e2c7e2c6d883d87c587c587b58495846d846d845d22765b7653f65af653760375fe7602f5fde355634fe354e34f6304e2ffe30462ff58d4ec06ebf2ec05ebf0eb85eb73eb84eb72c609c5f4c608c5f3c58ec57bc58dc57a40008c8cc6aac68fc6a9c68ec609c5f4c608c5f3b17ab164b179b163b0f7b0e3b0f6b0e2aa6304e2fa630462f9e2c762bde2c6e2bd587bd871d87b58715846583dd845d83d5443

private theorem cap111001011111Accepted : Accepted table cap111001011111Box cap111001011111Tree := by
  decide +kernel

private def cap11100101111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111001011110Tree <*> cap111001011111Tree

private theorem cap11100101111Accepted : Accepted table cap11100101111Box cap11100101111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11100101111Box 2 (midpoint cap11100101111Box 2) = cap111001011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001011110Accepted
  · have h : rightBox cap11100101111Box 2 (midpoint cap11100101111Box 2) = cap111001011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001011111Accepted

private def cap1110010111Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11100101110Tree <*> cap11100101111Tree

private theorem cap1110010111Accepted : Accepted table cap1110010111Box cap1110010111Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110010111Box 1 (midpoint cap1110010111Box 1) = cap11100101110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100101110Accepted
  · have h : rightBox cap1110010111Box 1 (midpoint cap1110010111Box 1) = cap11100101111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100101111Accepted

private def cap111001011Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap1110010110Tree <*> cap1110010111Tree

private theorem cap111001011Accepted : Accepted table cap111001011Box cap111001011Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap111001011Box 0 (midpoint cap111001011Box 0) = cap1110010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110010110Accepted
  · have h : rightBox cap111001011Box 0 (midpoint cap111001011Box 0) = cap1110010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110010111Accepted

private def cap11100101Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap111001010Tree <*> cap111001011Tree

private theorem cap11100101Accepted : Accepted table cap11100101Box cap11100101Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11100101Box 3 (midpoint cap11100101Box 3) = cap111001010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001010Accepted
  · have h : rightBox cap11100101Box 3 (midpoint cap11100101Box 3) = cap111001011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001011Accepted

def cap1110010Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11100100Tree <*> cap11100101Tree

theorem cap1110010Accepted : Accepted table cap1110010Box cap1110010Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1110010Box 2 (midpoint cap1110010Box 2) = cap11100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100100Accepted
  · have h : rightBox cap1110010Box 2 (midpoint cap1110010Box 2) = cap11100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover08
