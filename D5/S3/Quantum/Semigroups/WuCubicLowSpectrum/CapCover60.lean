import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover60

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap111111101Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap1111111010Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap11111110100Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 441 / 800), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap11111110100Tree : Option PackedTree := decode 7 0xd9bd59bcd9b959b8d8d0d8d058cf58ced1ee51edd1ea51e9d12dd12d512c512bda3dca3dba3d4a3d3a25ba25aa258a257999899979991999098629861985f985ea2cde6cddecdc6cdbec98ec98ac97ec97a8f6e8f668f4e8f468bda8bd68bce8bcad931d931592fd92f58d058cfd8ced8ce517b517ad179d179512d512cd12bd12b5347b747b347a747a345ed45eb45e745e5332f332b3321331d31c331c131bd31bb68bda8bd68bce8bca896a8966895e895a63866382637a637661866182617a617690ecdcacdc6cdb2cdaac982c97ec96ec96a8f528f4e8f3a8f328bd28bce8bbe8bbad9b659b559b259b1592dd92d592a592951e751e651e351e25177d177517451735564c164bf64a964a5633d633b6329632745e945e745d145cd44b144af44a1449f4d1ea51e9d1e751e6517a5179d177d1774cc8ccc84cc5ccc4cc6fcc6f4c6d4c6cda3cea3cca3c6a3c4a2efa2eea2e8a2e6998b99899983998198da98d998d398d1aa8bd28bce8ba28b9a8962895e8942893e637e637a634e6346617e617a616e616a9166e366df66d566d164bf64bd64b564b147a747a34799479545e745e545dd45d96cdaacda6cd8acd86c96ac966c94ac9468f328f2e8f128f0e8bba8bb68b9a8b96d9b4d9b459b0d9b0592cd92c5928d92851e5d1e551e1d1e15176d1765172d17256ac97ec97ac96ac962c676c672c666c6628bce8bca8bba8bb2895e895a894e894ad92d592c5929592858ccd8cc58c9d8c8d1775176517351725129d1295127d126d468f4e8f468f328f2a8bce8bca8bba8bb26642663a6626661e637a63766366635ed1e651e5d1e251e1d1775176d1735172ccc4ccc44cc0ccc04c6ccc6c4c68cc685a3cba3caa3c3a3c2a2eda2eca2e5a2e4998899879980997e98d898d798d098cfad5179d17951735172512bd12b5127d126cc6f4c6ecc68cc67cc2f4c2ecc2d4c2cd21a

private theorem cap11111110100Accepted : Accepted table cap11111110100Box cap11111110100Tree := by
  decide +kernel

private def cap11111110101Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap111111101010Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 1)]

private def cap1111111010100Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap11111110101000Box : Box := ![(11 / 10, 9 / 8), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101010000Box : Box := ![(11 / 10, 9 / 8), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101010000Tree : Option PackedTree := decode 5 0x34a174a154a094a0747a747a54799479735273525351935173321331f331333116942a9426940e940a8f4a8f468f2e8f2a6a4a6a466a2e6a2a663e663a6622661eba504a503a4f2a4f0a3cca3cba3c4a3c39e6d9e6c9e5e9e5c9d709d6f9d699d68b3cdb3cd93cbd3cb93ae13adf3ad33ad135193517350134ff331333113303330145281d281527852775233d233522f522ecf364f35cf2e4f2d4ef5cef54ef34ef2da467a466a45ea45da3cba3caa3c3a3c29deb9dea9de69de59d6f9d6e9d689d67a679b279ae7972796a77ae77aa779a77966a2e6a2a69fe69f66832682e681e681acef5cef54ef34ef2ceb7ceb74eb44eb3cd064d05cd03cd034cc44cc3ccc04cbf521a

private theorem cap111111101010000Accepted : Accepted table cap111111101010000Box cap111111101010000Tree := by
  decide +kernel

private def cap111111101010001Box : Box := ![(11 / 10, 9 / 8), (189 / 320, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111010100010Box : Box := ![(11 / 10, 9 / 8), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 15 / 16)]

private def cap1111111010100010Tree : Option PackedTree := decode 7 0xd34bd34b5346d345d2e1d2e152dcd2dbcfd1cfd14fcd4fcc4f82cf824f7e4f7d5a68da68ca681a680a5b9a5b8a5aea5ad9f9a9f999f8f9f8e9efc9efb9ef19ef0b4d194d174d014cff4b714b6f4b5b4b593f333f313f1d3f1b3df73df53de13ddf5aa5c3a5c2a5b9a5b7a504a503a4fda4fc9f059f049efc9efa9e6d9e6c9e679e66b4b734b6f4b5d4b5949fb49f949e549e13df93df53de33ddf3ccf3ccd3cbd3cb9519fa39fa29f9a9f989f059f049efc9efa9bc29bc19bba9bb89b2a9b299b229b20b3f353f333f1f3f1d3df93df73de33de137753773375f375d36453643362f362d67e667e627e3a7e367bee7bea7bc27bbe6ee66ee26eba6eb66c866c826c5a6c56b53e0b3e093de33ddf3cdb3cd93cbd3cb936553653362f362b35193517350134ff48a696a695a68ba68aa5c2a5c1a5b7a5b69fa29fa19f989f979f049f039efa9ef9b4d2b4d294d154d134b834b814b6d4b6b3f433f413f2f3f2d3e073e053df33df15d345d345533fd33f52dbd2db52d652d5d03dd03d503ad03a500e500dd00b500ada07ba07aa075a074a01ca01ba016a0159f989f979f8d9f8c9efa9ef99eef9eeea29a2a9a2699fa99f696da96d696ae96aa81ea81e681d281ce806e806a80568052d03d503cd03a5039d00dd00d500ad00a4fcbcfcb4fc64fc5cf7ccf7c4f774f76d0d52e152e052dbd2dad281d281527e527d4f824f814f7d4f7c4f364f35cf334f325a5b7a5b6a5aca5aba4fca4fba4f0a4ef9efa9ef99eef9eee9e669e659e5c9e5bb4b6d4b6b4b574b5549f749f549df49dd3df33df13ddd3ddb3ccb3cc93cb73cb55a33f453f433f313f2f3e093e073df53df3378337813771376f365336513641363f67e867e827e5e7e5a7c0e7c0a7be67be26f026efe6ede6eda6ca26c9e6c7e6c7ab9f989f979f8d9f8c9efa9ef99eef9eee9bb89bb79bad9bac9b209b1f9b159b14b3f2f3f2d3f193f173df33df13ddd3ddb38c138bf38b738b5384338413839383767182717e716e716a708670827072706e6ede6eda6eb26eae6c7e6c7a6c526c4e86a7c127c0a7bea7be279b279ae799a79926ca66c9e6c826c7a6a2e6a2a6a1a6a16cf7d4f7c4f77cf76cf334f324f2e4f2d4d904d8f4d8acd89cd434d42cd3fcd3ed443

private theorem cap1111111010100010Accepted : Accepted table cap1111111010100010Box cap1111111010100010Tree := by
  decide +kernel

private def cap1111111010100011Box : Box := ![(11 / 10, 9 / 8), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111010100011Tree : Option PackedTree := decode 5 0x34d4d4d4b4d2f4d2d4ba34ba14b874b853f5f3f5d3f473f453e213e1f3e0b3e09697469742970e970a942e942a9412940e7c427c3e7c167c1279d279ce79b679b299faf9fae9fa39fa29f109f0f9f059f049bcc9bcb9bc29bc19b339b329b2a9b29b3e213e1f3e0b3e093ce93ce73cdb3cd93667366536553653352735253519351748a6a5a6a4a6a0a69ea5d0a5cfa5cba5c99fae9fad9fa99fa89f0f9f0e9f0a9f09b4d414d3d4d2d4d294b974b934b854b813f533f513f453f413e153e133e093e05552e852e7d2e152e052855284d281d2814f87cf874f824f814f39cf394f364f35d33f5d3f5b3f533f513e1f3e1d3e153e1337973795378f378d36653663365d365b67ea67ea27e8a7e827c2a7c267c127c0a6f1e6f1a6f066efe6cba6cb66ca66c9ea9f0f9f0e9f049f029e739e729e6c9e6b9b329b319b299b279a929a919a8b9a8aa43

private theorem cap1111111010100011Accepted : Accepted table cap1111111010100011Box cap1111111010100011Tree := by
  decide +kernel

private def cap111111101010001Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1111111010100010Tree <*> cap1111111010100011Tree

private theorem cap111111101010001Accepted : Accepted table cap111111101010001Box cap111111101010001Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111111101010001Box 2 (midpoint cap111111101010001Box 2) = cap1111111010100010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111010100010Accepted
  · have h : rightBox cap111111101010001Box 2 (midpoint cap111111101010001Box 2) = cap1111111010100011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111010100011Accepted

private def cap11111110101000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111101010000Tree <*> cap111111101010001Tree

private theorem cap11111110101000Accepted : Accepted table cap11111110101000Box cap11111110101000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110101000Box 1 (midpoint cap11111110101000Box 1) = cap111111101010000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101010000Accepted
  · have h : rightBox cap11111110101000Box 1 (midpoint cap11111110101000Box 1) = cap111111101010001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101010001Accepted

private def cap11111110101001Box : Box := ![(9 / 8, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101010010Box : Box := ![(9 / 8, 23 / 20), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101010010Tree : Option PackedTree := decode 6 0x369e369e169c769c566e366e166d566d34a174a154a094a0747a747a5479947976d3c2d3bed38ad382cdc2cdbecda6cda2aa72aa6eaa4aaa42a5a2a59ea58ea58ad54e554dd549554854b454b3d4b1d4b152855284d281d28151e951e8d1e5d1e550ed38ed38ad336d32ecdaacda6cd8acd86aa4eaa4aa9f6a9eea592a58ea576a572d549d549553ed53dd4b254b1d4aed4ae52825281d279527851e651e5d1e251e1d169c569c169b169ad6845684368396837552555215511550d53f153ef53e553e36d362d35ad32ed326d072d06ed04ed046aa22aa1aa9eea9e6a7caa7c6a7b2a7aaab422b421b413b411b369b368b361b360a9f8a9f7a9eca9eaa963a962a95ca95ba6aa4aaa42a9eea9e6a7e2a7dea7b2a7aa940e940a93c293ba919e919a917a9176d4fc54fbd4f654f554b1d4b154ae54add233d233522f522ed1e5d1e551e1d1e1521a

private theorem cap111111101010010Accepted : Accepted table cap111111101010010Box cap111111101010010Tree := by
  decide +kernel

private def cap111111101010011Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111010100110Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 15 / 16)]

private def cap11111110101001100Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 29 / 32)]

private def cap11111110101001100Tree : Option PackedTree := decode 8 0xdb92db925b8d5b8cdaf6daf65af15af0d632d632562d562cd5afd5af55aa55a9db724b723b719b718b5ecb5ebb5e1b5e0ae42ae41ae3bae3aad78ad77ad71ad70b5c855c835c775c755af15aef5ae35ae158c958c758b358b156bd56bb56a756a543b71ab719b705b704b5e2b5e1b5d2b5d1ae3cae3bae2dae2cad72ad71ad6aad69b5c795c775c5b5c595ae55ae35ad55ad358b558b35893589156a956a75691568f45b8cdb8c5b88db885b315b30db2e5b2dd71dd71d571ad71a56e856e7d6e5d6e55b711b710b704b702b65cb65bb653b651ae35ae34ae2cae2badcbadcaadc3adc2aad98ad986d94ed946d786d782d746d742b742b73eb70eb70ab5c6b5c2b5a6b5a29ae3bae3aae35ae34add0adcfadcbadcaac59ac58ac51ac50abbdabbcabb8abb7b5c6b5c695c595c575b975b955b875b8558a358a15891588f5771576f57675765556e856e7d6e1d6e156b8d6b856b4d6b455ded5de55d9d5d955a9d5a955a3d5a3521ab5edb5ecb5e2b5e1b4e2b4e1b4d8b4d7ab5fab5eab54ab53aa92aa91aa88aa87b6bd96bd76bc36bc169c369c169af69ad56bd56bb56a756a555235521550f550d5daf15af0dae95ae8da6c5a6bda65da6555aa55a9d5a455a3d5445543d53dd53d5b5e1b5e0b5d1b5d0b4d7b4d6b4cab4c9ab53ab52ab47ab46aa87aa86aa7aaa79ad1ac65ac64ac5aac59ab5fab5eab54ab53a696a695a68ba68aa5c2a5c1a5b7a5b6b58c958c758b358b156bd56bb56a756a54fd14fcf4fc54fc34eb54eb34ea94ea769fa29f9e9f8a9f869d6a9d669d529d4e9a569a529a2a9a269706970296da96d68758b558b35893589156a956a75691568f4fc74fc54fb94fb74eab4ea94e9d4e9b69f8e9f8a9f729f6e9d569d529d3a9d369a2e9a2a99fe99fa96de96da96b296ae8ac59ac58ac48ac47abbdabbcabb3abb2a7e2a7e1a7dba7daa798a797a793a792b577b57795767576556a756a5568f568d4f314f2f4f274f254ea94ea74e9b4e994d3f153f0d3edd3ed53cc53cbd3c9d3c953455344d33f533ed301d30152ff52feda798a797a793a792a754a753a74da74ca603a602a5fea5fda5b6a5b5a5aba5aaa43556bf56bb56a956a5552555215511550d4b854b814b6f4b6b4a074a0549f949f56ad52ad4ead22ad1eaa22aa1ea9eea9ea96de96da96b296ae93f293ee93c293bed5a9d5a955a3d5a35543d543553d553cd2db52dad2d5d2d5527dd27d5277d2775688

private theorem cap11111110101001100Accepted : Accepted table cap11111110101001100Box cap11111110101001100Tree := by
  decide +kernel

private def cap11111110101001101Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (29 / 32, 15 / 16)]

private def cap11111110101001101Tree : Option PackedTree := decode 5 0x36e4d6e4b6e396e356bdd6bdb6bc96bc558cd58cb58b958b556c156bf56ad56a96dc72dc6edc1edc1ad792d78ed752d74eb172b16eb12eb12aad5aad56ad2aad26db8ddb8d5b835b82daf1daf15ae9dae9562dd62d56255624d5aad5aa55a4d5a456ad7bad7b6d792d78ad38ed38ad366d362ad82ad7ead5aad52aa4eaa4aaa26aa22daf25af15aea5ae95a6cda6c5a66da65d5ab55aa55a555a45544d544553ed53dd46b19ab196b172b16aad82ad7ead5aad529a5e9a5a9a369a2e970e970a96e696ded62e562dd625d62555ab55aad5a555a4d346d3465340d34052dcd2dc52d752d6dac5bac5aac4aac49ab55ab54ab49ab48a68ca68ba680a67fa5b8a5b7a5ada5acad55b055afd5ab55aa5549d5495544d54452e1d2e152dcd2dbd2825281d27ed27e5ab56ab54ab4aab48aa89aa88aa7daa7ba5b9a5b7a5aea5aca4fda4fca4f2a4f0a88

private theorem cap11111110101001101Accepted : Accepted table cap11111110101001101Box cap11111110101001101Tree := by
  decide +kernel

private def cap1111111010100110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11111110101001100Tree <*> cap11111110101001101Tree

private theorem cap1111111010100110Accepted : Accepted table cap1111111010100110Box cap1111111010100110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1111111010100110Box 3 (midpoint cap1111111010100110Box 3) = cap11111110101001100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110101001100Accepted
  · have h : rightBox cap1111111010100110Box 3 (midpoint cap1111111010100110Box 3) = cap11111110101001101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110101001101Accepted

private def cap1111111010100111Box : Box := ![(9 / 8, 23 / 20), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111010100111Tree : Option PackedTree := decode 6 0x36e716e6f6e4d6e4b6bfd6bfb6bdd6bdb58ed58eb58cd58cb56e156df56c156bf6d7fad7f6d7bad7b6d3c6d3c2d38ed38aadc2adbead82ad7eaa76aa72aa4eaa4a9ac76ac75ac66ac65ab70ab6fab60ab5fa6a6a6a5a697a696a5d1a5d0a5c3a5c2b56e156df56c156bf553b5539552755254ba34ba14b874b854a174a154a094a0748b737b736b731b72fb5fdb5fcb5f7b5f5ac75ac74ac6fac6dab6fab6eab69ab67b6e636e616e4b6e496bef6bed6bdb6bd958df58dd58cb58c956d356d156bf56bd6dcc2dcbedc92dc8ed7dad7d6d7b2d7aeb1bab1b6b192b18eada2ad9ead7aad76b56bfb6bf96bdb6bd769e169df69c569c156df56dd56bf56bb55395537552555214d63ad63a5637d636d5b7d5b755b4d5b3d352d3525350534f52e852e7d2e5d2e4dac6fac6eac65ac64ab69ab68ab5fab5ea6a0a69fa696a695a5cba5caa5c2a5c1b58dd58db58c958c756d156cf56bd56bb4d3f4d3d4d2b4d294b954b934b834b815aab6fab6eab5fab5daa9caa9baa92aa90a5d0a5cfa5c2a5c0a50aa509a503a502a43

private theorem cap1111111010100111Accepted : Accepted table cap1111111010100111Box cap1111111010100111Tree := by
  decide +kernel

private def cap111111101010011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1111111010100110Tree <*> cap1111111010100111Tree

private theorem cap111111101010011Accepted : Accepted table cap111111101010011Box cap111111101010011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111111101010011Box 2 (midpoint cap111111101010011Box 2) = cap1111111010100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111010100110Accepted
  · have h : rightBox cap111111101010011Box 2 (midpoint cap111111101010011Box 2) = cap1111111010100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111010100111Accepted

private def cap11111110101001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111101010010Tree <*> cap111111101010011Tree

private theorem cap11111110101001Accepted : Accepted table cap11111110101001Box cap11111110101001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110101001Box 1 (midpoint cap11111110101001Box 1) = cap111111101010010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101010010Accepted
  · have h : rightBox cap11111110101001Box 1 (midpoint cap11111110101001Box 1) = cap111111101010011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101010011Accepted

private def cap1111111010100Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11111110101000Tree <*> cap11111110101001Tree

private theorem cap1111111010100Accepted : Accepted table cap1111111010100Box cap1111111010100Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1111111010100Box 0 (midpoint cap1111111010100Box 0) = cap11111110101000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110101000Accepted
  · have h : rightBox cap1111111010100Box 0 (midpoint cap1111111010100Box 0) = cap11111110101001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110101001Accepted

private def cap1111111010101Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (15 / 16, 1)]

private def cap1111111010101Tree : Option PackedTree := decode 7 0xdb9d5b9cdb94db945a79da795a72da7253545353d34cd34c5286d28652835282db739b738b728b726b4f2b4f1b4e4b4e3ac77ac76ac67ac66aa9eaa9daa94aa93b58ef58ed58cf58cd553d553b552955274d4f4d4d4d314d2f4a194a174a0b4a0943b729b728b709b708b4e5b4e4b4cfb4cea699a698a683a682a506a505a4f4a4f3b6e516e4d6e116e0f6bdf6bdd6bab6ba958cf58cd5899589756c356c1569756956d7bed7bad756d752d392d38ed33ad336ad86ad82ad2ead2aaa52aa4ea9faa9f69ac67ac66ac4cac4bab61ab60ab4bab4aa698a697a682a681a5c4a5c3a5afa5aeb56c356c1569756955529552754fd54fb4b894b874b5f4b5d4a0b4a0949e749e5486ad3ced3c6d396d38ecdcacdc6cdb2cdaa9436942e941a94128f528f4e8f3a8f32da72da725a67da6759b659b5d9b259b1d2835282d27a5279d1e751e6d1e351e2db4e4b4e3b4ceb4cdb36bb36ab363b362a505a504a4f3a4f2a3cda3cca3c5a3c4ad1a6a8a6a7a699a698a50da50ca506a5059bce9bcd9bc49bc39a959a949a8e9a8db4d4f4d4d4d314d2f4a194a174a0b4a093f613f5f3f493f473ceb3ce93cdd3cdb67ec27ebe7e927e8e79d679d279ba79b66f366f326f0e6f0a6a526a4e6a366a32874d334d314d074d054a0d4a0b49e949e73f4b3f493f233f213cdf3cdd3cc13cbf67e967e927e467e4279be79ba7982797e6f126f0e6ec66ec26a3a6a366a0a6a068a698a697a682a681a5c4a5c3a5afa5ae9fa49fa39f909f8f9f069f059ef29ef1b4b894b874b5f4b5d4a0b4a0949e749e53e0d3e0b3de53de33cdd3cdb3cbf3cbd4cfd24fd1cfc84fc7cf834f82cf794f78cde1cde14dd84dd7cd95cd954d8c4d8bd9f069f059ef29ef19e6e9e6d9e5f9e5e9b2b9b2a9b189b179a8d9a8c9a819a80a4354a1b4a174a0d4a0947a947a7479d4799352b3527351d351933233321331733136941a941693d293ce8f3a8f368f1a8f166a3a6a366a0a6a06662e662a660e660ad282d2825279d27951e6d1e651e2d1e24d46cd464d40cd404cc54cc4ccc14cc0d688

private theorem cap1111111010101Accepted : Accepted table cap1111111010101Box cap1111111010101Tree := by
  decide +kernel

private def cap111111101010Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1111111010100Tree <*> cap1111111010101Tree

private theorem cap111111101010Accepted : Accepted table cap111111101010Box cap111111101010Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111111101010Box 3 (midpoint cap111111101010Box 3) = cap1111111010100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111010100Accepted
  · have h : rightBox cap111111101010Box 3 (midpoint cap111111101010Box 3) = cap1111111010101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111010101Accepted

private def cap111111101011Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (7 / 8, 1)]

private def cap111111101011Tree : Option PackedTree := decode 8 0x36e8f6e8d6e876e8369fb69f969f369ef4d654d634d5d4d594a2f4a2d4a274a236dd0edd0adceadce6d3e6d3e2d3ced3ca9aba9ab69aa29a9e944e944a94369432dba15ba0db9cdb9c5a7c5a7bda795a78d356d3565353d35352895288d2865285d6ad3f6d3f2d3ced3c6cdeacde6cdcacdc6945e945a9436942e8f728f6e8f528f4e9a6b2a6b1a6aea6aca517a516a513a5119bd89bd79bd49bd29a9f9a9e9a9b9a99b4d5d4d5b4d514d4f4a274a254a1b4a1937a937a7379d379b35373535352b352969ab69ab29a9e9a9a944a94469432942e6f4e6f4a6f366f326a6a6a666a526a4eb54a2f4a2d4a1b4a1747b947b747a947a7353f353d352b35273331332f3323332148b746b745b741b740b4fcb4fbb4f7b4f6a6b1a6b0a6aca6aba516a515a511a510b6e8b6e896e816e7f69f769f569ed69eb4d614d5f4d574d554a2b4a294a214a1f5dba0dba05b9c5b9bda7bda7b5a78da78563dd63d563b563ad5515550d54ed54e5ac7bac7aac76ac75aaa2aaa1aa9daa9ca6aca6aba6a6a6a5a511a510a50ba50aa2dd02dcfedcdedcdad812d80ed7f6d7f2b1eab1e6b1d6b1d2adceadcaadbeadbadb025b01dafedafe5a7b5a7ada785a77d5b9d5b955b7d5b75550d550554e554dd358f558f358eb58e956e756e556df56dd4d574d554d4b4d494ba94ba74ba14b9f6adceadcaadbeadbaaa86aa82aa72aa6e9752974e9742973e9442943e942a942690d5a7e5a7d5a7bda7ad9bcd9bbd9bb59ba528b528a5288d287d1edd1ecd1ec51eb5b4f7b4f6b4f1b4f0b376b375b371b370a511a510a50ba50aa3d8a3d7a3d3a3d2b69ed69eb69e169df66eb66e966e166df4a214a1f4a154a1347af47ad47a547a35a34d634d614d594d574a2d4a2b4a234a2137af37ad37a537a3353d353b3533353169ac29abe9aae9aaa945694529442943e6f5a6f566f466f426a766a726a626a5eba6aca6aba6a6a6a5a511a510a50ba50a9bd29bd19bcc9bcb9a999a989a939a92b4d574d554d4b4d494a214a1f4a154a133f673f653f5d3f5b3cf13cef3ce73ce567ece7eca7eba7eb679e279de79ce79ca6f466f426f2e6f2a6a626a5e6a4a6a4686a945a94529446943e8f6e8f668f628f5a6a7a6a726a666a5e665e66566652664ed288d287d285d284d1ec51eb51e9d1e8cd4ccd4bcd49cd48ccca4cc9ccc84cc75443

private theorem cap111111101011Accepted : Accepted table cap111111101011Box cap111111101011Tree := by
  decide +kernel

private def cap11111110101Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111111101010Tree <*> cap111111101011Tree

private theorem cap11111110101Accepted : Accepted table cap11111110101Box cap11111110101Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11111110101Box 2 (midpoint cap11111110101Box 2) = cap111111101010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101010Accepted
  · have h : rightBox cap11111110101Box 2 (midpoint cap11111110101Box 2) = cap111111101011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101011Accepted

private def cap1111111010Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11111110100Tree <*> cap11111110101Tree

private theorem cap1111111010Accepted : Accepted table cap1111111010Box cap1111111010Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1111111010Box 1 (midpoint cap1111111010Box 1) = cap11111110100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110100Accepted
  · have h : rightBox cap1111111010Box 1 (midpoint cap1111111010Box 1) = cap11111110101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110101Accepted

private def cap1111111011Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 63 / 100), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap11111110110Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap11111110110Tree : Option PackedTree := decode 8 0xf7b477b3f7b077aff66e766df66cf66c64846483e480647fe3696368e367e3675c908c907c900c8ffc6d2c6d1c6cfc6ceb37ab379b372b371b1a1b1a0b19eb19da3bd9fbd97bd7fbd77b7dbb7d7b7c7b7bf241f241723ff23f71f171f131f031efaf6fb76faf6f8f6f7f66df66d766c766be3e2e3e263e063df6368e36863676366d3920f920b91ff91fb8f8b8f898f818f7d66f366ef66e366df64c764c564bf64bd71f171f131f031efb1b471b431b3b1b36c98ec98ac97ec97ac682c67ec676c67290fbd83bd7fbd2bbd23b7cbb7c7b79bb797240323ff23af23a71f071f031ed31ecaf6f976f8f6f376f2f66cf66c7667f66763e0e3e063da63d96367e3676362e36253920191ff91f591f18f838f818f778f7566e566e366d966d564c164bf64b764b5723eb23e323af23a71eef1eeb1ed31ecacdb2cdaacd92cd8ac96ec96ac952c94aac7c1c7c0c7b4c7b2c6cfc6cec6c5c6c4b260b25fb254b252b19eb19db194b193a477aff7af77ac77abf6f8f6f876f676f5e47fe47f647c647be3e063dfe3dd63dcdef5eef5def57ef56edf0edefedebedeac8fec8fdc8f7c8f6c7bfc7bec7b9c7b8afbd63bd5fbd23bd1fb7b3b7afb797b79323e323df23a723a31eeb1ee71ecb1ec6f7abf7ab77a3f7a376f5f6f576f276f1ebb46bb3ebad6baceb166b15eb13eb135d768d767d75ad759d62cd62bd627d626c8f7c8f6c8e8c8e7c7b9c7b8c7b1c7b0a1aedf1edefedecedeaecd8ecd7ecd4ecd3c7c0c7bec7bac7b8c6cec6cdc6cac6c9bdbd9dbd5dbcbdbc7d9a9d9a7d99dd9998f758f718f658f618d958d938d898d8551c8ffc8fdc8f8c8f6c7c0c7bec7bac7b8b371b36fb36ab368b25fb25eb25ab258b91f191ef91d391d18f758f738f658f6366d566d366c566c364b564b364a564a3723df23db23a3239f1ee71ee31ec71ec2cda6cda2cd86cd82c966c962c946c942b58f818f7d8f758f718d9d8d9b8d958d9364bf64bd64b564b1633b63396333633171eeb1ee31ecb1ec31b2b1b271b131b0ac96ac962c94ac942c666c662c64ec646a21a

private theorem cap11111110110Accepted : Accepted table cap11111110110Box cap11111110110Tree := by
  decide +kernel

private def cap11111110111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (3 / 4, 7 / 8), (7 / 8, 1)]

private def cap111111101110Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 1)]

private def cap1111111011100Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap11111110111000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101110000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101110000Tree : Option PackedTree := decode 6 0xe580657fe578e578647fe47f647c647bda78da785a71da7159b8d9b859b559b4dcaffcafecaf0caeec8fec8fdc8f7c8f6bd85bd84bd77bd75bc00bbffbbfbbbfab7b0b7b097aef7aeb780177ff77f777f569e169df69c569c166e166df66d366d143caf1caf0cadbcadac8f8c8f7c8e9c8e8bd78bd77bd63bd62bbfcbbfbbbf0bbefb7af17aef7ac77ac577f977f777e177df69c769c5699b699766d566d366c566c34657865776573e572e4ebe4eb64e7e4e75ebbdebadeb6deb5de535e52de4f5e4edcae7cae5cadacad8c9cfc9cec9c5c9c3bd6dbd6bbd62bd60bc9ebc9dbc95bc93ab275f275b2717270f23df23db23a3239ef29af296f256f24eefeeefeaefbeefba9bd77bd75bd6dbd6bbca6bca5bc9ebc9db4e2b4e0b4d8b4d6b422b421b41cb41bb7adb7ad77ac57ac1793d793b792b792769b169ad69976993683968376827682355e535e52de4ade49ddfdddfd5df7ddf75a115a10da09da08d9b4d9b459b0d9b0521a

private theorem cap111111101110000Accepted : Accepted table cap111111101110000Box cap111111101110000Tree := by
  decide +kernel

private def cap111111101110001Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111011100010Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 15 / 16)]

private def cap11111110111000100Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 29 / 32)]

private def cap111111101110001000Box : Box := ![(23 / 20, 93 / 80), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 29 / 32)]

private def cap111111101110001000Tree : Option PackedTree := decode 7 0x3801980177ff57ff37d4f7d4d7d397d376e4b6e496e356e336bdb6bd96bc56bc37002f002affe6ffe2fcfafcf6fcc6fcc2e6e6e6e2e6b6e6b2e4b2e4aee48ae486df9f5f9edf98df985f535f52df4ddf4d5c965c95dc915c90dc595c58dc555c54d373737371735b735972597257724572436e496e476e336e316cd16ccf6cc56cc36e4b2e4aee48ae486e2cae2c6e2aae2a6d9a2d99ed98ad986d7b2d7aed786d78290effeaffe6ff86ff82fa72fa6efa1efa1ae6bae6b6e65ee65ae2aee2aae27ee27adcd75cd6dccbdccb5c55dc555c4fdc4f5b8d5b8cdb82db825af15af0dae95ae8d17ff37ff17fdd7fdb7e637e617e517e4f735b73597343734172457243723372316ffbaffb6ff82ff7afca2fc9efc76fc6ee686e682e65ae652e466e462e43ee436abf31bf30bf1dbf1bbe9bbe9abe86be85b922b921b90fb90db8aab8a9b89eb89da6e6b6e6b2e686e682e48ae486e466e462dc66dc62dc46dc42d98ad986d972d96edcd0dcd05ccb5cca5c8cdc8c5c87dc86db88db885b825b815b2e5b2ddb29db28d572457243721f721b71557153713d713b6cc56cc36ca76ca36bc36bc16ba36ba1486afa9efa9afa72fa6ef5def5daf5b6f5b2d7b6d7b2d78ad786d38ad386d362d35edf535f52df4ddf4d5ebb5ebadeb65eb5daf65af5daf0daf05a70da705a6bda6b577d397d377d0f7d0d7adb7ad97ac57ac36bc56bc36ba56ba369b169af699769956fa6efa6afa1afa16f5b2f5aef586f582e2aae2a6e27ae276dfdadfd6dfc2dfbedc555c54dc4f5c4edbfb5bfadbf85bf7daf0daf05ae8dae85a6bda6b5a655a64d0d1

private theorem cap111111101110001000Accepted : Accepted table cap111111101110001000Box cap111111101110001000Tree := by
  decide +kernel

private def cap111111101110001001Box : Box := ![(93 / 80, 47 / 40), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 29 / 32)]

private def cap111111101110001001Tree : Option PackedTree := decode 7 0x39c379c359c039c0198d198cf98af98ad801980177ff57ff37d4f7d4d7d397d377386b3867380337ff344f344b33ff33fb0f130f0f0ec30ebf0c370c330bef0beae689e689667fe67f6633e633662b662ae186e186617de17d613b613ae1356134d3878987878761875f861b861985f785f5801780157ff37ff17e7d7e7b7e637e6170c370c330bef0beb09db09d709ab09a6fcfafcf6fcc6fcc2fa9afa96fa6efa6a90f38073803377f377b315f315b30f330ef0ec70ec30e630e5f09af09ab0963095ee1d8e1d861cc61cbe135e135612c612bdffd5ffcdff0dff05f4e5f4ddf43df43519c019bff9be39be199ff99fd99e999e78761875f8747874585f785f585e185df737c737c3377b377733d333cf33a3339f0e8f0e8b0e5f0e570bc30bbf0b970b8eaccffccfecce8cce7cc56cc55cc3bcc3ac2fbc2fac2e5c2e3c26ac269c257c256a70ec30ebf0e8f0e8b0bef0beb0bc30bbeffe6ffe2ffbaffb6fcc6fcc2fca2fc9ee1d1e1d161cbe1cae1786177e172e171dff75ff6dff05fef5f945f93df8edf8dd585f785f585cb85c784d584d384af84ad7e637e617e3b7e377d377d357d0d7d0b486b31a3319f315f315b2bc32bbf2b9f2b9afa9efa9afa72fa6ef5def5daf5b6f5b2e633e633662b662ae577e57765736572df535f52df4ddf4d5ebb5ebadeb65eb5d798af98ad9879987795cf95cd95b595b37d397d377d0f7d0d7adb7ad97ac57ac37315b315730ef30eb2b9b2b972b672b6309ab09a7095f095b05fb05f705df05dae1356134e12be12b60bf60bee0bbe0bb5f4ddf4d5f435f42deb65eb5deb0deb050d1

private theorem cap111111101110001001Accepted : Accepted table cap111111101110001001Box cap111111101110001001Tree := by
  decide +kernel

private def cap11111110111000100Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111111101110001000Tree <*> cap111111101110001001Tree

private theorem cap11111110111000100Accepted : Accepted table cap11111110111000100Box cap11111110111000100Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11111110111000100Box 0 (midpoint cap11111110111000100Box 0) = cap111111101110001000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101110001000Accepted
  · have h : rightBox cap11111110111000100Box 0 (midpoint cap11111110111000100Box 0) = cap111111101110001001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101110001001Accepted

private def cap11111110111000101Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (29 / 32, 15 / 16)]

private def cap11111110111000101Tree : Option PackedTree := decode 5 0xe70e670de701e700e634e634662ce62be006e0065ffe5ffd5f545f53df4f5f4e5ce03ce02cde1cde0cc59cc58cc3ecc3dbffcbffbbfe3bfe2be9ebe9dbe8abe89b9c059c039bc19bbf98b198af987b98797ff77ff57fc57fc37d3b7d397d137d0f5acc69cc68cc3ecc3ccaf1caf0cadbcadabea8bea7be8abe88bd78bd77bd63bd6200103c700370032fff2ffeafaa2fa9efa7afa72dc9adc96dc72dc6ad7bad7b6d792d78adffe5ffddff1dff15f4f5f4edf455f44db8e5b8ddb83db835af25af1daea5ae9dbffbbffabfe2bfe1be9dbe9cbe89be87b71bb71ab706b705b5e3b5e2b5d3b5d2ad5f545f53df4f5f4e5ebc5ebbdeb75eb6daf75af6daf25af15a71da715a6cda6c5be9ebe9cbe8abe87bd6ebd6dbd63bd62b5e4b5e2b5d4b5d2b4d9b4d8b4cdb4cba88

private theorem cap11111110111000101Accepted : Accepted table cap11111110111000101Box cap11111110111000101Tree := by
  decide +kernel

private def cap1111111011100010Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11111110111000100Tree <*> cap11111110111000101Tree

private theorem cap1111111011100010Accepted : Accepted table cap1111111011100010Box cap1111111011100010Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1111111011100010Box 3 (midpoint cap1111111011100010Box 3) = cap11111110111000100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110111000100Accepted
  · have h : rightBox cap1111111011100010Box 3 (midpoint cap1111111011100010Box 3) = cap11111110111000101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110111000101Accepted

private def cap1111111011100011Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111011100011Tree : Option PackedTree := decode 6 0x39c639c619c399c3798f198ef98d398d1803b8039801b80197d717d6f7d517d4f731e331df31a731a32c032bff2bc72bc2fae2fadefaa2fa9ef61af616f5e2f5de9c01dc01cc00dc00cbeb8beb7bea8bea7b738b737b726b725b5feb5fdb5eeb5edb7d717d6f7d517d4f7b0d7b0b7af17aef6bfd6bfb6bdd6bdb69e369e169c769c548ce30ce2fce2ace28cc77cc76cc71cc6fc01cc01bc016c014beb7beb6beb1beafb9c559c539c379c3598e398e198d198cf802d802b801980177d637d617d4f7d4d738a738a3386b386731c331bf319f319b00570053002f002afac2fabefa9afa96b598ef98ed98e398df95ff95fd95f595f37d6f7d6d7d637d5f7b0b7b097b017aff731c731bf31a3319b2beb2be72bc32bbafac6fabefa9efa96f602f5fef5def5d6a380398037802d80297d6f7d6d7d637d5f6e6f6e6d6e636e5f6bfb6bf96bef6beb7005b00570033002efac6fac2fa9efa9adcc6dcc2dc96dc92d7ded7dad7b6d7b2e00ae00a6005e0055f585f57df535f52db985b97db925b91dafb5afadaf65af5d6afadefadafac6fabef616f612f602f5fed7f6d7f2d7ded7d6d3c2d3bed3aed3aadf58df57df53df52dec05ebfdebbdebadafbdafadaf6daf5da75da755a715a705443

private theorem cap1111111011100011Accepted : Accepted table cap1111111011100011Box cap1111111011100011Tree := by
  decide +kernel

private def cap111111101110001Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1111111011100010Tree <*> cap1111111011100011Tree

private theorem cap111111101110001Accepted : Accepted table cap111111101110001Box cap111111101110001Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111111101110001Box 2 (midpoint cap111111101110001Box 2) = cap1111111011100010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111011100010Accepted
  · have h : rightBox cap111111101110001Box 2 (midpoint cap111111101110001Box 2) = cap1111111011100011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111011100011Accepted

private def cap11111110111000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111101110000Tree <*> cap111111101110001Tree

private theorem cap11111110111000Accepted : Accepted table cap11111110111000Box cap11111110111000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110111000Box 1 (midpoint cap11111110111000Box 1) = cap111111101110000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101110000Accepted
  · have h : rightBox cap11111110111000Box 1 (midpoint cap11111110111000Box 1) = cap111111101110001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101110001Accepted

private def cap11111110111001Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101110010Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap111111101110010Tree : Option PackedTree := decode 6 0xf8f178f0f8e978e8f7aff7af77ac77abe580657fe578e578647fe47f647c647bdf1e1f1e0f1d1f1cfef5eef5def57ef56d99cd99bd98dd98bd76dd76cd768d767bb339b337b31bb317aedbaed9aed1aecf95ff95fd95e195dd91fd91fb91ef91ed43f1d2f1d1f1b4f1b3ef58ef57ef48ef47d98ed98dd975d974d769d768d75bd75abb31db31bb2ebb2e9aed3aed1aeb7aeb595e395e195b795b591f191ef91d391d1478e8f8e7f8e478e378367835f8327831ecc6ecc5ecc26cc16c2b6c2aec276c26df1c8f1c6f1b3f1b1f064f063f05af058d984d982d974d972d84ed84dd844d842abc1b3c1afc16bc163bd5fbd5bbd1fbd1b615b61576113610b5da35d9f5d6b5d669d98dd98bd984d982d856d855d84ed84dcaf0caeecae7cae5c9d7c9d6c9cfc9cebb309b305b2e9b2e5b09db09bb089b08595cf95cb95b595b1939f939d938b938756c2b6c2aec226c216bb46bb3ebad6bace4ebe4eb64e2e4e1e47be47b64746473d21a

private theorem cap111111101110010Accepted : Accepted table cap111111101110010Box cap111111101110010Tree := by
  decide +kernel

private def cap111111101110011Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (3 / 4, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111011100110Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 15 / 16)]

private def cap11111110111001100Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (7 / 8, 29 / 32)]

private def cap11111110111001100Tree : Option PackedTree := decode 8 0x3ed49ed47ece1ecdfe74be749e71be719bafdbafbbabfbabdb65db65bb631b62f7da8fda8bd9bfd9bbce93ce8fce33ce2f973b97379693968f8d038cff8cab8ca6f2e772e6f2d272d1f1a0719ff1957194eebeeebe6eaf6eaeed96ed966d8bed8b50fd9c3d9bfd8b3d8afce37ce33cdbbcdb7757f757b74a3749f6c636c5f6bf76bf2fb37fb377b15fb157a60fa607a44fa4472d272d1f2b0f2b07220721ff208f2085f4c1f4c0f489f488f38cf38bf36df36ce440e43fe411e410e32ae329e30ee30da79693968f95879583910390ff90479043757b7577749f749b7013700f6f8b6f86f220721ff208f20871957194f1877186ee026e01edf16df0ed8bed8b6d7e6d7dd21af3a5f3a4f38df38cf1d1f1d0f1c8f1c7db2edb2ddb18db17d98dd98cd984d983be749e747e719e717e3a1e39fe38fe38db65bb659b62fb62db319b317b307b3055f9c6f9c679b779b6f8e478e3f8d9f8d96d8c6d8bed7eed7e6cc26cc1ecba6cb9df38cf38bf36df36cf1c7f1c6f1b2f1b1e32ae329e30ee30de1c4e1c3e1b3e1b2bc655c653c61dc61bc389c387c367c365b62fb62db5f9b5f7b307b305b2e7b2e5434775fb75f7757f757b6cbb6cb76c636c5f386f386b3807380331a3319f315f315aeebeeebe6eaf6eaeee0e6e0dee026e01e9b169b0e9a569a4e938e938692de92d5dc1cdc1bdc04dc03db2ddb2cdb17db16d271d270d25bd25ad1b7d1b6d1a6d1a5a74d8b4d874d2b4d2749c749c3496f496b386b3867380337ff344f344b33ff33fae938e938692de92d68dbe8db68d368d2e689e689667fe67f6633e633662b662ad21eeafeeaf6e946e93ed8c6d8bed7eed7e69a5e9a56990e99068d3e8d368c7e8c75d34bd34ad321d320d1a7d1a6d18fd18ece01ce00cddfcddecc57cc56cc3ccc3ba3757b7577749f749b7013700f6f8b6f874d2b4d274c834c7f496f496b490749000040f6e026e01edf16df0ed8bed8b6d7e6d7de92de92d6920e92068d368d2e8c768c6d3a695a693a66da66ba4b7a4b5a49da49b9c019bff9be39be199ff99fd99e999e774cdb4cd74c834c7b493b49374907490337c737c3377b377733d333cf33a3339ead25bd25ad241d240d1a6d1a5d18ed18dccffccfecce8cce7cc56cc55cc3bcc3aa435b65db65bb631b62fb31bb319b309b30798d198cf98af98ad95e195df95cf95cd76cb76cb36c5f6c5b6633662f660f660b319f319b315b31572bbf2bbb2b9b2b96bdb18db17dafddafcd984d983d974d973cc57cc56cc3ccc3bcae7cae6cadacad9bb62fb62db5f9b5f7b307b305b2e7b2e5a34da34ba31da31ba11ba119a105a1037469b4697463b463742374233420b4207315b315730ef30eb2b9b2b972b672b628688

private theorem cap11111110111001100Accepted : Accepted table cap11111110111001100Box cap11111110111001100Tree := by
  decide +kernel

private def cap11111110111001101Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (3 / 4, 25 / 32), (29 / 32, 15 / 16)]

private def cap11111110111001101Tree : Option PackedTree := decode 4 0x3ed4bed49ece3ece1e74de74be71de71bbaffbafdbac1babfb65fb65db633b6317d9c7d9c3d8b7d8b3ce3bce37cdbfcdbb7583757f74ab74a36c676c636bff6bf6af3a6f3a5f36ff36ef1d2f1d1f1b4f1b3db2fdb2edaffdafdd98ed98dd975d974a775ff75fb7583757f6cbf6cbb6c676c633873386f380f380731a731a33167315eeeb06eafee956e946d8ced8c6d7fed7ee701e700e6f0e6efe62ce62be61f661e55b65fb65db5ffb5fbb31db31bb2ebb2e998d398d1987d987995e395e195b795b548

private theorem cap11111110111001101Accepted : Accepted table cap11111110111001101Box cap11111110111001101Tree := by
  decide +kernel

private def cap1111111011100110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11111110111001100Tree <*> cap11111110111001101Tree

private theorem cap1111111011100110Accepted : Accepted table cap1111111011100110Box cap1111111011100110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1111111011100110Box 3 (midpoint cap1111111011100110Box 3) = cap11111110111001100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110111001100Accepted
  · have h : rightBox cap1111111011100110Box 3 (midpoint cap1111111011100110Box 3) = cap11111110111001101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110111001101Accepted

private def cap1111111011100111Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (25 / 32, 13 / 16), (7 / 8, 15 / 16)]

private def cap1111111011100111Tree : Option PackedTree := decode 6 0x3ed8ded8bed4bed49e775e773e74de74bbb37bb35baffbafdb687b685b65fb65d7ceebcee7ce9bce97c78bc787c74bc7476d0f6d0b6cbf6cbb66776673663b66369dd9bdd9add7fdd7edb43db42db2fdb2ece31ce30ce1cce1bcc78cc77cc69cc68bb687b685b65fb65db33bb339b31db31b98f198ef98d398d1960195ff95e395e148f6c5f6c4f6bbf6b9f3b9f3b8f3b3f3b1dd9add99dd94dd92db42db41db3cdb3abed77ed75ed49ed47e767e765e74be749bb29bb27bafdbafbb679b677b65db65b7daebdae7da8fda8bcecbcec7ce93ce8f764f764b75f775f36cef6ceb6cb76cb2b5e773e771e767e763e3c3e3c1e3b7e3b5b685b683b679b675b339b337b32db32b7cecfcec7ce97ce8fc76fc76bc747c73f6cf36ceb6cbb6cb3665b66576637662ea3bb35bb33bb29bb25b685b683b679b6759c619c5f9c559c5198ef98ed98e398df77653764f75fb75f76cf36cef6cbb6cb738ab38a7386f386b31c731c331a3319eeec9eec96ebeeebe6d9ded9d6d96ed966714e714670d670ce6386637e633e63356b6d0b6d076cf36ceb6673666f665b665731df31db31c731bf2bff2bfb2beb2be6ed9e6d9d6d976d966ccb6ccaecc6ecc5e638e637e6346633657d657ce57865775443

private theorem cap1111111011100111Accepted : Accepted table cap1111111011100111Box cap1111111011100111Tree := by
  decide +kernel

private def cap111111101110011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1111111011100110Tree <*> cap1111111011100111Tree

private theorem cap111111101110011Accepted : Accepted table cap111111101110011Box cap111111101110011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111111101110011Box 2 (midpoint cap111111101110011Box 2) = cap1111111011100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111011100110Accepted
  · have h : rightBox cap111111101110011Box 2 (midpoint cap111111101110011Box 2) = cap1111111011100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111011100111Accepted

private def cap11111110111001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111111101110010Tree <*> cap111111101110011Tree

private theorem cap11111110111001Accepted : Accepted table cap11111110111001Box cap11111110111001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11111110111001Box 1 (midpoint cap11111110111001Box 1) = cap111111101110010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101110010Accepted
  · have h : rightBox cap11111110111001Box 1 (midpoint cap11111110111001Box 1) = cap111111101110011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101110011Accepted

private def cap1111111011100Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11111110111000Tree <*> cap11111110111001Tree

private theorem cap1111111011100Accepted : Accepted table cap1111111011100Box cap1111111011100Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1111111011100Box 0 (midpoint cap1111111011100Box 0) = cap11111110111000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110111000Accepted
  · have h : rightBox cap1111111011100Box 0 (midpoint cap1111111011100Box 0) = cap11111110111001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110111001Accepted

private def cap1111111011101Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (3 / 4, 13 / 16), (15 / 16, 1)]

private def cap1111111011101Tree : Option PackedTree := decode 7 0xfb647b63fb53fb5378f278f1f8ea78e9e719e719670f670ee5816580e579e5795f6c7f6c6f6a6f6a5f1e3f1e2f1d3f1d2ce32ce31ce1dce1ccb01cb00caf2caf1afda9fda9bd8bfd8bbc753c74fc6dbc6d7387b3877378f378b2bcf2bcb2b772b72fb537b52fb177b16f8e9f8e978daf8da6ec06ebfee95ee956cc7ecc76cbb6cbaddd80dd7fdd2bdd2ad98fd98ed976d975ce1dce1ccde2cde1caf2caf1cadccadba1af1e4f1e2f1d4f1d2ef60ef5fef5aef58cb02cb00caf3caf1c900c8ffc8fac8f8be3a9e3a7e36de36bdeb5deb3de95de9395e795e595bb95b991f591f391d791d57c74fc74bc6d7c6d3bd67bd63bd27bd232bcb2bc72b732b6f23e723e323ab23a6b4738cf38cb387b38772c0b2c072bcf2bcadceadce6dca6dca2d3ced3cad396d392e7196718e70ee70e6580e58065796578db9cdb9c5b945b93da795a78da725a7180084e79c3d9c3b9bc79bc595e795e595bb95b96e536e516e136e1169cb69c9699f699d738773873378b37872bcb2bc72b732b6f003b0036ff92ff8ef5e6f5e2f592f58ee0076006dff25ff1df54df545f45df455b945b935b845b83daf7daf75aeadaea5bea9bea8be8bbe8abd79bd78bd64bd63b5efb5eeb5d5b5d4b4e4b4e3b4ceb4cda4359605960195e795e3920191ff91f591f169e769e369cb69c766e566e366d966d572bcf2bcb2b772b7323eb23e723af23aad396d392d33ed33acdb2cdaecd92cd8ee5796578e56e656de47ce47c64756474da725a71da675a66d9b5d9b559b1d9b15688

private theorem cap1111111011101Accepted : Accepted table cap1111111011101Box cap1111111011101Tree := by
  decide +kernel

private def cap111111101110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1111111011100Tree <*> cap1111111011101Tree

private theorem cap111111101110Accepted : Accepted table cap111111101110Box cap111111101110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111111101110Box 3 (midpoint cap111111101110Box 3) = cap1111111011100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111011100Accepted
  · have h : rightBox cap111111101110Box 3 (midpoint cap111111101110Box 3) = cap1111111011101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111011101Accepted

private def cap111111101111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (13 / 16, 7 / 8), (7 / 8, 1)]

private def cap111111101111Tree : Option PackedTree := decode 8 0xfb6b7b6afb697b68f8f778f6f8f578f4e7216720e71f671e6586e5866584e583df6d2f6d1f6c8f6c6f1eaf1e9f1e4f1e2ce3ece3cce33ce31cb09cb07cb02cb00abc7bbc7b7c793c78bbda3bd9fbd83bd7f2c372c332c0b2c032423241f240323fe9ce42ce41ce3ece3ccb0dcb0ccb09cb07b747b746b743b741b4fdb4fcb4f9b4f7b9c7d9c7b9c679c6596139611960596036e876e856e756e7369f369f169e769e5738f738f338cb38c72c232c1f2c072c02dd0add06dce6dce2d3e2d3ded3cad3c6b5961b9619960596019211920f920191ff69fb69f969e769e366f566f366e566e348f6d5f6d4f6d1f6d0f1edf1ecf1e9f1e8ce41ce40ce3cce3bcb0ccb0bcb07cb06beda9eda7eda1ed9fe3d9e3d7e3d1e3cf9c819c7f9c779c7596179615960d960b5fb68fb687b637b62f8f4f8f478f178f0eed26ed1eecdeecd6cd16cd0ecceecce5dda4dda3dd9bdd9ad9a2d9a1d99dd99cce3cce3bce31ce30cb07cb06cb00caffa3db43db3fdb17db13cf0bcf07cee7cee3768f768b766b76676d2f6d2b6d0b6d06f9e179e0f9dcf9dc78f478f3f8f0f8f06da5eda56da16da0ecd0ecd06cce6ccdd3bb47bb45bb35bb33b697b695b685b6839c779c759c619c5f990198ff98ef98ed76d2f6d2b6d0b6d07668766836673666f320331ff31df31db2c1b2c172bff2bfa90d78f6f8f5f8f4f8f3f7b3f7b2f7b277b1658665856583e582e483e482e48264815f1e9f1e8f1e2f1e1ef64ef63ef5fef5ecb07cb06cb00caffc904c903c8ffc8febe3d1e3cfe3c3e3c1dec7dec5debddebb960d960b95ff95fd9207920591fd91fb5a39c839c819c799c7796199617960f960d6e8d6e8b6e836e8169f969f769ef69ed7390338ff38ef38eb2c2f2c2b2c1b2c16dd16dd12dd02dcfed3eed3ead3dad3d6bce3cce3bce31ce30cb07cb06cb00caffc026c025c01dc01cbd8abd89bd86bd85b804d804b803b80397b157b137b0d7b0b6e836e816e716e6f69ef69ed69e369e14671de71d67186717e640663fe63be63b6012e012600e600ddf605f5fdf5bdf5b5cc80cc7fcc77cc76cb06cb05caffcafebec0bebfbeb7beb6bd89bd88bd85bd84a7009700930073006efb02fafefadefadadd02dcfedcdedcdad812d80ed7f6d7f2df605f5fdf5bdf5b5ec4dec45ec2dec25b025b01dafedafe5a7b5a7ada785a77d21acb0ccb0acb07cb05c907c905c904c902b4fcb4fab4f7b4f5b379b377b376b374b960f960d960195ff9209920791ff91fd69ef69ed69e369e166ed66eb66e366e172c1b2c172bff2bfb240f240b23fb23f6d3dad3d6d3c2d3becdd6cdd2cdc2cdbeb443

private theorem cap111111101111Accepted : Accepted table cap111111101111Box cap111111101111Tree := by
  decide +kernel

private def cap11111110111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111111101110Tree <*> cap111111101111Tree

private theorem cap11111110111Accepted : Accepted table cap11111110111Box cap11111110111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11111110111Box 2 (midpoint cap11111110111Box 2) = cap111111101110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101110Accepted
  · have h : rightBox cap11111110111Box 2 (midpoint cap11111110111Box 2) = cap111111101111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111111101111Accepted

private def cap1111111011Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11111110110Tree <*> cap11111110111Tree

private theorem cap1111111011Accepted : Accepted table cap1111111011Box cap1111111011Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1111111011Box 1 (midpoint cap1111111011Box 1) = cap11111110110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110110Accepted
  · have h : rightBox cap1111111011Box 1 (midpoint cap1111111011Box 1) = cap11111110111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11111110111Accepted

def cap111111101Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap1111111010Tree <*> cap1111111011Tree

theorem cap111111101Accepted : Accepted table cap111111101Box cap111111101Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap111111101Box 0 (midpoint cap111111101Box 0) = cap1111111010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111010Accepted
  · have h : rightBox cap111111101Box 0 (midpoint cap111111101Box 0) = cap1111111011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1111111011Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover60
