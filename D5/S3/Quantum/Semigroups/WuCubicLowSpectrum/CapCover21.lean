import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover21

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap1110111001Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 63 / 100), (1 / 2, 5 / 8), (3 / 4, 7 / 8)]

private def cap11101110010Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (1 / 2, 5 / 8), (3 / 4, 7 / 8)]

private def cap111011100100Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (1 / 2, 9 / 16), (3 / 4, 7 / 8)]

private def cap1110111001000Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (1 / 2, 9 / 16), (3 / 4, 13 / 16)]

private def cap1110111001000Tree : Option PackedTree := decode 7 0x3dd53dd51dbf7dbf5dac1dabfdaa9daa7ad9fad9dac63ac61ab67ab65ab59ab5775b3f5b3b58c758c356cf56cb56b356af215f215b1f2b1f271cf71cf31cc31cbe8eea8eea7edfaedf9ed5fed5eed53ed52d6ced6cdd630d62fd5b2d5b1d5abd5aabad9dad9bac61ac5fab65ab63ab57ab5590ad90ab8f938f918e798e778e5f8e5d43edfbedfaed46ed44ed54ed53ed39ed38d631d630d5a6d5a5d5acd5abd5a1d5a0bac63ac61ab4dab4bab59ab57ab43ab418f958f938e438e418e618e5f8e298e27476fd76fcf6a2f6a1f6a9f6a9769c769be3e4e3e46390638fe397e3976389e38910003e6bb583b57fb553b54fb39bb397b387b38356cf56cb56b356af554f554b553b5536f6737672f670f670763cf63c76367635eaa9eaa96aa76aa6ea85ea856a826a81d3ab67ab65ab59ab57aaa7aaa5aa9daa9b8e7b8e798e618e5f8daf8dad8da98da77554f554b553b5537542f542b5413540f1b5f1b5b1b531b4f19db19d7199f199a91dabfdabddaa7daa5d8f1d8efd8d7d8d5ab65ab63ab57ab55aa15aa13aa07aa05756cb56c756af56ab542b5427540f540b1cf31cef1cbf1cbb19d719d3199b199687daa9daa7da73da71d8d9d8d7d8c5d8c3ab59ab57ab43ab41aa09aa07a9ffa9fd756b356af568756835413540f53ff53fb1cc31cbf1c531c4f199f199b197719728ed53ed52ed38ed37ec6bec6aec61ec60c72fc72ec713c712c666c665c65cc65bad1c857c856c7cac7c9c73dc73cc730c72fbb71bb70baf6baf5ba92ba91ba8bba8ab76e376e175ed75eb752575237517751565bf65bd64d164cf63e363e163cb63c94642b642ae3e4e3e4639e639de397e397596f596ed933d93358f858f7d8f258f1d78f958f938e438e418e618e5f8e298e2775ed75eb750b750975177515750174ff6ebdaebd6ea16ea12ea2eea2aea02e9fec9a2c99ec75ac756c796c792c72ac7268c7c9c7c8c720c71fc72fc72ec713c712b267b266b1d5b1d4b1e4b1e3b1c9b1c8ad639ee39e63986397e33b633ae333e3335d495d48dd45dd455d115d10dd0ddd0d5ba92ba91ba8bba8aba22ba21ba1bba1ab1f1b1f0b1e5b1e4b150b14fb143b142a31cf31cef1cbf1cbb19d719d3199b1996ea46ea42ea2aea26e886e882e86ae866dd48dd485d455d44dd10dd105d0d5d0cd8f858f7d8f258f1d8a7d8a758a158a0d0f1cc31cbf1c531c4f19a3199b19771972c796c792c72ac726c50ec50ac4e2c4dc200236397e3976389e38963336332e32e632dd8f258f1d8e4d8e458a158a0d89bd89b5688

private theorem cap1110111001000Accepted : Accepted table cap1110111001000Box cap1110111001000Tree := by
  decide +kernel

private def cap1110111001001Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (1 / 2, 9 / 16), (13 / 16, 7 / 8)]

private def cap11101110010010Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (1 / 2, 9 / 16), (13 / 16, 7 / 8)]

private def cap11101110010010Tree : Option PackedTree := decode 5 0x390b390b18f998f978e818e7f8e658e6376e776e575f175ef75297527751b751808011aedceedcaebe2ebdeea52ea4eea36ea32cb86cb82c9aac9a6c7cec7cac79ec79a8c858c857c7cbc7cac73fc73dc731c730bb72bb71baf7baf6ba93ba92ba8cba8b08008d76e576e375ef75ed752775257519751765c165bf64d364d163e563e363cd63cb43c7ccc7cbc723c722c732c731c716c715baf8baf7ba87ba86ba8dba8cba82ba81b75f175ef750f750d751b75197505750364d564d363b163af63cf63cd63996397463e5e3e563916390e398e398638ae38a5d7bdd7b5d435d42dd465d45dd40dd405baf7baf6ba86ba85ba8cba8bba81ba80b269b268b1d7b1d6b1e6b1e5b1cbb1caa1ac740c73fc732c731c678c677c66ac669ba94ba93ba8dba8cba24ba23ba1dba1c40008d75297527751b751974497447743b743963e763e563cf63cd62a562a3628b62894639fe39ee398e398633be33b6334e333dd49dd495d465d45dd11dd115d0e5d0dc00046ba93ba92ba8cba8bba23ba22ba1cba1bb1f2b1f1b1e6b1e5b151b150b144b143a1e3996398e38b638ae3356334e32fe32f5d46dd465d415d40dd0edd0e5d0c5d0bdba8dba8cba82ba81ba1dba1cba18ba17b1e7b1e6b1ccb1cbb145b144b13ab139a31cc71cc31c571c5319a7199f197b1976ea32ea2eea06ea02e872e86ee85ee85add465d45dd40dd405d0e5d0ddd0bdd0b58f358f2d8e5d8e558a258a1d89cd89c50d1

private theorem cap11101110010010Accepted : Accepted table cap11101110010010Box cap11101110010010Tree := by
  decide +kernel

private def cap11101110010011Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (1 / 2, 9 / 16), (13 / 16, 7 / 8)]

private def cap11101110010011Tree : Option PackedTree := decode 6 0xf755f75576fef6fe76b1f6b176ab76aaeb68eb686b19eb196adb6adaead76ad6820246d6d1d6d0d633d632d5b6d5b5d5aed5adc859c858c7ccc7cbc740c73fc732c73104048c3baabbaa7b7f3b7efb58bb583b557b5535b435b3f58cb58c756d756cf56b756b0202236b686b67eb196b18eadaead9ead6ead6642c642be3e5e3e5639fe39ee398e3980404460fb7f7b7f3b523b51fb55bb557b4efb4eb58cf58cb56a3569f56bb56b7568f568aeb19eb196ad46ad3ead76ad6ead1ead163e663e5e391e39163996398e38b638ad1dbf9dbf7da8fda8ddaabdaa9da75da73ac65ac63ab4fab4dab5bab59ab45ab43758cb58c7569f569b56b756b3568b56871f2f1f2b1c8b1c871cc71cc31c571c5286bb58fb587b55bb557b3a3b39fb38fb38b56db56d356bb56b7555755535543553ef6747673f671f671763df63d76377636eaaaeaaa6aa86aa7ea876a866a836a82d3ab6dab6bab5dab5baa1daa1baa0daa0b8e818e7f8e658e638cf18cef8cd58cd288811876b0f6b076aaf6aa7673f67376717670eada6ad9ead6ead66aaa6aa9eaa7eaa75ece7ece6ece2ece1ec7aec79ec6dec6cd554d553d54fd54ed50cd50bd505d504a756d356cf56b756b35553554f553f553b1cfb1cf71cc71cc31b631b5f1b571b52eaaa6aa9eaa7eaa76a866a85ea82ea82636c636be36ae36a633be33b6334e333d21f6ab76aaf69df69d76377636f6327631ead76ad6ead1ead16a836a82ea80ea805d5aed5add5a3d5a2d506d505d501d500c732c731c716c715c66ac669c65fc65ea3b557b553b4ebb4e7b1b7b1b3b18fb18b56b756b3568b568754175413540353feead6ead66ad16ad0ea82ea826a806a7fe398e398638ae38a6334e333e32f632ed0d1

private theorem cap11101110010011Accepted : Accepted table cap11101110010011Box cap11101110010011Tree := by
  decide +kernel

private def cap1110111001001Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101110010010Tree <*> cap11101110010011Tree

private theorem cap1110111001001Accepted : Accepted table cap1110111001001Box cap1110111001001Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111001001Box 0 (midpoint cap1110111001001Box 0) = cap11101110010010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110010010Accepted
  · have h : rightBox cap1110111001001Box 0 (midpoint cap1110111001001Box 0) = cap11101110010011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110010011Accepted

private def cap111011100100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111001000Tree <*> cap1110111001001Tree

private theorem cap111011100100Accepted : Accepted table cap111011100100Box cap111011100100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011100100Box 3 (midpoint cap111011100100Box 3) = cap1110111001000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001000Accepted
  · have h : rightBox cap111011100100Box 3 (midpoint cap111011100100Box 3) = cap1110111001001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001001Accepted

private def cap111011100101Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (3 / 4, 7 / 8)]

private def cap1110111001010Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap11101110010100Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap11101110010100Tree : Option PackedTree := decode 7 0xe43ce43be436643563fce3fbe3f863f75dc4ddc3ddbfddbf5d8edd8ddd8a5d89dc86cc86ac863c862c7f0c7eec7e8c7e7bb7fbb7ebb78bb77bb14bb13bb0ebb0dab1fe71fdf1fc31fbb1d931d8b1d5f1d56ec76ec6eec52ec4eeab6eaaeea8eea8ae3f863f763f463f3e3abe3aae3a763a6dd8a5d89dd875d86dd51dd515d4e5d4dd46ee26ee1eedfeedfaec76ec6eec52ec4ecbfecbfacbcecbcaca4aca46ca2aca26ddbfddbf5dbc5dbbdd8a5d89dd875d86d979d97959755974d9455944d9425941d5763b763776297627755b7557754775456525652365156513641d641b640b64096ec52ec4eec3aec36ea8eea8aea72ea6eca2aca26ca12ca0ec816c812c7f2c7eea2321df21db218b21871fdf1fdb1f9f1f9aee1eee1aeddeeddaec6eec6aec36ec32e3fbe3fb63f3e3f363b163b0e3a6e3a65d8ddd8d5d86dd865d55dd555d4ddd4d53770f770d76ef76ed755775557537753565fd65fb65d365d1641b641963f763f543c863c862c857c856c7e8c7e7c7dfc7debb78bb77bb71bb70bb0ebb0dbb05bb04b8fd18fcf8fbf8fbd8e9d8e9b8e7b8e79761d761b760b760975397537752575234ddbc5dbbddb8ddb85d875d86dd82dd8259755974d96fd96f59425941d93f593edbb0ebb0dbb05bb04ba9cba9bba92ba91b284b283b27eb27db1fcb1fbb1f1b1f0a464316430e42b642ae3a6e3a6639e639dddbbddbb5db85db7dd4ddd4d5d48dd485bb77bb76bb70bb6fba9bba9aba91ba90b2e9b2e8b2deb2ddb1fbb1fab1f0b1efa1ac764c762c757c755c6ebc6e9c6e5c6e4baadbaabbaa3baa2ba63ba62ba5eba5db8eaf8eab8e9d8e9b8dcb8dc98dc18dbf754775457539753774bd74bb74b374b156375e374e370636fe3496348e3416340dd31dd315d2cdd2c5d195d18dd14dd1453755d75577539753774c774c574b374b1641d641b63f963f7636763656357635500013ae98ee98ae966e962e8cae8c6e8a6e8a2c6cec6cac6aec6aac59ec59ac56ec56a918ec58ec38e9b8e998dd38dd18dbf8dbd755775557537753574c574c374b174af71ba71ba31b7f1b7b1a471a431a071a02e98ae986e962e95ee8c6e8c2e8a2e89e9baabbaaaba9bba9aba31ba30ba28ba27b20db20cb1fbb1fab166b165b15ab159a1e3a763a6e39ee39e6370636fe36be36b5d4e5d4ddd495d48dd2cdd2c5d285d27dc6e0c6dfc6d7c6d6c682c681c676c675ba59ba58ba50ba4fba29ba28ba22ba21a6ea72ea6eea4aea46e966e962e942e93ec7f2c7eec7c6c7c2c6aec6aac69ac696dd2cdd2c5d285d27dd14dd145d115d10d8d5d8d558d358d2d8add8ad58a858a7d231d371d331cf31cef1a071a0319d719d2ea6eea6aea46ea42e8a2e89ee886e882dd4ddd4d5d48dd485d145d13dd10dd1058fdd8fd58f858f7d8ad58acd8a7d8a750d1

private theorem cap11101110010100Accepted : Accepted table cap11101110010100Box cap11101110010100Tree := by
  decide +kernel

private def cap11101110010101Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap111011100101010Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap111011100101010Tree : Option PackedTree := decode 7 0xf6c5f6c576be76bdf6817680f67c767beaea6ae9eae56ae4eab7eab76ab36ab2ded8aed89ed7bed7aed01ecffecf7ecf6d5d3d5d2d5c9d5c8d56ed56dd565d564afb5f7b5ebb5cbb5c7b3e3b3dbb3c3b3bf572b5723570756ff559b559355775572000232ed02ecffecf8ecf6ec9aec99ec91ec90d56fd56dd566d564d525d523d51ed51dbd9f1d9edd9e1d9dfd923d921d911d90faacdaac9aabbaab9aa3daa3baa31aa2d51d5d5d5d2d5cad5c8d56fd56dd566d564c764c762c757c755c6ebc6e9c6e5c6e480009dab95ab91ab83ab7faacdaac9aabbaab98eaf8eab8e9d8e9b8dcb8dc98dc18dbf56ab7eab6eab36ab26a92ea91ea8f6a8ee375e374e372e37263496348e3456344dd566d564d55dd55cd51ed51dd518d516c6e5c6e4c6e0c6dfc68ac689c682c681a88ed89ed88ed7aed79ecffecfeecf6ecf5d5d2d5d1d5c8d5c7d56dd56cd564d563bdaf5daf3dae3dadfd9edd9ebd9dfd9ddab91ab8fab7fab7daac9aac7aab9aab757680767f7677f677764cf64c7643f6436ab6eab66aae6aadea91ea916a8b6a8ac000463aba5aba3ab7fab7daadbaad9aab9aab78ec58ec38e9b8e998dd38dd18dbf8dbd755b755b35573556f548f548b545b54571ba71ba31b7f1b7b1a471a431a071a0290fb5cbb5c7b5a7b5a3b3c3b3bfb3afb3ab570756ff56eb56e7557755735563555ef6b4f6b476b076aff675f67576737672eadd6adcead9ead96aac6aabeaa9eaa955d9e1d9dfd9d7d9d5d911d90fd903d901aabbaab9aab1aaafaa31aa2daa25aa237b3afb3abb39bb397b207b203b1e7b1e35563555f554f554b544b5447542f542aa3ab85ab7fab67ab65aabdaab9aaa7aaa58e9d8e9b8e7b8e798dc18dbf8daf8dad10011b557b5573554f554b5463545b542f542b1b831b7f1b5f1b5b1a0b1a0719db19d60002311dae3dadfdabfdabdd9dfd9ddd9cbd9c9ab7fab7dab65ab63aab9aab7aaa5aaa37b3bfb3bbb397b393b21fb21bb1e3b1df5573556f554b5547545b5457542b54269d5c0d5bed5b2d5b1d517d515d50ad509c74dc74cc73cc73bc681c680c675c67488008c1a

private theorem cap111011100101010Accepted : Accepted table cap111011100101010Box cap111011100101010Tree := by
  decide +kernel

private def cap111011100101011Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap111011100101011Tree : Option PackedTree := decode 7 0x3dd9bdd99dd7fdd7ddc5ddc5bdc47dc45add5add3adc1adbfacbfacbdaca9aca77bb33bb2fbafbbaf7b8b7b8b3b88bb8875ba75ba35b7f5b7b597b5977594f594abeebfeebdeeb5eeb4ee23ee21ee1bee1ad6e0d6ded6d7d6d6d654d652d64bd64aabb8bbb8b7b88fb88bb62fb62bb5f3b5ef597f597b5953594f5753574f572b5726f716f71677117710f6c576c4f6bdf6bd6b2f6b2eeb29eb296ae9eae96ae4eae457dc47dc43dc37dc35dafbdaf5dae5dae3aca9aca5ac97ac95ab95ab91ab83ab7e1001191d6ead6e9d6e0d6dfd65fd65ed654d653c879c878c86cc86bc7f9c7f8c7f0c7efbadd3add1adbfadbdacbdacbbaca7aca590f190ef90d790d58ff18fef8fdf8fdd5eb706b6f6b6beb6b6b2a6b296b25eb25643664356431e43163f863f763f463f3d5acbfacbdaca9aca7aba9aba7ab95ab938ff38ff18fe18fdf8ec98ec78eaf8ead7597b5977594f594b574f574b572757231fe31fdf1fbf1fbb1d8f1d8b1d5b1d56bd654d652d64bd64ad5cad5c8d5c1d5bfc7f0c7eec7e8c7e7c757c755c74ec74da88eecbeec9eebdeebcee2cee2bee21ee20d6e8d6e7d6ded6ddd65dd65cd652d651bdd7bdd79dd69dd67dc43dc41dc35dc33adbdadbbadadadabaca5aca3ac95ac93577167715f710f71076c4f6c476bd76bceb2eeb2e6b296b28eae96ae8eae46ae3dee21ee20ee1aee19ed7aed79ed71ed6fd652d651d64ad649d5c8d5c7d5bfd5bea8eb746b73eb6b6b6aeb2eeb2e6b256b24e43be43b64316430e3fbe3fb63f3e3f35d65dd65cd64ad649d5d2d5d1d5bfd5bec7f7c7f6c7e7c7e6c762c761c74dc74ca43eeb5eeb4eea9eea8ee1bee1aee11ee10d6d7d6d6d6cfd6ced64bd64ad641d640bdc37dc35dc2ddc2bdae5dae3dad3dad1ac97ac95ac8dac8bab83ab7fab75ab737b85bb857b847b843b5a7b5a3b583b57f591b59175907590356eb56e756cf56caa3adafadadad9fad9dac97ac95ac83ac8190c790c590af90ad8fd18fcf8fbf8fbd7592f592b59075903570b56ff56cf56cb1fa31f9f1f7f1f7b1d3b1d371cf71cf02002311dd69dd67dd51dd4fdc35dc33dc21dc1fadadadabad9dad9bac95ac93ac81ac7f7b86bb867b843b83fb5c7b5bfb57fb57b592b5927590358ff56ff56fb56cb56c69d6d6d6d5d6ced6cdd5c0d5bed5b2d5b1c862c861c856c855c74dc74cc73cc73b08008c1a

private theorem cap111011100101011Accepted : Accepted table cap111011100101011Box cap111011100101011Tree := by
  decide +kernel

private def cap11101110010101Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011100101010Tree <*> cap111011100101011Tree

private theorem cap11101110010101Accepted : Accepted table cap11101110010101Box cap11101110010101Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101110010101Box 1 (midpoint cap11101110010101Box 1) = cap111011100101010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100101010Accepted
  · have h : rightBox cap11101110010101Box 1 (midpoint cap11101110010101Box 1) = cap111011100101011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100101011Accepted

private def cap1110111001010Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101110010100Tree <*> cap11101110010101Tree

private theorem cap1110111001010Accepted : Accepted table cap1110111001010Box cap1110111001010Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111001010Box 0 (midpoint cap1110111001010Box 0) = cap11101110010100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110010100Accepted
  · have h : rightBox cap1110111001010Box 0 (midpoint cap1110111001010Box 0) = cap11101110010101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110010101Accepted

private def cap1110111001011Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap11101110010110Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100101100Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 819 / 1600), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100101100Tree : Option PackedTree := decode 6 0x38ed18ecd8eb78eb38ddd8ddb8dcf8dcd75657561754f754b74cb74c974c174bf71d6f1d671d431d3f1b9f1b9b1b8b1b86ea9eea96ea7aea76e982e97ee96ee96aac6eec6edc6e2c6e1c695c694c684c683ba65ba64ba5bba5aba34ba33ba2cba2aa6eacaeac2ea9eea96e996e992e982e97ec84ec842c81ec81ac6d6c6d2c6c6c6c2dd53dd52dd4f5d4edd305d2fdd2ddd2d5903d90358ffd8ff58d8d8d858d6d8d65574cb74c974b774b57469746774597455636b6369635b635962d362d162bb62b948c766c764c759c757c6edc6ebc6e6c6e5bab0baadbaa5baa3ba64ba63ba5fba5eb8eb38eaf8e9f8e9d8dcd8dcb8dc38dc1754b7547753b753974bf74bd74b574b356376e375e370e370634a63496341e3415d325d31dd2d5d2cdd19dd195d155d14d37561755b754b754774c974c774bf74bd6421641d640d640b636963676361635f6ea96ea8eea76ea72e97ee97ae96ae966c81ac816c7fac7f2c6c2c6bec6b2c6aeaba64ba63ba5aba59ba33ba32ba2aba29b1b4b1b3b1acb1abb168b167b15cb15ba43c750c74fc748c747c6e2c6e1c6ddc6dcba9eba9dba99ba98ba5bba5aba56ba55b8e918e8f8e818e7d8dbb8db98db38db1753375317529752774ad74ab74a574a3563716370e36ce36c63426341e33c633bdd2ddd2d5d295d28dd165d155d125d11d3753d753b7529752774b774b574a574a363ff63fd63e763e5635b63596351634f6e96ee96ae94ae946e8b2e8aae892e88ec6b6c6b2c6a2c69ec576c572c54ac546918e9f8e9d8e8f8e8d8dc38dc18db98db7753b75397531752f74b574b374ab74a971d1f1d1b1cfb1cf71b731b6f1b631b5eea62ea5eea4eea4ae956e952e946e942ac6e1c6e0c6d8c6d7c683c682c677c676ba5aba59ba51ba50ba2aba29ba23ba22a6ea76ea72ea4eea4ae96ae966e946e942c7fac7f2c7cac7c6c6b2c6aec69ec69add2d5d2cdd28dd285d155d14dd11dd1158d658d5d8d3d8d358ae58add8a8d8a8521a

private theorem cap111011100101100Accepted : Accepted table cap111011100101100Box cap111011100101100Tree := by
  decide +kernel

private def cap111011100101101Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100101101Tree : Option PackedTree := decode 7 0x390fb90f990e190df8ffb8ff98fe98fe7771d771b77077705764576437631762f721f321ef21bf21bb1ff31fef1fcf1fcaee36ee32ee0aee06ec86ec7eec5eec5abc870c86ec865c864c7f4c7f2c7ebc7e9bb83bb81bb7abb79bb18bb16bb10bb0fab1ff71ff31fd31fcf1da31d9f1d6f1d6aec8aec86ec62ec5eeacaeac6ea9eea9ae3fe63fde3f9e3f963b3e3b363ad63acdd90dd8fdd8bdd8b5d58dd585d535d52d78fe98fe58fd78fd38eb78eb38ea18e9f7631762d7621761f754f754b753d753b51bb8ebb8dbb83bb82bb22bb21bb18bb17b303b302b2f7b2f6b296b295b28eb28db771b7719770577037643763f762f762d6605660365ed65eb652b6529651b65195ddc1ddc0ddbd5dbcdd8c5d8b5d885d87d97bd97ad9765975d947594659435942d5764576417631762d75657561754f754b652d6529651d651964276421640f640c80013aec62ec5aec42ec3eea9eea96ea7aea76ca3aca32ca1aca16c81ec81ac7fec7faa2321ef21eb21bb21b71fef1feb1fcb1fc6ee32ee2eee06ee02ec7eec7aec5aec56e43d643ce436e43663fd63fce3f8e3f85dc5ddc4ddc05dbfdd8f5d8edd8add8a5790dd90d990c990c78fe58fe18fd38fd1770376ff76f376f1762d7629761f761d563fde3fd63f963f8e3b363b2e3ace3ac5d8fdd8f5d8b5d8add585d57dd52dd525c7fac7f9c7f1c7f0c765c764c758c757bb1ebb1dbb15bb14baafbaadbaa4baa3af1fcb1fc31fa71fa31d671d5f1d3f1d3aec5aec52ec3eec3aea96ea8eea76ea72a37719771777037701763f763d762d762b6603660165eb65e965296527651965176ee2eee26ee02edfeec7aec76ec56ec52cc02cbfecbd2cbceca4eca4aca2eca2abbb81bb7fbb79bb78bb16bb14bb0fbb0eb2f5b2f3b2ebb2eab28cb28ab285b284aaec82ec76ec5aec52eac2eab6ea96ea8eca52ca4aca32ca2ac842c83ac81ac816000275d8b5d8a5d87dd875d52dd51dd4edd4e594659455942d94259035902d8ff58fe5443c865c864c859c858c7ebc7eac7e1c7e0bb7abb79bb73bb72bb10bb0fbb07bb0604009d8fd78fd38fcb8fc98ea18e9f8e918e8f7621761f76177615753d753b7533753171f971f931f871f831d231d1f1d031cfaec2eec2aec1eec1aea66ea62ea52ea4ea376f576f376e776e57621761f760f760d65d965d765c365c1650d650b650164ff6ec42ec3eec1eec1aea7aea76ea52ea4eca1aca16ca02c9fec7fec7fac7cec7ca9190c990c790b190af8fd58fd18fc18fbf76f376f176e576e3761f761d760d760a10013b1fa71fa31f931f8f1d3f1d3b1d1f1d1aec3eec3aec2aec26ea76ea72ea62ea5ee3f263f1e3f063efe3a3e3a3639f639edd855d84dd835d82dd4c5d4bdd49dd49546ede6ede2edcaedc6ec3eec3aec1aec16cbaecbaacb82cb7eca16ca12c9fec9fadd87dd875d835d82dd4edd4e5d49dd495942d942593fd93f58ff58fe58f958f8d21a

private theorem cap111011100101101Accepted : Accepted table cap111011100101101Box cap111011100101101Tree := by
  decide +kernel

private def cap11101110010110Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011100101100Tree <*> cap111011100101101Tree

private theorem cap11101110010110Accepted : Accepted table cap11101110010110Box cap11101110010110Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101110010110Box 1 (midpoint cap11101110010110Box 1) = cap111011100101100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100101100Accepted
  · have h : rightBox cap11101110010110Box 1 (midpoint cap11101110010110Box 1) = cap111011100101101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100101101Accepted

private def cap11101110010111Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100101110Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100101110Tree : Option PackedTree := decode 7 0x3db1fdb1ddb05db03da0dda0bd9f9d9f7abb5abb3ab9dab9baae9aae7aad5aad37b63bb637b607b5ffb417b413b3efb3eb5767575f5737573355cf55c755a755a2bed82ed80ed74ed73ecfcecfaecf3ecf1d5ced5ccd5c4d5c3d56ad568d561d55f40009cbb41bb413b3f3b3ebb273b26fb24fb24b55d355c755ab55a354a3549b5483547ef67e767d7679f678f649f6497645f6456ab56ab46ab0eaafea906a8fea8d6a8cd47576b5763573b573355d355c755ab55a31da31d9b1d6f1d671bbb1bb71b9f1b99000276ae76ae66ae26ae1eab56ab46ab0eaafe3ade3ace3a863a7e373e37363716370d5aae9aae5aac3aac1aa51aa4daa35aa338ddd8ddb8dc58dc38d2b8d298d098d06a001388ed8ded8ced7fed7eed04ed03ecfaecf9d5d7d5d6d5ccd5cbd571d570d568d567bdb19db17dafddaf9da07da05d9f3d9f1abadaba9ab97ab95aae1aadfaacfaacd5f6c076bef6b9f6b9767d767c7678f6786ae66ae56ae1eae0eab46ab36aafeaaec0004a000475da09da05d9f5d9f1d937d935d925d923aae3aadfaad1aacdaa4daa4baa3faa3d7b3ebb3e3b3c7b3c3b24bb247b22bb22355a3559b557f5577547f547b54675462a3abb1ababab99ab95aae3aadfaad1aacd8ecd8ec98eb38eaf8ddb8dd78dcd8dcb80013b5733572b570f570755a3559b557f55771d671d5f1d3f1d3b1b9b1b971b871b82ad571d56fd568d566d526d525d51fd51ec6edc6ebc6e6c6e5c694c692c68bc68abaad1aacdaabfaabbaa3faa3daa33aa318dcd8dcb8dc38dc18d178d158d078d05510fb5d3b5cfb5afb5abb3cfb3c7b3b7b3b35713570f56f356ef5587557f556b5566f6b5f6b576b1f6b0f676f67676747673eade6addeadb6ada6aad6aaceaaaeaaa55d9e7d9e5d9d1d9cfd917d915d8f7d8f5aac3aac1aaabaaa9aa35aa33aa1daa18808138eae26ae1eade6addeab0eaafeaad6aace3a863a7e3a463a3e3716370e36ee36e5d5bcd5bbd5b6d5b4d55ad559d555d554c748c747c740c73ec6ddc6dcc6d9c6d8ab5587558355575553546b5467543b54331b8b1b871b671b631a131a0f19e319dd0002711dae7dae5dad5dad3d9e3d9e1d9d9d9d7ab87ab83ab77ab75aabfaabbaab3aab17b5abb5a7b587b583b3b3b3afb39fb39b56ef56eb56d356cf556755635553554eaecf1ecf0ecececebec8aec88ec82ec81d55fd55dd559d558d519d518d513d512bd9d9d9d7d9cfd9cdd905d903d8f5d8f3aab3aab1aaa9aaa7aa27aa25aa19aa1751d5c3d5c1d5bbd5bad55fd55dd559d558c74fc74ec747c746c6e1c6e0c6dcc6dbbab77ab75ab69ab67aab3aab1aaa9aaa78e8f8e8d8e7d8e7b8db98db78db18daf56ab06aaf6aaa6aa9ea8cea8c6a866a85e370e370636c636be341e341633be33b40004a0004721a

private theorem cap111011100101110Accepted : Accepted table cap111011100101110Box cap111011100101110Tree := by
  decide +kernel

private def cap111011100101111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap1110111001011110Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (9 / 16, 19 / 32), (13 / 16, 7 / 8)]

private def cap1110111001011110Tree : Option PackedTree := decode 5 0x3dd6fdd6ddd57dd55dc3ddc3bdc27dc25adb5adb3ada3ada1ac9dac9bac87ac8408093bb87bb873b863b85fb5d3b5cfb5afb5ab593b59335923591f5713570f56f356eef70c770bf709f70976b5f6b576b1f6b0eb246b23eb21eb216ade6addeadb6ada5475b6b5b675b475b43593b5937590f590b21972193216721631faf1fab1f871f80101276b276b266b246b23eae26ae1eade6adde3f5e3f4e3f2e3f263a863a7e3a463a3dd648d647d643d642d5bcd5bbd5b6d5b4c7e5c7e4c7e1c7e0c748c747c740c73ea88eeb6eeb5eeaaeea9ee1dee1bee12ee11d6d9d6d7d6d0d6cfd64dd64bd642d64108089ddc39dc37dc2fdc2ddae7dae5dad5dad3ac99ac97ac8fac8dab87ab83ab77ab757b85fb85bb84bb847b5abb5a7b587b583591f591b590b590756ef56eb56d356cea3adb3adafada1ad9fac9bac97ac85ac8390c990c790b190af8fd58fd18fc18fbe10113b5933592f591f591b570f570756ef56eb1fa71fa31f931f8f1d3f1d3b1d1f1d1aeb23eb236b216b20eaddeadd6ada6ad9e3f263f1e3f063efe3a3e3a3639f639ed443

private theorem cap1110111001011110Accepted : Accepted table cap1110111001011110Box cap1110111001011110Tree := by
  decide +kernel

private def cap1110111001011111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (19 / 32, 5 / 8), (13 / 16, 7 / 8)]

private def cap1110111001011111Tree : Option PackedTree := decode 6 0x3dda5dda3dd87dd85dc65dc63dc51dc4fadddaddbadc9adc7acc7acc5acb3acb17bb47bb43bb0bbb07b8c7b8c3b89fb8975bb75bb35b8f5b8b598b59875963595abeec3eec1eeb7eeb6ee28ee26ee1eee1cd6e4d6e2d6dad6d9d659d657d64ed64c04049cbb8cbb8c7b8a3b89fb63fb63bb60bb607598f598b59675963576b5767573b5736f718f7187713f712f6c776c6f6c0f6bfeb316b30eb2c6b2b6aeceaebeae6eae657dc51dc4ddc3ddc39db05db01dae9dae7acb3acafac9dac99ab9dab99ab89ab868881391d6eed6edd6e4d6e3d663d662d659d658c87dc87cc870c86fc7fdc7fcc7f4c7f3baddbadd9adc7adc5acc5acc3acb1acad90f990f790df90dd8ff98ff78fe78fe55eb726b716b6d6b6ceb2ceb2beb276b26643864376432e43263fa63f963f5e3f482004e5acc7acc5acb3acb1abb5abb3ab9dab9b8ffb8ff98fe98fe78ed18ecf8eb78eb57598b59875963595b5767575f573757331ff31fef1fcf1fcb1d9f1d9b1d6b1d66bd659d657d64ed64cd5ced5ccd5c4d5c3c7f4c7f2c7ebc7e9c75bc759c750c74f40009c88eed0eecfeec1eec0ee30ee2fee25ee24d6ecd6ebd6e2d6e1d661d660d656d655bdd9fdd9bdd81dd7fdc5fdc5ddc49dc47add7add5adc3adc1acc1acbfacabaca95f760f75ff75b775af7137711f70e770deb716b706b6ceb6beb2beb2a6b266b2584044e5dc61dc5fdc4bdc49db1bdb19daffdafdacc3acc1acadacababafabadab99ab977b8bfb8bbb893b88fb633b62fb5fbb5f35983597f59575953575b5753572f572abee26ee23ee1cee1bed80ed7ded73ed72d657d654d64cd64bd5ccd5cad5c3d5c10400888809e8eb766b75eb716b70eb30eb306b2b6b2ae43de43d64376436e3fde3fd63f963f8dd6ebd6ead6e1d6e0d660d65fd655d654c87ac879c86dc86cc7fac7f9c7f1c7f0af5b8b5b835b675b5f595f59535933592f21bb21b32193218f1fcb1fc31fa71fa0200272d661d660d656d655d5d7d5d6d5ccd5cbc7fbc7fac7f2c7f1c766c765c759c758bacc1acbfacabaca9abadaba9ab97ab958ff58ff38fe38fe18ecb8ec98eb18eaf5eb2beb2a6b266b25eae66ae56ae1eae0e3f963f863f4e3f463ace3abe3a7e3a740004e443

private theorem cap1110111001011111Accepted : Accepted table cap1110111001011111Box cap1110111001011111Tree := by
  decide +kernel

private def cap111011100101111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111001011110Tree <*> cap1110111001011111Tree

private theorem cap111011100101111Accepted : Accepted table cap111011100101111Box cap111011100101111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011100101111Box 2 (midpoint cap111011100101111Box 2) = cap1110111001011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001011110Accepted
  · have h : rightBox cap111011100101111Box 2 (midpoint cap111011100101111Box 2) = cap1110111001011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001011111Accepted

private def cap11101110010111Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011100101110Tree <*> cap111011100101111Tree

private theorem cap11101110010111Accepted : Accepted table cap11101110010111Box cap11101110010111Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101110010111Box 1 (midpoint cap11101110010111Box 1) = cap111011100101110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100101110Accepted
  · have h : rightBox cap11101110010111Box 1 (midpoint cap11101110010111Box 1) = cap111011100101111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100101111Accepted

private def cap1110111001011Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101110010110Tree <*> cap11101110010111Tree

private theorem cap1110111001011Accepted : Accepted table cap1110111001011Box cap1110111001011Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111001011Box 0 (midpoint cap1110111001011Box 0) = cap11101110010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110010110Accepted
  · have h : rightBox cap1110111001011Box 0 (midpoint cap1110111001011Box 0) = cap11101110010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110010111Accepted

private def cap111011100101Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111001010Tree <*> cap1110111001011Tree

private theorem cap111011100101Accepted : Accepted table cap111011100101Box cap111011100101Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011100101Box 3 (midpoint cap111011100101Box 3) = cap1110111001010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001010Accepted
  · have h : rightBox cap111011100101Box 3 (midpoint cap111011100101Box 3) = cap1110111001011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001011Accepted

private def cap11101110010Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111011100100Tree <*> cap111011100101Tree

private theorem cap11101110010Accepted : Accepted table cap11101110010Box cap11101110010Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11101110010Box 2 (midpoint cap11101110010Box 2) = cap111011100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100100Accepted
  · have h : rightBox cap11101110010Box 2 (midpoint cap11101110010Box 2) = cap111011100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100101Accepted

private def cap11101110011Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (1 / 2, 5 / 8), (3 / 4, 7 / 8)]

private def cap111011100110Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (1 / 2, 9 / 16), (3 / 4, 7 / 8)]

private def cap111011100110Tree : Option PackedTree := decode 8 0x3277cf77cef702f7027755f75576fef6fe6bcc6bcbeb1ceb1c6b68eb686b19eb195335e635e5f58e758e35b475b4358cf58cb248f248b1f531f4f216721631f331f2e913be77be73b813b80fbaabbaa7b7f3b7ef5e5f5e5b58e358df5b435b3f58cb58c699af2faf2dac71ac6fada1ad9fac65ac63924592438fa78fa590b190af8f978f954871193248f248b1f531f4f216721631f331f2ef03af036ebfaebf6edceedcaebe2ebde99781d781b75fd75fb76e776e575f175ef6705670364e564e365c365c164d564d3489924592438fa78fa590b190af8f978f95781b781975fb75f976e576e375ef75ed4cbc0dbc0cbafdbafcbb72bb71baf7baf6b381b380b271b270b2e0b2dfb269b268a4388893be73be6fb80fb80bbaa7baa3b7efb7eb5e5b5e5758df58db5b3f5b3b58c758c299af2daf2bac6fac6dad9fad9dac63ac61924392418fa58fa390af90ad8f958f9348efa4efa3ee0aee09eea8eea7edfaedf9d79bd79ad63cd63bd6ced6cdd630d62fbaf37af35ac79ac77ad9dad9bac61ac5f925392518fb38fb190ad90ab8f938f914388c9924392418fa58fa390af90ad8f958f937819781775f975f776e376e175ed75eb4cbc0cbc0bbafcbafbbb71bb70baf6baf5b380b37fb270b26fb2dfb2deb268b267a46494e49463ece3ec642b642ae3e4e3e45e08de085d80dd805db85db7dd7add7a5bc11bc10bb01bb00bb70bb6fbaf5baf4b389b388b277b276b2deb2ddb267b266a1c443

private theorem cap111011100110Accepted : Accepted table cap111011100110Box cap111011100110Tree := by
  decide +kernel

private def cap111011100111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (9 / 16, 5 / 8), (3 / 4, 7 / 8)]

private def cap1110111001110Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap11101110011100Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 63 / 100), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap11101110011100Tree : Option PackedTree := decode 7 0xe691e691658de58d651de51d65156514dfa2dfa25eca5ec9de705e6fde69de695bf45bf44bd94bd93bce0bcdfbcd3bcd2b66eb66db50ab509b451b450b440b43fa3348b34872c6b2c6728eb28e728a728a2d9b6d9b2d426d422d142d13ed0fed0fab9962596239267926594559453925592537b1b7b197833783179a779a5782578234cbd8dbd8cbc19bc18bcd3bcd2bc12bc11b501b500b392b391b440b43fb38ab389a4658d658ce49e649de514e5146494e4945ec9dec95e0f5e0ede695e68de08de085bd93bd92bc1ebc1dbcd2bcd1bc11bc10b509b508b39bb399b43fb43eb389b388a1aca3bca3aca2aca29c951c94fc942c941bce0bcdfbcd3bcd2bc31bc2fbc22bc21b92a3929f9291928f90f390ef90d990d57863785f7851784f7713770f76ff76fd72523251f250b250721b321ab218f218af0a2f09ef08af086edfeedfaede2eddea379c179bf79a779a57863785f7845784368a368a16881687f675d675b6741673f6f0c6f0bef08af086ee2aee1eede2eddecebaceb6ce82ce7ecbfecbfacbaacba42002311947594739453945190ef90ed90c590c379bf79bd79a579a3770f770d76ef76ed6f37ef37af34af346ee1eee1aeddeeddad142d13ed0fed0facbfacbf6cba6cba287945594539255925390c790c590af90ad79a779a57825782376f176ef76e376e16f34ef34af04af046ede2eddeedc6edc2d102d0fece2ace26cbaacba6cb7ecb7a8ca29ca28c929c928c862c861c856c855b43fb43eb389b388b2e9b2e8b2deb2ddad1

private theorem cap11101110011100Accepted : Accepted table cap11101110011100Box cap11101110011100Tree := by
  decide +kernel

private def cap11101110011101Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 63 / 100), (9 / 16, 5 / 8), (3 / 4, 13 / 16)]

private def cap11101110011101Tree : Option PackedTree := decode 7 0x3ea01e9ffe3fbe3f7e1f9e1f5e1d5e1d3b86bb869b359b357b193b18fb179b17640011b70d770d366b366af6327631f62f362ef348f348b2c6f2c6b28ef28eb28ab28a68f4fff4fef1fbf1f9f0faf0f9f0e9f0e8cd22cd21cb1acb19ca3aca39ca29ca28ae78f9f8f977d777d6f8757874f7d2f7d26cd36cd2ebd1ebd16c5e6c5debce6bcdd33669b66975e8f5e8b62f362ef5e735e6f2c4b2c4724cf24cb28ab28a724ab24a6913c7cbc7c7beb7beb3c3a7c3a3be93be8f669766935e8b5e8762ef62eb5e6f5e6a99b34bb349af45af43b177b175af37af3596239621926592639453945192539251486bc3f3c3ebc3abc3a7bf2bbf23bef3beef6327631f62f362ef5eef5ee75eb35eaef7e577e477e0f7e077677765f75ff75eebddebdcebd96bd8eb756b746b706b6f040046efc1efc0efbcefbbeebfeebdeeb5eeb4d7b2d7b1d7acd7abd6e0d6ded6d7d6d6a8ec64ec63ec5e6c5debddebdcebd66bd5e51de51d65156514e4a8e4a7e4a164a0dd7bbd7b9d7b2d7b1d6ead6e8d6e0d6dec951c94fc948c947c879c877c86cc86abaf65af63af59af57adc1adbdadafadad9291928f9285928390d990d590c790c5511e1f5e1f3e1d3e1d1df91df8fdf77df75b18fb18db177b175af73af71af57af557bf23bf1fbeefbeebbb2fbb27bad3bacf5ee75ee35eaf5eab5ba35b9f5b5b5b569d8c7d8c6d8bbd8bad7b9d7b8d7abd7aaca3aca39ca29ca28c94fc94ec941c940baf73af71af57af55add1adcfadadadab929f929d9283928190ef90ed90c590c3487e1d5e1d3df4bdf49df79df77df39df37b179b177af39af37af59af57af2daf2b7bef3beefbe73be6fbad7bad3baa7baa35eb35eaf5e5b5e575b5f5b5b5b3f5b3a9d8bcd8bbd79cd79bd6d8d6d6d6cfd6ceca2aca29c92ac929c863c862c857c85608008c3c3a7c3a3be93be8fbad3bacfbaa3ba9f62ef62eb5e6f5e6b5b5b5b575b3b5b36ec5dec5d6bcdebcd6b6b6b6aeb676b66e514e5146494e49464316430e42b642ad0d1

private theorem cap11101110011101Accepted : Accepted table cap11101110011101Box cap11101110011101Tree := by
  decide +kernel

private def cap1110111001110Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101110011100Tree <*> cap11101110011101Tree

private theorem cap1110111001110Accepted : Accepted table cap1110111001110Box cap1110111001110Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111001110Box 0 (midpoint cap1110111001110Box 0) = cap11101110011100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110011100Accepted
  · have h : rightBox cap1110111001110Box 0 (midpoint cap1110111001110Box 0) = cap11101110011101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110011101Accepted

private def cap1110111001111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap11101110011110Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 63 / 100), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100111100Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100111100Tree : Option PackedTree := decode 7 0x3947f947b9467946592ab92a79299929579c979c579b779b5786b786778597855728cf28cb28b328af2533252b2513250ef36ef36af356f352f0b2f0aaf092f08eac955c954c94cc94bc87dc87cc870c86fbc35bc34bc2cbc2bbb8ebb8dbb83bb82b92a992a79297929590f990f790df90dd7869786778577855771b7719770577035e4a664a564a264a1e43864376432e4325e165e155e125e11ddc1ddc0ddbd5dbcd46f392f38af36ef36af0d6f0cef0b2f0aad156d14ed126d122cecacec2cea6ce9ede6dde6d5e6ade6a5e165e155e125e11da24da245a215a20d9d4d9d3d9d159d0d5786b786978597857771d771b7707770567656763675367516607660565ef65ed6f0d2f0cef0aef0aaee36ee32ee0aee06cec6cec2cea2ce9ecc0acc06cbdacbd6bbc2cbc2abc24bc23bb83bb81bb7abb79b3a9b3a7b3a2b3a1b2f7b2f5b2ecb2eba88ca3dca3bca32ca31c953c951c94ac948bce2bce0bcdabcd9bc33bc31bc2abc28b9465946394579455929592919287928579b579b379a979a77855785178477845564a9e4a964a564a4e43de43d64376436de19de195e155e14ddc65dc5ddc0ddc05c952c951c949c948c87ac879c86dc86cbc32bc31bc29bc28bb8bbb89bb80bb7faf252b2523250f250b21bb21b32193218ef0aaf0a2f08ef08aee06edfeede6ede2a379c579c179b579b3786778637855785168a768a36891688f6761675d674f674b6f36af366f352f34ef0aaf0a2f08ef08ad122d11ed106d102ce9ece96ce86ce82abc33bc32bc2abc29bb8cbb8bbb81bb80b3b0b3afb3a7b3a6b301b300b2f5b2f4b786578637853785177177713770176ff675f675d674d674b660165ff65e965e75de155e145e11de115dc0ddbfddbcddbc59d3d9d2d9d0d9d0597ad979d975d9755443ca2cca2bc92cc92bc944c943c923c922bcd5bcd4bc14bc13bc24bc23bc0ebc0db928992879247924590cb90c990b390b178497847781d781b76f576f376e776e54de6ade6a5e0a5e09de125e11de075e06da215a20d9c659c5d9d159d0d9c159c0dbc24bc23bc0ebc0dbb7abb79bb73bb72b3a2b3a1b382b381b2ecb2ebb2e1b2e0a46515e5156495e49564a1e4a164916490de6a5e69de09de095e11de115e06de065c943c942c922c921c864c863c858c857bc23bc22bc0dbc0cbb79bb78bb72bb71a6f352f34ef04ef04af08ef08af036f032d106d102ce2ece2ace86ce82ce06ce02de11de115e06de065dbcddbc5db95db8d9d0d9d059c0d9c05975d9755970596fd21a

private theorem cap111011100111100Accepted : Accepted table cap111011100111100Box cap111011100111100Tree := by
  decide +kernel

private def cap111011100111101Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100111101Tree : Option PackedTree := decode 6 0xe692e69265c9e5c965cce5cc65c865c7dfa3dfa35ef4def45ef7def6def35ef2d8b2e672e632c532c4f28ff28f728b328aef7bef7b6f63ef63af392f38af356f3529bf47bf46bde9bde8bdefbdedbde6bde5b670b66fb547b546b54eb54cb543b542b15ef7def6def35ef2de725e715e6dde6d5aa75aa65aa1daa15a2ada29da24da245bde6bde5bd8fbd8ebcdbbcdabcd5bcd4b543b542b503b502b449b448b442b441a88cd24cd23cb1ccb1bcb98cb97cb13cb12bf46bf45bd95bd94bdedbdecbd8ebd8db9731972f96279625947b9477945794557bdb7bd97b1d7b1b79c579c179a979a74dfa35fa2decadeca5ef6def65ec75ec6db37db375a85da855aa65aa5da815a80dbdedbdecbd8ebd8dbce2bce0bcd4bcd3b54cb54bb502b501b453b451b441b440a4399629962793c793c59459945793c193bf7b1f7b1d7963796179ab79a9795d795b6232f63ef63af2c6f2c2f356f352f2baf2b6d40ed40ad0aad0a6d10ad106d09ed09ac444cb13cb12c934c933ca2bca2ac92bc92abd8ebd8dbc1abc19bcd4bcd3bc13bc1220209c65ec75ec6de0d5e0cde6a5e69de09de095a815a80d9c9d9c95a20da2059c5d9c510004e21a

private theorem cap111011100111101Accepted : Accepted table cap111011100111101Box cap111011100111101Tree := by
  decide +kernel

private def cap11101110011110Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011100111100Tree <*> cap111011100111101Tree

private theorem cap11101110011110Accepted : Accepted table cap11101110011110Box cap11101110011110Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101110011110Box 1 (midpoint cap11101110011110Box 1) = cap111011100111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100111100Accepted
  · have h : rightBox cap11101110011110Box 1 (midpoint cap11101110011110Box 1) = cap111011100111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100111101Accepted

private def cap11101110011111Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 63 / 100), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100111110Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100111110Tree : Option PackedTree := decode 7 0x3e201e1fde1e7e1e5df9ddf99df8bdf87b19bb197b187b185af7faf7baf6daf697c3cfc3cbc3b3c3afbf17bf0fbefbbef7630f630b62fb62f75edb5ed35ebb5eb6aefceefcdefc5efc4eed2eed1eec3eec2d7bfd7bed7b6d7b5d6eed6edd6e4d6e3bdf9bdf99df89df87dda3dda1dd85dd83af7daf7baf6baf69addbadd9adc7adc55f7e2f7e1f7df77def761f760f75bf75b6bdb6bda6bd76bd6eb726b716b6d6b6cd476337632f630f630b5eff5ef75edb5ed328ff28f728cf28cb2557254f2533252aec61ec616c5f6c5eebdb6bda6bd76bd6e519e51965166515e4a664a564a264a1d5af7faf7daf6daf6badddaddbadc9adc792ab92a99299929790fb90f990e190df75efb5ef75ed75ed35bb75bb35b8f5b8b2553254f252f252b21f321ef21bf21babd7b6d7b4d7aed7add6e4d6e2d6dad6d9c94cc94ac944c943c870c86ec865c864a88f0fef0fcf0f2f0f1efccefcaefc3efc1d8cbd8c9d8c2d8c1d7bdd7bbd7b4d7b2be1e5e1e3e1d7e1d5df87df83df7bdf79b185b183b17bb179af69af65af5baf59577e677e5f7e1f7e177687767f760f7606bdeebde6bda6bd9eb766b75eb716b70defcbefcaefc2efc1eecfeecdeec0eebfd7bcd7bbd7b3d7b2d6ebd6ead6e1d6e0afbf0fbf07bef7bef3bb07baffbadbbad75ed35ecb5eb75eb35b8b5b835b675b5ea3b197b193b185b183af7baf77af69af65947b94779465946392a792a3929592917630b630762f762f35ed35ecb5eb75eb328cb28c728af28ab252b2523250f250aad7bdd7bcd7b4d7b3d6ecd6ebd6e2d6e1c953c952c94ac949c87bc87ac86ec86dbaf79af77af67af65add7add5adc3adc192a592a39293929190f590f390db90d95ebda6bd96bd6ebd66b716b706b6ceb6be4a564a464a1e4a16437643664326431d443f0ecf0ebefa7efa6efbeefbdef9eef9dd8bed8bdd79ed79dd7aed7add798d797bdf7ddf7bdf3ddf3bdd6fdd6ddd57dd55af5daf5baf31af2fadb5adb3ada3ada14ec5f6c5eebcf6bceebd76bd6ebcc6bcbe5166515e4966495e4a264a1e491e4915d7aed7add798d797d6dad6d9d6d1d6d0c944c943c923c922c865c864c859c858a47875f87577d377d2f7def7de77cef7ce6c5eec5e6bceebce6bd6ebd66bcbebcb5efbdefbcef9def9ceeb6eeb5eeaaeea9d7add7acd797d796d6d9d6d7d6d0d6cfa762f762f35e775e735eb75eb35e5f5e5b28af28ab24af24ab250f250b248b2486ebd6ebd66bcbebcb6b6ceb6beb686b67e4a1e4a164916490e4326431e42c642bd21a

private theorem cap111011100111110Accepted : Accepted table cap111011100111110Box cap111011100111110Tree := by
  decide +kernel

private def cap111011100111111Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (9 / 16, 5 / 8), (13 / 16, 7 / 8)]

private def cap111011100111111Tree : Option PackedTree := decode 5 0x3ea05ea03e3ffe3fde581e57fe3ebe3e9b86fb86db35db35bb49db49bb351b34f7cb03caffc7d7c7d3c403c3fbc3b3c3af693b693766a3669f6337632f62fb62f69dc37dc36d9aed9adda4eda4dd9a8d9a7cd25cd24cb1dcb1ccb99cb98cb14cb13bb49db49bb351b34fb19bb197b17db17b9733973196299627947f947b9459945748f501f500f1fef1fcf2bff2bef1f4f1f3dc36dc35d9add9acda4dda4cd9a7d9a6be57fe57de3e9e3e7e1fde1f9e1d7e1d5b49bb499b34fb34db197b193b17bb1794ee1b6e1aecd6ecd66d26ed266cd3ecd366926691e58e658de5cc65cbe589e5895da4dda4cd9a7d9a6d8cbd8c9d8bdd8bccb98cb97cb13cb12ca3dca3bca2bca2aa439e3ebe3e9df61df5fe1d9e1d7df4fdf4db351b34faf4baf49b17db17baf3daf3a202138cd9a8d9a7d7a5d7a4d8bed8bdd79ed79dcb14cb13c935c934ca2cca2bc92cc92b10109c44f1f4f1f3efafefaef0ebf0eaefa6efa5d9a7d9a6d7a4d7a3d8bdd8bcd79dd79c20209c66cd3ecd36bd26bd1ec5eec5e6bceebce6589e589649a6499e515e5156495e49510104e21a

private theorem cap111011100111111Accepted : Accepted table cap111011100111111Box cap111011100111111Tree := by
  decide +kernel

private def cap11101110011111Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011100111110Tree <*> cap111011100111111Tree

private theorem cap11101110011111Accepted : Accepted table cap11101110011111Box cap11101110011111Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101110011111Box 1 (midpoint cap11101110011111Box 1) = cap111011100111110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100111110Accepted
  · have h : rightBox cap11101110011111Box 1 (midpoint cap11101110011111Box 1) = cap111011100111111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100111111Accepted

private def cap1110111001111Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101110011110Tree <*> cap11101110011111Tree

private theorem cap1110111001111Accepted : Accepted table cap1110111001111Box cap1110111001111Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111001111Box 0 (midpoint cap1110111001111Box 0) = cap11101110011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110011110Accepted
  · have h : rightBox cap1110111001111Box 0 (midpoint cap1110111001111Box 0) = cap11101110011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110011111Accepted

private def cap111011100111Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111001110Tree <*> cap1110111001111Tree

private theorem cap111011100111Accepted : Accepted table cap111011100111Box cap111011100111Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011100111Box 3 (midpoint cap111011100111Box 3) = cap1110111001110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001110Accepted
  · have h : rightBox cap111011100111Box 3 (midpoint cap111011100111Box 3) = cap1110111001111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111001111Accepted

private def cap11101110011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111011100110Tree <*> cap111011100111Tree

private theorem cap11101110011Accepted : Accepted table cap11101110011Box cap11101110011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11101110011Box 2 (midpoint cap11101110011Box 2) = cap111011100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100110Accepted
  · have h : rightBox cap11101110011Box 2 (midpoint cap11101110011Box 2) = cap111011100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011100111Accepted

def cap1110111001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11101110010Tree <*> cap11101110011Tree

theorem cap1110111001Accepted : Accepted table cap1110111001Box cap1110111001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110111001Box 1 (midpoint cap1110111001Box 1) = cap11101110010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110010Accepted
  · have h : rightBox cap1110111001Box 1 (midpoint cap1110111001Box 1) = cap11101110011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101110011Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover21
