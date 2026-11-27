import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover09

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap1110011Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (1 / 2, 3 / 4), (1 / 2, 3 / 4)]

private def cap11100110Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (1 / 2, 5 / 8), (1 / 2, 3 / 4)]

private def cap111001100Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (1 / 2, 5 / 8), (1 / 2, 5 / 8)]

private def cap111001100Tree : Option PackedTree := decode 6 0xfa7df7d977d977cd7762f751f751f7515b34d9cb59cb59bf597d596d596d596cdefb2ed4fef9aed4ceea3ed40eea2ed3fc938c72bc91fc728c851c71cc850c71bb92718e57923f8e5190a38e3990a18e37672d63c166fd63bb65b563a565b363a343efb2ef9aed4fed4ceea3eea2ed40ed3fc938c91fc72bc728c851c850c71cc71bb9271923f8e578e5190a390a18e398e37672d66fd63c163bb65b565b363a563a3477cd76a676a67699f751769ff69ff69959bf58eed8eed8e2d96cd8e8d8e8d8e256bbb17ba8fba8fba8bb253b1cfb1cfb1cb21cb2147214721431a3319c319c319bee4396428e428e4286346633863386337d97d596d596d596cd8b158a5d8a5d8a551dd47da81dd45da7fd8e7d8bbd8e5d8b990a38e3990a18e378ce18cb18cdf8caf721471c7321431c6f19c3196319bf195ecb6ac74acb66c746c52ec4d2c52ac4ce87dd47dd45da81da7fd8e7d8e5d8bbd8b990a390a18e398e378ce18cdf8cb18caf7214721431c731c6f19c319bf1963195ecb6acb66c74ac746c52ec52ac4d2c4ce8eea2ed3fed3fed32ec72ec5cec5cec5bb2d9b1d1b1d1b1c4b14ab133b133b132ad1b669b396b396b37eb2fab2dab2dab2d99b4399b199b1999c9938991f991f991eb672d63c166fd63bb65b563a565b363a333633103333930fd323f30e7323d30e55d9cb59bf58f058eed96d596cd8e958e8ccd8ccce4c40cc3f4c8fcc8f4c39cc395b37eb1ddb1ddb1c5b2d9b1d1b1d1b1c4999c987e987e9867991e987298729866ad597d596d596d596cd8b158a5d8a5d8a54c9c4c8fcc8fcc8f4c16cc0c4c0c4c0bdb2dab1d2b2d9b1d1b14bb134b14ab133991f9873991e98729818980298179801aecb6acb66c74ac746c52ec52ac4d2c4ce647e647a61ce61ca6062605e600a6006d96cd8e8d8e8d8e258a55899d899d8994c8f4c394c394c334c0bcc00cc00cc005688

private theorem cap111001100Accepted : Accepted table cap111001100Box cap111001100Tree := by
  decide +kernel

private def cap111001101Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap1110011010Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 63 / 100), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100110100Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 441 / 800), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100110100Tree : Option PackedTree := decode 7 0x365fb65f965d165cf6419641763f563f346d746d546b546b34561455f4541453f6cbf2cbeecb9ecb9ac82ec82ac7e6c7e28daa8da68d668d628abe8aba8a7e8a7abb2e8b2e7b2ddb2dcb1fab1f9b1efb1eea35aa359a34fa34ea2a0a29fa295a294b65cf65cd65b965b763f363f163dd63db46b346b1469d469b453f453d452945275ab20cb20bb1fab1f9b165b164b159b158a2b0a2afa2a0a29fa221a220a214a213b6417641563f363f162c962c762b162af455f455d453f453d4441443f442744255d8fd58fcd8f7d8f758acd8ac58a758a6d150514fd14ad14a510a5109d103d1035b1f9b1f8b1eeb1edb158b157b14db14ca29fa29ea294a293a213a212a206a205ad1a36ba369a35aa358a2b0a2aea2a0a29e993c9939992b992a98a398a198989897b46b546b1469f469b4541453d452b452732573255324332413131312f311d311b5515851575150514f5110d10fd10a51094c51cc50cc4c4c4bcc184c174c124c11da2a0a29ea295a293a214a212a207a20598989897988e988d98249823981a9819a88b2fbb2fab2dbb2dab20ab209b1edb1eca369a368a34da34ca2aea2ada293a292b6415641363db63d962c762c562996297455d455b45274525443f443d440b44094d1b4d1b451a6d1a6510fd10f5102d1024c9ccc9c4c904c8fcc174c16cc0ccc0c50ecb76cb6ec99ac992c7bec7b6c78ec7868d3e8d368be28bde8a568a4e8a268a22d933593258ea58e9d8f1d8f0d8e458e3d17c517bd13dd13d5144d14451385137d563df63db63c763c3629d62996283627f452b452745134511440f440b43f743f56c78ec786c722c71ec506c4fec4dac4d68a268a2289c289be87ee87ea87c687c2a3469f469b44f744f5452b452744e144df3243324130eb30e9311d311b30d330d168a568a4e8a268a22881e881687ee87ea623a62366212620e606a6066603a6036d144d14451385137d0fdd0fd50f8d0f84c424c41cc34cc344c074c06cc024c01d44596dd96d58e9d8e958a658a5d89ad89a51a6d1a6513d513cd102d10250f850f7da34da34ca27aa279a205a204a1f0a1ef9920991f987498739819981898039802a1a

private theorem cap11100110100Accepted : Accepted table cap11100110100Box cap11100110100Tree := by
  decide +kernel

private def cap11100110101Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100110101Tree : Option PackedTree := decode 7 0x36cd96cd56a116a0d689f689b687d68794c0f4c0b4a454a43490348ff48e148dd6d422d41ace6ace5ed0fad0f2ce22ce1a948a94868fde8fda91c291ba8f9a8f94800172b44fb44eb43eb43db2fdb2fcb2e8b2e7a481a480a470a46fa36ba36aa35aa359b689d689b687b687965f965f765cf65cd490148ff48df48dd46d546d346b346b15da1f5a1e59c459c359745973596ed96dd238523751f351f2d1ad51ac51a7d1a6d46981e9816948a9486920691fe91c291ba6d1a6d126aa26a9e6876686e683a6836d2915290d1fbd1fb5238523751f351f2cd544d53ccd9ccd94d074d06ccd14cd0d5490348ff48e148dd46d746d346b546b1343b3437341d341b3279327332573255691c291ba8f9a8f968d6a8d628d3e8d36683a6836668a668664ae64aa64866482a22d9aad9a6ce5ece5acbeecbeacb6ecb6a981698128fda8fd68da68da28d368d32d302d30251fb51fad1b4d1b451a6d1a64da24da1ccd94cd8cc9ccc9c4c904c8fd0e59c459c3593b593a596ed96dd933593251f351f2d183d18351a7d1a6d17c517bd88ca3e6a3e5a307a306a34fa34da2f8a2f799a299a198f198f09921992098e398e2b1112ce1ace16c77ec77acb6ecb6ac74ec74a8f968f928a168a128d368d3289ea89e69a3f6a3f5a287a286a34da34ca27aa27999b299b1988298819920991f98749873a1a

private theorem cap11100110101Accepted : Accepted table cap11100110101Box cap11100110101Tree := by
  decide +kernel

private def cap1110011010Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11100110100Tree <*> cap11100110101Tree

private theorem cap1110011010Accepted : Accepted table cap1110011010Box cap1110011010Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110011010Box 1 (midpoint cap1110011010Box 1) = cap11100110100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100110100Accepted
  · have h : rightBox cap1110011010Box 1 (midpoint cap1110011010Box 1) = cap11100110101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100110101Accepted

private def cap1110011011Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 63 / 100), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100110110Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap111001101100Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (1 / 2, 9 / 16), (5 / 8, 3 / 4)]

private def cap111001101100Tree : Option PackedTree := decode 6 0xf753f75376fcf6fc76af76aef6a976a8e42ae42a63e463e3e39de39d63976396deea6eea5edf8edf7ed5ded5ced51ed50c854c853c7c7c7c6c73ac739c72dc72cafb7e7b7e3b50fb50bb54bb547b4dfb4db1f231f1f1c7f1c7b1cbb1cb71c4b1c46f6fc76fbf6a176a0f6a8f6a8769b769ae3e3e3e3638f638ee396e3966388e38856bb57bb577b54bb547b1dfb1dbb1abb1a71cef1ceb1cbb1cb719d319cf19971992f6aef6ae76a8f6a8763b763af634f634639d639ce396e3966339e33963326331d7daa5daa3da6fda6dd8d5d8d3d8c1d8bf8e5d8e5b8e258e238ccb8cc98cb78cb57b547b543b4dbb4d7b1a7b1a3b17fb17b1cb71cb31c471c431993198f196b1966b472157214f1f231f1b1cef1ce71cbb1cb2cb76cb6ec99ac992c7bec7b6c78ec786e3e463e3638fe38ee3976396638963885933593258ea58e9d8f1d8f0d8e458e3d58e778e758e5d8e5b8ce98ce78ccb8cc963df63dd63c763c5629d629b6283628171ceb1ce71cb71cb319cf19cb1993198ec7bac7b6c78ac786c536c532c502c4febc72ec72cc712c710c665c663c65bc659b1e3b1e1b1c8b1c7b141b13fb136b135a88eea5eea3ed41ed40ed5ced5aed35ed34c853c851c71dc71cc739c737c710c70fbdab9dab5da6bda69d8ebd8e7d8bdd8bb8e738e6f8e218e1f8ce58ce18cb38cb14e429e428e38ee38e639ce39be3886387d96dd96d58e9d8e958f6d8f658e3d8e35c739c737c710c70fc672c670c659c658b1edb1ecb1c7b1c6b14cb14bb135b134a43

private theorem cap111001101100Accepted : Accepted table cap111001101100Box cap111001101100Tree := by
  decide +kernel

private def cap111001101101Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (9 / 16, 5 / 8), (5 / 8, 3 / 4)]

private def cap111001101101Tree : Option PackedTree := decode 7 0xf764f7647759f75976c476c3f6b7f6b76b73eb736b6aeb6a6ae8eae86adf6adedd6e7d6e6d6d5d6d4d5d1d5d0d5bed5bdc876c875c861c860c761c760c74cc74ba3bb23bb1fbacbbac7b61fb61bb5bbb5b721d721d32183217f1d831d7f1d2f1d2abeeb3eeb2eea7eea6ed70ed6eed5eed5dc861c860c855c854c74cc74bc73bc73a08007ddd65dd63dd4ddd4bdadddadbdabbdab990c190bf90a990a78e978e958e758e735aed88ed87ed6fed6eec98ec97ec86ec85d5d1d5d0d5bed5bdd522d521d515d514baba3aba1ab7dab7baa45aa43aa2baa298ec38ec18e998e978d218d1f8d018cff476c3f6c376b776b6f64bf64b7642f64263b063afe3a5e3a56347e347633fe33f57dadfdadddabddabbd90dd90bd8efd8edab7dab7bab63ab61aa2baa29aa13aa11756fb56f756c756c354575453542754231d331d2f1cef1ceb1a0319ff19d319ce8ed6eed6ded5ded5cec85ec84ec76ec75c74bc74ac73ac739c67fc67ec673c672ad1c876c875c861c860c761c760c74cc74bb2fdb2fcb2e8b2e7b20cb20bb1fab1f9b90eb90e990c190bf8ec18ebf8e978e9565f965f765cf65cd6417641563f363f15e430e430642ae42a63a663a5e39de39d59745973d96ed96e58fd58fcd8f7d8f75c860c85fc854c853c74bc74ac73ac739b2e7b2e6b2dcb2dbb1f9b1f8b1eeb1edad63b0e3b063a663a5e3486347e340633fd9065905d8fd58fcd8b2d8b258acd8ac5c760c75fc74bc74ac68fc68ec67fc67eb20bb20ab1f9b1f8b164b163b158b157af1d331d2f1cef1ceb1a0319ff19d319cec7eac7e6c7bec7bac566c562c53ac536e3a5e3a5639d639ce33fe33f6339e33958fcd8fc58f758f6d8ac58abd8a6d8a65688eec7eec5eeb1eeb0ed86ed84ed6ded6cc874c872c85fc85ec75fc75dc74ac749bdd63dd61dd4bdd47dadbdad9dab9dab590bf90bd90a790a38e958e938e738e6f576c376c276b6f6b6764b764a76427641e3afe3aee3a563a4e3476346633f633eded6ded6ced5ced5aec84ec83ec75ec73c74ac749c739c737c67ec67dc672c670a8e43a64396429e428e3afe3aee39ce39bd97dd97d596dd96d59055904d8f6d8f65c75fc75dc739c737c68ec68cc672c670b20ab209b1edb1ecb163b162b14cb14ba43

private theorem cap111001101101Accepted : Accepted table cap111001101101Box cap111001101101Tree := by
  decide +kernel

private def cap11100110110Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111001101100Tree <*> cap111001101101Tree

private theorem cap11100110110Accepted : Accepted table cap11100110110Box cap11100110110Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11100110110Box 2 (midpoint cap11100110110Box 2) = cap111001101100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001101100Accepted
  · have h : rightBox cap11100110110Box 2 (midpoint cap11100110110Box 2) = cap111001101101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001101101Accepted

private def cap11100110111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (1 / 2, 5 / 8), (5 / 8, 3 / 4)]

private def cap11100110111Tree : Option PackedTree := decode 7 0xfa7f7a7e78fd78fbf87cf87bf87478736690e68fe58ce58be51ce51be514651310005ef1f9f1f8efb5efb4f0e8f0e7efa3efa2cb19cb18c93bc93aca28ca27c928c927be3f1e3efdf69df67e1cfe1cddf45df439631962f92759273944f944d924f924d5af0f9f0f8f0e8f0e7eecaeec8eeb3eeb2ca39ca38ca28ca27c876c875c861c86008005de1f1e1efe1cfe1cddd91dd8fdd65dd639471946f944f944d90eb90e990c190bf5f8747873f7d1f7d17759f7597753f75365146513e4946493e430e430642ae42a5f0e7f0e6efa2efa1eeb2eeb1eea6eea5ca27ca26c927c926c860c85fc854c853ad1cd21cd1fcb19cb17ca39ca37ca28ca26b66cb66ab508b506b44fb44db43eb43cb96339631927792759451944f9251924f6a116a0f67336731687d687b6711670f72c632c5f24eb24e7289f289b249f249ad41ed41ace62ce5ed0f6d0f2ce1ece1ab5947394719451944f90ed90eb90c390c1689f689d687d687b65fb65f965d165cf728e328df289f289b21d721d32183217ed13ad136d0f6d0f2cbf2cbeecb9ecb9abca28ca26c928c926c861c85fc855c853b43eb43cb388b386b2e8b2e6b2ddb2dba88f4fcf4fbefb3efb2f0f7f0f5efa1efa0cd1fcd1ec939c938ca37ca35c926c925be1efe1ebdf43df41dd8fdd8bdd4bdd47946f946b924d924b90e990e590a790a34e68fe68f649ce49c651be51ae4936492db355b34d9cbd9cb5a26da2659c359c2dca37ca35c926c925c874c872c853c851b44db44cb386b385b2fbb2fab2dbb2daa439df47df45dc13dc11dd4fdd4ddbf3dbf19251924f8fb18faf90ab90a98f918f8f7be8bbe87b823b81fba9bba97b7e3b7df249f249b1f5f1f5b2153214f1f1f1f1ab88cc928c927c7d8c7d7c855c854c7c8c7c7b388b387b276b275b2ddb2dcb266b265b924f924d8faf8fad90a990a78f8f8f8d670f670d64eb64e965b965b764cb64c95c444efa1efa0ed4eed4deea5eea3ed41ed40c926c925c72ac729c853c851c71dc71ca664936492e3956394e429e428e38ee38e59c359c2d8efd8ef596dd96d58e9d8e9521a

private theorem cap11100110111Accepted : Accepted table cap11100110111Box cap11100110111Tree := by
  decide +kernel

private def cap1110011011Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11100110110Tree <*> cap11100110111Tree

private theorem cap1110011011Accepted : Accepted table cap1110011011Box cap1110011011Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110011011Box 1 (midpoint cap1110011011Box 1) = cap11100110110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100110110Accepted
  · have h : rightBox cap1110011011Box 1 (midpoint cap1110011011Box 1) = cap11100110111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100110111Accepted

private def cap111001101Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap1110011010Tree <*> cap1110011011Tree

private theorem cap111001101Accepted : Accepted table cap111001101Box cap111001101Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap111001101Box 0 (midpoint cap111001101Box 0) = cap1110011010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011010Accepted
  · have h : rightBox cap111001101Box 0 (midpoint cap111001101Box 0) = cap1110011011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011011Accepted

private def cap11100110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap111001100Tree <*> cap111001101Tree

private theorem cap11100110Accepted : Accepted table cap11100110Box cap11100110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11100110Box 3 (midpoint cap11100110Box 3) = cap111001100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001100Accepted
  · have h : rightBox cap11100110Box 3 (midpoint cap11100110Box 3) = cap111001101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001101Accepted

private def cap11100111Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (5 / 8, 3 / 4), (1 / 2, 3 / 4)]

private def cap111001110Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (5 / 8, 3 / 4), (1 / 2, 5 / 8)]

private def cap111001110Tree : Option PackedTree := decode 8 0xcf4fcefb3f4fbefb2f0f7efa1f0f5efa0cd1fc939cd1ec938ca37c926ca35c925be1efdf43e1ebdf41dd8fdd4bdd8bdd47946f924d946b924b90e990a790e590a34e68fe49ce68f649c651be493651ae492db3559cbdb34d9cb5a26d9c35a2659c2dca37c926ca35c925c874c853c872c851b44db386b44cb385b2fbb2dbb2fab2daa446a4eec6eea4eec5eea3ed85ed5bed84ed5ac873c852c872c851c75ec738c75dc737aa76c2f6adf6c276ad764af63a764a7639e3af639c63aee39be346e338e346633854721d3214f21cb21471d7f1ce71d771cdecbeecb6ecbeacb6ac82ac7b6c826c7b2e3afe39ce3aee39be347633963466338590558f6d904d8f658b1d8a658b158a5d223465b3559cbdb34d9cb597dd96dd97d596d5302d1fb530251fad1b4d1a6d1b451a65a605a3f6a604a3f5a369a34da368a34c9b4499b29b4399b1993999209938991fa2352cbeecb6ecbeacb6ac82ac7b6c826c7b28da68d368da28d328aba8a4e8ab68a4ad90558f6d904d8f658b1d8a658b158a5d1575149d156d149510fd102d10f51025346d3469b46d14699443f440b443d4409327332413271323f305d3033305b303144688

private theorem cap111001110Accepted : Accepted table cap111001110Box cap111001110Tree := by
  decide +kernel

private def cap111001111Box : Box := ![(11 / 10, 6 / 5), (189 / 400, 63 / 100), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap1110011110Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 63 / 100), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap11100111100Box : Box := ![(11 / 10, 23 / 20), (189 / 400, 441 / 800), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap11100111100Tree : Option PackedTree := decode 7 0xd9ae59a359a359a2d9265921d921d92151df51d751d751d6d170516bd16bd16b5b346b32eb345b32db243b236b242b235a3aea397a3ada396a2d7a2cda2d6a2ccaecd1acd16ccbaccb6c90ec90ac8dac8d68eba8eb68e5e8e5a8b5e8b5a8b368b32d9a2d996d996d9965921591ad91ad91a51d6d1cb51cb51cad16b516651665165d6ac932c90ec90ec90ac636c616c616c6128b828b5e8b5e8b5a8926890689068902d921d91b5921591ad8c2d8bdd8c258bd516bd166d16b51665120d11bd120511b5764876485646d646b630b630962f762f545af45ad459b459944834481446f446d6c90ac8d6c8d6c8d2c612c5eac5eac5e68b5a8b328b328b2e890288da88da88d6b468efa8e5e8eba8e5a8b828b368b5e8b3265ea658665c66582632e62e6630a62e2d1d751cb51cbd1cad16bd1665166d165ccb8ccb04cb0ccafcc614c5c4c5ccc5bd545c1459b45af45994493446f4483446d319731733185317130ad308b309d308968b5e8b328b368b2e890688da88de88d6630a62e262e662de613a61126116610ea225996d97e5996597dd91ad905d91a590551cb51b551cad1b4d1665157d165d157552c8d6c82ec8d2c82ac5eac592c5e6c58e8b328abe8b2e8aba88da888288d6887ea328e5a8daa8e568da68b328abe8b2e8aba658264ee657e64e662e2628a62de6286a94599455f4597455d446d4441446b443f31713145316f31433089305f3087305d510eccbaccb6cc56cc52c8dac8d6c886c8828e5e8e5a8e028dfe8b368b328afe8afad996d996598a5989d91ad91a5910590fd1cb51cad1bfd1bf51665165d15f515ed7662b662965fb65f96443644164196417470146ff46d746d5457f457d4561455f6cc52cc4ecbf2cbeec882c87ec82ec82a8dfe8dfa8daa8da68afa8af68abe8abab5646d646b6443644162f762f562e162df459b4599457f457d446f446d445944576c8d6c8d2c882c87ec5eac5e6c5bec5ba8b328b2e8afa8af688da88d688ae88aabb221b220b20cb20bb170b16fb165b164a2bfa2bea2b0a2afa22ca22ba221a220b6441643f6417641562df62dd62c962c7457d457b455f455d445744554441443f5a3472f472b470146fd459b4597457f457b32c332bf329b32993173316f315b315968e028dfa8dae8da68afe8af68ac28aba6536653264f264e662b662b2628e6286aa2cda2cba2bfa2bda237a235a22ca22a98b998b798ad98ac98459843983a9839b457f457b4561455d445944554443443f315b315931473143307530733061305d511665965f765f765f56469641564156413472b46d346d346d14597455d455d455b6c8d2c82ac82ac826c5e6c58ec58ec58a8b2e8aba8aba8ab688d6887e887e887a9a395a369a369a368a235a21fa21fa21e995f9939993999389843982e982e982da1a

private theorem cap11100111100Accepted : Accepted table cap11100111100Box cap11100111100Tree := by
  decide +kernel

private def cap11100111101Box : Box := ![(11 / 10, 23 / 20), (441 / 800, 63 / 100), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap11100111101Tree : Option PackedTree := decode 7 0x36def6d856d856d836983694f694f694d4ced4cab4cab4ca949cf499f499f499d6db0ada6adb06da66d29ed20ed29ad20a995698d6995298d2933e92d2933a92cebb6c2b6c1b69ab699b4a7b4a6b483b482a655a654a635a634a4cfa4cea4b4a4b3b6d836d336d336d31694d6905690569034ca94c694c694c67499d4967496749655ab4c1b4a7b4a7b4a6b35cb346b346b345a4e7a4cfa4cfa4cea3bea3aea3aea3adb694f6907694d6905668d665d668b665b499f4969499d4967475d472f475b472d5da53da535a41da4159a359a2d9975996d267d267525a5259d1d751d6d1cbd1cb5b4a6b482b482b481b345b32db32db32ca4cea4b3a4b3a4b2a3ada396a396a395ad1a676a635a655a634a4e7a4b4a4cfa4b39ba59b719b8b9b709a789a4a9a629a49b4cab4c694c6b4c67499f496749694965371736e136e336df34c534933495349155273d25a5267d259d1df51cbd1d751cb4d3c4d254d314d24ccbd4cb0ccb8ccb05a4cfa4b3a4b4a4b2a3aea396a397a3959a629a499a4a9a48997199609961995fa8896d336cd76d316cd56905689d6903689b4c694c0d4c674c0b49674901496548ff54b482b44eb481b44db32db2fcb32cb2fba4b3a480a4b2a47fa396a36aa395a369a8ca634a606a633a605a4b3a480a4b2a47f9b709b459b6f9b449a499a1c9a489a1baa5259d2405259523fd1cb51b551cad1b4cd24cd0e4d244d0dccb04c9dccafcc9cd443b69ab699b67fb67eb483b482b467b466a635a634a61ba61aa4b4a4b3a498a497b6d336d316cfd6cfb6905690368cd68cb4c694c674c354c3349674965492f492d5db3fdb3edb365b355a33da32da27da26d30dd30cd303d302d24c524b5240d23fd56907690568cf68cd665d665b662b6629496949674931492f472f472d470146ff6d20ad206d19ad196ccb6ccb2cc52cc4e92ce92ca925e925a8e5a8e568dfe8dfabb467b466b44fb44eb315b314b2fdb2fca498a497a481a480a380a37fa36ba36ab68cd68cb689d689b6629662765f965f7492f492d490148ff46ff46fd46d546d35a34c6b4c674c374c33496949654931492d36e336df36b136af34953491346334616986e9866981e98169262925a920691fe6d626d5e6d1a6d1268c668c26876686eaa4b4a4b2a498a496a397a395a380a37e9a4a9a489a319a309961995f994d994cb4931492d490348ff470146fd46d746d334633461343b3437329b3299327932735116d316cd56cd56cd36903689b689b68994c674c0b4c0b4c09496548ff48ff48fd6d206d136d136d132ccb2cbeecbeecbea92ca91fe91fe91fa8e568da68da68da29a633a605a605a604a395a369a369a3689b6f9b449b449b43995f993999399938a1a

private theorem cap11100111101Accepted : Accepted table cap11100111101Box cap11100111101Tree := by
  decide +kernel

private def cap1110011110Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11100111100Tree <*> cap11100111101Tree

private theorem cap1110011110Accepted : Accepted table cap1110011110Box cap1110011110Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110011110Box 1 (midpoint cap1110011110Box 1) = cap11100111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100111100Accepted
  · have h : rightBox cap1110011110Box 1 (midpoint cap1110011110Box 1) = cap11100111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100111101Accepted

private def cap1110011111Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 63 / 100), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap11100111110Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap111001111100Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (5 / 8, 3 / 4)]

private def cap1110011111000Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (5 / 8, 11 / 16)]

private def cap1110011111000Tree : Option PackedTree := decode 4 0x3de0bdd8fddc9dd8ddb6fdb0ddb3ddb0b915390e9911d90e78f1b8ebf8eed8ebd7bb93bb1bbb1fbb17b67bb617b61bb613223b21cf21d321cb1ddb1d7b1d7f1d76aedb7ed86ed9eed85ecb5ec96eca6ec95c78dc75fc776c75ec6a9c68ec69ec68dbdb3ddb0bdb0ddb09d94dd92bd92dd9298eed8ebd8ebf8ebb8d3d8d1b8d1d8d1951c8a9c874c874c872c78dc75fc75fc75db32cb2fbb2fbb2fab234b20ab20ab209b8f1b8ebf8ebf8ebb8d538d1d8d1d8d19646964156415641362f362c762c762c548

private theorem cap1110011111000Accepted : Accepted table cap1110011111000Box cap1110011111000Tree := by
  decide +kernel

private def cap1110011111001Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (5 / 8, 11 / 16), (11 / 16, 3 / 4)]

private def cap1110011111001Tree : Option PackedTree := decode 7 0x3de0fde0dddcdddcbdcb7dcb5dc85dc83ae3fae3dae05ae03ad19ad17ace7ace57b96fb96bb90bb907b6e7b6e3b683b67f5a335a2f59cf59cb5807580357a757a29d71fd71ed702d701d601d600d5e9d5e8c8abc8aac890c88fc78fc78ec778c777a3bc1bbc17bb97bb93b6e3b6dfb67fb67b22ab22a7223f223b1e3b1e371ddf1ddabeee6eee5eec9eec8ee42ee41ee2bee2ad702d701d6e7d6e6d673d672d65cd65bbdc85dc83dc57dc55db41db3fdb11db0face7ace5acb9acb7abd3abd1aba3aba14eb816b80eb73eb736af4eaf46ae8eae864486447e43b643ae3bc63bbe3b0e3b051ddcbddc9dd91dd8fdb3fdb3ddb0fdb0d911f911d90eb90e98eef8eed8ec18ebf5aedb9edb8eda0ed9fed22ed21ed11ed10d601d600d5e9d5e8d590d58fd57fd57ebda45da43da23da21d96fd96dd951d94fab21ab1faaffaafdaa77aa75aa61aa5f4eb00eb006af4eaf46a9dea9d6a986a97e3c7e3c763bc63bbe355e3556350634fd1db71db6fdb3fdb3dd96dd96bd94fd94d8f1d8f1b8eef8eed8d558d538d3f8d3d5f6d076cff6c476c3f688f688767f767eeaf4eaf46ae8eae86abfeabf6ab66ab5ded11ed10ecfeecfdeca8eca7ec98ec97d57fd57ed56cd56bd530d52fd522d521a757a757a35747574354c354bf548b54871de31ddf1d871d831a831a7f1a431a3e8ed9fed9eed87ed86eca7eca6ec97ec96c777c776c760c75fc69fc69ec68fc68ead1c8abc8aac890c88fc78fc78ec778c777bbb6bbb5bb9ebb9dbad3bad2babfbabeb776d776b773d773b75a775a5757f757d665d665b662b6629646d646b64436441464556454e447e44763c763c6e3bbe3bb5996d996598a5989d91ad91a5910590fd79121911f90ed90eb8ef18eef8ec38ec1773d773b770d770b757f757d755575536ee7aee76ee1aee16eafeeafaeaaaeaa6cc56cc52cbf6cbf2c886c882c832c82e8c88fc88ec875c874c777c776c760c75fb314b313b2fcb2fbb220b21fb20bb20aad63c7e3c763bc63bbe355e3556350634fdd69dd695d5fdd5f5d205d1fdd1c5d1bdbad3bad2babfbabeba40ba3fba38ba37b236b235b221b220b17bb17ab170b16fa31e3b1e371ddf1ddb1aab1aa71a7f1a7ac8d6c8d2c882c87ec5eac5e6c5bec5babc778c777c761c760c6a0c69fc690c68fbabfbabebaaabaa9ba38ba37ba30ba2fb757f757d755575537471746f7461745f644364416419641762e162df62cb62c9463bbe3bb63b063afe34fe34f6347e3475910590fd905d90558b7d8b758b258b1d688

private theorem cap1110011111001Accepted : Accepted table cap1110011111001Box cap1110011111001Tree := by
  decide +kernel

private def cap111001111100Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110011111000Tree <*> cap1110011111001Tree

private theorem cap111001111100Accepted : Accepted table cap111001111100Box cap111001111100Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111001111100Box 3 (midpoint cap111001111100Box 3) = cap1110011111000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011111000Accepted
  · have h : rightBox cap111001111100Box 3 (midpoint cap111001111100Box 3) = cap1110011111001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011111001Accepted

private def cap111001111101Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (5 / 8, 3 / 4)]

private def cap111001111101Tree : Option PackedTree := decode 8 0xf79ef792f792f7927742f73977397738eba8eb9ceb9ceb9c6b5beb526b526b51dee85ee72ee72ee71eddfedd1edd1edd0d6b7d6a4d6a4d6a3d622d616d616d615a75d475ce75ce75ce3588b585b585b5857237f231f231f231b1eb31e8f1e8f1e8a8ef25ef07ef24ef06ee72ee5bee71ee5ad739d71fd738d71ed6a4d68cd6a3d68bbdce5dcb7dce3dcb5dba3db73dba1db71ad49ad19ad47ad17ac2dac03ac2bac014eb9ceb8feb9c6b8f6b0b6b00eb0aeb006463e455e463645563d1e3c7e3d163c750fbc97bc93bc1fbc1bb9cbb9c7b96fb96b5ce75ce35c7f5c7b5a935a8f5a335a2ef7397738f72df72d76e8f6e876dcf6dc6b526b51eb466b45eb0b6b0aeb00eb0053ae73ae71ae3fae3dac2dac2bac03ac01918f918d915791558f478f458f1f8f1d47792778377837782f6e876dc76dc76dbe463645564556454e3d163c763c763c6d6bb77fb747b747b743b323b303b303b2ff588b585b585b58575523550b550b5506eb116b0b6b0b6b0aeaa46aa16aa16aa0e3d663d1e3d1e3d1635f635b635b635ad1dba3db73dba1db71d981d96fd97fd96dac2dac03ac2bac01aa85aa77aa83aa757585b580758575803550b54ef550754eb1e8f1e3f1e8b1e3b1adb1aaf1ad71aaa87dba3dba1db73db71d981d97fd96fd96dac2dac2bac03ac01aa85aa83aa77aa757585b585758075803550b550754ef54eb1e8f1e8b1e3f1e3b1adb1ad71aaf1aaa8edd0edb8edb8edb7ecbfecb6ecb6ecb5c7a2c78ec78ec78dc6b5c6aac6aac6a9ad1c8dfc8c7c8c7c8c6c7acc7a3c7a3c7a2bbe6bbd0bbd0bbcfbaeabae3bae3bae2b77cd77a177a1779f75d575c775c775c566b9668d668d668b649964876487648546463e455e463645563d1e3c7e3d163c75de85ddb5de7dddadd71dd69dd715d695bbd0bbb6bbcfbbb5bae3bad3bae2bad2b346b32eb345b32db243b236b242b235a1e463e4636455e45563d1e3d163c7e3c75de85de7dddb5ddadd71dd715d69dd695bbd0bbcfbbb6bbb5bae3bae2bad3bad2b346b345b32eb32db243b242b236b235a3231b22ab22ab22a71e8b1e3b1e3b1e36cd16ccb6ccb6ccb2c90ac8d6c8d6c8d2b58f598f478f478f458d7d8d6d8d6d8d6b6499648764876485631b630b630b630971e8f1e3f1e8b1e3b1adb1aaf1ad71aaac90ec8dac90ac8d6c616c5eec612c5eabc7a3c7a2c78fc78ec6b6c6b5c6abc6aab243b242b236b235b185b184b17bb17ab8f458f1d8f1d8f1b8d6b8d558d558d536485646b646b6469630962f562f562f35a2277837772f782f77276dc76cff6dbf6cf64556447e454e44763c763bbe3c6e3bb58d4edb8ed9fedb7ed9eecb6eca7ecb5eca6c78ec777c78dc776c6aac69fc6a9c69eb1a3322ab223f22a7223b1e3b1ddf1e371ddaccb6cc52ccb2cc4ec8d6c882c8d2c87ec6a63c763b063c6e3afe3556347e354e347591ad905d91a590558bd58b258bcd8b1d443

private theorem cap111001111101Accepted : Accepted table cap111001111101Box cap111001111101Tree := by
  decide +kernel

private def cap11100111110Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111001111100Tree <*> cap111001111101Tree

private theorem cap11100111110Accepted : Accepted table cap11100111110Box cap11100111110Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11100111110Box 2 (midpoint cap11100111110Box 2) = cap111001111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001111100Accepted
  · have h : rightBox cap11100111110Box 2 (midpoint cap11100111110Box 2) = cap111001111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001111101Accepted

private def cap11100111111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 3 / 4), (5 / 8, 3 / 4)]

private def cap111001111110Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (5 / 8, 3 / 4)]

private def cap111001111110Tree : Option PackedTree := decode 8 0xfad4fad47ac8fac878987897f888f8886e536e52ee486e47ec7dec7d6c6eec6e5dca6dca5dc90dc8fd8fbd8fad8ddd8dccd63cd62cd4acd49ca71ca70ca51ca50a3d6a3d69fd643d63fc4bfc4bbc443c43f358b35873527352329c329bf2943293ebf591f590f4fef4fdf111f110f0f9f0f8cd4acd49cd21cd20ca51ca50ca39ca38beb21eb1fe9fbe9f9e221e21fe1f1e1ef9a939a919a419a3f94a1949f9471946f5af130f12ff111f110effceffbefdcefdbd8fbd8fad8ddd8dcd7ecd7ebd7cfd7cebdff9dff7dfb9dfb7de0fde0dddcdddcbafd9afd7af9faf9dae3fae3dae05ae034ec7dec7d6c6eec6e6b8feb8f6b816b80e538e5386528e5286455e45564486447d1e25fe25de221e21fde0dde0bddcbddc994e194df94a1949f91559153911f911d5f888f888787cf87c77737772f764f7646c6eec6e6c636c62eb816b80eb73eb735d8ddd8dcd8c6d8c5d702d701d6e7d6e6ca51ca50ca39ca38c890c88fc876c875a3c443c43fc3e3c3dfbb97bb93bb23bb1f2943293f28e328df223f223b21d721d2b47358f358b352b352729c729c329472942da6ada66d9fed9fad20ed20ad19ed19ae6b166b0e6a4e6a465386537e5286527db4cdb4c5b3f5b3eda415a40da335a32d79a959a939a439a4194a394a1947394716cff6cfd6cd96cd768cf68cd689f689d7352735233483347f2943293f28e328ded9fad9f6d9aed9aad19ad196d13ad136b594e394e194a394a1915791559121911f7a217a1f79eb79e9776d776b773d773b6f442f43ef3d6f3d2eedaeed6ee7aee76d20ed20ad19ed19accbaccb6cc56cc528ca70ca6fca50ca4fc8aac8a9c88fc88eb482b481b466b465b32db32cb314b313af2947294328e728e32243223f21db21d6f3d6f3d2f37af376ee7aee76ee1aee16de7ade7a5e6f5e6eddcf5dceddc35dc2da33da335a27da27598ad98a597ed97e5194a1949f9471946f911f911d90eb90e968cd68cb689d689b6629662765f965f75a23d69fd3f3d3f3d3efc4bbc3dfc3dfc3d73587347f347f347b29bf28df28df28d6f897787bf887f87b7782f763f77277636537e51be527e51b6454e43a64476439df10ff0f6f0f7f0f5eee4eec6eec7eec5ca4fca36ca37ca35c88ec873c874c872a8e6b0e68fe68fe68f6537e51be51be51adb4c5b355b355b34da40da26da26da265ca6fca37ca37ca35c8a9c874c874c872b481b44db44db44cb32cb2fbb2fbb2faa43

private theorem cap111001111110Accepted : Accepted table cap111001111110Box cap111001111110Tree := by
  decide +kernel

private def cap111001111111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (11 / 16, 3 / 4), (5 / 8, 3 / 4)]

private def cap1110011111110Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (11 / 16, 3 / 4), (5 / 8, 11 / 16)]

private def cap1110011111110Tree : Option PackedTree := decode 5 0xcf5a8f590f5a7f58ff12ff110f12ef10fcd62cd49cd61cd48ca70ca50ca6fca4fb1a9e25fe221e25de21fde0dddcbde0bddc994e194a194df949f9155911f9153911d634666b1669066b0e68fe538651c6537e51bdb4cdb35db4c5b355a415a275a40da26d5329c3294329bf293f22ab223f22a7223ad20ad19ad206d196ccb6cc52ccb2cc4ec688

private theorem cap1110011111110Accepted : Accepted table cap1110011111110Box cap1110011111110Tree := by
  decide +kernel

private def cap1110011111111Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (11 / 16, 3 / 4), (11 / 16, 3 / 4)]

private def cap11100111111110Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 63 / 100), (11 / 16, 3 / 4), (11 / 16, 3 / 4)]

private def cap11100111111110Tree : Option PackedTree := decode 5 0x39b9f9b1b9b1b9b19959f95419541953f7fa17f257f257f237ab17a717a717a6f6ff42fe4afe4afe46f562f4e2f4e2f4dedbdedb0adb0adb06d306d29ed29ed29a8cd8dcd63cd8ccd62caa0ca71ca9fca70bf92bf6abf91bf69bd38bd10bd37bd0fb7f257ed57f237ed37a717a217a6f7a1f6d856d356d836d33694f6907694d690543cd8dcd8ccd63cd62caa0ca9fca71ca70bf92bf91bf6abf69bd38bd37bd10bd0fb7f257f237ed57ed37a717a6f7a217a1f6d856d836d356d33694f694d69076905466c666b166b166b0e54fe53865386537db60db4cdb4cdb4c5a535a415a415a40d6b2b3f2a832a832a7f237f231f231f231af562f4e2f4e2f4deef9aef42ef42ef3edeac5e9c5e9c5e9bddf35de85de85de7da60da53da53da5359ae59a359a359a2d1954194e3953f94e1918f9157918d91557a717a217a6f7a1f77a1776d779f776b6f4e2f442f4def43eef42eedaef3eeed6d29ed20ed29ad20acd1accbacd16ccb6879541953f94e394e1918f918d915791557a717a6f7a217a1f77a1779f776d776b6f4e2f4def442f43eef42ef3eeedaeed6d29ed29ad20ed20acd1acd16ccbaccb68ca9fca70ca70ca6fc8c6c8aac8aac8a9b4a6b482b482b481b345b32db32db32cad1

private theorem cap11100111111110Accepted : Accepted table cap11100111111110Box cap11100111111110Tree := by
  decide +kernel

private def cap11100111111111Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 63 / 100), (11 / 16, 3 / 4), (11 / 16, 3 / 4)]

private def cap11100111111111Tree : Option PackedTree := decode 6 0x3ec2feb97eb97eb95e6b7e625e625e623ba27b991b991b98fb5dbb54db54db54b7cd6fcc4bcc4bcc47c693c5a7c5a7c5a36bb76a9b6a9b6a97659f64bf64bf64ba9dd13dcc8dcc8dcc7d967d92fd92fd92ecdcfcd8dcd8dcd8ccacfcaa0caa0ca9fa3d72fd6a7d72bd6a3cc4bcb8bcc47cb877323729b731f72976a9b69c36a9769bef98979717988f970f8b4f89878b47897ed536d386d52ed37ec97ec7dec976c7d53b991b94db98fb94bb25fb1f7b25db1f59b1b9ac79b199ac5954194e3953f94e143f5cbf5caf5a9f5a8f312f311f2e2f2e1dcc8dcc7dca6dca5daa6daa5da70da6fbe625e623e5c5e5c3e2d3e2d1e261e25fb54db54bb4e1b4dfb25fb25db1f7b1f54ee646e63ee536e52ec97ec976c7dec7d66c6e6c666b1e6b16550654fe538e53851eb95eb51eb51eb4fe2d1e25fe25fe25d9b199ac59ac59ac3953f94e194e194df5af1a4f169f169f168f04ff02bf02bf02ad967d92fd92fd92ed83ad81bd81bd81abe09fe057e057e055de7bde4bde4bde49b075b037b037b035aea3ae73ae73ae714ecb3ec97ec97ec976ba8eb9ceb9ceb9c6567e5506550654fe46fe463e463e46351e2d3e261e2d1e25fe057dff9e055dff7b25fb1f7b25db1f5b037afd9b035afd77c0afbff3c0abbfefbc97bc1fbc93bc1b606f5fb3606b5faf5ce75c7f5ce35c7a9d92fd8fbd92ed8fad739d71fd738d71ecaa0ca71ca9fca70c8c7c8abc8c6c8aaa1f8b4f8b478987897f815f81577fe77fdec97ec976c7dec7d6c0dec0d6bf66bf5df02bf02aeffceffbef25ef24ef07ef06d81bd81ad7ecd7ebd739d738d71fd71ea764bf64bb63ef63eb5ce75ce35c7f5c7b2a832a7f29c729c3231f231b22af22aa8f168f12ff12ff12eef24ef06ef06ef05ca9fca70ca70ca6fc8c6c8aac8aac8a9ad1

private theorem cap11100111111111Accepted : Accepted table cap11100111111111Box cap11100111111111Tree := by
  decide +kernel

private def cap1110011111111Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11100111111110Tree <*> cap11100111111111Tree

private theorem cap1110011111111Accepted : Accepted table cap1110011111111Box cap1110011111111Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110011111111Box 0 (midpoint cap1110011111111Box 0) = cap11100111111110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100111111110Accepted
  · have h : rightBox cap1110011111111Box 0 (midpoint cap1110011111111Box 0) = cap11100111111111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100111111111Accepted

private def cap111001111111Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110011111110Tree <*> cap1110011111111Tree

private theorem cap111001111111Accepted : Accepted table cap111001111111Box cap111001111111Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111001111111Box 3 (midpoint cap111001111111Box 3) = cap1110011111110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011111110Accepted
  · have h : rightBox cap111001111111Box 3 (midpoint cap111001111111Box 3) = cap1110011111111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011111111Accepted

private def cap11100111111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap111001111110Tree <*> cap111001111111Tree

private theorem cap11100111111Accepted : Accepted table cap11100111111Box cap11100111111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap11100111111Box 2 (midpoint cap11100111111Box 2) = cap111001111110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001111110Accepted
  · have h : rightBox cap11100111111Box 2 (midpoint cap11100111111Box 2) = cap111001111111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001111111Accepted

private def cap1110011111Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap11100111110Tree <*> cap11100111111Tree

private theorem cap1110011111Accepted : Accepted table cap1110011111Box cap1110011111Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap1110011111Box 1 (midpoint cap1110011111Box 1) = cap11100111110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100111110Accepted
  · have h : rightBox cap1110011111Box 1 (midpoint cap1110011111Box 1) = cap11100111111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100111111Accepted

private def cap111001111Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap1110011110Tree <*> cap1110011111Tree

private theorem cap111001111Accepted : Accepted table cap111001111Box cap111001111Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap111001111Box 0 (midpoint cap111001111Box 0) = cap1110011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011110Accepted
  · have h : rightBox cap111001111Box 0 (midpoint cap111001111Box 0) = cap1110011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110011111Accepted

private def cap11100111Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap111001110Tree <*> cap111001111Tree

private theorem cap11100111Accepted : Accepted table cap11100111Box cap11100111Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap11100111Box 3 (midpoint cap11100111Box 3) = cap111001110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001110Accepted
  · have h : rightBox cap11100111Box 3 (midpoint cap11100111Box 3) = cap111001111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111001111Accepted

def cap1110011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap11100110Tree <*> cap11100111Tree

theorem cap1110011Accepted : Accepted table cap1110011Box cap1110011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap1110011Box 2 (midpoint cap1110011Box 2) = cap11100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100110Accepted
  · have h : rightBox cap1110011Box 2 (midpoint cap1110011Box 2) = cap11100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11100111Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover09
