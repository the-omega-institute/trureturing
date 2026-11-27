import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover28

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap111011110101Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (3 / 4, 7 / 8)]

private def cap1110111101010Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (3 / 4, 13 / 16)]

private def cap11101111010100Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (3 / 4, 13 / 16)]

private def cap11101111010100Tree : Option PackedTree := decode 8 0xe471e470e46ce46be4246423e420e41fddf55df45df05def5db45db3ddb1ddb15c8d9c8d7c8cbc8c9c841c83fc838c836bbe0bbdebbd4bbd2bb63bb62bb5bbb59ab2123211f20e320db1ebb1eb71e971e92eda2ed9eed6eed66ebb2ebaeeb96eb929bbeabbe8bbd4bbd2bb68bb67bb5bbb59b35eb35db349b347b2d5b2d4b2ccb2cbb76d176cf76b776b375d975d775cb75c965ab65a965996597649d649b648b648948c8e1c8dfc8c9c8c7c847c845c836c834bbe8bbe6bbd2bbd0bb67bb66bb59bb58b908f908b906d90698f5b8f598f498f4776cf76cd76b376b175d775d575c975c74ddf45df35de95de85d75dd755d725d71d9aed9ae59a3d9a35926d92659225921d0f232f232b22ff22fb20e320df20bb20b6ef52ef4eef1aef16ed6eed6aed4aed46e4656464e45f645ee41be41b6416e4165de9dde95de2dde25dad5dacdda8dda857917f917d915f915d905d905b90479045778d778b7773777176a576a3768f768d722fb22f722bb22b720b720b3208b2086ef16ef12eee2eedeed46ed42ed1aed16b59071906d905d90598f4b8f498f3d8f3976b776b376a576a175cb75c975bf75bd720bb20b3208f20871e7b1e731e4b1e42ed4aed42ed1eed16eb7eeb7aeb5aeb52a377a977a5778d778976b776b376a576a16693668f667b667765996597658965856ef1aef16eee6eee2ed4aed46ed1eed1accf6ccf2ccc6ccc2cb12cb0ecaeacae6dde2dde25ddc5ddbdda8dda85da35da2d99e599dd9985997d961d961595cd95c56aed6eed66ed1eed16eb96eb92eb5aeb52cb32cb2ecaeacae2c916c912c8e2c8de919193918f917b9177906d90699059905777a577a17789778776b376b176a1769f722f722ef22b722af20b320af20872082ef12ef0eeedeeedaed42ed3eed16ed12ac836c834c821c820c7a4c7a3c790c78fbb59bb58bb45bb44bae4bae3bad4bad3a6ef4aef42eedeeedaed66ed62ed16ed12cd1ecd1accbeccbacb2ecb2acae2cadeddacddac5da2dda25d725d71dd6a5d69d965d965595c595bd9225921d91bd91b521ac7aec7adc7a5c7a4c6c0c6bfc6b8c6b7baecbaebbae5bae4ba4dba4cba48ba47b75d975d775cb75c9749b74997491748f649d649b648b6489631f631d630f630d463d6e3d663d263d1e35fe35f635be35b5926d92659225921d8c758c6d8c358c2d78f4b8f498f258f218e158e138e098e0775cb75c975ad75a974f974f774ef74ed71c2b1c271c131c0f1ae31adf1ab71ab2e9f2e9eee9dee9dae922e91ee90ae9069bae5bae4bad6bad4ba48ba47ba42ba41b245b244b238b237b187b186b17db17ca31e931e8f1e431e3f1adf1adb1ab31aaeeb92eb8eeb52eb4ee91ee91ae906e902dd725d71dd6a5d69dd23dd235d20dd2059225921d91bd91b58c358c2d8be58bdd0d1

private theorem cap11101111010100Accepted : Accepted table cap11101111010100Box cap11101111010100Tree := by
  decide +kernel

private def cap11101111010101Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (3 / 4, 13 / 16)]

private def cap111011110101010Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (11 / 16, 3 / 4), (3 / 4, 13 / 16)]

private def cap111011110101010Tree : Option PackedTree := decode 6 0xf6f0f6f076ea76e976657664f6617660eb126b11eb0ceb0beaa56aa4eaa26aa1dd624d623d619d617d54ad549d544d543c7aec7adc7a5c7a4c6c0c6bfc6b8c6b7a3b783b77fb74bb747b327b323b307b303588f588b585f585b55275523550f550aeb11eb116b0beb0b6aa4eaa46aa1eaa163d6e3d663d263d1e35fe35f635be35b50fb753b74bb72fb727b4bfb4bbb4afb4ab5867585f5843583b5677567356675662f6e5f6e4f6df76ddf695f6957692f691eb086b076b02eb01eacceacc6ac9eac8d5da5fda5dda4bda47d985d983d973d971ab3bab39ab27ab23aa89aa87aa7baa794eb0ceb0beb02eb01eaceeace6ac9eac8e3d2e3d263c963c863856384e3826381dd59dd59cd593d591d544d543d53dd53cc70ac709c704c703c6b8c6b7c6adc6aca476e976e8f6de76dcf6977696f691f6916b0beb0b6b01eb00eace6acdeac8eac8100046ed2eed2ded23ed22ecc1ecc0ecb8ecb7d59cd59bd591d590d543d542d53cd53ba7585f585b580f58075673566f564756431e931e8f1e431e3f1c271c231c0f1c0aeace6acdeac8eac86aa1eaa16a9e6a9de384e3846381e381635be35b63566355d21a

private theorem cap111011110101010Accepted : Accepted table cap111011110101010Box cap111011110101010Tree := by
  decide +kernel

private def cap111011110101011Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (11 / 16, 3 / 4), (3 / 4, 13 / 16)]

private def cap1110111101010110Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (11 / 16, 23 / 32), (3 / 4, 13 / 16)]

private def cap1110111101010110Tree : Option PackedTree := decode 8 0x3de53de51de39de37dceddcebdcd7dcd5c041c03fc033c031bfb7bfb5bfabbfa978083807f806780637f6f7f6b7f577f535cf75cf35cc35cbf5aa35a9f5a775a728ef28ef27ef1bef1aee75ee74ee6aee69e01fe01ee018e017dfdadfd9dfd4dfd3bc03fc03dc031c02fbfb5bfb3bfa9bfa7ae79ae77ae5fae5dad4fad4dad39ad3743ef1cef1bef0bef0aee9fee9eee9bee9ae019e018e00de00cdfebdfeadfe7dfe6bdd3fdd3ddd37dd35dcd7dcd5dcbfdcbdbfd7bfd5bfcfbfcdbfabbfa9bf9fbf9d4f00cf00c700770066feaefea6fe7efe76b986b97eb91eb916b4eeb4e6b486b4790004e1de37de35de15de13dcd5dcd3dcbddcbbc031c02fc019c017bfa9bfa7bf9dbf9b78063805f8033802f7f537f4f7f3b7f375cbf5cbb5c8b5c875a735a6f5a3f5a3a86bb9dbb9d7b9afb9abb753b74fb72fb72b5aa35a9f5a775a73586758635843583ef73af73a77357734f6e9f6e976e576e4eb53eb536b4e6b4deb0c6b0beb07eb0757dcd7dcd5dcbfdcbddb97db95db7ddb7bad3bad39ad21ad1fac21ac1fac0bac097b9abb9a7b97bb977b72bb727b6f7b6ef5a735a6f5a3f5a3b583f583b5813580eb475cf75cf35cc35cbf5aa35a9f5a775a73232f232b22ff22fb20e320df20bb20b6eb9e6b9deb97eb976b53eb536b4e6b4de4656464e45f645ee41be41b6416e41657ae61ae5fae47ae45ad3bad39ad21ad1f9e999e979e8b9e899e5d9e5b9e539e5173d333d2f3d173d133cbb3cb73ca73ca322ff22fb22bf22bb20bb20b7208f208a8d72fd72ed722d721d69cd69bd68fd68ec8bec8bdc8aec8adc82dc82cc822c821ad6b546b536b4eeb4deb0ceb0beb086b07641c641b6417641663d2e3d263cf63ce5d69dd69cd690d68fd610d60fd605d604c82ec82dc823c822c79ec79dc792c791bad39ad37ad1fad1dac1fac1dac09ac07905b9059904590438f3b8f398f238f215a23bc9fbc9bbc6bbc67b9d3b9cfb9a7b9a35cef5ceb5cbb5cb75a9b5a975a6f5a6af7937792f78cf78c7739f73977347733eb9d6b9ceb96eb966b52eb526b4d6b4cd7de35de33de13de11dcd3dcd1dcbbdcb9ae5dae5bae43ae41ad37ad35ad1dad1b7bc67bc63bc23bc1fb9a3b99fb973b96f5cb75cb35c835c7f5a6b5a675a375a32b5dce9dce5dcd3dccfdba5dba3db93db8fad4dad49ad37ad33ac2fac2dac1dac197b9a7b9a3b977b973b727b723b6efb6eb5a6f5a6b5a3b5a37583b5837580f580af7347733f72e772df6e476e3f6dd76dceb4d6b4ceb46eb466b06eb066b016b00d68eb9deb9ceb976b966b536b526b4deb4ce464e463e45ee45de41b641a64166415dd72ed72cd721d71fd69bd699d68ed68cc8bdc8bbc8adc8abc82cc82bc821c820ab5a9b5a935a6f5a67585f585b583b583320db20d320b320af1e931e8f1e731e6eeb4deb4ceb476b466b076b066b01eb00e4166415e410e41063ce63cde3c863c7d443

private theorem cap1110111101010110Accepted : Accepted table cap1110111101010110Box cap1110111101010110Tree := by
  decide +kernel

private def cap1110111101010111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (23 / 32, 3 / 4), (3 / 4, 13 / 16)]

private def cap1110111101010111Tree : Option PackedTree := decode 6 0xf7a0f7a0779bf79b7744f7447740773febaaebaa6ba5eba56b5deb5d6b596b58def40ef3fef36ef35ee88ee87ee7fee7ed754d753d74ad749d6bad6b9d6b1d6b0afbcdfbcdbbca7bca3ba03b9ffb9dbb9d75d2f5d2b5cf75cf35acb5ac75aa35a9ef79b779af7947793f73ff73f773af73a6ba56ba4eb9e6b9deb58eb586b53eb5356bba27ba1fba03b9fbb787b783b777b7735aef5ae75acb5ac35893588f5883587ef740773f773b773a76eef6ee76ea76e96b596b586b546b536b106b0feb0ceb0bd475d575d4f5d2f5d275aef5ae75acb5ac3238f23872367235f2123211f210720feeba5eba56b9eeb9e6b596b58eb546b53e46ce46c6465e4656420e420641c641bdd74ad749d73cd73bd6b1d6b0d6a7d6a6c8d8c8d7c8cac8c9c840c83fc837c836ad6b5deb5ceb546b536b126b11eb0ceb0be4246423e41c641b63d763d6e3d2e3d2523bcffbcf7bcd7bccfba1fba17b9fbb9f35d4f5d475d275d1f5ae75adf5ac35abaf79af79a7793f793773f773ef73a7739eba4eba46b9deb9d6b586b57eb536b52def34ef33ef26ef25ee7dee7cee73ee72d748d747d73ad739d6afd6aed6a5d6a4ad7743f742f73a773976f076eff6e976e8eb5ceb5beb536b526b11eb116b0beb0b53aea7aea3ae93ae8fad73ad6fad61ad5d91c391bf91af91ab908f908b907f907d75d275d1f5cef5ce75ac35abb5a9b5a93235f23572327231f20ff20fb20db20d2ad6b9d6b7d6a6d6a4d623d622d617d616c847c845c836c834c7adc7acc7a4c7a3a43

private theorem cap1110111101010111Accepted : Accepted table cap1110111101010111Box cap1110111101010111Tree := by
  decide +kernel

private def cap111011110101011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101010110Tree <*> cap1110111101010111Tree

private theorem cap111011110101011Accepted : Accepted table cap111011110101011Box cap111011110101011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110101011Box 2 (midpoint cap111011110101011Box 2) = cap1110111101010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101010110Accepted
  · have h : rightBox cap111011110101011Box 2 (midpoint cap111011110101011Box 2) = cap1110111101010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101010111Accepted

private def cap11101111010101Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110101010Tree <*> cap111011110101011Tree

private theorem cap11101111010101Accepted : Accepted table cap11101111010101Box cap11101111010101Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111010101Box 1 (midpoint cap11101111010101Box 1) = cap111011110101010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110101010Accepted
  · have h : rightBox cap11101111010101Box 1 (midpoint cap11101111010101Box 1) = cap111011110101011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110101011Accepted

private def cap1110111101010Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111010100Tree <*> cap11101111010101Tree

private theorem cap1110111101010Accepted : Accepted table cap1110111101010Box cap1110111101010Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111101010Box 0 (midpoint cap1110111101010Box 0) = cap11101111010100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010100Accepted
  · have h : rightBox cap1110111101010Box 0 (midpoint cap1110111101010Box 0) = cap11101111010101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010101Accepted

private def cap1110111101011Box : Box := ![(23 / 20, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (13 / 16, 7 / 8)]

private def cap11101111010110Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (13 / 16, 7 / 8)]

private def cap111011110101100Box : Box := ![(23 / 20, 47 / 40), (189 / 400, 819 / 1600), (11 / 16, 3 / 4), (13 / 16, 7 / 8)]

private def cap111011110101100Tree : Option PackedTree := decode 5 0xe3d863d7e3d3e3d363616360e35d635cd9285927d923d92358c8d8c858c4d8c45c7afc7aec7a6c7a5c6c1c6c0c6b9c6b8baedbaecbae6bae5ba4eba4dba49ba48b75db75d975cd75cb749d749b74937491649f649d648d648b6321631f6311630f43c7a7c7a6c796c794c70cc70bc706c705bae7bae6badabad8ba7eba7dba79ba78b8e198e178e0d8e0b8d758d738d5f8d5d74fd74fb74f374f174957493748974874dd73dd735d6d5d6c5d255d24dd225d21d923d923591d591cd8c4d8c458bfd8bf518f4d8f4b8f298f258e178e158e0b8e0975cd75cb75b175ad74fb74f974f174ef71c2f1c2b1c171c131ae71ae31abb1ab6e9f6e9f2e9e2e9dee926e922e90ee90a9bae6bae5bad8bad6ba49ba48ba43ba42b246b245b239b238b188b187b17eb17da1a

private theorem cap111011110101100Accepted : Accepted table cap111011110101100Box cap111011110101100Tree := by
  decide +kernel

private def cap111011110101101Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (11 / 16, 3 / 4), (13 / 16, 7 / 8)]

private def cap1110111101011010Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (11 / 16, 23 / 32), (13 / 16, 7 / 8)]

private def cap1110111101011010Tree : Option PackedTree := decode 6 0x3919f919d91879185907990779065906377b177af7797779576bf76bd76ad76ab7233b2337230b230720ef20eb20c720c2ef5eef5aef2aef22ed7aed76ed56ed52bc8c3c8c2c8b5c8b4c832c831c827c826bbcbbbcabbbdbbbcbb56bb55bb4bbb4ab918591839169916790639061904d904b779577917779777776ab76a976957692200139ac83cc83ac832c830c7a7c7a6c7a1c7a0bb5fbb5dbb56bb54bae7bae6bae1bae0b90659061904f904b8f438f418f2d8f2976ad76a97697769375c375c175b575b151bbd8bbd6bbcbbbc9bb5fbb5dbb56bb54b34db34bb341b33fb2ceb2cdb2c8b2c610009d77977795777b777976ad76ab7697769566836681666b66696591658f657d657b6ef2aef22eef2eeeeed56ed52ed2aed26cd02ccfeccd2cccecb1ecb1acaf6caf2b576bf76bb76ad76a975cf75cd75c375c1659d659b6591658d648f648d648364816ed5aed52ed2eed26eb86eb82eb6aeb62cb22cb1acafacaf2c906c902c8eac8e6a23233723332307230320eb20e720c320beef5aef56ef22ef1eed76ed72ed52ed4ee4666465e460645fe41ce41c6417e4175deaddea5de3dde35dae5daddda9dda95791839181916791639061905f904b90497791778f7777777576a976a77693769060013b230322ff22c722bf20bf20bb2093208eef1eef1aeeeaeee6ed4eed4aed22ed1c8002735907590719061905d8f4d8f4b8f418f3d76bb76b776a976a575cd75cb75c175bf720c320bb2097208f1e831e7b1e531e4aed52ed4aed26ed1eeb82eb7eeb62eb5aa377ad77a97793778d76bb76b776a976a566976693667f667b659b6599658d658840013aef22ef1eeeeeeeeaed52ed4eed26ed22ccfeccfacccecccacb1acb16caf2caeedde3dde35ddd5ddcdda9dda95da45da3d99f599ed9995998d962d962595dd95d56aed76ed6eed52ed4aeb9aeb96eb82eb7ecb36cb32cb1acb12c91ac916c902c8feddaa5da95da4dda3dd705d6fdd6c5d6b59635962595e595d5920591fd91cd91c5443

private theorem cap1110111101011010Accepted : Accepted table cap1110111101011010Box cap1110111101011010Tree := by
  decide +kernel

private def cap1110111101011011Box : Box := ![(23 / 20, 47 / 40), (819 / 1600, 441 / 800), (23 / 32, 3 / 4), (13 / 16, 7 / 8)]

private def cap1110111101011011Tree : Option PackedTree := decode 5 0x391cf91cb91bb91b7909590939089908777dd77d977c977c576d576d376cb76c972377236f233f23372113210f20f320eaef92ef8aef62ef5aed96ed92ed7eed76ac84ac849c83cc83ac7b0c7afc7a7c7a6bb6abb69bb5fbb5dbaeebaedbae7bae6a6efbaefb2ef92ef8aedaaeda6ed96ed92cd82cd7ecd6acd62cb5ecb5acb4ecb4addf25df15dec5deb5db2ddb25dafddaed9ad59ac59a6d9a5d969d96959675966d576d576d376bf76bb75dd75db75cf75cd65af65ad659d659b64a1649f648f648d48c8e5c8e3c8dbc8d9c849c848c843c841bbecbbeabbe2bbe0bb69bb68bb64bb63b91b791b3919b9197908790839075907177c577c177ad77a976c976c776bb76b756424e424641d641c63d7e3d763d363d2ddb4ddb45daeddaddd76dd765d735d72d377d977d577c577c176d376d176c976c766bf66bd66b166ad65ad65ab65a565a36ef8aef82ef5aef52ed92ed8eed76ed6ecd62cd5acd2ecd26cb4acb46cb36cb32abb69bb68bb5dbb5bbaedbaecbae6bae5b2d6b2d5b2cdb2ccb24fb24eb246b245a43

private theorem cap1110111101011011Accepted : Accepted table cap1110111101011011Box cap1110111101011011Tree := by
  decide +kernel

private def cap111011110101101Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101011010Tree <*> cap1110111101011011Tree

private theorem cap111011110101101Accepted : Accepted table cap111011110101101Box cap111011110101101Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110101101Box 2 (midpoint cap111011110101101Box 2) = cap1110111101011010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101011010Accepted
  · have h : rightBox cap111011110101101Box 2 (midpoint cap111011110101101Box 2) = cap1110111101011011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101011011Accepted

private def cap11101111010110Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110101100Tree <*> cap111011110101101Tree

private theorem cap11101111010110Accepted : Accepted table cap11101111010110Box cap11101111010110Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111010110Box 1 (midpoint cap11101111010110Box 1) = cap111011110101100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110101100Accepted
  · have h : rightBox cap11101111010110Box 1 (midpoint cap11101111010110Box 1) = cap111011110101101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110101101Accepted

private def cap11101111010111Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 441 / 800), (11 / 16, 3 / 4), (13 / 16, 7 / 8)]

private def cap111011110101110Box : Box := ![(47 / 40, 6 / 5), (189 / 400, 819 / 1600), (11 / 16, 3 / 4), (13 / 16, 7 / 8)]

private def cap111011110101110Tree : Option PackedTree := decode 6 0xf6f1f6f176ebf6eb76667665f6627661eb136b12eb0e6b0deaa66aa5eaa36aa2dd626d625d61cd61bd54cd54bd546d545c7b0c7afc7a7c7a6c6c2c6c1c6bac6b9a3b78bb787b75bb753b32fb32bb30fb30b58975893586f5867552f552b55175512eb12eb126b0deb0ceaa5eaa56aa2eaa263d7e3d763d363d2e360e360635ce35c50fb75fb75bb70bb703b4c7b4c3b4a3b49f5873586f5827581f567f567b565b5656f698f69876947693f6627661f65df65d6acfeacf6acb6acaeaa36aa2ea9fea9f53ac39ac37ac13ac0fab3fab3dab2dab2b8f4f8f4d8f2d8f298e198e178e0d8e0b7567f567b565b5657551b551754ff54fb1c331c2f1c1b1c171aeb1ae71abf1aba91dbaddba9db9bdb97da61da5fda59da57ac37ac33ac25ac21ab3dab3bab35ab337b737b72fb703b6fbb4b3b4afb49fb497584b5843581f5817566b56675657564eaed30ed2fed27ed25ecc3ecc2ecbaecb9d59ed59dd595d593d545d544d53ed53da7586f5867581f5817567b56775657564f1e9b1e971e531e4b1c2f1c2b1c171c12eacf6aceeacaeac9eaa2eaa26a9f6a9ee385e3856382e382635ce35c63576356d21a

private theorem cap111011110101110Accepted : Accepted table cap111011110101110Box cap111011110101110Tree := by
  decide +kernel

private def cap111011110101111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (11 / 16, 3 / 4), (13 / 16, 7 / 8)]

private def cap1110111101011110Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (11 / 16, 23 / 32), (13 / 16, 7 / 8)]

private def cap11101111010111100Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (11 / 16, 23 / 32), (13 / 16, 27 / 32)]

private def cap11101111010111100Tree : Option PackedTree := decode 7 0xf795f795778f778ef73c773bf736f73670117010f00df00d6feeefee6febefeb5e022e021e01be01adfdddfdcdfd7dfd6d73fd73ed733d731d6aad6a9d69fd69ea3bcabbca7bc77bc73b9dfb9dbb9b3b9af80878083806b80677f737f6f7f5b7f56f010f010700d700cefee6fedefeb6feaeb9f6b9eeb98eb986b54eb546b4f6b4ed0fbc7bbc77bc37bc33ba87ba83ba77ba73806f806b8047803f7fb77fb37fa77fa2f750f750774ef74e7736f7367730f7306ff6eff66ff4eff46febefeb6fe8efe853c037c035c023c021bfafbfadbfa3bfa1ae67ae63ae4bae49ad3fad3dad25ad22200138778ef78e77867785f750774ff74e774df00d700cf007f006eff66ff5eff46ff3deea0ee9fee9cee9bee6cee6bee60ee5fdfecdfebdfe8dfe7dfd6dfd5dfd0dfcfa7806b80678043803b7f5b7f577f437f3f5cc75cc35c935c8f5a7b5a775a475a40c002706bb9e3b9dfb9b7b9b3b75bb757b737b7335aab5aa75a7f5a7b586f586b584b5846f73bf73b77367735f6eaf6ea76e676e5eb54eb546b4f6b4eeb0d6b0ceb08eb0857dcdbdcd9dcc3dcc1db9bdb99db81db7fad3fad3dad25ad23ac25ac23ac0fac0d7b9b3b9afb983b97fb733b72fb6ffb6fb5a7b5a775a475a4358475843581b5816b475cff5cfb5ccf5ccb5aab5aa75a7f5a7b233723332307230320eb20e720c320bc400276b9f6b9eeb996b986b54eb546b4f6b4ee4666465e460645fe41ce41c6417e41710004e7ae67ae63ae4bae49ad3fad3dad25ad239e9d9e9b9e8f9e8d9e619e5f9e579e5573d3b3d373d1f3d1b3cc33cbf3caf3cab2307230322cb22c320c320bf209720928d731d730d724d723d69ed69dd691d690cf4dcf4ccf46cf45cf2fcf2ecf2acf29b9e9b9e999e8d9e8b9e5f9e5d9e559e539181917f9161915f905f905d90499047435ad55ad51ad3fad3bac37ac33ac25ac21907590719061905d8f4d8f4b8f418f3d75a7f5a7b5a4b5a47584b5847581f581b20c320bf209720931e831e7f1e531e4eeb4f6b4eeb48eb486b08eb086b036b02e417e41764126411e3cfe3cf63c9e3c95688

private theorem cap11101111010111100Accepted : Accepted table cap11101111010111100Box cap11101111010111100Tree := by
  decide +kernel

private def cap11101111010111101Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (11 / 16, 23 / 32), (27 / 32, 7 / 8)]

private def cap11101111010111101Tree : Option PackedTree := decode 6 0xf796f7967790f790773d773cf737f7376ba16ba0eb9aeb9a6b566b55eb50eb505ef2cef2bef20ef1fee79ee78ee6eee6dd741d73fd734d733d6abd6aad6a0d69f10009cfbc87bc83bc3fbc3bb9bfb9bbb98fb98b5cd75cd35c9f5c9b5a875a835a575a52f790778f77877786f7377736f7317730f00e700df0097008efec6febefe96fe8de01ce01be012e011dfd8dfd7dfd2dfd1d734d733d726d725d6a0d69fd694d692a1aee7aee78ee6fee6dedd7edd6edcfedcdd6acd6aad6a1d69fd61cd61bd614d612bdcdfdcdddcc7dcc5db9fdb9ddb85db83ad43ad41ad2bad29ac29ac27ac13ac117b9bbb9b7b98bb987b73bb737b707b7035a835a7f5a535a4b584f584b5823581eb475d0b5d075cd75cd35ab35aaf5a875a83233f233b230f230b20f320ef20cb20c6eba0eb9feb9a6b99eb55eb556b506b4fe4676466e4616460e41de41d6418e41857ae6bae69ae4fae4dad43ad41ad2bad2991879185916b916990659063904f904d75cd35ccf5c9b5c975a835a7f5a535a4b3d3f3d3b3d233d1f3cc73cc33cb33caee7a7e7a767a467a3e798e79867966795e4616460e45a64596418e41864136412d0d6b566b556b50eb4feb0e6b0deb0a6b09641e641d6419641863d3e3d363d0e3d05d6a1d69fd695d693d614d612d609d607c832c830c827c825c7a1c7a0c796c79410009c88

private theorem cap11101111010111101Accepted : Accepted table cap11101111010111101Box cap11101111010111101Tree := by
  decide +kernel

private def cap1110111101011110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111010111100Tree <*> cap11101111010111101Tree

private theorem cap1110111101011110Accepted : Accepted table cap1110111101011110Box cap1110111101011110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111101011110Box 3 (midpoint cap1110111101011110Box 3) = cap11101111010111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010111100Accepted
  · have h : rightBox cap1110111101011110Box 3 (midpoint cap1110111101011110Box 3) = cap11101111010111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010111101Accepted

private def cap1110111101011111Box : Box := ![(47 / 40, 6 / 5), (819 / 1600, 441 / 800), (23 / 32, 3 / 4), (13 / 16, 7 / 8)]

private def cap1110111101011111Tree : Option PackedTree := decode 6 0xf7a377a2779df79cf7467745f74277416bacebabeba7eba6eb5f6b5eeb5b6b5a5ef3bef3aef2def2cee84ee83ee7aee79d74fd74ed742d741d6b6d6b5d6acd6abbde75de73de59de57dd07dd05dcf3dcf1ae9dae9bae83ae7fad6bad69ad57ad555aee8cee8bee7aee78ede3ede2edd7edd6d6bed6bdd6acd6aad626d625d61cd61ba75d675d5f5d3f5d375afb5af75adb5ad3239f23972377236f212b21272113210eeba7eba6eba16ba06b5b6b5a6b566b55646ee46de467e466e4226421e41e641d08004e5ad7dad7bad59ad55ac4dac4bac39ac3790959093907990758f618f5f8f4f8f4d48ef44ef43ef39ef38ee8bee8aee82ee81d757d756d74dd74cd6bdd6bcd6b4d6b3bde87de83de71de6fdd15dd13dd03dd01aeadaeabae99ae97ad79ad77ad67ad655f79cf79c7795f79577417740f73c773beba6eba66b9feb9f6b5a6b59eb556b54def38ef37ef2aef29ee81ee80ee77ee76d74cd74bd73ed73dd6b3d6b2d6a9d6a8ad7745f744f741774076f176f0f6ef76eeeb5eeb5deb5a6b596b12eb126b10eb105ee82ee80ee78ee76eddeedddedd6edd4d6b4d6b2d6aad6a8d621d620d61bd619a8ebabebaaeba6eba5eb5eeb5deb5a6b596472e471e46de46ce424e4246421e420dd74dd74cd73fd73ed6b4d6b3d6aad6a9c8dbc8dac8cdc8ccc843c842c83ac839bae99ae97ae7dae7bad67ad65ad53ad5191b591b39199919790859083907390715ad6bdd6bbd6aad6a8d625d624d61bd619c849c848c83ac838c7afc7aec7a6c7a5a43

private theorem cap1110111101011111Accepted : Accepted table cap1110111101011111Box cap1110111101011111Tree := by
  decide +kernel

private def cap111011110101111Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111101011110Tree <*> cap1110111101011111Tree

private theorem cap111011110101111Accepted : Accepted table cap111011110101111Box cap111011110101111Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011110101111Box 2 (midpoint cap111011110101111Box 2) = cap1110111101011110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101011110Accepted
  · have h : rightBox cap111011110101111Box 2 (midpoint cap111011110101111Box 2) = cap1110111101011111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101011111Accepted

private def cap11101111010111Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011110101110Tree <*> cap111011110101111Tree

private theorem cap11101111010111Accepted : Accepted table cap11101111010111Box cap11101111010111Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111010111Box 1 (midpoint cap11101111010111Box 1) = cap111011110101110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110101110Accepted
  · have h : rightBox cap11101111010111Box 1 (midpoint cap11101111010111Box 1) = cap111011110101111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011110101111Accepted

private def cap1110111101011Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111010110Tree <*> cap11101111010111Tree

private theorem cap1110111101011Accepted : Accepted table cap1110111101011Box cap1110111101011Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111101011Box 0 (midpoint cap1110111101011Box 0) = cap11101111010110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010110Accepted
  · have h : rightBox cap1110111101011Box 0 (midpoint cap1110111101011Box 0) = cap11101111010111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111010111Accepted

def cap111011110101Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111101010Tree <*> cap1110111101011Tree

theorem cap111011110101Accepted : Accepted table cap111011110101Box cap111011110101Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011110101Box 3 (midpoint cap111011110101Box 3) = cap1110111101010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101010Accepted
  · have h : rightBox cap111011110101Box 3 (midpoint cap111011110101Box 3) = cap1110111101011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111101011Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover28
