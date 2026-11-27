import D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option linter.style.longLine false

namespace D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover45

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.Factored

open WuCubicLowSpectrumCover (Box Tree)
open private midpoint from D5.S3.Quantum.Semigroups.WuCubicLowSpectrumCover
open private leftBox rightBox from D5.S0.Certificates.BoxCover.CheckedRationalBoxCover

open D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapRows (table)

def cap111011111110Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (7 / 8, 1)]

private def cap1110111111100Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap11101111111000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111110000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap1110111111100000Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (5 / 8, 21 / 32), (7 / 8, 15 / 16)]

private def cap1110111111100000Tree : Option PackedTree := decode 6 0x394b794b5949d949b92df92dd92c792c57a0179fd79e779e5789d7899788578837293b2937290b2907258f258b2563255ef3cef3caf39ef39af10af106f0e2f0deac96fc96ec963c962c89bc89ac88dc88cbc4ebc4cbc42bc41bba8bba7bb9cbb9bb92c792c592b192af911b9119910190ff788578837871786f773977377723772151bd00bcfebcf3bcf2bc4ebc4cbc42bc41b472b470b464b462b3ceb3ccb3c1b3bfb79e779e579cf79cd788578837871786f68c968c568b168af6783677f676b676955e275e265e215e20ddd45dd3ddce5dcdd9e759e659e0d9dfd98fd98f59895988dbc42bc41bc38bc37bb9cbb9bbb91bb90b3c1b3bfb3b5b3b4b312b311b306b305a88ca5aca59ca4dca4cc96ec96dc962c961bcfebcfdbcf2bcf1bc4cbc4bbc41bc40b94b394b19499949792db92d992c392c179fb79f979e379df789778957881787f5e526e5266520e52064b164b0e4abe4ab5e795e78de735e72de20de205e1bde1b5ca4cca4bca40ca3fc961c960c956c955bcf1bcefbce5bce4bc40bc3fbc36bc35ad64b764b6e4b164b0e44d644ce4466445de265e25de20de205dd3ddd35dcdddcd5c96dc96cc961c960c899c898c88bc88abc4bbc4abc40bc3fbba6bba5bb9abb99af258b2587255f255b2233222f21ff21faf106f102f0def0daee6eee6aee42ee3ee4b0e4b064ab64aae445e445643f643ede205e1fde1b5e1addcd5dccddc7ddc7568de7f5e7ede795e78de265e25de20de205a385a37da315a30d9e659e5d9dfd9df5bcfdbcfcbcf1bcefbc4bbc4abc40bc3fb46fb46eb461b460b3cbb3cab3beb3bdaef3caf3c6f39af396f106f102f0def0dad18ad186d15ed15acefecefaced2cecede78de77de72de725e205e1fde1b5e1ada30da305a2b5a2ad9df59ded9d9d9d956af132f12ef106f102ee9eee9aee6eee6acf32cf2ecefecefacc7acc76cc46cc42de25de255e205e1fddd35dd2ddcd5dccd9e5d9e559df59ded98ed98e59885987d778837881786f786d773777357721771f677f677d6769676766236621660b66096f102f0fef0daf0d6ee6aee66ee3eee3acefacef6cecececacc42cc3ecc12cc0eb443

private theorem cap1110111111100000Accepted : Accepted table cap1110111111100000Box cap1110111111100000Tree := by
  decide +kernel

private def cap1110111111100001Box : Box := ![(23 / 20, 47 / 40), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (7 / 8, 15 / 16)]

private def cap1110111111100001Tree : Option PackedTree := decode 7 0x394fb94f794d794d39319931792f992f77a397a357a1d7a1978cf78cb78b778b3729af29a7296f296b25f325ef25bf25baf43af432f402f3faf16ef166f13af132ac98cc98bc97cc97bc8b8c8b7c8a8c8a7bc67bc65bc5bbc59bbc1bbbfbbb4bbb3b92f992f792df92dd9151914f9137913578b778b3789d7899776977677751774f51bd1cbd1bbd0ebd0dbc67bc66bc5bbc5ab491b490b480b47fb3e7b3e6b3dbb3dab7a377a357a1b7a1978cd78cb78b578b36921691f68ff68fd67cd67cb67b567b35de875e86de805e7fde2dde2d5e275e26da405a3fda395a38d9edd9ed59e759e6dbd0dbd0cbcffbcfebc5abc59bc4dbc4cb47fb47eb471b470b3dab3d9b3cdb3ccad5e33de32de2dde2cdde0dddfddda5dd9d9f3d9f2d9edd9ecd99c599bd995d9955bc5bbc59bc4ebc4cbbb4bbb3bba8bba7b3dbb3d9b3ceb3ccb32bb32ab31fb31ea88ca7bca7aca69ca68c98bc98ac97bc97abd1abd19bd0cbd0bbc65bc64bc59bc58b94f594f394d194cf9315931392f592f1826d826b82538251819381918185818200813b04db04d704a704a303270323030b0306f466f462f42ef42af192f18ef162f159010270794d394d194b594b392f792f592dd92db7a197a1779fd79fb78b378b178997897729a3299f2967296325eb25e325b725b304a704a304870483030b030702eb02e6e094e0946090e09060616060e05d605cde85de855e7ede7e5e2c5e2b5e25de2550d64c5e4c564bde4bd645be45b6453e4535e32de325e2cde2c5ddfdddf5dd9ddd95c98ac989c97ac979c8b6c8b5c8a6c8a5bc64bc63bc58bc57bbbebbbdbbb2bbb110109cf25ef25eb25bb25b7229f229b226b2266f166f162f132f12eeeceeecaee9eee9ae4bd64bce4b6e4b664536452e44ce44c5e2c5e2bde25de255dd95dd8ddd35dd2a0204e68de8d5e8cde865e85de32de325e2cde2c5a47da475a3f5a3ed9f2d9f259ecd9ec00204ebd19bd18bd0bbd0abc64bc63bc58bc56b7c4b7c3b7bcb7bbb77eb77db778b77740409d6f896f876f796f776efd6efb6ef16eef691b691968fb68f967c967c767b167ac8081383bd0cbd0bbcfebcfdbc59bc58bc4cbc4bb47eb47db470b46fb3d9b3d8b3ccb3cbb7a177a1579fb79f978b178ad789778956f796f776f6d6f6b6ef16eef6ee56ee36def2deeededaded6dde2dddeddcaddc6d1f6d1f2d1bed1bacf62cf5acf2ecf2a86af196f192f166f162eefeeefaeeceeecacf96cf92cf66cf62ccdeccdaccaacca6de325e31de2c5e2bdddf5ddeddd95dd8d9f259f1d9ec59ebd99b599ad994d99408084e778b378b17899789777677765774f774d67b367b16799679766556653663d663b6f162f15ef12ef12aeecaeec6ee9aee96cf62cf5ecf2ecf2acca6cca2cc76cc71010273443

private theorem cap1110111111100001Accepted : Accepted table cap1110111111100001Box cap1110111111100001Tree := by
  decide +kernel

private def cap111011111110000Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111111100000Tree <*> cap1110111111100001Tree

private theorem cap111011111110000Accepted : Accepted table cap111011111110000Box cap111011111110000Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011111110000Box 2 (midpoint cap111011111110000Box 2) = cap1110111111100000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100000Accepted
  · have h : rightBox cap111011111110000Box 2 (midpoint cap111011111110000Box 2) = cap1110111111100001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100001Accepted

private def cap111011111110001Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap1110111111100010Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (5 / 8, 21 / 32), (7 / 8, 15 / 16)]

private def cap1110111111100010Tree : Option PackedTree := decode 6 0xe6a9e6a966a3e6a365d7e5d765d265d1dfae5fad5fa8dfa85f03df02defddefd5cd47cd46cd27cd26cba4cba3cb9bcb9abf51bf50bf49bf48bdfbbdfabdf2bdf1ab2ebf2ebb2e932e8f296f296b293b2936f81ef816f7eef7eaf402f3faf3cef3cae5d265d1e5cde5cd65276526e5216520defddefd5ef95ef8de79de795e73de73546fd72fd6afd46fd42f81ef816f7eef7eada26da1ed9f2d9ead5a2d59ad572d56adfa8dfa85fa4dfa45efddefd5ef95ef8db3e5b3d5b395b38daae5aad5aa8daa8557c0f7c0b7bf77bf57a0179fd79e779e56ad16acd6ab96ab568e568e168c968c56f7eef7eaf7caf7c6f3cef3caf39ef39ad572d56ad546d542d192d18ad162d15ea23354b3547351b35172ebb2eb72e8f2e8afd6afd66fd42fd3ef816f812f7eaf7e6e6a8e6a866a2e6a265d6e5d665d165d0dfacdfac5fa7dfa75f025f01defcdefc579a8d9a899a4d9a4b97479743973597337ea17e9d7e917e8f7bf57bf17be37bdf565d765d6e5d1e5d1652d652ce526e5265f02df025efd5efcde7f5e7ede795e78dcbadcbaccba2cba1ca59ca58ca4cca4bbe04be03bdf9bdf8bcfdbcfcbcf1bcefaf2e8f2e872e6b2e672937292f290728fef7eaf7e2f7c6f7bef3caf3c2f39af39000127237eb57eb37ea17e9f7c0b7c097bf57bf36d0f6d0d6cf56cf36acd6acb6ab56ab36fd66fd62fd3efd3af812f80ef7e6f7e2da1ada16d9e6d9e2d596d592d566d562bbf50bf4ebf48bf47bdfabdf8bdf1bdefb67ab678b671b670b55ab558b550b54eaaf816f812f7eaf7e6f3faf3f6f3caf3c6d59ad596d56ad566d1c2d1bed18ad186df025f01defcdefc5e7ede7e5e78de77dab2dab25aacdaac5a37da375a30da30577bf57bf37be37be179e579e379cd79cb6ab56ab36aa16a9f68c568c368af68ad6f7e6f7e2f7c2f7bef3c6f3bef396f392d566d562d53ed53ad186d182d15ad156b443

private theorem cap1110111111100010Accepted : Accepted table cap1110111111100010Box cap1110111111100010Tree := by
  decide +kernel

private def cap1110111111100011Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (21 / 32, 11 / 16), (7 / 8, 15 / 16)]

private def cap11101111111000110Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (21 / 32, 11 / 16), (7 / 8, 29 / 32)]

private def cap111011111110001100Box : Box := ![(23 / 20, 93 / 80), (189 / 320, 63 / 100), (21 / 32, 11 / 16), (7 / 8, 29 / 32)]

private def cap111011111110001100Tree : Option PackedTree := decode 6 0x37ee77ee57ecd7ecb7c3f7c3d7c257c237281727f72737271709d709b708f708d6e502e4fee4e6e4e2e13ae136e11ee11ada8eda8ada52da4ed5fed5fad5cad5c68bf72bf71bf65bf64becbbecabec5bec4b93fb93eb938b937b8c0b8bfb8bbb8bab7d977d957d8b7d897c3d7c3b7c237c1f7181717f71777175709b7099708d708b4dc9fdc9f5c9c5c9bdc605c5fdc5ddc5d5b515b50db49db495b06db065b045b03db8c0b8bfb8bbb8bab84db84cb846b845b60db60cb608b607b57eb57db571b570a43bf66bf65bf5abf59be12be11be05be04b694b693b687b686b572b571b566b565b7ecb7ec97eb37eb17c237c1f7c097c077271726f72677265708d708b7081707f6e4e2e4dee4cee4cae11ae116e102e0feda4eda4ada1ada16d5c6d5c2d596d59286af87ef87af84af846f46af466f432f42ee13ae136e11ee11adf16df12def6def2dc275c26dc23dc235be2dbe25bdedbde5abfdabf5ab95ab8da47da46da3f5a3ed17c3d7c3b7c237c1f7b477b457b3b7b39709b7099708d708b700970076ffd6ffb6f68ef68af676f672f466f45ef42ef42ae012e00edffadff6df12df0adef2deee9b84db84cb846b845b804b803b7feb7fdb57eb57db571b570b519b518b514b513b700970076ffd6ffb6f896f856f796f776a336a316a296a27691b691768fb68f94877c257c237c0b7c097a197a1779fd79fb6ae56ae36acd6acb68fd68fb68e168df6f846f83ef812f80ef42ef42af3f6f3f2e11ae116e102e0fedef2deeededaded6dc235c22dc205c1fdbde5bdddbdb5bdadab8dab85ab2dab25a3eda3e5a37da3750d1

private theorem cap111011111110001100Accepted : Accepted table cap111011111110001100Box cap111011111110001100Tree := by
  decide +kernel

private def cap111011111110001101Box : Box := ![(93 / 80, 47 / 40), (189 / 320, 63 / 100), (21 / 32, 11 / 16), (7 / 8, 29 / 32)]

private def cap111011111110001101Tree : Option PackedTree := decode 6 0xe6b666b5e6af66aee5e365e2e5dd65dce19a6199e1966195e100e10060fc60fbdc334c333c32cc32bc201c200c1f8c1f7bf73bf72bf66bf65be1fbe1ebe12be11a335af35ab357735732f172f132ee72ee30ccf0ccb0caf0cab080307ff07df07d8001276199e1996195e1956145e1456142e1425fb95fb8dfb2dfb25f65df655f62df625c28bc28ac285c284c200c1fec1f7c1f6becbbecabec5bec4be1ebe1dbe11be0fa43cd5ecd5dcd52cd51cbbacbb9cbaecbadbf66bf65bf5abf59be12be11be05be04b9abb9ab99aa39aa197739771975b97597ecb7ec97eb37eb17c237c217c097c06000939acbc6cbc5cbbacbb9ca7bca7aca69ca68c201c200c1f8c1f7c137c136c12ac129b8403840183f183ef826f826d825582537c3f7c3d7c257c237a357a337a197a17465e2e5e265dce5dc653d653ce5346533e10060ffe0fbe0fb609b609ae094e09400224ec200c1fec1f7c1f6c193c192c18ac189be1ebe1dbe11be0fbda3bda2bd9dbd9cb8327832583158313826d8269825382517b477b457b3b7b397a337a2f7a177a1548797759773975d975b94d394d194b594b37c257c237c0b7c097a197a1779fd79fb72ee72ee32eb72eb329a3299f2967296307df07db07c307bf04a704a304870482e0fbe0fb60f860f7e094e0946090e0905f08df07df025f01de85de855e7ede7e50d1

private theorem cap111011111110001101Accepted : Accepted table cap111011111110001101Box cap111011111110001101Tree := by
  decide +kernel

private def cap11101111111000110Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap111011111110001100Tree <*> cap111011111110001101Tree

private theorem cap11101111111000110Accepted : Accepted table cap11101111111000110Box cap11101111111000110Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap11101111111000110Box 0 (midpoint cap11101111111000110Box 0) = cap111011111110001100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111110001100Accepted
  · have h : rightBox cap11101111111000110Box 0 (midpoint cap11101111111000110Box 0) = cap111011111110001101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111110001101Accepted

private def cap11101111111000111Box : Box := ![(23 / 20, 47 / 40), (189 / 320, 63 / 100), (21 / 32, 11 / 16), (29 / 32, 15 / 16)]

private def cap11101111111000111Tree : Option PackedTree := decode 5 0x39add9adb9ac19abf9791978f977997777eeb7ee97ed17ecf7c437c417c297c27735b735b3357f357b2f1f2f1b2eef2eeafdd2fdcefd9efd9af882f87ef84ef84abcd60cd5ecd53cd52cbbccbbacbafcbaebf68bf66bf5cbf5abe14be12be07be05ab2f232f1f2ef32eef29f729f329af29aaf886f882f852f84ef472f46ef43af436e5e3e5e365dde5dd653e653de5356534df105f0fdf09df095e8dde8d5e86de865797799775975f975d94d794d394b794b57c297c257c0f7c0b7a1d7a197a0179fd51bf75bf74bf68bf67be21be20be14be13b6a5b6a4b696b695b581b580b574b573b7ee97ee77ecf7ecd7c417c3f7c277c256d496d476d2b6d296b016aff6ae76ae55dfb45fb3dfae5faddf0a5f09df03df035b4b5b4adb44db445aba5ab9dab45ab3dbf67bf66bf5bbf5abe13be12be06be05b695b694b688b687b573b572b567b566ad5f10df105f0a5f09de8e5e8dde875e86dac0dac05aba5ab9da48da485a405a3fdbe20be1fbe13be12bd1bbd1abd0dbd0cb580b57fb573b572b490b48fb47fb47eaef852f84ef81ef81af43af436f402f3fed5d2d5ced5a2d59ed202d1fed1cad1c6df09df095f035f02de86de865e7fde7f5ab9dab95ab3dab35a3fda3f5a38da385688

private theorem cap11101111111000111Accepted : Accepted table cap11101111111000111Box cap11101111111000111Tree := by
  decide +kernel

private def cap1110111111100011Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap11101111111000110Tree <*> cap11101111111000111Tree

private theorem cap1110111111100011Accepted : Accepted table cap1110111111100011Box cap1110111111100011Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap1110111111100011Box 3 (midpoint cap1110111111100011Box 3) = cap11101111111000110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111111000110Accepted
  · have h : rightBox cap1110111111100011Box 3 (midpoint cap1110111111100011Box 3) = cap11101111111000111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111111000111Accepted

private def cap111011111110001Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111111100010Tree <*> cap1110111111100011Tree

private theorem cap111011111110001Accepted : Accepted table cap111011111110001Box cap111011111110001Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011111110001Box 2 (midpoint cap111011111110001Box 2) = cap1110111111100010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100010Accepted
  · have h : rightBox cap111011111110001Box 2 (midpoint cap111011111110001Box 2) = cap1110111111100011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100011Accepted

private def cap11101111111000Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011111110000Tree <*> cap111011111110001Tree

private theorem cap11101111111000Accepted : Accepted table cap11101111111000Box cap11101111111000Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111111000Box 1 (midpoint cap11101111111000Box 1) = cap111011111110000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111110000Accepted
  · have h : rightBox cap11101111111000Box 1 (midpoint cap11101111111000Box 1) = cap111011111110001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111110001Accepted

private def cap11101111111001Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap111011111110010Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap1110111111100100Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (5 / 8, 21 / 32), (7 / 8, 15 / 16)]

private def cap1110111111100100Tree : Option PackedTree := decode 6 0x3e237e235e205e203dfd1dfcfdfa1df9fb1cfb1cdb1a1b19fafb5afb3af85af837bfa3bf9fbf43bf3fbbcfbbcbbb53bb4f5f6b5f675f0b5f075c3f5c3b5bc75bc29d8e7d8e6d8d0d8cfd7dad7d9d7c2d7c1ca5bca5aca42ca41c96fc96ec958c957bafb5afb3af85af83ae1fae1dade3ade192df92dd92b192af91379135910190ff48f11af119f10ef10defe7efe6efdaefd9d8e6d8e5d8dbd8dad7d9d7d8d7cdd7ccbe233e231e21be219dfcddfcbdfb3dfb1b1cbb1c9b1b5b1b3afb1afafaf99af955f88778867880f88077ed77ec77e7f7e76c6dec6cec67ec66ebe6ebe5ebe0ebdf80024e5dfcfdfcddfb5dfb3dde5dde3ddc7ddc5afb3afb1af9baf99ae1dae1bae01adff7bf9bbf97bf67bf63bbc7bbc3bb8bbb875f635f5f5f335f2b5c375c335bff5bf6befdaefd8efcfefceeee3eee1eed3eed2d7cdd7cbd7c1d7bfd700d6fed6f0d6ee00449c8ec736c72ec6dec6d6becebec6be6ebe6652d652ce526e52664b764b6e4b164b0dd8e5d8e4d8dad8d9d7d8d7d7d7ccd7caca59ca58ca4cca4bc96dc96cc961c960af636f636b633f633b5f375f335f075f032937293329072903258b2587255f255aec6d6c6cec676c66ebe66be56be06bdfe5266525e520651fe4b0e4b064ab64aad6b5f675f635f375f335c3b5c375c035bff25bb25b7258b2587226b22672233222eebec6bebebe66be56b86eb866b7feb7ee4b6e4b664b0e4b0644ce44c6445e44557af9baf99af83af81ae01adffade1addf92c592c392af92ad9119911790ff90fd75f335f2b5f035eff5bff5bf75bbf5bbb25872583255b2557222f222b21fb21f6b443

private theorem cap1110111111100100Accepted : Accepted table cap1110111111100100Box cap1110111111100100Tree := by
  decide +kernel

private def cap1110111111100101Box : Box := ![(47 / 40, 6 / 5), (441 / 800, 189 / 320), (21 / 32, 11 / 16), (7 / 8, 15 / 16)]

private def cap1110111111100101Tree : Option PackedTree := decode 7 0x3e27be279e237e235e017e015dfd1dfcfb213b211b1cfb1cdaff9aff7afb5afb37c02fc02bbfa3bf9fbc4bbc47bbcfbbcb5ff35fef5f6b5f675cab5ca75c3f5c3a9d909d908d8f5d8f4d7fcd7fbd7e6d7e5ca7dca7bca6bca69c98cc98bc97cc97bbb1ebb1e9b1cfb1cdafcdafcbafb5afb394d794d394b794b592f992f792df92dd56bfe6bfdebed6beceb956b94eb87eb8764c664c5e4b7e4b7645c645be44de44d523c4f3c4efc4a3c49fc02bc027bfd7bfd36423641f63d363cf5fef5feb5f975f92f89df89d7893f8937804f80477fa77f9f0a870a7f0a170a0f0417040f038f0385e150e14fe142e141e082e081e071e070d907d906d8f3d8f2d7fad7f9d7e4d7e3a1f8947893f88d788cf7faf7fa77f3f7f36c7a6c79ec736c72ebf2ebf26becebec5f127f126f119f118eff4eff3efe6efe5d8f3d8f2d8e5d8e4d7e4d7e3d7d8d7d7ad78057804f7faf7fa7788f7887780f7806bfdebfd6bf2ebf26b94eb946b8eeb8e5f009f008eff4eff3ef10ef0fef00eeffd7fad7f9d7e4d7e3d728d727d71cd71bafbfd7bfd3bf9fbf9bbc07bc03bbcbbbc75f975f935f675f635c775c735c3b5c36f7fa77f9f7f377f2f780777ff778f7786bf26bf1ebec6bebeb8e6b8deb86eb86568ec846c83ec7a6c79ebfdebfd6bf2ebf2653de53d6534e53464c5e4c564bde4bd5d907d906d8f3d8f2d7fad7f9d7e4d7e3d032d031d026d025cf98cf97cf8bcf8aba065a063a04da04b9f319f2f9f179f1594f594f394d194cf9315931392f592f143d8f4d8f3d8e6d8e5d7e5d7e4d7d9d7d8ca69ca68ca5aca59c97bc97ac96ec96dbb1e7b1e5b1cbb1c9afc9afc7afb1afafa04da04ba03da03b9f179f159f079f057409b4097407b40773e2f3e2b3e0f3e0b29a3299f2967296325eb25e325b725b286b5fef5feb5f975f935ca75ca35c775c73262f262b25ef25eb22df22db229f229aebfd6bfcebf26bf1eb946b93eb8e6b8de4c564c4e4bd64bce45b645ae453645280084e7afcbafc9afb3afb1ae3bae39ae1dae1b92f792f592dd92db914f914d9135913375f935f8f5f635f5f5c735c6f5c375c3325eb25e725b725b3229b229722672260010273443

private theorem cap1110111111100101Accepted : Accepted table cap1110111111100101Box cap1110111111100101Tree := by
  decide +kernel

private def cap111011111110010Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111111100100Tree <*> cap1110111111100101Tree

private theorem cap111011111110010Accepted : Accepted table cap111011111110010Box cap111011111110010Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011111110010Box 2 (midpoint cap111011111110010Box 2) = cap1110111111100100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100100Accepted
  · have h : rightBox cap111011111110010Box 2 (midpoint cap111011111110010Box 2) = cap1110111111100101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100101Accepted

private def cap111011111110011Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (5 / 8, 11 / 16), (7 / 8, 15 / 16)]

private def cap1110111111100110Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (5 / 8, 21 / 32), (7 / 8, 15 / 16)]

private def cap1110111111100110Tree : Option PackedTree := decode 6 0x3eb35eb33ea09ea07e5abe5a9e585e583b933b931b873b871b4c7b4c5b4a1b49f7cb57cb53cb0bcb07c46fc46bc40bc407698f698b6943693f639f639b6343633e9dc99dc98dc39dc38da63da62da50da4fcd53cd52cd27cd26cbafcbaecb9bcb9abb4c7b4c5b4a1b49fb1cfb1cdb1a1b19f975f975d9737973594b794b59485948348f599f597f58ef58df2d4f2d2f2caf2c8dc98dc96dc8edc8dda62da60da58da56beb1deb1bea07ea05e595e591e583e581b91db91bb871b86fb4b1b4adb49fb49d5796a7969f9657964f88d788cf8877886ed316d30ed2c6d2bec736c72ec6dec6d5f2d3f2d2f2c9f2c8f119f118f10df10cda61da60da57da56d8e5d8e4d8dad8d9afcb2bcb23cb07cb03c43bc433c407c4036963695b693f693b636f6367633f6336a3b931b92db91db91bb4c5b4c1b4b1b4ad9aa59aa19a8d9a89975d9759974797437723b723770e370df6963695b693f693b351b3513349b34972e8f2e872e6b2e66ada62da61da58da57d8e6d8e5d8dbd8dacbaecbadcba3cba2ca5aca59ca4dca4cbb4c3b4c1b4afb4adb1cbb1c9b1b5b1b3975b97599745974394b394b1949994975ed2c6d2b6d27ed276c6dec6cec67ec66e5d1e5d0e5cd65cce526e525e520e51fd443

private theorem cap1110111111100110Accepted : Accepted table cap1110111111100110Box cap1110111111100110Tree := by
  decide +kernel

private def cap1110111111100111Box : Box := ![(47 / 40, 6 / 5), (189 / 320, 63 / 100), (21 / 32, 11 / 16), (7 / 8, 15 / 16)]

private def cap1110111111100111Tree : Option PackedTree := decode 7 0xfad9fad97ad37ad2f976f9767970796fee586e57ee526e51ed3e6d3ded376d36df5a6f5a5f59af599f2e0f2dff2d5f2d4dca4dca3dc99dc98da6eda6dda63da62abcbb7cbb3cb83cb7fc4f7c4f3c4a7c4a369f369ef69bb69b76427642363d763d2f970796ff96af96a7894f894788df88d6d376d36ed31ed316c7aec7a6c73ec7354772c372bf7293728f69f369ef69bb69b735bb35b33583357b2f232f1b2ef32eeaee526e51ee4cee4c6d376d36ed31ed3166b066af66a9e6a965de65dd65d7e5d755b4f9b4f7b4ddb4dbb213b211b1ebb1e99791978d9779977594fb94f794d794d3769bb69b7698f698b63d763d3639f639b2ef32eeb2ebf2ebb29af29a7296f296aa23d6cbd6c7d697d693cbb3cbafcb7fcb7b72bf72bb728f728b69ef69eb69b769b2fad8fad87ad27ad1f975f975796f796ef27df27d727a7279f14cf14c71487147de4fbe4fae4f4e4f3e299e298e290e28fdcaedcaddca2dca1da7ada79da6cda6ba1fad2fad27accfacc796ff96f796a7969ee51ee516e4c6e4bed36ed366d316d30df5a4f5a3f598f597f2def2ddf2d3f2d2dca2dca1dc97dc96da6cda6bda61da60ad79767975f96ff96f789e789df8947893ed3ded3d6d36ed366c846c83ec7a6c79df2ebf2eaf2def2ddf13bf13af127f126e299e298e290e28fe150e14fe142e141bc533c531c521c51fc2a1c29fc285c283b4f5b4f3b4d9b4d7b20fb20db1e7b1e543f2dff2def2d4f2d3f128f127f11af119da6dda6cda62da61d8f4d8f3d8e6d8e5be5bde5bbe5a7e5a5e24fe24de233e231b4d9b4d7b4c3b4c1b1e7b1e5b1cbb1c95a3b95fb95db947b945b4f7b4f5b4dbb4d99ad99ad79abd9abb978d978b97759773772bb72b7728b728769eb69e769b369af4b0b4b074aef4aeb44a744a344874482e9616960e95de95d6894e8946890e89066b5e6b566aee6ae65e2e5e265dce5dc50f728f728b7263725f69b769b3698b6987357b3577354b35472eeb2ee72ebb2eb6ee516e50ee4bee4b6d366d35ed30ed3066aee6ae66a8e6a865dce5dc65d6e5d656b69ef69eb69b769b36423641f63d363cf2f1b2f172eeb2ee729ef29eb29a729a2ed3d6d3ced366d35ec83ec836c79ec796894e8946890e89068196818e8136812dd129d128d121d120d032d031d026d025cbc5cbc4cbb9cbb8ca7aca79ca68ca67a1ed36ed366d316d30ec7a6c79ec736c72e5dd65dce5d765d6e534e534652d652cdda6cda6bda61da60d8f3d8f2d8e5d8e4d121d120d11ad119d026d025d01ed01dba243a241a235a233a04da04ba03da03b97739771975b975994d194cf94b394b143443

private theorem cap1110111111100111Accepted : Accepted table cap1110111111100111Box cap1110111111100111Tree := by
  decide +kernel

private def cap111011111110011Tree : Option PackedTree :=
  PackedTree.split 2 <$> cap1110111111100110Tree <*> cap1110111111100111Tree

private theorem cap111011111110011Accepted : Accepted table cap111011111110011Box cap111011111110011Tree := by
  apply acceptedSplit 2
  · have h : leftBox cap111011111110011Box 2 (midpoint cap111011111110011Box 2) = cap1110111111100110Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100110Accepted
  · have h : rightBox cap111011111110011Box 2 (midpoint cap111011111110011Box 2) = cap1110111111100111Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100111Accepted

private def cap11101111111001Tree : Option PackedTree :=
  PackedTree.split 1 <$> cap111011111110010Tree <*> cap111011111110011Tree

private theorem cap11101111111001Accepted : Accepted table cap11101111111001Box cap11101111111001Tree := by
  apply acceptedSplit 1
  · have h : leftBox cap11101111111001Box 1 (midpoint cap11101111111001Box 1) = cap111011111110010Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111110010Accepted
  · have h : rightBox cap11101111111001Box 1 (midpoint cap11101111111001Box 1) = cap111011111110011Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap111011111110011Accepted

private def cap1110111111100Tree : Option PackedTree :=
  PackedTree.split 0 <$> cap11101111111000Tree <*> cap11101111111001Tree

private theorem cap1110111111100Accepted : Accepted table cap1110111111100Box cap1110111111100Tree := by
  apply acceptedSplit 0
  · have h : leftBox cap1110111111100Box 0 (midpoint cap1110111111100Box 0) = cap11101111111000Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111111000Accepted
  · have h : rightBox cap1110111111100Box 0 (midpoint cap1110111111100Box 0) = cap11101111111001Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap11101111111001Accepted

private def cap1110111111101Box : Box := ![(23 / 20, 6 / 5), (441 / 800, 63 / 100), (5 / 8, 11 / 16), (15 / 16, 1)]

private def cap1110111111101Tree : Option PackedTree := decode 7 0x3eb6beb69eb39eb37e27fe27de23be2399ae19adf9aab9aa994ff94fd94bb94b97d6d3d6cfd66fd66bc4fbc4f7c473c46f72c772c3726b7267642b642763a3639eee58ee586e4d6e4cec856c84ec746c73e6b7e6b766aa66a9e53f653ee52e652dd0fd673d66fd41bd417c477c473c413c40f3557355334a734a3297729732913290efacdfacd7a82fa82788e788df881f8816e4d6e4cee1d6e1cec746c73ec68ec685dc9adc99dc3adc39d8e8d8e7d8d1d8d0cd54cd53cd28cd27ca5cca5bca43ca42a1af13ff13ef11df11cef14ef13eef5eef4ca7fca7eca5dca5cc8bac8b9c89dc89cbe27de27be239e237de27de25dde9dde7b215b213b1d1b1cfae57ae55ae21ae1f7642b642763a3639f5caf5cab5c435c3f29fb29f72973296f22e722e32273226e87e23be239e209e207ddebdde9ddadddab94bb94b994899487913b9139910591037c473c46fc40fc40bbbd3bbcfbb57bb5363a3639f634763435c435c3f5bcb5bc6ec746c73ec68ec686b886b87eb796b78e52e652de521e521644e644de440e44050d1cd70cd6fcd55cd54ca7fca7eca5dca5cb6a7b6a6b68bb68ab493b492b475b474b9adf9add9aa99aa7979397919761975f7eed7eeb7ebb7eb97c457c437c117c0f72f272f232ec32ebf29fb29f72973296ef88af886f822f81ef476f472f406f4029bf76bf75bf5dbf5cbe22be21be08be07b6a6b6a5b68ab689b582b581b569b568b7c457c437c117c0f7a3b7a397a037a016b056b036ad36ad16925692368e968e54879aab9aa99a539a5194bb94b9948994876d176d156ce96ce768eb68e968b568b373553354f34a3349f2973296f290f290afd76fd72fd2afd26f406f402f3a2f39edfaedfae5fa55fa4de80de805e745e73db455b44db39db395a3a5a39da2cda2c00024e0d653fe53f652ee52e645d645ce44ee44e5a49da495a3ada3a599d599cd990d9905ca7eca7dca5cca5bc8b9c8b8c89cc89bbd1dbd1cbd01bd00bbc2bbc1bba9bba8b7a3b7a397a037a0177857783775377516925692368e968e7667366716641663e0021383ca5dca5cca44ca43c89dc89cc882c881b475b474b45ab459b321b320b308b307b94b994b79487948591399137910391017a037a0179d179cf77537751772577236f406f402f3a2f39eeea6eea2ee4aee46d1d2d1ced166d162cc82cc7ecc1ecc18010270688

private theorem cap1110111111101Accepted : Accepted table cap1110111111101Box cap1110111111101Tree := by
  decide +kernel

def cap111011111110Tree : Option PackedTree :=
  PackedTree.split 3 <$> cap1110111111100Tree <*> cap1110111111101Tree

theorem cap111011111110Accepted : Accepted table cap111011111110Box cap111011111110Tree := by
  apply acceptedSplit 3
  · have h : leftBox cap111011111110Box 3 (midpoint cap111011111110Box 3) = cap1110111111100Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111100Accepted
  · have h : rightBox cap111011111110Box 3 (midpoint cap111011111110Box 3) = cap1110111111101Box := by
      funext i
      fin_cases i <;> decide +kernel
    simpa only [h] using cap1110111111101Accepted

end D5.S3.Quantum.Semigroups.WuCubicLowSpectrum.CapCover45
