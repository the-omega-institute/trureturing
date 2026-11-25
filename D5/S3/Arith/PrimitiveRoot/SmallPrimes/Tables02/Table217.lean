/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table217
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table217.pv815261
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table100

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr815261 : PrimeCertificate 815261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv40763]) (by decide +kernel)
def pv815261 : PrimeValue := ⟨815261, pr815261⟩
private theorem pr815341 : PrimeCertificate 815341 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv107,pv127]) (by decide +kernel)
def pv815341 : PrimeValue := ⟨815341, pr815341⟩
private theorem pr815413 : PrimeCertificate 815413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv5227]) (by decide +kernel)
def pv815413 : PrimeValue := ⟨815413, pr815413⟩
private theorem pr815587 : PrimeCertificate 815587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv181,pv751]) (by decide +kernel)
def pv815587 : PrimeValue := ⟨815587, pr815587⟩
private theorem pr815831 : PrimeCertificate 815831 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv17,pv4799]) (by decide +kernel)
def pv815831 : PrimeValue := ⟨815831, pr815831⟩
private theorem pr816157 : PrimeCertificate 816157 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv229]) (by decide +kernel)
def pv816157 : PrimeValue := ⟨816157, pr816157⟩
private theorem pr816163 : PrimeCertificate 816163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv136027]) (by decide +kernel)
def pv816163 : PrimeValue := ⟨816163, pr816163⟩
private theorem pr816203 : PrimeCertificate 816203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv47,pv457]) (by decide +kernel)
def pv816203 : PrimeValue := ⟨816203, pr816203⟩
private theorem pr816227 : PrimeCertificate 816227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv9491]) (by decide +kernel)
def pv816227 : PrimeValue := ⟨816227, pr816227⟩
private theorem pr816317 : PrimeCertificate 816317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv467]) (by decide +kernel)
def pv816317 : PrimeValue := ⟨816317, pr816317⟩
private theorem pr816353 : PrimeCertificate 816353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv263]) (by decide +kernel)
def pv816353 : PrimeValue := ⟨816353, pr816353⟩
private theorem pr816367 : PrimeCertificate 816367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv359,pv379]) (by decide +kernel)
def pv816367 : PrimeValue := ⟨816367, pr816367⟩
private theorem pr816587 : PrimeCertificate 816587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv281,pv1453]) (by decide +kernel)
def pv816587 : PrimeValue := ⟨816587, pr816587⟩
private theorem pr816667 : PrimeCertificate 816667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv136111]) (by decide +kernel)
def pv816667 : PrimeValue := ⟨816667, pr816667⟩
private theorem pr816743 : PrimeCertificate 816743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv9497]) (by decide +kernel)
def pv816743 : PrimeValue := ⟨816743, pr816743⟩
private theorem pr816821 : PrimeCertificate 816821 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv40841]) (by decide +kernel)
def pv816821 : PrimeValue := ⟨816821, pr816821⟩
private theorem pr816941 : PrimeCertificate 816941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv40847]) (by decide +kernel)
def pv816941 : PrimeValue := ⟨816941, pr816941⟩
private theorem pr816947 : PrimeCertificate 816947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2417]) (by decide +kernel)
def pv816947 : PrimeValue := ⟨816947, pr816947⟩
private theorem pr817337 : PrimeCertificate 817337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv29,pv271]) (by decide +kernel)
def pv817337 : PrimeValue := ⟨817337, pr817337⟩
private theorem pr817483 : PrimeCertificate 817483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv136247]) (by decide +kernel)
def pv817483 : PrimeValue := ⟨817483, pr817483⟩
private theorem pr817603 : PrimeCertificate 817603 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv3169]) (by decide +kernel)
def pv817603 : PrimeValue := ⟨817603, pr817603⟩
private theorem pr817711 : PrimeCertificate 817711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv97,pv281]) (by decide +kernel)
def pv817711 : PrimeValue := ⟨817711, pr817711⟩
private theorem pr817721 : PrimeCertificate 817721 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv20443]) (by decide +kernel)
def pv817721 : PrimeValue := ⟨817721, pr817721⟩
private theorem pr817757 : PrimeCertificate 817757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv204439]) (by decide +kernel)
def pv817757 : PrimeValue := ⟨817757, pr817757⟩
private theorem pr817787 : PrimeCertificate 817787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv9973]) (by decide +kernel)
def pv817787 : PrimeValue := ⟨817787, pr817787⟩
private theorem pr817987 : PrimeCertificate 817987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv10487]) (by decide +kernel)
def pv817987 : PrimeValue := ⟨817987, pr817987⟩
private theorem pr818011 : PrimeCertificate 818011 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv61,pv149]) (by decide +kernel)
def pv818011 : PrimeValue := ⟨818011, pr818011⟩
private theorem pr818093 : PrimeCertificate 818093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv18593]) (by decide +kernel)
def pv818093 : PrimeValue := ⟨818093, pr818093⟩
private theorem pr818291 : PrimeCertificate 818291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv43,pv173]) (by decide +kernel)
def pv818291 : PrimeValue := ⟨818291, pr818291⟩
private theorem pr818341 : PrimeCertificate 818341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv593]) (by decide +kernel)
def pv818341 : PrimeValue := ⟨818341, pr818341⟩
private theorem pr818603 : PrimeCertificate 818603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv563,pv727]) (by decide +kernel)
def pv818603 : PrimeValue := ⟨818603, pr818603⟩
private theorem pr819031 : PrimeCertificate 819031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv1187]) (by decide +kernel)
def pv819031 : PrimeValue := ⟨819031, pr819031⟩
private theorem pr819101 : PrimeCertificate 819101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8191]) (by decide +kernel)
def pv819101 : PrimeValue := ⟨819101, pr819101⟩
private theorem pr819241 : PrimeCertificate 819241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv6827]) (by decide +kernel)
def pv819241 : PrimeValue := ⟨819241, pr819241⟩
private theorem pr819307 : PrimeCertificate 819307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1979]) (by decide +kernel)
def pv819307 : PrimeValue := ⟨819307, pr819307⟩
private theorem pr819367 : PrimeCertificate 819367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv29,pv277]) (by decide +kernel)
def pv819367 : PrimeValue := ⟨819367, pr819367⟩
private theorem pr819373 : PrimeCertificate 819373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv68281]) (by decide +kernel)
def pv819373 : PrimeValue := ⟨819373, pr819373⟩
private theorem pr819391 : PrimeCertificate 819391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv13,pv191]) (by decide +kernel)
def pv819391 : PrimeValue := ⟨819391, pr819391⟩
private theorem pr819503 : PrimeCertificate 819503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv24103]) (by decide +kernel)
def pv819503 : PrimeValue := ⟨819503, pr819503⟩
private theorem pr819523 : PrimeCertificate 819523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv4139]) (by decide +kernel)
def pv819523 : PrimeValue := ⟨819523, pr819523⟩
private theorem pr819761 : PrimeCertificate 819761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10247]) (by decide +kernel)
def pv819761 : PrimeValue := ⟨819761, pr819761⟩
private theorem pr819781 : PrimeCertificate 819781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv1051]) (by decide +kernel)
def pv819781 : PrimeValue := ⟨819781, pr819781⟩
private theorem pr819937 : PrimeCertificate 819937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv73]) (by decide +kernel)
def pv819937 : PrimeValue := ⟨819937, pr819937⟩
private theorem pr820067 : PrimeCertificate 820067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv31541]) (by decide +kernel)
def pv820067 : PrimeValue := ⟨820067, pr820067⟩
private theorem pr820241 : PrimeCertificate 820241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10253]) (by decide +kernel)
def pv820241 : PrimeValue := ⟨820241, pr820241⟩
private theorem pr820427 : PrimeCertificate 820427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv97,pv4229]) (by decide +kernel)
def pv820427 : PrimeValue := ⟨820427, pr820427⟩
private theorem pr820577 : PrimeCertificate 820577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv25643]) (by decide +kernel)
def pv820577 : PrimeValue := ⟨820577, pr820577⟩
private theorem pr820657 : PrimeCertificate 820657 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv139]) (by decide +kernel)
def pv820657 : PrimeValue := ⟨820657, pr820657⟩
private theorem pr820691 : PrimeCertificate 820691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv59,pv107]) (by decide +kernel)
def pv820691 : PrimeValue := ⟨820691, pr820691⟩
private theorem pr820711 : PrimeCertificate 820711 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv829]) (by decide +kernel)
def pv820711 : PrimeValue := ⟨820711, pr820711⟩
private theorem pr820907 : PrimeCertificate 820907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv410453]) (by decide +kernel)
def pv820907 : PrimeValue := ⟨820907, pr820907⟩
private theorem pr820997 : PrimeCertificate 820997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47,pv397]) (by decide +kernel)
def pv820997 : PrimeValue := ⟨820997, pr820997⟩
private theorem pr821281 : PrimeCertificate 821281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv59]) (by decide +kernel)
def pv821281 : PrimeValue := ⟨821281, pr821281⟩
private theorem pr821383 : PrimeCertificate 821383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv136897]) (by decide +kernel)
def pv821383 : PrimeValue := ⟨821383, pr821383⟩
private theorem pr821477 : PrimeCertificate 821477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv5009]) (by decide +kernel)
def pv821477 : PrimeValue := ⟨821477, pr821477⟩
private theorem pr821747 : PrimeCertificate 821747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv24169]) (by decide +kernel)
def pv821747 : PrimeValue := ⟨821747, pr821747⟩
private theorem pr821803 : PrimeCertificate 821803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv4723]) (by decide +kernel)
def pv821803 : PrimeValue := ⟨821803, pr821803⟩
private theorem pr821911 : PrimeCertificate 821911 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv27397]) (by decide +kernel)
def pv821911 : PrimeValue := ⟨821911, pr821911⟩
private theorem pr822191 : PrimeCertificate 822191 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv82219]) (by decide +kernel)
def pv822191 : PrimeValue := ⟨822191, pr822191⟩
private theorem pr822293 : PrimeCertificate 822293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv853]) (by decide +kernel)
def pv822293 : PrimeValue := ⟨822293, pr822293⟩
private theorem pr822517 : PrimeCertificate 822517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv68543]) (by decide +kernel)
def pv822517 : PrimeValue := ⟨822517, pr822517⟩
private theorem pr822541 : PrimeCertificate 822541 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13709]) (by decide +kernel)
def pv822541 : PrimeValue := ⟨822541, pr822541⟩
private theorem pr822581 : PrimeCertificate 822581 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv3739]) (by decide +kernel)
def pv822581 : PrimeValue := ⟨822581, pr822581⟩
private theorem pr822587 : PrimeCertificate 822587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv21647]) (by decide +kernel)
def pv822587 : PrimeValue := ⟨822587, pr822587⟩
private theorem pr822631 : PrimeCertificate 822631 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv17,pv1613]) (by decide +kernel)
def pv822631 : PrimeValue := ⟨822631, pr822631⟩
private theorem pr822713 : PrimeCertificate 822713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv9349]) (by decide +kernel)
def pv822713 : PrimeValue := ⟨822713, pr822713⟩
private theorem pr822761 : PrimeCertificate 822761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv67,pv307]) (by decide +kernel)
def pv822761 : PrimeValue := ⟨822761, pr822761⟩
private theorem pr822881 : PrimeCertificate 822881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv139]) (by decide +kernel)
def pv822881 : PrimeValue := ⟨822881, pr822881⟩
private theorem pr822973 : PrimeCertificate 822973 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv68581]) (by decide +kernel)
def pv822973 : PrimeValue := ⟨822973, pr822973⟩
private theorem pr823231 : PrimeCertificate 823231 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3049]) (by decide +kernel)
def pv823231 : PrimeValue := ⟨823231, pr823231⟩
private theorem pr823237 : PrimeCertificate 823237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv2213]) (by decide +kernel)
def pv823237 : PrimeValue := ⟨823237, pr823237⟩
private theorem pr823261 : PrimeCertificate 823261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13721]) (by decide +kernel)
def pv823261 : PrimeValue := ⟨823261, pr823261⟩
private theorem pr823483 : PrimeCertificate 823483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv4159]) (by decide +kernel)
def pv823483 : PrimeValue := ⟨823483, pr823483⟩
private theorem pr823547 : PrimeCertificate 823547 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv37,pv359]) (by decide +kernel)
def pv823547 : PrimeValue := ⟨823547, pr823547⟩
private theorem pr823553 : PrimeCertificate 823553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3217]) (by decide +kernel)
def pv823553 : PrimeValue := ⟨823553, pr823553⟩
private theorem pr823651 : PrimeCertificate 823651 :=
  certifyPrime (q := pv53) (ls := [pv2,pv3,pv5,pv17,pv19]) (by decide +kernel)
def pv823651 : PrimeValue := ⟨823651, pr823651⟩
private theorem pr823723 : PrimeCertificate 823723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv47,pv127]) (by decide +kernel)
def pv823723 : PrimeValue := ⟨823723, pr823723⟩
private theorem pr823913 : PrimeCertificate 823913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv181,pv569]) (by decide +kernel)
def pv823913 : PrimeValue := ⟨823913, pr823913⟩
private theorem pr823961 : PrimeCertificate 823961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv20599]) (by decide +kernel)
def pv823961 : PrimeValue := ⟨823961, pr823961⟩
private theorem pr823993 : PrimeCertificate 823993 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv13,pv19,pv139]) (by decide +kernel)
def pv823993 : PrimeValue := ⟨823993, pr823993⟩
private theorem pr824077 : PrimeCertificate 824077 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv2081]) (by decide +kernel)
def pv824077 : PrimeValue := ⟨824077, pr824077⟩
private theorem pr824081 : PrimeCertificate 824081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv10301]) (by decide +kernel)
def pv824081 : PrimeValue := ⟨824081, pr824081⟩
private theorem pr824281 : PrimeCertificate 824281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv6869]) (by decide +kernel)
def pv824281 : PrimeValue := ⟨824281, pr824281⟩
private theorem pr824801 : PrimeCertificate 824801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1031]) (by decide +kernel)
def pv824801 : PrimeValue := ⟨824801, pr824801⟩
private theorem pr824843 : PrimeCertificate 824843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv6761]) (by decide +kernel)
def pv824843 : PrimeValue := ⟨824843, pr824843⟩
private theorem pr824861 : PrimeCertificate 824861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41243]) (by decide +kernel)
def pv824861 : PrimeValue := ⟨824861, pr824861⟩
private theorem pr824893 : PrimeCertificate 824893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv1297]) (by decide +kernel)
def pv824893 : PrimeValue := ⟨824893, pr824893⟩
private theorem pr824933 : PrimeCertificate 824933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv206233]) (by decide +kernel)
def pv824933 : PrimeValue := ⟨824933, pr824933⟩
private theorem pr825017 : PrimeCertificate 825017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv281,pv367]) (by decide +kernel)
def pv825017 : PrimeValue := ⟨825017, pr825017⟩
private theorem pr825067 : PrimeCertificate 825067 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv463]) (by decide +kernel)
def pv825067 : PrimeValue := ⟨825067, pr825067⟩
private theorem pr825337 : PrimeCertificate 825337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv3821]) (by decide +kernel)
def pv825337 : PrimeValue := ⟨825337, pr825337⟩
private theorem pr825353 : PrimeCertificate 825353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv83,pv113]) (by decide +kernel)
def pv825353 : PrimeValue := ⟨825353, pr825353⟩
private theorem pr825533 : PrimeCertificate 825533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv206383]) (by decide +kernel)
def pv825533 : PrimeValue := ⟨825533, pr825533⟩
private theorem pr825611 : PrimeCertificate 825611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv82561]) (by decide +kernel)
def pv825611 : PrimeValue := ⟨825611, pr825611⟩
private theorem pr825613 : PrimeCertificate 825613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv107,pv643]) (by decide +kernel)
def pv825613 : PrimeValue := ⟨825613, pr825613⟩
private theorem pr825821 : PrimeCertificate 825821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv157,pv263]) (by decide +kernel)
def pv825821 : PrimeValue := ⟨825821, pr825821⟩
private theorem pr825991 : PrimeCertificate 825991 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv2503]) (by decide +kernel)
def pv825991 : PrimeValue := ⟨825991, pr825991⟩
private theorem pr826193 : PrimeCertificate 826193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv51637]) (by decide +kernel)
def pv826193 : PrimeValue := ⟨826193, pr826193⟩
private theorem pr826201 : PrimeCertificate 826201 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv826201 : PrimeValue := ⟨826201, pr826201⟩
private theorem pr826303 : PrimeCertificate 826303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv8101]) (by decide +kernel)
def pv826303 : PrimeValue := ⟨826303, pr826303⟩
private theorem pr826391 : PrimeCertificate 826391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv23,pv3593]) (by decide +kernel)
def pv826391 : PrimeValue := ⟨826391, pr826391⟩
private theorem pr826411 : PrimeCertificate 826411 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv163]) (by decide +kernel)
def pv826411 : PrimeValue := ⟨826411, pr826411⟩
private theorem pr826453 : PrimeCertificate 826453 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv2087]) (by decide +kernel)
def pv826453 : PrimeValue := ⟨826453, pr826453⟩
private theorem pr826723 : PrimeCertificate 826723 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv3533]) (by decide +kernel)
def pv826723 : PrimeValue := ⟨826723, pr826723⟩
private theorem pr826753 : PrimeCertificate 826753 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2153]) (by decide +kernel)
def pv826753 : PrimeValue := ⟨826753, pr826753⟩
private theorem pr826831 : PrimeCertificate 826831 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv9187]) (by decide +kernel)
def pv826831 : PrimeValue := ⟨826831, pr826831⟩
private theorem pr826907 : PrimeCertificate 826907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv53,pv269]) (by decide +kernel)
def pv826907 : PrimeValue := ⟨826907, pr826907⟩
private theorem pr826927 : PrimeCertificate 826927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv283,pv487]) (by decide +kernel)
def pv826927 : PrimeValue := ⟨826927, pr826927⟩
private theorem pr827131 : PrimeCertificate 827131 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv79,pv349]) (by decide +kernel)
def pv827131 : PrimeValue := ⟨827131, pr827131⟩
private theorem pr827161 : PrimeCertificate 827161 :=
  certifyPrime (q := pv67) (ls := [pv2,pv3,pv5,pv61,pv113]) (by decide +kernel)
def pv827161 : PrimeValue := ⟨827161, pr827161⟩
private theorem pr827227 : PrimeCertificate 827227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv15319]) (by decide +kernel)
def pv827227 : PrimeValue := ⟨827227, pr827227⟩
private theorem pr827417 : PrimeCertificate 827417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv1753]) (by decide +kernel)
def pv827417 : PrimeValue := ⟨827417, pr827417⟩
private theorem pr827501 : PrimeCertificate 827501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv331]) (by decide +kernel)
def pv827501 : PrimeValue := ⟨827501, pr827501⟩
private theorem pr827633 : PrimeCertificate 827633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv23,pv173]) (by decide +kernel)
def pv827633 : PrimeValue := ⟨827633, pr827633⟩
private theorem pr827837 : PrimeCertificate 827837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv4813]) (by decide +kernel)
def pv827837 : PrimeValue := ⟨827837, pr827837⟩
private theorem pr827857 : PrimeCertificate 827857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5749]) (by decide +kernel)
def pv827857 : PrimeValue := ⟨827857, pr827857⟩
private theorem pr827867 : PrimeCertificate 827867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv1873]) (by decide +kernel)
def pv827867 : PrimeValue := ⟨827867, pr827867⟩
private theorem pr827941 : PrimeCertificate 827941 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv5,pv13799]) (by decide +kernel)
def pv827941 : PrimeValue := ⟨827941, pr827941⟩
private theorem pr827987 : PrimeCertificate 827987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv67,pv167]) (by decide +kernel)
def pv827987 : PrimeValue := ⟨827987, pr827987⟩
private theorem pr828071 : PrimeCertificate 828071 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv17,pv4871]) (by decide +kernel)
def pv828071 : PrimeValue := ⟨828071, pr828071⟩
private theorem pr828127 : PrimeCertificate 828127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv3539]) (by decide +kernel)
def pv828127 : PrimeValue := ⟨828127, pr828127⟩
private theorem pr828371 : PrimeCertificate 828371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv82837]) (by decide +kernel)
def pv828371 : PrimeValue := ⟨828371, pr828371⟩
private theorem pr828431 : PrimeCertificate 828431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv37,pv2239]) (by decide +kernel)
def pv828431 : PrimeValue := ⟨828431, pr828431⟩
private theorem pr828523 : PrimeCertificate 828523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv67,pv229]) (by decide +kernel)
def pv828523 : PrimeValue := ⟨828523, pr828523⟩
private theorem pr828637 : PrimeCertificate 828637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199,pv347]) (by decide +kernel)
def pv828637 : PrimeValue := ⟨828637, pr828637⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
