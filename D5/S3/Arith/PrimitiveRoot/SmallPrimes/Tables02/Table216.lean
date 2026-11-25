/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table216
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table216.pv803963
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table018
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table031
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table048
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table099
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table100

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr803963 : PrimeCertificate 803963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv401981]) (by decide +kernel)
def pv803963 : PrimeValue := ⟨803963, pr803963⟩
private theorem pr804017 : PrimeCertificate 804017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv1621]) (by decide +kernel)
def pv804017 : PrimeValue := ⟨804017, pr804017⟩
private theorem pr804031 : PrimeCertificate 804031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv26801]) (by decide +kernel)
def pv804031 : PrimeValue := ⟨804031, pr804031⟩
private theorem pr804073 : PrimeCertificate 804073 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv33503]) (by decide +kernel)
def pv804073 : PrimeValue := ⟨804073, pr804073⟩
private theorem pr804157 : PrimeCertificate 804157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv3527]) (by decide +kernel)
def pv804157 : PrimeValue := ⟨804157, pr804157⟩
private theorem pr804211 : PrimeCertificate 804211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv2437]) (by decide +kernel)
def pv804211 : PrimeValue := ⟨804211, pr804211⟩
private theorem pr804313 : PrimeCertificate 804313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11171]) (by decide +kernel)
def pv804313 : PrimeValue := ⟨804313, pr804313⟩
private theorem pr804317 : PrimeCertificate 804317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233,pv863]) (by decide +kernel)
def pv804317 : PrimeValue := ⟨804317, pr804317⟩
private theorem pr804757 : PrimeCertificate 804757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv199,pv337]) (by decide +kernel)
def pv804757 : PrimeValue := ⟨804757, pr804757⟩
private theorem pr804877 : PrimeCertificate 804877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67073]) (by decide +kernel)
def pv804877 : PrimeValue := ⟨804877, pr804877⟩
private theorem pr804893 : PrimeCertificate 804893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv1663]) (by decide +kernel)
def pv804893 : PrimeValue := ⟨804893, pr804893⟩
private theorem pr805037 : PrimeCertificate 805037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv313,pv643]) (by decide +kernel)
def pv805037 : PrimeValue := ⟨805037, pr805037⟩
private theorem pr805073 : PrimeCertificate 805073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv751]) (by decide +kernel)
def pv805073 : PrimeValue := ⟨805073, pr805073⟩
private theorem pr805081 : PrimeCertificate 805081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv6709]) (by decide +kernel)
def pv805081 : PrimeValue := ⟨805081, pr805081⟩
private theorem pr805327 : PrimeCertificate 805327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv1699]) (by decide +kernel)
def pv805327 : PrimeValue := ⟨805327, pr805327⟩
private theorem pr805331 : PrimeCertificate 805331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv2777]) (by decide +kernel)
def pv805331 : PrimeValue := ⟨805331, pr805331⟩
private theorem pr805333 : PrimeCertificate 805333 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv11,pv6101]) (by decide +kernel)
def pv805333 : PrimeValue := ⟨805333, pr805333⟩
private theorem pr805381 : PrimeCertificate 805381 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv31,pv433]) (by decide +kernel)
def pv805381 : PrimeValue := ⟨805381, pr805381⟩
private theorem pr805403 : PrimeCertificate 805403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv30977]) (by decide +kernel)
def pv805403 : PrimeValue := ⟨805403, pr805403⟩
private theorem pr805523 : PrimeCertificate 805523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv402761]) (by decide +kernel)
def pv805523 : PrimeValue := ⟨805523, pr805523⟩
private theorem pr805531 : PrimeCertificate 805531 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv11,pv2441]) (by decide +kernel)
def pv805531 : PrimeValue := ⟨805531, pr805531⟩
private theorem pr805711 : PrimeCertificate 805711 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv107,pv251]) (by decide +kernel)
def pv805711 : PrimeValue := ⟨805711, pr805711⟩
private theorem pr805867 : PrimeCertificate 805867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv7069]) (by decide +kernel)
def pv805867 : PrimeValue := ⟨805867, pr805867⟩
private theorem pr805877 : PrimeCertificate 805877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv67,pv97]) (by decide +kernel)
def pv805877 : PrimeValue := ⟨805877, pr805877⟩
private theorem pr805991 : PrimeCertificate 805991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv80599]) (by decide +kernel)
def pv805991 : PrimeValue := ⟨805991, pr805991⟩
private theorem pr806011 : PrimeCertificate 806011 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv67,pv401]) (by decide +kernel)
def pv806011 : PrimeValue := ⟨806011, pr806011⟩
private theorem pr806087 : PrimeCertificate 806087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv403043]) (by decide +kernel)
def pv806087 : PrimeValue := ⟨806087, pr806087⟩
private theorem pr806203 : PrimeCertificate 806203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv44789]) (by decide +kernel)
def pv806203 : PrimeValue := ⟨806203, pr806203⟩
private theorem pr806263 : PrimeCertificate 806263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv83,pv1619]) (by decide +kernel)
def pv806263 : PrimeValue := ⟨806263, pr806263⟩
private theorem pr806447 : PrimeCertificate 806447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv23719]) (by decide +kernel)
def pv806447 : PrimeValue := ⟨806447, pr806447⟩
private theorem pr806453 : PrimeCertificate 806453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv5449]) (by decide +kernel)
def pv806453 : PrimeValue := ⟨806453, pr806453⟩
private theorem pr806521 : PrimeCertificate 806521 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv11,pv13,pv47]) (by decide +kernel)
def pv806521 : PrimeValue := ⟨806521, pr806521⟩
private theorem pr806581 : PrimeCertificate 806581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4481]) (by decide +kernel)
def pv806581 : PrimeValue := ⟨806581, pr806581⟩
private theorem pr806671 : PrimeCertificate 806671 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv8963]) (by decide +kernel)
def pv806671 : PrimeValue := ⟨806671, pr806671⟩
private theorem pr806893 : PrimeCertificate 806893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv3539]) (by decide +kernel)
def pv806893 : PrimeValue := ⟨806893, pr806893⟩
private theorem pr806941 : PrimeCertificate 806941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv4483]) (by decide +kernel)
def pv806941 : PrimeValue := ⟨806941, pr806941⟩
private theorem pr807071 : PrimeCertificate 807071 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11,pv23,pv29]) (by decide +kernel)
def pv807071 : PrimeValue := ⟨807071, pr807071⟩
private theorem pr807097 : PrimeCertificate 807097 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv33629]) (by decide +kernel)
def pv807097 : PrimeValue := ⟨807097, pr807097⟩
private theorem pr807113 : PrimeCertificate 807113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv233,pv433]) (by decide +kernel)
def pv807113 : PrimeValue := ⟨807113, pr807113⟩
private theorem pr807197 : PrimeCertificate 807197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv43]) (by decide +kernel)
def pv807197 : PrimeValue := ⟨807197, pr807197⟩
private theorem pr807251 : PrimeCertificate 807251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv3229]) (by decide +kernel)
def pv807251 : PrimeValue := ⟨807251, pr807251⟩
private theorem pr807281 : PrimeCertificate 807281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv10091]) (by decide +kernel)
def pv807281 : PrimeValue := ⟨807281, pr807281⟩
private theorem pr807371 : PrimeCertificate 807371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv80737]) (by decide +kernel)
def pv807371 : PrimeValue := ⟨807371, pr807371⟩
private theorem pr807403 : PrimeCertificate 807403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv2539]) (by decide +kernel)
def pv807403 : PrimeValue := ⟨807403, pr807403⟩
private theorem pr807407 : PrimeCertificate 807407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv403703]) (by decide +kernel)
def pv807407 : PrimeValue := ⟨807407, pr807407⟩
private theorem pr807491 : PrimeCertificate 807491 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv80749]) (by decide +kernel)
def pv807491 : PrimeValue := ⟨807491, pr807491⟩
private theorem pr807637 : PrimeCertificate 807637 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv37,pv107]) (by decide +kernel)
def pv807637 : PrimeValue := ⟨807637, pr807637⟩
private theorem pr807907 : PrimeCertificate 807907 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv12241]) (by decide +kernel)
def pv807907 : PrimeValue := ⟨807907, pr807907⟩
private theorem pr808097 : PrimeCertificate 808097 :=
  certifyPrime (q := pv3) (ls := [pv2,pv25253]) (by decide +kernel)
def pv808097 : PrimeValue := ⟨808097, pr808097⟩
private theorem pr808261 : PrimeCertificate 808261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv709]) (by decide +kernel)
def pv808261 : PrimeValue := ⟨808261, pr808261⟩
private theorem pr808307 : PrimeCertificate 808307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv8599]) (by decide +kernel)
def pv808307 : PrimeValue := ⟨808307, pr808307⟩
private theorem pr808351 : PrimeCertificate 808351 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv317]) (by decide +kernel)
def pv808351 : PrimeValue := ⟨808351, pr808351⟩
private theorem pr808373 : PrimeCertificate 808373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv3313]) (by decide +kernel)
def pv808373 : PrimeValue := ⟨808373, pr808373⟩
private theorem pr808391 : PrimeCertificate 808391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv7349]) (by decide +kernel)
def pv808391 : PrimeValue := ⟨808391, pr808391⟩
private theorem pr808441 : PrimeCertificate 808441 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv6737]) (by decide +kernel)
def pv808441 : PrimeValue := ⟨808441, pr808441⟩
private theorem pr808603 : PrimeCertificate 808603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv41,pv173]) (by decide +kernel)
def pv808603 : PrimeValue := ⟨808603, pr808603⟩
private theorem pr808651 : PrimeCertificate 808651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv599]) (by decide +kernel)
def pv808651 : PrimeValue := ⟨808651, pr808651⟩
private theorem pr808867 : PrimeCertificate 808867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4993]) (by decide +kernel)
def pv808867 : PrimeValue := ⟨808867, pr808867⟩
private theorem pr809041 : PrimeCertificate 809041 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv3371]) (by decide +kernel)
def pv809041 : PrimeValue := ⟨809041, pr809041⟩
private theorem pr809051 : PrimeCertificate 809051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1471]) (by decide +kernel)
def pv809051 : PrimeValue := ⟨809051, pr809051⟩
private theorem pr809063 : PrimeCertificate 809063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv404531]) (by decide +kernel)
def pv809063 : PrimeValue := ⟨809063, pr809063⟩
private theorem pr809101 : PrimeCertificate 809101 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv29,pv31]) (by decide +kernel)
def pv809101 : PrimeValue := ⟨809101, pr809101⟩
private theorem pr809141 : PrimeCertificate 809141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv1759]) (by decide +kernel)
def pv809141 : PrimeValue := ⟨809141, pr809141⟩
private theorem pr809177 : PrimeCertificate 809177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv2467]) (by decide +kernel)
def pv809177 : PrimeValue := ⟨809177, pr809177⟩
private theorem pr809203 : PrimeCertificate 809203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv134867]) (by decide +kernel)
def pv809203 : PrimeValue := ⟨809203, pr809203⟩
private theorem pr809261 : PrimeCertificate 809261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv941]) (by decide +kernel)
def pv809261 : PrimeValue := ⟨809261, pr809261⟩
private theorem pr809357 : PrimeCertificate 809357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202339]) (by decide +kernel)
def pv809357 : PrimeValue := ⟨809357, pr809357⟩
private theorem pr809377 : PrimeCertificate 809377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8431]) (by decide +kernel)
def pv809377 : PrimeValue := ⟨809377, pr809377⟩
private theorem pr809491 : PrimeCertificate 809491 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv223]) (by decide +kernel)
def pv809491 : PrimeValue := ⟨809491, pr809491⟩
private theorem pr809581 : PrimeCertificate 809581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv103,pv131]) (by decide +kernel)
def pv809581 : PrimeValue := ⟨809581, pr809581⟩
private theorem pr809701 : PrimeCertificate 809701 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv2699]) (by decide +kernel)
def pv809701 : PrimeValue := ⟨809701, pr809701⟩
private theorem pr809737 : PrimeCertificate 809737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv33739]) (by decide +kernel)
def pv809737 : PrimeValue := ⟨809737, pr809737⟩
private theorem pr809771 : PrimeCertificate 809771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv6229]) (by decide +kernel)
def pv809771 : PrimeValue := ⟨809771, pr809771⟩
private theorem pr809797 : PrimeCertificate 809797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv179]) (by decide +kernel)
def pv809797 : PrimeValue := ⟨809797, pr809797⟩
private theorem pr809903 : PrimeCertificate 809903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv404951]) (by decide +kernel)
def pv809903 : PrimeValue := ⟨809903, pr809903⟩
private theorem pr810091 : PrimeCertificate 810091 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv9001]) (by decide +kernel)
def pv810091 : PrimeValue := ⟨810091, pr810091⟩
private theorem pr810457 : PrimeCertificate 810457 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv33769]) (by decide +kernel)
def pv810457 : PrimeValue := ⟨810457, pr810457⟩
private theorem pr810547 : PrimeCertificate 810547 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv12281]) (by decide +kernel)
def pv810547 : PrimeValue := ⟨810547, pr810547⟩
private theorem pr810571 : PrimeCertificate 810571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv41,pv659]) (by decide +kernel)
def pv810571 : PrimeValue := ⟨810571, pr810571⟩
private theorem pr810653 : PrimeCertificate 810653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv4943]) (by decide +kernel)
def pv810653 : PrimeValue := ⟨810653, pr810653⟩
private theorem pr810871 : PrimeCertificate 810871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv151,pv179]) (by decide +kernel)
def pv810871 : PrimeValue := ⟨810871, pr810871⟩
private theorem pr810913 : PrimeCertificate 810913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8447]) (by decide +kernel)
def pv810913 : PrimeValue := ⟨810913, pr810913⟩
private theorem pr810941 : PrimeCertificate 810941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv3119]) (by decide +kernel)
def pv810941 : PrimeValue := ⟨810941, pr810941⟩
private theorem pr810967 : PrimeCertificate 810967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv37,pv281]) (by decide +kernel)
def pv810967 : PrimeValue := ⟨810967, pr810967⟩
private theorem pr811207 : PrimeCertificate 811207 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv17,pv241]) (by decide +kernel)
def pv811207 : PrimeValue := ⟨811207, pr811207⟩
private theorem pr811351 : PrimeCertificate 811351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv601]) (by decide +kernel)
def pv811351 : PrimeValue := ⟨811351, pr811351⟩
private theorem pr811387 : PrimeCertificate 811387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv45077]) (by decide +kernel)
def pv811387 : PrimeValue := ⟨811387, pr811387⟩
private theorem pr811411 : PrimeCertificate 811411 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv5,pv17,pv37,pv43]) (by decide +kernel)
def pv811411 : PrimeValue := ⟨811411, pr811411⟩
private theorem pr811583 : PrimeCertificate 811583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv43,pv9437]) (by decide +kernel)
def pv811583 : PrimeValue := ⟨811583, pr811583⟩
private theorem pr811627 : PrimeCertificate 811627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv135271]) (by decide +kernel)
def pv811627 : PrimeValue := ⟨811627, pr811627⟩
private theorem pr811697 : PrimeCertificate 811697 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv523]) (by decide +kernel)
def pv811697 : PrimeValue := ⟨811697, pr811697⟩
private theorem pr811703 : PrimeCertificate 811703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv107,pv3793]) (by decide +kernel)
def pv811703 : PrimeValue := ⟨811703, pr811703⟩
private theorem pr811871 : PrimeCertificate 811871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv4273]) (by decide +kernel)
def pv811871 : PrimeValue := ⟨811871, pr811871⟩
private theorem pr811997 : PrimeCertificate 811997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv202999]) (by decide +kernel)
def pv811997 : PrimeValue := ⟨811997, pr811997⟩
private theorem pr812173 : PrimeCertificate 812173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv1277]) (by decide +kernel)
def pv812173 : PrimeValue := ⟨812173, pr812173⟩
private theorem pr812213 : PrimeCertificate 812213 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv10687]) (by decide +kernel)
def pv812213 : PrimeValue := ⟨812213, pr812213⟩
private theorem pr812221 : PrimeCertificate 812221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13537]) (by decide +kernel)
def pv812221 : PrimeValue := ⟨812221, pr812221⟩
private theorem pr812233 : PrimeCertificate 812233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv389]) (by decide +kernel)
def pv812233 : PrimeValue := ⟨812233, pr812233⟩
private theorem pr812297 : PrimeCertificate 812297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101537]) (by decide +kernel)
def pv812297 : PrimeValue := ⟨812297, pr812297⟩
private theorem pr812353 : PrimeCertificate 812353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4231]) (by decide +kernel)
def pv812353 : PrimeValue := ⟨812353, pr812353⟩
private theorem pr812431 : PrimeCertificate 812431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17,pv59]) (by decide +kernel)
def pv812431 : PrimeValue := ⟨812431, pr812431⟩
private theorem pr812467 : PrimeCertificate 812467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv45137]) (by decide +kernel)
def pv812467 : PrimeValue := ⟨812467, pr812467⟩
private theorem pr812627 : PrimeCertificate 812627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv406313]) (by decide +kernel)
def pv812627 : PrimeValue := ⟨812627, pr812627⟩
private theorem pr812641 : PrimeCertificate 812641 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1693]) (by decide +kernel)
def pv812641 : PrimeValue := ⟨812641, pr812641⟩
private theorem pr813017 : PrimeCertificate 813017 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101627]) (by decide +kernel)
def pv813017 : PrimeValue := ⟨813017, pr813017⟩
private theorem pr813083 : PrimeCertificate 813083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv3947]) (by decide +kernel)
def pv813083 : PrimeValue := ⟨813083, pr813083⟩
private theorem pr813157 : PrimeCertificate 813157 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67763]) (by decide +kernel)
def pv813157 : PrimeValue := ⟨813157, pr813157⟩
private theorem pr813227 : PrimeCertificate 813227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv5147]) (by decide +kernel)
def pv813227 : PrimeValue := ⟨813227, pr813227⟩
private theorem pr813301 : PrimeCertificate 813301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2711]) (by decide +kernel)
def pv813301 : PrimeValue := ⟨813301, pr813301⟩
private theorem pr813343 : PrimeCertificate 813343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv283,pv479]) (by decide +kernel)
def pv813343 : PrimeValue := ⟨813343, pr813343⟩
private theorem pr813493 : PrimeCertificate 813493 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv383]) (by decide +kernel)
def pv813493 : PrimeValue := ⟨813493, pr813493⟩
private theorem pr813721 : PrimeCertificate 813721 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv6781]) (by decide +kernel)
def pv813721 : PrimeValue := ⟨813721, pr813721⟩
private theorem pr814183 : PrimeCertificate 814183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv135697]) (by decide +kernel)
def pv814183 : PrimeValue := ⟨814183, pr814183⟩
private theorem pr814237 : PrimeCertificate 814237 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv67853]) (by decide +kernel)
def pv814237 : PrimeValue := ⟨814237, pr814237⟩
private theorem pr814477 : PrimeCertificate 814477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv23,pv227]) (by decide +kernel)
def pv814477 : PrimeValue := ⟨814477, pr814477⟩
private theorem pr814531 : PrimeCertificate 814531 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv1429]) (by decide +kernel)
def pv814531 : PrimeValue := ⟨814531, pr814531⟩
private theorem pr814687 : PrimeCertificate 814687 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv135781]) (by decide +kernel)
def pv814687 : PrimeValue := ⟨814687, pr814687⟩
private theorem pr814741 : PrimeCertificate 814741 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv37,pv367]) (by decide +kernel)
def pv814741 : PrimeValue := ⟨814741, pr814741⟩
private theorem pr814763 : PrimeCertificate 814763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv31337]) (by decide +kernel)
def pv814763 : PrimeValue := ⟨814763, pr814763⟩
private theorem pr814873 : PrimeCertificate 814873 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv19,pv1787]) (by decide +kernel)
def pv814873 : PrimeValue := ⟨814873, pr814873⟩
private theorem pr814901 : PrimeCertificate 814901 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv281]) (by decide +kernel)
def pv814901 : PrimeValue := ⟨814901, pr814901⟩
private theorem pr814903 : PrimeCertificate 814903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv12347]) (by decide +kernel)
def pv814903 : PrimeValue := ⟨814903, pr814903⟩
private theorem pr815033 : PrimeCertificate 815033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101879]) (by decide +kernel)
def pv815033 : PrimeValue := ⟨815033, pr815033⟩
private theorem pr815173 : PrimeCertificate 815173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67931]) (by decide +kernel)
def pv815173 : PrimeValue := ⟨815173, pr815173⟩
private theorem pr815251 : PrimeCertificate 815251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1087]) (by decide +kernel)
def pv815251 : PrimeValue := ⟨815251, pr815251⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
