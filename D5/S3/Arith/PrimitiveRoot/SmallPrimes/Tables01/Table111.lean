/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table111
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table111.pv505357
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table032
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table076
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table077

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr505357 : PrimeCertificate 505357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1831]) (by decide +kernel)
def pv505357 : PrimeValue := ⟨505357, pr505357⟩
private theorem pr505399 : PrimeCertificate 505399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv131,pv643]) (by decide +kernel)
def pv505399 : PrimeValue := ⟨505399, pr505399⟩
private theorem pr505411 : PrimeCertificate 505411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv991]) (by decide +kernel)
def pv505411 : PrimeValue := ⟨505411, pr505411⟩
private theorem pr505459 : PrimeCertificate 505459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28081]) (by decide +kernel)
def pv505459 : PrimeValue := ⟨505459, pr505459⟩
private theorem pr505501 : PrimeCertificate 505501 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv505501 : PrimeValue := ⟨505501, pr505501⟩
private theorem pr505511 : PrimeCertificate 505511 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv50551]) (by decide +kernel)
def pv505511 : PrimeValue := ⟨505511, pr505511⟩
private theorem pr505537 : PrimeCertificate 505537 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2633]) (by decide +kernel)
def pv505537 : PrimeValue := ⟨505537, pr505537⟩
private theorem pr505607 : PrimeCertificate 505607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv2503]) (by decide +kernel)
def pv505607 : PrimeValue := ⟨505607, pr505607⟩
private theorem pr505619 : PrimeCertificate 505619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv1049]) (by decide +kernel)
def pv505619 : PrimeValue := ⟨505619, pr505619⟩
private theorem pr505643 : PrimeCertificate 505643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv6833]) (by decide +kernel)
def pv505643 : PrimeValue := ⟨505643, pr505643⟩
private theorem pr505693 : PrimeCertificate 505693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1277]) (by decide +kernel)
def pv505693 : PrimeValue := ⟨505693, pr505693⟩
private theorem pr505763 : PrimeCertificate 505763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv252881]) (by decide +kernel)
def pv505763 : PrimeValue := ⟨505763, pr505763⟩
private theorem pr505867 : PrimeCertificate 505867 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv59,pv1429]) (by decide +kernel)
def pv505867 : PrimeValue := ⟨505867, pr505867⟩
private theorem pr506047 : PrimeCertificate 506047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv23,pv193]) (by decide +kernel)
def pv506047 : PrimeValue := ⟨506047, pr506047⟩
private theorem pr506071 : PrimeCertificate 506071 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv5623]) (by decide +kernel)
def pv506071 : PrimeValue := ⟨506071, pr506071⟩
private theorem pr506083 : PrimeCertificate 506083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv84347]) (by decide +kernel)
def pv506083 : PrimeValue := ⟨506083, pr506083⟩
private theorem pr506263 : PrimeCertificate 506263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv84377]) (by decide +kernel)
def pv506263 : PrimeValue := ⟨506263, pr506263⟩
private theorem pr506281 : PrimeCertificate 506281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv4219]) (by decide +kernel)
def pv506281 : PrimeValue := ⟨506281, pr506281⟩
private theorem pr506327 : PrimeCertificate 506327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv383,pv661]) (by decide +kernel)
def pv506327 : PrimeValue := ⟨506327, pr506327⟩
private theorem pr506333 : PrimeCertificate 506333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv126583]) (by decide +kernel)
def pv506333 : PrimeValue := ⟨506333, pr506333⟩
private theorem pr506339 : PrimeCertificate 506339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv59,pv613]) (by decide +kernel)
def pv506339 : PrimeValue := ⟨506339, pr506339⟩
private theorem pr506351 : PrimeCertificate 506351 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv19,pv41]) (by decide +kernel)
def pv506351 : PrimeValue := ⟨506351, pr506351⟩
private theorem pr506381 : PrimeCertificate 506381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv3617]) (by decide +kernel)
def pv506381 : PrimeValue := ⟨506381, pr506381⟩
private theorem pr506459 : PrimeCertificate 506459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv253229]) (by decide +kernel)
def pv506459 : PrimeValue := ⟨506459, pr506459⟩
private theorem pr506479 : PrimeCertificate 506479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv31,pv389]) (by decide +kernel)
def pv506479 : PrimeValue := ⟨506479, pr506479⟩
private theorem pr506491 : PrimeCertificate 506491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv16883]) (by decide +kernel)
def pv506491 : PrimeValue := ⟨506491, pr506491⟩
private theorem pr506501 : PrimeCertificate 506501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1013]) (by decide +kernel)
def pv506501 : PrimeValue := ⟨506501, pr506501⟩
private theorem pr506531 : PrimeCertificate 506531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37]) (by decide +kernel)
def pv506531 : PrimeValue := ⟨506531, pr506531⟩
private theorem pr506551 : PrimeCertificate 506551 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv307]) (by decide +kernel)
def pv506551 : PrimeValue := ⟨506551, pr506551⟩
private theorem pr506593 : PrimeCertificate 506593 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1759]) (by decide +kernel)
def pv506593 : PrimeValue := ⟨506593, pr506593⟩
private theorem pr506599 : PrimeCertificate 506599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv3671]) (by decide +kernel)
def pv506599 : PrimeValue := ⟨506599, pr506599⟩
private theorem pr506629 : PrimeCertificate 506629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4691]) (by decide +kernel)
def pv506629 : PrimeValue := ⟨506629, pr506629⟩
private theorem pr506683 : PrimeCertificate 506683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv853]) (by decide +kernel)
def pv506683 : PrimeValue := ⟨506683, pr506683⟩
private theorem pr506699 : PrimeCertificate 506699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv253349]) (by decide +kernel)
def pv506699 : PrimeValue := ⟨506699, pr506699⟩
private theorem pr506773 : PrimeCertificate 506773 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv2011]) (by decide +kernel)
def pv506773 : PrimeValue := ⟨506773, pr506773⟩
private theorem pr506783 : PrimeCertificate 506783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv479]) (by decide +kernel)
def pv506783 : PrimeValue := ⟨506783, pr506783⟩
private theorem pr506809 : PrimeCertificate 506809 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7039]) (by decide +kernel)
def pv506809 : PrimeValue := ⟨506809, pr506809⟩
private theorem pr506843 : PrimeCertificate 506843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv41,pv883]) (by decide +kernel)
def pv506843 : PrimeValue := ⟨506843, pr506843⟩
private theorem pr506887 : PrimeCertificate 506887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv84481]) (by decide +kernel)
def pv506887 : PrimeValue := ⟨506887, pr506887⟩
private theorem pr506993 : PrimeCertificate 506993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31687]) (by decide +kernel)
def pv506993 : PrimeValue := ⟨506993, pr506993⟩
private theorem pr507049 : PrimeCertificate 507049 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv37,pv571]) (by decide +kernel)
def pv507049 : PrimeValue := ⟨507049, pr507049⟩
private theorem pr507103 : PrimeCertificate 507103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv223,pv379]) (by decide +kernel)
def pv507103 : PrimeValue := ⟨507103, pr507103⟩
private theorem pr507193 : PrimeCertificate 507193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv3019]) (by decide +kernel)
def pv507193 : PrimeValue := ⟨507193, pr507193⟩
private theorem pr507217 : PrimeCertificate 507217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10567]) (by decide +kernel)
def pv507217 : PrimeValue := ⟨507217, pr507217⟩
private theorem pr507317 : PrimeCertificate 507317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv2393]) (by decide +kernel)
def pv507317 : PrimeValue := ⟨507317, pr507317⟩
private theorem pr507359 : PrimeCertificate 507359 :=
  certifyPrime (q := pv13) (ls := [pv2,pv253679]) (by decide +kernel)
def pv507359 : PrimeValue := ⟨507359, pr507359⟩
private theorem pr507371 : PrimeCertificate 507371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv113,pv449]) (by decide +kernel)
def pv507371 : PrimeValue := ⟨507371, pr507371⟩
private theorem pr507383 : PrimeCertificate 507383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv14923]) (by decide +kernel)
def pv507383 : PrimeValue := ⟨507383, pr507383⟩
private theorem pr507401 : PrimeCertificate 507401 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv43,pv59]) (by decide +kernel)
def pv507401 : PrimeValue := ⟨507401, pr507401⟩
private theorem pr507421 : PrimeCertificate 507421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2819]) (by decide +kernel)
def pv507421 : PrimeValue := ⟨507421, pr507421⟩
private theorem pr507431 : PrimeCertificate 507431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv659]) (by decide +kernel)
def pv507431 : PrimeValue := ⟨507431, pr507431⟩
private theorem pr507497 : PrimeCertificate 507497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv73,pv79]) (by decide +kernel)
def pv507497 : PrimeValue := ⟨507497, pr507497⟩
private theorem pr507499 : PrimeCertificate 507499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv2063]) (by decide +kernel)
def pv507499 : PrimeValue := ⟨507499, pr507499⟩
private theorem pr507503 : PrimeCertificate 507503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv253751]) (by decide +kernel)
def pv507503 : PrimeValue := ⟨507503, pr507503⟩
private theorem pr507523 : PrimeCertificate 507523 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv251,pv337]) (by decide +kernel)
def pv507523 : PrimeValue := ⟨507523, pr507523⟩
private theorem pr507599 : PrimeCertificate 507599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv2789]) (by decide +kernel)
def pv507599 : PrimeValue := ⟨507599, pr507599⟩
private theorem pr507667 : PrimeCertificate 507667 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv211,pv401]) (by decide +kernel)
def pv507667 : PrimeValue := ⟨507667, pr507667⟩
private theorem pr507673 : PrimeCertificate 507673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv641]) (by decide +kernel)
def pv507673 : PrimeValue := ⟨507673, pr507673⟩
private theorem pr507697 : PrimeCertificate 507697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1511]) (by decide +kernel)
def pv507697 : PrimeValue := ⟨507697, pr507697⟩
private theorem pr507779 : PrimeCertificate 507779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv307,pv827]) (by decide +kernel)
def pv507779 : PrimeValue := ⟨507779, pr507779⟩
private theorem pr507883 : PrimeCertificate 507883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv1801]) (by decide +kernel)
def pv507883 : PrimeValue := ⟨507883, pr507883⟩
private theorem pr507937 : PrimeCertificate 507937 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv13,pv37]) (by decide +kernel)
def pv507937 : PrimeValue := ⟨507937, pr507937⟩
private theorem pr507953 : PrimeCertificate 507953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv599]) (by decide +kernel)
def pv507953 : PrimeValue := ⟨507953, pr507953⟩
private theorem pr507961 : PrimeCertificate 507961 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv17,pv83]) (by decide +kernel)
def pv507961 : PrimeValue := ⟨507961, pr507961⟩
private theorem pr508033 : PrimeCertificate 508033 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv508033 : PrimeValue := ⟨508033, pr508033⟩
private theorem pr508087 : PrimeCertificate 508087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv97]) (by decide +kernel)
def pv508087 : PrimeValue := ⟨508087, pr508087⟩
private theorem pr508159 : PrimeCertificate 508159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv37,pv109]) (by decide +kernel)
def pv508159 : PrimeValue := ⟨508159, pr508159⟩
private theorem pr508171 : PrimeCertificate 508171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv1303]) (by decide +kernel)
def pv508171 : PrimeValue := ⟨508171, pr508171⟩
private theorem pr508213 : PrimeCertificate 508213 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv743]) (by decide +kernel)
def pv508213 : PrimeValue := ⟨508213, pr508213⟩
private theorem pr508243 : PrimeCertificate 508243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv12101]) (by decide +kernel)
def pv508243 : PrimeValue := ⟨508243, pr508243⟩
private theorem pr508273 : PrimeCertificate 508273 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv10589]) (by decide +kernel)
def pv508273 : PrimeValue := ⟨508273, pr508273⟩
private theorem pr508297 : PrimeCertificate 508297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv21179]) (by decide +kernel)
def pv508297 : PrimeValue := ⟨508297, pr508297⟩
private theorem pr508301 : PrimeCertificate 508301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv17,pv23]) (by decide +kernel)
def pv508301 : PrimeValue := ⟨508301, pr508301⟩
private theorem pr508327 : PrimeCertificate 508327 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv13,pv19]) (by decide +kernel)
def pv508327 : PrimeValue := ⟨508327, pr508327⟩
private theorem pr508331 : PrimeCertificate 508331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv50833]) (by decide +kernel)
def pv508331 : PrimeValue := ⟨508331, pr508331⟩
private theorem pr508373 : PrimeCertificate 508373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv1741]) (by decide +kernel)
def pv508373 : PrimeValue := ⟨508373, pr508373⟩
private theorem pr508393 : PrimeCertificate 508393 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv307]) (by decide +kernel)
def pv508393 : PrimeValue := ⟨508393, pr508393⟩
private theorem pr508439 : PrimeCertificate 508439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv1579]) (by decide +kernel)
def pv508439 : PrimeValue := ⟨508439, pr508439⟩
private theorem pr508513 : PrimeCertificate 508513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5297]) (by decide +kernel)
def pv508513 : PrimeValue := ⟨508513, pr508513⟩
private theorem pr508559 : PrimeCertificate 508559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv254279]) (by decide +kernel)
def pv508559 : PrimeValue := ⟨508559, pr508559⟩
private theorem pr508567 : PrimeCertificate 508567 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv84761]) (by decide +kernel)
def pv508567 : PrimeValue := ⟨508567, pr508567⟩
private theorem pr508577 : PrimeCertificate 508577 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv691]) (by decide +kernel)
def pv508577 : PrimeValue := ⟨508577, pr508577⟩
private theorem pr508579 : PrimeCertificate 508579 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv12109]) (by decide +kernel)
def pv508579 : PrimeValue := ⟨508579, pr508579⟩
private theorem pr508661 : PrimeCertificate 508661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv877]) (by decide +kernel)
def pv508661 : PrimeValue := ⟨508661, pr508661⟩
private theorem pr508727 : PrimeCertificate 508727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113,pv2251]) (by decide +kernel)
def pv508727 : PrimeValue := ⟨508727, pr508727⟩
private theorem pr508811 : PrimeCertificate 508811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv41,pv73]) (by decide +kernel)
def pv508811 : PrimeValue := ⟨508811, pr508811⟩
private theorem pr508841 : PrimeCertificate 508841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv12721]) (by decide +kernel)
def pv508841 : PrimeValue := ⟨508841, pr508841⟩
private theorem pr508913 : PrimeCertificate 508913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1871]) (by decide +kernel)
def pv508913 : PrimeValue := ⟨508913, pr508913⟩
private theorem pr508951 : PrimeCertificate 508951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv29]) (by decide +kernel)
def pv508951 : PrimeValue := ⟨508951, pr508951⟩
private theorem pr508961 : PrimeCertificate 508961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv3181]) (by decide +kernel)
def pv508961 : PrimeValue := ⟨508961, pr508961⟩
private theorem pr508987 : PrimeCertificate 508987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28277]) (by decide +kernel)
def pv508987 : PrimeValue := ⟨508987, pr508987⟩
private theorem pr509053 : PrimeCertificate 509053 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv59,pv719]) (by decide +kernel)
def pv509053 : PrimeValue := ⟨509053, pr509053⟩
private theorem pr509123 : PrimeCertificate 509123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv3067]) (by decide +kernel)
def pv509123 : PrimeValue := ⟨509123, pr509123⟩
private theorem pr509149 : PrimeCertificate 509149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv14143]) (by decide +kernel)
def pv509149 : PrimeValue := ⟨509149, pr509149⟩
private theorem pr509227 : PrimeCertificate 509227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv84871]) (by decide +kernel)
def pv509227 : PrimeValue := ⟨509227, pr509227⟩
private theorem pr509281 : PrimeCertificate 509281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1061]) (by decide +kernel)
def pv509281 : PrimeValue := ⟨509281, pr509281⟩
private theorem pr509287 : PrimeCertificate 509287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv4993]) (by decide +kernel)
def pv509287 : PrimeValue := ⟨509287, pr509287⟩
private theorem pr509359 : PrimeCertificate 509359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv3691]) (by decide +kernel)
def pv509359 : PrimeValue := ⟨509359, pr509359⟩
private theorem pr509429 : PrimeCertificate 509429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv6703]) (by decide +kernel)
def pv509429 : PrimeValue := ⟨509429, pr509429⟩
private theorem pr509477 : PrimeCertificate 509477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv11579]) (by decide +kernel)
def pv509477 : PrimeValue := ⟨509477, pr509477⟩
private theorem pr509513 : PrimeCertificate 509513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv63689]) (by decide +kernel)
def pv509513 : PrimeValue := ⟨509513, pr509513⟩
private theorem pr509581 : PrimeCertificate 509581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv149]) (by decide +kernel)
def pv509581 : PrimeValue := ⟨509581, pr509581⟩
private theorem pr509591 : PrimeCertificate 509591 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv131,pv389]) (by decide +kernel)
def pv509591 : PrimeValue := ⟨509591, pr509591⟩
private theorem pr509603 : PrimeCertificate 509603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv3803]) (by decide +kernel)
def pv509603 : PrimeValue := ⟨509603, pr509603⟩
private theorem pr509623 : PrimeCertificate 509623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv157,pv541]) (by decide +kernel)
def pv509623 : PrimeValue := ⟨509623, pr509623⟩
private theorem pr509633 : PrimeCertificate 509633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7963]) (by decide +kernel)
def pv509633 : PrimeValue := ⟨509633, pr509633⟩
private theorem pr509647 : PrimeCertificate 509647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv101]) (by decide +kernel)
def pv509647 : PrimeValue := ⟨509647, pr509647⟩
private theorem pr509659 : PrimeCertificate 509659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv173,pv491]) (by decide +kernel)
def pv509659 : PrimeValue := ⟨509659, pr509659⟩
private theorem pr509699 : PrimeCertificate 509699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv743]) (by decide +kernel)
def pv509699 : PrimeValue := ⟨509699, pr509699⟩
private theorem pr509723 : PrimeCertificate 509723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv5927]) (by decide +kernel)
def pv509723 : PrimeValue := ⟨509723, pr509723⟩
private theorem pr509731 : PrimeCertificate 509731 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv13,pv1307]) (by decide +kernel)
def pv509731 : PrimeValue := ⟨509731, pr509731⟩
private theorem pr509737 : PrimeCertificate 509737 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv67,pv317]) (by decide +kernel)
def pv509737 : PrimeValue := ⟨509737, pr509737⟩
private theorem pr509767 : PrimeCertificate 509767 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv84961]) (by decide +kernel)
def pv509767 : PrimeValue := ⟨509767, pr509767⟩
private theorem pr509833 : PrimeCertificate 509833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv73,pv97]) (by decide +kernel)
def pv509833 : PrimeValue := ⟨509833, pr509833⟩
private theorem pr509843 : PrimeCertificate 509843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv1123]) (by decide +kernel)
def pv509843 : PrimeValue := ⟨509843, pr509843⟩
private theorem pr509863 : PrimeCertificate 509863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv84977]) (by decide +kernel)
def pv509863 : PrimeValue := ⟨509863, pr509863⟩
private theorem pr509909 : PrimeCertificate 509909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv18211]) (by decide +kernel)
def pv509909 : PrimeValue := ⟨509909, pr509909⟩
private theorem pr509911 : PrimeCertificate 509911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv23,pv739]) (by decide +kernel)
def pv509911 : PrimeValue := ⟨509911, pr509911⟩
private theorem pr509921 : PrimeCertificate 509921 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv3187]) (by decide +kernel)
def pv509921 : PrimeValue := ⟨509921, pr509921⟩
private theorem pr509947 : PrimeCertificate 509947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv84991]) (by decide +kernel)
def pv509947 : PrimeValue := ⟨509947, pr509947⟩
private theorem pr509959 : PrimeCertificate 509959 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv41,pv691]) (by decide +kernel)
def pv509959 : PrimeValue := ⟨509959, pr509959⟩
private theorem pr509963 : PrimeCertificate 509963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv2383]) (by decide +kernel)
def pv509963 : PrimeValue := ⟨509963, pr509963⟩
private theorem pr509989 : PrimeCertificate 509989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv42499]) (by decide +kernel)
def pv509989 : PrimeValue := ⟨509989, pr509989⟩
private theorem pr510007 : PrimeCertificate 510007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv12143]) (by decide +kernel)
def pv510007 : PrimeValue := ⟨510007, pr510007⟩
private theorem pr510073 : PrimeCertificate 510073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv53,pv401]) (by decide +kernel)
def pv510073 : PrimeValue := ⟨510073, pr510073⟩
private theorem pr510127 : PrimeCertificate 510127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv85021]) (by decide +kernel)
def pv510127 : PrimeValue := ⟨510127, pr510127⟩
private theorem pr510137 : PrimeCertificate 510137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv31]) (by decide +kernel)
def pv510137 : PrimeValue := ⟨510137, pr510137⟩
private theorem pr510203 : PrimeCertificate 510203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv3313]) (by decide +kernel)
def pv510203 : PrimeValue := ⟨510203, pr510203⟩
private theorem pr510227 : PrimeCertificate 510227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv463]) (by decide +kernel)
def pv510227 : PrimeValue := ⟨510227, pr510227⟩
private theorem pr510247 : PrimeCertificate 510247 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv859]) (by decide +kernel)
def pv510247 : PrimeValue := ⟨510247, pr510247⟩
private theorem pr510299 : PrimeCertificate 510299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv255149]) (by decide +kernel)
def pv510299 : PrimeValue := ⟨510299, pr510299⟩
private theorem pr510401 : PrimeCertificate 510401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv29]) (by decide +kernel)
def pv510401 : PrimeValue := ⟨510401, pr510401⟩
private theorem pr510463 : PrimeCertificate 510463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv137]) (by decide +kernel)
def pv510463 : PrimeValue := ⟨510463, pr510463⟩
private theorem pr510553 : PrimeCertificate 510553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1013]) (by decide +kernel)
def pv510553 : PrimeValue := ⟨510553, pr510553⟩
private theorem pr510583 : PrimeCertificate 510583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv1979]) (by decide +kernel)
def pv510583 : PrimeValue := ⟨510583, pr510583⟩
private theorem pr510589 : PrimeCertificate 510589 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv1091]) (by decide +kernel)
def pv510589 : PrimeValue := ⟨510589, pr510589⟩
private theorem pr510617 : PrimeCertificate 510617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv769]) (by decide +kernel)
def pv510617 : PrimeValue := ⟨510617, pr510617⟩
private theorem pr510619 : PrimeCertificate 510619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv85103]) (by decide +kernel)
def pv510619 : PrimeValue := ⟨510619, pr510619⟩
private theorem pr510683 : PrimeCertificate 510683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv89,pv151]) (by decide +kernel)
def pv510683 : PrimeValue := ⟨510683, pr510683⟩
private theorem pr510767 : PrimeCertificate 510767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv255383]) (by decide +kernel)
def pv510767 : PrimeValue := ⟨510767, pr510767⟩
private theorem pr510817 : PrimeCertificate 510817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv313]) (by decide +kernel)
def pv510817 : PrimeValue := ⟨510817, pr510817⟩
private theorem pr511061 : PrimeCertificate 511061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv23,pv101]) (by decide +kernel)
def pv511061 : PrimeValue := ⟨511061, pr511061⟩
private theorem pr511151 : PrimeCertificate 511151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv10223]) (by decide +kernel)
def pv511151 : PrimeValue := ⟨511151, pr511151⟩
private theorem pr511177 : PrimeCertificate 511177 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv59]) (by decide +kernel)
def pv511177 : PrimeValue := ⟨511177, pr511177⟩
private theorem pr511193 : PrimeCertificate 511193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv37,pv157]) (by decide +kernel)
def pv511193 : PrimeValue := ⟨511193, pr511193⟩
private theorem pr511213 : PrimeCertificate 511213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv29,pv113]) (by decide +kernel)
def pv511213 : PrimeValue := ⟨511213, pr511213⟩
private theorem pr511237 : PrimeCertificate 511237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1291]) (by decide +kernel)
def pv511237 : PrimeValue := ⟨511237, pr511237⟩
private theorem pr511243 : PrimeCertificate 511243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv139,pv613]) (by decide +kernel)
def pv511243 : PrimeValue := ⟨511243, pr511243⟩
private theorem pr511297 : PrimeCertificate 511297 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2663]) (by decide +kernel)
def pv511297 : PrimeValue := ⟨511297, pr511297⟩
private theorem pr511327 : PrimeCertificate 511327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv557]) (by decide +kernel)
def pv511327 : PrimeValue := ⟨511327, pr511327⟩
private theorem pr511333 : PrimeCertificate 511333 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv42611]) (by decide +kernel)
def pv511333 : PrimeValue := ⟨511333, pr511333⟩
private theorem pr511417 : PrimeCertificate 511417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7103]) (by decide +kernel)
def pv511417 : PrimeValue := ⟨511417, pr511417⟩
private theorem pr511447 : PrimeCertificate 511447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv79,pv83]) (by decide +kernel)
def pv511447 : PrimeValue := ⟨511447, pr511447⟩
private theorem pr511477 : PrimeCertificate 511477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv6089]) (by decide +kernel)
def pv511477 : PrimeValue := ⟨511477, pr511477⟩
private theorem pr511507 : PrimeCertificate 511507 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv157,pv181]) (by decide +kernel)
def pv511507 : PrimeValue := ⟨511507, pr511507⟩
private theorem pr511523 : PrimeCertificate 511523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv23251]) (by decide +kernel)
def pv511523 : PrimeValue := ⟨511523, pr511523⟩
private theorem pr511541 : PrimeCertificate 511541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv25577]) (by decide +kernel)
def pv511541 : PrimeValue := ⟨511541, pr511541⟩
private theorem pr511573 : PrimeCertificate 511573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv479]) (by decide +kernel)
def pv511573 : PrimeValue := ⟨511573, pr511573⟩
private theorem pr511583 : PrimeCertificate 511583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv179,pv1429]) (by decide +kernel)
def pv511583 : PrimeValue := ⟨511583, pr511583⟩
private theorem pr511631 : PrimeCertificate 511631 :=
  certifyPrime (q := pv37) (ls := [pv2,pv5,pv7,pv7309]) (by decide +kernel)
def pv511631 : PrimeValue := ⟨511631, pr511631⟩
private theorem pr511669 : PrimeCertificate 511669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv233]) (by decide +kernel)
def pv511669 : PrimeValue := ⟨511669, pr511669⟩
private theorem pr511723 : PrimeCertificate 511723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv28429]) (by decide +kernel)
def pv511723 : PrimeValue := ⟨511723, pr511723⟩
private theorem pr511801 : PrimeCertificate 511801 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv853]) (by decide +kernel)
def pv511801 : PrimeValue := ⟨511801, pr511801⟩
private theorem pr511811 : PrimeCertificate 511811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv31,pv127]) (by decide +kernel)
def pv511811 : PrimeValue := ⟨511811, pr511811⟩
private theorem pr511859 : PrimeCertificate 511859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv6917]) (by decide +kernel)
def pv511859 : PrimeValue := ⟨511859, pr511859⟩
private theorem pr511873 : PrimeCertificate 511873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv43]) (by decide +kernel)
def pv511873 : PrimeValue := ⟨511873, pr511873⟩
private theorem pr511909 : PrimeCertificate 511909 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv1471]) (by decide +kernel)
def pv511909 : PrimeValue := ⟨511909, pr511909⟩
private theorem pr511933 : PrimeCertificate 511933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1153]) (by decide +kernel)
def pv511933 : PrimeValue := ⟨511933, pr511933⟩
private theorem pr511997 : PrimeCertificate 511997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv4129]) (by decide +kernel)
def pv511997 : PrimeValue := ⟨511997, pr511997⟩
private theorem pr512011 : PrimeCertificate 512011 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv5689]) (by decide +kernel)
def pv512011 : PrimeValue := ⟨512011, pr512011⟩
private theorem pr512021 : PrimeCertificate 512021 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv25601]) (by decide +kernel)
def pv512021 : PrimeValue := ⟨512021, pr512021⟩
private theorem pr512047 : PrimeCertificate 512047 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv28447]) (by decide +kernel)
def pv512047 : PrimeValue := ⟨512047, pr512047⟩
private theorem pr512101 : PrimeCertificate 512101 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv569]) (by decide +kernel)
def pv512101 : PrimeValue := ⟨512101, pr512101⟩
private theorem pr512269 : PrimeCertificate 512269 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv42689]) (by decide +kernel)
def pv512269 : PrimeValue := ⟨512269, pr512269⟩
private theorem pr512287 : PrimeCertificate 512287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv85381]) (by decide +kernel)
def pv512287 : PrimeValue := ⟨512287, pr512287⟩
private theorem pr512333 : PrimeCertificate 512333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv349,pv367]) (by decide +kernel)
def pv512333 : PrimeValue := ⟨512333, pr512333⟩
private theorem pr512503 : PrimeCertificate 512503 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv229,pv373]) (by decide +kernel)
def pv512503 : PrimeValue := ⟨512503, pr512503⟩
private theorem pr512507 : PrimeCertificate 512507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv13487]) (by decide +kernel)
def pv512507 : PrimeValue := ⟨512507, pr512507⟩
private theorem pr512569 : PrimeCertificate 512569 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv113]) (by decide +kernel)
def pv512569 : PrimeValue := ⟨512569, pr512569⟩
private theorem pr512573 : PrimeCertificate 512573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv1009]) (by decide +kernel)
def pv512573 : PrimeValue := ⟨512573, pr512573⟩
private theorem pr512591 : PrimeCertificate 512591 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv3943]) (by decide +kernel)
def pv512591 : PrimeValue := ⟨512591, pr512591⟩
private theorem pr512663 : PrimeCertificate 512663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv8839]) (by decide +kernel)
def pv512663 : PrimeValue := ⟨512663, pr512663⟩
private theorem pr512683 : PrimeCertificate 512683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv85447]) (by decide +kernel)
def pv512683 : PrimeValue := ⟨512683, pr512683⟩
private theorem pr512741 : PrimeCertificate 512741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv827]) (by decide +kernel)
def pv512741 : PrimeValue := ⟨512741, pr512741⟩
private theorem pr512747 : PrimeCertificate 512747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv41]) (by decide +kernel)
def pv512747 : PrimeValue := ⟨512747, pr512747⟩
private theorem pr512797 : PrimeCertificate 512797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv151,pv283]) (by decide +kernel)
def pv512797 : PrimeValue := ⟨512797, pr512797⟩
private theorem pr512903 : PrimeCertificate 512903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv19727]) (by decide +kernel)
def pv512903 : PrimeValue := ⟨512903, pr512903⟩
private theorem pr513059 : PrimeCertificate 513059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv2819]) (by decide +kernel)
def pv513059 : PrimeValue := ⟨513059, pr513059⟩
private theorem pr513083 : PrimeCertificate 513083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv256541]) (by decide +kernel)
def pv513083 : PrimeValue := ⟨513083, pr513083⟩
private theorem pr513157 : PrimeCertificate 513157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv41,pv149]) (by decide +kernel)
def pv513157 : PrimeValue := ⟨513157, pr513157⟩
private theorem pr513167 : PrimeCertificate 513167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv379,pv677]) (by decide +kernel)
def pv513167 : PrimeValue := ⟨513167, pr513167⟩
private theorem pr513173 : PrimeCertificate 513173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv107,pv109]) (by decide +kernel)
def pv513173 : PrimeValue := ⟨513173, pr513173⟩
private theorem pr513203 : PrimeCertificate 513203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv1873]) (by decide +kernel)
def pv513203 : PrimeValue := ⟨513203, pr513203⟩
private theorem pr513239 : PrimeCertificate 513239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv41,pv569]) (by decide +kernel)
def pv513239 : PrimeValue := ⟨513239, pr513239⟩
private theorem pr513257 : PrimeCertificate 513257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv64157]) (by decide +kernel)
def pv513257 : PrimeValue := ⟨513257, pr513257⟩
private theorem pr513277 : PrimeCertificate 513277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv42773]) (by decide +kernel)
def pv513277 : PrimeValue := ⟨513277, pr513277⟩
private theorem pr513313 : PrimeCertificate 513313 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5347]) (by decide +kernel)
def pv513313 : PrimeValue := ⟨513313, pr513313⟩
private theorem pr513407 : PrimeCertificate 513407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv11161]) (by decide +kernel)
def pv513407 : PrimeValue := ⟨513407, pr513407⟩
private theorem pr513439 : PrimeCertificate 513439 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv1031]) (by decide +kernel)
def pv513439 : PrimeValue := ⟨513439, pr513439⟩
private theorem pr513473 : PrimeCertificate 513473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv113]) (by decide +kernel)
def pv513473 : PrimeValue := ⟨513473, pr513473⟩
private theorem pr513481 : PrimeCertificate 513481 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv389]) (by decide +kernel)
def pv513481 : PrimeValue := ⟨513481, pr513481⟩
private theorem pr513533 : PrimeCertificate 513533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv233]) (by decide +kernel)
def pv513533 : PrimeValue := ⟨513533, pr513533⟩
private theorem pr513649 : PrimeCertificate 513649 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv29,pv41]) (by decide +kernel)
def pv513649 : PrimeValue := ⟨513649, pr513649⟩
private theorem pr513761 : PrimeCertificate 513761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv19]) (by decide +kernel)
def pv513761 : PrimeValue := ⟨513761, pr513761⟩
private theorem pr513839 : PrimeCertificate 513839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv19763]) (by decide +kernel)
def pv513839 : PrimeValue := ⟨513839, pr513839⟩
private theorem pr513899 : PrimeCertificate 513899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv47,pv71]) (by decide +kernel)
def pv513899 : PrimeValue := ⟨513899, pr513899⟩
private theorem pr513917 : PrimeCertificate 513917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv9883]) (by decide +kernel)
def pv513917 : PrimeValue := ⟨513917, pr513917⟩
private theorem pr514001 : PrimeCertificate 514001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv257]) (by decide +kernel)
def pv514001 : PrimeValue := ⟨514001, pr514001⟩
private theorem pr514013 : PrimeCertificate 514013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv7559]) (by decide +kernel)
def pv514013 : PrimeValue := ⟨514013, pr514013⟩
private theorem pr514021 : PrimeCertificate 514021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv659]) (by decide +kernel)
def pv514021 : PrimeValue := ⟨514021, pr514021⟩
private theorem pr514049 : PrimeCertificate 514049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv251]) (by decide +kernel)
def pv514049 : PrimeValue := ⟨514049, pr514049⟩
private theorem pr514103 : PrimeCertificate 514103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv83,pv163]) (by decide +kernel)
def pv514103 : PrimeValue := ⟨514103, pr514103⟩
private theorem pr514147 : PrimeCertificate 514147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv85691]) (by decide +kernel)
def pv514147 : PrimeValue := ⟨514147, pr514147⟩
private theorem pr514177 : PrimeCertificate 514177 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv103]) (by decide +kernel)
def pv514177 : PrimeValue := ⟨514177, pr514177⟩
private theorem pr514187 : PrimeCertificate 514187 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257093]) (by decide +kernel)
def pv514187 : PrimeValue := ⟨514187, pr514187⟩
private theorem pr514243 : PrimeCertificate 514243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv107]) (by decide +kernel)
def pv514243 : PrimeValue := ⟨514243, pr514243⟩
private theorem pr514289 : PrimeCertificate 514289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv32143]) (by decide +kernel)
def pv514289 : PrimeValue := ⟨514289, pr514289⟩
private theorem pr514333 : PrimeCertificate 514333 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13,pv157]) (by decide +kernel)
def pv514333 : PrimeValue := ⟨514333, pr514333⟩
private theorem pr514399 : PrimeCertificate 514399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv85733]) (by decide +kernel)
def pv514399 : PrimeValue := ⟨514399, pr514399⟩
private theorem pr514417 : PrimeCertificate 514417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv1531]) (by decide +kernel)
def pv514417 : PrimeValue := ⟨514417, pr514417⟩
private theorem pr514433 : PrimeCertificate 514433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv4019]) (by decide +kernel)
def pv514433 : PrimeValue := ⟨514433, pr514433⟩
private theorem pr514453 : PrimeCertificate 514453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv997]) (by decide +kernel)
def pv514453 : PrimeValue := ⟨514453, pr514453⟩
private theorem pr514499 : PrimeCertificate 514499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257249]) (by decide +kernel)
def pv514499 : PrimeValue := ⟨514499, pr514499⟩
private theorem pr514639 : PrimeCertificate 514639 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv28591]) (by decide +kernel)
def pv514639 : PrimeValue := ⟨514639, pr514639⟩
private theorem pr514643 : PrimeCertificate 514643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257321]) (by decide +kernel)
def pv514643 : PrimeValue := ⟨514643, pr514643⟩
private theorem pr514651 : PrimeCertificate 514651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv47,pv73]) (by decide +kernel)
def pv514651 : PrimeValue := ⟨514651, pr514651⟩
private theorem pr514669 : PrimeCertificate 514669 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv557]) (by decide +kernel)
def pv514669 : PrimeValue := ⟨514669, pr514669⟩
private theorem pr514681 : PrimeCertificate 514681 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv4289]) (by decide +kernel)
def pv514681 : PrimeValue := ⟨514681, pr514681⟩
private theorem pr514733 : PrimeCertificate 514733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv128683]) (by decide +kernel)
def pv514733 : PrimeValue := ⟨514733, pr514733⟩
private theorem pr514741 : PrimeCertificate 514741 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv373]) (by decide +kernel)
def pv514741 : PrimeValue := ⟨514741, pr514741⟩
private theorem pr514747 : PrimeCertificate 514747 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv28597]) (by decide +kernel)
def pv514747 : PrimeValue := ⟨514747, pr514747⟩
private theorem pr514783 : PrimeCertificate 514783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv9533]) (by decide +kernel)
def pv514783 : PrimeValue := ⟨514783, pr514783⟩
private theorem pr514823 : PrimeCertificate 514823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11,pv3343]) (by decide +kernel)
def pv514823 : PrimeValue := ⟨514823, pr514823⟩
private theorem pr514847 : PrimeCertificate 514847 :=
  certifyPrime (q := pv5) (ls := [pv2,pv137,pv1879]) (by decide +kernel)
def pv514847 : PrimeValue := ⟨514847, pr514847⟩
private theorem pr514867 : PrimeCertificate 514867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv29,pv269]) (by decide +kernel)
def pv514867 : PrimeValue := ⟨514867, pr514867⟩
private theorem pr514873 : PrimeCertificate 514873 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7151]) (by decide +kernel)
def pv514873 : PrimeValue := ⟨514873, pr514873⟩
private theorem pr514903 : PrimeCertificate 514903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv85817]) (by decide +kernel)
def pv514903 : PrimeValue := ⟨514903, pr514903⟩
private theorem pr514967 : PrimeCertificate 514967 :=
  certifyPrime (q := pv5) (ls := [pv2,pv37,pv6959]) (by decide +kernel)
def pv514967 : PrimeValue := ⟨514967, pr514967⟩
private theorem pr515041 : PrimeCertificate 515041 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv29,pv37]) (by decide +kernel)
def pv515041 : PrimeValue := ⟨515041, pr515041⟩
private theorem pr515087 : PrimeCertificate 515087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv1801]) (by decide +kernel)
def pv515087 : PrimeValue := ⟨515087, pr515087⟩
private theorem pr515153 : PrimeCertificate 515153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv2927]) (by decide +kernel)
def pv515153 : PrimeValue := ⟨515153, pr515153⟩
private theorem pr515191 : PrimeCertificate 515191 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv13,pv1321]) (by decide +kernel)
def pv515191 : PrimeValue := ⟨515191, pr515191⟩
private theorem pr515227 : PrimeCertificate 515227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv1997]) (by decide +kernel)
def pv515227 : PrimeValue := ⟨515227, pr515227⟩
private theorem pr515293 : PrimeCertificate 515293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv1867]) (by decide +kernel)
def pv515293 : PrimeValue := ⟨515293, pr515293⟩
private theorem pr515323 : PrimeCertificate 515323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3181]) (by decide +kernel)
def pv515323 : PrimeValue := ⟨515323, pr515323⟩
private theorem pr515351 : PrimeCertificate 515351 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv937]) (by decide +kernel)
def pv515351 : PrimeValue := ⟨515351, pr515351⟩
private theorem pr515369 : PrimeCertificate 515369 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv9203]) (by decide +kernel)
def pv515369 : PrimeValue := ⟨515369, pr515369⟩
private theorem pr515381 : PrimeCertificate 515381 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv73,pv353]) (by decide +kernel)
def pv515381 : PrimeValue := ⟨515381, pr515381⟩
private theorem pr515507 : PrimeCertificate 515507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv2281]) (by decide +kernel)
def pv515507 : PrimeValue := ⟨515507, pr515507⟩
private theorem pr515639 : PrimeCertificate 515639 :=
  certifyPrime (q := pv11) (ls := [pv2,pv311,pv829]) (by decide +kernel)
def pv515639 : PrimeValue := ⟨515639, pr515639⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
