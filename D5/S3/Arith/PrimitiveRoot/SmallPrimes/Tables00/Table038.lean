/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table038
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table038.pv100193
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table020
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table021

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr100193 : PrimeCertificate 100193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv101]) (by decide +kernel)
def pv100193 : PrimeValue := ⟨100193, pr100193⟩
private theorem pr100207 : PrimeCertificate 100207 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv293]) (by decide +kernel)
def pv100207 : PrimeValue := ⟨100207, pr100207⟩
private theorem pr100213 : PrimeCertificate 100213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1193]) (by decide +kernel)
def pv100213 : PrimeValue := ⟨100213, pr100213⟩
private theorem pr100237 : PrimeCertificate 100237 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8353]) (by decide +kernel)
def pv100237 : PrimeValue := ⟨100237, pr100237⟩
private theorem pr100267 : PrimeCertificate 100267 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv983]) (by decide +kernel)
def pv100267 : PrimeValue := ⟨100267, pr100267⟩
private theorem pr100291 : PrimeCertificate 100291 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3343]) (by decide +kernel)
def pv100291 : PrimeValue := ⟨100291, pr100291⟩
private theorem pr100297 : PrimeCertificate 100297 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv199]) (by decide +kernel)
def pv100297 : PrimeValue := ⟨100297, pr100297⟩
private theorem pr100313 : PrimeCertificate 100313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12539]) (by decide +kernel)
def pv100313 : PrimeValue := ⟨100313, pr100313⟩
private theorem pr100333 : PrimeCertificate 100333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv929]) (by decide +kernel)
def pv100333 : PrimeValue := ⟨100333, pr100333⟩
private theorem pr100343 : PrimeCertificate 100343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv4561]) (by decide +kernel)
def pv100343 : PrimeValue := ⟨100343, pr100343⟩
private theorem pr100357 : PrimeCertificate 100357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8363]) (by decide +kernel)
def pv100357 : PrimeValue := ⟨100357, pr100357⟩
private theorem pr100361 : PrimeCertificate 100361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv193]) (by decide +kernel)
def pv100361 : PrimeValue := ⟨100361, pr100361⟩
private theorem pr100363 : PrimeCertificate 100363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv389]) (by decide +kernel)
def pv100363 : PrimeValue := ⟨100363, pr100363⟩
private theorem pr100393 : PrimeCertificate 100393 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv47,pv89]) (by decide +kernel)
def pv100393 : PrimeValue := ⟨100393, pr100393⟩
private theorem pr100403 : PrimeCertificate 100403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2953]) (by decide +kernel)
def pv100403 : PrimeValue := ⟨100403, pr100403⟩
private theorem pr100411 : PrimeCertificate 100411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3347]) (by decide +kernel)
def pv100411 : PrimeValue := ⟨100411, pr100411⟩
private theorem pr100417 : PrimeCertificate 100417 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv523]) (by decide +kernel)
def pv100417 : PrimeValue := ⟨100417, pr100417⟩
private theorem pr100447 : PrimeCertificate 100447 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16741]) (by decide +kernel)
def pv100447 : PrimeValue := ⟨100447, pr100447⟩
private theorem pr100459 : PrimeCertificate 100459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5581]) (by decide +kernel)
def pv100459 : PrimeValue := ⟨100459, pr100459⟩
private theorem pr100469 : PrimeCertificate 100469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25117]) (by decide +kernel)
def pv100469 : PrimeValue := ⟨100469, pr100469⟩
private theorem pr100483 : PrimeCertificate 100483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16747]) (by decide +kernel)
def pv100483 : PrimeValue := ⟨100483, pr100483⟩
private theorem pr100493 : PrimeCertificate 100493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv97]) (by decide +kernel)
def pv100493 : PrimeValue := ⟨100493, pr100493⟩
private theorem pr100501 : PrimeCertificate 100501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv67]) (by decide +kernel)
def pv100501 : PrimeValue := ⟨100501, pr100501⟩
private theorem pr100511 : PrimeCertificate 100511 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv23]) (by decide +kernel)
def pv100511 : PrimeValue := ⟨100511, pr100511⟩
private theorem pr100517 : PrimeCertificate 100517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv1933]) (by decide +kernel)
def pv100517 : PrimeValue := ⟨100517, pr100517⟩
private theorem pr100519 : PrimeCertificate 100519 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv1523]) (by decide +kernel)
def pv100519 : PrimeValue := ⟨100519, pr100519⟩
private theorem pr100523 : PrimeCertificate 100523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50261]) (by decide +kernel)
def pv100523 : PrimeValue := ⟨100523, pr100523⟩
private theorem pr100537 : PrimeCertificate 100537 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv59,pv71]) (by decide +kernel)
def pv100537 : PrimeValue := ⟨100537, pr100537⟩
private theorem pr100547 : PrimeCertificate 100547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50273]) (by decide +kernel)
def pv100547 : PrimeValue := ⟨100547, pr100547⟩
private theorem pr100549 : PrimeCertificate 100549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv100549 : PrimeValue := ⟨100549, pr100549⟩
private theorem pr100559 : PrimeCertificate 100559 :=
  certifyPrime (q := pv7) (ls := [pv2,pv137,pv367]) (by decide +kernel)
def pv100559 : PrimeValue := ⟨100559, pr100559⟩
private theorem pr100591 : PrimeCertificate 100591 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv7,pv479]) (by decide +kernel)
def pv100591 : PrimeValue := ⟨100591, pr100591⟩
private theorem pr100609 : PrimeCertificate 100609 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv100609 : PrimeValue := ⟨100609, pr100609⟩
private theorem pr100613 : PrimeCertificate 100613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25153]) (by decide +kernel)
def pv100613 : PrimeValue := ⟨100613, pr100613⟩
private theorem pr100621 : PrimeCertificate 100621 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv13,pv43]) (by decide +kernel)
def pv100621 : PrimeValue := ⟨100621, pr100621⟩
private theorem pr100649 : PrimeCertificate 100649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv547]) (by decide +kernel)
def pv100649 : PrimeValue := ⟨100649, pr100649⟩
private theorem pr100669 : PrimeCertificate 100669 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv8389]) (by decide +kernel)
def pv100669 : PrimeValue := ⟨100669, pr100669⟩
private theorem pr100673 : PrimeCertificate 100673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv13]) (by decide +kernel)
def pv100673 : PrimeValue := ⟨100673, pr100673⟩
private theorem pr100693 : PrimeCertificate 100693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2797]) (by decide +kernel)
def pv100693 : PrimeValue := ⟨100693, pr100693⟩
private theorem pr100699 : PrimeCertificate 100699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1291]) (by decide +kernel)
def pv100699 : PrimeValue := ⟨100699, pr100699⟩
private theorem pr100703 : PrimeCertificate 100703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv7193]) (by decide +kernel)
def pv100703 : PrimeValue := ⟨100703, pr100703⟩
private theorem pr100733 : PrimeCertificate 100733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25183]) (by decide +kernel)
def pv100733 : PrimeValue := ⟨100733, pr100733⟩
private theorem pr100741 : PrimeCertificate 100741 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv23,pv73]) (by decide +kernel)
def pv100741 : PrimeValue := ⟨100741, pr100741⟩
private theorem pr100747 : PrimeCertificate 100747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv193]) (by decide +kernel)
def pv100747 : PrimeValue := ⟨100747, pr100747⟩
private theorem pr100769 : PrimeCertificate 100769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv67]) (by decide +kernel)
def pv100769 : PrimeValue := ⟨100769, pr100769⟩
private theorem pr100787 : PrimeCertificate 100787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv313]) (by decide +kernel)
def pv100787 : PrimeValue := ⟨100787, pr100787⟩
private theorem pr100799 : PrimeCertificate 100799 :=
  certifyPrime (q := pv17) (ls := [pv2,pv101,pv499]) (by decide +kernel)
def pv100799 : PrimeValue := ⟨100799, pr100799⟩
private theorem pr100801 : PrimeCertificate 100801 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv100801 : PrimeValue := ⟨100801, pr100801⟩
private theorem pr100811 : PrimeCertificate 100811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv593]) (by decide +kernel)
def pv100811 : PrimeValue := ⟨100811, pr100811⟩
private theorem pr100823 : PrimeCertificate 100823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv50411]) (by decide +kernel)
def pv100823 : PrimeValue := ⟨100823, pr100823⟩
private theorem pr100829 : PrimeCertificate 100829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv277]) (by decide +kernel)
def pv100829 : PrimeValue := ⟨100829, pr100829⟩
private theorem pr100907 : PrimeCertificate 100907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv3881]) (by decide +kernel)
def pv100907 : PrimeValue := ⟨100907, pr100907⟩
private theorem pr100913 : PrimeCertificate 100913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv53]) (by decide +kernel)
def pv100913 : PrimeValue := ⟨100913, pr100913⟩
private theorem pr100927 : PrimeCertificate 100927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv89]) (by decide +kernel)
def pv100927 : PrimeValue := ⟨100927, pr100927⟩
private theorem pr100937 : PrimeCertificate 100937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv31,pv37]) (by decide +kernel)
def pv100937 : PrimeValue := ⟨100937, pr100937⟩
private theorem pr100957 : PrimeCertificate 100957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv179]) (by decide +kernel)
def pv100957 : PrimeValue := ⟨100957, pr100957⟩
private theorem pr100981 : PrimeCertificate 100981 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv100981 : PrimeValue := ⟨100981, pr100981⟩
private theorem pr100987 : PrimeCertificate 100987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16831]) (by decide +kernel)
def pv100987 : PrimeValue := ⟨100987, pr100987⟩
private theorem pr100999 : PrimeCertificate 100999 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv181]) (by decide +kernel)
def pv100999 : PrimeValue := ⟨100999, pr100999⟩
private theorem pr101009 : PrimeCertificate 101009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv107]) (by decide +kernel)
def pv101009 : PrimeValue := ⟨101009, pr101009⟩
private theorem pr101021 : PrimeCertificate 101021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5051]) (by decide +kernel)
def pv101021 : PrimeValue := ⟨101021, pr101021⟩
private theorem pr101027 : PrimeCertificate 101027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50513]) (by decide +kernel)
def pv101027 : PrimeValue := ⟨101027, pr101027⟩
private theorem pr101051 : PrimeCertificate 101051 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv47]) (by decide +kernel)
def pv101051 : PrimeValue := ⟨101051, pr101051⟩
private theorem pr101063 : PrimeCertificate 101063 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv23]) (by decide +kernel)
def pv101063 : PrimeValue := ⟨101063, pr101063⟩
private theorem pr101081 : PrimeCertificate 101081 :=
  certifyPrime (q := pv59) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv101081 : PrimeValue := ⟨101081, pr101081⟩
private theorem pr101089 : PrimeCertificate 101089 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv101089 : PrimeValue := ⟨101089, pr101089⟩
private theorem pr101107 : PrimeCertificate 101107 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv41,pv137]) (by decide +kernel)
def pv101107 : PrimeValue := ⟨101107, pr101107⟩
private theorem pr101111 : PrimeCertificate 101111 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv10111]) (by decide +kernel)
def pv101111 : PrimeValue := ⟨101111, pr101111⟩
private theorem pr101113 : PrimeCertificate 101113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv383]) (by decide +kernel)
def pv101113 : PrimeValue := ⟨101113, pr101113⟩
private theorem pr101117 : PrimeCertificate 101117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1487]) (by decide +kernel)
def pv101117 : PrimeValue := ⟨101117, pr101117⟩
private theorem pr101119 : PrimeCertificate 101119 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv887]) (by decide +kernel)
def pv101119 : PrimeValue := ⟨101119, pr101119⟩
private theorem pr101141 : PrimeCertificate 101141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv389]) (by decide +kernel)
def pv101141 : PrimeValue := ⟨101141, pr101141⟩
private theorem pr101149 : PrimeCertificate 101149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8429]) (by decide +kernel)
def pv101149 : PrimeValue := ⟨101149, pr101149⟩
private theorem pr101159 : PrimeCertificate 101159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv37,pv1367]) (by decide +kernel)
def pv101159 : PrimeValue := ⟨101159, pr101159⟩
private theorem pr101161 : PrimeCertificate 101161 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv101161 : PrimeValue := ⟨101161, pr101161⟩
private theorem pr101173 : PrimeCertificate 101173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8431]) (by decide +kernel)
def pv101173 : PrimeValue := ⟨101173, pr101173⟩
private theorem pr101183 : PrimeCertificate 101183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv50591]) (by decide +kernel)
def pv101183 : PrimeValue := ⟨101183, pr101183⟩
private theorem pr101197 : PrimeCertificate 101197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv937]) (by decide +kernel)
def pv101197 : PrimeValue := ⟨101197, pr101197⟩
private theorem pr101203 : PrimeCertificate 101203 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv101,pv167]) (by decide +kernel)
def pv101203 : PrimeValue := ⟨101203, pr101203⟩
private theorem pr101209 : PrimeCertificate 101209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv4217]) (by decide +kernel)
def pv101209 : PrimeValue := ⟨101209, pr101209⟩
private theorem pr101267 : PrimeCertificate 101267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4603]) (by decide +kernel)
def pv101267 : PrimeValue := ⟨101267, pr101267⟩
private theorem pr101273 : PrimeCertificate 101273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12659]) (by decide +kernel)
def pv101273 : PrimeValue := ⟨101273, pr101273⟩
private theorem pr101279 : PrimeCertificate 101279 :=
  certifyPrime (q := pv17) (ls := [pv2,pv79,pv641]) (by decide +kernel)
def pv101279 : PrimeValue := ⟨101279, pr101279⟩
private theorem pr101281 : PrimeCertificate 101281 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv211]) (by decide +kernel)
def pv101281 : PrimeValue := ⟨101281, pr101281⟩
private theorem pr101287 : PrimeCertificate 101287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv331]) (by decide +kernel)
def pv101287 : PrimeValue := ⟨101287, pr101287⟩
private theorem pr101293 : PrimeCertificate 101293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv367]) (by decide +kernel)
def pv101293 : PrimeValue := ⟨101293, pr101293⟩
private theorem pr101323 : PrimeCertificate 101323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv433]) (by decide +kernel)
def pv101323 : PrimeValue := ⟨101323, pr101323⟩
private theorem pr101333 : PrimeCertificate 101333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv47]) (by decide +kernel)
def pv101333 : PrimeValue := ⟨101333, pr101333⟩
private theorem pr101341 : PrimeCertificate 101341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv563]) (by decide +kernel)
def pv101341 : PrimeValue := ⟨101341, pr101341⟩
private theorem pr101347 : PrimeCertificate 101347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv127]) (by decide +kernel)
def pv101347 : PrimeValue := ⟨101347, pr101347⟩
private theorem pr101359 : PrimeCertificate 101359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1877]) (by decide +kernel)
def pv101359 : PrimeValue := ⟨101359, pr101359⟩
private theorem pr101363 : PrimeCertificate 101363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv859]) (by decide +kernel)
def pv101363 : PrimeValue := ⟨101363, pr101363⟩
private theorem pr101377 : PrimeCertificate 101377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv101377 : PrimeValue := ⟨101377, pr101377⟩
private theorem pr101383 : PrimeCertificate 101383 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv61,pv277]) (by decide +kernel)
def pv101383 : PrimeValue := ⟨101383, pr101383⟩
private theorem pr101399 : PrimeCertificate 101399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv419]) (by decide +kernel)
def pv101399 : PrimeValue := ⟨101399, pr101399⟩
private theorem pr101411 : PrimeCertificate 101411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv10141]) (by decide +kernel)
def pv101411 : PrimeValue := ⟨101411, pr101411⟩
private theorem pr101419 : PrimeCertificate 101419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv16903]) (by decide +kernel)
def pv101419 : PrimeValue := ⟨101419, pr101419⟩
private theorem pr101429 : PrimeCertificate 101429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25357]) (by decide +kernel)
def pv101429 : PrimeValue := ⟨101429, pr101429⟩
private theorem pr101467 : PrimeCertificate 101467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1879]) (by decide +kernel)
def pv101467 : PrimeValue := ⟨101467, pr101467⟩
private theorem pr101477 : PrimeCertificate 101477 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv1103]) (by decide +kernel)
def pv101477 : PrimeValue := ⟨101477, pr101477⟩
private theorem pr101483 : PrimeCertificate 101483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50741]) (by decide +kernel)
def pv101483 : PrimeValue := ⟨101483, pr101483⟩
private theorem pr101489 : PrimeCertificate 101489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6343]) (by decide +kernel)
def pv101489 : PrimeValue := ⟨101489, pr101489⟩
private theorem pr101501 : PrimeCertificate 101501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv29]) (by decide +kernel)
def pv101501 : PrimeValue := ⟨101501, pr101501⟩
private theorem pr101503 : PrimeCertificate 101503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5639]) (by decide +kernel)
def pv101503 : PrimeValue := ⟨101503, pr101503⟩
private theorem pr101513 : PrimeCertificate 101513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12689]) (by decide +kernel)
def pv101513 : PrimeValue := ⟨101513, pr101513⟩
private theorem pr101527 : PrimeCertificate 101527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv16921]) (by decide +kernel)
def pv101527 : PrimeValue := ⟨101527, pr101527⟩
private theorem pr101531 : PrimeCertificate 101531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv71]) (by decide +kernel)
def pv101531 : PrimeValue := ⟨101531, pr101531⟩
private theorem pr101533 : PrimeCertificate 101533 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8461]) (by decide +kernel)
def pv101533 : PrimeValue := ⟨101533, pr101533⟩
private theorem pr101537 : PrimeCertificate 101537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv167]) (by decide +kernel)
def pv101537 : PrimeValue := ⟨101537, pr101537⟩
private theorem pr101561 : PrimeCertificate 101561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2539]) (by decide +kernel)
def pv101561 : PrimeValue := ⟨101561, pr101561⟩
private theorem pr101573 : PrimeCertificate 101573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv379]) (by decide +kernel)
def pv101573 : PrimeValue := ⟨101573, pr101573⟩
private theorem pr101581 : PrimeCertificate 101581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1693]) (by decide +kernel)
def pv101581 : PrimeValue := ⟨101581, pr101581⟩
private theorem pr101599 : PrimeCertificate 101599 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv41,pv59]) (by decide +kernel)
def pv101599 : PrimeValue := ⟨101599, pr101599⟩
private theorem pr101603 : PrimeCertificate 101603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv1373]) (by decide +kernel)
def pv101603 : PrimeValue := ⟨101603, pr101603⟩
private theorem pr101611 : PrimeCertificate 101611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1129]) (by decide +kernel)
def pv101611 : PrimeValue := ⟨101611, pr101611⟩
private theorem pr101627 : PrimeCertificate 101627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv61]) (by decide +kernel)
def pv101627 : PrimeValue := ⟨101627, pr101627⟩
private theorem pr101641 : PrimeCertificate 101641 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv101641 : PrimeValue := ⟨101641, pr101641⟩
private theorem pr101653 : PrimeCertificate 101653 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv43,pv197]) (by decide +kernel)
def pv101653 : PrimeValue := ⟨101653, pr101653⟩
private theorem pr101663 : PrimeCertificate 101663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv4621]) (by decide +kernel)
def pv101663 : PrimeValue := ⟨101663, pr101663⟩
private theorem pr101681 : PrimeCertificate 101681 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv41]) (by decide +kernel)
def pv101681 : PrimeValue := ⟨101681, pr101681⟩
private theorem pr101693 : PrimeCertificate 101693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25423]) (by decide +kernel)
def pv101693 : PrimeValue := ⟨101693, pr101693⟩
private theorem pr101701 : PrimeCertificate 101701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv113]) (by decide +kernel)
def pv101701 : PrimeValue := ⟨101701, pr101701⟩
private theorem pr101719 : PrimeCertificate 101719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5651]) (by decide +kernel)
def pv101719 : PrimeValue := ⟨101719, pr101719⟩
private theorem pr101723 : PrimeCertificate 101723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv181,pv281]) (by decide +kernel)
def pv101723 : PrimeValue := ⟨101723, pr101723⟩
private theorem pr101737 : PrimeCertificate 101737 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv157]) (by decide +kernel)
def pv101737 : PrimeValue := ⟨101737, pr101737⟩
private theorem pr101741 : PrimeCertificate 101741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5087]) (by decide +kernel)
def pv101741 : PrimeValue := ⟨101741, pr101741⟩
private theorem pr101747 : PrimeCertificate 101747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50873]) (by decide +kernel)
def pv101747 : PrimeValue := ⟨101747, pr101747⟩
private theorem pr101749 : PrimeCertificate 101749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv139]) (by decide +kernel)
def pv101749 : PrimeValue := ⟨101749, pr101749⟩
private theorem pr101771 : PrimeCertificate 101771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv10177]) (by decide +kernel)
def pv101771 : PrimeValue := ⟨101771, pr101771⟩
private theorem pr101789 : PrimeCertificate 101789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25447]) (by decide +kernel)
def pv101789 : PrimeValue := ⟨101789, pr101789⟩
private theorem pr101797 : PrimeCertificate 101797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv499]) (by decide +kernel)
def pv101797 : PrimeValue := ⟨101797, pr101797⟩
private theorem pr101807 : PrimeCertificate 101807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv109,pv467]) (by decide +kernel)
def pv101807 : PrimeValue := ⟨101807, pr101807⟩
private theorem pr101833 : PrimeCertificate 101833 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4243]) (by decide +kernel)
def pv101833 : PrimeValue := ⟨101833, pr101833⟩
private theorem pr101837 : PrimeCertificate 101837 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv3637]) (by decide +kernel)
def pv101837 : PrimeValue := ⟨101837, pr101837⟩
private theorem pr101839 : PrimeCertificate 101839 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv1543]) (by decide +kernel)
def pv101839 : PrimeValue := ⟨101839, pr101839⟩
private theorem pr101863 : PrimeCertificate 101863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5659]) (by decide +kernel)
def pv101863 : PrimeValue := ⟨101863, pr101863⟩
private theorem pr101869 : PrimeCertificate 101869 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv653]) (by decide +kernel)
def pv101869 : PrimeValue := ⟨101869, pr101869⟩
private theorem pr101873 : PrimeCertificate 101873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6367]) (by decide +kernel)
def pv101873 : PrimeValue := ⟨101873, pr101873⟩
private theorem pr101879 : PrimeCertificate 101879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv383]) (by decide +kernel)
def pv101879 : PrimeValue := ⟨101879, pr101879⟩
private theorem pr101891 : PrimeCertificate 101891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv443]) (by decide +kernel)
def pv101891 : PrimeValue := ⟨101891, pr101891⟩
private theorem pr101917 : PrimeCertificate 101917 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv149]) (by decide +kernel)
def pv101917 : PrimeValue := ⟨101917, pr101917⟩
private theorem pr101921 : PrimeCertificate 101921 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv101921 : PrimeValue := ⟨101921, pr101921⟩
private theorem pr101929 : PrimeCertificate 101929 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv31,pv137]) (by decide +kernel)
def pv101929 : PrimeValue := ⟨101929, pr101929⟩
private theorem pr101939 : PrimeCertificate 101939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50969]) (by decide +kernel)
def pv101939 : PrimeValue := ⟨101939, pr101939⟩
private theorem pr101957 : PrimeCertificate 101957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv359]) (by decide +kernel)
def pv101957 : PrimeValue := ⟨101957, pr101957⟩
private theorem pr101963 : PrimeCertificate 101963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv7283]) (by decide +kernel)
def pv101963 : PrimeValue := ⟨101963, pr101963⟩
private theorem pr101977 : PrimeCertificate 101977 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv607]) (by decide +kernel)
def pv101977 : PrimeValue := ⟨101977, pr101977⟩
private theorem pr101987 : PrimeCertificate 101987 :=
  certifyPrime (q := pv2) (ls := [pv2,pv50993]) (by decide +kernel)
def pv101987 : PrimeValue := ⟨101987, pr101987⟩
private theorem pr101999 : PrimeCertificate 101999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv3923]) (by decide +kernel)
def pv101999 : PrimeValue := ⟨101999, pr101999⟩
private theorem pr102001 : PrimeCertificate 102001 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv102001 : PrimeValue := ⟨102001, pr102001⟩
private theorem pr102013 : PrimeCertificate 102013 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv8501]) (by decide +kernel)
def pv102013 : PrimeValue := ⟨102013, pr102013⟩
private theorem pr102019 : PrimeCertificate 102019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv347]) (by decide +kernel)
def pv102019 : PrimeValue := ⟨102019, pr102019⟩
private theorem pr102023 : PrimeCertificate 102023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv1759]) (by decide +kernel)
def pv102023 : PrimeValue := ⟨102023, pr102023⟩
private theorem pr102031 : PrimeCertificate 102031 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv19,pv179]) (by decide +kernel)
def pv102031 : PrimeValue := ⟨102031, pr102031⟩
private theorem pr102043 : PrimeCertificate 102043 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv5669]) (by decide +kernel)
def pv102043 : PrimeValue := ⟨102043, pr102043⟩
private theorem pr102059 : PrimeCertificate 102059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4639]) (by decide +kernel)
def pv102059 : PrimeValue := ⟨102059, pr102059⟩
private theorem pr102061 : PrimeCertificate 102061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv102061 : PrimeValue := ⟨102061, pr102061⟩
private theorem pr102071 : PrimeCertificate 102071 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv59,pv173]) (by decide +kernel)
def pv102071 : PrimeValue := ⟨102071, pr102071⟩
private theorem pr102077 : PrimeCertificate 102077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv151]) (by decide +kernel)
def pv102077 : PrimeValue := ⟨102077, pr102077⟩
private theorem pr102079 : PrimeCertificate 102079 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv53,pv107]) (by decide +kernel)
def pv102079 : PrimeValue := ⟨102079, pr102079⟩
private theorem pr102101 : PrimeCertificate 102101 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1021]) (by decide +kernel)
def pv102101 : PrimeValue := ⟨102101, pr102101⟩
private theorem pr102103 : PrimeCertificate 102103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv13,pv17]) (by decide +kernel)
def pv102103 : PrimeValue := ⟨102103, pr102103⟩
private theorem pr102107 : PrimeCertificate 102107 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2687]) (by decide +kernel)
def pv102107 : PrimeValue := ⟨102107, pr102107⟩
private theorem pr102121 : PrimeCertificate 102121 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv37]) (by decide +kernel)
def pv102121 : PrimeValue := ⟨102121, pr102121⟩
private theorem pr102149 : PrimeCertificate 102149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25537]) (by decide +kernel)
def pv102149 : PrimeValue := ⟨102149, pr102149⟩
private theorem pr102161 : PrimeCertificate 102161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv1277]) (by decide +kernel)
def pv102161 : PrimeValue := ⟨102161, pr102161⟩
private theorem pr102181 : PrimeCertificate 102181 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv131]) (by decide +kernel)
def pv102181 : PrimeValue := ⟨102181, pr102181⟩
private theorem pr102191 : PrimeCertificate 102191 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv929]) (by decide +kernel)
def pv102191 : PrimeValue := ⟨102191, pr102191⟩
private theorem pr102199 : PrimeCertificate 102199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv17033]) (by decide +kernel)
def pv102199 : PrimeValue := ⟨102199, pr102199⟩
private theorem pr102203 : PrimeCertificate 102203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv373]) (by decide +kernel)
def pv102203 : PrimeValue := ⟨102203, pr102203⟩
private theorem pr102217 : PrimeCertificate 102217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4259]) (by decide +kernel)
def pv102217 : PrimeValue := ⟨102217, pr102217⟩
private theorem pr102229 : PrimeCertificate 102229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1217]) (by decide +kernel)
def pv102229 : PrimeValue := ⟨102229, pr102229⟩
private theorem pr102233 : PrimeCertificate 102233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv983]) (by decide +kernel)
def pv102233 : PrimeValue := ⟨102233, pr102233⟩
private theorem pr102241 : PrimeCertificate 102241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv102241 : PrimeValue := ⟨102241, pr102241⟩
private theorem pr102251 : PrimeCertificate 102251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv409]) (by decide +kernel)
def pv102251 : PrimeValue := ⟨102251, pr102251⟩
private theorem pr102253 : PrimeCertificate 102253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8521]) (by decide +kernel)
def pv102253 : PrimeValue := ⟨102253, pr102253⟩
private theorem pr102259 : PrimeCertificate 102259 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv19,pv23]) (by decide +kernel)
def pv102259 : PrimeValue := ⟨102259, pr102259⟩
private theorem pr102293 : PrimeCertificate 102293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv239]) (by decide +kernel)
def pv102293 : PrimeValue := ⟨102293, pr102293⟩
private theorem pr102299 : PrimeCertificate 102299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv7307]) (by decide +kernel)
def pv102299 : PrimeValue := ⟨102299, pr102299⟩
private theorem pr102301 : PrimeCertificate 102301 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv31]) (by decide +kernel)
def pv102301 : PrimeValue := ⟨102301, pr102301⟩
private theorem pr102317 : PrimeCertificate 102317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25579]) (by decide +kernel)
def pv102317 : PrimeValue := ⟨102317, pr102317⟩
private theorem pr102329 : PrimeCertificate 102329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv12791]) (by decide +kernel)
def pv102329 : PrimeValue := ⟨102329, pr102329⟩
private theorem pr102337 : PrimeCertificate 102337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv41]) (by decide +kernel)
def pv102337 : PrimeValue := ⟨102337, pr102337⟩
private theorem pr102359 : PrimeCertificate 102359 :=
  certifyPrime (q := pv11) (ls := [pv2,pv61,pv839]) (by decide +kernel)
def pv102359 : PrimeValue := ⟨102359, pr102359⟩
private theorem pr102367 : PrimeCertificate 102367 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv102367 : PrimeValue := ⟨102367, pr102367⟩
private theorem pr102397 : PrimeCertificate 102397 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv23,pv53]) (by decide +kernel)
def pv102397 : PrimeValue := ⟨102397, pr102397⟩
private theorem pr102407 : PrimeCertificate 102407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv51203]) (by decide +kernel)
def pv102407 : PrimeValue := ⟨102407, pr102407⟩
private theorem pr102409 : PrimeCertificate 102409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv251]) (by decide +kernel)
def pv102409 : PrimeValue := ⟨102409, pr102409⟩
private theorem pr102433 : PrimeCertificate 102433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv102433 : PrimeValue := ⟨102433, pr102433⟩
private theorem pr102437 : PrimeCertificate 102437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv25609]) (by decide +kernel)
def pv102437 : PrimeValue := ⟨102437, pr102437⟩
private theorem pr102451 : PrimeCertificate 102451 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv683]) (by decide +kernel)
def pv102451 : PrimeValue := ⟨102451, pr102451⟩
private theorem pr102461 : PrimeCertificate 102461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv109]) (by decide +kernel)
def pv102461 : PrimeValue := ⟨102461, pr102461⟩
private theorem pr102481 : PrimeCertificate 102481 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv61]) (by decide +kernel)
def pv102481 : PrimeValue := ⟨102481, pr102481⟩
private theorem pr102497 : PrimeCertificate 102497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3203]) (by decide +kernel)
def pv102497 : PrimeValue := ⟨102497, pr102497⟩
private theorem pr102499 : PrimeCertificate 102499 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv1553]) (by decide +kernel)
def pv102499 : PrimeValue := ⟨102499, pr102499⟩
private theorem pr102503 : PrimeCertificate 102503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv967]) (by decide +kernel)
def pv102503 : PrimeValue := ⟨102503, pr102503⟩
private theorem pr102523 : PrimeCertificate 102523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2441]) (by decide +kernel)
def pv102523 : PrimeValue := ⟨102523, pr102523⟩
private theorem pr102539 : PrimeCertificate 102539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv307]) (by decide +kernel)
def pv102539 : PrimeValue := ⟨102539, pr102539⟩
private theorem pr102547 : PrimeCertificate 102547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv211]) (by decide +kernel)
def pv102547 : PrimeValue := ⟨102547, pr102547⟩
private theorem pr102551 : PrimeCertificate 102551 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv293]) (by decide +kernel)
def pv102551 : PrimeValue := ⟨102551, pr102551⟩
private theorem pr102559 : PrimeCertificate 102559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17093]) (by decide +kernel)
def pv102559 : PrimeValue := ⟨102559, pr102559⟩
private theorem pr102563 : PrimeCertificate 102563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2699]) (by decide +kernel)
def pv102563 : PrimeValue := ⟨102563, pr102563⟩
private theorem pr102587 : PrimeCertificate 102587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv4663]) (by decide +kernel)
def pv102587 : PrimeValue := ⟨102587, pr102587⟩
private theorem pr102593 : PrimeCertificate 102593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv229]) (by decide +kernel)
def pv102593 : PrimeValue := ⟨102593, pr102593⟩
private theorem pr102607 : PrimeCertificate 102607 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv349]) (by decide +kernel)
def pv102607 : PrimeValue := ⟨102607, pr102607⟩
private theorem pr102611 : PrimeCertificate 102611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv331]) (by decide +kernel)
def pv102611 : PrimeValue := ⟨102611, pr102611⟩
private theorem pr102643 : PrimeCertificate 102643 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17107]) (by decide +kernel)
def pv102643 : PrimeValue := ⟨102643, pr102643⟩
private theorem pr102647 : PrimeCertificate 102647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv3019]) (by decide +kernel)
def pv102647 : PrimeValue := ⟨102647, pr102647⟩
private theorem pr102653 : PrimeCertificate 102653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2333]) (by decide +kernel)
def pv102653 : PrimeValue := ⟨102653, pr102653⟩
private theorem pr102667 : PrimeCertificate 102667 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv71,pv241]) (by decide +kernel)
def pv102667 : PrimeValue := ⟨102667, pr102667⟩
private theorem pr102673 : PrimeCertificate 102673 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv31]) (by decide +kernel)
def pv102673 : PrimeValue := ⟨102673, pr102673⟩
private theorem pr102677 : PrimeCertificate 102677 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv19,pv193]) (by decide +kernel)
def pv102677 : PrimeValue := ⟨102677, pr102677⟩
private theorem pr102679 : PrimeCertificate 102679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv157]) (by decide +kernel)
def pv102679 : PrimeValue := ⟨102679, pr102679⟩
private theorem pr102701 : PrimeCertificate 102701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv79]) (by decide +kernel)
def pv102701 : PrimeValue := ⟨102701, pr102701⟩
private theorem pr102761 : PrimeCertificate 102761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv367]) (by decide +kernel)
def pv102761 : PrimeValue := ⟨102761, pr102761⟩
private theorem pr102763 : PrimeCertificate 102763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv173]) (by decide +kernel)
def pv102763 : PrimeValue := ⟨102763, pr102763⟩
private theorem pr102769 : PrimeCertificate 102769 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv2141]) (by decide +kernel)
def pv102769 : PrimeValue := ⟨102769, pr102769⟩
private theorem pr102793 : PrimeCertificate 102793 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4283]) (by decide +kernel)
def pv102793 : PrimeValue := ⟨102793, pr102793⟩
private theorem pr102797 : PrimeCertificate 102797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv829]) (by decide +kernel)
def pv102797 : PrimeValue := ⟨102797, pr102797⟩
private theorem pr102811 : PrimeCertificate 102811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv23,pv149]) (by decide +kernel)
def pv102811 : PrimeValue := ⟨102811, pr102811⟩
private theorem pr102829 : PrimeCertificate 102829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv41]) (by decide +kernel)
def pv102829 : PrimeValue := ⟨102829, pr102829⟩
private theorem pr102841 : PrimeCertificate 102841 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv857]) (by decide +kernel)
def pv102841 : PrimeValue := ⟨102841, pr102841⟩
private theorem pr102859 : PrimeCertificate 102859 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv31,pv79]) (by decide +kernel)
def pv102859 : PrimeValue := ⟨102859, pr102859⟩
private theorem pr102871 : PrimeCertificate 102871 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv102871 : PrimeValue := ⟨102871, pr102871⟩
private theorem pr102877 : PrimeCertificate 102877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv8573]) (by decide +kernel)
def pv102877 : PrimeValue := ⟨102877, pr102877⟩
private theorem pr102881 : PrimeCertificate 102881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv643]) (by decide +kernel)
def pv102881 : PrimeValue := ⟨102881, pr102881⟩
private theorem pr102911 : PrimeCertificate 102911 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv41,pv251]) (by decide +kernel)
def pv102911 : PrimeValue := ⟨102911, pr102911⟩
private theorem pr102913 : PrimeCertificate 102913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv102913 : PrimeValue := ⟨102913, pr102913⟩
private theorem pr102929 : PrimeCertificate 102929 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv919]) (by decide +kernel)
def pv102929 : PrimeValue := ⟨102929, pr102929⟩
private theorem pr102931 : PrimeCertificate 102931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv47,pv73]) (by decide +kernel)
def pv102931 : PrimeValue := ⟨102931, pr102931⟩
private theorem pr102953 : PrimeCertificate 102953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv757]) (by decide +kernel)
def pv102953 : PrimeValue := ⟨102953, pr102953⟩
private theorem pr102967 : PrimeCertificate 102967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv102967 : PrimeValue := ⟨102967, pr102967⟩
private theorem pr102983 : PrimeCertificate 102983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv31,pv151]) (by decide +kernel)
def pv102983 : PrimeValue := ⟨102983, pr102983⟩
private theorem pr103001 : PrimeCertificate 103001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv103]) (by decide +kernel)
def pv103001 : PrimeValue := ⟨103001, pr103001⟩
private theorem pr103007 : PrimeCertificate 103007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv51503]) (by decide +kernel)
def pv103007 : PrimeValue := ⟨103007, pr103007⟩
private theorem pr103043 : PrimeCertificate 103043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv51521]) (by decide +kernel)
def pv103043 : PrimeValue := ⟨103043, pr103043⟩
private theorem pr103049 : PrimeCertificate 103049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1171]) (by decide +kernel)
def pv103049 : PrimeValue := ⟨103049, pr103049⟩
private theorem pr103067 : PrimeCertificate 103067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1777]) (by decide +kernel)
def pv103067 : PrimeValue := ⟨103067, pr103067⟩
private theorem pr103069 : PrimeCertificate 103069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv409]) (by decide +kernel)
def pv103069 : PrimeValue := ⟨103069, pr103069⟩
private theorem pr103079 : PrimeCertificate 103079 :=
  certifyPrime (q := pv7) (ls := [pv2,pv51539]) (by decide +kernel)
def pv103079 : PrimeValue := ⟨103079, pr103079⟩
private theorem pr103087 : PrimeCertificate 103087 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv83]) (by decide +kernel)
def pv103087 : PrimeValue := ⟨103087, pr103087⟩
private theorem pr103091 : PrimeCertificate 103091 :=
  certifyPrime (q := pv89) (ls := [pv2,pv5,pv13,pv61]) (by decide +kernel)
def pv103091 : PrimeValue := ⟨103091, pr103091⟩
private theorem pr103093 : PrimeCertificate 103093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv71]) (by decide +kernel)
def pv103093 : PrimeValue := ⟨103093, pr103093⟩
private theorem pr103099 : PrimeCertificate 103099 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv17183]) (by decide +kernel)
def pv103099 : PrimeValue := ⟨103099, pr103099⟩
private theorem pr103123 : PrimeCertificate 103123 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv337]) (by decide +kernel)
def pv103123 : PrimeValue := ⟨103123, pr103123⟩
private theorem pr103141 : PrimeCertificate 103141 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv103141 : PrimeValue := ⟨103141, pr103141⟩
private theorem pr103171 : PrimeCertificate 103171 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv19,pv181]) (by decide +kernel)
def pv103171 : PrimeValue := ⟨103171, pr103171⟩
private theorem pr103177 : PrimeCertificate 103177 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv1433]) (by decide +kernel)
def pv103177 : PrimeValue := ⟨103177, pr103177⟩
private theorem pr103183 : PrimeCertificate 103183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv593]) (by decide +kernel)
def pv103183 : PrimeValue := ⟨103183, pr103183⟩
private theorem pr103217 : PrimeCertificate 103217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv6451]) (by decide +kernel)
def pv103217 : PrimeValue := ⟨103217, pr103217⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
