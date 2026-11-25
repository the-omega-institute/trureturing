/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table175
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table175.pv321631
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table013
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table055
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table056
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table057

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr321631 : PrimeCertificate 321631 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv71,pv151]) (by decide +kernel)
def pv321631 : PrimeValue := ⟨321631, pr321631⟩
private theorem pr321743 : PrimeCertificate 321743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv9463]) (by decide +kernel)
def pv321743 : PrimeValue := ⟨321743, pr321743⟩
private theorem pr321961 : PrimeCertificate 321961 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2683]) (by decide +kernel)
def pv321961 : PrimeValue := ⟨321961, pr321961⟩
private theorem pr322067 : PrimeCertificate 322067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv161033]) (by decide +kernel)
def pv322067 : PrimeValue := ⟨322067, pr322067⟩
private theorem pr322093 : PrimeCertificate 322093 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv389]) (by decide +kernel)
def pv322093 : PrimeValue := ⟨322093, pr322093⟩
private theorem pr322169 : PrimeCertificate 322169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv523]) (by decide +kernel)
def pv322169 : PrimeValue := ⟨322169, pr322169⟩
private theorem pr322243 : PrimeCertificate 322243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv43,pv1249]) (by decide +kernel)
def pv322243 : PrimeValue := ⟨322243, pr322243⟩
private theorem pr322261 : PrimeCertificate 322261 :=
  certifyPrime (q := pv61) (ls := [pv2,pv3,pv5,pv41,pv131]) (by decide +kernel)
def pv322261 : PrimeValue := ⟨322261, pr322261⟩
private theorem pr322351 : PrimeCertificate 322351 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv307]) (by decide +kernel)
def pv322351 : PrimeValue := ⟨322351, pr322351⟩
private theorem pr322463 : PrimeCertificate 322463 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv31,pv743]) (by decide +kernel)
def pv322463 : PrimeValue := ⟨322463, pr322463⟩
private theorem pr322559 : PrimeCertificate 322559 :=
  certifyPrime (q := pv29) (ls := [pv2,pv17,pv53,pv179]) (by decide +kernel)
def pv322559 : PrimeValue := ⟨322559, pr322559⟩
private theorem pr322583 : PrimeCertificate 322583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv19,pv653]) (by decide +kernel)
def pv322583 : PrimeValue := ⟨322583, pr322583⟩
private theorem pr322891 : PrimeCertificate 322891 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv47,pv229]) (by decide +kernel)
def pv322891 : PrimeValue := ⟨322891, pr322891⟩
private theorem pr323009 : PrimeCertificate 323009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv103]) (by decide +kernel)
def pv323009 : PrimeValue := ⟨323009, pr323009⟩
private theorem pr323123 : PrimeCertificate 323123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv161561]) (by decide +kernel)
def pv323123 : PrimeValue := ⟨323123, pr323123⟩
private theorem pr323273 : PrimeCertificate 323273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv2377]) (by decide +kernel)
def pv323273 : PrimeValue := ⟨323273, pr323273⟩
private theorem pr323339 : PrimeCertificate 323339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv269,pv601]) (by decide +kernel)
def pv323339 : PrimeValue := ⟨323339, pr323339⟩
private theorem pr323371 : PrimeCertificate 323371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3593]) (by decide +kernel)
def pv323371 : PrimeValue := ⟨323371, pr323371⟩
private theorem pr323419 : PrimeCertificate 323419 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv2837]) (by decide +kernel)
def pv323419 : PrimeValue := ⟨323419, pr323419⟩
private theorem pr323507 : PrimeCertificate 323507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv161753]) (by decide +kernel)
def pv323507 : PrimeValue := ⟨323507, pr323507⟩
private theorem pr323579 : PrimeCertificate 323579 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv31,pv307]) (by decide +kernel)
def pv323579 : PrimeValue := ⟨323579, pr323579⟩
private theorem pr323597 : PrimeCertificate 323597 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv127]) (by decide +kernel)
def pv323597 : PrimeValue := ⟨323597, pr323597⟩
private theorem pr323599 : PrimeCertificate 323599 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv11,pv4903]) (by decide +kernel)
def pv323599 : PrimeValue := ⟨323599, pr323599⟩
private theorem pr323711 : PrimeCertificate 323711 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv32371]) (by decide +kernel)
def pv323711 : PrimeValue := ⟨323711, pr323711⟩
private theorem pr323759 : PrimeCertificate 323759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv161879]) (by decide +kernel)
def pv323759 : PrimeValue := ⟨323759, pr323759⟩
private theorem pr323899 : PrimeCertificate 323899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1459]) (by decide +kernel)
def pv323899 : PrimeValue := ⟨323899, pr323899⟩
private theorem pr323933 : PrimeCertificate 323933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv503]) (by decide +kernel)
def pv323933 : PrimeValue := ⟨323933, pr323933⟩
private theorem pr324161 : PrimeCertificate 324161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1013]) (by decide +kernel)
def pv324161 : PrimeValue := ⟨324161, pr324161⟩
private theorem pr324179 : PrimeCertificate 324179 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv449]) (by decide +kernel)
def pv324179 : PrimeValue := ⟨324179, pr324179⟩
private theorem pr324293 : PrimeCertificate 324293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv19,pv251]) (by decide +kernel)
def pv324293 : PrimeValue := ⟨324293, pr324293⟩
private theorem pr324299 : PrimeCertificate 324299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv12473]) (by decide +kernel)
def pv324299 : PrimeValue := ⟨324299, pr324299⟩
private theorem pr324329 : PrimeCertificate 324329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv71,pv571]) (by decide +kernel)
def pv324329 : PrimeValue := ⟨324329, pr324329⟩
private theorem pr324361 : PrimeCertificate 324361 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv17,pv53]) (by decide +kernel)
def pv324361 : PrimeValue := ⟨324361, pr324361⟩
private theorem pr324437 : PrimeCertificate 324437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11587]) (by decide +kernel)
def pv324437 : PrimeValue := ⟨324437, pr324437⟩
private theorem pr324593 : PrimeCertificate 324593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20287]) (by decide +kernel)
def pv324593 : PrimeValue := ⟨324593, pr324593⟩
private theorem pr324647 : PrimeCertificate 324647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23189]) (by decide +kernel)
def pv324647 : PrimeValue := ⟨324647, pr324647⟩
private theorem pr324707 : PrimeCertificate 324707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv179,pv907]) (by decide +kernel)
def pv324707 : PrimeValue := ⟨324707, pr324707⟩
private theorem pr324931 : PrimeCertificate 324931 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv10831]) (by decide +kernel)
def pv324931 : PrimeValue := ⟨324931, pr324931⟩
private theorem pr324983 : PrimeCertificate 324983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv139,pv167]) (by decide +kernel)
def pv324983 : PrimeValue := ⟨324983, pr324983⟩
private theorem pr325019 : PrimeCertificate 325019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv1609]) (by decide +kernel)
def pv325019 : PrimeValue := ⟨325019, pr325019⟩
private theorem pr325043 : PrimeCertificate 325043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv331,pv491]) (by decide +kernel)
def pv325043 : PrimeValue := ⟨325043, pr325043⟩
private theorem pr325133 : PrimeCertificate 325133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81283]) (by decide +kernel)
def pv325133 : PrimeValue := ⟨325133, pr325133⟩
private theorem pr325319 : PrimeCertificate 325319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv19,pv1223]) (by decide +kernel)
def pv325319 : PrimeValue := ⟨325319, pr325319⟩
private theorem pr325411 : PrimeCertificate 325411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv10847]) (by decide +kernel)
def pv325411 : PrimeValue := ⟨325411, pr325411⟩
private theorem pr325439 : PrimeCertificate 325439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv31,pv181]) (by decide +kernel)
def pv325439 : PrimeValue := ⟨325439, pr325439⟩
private theorem pr325541 : PrimeCertificate 325541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv397]) (by decide +kernel)
def pv325541 : PrimeValue := ⟨325541, pr325541⟩
private theorem pr325877 : PrimeCertificate 325877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257,pv317]) (by decide +kernel)
def pv325877 : PrimeValue := ⟨325877, pr325877⟩
private theorem pr326057 : PrimeCertificate 326057 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv769]) (by decide +kernel)
def pv326057 : PrimeValue := ⟨326057, pr326057⟩
private theorem pr326063 : PrimeCertificate 326063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv14821]) (by decide +kernel)
def pv326063 : PrimeValue := ⟨326063, pr326063⟩
private theorem pr326153 : PrimeCertificate 326153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv59,pv691]) (by decide +kernel)
def pv326153 : PrimeValue := ⟨326153, pr326153⟩
private theorem pr326251 : PrimeCertificate 326251 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv326251 : PrimeValue := ⟨326251, pr326251⟩
private theorem pr326549 : PrimeCertificate 326549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv81637]) (by decide +kernel)
def pv326549 : PrimeValue := ⟨326549, pr326549⟩
private theorem pr326693 : PrimeCertificate 326693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv53,pv67]) (by decide +kernel)
def pv326693 : PrimeValue := ⟨326693, pr326693⟩
private theorem pr326863 : PrimeCertificate 326863 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6053]) (by decide +kernel)
def pv326863 : PrimeValue := ⟨326863, pr326863⟩
private theorem pr326993 : PrimeCertificate 326993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv107,pv191]) (by decide +kernel)
def pv326993 : PrimeValue := ⟨326993, pr326993⟩
private theorem pr327071 : PrimeCertificate 327071 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv32707]) (by decide +kernel)
def pv327071 : PrimeValue := ⟨327071, pr327071⟩
private theorem pr327251 : PrimeCertificate 327251 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv11,pv17]) (by decide +kernel)
def pv327251 : PrimeValue := ⟨327251, pr327251⟩
private theorem pr327347 : PrimeCertificate 327347 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163673]) (by decide +kernel)
def pv327347 : PrimeValue := ⟨327347, pr327347⟩
private theorem pr327421 : PrimeCertificate 327421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv107]) (by decide +kernel)
def pv327421 : PrimeValue := ⟨327421, pr327421⟩
private theorem pr327463 : PrimeCertificate 327463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv54577]) (by decide +kernel)
def pv327463 : PrimeValue := ⟨327463, pr327463⟩
private theorem pr327493 : PrimeCertificate 327493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv827]) (by decide +kernel)
def pv327493 : PrimeValue := ⟨327493, pr327493⟩
private theorem pr327553 : PrimeCertificate 327553 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv853]) (by decide +kernel)
def pv327553 : PrimeValue := ⟨327553, pr327553⟩
private theorem pr327559 : PrimeCertificate 327559 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv709]) (by decide +kernel)
def pv327559 : PrimeValue := ⟨327559, pr327559⟩
private theorem pr327581 : PrimeCertificate 327581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1489]) (by decide +kernel)
def pv327581 : PrimeValue := ⟨327581, pr327581⟩
private theorem pr327739 : PrimeCertificate 327739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv54623]) (by decide +kernel)
def pv327739 : PrimeValue := ⟨327739, pr327739⟩
private theorem pr327871 : PrimeCertificate 327871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3643]) (by decide +kernel)
def pv327871 : PrimeValue := ⟨327871, pr327871⟩
private theorem pr327889 : PrimeCertificate 327889 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv327889 : PrimeValue := ⟨327889, pr327889⟩
private theorem pr327983 : PrimeCertificate 327983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv163991]) (by decide +kernel)
def pv327983 : PrimeValue := ⟨327983, pr327983⟩
private theorem pr328037 : PrimeCertificate 328037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv82009]) (by decide +kernel)
def pv328037 : PrimeValue := ⟨328037, pr328037⟩
private theorem pr328061 : PrimeCertificate 328061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv349]) (by decide +kernel)
def pv328061 : PrimeValue := ⟨328061, pr328061⟩
private theorem pr328109 : PrimeCertificate 328109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv7457]) (by decide +kernel)
def pv328109 : PrimeValue := ⟨328109, pr328109⟩
private theorem pr328277 : PrimeCertificate 328277 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv59,pv107]) (by decide +kernel)
def pv328277 : PrimeValue := ⟨328277, pr328277⟩
private theorem pr328333 : PrimeCertificate 328333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27361]) (by decide +kernel)
def pv328333 : PrimeValue := ⟨328333, pr328333⟩
private theorem pr328421 : PrimeCertificate 328421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv16421]) (by decide +kernel)
def pv328421 : PrimeValue := ⟨328421, pr328421⟩
private theorem pr328439 : PrimeCertificate 328439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv14929]) (by decide +kernel)
def pv328439 : PrimeValue := ⟨328439, pr328439⟩
private theorem pr328709 : PrimeCertificate 328709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv2221]) (by decide +kernel)
def pv328709 : PrimeValue := ⟨328709, pr328709⟩
private theorem pr329009 : PrimeCertificate 329009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv20563]) (by decide +kernel)
def pv329009 : PrimeValue := ⟨329009, pr329009⟩
private theorem pr329089 : PrimeCertificate 329089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv857]) (by decide +kernel)
def pv329089 : PrimeValue := ⟨329089, pr329089⟩
private theorem pr329101 : PrimeCertificate 329101 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv1097]) (by decide +kernel)
def pv329101 : PrimeValue := ⟨329101, pr329101⟩
private theorem pr329111 : PrimeCertificate 329111 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv32911]) (by decide +kernel)
def pv329111 : PrimeValue := ⟨329111, pr329111⟩
private theorem pr329209 : PrimeCertificate 329209 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv11,pv29,pv43]) (by decide +kernel)
def pv329209 : PrimeValue := ⟨329209, pr329209⟩
private theorem pr329401 : PrimeCertificate 329401 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv329401 : PrimeValue := ⟨329401, pr329401⟩
private theorem pr329533 : PrimeCertificate 329533 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv3923]) (by decide +kernel)
def pv329533 : PrimeValue := ⟨329533, pr329533⟩
private theorem pr329717 : PrimeCertificate 329717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv2659]) (by decide +kernel)
def pv329717 : PrimeValue := ⟨329717, pr329717⟩
private theorem pr329723 : PrimeCertificate 329723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv4021]) (by decide +kernel)
def pv329723 : PrimeValue := ⟨329723, pr329723⟩
private theorem pr329729 : PrimeCertificate 329729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv23]) (by decide +kernel)
def pv329729 : PrimeValue := ⟨329729, pr329729⟩
private theorem pr329803 : PrimeCertificate 329803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv19,pv263]) (by decide +kernel)
def pv329803 : PrimeValue := ⟨329803, pr329803⟩
private theorem pr329867 : PrimeCertificate 329867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv71,pv101]) (by decide +kernel)
def pv329867 : PrimeValue := ⟨329867, pr329867⟩
private theorem pr329873 : PrimeCertificate 329873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv53,pv389]) (by decide +kernel)
def pv329873 : PrimeValue := ⟨329873, pr329873⟩
private theorem pr329899 : PrimeCertificate 329899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv54983]) (by decide +kernel)
def pv329899 : PrimeValue := ⟨329899, pr329899⟩
private theorem pr329957 : PrimeCertificate 329957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv7499]) (by decide +kernel)
def pv329957 : PrimeValue := ⟨329957, pr329957⟩
private theorem pr330203 : PrimeCertificate 330203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv1543]) (by decide +kernel)
def pv330203 : PrimeValue := ⟨330203, pr330203⟩
private theorem pr330287 : PrimeCertificate 330287 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv15013]) (by decide +kernel)
def pv330287 : PrimeValue := ⟨330287, pr330287⟩
private theorem pr330469 : PrimeCertificate 330469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv27539]) (by decide +kernel)
def pv330469 : PrimeValue := ⟨330469, pr330469⟩
private theorem pr330653 : PrimeCertificate 330653 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv241]) (by decide +kernel)
def pv330653 : PrimeValue := ⟨330653, pr330653⟩
private theorem pr330683 : PrimeCertificate 330683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv15031]) (by decide +kernel)
def pv330683 : PrimeValue := ⟨330683, pr330683⟩
private theorem pr330821 : PrimeCertificate 330821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv139]) (by decide +kernel)
def pv330821 : PrimeValue := ⟨330821, pr330821⟩
private theorem pr330857 : PrimeCertificate 330857 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41357]) (by decide +kernel)
def pv330857 : PrimeValue := ⟨330857, pr330857⟩
private theorem pr330983 : PrimeCertificate 330983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv2267]) (by decide +kernel)
def pv330983 : PrimeValue := ⟨330983, pr330983⟩
private theorem pr331043 : PrimeCertificate 331043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv1607]) (by decide +kernel)
def pv331043 : PrimeValue := ⟨331043, pr331043⟩
private theorem pr331063 : PrimeCertificate 331063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv2399]) (by decide +kernel)
def pv331063 : PrimeValue := ⟨331063, pr331063⟩
private theorem pr331081 : PrimeCertificate 331081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv31,pv89]) (by decide +kernel)
def pv331081 : PrimeValue := ⟨331081, pr331081⟩
private theorem pr331127 : PrimeCertificate 331127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv9739]) (by decide +kernel)
def pv331127 : PrimeValue := ⟨331127, pr331127⟩
private theorem pr331171 : PrimeCertificate 331171 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv19,pv83]) (by decide +kernel)
def pv331171 : PrimeValue := ⟨331171, pr331171⟩
private theorem pr331367 : PrimeCertificate 331367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23669]) (by decide +kernel)
def pv331367 : PrimeValue := ⟨331367, pr331367⟩
private theorem pr331519 : PrimeCertificate 331519 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv5023]) (by decide +kernel)
def pv331519 : PrimeValue := ⟨331519, pr331519⟩
private theorem pr331883 : PrimeCertificate 331883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv165941]) (by decide +kernel)
def pv331883 : PrimeValue := ⟨331883, pr331883⟩
private theorem pr331999 : PrimeCertificate 331999 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv55333]) (by decide +kernel)
def pv331999 : PrimeValue := ⟨331999, pr331999⟩
private theorem pr332011 : PrimeCertificate 332011 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv17,pv31]) (by decide +kernel)
def pv332011 : PrimeValue := ⟨332011, pr332011⟩
private theorem pr332393 : PrimeCertificate 332393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41549]) (by decide +kernel)
def pv332393 : PrimeValue := ⟨332393, pr332393⟩
private theorem pr332513 : PrimeCertificate 332513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv10391]) (by decide +kernel)
def pv332513 : PrimeValue := ⟨332513, pr332513⟩
private theorem pr332641 : PrimeCertificate 332641 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv332641 : PrimeValue := ⟨332641, pr332641⟩
private theorem pr332699 : PrimeCertificate 332699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv166349]) (by decide +kernel)
def pv332699 : PrimeValue := ⟨332699, pr332699⟩
private theorem pr332851 : PrimeCertificate 332851 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv317]) (by decide +kernel)
def pv332851 : PrimeValue := ⟨332851, pr332851⟩
private theorem pr333023 : PrimeCertificate 333023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv269,pv619]) (by decide +kernel)
def pv333023 : PrimeValue := ⟨333023, pr333023⟩
private theorem pr333049 : PrimeCertificate 333049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13877]) (by decide +kernel)
def pv333049 : PrimeValue := ⟨333049, pr333049⟩
private theorem pr333161 : PrimeCertificate 333161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv8329]) (by decide +kernel)
def pv333161 : PrimeValue := ⟨333161, pr333161⟩
private theorem pr333209 : PrimeCertificate 333209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41651]) (by decide +kernel)
def pv333209 : PrimeValue := ⟨333209, pr333209⟩
private theorem pr333269 : PrimeCertificate 333269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv29]) (by decide +kernel)
def pv333269 : PrimeValue := ⟨333269, pr333269⟩
private theorem pr333349 : PrimeCertificate 333349 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv27779]) (by decide +kernel)
def pv333349 : PrimeValue := ⟨333349, pr333349⟩
private theorem pr333383 : PrimeCertificate 333383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23813]) (by decide +kernel)
def pv333383 : PrimeValue := ⟨333383, pr333383⟩
private theorem pr333419 : PrimeCertificate 333419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv3547]) (by decide +kernel)
def pv333419 : PrimeValue := ⟨333419, pr333419⟩
private theorem pr333439 : PrimeCertificate 333439 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv467]) (by decide +kernel)
def pv333439 : PrimeValue := ⟨333439, pr333439⟩
private theorem pr333691 : PrimeCertificate 333691 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv7,pv227]) (by decide +kernel)
def pv333691 : PrimeValue := ⟨333691, pr333691⟩
private theorem pr333769 : PrimeCertificate 333769 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv13907]) (by decide +kernel)
def pv333769 : PrimeValue := ⟨333769, pr333769⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
