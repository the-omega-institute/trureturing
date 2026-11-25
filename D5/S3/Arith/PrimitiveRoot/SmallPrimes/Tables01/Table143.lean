/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table143
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table143.pv1201643
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table044
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table045
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table119
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table120

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1201643 : PrimeCertificate 1201643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv113,pv409]) (by decide +kernel)
def pv1201643 : PrimeValue := ⟨1201643, pr1201643⟩
private theorem pr1201691 : PrimeCertificate 1201691 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv7,pv17167]) (by decide +kernel)
def pv1201691 : PrimeValue := ⟨1201691, pr1201691⟩
private theorem pr1201703 : PrimeCertificate 1201703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv29,pv20719]) (by decide +kernel)
def pv1201703 : PrimeValue := ⟨1201703, pr1201703⟩
private theorem pr1201709 : PrimeCertificate 1201709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv300427]) (by decide +kernel)
def pv1201709 : PrimeValue := ⟨1201709, pr1201709⟩
private theorem pr1201793 : PrimeCertificate 1201793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv229]) (by decide +kernel)
def pv1201793 : PrimeValue := ⟨1201793, pr1201793⟩
private theorem pr1201829 : PrimeCertificate 1201829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv5669]) (by decide +kernel)
def pv1201829 : PrimeValue := ⟨1201829, pr1201829⟩
private theorem pr1202321 : PrimeCertificate 1202321 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv113]) (by decide +kernel)
def pv1202321 : PrimeValue := ⟨1202321, pr1202321⟩
private theorem pr1202423 : PrimeCertificate 1202423 :=
  certifyPrime (q := pv23) (ls := [pv2,pv13,pv103,pv449]) (by decide +kernel)
def pv1202423 : PrimeValue := ⟨1202423, pr1202423⟩
private theorem pr1202429 : PrimeCertificate 1202429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv9697]) (by decide +kernel)
def pv1202429 : PrimeValue := ⟨1202429, pr1202429⟩
private theorem pr1202501 : PrimeCertificate 1202501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv37]) (by decide +kernel)
def pv1202501 : PrimeValue := ⟨1202501, pr1202501⟩
private theorem pr1203731 : PrimeCertificate 1203731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv31,pv353]) (by decide +kernel)
def pv1203731 : PrimeValue := ⟨1203731, pr1203731⟩
private theorem pr1203791 : PrimeCertificate 1203791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv29,pv593]) (by decide +kernel)
def pv1203791 : PrimeValue := ⟨1203791, pr1203791⟩
private theorem pr1203899 : PrimeCertificate 1203899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv601949]) (by decide +kernel)
def pv1203899 : PrimeValue := ⟨1203899, pr1203899⟩
private theorem pr1203941 : PrimeCertificate 1203941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv3541]) (by decide +kernel)
def pv1203941 : PrimeValue := ⟨1203941, pr1203941⟩
private theorem pr1203971 : PrimeCertificate 1203971 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv120397]) (by decide +kernel)
def pv1203971 : PrimeValue := ⟨1203971, pr1203971⟩
private theorem pr1204019 : PrimeCertificate 1204019 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv71,pv139]) (by decide +kernel)
def pv1204019 : PrimeValue := ⟨1204019, pr1204019⟩
private theorem pr1204139 : PrimeCertificate 1204139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv29,pv1597]) (by decide +kernel)
def pv1204139 : PrimeValue := ⟨1204139, pr1204139⟩
private theorem pr1204421 : PrimeCertificate 1204421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1229]) (by decide +kernel)
def pv1204421 : PrimeValue := ⟨1204421, pr1204421⟩
private theorem pr1204583 : PrimeCertificate 1204583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv269,pv2239]) (by decide +kernel)
def pv1204583 : PrimeValue := ⟨1204583, pr1204583⟩
private theorem pr1204649 : PrimeCertificate 1204649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv6547]) (by decide +kernel)
def pv1204649 : PrimeValue := ⟨1204649, pr1204649⟩
private theorem pr1205471 : PrimeCertificate 1205471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv1013]) (by decide +kernel)
def pv1205471 : PrimeValue := ⟨1205471, pr1205471⟩
private theorem pr1205513 : PrimeCertificate 1205513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv19,pv103]) (by decide +kernel)
def pv1205513 : PrimeValue := ⟨1205513, pr1205513⟩
private theorem pr1205609 : PrimeCertificate 1205609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv4073]) (by decide +kernel)
def pv1205609 : PrimeValue := ⟨1205609, pr1205609⟩
private theorem pr1205819 : PrimeCertificate 1205819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv602909]) (by decide +kernel)
def pv1205819 : PrimeValue := ⟨1205819, pr1205819⟩
private theorem pr1206059 : PrimeCertificate 1206059 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv277,pv311]) (by decide +kernel)
def pv1206059 : PrimeValue := ⟨1206059, pr1206059⟩
private theorem pr1206071 : PrimeCertificate 1206071 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv120607]) (by decide +kernel)
def pv1206071 : PrimeValue := ⟨1206071, pr1206071⟩
private theorem pr1206323 : PrimeCertificate 1206323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43,pv83]) (by decide +kernel)
def pv1206323 : PrimeValue := ⟨1206323, pr1206323⟩
private theorem pr1206449 : PrimeCertificate 1206449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv75403]) (by decide +kernel)
def pv1206449 : PrimeValue := ⟨1206449, pr1206449⟩
private theorem pr1206479 : PrimeCertificate 1206479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv947]) (by decide +kernel)
def pv1206479 : PrimeValue := ⟨1206479, pr1206479⟩
private theorem pr1206581 : PrimeCertificate 1206581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv43,pv61]) (by decide +kernel)
def pv1206581 : PrimeValue := ⟨1206581, pr1206581⟩
private theorem pr1206713 : PrimeCertificate 1206713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv41,pv283]) (by decide +kernel)
def pv1206713 : PrimeValue := ⟨1206713, pr1206713⟩
private theorem pr1206869 : PrimeCertificate 1206869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23209]) (by decide +kernel)
def pv1206869 : PrimeValue := ⟨1206869, pr1206869⟩
private theorem pr1206941 : PrimeCertificate 1206941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv37,pv233]) (by decide +kernel)
def pv1206941 : PrimeValue := ⟨1206941, pr1206941⟩
private theorem pr1207721 : PrimeCertificate 1207721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv109,pv277]) (by decide +kernel)
def pv1207721 : PrimeValue := ⟨1207721, pr1207721⟩
private theorem pr1207751 : PrimeCertificate 1207751 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv4831]) (by decide +kernel)
def pv1207751 : PrimeValue := ⟨1207751, pr1207751⟩
private theorem pr1207919 : PrimeCertificate 1207919 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv35527]) (by decide +kernel)
def pv1207919 : PrimeValue := ⟨1207919, pr1207919⟩
private theorem pr1208033 : PrimeCertificate 1208033 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv5393]) (by decide +kernel)
def pv1208033 : PrimeValue := ⟨1208033, pr1208033⟩
private theorem pr1208243 : PrimeCertificate 1208243 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv12329]) (by decide +kernel)
def pv1208243 : PrimeValue := ⟨1208243, pr1208243⟩
private theorem pr1208303 : PrimeCertificate 1208303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv151,pv4001]) (by decide +kernel)
def pv1208303 : PrimeValue := ⟨1208303, pr1208303⟩
private theorem pr1208873 : PrimeCertificate 1208873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv21587]) (by decide +kernel)
def pv1208873 : PrimeValue := ⟨1208873, pr1208873⟩
private theorem pr1209563 : PrimeCertificate 1209563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv604781]) (by decide +kernel)
def pv1209563 : PrimeValue := ⟨1209563, pr1209563⟩
private theorem pr1209629 : PrimeCertificate 1209629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv43201]) (by decide +kernel)
def pv1209629 : PrimeValue := ⟨1209629, pr1209629⟩
private theorem pr1209671 : PrimeCertificate 1209671 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv11,pv1571]) (by decide +kernel)
def pv1209671 : PrimeValue := ⟨1209671, pr1209671⟩
private theorem pr1209809 : PrimeCertificate 1209809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv83,pv911]) (by decide +kernel)
def pv1209809 : PrimeValue := ⟨1209809, pr1209809⟩
private theorem pr1209959 : PrimeCertificate 1209959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv19,pv1873]) (by decide +kernel)
def pv1209959 : PrimeValue := ⟨1209959, pr1209959⟩
private theorem pr1210169 : PrimeCertificate 1210169 :=
  certifyPrime (q := pv17) (ls := [pv2,pv23,pv6577]) (by decide +kernel)
def pv1210169 : PrimeValue := ⟨1210169, pr1210169⟩
private theorem pr1210211 : PrimeCertificate 1210211 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv121021]) (by decide +kernel)
def pv1210211 : PrimeValue := ⟨1210211, pr1210211⟩
private theorem pr1210229 : PrimeCertificate 1210229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv10433]) (by decide +kernel)
def pv1210229 : PrimeValue := ⟨1210229, pr1210229⟩
private theorem pr1210259 : PrimeCertificate 1210259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv137,pv631]) (by decide +kernel)
def pv1210259 : PrimeValue := ⟨1210259, pr1210259⟩
private theorem pr1210403 : PrimeCertificate 1210403 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv41,pv509]) (by decide +kernel)
def pv1210403 : PrimeValue := ⟨1210403, pr1210403⟩
private theorem pr1210439 : PrimeCertificate 1210439 :=
  certifyPrime (q := pv17) (ls := [pv2,pv47,pv79,pv163]) (by decide +kernel)
def pv1210439 : PrimeValue := ⟨1210439, pr1210439⟩
private theorem pr1210523 : PrimeCertificate 1210523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv605261]) (by decide +kernel)
def pv1210523 : PrimeValue := ⟨1210523, pr1210523⟩
private theorem pr1210871 : PrimeCertificate 1210871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv19,pv6373]) (by decide +kernel)
def pv1210871 : PrimeValue := ⟨1210871, pr1210871⟩
private theorem pr1210883 : PrimeCertificate 1210883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv3137]) (by decide +kernel)
def pv1210883 : PrimeValue := ⟨1210883, pr1210883⟩
private theorem pr1211261 : PrimeCertificate 1211261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv71,pv853]) (by decide +kernel)
def pv1211261 : PrimeValue := ⟨1211261, pr1211261⟩
private theorem pr1211279 : PrimeCertificate 1211279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv605639]) (by decide +kernel)
def pv1211279 : PrimeValue := ⟨1211279, pr1211279⟩
private theorem pr1211543 : PrimeCertificate 1211543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv19541]) (by decide +kernel)
def pv1211543 : PrimeValue := ⟨1211543, pr1211543⟩
private theorem pr1211669 : PrimeCertificate 1211669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv107,pv149]) (by decide +kernel)
def pv1211669 : PrimeValue := ⟨1211669, pr1211669⟩
private theorem pr1211813 : PrimeCertificate 1211813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv113,pv383]) (by decide +kernel)
def pv1211813 : PrimeValue := ⟨1211813, pr1211813⟩
private theorem pr1211999 : PrimeCertificate 1211999 :=
  certifyPrime (q := pv29) (ls := [pv2,pv17,pv43,pv829]) (by decide +kernel)
def pv1211999 : PrimeValue := ⟨1211999, pr1211999⟩
private theorem pr1212443 : PrimeCertificate 1212443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv7873]) (by decide +kernel)
def pv1212443 : PrimeValue := ⟨1212443, pr1212443⟩
private theorem pr1212521 : PrimeCertificate 1212521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv30313]) (by decide +kernel)
def pv1212521 : PrimeValue := ⟨1212521, pr1212521⟩
private theorem pr1212569 : PrimeCertificate 1212569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv59,pv367]) (by decide +kernel)
def pv1212569 : PrimeValue := ⟨1212569, pr1212569⟩
private theorem pr1213109 : PrimeCertificate 1213109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41,pv569]) (by decide +kernel)
def pv1213109 : PrimeValue := ⟨1213109, pr1213109⟩
private theorem pr1213133 : PrimeCertificate 1213133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv303283]) (by decide +kernel)
def pv1213133 : PrimeValue := ⟨1213133, pr1213133⟩
private theorem pr1213301 : PrimeCertificate 1213301 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1103]) (by decide +kernel)
def pv1213301 : PrimeValue := ⟨1213301, pr1213301⟩
private theorem pr1213529 : PrimeCertificate 1213529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv8923]) (by decide +kernel)
def pv1213529 : PrimeValue := ⟨1213529, pr1213529⟩
private theorem pr1213631 : PrimeCertificate 1213631 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv17,pv59]) (by decide +kernel)
def pv1213631 : PrimeValue := ⟨1213631, pr1213631⟩
private theorem pr1213643 : PrimeCertificate 1213643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv239,pv2539]) (by decide +kernel)
def pv1213643 : PrimeValue := ⟨1213643, pr1213643⟩
private theorem pr1213763 : PrimeCertificate 1213763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv55171]) (by decide +kernel)
def pv1213763 : PrimeValue := ⟨1213763, pr1213763⟩
private theorem pr1213841 : PrimeCertificate 1213841 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15173]) (by decide +kernel)
def pv1213841 : PrimeValue := ⟨1213841, pr1213841⟩
private theorem pr1213931 : PrimeCertificate 1213931 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv233,pv521]) (by decide +kernel)
def pv1213931 : PrimeValue := ⟨1213931, pr1213931⟩
private theorem pr1214039 : PrimeCertificate 1214039 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv17,pv5101]) (by decide +kernel)
def pv1214039 : PrimeValue := ⟨1214039, pr1214039⟩
private theorem pr1214189 : PrimeCertificate 1214189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv303547]) (by decide +kernel)
def pv1214189 : PrimeValue := ⟨1214189, pr1214189⟩
private theorem pr1214333 : PrimeCertificate 1214333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv1399]) (by decide +kernel)
def pv1214333 : PrimeValue := ⟨1214333, pr1214333⟩
private theorem pr1214393 : PrimeCertificate 1214393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv151799]) (by decide +kernel)
def pv1214393 : PrimeValue := ⟨1214393, pr1214393⟩
private theorem pr1214441 : PrimeCertificate 1214441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv97,pv313]) (by decide +kernel)
def pv1214441 : PrimeValue := ⟨1214441, pr1214441⟩
private theorem pr1214459 : PrimeCertificate 1214459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv223,pv389]) (by decide +kernel)
def pv1214459 : PrimeValue := ⟨1214459, pr1214459⟩
private theorem pr1214639 : PrimeCertificate 1214639 :=
  certifyPrime (q := pv17) (ls := [pv2,pv607319]) (by decide +kernel)
def pv1214639 : PrimeValue := ⟨1214639, pr1214639⟩
private theorem pr1214729 : PrimeCertificate 1214729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv151841]) (by decide +kernel)
def pv1214729 : PrimeValue := ⟨1214729, pr1214729⟩
private theorem pr1215569 : PrimeCertificate 1215569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv41,pv109]) (by decide +kernel)
def pv1215569 : PrimeValue := ⟨1215569, pr1215569⟩
private theorem pr1215719 : PrimeCertificate 1215719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv86837]) (by decide +kernel)
def pv1215719 : PrimeValue := ⟨1215719, pr1215719⟩
private theorem pr1215881 : PrimeCertificate 1215881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv113,pv269]) (by decide +kernel)
def pv1215881 : PrimeValue := ⟨1215881, pr1215881⟩
private theorem pr1216109 : PrimeCertificate 1216109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv5153]) (by decide +kernel)
def pv1216109 : PrimeValue := ⟨1216109, pr1216109⟩
private theorem pr1216529 : PrimeCertificate 1216529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv139,pv547]) (by decide +kernel)
def pv1216529 : PrimeValue := ⟨1216529, pr1216529⟩
private theorem pr1216601 : PrimeCertificate 1216601 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv7,pv11,pv79]) (by decide +kernel)
def pv1216601 : PrimeValue := ⟨1216601, pr1216601⟩
private theorem pr1216751 : PrimeCertificate 1216751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv31,pv157]) (by decide +kernel)
def pv1216751 : PrimeValue := ⟨1216751, pr1216751⟩
private theorem pr1217063 : PrimeCertificate 1217063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv1129]) (by decide +kernel)
def pv1217063 : PrimeValue := ⟨1217063, pr1217063⟩
private theorem pr1217393 : PrimeCertificate 1217393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv6917]) (by decide +kernel)
def pv1217393 : PrimeValue := ⟨1217393, pr1217393⟩
private theorem pr1217399 : PrimeCertificate 1217399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv6689]) (by decide +kernel)
def pv1217399 : PrimeValue := ⟨1217399, pr1217399⟩
private theorem pr1217483 : PrimeCertificate 1217483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv23,pv199]) (by decide +kernel)
def pv1217483 : PrimeValue := ⟨1217483, pr1217483⟩
private theorem pr1217663 : PrimeCertificate 1217663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv608831]) (by decide +kernel)
def pv1217663 : PrimeValue := ⟨1217663, pr1217663⟩
private theorem pr1217669 : PrimeCertificate 1217669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv304417]) (by decide +kernel)
def pv1217669 : PrimeValue := ⟨1217669, pr1217669⟩
private theorem pr1217759 : PrimeCertificate 1217759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv1151]) (by decide +kernel)
def pv1217759 : PrimeValue := ⟨1217759, pr1217759⟩
private theorem pr1217813 : PrimeCertificate 1217813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv17909]) (by decide +kernel)
def pv1217813 : PrimeValue := ⟨1217813, pr1217813⟩
private theorem pr1218209 : PrimeCertificate 1218209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv38069]) (by decide +kernel)
def pv1218209 : PrimeValue := ⟨1218209, pr1218209⟩
private theorem pr1218281 : PrimeCertificate 1218281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv229]) (by decide +kernel)
def pv1218281 : PrimeValue := ⟨1218281, pr1218281⟩
private theorem pr1218779 : PrimeCertificate 1218779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv55399]) (by decide +kernel)
def pv1218779 : PrimeValue := ⟨1218779, pr1218779⟩
private theorem pr1218923 : PrimeCertificate 1218923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv609461]) (by decide +kernel)
def pv1218923 : PrimeValue := ⟨1218923, pr1218923⟩
private theorem pr1219301 : PrimeCertificate 1219301 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv89,pv137]) (by decide +kernel)
def pv1219301 : PrimeValue := ⟨1219301, pr1219301⟩
private theorem pr1219313 : PrimeCertificate 1219313 :=
  certifyPrime (q := pv3) (ls := [pv2,pv76207]) (by decide +kernel)
def pv1219313 : PrimeValue := ⟨1219313, pr1219313⟩
private theorem pr1219703 : PrimeCertificate 1219703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv55441]) (by decide +kernel)
def pv1219703 : PrimeValue := ⟨1219703, pr1219703⟩
private theorem pr1219721 : PrimeCertificate 1219721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv30493]) (by decide +kernel)
def pv1219721 : PrimeValue := ⟨1219721, pr1219721⟩
private theorem pr1219763 : PrimeCertificate 1219763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv32099]) (by decide +kernel)
def pv1219763 : PrimeValue := ⟨1219763, pr1219763⟩
private theorem pr1219859 : PrimeCertificate 1219859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv609929]) (by decide +kernel)
def pv1219859 : PrimeValue := ⟨1219859, pr1219859⟩
private theorem pr1219919 : PrimeCertificate 1219919 :=
  certifyPrime (q := pv19) (ls := [pv2,pv7,pv79,pv1103]) (by decide +kernel)
def pv1219919 : PrimeValue := ⟨1219919, pr1219919⟩
private theorem pr1220249 : PrimeCertificate 1220249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv152531]) (by decide +kernel)
def pv1220249 : PrimeValue := ⟨1220249, pr1220249⟩
private theorem pr1220333 : PrimeCertificate 1220333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv16057]) (by decide +kernel)
def pv1220333 : PrimeValue := ⟨1220333, pr1220333⟩
private theorem pr1220393 : PrimeCertificate 1220393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv1931]) (by decide +kernel)
def pv1220393 : PrimeValue := ⟨1220393, pr1220393⟩
private theorem pr1220729 : PrimeCertificate 1220729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv331,pv461]) (by decide +kernel)
def pv1220729 : PrimeValue := ⟨1220729, pr1220729⟩
private theorem pr1220819 : PrimeCertificate 1220819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv610409]) (by decide +kernel)
def pv1220819 : PrimeValue := ⟨1220819, pr1220819⟩
private theorem pr1220903 : PrimeCertificate 1220903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv89]) (by decide +kernel)
def pv1220903 : PrimeValue := ⟨1220903, pr1220903⟩
private theorem pr1220993 : PrimeCertificate 1220993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9539]) (by decide +kernel)
def pv1220993 : PrimeValue := ⟨1220993, pr1220993⟩
private theorem pr1221029 : PrimeCertificate 1221029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv43,pv229]) (by decide +kernel)
def pv1221029 : PrimeValue := ⟨1221029, pr1221029⟩
private theorem pr1221089 : PrimeCertificate 1221089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv3469]) (by decide +kernel)
def pv1221089 : PrimeValue := ⟨1221089, pr1221089⟩
private theorem pr1221113 : PrimeCertificate 1221113 :=
  certifyPrime (q := pv3) (ls := [pv2,pv152639]) (by decide +kernel)
def pv1221113 : PrimeValue := ⟨1221113, pr1221113⟩
private theorem pr1221131 : PrimeCertificate 1221131 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv6427]) (by decide +kernel)
def pv1221131 : PrimeValue := ⟨1221131, pr1221131⟩
private theorem pr1221299 : PrimeCertificate 1221299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv107,pv439]) (by decide +kernel)
def pv1221299 : PrimeValue := ⟨1221299, pr1221299⟩
private theorem pr1221383 : PrimeCertificate 1221383 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv35923]) (by decide +kernel)
def pv1221383 : PrimeValue := ⟨1221383, pr1221383⟩
private theorem pr1221641 : PrimeCertificate 1221641 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv4363]) (by decide +kernel)
def pv1221641 : PrimeValue := ⟨1221641, pr1221641⟩
private theorem pr1221791 : PrimeCertificate 1221791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17,pv7187]) (by decide +kernel)
def pv1221791 : PrimeValue := ⟨1221791, pr1221791⟩
private theorem pr1221821 : PrimeCertificate 1221821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61091]) (by decide +kernel)
def pv1221821 : PrimeValue := ⟨1221821, pr1221821⟩
private theorem pr1222433 : PrimeCertificate 1222433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv38201]) (by decide +kernel)
def pv1222433 : PrimeValue := ⟨1222433, pr1222433⟩
private theorem pr1222601 : PrimeCertificate 1222601 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv6113]) (by decide +kernel)
def pv1222601 : PrimeValue := ⟨1222601, pr1222601⟩
private theorem pr1222913 : PrimeCertificate 1222913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv281]) (by decide +kernel)
def pv1222913 : PrimeValue := ⟨1222913, pr1222913⟩
private theorem pr1222943 : PrimeCertificate 1222943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv12479]) (by decide +kernel)
def pv1222943 : PrimeValue := ⟨1222943, pr1222943⟩
private theorem pr1223021 : PrimeCertificate 1223021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61151]) (by decide +kernel)
def pv1223021 : PrimeValue := ⟨1223021, pr1223021⟩
private theorem pr1223231 : PrimeCertificate 1223231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv122323]) (by decide +kernel)
def pv1223231 : PrimeValue := ⟨1223231, pr1223231⟩
private theorem pr1223459 : PrimeCertificate 1223459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv611729]) (by decide +kernel)
def pv1223459 : PrimeValue := ⟨1223459, pr1223459⟩
private theorem pr1223633 : PrimeCertificate 1223633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv2467]) (by decide +kernel)
def pv1223633 : PrimeValue := ⟨1223633, pr1223633⟩
private theorem pr1223879 : PrimeCertificate 1223879 :=
  certifyPrime (q := pv13) (ls := [pv2,pv611939]) (by decide +kernel)
def pv1223879 : PrimeValue := ⟨1223879, pr1223879⟩
private theorem pr1223921 : PrimeCertificate 1223921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv15299]) (by decide +kernel)
def pv1223921 : PrimeValue := ⟨1223921, pr1223921⟩
private theorem pr1224053 : PrimeCertificate 1224053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv103,pv2971]) (by decide +kernel)
def pv1224053 : PrimeValue := ⟨1224053, pr1224053⟩
private theorem pr1224131 : PrimeCertificate 1224131 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv163,pv751]) (by decide +kernel)
def pv1224131 : PrimeValue := ⟨1224131, pr1224131⟩
private theorem pr1224269 : PrimeCertificate 1224269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv421,pv727]) (by decide +kernel)
def pv1224269 : PrimeValue := ⟨1224269, pr1224269⟩
private theorem pr1224413 : PrimeCertificate 1224413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv6247]) (by decide +kernel)
def pv1224413 : PrimeValue := ⟨1224413, pr1224413⟩
private theorem pr1224599 : PrimeCertificate 1224599 :=
  certifyPrime (q := pv19) (ls := [pv2,pv281,pv2179]) (by decide +kernel)
def pv1224599 : PrimeValue := ⟨1224599, pr1224599⟩
private theorem pr1224809 : PrimeCertificate 1224809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv11777]) (by decide +kernel)
def pv1224809 : PrimeValue := ⟨1224809, pr1224809⟩
private theorem pr1224893 : PrimeCertificate 1224893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv71,pv227]) (by decide +kernel)
def pv1224893 : PrimeValue := ⟨1224893, pr1224893⟩
private theorem pr1224953 : PrimeCertificate 1224953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv9007]) (by decide +kernel)
def pv1224953 : PrimeValue := ⟨1224953, pr1224953⟩
private theorem pr1225109 : PrimeCertificate 1225109 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv1879]) (by decide +kernel)
def pv1225109 : PrimeValue := ⟨1225109, pr1225109⟩
private theorem pr1225331 : PrimeCertificate 1225331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv122533]) (by decide +kernel)
def pv1225331 : PrimeValue := ⟨1225331, pr1225331⟩
private theorem pr1225571 : PrimeCertificate 1225571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv122557]) (by decide +kernel)
def pv1225571 : PrimeValue := ⟨1225571, pr1225571⟩
private theorem pr1225769 : PrimeCertificate 1225769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv9013]) (by decide +kernel)
def pv1225769 : PrimeValue := ⟨1225769, pr1225769⟩
private theorem pr1225883 : PrimeCertificate 1225883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1787]) (by decide +kernel)
def pv1225883 : PrimeValue := ⟨1225883, pr1225883⟩
private theorem pr1226111 : PrimeCertificate 1226111 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv122611]) (by decide +kernel)
def pv1226111 : PrimeValue := ⟨1226111, pr1226111⟩
private theorem pr1226213 : PrimeCertificate 1226213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23581]) (by decide +kernel)
def pv1226213 : PrimeValue := ⟨1226213, pr1226213⟩
private theorem pr1226339 : PrimeCertificate 1226339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv613169]) (by decide +kernel)
def pv1226339 : PrimeValue := ⟨1226339, pr1226339⟩
private theorem pr1226651 : PrimeCertificate 1226651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv24533]) (by decide +kernel)
def pv1226651 : PrimeValue := ⟨1226651, pr1226651⟩
private theorem pr1226741 : PrimeCertificate 1226741 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv83,pv739]) (by decide +kernel)
def pv1226741 : PrimeValue := ⟨1226741, pr1226741⟩
private theorem pr1226783 : PrimeCertificate 1226783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv167,pv3673]) (by decide +kernel)
def pv1226783 : PrimeValue := ⟨1226783, pr1226783⟩
private theorem pr1226891 : PrimeCertificate 1226891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv1031]) (by decide +kernel)
def pv1226891 : PrimeValue := ⟨1226891, pr1226891⟩
private theorem pr1227053 : PrimeCertificate 1227053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv306763]) (by decide +kernel)
def pv1227053 : PrimeValue := ⟨1227053, pr1227053⟩
private theorem pr1227563 : PrimeCertificate 1227563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv87683]) (by decide +kernel)
def pv1227563 : PrimeValue := ⟨1227563, pr1227563⟩
private theorem pr1227881 : PrimeCertificate 1227881 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv30697]) (by decide +kernel)
def pv1227881 : PrimeValue := ⟨1227881, pr1227881⟩
private theorem pr1227911 : PrimeCertificate 1227911 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv17,pv31,pv233]) (by decide +kernel)
def pv1227911 : PrimeValue := ⟨1227911, pr1227911⟩
private theorem pr1228373 : PrimeCertificate 1228373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv307093]) (by decide +kernel)
def pv1228373 : PrimeValue := ⟨1228373, pr1228373⟩
private theorem pr1228589 : PrimeCertificate 1228589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv307147]) (by decide +kernel)
def pv1228589 : PrimeValue := ⟨1228589, pr1228589⟩
private theorem pr1228613 : PrimeCertificate 1228613 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv3989]) (by decide +kernel)
def pv1228613 : PrimeValue := ⟨1228613, pr1228613⟩
private theorem pr1228691 : PrimeCertificate 1228691 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv122869]) (by decide +kernel)
def pv1228691 : PrimeValue := ⟨1228691, pr1228691⟩
private theorem pr1228919 : PrimeCertificate 1228919 :=
  certifyPrime (q := pv17) (ls := [pv2,pv37,pv16607]) (by decide +kernel)
def pv1228919 : PrimeValue := ⟨1228919, pr1228919⟩
private theorem pr1228949 : PrimeCertificate 1228949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv43891]) (by decide +kernel)
def pv1228949 : PrimeValue := ⟨1228949, pr1228949⟩
private theorem pr1229141 : PrimeCertificate 1229141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv37,pv151]) (by decide +kernel)
def pv1229141 : PrimeValue := ⟨1229141, pr1229141⟩
private theorem pr1229201 : PrimeCertificate 1229201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv439]) (by decide +kernel)
def pv1229201 : PrimeValue := ⟨1229201, pr1229201⟩
private theorem pr1229213 : PrimeCertificate 1229213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv31,pv431]) (by decide +kernel)
def pv1229213 : PrimeValue := ⟨1229213, pr1229213⟩
private theorem pr1229561 : PrimeCertificate 1229561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv59,pv521]) (by decide +kernel)
def pv1229561 : PrimeValue := ⟨1229561, pr1229561⟩
private theorem pr1229939 : PrimeCertificate 1229939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv157,pv3917]) (by decide +kernel)
def pv1229939 : PrimeValue := ⟨1229939, pr1229939⟩
private theorem pr1230233 : PrimeCertificate 1230233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv103,pv1493]) (by decide +kernel)
def pv1230233 : PrimeValue := ⟨1230233, pr1230233⟩
private theorem pr1230263 : PrimeCertificate 1230263 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv55921]) (by decide +kernel)
def pv1230263 : PrimeValue := ⟨1230263, pr1230263⟩
private theorem pr1230329 : PrimeCertificate 1230329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv31,pv41]) (by decide +kernel)
def pv1230329 : PrimeValue := ⟨1230329, pr1230329⟩
private theorem pr1230371 : PrimeCertificate 1230371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv2017]) (by decide +kernel)
def pv1230371 : PrimeValue := ⟨1230371, pr1230371⟩
private theorem pr1230401 : PrimeCertificate 1230401 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv769]) (by decide +kernel)
def pv1230401 : PrimeValue := ⟨1230401, pr1230401⟩
private theorem pr1230479 : PrimeCertificate 1230479 :=
  certifyPrime (q := pv19) (ls := [pv2,pv19,pv32381]) (by decide +kernel)
def pv1230479 : PrimeValue := ⟨1230479, pr1230479⟩
private theorem pr1230863 : PrimeCertificate 1230863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv615431]) (by decide +kernel)
def pv1230863 : PrimeValue := ⟨1230863, pr1230863⟩
private theorem pr1231049 : PrimeCertificate 1231049 :=
  certifyPrime (q := pv17) (ls := [pv2,pv7,pv13,pv19,pv89]) (by decide +kernel)
def pv1231049 : PrimeValue := ⟨1231049, pr1231049⟩
private theorem pr1231319 : PrimeCertificate 1231319 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv97,pv577]) (by decide +kernel)
def pv1231319 : PrimeValue := ⟨1231319, pr1231319⟩
private theorem pr1231421 : PrimeCertificate 1231421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv2677]) (by decide +kernel)
def pv1231421 : PrimeValue := ⟨1231421, pr1231421⟩
private theorem pr1231469 : PrimeCertificate 1231469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv61,pv103]) (by decide +kernel)
def pv1231469 : PrimeValue := ⟨1231469, pr1231469⟩
private theorem pr1231721 : PrimeCertificate 1231721 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv53,pv83]) (by decide +kernel)
def pv1231721 : PrimeValue := ⟨1231721, pr1231721⟩
private theorem pr1231733 : PrimeCertificate 1231733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv853]) (by decide +kernel)
def pv1231733 : PrimeValue := ⟨1231733, pr1231733⟩
private theorem pr1231883 : PrimeCertificate 1231883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv615941]) (by decide +kernel)
def pv1231883 : PrimeValue := ⟨1231883, pr1231883⟩
private theorem pr1231889 : PrimeCertificate 1231889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv647]) (by decide +kernel)
def pv1231889 : PrimeValue := ⟨1231889, pr1231889⟩
private theorem pr1231943 : PrimeCertificate 1231943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv615971]) (by decide +kernel)
def pv1231943 : PrimeValue := ⟨1231943, pr1231943⟩
private theorem pr1232201 : PrimeCertificate 1232201 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv61,pv101]) (by decide +kernel)
def pv1232201 : PrimeValue := ⟨1232201, pr1232201⟩
private theorem pr1232243 : PrimeCertificate 1232243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv79,pv709]) (by decide +kernel)
def pv1232243 : PrimeValue := ⟨1232243, pr1232243⟩
private theorem pr1232411 : PrimeCertificate 1232411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv251,pv491]) (by decide +kernel)
def pv1232411 : PrimeValue := ⟨1232411, pr1232411⟩
private theorem pr1232531 : PrimeCertificate 1232531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv19,pv499]) (by decide +kernel)
def pv1232531 : PrimeValue := ⟨1232531, pr1232531⟩
private theorem pr1232771 : PrimeCertificate 1232771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv11,pv1601]) (by decide +kernel)
def pv1232771 : PrimeValue := ⟨1232771, pr1232771⟩
private theorem pr1232909 : PrimeCertificate 1232909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv18131]) (by decide +kernel)
def pv1232909 : PrimeValue := ⟨1232909, pr1232909⟩
private theorem pr1232981 : PrimeCertificate 1232981 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv8807]) (by decide +kernel)
def pv1232981 : PrimeValue := ⟨1232981, pr1232981⟩
private theorem pr1233509 : PrimeCertificate 1233509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv2729]) (by decide +kernel)
def pv1233509 : PrimeValue := ⟨1233509, pr1233509⟩
private theorem pr1233569 : PrimeCertificate 1233569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv5507]) (by decide +kernel)
def pv1233569 : PrimeValue := ⟨1233569, pr1233569⟩
private theorem pr1233653 : PrimeCertificate 1233653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv44059]) (by decide +kernel)
def pv1233653 : PrimeValue := ⟨1233653, pr1233653⟩
private theorem pr1233779 : PrimeCertificate 1233779 :=
  certifyPrime (q := pv29) (ls := [pv2,pv7,pv13,pv6779]) (by decide +kernel)
def pv1233779 : PrimeValue := ⟨1233779, pr1233779⟩
private theorem pr1233929 : PrimeCertificate 1233929 :=
  certifyPrime (q := pv13) (ls := [pv2,pv17,pv43,pv211]) (by decide +kernel)
def pv1233929 : PrimeValue := ⟨1233929, pr1233929⟩
private theorem pr1234049 : PrimeCertificate 1234049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv311]) (by decide +kernel)
def pv1234049 : PrimeValue := ⟨1234049, pr1234049⟩
private theorem pr1234253 : PrimeCertificate 1234253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv3467]) (by decide +kernel)
def pv1234253 : PrimeValue := ⟨1234253, pr1234253⟩
private theorem pr1234703 : PrimeCertificate 1234703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv43,pv293]) (by decide +kernel)
def pv1234703 : PrimeValue := ⟨1234703, pr1234703⟩
private theorem pr1234991 : PrimeCertificate 1234991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv123499]) (by decide +kernel)
def pv1234991 : PrimeValue := ⟨1234991, pr1234991⟩
private theorem pr1235099 : PrimeCertificate 1235099 :=
  certifyPrime (q := pv13) (ls := [pv2,pv313,pv1973]) (by decide +kernel)
def pv1235099 : PrimeValue := ⟨1235099, pr1235099⟩
private theorem pr1235159 : PrimeCertificate 1235159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv617579]) (by decide +kernel)
def pv1235159 : PrimeValue := ⟨1235159, pr1235159⟩
private theorem pr1235369 : PrimeCertificate 1235369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv307,pv503]) (by decide +kernel)
def pv1235369 : PrimeValue := ⟨1235369, pr1235369⟩
private theorem pr1235831 : PrimeCertificate 1235831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv123583]) (by decide +kernel)
def pv1235831 : PrimeValue := ⟨1235831, pr1235831⟩
private theorem pr1236173 : PrimeCertificate 1236173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17,pv53]) (by decide +kernel)
def pv1236173 : PrimeValue := ⟨1236173, pr1236173⟩
private theorem pr1236479 : PrimeCertificate 1236479 :=
  certifyPrime (q := pv19) (ls := [pv2,pv17,pv41,pv887]) (by decide +kernel)
def pv1236479 : PrimeValue := ⟨1236479, pr1236479⟩
private theorem pr1236533 : PrimeCertificate 1236533 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv157,pv179]) (by decide +kernel)
def pv1236533 : PrimeValue := ⟨1236533, pr1236533⟩
private theorem pr1236803 : PrimeCertificate 1236803 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23,pv167]) (by decide +kernel)
def pv1236803 : PrimeValue := ⟨1236803, pr1236803⟩
private theorem pr1236953 : PrimeCertificate 1236953 :=
  certifyPrime (q := pv3) (ls := [pv2,pv154619]) (by decide +kernel)
def pv1236953 : PrimeValue := ⟨1236953, pr1236953⟩
private theorem pr1237091 : PrimeCertificate 1237091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv19,pv383]) (by decide +kernel)
def pv1237091 : PrimeValue := ⟨1237091, pr1237091⟩
private theorem pr1237499 : PrimeCertificate 1237499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv2141]) (by decide +kernel)
def pv1237499 : PrimeValue := ⟨1237499, pr1237499⟩
private theorem pr1237823 : PrimeCertificate 1237823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv163,pv3797]) (by decide +kernel)
def pv1237823 : PrimeValue := ⟨1237823, pr1237823⟩
private theorem pr1237919 : PrimeCertificate 1237919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv56269]) (by decide +kernel)
def pv1237919 : PrimeValue := ⟨1237919, pr1237919⟩
private theorem pr1238273 : PrimeCertificate 1238273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv691]) (by decide +kernel)
def pv1238273 : PrimeValue := ⟨1238273, pr1238273⟩
private theorem pr1238291 : PrimeCertificate 1238291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv123829]) (by decide +kernel)
def pv1238291 : PrimeValue := ⟨1238291, pr1238291⟩
private theorem pr1238333 : PrimeCertificate 1238333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv309583]) (by decide +kernel)
def pv1238333 : PrimeValue := ⟨1238333, pr1238333⟩
private theorem pr1238903 : PrimeCertificate 1238903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv88493]) (by decide +kernel)
def pv1238903 : PrimeValue := ⟨1238903, pr1238903⟩
private theorem pr1239041 : PrimeCertificate 1239041 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv1239041 : PrimeValue := ⟨1239041, pr1239041⟩
private theorem pr1239239 : PrimeCertificate 1239239 :=
  certifyPrime (q := pv11) (ls := [pv2,pv7,pv11,pv13,pv619]) (by decide +kernel)
def pv1239239 : PrimeValue := ⟨1239239, pr1239239⟩
private theorem pr1239449 : PrimeCertificate 1239449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv22133]) (by decide +kernel)
def pv1239449 : PrimeValue := ⟨1239449, pr1239449⟩
private theorem pr1239509 : PrimeCertificate 1239509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv309877]) (by decide +kernel)
def pv1239509 : PrimeValue := ⟨1239509, pr1239509⟩
private theorem pr1239761 : PrimeCertificate 1239761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv15497]) (by decide +kernel)
def pv1239761 : PrimeValue := ⟨1239761, pr1239761⟩
private theorem pr1239839 : PrimeCertificate 1239839 :=
  certifyPrime (q := pv17) (ls := [pv2,pv23,pv26953]) (by decide +kernel)
def pv1239839 : PrimeValue := ⟨1239839, pr1239839⟩
private theorem pr1239893 : PrimeCertificate 1239893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv401,pv773]) (by decide +kernel)
def pv1239893 : PrimeValue := ⟨1239893, pr1239893⟩
private theorem pr1239923 : PrimeCertificate 1239923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv15121]) (by decide +kernel)
def pv1239923 : PrimeValue := ⟨1239923, pr1239923⟩
private theorem pr1240241 : PrimeCertificate 1240241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv419]) (by decide +kernel)
def pv1240241 : PrimeValue := ⟨1240241, pr1240241⟩
private theorem pr1240391 : PrimeCertificate 1240391 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv23,pv5393]) (by decide +kernel)
def pv1240391 : PrimeValue := ⟨1240391, pr1240391⟩
private theorem pr1240523 : PrimeCertificate 1240523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv620261]) (by decide +kernel)
def pv1240523 : PrimeValue := ⟨1240523, pr1240523⟩
private theorem pr1240553 : PrimeCertificate 1240553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv155069]) (by decide +kernel)
def pv1240553 : PrimeValue := ⟨1240553, pr1240553⟩
private theorem pr1240751 : PrimeCertificate 1240751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv709]) (by decide +kernel)
def pv1240751 : PrimeValue := ⟨1240751, pr1240751⟩
private theorem pr1240859 : PrimeCertificate 1240859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv620429]) (by decide +kernel)
def pv1240859 : PrimeValue := ⟨1240859, pr1240859⟩
private theorem pr1240931 : PrimeCertificate 1240931 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv31,pv4003]) (by decide +kernel)
def pv1240931 : PrimeValue := ⟨1240931, pr1240931⟩
private theorem pr1240979 : PrimeCertificate 1240979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv433,pv1433]) (by decide +kernel)
def pv1240979 : PrimeValue := ⟨1240979, pr1240979⟩
private theorem pr1241249 : PrimeCertificate 1241249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv79,pv491]) (by decide +kernel)
def pv1241249 : PrimeValue := ⟨1241249, pr1241249⟩
private theorem pr1241291 : PrimeCertificate 1241291 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv101,pv1229]) (by decide +kernel)
def pv1241291 : PrimeValue := ⟨1241291, pr1241291⟩
private theorem pr1241351 : PrimeCertificate 1241351 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv37,pv61]) (by decide +kernel)
def pv1241351 : PrimeValue := ⟨1241351, pr1241351⟩
private theorem pr1241483 : PrimeCertificate 1241483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv56431]) (by decide +kernel)
def pv1241483 : PrimeValue := ⟨1241483, pr1241483⟩
private theorem pr1241549 : PrimeCertificate 1241549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv29,pv139]) (by decide +kernel)
def pv1241549 : PrimeValue := ⟨1241549, pr1241549⟩
private theorem pr1241573 : PrimeCertificate 1241573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv8389]) (by decide +kernel)
def pv1241573 : PrimeValue := ⟨1241573, pr1241573⟩
private theorem pr1241741 : PrimeCertificate 1241741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv47,pv1321]) (by decide +kernel)
def pv1241741 : PrimeValue := ⟨1241741, pr1241741⟩
private theorem pr1241771 : PrimeCertificate 1241771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv23,pv5399]) (by decide +kernel)
def pv1241771 : PrimeValue := ⟨1241771, pr1241771⟩
private theorem pr1242029 : PrimeCertificate 1242029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv310507]) (by decide +kernel)
def pv1242029 : PrimeValue := ⟨1242029, pr1242029⟩
private theorem pr1242089 : PrimeCertificate 1242089 :=
  certifyPrime (q := pv11) (ls := [pv2,pv17,pv9133]) (by decide +kernel)
def pv1242089 : PrimeValue := ⟨1242089, pr1242089⟩
private theorem pr1242413 : PrimeCertificate 1242413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv263,pv1181]) (by decide +kernel)
def pv1242413 : PrimeValue := ⟨1242413, pr1242413⟩
private theorem pr1242641 : PrimeCertificate 1242641 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv317]) (by decide +kernel)
def pv1242641 : PrimeValue := ⟨1242641, pr1242641⟩
private theorem pr1242803 : PrimeCertificate 1242803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv17,pv3323]) (by decide +kernel)
def pv1242803 : PrimeValue := ⟨1242803, pr1242803⟩
private theorem pr1242869 : PrimeCertificate 1242869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv47,pv601]) (by decide +kernel)
def pv1242869 : PrimeValue := ⟨1242869, pr1242869⟩
private theorem pr1243013 : PrimeCertificate 1243013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv59,pv229]) (by decide +kernel)
def pv1243013 : PrimeValue := ⟨1243013, pr1243013⟩
private theorem pr1243211 : PrimeCertificate 1243211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv71,pv103]) (by decide +kernel)
def pv1243211 : PrimeValue := ⟨1243211, pr1243211⟩
private theorem pr1243349 : PrimeCertificate 1243349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv37,pv271]) (by decide +kernel)
def pv1243349 : PrimeValue := ⟨1243349, pr1243349⟩
private theorem pr1243373 : PrimeCertificate 1243373 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23911]) (by decide +kernel)
def pv1243373 : PrimeValue := ⟨1243373, pr1243373⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
