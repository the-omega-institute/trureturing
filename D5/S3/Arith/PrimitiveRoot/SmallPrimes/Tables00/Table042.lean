/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table042
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table042.pv112657
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table005
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table008
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table022
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table023

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr112657 : PrimeCertificate 112657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv2347]) (by decide +kernel)
def pv112657 : PrimeValue := ⟨112657, pr112657⟩
private theorem pr112663 : PrimeCertificate 112663 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv11,pv569]) (by decide +kernel)
def pv112663 : PrimeValue := ⟨112663, pr112663⟩
private theorem pr112691 : PrimeCertificate 112691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv59,pv191]) (by decide +kernel)
def pv112691 : PrimeValue := ⟨112691, pr112691⟩
private theorem pr112741 : PrimeCertificate 112741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1879]) (by decide +kernel)
def pv112741 : PrimeValue := ⟨112741, pr112741⟩
private theorem pr112757 : PrimeCertificate 112757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4027]) (by decide +kernel)
def pv112757 : PrimeValue := ⟨112757, pr112757⟩
private theorem pr112771 : PrimeCertificate 112771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv179]) (by decide +kernel)
def pv112771 : PrimeValue := ⟨112771, pr112771⟩
private theorem pr112799 : PrimeCertificate 112799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv1151]) (by decide +kernel)
def pv112799 : PrimeValue := ⟨112799, pr112799⟩
private theorem pr112807 : PrimeCertificate 112807 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2089]) (by decide +kernel)
def pv112807 : PrimeValue := ⟨112807, pr112807⟩
private theorem pr112831 : PrimeCertificate 112831 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5,pv3761]) (by decide +kernel)
def pv112831 : PrimeValue := ⟨112831, pr112831⟩
private theorem pr112859 : PrimeCertificate 112859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv773]) (by decide +kernel)
def pv112859 : PrimeValue := ⟨112859, pr112859⟩
private theorem pr112877 : PrimeCertificate 112877 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28219]) (by decide +kernel)
def pv112877 : PrimeValue := ⟨112877, pr112877⟩
private theorem pr112901 : PrimeCertificate 112901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1129]) (by decide +kernel)
def pv112901 : PrimeValue := ⟨112901, pr112901⟩
private theorem pr112909 : PrimeCertificate 112909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97]) (by decide +kernel)
def pv112909 : PrimeValue := ⟨112909, pr112909⟩
private theorem pr112913 : PrimeCertificate 112913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7057]) (by decide +kernel)
def pv112913 : PrimeValue := ⟨112913, pr112913⟩
private theorem pr112919 : PrimeCertificate 112919 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv43,pv101]) (by decide +kernel)
def pv112919 : PrimeValue := ⟨112919, pr112919⟩
private theorem pr112921 : PrimeCertificate 112921 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv941]) (by decide +kernel)
def pv112921 : PrimeValue := ⟨112921, pr112921⟩
private theorem pr112927 : PrimeCertificate 112927 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv29,pv59]) (by decide +kernel)
def pv112927 : PrimeValue := ⟨112927, pr112927⟩
private theorem pr112939 : PrimeCertificate 112939 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7,pv2689]) (by decide +kernel)
def pv112939 : PrimeValue := ⟨112939, pr112939⟩
private theorem pr112951 : PrimeCertificate 112951 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv251]) (by decide +kernel)
def pv112951 : PrimeValue := ⟨112951, pr112951⟩
private theorem pr112967 : PrimeCertificate 112967 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv8069]) (by decide +kernel)
def pv112967 : PrimeValue := ⟨112967, pr112967⟩
private theorem pr112979 : PrimeCertificate 112979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56489]) (by decide +kernel)
def pv112979 : PrimeValue := ⟨112979, pr112979⟩
private theorem pr112997 : PrimeCertificate 112997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv41,pv53]) (by decide +kernel)
def pv112997 : PrimeValue := ⟨112997, pr112997⟩
private theorem pr113011 : PrimeCertificate 113011 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv3767]) (by decide +kernel)
def pv113011 : PrimeValue := ⟨113011, pr113011⟩
private theorem pr113017 : PrimeCertificate 113017 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv17,pv277]) (by decide +kernel)
def pv113017 : PrimeValue := ⟨113017, pr113017⟩
private theorem pr113021 : PrimeCertificate 113021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5651]) (by decide +kernel)
def pv113021 : PrimeValue := ⟨113021, pr113021⟩
private theorem pr113023 : PrimeCertificate 113023 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv23]) (by decide +kernel)
def pv113023 : PrimeValue := ⟨113023, pr113023⟩
private theorem pr113027 : PrimeCertificate 113027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1823]) (by decide +kernel)
def pv113027 : PrimeValue := ⟨113027, pr113027⟩
private theorem pr113051 : PrimeCertificate 113051 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv19]) (by decide +kernel)
def pv113051 : PrimeValue := ⟨113051, pr113051⟩
private theorem pr113063 : PrimeCertificate 113063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv56531]) (by decide +kernel)
def pv113063 : PrimeValue := ⟨113063, pr113063⟩
private theorem pr113081 : PrimeCertificate 113081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv257]) (by decide +kernel)
def pv113081 : PrimeValue := ⟨113081, pr113081⟩
private theorem pr113083 : PrimeCertificate 113083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv401]) (by decide +kernel)
def pv113083 : PrimeValue := ⟨113083, pr113083⟩
private theorem pr113089 : PrimeCertificate 113089 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19,pv31]) (by decide +kernel)
def pv113089 : PrimeValue := ⟨113089, pr113089⟩
private theorem pr113093 : PrimeCertificate 113093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv577]) (by decide +kernel)
def pv113093 : PrimeValue := ⟨113093, pr113093⟩
private theorem pr113111 : PrimeCertificate 113111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11311]) (by decide +kernel)
def pv113111 : PrimeValue := ⟨113111, pr113111⟩
private theorem pr113123 : PrimeCertificate 113123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv163,pv347]) (by decide +kernel)
def pv113123 : PrimeValue := ⟨113123, pr113123⟩
private theorem pr113131 : PrimeCertificate 113131 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv419]) (by decide +kernel)
def pv113131 : PrimeValue := ⟨113131, pr113131⟩
private theorem pr113143 : PrimeCertificate 113143 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv109,pv173]) (by decide +kernel)
def pv113143 : PrimeValue := ⟨113143, pr113143⟩
private theorem pr113147 : PrimeCertificate 113147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv139]) (by decide +kernel)
def pv113147 : PrimeValue := ⟨113147, pr113147⟩
private theorem pr113149 : PrimeCertificate 113149 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv449]) (by decide +kernel)
def pv113149 : PrimeValue := ⟨113149, pr113149⟩
private theorem pr113153 : PrimeCertificate 113153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv17]) (by decide +kernel)
def pv113153 : PrimeValue := ⟨113153, pr113153⟩
private theorem pr113159 : PrimeCertificate 113159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv1951]) (by decide +kernel)
def pv113159 : PrimeValue := ⟨113159, pr113159⟩
private theorem pr113161 : PrimeCertificate 113161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv23,pv41]) (by decide +kernel)
def pv113161 : PrimeValue := ⟨113161, pr113161⟩
private theorem pr113167 : PrimeCertificate 113167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv6287]) (by decide +kernel)
def pv113167 : PrimeValue := ⟨113167, pr113167⟩
private theorem pr113171 : PrimeCertificate 113171 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11317]) (by decide +kernel)
def pv113171 : PrimeValue := ⟨113171, pr113171⟩
private theorem pr113173 : PrimeCertificate 113173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9431]) (by decide +kernel)
def pv113173 : PrimeValue := ⟨113173, pr113173⟩
private theorem pr113177 : PrimeCertificate 113177 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv43,pv47]) (by decide +kernel)
def pv113177 : PrimeValue := ⟨113177, pr113177⟩
private theorem pr113189 : PrimeCertificate 113189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28297]) (by decide +kernel)
def pv113189 : PrimeValue := ⟨113189, pr113189⟩
private theorem pr113209 : PrimeCertificate 113209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53,pv89]) (by decide +kernel)
def pv113209 : PrimeValue := ⟨113209, pr113209⟩
private theorem pr113213 : PrimeCertificate 113213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv83]) (by decide +kernel)
def pv113213 : PrimeValue := ⟨113213, pr113213⟩
private theorem pr113227 : PrimeCertificate 113227 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv113,pv167]) (by decide +kernel)
def pv113227 : PrimeValue := ⟨113227, pr113227⟩
private theorem pr113233 : PrimeCertificate 113233 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv337]) (by decide +kernel)
def pv113233 : PrimeValue := ⟨113233, pr113233⟩
private theorem pr113279 : PrimeCertificate 113279 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv19,pv271]) (by decide +kernel)
def pv113279 : PrimeValue := ⟨113279, pr113279⟩
private theorem pr113287 : PrimeCertificate 113287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv239]) (by decide +kernel)
def pv113287 : PrimeValue := ⟨113287, pr113287⟩
private theorem pr113327 : PrimeCertificate 113327 :=
  certifyPrime (q := pv5) (ls := [pv2,pv56663]) (by decide +kernel)
def pv113327 : PrimeValue := ⟨113327, pr113327⟩
private theorem pr113329 : PrimeCertificate 113329 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv787]) (by decide +kernel)
def pv113329 : PrimeValue := ⟨113329, pr113329⟩
private theorem pr113341 : PrimeCertificate 113341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv1889]) (by decide +kernel)
def pv113341 : PrimeValue := ⟨113341, pr113341⟩
private theorem pr113357 : PrimeCertificate 113357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv1667]) (by decide +kernel)
def pv113357 : PrimeValue := ⟨113357, pr113357⟩
private theorem pr113359 : PrimeCertificate 113359 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2699]) (by decide +kernel)
def pv113359 : PrimeValue := ⟨113359, pr113359⟩
private theorem pr113363 : PrimeCertificate 113363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56681]) (by decide +kernel)
def pv113363 : PrimeValue := ⟨113363, pr113363⟩
private theorem pr113371 : PrimeCertificate 113371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3779]) (by decide +kernel)
def pv113371 : PrimeValue := ⟨113371, pr113371⟩
private theorem pr113383 : PrimeCertificate 113383 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6299]) (by decide +kernel)
def pv113383 : PrimeValue := ⟨113383, pr113383⟩
private theorem pr113417 : PrimeCertificate 113417 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14177]) (by decide +kernel)
def pv113417 : PrimeValue := ⟨113417, pr113417⟩
private theorem pr113437 : PrimeCertificate 113437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv137]) (by decide +kernel)
def pv113437 : PrimeValue := ⟨113437, pr113437⟩
private theorem pr113453 : PrimeCertificate 113453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv251]) (by decide +kernel)
def pv113453 : PrimeValue := ⟨113453, pr113453⟩
private theorem pr113467 : PrimeCertificate 113467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv18911]) (by decide +kernel)
def pv113467 : PrimeValue := ⟨113467, pr113467⟩
private theorem pr113489 : PrimeCertificate 113489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv173]) (by decide +kernel)
def pv113489 : PrimeValue := ⟨113489, pr113489⟩
private theorem pr113497 : PrimeCertificate 113497 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4729]) (by decide +kernel)
def pv113497 : PrimeValue := ⟨113497, pr113497⟩
private theorem pr113501 : PrimeCertificate 113501 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv227]) (by decide +kernel)
def pv113501 : PrimeValue := ⟨113501, pr113501⟩
private theorem pr113513 : PrimeCertificate 113513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2027]) (by decide +kernel)
def pv113513 : PrimeValue := ⟨113513, pr113513⟩
private theorem pr113539 : PrimeCertificate 113539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv127,pv149]) (by decide +kernel)
def pv113539 : PrimeValue := ⟨113539, pr113539⟩
private theorem pr113557 : PrimeCertificate 113557 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9463]) (by decide +kernel)
def pv113557 : PrimeValue := ⟨113557, pr113557⟩
private theorem pr113567 : PrimeCertificate 113567 :=
  certifyPrime (q := pv5) (ls := [pv2,pv56783]) (by decide +kernel)
def pv113567 : PrimeValue := ⟨113567, pr113567⟩
private theorem pr113591 : PrimeCertificate 113591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv37,pv307]) (by decide +kernel)
def pv113591 : PrimeValue := ⟨113591, pr113591⟩
private theorem pr113621 : PrimeCertificate 113621 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv13,pv19,pv23]) (by decide +kernel)
def pv113621 : PrimeValue := ⟨113621, pr113621⟩
private theorem pr113623 : PrimeCertificate 113623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv29,pv653]) (by decide +kernel)
def pv113623 : PrimeValue := ⟨113623, pr113623⟩
private theorem pr113647 : PrimeCertificate 113647 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv31,pv47]) (by decide +kernel)
def pv113647 : PrimeValue := ⟨113647, pr113647⟩
private theorem pr113657 : PrimeCertificate 113657 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14207]) (by decide +kernel)
def pv113657 : PrimeValue := ⟨113657, pr113657⟩
private theorem pr113683 : PrimeCertificate 113683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv18947]) (by decide +kernel)
def pv113683 : PrimeValue := ⟨113683, pr113683⟩
private theorem pr113717 : PrimeCertificate 113717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28429]) (by decide +kernel)
def pv113717 : PrimeValue := ⟨113717, pr113717⟩
private theorem pr113719 : PrimeCertificate 113719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv1723]) (by decide +kernel)
def pv113719 : PrimeValue := ⟨113719, pr113719⟩
private theorem pr113723 : PrimeCertificate 113723 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv8123]) (by decide +kernel)
def pv113723 : PrimeValue := ⟨113723, pr113723⟩
private theorem pr113731 : PrimeCertificate 113731 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv17,pv223]) (by decide +kernel)
def pv113731 : PrimeValue := ⟨113731, pr113731⟩
private theorem pr113759 : PrimeCertificate 113759 :=
  certifyPrime (q := pv7) (ls := [pv2,pv23,pv2473]) (by decide +kernel)
def pv113759 : PrimeValue := ⟨113759, pr113759⟩
private theorem pr113761 : PrimeCertificate 113761 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv113761 : PrimeValue := ⟨113761, pr113761⟩
private theorem pr113777 : PrimeCertificate 113777 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv547]) (by decide +kernel)
def pv113777 : PrimeValue := ⟨113777, pr113777⟩
private theorem pr113779 : PrimeCertificate 113779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv43]) (by decide +kernel)
def pv113779 : PrimeValue := ⟨113779, pr113779⟩
private theorem pr113783 : PrimeCertificate 113783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv56891]) (by decide +kernel)
def pv113783 : PrimeValue := ⟨113783, pr113783⟩
private theorem pr113797 : PrimeCertificate 113797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv109]) (by decide +kernel)
def pv113797 : PrimeValue := ⟨113797, pr113797⟩
private theorem pr113809 : PrimeCertificate 113809 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv2371]) (by decide +kernel)
def pv113809 : PrimeValue := ⟨113809, pr113809⟩
private theorem pr113819 : PrimeCertificate 113819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56909]) (by decide +kernel)
def pv113819 : PrimeValue := ⟨113819, pr113819⟩
private theorem pr113837 : PrimeCertificate 113837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv149,pv191]) (by decide +kernel)
def pv113837 : PrimeValue := ⟨113837, pr113837⟩
private theorem pr113843 : PrimeCertificate 113843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56921]) (by decide +kernel)
def pv113843 : PrimeValue := ⟨113843, pr113843⟩
private theorem pr113891 : PrimeCertificate 113891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1627]) (by decide +kernel)
def pv113891 : PrimeValue := ⟨113891, pr113891⟩
private theorem pr113899 : PrimeCertificate 113899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv463]) (by decide +kernel)
def pv113899 : PrimeValue := ⟨113899, pr113899⟩
private theorem pr113903 : PrimeCertificate 113903 :=
  certifyPrime (q := pv5) (ls := [pv2,pv56951]) (by decide +kernel)
def pv113903 : PrimeValue := ⟨113903, pr113903⟩
private theorem pr113909 : PrimeCertificate 113909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28477]) (by decide +kernel)
def pv113909 : PrimeValue := ⟨113909, pr113909⟩
private theorem pr113921 : PrimeCertificate 113921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv89]) (by decide +kernel)
def pv113921 : PrimeValue := ⟨113921, pr113921⟩
private theorem pr113933 : PrimeCertificate 113933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv313]) (by decide +kernel)
def pv113933 : PrimeValue := ⟨113933, pr113933⟩
private theorem pr113947 : PrimeCertificate 113947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2713]) (by decide +kernel)
def pv113947 : PrimeValue := ⟨113947, pr113947⟩
private theorem pr113957 : PrimeCertificate 113957 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv919]) (by decide +kernel)
def pv113957 : PrimeValue := ⟨113957, pr113957⟩
private theorem pr113963 : PrimeCertificate 113963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv2999]) (by decide +kernel)
def pv113963 : PrimeValue := ⟨113963, pr113963⟩
private theorem pr113969 : PrimeCertificate 113969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv419]) (by decide +kernel)
def pv113969 : PrimeValue := ⟨113969, pr113969⟩
private theorem pr113983 : PrimeCertificate 113983 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv157]) (by decide +kernel)
def pv113983 : PrimeValue := ⟨113983, pr113983⟩
private theorem pr113989 : PrimeCertificate 113989 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv23,pv59]) (by decide +kernel)
def pv113989 : PrimeValue := ⟨113989, pr113989⟩
private theorem pr114001 : PrimeCertificate 114001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv114001 : PrimeValue := ⟨114001, pr114001⟩
private theorem pr114013 : PrimeCertificate 114013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3167]) (by decide +kernel)
def pv114013 : PrimeValue := ⟨114013, pr114013⟩
private theorem pr114031 : PrimeCertificate 114031 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv114031 : PrimeValue := ⟨114031, pr114031⟩
private theorem pr114043 : PrimeCertificate 114043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv83,pv229]) (by decide +kernel)
def pv114043 : PrimeValue := ⟨114043, pr114043⟩
private theorem pr114067 : PrimeCertificate 114067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6337]) (by decide +kernel)
def pv114067 : PrimeValue := ⟨114067, pr114067⟩
private theorem pr114073 : PrimeCertificate 114073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv97]) (by decide +kernel)
def pv114073 : PrimeValue := ⟨114073, pr114073⟩
private theorem pr114077 : PrimeCertificate 114077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv79]) (by decide +kernel)
def pv114077 : PrimeValue := ⟨114077, pr114077⟩
private theorem pr114083 : PrimeCertificate 114083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57041]) (by decide +kernel)
def pv114083 : PrimeValue := ⟨114083, pr114083⟩
private theorem pr114089 : PrimeCertificate 114089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1097]) (by decide +kernel)
def pv114089 : PrimeValue := ⟨114089, pr114089⟩
private theorem pr114143 : PrimeCertificate 114143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv31,pv263]) (by decide +kernel)
def pv114143 : PrimeValue := ⟨114143, pr114143⟩
private theorem pr114157 : PrimeCertificate 114157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv151]) (by decide +kernel)
def pv114157 : PrimeValue := ⟨114157, pr114157⟩
private theorem pr114167 : PrimeCertificate 114167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv4391]) (by decide +kernel)
def pv114167 : PrimeValue := ⟨114167, pr114167⟩
private theorem pr114193 : PrimeCertificate 114193 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv61]) (by decide +kernel)
def pv114193 : PrimeValue := ⟨114193, pr114193⟩
private theorem pr114199 : PrimeCertificate 114199 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv2719]) (by decide +kernel)
def pv114199 : PrimeValue := ⟨114199, pr114199⟩
private theorem pr114203 : PrimeCertificate 114203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv29,pv179]) (by decide +kernel)
def pv114203 : PrimeValue := ⟨114203, pr114203⟩
private theorem pr114217 : PrimeCertificate 114217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4759]) (by decide +kernel)
def pv114217 : PrimeValue := ⟨114217, pr114217⟩
private theorem pr114221 : PrimeCertificate 114221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv5711]) (by decide +kernel)
def pv114221 : PrimeValue := ⟨114221, pr114221⟩
private theorem pr114229 : PrimeCertificate 114229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv167]) (by decide +kernel)
def pv114229 : PrimeValue := ⟨114229, pr114229⟩
private theorem pr114259 : PrimeCertificate 114259 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv137,pv139]) (by decide +kernel)
def pv114259 : PrimeValue := ⟨114259, pr114259⟩
private theorem pr114269 : PrimeCertificate 114269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv53]) (by decide +kernel)
def pv114269 : PrimeValue := ⟨114269, pr114269⟩
private theorem pr114277 : PrimeCertificate 114277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv107]) (by decide +kernel)
def pv114277 : PrimeValue := ⟨114277, pr114277⟩
private theorem pr114281 : PrimeCertificate 114281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv2857]) (by decide +kernel)
def pv114281 : PrimeValue := ⟨114281, pr114281⟩
private theorem pr114299 : PrimeCertificate 114299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57149]) (by decide +kernel)
def pv114299 : PrimeValue := ⟨114299, pr114299⟩
private theorem pr114311 : PrimeCertificate 114311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv23,pv71]) (by decide +kernel)
def pv114311 : PrimeValue := ⟨114311, pr114311⟩
private theorem pr114319 : PrimeCertificate 114319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv73]) (by decide +kernel)
def pv114319 : PrimeValue := ⟨114319, pr114319⟩
private theorem pr114329 : PrimeCertificate 114329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv461]) (by decide +kernel)
def pv114329 : PrimeValue := ⟨114329, pr114329⟩
private theorem pr114343 : PrimeCertificate 114343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv19,pv59]) (by decide +kernel)
def pv114343 : PrimeValue := ⟨114343, pr114343⟩
private theorem pr114371 : PrimeCertificate 114371 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11437]) (by decide +kernel)
def pv114371 : PrimeValue := ⟨114371, pr114371⟩
private theorem pr114377 : PrimeCertificate 114377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv29]) (by decide +kernel)
def pv114377 : PrimeValue := ⟨114377, pr114377⟩
private theorem pr114407 : PrimeCertificate 114407 :=
  certifyPrime (q := pv5) (ls := [pv2,pv57203]) (by decide +kernel)
def pv114407 : PrimeValue := ⟨114407, pr114407⟩
private theorem pr114419 : PrimeCertificate 114419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3011]) (by decide +kernel)
def pv114419 : PrimeValue := ⟨114419, pr114419⟩
private theorem pr114451 : PrimeCertificate 114451 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv109]) (by decide +kernel)
def pv114451 : PrimeValue := ⟨114451, pr114451⟩
private theorem pr114467 : PrimeCertificate 114467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv43]) (by decide +kernel)
def pv114467 : PrimeValue := ⟨114467, pr114467⟩
private theorem pr114473 : PrimeCertificate 114473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv349]) (by decide +kernel)
def pv114473 : PrimeValue := ⟨114473, pr114473⟩
private theorem pr114479 : PrimeCertificate 114479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv17,pv37]) (by decide +kernel)
def pv114479 : PrimeValue := ⟨114479, pr114479⟩
private theorem pr114487 : PrimeCertificate 114487 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19081]) (by decide +kernel)
def pv114487 : PrimeValue := ⟨114487, pr114487⟩
private theorem pr114493 : PrimeCertificate 114493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv29,pv47]) (by decide +kernel)
def pv114493 : PrimeValue := ⟨114493, pr114493⟩
private theorem pr114547 : PrimeCertificate 114547 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv1123]) (by decide +kernel)
def pv114547 : PrimeValue := ⟨114547, pr114547⟩
private theorem pr114571 : PrimeCertificate 114571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv19,pv67]) (by decide +kernel)
def pv114571 : PrimeValue := ⟨114571, pr114571⟩
private theorem pr114577 : PrimeCertificate 114577 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv114577 : PrimeValue := ⟨114577, pr114577⟩
private theorem pr114593 : PrimeCertificate 114593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3581]) (by decide +kernel)
def pv114593 : PrimeValue := ⟨114593, pr114593⟩
private theorem pr114599 : PrimeCertificate 114599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv5209]) (by decide +kernel)
def pv114599 : PrimeValue := ⟨114599, pr114599⟩
private theorem pr114601 : PrimeCertificate 114601 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv191]) (by decide +kernel)
def pv114601 : PrimeValue := ⟨114601, pr114601⟩
private theorem pr114613 : PrimeCertificate 114613 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv9551]) (by decide +kernel)
def pv114613 : PrimeValue := ⟨114613, pr114613⟩
private theorem pr114617 : PrimeCertificate 114617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14327]) (by decide +kernel)
def pv114617 : PrimeValue := ⟨114617, pr114617⟩
private theorem pr114641 : PrimeCertificate 114641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1433]) (by decide +kernel)
def pv114641 : PrimeValue := ⟨114641, pr114641⟩
private theorem pr114643 : PrimeCertificate 114643 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv193]) (by decide +kernel)
def pv114643 : PrimeValue := ⟨114643, pr114643⟩
private theorem pr114649 : PrimeCertificate 114649 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv17,pv281]) (by decide +kernel)
def pv114649 : PrimeValue := ⟨114649, pr114649⟩
private theorem pr114659 : PrimeCertificate 114659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57329]) (by decide +kernel)
def pv114659 : PrimeValue := ⟨114659, pr114659⟩
private theorem pr114661 : PrimeCertificate 114661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv114661 : PrimeValue := ⟨114661, pr114661⟩
private theorem pr114671 : PrimeCertificate 114671 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv11467]) (by decide +kernel)
def pv114671 : PrimeValue := ⟨114671, pr114671⟩
private theorem pr114679 : PrimeCertificate 114679 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv23,pv277]) (by decide +kernel)
def pv114679 : PrimeValue := ⟨114679, pr114679⟩
private theorem pr114689 : PrimeCertificate 114689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7]) (by decide +kernel)
def pv114689 : PrimeValue := ⟨114689, pr114689⟩
private theorem pr114691 : PrimeCertificate 114691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv3823]) (by decide +kernel)
def pv114691 : PrimeValue := ⟨114691, pr114691⟩
private theorem pr114713 : PrimeCertificate 114713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1103]) (by decide +kernel)
def pv114713 : PrimeValue := ⟨114713, pr114713⟩
private theorem pr114743 : PrimeCertificate 114743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv557]) (by decide +kernel)
def pv114743 : PrimeValue := ⟨114743, pr114743⟩
private theorem pr114749 : PrimeCertificate 114749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28687]) (by decide +kernel)
def pv114749 : PrimeValue := ⟨114749, pr114749⟩
private theorem pr114757 : PrimeCertificate 114757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv131]) (by decide +kernel)
def pv114757 : PrimeValue := ⟨114757, pr114757⟩
private theorem pr114761 : PrimeCertificate 114761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv151]) (by decide +kernel)
def pv114761 : PrimeValue := ⟨114761, pr114761⟩
private theorem pr114769 : PrimeCertificate 114769 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv797]) (by decide +kernel)
def pv114769 : PrimeValue := ⟨114769, pr114769⟩
private theorem pr114773 : PrimeCertificate 114773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4099]) (by decide +kernel)
def pv114773 : PrimeValue := ⟨114773, pr114773⟩
private theorem pr114781 : PrimeCertificate 114781 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv1913]) (by decide +kernel)
def pv114781 : PrimeValue := ⟨114781, pr114781⟩
private theorem pr114797 : PrimeCertificate 114797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv2609]) (by decide +kernel)
def pv114797 : PrimeValue := ⟨114797, pr114797⟩
private theorem pr114799 : PrimeCertificate 114799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv53]) (by decide +kernel)
def pv114799 : PrimeValue := ⟨114799, pr114799⟩
private theorem pr114809 : PrimeCertificate 114809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv113,pv127]) (by decide +kernel)
def pv114809 : PrimeValue := ⟨114809, pr114809⟩
private theorem pr114827 : PrimeCertificate 114827 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57413]) (by decide +kernel)
def pv114827 : PrimeValue := ⟨114827, pr114827⟩
private theorem pr114833 : PrimeCertificate 114833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7177]) (by decide +kernel)
def pv114833 : PrimeValue := ⟨114833, pr114833⟩
private theorem pr114847 : PrimeCertificate 114847 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19141]) (by decide +kernel)
def pv114847 : PrimeValue := ⟨114847, pr114847⟩
private theorem pr114859 : PrimeCertificate 114859 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv709]) (by decide +kernel)
def pv114859 : PrimeValue := ⟨114859, pr114859⟩
private theorem pr114883 : PrimeCertificate 114883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv467]) (by decide +kernel)
def pv114883 : PrimeValue := ⟨114883, pr114883⟩
private theorem pr114889 : PrimeCertificate 114889 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv4787]) (by decide +kernel)
def pv114889 : PrimeValue := ⟨114889, pr114889⟩
private theorem pr114901 : PrimeCertificate 114901 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv383]) (by decide +kernel)
def pv114901 : PrimeValue := ⟨114901, pr114901⟩
private theorem pr114913 : PrimeCertificate 114913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv19]) (by decide +kernel)
def pv114913 : PrimeValue := ⟨114913, pr114913⟩
private theorem pr114941 : PrimeCertificate 114941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv821]) (by decide +kernel)
def pv114941 : PrimeValue := ⟨114941, pr114941⟩
private theorem pr114967 : PrimeCertificate 114967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2129]) (by decide +kernel)
def pv114967 : PrimeValue := ⟨114967, pr114967⟩
private theorem pr114973 : PrimeCertificate 114973 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv13,pv67]) (by decide +kernel)
def pv114973 : PrimeValue := ⟨114973, pr114973⟩
private theorem pr114997 : PrimeCertificate 114997 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv37]) (by decide +kernel)
def pv114997 : PrimeValue := ⟨114997, pr114997⟩
private theorem pr115001 : PrimeCertificate 115001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23]) (by decide +kernel)
def pv115001 : PrimeValue := ⟨115001, pr115001⟩
private theorem pr115013 : PrimeCertificate 115013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28753]) (by decide +kernel)
def pv115013 : PrimeValue := ⟨115013, pr115013⟩
private theorem pr115021 : PrimeCertificate 115021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv115021 : PrimeValue := ⟨115021, pr115021⟩
private theorem pr115061 : PrimeCertificate 115061 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv523]) (by decide +kernel)
def pv115061 : PrimeValue := ⟨115061, pr115061⟩
private theorem pr115067 : PrimeCertificate 115067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8219]) (by decide +kernel)
def pv115067 : PrimeValue := ⟨115067, pr115067⟩
private theorem pr115079 : PrimeCertificate 115079 :=
  certifyPrime (q := pv17) (ls := [pv2,pv163,pv353]) (by decide +kernel)
def pv115079 : PrimeValue := ⟨115079, pr115079⟩
private theorem pr115099 : PrimeCertificate 115099 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19183]) (by decide +kernel)
def pv115099 : PrimeValue := ⟨115099, pr115099⟩
private theorem pr115123 : PrimeCertificate 115123 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv2741]) (by decide +kernel)
def pv115123 : PrimeValue := ⟨115123, pr115123⟩
private theorem pr115127 : PrimeCertificate 115127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv5233]) (by decide +kernel)
def pv115127 : PrimeValue := ⟨115127, pr115127⟩
private theorem pr115133 : PrimeCertificate 115133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv269]) (by decide +kernel)
def pv115133 : PrimeValue := ⟨115133, pr115133⟩
private theorem pr115151 : PrimeCertificate 115151 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv47]) (by decide +kernel)
def pv115151 : PrimeValue := ⟨115151, pr115151⟩
private theorem pr115153 : PrimeCertificate 115153 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2399]) (by decide +kernel)
def pv115153 : PrimeValue := ⟨115153, pr115153⟩
private theorem pr115163 : PrimeCertificate 115163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv811]) (by decide +kernel)
def pv115163 : PrimeValue := ⟨115163, pr115163⟩
private theorem pr115201 : PrimeCertificate 115201 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv115201 : PrimeValue := ⟨115201, pr115201⟩
private theorem pr115211 : PrimeCertificate 115211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv41,pv281]) (by decide +kernel)
def pv115211 : PrimeValue := ⟨115211, pr115211⟩
private theorem pr115223 : PrimeCertificate 115223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv53,pv1087]) (by decide +kernel)
def pv115223 : PrimeValue := ⟨115223, pr115223⟩
private theorem pr115237 : PrimeCertificate 115237 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv97]) (by decide +kernel)
def pv115237 : PrimeValue := ⟨115237, pr115237⟩
private theorem pr115249 : PrimeCertificate 115249 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv115249 : PrimeValue := ⟨115249, pr115249⟩
private theorem pr115259 : PrimeCertificate 115259 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv31]) (by decide +kernel)
def pv115259 : PrimeValue := ⟨115259, pr115259⟩
private theorem pr115279 : PrimeCertificate 115279 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv19213]) (by decide +kernel)
def pv115279 : PrimeValue := ⟨115279, pr115279⟩
private theorem pr115309 : PrimeCertificate 115309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3203]) (by decide +kernel)
def pv115309 : PrimeValue := ⟨115309, pr115309⟩
private theorem pr115319 : PrimeCertificate 115319 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv8237]) (by decide +kernel)
def pv115319 : PrimeValue := ⟨115319, pr115319⟩
private theorem pr115321 : PrimeCertificate 115321 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv31]) (by decide +kernel)
def pv115321 : PrimeValue := ⟨115321, pr115321⟩
private theorem pr115327 : PrimeCertificate 115327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv149]) (by decide +kernel)
def pv115327 : PrimeValue := ⟨115327, pr115327⟩
private theorem pr115331 : PrimeCertificate 115331 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv19,pv607]) (by decide +kernel)
def pv115331 : PrimeValue := ⟨115331, pr115331⟩
private theorem pr115337 : PrimeCertificate 115337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv1109]) (by decide +kernel)
def pv115337 : PrimeValue := ⟨115337, pr115337⟩
private theorem pr115343 : PrimeCertificate 115343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv101,pv571]) (by decide +kernel)
def pv115343 : PrimeValue := ⟨115343, pr115343⟩
private theorem pr115361 : PrimeCertificate 115361 :=
  certifyPrime (q := pv41) (ls := [pv2,pv5,pv7,pv103]) (by decide +kernel)
def pv115361 : PrimeValue := ⟨115361, pr115361⟩
private theorem pr115363 : PrimeCertificate 115363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv17,pv29]) (by decide +kernel)
def pv115363 : PrimeValue := ⟨115363, pr115363⟩
private theorem pr115399 : PrimeCertificate 115399 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv2137]) (by decide +kernel)
def pv115399 : PrimeValue := ⟨115399, pr115399⟩
private theorem pr115421 : PrimeCertificate 115421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv199]) (by decide +kernel)
def pv115421 : PrimeValue := ⟨115421, pr115421⟩
private theorem pr115429 : PrimeCertificate 115429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9619]) (by decide +kernel)
def pv115429 : PrimeValue := ⟨115429, pr115429⟩
private theorem pr115459 : PrimeCertificate 115459 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv2749]) (by decide +kernel)
def pv115459 : PrimeValue := ⟨115459, pr115459⟩
private theorem pr115469 : PrimeCertificate 115469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28867]) (by decide +kernel)
def pv115469 : PrimeValue := ⟨115469, pr115469⟩
private theorem pr115471 : PrimeCertificate 115471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv1283]) (by decide +kernel)
def pv115471 : PrimeValue := ⟨115471, pr115471⟩
private theorem pr115499 : PrimeCertificate 115499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv43,pv79]) (by decide +kernel)
def pv115499 : PrimeValue := ⟨115499, pr115499⟩
private theorem pr115513 : PrimeCertificate 115513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv4813]) (by decide +kernel)
def pv115513 : PrimeValue := ⟨115513, pr115513⟩
private theorem pr115523 : PrimeCertificate 115523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv59,pv89]) (by decide +kernel)
def pv115523 : PrimeValue := ⟨115523, pr115523⟩
private theorem pr115547 : PrimeCertificate 115547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57773]) (by decide +kernel)
def pv115547 : PrimeValue := ⟨115547, pr115547⟩
private theorem pr115553 : PrimeCertificate 115553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv157]) (by decide +kernel)
def pv115553 : PrimeValue := ⟨115553, pr115553⟩
private theorem pr115561 : PrimeCertificate 115561 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv115561 : PrimeValue := ⟨115561, pr115561⟩
private theorem pr115571 : PrimeCertificate 115571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv127]) (by decide +kernel)
def pv115571 : PrimeValue := ⟨115571, pr115571⟩
private theorem pr115589 : PrimeCertificate 115589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv37,pv71]) (by decide +kernel)
def pv115589 : PrimeValue := ⟨115589, pr115589⟩
private theorem pr115597 : PrimeCertificate 115597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv115597 : PrimeValue := ⟨115597, pr115597⟩
private theorem pr115601 : PrimeCertificate 115601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv115601 : PrimeValue := ⟨115601, pr115601⟩
private theorem pr115603 : PrimeCertificate 115603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19267]) (by decide +kernel)
def pv115603 : PrimeValue := ⟨115603, pr115603⟩
private theorem pr115613 : PrimeCertificate 115613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv4129]) (by decide +kernel)
def pv115613 : PrimeValue := ⟨115613, pr115613⟩
private theorem pr115631 : PrimeCertificate 115631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv31,pv373]) (by decide +kernel)
def pv115631 : PrimeValue := ⟨115631, pr115631⟩
private theorem pr115637 : PrimeCertificate 115637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28909]) (by decide +kernel)
def pv115637 : PrimeValue := ⟨115637, pr115637⟩
private theorem pr115657 : PrimeCertificate 115657 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv61,pv79]) (by decide +kernel)
def pv115657 : PrimeValue := ⟨115657, pr115657⟩
private theorem pr115663 : PrimeCertificate 115663 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv37,pv521]) (by decide +kernel)
def pv115663 : PrimeValue := ⟨115663, pr115663⟩
private theorem pr115679 : PrimeCertificate 115679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv57839]) (by decide +kernel)
def pv115679 : PrimeValue := ⟨115679, pr115679⟩
private theorem pr115693 : PrimeCertificate 115693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv311]) (by decide +kernel)
def pv115693 : PrimeValue := ⟨115693, pr115693⟩
private theorem pr115733 : PrimeCertificate 115733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv28933]) (by decide +kernel)
def pv115733 : PrimeValue := ⟨115733, pr115733⟩
private theorem pr115741 : PrimeCertificate 115741 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv643]) (by decide +kernel)
def pv115741 : PrimeValue := ⟨115741, pr115741⟩
private theorem pr115751 : PrimeCertificate 115751 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv463]) (by decide +kernel)
def pv115751 : PrimeValue := ⟨115751, pr115751⟩
private theorem pr115757 : PrimeCertificate 115757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv673]) (by decide +kernel)
def pv115757 : PrimeValue := ⟨115757, pr115757⟩
private theorem pr115769 : PrimeCertificate 115769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv499]) (by decide +kernel)
def pv115769 : PrimeValue := ⟨115769, pr115769⟩
private theorem pr115771 : PrimeCertificate 115771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17,pv227]) (by decide +kernel)
def pv115771 : PrimeValue := ⟨115771, pr115771⟩
private theorem pr115777 : PrimeCertificate 115777 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv115777 : PrimeValue := ⟨115777, pr115777⟩
private theorem pr115781 : PrimeCertificate 115781 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv827]) (by decide +kernel)
def pv115781 : PrimeValue := ⟨115781, pr115781⟩
private theorem pr115783 : PrimeCertificate 115783 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv23,pv839]) (by decide +kernel)
def pv115783 : PrimeValue := ⟨115783, pr115783⟩
private theorem pr115793 : PrimeCertificate 115793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7237]) (by decide +kernel)
def pv115793 : PrimeValue := ⟨115793, pr115793⟩
private theorem pr115807 : PrimeCertificate 115807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19301]) (by decide +kernel)
def pv115807 : PrimeValue := ⟨115807, pr115807⟩
private theorem pr115811 : PrimeCertificate 115811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv37,pv313]) (by decide +kernel)
def pv115811 : PrimeValue := ⟨115811, pr115811⟩
private theorem pr115823 : PrimeCertificate 115823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv8273]) (by decide +kernel)
def pv115823 : PrimeValue := ⟨115823, pr115823⟩
private theorem pr115831 : PrimeCertificate 115831 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv115831 : PrimeValue := ⟨115831, pr115831⟩
private theorem pr115849 : PrimeCertificate 115849 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1609]) (by decide +kernel)
def pv115849 : PrimeValue := ⟨115849, pr115849⟩
private theorem pr115859 : PrimeCertificate 115859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv1093]) (by decide +kernel)
def pv115859 : PrimeValue := ⟨115859, pr115859⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
