/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table134
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables01/Table134.pv864103
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table014
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table019
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table024
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table025
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table034
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table051
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table103
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table104
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table105

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr864103 : PrimeCertificate 864103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv79,pv1823]) (by decide +kernel)
def pv864103 : PrimeValue := ⟨864103, pr864103⟩
private theorem pr864277 : PrimeCertificate 864277 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv10289]) (by decide +kernel)
def pv864277 : PrimeValue := ⟨864277, pr864277⟩
private theorem pr864307 : PrimeCertificate 864307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv48017]) (by decide +kernel)
def pv864307 : PrimeValue := ⟨864307, pr864307⟩
private theorem pr864491 : PrimeCertificate 864491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv29,pv271]) (by decide +kernel)
def pv864491 : PrimeValue := ⟨864491, pr864491⟩
private theorem pr864551 : PrimeCertificate 864551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17291]) (by decide +kernel)
def pv864551 : PrimeValue := ⟨864551, pr864551⟩
private theorem pr864583 : PrimeCertificate 864583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv103,pv1399]) (by decide +kernel)
def pv864583 : PrimeValue := ⟨864583, pr864583⟩
private theorem pr864641 : PrimeCertificate 864641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv193]) (by decide +kernel)
def pv864641 : PrimeValue := ⟨864641, pr864641⟩
private theorem pr864733 : PrimeCertificate 864733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv6551]) (by decide +kernel)
def pv864733 : PrimeValue := ⟨864733, pr864733⟩
private theorem pr864911 : PrimeCertificate 864911 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv86491]) (by decide +kernel)
def pv864911 : PrimeValue := ⟨864911, pr864911⟩
private theorem pr864979 : PrimeCertificate 864979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv144163]) (by decide +kernel)
def pv864979 : PrimeValue := ⟨864979, pr864979⟩
private theorem pr865043 : PrimeCertificate 865043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv523,pv827]) (by decide +kernel)
def pv865043 : PrimeValue := ⟨865043, pr865043⟩
private theorem pr865103 : PrimeCertificate 865103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv61,pv1013]) (by decide +kernel)
def pv865103 : PrimeValue := ⟨865103, pr865103⟩
private theorem pr865253 : PrimeCertificate 865253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv199,pv1087]) (by decide +kernel)
def pv865253 : PrimeValue := ⟨865253, pr865253⟩
private theorem pr865327 : PrimeCertificate 865327 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv1873]) (by decide +kernel)
def pv865327 : PrimeValue := ⟨865327, pr865327⟩
private theorem pr865339 : PrimeCertificate 865339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv144223]) (by decide +kernel)
def pv865339 : PrimeValue := ⟨865339, pr865339⟩
private theorem pr865363 : PrimeCertificate 865363 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv233,pv619]) (by decide +kernel)
def pv865363 : PrimeValue := ⟨865363, pr865363⟩
private theorem pr865499 : PrimeCertificate 865499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv432749]) (by decide +kernel)
def pv865499 : PrimeValue := ⟨865499, pr865499⟩
private theorem pr865643 : PrimeCertificate 865643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv269,pv1609]) (by decide +kernel)
def pv865643 : PrimeValue := ⟨865643, pr865643⟩
private theorem pr865747 : PrimeCertificate 865747 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv6871]) (by decide +kernel)
def pv865747 : PrimeValue := ⟨865747, pr865747⟩
private theorem pr865769 : PrimeCertificate 865769 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv3491]) (by decide +kernel)
def pv865769 : PrimeValue := ⟨865769, pr865769⟩
private theorem pr865819 : PrimeCertificate 865819 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv103,pv467]) (by decide +kernel)
def pv865819 : PrimeValue := ⟨865819, pr865819⟩
private theorem pr865829 : PrimeCertificate 865829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv233,pv929]) (by decide +kernel)
def pv865829 : PrimeValue := ⟨865829, pr865829⟩
private theorem pr866029 : PrimeCertificate 866029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv72169]) (by decide +kernel)
def pv866029 : PrimeValue := ⟨866029, pr866029⟩
private theorem pr866083 : PrimeCertificate 866083 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv17,pv1213]) (by decide +kernel)
def pv866083 : PrimeValue := ⟨866083, pr866083⟩
private theorem pr866231 : PrimeCertificate 866231 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv29,pv103]) (by decide +kernel)
def pv866231 : PrimeValue := ⟨866231, pr866231⟩
private theorem pr866329 : PrimeCertificate 866329 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv36097]) (by decide +kernel)
def pv866329 : PrimeValue := ⟨866329, pr866329⟩
private theorem pr866399 : PrimeCertificate 866399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv13,pv47,pv709]) (by decide +kernel)
def pv866399 : PrimeValue := ⟨866399, pr866399⟩
private theorem pr866639 : PrimeCertificate 866639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv433319]) (by decide +kernel)
def pv866639 : PrimeValue := ⟨866639, pr866639⟩
private theorem pr866653 : PrimeCertificate 866653 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv72221]) (by decide +kernel)
def pv866653 : PrimeValue := ⟨866653, pr866653⟩
private theorem pr866683 : PrimeCertificate 866683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv541]) (by decide +kernel)
def pv866683 : PrimeValue := ⟨866683, pr866683⟩
private theorem pr866707 : PrimeCertificate 866707 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv144451]) (by decide +kernel)
def pv866707 : PrimeValue := ⟨866707, pr866707⟩
private theorem pr866759 : PrimeCertificate 866759 :=
  certifyPrime (q := pv11) (ls := [pv2,pv191,pv2269]) (by decide +kernel)
def pv866759 : PrimeValue := ⟨866759, pr866759⟩
private theorem pr866819 : PrimeCertificate 866819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv22811]) (by decide +kernel)
def pv866819 : PrimeValue := ⟨866819, pr866819⟩
private theorem pr866917 : PrimeCertificate 866917 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv349]) (by decide +kernel)
def pv866917 : PrimeValue := ⟨866917, pr866917⟩
private theorem pr867007 : PrimeCertificate 867007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv983]) (by decide +kernel)
def pv867007 : PrimeValue := ⟨867007, pr867007⟩
private theorem pr867011 : PrimeCertificate 867011 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv277,pv313]) (by decide +kernel)
def pv867011 : PrimeValue := ⟨867011, pr867011⟩
private theorem pr867253 : PrimeCertificate 867253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv72271]) (by decide +kernel)
def pv867253 : PrimeValue := ⟨867253, pr867253⟩
private theorem pr867343 : PrimeCertificate 867343 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv107,pv193]) (by decide +kernel)
def pv867343 : PrimeValue := ⟨867343, pr867343⟩
private theorem pr867413 : PrimeCertificate 867413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv2383]) (by decide +kernel)
def pv867413 : PrimeValue := ⟨867413, pr867413⟩
private theorem pr867553 : PrimeCertificate 867553 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv1291]) (by decide +kernel)
def pv867553 : PrimeValue := ⟨867553, pr867553⟩
private theorem pr867619 : PrimeCertificate 867619 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16067]) (by decide +kernel)
def pv867619 : PrimeValue := ⟨867619, pr867619⟩
private theorem pr867829 : PrimeCertificate 867829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv5563]) (by decide +kernel)
def pv867829 : PrimeValue := ⟨867829, pr867829⟩
private theorem pr867913 : PrimeCertificate 867913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29,pv43]) (by decide +kernel)
def pv867913 : PrimeValue := ⟨867913, pr867913⟩
private theorem pr867943 : PrimeCertificate 867943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv16073]) (by decide +kernel)
def pv867943 : PrimeValue := ⟨867943, pr867943⟩
private theorem pr867959 : PrimeCertificate 867959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv13,pv19,pv251]) (by decide +kernel)
def pv867959 : PrimeValue := ⟨867959, pr867959⟩
private theorem pr868069 : PrimeCertificate 868069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv24113]) (by decide +kernel)
def pv868069 : PrimeValue := ⟨868069, pr868069⟩
private theorem pr868123 : PrimeCertificate 868123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv2837]) (by decide +kernel)
def pv868123 : PrimeValue := ⟨868123, pr868123⟩
private theorem pr868151 : PrimeCertificate 868151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv97,pv179]) (by decide +kernel)
def pv868151 : PrimeValue := ⟨868151, pr868151⟩
private theorem pr868229 : PrimeCertificate 868229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv217057]) (by decide +kernel)
def pv868229 : PrimeValue := ⟨868229, pr868229⟩
private theorem pr868379 : PrimeCertificate 868379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8861]) (by decide +kernel)
def pv868379 : PrimeValue := ⟨868379, pr868379⟩
private theorem pr868489 : PrimeCertificate 868489 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv36187]) (by decide +kernel)
def pv868489 : PrimeValue := ⟨868489, pr868489⟩
private theorem pr868529 : PrimeCertificate 868529 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv2857]) (by decide +kernel)
def pv868529 : PrimeValue := ⟨868529, pr868529⟩
private theorem pr868603 : PrimeCertificate 868603 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv20681]) (by decide +kernel)
def pv868603 : PrimeValue := ⟨868603, pr868603⟩
private theorem pr868669 : PrimeCertificate 868669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv191,pv379]) (by decide +kernel)
def pv868669 : PrimeValue := ⟨868669, pr868669⟩
private theorem pr868739 : PrimeCertificate 868739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv33413]) (by decide +kernel)
def pv868739 : PrimeValue := ⟨868739, pr868739⟩
private theorem pr868799 : PrimeCertificate 868799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv62057]) (by decide +kernel)
def pv868799 : PrimeValue := ⟨868799, pr868799⟩
private theorem pr868867 : PrimeCertificate 868867 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv179,pv809]) (by decide +kernel)
def pv868867 : PrimeValue := ⟨868867, pr868867⟩
private theorem pr868939 : PrimeCertificate 868939 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv17,pv1217]) (by decide +kernel)
def pv868939 : PrimeValue := ⟨868939, pr868939⟩
private theorem pr868943 : PrimeCertificate 868943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv434471]) (by decide +kernel)
def pv868943 : PrimeValue := ⟨868943, pr868943⟩
private theorem pr869021 : PrimeCertificate 869021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43451]) (by decide +kernel)
def pv869021 : PrimeValue := ⟨869021, pr869021⟩
private theorem pr869119 : PrimeCertificate 869119 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv41,pv3533]) (by decide +kernel)
def pv869119 : PrimeValue := ⟨869119, pr869119⟩
private theorem pr869153 : PrimeCertificate 869153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv157,pv173]) (by decide +kernel)
def pv869153 : PrimeValue := ⟨869153, pr869153⟩
private theorem pr869317 : PrimeCertificate 869317 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv79,pv131]) (by decide +kernel)
def pv869317 : PrimeValue := ⟨869317, pr869317⟩
private theorem pr869369 : PrimeCertificate 869369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv271,pv401]) (by decide +kernel)
def pv869369 : PrimeValue := ⟨869369, pr869369⟩
private theorem pr869399 : PrimeCertificate 869399 :=
  certifyPrime (q := pv11) (ls := [pv2,pv434699]) (by decide +kernel)
def pv869399 : PrimeValue := ⟨869399, pr869399⟩
private theorem pr869413 : PrimeCertificate 869413 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv53,pv1367]) (by decide +kernel)
def pv869413 : PrimeValue := ⟨869413, pr869413⟩
private theorem pr869467 : PrimeCertificate 869467 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv71,pv157]) (by decide +kernel)
def pv869467 : PrimeValue := ⟨869467, pr869467⟩
private theorem pr869471 : PrimeCertificate 869471 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv12421]) (by decide +kernel)
def pv869471 : PrimeValue := ⟨869471, pr869471⟩
private theorem pr869863 : PrimeCertificate 869863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv139,pv149]) (by decide +kernel)
def pv869863 : PrimeValue := ⟨869863, pr869863⟩
private theorem pr869893 : PrimeCertificate 869893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv71,pv1021]) (by decide +kernel)
def pv869893 : PrimeValue := ⟨869893, pr869893⟩
private theorem pr869983 : PrimeCertificate 869983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv61,pv2377]) (by decide +kernel)
def pv869983 : PrimeValue := ⟨869983, pr869983⟩
private theorem pr870059 : PrimeCertificate 870059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv29,pv2143]) (by decide +kernel)
def pv870059 : PrimeValue := ⟨870059, pr870059⟩
private theorem pr870109 : PrimeCertificate 870109 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv31,pv2339]) (by decide +kernel)
def pv870109 : PrimeValue := ⟨870109, pr870109⟩
private theorem pr870127 : PrimeCertificate 870127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv145021]) (by decide +kernel)
def pv870127 : PrimeValue := ⟨870127, pr870127⟩
private theorem pr870169 : PrimeCertificate 870169 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv2789]) (by decide +kernel)
def pv870169 : PrimeValue := ⟨870169, pr870169⟩
private theorem pr870367 : PrimeCertificate 870367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv17,pv23,pv53]) (by decide +kernel)
def pv870367 : PrimeValue := ⟨870367, pr870367⟩
private theorem pr870547 : PrimeCertificate 870547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv145091]) (by decide +kernel)
def pv870547 : PrimeValue := ⟨870547, pr870547⟩
private theorem pr870643 : PrimeCertificate 870643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv701]) (by decide +kernel)
def pv870643 : PrimeValue := ⟨870643, pr870643⟩
private theorem pr870773 : PrimeCertificate 870773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv137,pv227]) (by decide +kernel)
def pv870773 : PrimeValue := ⟨870773, pr870773⟩
private theorem pr870853 : PrimeCertificate 870853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv2341]) (by decide +kernel)
def pv870853 : PrimeValue := ⟨870853, pr870853⟩
private theorem pr871289 : PrimeCertificate 871289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv9901]) (by decide +kernel)
def pv871289 : PrimeValue := ⟨871289, pr871289⟩
private theorem pr871571 : PrimeCertificate 871571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv12451]) (by decide +kernel)
def pv871571 : PrimeValue := ⟨871571, pr871571⟩
private theorem pr871589 : PrimeCertificate 871589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv193,pv1129]) (by decide +kernel)
def pv871589 : PrimeValue := ⟨871589, pr871589⟩
private theorem pr871679 : PrimeCertificate 871679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv435839]) (by decide +kernel)
def pv871679 : PrimeValue := ⟨871679, pr871679⟩
private theorem pr871763 : PrimeCertificate 871763 :=
  certifyPrime (q := pv2) (ls := [pv2,pv435881]) (by decide +kernel)
def pv871763 : PrimeValue := ⟨871763, pr871763⟩
private theorem pr871901 : PrimeCertificate 871901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8719]) (by decide +kernel)
def pv871901 : PrimeValue := ⟨871901, pr871901⟩
private theorem pr872429 : PrimeCertificate 872429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv218107]) (by decide +kernel)
def pv872429 : PrimeValue := ⟨872429, pr872429⟩
private theorem pr872843 : PrimeCertificate 872843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv101,pv149]) (by decide +kernel)
def pv872843 : PrimeValue := ⟨872843, pr872843⟩
private theorem pr873083 : PrimeCertificate 873083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv59,pv151]) (by decide +kernel)
def pv873083 : PrimeValue := ⟨873083, pr873083⟩
private theorem pr873209 : PrimeCertificate 873209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv503]) (by decide +kernel)
def pv873209 : PrimeValue := ⟨873209, pr873209⟩
private theorem pr873293 : PrimeCertificate 873293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31189]) (by decide +kernel)
def pv873293 : PrimeValue := ⟨873293, pr873293⟩
private theorem pr873461 : PrimeCertificate 873461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv17,pv367]) (by decide +kernel)
def pv873461 : PrimeValue := ⟨873461, pr873461⟩
private theorem pr873539 : PrimeCertificate 873539 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv15061]) (by decide +kernel)
def pv873539 : PrimeValue := ⟨873539, pr873539⟩
private theorem pr873863 : PrimeCertificate 873863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv23,pv157]) (by decide +kernel)
def pv873863 : PrimeValue := ⟨873863, pr873863⟩
private theorem pr873989 : PrimeCertificate 873989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv151,pv1447]) (by decide +kernel)
def pv873989 : PrimeValue := ⟨873989, pr873989⟩
private theorem pr874001 : PrimeCertificate 874001 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv23]) (by decide +kernel)
def pv874001 : PrimeValue := ⟨874001, pr874001⟩
private theorem pr874229 : PrimeCertificate 874229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv11503]) (by decide +kernel)
def pv874229 : PrimeValue := ⟨874229, pr874229⟩
private theorem pr874619 : PrimeCertificate 874619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv61,pv67,pv107]) (by decide +kernel)
def pv874619 : PrimeValue := ⟨874619, pr874619⟩
private theorem pr874721 : PrimeCertificate 874721 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv11,pv71]) (by decide +kernel)
def pv874721 : PrimeValue := ⟨874721, pr874721⟩
private theorem pr874823 : PrimeCertificate 874823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv33647]) (by decide +kernel)
def pv874823 : PrimeValue := ⟨874823, pr874823⟩
private theorem pr874889 : PrimeCertificate 874889 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv17,pv919]) (by decide +kernel)
def pv874889 : PrimeValue := ⟨874889, pr874889⟩
private theorem pr875141 : PrimeCertificate 875141 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv47]) (by decide +kernel)
def pv875141 : PrimeValue := ⟨875141, pr875141⟩
private theorem pr875261 : PrimeCertificate 875261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv107,pv409]) (by decide +kernel)
def pv875261 : PrimeValue := ⟨875261, pr875261⟩
private theorem pr875519 : PrimeCertificate 875519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv23,pv2719]) (by decide +kernel)
def pv875519 : PrimeValue := ⟨875519, pr875519⟩
private theorem pr875663 : PrimeCertificate 875663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv367,pv1193]) (by decide +kernel)
def pv875663 : PrimeValue := ⟨875663, pr875663⟩
private theorem pr875783 : PrimeCertificate 875783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv397,pv1103]) (by decide +kernel)
def pv875783 : PrimeValue := ⟨875783, pr875783⟩
private theorem pr876131 : PrimeCertificate 876131 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv87613]) (by decide +kernel)
def pv876131 : PrimeValue := ⟨876131, pr876131⟩
private theorem pr876203 : PrimeCertificate 876203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113,pv3877]) (by decide +kernel)
def pv876203 : PrimeValue := ⟨876203, pr876203⟩
private theorem pr876233 : PrimeCertificate 876233 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv15647]) (by decide +kernel)
def pv876233 : PrimeValue := ⟨876233, pr876233⟩
private theorem pr876329 : PrimeCertificate 876329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109541]) (by decide +kernel)
def pv876329 : PrimeValue := ⟨876329, pr876329⟩
private theorem pr876569 : PrimeCertificate 876569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv1423]) (by decide +kernel)
def pv876569 : PrimeValue := ⟨876569, pr876569⟩
private theorem pr876719 : PrimeCertificate 876719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv557,pv787]) (by decide +kernel)
def pv876719 : PrimeValue := ⟨876719, pr876719⟩
private theorem pr876971 : PrimeCertificate 876971 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv87697]) (by decide +kernel)
def pv876971 : PrimeValue := ⟨876971, pr876971⟩
private theorem pr877073 : PrimeCertificate 877073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv41,pv191]) (by decide +kernel)
def pv877073 : PrimeValue := ⟨877073, pr877073⟩
private theorem pr877223 : PrimeCertificate 877223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv438611]) (by decide +kernel)
def pv877223 : PrimeValue := ⟨877223, pr877223⟩
private theorem pr877469 : PrimeCertificate 877469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv53,pv4139]) (by decide +kernel)
def pv877469 : PrimeValue := ⟨877469, pr877469⟩
private theorem pr877853 : PrimeCertificate 877853 :=
  certifyPrime (q := pv2) (ls := [pv2,pv219463]) (by decide +kernel)
def pv877853 : PrimeValue := ⟨877853, pr877853⟩
private theorem pr878099 : PrimeCertificate 878099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv33773]) (by decide +kernel)
def pv878099 : PrimeValue := ⟨878099, pr878099⟩
private theorem pr878159 : PrimeCertificate 878159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv37,pv11867]) (by decide +kernel)
def pv878159 : PrimeValue := ⟨878159, pr878159⟩
private theorem pr878411 : PrimeCertificate 878411 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv29,pv233]) (by decide +kernel)
def pv878411 : PrimeValue := ⟨878411, pr878411⟩
private theorem pr878681 : PrimeCertificate 878681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1997]) (by decide +kernel)
def pv878681 : PrimeValue := ⟨878681, pr878681⟩
private theorem pr878831 : PrimeCertificate 878831 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv23,pv3821]) (by decide +kernel)
def pv878831 : PrimeValue := ⟨878831, pr878831⟩
private theorem pr879089 : PrimeCertificate 879089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv47,pv167]) (by decide +kernel)
def pv879089 : PrimeValue := ⟨879089, pr879089⟩
private theorem pr879143 : PrimeCertificate 879143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv89,pv449]) (by decide +kernel)
def pv879143 : PrimeValue := ⟨879143, pr879143⟩
private theorem pr879269 : PrimeCertificate 879269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv37,pv457]) (by decide +kernel)
def pv879269 : PrimeValue := ⟨879269, pr879269⟩
private theorem pr879449 : PrimeCertificate 879449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv211,pv521]) (by decide +kernel)
def pv879449 : PrimeValue := ⟨879449, pr879449⟩
private theorem pr879689 : PrimeCertificate 879689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv109961]) (by decide +kernel)
def pv879689 : PrimeValue := ⟨879689, pr879689⟩
private theorem pr879713 : PrimeCertificate 879713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv743]) (by decide +kernel)
def pv879713 : PrimeValue := ⟨879713, pr879713⟩
private theorem pr879821 : PrimeCertificate 879821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43991]) (by decide +kernel)
def pv879821 : PrimeValue := ⟨879821, pr879821⟩
private theorem pr879881 : PrimeCertificate 879881 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv21997]) (by decide +kernel)
def pv879881 : PrimeValue := ⟨879881, pr879881⟩
private theorem pr880133 : PrimeCertificate 880133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv83,pv241]) (by decide +kernel)
def pv880133 : PrimeValue := ⟨880133, pr880133⟩
private theorem pr880283 : PrimeCertificate 880283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv33857]) (by decide +kernel)
def pv880283 : PrimeValue := ⟨880283, pr880283⟩
private theorem pr880349 : PrimeCertificate 880349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv23,pv1367]) (by decide +kernel)
def pv880349 : PrimeValue := ⟨880349, pr880349⟩
private theorem pr880361 : PrimeCertificate 880361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv1693]) (by decide +kernel)
def pv880361 : PrimeValue := ⟨880361, pr880361⟩
private theorem pr880553 : PrimeCertificate 880553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv110069]) (by decide +kernel)
def pv880553 : PrimeValue := ⟨880553, pr880553⟩
private theorem pr880703 : PrimeCertificate 880703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv25903]) (by decide +kernel)
def pv880703 : PrimeValue := ⟨880703, pr880703⟩
private theorem pr880751 : PrimeCertificate 880751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv13,pv271]) (by decide +kernel)
def pv880751 : PrimeValue := ⟨880751, pr880751⟩
private theorem pr881249 : PrimeCertificate 881249 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27539]) (by decide +kernel)
def pv881249 : PrimeValue := ⟨881249, pr881249⟩
private theorem pr881711 : PrimeCertificate 881711 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv37,pv2383]) (by decide +kernel)
def pv881711 : PrimeValue := ⟨881711, pr881711⟩
private theorem pr881729 : PrimeCertificate 881729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv599]) (by decide +kernel)
def pv881729 : PrimeValue := ⟨881729, pr881729⟩
private theorem pr881813 : PrimeCertificate 881813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv2477]) (by decide +kernel)
def pv881813 : PrimeValue := ⟨881813, pr881813⟩
private theorem pr882239 : PrimeCertificate 882239 :=
  certifyPrime (q := pv13) (ls := [pv2,pv7,pv29,pv41,pv53]) (by decide +kernel)
def pv882239 : PrimeValue := ⟨882239, pr882239⟩
private theorem pr882389 : PrimeCertificate 882389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv71,pv239]) (by decide +kernel)
def pv882389 : PrimeValue := ⟨882389, pr882389⟩
private theorem pr882449 : PrimeCertificate 882449 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv7879]) (by decide +kernel)
def pv882449 : PrimeValue := ⟨882449, pr882449⟩
private theorem pr882593 : PrimeCertificate 882593 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27581]) (by decide +kernel)
def pv882593 : PrimeValue := ⟨882593, pr882593⟩
private theorem pr882701 : PrimeCertificate 882701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv13,pv97]) (by decide +kernel)
def pv882701 : PrimeValue := ⟨882701, pr882701⟩
private theorem pr882779 : PrimeCertificate 882779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv19,pv1787]) (by decide +kernel)
def pv882779 : PrimeValue := ⟨882779, pr882779⟩
private theorem pr882851 : PrimeCertificate 882851 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17657]) (by decide +kernel)
def pv882851 : PrimeValue := ⟨882851, pr882851⟩
private theorem pr883049 : PrimeCertificate 883049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv43,pv151]) (by decide +kernel)
def pv883049 : PrimeValue := ⟨883049, pr883049⟩
private theorem pr883061 : PrimeCertificate 883061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv67,pv659]) (by decide +kernel)
def pv883061 : PrimeValue := ⟨883061, pr883061⟩
private theorem pr883121 : PrimeCertificate 883121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv83]) (by decide +kernel)
def pv883121 : PrimeValue := ⟨883121, pr883121⟩
private theorem pr883163 : PrimeCertificate 883163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv199,pv317]) (by decide +kernel)
def pv883163 : PrimeValue := ⟨883163, pr883163⟩
private theorem pr883229 : PrimeCertificate 883229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv220807]) (by decide +kernel)
def pv883229 : PrimeValue := ⟨883229, pr883229⟩
private theorem pr883331 : PrimeCertificate 883331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv12619]) (by decide +kernel)
def pv883331 : PrimeValue := ⟨883331, pr883331⟩
private theorem pr883451 : PrimeCertificate 883451 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17669]) (by decide +kernel)
def pv883451 : PrimeValue := ⟨883451, pr883451⟩
private theorem pr883691 : PrimeCertificate 883691 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv4651]) (by decide +kernel)
def pv883691 : PrimeValue := ⟨883691, pr883691⟩
private theorem pr883703 : PrimeCertificate 883703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv59,pv7489]) (by decide +kernel)
def pv883703 : PrimeValue := ⟨883703, pr883703⟩
private theorem pr883973 : PrimeCertificate 883973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv991]) (by decide +kernel)
def pv883973 : PrimeValue := ⟨883973, pr883973⟩
private theorem pr883979 : PrimeCertificate 883979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv15241]) (by decide +kernel)
def pv883979 : PrimeValue := ⟨883979, pr883979⟩
private theorem pr884111 : PrimeCertificate 884111 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv88411]) (by decide +kernel)
def pv884111 : PrimeValue := ⟨884111, pr884111⟩
private theorem pr884171 : PrimeCertificate 884171 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv743]) (by decide +kernel)
def pv884171 : PrimeValue := ⟨884171, pr884171⟩
private theorem pr884183 : PrimeCertificate 884183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv31,pv1097]) (by decide +kernel)
def pv884183 : PrimeValue := ⟨884183, pr884183⟩
private theorem pr884309 : PrimeCertificate 884309 :=
  certifyPrime (q := pv2) (ls := [pv2,pv221077]) (by decide +kernel)
def pv884309 : PrimeValue := ⟨884309, pr884309⟩
private theorem pr884363 : PrimeCertificate 884363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv442181]) (by decide +kernel)
def pv884363 : PrimeValue := ⟨884363, pr884363⟩
private theorem pr884483 : PrimeCertificate 884483 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv4969]) (by decide +kernel)
def pv884483 : PrimeValue := ⟨884483, pr884483⟩
private theorem pr884699 : PrimeCertificate 884699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv10789]) (by decide +kernel)
def pv884699 : PrimeValue := ⟨884699, pr884699⟩
private theorem pr884813 : PrimeCertificate 884813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv221203]) (by decide +kernel)
def pv884813 : PrimeValue := ⟨884813, pr884813⟩
private theorem pr885359 : PrimeCertificate 885359 :=
  certifyPrime (q := pv13) (ls := [pv2,pv149,pv2971]) (by decide +kernel)
def pv885359 : PrimeValue := ⟨885359, pr885359⟩
private theorem pr885551 : PrimeCertificate 885551 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv89,pv199]) (by decide +kernel)
def pv885551 : PrimeValue := ⟨885551, pr885551⟩
private theorem pr885611 : PrimeCertificate 885611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv83,pv97]) (by decide +kernel)
def pv885611 : PrimeValue := ⟨885611, pr885611⟩
private theorem pr885803 : PrimeCertificate 885803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv26053]) (by decide +kernel)
def pv885803 : PrimeValue := ⟨885803, pr885803⟩
private theorem pr885893 : PrimeCertificate 885893 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv29,pv1091]) (by decide +kernel)
def pv885893 : PrimeValue := ⟨885893, pr885893⟩
private theorem pr886043 : PrimeCertificate 886043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv461]) (by decide +kernel)
def pv886043 : PrimeValue := ⟨886043, pr886043⟩
private theorem pr886163 : PrimeCertificate 886163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv563,pv787]) (by decide +kernel)
def pv886163 : PrimeValue := ⟨886163, pr886163⟩
private theorem pr886199 : PrimeCertificate 886199 :=
  certifyPrime (q := pv17) (ls := [pv2,pv19,pv23321]) (by decide +kernel)
def pv886199 : PrimeValue := ⟨886199, pr886199⟩
private theorem pr886241 : PrimeCertificate 886241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv29,pv191]) (by decide +kernel)
def pv886241 : PrimeValue := ⟨886241, pr886241⟩
private theorem pr886433 : PrimeCertificate 886433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv27701]) (by decide +kernel)
def pv886433 : PrimeValue := ⟨886433, pr886433⟩
private theorem pr886493 : PrimeCertificate 886493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv221623]) (by decide +kernel)
def pv886493 : PrimeValue := ⟨886493, pr886493⟩
private theorem pr886793 : PrimeCertificate 886793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv110849]) (by decide +kernel)
def pv886793 : PrimeValue := ⟨886793, pr886793⟩
private theorem pr886859 : PrimeCertificate 886859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv63347]) (by decide +kernel)
def pv886859 : PrimeValue := ⟨886859, pr886859⟩
private theorem pr887069 : PrimeCertificate 887069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv2437]) (by decide +kernel)
def pv887069 : PrimeValue := ⟨887069, pr887069⟩
private theorem pr887261 : PrimeCertificate 887261 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv37,pv109]) (by decide +kernel)
def pv887261 : PrimeValue := ⟨887261, pr887261⟩
private theorem pr887291 : PrimeCertificate 887291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv88729]) (by decide +kernel)
def pv887291 : PrimeValue := ⟨887291, pr887291⟩
private theorem pr887333 : PrimeCertificate 887333 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv13049]) (by decide +kernel)
def pv887333 : PrimeValue := ⟨887333, pr887333⟩
private theorem pr887693 : PrimeCertificate 887693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv43,pv397]) (by decide +kernel)
def pv887693 : PrimeValue := ⟨887693, pr887693⟩
private theorem pr887921 : PrimeCertificate 887921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv1009]) (by decide +kernel)
def pv887921 : PrimeValue := ⟨887921, pr887921⟩
private theorem pr888011 : PrimeCertificate 888011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv88801]) (by decide +kernel)
def pv888011 : PrimeValue := ⟨888011, pr888011⟩
private theorem pr888059 : PrimeCertificate 888059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv444029]) (by decide +kernel)
def pv888059 : PrimeValue := ⟨888059, pr888059⟩
private theorem pr888161 : PrimeCertificate 888161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv61]) (by decide +kernel)
def pv888161 : PrimeValue := ⟨888161, pr888161⟩
private theorem pr888389 : PrimeCertificate 888389 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv5417]) (by decide +kernel)
def pv888389 : PrimeValue := ⟨888389, pr888389⟩
private theorem pr888533 : PrimeCertificate 888533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv191,pv1163]) (by decide +kernel)
def pv888533 : PrimeValue := ⟨888533, pr888533⟩
private theorem pr888623 : PrimeCertificate 888623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv63473]) (by decide +kernel)
def pv888623 : PrimeValue := ⟨888623, pr888623⟩
private theorem pr888689 : PrimeCertificate 888689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv67,pv829]) (by decide +kernel)
def pv888689 : PrimeValue := ⟨888689, pr888689⟩
private theorem pr888773 : PrimeCertificate 888773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv222193]) (by decide +kernel)
def pv888773 : PrimeValue := ⟨888773, pr888773⟩
private theorem pr889001 : PrimeCertificate 889001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv127]) (by decide +kernel)
def pv889001 : PrimeValue := ⟨889001, pr889001⟩
private theorem pr889139 : PrimeCertificate 889139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv444569]) (by decide +kernel)
def pv889139 : PrimeValue := ⟨889139, pr889139⟩
private theorem pr889211 : PrimeCertificate 889211 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv12703]) (by decide +kernel)
def pv889211 : PrimeValue := ⟨889211, pr889211⟩
private theorem pr889373 : PrimeCertificate 889373 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv29,pv41]) (by decide +kernel)
def pv889373 : PrimeValue := ⟨889373, pr889373⟩
private theorem pr889439 : PrimeCertificate 889439 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv40429]) (by decide +kernel)
def pv889439 : PrimeValue := ⟨889439, pr889439⟩
private theorem pr889481 : PrimeCertificate 889481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv37,pv601]) (by decide +kernel)
def pv889481 : PrimeValue := ⟨889481, pr889481⟩
private theorem pr889673 : PrimeCertificate 889673 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv15887]) (by decide +kernel)
def pv889673 : PrimeValue := ⟨889673, pr889673⟩
private theorem pr890003 : PrimeCertificate 890003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv445001]) (by decide +kernel)
def pv890003 : PrimeValue := ⟨890003, pr890003⟩
private theorem pr890063 : PrimeCertificate 890063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv445031]) (by decide +kernel)
def pv890063 : PrimeValue := ⟨890063, pr890063⟩
private theorem pr890231 : PrimeCertificate 890231 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv11,pv8093]) (by decide +kernel)
def pv890231 : PrimeValue := ⟨890231, pr890231⟩
private theorem pr890303 : PrimeCertificate 890303 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19,pv3347]) (by decide +kernel)
def pv890303 : PrimeValue := ⟨890303, pr890303⟩
private theorem pr890531 : PrimeCertificate 890531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv43,pv109]) (by decide +kernel)
def pv890531 : PrimeValue := ⟨890531, pr890531⟩
private theorem pr890969 : PrimeCertificate 890969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv659]) (by decide +kernel)
def pv890969 : PrimeValue := ⟨890969, pr890969⟩
private theorem pr891101 : PrimeCertificate 891101 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv67]) (by decide +kernel)
def pv891101 : PrimeValue := ⟨891101, pr891101⟩
private theorem pr891251 : PrimeCertificate 891251 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv31]) (by decide +kernel)
def pv891251 : PrimeValue := ⟨891251, pr891251⟩
private theorem pr891323 : PrimeCertificate 891323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv3253]) (by decide +kernel)
def pv891323 : PrimeValue := ⟨891323, pr891323⟩
private theorem pr891521 : PrimeCertificate 891521 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv199]) (by decide +kernel)
def pv891521 : PrimeValue := ⟨891521, pr891521⟩
private theorem pr891659 : PrimeCertificate 891659 :=
  certifyPrime (q := pv2) (ls := [pv2,pv445829]) (by decide +kernel)
def pv891659 : PrimeValue := ⟨891659, pr891659⟩
private theorem pr891749 : PrimeCertificate 891749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv1559]) (by decide +kernel)
def pv891749 : PrimeValue := ⟨891749, pr891749⟩
private theorem pr891809 : PrimeCertificate 891809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv29,pv31]) (by decide +kernel)
def pv891809 : PrimeValue := ⟨891809, pr891809⟩
private theorem pr891899 : PrimeCertificate 891899 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv19,pv479]) (by decide +kernel)
def pv891899 : PrimeValue := ⟨891899, pr891899⟩
private theorem pr892481 : PrimeCertificate 892481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv2789]) (by decide +kernel)
def pv892481 : PrimeValue := ⟨892481, pr892481⟩
private theorem pr892709 : PrimeCertificate 892709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv3331]) (by decide +kernel)
def pv892709 : PrimeValue := ⟨892709, pr892709⟩
private theorem pr892841 : PrimeCertificate 892841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv17,pv101]) (by decide +kernel)
def pv892841 : PrimeValue := ⟨892841, pr892841⟩
private theorem pr892901 : PrimeCertificate 892901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv8929]) (by decide +kernel)
def pv892901 : PrimeValue := ⟨892901, pr892901⟩
private theorem pr892973 : PrimeCertificate 892973 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223243]) (by decide +kernel)
def pv892973 : PrimeValue := ⟨892973, pr892973⟩
private theorem pr893111 : PrimeCertificate 893111 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv31,pv43,pv67]) (by decide +kernel)
def pv893111 : PrimeValue := ⟨893111, pr893111⟩
private theorem pr893219 : PrimeCertificate 893219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv446609]) (by decide +kernel)
def pv893219 : PrimeValue := ⟨893219, pr893219⟩
private theorem pr893339 : PrimeCertificate 893339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv223,pv2003]) (by decide +kernel)
def pv893339 : PrimeValue := ⟨893339, pr893339⟩
private theorem pr893363 : PrimeCertificate 893363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv421,pv1061]) (by decide +kernel)
def pv893363 : PrimeValue := ⟨893363, pr893363⟩
private theorem pr893489 : PrimeCertificate 893489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv55843]) (by decide +kernel)
def pv893489 : PrimeValue := ⟨893489, pr893489⟩
private theorem pr893723 : PrimeCertificate 893723 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv29,pv811]) (by decide +kernel)
def pv893723 : PrimeValue := ⟨893723, pr893723⟩
private theorem pr894011 : PrimeCertificate 894011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv23]) (by decide +kernel)
def pv894011 : PrimeValue := ⟨894011, pr894011⟩
private theorem pr894119 : PrimeCertificate 894119 :=
  certifyPrime (q := pv7) (ls := [pv2,pv167,pv2677]) (by decide +kernel)
def pv894119 : PrimeValue := ⟨894119, pr894119⟩
private theorem pr894221 : PrimeCertificate 894221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv44711]) (by decide +kernel)
def pv894221 : PrimeValue := ⟨894221, pr894221⟩
private theorem pr894329 : PrimeCertificate 894329 :=
  certifyPrime (q := pv3) (ls := [pv2,pv111791]) (by decide +kernel)
def pv894329 : PrimeValue := ⟨894329, pr894329⟩
private theorem pr894431 : PrimeCertificate 894431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv89443]) (by decide +kernel)
def pv894431 : PrimeValue := ⟨894431, pr894431⟩
private theorem pr894581 : PrimeCertificate 894581 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv44729]) (by decide +kernel)
def pv894581 : PrimeValue := ⟨894581, pr894581⟩
private theorem pr894611 : PrimeCertificate 894611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv137,pv653]) (by decide +kernel)
def pv894611 : PrimeValue := ⟨894611, pr894611⟩
private theorem pr894713 : PrimeCertificate 894713 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv1229]) (by decide +kernel)
def pv894713 : PrimeValue := ⟨894713, pr894713⟩
private theorem pr894749 : PrimeCertificate 894749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv61,pv193]) (by decide +kernel)
def pv894749 : PrimeValue := ⟨894749, pr894749⟩
private theorem pr894779 : PrimeCertificate 894779 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv26317]) (by decide +kernel)
def pv894779 : PrimeValue := ⟨894779, pr894779⟩
private theorem pr894791 : PrimeCertificate 894791 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv13,pv6883]) (by decide +kernel)
def pv894791 : PrimeValue := ⟨894791, pr894791⟩
private theorem pr894893 : PrimeCertificate 894893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv409,pv547]) (by decide +kernel)
def pv894893 : PrimeValue := ⟨894893, pr894893⟩
private theorem pr895151 : PrimeCertificate 895151 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv17903]) (by decide +kernel)
def pv895151 : PrimeValue := ⟨895151, pr895151⟩
private theorem pr895241 : PrimeCertificate 895241 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv22381]) (by decide +kernel)
def pv895241 : PrimeValue := ⟨895241, pr895241⟩
private theorem pr895253 : PrimeCertificate 895253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv37,pv263]) (by decide +kernel)
def pv895253 : PrimeValue := ⟨895253, pr895253⟩
private theorem pr895469 : PrimeCertificate 895469 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31981]) (by decide +kernel)
def pv895469 : PrimeValue := ⟨895469, pr895469⟩
private theorem pr895703 : PrimeCertificate 895703 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv5669]) (by decide +kernel)
def pv895703 : PrimeValue := ⟨895703, pr895703⟩
private theorem pr895799 : PrimeCertificate 895799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv26347]) (by decide +kernel)
def pv895799 : PrimeValue := ⟨895799, pr895799⟩
private theorem pr895841 : PrimeCertificate 895841 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv509]) (by decide +kernel)
def pv895841 : PrimeValue := ⟨895841, pr895841⟩
private theorem pr896069 : PrimeCertificate 896069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv83,pv2699]) (by decide +kernel)
def pv896069 : PrimeValue := ⟨896069, pr896069⟩
private theorem pr896123 : PrimeCertificate 896123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv2683]) (by decide +kernel)
def pv896123 : PrimeValue := ⟨896123, pr896123⟩
private theorem pr896561 : PrimeCertificate 896561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1601]) (by decide +kernel)
def pv896561 : PrimeValue := ⟨896561, pr896561⟩
private theorem pr896573 : PrimeCertificate 896573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv47,pv251]) (by decide +kernel)
def pv896573 : PrimeValue := ⟨896573, pr896573⟩
private theorem pr896921 : PrimeCertificate 896921 :=
  certifyPrime (q := pv31) (ls := [pv2,pv5,pv17,pv1319]) (by decide +kernel)
def pv896921 : PrimeValue := ⟨896921, pr896921⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
