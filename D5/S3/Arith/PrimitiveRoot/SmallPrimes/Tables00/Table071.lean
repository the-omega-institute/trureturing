/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table071
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table071.pv224513
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table010
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table015
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table016
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table041
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table042

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr224513 : PrimeCertificate 224513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv877]) (by decide +kernel)
def pv224513 : PrimeValue := ⟨224513, pr224513⟩
private theorem pr224527 : PrimeCertificate 224527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv1627]) (by decide +kernel)
def pv224527 : PrimeValue := ⟨224527, pr224527⟩
private theorem pr224563 : PrimeCertificate 224563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv2879]) (by decide +kernel)
def pv224563 : PrimeValue := ⟨224563, pr224563⟩
private theorem pr224569 : PrimeCertificate 224569 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv3119]) (by decide +kernel)
def pv224569 : PrimeValue := ⟨224569, pr224569⟩
private theorem pr224603 : PrimeCertificate 224603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv61,pv263]) (by decide +kernel)
def pv224603 : PrimeValue := ⟨224603, pr224603⟩
private theorem pr224611 : PrimeCertificate 224611 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7487]) (by decide +kernel)
def pv224611 : PrimeValue := ⟨224611, pr224611⟩
private theorem pr224633 : PrimeCertificate 224633 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv653]) (by decide +kernel)
def pv224633 : PrimeValue := ⟨224633, pr224633⟩
private theorem pr224669 : PrimeCertificate 224669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56167]) (by decide +kernel)
def pv224669 : PrimeValue := ⟨224669, pr224669⟩
private theorem pr224677 : PrimeCertificate 224677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv79]) (by decide +kernel)
def pv224677 : PrimeValue := ⟨224677, pr224677⟩
private theorem pr224683 : PrimeCertificate 224683 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37447]) (by decide +kernel)
def pv224683 : PrimeValue := ⟨224683, pr224683⟩
private theorem pr224699 : PrimeCertificate 224699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv112349]) (by decide +kernel)
def pv224699 : PrimeValue := ⟨224699, pr224699⟩
private theorem pr224729 : PrimeCertificate 224729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv4013]) (by decide +kernel)
def pv224729 : PrimeValue := ⟨224729, pr224729⟩
private theorem pr224759 : PrimeCertificate 224759 :=
  certifyPrime (q := pv13) (ls := [pv2,pv109,pv1031]) (by decide +kernel)
def pv224759 : PrimeValue := ⟨224759, pr224759⟩
private theorem pr224771 : PrimeCertificate 224771 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv13,pv19]) (by decide +kernel)
def pv224771 : PrimeValue := ⟨224771, pr224771⟩
private theorem pr224797 : PrimeCertificate 224797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv131]) (by decide +kernel)
def pv224797 : PrimeValue := ⟨224797, pr224797⟩
private theorem pr224813 : PrimeCertificate 224813 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv31,pv37]) (by decide +kernel)
def pv224813 : PrimeValue := ⟨224813, pr224813⟩
private theorem pr224831 : PrimeCertificate 224831 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv22483]) (by decide +kernel)
def pv224831 : PrimeValue := ⟨224831, pr224831⟩
private theorem pr224863 : PrimeCertificate 224863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv3407]) (by decide +kernel)
def pv224863 : PrimeValue := ⟨224863, pr224863⟩
private theorem pr224869 : PrimeCertificate 224869 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv7,pv2677]) (by decide +kernel)
def pv224869 : PrimeValue := ⟨224869, pr224869⟩
private theorem pr224881 : PrimeCertificate 224881 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv937]) (by decide +kernel)
def pv224881 : PrimeValue := ⟨224881, pr224881⟩
private theorem pr224891 : PrimeCertificate 224891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv43,pv523]) (by decide +kernel)
def pv224891 : PrimeValue := ⟨224891, pr224891⟩
private theorem pr224897 : PrimeCertificate 224897 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv251]) (by decide +kernel)
def pv224897 : PrimeValue := ⟨224897, pr224897⟩
private theorem pr224911 : PrimeCertificate 224911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv17]) (by decide +kernel)
def pv224911 : PrimeValue := ⟨224911, pr224911⟩
private theorem pr224929 : PrimeCertificate 224929 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv71]) (by decide +kernel)
def pv224929 : PrimeValue := ⟨224929, pr224929⟩
private theorem pr224947 : PrimeCertificate 224947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12497]) (by decide +kernel)
def pv224947 : PrimeValue := ⟨224947, pr224947⟩
private theorem pr224951 : PrimeCertificate 224951 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv11,pv409]) (by decide +kernel)
def pv224951 : PrimeValue := ⟨224951, pr224951⟩
private theorem pr224969 : PrimeCertificate 224969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv61,pv461]) (by decide +kernel)
def pv224969 : PrimeValue := ⟨224969, pr224969⟩
private theorem pr224993 : PrimeCertificate 224993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv79,pv89]) (by decide +kernel)
def pv224993 : PrimeValue := ⟨224993, pr224993⟩
private theorem pr225037 : PrimeCertificate 225037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv47]) (by decide +kernel)
def pv225037 : PrimeValue := ⟨225037, pr225037⟩
private theorem pr225061 : PrimeCertificate 225061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11,pv31]) (by decide +kernel)
def pv225061 : PrimeValue := ⟨225061, pr225061⟩
private theorem pr225067 : PrimeCertificate 225067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37511]) (by decide +kernel)
def pv225067 : PrimeValue := ⟨225067, pr225067⟩
private theorem pr225089 : PrimeCertificate 225089 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3517]) (by decide +kernel)
def pv225089 : PrimeValue := ⟨225089, pr225089⟩
private theorem pr225119 : PrimeCertificate 225119 :=
  certifyPrime (q := pv11) (ls := [pv2,pv112559]) (by decide +kernel)
def pv225119 : PrimeValue := ⟨225119, pr225119⟩
private theorem pr225133 : PrimeCertificate 225133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv257]) (by decide +kernel)
def pv225133 : PrimeValue := ⟨225133, pr225133⟩
private theorem pr225143 : PrimeCertificate 225143 :=
  certifyPrime (q := pv5) (ls := [pv2,pv112571]) (by decide +kernel)
def pv225143 : PrimeValue := ⟨225143, pr225143⟩
private theorem pr225149 : PrimeCertificate 225149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv17,pv43]) (by decide +kernel)
def pv225149 : PrimeValue := ⟨225149, pr225149⟩
private theorem pr225163 : PrimeCertificate 225163 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv1787]) (by decide +kernel)
def pv225163 : PrimeValue := ⟨225163, pr225163⟩
private theorem pr225167 : PrimeCertificate 225167 :=
  certifyPrime (q := pv5) (ls := [pv2,pv112583]) (by decide +kernel)
def pv225167 : PrimeValue := ⟨225167, pr225167⟩
private theorem pr225217 : PrimeCertificate 225217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv17,pv23]) (by decide +kernel)
def pv225217 : PrimeValue := ⟨225217, pr225217⟩
private theorem pr225221 : PrimeCertificate 225221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11261]) (by decide +kernel)
def pv225221 : PrimeValue := ⟨225221, pr225221⟩
private theorem pr225223 : PrimeCertificate 225223 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37537]) (by decide +kernel)
def pv225223 : PrimeValue := ⟨225223, pr225223⟩
private theorem pr225227 : PrimeCertificate 225227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv5927]) (by decide +kernel)
def pv225227 : PrimeValue := ⟨225227, pr225227⟩
private theorem pr225241 : PrimeCertificate 225241 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv1877]) (by decide +kernel)
def pv225241 : PrimeValue := ⟨225241, pr225241⟩
private theorem pr225257 : PrimeCertificate 225257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37,pv761]) (by decide +kernel)
def pv225257 : PrimeValue := ⟨225257, pr225257⟩
private theorem pr225299 : PrimeCertificate 225299 :=
  certifyPrime (q := pv2) (ls := [pv2,pv127,pv887]) (by decide +kernel)
def pv225299 : PrimeValue := ⟨225299, pr225299⟩
private theorem pr225307 : PrimeCertificate 225307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12517]) (by decide +kernel)
def pv225307 : PrimeValue := ⟨225307, pr225307⟩
private theorem pr225349 : PrimeCertificate 225349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89,pv211]) (by decide +kernel)
def pv225349 : PrimeValue := ⟨225349, pr225349⟩
private theorem pr225353 : PrimeCertificate 225353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1657]) (by decide +kernel)
def pv225353 : PrimeValue := ⟨225353, pr225353⟩
private theorem pr225371 : PrimeCertificate 225371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv31,pv727]) (by decide +kernel)
def pv225371 : PrimeValue := ⟨225371, pr225371⟩
private theorem pr225383 : PrimeCertificate 225383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv112691]) (by decide +kernel)
def pv225383 : PrimeValue := ⟨225383, pr225383⟩
private theorem pr225427 : PrimeCertificate 225427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37571]) (by decide +kernel)
def pv225427 : PrimeValue := ⟨225427, pr225427⟩
private theorem pr225431 : PrimeCertificate 225431 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv22543]) (by decide +kernel)
def pv225431 : PrimeValue := ⟨225431, pr225431⟩
private theorem pr225493 : PrimeCertificate 225493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv23,pv43]) (by decide +kernel)
def pv225493 : PrimeValue := ⟨225493, pr225493⟩
private theorem pr225499 : PrimeCertificate 225499 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv13,pv59]) (by decide +kernel)
def pv225499 : PrimeValue := ⟨225499, pr225499⟩
private theorem pr225503 : PrimeCertificate 225503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv137,pv823]) (by decide +kernel)
def pv225503 : PrimeValue := ⟨225503, pr225503⟩
private theorem pr225509 : PrimeCertificate 225509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56377]) (by decide +kernel)
def pv225509 : PrimeValue := ⟨225509, pr225509⟩
private theorem pr225527 : PrimeCertificate 225527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv89,pv181]) (by decide +kernel)
def pv225527 : PrimeValue := ⟨225527, pr225527⟩
private theorem pr225529 : PrimeCertificate 225529 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv9397]) (by decide +kernel)
def pv225529 : PrimeValue := ⟨225529, pr225529⟩
private theorem pr225581 : PrimeCertificate 225581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11279]) (by decide +kernel)
def pv225581 : PrimeValue := ⟨225581, pr225581⟩
private theorem pr225583 : PrimeCertificate 225583 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv41,pv131]) (by decide +kernel)
def pv225583 : PrimeValue := ⟨225583, pr225583⟩
private theorem pr225601 : PrimeCertificate 225601 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv225601 : PrimeValue := ⟨225601, pr225601⟩
private theorem pr225613 : PrimeCertificate 225613 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2089]) (by decide +kernel)
def pv225613 : PrimeValue := ⟨225613, pr225613⟩
private theorem pr225619 : PrimeCertificate 225619 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv31,pv1213]) (by decide +kernel)
def pv225619 : PrimeValue := ⟨225619, pr225619⟩
private theorem pr225671 : PrimeCertificate 225671 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv22567]) (by decide +kernel)
def pv225671 : PrimeValue := ⟨225671, pr225671⟩
private theorem pr225689 : PrimeCertificate 225689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv28211]) (by decide +kernel)
def pv225689 : PrimeValue := ⟨225689, pr225689⟩
private theorem pr225697 : PrimeCertificate 225697 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv2351]) (by decide +kernel)
def pv225697 : PrimeValue := ⟨225697, pr225697⟩
private theorem pr225721 : PrimeCertificate 225721 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv225721 : PrimeValue := ⟨225721, pr225721⟩
private theorem pr225733 : PrimeCertificate 225733 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv13,pv1447]) (by decide +kernel)
def pv225733 : PrimeValue := ⟨225733, pr225733⟩
private theorem pr225749 : PrimeCertificate 225749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56437]) (by decide +kernel)
def pv225749 : PrimeValue := ⟨225749, pr225749⟩
private theorem pr225751 : PrimeCertificate 225751 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv225751 : PrimeValue := ⟨225751, pr225751⟩
private theorem pr225767 : PrimeCertificate 225767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv157,pv719]) (by decide +kernel)
def pv225767 : PrimeValue := ⟨225767, pr225767⟩
private theorem pr225769 : PrimeCertificate 225769 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv23,pv409]) (by decide +kernel)
def pv225769 : PrimeValue := ⟨225769, pr225769⟩
private theorem pr225781 : PrimeCertificate 225781 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv53,pv71]) (by decide +kernel)
def pv225781 : PrimeValue := ⟨225781, pr225781⟩
private theorem pr225809 : PrimeCertificate 225809 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1283]) (by decide +kernel)
def pv225809 : PrimeValue := ⟨225809, pr225809⟩
private theorem pr225821 : PrimeCertificate 225821 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv1613]) (by decide +kernel)
def pv225821 : PrimeValue := ⟨225821, pr225821⟩
private theorem pr225839 : PrimeCertificate 225839 :=
  certifyPrime (q := pv11) (ls := [pv2,pv112919]) (by decide +kernel)
def pv225839 : PrimeValue := ⟨225839, pr225839⟩
private theorem pr225871 : PrimeCertificate 225871 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7529]) (by decide +kernel)
def pv225871 : PrimeValue := ⟨225871, pr225871⟩
private theorem pr225919 : PrimeCertificate 225919 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv163]) (by decide +kernel)
def pv225919 : PrimeValue := ⟨225919, pr225919⟩
private theorem pr225941 : PrimeCertificate 225941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv13,pv79]) (by decide +kernel)
def pv225941 : PrimeValue := ⟨225941, pr225941⟩
private theorem pr225943 : PrimeCertificate 225943 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37657]) (by decide +kernel)
def pv225943 : PrimeValue := ⟨225943, pr225943⟩
private theorem pr225977 : PrimeCertificate 225977 :=
  certifyPrime (q := pv3) (ls := [pv2,pv47,pv601]) (by decide +kernel)
def pv225977 : PrimeValue := ⟨225977, pr225977⟩
private theorem pr225983 : PrimeCertificate 225983 :=
  certifyPrime (q := pv5) (ls := [pv2,pv103,pv1097]) (by decide +kernel)
def pv225983 : PrimeValue := ⟨225983, pr225983⟩
private theorem pr225989 : PrimeCertificate 225989 :=
  certifyPrime (q := pv19) (ls := [pv2,pv7,pv1153]) (by decide +kernel)
def pv225989 : PrimeValue := ⟨225989, pr225989⟩
private theorem pr226001 : PrimeCertificate 226001 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv113]) (by decide +kernel)
def pv226001 : PrimeValue := ⟨226001, pr226001⟩
private theorem pr226013 : PrimeCertificate 226013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56503]) (by decide +kernel)
def pv226013 : PrimeValue := ⟨226013, pr226013⟩
private theorem pr226063 : PrimeCertificate 226063 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv661]) (by decide +kernel)
def pv226063 : PrimeValue := ⟨226063, pr226063⟩
private theorem pr226099 : PrimeCertificate 226099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv53,pv79]) (by decide +kernel)
def pv226099 : PrimeValue := ⟨226099, pr226099⟩
private theorem pr226103 : PrimeCertificate 226103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv113051]) (by decide +kernel)
def pv226103 : PrimeValue := ⟨226103, pr226103⟩
private theorem pr226129 : PrimeCertificate 226129 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv673]) (by decide +kernel)
def pv226129 : PrimeValue := ⟨226129, pr226129⟩
private theorem pr226169 : PrimeCertificate 226169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv1663]) (by decide +kernel)
def pv226169 : PrimeValue := ⟨226169, pr226169⟩
private theorem pr226183 : PrimeCertificate 226183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11,pv23,pv149]) (by decide +kernel)
def pv226183 : PrimeValue := ⟨226183, pr226183⟩
private theorem pr226189 : PrimeCertificate 226189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv103]) (by decide +kernel)
def pv226189 : PrimeValue := ⟨226189, pr226189⟩
private theorem pr226199 : PrimeCertificate 226199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv107,pv151]) (by decide +kernel)
def pv226199 : PrimeValue := ⟨226199, pr226199⟩
private theorem pr226283 : PrimeCertificate 226283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv2309]) (by decide +kernel)
def pv226283 : PrimeValue := ⟨226283, pr226283⟩
private theorem pr226307 : PrimeCertificate 226307 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113153]) (by decide +kernel)
def pv226307 : PrimeValue := ⟨226307, pr226307⟩
private theorem pr226337 : PrimeCertificate 226337 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv643]) (by decide +kernel)
def pv226337 : PrimeValue := ⟨226337, pr226337⟩
private theorem pr226357 : PrimeCertificate 226357 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv1451]) (by decide +kernel)
def pv226357 : PrimeValue := ⟨226357, pr226357⟩
private theorem pr226367 : PrimeCertificate 226367 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19,pv23,pv37]) (by decide +kernel)
def pv226367 : PrimeValue := ⟨226367, pr226367⟩
private theorem pr226379 : PrimeCertificate 226379 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113189]) (by decide +kernel)
def pv226379 : PrimeValue := ⟨226379, pr226379⟩
private theorem pr226451 : PrimeCertificate 226451 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv647]) (by decide +kernel)
def pv226451 : PrimeValue := ⟨226451, pr226451⟩
private theorem pr226463 : PrimeCertificate 226463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv199,pv569]) (by decide +kernel)
def pv226463 : PrimeValue := ⟨226463, pr226463⟩
private theorem pr226483 : PrimeCertificate 226483 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37747]) (by decide +kernel)
def pv226483 : PrimeValue := ⟨226483, pr226483⟩
private theorem pr226511 : PrimeCertificate 226511 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv22651]) (by decide +kernel)
def pv226511 : PrimeValue := ⟨226511, pr226511⟩
private theorem pr226547 : PrimeCertificate 226547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv227,pv499]) (by decide +kernel)
def pv226547 : PrimeValue := ⟨226547, pr226547⟩
private theorem pr226549 : PrimeCertificate 226549 :=
  certifyPrime (q := pv41) (ls := [pv2,pv3,pv7,pv29,pv31]) (by decide +kernel)
def pv226549 : PrimeValue := ⟨226549, pr226549⟩
private theorem pr226553 : PrimeCertificate 226553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv28319]) (by decide +kernel)
def pv226553 : PrimeValue := ⟨226553, pr226553⟩
private theorem pr226571 : PrimeCertificate 226571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv139,pv163]) (by decide +kernel)
def pv226571 : PrimeValue := ⟨226571, pr226571⟩
private theorem pr226621 : PrimeCertificate 226621 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv1259]) (by decide +kernel)
def pv226621 : PrimeValue := ⟨226621, pr226621⟩
private theorem pr226637 : PrimeCertificate 226637 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56659]) (by decide +kernel)
def pv226637 : PrimeValue := ⟨226637, pr226637⟩
private theorem pr226643 : PrimeCertificate 226643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv379]) (by decide +kernel)
def pv226643 : PrimeValue := ⟨226643, pr226643⟩
private theorem pr226649 : PrimeCertificate 226649 :=
  certifyPrime (q := pv3) (ls := [pv2,pv41,pv691]) (by decide +kernel)
def pv226649 : PrimeValue := ⟨226649, pr226649⟩
private theorem pr226657 : PrimeCertificate 226657 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv787]) (by decide +kernel)
def pv226657 : PrimeValue := ⟨226657, pr226657⟩
private theorem pr226663 : PrimeCertificate 226663 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37,pv1021]) (by decide +kernel)
def pv226663 : PrimeValue := ⟨226663, pr226663⟩
private theorem pr226783 : PrimeCertificate 226783 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv293]) (by decide +kernel)
def pv226783 : PrimeValue := ⟨226783, pr226783⟩
private theorem pr226799 : PrimeCertificate 226799 :=
  certifyPrime (q := pv11) (ls := [pv2,pv11,pv13,pv61]) (by decide +kernel)
def pv226799 : PrimeValue := ⟨226799, pr226799⟩
private theorem pr226813 : PrimeCertificate 226813 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv41,pv461]) (by decide +kernel)
def pv226813 : PrimeValue := ⟨226813, pr226813⟩
private theorem pr226817 : PrimeCertificate 226817 :=
  certifyPrime (q := pv3) (ls := [pv2,pv443]) (by decide +kernel)
def pv226817 : PrimeValue := ⟨226817, pr226817⟩
private theorem pr226823 : PrimeCertificate 226823 :=
  certifyPrime (q := pv7) (ls := [pv2,pv19,pv47,pv127]) (by decide +kernel)
def pv226823 : PrimeValue := ⟨226823, pr226823⟩
private theorem pr226843 : PrimeCertificate 226843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv11,pv491]) (by decide +kernel)
def pv226843 : PrimeValue := ⟨226843, pr226843⟩
private theorem pr226903 : PrimeCertificate 226903 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv2909]) (by decide +kernel)
def pv226903 : PrimeValue := ⟨226903, pr226903⟩
private theorem pr226907 : PrimeCertificate 226907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113453]) (by decide +kernel)
def pv226907 : PrimeValue := ⟨226907, pr226907⟩
private theorem pr226913 : PrimeCertificate 226913 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv1013]) (by decide +kernel)
def pv226913 : PrimeValue := ⟨226913, pr226913⟩
private theorem pr226937 : PrimeCertificate 226937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv1493]) (by decide +kernel)
def pv226937 : PrimeValue := ⟨226937, pr226937⟩
private theorem pr226943 : PrimeCertificate 226943 :=
  certifyPrime (q := pv5) (ls := [pv2,pv233,pv487]) (by decide +kernel)
def pv226943 : PrimeValue := ⟨226943, pr226943⟩
private theorem pr226991 : PrimeCertificate 226991 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv22699]) (by decide +kernel)
def pv226991 : PrimeValue := ⟨226991, pr226991⟩
private theorem pr227011 : PrimeCertificate 227011 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv23,pv47]) (by decide +kernel)
def pv227011 : PrimeValue := ⟨227011, pr227011⟩
private theorem pr227027 : PrimeCertificate 227027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv113513]) (by decide +kernel)
def pv227027 : PrimeValue := ⟨227027, pr227027⟩
private theorem pr227053 : PrimeCertificate 227053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv17,pv53]) (by decide +kernel)
def pv227053 : PrimeValue := ⟨227053, pr227053⟩
private theorem pr227093 : PrimeCertificate 227093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56773]) (by decide +kernel)
def pv227093 : PrimeValue := ⟨227093, pr227093⟩
private theorem pr227113 : PrimeCertificate 227113 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv9463]) (by decide +kernel)
def pv227113 : PrimeValue := ⟨227113, pr227113⟩
private theorem pr227131 : PrimeCertificate 227131 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv67,pv113]) (by decide +kernel)
def pv227131 : PrimeValue := ⟨227131, pr227131⟩
private theorem pr227147 : PrimeCertificate 227147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv137,pv829]) (by decide +kernel)
def pv227147 : PrimeValue := ⟨227147, pr227147⟩
private theorem pr227153 : PrimeCertificate 227153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14197]) (by decide +kernel)
def pv227153 : PrimeValue := ⟨227153, pr227153⟩
private theorem pr227159 : PrimeCertificate 227159 :=
  certifyPrime (q := pv7) (ls := [pv2,pv53,pv2143]) (by decide +kernel)
def pv227159 : PrimeValue := ⟨227159, pr227159⟩
private theorem pr227167 : PrimeCertificate 227167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37861]) (by decide +kernel)
def pv227167 : PrimeValue := ⟨227167, pr227167⟩
private theorem pr227189 : PrimeCertificate 227189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv17,pv257]) (by decide +kernel)
def pv227189 : PrimeValue := ⟨227189, pr227189⟩
private theorem pr227207 : PrimeCertificate 227207 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv16229]) (by decide +kernel)
def pv227207 : PrimeValue := ⟨227207, pr227207⟩
private theorem pr227267 : PrimeCertificate 227267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv8741]) (by decide +kernel)
def pv227267 : PrimeValue := ⟨227267, pr227267⟩
private theorem pr227281 : PrimeCertificate 227281 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv947]) (by decide +kernel)
def pv227281 : PrimeValue := ⟨227281, pr227281⟩
private theorem pr227363 : PrimeCertificate 227363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv79,pv1439]) (by decide +kernel)
def pv227363 : PrimeValue := ⟨227363, pr227363⟩
private theorem pr227377 : PrimeCertificate 227377 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv1579]) (by decide +kernel)
def pv227377 : PrimeValue := ⟨227377, pr227377⟩
private theorem pr227387 : PrimeCertificate 227387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv47,pv59]) (by decide +kernel)
def pv227387 : PrimeValue := ⟨227387, pr227387⟩
private theorem pr227393 : PrimeCertificate 227393 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv17,pv19]) (by decide +kernel)
def pv227393 : PrimeValue := ⟨227393, pr227393⟩
private theorem pr227399 : PrimeCertificate 227399 :=
  certifyPrime (q := pv7) (ls := [pv2,pv67,pv1697]) (by decide +kernel)
def pv227399 : PrimeValue := ⟨227399, pr227399⟩
private theorem pr227419 : PrimeCertificate 227419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv1307]) (by decide +kernel)
def pv227419 : PrimeValue := ⟨227419, pr227419⟩
private theorem pr227431 : PrimeCertificate 227431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv19]) (by decide +kernel)
def pv227431 : PrimeValue := ⟨227431, pr227431⟩
private theorem pr227453 : PrimeCertificate 227453 :=
  certifyPrime (q := pv2) (ls := [pv2,pv101,pv563]) (by decide +kernel)
def pv227453 : PrimeValue := ⟨227453, pr227453⟩
private theorem pr227459 : PrimeCertificate 227459 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv211]) (by decide +kernel)
def pv227459 : PrimeValue := ⟨227459, pr227459⟩
private theorem pr227471 : PrimeCertificate 227471 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv23,pv43]) (by decide +kernel)
def pv227471 : PrimeValue := ⟨227471, pr227471⟩
private theorem pr227489 : PrimeCertificate 227489 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7109]) (by decide +kernel)
def pv227489 : PrimeValue := ⟨227489, pr227489⟩
private theorem pr227497 : PrimeCertificate 227497 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv9479]) (by decide +kernel)
def pv227497 : PrimeValue := ⟨227497, pr227497⟩
private theorem pr227501 : PrimeCertificate 227501 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13]) (by decide +kernel)
def pv227501 : PrimeValue := ⟨227501, pr227501⟩
private theorem pr227519 : PrimeCertificate 227519 :=
  certifyPrime (q := pv13) (ls := [pv2,pv113759]) (by decide +kernel)
def pv227519 : PrimeValue := ⟨227519, pr227519⟩
private theorem pr227531 : PrimeCertificate 227531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv61,pv373]) (by decide +kernel)
def pv227531 : PrimeValue := ⟨227531, pr227531⟩
private theorem pr227533 : PrimeCertificate 227533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv67,pv283]) (by decide +kernel)
def pv227533 : PrimeValue := ⟨227533, pr227533⟩
private theorem pr227537 : PrimeCertificate 227537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv14221]) (by decide +kernel)
def pv227537 : PrimeValue := ⟨227537, pr227537⟩
private theorem pr227561 : PrimeCertificate 227561 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv5689]) (by decide +kernel)
def pv227561 : PrimeValue := ⟨227561, pr227561⟩
private theorem pr227569 : PrimeCertificate 227569 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv11,pv431]) (by decide +kernel)
def pv227569 : PrimeValue := ⟨227569, pr227569⟩
private theorem pr227597 : PrimeCertificate 227597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv3347]) (by decide +kernel)
def pv227597 : PrimeValue := ⟨227597, pr227597⟩
private theorem pr227609 : PrimeCertificate 227609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv1237]) (by decide +kernel)
def pv227609 : PrimeValue := ⟨227609, pr227609⟩
private theorem pr227611 : PrimeCertificate 227611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv227611 : PrimeValue := ⟨227611, pr227611⟩
private theorem pr227627 : PrimeCertificate 227627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv71,pv229]) (by decide +kernel)
def pv227627 : PrimeValue := ⟨227627, pr227627⟩
private theorem pr227651 : PrimeCertificate 227651 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv157]) (by decide +kernel)
def pv227651 : PrimeValue := ⟨227651, pr227651⟩
private theorem pr227653 : PrimeCertificate 227653 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61,pv311]) (by decide +kernel)
def pv227653 : PrimeValue := ⟨227653, pr227653⟩
private theorem pr227663 : PrimeCertificate 227663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv89,pv1279]) (by decide +kernel)
def pv227663 : PrimeValue := ⟨227663, pr227663⟩
private theorem pr227693 : PrimeCertificate 227693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv56923]) (by decide +kernel)
def pv227693 : PrimeValue := ⟨227693, pr227693⟩
private theorem pr227699 : PrimeCertificate 227699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv37,pv181]) (by decide +kernel)
def pv227699 : PrimeValue := ⟨227699, pr227699⟩
private theorem pr227707 : PrimeCertificate 227707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37951]) (by decide +kernel)
def pv227707 : PrimeValue := ⟨227707, pr227707⟩
private theorem pr227719 : PrimeCertificate 227719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv4217]) (by decide +kernel)
def pv227719 : PrimeValue := ⟨227719, pr227719⟩
private theorem pr227729 : PrimeCertificate 227729 :=
  certifyPrime (q := pv3) (ls := [pv2,pv43,pv331]) (by decide +kernel)
def pv227729 : PrimeValue := ⟨227729, pr227729⟩
private theorem pr227743 : PrimeCertificate 227743 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv37957]) (by decide +kernel)
def pv227743 : PrimeValue := ⟨227743, pr227743⟩
private theorem pr227789 : PrimeCertificate 227789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv31,pv167]) (by decide +kernel)
def pv227789 : PrimeValue := ⟨227789, pr227789⟩
private theorem pr227869 : PrimeCertificate 227869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1117]) (by decide +kernel)
def pv227869 : PrimeValue := ⟨227869, pr227869⟩
private theorem pr227873 : PrimeCertificate 227873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7121]) (by decide +kernel)
def pv227873 : PrimeValue := ⟨227873, pr227873⟩
private theorem pr227893 : PrimeCertificate 227893 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv2713]) (by decide +kernel)
def pv227893 : PrimeValue := ⟨227893, pr227893⟩
private theorem pr227947 : PrimeCertificate 227947 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37991]) (by decide +kernel)
def pv227947 : PrimeValue := ⟨227947, pr227947⟩
private theorem pr227951 : PrimeCertificate 227951 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv47,pv97]) (by decide +kernel)
def pv227951 : PrimeValue := ⟨227951, pr227951⟩
private theorem pr227989 : PrimeCertificate 227989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv2111]) (by decide +kernel)
def pv227989 : PrimeValue := ⟨227989, pr227989⟩
private theorem pr228013 : PrimeCertificate 228013 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19001]) (by decide +kernel)
def pv228013 : PrimeValue := ⟨228013, pr228013⟩
private theorem pr228023 : PrimeCertificate 228023 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv4957]) (by decide +kernel)
def pv228023 : PrimeValue := ⟨228023, pr228023⟩
private theorem pr228061 : PrimeCertificate 228061 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv181]) (by decide +kernel)
def pv228061 : PrimeValue := ⟨228061, pr228061⟩
private theorem pr228077 : PrimeCertificate 228077 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv3001]) (by decide +kernel)
def pv228077 : PrimeValue := ⟨228077, pr228077⟩
private theorem pr228103 : PrimeCertificate 228103 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5431]) (by decide +kernel)
def pv228103 : PrimeValue := ⟨228103, pr228103⟩
private theorem pr228197 : PrimeCertificate 228197 :=
  certifyPrime (q := pv2) (ls := [pv2,pv89,pv641]) (by decide +kernel)
def pv228197 : PrimeValue := ⟨228197, pr228197⟩
private theorem pr228199 : PrimeCertificate 228199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv73,pv521]) (by decide +kernel)
def pv228199 : PrimeValue := ⟨228199, pr228199⟩
private theorem pr228203 : PrimeCertificate 228203 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv67,pv131]) (by decide +kernel)
def pv228203 : PrimeValue := ⟨228203, pr228203⟩
private theorem pr228223 : PrimeCertificate 228223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv31,pv409]) (by decide +kernel)
def pv228223 : PrimeValue := ⟨228223, pr228223⟩
private theorem pr228251 : PrimeCertificate 228251 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv83]) (by decide +kernel)
def pv228251 : PrimeValue := ⟨228251, pr228251⟩
private theorem pr228301 : PrimeCertificate 228301 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv761]) (by decide +kernel)
def pv228301 : PrimeValue := ⟨228301, pr228301⟩
private theorem pr228311 : PrimeCertificate 228311 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv79]) (by decide +kernel)
def pv228311 : PrimeValue := ⟨228311, pr228311⟩
private theorem pr228331 : PrimeCertificate 228331 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv43,pv59]) (by decide +kernel)
def pv228331 : PrimeValue := ⟨228331, pr228331⟩
private theorem pr228341 : PrimeCertificate 228341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv233]) (by decide +kernel)
def pv228341 : PrimeValue := ⟨228341, pr228341⟩
private theorem pr228359 : PrimeCertificate 228359 :=
  certifyPrime (q := pv19) (ls := [pv2,pv13,pv8783]) (by decide +kernel)
def pv228359 : PrimeValue := ⟨228359, pr228359⟩
private theorem pr228383 : PrimeCertificate 228383 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv1483]) (by decide +kernel)
def pv228383 : PrimeValue := ⟨228383, pr228383⟩
private theorem pr228409 : PrimeCertificate 228409 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv31,pv307]) (by decide +kernel)
def pv228409 : PrimeValue := ⟨228409, pr228409⟩
private theorem pr228421 : PrimeCertificate 228421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv228421 : PrimeValue := ⟨228421, pr228421⟩
private theorem pr228427 : PrimeCertificate 228427 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv3461]) (by decide +kernel)
def pv228427 : PrimeValue := ⟨228427, pr228427⟩
private theorem pr228461 : PrimeCertificate 228461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11423]) (by decide +kernel)
def pv228461 : PrimeValue := ⟨228461, pr228461⟩
private theorem pr228469 : PrimeCertificate 228469 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv79,pv241]) (by decide +kernel)
def pv228469 : PrimeValue := ⟨228469, pr228469⟩
private theorem pr228479 : PrimeCertificate 228479 :=
  certifyPrime (q := pv11) (ls := [pv2,pv71,pv1609]) (by decide +kernel)
def pv228479 : PrimeValue := ⟨228479, pr228479⟩
private theorem pr228509 : PrimeCertificate 228509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8161]) (by decide +kernel)
def pv228509 : PrimeValue := ⟨228509, pr228509⟩
private theorem pr228517 : PrimeCertificate 228517 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv137,pv139]) (by decide +kernel)
def pv228517 : PrimeValue := ⟨228517, pr228517⟩
private theorem pr228521 : PrimeCertificate 228521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29,pv197]) (by decide +kernel)
def pv228521 : PrimeValue := ⟨228521, pr228521⟩
private theorem pr228523 : PrimeCertificate 228523 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv5441]) (by decide +kernel)
def pv228523 : PrimeValue := ⟨228523, pr228523⟩
private theorem pr228539 : PrimeCertificate 228539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv114269]) (by decide +kernel)
def pv228539 : PrimeValue := ⟨228539, pr228539⟩
private theorem pr228559 : PrimeCertificate 228559 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv3463]) (by decide +kernel)
def pv228559 : PrimeValue := ⟨228559, pr228559⟩
private theorem pr228581 : PrimeCertificate 228581 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv1039]) (by decide +kernel)
def pv228581 : PrimeValue := ⟨228581, pr228581⟩
private theorem pr228601 : PrimeCertificate 228601 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv127]) (by decide +kernel)
def pv228601 : PrimeValue := ⟨228601, pr228601⟩
private theorem pr228617 : PrimeCertificate 228617 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv41]) (by decide +kernel)
def pv228617 : PrimeValue := ⟨228617, pr228617⟩
private theorem pr228619 : PrimeCertificate 228619 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13,pv977]) (by decide +kernel)
def pv228619 : PrimeValue := ⟨228619, pr228619⟩
private theorem pr228677 : PrimeCertificate 228677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv8167]) (by decide +kernel)
def pv228677 : PrimeValue := ⟨228677, pr228677⟩
private theorem pr228707 : PrimeCertificate 228707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv173,pv661]) (by decide +kernel)
def pv228707 : PrimeValue := ⟨228707, pr228707⟩
private theorem pr228713 : PrimeCertificate 228713 :=
  certifyPrime (q := pv17) (ls := [pv2,pv11,pv23,pv113]) (by decide +kernel)
def pv228713 : PrimeValue := ⟨228713, pr228713⟩
private theorem pr228731 : PrimeCertificate 228731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv89,pv257]) (by decide +kernel)
def pv228731 : PrimeValue := ⟨228731, pr228731⟩
private theorem pr228737 : PrimeCertificate 228737 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1787]) (by decide +kernel)
def pv228737 : PrimeValue := ⟨228737, pr228737⟩
private theorem pr228757 : PrimeCertificate 228757 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv1733]) (by decide +kernel)
def pv228757 : PrimeValue := ⟨228757, pr228757⟩
private theorem pr228773 : PrimeCertificate 228773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57193]) (by decide +kernel)
def pv228773 : PrimeValue := ⟨228773, pr228773⟩
private theorem pr228793 : PrimeCertificate 228793 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv9533]) (by decide +kernel)
def pv228793 : PrimeValue := ⟨228793, pr228793⟩
private theorem pr228799 : PrimeCertificate 228799 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv223]) (by decide +kernel)
def pv228799 : PrimeValue := ⟨228799, pr228799⟩
private theorem pr228829 : PrimeCertificate 228829 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19069]) (by decide +kernel)
def pv228829 : PrimeValue := ⟨228829, pr228829⟩
private theorem pr228847 : PrimeCertificate 228847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv43,pv887]) (by decide +kernel)
def pv228847 : PrimeValue := ⟨228847, pr228847⟩
private theorem pr228859 : PrimeCertificate 228859 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv5449]) (by decide +kernel)
def pv228859 : PrimeValue := ⟨228859, pr228859⟩
private theorem pr228869 : PrimeCertificate 228869 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv1973]) (by decide +kernel)
def pv228869 : PrimeValue := ⟨228869, pr228869⟩
private theorem pr228883 : PrimeCertificate 228883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv1031]) (by decide +kernel)
def pv228883 : PrimeValue := ⟨228883, pr228883⟩
private theorem pr228887 : PrimeCertificate 228887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv16349]) (by decide +kernel)
def pv228887 : PrimeValue := ⟨228887, pr228887⟩
private theorem pr228901 : PrimeCertificate 228901 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv109]) (by decide +kernel)
def pv228901 : PrimeValue := ⟨228901, pr228901⟩
private theorem pr228911 : PrimeCertificate 228911 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv2081]) (by decide +kernel)
def pv228911 : PrimeValue := ⟨228911, pr228911⟩
private theorem pr228913 : PrimeCertificate 228913 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv19,pv251]) (by decide +kernel)
def pv228913 : PrimeValue := ⟨228913, pr228913⟩
private theorem pr228923 : PrimeCertificate 228923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv6733]) (by decide +kernel)
def pv228923 : PrimeValue := ⟨228923, pr228923⟩
private theorem pr228959 : PrimeCertificate 228959 :=
  certifyPrime (q := pv11) (ls := [pv2,pv114479]) (by decide +kernel)
def pv228959 : PrimeValue := ⟨228959, pr228959⟩
private theorem pr228989 : PrimeCertificate 228989 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv23,pv131]) (by decide +kernel)
def pv228989 : PrimeValue := ⟨228989, pr228989⟩
private theorem pr229003 : PrimeCertificate 229003 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv38167]) (by decide +kernel)
def pv229003 : PrimeValue := ⟨229003, pr229003⟩
private theorem pr229027 : PrimeCertificate 229027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv41]) (by decide +kernel)
def pv229027 : PrimeValue := ⟨229027, pr229027⟩
private theorem pr229037 : PrimeCertificate 229037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv57259]) (by decide +kernel)
def pv229037 : PrimeValue := ⟨229037, pr229037⟩
private theorem pr229081 : PrimeCertificate 229081 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv23,pv83]) (by decide +kernel)
def pv229081 : PrimeValue := ⟨229081, pr229081⟩
private theorem pr229093 : PrimeCertificate 229093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv1123]) (by decide +kernel)
def pv229093 : PrimeValue := ⟨229093, pr229093⟩
private theorem pr229123 : PrimeCertificate 229123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv4243]) (by decide +kernel)
def pv229123 : PrimeValue := ⟨229123, pr229123⟩
private theorem pr229127 : PrimeCertificate 229127 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv23,pv293]) (by decide +kernel)
def pv229127 : PrimeValue := ⟨229127, pr229127⟩
private theorem pr229139 : PrimeCertificate 229139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv1259]) (by decide +kernel)
def pv229139 : PrimeValue := ⟨229139, pr229139⟩
private theorem pr229153 : PrimeCertificate 229153 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv7,pv11,pv31]) (by decide +kernel)
def pv229153 : PrimeValue := ⟨229153, pr229153⟩
private theorem pr229157 : PrimeCertificate 229157 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv971]) (by decide +kernel)
def pv229157 : PrimeValue := ⟨229157, pr229157⟩
private theorem pr229171 : PrimeCertificate 229171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7639]) (by decide +kernel)
def pv229171 : PrimeValue := ⟨229171, pr229171⟩
private theorem pr229181 : PrimeCertificate 229181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv1637]) (by decide +kernel)
def pv229181 : PrimeValue := ⟨229181, pr229181⟩
private theorem pr229199 : PrimeCertificate 229199 :=
  certifyPrime (q := pv11) (ls := [pv2,pv114599]) (by decide +kernel)
def pv229199 : PrimeValue := ⟨229199, pr229199⟩
private theorem pr229213 : PrimeCertificate 229213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv6367]) (by decide +kernel)
def pv229213 : PrimeValue := ⟨229213, pr229213⟩
private theorem pr229217 : PrimeCertificate 229217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv19,pv29]) (by decide +kernel)
def pv229217 : PrimeValue := ⟨229217, pr229217⟩
private theorem pr229223 : PrimeCertificate 229223 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2339]) (by decide +kernel)
def pv229223 : PrimeValue := ⟨229223, pr229223⟩
private theorem pr229237 : PrimeCertificate 229237 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv2729]) (by decide +kernel)
def pv229237 : PrimeValue := ⟨229237, pr229237⟩
private theorem pr229249 : PrimeCertificate 229249 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv199]) (by decide +kernel)
def pv229249 : PrimeValue := ⟨229249, pr229249⟩
private theorem pr229253 : PrimeCertificate 229253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv1549]) (by decide +kernel)
def pv229253 : PrimeValue := ⟨229253, pr229253⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
