/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table246
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables03/Table246.pv1914443
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table033
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table049
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table064
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables01.Table136

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr1914443 : PrimeCertificate 1914443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv957221]) (by decide +kernel)
def pv1914443 : PrimeValue := ⟨1914443, pr1914443⟩
private theorem pr1914569 : PrimeCertificate 1914569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv89,pv2689]) (by decide +kernel)
def pv1914569 : PrimeValue := ⟨1914569, pr1914569⟩
private theorem pr1914641 : PrimeCertificate 1914641 :=
  certifyPrime (q := pv83) (ls := [pv2,pv5,pv7,pv13,pv263]) (by decide +kernel)
def pv1914641 : PrimeValue := ⟨1914641, pr1914641⟩
private theorem pr1914743 : PrimeCertificate 1914743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv269,pv3559]) (by decide +kernel)
def pv1914743 : PrimeValue := ⟨1914743, pr1914743⟩
private theorem pr1914959 : PrimeCertificate 1914959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv131,pv7309]) (by decide +kernel)
def pv1914959 : PrimeValue := ⟨1914959, pr1914959⟩
private theorem pr1915103 : PrimeCertificate 1915103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv29,pv53,pv89]) (by decide +kernel)
def pv1915103 : PrimeValue := ⟨1915103, pr1915103⟩
private theorem pr1915163 : PrimeCertificate 1915163 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv101,pv499]) (by decide +kernel)
def pv1915163 : PrimeValue := ⟨1915163, pr1915163⟩
private theorem pr1915229 : PrimeCertificate 1915229 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv73,pv937]) (by decide +kernel)
def pv1915229 : PrimeValue := ⟨1915229, pr1915229⟩
private theorem pr1915289 : PrimeCertificate 1915289 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv14083]) (by decide +kernel)
def pv1915289 : PrimeValue := ⟨1915289, pr1915289⟩
private theorem pr1915481 : PrimeCertificate 1915481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv6841]) (by decide +kernel)
def pv1915481 : PrimeValue := ⟨1915481, pr1915481⟩
private theorem pr1915733 : PrimeCertificate 1915733 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv13,pv19,pv277]) (by decide +kernel)
def pv1915733 : PrimeValue := ⟨1915733, pr1915733⟩
private theorem pr1915799 : PrimeCertificate 1915799 :=
  certifyPrime (q := pv7) (ls := [pv2,pv17,pv29,pv67]) (by decide +kernel)
def pv1915799 : PrimeValue := ⟨1915799, pr1915799⟩
private theorem pr1915811 : PrimeCertificate 1915811 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv14737]) (by decide +kernel)
def pv1915811 : PrimeValue := ⟨1915811, pr1915811⟩
private theorem pr1915961 : PrimeCertificate 1915961 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv2521]) (by decide +kernel)
def pv1915961 : PrimeValue := ⟨1915961, pr1915961⟩
private theorem pr1916339 : PrimeCertificate 1916339 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv22283]) (by decide +kernel)
def pv1916339 : PrimeValue := ⟨1916339, pr1916339⟩
private theorem pr1916543 : PrimeCertificate 1916543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv73,pv13127]) (by decide +kernel)
def pv1916543 : PrimeValue := ⟨1916543, pr1916543⟩
private theorem pr1916591 : PrimeCertificate 1916591 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv13,pv23,pv641]) (by decide +kernel)
def pv1916591 : PrimeValue := ⟨1916591, pr1916591⟩
private theorem pr1917029 : PrimeCertificate 1917029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv8123]) (by decide +kernel)
def pv1917029 : PrimeValue := ⟨1917029, pr1917029⟩
private theorem pr1917203 : PrimeCertificate 1917203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv136943]) (by decide +kernel)
def pv1917203 : PrimeValue := ⟨1917203, pr1917203⟩
private theorem pr1917479 : PrimeCertificate 1917479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv958739]) (by decide +kernel)
def pv1917479 : PrimeValue := ⟨1917479, pr1917479⟩
private theorem pr1917743 : PrimeCertificate 1917743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv958871]) (by decide +kernel)
def pv1917743 : PrimeValue := ⟨1917743, pr1917743⟩
private theorem pr1918121 : PrimeCertificate 1918121 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv79,pv607]) (by decide +kernel)
def pv1918121 : PrimeValue := ⟨1918121, pr1918121⟩
private theorem pr1918181 : PrimeCertificate 1918181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv8719]) (by decide +kernel)
def pv1918181 : PrimeValue := ⟨1918181, pr1918181⟩
private theorem pr1918193 : PrimeCertificate 1918193 :=
  certifyPrime (q := pv3) (ls := [pv2,pv101,pv1187]) (by decide +kernel)
def pv1918193 : PrimeValue := ⟨1918193, pr1918193⟩
private theorem pr1918463 : PrimeCertificate 1918463 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv83,pv127]) (by decide +kernel)
def pv1918463 : PrimeValue := ⟨1918463, pr1918463⟩
private theorem pr1918571 : PrimeCertificate 1918571 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv173,pv1109]) (by decide +kernel)
def pv1918571 : PrimeValue := ⟨1918571, pr1918571⟩
private theorem pr1918643 : PrimeCertificate 1918643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv87211]) (by decide +kernel)
def pv1918643 : PrimeValue := ⟨1918643, pr1918643⟩
private theorem pr1918733 : PrimeCertificate 1918733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv6571]) (by decide +kernel)
def pv1918733 : PrimeValue := ⟨1918733, pr1918733⟩
private theorem pr1919429 : PrimeCertificate 1919429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv1399]) (by decide +kernel)
def pv1919429 : PrimeValue := ⟨1919429, pr1919429⟩
private theorem pr1919441 : PrimeCertificate 1919441 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv23993]) (by decide +kernel)
def pv1919441 : PrimeValue := ⟨1919441, pr1919441⟩
private theorem pr1919789 : PrimeCertificate 1919789 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv36919]) (by decide +kernel)
def pv1919789 : PrimeValue := ⟨1919789, pr1919789⟩
private theorem pr1919891 : PrimeCertificate 1919891 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv27427]) (by decide +kernel)
def pv1919891 : PrimeValue := ⟨1919891, pr1919891⟩
private theorem pr1920101 : PrimeCertificate 1920101 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv13,pv211]) (by decide +kernel)
def pv1920101 : PrimeValue := ⟨1920101, pr1920101⟩
private theorem pr1920239 : PrimeCertificate 1920239 :=
  certifyPrime (q := pv19) (ls := [pv2,pv960119]) (by decide +kernel)
def pv1920239 : PrimeValue := ⟨1920239, pr1920239⟩
private theorem pr1920599 : PrimeCertificate 1920599 :=
  certifyPrime (q := pv7) (ls := [pv2,pv960299]) (by decide +kernel)
def pv1920599 : PrimeValue := ⟨1920599, pr1920599⟩
private theorem pr1920683 : PrimeCertificate 1920683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv960341]) (by decide +kernel)
def pv1920683 : PrimeValue := ⟨1920683, pr1920683⟩
private theorem pr1920701 : PrimeCertificate 1920701 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19207]) (by decide +kernel)
def pv1920701 : PrimeValue := ⟨1920701, pr1920701⟩
private theorem pr1920839 : PrimeCertificate 1920839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv960419]) (by decide +kernel)
def pv1920839 : PrimeValue := ⟨1920839, pr1920839⟩
private theorem pr1920959 : PrimeCertificate 1920959 :=
  certifyPrime (q := pv17) (ls := [pv2,pv13,pv73883]) (by decide +kernel)
def pv1920959 : PrimeValue := ⟨1920959, pr1920959⟩
private theorem pr1921253 : PrimeCertificate 1921253 :=
  certifyPrime (q := pv2) (ls := [pv2,pv241,pv1993]) (by decide +kernel)
def pv1921253 : PrimeValue := ⟨1921253, pr1921253⟩
private theorem pr1921481 : PrimeCertificate 1921481 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv397]) (by decide +kernel)
def pv1921481 : PrimeValue := ⟨1921481, pr1921481⟩
private theorem pr1921499 : PrimeCertificate 1921499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv22343]) (by decide +kernel)
def pv1921499 : PrimeValue := ⟨1921499, pr1921499⟩
private theorem pr1921553 : PrimeCertificate 1921553 :=
  certifyPrime (q := pv3) (ls := [pv2,pv120097]) (by decide +kernel)
def pv1921553 : PrimeValue := ⟨1921553, pr1921553⟩
private theorem pr1921709 : PrimeCertificate 1921709 :=
  certifyPrime (q := pv2) (ls := [pv2,pv480427]) (by decide +kernel)
def pv1921709 : PrimeValue := ⟨1921709, pr1921709⟩
private theorem pr1922153 : PrimeCertificate 1922153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv97,pv2477]) (by decide +kernel)
def pv1922153 : PrimeValue := ⟨1922153, pr1922153⟩
private theorem pr1922423 : PrimeCertificate 1922423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv163,pv5897]) (by decide +kernel)
def pv1922423 : PrimeValue := ⟨1922423, pr1922423⟩
private theorem pr1922471 : PrimeCertificate 1922471 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv17477]) (by decide +kernel)
def pv1922471 : PrimeValue := ⟨1922471, pr1922471⟩
private theorem pr1922561 : PrimeCertificate 1922561 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv751]) (by decide +kernel)
def pv1922561 : PrimeValue := ⟨1922561, pr1922561⟩
private theorem pr1922579 : PrimeCertificate 1922579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv89,pv1543]) (by decide +kernel)
def pv1922579 : PrimeValue := ⟨1922579, pr1922579⟩
private theorem pr1922663 : PrimeCertificate 1922663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv23,pv853]) (by decide +kernel)
def pv1922663 : PrimeValue := ⟨1922663, pr1922663⟩
private theorem pr1922873 : PrimeCertificate 1922873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv34337]) (by decide +kernel)
def pv1922873 : PrimeValue := ⟨1922873, pr1922873⟩
private theorem pr1922951 : PrimeCertificate 1922951 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv38459]) (by decide +kernel)
def pv1922951 : PrimeValue := ⟨1922951, pr1922951⟩
private theorem pr1923353 : PrimeCertificate 1923353 :=
  certifyPrime (q := pv3) (ls := [pv2,pv23,pv10453]) (by decide +kernel)
def pv1923353 : PrimeValue := ⟨1923353, pr1923353⟩
private theorem pr1923749 : PrimeCertificate 1923749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv480937]) (by decide +kernel)
def pv1923749 : PrimeValue := ⟨1923749, pr1923749⟩
private theorem pr1923791 : PrimeCertificate 1923791 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv11,pv17489]) (by decide +kernel)
def pv1923791 : PrimeValue := ⟨1923791, pr1923791⟩
private theorem pr1924343 : PrimeCertificate 1924343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv137453]) (by decide +kernel)
def pv1924343 : PrimeValue := ⟨1924343, pr1924343⟩
private theorem pr1924649 : PrimeCertificate 1924649 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv21871]) (by decide +kernel)
def pv1924649 : PrimeValue := ⟨1924649, pr1924649⟩
private theorem pr1924679 : PrimeCertificate 1924679 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv137477]) (by decide +kernel)
def pv1924679 : PrimeValue := ⟨1924679, pr1924679⟩
private theorem pr1925531 : PrimeCertificate 1925531 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv192553]) (by decide +kernel)
def pv1925531 : PrimeValue := ⟨1925531, pr1925531⟩
private theorem pr1925639 : PrimeCertificate 1925639 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv13,pv6733]) (by decide +kernel)
def pv1925639 : PrimeValue := ⟨1925639, pr1925639⟩
private theorem pr1925681 : PrimeCertificate 1925681 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv24071]) (by decide +kernel)
def pv1925681 : PrimeValue := ⟨1925681, pr1925681⟩
private theorem pr1925711 : PrimeCertificate 1925711 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv192571]) (by decide +kernel)
def pv1925711 : PrimeValue := ⟨1925711, pr1925711⟩
private theorem pr1925873 : PrimeCertificate 1925873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv47,pv197]) (by decide +kernel)
def pv1925873 : PrimeValue := ⟨1925873, pr1925873⟩
private theorem pr1925909 : PrimeCertificate 1925909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv467,pv1031]) (by decide +kernel)
def pv1925909 : PrimeValue := ⟨1925909, pr1925909⟩
private theorem pr1926161 : PrimeCertificate 1926161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv24077]) (by decide +kernel)
def pv1926161 : PrimeValue := ⟨1926161, pr1926161⟩
private theorem pr1926269 : PrimeCertificate 1926269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv271,pv1777]) (by decide +kernel)
def pv1926269 : PrimeValue := ⟨1926269, pr1926269⟩
private theorem pr1926341 : PrimeCertificate 1926341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv31,pv239]) (by decide +kernel)
def pv1926341 : PrimeValue := ⟨1926341, pr1926341⟩
private theorem pr1926461 : PrimeCertificate 1926461 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv96323]) (by decide +kernel)
def pv1926461 : PrimeValue := ⟨1926461, pr1926461⟩
private theorem pr1926623 : PrimeCertificate 1926623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv963311]) (by decide +kernel)
def pv1926623 : PrimeValue := ⟨1926623, pr1926623⟩
private theorem pr1926773 : PrimeCertificate 1926773 :=
  certifyPrime (q := pv2) (ls := [pv2,pv481693]) (by decide +kernel)
def pv1926773 : PrimeValue := ⟨1926773, pr1926773⟩
private theorem pr1926791 : PrimeCertificate 1926791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv19,pv10141]) (by decide +kernel)
def pv1926791 : PrimeValue := ⟨1926791, pr1926791⟩
private theorem pr1926863 : PrimeCertificate 1926863 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv137633]) (by decide +kernel)
def pv1926863 : PrimeValue := ⟨1926863, pr1926863⟩
private theorem pr1927031 : PrimeCertificate 1927031 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv27529]) (by decide +kernel)
def pv1927031 : PrimeValue := ⟨1927031, pr1927031⟩
private theorem pr1927241 : PrimeCertificate 1927241 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv7,pv6883]) (by decide +kernel)
def pv1927241 : PrimeValue := ⟨1927241, pr1927241⟩
private theorem pr1927361 : PrimeCertificate 1927361 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv317]) (by decide +kernel)
def pv1927361 : PrimeValue := ⟨1927361, pr1927361⟩
private theorem pr1927421 : PrimeCertificate 1927421 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv8761]) (by decide +kernel)
def pv1927421 : PrimeValue := ⟨1927421, pr1927421⟩
private theorem pr1927571 : PrimeCertificate 1927571 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv192757]) (by decide +kernel)
def pv1927571 : PrimeValue := ⟨1927571, pr1927571⟩
private theorem pr1927619 : PrimeCertificate 1927619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv12517]) (by decide +kernel)
def pv1927619 : PrimeValue := ⟨1927619, pr1927619⟩
private theorem pr1927823 : PrimeCertificate 1927823 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv53,pv1399]) (by decide +kernel)
def pv1927823 : PrimeValue := ⟨1927823, pr1927823⟩
private theorem pr1928093 : PrimeCertificate 1928093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv509,pv947]) (by decide +kernel)
def pv1928093 : PrimeValue := ⟨1928093, pr1928093⟩
private theorem pr1928099 : PrimeCertificate 1928099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv964049]) (by decide +kernel)
def pv1928099 : PrimeValue := ⟨1928099, pr1928099⟩
private theorem pr1928183 : PrimeCertificate 1928183 :=
  certifyPrime (q := pv5) (ls := [pv2,pv23,pv167,pv251]) (by decide +kernel)
def pv1928183 : PrimeValue := ⟨1928183, pr1928183⟩
private theorem pr1928351 : PrimeCertificate 1928351 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv38567]) (by decide +kernel)
def pv1928351 : PrimeValue := ⟨1928351, pr1928351⟩
private theorem pr1928411 : PrimeCertificate 1928411 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv47,pv373]) (by decide +kernel)
def pv1928411 : PrimeValue := ⟨1928411, pr1928411⟩
private theorem pr1928501 : PrimeCertificate 1928501 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv19,pv29]) (by decide +kernel)
def pv1928501 : PrimeValue := ⟨1928501, pr1928501⟩
private theorem pr1928513 : PrimeCertificate 1928513 :=
  certifyPrime (q := pv3) (ls := [pv2,pv30133]) (by decide +kernel)
def pv1928513 : PrimeValue := ⟨1928513, pr1928513⟩
private theorem pr1928831 : PrimeCertificate 1928831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv192883]) (by decide +kernel)
def pv1928831 : PrimeValue := ⟨1928831, pr1928831⟩
private theorem pr1928873 : PrimeCertificate 1928873 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv23,pv953]) (by decide +kernel)
def pv1928873 : PrimeValue := ⟨1928873, pr1928873⟩
private theorem pr1929071 : PrimeCertificate 1929071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv13,pv19,pv71]) (by decide +kernel)
def pv1929071 : PrimeValue := ⟨1929071, pr1929071⟩
private theorem pr1929149 : PrimeCertificate 1929149 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv23,pv1613]) (by decide +kernel)
def pv1929149 : PrimeValue := ⟨1929149, pr1929149⟩
private theorem pr1929503 : PrimeCertificate 1929503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv31,pv31121]) (by decide +kernel)
def pv1929503 : PrimeValue := ⟨1929503, pr1929503⟩
private theorem pr1929509 : PrimeCertificate 1929509 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv137,pv503]) (by decide +kernel)
def pv1929509 : PrimeValue := ⟨1929509, pr1929509⟩
private theorem pr1929563 : PrimeCertificate 1929563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41947]) (by decide +kernel)
def pv1929563 : PrimeValue := ⟨1929563, pr1929563⟩
private theorem pr1929569 : PrimeCertificate 1929569 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv3547]) (by decide +kernel)
def pv1929569 : PrimeValue := ⟨1929569, pr1929569⟩
private theorem pr1929923 : PrimeCertificate 1929923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv13591]) (by decide +kernel)
def pv1929923 : PrimeValue := ⟨1929923, pr1929923⟩
private theorem pr1930073 : PrimeCertificate 1930073 :=
  certifyPrime (q := pv3) (ls := [pv2,pv241259]) (by decide +kernel)
def pv1930073 : PrimeValue := ⟨1930073, pr1930073⟩
private theorem pr1930133 : PrimeCertificate 1930133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv499,pv967]) (by decide +kernel)
def pv1930133 : PrimeValue := ⟨1930133, pr1930133⟩
private theorem pr1930433 : PrimeCertificate 1930433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv31,pv139]) (by decide +kernel)
def pv1930433 : PrimeValue := ⟨1930433, pr1930433⟩
private theorem pr1930451 : PrimeCertificate 1930451 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv38609]) (by decide +kernel)
def pv1930451 : PrimeValue := ⟨1930451, pr1930451⟩
private theorem pr1930541 : PrimeCertificate 1930541 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv96527]) (by decide +kernel)
def pv1930541 : PrimeValue := ⟨1930541, pr1930541⟩
private theorem pr1930583 : PrimeCertificate 1930583 :=
  certifyPrime (q := pv5) (ls := [pv2,pv965291]) (by decide +kernel)
def pv1930583 : PrimeValue := ⟨1930583, pr1930583⟩
private theorem pr1930793 : PrimeCertificate 1930793 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv14197]) (by decide +kernel)
def pv1930793 : PrimeValue := ⟨1930793, pr1930793⟩
private theorem pr1930931 : PrimeCertificate 1930931 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv193093]) (by decide +kernel)
def pv1930931 : PrimeValue := ⟨1930931, pr1930931⟩
private theorem pr1931213 : PrimeCertificate 1931213 :=
  certifyPrime (q := pv2) (ls := [pv2,pv482803]) (by decide +kernel)
def pv1931213 : PrimeValue := ⟨1931213, pr1931213⟩
private theorem pr1931651 : PrimeCertificate 1931651 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv5519]) (by decide +kernel)
def pv1931651 : PrimeValue := ⟨1931651, pr1931651⟩
private theorem pr1931669 : PrimeCertificate 1931669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv482917]) (by decide +kernel)
def pv1931669 : PrimeValue := ⟨1931669, pr1931669⟩
private theorem pr1931801 : PrimeCertificate 1931801 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv13,pv743]) (by decide +kernel)
def pv1931801 : PrimeValue := ⟨1931801, pr1931801⟩
private theorem pr1931843 : PrimeCertificate 1931843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv87811]) (by decide +kernel)
def pv1931843 : PrimeValue := ⟨1931843, pr1931843⟩
private theorem pr1931921 : PrimeCertificate 1931921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv19,pv31,pv41]) (by decide +kernel)
def pv1931921 : PrimeValue := ⟨1931921, pr1931921⟩
private theorem pr1932341 : PrimeCertificate 1932341 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv79,pv1223]) (by decide +kernel)
def pv1932341 : PrimeValue := ⟨1932341, pr1932341⟩
private theorem pr1932401 : PrimeCertificate 1932401 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv4831]) (by decide +kernel)
def pv1932401 : PrimeValue := ⟨1932401, pr1932401⟩
private theorem pr1932503 : PrimeCertificate 1932503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv13,pv29,pv233]) (by decide +kernel)
def pv1932503 : PrimeValue := ⟨1932503, pr1932503⟩
private theorem pr1932641 : PrimeCertificate 1932641 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv47,pv257]) (by decide +kernel)
def pv1932641 : PrimeValue := ⟨1932641, pr1932641⟩
private theorem pr1932761 : PrimeCertificate 1932761 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv211,pv229]) (by decide +kernel)
def pv1932761 : PrimeValue := ⟨1932761, pr1932761⟩
private theorem pr1932923 : PrimeCertificate 1932923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv20563]) (by decide +kernel)
def pv1932923 : PrimeValue := ⟨1932923, pr1932923⟩
private theorem pr1933049 : PrimeCertificate 1933049 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv18587]) (by decide +kernel)
def pv1933049 : PrimeValue := ⟨1933049, pr1933049⟩
private theorem pr1933199 : PrimeCertificate 1933199 :=
  certifyPrime (q := pv7) (ls := [pv2,pv29,pv33331]) (by decide +kernel)
def pv1933199 : PrimeValue := ⟨1933199, pr1933199⟩
private theorem pr1933433 : PrimeCertificate 1933433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv241679]) (by decide +kernel)
def pv1933433 : PrimeValue := ⟨1933433, pr1933433⟩
private theorem pr1933523 : PrimeCertificate 1933523 :=
  certifyPrime (q := pv2) (ls := [pv2,pv797,pv1213]) (by decide +kernel)
def pv1933523 : PrimeValue := ⟨1933523, pr1933523⟩
private theorem pr1933661 : PrimeCertificate 1933661 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv109,pv887]) (by decide +kernel)
def pv1933661 : PrimeValue := ⟨1933661, pr1933661⟩
private theorem pr1933973 : PrimeCertificate 1933973 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv25447]) (by decide +kernel)
def pv1933973 : PrimeValue := ⟨1933973, pr1933973⟩
private theorem pr1934021 : PrimeCertificate 1934021 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv11,pv59,pv149]) (by decide +kernel)
def pv1934021 : PrimeValue := ⟨1934021, pr1934021⟩
private theorem pr1934381 : PrimeCertificate 1934381 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv7,pv41,pv337]) (by decide +kernel)
def pv1934381 : PrimeValue := ⟨1934381, pr1934381⟩
private theorem pr1934843 : PrimeCertificate 1934843 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv13,pv10631]) (by decide +kernel)
def pv1934843 : PrimeValue := ⟨1934843, pr1934843⟩
private theorem pr1934879 : PrimeCertificate 1934879 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv37,pv2377]) (by decide +kernel)
def pv1934879 : PrimeValue := ⟨1934879, pr1934879⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
