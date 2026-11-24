/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table022
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table022.pv54011
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table004
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table012

set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr54011 : Nat.Prime 54011 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv491]) (by decide +kernel)
def pv54011 : PrimeValue := ⟨54011, pr54011⟩
private theorem pr54013 : Nat.Prime 54013 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv643]) (by decide +kernel)
def pv54013 : PrimeValue := ⟨54013, pr54013⟩
private theorem pr54037 : Nat.Prime 54037 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv79]) (by decide +kernel)
def pv54037 : PrimeValue := ⟨54037, pr54037⟩
private theorem pr54049 : Nat.Prime 54049 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv563]) (by decide +kernel)
def pv54049 : PrimeValue := ⟨54049, pr54049⟩
private theorem pr54059 : Nat.Prime 54059 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv151,pv179]) (by decide +kernel)
def pv54059 : PrimeValue := ⟨54059, pr54059⟩
private theorem pr54083 : Nat.Prime 54083 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv3863]) (by decide +kernel)
def pv54083 : PrimeValue := ⟨54083, pr54083⟩
private theorem pr54091 : Nat.Prime 54091 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv601]) (by decide +kernel)
def pv54091 : PrimeValue := ⟨54091, pr54091⟩
private theorem pr54101 : Nat.Prime 54101 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv541]) (by decide +kernel)
def pv54101 : PrimeValue := ⟨54101, pr54101⟩
private theorem pr54121 : Nat.Prime 54121 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv11,pv41]) (by decide +kernel)
def pv54121 : PrimeValue := ⟨54121, pr54121⟩
private theorem pr54133 : Nat.Prime 54133 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv347]) (by decide +kernel)
def pv54133 : PrimeValue := ⟨54133, pr54133⟩
private theorem pr54139 : Nat.Prime 54139 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv1289]) (by decide +kernel)
def pv54139 : PrimeValue := ⟨54139, pr54139⟩
private theorem pr54151 : Nat.Prime 54151 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv54151 : PrimeValue := ⟨54151, pr54151⟩
private theorem pr54163 : Nat.Prime 54163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv59]) (by decide +kernel)
def pv54163 : PrimeValue := ⟨54163, pr54163⟩
private theorem pr54167 : Nat.Prime 54167 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv53,pv73]) (by decide +kernel)
def pv54167 : PrimeValue := ⟨54167, pr54167⟩
private theorem pr54181 : Nat.Prime 54181 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv43]) (by decide +kernel)
def pv54181 : PrimeValue := ⟨54181, pr54181⟩
private theorem pr54193 : Nat.Prime 54193 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv1129]) (by decide +kernel)
def pv54193 : PrimeValue := ⟨54193, pr54193⟩
private theorem pr54217 : Nat.Prime 54217 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv54217 : PrimeValue := ⟨54217, pr54217⟩
private theorem pr54251 : Nat.Prime 54251 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv54251 : PrimeValue := ⟨54251, pr54251⟩
private theorem pr54269 : Nat.Prime 54269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13567]) (by decide +kernel)
def pv54269 : PrimeValue := ⟨54269, pr54269⟩
private theorem pr54277 : Nat.Prime 54277 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv4523]) (by decide +kernel)
def pv54277 : PrimeValue := ⟨54277, pr54277⟩
private theorem pr54287 : Nat.Prime 54287 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv27143]) (by decide +kernel)
def pv54287 : PrimeValue := ⟨54287, pr54287⟩
private theorem pr54293 : Nat.Prime 54293 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv277]) (by decide +kernel)
def pv54293 : PrimeValue := ⟨54293, pr54293⟩
private theorem pr54311 : Nat.Prime 54311 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv5431]) (by decide +kernel)
def pv54311 : PrimeValue := ⟨54311, pr54311⟩
private theorem pr54319 : Nat.Prime 54319 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv823]) (by decide +kernel)
def pv54319 : PrimeValue := ⟨54319, pr54319⟩
private theorem pr54323 : Nat.Prime 54323 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv157,pv173]) (by decide +kernel)
def pv54323 : PrimeValue := ⟨54323, pr54323⟩
private theorem pr54331 : Nat.Prime 54331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1811]) (by decide +kernel)
def pv54331 : PrimeValue := ⟨54331, pr54331⟩
private theorem pr54347 : Nat.Prime 54347 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv29,pv937]) (by decide +kernel)
def pv54347 : PrimeValue := ⟨54347, pr54347⟩
private theorem pr54361 : Nat.Prime 54361 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv151]) (by decide +kernel)
def pv54361 : PrimeValue := ⟨54361, pr54361⟩
private theorem pr54367 : Nat.Prime 54367 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv41]) (by decide +kernel)
def pv54367 : PrimeValue := ⟨54367, pr54367⟩
private theorem pr54371 : Nat.Prime 54371 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv5437]) (by decide +kernel)
def pv54371 : PrimeValue := ⟨54371, pr54371⟩
private theorem pr54377 : Nat.Prime 54377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv971]) (by decide +kernel)
def pv54377 : PrimeValue := ⟨54377, pr54377⟩
private theorem pr54401 : Nat.Prime 54401 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv54401 : PrimeValue := ⟨54401, pr54401⟩
private theorem pr54403 : Nat.Prime 54403 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9067]) (by decide +kernel)
def pv54403 : PrimeValue := ⟨54403, pr54403⟩
private theorem pr54409 : Nat.Prime 54409 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv2267]) (by decide +kernel)
def pv54409 : PrimeValue := ⟨54409, pr54409⟩
private theorem pr54413 : Nat.Prime 54413 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv223]) (by decide +kernel)
def pv54413 : PrimeValue := ⟨54413, pr54413⟩
private theorem pr54419 : Nat.Prime 54419 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv13,pv23]) (by decide +kernel)
def pv54419 : PrimeValue := ⟨54419, pr54419⟩
private theorem pr54421 : Nat.Prime 54421 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv907]) (by decide +kernel)
def pv54421 : PrimeValue := ⟨54421, pr54421⟩
private theorem pr54437 : Nat.Prime 54437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv31,pv439]) (by decide +kernel)
def pv54437 : PrimeValue := ⟨54437, pr54437⟩
private theorem pr54443 : Nat.Prime 54443 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv163,pv167]) (by decide +kernel)
def pv54443 : PrimeValue := ⟨54443, pr54443⟩
private theorem pr54449 : Nat.Prime 54449 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv83]) (by decide +kernel)
def pv54449 : PrimeValue := ⟨54449, pr54449⟩
private theorem pr54469 : Nat.Prime 54469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv89]) (by decide +kernel)
def pv54469 : PrimeValue := ⟨54469, pr54469⟩
private theorem pr54493 : Nat.Prime 54493 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv239]) (by decide +kernel)
def pv54493 : PrimeValue := ⟨54493, pr54493⟩
private theorem pr54497 : Nat.Prime 54497 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv131]) (by decide +kernel)
def pv54497 : PrimeValue := ⟨54497, pr54497⟩
private theorem pr54499 : Nat.Prime 54499 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv293]) (by decide +kernel)
def pv54499 : PrimeValue := ⟨54499, pr54499⟩
private theorem pr54503 : Nat.Prime 54503 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv17,pv229]) (by decide +kernel)
def pv54503 : PrimeValue := ⟨54503, pr54503⟩
private theorem pr54517 : Nat.Prime 54517 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv11,pv59]) (by decide +kernel)
def pv54517 : PrimeValue := ⟨54517, pr54517⟩
private theorem pr54521 : Nat.Prime 54521 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv29,pv47]) (by decide +kernel)
def pv54521 : PrimeValue := ⟨54521, pr54521⟩
private theorem pr54539 : Nat.Prime 54539 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv37,pv67]) (by decide +kernel)
def pv54539 : PrimeValue := ⟨54539, pr54539⟩
private theorem pr54541 : Nat.Prime 54541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv54541 : PrimeValue := ⟨54541, pr54541⟩
private theorem pr54547 : Nat.Prime 54547 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9091]) (by decide +kernel)
def pv54547 : PrimeValue := ⟨54547, pr54547⟩
private theorem pr54559 : Nat.Prime 54559 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv433]) (by decide +kernel)
def pv54559 : PrimeValue := ⟨54559, pr54559⟩
private theorem pr54563 : Nat.Prime 54563 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv27281]) (by decide +kernel)
def pv54563 : PrimeValue := ⟨54563, pr54563⟩
private theorem pr54577 : Nat.Prime 54577 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv379]) (by decide +kernel)
def pv54577 : PrimeValue := ⟨54577, pr54577⟩
private theorem pr54581 : Nat.Prime 54581 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv2729]) (by decide +kernel)
def pv54581 : PrimeValue := ⟨54581, pr54581⟩
private theorem pr54583 : Nat.Prime 54583 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv827]) (by decide +kernel)
def pv54583 : PrimeValue := ⟨54583, pr54583⟩
private theorem pr54601 : Nat.Prime 54601 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv54601 : PrimeValue := ⟨54601, pr54601⟩
private theorem pr54617 : Nat.Prime 54617 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6827]) (by decide +kernel)
def pv54617 : PrimeValue := ⟨54617, pr54617⟩
private theorem pr54623 : Nat.Prime 54623 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv31,pv881]) (by decide +kernel)
def pv54623 : PrimeValue := ⟨54623, pr54623⟩
private theorem pr54629 : Nat.Prime 54629 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv1951]) (by decide +kernel)
def pv54629 : PrimeValue := ⟨54629, pr54629⟩
private theorem pr54631 : Nat.Prime 54631 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv607]) (by decide +kernel)
def pv54631 : PrimeValue := ⟨54631, pr54631⟩
private theorem pr54647 : Nat.Prime 54647 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv89,pv307]) (by decide +kernel)
def pv54647 : PrimeValue := ⟨54647, pr54647⟩
private theorem pr54667 : Nat.Prime 54667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3037]) (by decide +kernel)
def pv54667 : PrimeValue := ⟨54667, pr54667⟩
private theorem pr54673 : Nat.Prime 54673 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv67]) (by decide +kernel)
def pv54673 : PrimeValue := ⟨54673, pr54673⟩
private theorem pr54679 : Nat.Prime 54679 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv13,pv701]) (by decide +kernel)
def pv54679 : PrimeValue := ⟨54679, pr54679⟩
private theorem pr54713 : Nat.Prime 54713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv977]) (by decide +kernel)
def pv54713 : PrimeValue := ⟨54713, pr54713⟩
private theorem pr54721 : Nat.Prime 54721 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19]) (by decide +kernel)
def pv54721 : PrimeValue := ⟨54721, pr54721⟩
private theorem pr54727 : Nat.Prime 54727 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv1303]) (by decide +kernel)
def pv54727 : PrimeValue := ⟨54727, pr54727⟩
private theorem pr54751 : Nat.Prime 54751 :=
  checkPrime_prime (q := pv31) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv54751 : PrimeValue := ⟨54751, pr54751⟩
private theorem pr54767 : Nat.Prime 54767 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv139,pv197]) (by decide +kernel)
def pv54767 : PrimeValue := ⟨54767, pr54767⟩
private theorem pr54773 : Nat.Prime 54773 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13693]) (by decide +kernel)
def pv54773 : PrimeValue := ⟨54773, pr54773⟩
private theorem pr54779 : Nat.Prime 54779 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv61,pv449]) (by decide +kernel)
def pv54779 : PrimeValue := ⟨54779, pr54779⟩
private theorem pr54787 : Nat.Prime 54787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv397]) (by decide +kernel)
def pv54787 : PrimeValue := ⟨54787, pr54787⟩
private theorem pr54799 : Nat.Prime 54799 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9133]) (by decide +kernel)
def pv54799 : PrimeValue := ⟨54799, pr54799⟩
private theorem pr54829 : Nat.Prime 54829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv1523]) (by decide +kernel)
def pv54829 : PrimeValue := ⟨54829, pr54829⟩
private theorem pr54833 : Nat.Prime 54833 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv149]) (by decide +kernel)
def pv54833 : PrimeValue := ⟨54833, pr54833⟩
private theorem pr54851 : Nat.Prime 54851 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv1097]) (by decide +kernel)
def pv54851 : PrimeValue := ⟨54851, pr54851⟩
private theorem pr54869 : Nat.Prime 54869 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv29,pv43]) (by decide +kernel)
def pv54869 : PrimeValue := ⟨54869, pr54869⟩
private theorem pr54877 : Nat.Prime 54877 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv269]) (by decide +kernel)
def pv54877 : PrimeValue := ⟨54877, pr54877⟩
private theorem pr54881 : Nat.Prime 54881 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7]) (by decide +kernel)
def pv54881 : PrimeValue := ⟨54881, pr54881⟩
private theorem pr54907 : Nat.Prime 54907 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9151]) (by decide +kernel)
def pv54907 : PrimeValue := ⟨54907, pr54907⟩
private theorem pr54917 : Nat.Prime 54917 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13729]) (by decide +kernel)
def pv54917 : PrimeValue := ⟨54917, pr54917⟩
private theorem pr54919 : Nat.Prime 54919 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv113]) (by decide +kernel)
def pv54919 : PrimeValue := ⟨54919, pr54919⟩
private theorem pr54941 : Nat.Prime 54941 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv67]) (by decide +kernel)
def pv54941 : PrimeValue := ⟨54941, pr54941⟩
private theorem pr54949 : Nat.Prime 54949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv19,pv241]) (by decide +kernel)
def pv54949 : PrimeValue := ⟨54949, pr54949⟩
private theorem pr54959 : Nat.Prime 54959 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv27479]) (by decide +kernel)
def pv54959 : PrimeValue := ⟨54959, pr54959⟩
private theorem pr54979 : Nat.Prime 54979 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv11,pv17]) (by decide +kernel)
def pv54979 : PrimeValue := ⟨54979, pr54979⟩
private theorem pr54983 : Nat.Prime 54983 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv37,pv743]) (by decide +kernel)
def pv54983 : PrimeValue := ⟨54983, pr54983⟩
private theorem pr55001 : Nat.Prime 55001 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv11]) (by decide +kernel)
def pv55001 : PrimeValue := ⟨55001, pr55001⟩
private theorem pr55009 : Nat.Prime 55009 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv191]) (by decide +kernel)
def pv55009 : PrimeValue := ⟨55009, pr55009⟩
private theorem pr55021 : Nat.Prime 55021 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv7,pv131]) (by decide +kernel)
def pv55021 : PrimeValue := ⟨55021, pr55021⟩
private theorem pr55049 : Nat.Prime 55049 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv983]) (by decide +kernel)
def pv55049 : PrimeValue := ⟨55049, pr55049⟩
private theorem pr55051 : Nat.Prime 55051 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv367]) (by decide +kernel)
def pv55051 : PrimeValue := ⟨55051, pr55051⟩
private theorem pr55057 : Nat.Prime 55057 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv31,pv37]) (by decide +kernel)
def pv55057 : PrimeValue := ⟨55057, pr55057⟩
private theorem pr55061 : Nat.Prime 55061 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2753]) (by decide +kernel)
def pv55061 : PrimeValue := ⟨55061, pr55061⟩
private theorem pr55073 : Nat.Prime 55073 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1721]) (by decide +kernel)
def pv55073 : PrimeValue := ⟨55073, pr55073⟩
private theorem pr55079 : Nat.Prime 55079 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv27539]) (by decide +kernel)
def pv55079 : PrimeValue := ⟨55079, pr55079⟩
private theorem pr55103 : Nat.Prime 55103 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv27551]) (by decide +kernel)
def pv55103 : PrimeValue := ⟨55103, pr55103⟩
private theorem pr55109 : Nat.Prime 55109 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv23,pv599]) (by decide +kernel)
def pv55109 : PrimeValue := ⟨55109, pr55109⟩
private theorem pr55117 : Nat.Prime 55117 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv1531]) (by decide +kernel)
def pv55117 : PrimeValue := ⟨55117, pr55117⟩
private theorem pr55127 : Nat.Prime 55127 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv43,pv641]) (by decide +kernel)
def pv55127 : PrimeValue := ⟨55127, pr55127⟩
private theorem pr55147 : Nat.Prime 55147 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv13,pv101]) (by decide +kernel)
def pv55147 : PrimeValue := ⟨55147, pr55147⟩
private theorem pr55163 : Nat.Prime 55163 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv27581]) (by decide +kernel)
def pv55163 : PrimeValue := ⟨55163, pr55163⟩
private theorem pr55171 : Nat.Prime 55171 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv5,pv613]) (by decide +kernel)
def pv55171 : PrimeValue := ⟨55171, pr55171⟩
private theorem pr55201 : Nat.Prime 55201 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv23]) (by decide +kernel)
def pv55201 : PrimeValue := ⟨55201, pr55201⟩
private theorem pr55207 : Nat.Prime 55207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv3067]) (by decide +kernel)
def pv55207 : PrimeValue := ⟨55207, pr55207⟩
private theorem pr55213 : Nat.Prime 55213 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv43,pv107]) (by decide +kernel)
def pv55213 : PrimeValue := ⟨55213, pr55213⟩
private theorem pr55217 : Nat.Prime 55217 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv17,pv29]) (by decide +kernel)
def pv55217 : PrimeValue := ⟨55217, pr55217⟩
private theorem pr55219 : Nat.Prime 55219 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv9203]) (by decide +kernel)
def pv55219 : PrimeValue := ⟨55219, pr55219⟩
private theorem pr55229 : Nat.Prime 55229 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13807]) (by decide +kernel)
def pv55229 : PrimeValue := ⟨55229, pr55229⟩
private theorem pr55243 : Nat.Prime 55243 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv31]) (by decide +kernel)
def pv55243 : PrimeValue := ⟨55243, pr55243⟩
private theorem pr55249 : Nat.Prime 55249 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv1151]) (by decide +kernel)
def pv55249 : PrimeValue := ⟨55249, pr55249⟩
private theorem pr55259 : Nat.Prime 55259 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv3947]) (by decide +kernel)
def pv55259 : PrimeValue := ⟨55259, pr55259⟩
private theorem pr55291 : Nat.Prime 55291 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv19,pv97]) (by decide +kernel)
def pv55291 : PrimeValue := ⟨55291, pr55291⟩
private theorem pr55313 : Nat.Prime 55313 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3457]) (by decide +kernel)
def pv55313 : PrimeValue := ⟨55313, pr55313⟩
private theorem pr55331 : Nat.Prime 55331 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv503]) (by decide +kernel)
def pv55331 : PrimeValue := ⟨55331, pr55331⟩
private theorem pr55333 : Nat.Prime 55333 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv29,pv53]) (by decide +kernel)
def pv55333 : PrimeValue := ⟨55333, pr55333⟩
private theorem pr55337 : Nat.Prime 55337 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6917]) (by decide +kernel)
def pv55337 : PrimeValue := ⟨55337, pr55337⟩
private theorem pr55339 : Nat.Prime 55339 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv23,pv401]) (by decide +kernel)
def pv55339 : PrimeValue := ⟨55339, pr55339⟩
private theorem pr55343 : Nat.Prime 55343 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv7,pv59,pv67]) (by decide +kernel)
def pv55343 : PrimeValue := ⟨55343, pr55343⟩
private theorem pr55351 : Nat.Prime 55351 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv41]) (by decide +kernel)
def pv55351 : PrimeValue := ⟨55351, pr55351⟩
private theorem pr55373 : Nat.Prime 55373 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv109,pv127]) (by decide +kernel)
def pv55373 : PrimeValue := ⟨55373, pr55373⟩
private theorem pr55381 : Nat.Prime 55381 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv13,pv71]) (by decide +kernel)
def pv55381 : PrimeValue := ⟨55381, pr55381⟩
private theorem pr55399 : Nat.Prime 55399 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv1319]) (by decide +kernel)
def pv55399 : PrimeValue := ⟨55399, pr55399⟩
private theorem pr55411 : Nat.Prime 55411 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1847]) (by decide +kernel)
def pv55411 : PrimeValue := ⟨55411, pr55411⟩
private theorem pr55439 : Nat.Prime 55439 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv53,pv523]) (by decide +kernel)
def pv55439 : PrimeValue := ⟨55439, pr55439⟩
private theorem pr55441 : Nat.Prime 55441 :=
  checkPrime_prime (q := pv59) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv55441 : PrimeValue := ⟨55441, pr55441⟩
private theorem pr55457 : Nat.Prime 55457 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv1733]) (by decide +kernel)
def pv55457 : PrimeValue := ⟨55457, pr55457⟩
private theorem pr55469 : Nat.Prime 55469 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv283]) (by decide +kernel)
def pv55469 : PrimeValue := ⟨55469, pr55469⟩
private theorem pr55487 : Nat.Prime 55487 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv27743]) (by decide +kernel)
def pv55487 : PrimeValue := ⟨55487, pr55487⟩
private theorem pr55501 : Nat.Prime 55501 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv37]) (by decide +kernel)
def pv55501 : PrimeValue := ⟨55501, pr55501⟩
private theorem pr55511 : Nat.Prime 55511 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv5,pv7,pv13,pv61]) (by decide +kernel)
def pv55511 : PrimeValue := ⟨55511, pr55511⟩
private theorem pr55529 : Nat.Prime 55529 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv631]) (by decide +kernel)
def pv55529 : PrimeValue := ⟨55529, pr55529⟩
private theorem pr55541 : Nat.Prime 55541 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv2777]) (by decide +kernel)
def pv55541 : PrimeValue := ⟨55541, pr55541⟩
private theorem pr55547 : Nat.Prime 55547 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv27773]) (by decide +kernel)
def pv55547 : PrimeValue := ⟨55547, pr55547⟩
private theorem pr55579 : Nat.Prime 55579 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv157]) (by decide +kernel)
def pv55579 : PrimeValue := ⟨55579, pr55579⟩
private theorem pr55589 : Nat.Prime 55589 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv1069]) (by decide +kernel)
def pv55589 : PrimeValue := ⟨55589, pr55589⟩
private theorem pr55603 : Nat.Prime 55603 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3089]) (by decide +kernel)
def pv55603 : PrimeValue := ⟨55603, pr55603⟩
private theorem pr55609 : Nat.Prime 55609 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv331]) (by decide +kernel)
def pv55609 : PrimeValue := ⟨55609, pr55609⟩
private theorem pr55619 : Nat.Prime 55619 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv27809]) (by decide +kernel)
def pv55619 : PrimeValue := ⟨55619, pr55619⟩
private theorem pr55621 : Nat.Prime 55621 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv103]) (by decide +kernel)
def pv55621 : PrimeValue := ⟨55621, pr55621⟩
private theorem pr55631 : Nat.Prime 55631 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv5563]) (by decide +kernel)
def pv55631 : PrimeValue := ⟨55631, pr55631⟩
private theorem pr55633 : Nat.Prime 55633 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv19,pv61]) (by decide +kernel)
def pv55633 : PrimeValue := ⟨55633, pr55633⟩
private theorem pr55639 : Nat.Prime 55639 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv281]) (by decide +kernel)
def pv55639 : PrimeValue := ⟨55639, pr55639⟩
private theorem pr55661 : Nat.Prime 55661 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv11,pv23]) (by decide +kernel)
def pv55661 : PrimeValue := ⟨55661, pr55661⟩
private theorem pr55663 : Nat.Prime 55663 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9277]) (by decide +kernel)
def pv55663 : PrimeValue := ⟨55663, pr55663⟩
private theorem pr55667 : Nat.Prime 55667 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13,pv2141]) (by decide +kernel)
def pv55667 : PrimeValue := ⟨55667, pr55667⟩
private theorem pr55673 : Nat.Prime 55673 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6959]) (by decide +kernel)
def pv55673 : PrimeValue := ⟨55673, pr55673⟩
private theorem pr55681 : Nat.Prime 55681 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv5,pv29]) (by decide +kernel)
def pv55681 : PrimeValue := ⟨55681, pr55681⟩
private theorem pr55691 : Nat.Prime 55691 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv5569]) (by decide +kernel)
def pv55691 : PrimeValue := ⟨55691, pr55691⟩
private theorem pr55697 : Nat.Prime 55697 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv59]) (by decide +kernel)
def pv55697 : PrimeValue := ⟨55697, pr55697⟩
private theorem pr55711 : Nat.Prime 55711 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv619]) (by decide +kernel)
def pv55711 : PrimeValue := ⟨55711, pr55711⟩
private theorem pr55717 : Nat.Prime 55717 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4643]) (by decide +kernel)
def pv55717 : PrimeValue := ⟨55717, pr55717⟩
private theorem pr55721 : Nat.Prime 55721 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv7,pv199]) (by decide +kernel)
def pv55721 : PrimeValue := ⟨55721, pr55721⟩
private theorem pr55733 : Nat.Prime 55733 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13933]) (by decide +kernel)
def pv55733 : PrimeValue := ⟨55733, pr55733⟩
private theorem pr55763 : Nat.Prime 55763 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv569]) (by decide +kernel)
def pv55763 : PrimeValue := ⟨55763, pr55763⟩
private theorem pr55787 : Nat.Prime 55787 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv27893]) (by decide +kernel)
def pv55787 : PrimeValue := ⟨55787, pr55787⟩
private theorem pr55793 : Nat.Prime 55793 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv11,pv317]) (by decide +kernel)
def pv55793 : PrimeValue := ⟨55793, pr55793⟩
private theorem pr55799 : Nat.Prime 55799 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv23,pv1213]) (by decide +kernel)
def pv55799 : PrimeValue := ⟨55799, pr55799⟩
private theorem pr55807 : Nat.Prime 55807 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv71,pv131]) (by decide +kernel)
def pv55807 : PrimeValue := ⟨55807, pr55807⟩
private theorem pr55813 : Nat.Prime 55813 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4651]) (by decide +kernel)
def pv55813 : PrimeValue := ⟨55813, pr55813⟩
private theorem pr55817 : Nat.Prime 55817 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv6977]) (by decide +kernel)
def pv55817 : PrimeValue := ⟨55817, pr55817⟩
private theorem pr55819 : Nat.Prime 55819 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv443]) (by decide +kernel)
def pv55819 : PrimeValue := ⟨55819, pr55819⟩
private theorem pr55823 : Nat.Prime 55823 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv13,pv19,pv113]) (by decide +kernel)
def pv55823 : PrimeValue := ⟨55823, pr55823⟩
private theorem pr55829 : Nat.Prime 55829 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv821]) (by decide +kernel)
def pv55829 : PrimeValue := ⟨55829, pr55829⟩
private theorem pr55837 : Nat.Prime 55837 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv11,pv47]) (by decide +kernel)
def pv55837 : PrimeValue := ⟨55837, pr55837⟩
private theorem pr55843 : Nat.Prime 55843 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv41,pv227]) (by decide +kernel)
def pv55843 : PrimeValue := ⟨55843, pr55843⟩
private theorem pr55849 : Nat.Prime 55849 :=
  checkPrime_prime (q := pv41) (ls := [pv2,pv3,pv13,pv179]) (by decide +kernel)
def pv55849 : PrimeValue := ⟨55849, pr55849⟩
private theorem pr55871 : Nat.Prime 55871 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv37,pv151]) (by decide +kernel)
def pv55871 : PrimeValue := ⟨55871, pr55871⟩
private theorem pr55889 : Nat.Prime 55889 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv499]) (by decide +kernel)
def pv55889 : PrimeValue := ⟨55889, pr55889⟩
private theorem pr55897 : Nat.Prime 55897 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv137]) (by decide +kernel)
def pv55897 : PrimeValue := ⟨55897, pr55897⟩
private theorem pr55901 : Nat.Prime 55901 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv13,pv43]) (by decide +kernel)
def pv55901 : PrimeValue := ⟨55901, pr55901⟩
private theorem pr55903 : Nat.Prime 55903 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv55903 : PrimeValue := ⟨55903, pr55903⟩
private theorem pr55921 : Nat.Prime 55921 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv5,pv233]) (by decide +kernel)
def pv55921 : PrimeValue := ⟨55921, pr55921⟩
private theorem pr55927 : Nat.Prime 55927 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv13,pv239]) (by decide +kernel)
def pv55927 : PrimeValue := ⟨55927, pr55927⟩
private theorem pr55931 : Nat.Prime 55931 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv5,pv7,pv17,pv47]) (by decide +kernel)
def pv55931 : PrimeValue := ⟨55931, pr55931⟩
private theorem pr55933 : Nat.Prime 55933 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv59,pv79]) (by decide +kernel)
def pv55933 : PrimeValue := ⟨55933, pr55933⟩
private theorem pr55949 : Nat.Prime 55949 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv71,pv197]) (by decide +kernel)
def pv55949 : PrimeValue := ⟨55949, pr55949⟩
private theorem pr55967 : Nat.Prime 55967 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv27983]) (by decide +kernel)
def pv55967 : PrimeValue := ⟨55967, pr55967⟩
private theorem pr55987 : Nat.Prime 55987 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv31,pv43]) (by decide +kernel)
def pv55987 : PrimeValue := ⟨55987, pr55987⟩
private theorem pr55997 : Nat.Prime 55997 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv13999]) (by decide +kernel)
def pv55997 : PrimeValue := ⟨55997, pr55997⟩
private theorem pr56003 : Nat.Prime 56003 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv28001]) (by decide +kernel)
def pv56003 : PrimeValue := ⟨56003, pr56003⟩
private theorem pr56009 : Nat.Prime 56009 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7001]) (by decide +kernel)
def pv56009 : PrimeValue := ⟨56009, pr56009⟩
private theorem pr56039 : Nat.Prime 56039 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv28019]) (by decide +kernel)
def pv56039 : PrimeValue := ⟨56039, pr56039⟩
private theorem pr56041 : Nat.Prime 56041 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv467]) (by decide +kernel)
def pv56041 : PrimeValue := ⟨56041, pr56041⟩
private theorem pr56053 : Nat.Prime 56053 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv56053 : PrimeValue := ⟨56053, pr56053⟩
private theorem pr56081 : Nat.Prime 56081 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv701]) (by decide +kernel)
def pv56081 : PrimeValue := ⟨56081, pr56081⟩
private theorem pr56087 : Nat.Prime 56087 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv29,pv967]) (by decide +kernel)
def pv56087 : PrimeValue := ⟨56087, pr56087⟩
private theorem pr56093 : Nat.Prime 56093 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv37,pv379]) (by decide +kernel)
def pv56093 : PrimeValue := ⟨56093, pr56093⟩
private theorem pr56099 : Nat.Prime 56099 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4007]) (by decide +kernel)
def pv56099 : PrimeValue := ⟨56099, pr56099⟩
private theorem pr56101 : Nat.Prime 56101 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv17]) (by decide +kernel)
def pv56101 : PrimeValue := ⟨56101, pr56101⟩
private theorem pr56113 : Nat.Prime 56113 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv167]) (by decide +kernel)
def pv56113 : PrimeValue := ⟨56113, pr56113⟩
private theorem pr56123 : Nat.Prime 56123 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv2551]) (by decide +kernel)
def pv56123 : PrimeValue := ⟨56123, pr56123⟩
private theorem pr56131 : Nat.Prime 56131 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv1871]) (by decide +kernel)
def pv56131 : PrimeValue := ⟨56131, pr56131⟩
private theorem pr56149 : Nat.Prime 56149 :=
  checkPrime_prime (q := pv37) (ls := [pv2,pv3,pv4679]) (by decide +kernel)
def pv56149 : PrimeValue := ⟨56149, pr56149⟩
private theorem pr56167 : Nat.Prime 56167 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv11,pv23,pv37]) (by decide +kernel)
def pv56167 : PrimeValue := ⟨56167, pr56167⟩
private theorem pr56171 : Nat.Prime 56171 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv41,pv137]) (by decide +kernel)
def pv56171 : PrimeValue := ⟨56171, pr56171⟩
private theorem pr56179 : Nat.Prime 56179 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv3121]) (by decide +kernel)
def pv56179 : PrimeValue := ⟨56179, pr56179⟩
private theorem pr56197 : Nat.Prime 56197 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv7,pv223]) (by decide +kernel)
def pv56197 : PrimeValue := ⟨56197, pr56197⟩
private theorem pr56207 : Nat.Prime 56207 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv157,pv179]) (by decide +kernel)
def pv56207 : PrimeValue := ⟨56207, pr56207⟩
private theorem pr56209 : Nat.Prime 56209 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv3,pv1171]) (by decide +kernel)
def pv56209 : PrimeValue := ⟨56209, pr56209⟩
private theorem pr56237 : Nat.Prime 56237 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv17,pv827]) (by decide +kernel)
def pv56237 : PrimeValue := ⟨56237, pr56237⟩
private theorem pr56239 : Nat.Prime 56239 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv7,pv13,pv103]) (by decide +kernel)
def pv56239 : PrimeValue := ⟨56239, pr56239⟩
private theorem pr56249 : Nat.Prime 56249 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv79,pv89]) (by decide +kernel)
def pv56249 : PrimeValue := ⟨56249, pr56249⟩
private theorem pr56263 : Nat.Prime 56263 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9377]) (by decide +kernel)
def pv56263 : PrimeValue := ⟨56263, pr56263⟩
private theorem pr56267 : Nat.Prime 56267 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv4019]) (by decide +kernel)
def pv56267 : PrimeValue := ⟨56267, pr56267⟩
private theorem pr56269 : Nat.Prime 56269 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv521]) (by decide +kernel)
def pv56269 : PrimeValue := ⟨56269, pr56269⟩
private theorem pr56299 : Nat.Prime 56299 :=
  checkPrime_prime (q := pv17) (ls := [pv2,pv3,pv11,pv853]) (by decide +kernel)
def pv56299 : PrimeValue := ⟨56299, pr56299⟩
private theorem pr56311 : Nat.Prime 56311 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv1877]) (by decide +kernel)
def pv56311 : PrimeValue := ⟨56311, pr56311⟩
private theorem pr56333 : Nat.Prime 56333 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv14083]) (by decide +kernel)
def pv56333 : PrimeValue := ⟨56333, pr56333⟩
private theorem pr56359 : Nat.Prime 56359 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv31,pv101]) (by decide +kernel)
def pv56359 : PrimeValue := ⟨56359, pr56359⟩
private theorem pr56369 : Nat.Prime 56369 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv13,pv271]) (by decide +kernel)
def pv56369 : PrimeValue := ⟨56369, pr56369⟩
private theorem pr56377 : Nat.Prime 56377 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv56377 : PrimeValue := ⟨56377, pr56377⟩
private theorem pr56383 : Nat.Prime 56383 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9397]) (by decide +kernel)
def pv56383 : PrimeValue := ⟨56383, pr56383⟩
private theorem pr56393 : Nat.Prime 56393 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7,pv19,pv53]) (by decide +kernel)
def pv56393 : PrimeValue := ⟨56393, pr56393⟩
private theorem pr56401 : Nat.Prime 56401 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv56401 : PrimeValue := ⟨56401, pr56401⟩
private theorem pr56417 : Nat.Prime 56417 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv41,pv43]) (by decide +kernel)
def pv56417 : PrimeValue := ⟨56417, pr56417⟩
private theorem pr56431 : Nat.Prime 56431 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv11,pv19]) (by decide +kernel)
def pv56431 : PrimeValue := ⟨56431, pr56431⟩
private theorem pr56437 : Nat.Prime 56437 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv4703]) (by decide +kernel)
def pv56437 : PrimeValue := ⟨56437, pr56437⟩
private theorem pr56443 : Nat.Prime 56443 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv23,pv409]) (by decide +kernel)
def pv56443 : PrimeValue := ⟨56443, pr56443⟩
private theorem pr56453 : Nat.Prime 56453 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv11,pv1283]) (by decide +kernel)
def pv56453 : PrimeValue := ⟨56453, pr56453⟩
private theorem pr56467 : Nat.Prime 56467 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv3137]) (by decide +kernel)
def pv56467 : PrimeValue := ⟨56467, pr56467⟩
private theorem pr56473 : Nat.Prime 56473 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv13,pv181]) (by decide +kernel)
def pv56473 : PrimeValue := ⟨56473, pr56473⟩
private theorem pr56477 : Nat.Prime 56477 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv7,pv2017]) (by decide +kernel)
def pv56477 : PrimeValue := ⟨56477, pr56477⟩
private theorem pr56479 : Nat.Prime 56479 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv3,pv9413]) (by decide +kernel)
def pv56479 : PrimeValue := ⟨56479, pr56479⟩
private theorem pr56489 : Nat.Prime 56489 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv23,pv307]) (by decide +kernel)
def pv56489 : PrimeValue := ⟨56489, pr56489⟩
private theorem pr56501 : Nat.Prime 56501 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv113]) (by decide +kernel)
def pv56501 : PrimeValue := ⟨56501, pr56501⟩
private theorem pr56503 : Nat.Prime 56503 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv43,pv73]) (by decide +kernel)
def pv56503 : PrimeValue := ⟨56503, pr56503⟩
private theorem pr56509 : Nat.Prime 56509 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv17,pv277]) (by decide +kernel)
def pv56509 : PrimeValue := ⟨56509, pr56509⟩
private theorem pr56519 : Nat.Prime 56519 :=
  checkPrime_prime (q := pv13) (ls := [pv2,pv7,pv11,pv367]) (by decide +kernel)
def pv56519 : PrimeValue := ⟨56519, pr56519⟩
private theorem pr56527 : Nat.Prime 56527 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9421]) (by decide +kernel)
def pv56527 : PrimeValue := ⟨56527, pr56527⟩
private theorem pr56531 : Nat.Prime 56531 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv5,pv5653]) (by decide +kernel)
def pv56531 : PrimeValue := ⟨56531, pr56531⟩
private theorem pr56533 : Nat.Prime 56533 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv7,pv673]) (by decide +kernel)
def pv56533 : PrimeValue := ⟨56533, pr56533⟩
private theorem pr56543 : Nat.Prime 56543 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv17,pv1663]) (by decide +kernel)
def pv56543 : PrimeValue := ⟨56543, pr56543⟩
private theorem pr56569 : Nat.Prime 56569 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv2357]) (by decide +kernel)
def pv56569 : PrimeValue := ⟨56569, pr56569⟩
private theorem pr56591 : Nat.Prime 56591 :=
  checkPrime_prime (q := pv19) (ls := [pv2,pv5,pv5659]) (by decide +kernel)
def pv56591 : PrimeValue := ⟨56591, pr56591⟩
private theorem pr56597 : Nat.Prime 56597 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv14149]) (by decide +kernel)
def pv56597 : PrimeValue := ⟨56597, pr56597⟩
private theorem pr56599 : Nat.Prime 56599 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv9433]) (by decide +kernel)
def pv56599 : PrimeValue := ⟨56599, pr56599⟩
private theorem pr56611 : Nat.Prime 56611 :=
  checkPrime_prime (q := pv29) (ls := [pv2,pv3,pv5,pv17,pv37]) (by decide +kernel)
def pv56611 : PrimeValue := ⟨56611, pr56611⟩
private theorem pr56629 : Nat.Prime 56629 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv56629 : PrimeValue := ⟨56629, pr56629⟩
private theorem pr56633 : Nat.Prime 56633 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv7079]) (by decide +kernel)
def pv56633 : PrimeValue := ⟨56633, pr56633⟩
private theorem pr56659 : Nat.Prime 56659 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv7,pv19,pv71]) (by decide +kernel)
def pv56659 : PrimeValue := ⟨56659, pr56659⟩
private theorem pr56663 : Nat.Prime 56663 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv41,pv691]) (by decide +kernel)
def pv56663 : PrimeValue := ⟨56663, pr56663⟩
private theorem pr56671 : Nat.Prime 56671 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv3,pv5,pv1889]) (by decide +kernel)
def pv56671 : PrimeValue := ⟨56671, pr56671⟩
private theorem pr56681 : Nat.Prime 56681 :=
  checkPrime_prime (q := pv3) (ls := [pv2,pv5,pv13,pv109]) (by decide +kernel)
def pv56681 : PrimeValue := ⟨56681, pr56681⟩
private theorem pr56687 : Nat.Prime 56687 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv7,pv4049]) (by decide +kernel)
def pv56687 : PrimeValue := ⟨56687, pr56687⟩
private theorem pr56701 : Nat.Prime 56701 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv56701 : PrimeValue := ⟨56701, pr56701⟩
private theorem pr56711 : Nat.Prime 56711 :=
  checkPrime_prime (q := pv7) (ls := [pv2,pv5,pv53,pv107]) (by decide +kernel)
def pv56711 : PrimeValue := ⟨56711, pr56711⟩
private theorem pr56713 : Nat.Prime 56713 :=
  checkPrime_prime (q := pv5) (ls := [pv2,pv3,pv17,pv139]) (by decide +kernel)
def pv56713 : PrimeValue := ⟨56713, pr56713⟩
private theorem pr56731 : Nat.Prime 56731 :=
  checkPrime_prime (q := pv2) (ls := [pv2,pv3,pv5,pv31,pv61]) (by decide +kernel)
def pv56731 : PrimeValue := ⟨56731, pr56731⟩
private theorem pr56737 : Nat.Prime 56737 :=
  checkPrime_prime (q := pv11) (ls := [pv2,pv3,pv197]) (by decide +kernel)
def pv56737 : PrimeValue := ⟨56737, pr56737⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
