/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table004
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_GRH; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables00/Table004.pv7927
   digest: Shared Lucas certificates for the prime factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table002

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr7927 : PrimeCertificate 7927 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1321]) (by decide +kernel)
def pv7927 : PrimeValue := ⟨7927, pr7927⟩
private theorem pr7933 : PrimeCertificate 7933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv661]) (by decide +kernel)
def pv7933 : PrimeValue := ⟨7933, pr7933⟩
private theorem pr7937 : PrimeCertificate 7937 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31]) (by decide +kernel)
def pv7937 : PrimeValue := ⟨7937, pr7937⟩
private theorem pr7949 : PrimeCertificate 7949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv1987]) (by decide +kernel)
def pv7949 : PrimeValue := ⟨7949, pr7949⟩
private theorem pr7951 : PrimeCertificate 7951 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv53]) (by decide +kernel)
def pv7951 : PrimeValue := ⟨7951, pr7951⟩
private theorem pr7963 : PrimeCertificate 7963 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1327]) (by decide +kernel)
def pv7963 : PrimeValue := ⟨7963, pr7963⟩
private theorem pr7993 : PrimeCertificate 7993 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37]) (by decide +kernel)
def pv7993 : PrimeValue := ⟨7993, pr7993⟩
private theorem pr8009 : PrimeCertificate 8009 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv11,pv13]) (by decide +kernel)
def pv8009 : PrimeValue := ⟨8009, pr8009⟩
private theorem pr8011 : PrimeCertificate 8011 :=
  certifyPrime (q := pv43) (ls := [pv2,pv3,pv5,pv89]) (by decide +kernel)
def pv8011 : PrimeValue := ⟨8011, pr8011⟩
private theorem pr8017 : PrimeCertificate 8017 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv167]) (by decide +kernel)
def pv8017 : PrimeValue := ⟨8017, pr8017⟩
private theorem pr8039 : PrimeCertificate 8039 :=
  certifyPrime (q := pv11) (ls := [pv2,pv4019]) (by decide +kernel)
def pv8039 : PrimeValue := ⟨8039, pr8039⟩
private theorem pr8053 : PrimeCertificate 8053 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv61]) (by decide +kernel)
def pv8053 : PrimeValue := ⟨8053, pr8053⟩
private theorem pr8059 : PrimeCertificate 8059 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv79]) (by decide +kernel)
def pv8059 : PrimeValue := ⟨8059, pr8059⟩
private theorem pr8069 : PrimeCertificate 8069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2017]) (by decide +kernel)
def pv8069 : PrimeValue := ⟨8069, pr8069⟩
private theorem pr8081 : PrimeCertificate 8081 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv101]) (by decide +kernel)
def pv8081 : PrimeValue := ⟨8081, pr8081⟩
private theorem pr8087 : PrimeCertificate 8087 :=
  certifyPrime (q := pv5) (ls := [pv2,pv13,pv311]) (by decide +kernel)
def pv8087 : PrimeValue := ⟨8087, pr8087⟩
private theorem pr8089 : PrimeCertificate 8089 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv337]) (by decide +kernel)
def pv8089 : PrimeValue := ⟨8089, pr8089⟩
private theorem pr8093 : PrimeCertificate 8093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv17]) (by decide +kernel)
def pv8093 : PrimeValue := ⟨8093, pr8093⟩
private theorem pr8101 : PrimeCertificate 8101 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv8101 : PrimeValue := ⟨8101, pr8101⟩
private theorem pr8111 : PrimeCertificate 8111 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv811]) (by decide +kernel)
def pv8111 : PrimeValue := ⟨8111, pr8111⟩
private theorem pr8117 : PrimeCertificate 8117 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2029]) (by decide +kernel)
def pv8117 : PrimeValue := ⟨8117, pr8117⟩
private theorem pr8123 : PrimeCertificate 8123 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv131]) (by decide +kernel)
def pv8123 : PrimeValue := ⟨8123, pr8123⟩
private theorem pr8147 : PrimeCertificate 8147 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4073]) (by decide +kernel)
def pv8147 : PrimeValue := ⟨8147, pr8147⟩
private theorem pr8161 : PrimeCertificate 8161 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv8161 : PrimeValue := ⟨8161, pr8161⟩
private theorem pr8167 : PrimeCertificate 8167 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1361]) (by decide +kernel)
def pv8167 : PrimeValue := ⟨8167, pr8167⟩
private theorem pr8171 : PrimeCertificate 8171 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv43]) (by decide +kernel)
def pv8171 : PrimeValue := ⟨8171, pr8171⟩
private theorem pr8179 : PrimeCertificate 8179 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29,pv47]) (by decide +kernel)
def pv8179 : PrimeValue := ⟨8179, pr8179⟩
private theorem pr8191 : PrimeCertificate 8191 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv7,pv13]) (by decide +kernel)
def pv8191 : PrimeValue := ⟨8191, pr8191⟩
private theorem pr8209 : PrimeCertificate 8209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19]) (by decide +kernel)
def pv8209 : PrimeValue := ⟨8209, pr8209⟩
private theorem pr8219 : PrimeCertificate 8219 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv587]) (by decide +kernel)
def pv8219 : PrimeValue := ⟨8219, pr8219⟩
private theorem pr8221 : PrimeCertificate 8221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv137]) (by decide +kernel)
def pv8221 : PrimeValue := ⟨8221, pr8221⟩
private theorem pr8231 : PrimeCertificate 8231 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv823]) (by decide +kernel)
def pv8231 : PrimeValue := ⟨8231, pr8231⟩
private theorem pr8233 : PrimeCertificate 8233 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv7]) (by decide +kernel)
def pv8233 : PrimeValue := ⟨8233, pr8233⟩
private theorem pr8237 : PrimeCertificate 8237 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv71]) (by decide +kernel)
def pv8237 : PrimeValue := ⟨8237, pr8237⟩
private theorem pr8243 : PrimeCertificate 8243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv317]) (by decide +kernel)
def pv8243 : PrimeValue := ⟨8243, pr8243⟩
private theorem pr8263 : PrimeCertificate 8263 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17]) (by decide +kernel)
def pv8263 : PrimeValue := ⟨8263, pr8263⟩
private theorem pr8269 : PrimeCertificate 8269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv53]) (by decide +kernel)
def pv8269 : PrimeValue := ⟨8269, pr8269⟩
private theorem pr8273 : PrimeCertificate 8273 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv47]) (by decide +kernel)
def pv8273 : PrimeValue := ⟨8273, pr8273⟩
private theorem pr8287 : PrimeCertificate 8287 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1381]) (by decide +kernel)
def pv8287 : PrimeValue := ⟨8287, pr8287⟩
private theorem pr8291 : PrimeCertificate 8291 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv829]) (by decide +kernel)
def pv8291 : PrimeValue := ⟨8291, pr8291⟩
private theorem pr8293 : PrimeCertificate 8293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv691]) (by decide +kernel)
def pv8293 : PrimeValue := ⟨8293, pr8293⟩
private theorem pr8297 : PrimeCertificate 8297 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv61]) (by decide +kernel)
def pv8297 : PrimeValue := ⟨8297, pr8297⟩
private theorem pr8311 : PrimeCertificate 8311 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv277]) (by decide +kernel)
def pv8311 : PrimeValue := ⟨8311, pr8311⟩
private theorem pr8317 : PrimeCertificate 8317 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv11]) (by decide +kernel)
def pv8317 : PrimeValue := ⟨8317, pr8317⟩
private theorem pr8329 : PrimeCertificate 8329 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv347]) (by decide +kernel)
def pv8329 : PrimeValue := ⟨8329, pr8329⟩
private theorem pr8353 : PrimeCertificate 8353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv8353 : PrimeValue := ⟨8353, pr8353⟩
private theorem pr8363 : PrimeCertificate 8363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv113]) (by decide +kernel)
def pv8363 : PrimeValue := ⟨8363, pr8363⟩
private theorem pr8369 : PrimeCertificate 8369 :=
  certifyPrime (q := pv3) (ls := [pv2,pv523]) (by decide +kernel)
def pv8369 : PrimeValue := ⟨8369, pr8369⟩
private theorem pr8377 : PrimeCertificate 8377 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv349]) (by decide +kernel)
def pv8377 : PrimeValue := ⟨8377, pr8377⟩
private theorem pr8387 : PrimeCertificate 8387 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv599]) (by decide +kernel)
def pv8387 : PrimeValue := ⟨8387, pr8387⟩
private theorem pr8389 : PrimeCertificate 8389 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv233]) (by decide +kernel)
def pv8389 : PrimeValue := ⟨8389, pr8389⟩
private theorem pr8419 : PrimeCertificate 8419 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv23,pv61]) (by decide +kernel)
def pv8419 : PrimeValue := ⟨8419, pr8419⟩
private theorem pr8423 : PrimeCertificate 8423 :=
  certifyPrime (q := pv5) (ls := [pv2,pv4211]) (by decide +kernel)
def pv8423 : PrimeValue := ⟨8423, pr8423⟩
private theorem pr8429 : PrimeCertificate 8429 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv43]) (by decide +kernel)
def pv8429 : PrimeValue := ⟨8429, pr8429⟩
private theorem pr8431 : PrimeCertificate 8431 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv281]) (by decide +kernel)
def pv8431 : PrimeValue := ⟨8431, pr8431⟩
private theorem pr8443 : PrimeCertificate 8443 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv67]) (by decide +kernel)
def pv8443 : PrimeValue := ⟨8443, pr8443⟩
private theorem pr8447 : PrimeCertificate 8447 :=
  certifyPrime (q := pv5) (ls := [pv2,pv41,pv103]) (by decide +kernel)
def pv8447 : PrimeValue := ⟨8447, pr8447⟩
private theorem pr8461 : PrimeCertificate 8461 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv47]) (by decide +kernel)
def pv8461 : PrimeValue := ⟨8461, pr8461⟩
private theorem pr8467 : PrimeCertificate 8467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv17,pv83]) (by decide +kernel)
def pv8467 : PrimeValue := ⟨8467, pr8467⟩
private theorem pr8501 : PrimeCertificate 8501 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv17]) (by decide +kernel)
def pv8501 : PrimeValue := ⟨8501, pr8501⟩
private theorem pr8513 : PrimeCertificate 8513 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv19]) (by decide +kernel)
def pv8513 : PrimeValue := ⟨8513, pr8513⟩
private theorem pr8521 : PrimeCertificate 8521 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv71]) (by decide +kernel)
def pv8521 : PrimeValue := ⟨8521, pr8521⟩
private theorem pr8527 : PrimeCertificate 8527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv29]) (by decide +kernel)
def pv8527 : PrimeValue := ⟨8527, pr8527⟩
private theorem pr8537 : PrimeCertificate 8537 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv97]) (by decide +kernel)
def pv8537 : PrimeValue := ⟨8537, pr8537⟩
private theorem pr8539 : PrimeCertificate 8539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1423]) (by decide +kernel)
def pv8539 : PrimeValue := ⟨8539, pr8539⟩
private theorem pr8543 : PrimeCertificate 8543 :=
  certifyPrime (q := pv5) (ls := [pv2,pv4271]) (by decide +kernel)
def pv8543 : PrimeValue := ⟨8543, pr8543⟩
private theorem pr8563 : PrimeCertificate 8563 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1427]) (by decide +kernel)
def pv8563 : PrimeValue := ⟨8563, pr8563⟩
private theorem pr8573 : PrimeCertificate 8573 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2143]) (by decide +kernel)
def pv8573 : PrimeValue := ⟨8573, pr8573⟩
private theorem pr8581 : PrimeCertificate 8581 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv13]) (by decide +kernel)
def pv8581 : PrimeValue := ⟨8581, pr8581⟩
private theorem pr8597 : PrimeCertificate 8597 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv307]) (by decide +kernel)
def pv8597 : PrimeValue := ⟨8597, pr8597⟩
private theorem pr8599 : PrimeCertificate 8599 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1433]) (by decide +kernel)
def pv8599 : PrimeValue := ⟨8599, pr8599⟩
private theorem pr8609 : PrimeCertificate 8609 :=
  certifyPrime (q := pv3) (ls := [pv2,pv269]) (by decide +kernel)
def pv8609 : PrimeValue := ⟨8609, pr8609⟩
private theorem pr8623 : PrimeCertificate 8623 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv479]) (by decide +kernel)
def pv8623 : PrimeValue := ⟨8623, pr8623⟩
private theorem pr8627 : PrimeCertificate 8627 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv227]) (by decide +kernel)
def pv8627 : PrimeValue := ⟨8627, pr8627⟩
private theorem pr8629 : PrimeCertificate 8629 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv719]) (by decide +kernel)
def pv8629 : PrimeValue := ⟨8629, pr8629⟩
private theorem pr8641 : PrimeCertificate 8641 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv8641 : PrimeValue := ⟨8641, pr8641⟩
private theorem pr8647 : PrimeCertificate 8647 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv131]) (by decide +kernel)
def pv8647 : PrimeValue := ⟨8647, pr8647⟩
private theorem pr8663 : PrimeCertificate 8663 :=
  certifyPrime (q := pv5) (ls := [pv2,pv61,pv71]) (by decide +kernel)
def pv8663 : PrimeValue := ⟨8663, pr8663⟩
private theorem pr8669 : PrimeCertificate 8669 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv197]) (by decide +kernel)
def pv8669 : PrimeValue := ⟨8669, pr8669⟩
private theorem pr8677 : PrimeCertificate 8677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv241]) (by decide +kernel)
def pv8677 : PrimeValue := ⟨8677, pr8677⟩
private theorem pr8681 : PrimeCertificate 8681 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv7,pv31]) (by decide +kernel)
def pv8681 : PrimeValue := ⟨8681, pr8681⟩
private theorem pr8689 : PrimeCertificate 8689 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv181]) (by decide +kernel)
def pv8689 : PrimeValue := ⟨8689, pr8689⟩
private theorem pr8693 : PrimeCertificate 8693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv53]) (by decide +kernel)
def pv8693 : PrimeValue := ⟨8693, pr8693⟩
private theorem pr8699 : PrimeCertificate 8699 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4349]) (by decide +kernel)
def pv8699 : PrimeValue := ⟨8699, pr8699⟩
private theorem pr8707 : PrimeCertificate 8707 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv1451]) (by decide +kernel)
def pv8707 : PrimeValue := ⟨8707, pr8707⟩
private theorem pr8713 : PrimeCertificate 8713 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv11]) (by decide +kernel)
def pv8713 : PrimeValue := ⟨8713, pr8713⟩
private theorem pr8719 : PrimeCertificate 8719 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1453]) (by decide +kernel)
def pv8719 : PrimeValue := ⟨8719, pr8719⟩
private theorem pr8731 : PrimeCertificate 8731 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv97]) (by decide +kernel)
def pv8731 : PrimeValue := ⟨8731, pr8731⟩
private theorem pr8737 : PrimeCertificate 8737 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv8737 : PrimeValue := ⟨8737, pr8737⟩
private theorem pr8741 : PrimeCertificate 8741 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv19,pv23]) (by decide +kernel)
def pv8741 : PrimeValue := ⟨8741, pr8741⟩
private theorem pr8747 : PrimeCertificate 8747 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4373]) (by decide +kernel)
def pv8747 : PrimeValue := ⟨8747, pr8747⟩
private theorem pr8753 : PrimeCertificate 8753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv547]) (by decide +kernel)
def pv8753 : PrimeValue := ⟨8753, pr8753⟩
private theorem pr8761 : PrimeCertificate 8761 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv73]) (by decide +kernel)
def pv8761 : PrimeValue := ⟨8761, pr8761⟩
private theorem pr8779 : PrimeCertificate 8779 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv11,pv19]) (by decide +kernel)
def pv8779 : PrimeValue := ⟨8779, pr8779⟩
private theorem pr8783 : PrimeCertificate 8783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv4391]) (by decide +kernel)
def pv8783 : PrimeValue := ⟨8783, pr8783⟩
private theorem pr8803 : PrimeCertificate 8803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv163]) (by decide +kernel)
def pv8803 : PrimeValue := ⟨8803, pr8803⟩
private theorem pr8807 : PrimeCertificate 8807 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv17,pv37]) (by decide +kernel)
def pv8807 : PrimeValue := ⟨8807, pr8807⟩
private theorem pr8819 : PrimeCertificate 8819 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4409]) (by decide +kernel)
def pv8819 : PrimeValue := ⟨8819, pr8819⟩
private theorem pr8821 : PrimeCertificate 8821 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7]) (by decide +kernel)
def pv8821 : PrimeValue := ⟨8821, pr8821⟩
private theorem pr8831 : PrimeCertificate 8831 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv883]) (by decide +kernel)
def pv8831 : PrimeValue := ⟨8831, pr8831⟩
private theorem pr8837 : PrimeCertificate 8837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47]) (by decide +kernel)
def pv8837 : PrimeValue := ⟨8837, pr8837⟩
private theorem pr8839 : PrimeCertificate 8839 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv491]) (by decide +kernel)
def pv8839 : PrimeValue := ⟨8839, pr8839⟩
private theorem pr8849 : PrimeCertificate 8849 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv79]) (by decide +kernel)
def pv8849 : PrimeValue := ⟨8849, pr8849⟩
private theorem pr8861 : PrimeCertificate 8861 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv443]) (by decide +kernel)
def pv8861 : PrimeValue := ⟨8861, pr8861⟩
private theorem pr8863 : PrimeCertificate 8863 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv211]) (by decide +kernel)
def pv8863 : PrimeValue := ⟨8863, pr8863⟩
private theorem pr8867 : PrimeCertificate 8867 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv13,pv31]) (by decide +kernel)
def pv8867 : PrimeValue := ⟨8867, pr8867⟩
private theorem pr8887 : PrimeCertificate 8887 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1481]) (by decide +kernel)
def pv8887 : PrimeValue := ⟨8887, pr8887⟩
private theorem pr8893 : PrimeCertificate 8893 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv19]) (by decide +kernel)
def pv8893 : PrimeValue := ⟨8893, pr8893⟩
private theorem pr8923 : PrimeCertificate 8923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1487]) (by decide +kernel)
def pv8923 : PrimeValue := ⟨8923, pr8923⟩
private theorem pr8929 : PrimeCertificate 8929 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv31]) (by decide +kernel)
def pv8929 : PrimeValue := ⟨8929, pr8929⟩
private theorem pr8933 : PrimeCertificate 8933 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11,pv29]) (by decide +kernel)
def pv8933 : PrimeValue := ⟨8933, pr8933⟩
private theorem pr8941 : PrimeCertificate 8941 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv149]) (by decide +kernel)
def pv8941 : PrimeValue := ⟨8941, pr8941⟩
private theorem pr8951 : PrimeCertificate 8951 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv179]) (by decide +kernel)
def pv8951 : PrimeValue := ⟨8951, pr8951⟩
private theorem pr8963 : PrimeCertificate 8963 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4481]) (by decide +kernel)
def pv8963 : PrimeValue := ⟨8963, pr8963⟩
private theorem pr8969 : PrimeCertificate 8969 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19,pv59]) (by decide +kernel)
def pv8969 : PrimeValue := ⟨8969, pr8969⟩
private theorem pr8971 : PrimeCertificate 8971 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13,pv23]) (by decide +kernel)
def pv8971 : PrimeValue := ⟨8971, pr8971⟩
private theorem pr8999 : PrimeCertificate 8999 :=
  certifyPrime (q := pv7) (ls := [pv2,pv11,pv409]) (by decide +kernel)
def pv8999 : PrimeValue := ⟨8999, pr8999⟩
private theorem pr9001 : PrimeCertificate 9001 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv9001 : PrimeValue := ⟨9001, pr9001⟩
private theorem pr9007 : PrimeCertificate 9007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv79]) (by decide +kernel)
def pv9007 : PrimeValue := ⟨9007, pr9007⟩
private theorem pr9011 : PrimeCertificate 9011 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv17,pv53]) (by decide +kernel)
def pv9011 : PrimeValue := ⟨9011, pr9011⟩
private theorem pr9013 : PrimeCertificate 9013 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv751]) (by decide +kernel)
def pv9013 : PrimeValue := ⟨9013, pr9013⟩
private theorem pr9029 : PrimeCertificate 9029 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv61]) (by decide +kernel)
def pv9029 : PrimeValue := ⟨9029, pr9029⟩
private theorem pr9041 : PrimeCertificate 9041 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv113]) (by decide +kernel)
def pv9041 : PrimeValue := ⟨9041, pr9041⟩
private theorem pr9043 : PrimeCertificate 9043 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv137]) (by decide +kernel)
def pv9043 : PrimeValue := ⟨9043, pr9043⟩
private theorem pr9049 : PrimeCertificate 9049 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv13,pv29]) (by decide +kernel)
def pv9049 : PrimeValue := ⟨9049, pr9049⟩
private theorem pr9059 : PrimeCertificate 9059 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv647]) (by decide +kernel)
def pv9059 : PrimeValue := ⟨9059, pr9059⟩
private theorem pr9067 : PrimeCertificate 9067 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1511]) (by decide +kernel)
def pv9067 : PrimeValue := ⟨9067, pr9067⟩
private theorem pr9091 : PrimeCertificate 9091 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv101]) (by decide +kernel)
def pv9091 : PrimeValue := ⟨9091, pr9091⟩
private theorem pr9103 : PrimeCertificate 9103 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv37,pv41]) (by decide +kernel)
def pv9103 : PrimeValue := ⟨9103, pr9103⟩
private theorem pr9109 : PrimeCertificate 9109 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv11,pv23]) (by decide +kernel)
def pv9109 : PrimeValue := ⟨9109, pr9109⟩
private theorem pr9127 : PrimeCertificate 9127 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv13]) (by decide +kernel)
def pv9127 : PrimeValue := ⟨9127, pr9127⟩
private theorem pr9133 : PrimeCertificate 9133 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv761]) (by decide +kernel)
def pv9133 : PrimeValue := ⟨9133, pr9133⟩
private theorem pr9137 : PrimeCertificate 9137 :=
  certifyPrime (q := pv3) (ls := [pv2,pv571]) (by decide +kernel)
def pv9137 : PrimeValue := ⟨9137, pr9137⟩
private theorem pr9151 : PrimeCertificate 9151 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv61]) (by decide +kernel)
def pv9151 : PrimeValue := ⟨9151, pr9151⟩
private theorem pr9157 : PrimeCertificate 9157 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv7,pv109]) (by decide +kernel)
def pv9157 : PrimeValue := ⟨9157, pr9157⟩
private theorem pr9161 : PrimeCertificate 9161 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv229]) (by decide +kernel)
def pv9161 : PrimeValue := ⟨9161, pr9161⟩
private theorem pr9173 : PrimeCertificate 9173 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2293]) (by decide +kernel)
def pv9173 : PrimeValue := ⟨9173, pr9173⟩
private theorem pr9181 : PrimeCertificate 9181 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv17]) (by decide +kernel)
def pv9181 : PrimeValue := ⟨9181, pr9181⟩
private theorem pr9187 : PrimeCertificate 9187 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1531]) (by decide +kernel)
def pv9187 : PrimeValue := ⟨9187, pr9187⟩
private theorem pr9199 : PrimeCertificate 9199 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv73]) (by decide +kernel)
def pv9199 : PrimeValue := ⟨9199, pr9199⟩
private theorem pr9203 : PrimeCertificate 9203 :=
  certifyPrime (q := pv2) (ls := [pv2,pv43,pv107]) (by decide +kernel)
def pv9203 : PrimeValue := ⟨9203, pr9203⟩
private theorem pr9209 : PrimeCertificate 9209 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1151]) (by decide +kernel)
def pv9209 : PrimeValue := ⟨9209, pr9209⟩
private theorem pr9221 : PrimeCertificate 9221 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv461]) (by decide +kernel)
def pv9221 : PrimeValue := ⟨9221, pr9221⟩
private theorem pr9227 : PrimeCertificate 9227 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv659]) (by decide +kernel)
def pv9227 : PrimeValue := ⟨9227, pr9227⟩
private theorem pr9239 : PrimeCertificate 9239 :=
  certifyPrime (q := pv19) (ls := [pv2,pv31,pv149]) (by decide +kernel)
def pv9239 : PrimeValue := ⟨9239, pr9239⟩
private theorem pr9241 : PrimeCertificate 9241 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv7,pv11]) (by decide +kernel)
def pv9241 : PrimeValue := ⟨9241, pr9241⟩
private theorem pr9257 : PrimeCertificate 9257 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv89]) (by decide +kernel)
def pv9257 : PrimeValue := ⟨9257, pr9257⟩
private theorem pr9277 : PrimeCertificate 9277 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv773]) (by decide +kernel)
def pv9277 : PrimeValue := ⟨9277, pr9277⟩
private theorem pr9281 : PrimeCertificate 9281 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv29]) (by decide +kernel)
def pv9281 : PrimeValue := ⟨9281, pr9281⟩
private theorem pr9283 : PrimeCertificate 9283 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv17]) (by decide +kernel)
def pv9283 : PrimeValue := ⟨9283, pr9283⟩
private theorem pr9293 : PrimeCertificate 9293 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv101]) (by decide +kernel)
def pv9293 : PrimeValue := ⟨9293, pr9293⟩
private theorem pr9311 : PrimeCertificate 9311 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv19]) (by decide +kernel)
def pv9311 : PrimeValue := ⟨9311, pr9311⟩
private theorem pr9319 : PrimeCertificate 9319 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1553]) (by decide +kernel)
def pv9319 : PrimeValue := ⟨9319, pr9319⟩
private theorem pr9323 : PrimeCertificate 9323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv59,pv79]) (by decide +kernel)
def pv9323 : PrimeValue := ⟨9323, pr9323⟩
private theorem pr9337 : PrimeCertificate 9337 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv389]) (by decide +kernel)
def pv9337 : PrimeValue := ⟨9337, pr9337⟩
private theorem pr9341 : PrimeCertificate 9341 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv467]) (by decide +kernel)
def pv9341 : PrimeValue := ⟨9341, pr9341⟩
private theorem pr9343 : PrimeCertificate 9343 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv173]) (by decide +kernel)
def pv9343 : PrimeValue := ⟨9343, pr9343⟩
private theorem pr9349 : PrimeCertificate 9349 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv19,pv41]) (by decide +kernel)
def pv9349 : PrimeValue := ⟨9349, pr9349⟩
private theorem pr9371 : PrimeCertificate 9371 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv937]) (by decide +kernel)
def pv9371 : PrimeValue := ⟨9371, pr9371⟩
private theorem pr9377 : PrimeCertificate 9377 :=
  certifyPrime (q := pv3) (ls := [pv2,pv293]) (by decide +kernel)
def pv9377 : PrimeValue := ⟨9377, pr9377⟩
private theorem pr9391 : PrimeCertificate 9391 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv313]) (by decide +kernel)
def pv9391 : PrimeValue := ⟨9391, pr9391⟩
private theorem pr9397 : PrimeCertificate 9397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv9397 : PrimeValue := ⟨9397, pr9397⟩
private theorem pr9403 : PrimeCertificate 9403 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1567]) (by decide +kernel)
def pv9403 : PrimeValue := ⟨9403, pr9403⟩
private theorem pr9413 : PrimeCertificate 9413 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv181]) (by decide +kernel)
def pv9413 : PrimeValue := ⟨9413, pr9413⟩
private theorem pr9419 : PrimeCertificate 9419 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv277]) (by decide +kernel)
def pv9419 : PrimeValue := ⟨9419, pr9419⟩
private theorem pr9421 : PrimeCertificate 9421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv157]) (by decide +kernel)
def pv9421 : PrimeValue := ⟨9421, pr9421⟩
private theorem pr9431 : PrimeCertificate 9431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv23,pv41]) (by decide +kernel)
def pv9431 : PrimeValue := ⟨9431, pr9431⟩
private theorem pr9433 : PrimeCertificate 9433 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv131]) (by decide +kernel)
def pv9433 : PrimeValue := ⟨9433, pr9433⟩
private theorem pr9437 : PrimeCertificate 9437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv337]) (by decide +kernel)
def pv9437 : PrimeValue := ⟨9437, pr9437⟩
private theorem pr9439 : PrimeCertificate 9439 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv9439 : PrimeValue := ⟨9439, pr9439⟩
private theorem pr9461 : PrimeCertificate 9461 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv11,pv43]) (by decide +kernel)
def pv9461 : PrimeValue := ⟨9461, pr9461⟩
private theorem pr9463 : PrimeCertificate 9463 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv19,pv83]) (by decide +kernel)
def pv9463 : PrimeValue := ⟨9463, pr9463⟩
private theorem pr9467 : PrimeCertificate 9467 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4733]) (by decide +kernel)
def pv9467 : PrimeValue := ⟨9467, pr9467⟩
private theorem pr9473 : PrimeCertificate 9473 :=
  certifyPrime (q := pv3) (ls := [pv2,pv37]) (by decide +kernel)
def pv9473 : PrimeValue := ⟨9473, pr9473⟩
private theorem pr9479 : PrimeCertificate 9479 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv677]) (by decide +kernel)
def pv9479 : PrimeValue := ⟨9479, pr9479⟩
private theorem pr9491 : PrimeCertificate 9491 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv13,pv73]) (by decide +kernel)
def pv9491 : PrimeValue := ⟨9491, pr9491⟩
private theorem pr9497 : PrimeCertificate 9497 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1187]) (by decide +kernel)
def pv9497 : PrimeValue := ⟨9497, pr9497⟩
private theorem pr9511 : PrimeCertificate 9511 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv317]) (by decide +kernel)
def pv9511 : PrimeValue := ⟨9511, pr9511⟩
private theorem pr9521 : PrimeCertificate 9521 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv7,pv17]) (by decide +kernel)
def pv9521 : PrimeValue := ⟨9521, pr9521⟩
private theorem pr9533 : PrimeCertificate 9533 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2383]) (by decide +kernel)
def pv9533 : PrimeValue := ⟨9533, pr9533⟩
private theorem pr9539 : PrimeCertificate 9539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv19,pv251]) (by decide +kernel)
def pv9539 : PrimeValue := ⟨9539, pr9539⟩
private theorem pr9547 : PrimeCertificate 9547 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv37,pv43]) (by decide +kernel)
def pv9547 : PrimeValue := ⟨9547, pr9547⟩
private theorem pr9551 : PrimeCertificate 9551 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv191]) (by decide +kernel)
def pv9551 : PrimeValue := ⟨9551, pr9551⟩
private theorem pr9587 : PrimeCertificate 9587 :=
  certifyPrime (q := pv2) (ls := [pv2,pv4793]) (by decide +kernel)
def pv9587 : PrimeValue := ⟨9587, pr9587⟩
private theorem pr9601 : PrimeCertificate 9601 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv9601 : PrimeValue := ⟨9601, pr9601⟩
private theorem pr9613 : PrimeCertificate 9613 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv89]) (by decide +kernel)
def pv9613 : PrimeValue := ⟨9613, pr9613⟩
private theorem pr9619 : PrimeCertificate 9619 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv229]) (by decide +kernel)
def pv9619 : PrimeValue := ⟨9619, pr9619⟩
private theorem pr9623 : PrimeCertificate 9623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv17,pv283]) (by decide +kernel)
def pv9623 : PrimeValue := ⟨9623, pr9623⟩
private theorem pr9629 : PrimeCertificate 9629 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv83]) (by decide +kernel)
def pv9629 : PrimeValue := ⟨9629, pr9629⟩
private theorem pr9631 : PrimeCertificate 9631 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv107]) (by decide +kernel)
def pv9631 : PrimeValue := ⟨9631, pr9631⟩
private theorem pr9643 : PrimeCertificate 9643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv1607]) (by decide +kernel)
def pv9643 : PrimeValue := ⟨9643, pr9643⟩
private theorem pr9649 : PrimeCertificate 9649 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv67]) (by decide +kernel)
def pv9649 : PrimeValue := ⟨9649, pr9649⟩
private theorem pr9661 : PrimeCertificate 9661 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv7,pv23]) (by decide +kernel)
def pv9661 : PrimeValue := ⟨9661, pr9661⟩
private theorem pr9677 : PrimeCertificate 9677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv59]) (by decide +kernel)
def pv9677 : PrimeValue := ⟨9677, pr9677⟩
private theorem pr9679 : PrimeCertificate 9679 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1613]) (by decide +kernel)
def pv9679 : PrimeValue := ⟨9679, pr9679⟩
private theorem pr9689 : PrimeCertificate 9689 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv173]) (by decide +kernel)
def pv9689 : PrimeValue := ⟨9689, pr9689⟩
private theorem pr9697 : PrimeCertificate 9697 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv101]) (by decide +kernel)
def pv9697 : PrimeValue := ⟨9697, pr9697⟩
private theorem pr9719 : PrimeCertificate 9719 :=
  certifyPrime (q := pv17) (ls := [pv2,pv43,pv113]) (by decide +kernel)
def pv9719 : PrimeValue := ⟨9719, pr9719⟩
private theorem pr9721 : PrimeCertificate 9721 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5]) (by decide +kernel)
def pv9721 : PrimeValue := ⟨9721, pr9721⟩
private theorem pr9733 : PrimeCertificate 9733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv811]) (by decide +kernel)
def pv9733 : PrimeValue := ⟨9733, pr9733⟩
private theorem pr9739 : PrimeCertificate 9739 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv541]) (by decide +kernel)
def pv9739 : PrimeValue := ⟨9739, pr9739⟩
private theorem pr9743 : PrimeCertificate 9743 :=
  certifyPrime (q := pv5) (ls := [pv2,pv4871]) (by decide +kernel)
def pv9743 : PrimeValue := ⟨9743, pr9743⟩
private theorem pr9749 : PrimeCertificate 9749 :=
  certifyPrime (q := pv2) (ls := [pv2,pv2437]) (by decide +kernel)
def pv9749 : PrimeValue := ⟨9749, pr9749⟩
private theorem pr9767 : PrimeCertificate 9767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv19,pv257]) (by decide +kernel)
def pv9767 : PrimeValue := ⟨9767, pr9767⟩
private theorem pr9769 : PrimeCertificate 9769 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv11,pv37]) (by decide +kernel)
def pv9769 : PrimeValue := ⟨9769, pr9769⟩
private theorem pr9781 : PrimeCertificate 9781 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv163]) (by decide +kernel)
def pv9781 : PrimeValue := ⟨9781, pr9781⟩
private theorem pr9787 : PrimeCertificate 9787 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv233]) (by decide +kernel)
def pv9787 : PrimeValue := ⟨9787, pr9787⟩
private theorem pr9791 : PrimeCertificate 9791 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv11,pv89]) (by decide +kernel)
def pv9791 : PrimeValue := ⟨9791, pr9791⟩
private theorem pr9803 : PrimeCertificate 9803 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv29]) (by decide +kernel)
def pv9803 : PrimeValue := ⟨9803, pr9803⟩
private theorem pr9811 : PrimeCertificate 9811 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv109]) (by decide +kernel)
def pv9811 : PrimeValue := ⟨9811, pr9811⟩
private theorem pr9817 : PrimeCertificate 9817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv409]) (by decide +kernel)
def pv9817 : PrimeValue := ⟨9817, pr9817⟩
private theorem pr9829 : PrimeCertificate 9829 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv7,pv13]) (by decide +kernel)
def pv9829 : PrimeValue := ⟨9829, pr9829⟩
private theorem pr9833 : PrimeCertificate 9833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv1229]) (by decide +kernel)
def pv9833 : PrimeValue := ⟨9833, pr9833⟩
private theorem pr9839 : PrimeCertificate 9839 :=
  certifyPrime (q := pv7) (ls := [pv2,pv4919]) (by decide +kernel)
def pv9839 : PrimeValue := ⟨9839, pr9839⟩
private theorem pr9851 : PrimeCertificate 9851 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv197]) (by decide +kernel)
def pv9851 : PrimeValue := ⟨9851, pr9851⟩
private theorem pr9857 : PrimeCertificate 9857 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11]) (by decide +kernel)
def pv9857 : PrimeValue := ⟨9857, pr9857⟩
private theorem pr9859 : PrimeCertificate 9859 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv31,pv53]) (by decide +kernel)
def pv9859 : PrimeValue := ⟨9859, pr9859⟩
private theorem pr9871 : PrimeCertificate 9871 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv47]) (by decide +kernel)
def pv9871 : PrimeValue := ⟨9871, pr9871⟩
private theorem pr9883 : PrimeCertificate 9883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv61]) (by decide +kernel)
def pv9883 : PrimeValue := ⟨9883, pr9883⟩
private theorem pr9887 : PrimeCertificate 9887 :=
  certifyPrime (q := pv5) (ls := [pv2,pv4943]) (by decide +kernel)
def pv9887 : PrimeValue := ⟨9887, pr9887⟩
private theorem pr9901 : PrimeCertificate 9901 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv11]) (by decide +kernel)
def pv9901 : PrimeValue := ⟨9901, pr9901⟩
private theorem pr9907 : PrimeCertificate 9907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv13,pv127]) (by decide +kernel)
def pv9907 : PrimeValue := ⟨9907, pr9907⟩
private theorem pr9923 : PrimeCertificate 9923 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv41]) (by decide +kernel)
def pv9923 : PrimeValue := ⟨9923, pr9923⟩
private theorem pr9929 : PrimeCertificate 9929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv17,pv73]) (by decide +kernel)
def pv9929 : PrimeValue := ⟨9929, pr9929⟩
private theorem pr9931 : PrimeCertificate 9931 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv331]) (by decide +kernel)
def pv9931 : PrimeValue := ⟨9931, pr9931⟩
private theorem pr9941 : PrimeCertificate 9941 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv71]) (by decide +kernel)
def pv9941 : PrimeValue := ⟨9941, pr9941⟩
private theorem pr9949 : PrimeCertificate 9949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv829]) (by decide +kernel)
def pv9949 : PrimeValue := ⟨9949, pr9949⟩
private theorem pr9967 : PrimeCertificate 9967 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv11,pv151]) (by decide +kernel)
def pv9967 : PrimeValue := ⟨9967, pr9967⟩
private theorem pr9973 : PrimeCertificate 9973 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv277]) (by decide +kernel)
def pv9973 : PrimeValue := ⟨9973, pr9973⟩
private theorem pr10007 : PrimeCertificate 10007 :=
  certifyPrime (q := pv5) (ls := [pv2,pv5003]) (by decide +kernel)
def pv10007 : PrimeValue := ⟨10007, pr10007⟩
private theorem pr10009 : PrimeCertificate 10009 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv139]) (by decide +kernel)
def pv10009 : PrimeValue := ⟨10009, pr10009⟩
private theorem pr10037 : PrimeCertificate 10037 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv193]) (by decide +kernel)
def pv10037 : PrimeValue := ⟨10037, pr10037⟩
private theorem pr10039 : PrimeCertificate 10039 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv239]) (by decide +kernel)
def pv10039 : PrimeValue := ⟨10039, pr10039⟩
private theorem pr10061 : PrimeCertificate 10061 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv503]) (by decide +kernel)
def pv10061 : PrimeValue := ⟨10061, pr10061⟩
private theorem pr10067 : PrimeCertificate 10067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv719]) (by decide +kernel)
def pv10067 : PrimeValue := ⟨10067, pr10067⟩
private theorem pr10069 : PrimeCertificate 10069 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv839]) (by decide +kernel)
def pv10069 : PrimeValue := ⟨10069, pr10069⟩
private theorem pr10079 : PrimeCertificate 10079 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5039]) (by decide +kernel)
def pv10079 : PrimeValue := ⟨10079, pr10079⟩
private theorem pr10091 : PrimeCertificate 10091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv1009]) (by decide +kernel)
def pv10091 : PrimeValue := ⟨10091, pr10091⟩
private theorem pr10093 : PrimeCertificate 10093 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv29]) (by decide +kernel)
def pv10093 : PrimeValue := ⟨10093, pr10093⟩
private theorem pr10099 : PrimeCertificate 10099 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv17]) (by decide +kernel)
def pv10099 : PrimeValue := ⟨10099, pr10099⟩
private theorem pr10103 : PrimeCertificate 10103 :=
  certifyPrime (q := pv5) (ls := [pv2,pv5051]) (by decide +kernel)
def pv10103 : PrimeValue := ⟨10103, pr10103⟩
private theorem pr10111 : PrimeCertificate 10111 :=
  certifyPrime (q := pv31) (ls := [pv2,pv3,pv5,pv337]) (by decide +kernel)
def pv10111 : PrimeValue := ⟨10111, pr10111⟩
private theorem pr10133 : PrimeCertificate 10133 :=
  certifyPrime (q := pv2) (ls := [pv2,pv17,pv149]) (by decide +kernel)
def pv10133 : PrimeValue := ⟨10133, pr10133⟩
private theorem pr10139 : PrimeCertificate 10139 :=
  certifyPrime (q := pv2) (ls := [pv2,pv37,pv137]) (by decide +kernel)
def pv10139 : PrimeValue := ⟨10139, pr10139⟩
private theorem pr10141 : PrimeCertificate 10141 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv13]) (by decide +kernel)
def pv10141 : PrimeValue := ⟨10141, pr10141⟩
private theorem pr10151 : PrimeCertificate 10151 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv29]) (by decide +kernel)
def pv10151 : PrimeValue := ⟨10151, pr10151⟩
private theorem pr10159 : PrimeCertificate 10159 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv1693]) (by decide +kernel)
def pv10159 : PrimeValue := ⟨10159, pr10159⟩
private theorem pr10163 : PrimeCertificate 10163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5081]) (by decide +kernel)
def pv10163 : PrimeValue := ⟨10163, pr10163⟩
private theorem pr10169 : PrimeCertificate 10169 :=
  certifyPrime (q := pv3) (ls := [pv2,pv31,pv41]) (by decide +kernel)
def pv10169 : PrimeValue := ⟨10169, pr10169⟩
private theorem pr10177 : PrimeCertificate 10177 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv53]) (by decide +kernel)
def pv10177 : PrimeValue := ⟨10177, pr10177⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
