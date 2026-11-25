/- GID: D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table160
   generality: I
   mirror-B: none(waiver:finite-reduction-premise-in-main-proof-closure)
   mirror-E: none(waiver:kernel-checked-literal-certificate)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/PrimitiveRoot/Erdos985.erdos985_of_finiteHeight; instance=D5/S3/Arith/PrimitiveRoot/SmallPrimes/Tables02/Table160.pv148997
   digest: Shared Lucas certificates for the extended factor alphabet. -/

import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table007
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table011
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table029
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Tables00.Table030

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false

namespace D5.S3.Arith.PrimitiveRoot.SmallPrimes

private theorem pr148997 : PrimeCertificate 148997 :=
  certifyPrime (q := pv3) (ls := [pv2,pv193]) (by decide +kernel)
def pv148997 : PrimeValue := ⟨148997, pr148997⟩
private theorem pr149077 : PrimeCertificate 149077 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv41,pv101]) (by decide +kernel)
def pv149077 : PrimeValue := ⟨149077, pr149077⟩
private theorem pr149269 : PrimeCertificate 149269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv1777]) (by decide +kernel)
def pv149269 : PrimeValue := ⟨149269, pr149269⟩
private theorem pr149323 : PrimeCertificate 149323 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv41,pv607]) (by decide +kernel)
def pv149323 : PrimeValue := ⟨149323, pr149323⟩
private theorem pr149603 : PrimeCertificate 149603 :=
  certifyPrime (q := pv2) (ls := [pv2,pv131,pv571]) (by decide +kernel)
def pv149603 : PrimeValue := ⟨149603, pr149603⟩
private theorem pr149771 : PrimeCertificate 149771 :=
  certifyPrime (q := pv23) (ls := [pv2,pv5,pv17,pv881]) (by decide +kernel)
def pv149771 : PrimeValue := ⟨149771, pr149771⟩
private theorem pr149837 : PrimeCertificate 149837 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv797]) (by decide +kernel)
def pv149837 : PrimeValue := ⟨149837, pr149837⟩
private theorem pr149909 : PrimeCertificate 149909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv3407]) (by decide +kernel)
def pv149909 : PrimeValue := ⟨149909, pr149909⟩
private theorem pr149993 : PrimeCertificate 149993 :=
  certifyPrime (q := pv3) (ls := [pv2,pv18749]) (by decide +kernel)
def pv149993 : PrimeValue := ⟨149993, pr149993⟩
private theorem pr150083 : PrimeCertificate 150083 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75041]) (by decide +kernel)
def pv150083 : PrimeValue := ⟨150083, pr150083⟩
private theorem pr150193 : PrimeCertificate 150193 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv7,pv149]) (by decide +kernel)
def pv150193 : PrimeValue := ⟨150193, pr150193⟩
private theorem pr150413 : PrimeCertificate 150413 :=
  certifyPrime (q := pv2) (ls := [pv2,pv31,pv1213]) (by decide +kernel)
def pv150413 : PrimeValue := ⟨150413, pr150413⟩
private theorem pr150431 : PrimeCertificate 150431 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv307]) (by decide +kernel)
def pv150431 : PrimeValue := ⟨150431, pr150431⟩
private theorem pr150589 : PrimeCertificate 150589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv47,pv89]) (by decide +kernel)
def pv150589 : PrimeValue := ⟨150589, pr150589⟩
private theorem pr150707 : PrimeCertificate 150707 :=
  certifyPrime (q := pv2) (ls := [pv2,pv75353]) (by decide +kernel)
def pv150707 : PrimeValue := ⟨150707, pr150707⟩
private theorem pr150767 : PrimeCertificate 150767 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11,pv89]) (by decide +kernel)
def pv150767 : PrimeValue := ⟨150767, pr150767⟩
private theorem pr150929 : PrimeCertificate 150929 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9433]) (by decide +kernel)
def pv150929 : PrimeValue := ⟨150929, pr150929⟩
private theorem pr150959 : PrimeCertificate 150959 :=
  certifyPrime (q := pv7) (ls := [pv2,pv75479]) (by decide +kernel)
def pv150959 : PrimeValue := ⟨150959, pr150959⟩
private theorem pr151009 : PrimeCertificate 151009 :=
  certifyPrime (q := pv47) (ls := [pv2,pv3,pv11,pv13]) (by decide +kernel)
def pv151009 : PrimeValue := ⟨151009, pr151009⟩
private theorem pr151091 : PrimeCertificate 151091 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv29,pv521]) (by decide +kernel)
def pv151091 : PrimeValue := ⟨151091, pr151091⟩
private theorem pr151163 : PrimeCertificate 151163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv11,pv6871]) (by decide +kernel)
def pv151163 : PrimeValue := ⟨151163, pr151163⟩
private theorem pr151391 : PrimeCertificate 151391 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv15139]) (by decide +kernel)
def pv151391 : PrimeValue := ⟨151391, pr151391⟩
private theorem pr151549 : PrimeCertificate 151549 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv73,pv173]) (by decide +kernel)
def pv151549 : PrimeValue := ⟨151549, pr151549⟩
private theorem pr151561 : PrimeCertificate 151561 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv5,pv421]) (by decide +kernel)
def pv151561 : PrimeValue := ⟨151561, pr151561⟩
private theorem pr151681 : PrimeCertificate 151681 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv5,pv79]) (by decide +kernel)
def pv151681 : PrimeValue := ⟨151681, pr151681⟩
private theorem pr151693 : PrimeCertificate 151693 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12641]) (by decide +kernel)
def pv151693 : PrimeValue := ⟨151693, pr151693⟩
private theorem pr151733 : PrimeCertificate 151733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv5419]) (by decide +kernel)
def pv151733 : PrimeValue := ⟨151733, pr151733⟩
private theorem pr151787 : PrimeCertificate 151787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv29,pv2617]) (by decide +kernel)
def pv151787 : PrimeValue := ⟨151787, pr151787⟩
private theorem pr151817 : PrimeCertificate 151817 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv2711]) (by decide +kernel)
def pv151817 : PrimeValue := ⟨151817, pr151817⟩
private theorem pr151909 : PrimeCertificate 151909 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12659]) (by decide +kernel)
def pv151909 : PrimeValue := ⟨151909, pr151909⟩
private theorem pr152027 : PrimeCertificate 152027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10859]) (by decide +kernel)
def pv152027 : PrimeValue := ⟨152027, pr152027⟩
private theorem pr152203 : PrimeCertificate 152203 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv25367]) (by decide +kernel)
def pv152203 : PrimeValue := ⟨152203, pr152203⟩
private theorem pr152231 : PrimeCertificate 152231 :=
  certifyPrime (q := pv29) (ls := [pv2,pv5,pv13,pv1171]) (by decide +kernel)
def pv152231 : PrimeValue := ⟨152231, pr152231⟩
private theorem pr152363 : PrimeCertificate 152363 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv10883]) (by decide +kernel)
def pv152363 : PrimeValue := ⟨152363, pr152363⟩
private theorem pr152671 : PrimeCertificate 152671 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv7,pv727]) (by decide +kernel)
def pv152671 : PrimeValue := ⟨152671, pr152671⟩
private theorem pr152717 : PrimeCertificate 152717 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv523]) (by decide +kernel)
def pv152717 : PrimeValue := ⟨152717, pr152717⟩
private theorem pr152753 : PrimeCertificate 152753 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9547]) (by decide +kernel)
def pv152753 : PrimeValue := ⟨152753, pr152753⟩
private theorem pr152783 : PrimeCertificate 152783 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv1559]) (by decide +kernel)
def pv152783 : PrimeValue := ⟨152783, pr152783⟩
private theorem pr152939 : PrimeCertificate 152939 :=
  certifyPrime (q := pv2) (ls := [pv2,pv47,pv1627]) (by decide +kernel)
def pv152939 : PrimeValue := ⟨152939, pr152939⟩
private theorem pr152941 : PrimeCertificate 152941 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv2549]) (by decide +kernel)
def pv152941 : PrimeValue := ⟨152941, pr152941⟩
private theorem pr153067 : PrimeCertificate 153067 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv97,pv263]) (by decide +kernel)
def pv153067 : PrimeValue := ⟨153067, pr153067⟩
private theorem pr153259 : PrimeCertificate 153259 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv7,pv41,pv89]) (by decide +kernel)
def pv153259 : PrimeValue := ⟨153259, pr153259⟩
private theorem pr153337 : PrimeCertificate 153337 :=
  certifyPrime (q := pv11) (ls := [pv2,pv3,pv6389]) (by decide +kernel)
def pv153337 : PrimeValue := ⟨153337, pr153337⟩
private theorem pr153421 : PrimeCertificate 153421 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv5,pv2557]) (by decide +kernel)
def pv153421 : PrimeValue := ⟨153421, pr153421⟩
private theorem pr153487 : PrimeCertificate 153487 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv8527]) (by decide +kernel)
def pv153487 : PrimeValue := ⟨153487, pr153487⟩
private theorem pr153521 : PrimeCertificate 153521 :=
  certifyPrime (q := pv17) (ls := [pv2,pv5,pv19,pv101]) (by decide +kernel)
def pv153521 : PrimeValue := ⟨153521, pr153521⟩
private theorem pr153589 : PrimeCertificate 153589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12799]) (by decide +kernel)
def pv153589 : PrimeValue := ⟨153589, pr153589⟩
private theorem pr153623 : PrimeCertificate 153623 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv10973]) (by decide +kernel)
def pv153623 : PrimeValue := ⟨153623, pr153623⟩
private theorem pr153733 : PrimeCertificate 153733 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv23,pv557]) (by decide +kernel)
def pv153733 : PrimeValue := ⟨153733, pr153733⟩
private theorem pr153949 : PrimeCertificate 153949 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12829]) (by decide +kernel)
def pv153949 : PrimeValue := ⟨153949, pr153949⟩
private theorem pr154043 : PrimeCertificate 154043 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11003]) (by decide +kernel)
def pv154043 : PrimeValue := ⟨154043, pr154043⟩
private theorem pr154183 : PrimeCertificate 154183 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv3671]) (by decide +kernel)
def pv154183 : PrimeValue := ⟨154183, pr154183⟩
private theorem pr154321 : PrimeCertificate 154321 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv643]) (by decide +kernel)
def pv154321 : PrimeValue := ⟨154321, pr154321⟩
private theorem pr154493 : PrimeCertificate 154493 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv2971]) (by decide +kernel)
def pv154493 : PrimeValue := ⟨154493, pr154493⟩
private theorem pr154643 : PrimeCertificate 154643 :=
  certifyPrime (q := pv2) (ls := [pv2,pv167,pv463]) (by decide +kernel)
def pv154643 : PrimeValue := ⟨154643, pr154643⟩
private theorem pr154871 : PrimeCertificate 154871 :=
  certifyPrime (q := pv13) (ls := [pv2,pv5,pv17,pv911]) (by decide +kernel)
def pv154871 : PrimeValue := ⟨154871, pr154871⟩
private theorem pr155017 : PrimeCertificate 155017 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv2153]) (by decide +kernel)
def pv155017 : PrimeValue := ⟨155017, pr155017⟩
private theorem pr155153 : PrimeCertificate 155153 :=
  certifyPrime (q := pv3) (ls := [pv2,pv9697]) (by decide +kernel)
def pv155153 : PrimeValue := ⟨155153, pr155153⟩
private theorem pr155209 : PrimeCertificate 155209 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv29,pv223]) (by decide +kernel)
def pv155209 : PrimeValue := ⟨155209, pr155209⟩
private theorem pr155383 : PrimeCertificate 155383 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv19,pv29,pv47]) (by decide +kernel)
def pv155383 : PrimeValue := ⟨155383, pr155383⟩
private theorem pr155579 : PrimeCertificate 155579 :=
  certifyPrime (q := pv2) (ls := [pv2,pv107,pv727]) (by decide +kernel)
def pv155579 : PrimeValue := ⟨155579, pr155579⟩
private theorem pr155609 : PrimeCertificate 155609 :=
  certifyPrime (q := pv7) (ls := [pv2,pv53,pv367]) (by decide +kernel)
def pv155609 : PrimeValue := ⟨155609, pr155609⟩
private theorem pr155719 : PrimeCertificate 155719 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv41,pv211]) (by decide +kernel)
def pv155719 : PrimeValue := ⟨155719, pr155719⟩
private theorem pr155797 : PrimeCertificate 155797 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv12983]) (by decide +kernel)
def pv155797 : PrimeValue := ⟨155797, pr155797⟩
private theorem pr155891 : PrimeCertificate 155891 :=
  certifyPrime (q := pv7) (ls := [pv2,pv5,pv7,pv17,pv131]) (by decide +kernel)
def pv155891 : PrimeValue := ⟨155891, pr155891⟩
private theorem pr155921 : PrimeCertificate 155921 :=
  certifyPrime (q := pv3) (ls := [pv2,pv5,pv1949]) (by decide +kernel)
def pv155921 : PrimeValue := ⟨155921, pr155921⟩
private theorem pr156007 : PrimeCertificate 156007 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv107]) (by decide +kernel)
def pv156007 : PrimeValue := ⟨156007, pr156007⟩
private theorem pr156071 : PrimeCertificate 156071 :=
  certifyPrime (q := pv11) (ls := [pv2,pv5,pv15607]) (by decide +kernel)
def pv156071 : PrimeValue := ⟨156071, pr156071⟩
private theorem pr156217 : PrimeCertificate 156217 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv23,pv283]) (by decide +kernel)
def pv156217 : PrimeValue := ⟨156217, pr156217⟩
private theorem pr156307 : PrimeCertificate 156307 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv109,pv239]) (by decide +kernel)
def pv156307 : PrimeValue := ⟨156307, pr156307⟩
private theorem pr156353 : PrimeCertificate 156353 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv349]) (by decide +kernel)
def pv156353 : PrimeValue := ⟨156353, pr156353⟩
private theorem pr156421 : PrimeCertificate 156421 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv11,pv79]) (by decide +kernel)
def pv156421 : PrimeValue := ⟨156421, pr156421⟩
private theorem pr156437 : PrimeCertificate 156437 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv37,pv151]) (by decide +kernel)
def pv156437 : PrimeValue := ⟨156437, pr156437⟩
private theorem pr156521 : PrimeCertificate 156521 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv7,pv13,pv43]) (by decide +kernel)
def pv156521 : PrimeValue := ⟨156521, pr156521⟩
private theorem pr156539 : PrimeCertificate 156539 :=
  certifyPrime (q := pv2) (ls := [pv2,pv23,pv41,pv83]) (by decide +kernel)
def pv156539 : PrimeValue := ⟨156539, pr156539⟩
private theorem pr156577 : PrimeCertificate 156577 :=
  certifyPrime (q := pv13) (ls := [pv2,pv3,pv7,pv233]) (by decide +kernel)
def pv156577 : PrimeValue := ⟨156577, pr156577⟩
private theorem pr156631 : PrimeCertificate 156631 :=
  certifyPrime (q := pv17) (ls := [pv2,pv3,pv5,pv23,pv227]) (by decide +kernel)
def pv156631 : PrimeValue := ⟨156631, pr156631⟩
private theorem pr156683 : PrimeCertificate 156683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv78341]) (by decide +kernel)
def pv156683 : PrimeValue := ⟨156683, pr156683⟩
private theorem pr156841 : PrimeCertificate 156841 :=
  certifyPrime (q := pv19) (ls := [pv2,pv3,pv5,pv1307]) (by decide +kernel)
def pv156841 : PrimeValue := ⟨156841, pr156841⟩
private theorem pr156979 : PrimeCertificate 156979 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv17,pv19]) (by decide +kernel)
def pv156979 : PrimeValue := ⟨156979, pr156979⟩
private theorem pr157433 : PrimeCertificate 157433 :=
  certifyPrime (q := pv3) (ls := [pv2,pv11,pv1789]) (by decide +kernel)
def pv157433 : PrimeValue := ⟨157433, pr157433⟩
private theorem pr157457 : PrimeCertificate 157457 :=
  certifyPrime (q := pv3) (ls := [pv2,pv13,pv757]) (by decide +kernel)
def pv157457 : PrimeValue := ⟨157457, pr157457⟩
private theorem pr157907 : PrimeCertificate 157907 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11279]) (by decide +kernel)
def pv157907 : PrimeValue := ⟨157907, pr157907⟩
private theorem pr158189 : PrimeCertificate 158189 :=
  certifyPrime (q := pv2) (ls := [pv2,pv71,pv557]) (by decide +kernel)
def pv158189 : PrimeValue := ⟨158189, pr158189⟩
private theorem pr158243 : PrimeCertificate 158243 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv89,pv127]) (by decide +kernel)
def pv158243 : PrimeValue := ⟨158243, pr158243⟩
private theorem pr158269 : PrimeCertificate 158269 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv109]) (by decide +kernel)
def pv158269 : PrimeValue := ⟨158269, pr158269⟩
private theorem pr158507 : PrimeCertificate 158507 :=
  certifyPrime (q := pv2) (ls := [pv2,pv41,pv1933]) (by decide +kernel)
def pv158507 : PrimeValue := ⟨158507, pr158507⟩
private theorem pr158519 : PrimeCertificate 158519 :=
  certifyPrime (q := pv7) (ls := [pv2,pv79259]) (by decide +kernel)
def pv158519 : PrimeValue := ⟨158519, pr158519⟩
private theorem pr158527 : PrimeCertificate 158527 :=
  certifyPrime (q := pv37) (ls := [pv2,pv3,pv8807]) (by decide +kernel)
def pv158527 : PrimeValue := ⟨158527, pr158527⟩
private theorem pr158771 : PrimeCertificate 158771 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv15877]) (by decide +kernel)
def pv158771 : PrimeValue := ⟨158771, pr158771⟩
private theorem pr159503 : PrimeCertificate 159503 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv11393]) (by decide +kernel)
def pv159503 : PrimeValue := ⟨159503, pr159503⟩
private theorem pr159589 : PrimeCertificate 159589 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv13,pv31]) (by decide +kernel)
def pv159589 : PrimeValue := ⟨159589, pr159589⟩
private theorem pr159769 : PrimeCertificate 159769 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv7,pv317]) (by decide +kernel)
def pv159769 : PrimeValue := ⟨159769, pr159769⟩
private theorem pr159787 : PrimeCertificate 159787 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv11,pv269]) (by decide +kernel)
def pv159787 : PrimeValue := ⟨159787, pr159787⟩
private theorem pr159833 : PrimeCertificate 159833 :=
  certifyPrime (q := pv3) (ls := [pv2,pv19979]) (by decide +kernel)
def pv159833 : PrimeValue := ⟨159833, pr159833⟩
private theorem pr159931 : PrimeCertificate 159931 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv1777]) (by decide +kernel)
def pv159931 : PrimeValue := ⟨159931, pr159931⟩
private theorem pr159979 : PrimeCertificate 159979 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv7,pv13,pv293]) (by decide +kernel)
def pv159979 : PrimeValue := ⟨159979, pr159979⟩
private theorem pr160009 : PrimeCertificate 160009 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv59,pv113]) (by decide +kernel)
def pv160009 : PrimeValue := ⟨160009, pr160009⟩
private theorem pr160073 : PrimeCertificate 160073 :=
  certifyPrime (q := pv5) (ls := [pv2,pv11,pv17,pv107]) (by decide +kernel)
def pv160073 : PrimeValue := ⟨160073, pr160073⟩
private theorem pr160163 : PrimeCertificate 160163 :=
  certifyPrime (q := pv2) (ls := [pv2,pv73,pv1097]) (by decide +kernel)
def pv160163 : PrimeValue := ⟨160163, pr160163⟩
private theorem pr160217 : PrimeCertificate 160217 :=
  certifyPrime (q := pv3) (ls := [pv2,pv7,pv2861]) (by decide +kernel)
def pv160217 : PrimeValue := ⟨160217, pr160217⟩
private theorem pr160397 : PrimeCertificate 160397 :=
  certifyPrime (q := pv2) (ls := [pv2,pv40099]) (by decide +kernel)
def pv160397 : PrimeValue := ⟨160397, pr160397⟩
private theorem pr160499 : PrimeCertificate 160499 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6173]) (by decide +kernel)
def pv160499 : PrimeValue := ⟨160499, pr160499⟩
private theorem pr160591 : PrimeCertificate 160591 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv53,pv101]) (by decide +kernel)
def pv160591 : PrimeValue := ⟨160591, pr160591⟩
private theorem pr160883 : PrimeCertificate 160883 :=
  certifyPrime (q := pv2) (ls := [pv2,pv257,pv313]) (by decide +kernel)
def pv160883 : PrimeValue := ⟨160883, pr160883⟩
private theorem pr161017 : PrimeCertificate 161017 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv6709]) (by decide +kernel)
def pv161017 : PrimeValue := ⟨161017, pr161017⟩
private theorem pr161267 : PrimeCertificate 161267 :=
  certifyPrime (q := pv2) (ls := [pv2,pv7,pv11519]) (by decide +kernel)
def pv161267 : PrimeValue := ⟨161267, pr161267⟩
private theorem pr161323 : PrimeCertificate 161323 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv7,pv23,pv167]) (by decide +kernel)
def pv161323 : PrimeValue := ⟨161323, pr161323⟩
private theorem pr161461 : PrimeCertificate 161461 :=
  certifyPrime (q := pv7) (ls := [pv2,pv3,pv5,pv13,pv23]) (by decide +kernel)
def pv161461 : PrimeValue := ⟨161461, pr161461⟩
private theorem pr161773 : PrimeCertificate 161773 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv13,pv17,pv61]) (by decide +kernel)
def pv161773 : PrimeValue := ⟨161773, pr161773⟩
private theorem pr161911 : PrimeCertificate 161911 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv5,pv7,pv257]) (by decide +kernel)
def pv161911 : PrimeValue := ⟨161911, pr161911⟩
private theorem pr162359 : PrimeCertificate 162359 :=
  certifyPrime (q := pv7) (ls := [pv2,pv7,pv11597]) (by decide +kernel)
def pv162359 : PrimeValue := ⟨162359, pr162359⟩
private theorem pr162527 : PrimeCertificate 162527 :=
  certifyPrime (q := pv5) (ls := [pv2,pv7,pv13,pv19,pv47]) (by decide +kernel)
def pv162527 : PrimeValue := ⟨162527, pr162527⟩
private theorem pr162611 : PrimeCertificate 162611 :=
  certifyPrime (q := pv2) (ls := [pv2,pv5,pv7,pv23,pv101]) (by decide +kernel)
def pv162611 : PrimeValue := ⟨162611, pr162611⟩
private theorem pr162649 : PrimeCertificate 162649 :=
  certifyPrime (q := pv29) (ls := [pv2,pv3,pv251]) (by decide +kernel)
def pv162649 : PrimeValue := ⟨162649, pr162649⟩
private theorem pr162677 : PrimeCertificate 162677 :=
  certifyPrime (q := pv2) (ls := [pv2,pv67,pv607]) (by decide +kernel)
def pv162677 : PrimeValue := ⟨162677, pr162677⟩
private theorem pr162683 : PrimeCertificate 162683 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv6257]) (by decide +kernel)
def pv162683 : PrimeValue := ⟨162683, pr162683⟩
private theorem pr162727 : PrimeCertificate 162727 :=
  certifyPrime (q := pv5) (ls := [pv2,pv3,pv37,pv733]) (by decide +kernel)
def pv162727 : PrimeValue := ⟨162727, pr162727⟩
private theorem pr162739 : PrimeCertificate 162739 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv9041]) (by decide +kernel)
def pv162739 : PrimeValue := ⟨162739, pr162739⟩
private theorem pr162847 : PrimeCertificate 162847 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv83,pv109]) (by decide +kernel)
def pv162847 : PrimeValue := ⟨162847, pr162847⟩
private theorem pr162917 : PrimeCertificate 162917 :=
  certifyPrime (q := pv2) (ls := [pv2,pv13,pv241]) (by decide +kernel)
def pv162917 : PrimeValue := ⟨162917, pr162917⟩
private theorem pr163021 : PrimeCertificate 163021 :=
  certifyPrime (q := pv23) (ls := [pv2,pv3,pv5,pv11,pv13,pv19]) (by decide +kernel)
def pv163021 : PrimeValue := ⟨163021, pr163021⟩
private theorem pr163027 : PrimeCertificate 163027 :=
  certifyPrime (q := pv2) (ls := [pv2,pv3,pv3019]) (by decide +kernel)
def pv163027 : PrimeValue := ⟨163027, pr163027⟩
private theorem pr163063 : PrimeCertificate 163063 :=
  certifyPrime (q := pv3) (ls := [pv2,pv3,pv9059]) (by decide +kernel)
def pv163063 : PrimeValue := ⟨163063, pr163063⟩
private theorem pr163211 : PrimeCertificate 163211 :=
  certifyPrime (q := pv19) (ls := [pv2,pv5,pv19,pv859]) (by decide +kernel)
def pv163211 : PrimeValue := ⟨163211, pr163211⟩

end D5.S3.Arith.PrimitiveRoot.SmallPrimes
