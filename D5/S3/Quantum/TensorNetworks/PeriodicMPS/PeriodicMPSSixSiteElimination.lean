/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteElimination
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSSixSiteElimination
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteEliminationCertificate]
   utility: none
   digest: The physical six-site special fiber has a unique invariant triple. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteEliminationCertificate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elimination on the six-site special fiber

The six univariate dot products pair the certificate rows with the signed cofactors
of the constant row, up to a common scale. The resulting factored eliminant
restricts the possible projections of a physical invariant triple.
-/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteElimination

open PeriodicMPSSixSiteInvariants
open D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteEliminationCertificate (columns_zero)

open private column1 column2 column3 column4 column5 column6
  coeffUVSquared1 coeffUVSquared2 coeffUVSquared3 coeffUVSquared4 coeffUVSquared5 coeffUVSquared6
  coeffVSquared1 coeffVSquared2 coeffVSquared3 coeffVSquared4 coeffVSquared5 coeffVSquared6
  coeffUV1 coeffUV2 coeffUV3 coeffUV4 coeffUV5 coeffUV6
  coeffV1 coeffV2 coeffV3 coeffV4 coeffV5 coeffV6
  coeffU1 coeffU2 coeffU3 coeffU4 coeffU5 coeffU6
  coeffConstant1 coeffConstant2 coeffConstant3 coeffConstant4 coeffConstant5 coeffConstant6
  from D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSSixSiteEliminationCertificate

private def positiveFactor (t : ℝ) : ℝ :=
  8192000 * t ^ 16
  - 754483200 * t ^ 15
  + 80402882560 * t ^ 14
  + 47331269922816 * t ^ 13
  - 505746268527616 * t ^ 12
  - 1053365214106046976 * t ^ 11
  + 82734601922423398784 * t ^ 10
  + 968271911611500765248 * t ^ 9
  + 579775026684871436917344 * t ^ 8
  + 9219437102627568489303072 * t ^ 7
  + 99594307741202393725669912 * t ^ 6
  + 36271345478636576968985200004 * t ^ 5
  + 1507097162530079228672107732698 * t ^ 4
  + 22530344114876426313991984931098 * t ^ 3
  + 141953088291106567485645566286388 * t ^ 2
  + 325100363757733616268835412911209 * t
  + 240782252897256832861143685396345

private theorem positiveFactor_two_squares (t : ℝ) :
    positiveFactor t =
      8192000 * t ^ 14 * (t - 50) ^ 2
      + 64716800 * t ^ 15
      + 59922882560 * t ^ 14
      + t ^ 10 * ((47331269922816 * t + 8013882317579264) * (t - 90) ^ 2
        + 5750316683410944 * t + 17822155150031360384)
      + 968271911611500765248 * t ^ 9
      + 579775026684871436917344 * t ^ 8
      + 9219437102627568489303072 * t ^ 7
      + 99594307741202393725669912 * t ^ 6
      + 36271345478636576968985200004 * t ^ 5
      + 1507097162530079228672107732698 * t ^ 4
      + 22530344114876426313991984931098 * t ^ 3
      + 141953088291106567485645566286388 * t ^ 2
      + 325100363757733616268835412911209 * t ^ 1
      + 240782252897256832861143685396345 := by
  unfold positiveFactor
  ring1

private theorem positiveFactor_pos (t : ℝ) (ht : 0 ≤ t) : 0 < positiveFactor t := by
  rw [positiveFactor_two_squares]
  positivity

private def eliminant (t : ℝ) : ℝ :=
  (t - 26) * (t - 4) ^ 2 * (t + 5) ^ 5 * positiveFactor t

private def cofactor1 (t : ℝ) : ℝ :=
  -1040556054528000 * t ^ 17
  - 5126182117454131200 * t ^ 16
  + 1073434569163487262720 * t ^ 15
  + 4400531125273266001920 * t ^ 14
  - 58459915106764024055040 * t ^ 13
  - 134752937574968134061814720 * t ^ 12
  + 3506521296540956133419679840 * t ^ 11
  - 24790517417518302288159430320 * t ^ 10
  - 2598124620921835130123017670560 * t ^ 9
  + 111777822760913825561485443598980 * t ^ 8
  + 1063646576234923401987986440909190 * t ^ 7
  - 68295963648171271065519731608642715 * t ^ 6
  + 81677566048822511538464152723433380 * t ^ 5
  + 13619016270968394165518746092114188195 * t ^ 4
  - 2837722576111447511326876579179574415 * t ^ 3
  - 750286823189372091436797891282755906150 * t ^ 2
  + 1043882440376746845739103357721209102125 * t
  + 4584183334868053711127980319973508131250

private def cofactor2 (t : ℝ) : ℝ :=
  2822275325952000 * t ^ 18
  + 1701242110954716364800 * t ^ 17
  - 354544780071871416545280 * t ^ 16
  - 1667757074292967549409280 * t ^ 15
  + 104318026568448978737986560 * t ^ 14
  + 44305051970227827463932026880 * t ^ 13
  - 1251302659272103567725108941760 * t ^ 12
  + 12015113174664039007018569283680 * t ^ 11
  + 615729277967306899119549612561840 * t ^ 10
  - 38014382583057246472112334589793520 * t ^ 9
  - 53356794764582736847449251641497660 * t ^ 8
  + 21536054464305815132247630125483128710 * t ^ 7
  - 184247774743885022843786017388392525245 * t ^ 6
  - 3777283039479280216762918845130019995380 * t ^ 5
  + 31615181197477479820077854818711292500785 * t ^ 4
  + 218975651043108686964721893835325720253975 * t ^ 3
  - 1933145395876802180047004658106220835495750 * t ^ 2
  + 815951376417379306705849187196047586099375 * t
  + 9762811959615540861696929507965035986943750

private def cofactor3 (t : ℝ) : ℝ :=
  8039682175795200 * t ^ 18
  + 17667946046994554880 * t ^ 17
  - 4172377549494467063808 * t ^ 16
  + 49446390358468491374592 * t ^ 15
  + 583502988785558832608256 * t ^ 14
  + 565795117606514712685296768 * t ^ 13
  - 16913528658769054914375203136 * t ^ 12
  + 107696721219119668014173269728 * t ^ 11
  + 16547231100156656646173592738464 * t ^ 10
  - 532027557862470876553244798204472 * t ^ 9
  - 8457732189112399653611012009569396 * t ^ 8
  + 382872447270603758999697991498386406 * t ^ 7
  + 2010389848021480930824309771320588308 * t ^ 6
  - 88976439467891025480968563570131360418 * t ^ 5
  - 526709996650420947738583466782265312534 * t ^ 4
  + 5175287221509646487115275782285923466120 * t ^ 3
  + 26913370189521270672676942354933275809350 * t ^ 2
  - 81318464053203276500269660396683108372500 * t
  - 214398957762812186026223868751529193210000

private def cofactor4 (t : ℝ) : ℝ :=
  7613099174943129600 * t ^ 19
  - 19395093140039276789760 * t ^ 18
  + 3810742075147405394313216 * t ^ 17
  + 50181707876825506250981376 * t ^ 16
  - 1940476755496360283905370112 * t ^ 15
  - 463869248956080410398093641216 * t ^ 14
  + 13426561511976839022784157893632 * t ^ 13
  - 243048837069593748666177191496576 * t ^ 12
  + 1983657633164291374369192024324992 * t ^ 11
  + 351915709672751209188747788669154624 * t ^ 10
  - 6794077650476291564342834783611089888 * t ^ 9
  - 80403181517396427945533987658595619832 * t ^ 8
  + 5568646126905418576268009519931226855944 * t ^ 7
  - 37767032875212779716091886740530875636954 * t ^ 6
  - 911506710789790382220417392966529397870512 * t ^ 5
  + 9195442589723469635731591308378757092546630 * t ^ 4
  + 55749624818770405279289948920176144636560670 * t ^ 3
  - 600860802434674159258024889509517159247559800 * t ^ 2
  + 369267317044858879578054801868544147974274250 * t
  + 3183789062645505192153756733661728762545862500

private def cofactor5 (t : ℝ) : ℝ :=
  -450585439867699200 * t ^ 19
  - 699518174012862382080 * t ^ 18
  + 225541252172131937722368 * t ^ 17
  - 10472302068995689498976256 * t ^ 16
  - 251834386509882532120679424 * t ^ 15
  - 33562447945177890810485286144 * t ^ 14
  + 1485333788098299079519650043008 * t ^ 13
  - 8614609055042365878640655510592 * t ^ 12
  - 1351945154668281983961084180286848 * t ^ 11
  + 40334137607026683314888695492061808 * t ^ 10
  + 521123181035193117209148020126037192 * t ^ 9
  - 35338926572305094336634200204204612580 * t ^ 8
  - 164493080345031205327360023903568588968 * t ^ 7
  + 9422927741946837838619243324646566989440 * t ^ 6
  + 43139816496619693101219429351699152171784 * t ^ 5
  - 821895208318629043924098122388479579676036 * t ^ 4
  - 3005071290920342697293931067743179487720672 * t ^ 3
  + 23658555302886548849776541262856803541723080 * t ^ 2
  + 6534624379811357824016321651591758731016200 * t
  - 84482813892822276241866977855283938122920000

private def cofactor6 (t : ℝ) : ℝ :=
  -215267491282983321600 * t ^ 20
  + 208095163164263501660160 * t ^ 19
  - 38220927451480633349799936 * t ^ 18
  - 921407162842738771473973248 * t ^ 17
  + 43586165377371373317854650368 * t ^ 16
  + 4729129875141128655658776188928 * t ^ 15
  - 144808675277331956728338923659776 * t ^ 14
  + 4347827485787697486588637047477504 * t ^ 13
  - 195729100049221497108133016389098624 * t ^ 12
  - 907426750907465464981094297411118336 * t ^ 11
  + 167269216383449986481310484971485961696 * t ^ 10
  - 3396573858398323838555437653330490077360 * t ^ 9
  - 67842635384262086242899238490190181352424 * t ^ 8
  + 2654388308078276653192450903397412712887600 * t ^ 7
  - 5412649699976846983746520812737046739770888 * t ^ 6
  - 455356811901627412707444943349118231557848368 * t ^ 5
  + 2311233163029794654976067855976325543601704624 * t ^ 4
  + 27145870241699398102144021026784298862386355960 * t ^ 3
  - 182731324792061731567308488540903188160751445200 * t ^ 2
  + 36399004124609440772711238466137436041540663000 * t
  + 896533771146998093918078584114266130884715650000

private def dotUVSquared (t : ℝ) : ℝ :=
  coeffUVSquared1 t * cofactor1 t
      + coeffUVSquared2 t * cofactor2 t
      + coeffUVSquared3 t * cofactor3 t
      + coeffUVSquared4 t * cofactor4 t
      + coeffUVSquared5 t * cofactor5 t
      + coeffUVSquared6 t * cofactor6 t

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem dotUVSquared_eq (t : ℝ) :
    dotUVSquared t = 0 := by
  unfold dotUVSquared coeffUVSquared1 coeffUVSquared2 coeffUVSquared3 coeffUVSquared4
    coeffUVSquared5 coeffUVSquared6 cofactor1 cofactor2 cofactor3 cofactor4 cofactor5 cofactor6
  ring1

private def dotVSquared (t : ℝ) : ℝ :=
  coeffVSquared1 t * cofactor1 t
      + coeffVSquared2 t * cofactor2 t
      + coeffVSquared3 t * cofactor3 t
      + coeffVSquared4 t * cofactor4 t
      + coeffVSquared5 t * cofactor5 t
      + coeffVSquared6 t * cofactor6 t

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem dotVSquared_eq (t : ℝ) :
    dotVSquared t = 0 := by
  unfold dotVSquared coeffVSquared1 coeffVSquared2 coeffVSquared3 coeffVSquared4 coeffVSquared5
    coeffVSquared6 cofactor1 cofactor2 cofactor3 cofactor4 cofactor5 cofactor6
  ring1

private def dotUV (t : ℝ) : ℝ :=
  coeffUV1 t * cofactor1 t
      + coeffUV2 t * cofactor2 t
      + coeffUV3 t * cofactor3 t
      + coeffUV4 t * cofactor4 t
      + coeffUV5 t * cofactor5 t
      + coeffUV6 t * cofactor6 t

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem dotUV_eq (t : ℝ) :
    dotUV t = 0 := by
  unfold dotUV coeffUV1 coeffUV2 coeffUV3 coeffUV4 coeffUV5 coeffUV6 cofactor1 cofactor2
    cofactor3 cofactor4 cofactor5 cofactor6
  ring1

private def dotV (t : ℝ) : ℝ :=
  coeffV1 t * cofactor1 t
      + coeffV2 t * cofactor2 t
      + coeffV3 t * cofactor3 t
      + coeffV4 t * cofactor4 t
      + coeffV5 t * cofactor5 t
      + coeffV6 t * cofactor6 t

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem dotV_eq (t : ℝ) :
    dotV t = 0 := by
  unfold dotV coeffV1 coeffV2 coeffV3 coeffV4 coeffV5 coeffV6 cofactor1 cofactor2 cofactor3
    cofactor4 cofactor5 cofactor6
  ring1

private def dotU (t : ℝ) : ℝ :=
  coeffU1 t * cofactor1 t
      + coeffU2 t * cofactor2 t
      + coeffU3 t * cofactor3 t
      + coeffU4 t * cofactor4 t
      + coeffU5 t * cofactor5 t
      + coeffU6 t * cofactor6 t

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem dotU_eq (t : ℝ) :
    dotU t = 0 := by
  unfold dotU coeffU1 coeffU2 coeffU3 coeffU4 coeffU5 coeffU6 cofactor1 cofactor2 cofactor3
    cofactor4 cofactor5 cofactor6
  ring1

private def dotConstant (t : ℝ) : ℝ :=
  coeffConstant1 t * cofactor1 t
      + coeffConstant2 t * cofactor2 t
      + coeffConstant3 t * cofactor3 t
      + coeffConstant4 t * cofactor4 t
      + coeffConstant5 t * cofactor5 t
      + coeffConstant6 t * cofactor6 t

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem dotConstant_eq (t : ℝ) :
    dotConstant t = 10566556110000000 * eliminant t := by
  unfold dotConstant coeffConstant1 coeffConstant2 coeffConstant3 coeffConstant4 coeffConstant5
    coeffConstant6 cofactor1 cofactor2 cofactor3 cofactor4 cofactor5 cofactor6 eliminant
    positiveFactor
  ring1

private theorem sumByRows (u v t : ℝ) :
    column1 u v t * cofactor1 t
      + column2 u v t * cofactor2 t
      + column3 u v t * cofactor3 t
      + column4 u v t * cofactor4 t
      + column5 u v t * cofactor5 t
      + column6 u v t * cofactor6 t =
      u * v ^ 2 * dotUVSquared t
      + v ^ 2 * dotVSquared t
      + u * v * dotUV t
      + v * dotV t
      + u * dotU t
      + dotConstant t := by
  unfold column1 column2 column3 column4 column5 column6 dotUVSquared dotVSquared dotUV dotV
    dotU dotConstant
  ring1

private theorem eliminant_zero (u v t : ℝ)
    (h1 : column1 u v t = 0)
    (h2 : column2 u v t = 0)
    (h3 : column3 u v t = 0)
    (h4 : column4 u v t = 0)
    (h5 : column5 u v t = 0)
    (h6 : column6 u v t = 0) :
    eliminant t = 0 := by
  have h := sumByRows u v t
  simp only [h1, h2, h3, h4, h5, h6, dotUVSquared_eq, dotVSquared_eq, dotUV_eq,
    dotV_eq, dotU_eq, dotConstant_eq, zero_mul, mul_zero, add_zero, zero_add] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by norm_num)

private theorem possibleProjections (t : ℝ) (ht : 0 ≤ t) (he : eliminant t = 0) :
    t = 4 ∨ t = 26 := by
  have hp : positiveFactor t ≠ 0 := ne_of_gt (positiveFactor_pos t ht)
  have hn : t + 5 ≠ 0 := ne_of_gt (by linarith only [ht])
  unfold eliminant at he
  have h := (mul_eq_zero.mp he).resolve_right hp
  have h' := (mul_eq_zero.mp h).resolve_right (pow_ne_zero 5 hn)
  rcases mul_eq_zero.mp h' with h26 | h4
  · exact Or.inr (sub_eq_zero.mp h26)
  · exact Or.inl (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h4))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem coordinatesAt4 (u v : ℝ)
    (h1 : column1 u v 4 = 0)
    (h2 : column2 u v 4 = 0)
    (h3 : column3 u v 4 = 0)
    (h4 : column4 u v 4 = 0)
    (h5 : column5 u v 4 = 0) :
    u = (-1) ∧ v = 0 := by
  unfold column1 coeffUVSquared1 coeffVSquared1 coeffUV1 coeffV1 coeffU1 coeffConstant1 at h1
  unfold column2 coeffUVSquared2 coeffVSquared2 coeffUV2 coeffV2 coeffU2 coeffConstant2 at h2
  unfold column3 coeffUVSquared3 coeffVSquared3 coeffUV3 coeffV3 coeffU3 coeffConstant3 at h3
  unfold column4 coeffUVSquared4 coeffVSquared4 coeffUV4 coeffV4 coeffU4 coeffConstant4 at h4
  unfold column5 coeffUVSquared5 coeffVSquared5 coeffUV5 coeffV5 coeffU5 coeffConstant5 at h5
  norm_num at h1 h2 h3 h4 h5
  constructor
  · linear_combination (norm := ring1)
      (13143325534734941652077136708280189717 / 99017466595270107891302884604652811289574502742700000 : ℝ) * h1
      + (2664212323189273142543277429963680682449 / 33005822198423369297100961534884270429858167580900000 : ℝ) * h2
      + (-229900565076694834019478976170414824599 / 17681690463441090694875515107973716301709732632625000 : ℝ) * h3
      + (2751460458545438850911977514608753067873681 / 82514555496058423242752403837210676074645418952250000 : ℝ) * h4
      + (61233152220614250466406643213045708769703 / 8251455549605842324275240383721067607464541895225000 : ℝ) * h5
  · linear_combination (norm := ring1)
      (3689289342354812723985515816607674603 / 62868232758901655804001831495017657961634604916000000 : ℝ) * h1
      + (747787946042719040653503036816044340991 / 20956077586300551934667277165005885987211534972000000 : ℝ) * h2
      + (-451705599175975504103198717920901817227 / 78585290948627069755002289368772072452043256145000000 : ℝ) * h3
      + (772392495155688439668354470532947575559959 / 52390193965751379836668192912514714968028837430000000 : ℝ) * h4
      + (17186057488555084185028010930482485583597 / 5239019396575137983666819291251471496802883743000000 : ℝ) * h5

set_option maxRecDepth 2048 in
set_option maxHeartbeats 4000000 in
private theorem coordinatesAt26 (u v : ℝ)
    (h1 : column1 u v 26 = 0)
    (h2 : column2 u v 26 = 0)
    (h3 : column3 u v 26 = 0)
    (h4 : column4 u v 26 = 0)
    (h5 : column5 u v 26 = 0) :
    u = 1 ∧ v = 1 := by
  unfold column1 coeffUVSquared1 coeffVSquared1 coeffUV1 coeffV1 coeffU1 coeffConstant1 at h1
  unfold column2 coeffUVSquared2 coeffVSquared2 coeffUV2 coeffV2 coeffU2 coeffConstant2 at h2
  unfold column3 coeffUVSquared3 coeffVSquared3 coeffUV3 coeffV3 coeffU3 coeffConstant3 at h3
  unfold column4 coeffUVSquared4 coeffVSquared4 coeffUV4 coeffV4 coeffU4 coeffConstant4 at h4
  unfold column5 coeffUVSquared5 coeffVSquared5 coeffUV5 coeffV5 coeffU5 coeffConstant5 at h5
  norm_num at h1 h2 h3 h4 h5
  constructor
  · linear_combination (norm := ring1)
      (269787807488440057288666732724874101731 / 31994892565241611823950370045806664037373218303684351600000 : ℝ) * h1
      + (-477069693389634098796133284106360520022833 / 10664964188413870607983456681935554679124406101228117200000 : ℝ) * h2
      + (-6205111279223073970220654411049300658247 / 9998403926638003694984490639314582511679130719901359875000 : ℝ) * h3
      + (875930400812147165530899661585387261770199 / 78188887011831895952957893562577380345486848249473000000 : ℝ) * h4
      + (-409949236858144866671562432735748784990693 / 242385549736678877454169470043989879071009229573366300000 : ℝ) * h5
  · linear_combination (norm := ring1)
      (375167569506861673985224027334722168379 / 142199522512184941439779422425807395721658748016374896000000 : ℝ) * h1
      + (-449897060644184487115185973811582897230777 / 47399840837394980479926474141935798573886249338791632000000 : ℝ) * h2
      + (-4369165115965426302466940952159611953603 / 44437350785057794199931069508064811163018358755117155000000 : ℝ) * h3
      + (940738371121499720449338550689058488319151 / 347506164497030648679812860278121690424385992219880000000 : ℝ) * h4
      + (-1268865898482901172398447958713203404998717 / 1077269109940795010907419866862177240315596575881628000000 : ℝ) * h5

/-- The three invariant equations determine the physical invariant triple. -/
theorem specialFiber_unique {u v w t : ℝ} (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hproj : t = u + 25 * v - 10 * w)
    (h0 : specialEquation 0 u v w = 0)
    (h1 : specialEquation 1 u v w = 0)
    (h2 : specialEquation 2 u v w = 0) :
    u = 1 ∧ v = 1 ∧ w = 0 := by
  have hw : w = (u + 25 * v - t) / 10 := by
    linear_combination (1 / 10 : ℝ) * hproj
  rw [hw] at h0 h1 h2
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := columns_zero u v t h0 h1 h2
  have he := eliminant_zero u v t hc1 hc2 hc3 hc4 hc5 hc6
  rcases possibleProjections t ht he with ht4 | ht26
  · rw [ht4] at hc1 hc2 hc3 hc4 hc5
    have hu4 := (coordinatesAt4 u v hc1 hc2 hc3 hc4 hc5).1
    exfalso
    linarith only [hu, hu4]
  · rw [ht26] at hc1 hc2 hc3 hc4 hc5
    obtain ⟨hu26, hv26⟩ := coordinatesAt26 u v hc1 hc2 hc3 hc4 hc5
    refine ⟨hu26, hv26, ?_⟩
    linarith only [hproj, ht26, hu26, hv26]

end D5.S3.Quantum.TensorNetworks.PeriodicMPSSixSiteElimination
