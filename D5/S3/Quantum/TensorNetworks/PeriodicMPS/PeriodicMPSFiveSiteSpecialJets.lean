/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialJets
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSFiveSiteSpecialJets
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetCoordinates]
   utility: none
   digest: The four five-site special source points are regular and have distinct normal cubics. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSFiveSiteJetCoordinates

/-! Exact rational inverse matrices and source paths through the four lifts. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialJets

open Matrix PeriodicMPSFiveSiteJetCoordinates

private def source0 : Fin 9 → ℚ :=
  ![7 / 6, 7 / 6, 0, -1 / 2, 0, 0, 0, 0, 1]

private def derivative0 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![2695 / 108, 1955 / 54, -105 / 4, -1883 / 36, -7 / 3, 10 / 3, 161 / 12, -4, 33373 / 1296;
    23 / 12, 7 / 6, 7 / 4, -56 / 9, 25 / 12, 7 / 12, 40825 / 1296, 161 / 18, 161 / 72;
    -7 / 6, 23 / 12, -49 / 18, -9 / 4, 7 / 12, -25 / 12, -161 / 18, -30457 / 1296, 0;
    0, 0, 0, 0, -623 / 216, -1955 / 216, 161 / 36, 0, 0;
    0, 0, 0, 0, -1955 / 216, 623 / 216, 0, -161 / 36, 0;
    0, 0, 0, -1, -14 / 3, 20 / 3, 161 / 36, 2, 9 / 4;
    0, 0, 0, -1, 0, 1, 161 / 36, 2, 5 / 4;
    0, 0, 0, 0, 17 / 12, -7 / 12, 7 / 2, 0, 0;
    0, 0, 0, 0, -7 / 12, -17 / 12, 0, -7 / 2, 0]

private def inverse0 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![1209 / 33350, -233 / 870, -12 / 23, -12396867 / 15130895, 58561225 / 63549759, -5456131 / 3601800, 885677 / 360180, 1434171 / 1842022, 58268153 / 27235611;
    -294 / 16675, 238 / 435, 12 / 23, 148916203 / 105916265, -143768980 / 63549759, 6844571 / 1800900, -2685749 / 360180, -5373448 / 8289099, -489322019 / 381298554;
    -9 / 322, 1 / 2, 36 / 161, 10458559 / 15339597, -1264237 / 786646, 26569 / 11592, -25759 / 5796, -11660477 / 6002451, 2983075 / 4719876;
    0, 0, 0, 1811 / 4886, -62288 / 95277, 5 / 4, -9 / 4, 23575 / 29316, 226316 / 857493;
    0, 0, 0, -18 / 349, -414 / 4537, 0, 0, 23 / 349, 529 / 4537;
    0, 0, 0, -414 / 4537, 18 / 349, 0, 0, 529 / 4537, -23 / 349;
    0, 0, 0, 180 / 31759, 1446 / 31759, 0, 0, 8844 / 31759, -5543 / 95277;
    0, 0, 0, 1446 / 31759, -180 / 31759, 0, 0, -5543 / 95277, -8844 / 31759;
    0, 0, 0, 1254 / 4537, -3258 / 4537, 1, -1, -4807 / 13611, 4163 / 4537]

private def firstDirection0 : Fin 9 → ℚ :=
  ![58561225 / 63549759, -143768980 / 63549759, -1264237 / 786646, -62288 / 95277, -414 / 4537, 18 / 349, 1446 / 31759, -180 / 31759, -3258 / 4537]

private def secondDirection0 : Fin 9 → ℚ :=
  ![-21042295338856523415797 / 123985637186698371329700, -220544603020618159316321 / 123985637186698371329700, -124051870474164163493 / 61919105372667438714, 98747433525399180883 / 61919105372667438714, 173725546522371 / 3052307274606499, 21396503780151 / 132709011939413, -1419413158360759 / 21366150922245493, -1218138932790041 / 21366150922245493, -1565341344140065 / 3052307274606499]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Each differentiated entry is reduced once before matrix operations.
private lemma evalDerivative0 : tangentJacobian source0 = derivative0 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The inverse identity is checked one rational entry at a time.
private lemma hasInverse0 : tangentJacobian source0 * inverse0 = 1 := by
  rw [evalDerivative0]
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The closed rational identities are checked through cubic order.
private lemma jetCoefficients0 :
    (∀ j, rawJacobian source0 9 j = 0) ∧
    (∀ j : Fin 9, (tangentJacobian source0 *ᵥ firstDirection0) j = if j = 4 then 1 else 0) ∧
    (∀ j : Fin 9, quadraticCoefficient source0 firstDirection0 secondDirection0 j.castSucc = 0) ∧
    cubicCoefficient source0 firstDirection0 secondDirection0 9 = -3801462887520 / 1725217155212369 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> decide +kernel
  · intro j
    rw [evalDerivative0]
    fin_cases j <;> decide +kernel
  · intro j
    fin_cases j <;> decide +kernel
  · decide +kernel

private def source1 : Fin 9 → ℚ :=
  ![-7 / 6, -8 / 3, 0, -1 / 2, 0, 0, 0, 0, 1]

private def derivative1 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![-2695 / 108, -1955 / 54, 875 / 18, 2027 / 36, 7 / 3, -13 / 3, 161 / 12, -4, 33373 / 1296;
    -23 / 12, -7 / 6, 15 / 2, -49 / 18, 1 / 6, -7 / 12, 40825 / 1296, 161 / 18, 161 / 72;
    7 / 6, -23 / 12, -56 / 9, 7 / 2, -7 / 12, -1 / 6, -161 / 18, -30457 / 1296, 0;
    0, 0, 0, 0, 259 / 27, 1955 / 216, 161 / 36, 0, 0;
    0, 0, 0, 0, 1955 / 216, -259 / 27, 0, -161 / 36, 0;
    0, 0, 0, -1, 14 / 3, -26 / 3, 161 / 36, 2, 9 / 4;
    0, 0, 0, -1, 0, 1, 161 / 36, 2, 5 / 4;
    0, 0, 0, 0, 10 / 3, 7 / 12, 7 / 2, 0, 0;
    0, 0, 0, 0, 7 / 12, -10 / 3, 0, -7 / 2, 0]

private def inverse1 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![-14019 / 116725, 769 / 435, 192 / 161, 176278973119 / 41267189950, -350406033248 / 61900784925, 105777821 / 12606300, -19907617 / 1260630, -271422428449 / 32296061700, -21556781272 / 61900784925;
    294 / 16675, -238 / 435, -12 / 23, -54658756 / 421093775, -2954024417 / 2526562650, -22799 / 450225, 127267 / 180090, 469761938 / 164775825, 59935679447 / 15159375900;
    -9 / 322, 1 / 2, 36 / 161, 598024699 / 426901965, -1403647619 / 853803930, 26569 / 11592, -25759 / 5796, -477992987 / 167048595, 10437272407 / 15368470740;
    0, 0, 0, 1883573 / 5303130, -3720422 / 2651565, 5 / 4, -9 / 4, 78649811 / 95456340, 29148233 / 23864085;
    0, 0, 0, 6912 / 126265, 10764 / 126265, 0, 0, -8832 / 126265, -13754 / 126265;
    0, 0, 0, 10764 / 126265, -6912 / 126265, 0, 0, -13754 / 126265, 8832 / 126265;
    0, 0, 0, -58638 / 883855, -63696 / 883855, 0, 0, 982369 / 2651565, 244168 / 2651565;
    0, 0, 0, -63696 / 883855, 58638 / 883855, 0, 0, 244168 / 2651565, -982369 / 2651565;
    0, 0, 0, 71796 / 126265, -117048 / 126265, 1, -1, -275218 / 378795, 448684 / 378795]

private def firstDirection1 : Fin 9 → ℚ :=
  ![-350406033248 / 61900784925, -2954024417 / 2526562650, -1403647619 / 853803930, -3720422 / 2651565, 10764 / 126265, -6912 / 126265, -63696 / 883855, 58638 / 883855, -117048 / 126265]

private def secondDirection1 : Fin 9 → ℚ :=
  ![-196878599337488174527844436479 / 15589449649600667190348031250, 78004810492532378587434952892 / 23384174474401000785522046875, -2383452333400692911265989 / 444883224245441156442750, 1075262539399373714261263 / 1334649672736323469328250, -4503772818614854416 / 65791662857947523875, -408785933946532734 / 2860507080780327125, 7504810679687685284 / 460541640005632667125, 68084512779911369688 / 460541640005632667125, -148709210104663044538 / 65791662857947523875]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Each differentiated entry is reduced once before matrix operations.
private lemma evalDerivative1 : tangentJacobian source1 = derivative1 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The inverse identity is checked one rational entry at a time.
private lemma hasInverse1 : tangentJacobian source1 * inverse1 = 1 := by
  rw [evalDerivative1]
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The closed rational identities are checked through cubic order.
private lemma jetCoefficients1 :
    (∀ j, rawJacobian source1 9 j = 0) ∧
    (∀ j : Fin 9, (tangentJacobian source1 *ᵥ firstDirection1) j = if j = 4 then 1 else 0) ∧
    (∀ j : Fin 9, quadraticCoefficient source1 firstDirection1 secondDirection1 j.castSucc = 0) ∧
    cubicCoefficient source1 firstDirection1 secondDirection1 9 = 2415367969811712 / 408643868682903875 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> decide +kernel
  · intro j
    rw [evalDerivative1]
    fin_cases j <;> decide +kernel
  · intro j
    fin_cases j <;> decide +kernel
  · decide +kernel

private def source2 : Fin 9 → ℚ :=
  ![7 / 6, -7 / 6, 0, 1 / 2, 0, 0, 0, 0, 1]

private def derivative2 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![2695 / 108, -1955 / 54, -105 / 4, 1883 / 36, -7 / 3, -10 / 3, 161 / 12, 4, 33373 / 1296;
    23 / 12, -7 / 6, 7 / 4, 56 / 9, 25 / 12, -7 / 12, 40825 / 1296, -161 / 18, 161 / 72;
    7 / 6, 23 / 12, 49 / 18, -9 / 4, -7 / 12, -25 / 12, 161 / 18, -30457 / 1296, 0;
    0, 0, 0, 0, -623 / 216, 1955 / 216, 161 / 36, 0, 0;
    0, 0, 0, 0, 1955 / 216, 623 / 216, 0, -161 / 36, 0;
    0, 0, 0, 1, -14 / 3, -20 / 3, 161 / 36, -2, 9 / 4;
    0, 0, 0, 1, 0, -1, 161 / 36, -2, 5 / 4;
    0, 0, 0, 0, 17 / 12, 7 / 12, 7 / 2, 0, 0;
    0, 0, 0, 0, 7 / 12, -17 / 12, 0, -7 / 2, 0]

private def inverse2 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![1209 / 33350, -233 / 870, 12 / 23, -12396867 / 15130895, -58561225 / 63549759, -5456131 / 3601800, 885677 / 360180, 1434171 / 1842022, -58268153 / 27235611;
    294 / 16675, -238 / 435, 12 / 23, -148916203 / 105916265, -143768980 / 63549759, -6844571 / 1800900, 2685749 / 360180, 5373448 / 8289099, -489322019 / 381298554;
    -9 / 322, 1 / 2, -36 / 161, 10458559 / 15339597, 1264237 / 786646, 26569 / 11592, -25759 / 5796, -11660477 / 6002451, -2983075 / 4719876;
    0, 0, 0, -1811 / 4886, -62288 / 95277, -5 / 4, 9 / 4, -23575 / 29316, 226316 / 857493;
    0, 0, 0, -18 / 349, 414 / 4537, 0, 0, 23 / 349, -529 / 4537;
    0, 0, 0, 414 / 4537, 18 / 349, 0, 0, -529 / 4537, -23 / 349;
    0, 0, 0, 180 / 31759, -1446 / 31759, 0, 0, 8844 / 31759, 5543 / 95277;
    0, 0, 0, -1446 / 31759, -180 / 31759, 0, 0, 5543 / 95277, -8844 / 31759;
    0, 0, 0, 1254 / 4537, 3258 / 4537, 1, -1, -4807 / 13611, -4163 / 4537]

private def firstDirection2 : Fin 9 → ℚ :=
  ![-58561225 / 63549759, -143768980 / 63549759, 1264237 / 786646, -62288 / 95277, 414 / 4537, 18 / 349, -1446 / 31759, -180 / 31759, 3258 / 4537]

private def secondDirection2 : Fin 9 → ℚ :=
  ![-21042295338856523415797 / 123985637186698371329700, 220544603020618159316321 / 123985637186698371329700, -124051870474164163493 / 61919105372667438714, -98747433525399180883 / 61919105372667438714, 173725546522371 / 3052307274606499, -21396503780151 / 132709011939413, -1419413158360759 / 21366150922245493, 1218138932790041 / 21366150922245493, -1565341344140065 / 3052307274606499]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Each differentiated entry is reduced once before matrix operations.
private lemma evalDerivative2 : tangentJacobian source2 = derivative2 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The inverse identity is checked one rational entry at a time.
private lemma hasInverse2 : tangentJacobian source2 * inverse2 = 1 := by
  rw [evalDerivative2]
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The closed rational identities are checked through cubic order.
private lemma jetCoefficients2 :
    (∀ j, rawJacobian source2 9 j = 0) ∧
    (∀ j : Fin 9, (tangentJacobian source2 *ᵥ firstDirection2) j = if j = 4 then 1 else 0) ∧
    (∀ j : Fin 9, quadraticCoefficient source2 firstDirection2 secondDirection2 j.castSucc = 0) ∧
    cubicCoefficient source2 firstDirection2 secondDirection2 9 = 3801462887520 / 1725217155212369 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> decide +kernel
  · intro j
    rw [evalDerivative2]
    fin_cases j <;> decide +kernel
  · intro j
    fin_cases j <;> decide +kernel
  · decide +kernel

private def source3 : Fin 9 → ℚ :=
  ![-7 / 6, 8 / 3, 0, 1 / 2, 0, 0, 0, 0, 1]

private def derivative3 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![-2695 / 108, 1955 / 54, 875 / 18, -2027 / 36, 7 / 3, 13 / 3, 161 / 12, 4, 33373 / 1296;
    -23 / 12, 7 / 6, 15 / 2, 49 / 18, 1 / 6, 7 / 12, 40825 / 1296, -161 / 18, 161 / 72;
    -7 / 6, -23 / 12, 56 / 9, 7 / 2, 7 / 12, -1 / 6, 161 / 18, -30457 / 1296, 0;
    0, 0, 0, 0, 259 / 27, -1955 / 216, 161 / 36, 0, 0;
    0, 0, 0, 0, -1955 / 216, -259 / 27, 0, -161 / 36, 0;
    0, 0, 0, 1, 14 / 3, 26 / 3, 161 / 36, -2, 9 / 4;
    0, 0, 0, 1, 0, -1, 161 / 36, -2, 5 / 4;
    0, 0, 0, 0, 10 / 3, -7 / 12, 7 / 2, 0, 0;
    0, 0, 0, 0, -7 / 12, -10 / 3, 0, -7 / 2, 0]

private def inverse3 : Matrix (Fin 9) (Fin 9) ℚ :=
  !![-14019 / 116725, 769 / 435, -192 / 161, 176278973119 / 41267189950, 350406033248 / 61900784925, 105777821 / 12606300, -19907617 / 1260630, -271422428449 / 32296061700, 21556781272 / 61900784925;
    -294 / 16675, 238 / 435, -12 / 23, 54658756 / 421093775, -2954024417 / 2526562650, 22799 / 450225, -127267 / 180090, -469761938 / 164775825, 59935679447 / 15159375900;
    -9 / 322, 1 / 2, -36 / 161, 598024699 / 426901965, 1403647619 / 853803930, 26569 / 11592, -25759 / 5796, -477992987 / 167048595, -10437272407 / 15368470740;
    0, 0, 0, -1883573 / 5303130, -3720422 / 2651565, -5 / 4, 9 / 4, -78649811 / 95456340, 29148233 / 23864085;
    0, 0, 0, 6912 / 126265, -10764 / 126265, 0, 0, -8832 / 126265, 13754 / 126265;
    0, 0, 0, -10764 / 126265, -6912 / 126265, 0, 0, 13754 / 126265, 8832 / 126265;
    0, 0, 0, -58638 / 883855, 63696 / 883855, 0, 0, 982369 / 2651565, -244168 / 2651565;
    0, 0, 0, 63696 / 883855, 58638 / 883855, 0, 0, -244168 / 2651565, -982369 / 2651565;
    0, 0, 0, 71796 / 126265, 117048 / 126265, 1, -1, -275218 / 378795, -448684 / 378795]

private def firstDirection3 : Fin 9 → ℚ :=
  ![350406033248 / 61900784925, -2954024417 / 2526562650, 1403647619 / 853803930, -3720422 / 2651565, -10764 / 126265, -6912 / 126265, 63696 / 883855, 58638 / 883855, 117048 / 126265]

private def secondDirection3 : Fin 9 → ℚ :=
  ![-196878599337488174527844436479 / 15589449649600667190348031250, -78004810492532378587434952892 / 23384174474401000785522046875, -2383452333400692911265989 / 444883224245441156442750, -1075262539399373714261263 / 1334649672736323469328250, -4503772818614854416 / 65791662857947523875, 408785933946532734 / 2860507080780327125, 7504810679687685284 / 460541640005632667125, -68084512779911369688 / 460541640005632667125, -148709210104663044538 / 65791662857947523875]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Each differentiated entry is reduced once before matrix operations.
private lemma evalDerivative3 : tangentJacobian source3 = derivative3 := by
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The inverse identity is checked one rational entry at a time.
private lemma hasInverse3 : tangentJacobian source3 * inverse3 = 1 := by
  rw [evalDerivative3]
  ext j k
  fin_cases j <;> fin_cases k <;> decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The closed rational identities are checked through cubic order.
private lemma jetCoefficients3 :
    (∀ j, rawJacobian source3 9 j = 0) ∧
    (∀ j : Fin 9, (tangentJacobian source3 *ᵥ firstDirection3) j = if j = 4 then 1 else 0) ∧
    (∀ j : Fin 9, quadraticCoefficient source3 firstDirection3 secondDirection3 j.castSucc = 0) ∧
    cubicCoefficient source3 firstDirection3 secondDirection3 9 = -2415367969811712 / 408643868682903875 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> decide +kernel
  · intro j
    rw [evalDerivative3]
    fin_cases j <;> decide +kernel
  · intro j
    fin_cases j <;> decide +kernel
  · decide +kernel

/-- The four source points in trace-chart coordinates with raw gain one. -/
def source : Fin 4 → Fin 9 → ℚ := ![source0, source1, source2, source3]

/-- First-order source directions for the prescribed common tangential line. -/
def firstDirection : Fin 4 → Fin 9 → ℚ := ![firstDirection0, firstDirection1, firstDirection2, firstDirection3]

/-- The quadratic source corrections that cancel tangential curvature on the line. -/
def secondDirection : Fin 4 → Fin 9 → ℚ := ![secondDirection0, secondDirection1, secondDirection2, secondDirection3]

/-- The predicted cubic normal coefficients in the four tangential charts. -/
def normalCubics : Fin 4 → ℚ := ![-3801462887520 / 1725217155212369, 2415367969811712 / 408643868682903875, 3801462887520 / 1725217155212369, -2415367969811712 / 408643868682903875]

theorem tangent_nonsingular (i : Fin 4) : (tangentJacobian (source i)).det ≠ 0 := by
  have h : ∃ A, tangentJacobian (source i) * A = 1 := by
    fin_cases i
    · exact ⟨inverse0, hasInverse0⟩
    · exact ⟨inverse1, hasInverse1⟩
    · exact ⟨inverse2, hasInverse2⟩
    · exact ⟨inverse3, hasInverse3⟩
  obtain ⟨A, hA⟩ := h
  have hd := congrArg Matrix.det hA
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact left_ne_zero_of_mul_eq_one hd

/-- For each lift the normal differential vanishes and the corrected path
has zero tangential quadratic coefficient and the stated normal cubic. -/
theorem exact_jet_coefficients (i : Fin 4) :
    (∀ j, rawJacobian (source i) 9 j = 0) ∧
    (∀ j : Fin 9, (tangentJacobian (source i) *ᵥ firstDirection i) j = if j = 4 then 1 else 0) ∧
    (∀ j : Fin 9, quadraticCoefficient (source i) (firstDirection i) (secondDirection i) j.castSucc = 0) ∧
    cubicCoefficient (source i) (firstDirection i) (secondDirection i) 9 = normalCubics i := by
  fin_cases i
  · exact jetCoefficients0
  · exact jetCoefficients1
  · exact jetCoefficients2
  · exact jetCoefficients3

theorem normalCubics_injective : Function.Injective normalCubics := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | norm_num [normalCubics] at h

end D5.S3.Quantum.TensorNetworks.PeriodicMPSFiveSiteSpecialJets
