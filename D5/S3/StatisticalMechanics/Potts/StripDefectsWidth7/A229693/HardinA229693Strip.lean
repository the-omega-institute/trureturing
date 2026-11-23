/- GID: D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.result; premises=D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693Strip.polynomial_relation
   digest: The integer recurrence for canonical two-defect width-seven arrays. -/

/-
admission_basis: open-problem-resolution (#33283; Proved)
escape_witness: polynomial_relation computes the order-twelve vector relation at shift two
a: proof_shape=bind-only; consumers=result, scale_count
leading: proof_shape=bind-only; consumers=forward_step, leadingCoordinates, leading_rec, leading_step, w, w_leading
coefficients: proof_shape=content; consumers=polynomialCoordinates, polynomial_relation, result
sum_zip_mul: proof_shape=bind-only; consumers=exhausted_step, polynomial_relation
columnRank: proof_shape=bind-only; consumers=rightColumn, representative_data, w, exhausted_step
columnRepresentative: proof_shape=bind-only; consumers=representative_data, exhaustedRank, checkColumn, exhausted_step
representative_data: proof_shape=bind-only; consumers=w_representative, exhausted_step
w_representative: proof_shape=bind-only; consumers=exhausted_step
exhaustedRank: proof_shape=bind-only; consumers=exhaustedRow
exhaustedRow: proof_shape=content; consumers=w, w_leading
rightColumn: proof_shape=bind-only; consumers=checkColumn, exhausted_step, rightColumn_eq
rightColumn_eq: proof_shape=bind-only; consumers=exhausted_step._simp_4
arithmeticRow: proof_shape=bind-only; consumers=checkColumn, exhausted_step
w: proof_shape=content; consumers=arithmeticRow, checkColumn, exhausted_step, forward_step, forward_table, polynomialCoordinates, polynomial_relation, w_leading
w_leading: proof_shape=bind-only; consumers=forward_step
leadingCoefficient: proof_shape=bind-only; consumers=leadingCoordinates, leading_rec, leading_step
leadingIndex: proof_shape=bind-only; consumers=leadingCoordinates, leading_rec, leading_step
leadingCoordinates: proof_shape=bind-only; consumers=leading_rec
leading_rec: proof_shape=bind-only; consumers=leading_step
leading_step: proof_shape=bind-only; consumers=forward_step
checkColumn: proof_shape=content; consumers=exhausted_step, stepGroup
stepGroup: proof_shape=content; consumers=exhaustedSteps
exhaustedSteps: proof_shape=content; consumers=exhausted_step
exhausted_step: proof_shape=content; consumers=forward_step
leading_action: proof_shape=bind-only; consumers=forward_step
forward_step: proof_shape=content; consumers=forward_table
forward_table: proof_shape=content; consumers=polynomial_relation
polynomialCoordinates: proof_shape=content; consumers=polynomial_relation
polynomial_relation: proof_shape=content; consumers=result
scale_count: proof_shape=bind-only; consumers=result
result: proof_shape=content; consumers=Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip.Recurrence.family._proof_2
-/

import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693StripTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585Strip
import D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.HardinA229585StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import Mathlib.Data.Matrix.Block
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Eval

open scoped BigOperators
namespace D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
set_option Elab.async false

open D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
  (defects literalCount constant_defects relabel_defects forward forward_eq forward_shift)
open HardinA229585StripData (horizontal antidiagonal)
open HardinA229693StripTransfer (T initial terminal count_transfer exitRead)
open D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (canonical_pattern_card)

/-- Canonical arrays with exactly two monochromatic bonds. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun f : Fin n × Fin 7 → Fin 3 =>
    defects horizontal antidiagonal (List.ofFn fun i j => f (i, j)) = 2 ∧
      HardinA229585Strip.Normal f).card

private def leadingCoefficient : Fin 8 → ℤ := by
  exact (fun (c : Fin 8 → ℤ)
    (_ : HardinA229585StripData.W 10 = ∑ k : Fin 8,
      c k • HardinA229585StripData.W ⟨2 + k.val, by omega⟩) => c) _
    HardinA229585Strip.finite_certificate.2.2.2.2.2.2

-- Extend the signed vector recurrence beyond the frozen eleven rows.
private def leading : Fin 15 → Fin 72 → ℤ :=
  let values : Array (Array ℤ) := eval% (
    let seed := Array.ofFn fun i : Fin 11 => Array.ofFn (HardinA229585StripData.W i)
    (List.range 4).foldl (fun rows i =>
      rows.push (Array.ofFn fun j : Fin 72 =>
        (List.ofFn fun k : Fin 8 =>
          let row := rows[3 + i + k.val]!
          leadingCoefficient k * row[j.val]!).sum)) seed)
  Fin.append HardinA229585StripData.W
    (fun (i : Fin 4) (j : Fin 72) => values[i.val + 11]![j.val]!)

private def coefficients : Fin 12 → ℤ := ![-531441000, 1913187600, -2986698420, 2659094568, -1494608922, 554666940, -138045627, 22918302, -2474469, 165456, -6345, 126]

private theorem sum_zip_mul {n : ℕ} (u v : Fin n → ℤ) :
    (List.zipWith (· * ·) (List.ofFn u) (List.ofFn v)).sum = dotProduct u v := by
  rw [dotProduct, ← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intros
    simp

private def columnRank (j : Fin 96) : Fin 60 :=
  (#[
    0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 7, 7, 8,
    8, 9, 9, 10, 11, 12, 12, 13, 14, 13, 15, 15, 16, 16, 17, 17,
    18, 18, 19, 19, 20, 20, 21, 22, 21, 23, 23, 24, 25, 26, 26, 27,
    27, 28, 28, 29, 30, 30, 31, 31, 32, 32, 33, 33, 34, 34, 35, 36,
    37, 37, 38, 38, 39, 40, 41, 41, 42, 42, 43, 44, 45, 46, 47, 47,
    48, 49, 50, 50, 51, 51, 52, 53, 54, 54, 55, 56, 57, 58, 59, 59] : Array (Fin 60))[j.val]!

private def columnRepresentative (k : Fin 60) : Fin 96 :=
  (eval% (List.ofFn fun k : Fin 60 => Fin.ofNat 96
    ((List.ofFn columnRank).idxOf k)) : List (Fin 96))[k.val]!

-- Five bits per entry of the representative columns.
private def rightColumn (j : Fin 96) : List ℤ :=
  let columns : Array ℕ := #[
    151370913166682838952567340362139539947581226483115580048576493034792165880299365998514323989344664028351620,
    4587137357135172828055934322618308352225822109965444653259362284123045171119100951787746740074553454694532,
    146931878934900449851055696921056771704943683171663110388069269860335175290579512851874020807531079241207940,
    151514256830048853549233193445157760680764689459635056418783879644858250681922952637347406234697783309407333,
    151371048784842712178187509982464122446316583349940232561857829035588264231715423359680262080862469158405284,
    4587001747661224816513841423318225619711669109550384118763588344731254143113641403612717643486922675421348,
    147972022807309662790639014570034861665408644442905746611911389056931761752967499708440951691971094811682,
    458222688021560056309427504912405997673795808182449817459374709928248245095652611039870584553736843136543544818182142752390168915281711866380485190664893906782956578354801668597372882015618491507326881904941829071842764276075797816038231055316752109731,
    143626026039882977337637203456089430924104525999826440012064415335952028151716361395596781311708156334211,
    472555898494653832947502550934760305447890777251750430727988195422583823634308286053020732540089198195550621161996072736130737789336926257150077646964673777283145274942588513897652446226600051030236426209677595866481406957141142085325900307034283316322,
    4626242542693833154453066374409765264972986292589617474433183394998340288043752849440743980787451367556,
    146931739091896024798937987893430860632735557679145599858514289578488728226554524042963415330925092991570946,
    448145621017301313438196069343358174209261386689432249838687634560581808641312113364438517589262092478774060129813113863901107642118467602057249661364153471986182944394714654016113091192241152124625569924879359921616787038773654076634557301823476870,
    13984279906542298639383029536922540356897256989191979833332201630468885469483303523405240908665029909621196040290047139551398040746300209467704724454977568444324088871900700586779840192875462524890940076919508395300633269963725222927539805693938852,
    151514394565107332336525024224636916755097174405222224442581373160125033795722585019853581545433529392894083,
    4591618963384903438171321718992118293231663394742593679662094122797912509378547733058820879710567660720259,
    300593902105079063568060603419953237893299405891078310814221347750076232250432653268225600608197535774837828,
    153809990681781173148385460454139841976080251678892351833010053286356264016535019199350054866631647182358690,
    149227475192682938293534500707215011187368323394641355419151032911500798995772039566944135220661909891126339,
    227273690402284395671005227527666859298770235210102096944210895119807566604622236727789199305375029480458401,
    4591621084351125330628736677502673091789148692824295375393580539213633538655189906266076581467693952110724,
    230733797479135983656076742140475839854913068317503395475265713256067934270270269372417792994394702018657628509259104829792235462383556846602388141641773632827778042813823695225049030323536010677488501179260977310066188031536345872529819543881782378,
    149223133574956059921792027372506910819305664369892346633680791720476712664724075390189309879037016627384450,
    231395690645186749642792315837581115322943311532527327351461037454268494999402230824998864646125333835761493113756832081763711730185715034996688600513971855000198565999492246202922486332224604915448823646025878568950849422888144995696847900919468259,
    149222997961072462733113648677966475449154829399467408168815351254440371291931860742919688949638452881721445,
    2295884974886764502603526894836292469460161971500147595973232704602298993355768549080099475127728993276036,
    472772648232271519571531016041896140493299928137130321499999675013289172062721025656923536832346183974697476144848918853267443623912184846606474317408648652952630879643048524961307605341305436975805815250504470294258654920215208715028488408780760026274,
    73463837724562576802551193049523523992125951800498205271793362149815967278367845600598280497141788272855110,
    236270970990193026373160037487162708503007299574087685862080271418921565088740262675046723630737922278702603941451569071594672911024619820111348237038411904031754369721935170674478738088306246014077385867760872915484117733891440461151081323714222070853,
    75759442594645050748650931679774804156063437910221324400640074053301773894419963492634394233331341453231331,
    2295740620677585137054257615114487571696076329464636620137134388428586703099623244337637262991414828141635,
    75759435971151391509738545478686891641981594648700854022880516028061880225219016658703506646251589388606500,
    75710049364522427287553,
    77995139786653197960225,
    75558007981842037211137,
    77919123603379463389217,
    2361259877465139970080,
    76164947267908830208,
    73861358291925337088,
    75634028673182232249345,
    77921427192355446882337,
    2434972471762891047968,
    75560169571259999453185,
    2436123210775537979424,
    77993986936689861398561,
    41431424379435167517794,
    38998760004714720430146,
    1225050636694913024,
    38048770409824847872,
    36967834961207887872,
    38959632695965607002178,
    1180701958908318580800,
    38960713631414223962178,
    37816979507467113269250,
    1217521175081754036288,
    75559088776551018332161,
    3652493642377879096416,
    39035653528045437879362,
    1254414698412471485504,
    37781238834099732381698]
  let packed := columns[(columnRank j).val]!
  List.ofFn fun k : Fin 168 => (((packed >>> (5 * k.val)) % 32 : ℕ) : ℤ)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 6000000 in
private theorem rightColumn_eq (j : Fin 96) :
    List.ofFn (fun k : Fin 168 => T k (j.natAdd 72)) = rightColumn j := by
  fin_cases j <;> decide +kernel

set_option maxRecDepth 10000 in
private theorem representative_data (j : Fin 96) :
    columnRank (columnRepresentative (columnRank j)) = columnRank j ∧
    exitRead (columnRepresentative (columnRank j)) = exitRead j ∧
    initial ((columnRepresentative (columnRank j)).natAdd 72) = initial (j.natAdd 72) := by
  fin_cases j <;> decide +kernel

private def exhaustedRank (k : Fin 60) : ℕ :=
  let packed : ℕ := eval% (
    let novel := (List.finRange 60).filter fun k => 72 ≤ (exitRead (columnRepresentative k)).val
    Nat.ofDigits 64 (List.ofFn fun k : Fin 60 => novel.idxOf k))
  (packed >>> (6 * k.val)) % 64

-- Rows after the initial vector, restricted to exhausted coordinates with their own column.
private def exhaustedRow (i : Fin 14) (j : Fin 60) : ℤ :=
  let values : Array (Array ℤ) := #[
    #[1380, 1302, 1398, 1374,
      1374, 1308, 3582, 1452,
      3660, 3690, 3786, 1446,
      1350, 1494, 1302, 1308,
      1422, 3948, 4002, 3840,
      1350, 3732, 1278, 1494,
      180, 144, 180, 144,
      180, 144, 180, 144,
      180, 144, 180, 144],
    #[68718, 63492, 56460, 64122,
      64374, 66684, 359250, 72912,
      348780, 348576, 338142, 68082,
      63120, 58506, 62130, 67092,
      58620, 329358, 339594, 337686,
      64980, 348978, 60330, 59730,
      5724, 4752, 4932, 4068,
      4788, 4212, 5292, 3852,
      6120, 4680, 5292, 4392],
    #[2831886, 2557908, 2233620, 2640906,
      2676546, 2863368, 23028066, 3147084,
      21670380, 21823776, 19943118, 2879694,
      2539152, 2247030, 2637126, 2806776,
      2281320, 17755164, 19518858, 20332440,
      2750940, 21368394, 2602170, 2323926,
      184140, 152496, 150660, 127116,
      146340, 131436, 166860, 118476,
      196560, 148176, 166860, 139536],
    #[110901906, 98736948, 85346244, 103322034,
      105025302, 114432696, 1218239838, 126311616,
      1120258404, 1143238212, 1002331314, 114334902,
      98108820, 84361662, 105248430, 110894724,
      86139720, 835005348, 964099098, 1038120300,
      109401192, 1095931782, 104872914, 87767442,
      5886756, 4870368, 4765068, 4041252,
      4630932, 4175388, 5319108, 3757428,
      6282360, 4720680, 5319108, 4452408],
    #[4199557914, 3702130920, 3176028792, 3908472426,
      3976442442, 4385925792, 57941320626, 4855687236,
      52373492892, 54091076508, 46024489494, 4364180694,
      3679610652, 3100495158, 4033781046, 4221221040,
      3177412596, 36492811740, 43771224366, 48245918544,
      4182205608, 51007321458, 4045847778, 3237915870,
      188028540, 155531664, 151899300, 128952324,
      147641940, 133209684, 169832700, 119854404,
      200669400, 150691104, 169832700, 142176384],
    #[155161854450, 135798338700, 115836639084, 144286871562,
      146858372406, 163413806400, 2573858147958, 181303880472,
      2295999883332, 2395205611164, 1992290232186, 162129032838,
      134984798028, 112020203070, 150309716958, 156524757372,
      115110338328, 1520275547520, 1879901465994, 2108252882160,
      155551321728, 2229835036734, 151466331834, 117314110674,
      6005294964, 4967207712, 4849678332, 4117779828,
      4713868548, 4253589612, 5423867892, 3827066292,
      6409105560, 4812303960, 5423867892, 4540684392],
    #[5627653189146, 4898192996232, 4159650456216, 5229832016322,
      5324553138330, 5964332360688, 108993164030946, 6627897586044,
      96216542391564, 101214300469860, 82703638963638, 5904461012238,
      4869090286884, 3992939661294, 5486613095502, 5692430074824,
      4111813496628, 61197455276820, 77586545562390, 88182200758608,
      5670010496304, 93265570014786, 5548198044474, 4190859428814,
      191797144380, 158641585776, 154879447140, 131509620036,
      150542888580, 135846178596, 173226190140, 122224142916,
      204694714440, 153692667216, 173226190140, 145019550096],
    #[201202806733434, 174359352163572, 147545108464788, 186883896677922,
      190310062976406, 214289305884144, 4454400117236598, 238426577987040,
      3899108125368468, 4130337726082476, 3326928831733338, 211775495112702,
      173329547873724, 140789323375398, 197141786947494, 203949163506852,
      145230154066944, 2400241083036048, 3107161190914650, 3569359795953048,
      203509760083632, 3774328661986542, 199895852016738, 148031305215570,
      6125617000116, 5066688475008, 4946486099868, 4200131566692,
      4807990370772, 4338627295788, 5532491262708, 3903568697988,
      6537543900120, 4908621335400, 5532491262708, 4631629877208],
    #[7111631776682034, 6141055174938576, 5181603562377216, 6602785492162410,
      6725009156352858, 7604108667837072, 177114037081642002, 8469039838061556,
      153955078595737020, 164048348112179796, 130588998960532518, 7504607147065830,
      6104957036904180, 4920122896825014, 6996087920680470, 7220976505648992,
      5082528053463948, 92233371087877500, 121529663889368886, 140830084962208800,
      7215776145984384, 148874229655066242, 7109187903909234, 5180824225054062,
      195639959915100, 161819864591184, 157980579154020, 134143679778804,
      153557331938100, 138566926994724, 176696675398620, 124672037520564,
      208796107426920, 156771469548864, 176696675398620, 147924975117024],
    #[249028575131368242, 214413311595375036, 180478839214433340, 231131290257467514,
      235443594006825462, 267137262688177872, 6889830233804901414, 297764716710931848,
      5953895366091922116, 6376200948326213388, 5025805857576252234, 263345677097813478,
      213157918831635324, 170667648816513534, 245790431261532414, 253211655381045804,
      176511623863441464, 3485937596981083128, 4663603113427616490, 5443660317502139256,
      253327673006594928, 5752780847372017710, 250205561179357770, 179933112077347026,
      6248349284810004, 5168202841229472, 5045582286586332, 4284280319815188,
      4904312775435108, 4425549830966412, 5643338457355092, 3981774906087732,
      6668530489920600, 5006966938653240, 5643338457355092, 4724427916350792],
    #[8652830351266803546, 7431768700419259656, 6242845178013132312, 8028664700506486578,
      8179444644293543994, 9307196397777734928, 263269220623816015170, 10381294814421848364,
      226372210329806578476, 243481483454911718004, 190310555601128294838, 9166500161819165502,
      7388400472323365556, 5882865264388399518, 8563849238990440638, 8808492993123417912,
      6090495875325746676, 129952418190890268420, 176169430982621488806, 206905929897046750992,
      8821208218212289728, 218585513213931105378, 8730504042701293098, 6208781214612669102,
      199559788068985020, 165062068373361456, 161145804890453220, 136831346920473156,
      156633939958642020, 141343211852284356, 180236950437337020, 127169928104649156,
      212979536822036520, 159912514489348656, 180236950437337020, 150888784625726256],
    #[298690122775220251722, 256002398043554895876, 214673095830392580132, 277076788838717046930,
      282309302665154274390, 322016895781252060752, 9911259978836295771126, 359384905273051977264,
      8485600822002368133876, 9161425800869604574284, 7109225209756337678298, 316897335930915138222,
      254512753777713305628, 201686784845927316534, 296309386199805171318, 304366336432979374260,
      208988333441419797648, 4788687090147326124912, 6567552673847723539386, 7754247938835738344808,
      305060191610725698192, 8189434854851496321870, 302451037728195837042, 213053887018079507538,
      6373540791196442676, 5271752565127510848, 5146674892004047068, 4370119728580718532,
      5002574948528749812, 4514219672056015788, 5756407970401182708, 4061553318183088548,
      6802140750423272280, 5107286098205178120, 5756407970401182708, 4819086211254583608],
    #[10252933247636780430114, 8771738784098364999072, 7344532867927421206800, 9509031256196258171514,
      9689462354390937393114, 11075477370294450927312, 368461572595190590214898, 12366777466142391317796,
      314281488124999689646428, 340436598212032736561460, 262522764733254505543494, 10891975565665556049366,
      8720823408171527183508, 6882211679731177557510, 10191625231806262217574, 10456725589763375258064,
      7136814732214621621500, 174719434451153360633100, 242096507700458948570934, 287154165410942918129856,
      10488076295989061820960, 303180882913672776927234, 10413935493650142634530, 7275850746332516690094,
      203558154755340943260, 168369240807661772304, 164374509661068055140, 139572889921543632084,
      159772245491577207060, 144175154091034480164, 183848165826820646940, 129717895457283483924,
      217246780882429635240, 163116510512892472224, 183848165826820646940, 153911982173910776064],
    #[350241734731328265333474, 299171966172566206433292, 250165130390782457573196, 324770626271610842147946,
      330958491427238097331638, 378988418653993573424784, 13551015423406402699193862, 423354794737866152419224,
      11520447842324619589728996, 12515760724824872783653068, 9598281740308168560537066, 372489191866882427252598,
      297439186122410464378620, 233880404733774585685998, 348754060525438519907310, 357469232995976715247356,
      242695588078659981260520, 6320247971778669765211272, 8838048342882855587054922, 10525118378068958256317880,
      358764033565693265991408, 11109479883159529076458158, 356689646183326388766426, 247429642161654015030738,
      6501240633096725573844, 5377377049719549592032, 5249793319372823395932, 4457679154120649948148,
      5102806200004349118468, 4604666273489124225612, 5871742978790285999892, 4142930326967430161172,
      6938427993757659921240, 5209615341934804082520, 5871742978790285999892, 4915641103197855527592]
  ]
  let row := values[i.val]!
  row[exhaustedRank j]!

private def w (i : Fin 15) (j : Fin 168) : ℤ :=
  if h : i.val = 0 then initial j
  else Fin.addCases (leading i) (fun k =>
    if hk : (exitRead k).val < 72 then leading i ⟨(exitRead k).val, hk⟩
    else exhaustedRow (Fin.subNat 1 i (Nat.pos_of_ne_zero h)) (columnRank k)) j

private def arithmeticRow (i : Fin 15) : List ℤ :=
  List.ofFn (w i)

private theorem w_leading (i : Fin 15) (j : Fin 72) : w i (j.castAdd 96) = leading i j := by
  induction i using Fin.cases with
  | zero =>
    simp only [w, Fin.val_zero, dite_true, initial, Fin.append_left, leading]
    exact congrFun HardinA229585Strip.finite_certificate.2.2.2.2.2.1.1.symm j
  | succ i =>
    simp only [w, Fin.val_succ, Nat.succ_ne_zero, dite_false, Fin.addCases_left]

private def leadingIndex (i : Fin 5) (k : Fin 8) : Fin 15 :=
  ⟨2 + i.val + k.val, by omega⟩

-- Check the continuation rows beyond the last frozen forward vector.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem leadingCoordinates :
    (List.finRange 4).all (fun i => (List.finRange 72).all fun j =>
      leading (i.succ.natAdd 10) j ==
        (List.ofFn fun k : Fin 8 => leadingCoefficient k *
          leading (leadingIndex i.succ k) j).sum) = true := by
  decide +kernel

private theorem leading_rec (i : Fin 5) :
    leading (i.natAdd 10) = ∑ k : Fin 8, leadingCoefficient k • leading (leadingIndex i k) := by
  induction i using Fin.cases with
  | zero =>
    exact HardinA229585Strip.finite_certificate.2.2.2.2.2.2
  | succ i =>
    funext j
    have h := List.all_eq_true.mp
      (List.all_eq_true.mp leadingCoordinates i (List.mem_finRange i)) j (List.mem_finRange j)
    simpa only [beq_iff_eq, List.sum_ofFn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

private theorem leading_step (i : Fin 14) :
    leading i.succ = Matrix.vecMul (leading i.castSucc) HardinA229585StripData.T := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    by_cases h : i.val < 10
    · let k : Fin 10 := ⟨i.val, h⟩
      have hi : k.castAdd 4 = i := Fin.ext rfl
      rw [← hi]
      have hs : (k.castAdd 4).succ = k.succ.castAdd 4 := Fin.ext rfl
      have hc : (k.castAdd 4).castSucc = k.castSucc.castAdd 4 := Fin.ext rfl
      simp only [hs, hc, leading, Fin.append_left]
      exact HardinA229585Strip.finite_certificate.2.2.2.2.2.1.2 k
    · let k : Fin 4 := ⟨i.val - 10, by omega⟩
      have hp : i.castSucc = k.castSucc.natAdd 10 := Fin.ext (by dsimp [k]; omega)
      have hs : i.succ = k.succ.natAdd 10 := Fin.ext (by dsimp [k]; omega)
      rw [hp, hs, leading_rec, leading_rec, Matrix.sum_vecMul]
      simp only [Matrix.smul_vecMul]
      apply Finset.sum_congr rfl
      intro j _
      let x : Fin 14 := ⟨(leadingIndex k.castSucc j).val, by
        dsimp [leadingIndex]
        omega⟩
      have hx : x < i := by
        change x.val < i.val
        dsimp [x, leadingIndex, k]
        omega
      have hc : x.castSucc = leadingIndex k.castSucc j := Fin.ext rfl
      have hn : x.succ = leadingIndex k.succ j := Fin.ext (by
        simp [x, leadingIndex]
        omega)
      rw [← hc, ← hn, ih x hx]

private theorem w_representative (i : Fin 15) (j : Fin 96) :
    w i ((columnRepresentative (columnRank j)).natAdd 72) = w i (j.natAdd 72) := by
  rcases representative_data j with ⟨hrank, hexit, hstart⟩
  unfold w
  split
  · exact hstart
  · simp only [Fin.addCases_right, hexit, hrank]

private def checkColumn (k : Fin 60) : Bool :=
  let j := columnRepresentative k
  let column := rightColumn j
  (List.finRange 14).all fun i =>
    w i.succ (j.natAdd 72) ==
      (List.zipWith (· * ·) (arithmeticRow i.castSucc) column).sum

private def stepGroup (g : Fin 10) : Bool :=
  (((List.finRange 60).drop (6 * g.val)).take 6).all checkColumn

-- Check one destination from each class of equal right columns.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 6000000 in
private theorem exhaustedSteps (g : Fin 10) : stepGroup g = true := by
  fin_cases g <;> decide +kernel

private theorem exhausted_step (i : Fin 14) (j : Fin 96) :
    w i.succ (j.natAdd 72) = Matrix.vecMul (w i.castSucc) T (j.natAdd 72) := by
  let k := columnRank j
  let g : Fin 10 := ⟨k.val / 6, by omega⟩
  have hm : k ∈ ((List.finRange 60).drop (6 * g.val)).take 6 := by
    rw [List.mem_iff_getElem]
    refine ⟨k.val % 6, by simp [g]; omega, ?_⟩
    apply Fin.ext
    simp [List.getElem_take, List.getElem_drop, g]
    omega
  have h := List.all_eq_true.mp
    (List.all_eq_true.mp (exhaustedSteps g) k hm) i (List.mem_finRange i)
  change (w i.succ ((columnRepresentative k).natAdd 72) ==
    (List.zipWith (· * ·) (arithmeticRow i.castSucc) (rightColumn (columnRepresentative k))).sum)
      = true at h
  have hcol : rightColumn (columnRepresentative k) = rightColumn j := by
    unfold rightColumn
    rw [(representative_data j).1]
  rw [beq_iff_eq, w_representative, hcol] at h
  simpa only [arithmeticRow, ← rightColumn_eq, sum_zip_mul, Matrix.vecMul] using h

private theorem leading_action (v : Fin 168 → ℤ) (j : Fin 72) :
    Matrix.vecMul v T (j.castAdd 96) =
      Matrix.vecMul (fun k : Fin 72 => v (k.castAdd 96)) HardinA229585StripData.T j := by
  let e : Fin 72 ⊕ Fin 96 ≃ Fin 168 := finSumFinEquiv
  simp only [T, Matrix.reindex, Equiv.coe_fn_mk]
  rw [Matrix.submatrix_vecMul_equiv _ v e.symm e.symm, Matrix.vecMul_fromBlocks]
  have hj : e.symm (j.castAdd 96) = Sum.inl j :=
    finSumFinEquiv_symm_apply_castAdd (m := 72) (n := 96) j
  simp only [Function.comp_apply, Equiv.symm_symm, hj, Sum.elim_inl, Matrix.vecMul_zero,
    add_zero]
  rfl

private theorem forward_step (i : Fin 14) :
    w i.succ = Matrix.vecMul (w i.castSucc) T := by
  funext j
  induction j using Fin.addCases (m := 72) (n := 96) with
  | left j =>
    rw [leading_action]
    simpa only [w_leading] using congrFun (leading_step i) j
  | right j =>
    exact exhausted_step i j

private theorem forward_table (i : Fin 15) : forward T initial i.val = w i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    change (fun v => Matrix.vecMul v T)^[i.val + 1] initial = w i.succ
    rw [Function.iterate_succ_apply']
    change Matrix.vecMul (forward T initial i.castSucc.val) T = _
    rw [ih]
    exact (forward_step i).symm

-- The twelve scalar products are evaluated coordinate by coordinate.
set_option maxRecDepth 14000 in
set_option maxHeartbeats 3000000 in
private theorem polynomialCoordinates :
    (List.finRange 168).all (fun k =>
      w (Fin.last 14) k ==
        (List.zipWith (· * ·) (List.ofFn coefficients)
          (List.ofFn fun j : Fin 12 => w ((j.natAdd 2).castAdd 1) k)).sum) = true := by
  decide +kernel

private theorem polynomial_relation :
    forward T initial (2 + 12) =
      ∑ j : Fin 12, coefficients j • forward T initial (2 + j.val) := by
  change forward T initial (Fin.last 14).val = _
  rw [forward_table (Fin.last 14)]
  simp_rw [show ∀ j : Fin 12, forward T initial (2 + j.val) =
      w ((j.natAdd 2).castAdd 1) from fun j => forward_table ((j.natAdd 2).castAdd 1)]
  funext k
  have h := List.all_eq_true.mp polynomialCoordinates k (List.mem_finRange k)
  simpa only [beq_iff_eq, sum_zip_mul, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] using h

private theorem scale_count (m : ℕ) :
    literalCount (q := 3) horizontal antidiagonal 2 (m + 1) = 6 * a (m + 1) := by
  classical
  let s : (Fin (m + 1) × Fin 7 → Fin 3) → Prop := fun f =>
    defects horizontal antidiagonal (List.ofFn fun i j => f (i, j)) = 2
  have hinv (e : Equiv.Perm (Fin 3)) (f : Fin (m + 1) × Fin 7 → Fin 3) :
      s (e ∘ f) ↔ s f := by
    change defects horizontal antidiagonal _ = 2 ↔ _
    rw [show (List.ofFn fun i j => (e ∘ f) (i, j)) =
      (List.ofFn fun i j => f (i, j)).map (fun r => e ∘ r) by rw [List.map_ofFn]; rfl,
      relabel_defects]
  have huse (f : Fin (m + 1) × Fin 7 → Fin 3) (hf : s f) : ∃ i j, f i ≠ f j := by
    by_contra h
    push Not at h
    have he : f = fun _ => f (0, 0) := funext fun i => h i (0, 0)
    change defects horizontal antidiagonal _ = 2 at hf
    rw [he, List.ofFn_const, constant_defects] at hf
    have hc : horizontal.card = 6 ∧ antidiagonal.card = 6 := by decide +kernel
    rw [hc.1, hc.2] at hf
    omega
  have h := @canonical_pattern_card (Fin (m + 1) × Fin 7) inferInstance
    (HardinA229585Strip.cellOrder (m + 1)) s hinv huse
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, s] at h
  unfold literalCount a HardinA229585Strip.Normal
  convert h using 1
  apply congrArg (fun x : ℕ => 6 * x)
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

attribute [local irreducible] a T initial terminal

/-- Hardin's order-twelve recurrence from row count fifteen. -/
theorem result (t : ℕ) :
    (a (t + 15) : ℤ) = 126 * a (t + 14) - 6345 * a (t + 13) + 165456 * a (t + 12) - 2474469 * a (t + 11) +
      22918302 * a (t + 10) - 138045627 * a (t + 9) + 554666940 * a (t + 8) - 1494608922 * a (t + 7) +
      2659094568 * a (t + 6) - 2986698420 * a (t + 5) + 1913187600 * a (t + 4) - 531441000 * a (t + 3) := by
  have bridge (n : ℕ) :
      dotProduct initial ((T ^ n).mulVec terminal) = 6 * (a (n + 1) : ℤ) := by
    rw [← count_transfer, scale_count]
    push_cast
    rfl
  have h := forward_shift T initial terminal 12 2 coefficients polynomial_relation t
  simp_rw [bridge] at h
  norm_num only [coefficients, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    Fin.val_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Nat.add_assoc,
    Nat.add_zero, Nat.reduceAdd] at h
  linarith

end D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693.HardinA229693Strip
