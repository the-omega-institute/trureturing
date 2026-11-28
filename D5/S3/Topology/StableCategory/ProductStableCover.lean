/- GID: D5/S3/Topology/StableCategory/ProductStableCover
   generality: I
   mirror-B: D5/B/S3/Topology/StableCategory/ProductStableCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The seven-triangle face-poset product has a stable two-piece categorical cover. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Topology.StableCategory.ProductRigidCores
import D5.S3.Topology.StableCategory.OrdinarySubdivisionTransfer
import D5.S3.Topology.SubdivisionCategoricalCover

set_option autoImplicit false

/-! The two coordinate trajectories and the colour of each core vertex.
Each of the fourteen coordinate images uses six bits. The last bit is the colour. -/

namespace D5.S3.Topology.ProductStableCertificate

def faceMasks : Fin 22 → ℕ := ![  1, 2, 3, 4,
  5, 7, 8, 9,
  12, 13, 16, 24,
  28, 32, 33, 34,
  35, 40, 41, 48,
  50, 56]

def words : Fin 22 → Fin 22 → ℕ := ![
  ![  21803241009607782365925441, 2609144961313883440812097, 21803243352051334645026881, 2460432562360548596125761,
  21803241010751274458812481, 21803243353194826737913921, 2456230236677342769713217, 21803241011894766551699521,
  2461032227945150786834497, 21803250380525483575218241, 2532387765987823960985665, 2686501235753838130237505,
  21799043356228870029447233, 2532424952280351217293377, 21956754822937129997570113, 2685911087198873110059073,
  21956757165380682276671553, 2686501528558182517315649, 2686501528844056213723201, 2532425245084695885387841,
  21951960421734462328672321, 2686501821362527176890561],
  ![  2609144961028044232597634, 2609144961313883441340546, 21803243334036936136073346, 2456234775162308881031298,
  21803241010751274459340930, 21803243353194826738442370, 2456230236677376584458370, 21803241011894766552227970,
  2456234921564481142661250, 21803840676335842281398402, 2532387765987858729535618, 2532987431572426552125570,
  21875200883252367989678210, 2609144960882908697069698, 21951958075002814701772930, 2686501382727756839528578,
  21956757723827036071141506, 2609744626467476519659650, 21956755401684866487296130, 2685902155777958664603778,
  2686501675532101362788482, 2686501821362527577974914],
  ![  21803241009607782366458051, 2609144961313883441344707, 21803243352051334645559491, 2480216713675510481957059,
  21803241010751274459345091, 21803243353194826738446531, 2456230236677377675243715, 21803241011894766552232131,
  2480216860077682743587267, 21803840676335842281402563, 2532427587378714029463747, 21799043355085377937088707,
  21894690012481430206820547, 2685901862973615232129219, 2685911087194475064080579, 21951960417160493957656771,
  21956757741841434581692867, 2686501533061782682089667, 21956757707527875700994243, 2685904498212716077783235,
  21951960421734462329204931, 21952557744875477872156867],
  ![  2460427895773750462842628, 2613867913546179621429700, 21803241010179531684724996, 2460432562360583488341764,
  2460432580660855021045508, 21803248000909645456621828, 2456230236677342769713476, 21803241011894769824055556,
  21799048035398517395833092, 21803845360079458018803972, 2474819876624716780307204, 2475419539957485879464772,
  21818232653809143701061892, 2609145555639535565080324, 2613941709103098095011588, 21951960417160497229480196,
  21956757741841437852713220, 21951958077003929136152836, 21956755401684869759385860, 21951958079290913321926916,
  21951960421734465601028356, 21951958081577897507700996],
  ![  21803241009607782365925701, 2613868499014131179598277, 21803243352051339008168261, 21817632983650604234838341,
  21822430308331544857809221, 21822432650775101500051781, 2607351820216061881749829, 21803241011894770914840901,
  21818232649235176420036933, 21823029973916117043007813, 2552176730243382079968069, 21799043355085377936560453,
  21818232653809144791585093, 21951958074716941678022981, 21956755399397886664134981, 21951960417160498320265541,
  21956757741841438943236421, 21951958077003930226938181, 21956755401684870849909061, 21951958079290914412712261,
  21951960421734466691813701, 21952557744875482234769733],
  ![  21803241009607782366458311, 2613870840885937412256199, 21803243352051339008700871, 21817632983650604235370951,
  21822430308331544858341831, 21822432650775101500584391, 2682909683942011110699463, 21803241011894770915373511,
  21818232649235176420569543, 21823029973916117043540423, 21875200879821891711021511, 21875800545406459533078983,
  21894989844130226388103623, 21951958074716941678023111, 21956757705240895878361543, 21951960417160498320798151,
  21956757741841438943769031, 21951958077003930227462599, 21956757707527880064135623, 22028715269611996009230791,
  22028717612055548288332231, 22029314935196563831288263],
  ![  2460427895773749389100552, 2460427896341062616121864, 2611545965669130451387912, 2460432562360547641688584,
  2460432580660854083651080, 2611550650556235009590792, 2456230236677341815276040, 21803241011894765597262344,
  2461032246240988949938696, 2461032246245421905708552, 2474819876624712484291080, 21799043355085376982123016,
  21799043356228869075010056, 2456231270640519162693128, 2612180045044057758565896, 21951958075288686770029064,
  21956683954865138787451400, 21799043359659345353671176, 21957355064982449168613896, 21803278474978314715955720,
  21956755386243324231844360, 21803878140562882538013192],
  ![  21803241009607782365925961, 2613942285990426153620041, 21803243352051334781375049, 2461032081542944292901449,
  21803241010751274458813001, 21803243353194826874262089, 2614541347239422893398601, 21803840675192350324331081,
  21803765718137771439460937, 21803840676335842417218121, 2552176730243377716826697, 21803765721568247701340745,
  21803770406455352276324937, 21803278470404347418149449, 21956755399397882437341769, 21956757723541163183739465,
  21956757741841434716443209, 21803878135988915257250377, 21957355064982450259399241, 21803278474978315789963849,
  21956757728115131555287625, 21803878140562883628798537],
  ![  2460427895773750462842636, 21803243333751062157886220, 21803243352051338053731084, 2612147808994807831955212,
  2612147829546879178344204, 21803248036938442611933964, 21799043350511412905542412, 21803840675192353596687116,
  21803845341779186622448396, 21803845360079458155152140, 2474819876624716780307212, 21799043355085381345264396,
  21823029960189812927677196, 2609745074821931125507852, 2614541228848443608860428, 21956757723541166456095500,
  21956757741841437989061388, 21952558893223017515631372, 21957355064982453532017420, 21956755385671582548542220,
  21956757728115134827643660, 21957355051256150370599692],
  ![  21803241009607782366991181, 21803243333751063248671565, 21803243352051339144516429, 21822430290031273325105997,
  21822430308331544858874701, 21822432650775101636399949, 21803840656892081996071757, 21803840675192354687472461,
  21823029955615845646652237, 21823029973916117179355981, 2552176730243382079968077, 21803840661466051526316877,
  21823029960189814018200397, 21956755381097615199605581, 21956755399397886800483149, 21956757723541167546880845,
  21956757741841439079584589, 21957355046682183089836877, 21957355064982454622540621, 21956755385671583639327565,
  21956757728115135918429005, 21957355051256151461385037],
  ![  2460427895773749384973328, 2460430219917030131371024, 2460430238217301664074768, 2474819869816571253885968,
  2479617194497511876856848, 2479619536941065247263760, 2456230236677376584059920, 2461027561358317207030800,
  2475419535401139075943440, 2480216860082079698914320, 2474819876624729800508432, 2475419539957532714011664,
  21799047967914904682268176, 2609144960882908697070608, 2613942285563849320827920, 2613944609707130066439184,
  2613944628007402690448400, 2609744626467476519128080, 21957355064982466348484112, 21951958079290926411351056,
  21951960421734478690452496, 21951958081577910597125136],
  ![  2460432507459785401273880, 2460430238212903753911832, 2611550577355166327213592, 2479617176197240480501272,
  21803241010751273504376344, 21803247964880844215125528, 2456230236677376724602392, 21803250379381990527895064,
  2480216860077698972880408, 21803250380525486915749400, 2474819876624729936856600, 2552176730278614446345752,
  21799047967914904682268184, 2685303515008596814564888, 21956680441485700571891224, 21951958075288703949899288,
  21956757741841450805528088, 2685303661410770149936664, 21957355064982466348484120, 21956755385671595637966360,
  21956757728115147917067800, 21957355051256163460023832],
  ![  21954356737059627239245596, 21803243333751066521028380, 21954359079503183880439580, 21803245676194614436988700,
  21954361421946731797448476, 21954363764390288442902300, 21799043350511412905543452, 21954956402644199423395612,
  21803845341779186622449436, 21954961087531303981860636, 2479619488848412603959068, 21799043355085398525134620,
  21823029960189830107547420, 21951958074716962198423324, 21956755399397902889568028, 21956757723541183635965724,
  21956757741841455168931612, 21952558893223034695501596, 21957355064982470711887644, 21956755385671600001107740,
  21956757728115152280209180, 21957355051256167823165212],
  ![  21803241009607816180271136, 2609144961313917255157792, 21954359079503197106210848, 2474819869816571253884960,
  21803241010751308273158176, 21954359080646690272839712, 2456230236677376584058912, 21803241011894800366045216,
  2475419535401139075942432, 21803840676335876095215648, 2532387765987875909404704, 2532987431572443731994784,
  21799043356228903843792928, 2456267569372040788052000, 2609744480351177280718880, 21951960417160527771469856,
  2686501383013628771436576, 2609744626467476519127072, 21956754825224147997689888, 2533024764267107935455264,
  2686501675532117451343904, 21799080834182248216528928],
  ![  21956754813789228159604833, 2609144961313918345943137, 21956757156232780438706273, 2479617176197241434937441,
  2479619500340522181335137, 21956757157376272531593313, 2609744626326740121557089, 2609744626612613144778849,
  21799043351654901657901153, 21957354480517288074549345, 2532387765987876045985889, 21799043355085411750905953,
  21799062091203354795841633, 21803278470404382186932321, 2686501382441883815778401, 2686501383009231815710817,
  2686501383013629862221921, 2686501528839658167212129, 2686501528844056213723233, 21803278474978350558480481,
  21956757728115166324070497, 21803878140562918380537953],
  ![  21803241009607816180803746, 21951959831551838725482658, 21956757156232780439234722, 2475419388998966814845090,
  21803241010751309364471970, 21956757157376272532121762, 2456230236677376584591522, 2609745797548532350987426,
  2552176730225820299831458, 21803840676335877186529442, 2532387765987875909404834, 2532987431572443731994786,
  21875800546549986531092642, 2609744480065304258029730, 2609744480351177281513634, 21951960417160527772002466,
  2686501383013629862750370, 21951958077003959678142626, 2609745797689269839342754, 21951958079290943863916706,
  21951960421734496143550626, 21952557744875511686506658],
  ![  21956754813789228160137443, 21951959831551839816268003, 21956757156232780439238883, 2480216713675510482090211,
  21956754814932720253024483, 21956757157376272532125923, 2685320936796728155060451, 21956754816076212345911523,
  21799043351654901658433763, 21957354480517288075081955, 2685904498071994678778083, 21799043355085412842219747,
  21894694696225077577267427, 2686501382437485769799907, 2686501383004833769732323, 21956757723541197953054947,
  2686501383013629862754531, 21956755383384629842151651, 21956757707527910606125283, 21956755385671614027925731,
  21956757728115166324603107, 21957355051256181867555043],
  ![  2461027414956145086008872, 2613944627862267291404840, 21954359079503197106211368, 2479617176197240480500264,
  21803241010751309346900520, 21954359080646690409155112, 21799043350511408619063848, 21957354479373795027225128,
  2480216860077699241315880, 21957354480517288210893352, 2552176730243429801560616, 21799043355085411887254056,
  21799043356228903980141096, 2682942331767179171827240, 21956755399397916251687464, 21951960417160527907818024,
  21956757741841468530788904, 2685303661410786256064040, 21957355064982484073744936, 21803278474978349621086760,
  21956757728115165369633320, 21803878140562917443144232],
  ![  21956754813789228159605353, 21951959831551804910606953, 21956757156232780575054441, 2480216695379637131713129,
  21956754814932720252492393, 21956757157376272667941481, 21799043350511409692805737, 21957354479373796118010473,
  21954881445589600094820969, 21957354480517288210897513, 2552176730243429801826921, 21803765721568282623253097,
  21954904868881665689557609, 21803278470404382323280489, 21956755399397917342472809, 21956757723541198088870505,
  21956757741841469621574249, 21803878135988950162381417, 21957355064982485164530281, 21803278474978350711872105,
  21956757728115166460418665, 21803878140562918533929577],
  ![  2461027414956162125270064, 2613944609566392578608176, 21954359079503197106211888, 2474819869816571253886000,
  21803241010751308273159216, 21954359080646690272840752, 2456230236677376584059952, 21803250235266837220822064,
  21799044504576440079092784, 21803840676335876095216688, 2552176730243429937908784, 21799043355085428666600496,
  21799049120836444466941488, 21951958074716975492369456, 21956755399397916115340336, 21951960417160527771470896,
  21956757741841468394441776, 21951967444491202061339696, 21957355064982501526310448, 21951958079290961316482096,
  21951960421734513595583536, 21952557744875529138539568],
  ![  2614541804605524572777650, 21951959831551838725483698, 21956757156232780439235762, 2475419388998966814846130,
  21803241010751309364473010, 21956757157376272532122802, 2456230236677376584592562, 2614541951007696834407602,
  2552176730225820299832498, 21822734826010968232701106, 2552176730243429937908914, 2552176730278614310530226,
  2552176730296206496574642, 2609744480065304258030770, 2614541951113249950674098, 21951960417160527772003506,
  21956757741841469485755570, 2609745779388981126507698, 2614541951148434322762930, 22028715269612042913000626,
  22028717612055595192102066, 22029314935196610735058098],
  ![  2461032028893980775386680, 21803243333751062166408760, 21954359079503197242560056, 21803245676194614436990520,
  21803245694494921948565048, 21954363764390302878764600, 2456231407894772266012216, 21957354479373812207095352,
  2480216860077699241315896, 2480216860082097287827000, 2552176730243430074256952, 21950159082537257986657848,
  21954961073805031635127864, 21951958074716993081282104, 21956755399397933704252984, 21956757723541214450650680,
  21956757741841485983354424, 21952557740301560903339576, 21957355064982501526310456, 21956755385671630543097400,
  21956757728115182822198840, 21957355051256198365154872]]

end D5.S3.Topology.ProductStableCertificate

/-! Kernel verification of the two coordinate contractions of the product core. -/


namespace D5.S3.Topology.ProductStableCertificate

open ProductRigidCores (VertexLabel P Factor)
open private edgeRaw from D5.S3.Topology.StableCategory.ProductRigidCores
open ConnectedCategoryGraft (Categorical)
open Relation (EqvGen)

abbrev Index := Fin 22 × Fin 22

def decode (word : ℕ) : Finset VertexLabel :=
  Finset.univ.filter fun v => word.testBit v.val

def reduced (s : Finset VertexLabel) : Prop :=
  ∀ i : Fin 3, s ≠ edgeRaw i

instance (s : Finset VertexLabel) : Decidable (reduced s) := by
  unfold reduced
  infer_instance

def core : Set Factor := {s | reduced s.val}

abbrev Core := core

private def packed (x : Index) : ℕ := words x.1 x.2

def colour (x : Index) : Bool := (packed x).testBit 84

private def slot (axis : Bool) (t : Fin 7) : ℕ :=
  (if axis then 42 else 0) + 6 * t.val

private def slice (x : Index) (axis : Bool) (t : Fin 7) : ℕ :=
  (packed x >>> slot axis t) % 64

private theorem decode_face : ∀ a : Fin 22,
    decode (faceMasks a) ∈ P ∧ reduced (decode (faceMasks a)) := by
  decide +kernel

private theorem has_index : ∀ s : Finset VertexLabel, s ∈ P → reduced s →
    ∃ a : Fin 22, decode (faceMasks a) = s := by
  decide +kernel

def indexFace (a : Fin 22) : Core :=
  ⟨⟨decode (faceMasks a), (decode_face a).1⟩, (decode_face a).2⟩

private theorem indexFace_surjective : Function.Surjective indexFace := by
  rintro ⟨⟨s, hs⟩, hr⟩
  obtain ⟨a, ha⟩ := has_index s hs hr
  exact ⟨a, Subtype.ext (Subtype.ext ha)⟩

private theorem table_order : ∀ a b : Fin 22,
    indexFace a ≤ indexFace b ↔ faceMasks a &&& faceMasks b = faceMasks a := by
  decide +kernel

private def rowConditions (a : Fin 22) : Prop :=
  ∀ b : Fin 22, ∀ axis : Bool,
    (∀ t : Fin 7, ∃ c : Fin 22, faceMasks c = slice (a, b) axis t) ∧
    slice (a, b) axis 0 = faceMasks (if axis then b else a) ∧
    slice (a, b) axis 6 = 8 ∧
    ∀ t : Fin 6,
      let p := slice (a, b) axis t.castSucc
      let q := slice (a, b) axis t.succ
      p &&& q = (if t.val % 2 = 0 then p else q)

private def mapConditions (a : Fin 22) : Prop :=
  ∀ b c d : Fin 22, faceMasks a &&& faceMasks c = faceMasks a →
    faceMasks b &&& faceMasks d = faceMasks b →
    colour (a, b) = colour (c, d) →
    packed (a, b) &&& packed (c, d) = packed (a, b)

private instance (a : Fin 22) : Decidable (rowConditions a) := by
  unfold rowConditions
  infer_instance

private instance (a : Fin 22) : Decidable (mapConditions a) := by
  unfold mapConditions
  infer_instance

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
-- Check the membership, endpoints, and six comparisons of the coordinate rows.
private theorem rows_checked (a : Fin 22) : rowConditions a := by
  fin_cases a <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
-- Each packed comparison checks all fourteen coordinate rows at once.
private theorem maps_checked (a : Fin 22) : mapConditions a := by
  fin_cases a <;> decide +kernel

private theorem bit_mono {p q k : ℕ} (h : p &&& q = p) (hp : p.testBit k = true) :
    q.testBit k = true := by
  have eq := congrArg (fun x : ℕ => x.testBit k) h
  simpa only [Nat.testBit_and, hp, Bool.true_and] using eq

private theorem decode_mono_of_bits {p q : ℕ}
    (h : ∀ k : VertexLabel, p.testBit k.val = true → q.testBit k.val = true) :
    decode p ⊆ decode q := by
  intro k hk
  simp only [decode, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
  exact h k hk

private theorem slice_bit (x : Index) (axis : Bool) (t : Fin 7) (k : VertexLabel) :
    (slice x axis t).testBit k.val = (packed x).testBit (slot axis t + k.val) := by
  change ((packed x >>> slot axis t) % (2 ^ 6)).testBit k.val = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [k.isLt]

def row (axis : Bool) (t : Fin 7) (x : Index) : Core :=
  ⟨⟨decode (slice x axis t), by
    obtain ⟨c, hc⟩ := (rows_checked x.1 x.2 axis).1 t
    rw [← hc]
    exact (decode_face c).1⟩, by
    change reduced (decode (slice x axis t))
    obtain ⟨c, hc⟩ := (rows_checked x.1 x.2 axis).1 t
    rw [← hc]
    exact (decode_face c).2⟩

theorem row_mono (axis : Bool) (t : Fin 7) {x y : Index}
    (h₁ : indexFace x.1 ≤ indexFace y.1) (h₂ : indexFace x.2 ≤ indexFace y.2)
    (hcol : colour x = colour y) : row axis t x ≤ row axis t y := by
  have h := maps_checked x.1 x.2 y.1 y.2
    ((table_order _ _).mp h₁) ((table_order _ _).mp h₂) hcol
  change decode (slice x axis t) ⊆ decode (slice y axis t)
  apply decode_mono_of_bits
  intro k hk
  rw [slice_bit] at hk ⊢
  exact bit_mono h hk

theorem row_start (axis : Bool) (x : Index) :
    row axis 0 x = indexFace (if axis then x.2 else x.1) := by
  apply Subtype.ext
  apply Subtype.ext
  change decode (slice x axis 0) = _
  rw [(rows_checked x.1 x.2 axis).2.1]
  rfl

def terminal : Core := indexFace 6

theorem row_end (axis : Bool) (x : Index) : row axis 6 x = terminal := by
  apply Subtype.ext
  apply Subtype.ext
  change decode (slice x axis 6) = decode (faceMasks 6)
  rw [(rows_checked x.1 x.2 axis).2.2.1]
  rfl

theorem row_step (axis : Bool) (t : Fin 6) (x : Index) :
    if t.val % 2 = 0 then row axis t.castSucc x ≤ row axis t.succ x
    else row axis t.succ x ≤ row axis t.castSucc x := by
  have h := (rows_checked x.1 x.2 axis).2.2.2 t
  by_cases ht : t.val % 2 = 0
  · simp only [ite_eq_left ht]
    apply decode_mono_of_bits
    exact fun _ => bit_mono (by simpa only [ite_eq_left ht] using h)
  · simp only [ite_eq_right ht]
    apply decode_mono_of_bits
    exact fun _ => bit_mono (by simpa only [ite_eq_right ht, Nat.and_comm] using h)

noncomputable section

def faceIndex (x : Core) : Fin 22 := Classical.choose (indexFace_surjective x)

theorem index_faceIndex (x : Core) : indexFace (faceIndex x) = x :=
  Classical.choose_spec (indexFace_surjective x)

def pairIndex (x : Core × Core) : Index := (faceIndex x.1, faceIndex x.2)

def coreColour (x : Core × Core) : Bool := colour (pairIndex x)

def region (b : Bool) : Set (Core × Core) := {x | coreColour x = b}

def coordinate (b axis : Bool) (t : Fin 7) : region b →o Core where
  toFun x := row axis t (pairIndex x.val)
  monotone' x y h := row_mono axis t
    (by simpa only [pairIndex, index_faceIndex] using h.1)
    (by simpa only [pairIndex, index_faceIndex] using h.2)
    (x.property.trans y.property.symm)

def paired (b : Bool) (t : Fin 7) : region b →o Core × Core where
  toFun x := (coordinate b false t x, coordinate b true t x)
  monotone' _ _ h := ⟨(coordinate b false t).monotone h, (coordinate b true t).monotone h⟩

private theorem paired_start (b : Bool) :
    paired b 0 = (OrderEmbedding.subtype (region b)).toOrderHom := by
  apply OrderHom.ext
  funext x
  apply Prod.ext
  · change row false 0 (pairIndex x.val) = x.val.1
    rw [row_start]
    exact index_faceIndex x.val.1
  · change row true 0 (pairIndex x.val) = x.val.2
    rw [row_start]
    exact index_faceIndex x.val.2

private theorem paired_end (b : Bool) :
    paired b 6 = OrderHom.const (region b) (terminal, terminal) := by
  apply OrderHom.ext
  funext x
  exact Prod.ext (row_end false (pairIndex x.val)) (row_end true (pairIndex x.val))

private theorem paired_step (b : Bool) (t : Fin 6) :
    EqvGen (· ≤ ·) (paired b t.castSucc) (paired b t.succ) := by
  by_cases ht : t.val % 2 = 0
  · apply EqvGen.rel
    intro x
    change row false t.castSucc (pairIndex x.val) ≤ row false t.succ (pairIndex x.val) ∧
      row true t.castSucc (pairIndex x.val) ≤ row true t.succ (pairIndex x.val)
    exact ⟨by simpa [ht] using row_step false t (pairIndex x.val),
      by simpa [ht] using row_step true t (pairIndex x.val)⟩
  · apply EqvGen.symm
    apply EqvGen.rel
    intro x
    change row false t.succ (pairIndex x.val) ≤ row false t.castSucc (pairIndex x.val) ∧
      row true t.succ (pairIndex x.val) ≤ row true t.castSucc (pairIndex x.val)
    exact ⟨by simpa [ht] using row_step false t (pairIndex x.val),
      by simpa [ht] using row_step true t (pairIndex x.val)⟩

/-- The inherited product partition contracts in the original core poset. -/
theorem categorical_region (b : Bool) : Categorical (region b) := by
  refine ⟨(terminal, terminal), ?_⟩
  rw [← paired_start, ← paired_end]
  exact .trans _ _ _ (paired_step b 0) (.trans _ _ _ (paired_step b 1)
    (.trans _ _ _ (paired_step b 2) (.trans _ _ _ (paired_step b 3)
      (.trans _ _ _ (paired_step b 4) (paired_step b 5)))))

end
end D5.S3.Topology.ProductStableCertificate

noncomputable section

namespace D5.S3.Topology.StableCategory.ProductStableCover

open D5.S3.Topology.ProductRigidCores
open BarycentricGraphDistance (Face)
open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open PartialOrder (NonemptyFiniteChains)
open StableCategory.OrdinarySubdivisionTransfer (finiteSpaceSubdivision)
open private edgeRaw exceptionalRaw edge_le_exceptional edge_below_unique_facet map_fence
  from D5.S3.Topology.StableCategory.ProductRigidCores

/-- The face poset after removing the edges 12, 14, and 24. -/
abbrev Q := {s : Factor // ∀ i : Fin 3, s.val ≠ edgeRaw i}

def coreInclusion : Q →o Factor :=
  ⟨Subtype.val, fun _ _ h => h⟩

private def raiseFace (s : Factor) : Factor := by
  classical
  exact if h : ∃ i : Fin 3, s.val = edgeRaw i then exceptional h.choose else s

private theorem exceptional_kept : ∀ i j : Fin 3, exceptionalRaw i ≠ edgeRaw j := by
  decide +kernel

private theorem edge_interval :
    ∀ i : Fin 3, ∀ s ∈ (exceptionalRaw i).powerset,
      edgeRaw i ⊆ s → s = edgeRaw i ∨ s = exceptionalRaw i := by
  decide +kernel

private theorem le_raiseFace (s : Factor) : s ≤ raiseFace s := by
  by_cases h : ∃ i : Fin 3, s.val = edgeRaw i
  · rw [raiseFace, dif_pos h]
    change s.val ⊆ exceptionalRaw h.choose
    exact (show s.val ⊆ edgeRaw h.choose from h.choose_spec.le).trans
      (edge_le_exceptional h.choose)
  · have hs : raiseFace s = s := dif_neg h
    exact le_of_eq hs.symm

private theorem raiseFace_kept (s : Factor) : ∀ i : Fin 3, (raiseFace s).val ≠ edgeRaw i := by
  by_cases h : ∃ i : Fin 3, s.val = edgeRaw i
  · rw [raiseFace, dif_pos h]
    exact exceptional_kept h.choose
  · have hs : raiseFace s = s := dif_neg h
    rw [hs]
    exact fun i hi => h ⟨i, hi⟩

private theorem raiseFace_monotone : Monotone raiseFace := by
  intro x y hxy
  by_cases hx : ∃ i : Fin 3, x.val = edgeRaw i
  · have he : edgeRaw hx.choose ⊆ y.val :=
      (show edgeRaw hx.choose ⊆ x.val from hx.choose_spec.symm.le).trans hxy
    have ht := edge_below_unique_facet hx.choose y he
    rcases edge_interval hx.choose y.val (Finset.mem_powerset.mpr ht) he with hy | hy
    · have h : x = y := Subtype.ext (hx.choose_spec.trans hy.symm)
      exact le_of_eq (congrArg raiseFace h)
    · calc
        raiseFace x = exceptional hx.choose := dif_pos hx
        _ = y := Subtype.ext hy.symm
        _ ≤ raiseFace y := le_raiseFace y
  · have h : raiseFace x = x := dif_neg hx
    rw [h]
    exact hxy.trans (le_raiseFace y)

/-- Send 12 to 012, 14 to 145, and 24 to 234, fixing every other face. -/
def coreRetract : Factor →o Q :=
  ⟨fun s => ⟨raiseFace s, raiseFace_kept s⟩, raiseFace_monotone⟩

@[simp] theorem coreRetract_inclusion (q : Q) : coreRetract (coreInclusion q) = q := by
  have h : ¬ ∃ i : Fin 3, q.val.val = edgeRaw i := fun ⟨i, hi⟩ => q.property i hi
  apply Subtype.ext
  exact dif_neg h

theorem coreRetract_comp_inclusion : coreRetract.comp coreInclusion = OrderHom.id := by
  apply OrderHom.ext
  exact funext coreRetract_inclusion

theorem id_le_coreInclusion_retract : OrderHom.id ≤ coreInclusion.comp coreRetract :=
  fun s => le_raiseFace s

def productInclusion : Q × Q →o ProductPoset := coreInclusion.prodMap coreInclusion

def productRetract : ProductPoset →o Q × Q := coreRetract.prodMap coreRetract

theorem productRetract_comp_inclusion : productRetract.comp productInclusion = OrderHom.id := by
  apply OrderHom.ext
  funext q
  exact Prod.ext (coreRetract_inclusion q.1) (coreRetract_inclusion q.2)

theorem id_le_productInclusion_retract : OrderHom.id ≤ productInclusion.comp productRetract :=
  fun x => ⟨le_raiseFace x.1, le_raiseFace x.2⟩

abbrev coreFibre (label : Q × Q → Fin 2) (i : Fin 2) : Set (Q × Q) := {q | label q = i}

abbrev pulledFibre (label : Q × Q → Fin 2) (i : Fin 2) : Set ProductPoset :=
  {x | label (productRetract x) = i}

theorem categorical_pulledFibre (label : Q × Q → Fin 2) (i : Fin 2)
    (hcat : Categorical (coreFibre label i)) : Categorical (pulledFibre label i) := by
  obtain ⟨c, hc⟩ := hcat
  let pre : pulledFibre label i →o coreFibre label i :=
    ⟨fun x => ⟨productRetract x.val, x.property⟩, fun _ _ h => productRetract.monotone h⟩
  let lift (f : coreFibre label i →o Q × Q) : pulledFibre label i →o ProductPoset :=
    productInclusion.comp (f.comp pre)
  have hlift : Monotone lift := by
    intro f g h x
    exact productInclusion.monotone ((OrderHom.le_def.mp h) (pre x))
  have hstart : (OrderEmbedding.subtype (pulledFibre label i)).toOrderHom ≤
      lift (OrderEmbedding.subtype (coreFibre label i)).toOrderHom := by
    intro x
    exact (OrderHom.le_def.mp id_le_productInclusion_retract) x.val
  refine ⟨productInclusion c, .trans _ _ _ (.rel _ _ hstart) ?_⟩
  simpa only [lift, OrderHom.const_comp, OrderHom.comp_const] using map_fence lift hlift hc

theorem has_categorical_cover_double_subdivision_of_core_label (label : Q × Q → Fin 2)
    (hlabel : ∀ i, Categorical (coreFibre label i)) :
    @HasCategoricalCover (finiteSpaceSubdivision (Face P × Face P) 2).1
      (finiteSpaceSubdivision (Face P × Face P) 2).2 2 := by
  change HasCategoricalCover (NonemptyFiniteChains (NonemptyFiniteChains ProductPoset)) 2
  apply SubdivisionCategoricalCover.hasCategoricalCover_double_subdivision
    (A := pulledFibre label 0) (B := pulledFibre label 1)
    (categorical_pulledFibre label 0 (hlabel 0)) (categorical_pulledFibre label 1 (hlabel 1))
  intro x
  have hFin : ∀ i : Fin 2, i = 0 ∨ i = 1 := by decide +kernel
  exact hFin (label (productRetract x))

theorem ordinary_three_and_double_subdivision_two (label : Q × Q → Fin 2)
    (hlabel : ∀ i, Categorical (coreFibre label i)) :
    IsLeast {n : ℕ | HasCategoricalCover (Face P × Face P) n} 3 ∧
    @HasCategoricalCover (finiteSpaceSubdivision (Face P × Face P) 2).1
      (finiteSpaceSubdivision (Face P × Face P) 2).2 2 :=
  ⟨least_categorical_cover, has_categorical_cover_double_subdivision_of_core_label label hlabel⟩

private def verifiedLabel (q : Q × Q) : Fin 2 :=
  if ProductStableCertificate.coreColour q then 1 else 0

private theorem verifiedLabel_categorical (i : Fin 2) : Categorical (coreFibre verifiedLabel i) := by
  have all : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide +kernel
  rcases all i with rfl | rfl
  · have eq : coreFibre verifiedLabel 0 = ProductStableCertificate.region false := by
      ext x
      change (if ProductStableCertificate.coreColour x then (1 : Fin 2) else 0) = 0 ↔
        ProductStableCertificate.coreColour x = false
      cases ProductStableCertificate.coreColour x <;> decide
    rw [eq]
    exact ProductStableCertificate.categorical_region false
  · have eq : coreFibre verifiedLabel 1 = ProductStableCertificate.region true := by
      ext x
      change (if ProductStableCertificate.coreColour x then (1 : Fin 2) else 0) = 1 ↔
        ProductStableCertificate.coreColour x = true
      cases ProductStableCertificate.coreColour x <;> decide
    rw [eq]
    exact ProductStableCertificate.categorical_region true

/-- Two categorical lower sets cover the second ordinary subdivision of
the seven-triangle face-poset product. -/
theorem product_two_after_two_subdivisions :
    @HasCategoricalCover (finiteSpaceSubdivision (Face P × Face P) 2).1
      (finiteSpaceSubdivision (Face P × Face P) 2).2 2 :=
  has_categorical_cover_double_subdivision_of_core_label verifiedLabel verifiedLabel_categorical

end D5.S3.Topology.StableCategory.ProductStableCover

end
