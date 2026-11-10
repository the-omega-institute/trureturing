/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part17
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part17
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.middle_strict; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part17.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part17
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0722 : List (List (List (List ℕ))) :=
  [[[[59835471391253,41174759762453],[52487816187413,33827104558613]],[[100167372980266,62845949722666],[85472062572586,48150639314986]],[[35083576443413,16422864814613],[27735921239573,9075209610773]]],[[[236753364921940,162399086112340],[207388895554900,133034616745300]],[[394728852515240,246020294896040],[335999913781160,187291356161960]],[[137063346678100,62709067868500],[107698877311060,33344598501460]]],[[[351191286274750,240091604021950],[307184722791550,196085040538750]],[[583075851367100,360876486861500],[495062724400700,272863359895100]],[[200637779458750,89538097205950],[156631215975550,45531533722750]]],[[[231464174408500,157684799816500],[202153829498500,128374454906500]],[[382634271431000,235075522247000],[324013581611000,176454832427000]],[[130419647918500,56640273326500],[101109303008500,27329928416500]]],[[[57190778256875,38817518736875],[49870182666875,31496923146875]],[[94119892783750,57373373743750],[79478701603750,42732182563750]],[[31761635286875,13388375766875],[24441039696875,6067780176875]]]]

private theorem identity_0722 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(9708448283 / 162470559744 : ℝ)) =
      tensor4 coefficients_0722 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0722, p_headbox] <;> ring

private theorem negative_0722 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0722 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0722] at hp
  linarith only [hp]

private def coefficients_0723 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_0723 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_0723 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0723, p_qmass] <;> ring

private theorem negative_0723 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0723 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0723] at hp
  linarith only [hp]

private theorem node_0735 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0722 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0723 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0724 : List (List (List (List ℕ))) :=
  [[[[56148113982413,37487402353613],[48800458778573,30139747149773]],[[92792658162586,55471234904986],[78097347754906,40775924497306]],[[31396219034573,12735507405773],[24048563830733,5387852201933]]],[[[222030086734900,147675807925300],[192665617367860,118311338558260]],[[365282296141160,216573738521960],[306553357407080,157844799787880]],[[122340068491060,47985789681460],[92975599124020,18621320314420]]],[[[329146509561550,218046827308750],[285139946078350,174040263825550]],[[538986297940700,316786933435100],[450973170974300,228773806468700]],[[178593002745550,67493320492750],[134586439262350,23486757009550]]],[[[216795020678500,143015646086500],[187484675768500,113705301176500]],[[353295963971000,205737214787000],[294675274151000,147116524967000]],[[115750494188500,41971119596500],[86440149278500,12660774686500]]],[[[53530480461875,35157220941875],[46209884871875,27836625351875]],[[86799297193750,50052778153750],[72158106013750,35411586973750]],[[28101337491875,9728077971875],[20780741901875,2407482381875]]]]

private theorem identity_0724 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(3851971811 / 162470559744 : ℝ)) =
      tensor4 coefficients_0724 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0724, p_headbox] <;> ring

private theorem negative_0724 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0724 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0724] at hp
  linarith only [hp]

private def coefficients_0725 : List (List (List (List ℕ))) :=
  [[[[625126936945549,326555550884749],[507564453684109,208993067623309]],[[1094225315473178,497082543351578],[859100348950298,261957576828698]],[[448105077945229,149533691884429],[330542594683789,31971208622989]]],[[[2482317335868980,1290340333270580],[2012276614409780,820299611811380]],[[4337466045587560,1953512040390760],[3397384602669160,1013430597472360]],[[1771337826723380,579360824124980],[1301297105264180,109320102665780]]],[[[3695965656551758,1911458502734158],[2991222045322318,1206714891504718]],[[6446607769139996,2877593461504796],[5037120546681116,1468106239045916]],[[2625168953335438,840661799517838],[1920425342105998,135918188288398]]],[[[2445486664939668,1258117820856468],[1975871663353908,788502819270708]],[[4257717898933656,1882980210767256],[3318487895762136,943750207595736]],[[1728744362144388,541375518061188],[1259129360558628,71760516475428]]],[[[606711403903779,310444097100579],[489361775349699,193094468546499]],[[1054350853092918,461816239486518],[819651595984758,227116982378358]],[[426808154179539,130540847376339],[309458525625459,13191218822259]]]]

private theorem identity_0725 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1465690980251 / 180522844160000 : ℝ)) =
      tensor4 coefficients_0725 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0725, p_headbox] <;> ring

private theorem negative_0725 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (17 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0725 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0725] at hp
  linarith only [hp]

private def coefficients_0726 : List (List (List (List ℕ))) :=
  [[[[397395232,496559392],[2672711744,2871040064],[2303206432,2402370592]],[[1698888704,1897217024],[7186158208,7582814848],[5543049344,5741377664]],[[1308465952,1407630112],[4527391424,4725719744],[3246815392,3345979552]]],[[[994683640,1193011960],[5752763360,6149420000],[4813859560,5012187880]],[[3801340520,4197997160],[15194549680,15987862960],[11504768840,11901425480]],[[2820601840,3018930160],[9469676240,9866332880],[6704854240,6903182560]]],[[[597634409,696798569],[3080743618,3279071938],[2510999129,2610163289]],[[2103143818,2301472138],[8009775476,8406432116],[5962411498,6160739818]],[[1512481889,1611646049],[4942976818,5141305138],[3458384849,3557549009]]]]

private theorem identity_0726 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(12418601 / 86768640 : ℝ)) =
      tensor4 coefficients_0726 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0726, p_variance] <;> ring

private theorem negative_0726 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (17 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0726 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0726] at hp
  linarith only [hp]

private theorem node_0738 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (17 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0725 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0726 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0727 : List (List (List (List ℕ))) :=
  [[[[94127121,292455441],[3894127362,4290784002],[3855780081,4054108401]],[[3763974402,4160631042],[15069848004,15863161284],[11417433282,11814089922]],[[3725627121,3923955441],[11287280322,11683936962],[7617433041,7815761361]]],[[[581871078,978527718],[8590595436,9383908716],[8120284038,8516940678]],[[8330289516,9123602796],[31774591512,33361218072],[23667421356,24460734636]],[[7859978118,8256634758],[23407115436,24200428716],[15658696998,16055353638]]],[[[488435959,686764279],[4697852078,5094508718],[4265195959,4463524279]],[[4567699118,4964355758],[16707511516,17500824796],[12251372078,12648028718]],[[4135042999,4333371319],[12121219118,12517875758],[8041955959,8240284279]]]]

private theorem identity_0727 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(10458569 / 617021440 : ℝ)) =
      tensor4 coefficients_0727 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0727, p_variance] <;> ring

private theorem negative_0727 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0727 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0727] at hp
  linarith only [hp]

private theorem node_0737 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (41 / 64 : ℝ)
  · exact node_0738 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0727 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private theorem node_0736 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0724 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0737 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0734 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_0735 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0736 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0728 : List (List (List (List ℕ))) :=
  [[[[651481747038229,352910360977429],[592700505407509,294129119346709]],[[1062961733328938,465818961207338],[945399250067498,348256477945898]],[[390486685708309,91915299647509],[331705444077589,33134058016789]]],[[[2579759315388500,1387782312790100],[2344738954658900,1152761952060500]],[[4197106472645800,1813152467449000],[3727065751186600,1343111745989800]],[[1533536274262100,341559271663700],[1298515913532500,106538910934100]]],[[[3830184256275838,2045677102458238],[3477812450661118,1693305296843518]],[[6213152331576956,2644138023941756],[5508408720347516,1939394412712316]],[[2257494916048318,472987762230718],[1905123110433598,120615956615998]]],[[[2527017201062388,1339648356979188],[2292209700269508,1104840856186308]],[[4086831483780696,1712093795614296],[3617216482194936,1242478794028536]],[[1476327410868708,288958566785508],[1241519910075828,54151065992628]]],[[[625110509729259,328843202926059],[566435695452219,270168388649019]],[[1007823884705478,415289271099078],[890474256151398,297939642544998]],[[361882079966619,65614773163419],[303207265689579,6939958886379]]]]

private theorem identity_0728 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(771106542931 / 180522844160000 : ℝ)) =
      tensor4 coefficients_0728 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 32 : ℝ)) (1-((x2-0)/(1 / 32 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0728, p_headbox] <;> ring

private theorem negative_0728 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 32 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0728 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 32 : ℝ)) (1-((x2-0)/(1 / 32 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0728] at hp
  linarith only [hp]

private def coefficients_0729 : List (List (List (List ℕ))) :=
  [[[[329219872,428384032],[1599724544,1798052864],[1277477152,1376641312]],[[1560213824,1758542144],[5019266368,5415923008],[3472997504,3671325824]],[[1237966432,1337130592],[3433486784,3631815104],[2202492832,2301656992]]],[[[858332920,1056661240],[3603012200,3999668840],[2758624240,2956952560]],[[3523990760,3920647400],[10853212480,11646525760],[7357111640,7753768280]],[[2679602800,2877931120],[7278090200,7674746840],[4612432360,4810760680]]],[[[529459049,628623209],[2003979658,2202307978],[1481493089,1580657249]],[[1964468938,2162797258],[5835330116,6231986756],[3884806138,4083134458]],[[1441982369,1541146529],[3845295418,4043623738],[2410285529,2509449689]]]]

private theorem identity_0729 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(10288121 / 86768640 : ℝ)) =
      tensor4 coefficients_0729 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0729, p_variance] <;> ring

private theorem negative_0729 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 32 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0729 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0729] at hp
  linarith only [hp]

private theorem node_0743 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0728 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0729 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0730 : List (List (List (List ℕ))) :=
  [[[[308302432,407466592],[2503822784,2702151104],[2223410272,2322574432]],[[1516054784,1714383104],[6839083648,7235740288],[5378808704,5577137024]],[[1214724832,1313888992],[4349205824,4547534144],[3162370912,3261535072]]],[[[816498040,1014826360],[5414985440,5811642080],[4654267240,4852595560]],[[3435672680,3832329320],[14500400560,15293713840],[11176287560,11572944200]],[[2633119600,2831447920],[9113305040,9509961680],[6535965280,6734293600]]],[[[508541609,607705769],[2911854658,3110182978],[2431202969,2530367129]],[[1920309898,2118638218],[7662700916,8059357556],[5798170858,5996499178]],[[1418740769,1517904929],[4764791218,4963119538],[3373940369,3473104529]]]]

private theorem identity_0730 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(9634451 / 86768640 : ℝ)) =
      tensor4 coefficients_0730 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0730, p_variance] <;> ring

private theorem negative_0730 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0730 ((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0730] at hp
  linarith only [hp]

private theorem node_0742 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (41 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact node_0743 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0730 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0731 : List (List (List (List ℕ))) :=
  [[[[282456006332819,208389179632019],[253118599194299,179051772493499]],[[443713445289118,295579791887518],[385038631012078,236904977610478]],[[150841791451499,76774964750699],[121504384312979,47437557612179]]],[[[1116536444258600,820844041673000],[999240937546880,703548534961280]],[[1747085808677080,1155701003505880],[1512494795253640,921109990082440]],[[588967620304880,293275217719280],[471672113593160,175979711007560]]],[[[1654771150511000,1212093787362200],[1478909978757800,1036232615609000]],[[2578777348530400,1693422622232800],[2227055005024000,1341700278726400]],[[861754693826600,419077330677800],[685893522073400,243216158924600]]],[[[1089756810024000,795211984680000],[972571355484000,678026530140000]],[[1691150691180000,1102061040492000],[1456779782100000,867690131412000]],[[559973515092000,265428689748000],[442788060552000,148243235208000]]],[[[269066095735000,195573057655000],[239783713375000,166290675295000]],[[415745702630000,268759626470000],[357180937910000,210194861750000]],[[136344648415000,62851610335000],[107062266055000,33569227975000]]]]

private theorem identity_0731 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6713845595 / 162470559744 : ℝ)) =
      tensor4 coefficients_0731 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 32 : ℝ)) (1-((x2-0)/(1 / 32 : ℝ))) ((x3-0)/(1 / 32 : ℝ)) (1-((x3-0)/(1 / 32 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0731, p_headbox] <;> ring

private theorem negative_0731 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 32 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 32 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0731 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 32 : ℝ)) (1-((x2-0)/(1 / 32 : ℝ))) ((x3-0)/(1 / 32 : ℝ)) (1-((x3-0)/(1 / 32 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0731] at hp
  linarith only [hp]

private def coefficients_0732 : List (List (List (List ℕ))) :=
  [[[[73,201],[146,402],[55,183]]]]

private theorem identity_0732 (x0 x1 x2 x3 : ℝ) :
    (2048 : ℝ)*(-p_qmass x0 x1 x2 x3-(55 / 2048 : ℝ)) =
      tensor4 coefficients_0732 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 32 : ℝ)) (1-((x2-0)/(1 / 32 : ℝ))) ((x3-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x3-(1 / 32 : ℝ))/(1 / 32 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0732, p_qmass] <;> ring

private theorem negative_0732 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 32 : ℝ))
    (h3l : (1 / 32 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0732 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 32 : ℝ)) (1-((x2-0)/(1 / 32 : ℝ))) ((x3-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x3-(1 / 32 : ℝ))/(1 / 32 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0732] at hp
  linarith only [hp]

private theorem node_0746 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 32 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0731 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0732 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0733 : List (List (List (List ℕ))) :=
  [[[[858678921,1057007241],[3607480962,4004137602],[2762747001,2961075321]],[[3528459522,3925116162],[10869703524,11663016804],[7369133922,7765790562]],[[2683725561,2882053881],[7290112482,7686769122],[4620331881,4818660201]]],[[[2118528198,2515184838],[8024856156,8818169436],[5934217878,6330874518]],[[7866813276,8660126556],[23374302552,24960929112],[15563269116,16356582396]],[[5776174998,6172831638],[15405226236,16198539516],[9656941158,10053597798]]],[[[1260541279,1458869599],[4418759198,4815415838],[3172162879,3370491199]],[[4339737758,4736394398],[12507367036,13300680316],[8195519198,8592175838]],[[3093141439,3291469759],[8116497758,8513154398],[5037301279,5235629599]]]]

private theorem identity_0733 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(95408769 / 617021440 : ℝ)) =
      tensor4 coefficients_0733 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0733, p_variance] <;> ring

private theorem negative_0733 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 32 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0733 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0733] at hp
  linarith only [hp]

private theorem node_0745 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 32 : ℝ)
  · exact node_0746 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0733 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0734 : List (List (List (List ℕ))) :=
  [[[[816844041,1015172361],[5423230962,5819887602],[4662166761,4860495081]],[[3440141442,3836798082],[14524445124,15317758404],[11195863362,11592520002]],[[2637242361,2835570681],[9129104082,9525760722],[6547641561,6745969881]]],[[[2034858438,2431515078],[11663909676,12457222956],[9740610918,10137267558]],[[7690177116,8483490396],[30698892792,32285519352],[23231835036,24025148316]],[[5683208598,6079865238],[19090762956,19884076236],[13519114038,13915770678]]],[[[1218706399,1417034719],[6242062718,6638719358],[5079136159,5277464479]],[[4251419678,4648076318],[16177215676,16970528956],[12037355678,12434012318]],[[3046658239,3244986559],[9963042878,10359699518],[6972164479,7170492799]]]]

private theorem identity_0734 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(90760449 / 617021440 : ℝ)) =
      tensor4 coefficients_0734 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0734, p_variance] <;> ring

private theorem negative_0734 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0734 ((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(41 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0734] at hp
  linarith only [hp]

private theorem node_0744 (x0 x1 x2 x3 : ℝ)
    (h0l : (41 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact node_0745 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0734 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0741 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (41 / 64 : ℝ)
  · exact node_0742 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0744 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0735 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_0735 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_0735 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0735, p_qmass] <;> ring

private theorem negative_0735 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0735 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0735] at hp
  linarith only [hp]

private theorem node_0740 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0741 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0735 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0736 : List (List (List (List ℕ))) :=
  [[[[200837128,250419208],[879289136,978453296],[685424488,735006568]],[[860695856,959860016],[2692890592,2891218912],[1846139696,1945303856]],[[666831208,716413288],[1827546416,1926710576],[1167687688,1217269768]]],[[[503509224,602673384],[1966024968,2164353288],[1476460704,1575624864]],[[1928838408,2127166728],[5808228096,6204884736],[3907279608,4105607928]],[[1439274144,1538438304],[3870093048,4068421368],[2444763864,2543928024]]],[[[303018097,352600177],[1087427834,1186591994],[791382217,840964297]],[[1068834554,1167998714],[3116721508,3315049828],[2061831914,2160996074]],[[772788937,822371017],[2043238634,2142402794],[1277422177,1327004257]]]]

private theorem identity_0736 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(25104641 / 86768640 : ℝ)) =
      tensor4 coefficients_0736 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0736, p_variance] <;> ring

private theorem negative_0736 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0736 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0736] at hp
  linarith only [hp]

private theorem node_0739 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_0740 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0736 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0733 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0734 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0739 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0737 : List (List (List (List ℕ))) :=
  [[[[29373033423443,20186403663443],[25712735628443,16526105868443]],[[48615234981886,30241975461886],[41294639391886,22921379871886]],[[16658461938443,7471832178443],[12998164143443,3811534383443]]],[[[116141603003272,79538252219272],[101514393098272,64911042314272]],[[191383589779544,118176888211544],[162129169969544,88922468401544]],[[64947294368272,28343943584272],[50320084463272,13716733679272]]],[[[172158324764408,117467493174008],[150238930672808,95548099082408]],[[282405556335616,173023893154816],[238566768152416,129185104971616]],[[94865435186408,40174603596008],[72946041094808,18255209504408]]],[[[113383872927552,77065743058752],[98785520664672,62467390795872]],[[185121086790624,112484827053024],[155924382264864,83288122527264]],[[61522739837472,25204609968672],[46924387574592,10606257705792]]],[[[27994116039192,18950096736792],[24348245757912,15304226455512]],[[45483881845104,27395843240304],[38192141282544,20104102677744]],[[14946135377112,5902116074712],[11300265095832,2256245793432]]]]

private theorem identity_0737 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(31336747131 / 705167360000 : ℝ)) =
      tensor4 coefficients_0737 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0737, p_headbox] <;> ring

private theorem negative_0737 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0737 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0737] at hp
  linarith only [hp]

private def coefficients_0738 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_0738 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_0738 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0738, p_qmass] <;> ring

private theorem negative_0738 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0738 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0738] at hp
  linarith only [hp]

private theorem node_0749 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0737 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0738 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0739 : List (List (List (List ℕ))) :=
  [[[[48029345,147193505],[1026303730,1224632050],[992219345,1091383505]],[[993765490,1192093810],[3880559300,4277215940],[2914683730,3113012050]],[[959681105,1058845265],[2882145490,3080473810],[1936409345,2035573505]]],[[[293559110,491887430],[2455161820,2851818460],[2189492630,2387820950]],[[2390085340,2786741980],[8581334360,9374647640],[6247028860,6643685500]],[[2124416150,2322744470],[6181952380,6578609020],[4085426150,4283754470]]],[[[246221767,345385927],[1430242094,1628570414],[1197965287,1297129447]],[[1397703854,1596032174],[4703543068,5100199708],[3333729134,3532057454]],[[1165427047,1264591207],[3301190894,3499519214],[2149708807,2248872967]]]]

private theorem identity_0739 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(1372267 / 39665664 : ℝ)) =
      tensor4 coefficients_0739 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0739, p_variance] <;> ring

private theorem negative_0739 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0739 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0739] at hp
  linarith only [hp]

private theorem node_0748 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_0749 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0739 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0740 : List (List (List (List ℕ))) :=
  [[[[29436065,128600225],[1928658850,2126987170],[1955002625,2054166785]],[[951930610,1150258930],[5708511140,6105167780],[4868140210,5066468530]],[[936439505,1035603665],[3807742210,4006070530],[2927082545,3026246705]]],[[[256372550,454700870],[4267425580,4664082220],[4122612710,4320941030]],[[2306415580,2703072220],[12252345080,13045658360],[10169048860,10565705500]],[[2077932950,2276261270],[8040699340,8437355980],[6074326070,6272654390]]],[[[227628487,326792647],[2340150734,2538479054],[2168302087,2267466247]],[[1355868974,1554197294],[6546601948,6943258588],[5302292654,5500620974]],[[1142185447,1241349607],[4234341134,4432669454],[3147935527,3247099687]]]]

private theorem identity_0740 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(5887213 / 277659648 : ℝ)) =
      tensor4 coefficients_0740 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0740, p_variance] <;> ring

private theorem negative_0740 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0740 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0740] at hp
  linarith only [hp]

private theorem node_0747 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0748 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0740 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0732 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (21 / 32 : ℝ)
  · exact node_0733 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0747 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0741 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0741 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0741 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0741, p_qmass] <;> ring

private theorem negative_0741 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0741 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0741] at hp
  linarith only [hp]

private theorem node_0731 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0732 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0741 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0742 : List (List (List (List ℕ))) :=
  [[[[52242922,77033962],[342131204,391713284],[296860762,321651802]],[[335158724,384740804],[1161877288,1261041448],[840663524,890245604]],[[289888282,314679322],[833691044,883273124],[550775242,575566282]]],[[[155403328,204985408],[789874136,889038296],[648415768,697997848]],[[775929176,875093336],[2542531552,2740859872],[1794492296,1893656456]],[[634470808,684052888],[1780547336,1879711496],[1160021488,1209603568]]],[[[103506407,128297447],[448434934,498017014],[351901007,376692047]],[[441462454,491044534],[1382038268,1481202428],[954520774,1004102854]],[[344928527,369719567],[947548294,997130374],[609592247,634383287]]]]

private theorem identity_0742 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(26121461 / 86768640 : ℝ)) =
      tensor4 coefficients_0742 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0742, p_variance] <;> ring

private theorem negative_0742 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0742 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0742] at hp
  linarith only [hp]

private theorem node_0730 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0731 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0742 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0743 : List (List (List (List ℕ))) :=
  [[[[47594602,72385642],[575128244,624710324],[555423562,580214602]],[[323537924,373120004],[1639492168,1738656328],[1371734084,1421316164]],[[282915802,307706842],[1078308884,1127890964],[823283002,848074042]]],[[[146106688,195688768],[1259644976,1358809136],[1169318128,1218900208]],[[752687576,851851736],[3505314832,3703643152],[2864186936,2963351096]],[[620525848,670107928],[2273559776,2372723936],[1708813768,1758395848]]],[[[98858087,123649127],[685208734,734790814],[614240567,639031607]],[[429841654,479423734],[1867206668,1966370828],[1493144854,1542726934]],[[337956047,362747087],[1195942894,1245524974],[885876767,910667807]]]]

private theorem identity_0743 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(23797301 / 86768640 : ℝ)) =
      tensor4 coefficients_0743 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0743, p_variance] <;> ring

private theorem negative_0743 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0743 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0743] at hp
  linarith only [hp]

private theorem node_0729 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0730 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0743 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0744 : List (List (List (List ℕ))) :=
  [[[[57595701780709,39507663175909],[50303961218149,32215922613349]],[[94182703094858,58006625885258],[79599221969738,43423144760138]],[[31499740456549,13411701851749],[24207999893989,6119961289189]]],[[[227567989581268,155499940480468],[198430769606548,126362720505748]],[[370359693559016,226223595357416],[312085253609576,167949155407976]],[[122522565168148,50454516067348],[93385345193428,21317296092628]]],[[[337072562493358,229395531222958],[293412227963278,185735196692878]],[[545874036176636,330519973635836],[458553367116476,243199304575676]],[[178517308638478,70840277368078],[134856974108398,27179942837998]]],[[[221823747165060,150321677507460],[192747770549460,121245700891860]],[[357399383856120,214395244540920],[299247430624920,156243291309720]],[[115465679599860,43963609942260],[86389702984260,14887633326660]]],[[[54723469064699,36918420181499],[47462347567019,29657298683819]],[[87702331328518,52092233562118],[73180088333158,37569990566758]],[[27971192265419,10166143382219],[20710070767739,2905021884539]]]]

private theorem identity_0744 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(2905021884539 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0744 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0744, p_headbox] <;> ring

private theorem negative_0744 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0744 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0744] at hp
  linarith only [hp]

private def coefficients_0745 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_0745 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_0745 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0745, p_qmass] <;> ring

private theorem negative_0745 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0745 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0745] at hp
  linarith only [hp]

private theorem node_0756 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0744 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0745 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0746 : List (List (List (List ℕ))) :=
  [[[[73562778,123144858],[616024836,715188996],[549434538,599016618]],[[599755716,698919876],[2153579112,2351907432],[1567768356,1666932516]],[[533165418,582747498],[1551499236,1650663396],[1025306298,1074888378]]],[[[246567768,345731928],[1434710856,1633039176],[1202088048,1301252208]],[[1402172616,1600500936],[4720034112,5116690752],[3345751416,3544079736]],[[1169549808,1268713968],[3313213176,3511541496],[2157608328,2256772488]]],[[[173350991,222933071],[819378022,918542182],[652999511,702581591]],[[803108902,902273062],[2567839004,2766167324],[1778675062,1877839222]],[[636730391,686312471],[1762405942,1861570102],[1132648031,1182230111]]]]

private theorem identity_0746 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(4086821 / 38563840 : ℝ)) =
      tensor4 coefficients_0746 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0746, p_variance] <;> ring

private theorem negative_0746 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0746 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0746] at hp
  linarith only [hp]

private theorem node_0755 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_0756 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0746 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0747 : List (List (List (List ℕ))) :=
  [[[[64266138,113848218],[1070979156,1170143316],[1034602938,1084185018]],[[578838276,678002436],[3075108552,3273436872],[2552050116,2651214276]],[[521544618,571126698],[2018074356,2117238516],[1524419658,1574001738]]],[[[227974488,327138648],[2348396256,2546724576],[2176201608,2275365768]],[[1360337736,1558666056],[6570646512,6967303152],[5321868456,5520196776]],[[1146308208,1245472368],[4250140176,4448468496],[3159611808,3258775968]]],[[[164054351,213636431],[1278109102,1377273262],[1141944671,1191526751]],[[782191462,881355622],[3496921964,3695250284],[2770510342,2869674502]],[[625109591,674691671],[2232757822,2331921982],[1635538151,1685120231]]]]

private theorem identity_0747 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(3570341 / 38563840 : ℝ)) =
      tensor4 coefficients_0747 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0747, p_variance] <;> ring

private theorem negative_0747 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0747 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0747] at hp
  linarith only [hp]

private theorem node_0754 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0755 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0747 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0748 : List (List (List (List ℕ))) :=
  [[[[28191884004667,19289359563067],[24561323255827,15658798814227]],[[45511464608894,27706415725694],[38250343111214,20445294228014]],[[14815745605027,5913221163427],[11185184856187,2282660414587]]],[[[111302600565536,75833439861536],[96796102882616,61326942178616]],[[178750829164552,107812507756552],[149737833798712,78799512390712]],[[57472527151016,22003366447016],[42966029468096,7496868764096]]],[[[164727565361792,111734672100992],[142991869971392,89998976710592]],[[263128636129984,157142849608384],[219657245349184,113671458827584]],[[83496819538592,30503926277792],[61761124148192,8768230887392]]],[[[108314750130176,73126347954176],[93840606788096,58652204612096]],[[172050419471872,101673615119872],[143102132787712,72725328435712]],[[53838931229696,18650529053696],[39364787887616,4176385711616]]],[[[26697899625472,17935754447872],[23083514739712,14321369562112]],[[42161144489984,24636854134784],[34932374718464,17408084363264]],[[12998891533312,4236746355712],[9384506647552,622361469952]]]]

private theorem identity_0748 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(607774873 / 49582080000 : ℝ)) =
      tensor4 coefficients_0748 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0748, p_headbox] <;> ring

private theorem negative_0748 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0748 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0748] at hp
  linarith only [hp]

private def coefficients_0749 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_0749 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_0749 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0749, p_qmass] <;> ring

private theorem negative_0749 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0749 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0749] at hp
  linarith only [hp]

private theorem node_0759 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0748 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0749 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0750 : List (List (List (List ℕ))) :=
  [[[[246913769,346077929],[1439179618,1637507938],[1206210809,1305374969]],[[1406641378,1604969698],[4736525156,5133181796],[3357773698,3556102018]],[[1173672569,1272836729],[3325235458,3523563778],[2165507849,2264672009]]],[[[694095966,892424286],[3286449612,3683106252],[2620243566,2818571886]],[[3221373132,3618029772],[10304338104,11097651384],[7138744812,7535401452]],[[2555167086,2753495406],[7073668332,7470324972],[4546391166,4744719486]]],[[[447874199,547038359],[1848653998,2046982318],[1414724759,1513888919]],[[1816115758,2014444078],[5570580956,5967237596],[3782355118,3980683438]],[[1382186519,1481350679],[3749816878,3948145198],[2381575319,2480739479]]]]

private theorem identity_0750 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(246913769 / 1388298240 : ℝ)) =
      tensor4 coefficients_0750 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0750, p_variance] <;> ring

private theorem negative_0750 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0750 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0750] at hp
  linarith only [hp]

private theorem node_0758 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_0759 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0750 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0751 : List (List (List (List ℕ))) :=
  [[[[228320489,327484649],[2356641778,2554970098],[2184101129,2283265289]],[[1364806498,1563134818],[6594691076,6991347716],[5341444258,5539772578]],[[1150430969,1249595129],[4265939218,4464267538],[3171288089,3270452249]]],[[[656909406,855237726],[5128927452,5525584092],[4583577726,4781906046]],[[3137703372,3534360012],[14035776984,14829090264],[11121192972,11517849612]],[[2508683886,2707012206],[8962629372,9359286012],[6565505166,6763833486]]],[[[429280919,528445079],[2773669678,2971997998],[2400168599,2499332759]],[[1774280878,1972609198],[7443853916,7840510556],[5781132718,5979461038]],[[1358944919,1458109079],[4698074158,4896402478],[3394909079,3494073239]]]]

private theorem identity_0751 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(228320489 / 1388298240 : ℝ)) =
      tensor4 coefficients_0751 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0751, p_variance] <;> ring

private theorem negative_0751 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0751 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0751] at hp
  linarith only [hp]

private theorem node_0757 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0758 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0751 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0753 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0754 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0757 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0752 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0752 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0752 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0752, p_qmass] <;> ring

private theorem negative_0752 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0752 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0752] at hp
  linarith only [hp]

private theorem node_0752 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0753 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0752 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0753 : List (List (List (List ℕ))) :=
  [[[[155749329,205331409],[794342898,893507058],[652538529,702120609]],[[780397938,879562098],[2559022596,2757350916],[1806514578,1905678738]],[[638593569,688175649],[1792569618,1891733778],[1167921009,1217503089]]],[[[414717630,513881790],[1802677260,2001005580],[1415849550,1515013710]],[[1774787340,1973115660],[5561135160,5957791800],[3842127660,4040455980]],[[1387959630,1487123790],[3814237740,4012566060],[2454168030,2553332190]]],[[[259660303,309242383],[1009718366,1108882526],[764003023,813585103]],[[995773406,1094937566],[3004880572,3203208892],[2036997086,2136161246]],[[750058063,799640143],[2023052126,2122216286],[1286939023,1336521103]]]]

private theorem identity_0753 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(17305481 / 38563840 : ℝ)) =
      tensor4 coefficients_0753 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0753, p_variance] <;> ring

private theorem negative_0753 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0753 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0753] at hp
  linarith only [hp]

private theorem node_0751 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0752 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0753 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0754 : List (List (List (List ℕ))) :=
  [[[[146452689,196034769],[1267890498,1367054658],[1177217649,1226799729]],[[757156338,856320498],[3529359396,3727687716],[2883762738,2982926898]],[[624648609,674230689],[2289358818,2388522978],[1720490049,1770072129]]],[[[396124350,495288510],[2757325980,2955654300],[2472761310,2571925470]],[[1728304140,1926632460],[7516915800,7913572440],[6011731020,6210059340]],[[1360069710,1459233870],[4815369660,5013697980],[3566859630,3666023790]]],[[[250363663,299945743],[1490819486,1589983646],[1296235663,1345817743]],[[972531806,1071695966],[3990324412,4188652732],[3129352286,3228516446]],[[736113103,785695183],[2527394846,2626559006],[1847061583,1896643663]]]]

private theorem identity_0754 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(16272521 / 38563840 : ℝ)) =
      tensor4 coefficients_0754 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0754, p_variance] <;> ring

private theorem negative_0754 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0754 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0754] at hp
  linarith only [hp]

private theorem node_0750 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0751 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0754 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0728 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0729 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0750 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0755 : List (List (List (List ℕ))) :=
  [[[[10181299,31983398,19865299],[4080379,19781558,13764379]],[[16282219,44185238,25966219],[10181299,31983398,19865299]]],[[[18657720,60557040,38025720],[6165360,35572320,25533360]],[[31150080,85541760,50518080],[18657720,60557040,38025720]]],[[[8386642,28394084,18070642],[1995202,15611204,11679202]],[[14778082,41176964,24462082],[8386642,28394084,18070642]]]]

private theorem identity_0755 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(997601 / 15494400 : ℝ)) =
      tensor4 coefficients_0755 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0755, p_coupled] <;> ring

private theorem negative_0755 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0755 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0755] at hp
  linarith only [hp]

private theorem node_0727 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0728 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0755 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0756 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[27],[51]]],[[[9],[33]],[[33],[57]]]]

private theorem identity_0756 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0756 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0756, p_mass] <;> ring

private theorem negative_0756 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0756 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0756] at hp
  linarith only [hp]

private theorem node_0726 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0727 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_0756 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0757 : List (List (List (List ℕ))) :=
  [[[[3],[51]],[[27],[75]]],[[[9],[57]],[[33],[81]]]]

private theorem identity_0757 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0757 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0757, p_mass] <;> ring

private theorem negative_0757 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0757 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0757] at hp
  linarith only [hp]

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 4 : ℝ)
  · exact node_0726 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_0757 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0758 : List (List (List (List ℕ))) :=
  [[[[9917059,27581318,13790659],[4106659,15960518,7980259]],[[15727459,39202118,19601059],[9917059,27581318,13790659]]],[[[18308798,52111996,26055998],[6106958,27708316,13854158]],[[30510638,76515676,38257838],[18308798,52111996,26055998]]],[[[8212181,24171562,12085781],[1820741,11388682,5694341]],[[14603621,36954442,18477221],[8212181,24171562,12085781]]]]

private theorem identity_0758 (x0 x1 x2 x3 : ℝ) :
    (15494400 : ℝ)*(-p_coupled x0 x1 x2 x3-(1820741 / 15494400 : ℝ)) =
      tensor4 coefficients_0758 ((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0758, p_coupled] <;> ring

private theorem negative_0758 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0758 ((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0758] at hp
  linarith only [hp]

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.coupled) (negative_0758 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0759 : List (List (List (List ℕ))) :=
  [[[[3],[15]],[[15],[27]]],[[[6],[18]],[[18],[30]]]]

private theorem identity_0759 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 8 : ℝ)) =
      tensor4 coefficients_0759 ((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1)) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0759, p_mass] <;> ring

private theorem negative_0759 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0759 ((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0759] at hp
  linarith only [hp]

theorem exclude_02 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.mass) (negative_0759 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0760 : List (List (List (List ℕ))) :=
  [[[[140451169,78473569],[127668289,65690689]],[[268119458,144164258],[242553698,118598498]],[[92805889,30828289],[80023009,18045409]]],[[[269579946,145624746],[243433146,119477946]],[[513013092,265102692],[460719492,212809092]],[[173708346,49753146],[147561546,23606346]]],[[[128803959,66826359],[115440039,53462439]],[[244243998,120288798],[217516158,93560958]],[[80577639,18600039],[67213719,5236119]]]]

private theorem identity_0760 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(581791 / 6886400 : ℝ)) =
      tensor4 coefficients_0760 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0760, p_headsq] <;> ring

private theorem negative_0760 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0760 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0760] at hp
  linarith only [hp]

private def coefficients_0761 : List (List (List (List ℕ))) :=
  [[[[118855849,87867049],[106072969,75084169]],[[224928818,162951218],[199363058,137385458]],[[71210569,40221769],[58427689,27438889]]],[[[225808266,163830666],[199661466,137683866]],[[425469732,301514532],[373176132,249220932]],[[129936666,67959066],[103789866,41812266]]],[[[106627599,75638799],[93263679,62274879]],[[199891278,137913678],[173163438,111185838]],[[58401279,27412479],[45037359,14048559]]]]

private theorem identity_0761 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(1560951 / 6886400 : ℝ)) =
      tensor4 coefficients_0761 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0761, p_headsq] <;> ring

private theorem negative_0761 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0761 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0761] at hp
  linarith only [hp]

private def coefficients_0762 : List (List (List (List ℕ))) :=
  [[[[399893057,275937857],[348761537,224806337]],[[748654594,500744194],[646391554,398481154]],[[209311937,85356737],[158180417,34225217]]],[[[775979250,528068850],[672554130,424643730]],[[1448533380,952712580],[1241683140,745862340]],[[393654930,145744530],[290229810,42319410]]],[[[375761375,251806175],[323467775,199512575]],[[699229150,451318750],[594641950,346731550]],[[184018175,60062975],[131724575,7769375]]]]

private theorem identity_0762 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(310775 / 9916416 : ℝ)) =
      tensor4 coefficients_0762 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0762, p_headsq] <;> ring

private theorem negative_0762 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0762 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0762] at hp
  linarith only [hp]

private def coefficients_0763 : List (List (List (List ℕ))) :=
  [[[[161828297,99850697],[135681497,73703897]],[[310583194,186627994],[258289594,134334394]],[[131323697,69346097],[105176897,43199297]]],[[[311428344,187473144],[258553704,134598504]],[[596419368,348508968],[490670088,242759688]],[[250128624,126173424],[197253984,73298784]]],[[[149437638,87460038],[122709798,60732198]],[[285511356,161556156],[232055676,108100476]],[[118642518,56664918],[91914678,29937078]]]]

private theorem identity_0763 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(1663171 / 6886400 : ℝ)) =
      tensor4 coefficients_0763 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0763, p_headsq] <;> ring

private theorem negative_0763 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0763 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0763] at hp
  linarith only [hp]

private def coefficients_0764 : List (List (List (List ℕ))) :=
  [[[[157470497,95492897],[144397097,82419497]],[[267005194,143049994],[240858394,116903194]],[[92103497,30125897],[79030097,17052497]]],[[[302422224,178467024],[275984904,152029704]],[[508682328,260771928],[455807688,207897288]],[[171397704,47442504],[144960384,21005184]]],[[[144789318,82811718],[131425398,69447798]],[[241352316,117397116],[214624476,90669276]],[[79131798,17154198],[65767878,3790278]]]]

private theorem identity_0764 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(210571 / 6886400 : ℝ)) =
      tensor4 coefficients_0764 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0764, p_headsq] <;> ring

private theorem negative_0764 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0764 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0764] at hp
  linarith only [hp]

private def coefficients_0765 : List (List (List (List ℕ))) :=
  [[[[50112665,99694745],[556341730,655505890],[520174025,569756105]],[[565638370,664802530],[2076047780,2274376100],[1538299330,1637463490]],[[529470665,579052745],[1547595970,1646760130],[1032070265,1081652345]]],[[[198658790,297822950],[1317103900,1515432220],[1146335030,1245499190]],[[1335697180,1534025500],[4576043480,4972700120],[3296126140,3494454460]],[[1164928310,1264092470],[3314719420,3513047740],[2177681030,2276845190]]],[[[149238127,198820207],[762146174,861310334],[626853007,676435087]],[[771442814,870606974],[2502763708,2701092028],[1759210814,1858374974]],[[636149647,685731727],[1768507454,1867671614],[1146302767,1195884847]]]]

private theorem identity_0765 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(10022533 / 69414912 : ℝ)) =
      tensor4 coefficients_0765 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0765, p_variance] <;> ring

private theorem negative_0765 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0765 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0765] at hp
  linarith only [hp]

private theorem node_0769 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0764 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0765 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0768 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0763 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0769 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0767 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0762 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0768 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0766 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0761 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0767 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

theorem exclude_03 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0760 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0766 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part17
