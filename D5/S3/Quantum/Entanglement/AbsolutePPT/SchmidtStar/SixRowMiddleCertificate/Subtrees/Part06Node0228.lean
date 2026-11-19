/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part06Node0228
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part06Node0228
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part06.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part06Node0228.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part06Node0228
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0222 : List (List (List (List ℕ))) :=
  [[[[451429513,327474313],[409594633,285639433]],[[742491986,494581586],[658822226,410911826]],[[256200073,132244873],[214365193,90409993]]],[[[883087170,635176770],[798255330,550344930]],[[1444859220,949038420],[1275195540,779374740]],[[492047250,244136850],[407215410,159305010]]],[[[431332839,307377639],[388335879,264380679]],[[701717598,453807198],[615723678,367813278]],[[235522359,111567159],[192525399,68570199]]]]

private theorem identity_0222 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(7618911 / 27545600 : ℝ)) =
      tensor4 coefficients_0222 ((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0222, p_headsq] <;> ring

private theorem negative_0222 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0222 ((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0222] at hp
  linarith only [hp]

private def coefficients_0223 : List (List (List (List ℕ))) :=
  [[[[1084240529,836330129],[1000570769,752660369]],[[1708297378,1212476578],[1540957858,1045137058]],[[589194449,341284049],[505524689,257614289]]],[[[2127775266,1631954466],[1959273666,1463452866]],[[3334602132,2342960532],[2997598932,2005957332]],[[1137102066,641281266],[968600466,472779666]]],[[[1043209919,795299519],[958378079,710467679]],[[1625655118,1129834318],[1455991438,960170638]],[[547582799,299672399],[462750959,214840559]]]]

private theorem identity_0223 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(214840559 / 991641600 : ℝ)) =
      tensor4 coefficients_0223 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0223, p_headsq] <;> ring

private theorem negative_0223 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0223 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0223] at hp
  linarith only [hp]

private def coefficients_0224 : List (List (List (List ℕ))) :=
  [[[[59241824782589,14673484712189],[51720917395709,7152577325309]],[[121447864635898,32311184495098],[106406049862138,17269369721338]],[[55938617030909,11370276960509],[48417709644029,3849369573629]]],[[[236650941021172,59008264797172],[206569282361332,28926606137332]],[[484091227747304,128805875299304],[423927910427624,68642557979624]],[[222459285382132,44816609158132],[192377626722292,14734950498292]]],[[[354448792059694,88928572616494],[309330362053294,43810142610094]],[[723486011056988,192445572170588],[633249151044188,102208712157788]],[[331698438138094,66178218694894],[286580008131694,21059788688494]]],[[[235912001689732,59526231193732],[205836482879572,29450712383572]],[[480489692624504,127718151632504],[420338655004184,67567114012184]],[[219773441958772,43387671462772],[189697923148612,13312152652612]]],[[[58872322461059,14932435254659],[51354482384339,7414595177939]],[[119647037863798,31767263450998],[104611357710358,16731583297558]],[[54595668764339,10655781557939],[47077828687619,3137941481219]]]]

private theorem identity_0224 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(3137941481219 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0224 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0224, p_headbox] <;> ring

private theorem negative_0224 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0224 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0224] at hp
  linarith only [hp]

private def coefficients_0225 : List (List (List (List ℕ))) :=
  [[[[70274752,119856832],[596084864,695249024],[532782592,582364672]],[[591436544,690600704],[2110212928,2308541248],[1532721344,1631885504]],[[528134272,577716352],[1528073024,1627237184],[1006911232,1056493312]]],[[[241633968,340798128],[1398115416,1596443736],[1170426408,1269590568]],[[1388818776,1587147096],[4639870752,5036527392],[3278941896,3477270216]],[[1161129768,1260293928],[3269645256,3467973576],[2122460448,2221624608]]],[[[171705217,221287297],[802722554,901886714],[637989817,687571897]],[[798074234,897238394],[2531041828,2729370148],[1746912554,1846076714]],[[633341497,682923577],[1742264234,1841428394],[1115895217,1165477297]]]]

private theorem identity_0225 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(1098043 / 10846080 : ℝ)) =
      tensor4 coefficients_0225 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0225, p_variance] <;> ring

private theorem negative_0225 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0225 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0225] at hp
  linarith only [hp]

private theorem node_0234 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0224 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0225 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0233 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0223 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0234 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0226 : List (List (List (List ℕ))) :=
  [[[[532460801,408505601],[490044881,366089681]],[[834539242,586628842],[749707402,501797002]],[[284647241,160692041],[242231321,118276121]]],[[[1044243888,796333488],[958831008,710920608]],[[1627432536,1131611736],[1456606776,960785976]],[[548326248,300415848],[462913368,215002968]]],[[[511620678,387665478],[468623718,344668518]],[[792568476,544658076],[706574556,458664156]],[[263516598,139561398],[220519638,96564438]]]]

private theorem identity_0226 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(5364691 / 27545600 : ℝ)) =
      tensor4 coefficients_0226 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0226, p_headsq] <;> ring

private theorem negative_0226 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0226 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0226] at hp
  linarith only [hp]

private def coefficients_0227 : List (List (List (List ℕ))) :=
  [[[[29638530148427,7668586545227],[25879610110067,3909666506867]],[[60228256767694,16288369561294],[52710416690974,8770529484574]],[[27500203300067,5530259696867],[23741283261707,1771339658507]]],[[[118342764670960,30776101093360],[103309163769160,15742500191560]],[[239962256486120,64828929330920],[209895054682520,34761727527320]],[[109305429749560,21738766171960],[94271828847760,6705165270160]]],[[[177170474000744,46289029290344],[154623734507384,23742289796984]],[[358466809035328,96703919614528],[313373330048608,51610440627808]],[[162891131872184,32009687161784],[140344392378824,9462947668424]]],[[[117866738518944,30924065418144],[102838379469504,15895706368704]],[[237959809657248,64074463455648],[207903091558368,34017745356768]],[[107866757733504,20924084632704],[92838398684064,5895725583264]]],[[[29400497336952,7742548972152],[25644196917432,3986248552632]],[[59226996932784,15911100203184],[51714396093744,8398499364144]],[[26780850607032,5122902242232],[23024550187512,1366601822712]]]]

private theorem identity_0227 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(18980580871 / 705167360000 : ℝ)) =
      tensor4 coefficients_0227 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0227, p_headbox] <;> ring

private theorem negative_0227 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0227 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0227] at hp
  linarith only [hp]

private def coefficients_0228 : List (List (List (List ℕ))) :=
  [[[[241979969,341144129],[1402584178,1600912498],[1174549169,1273713329]],[[1393287538,1591615858],[4656361796,5053018436],[3290964178,3489292498]],[[1165252529,1264416689],[3281667538,3479995858],[2130359969,2229524129]]],[[[687512870,885841190],[3219827740,3616484380],[2560204790,2758533110]],[[3201234460,3597891100],[10157149400,10950462680],[7011694780,7408351420]],[[2541611510,2739939830],[6993101500,7389758140],[4479379910,4677708230]]],[[[446224903,545389063],[1818627566,2016955886],[1386347623,1485511783]],[[1809330926,2007659246],[5503555612,5900212252],[3722114606,3920442926]],[[1377050983,1476215143],[3712817966,3911146286],[2349711943,2448876103]]]]

private theorem identity_0228 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(34568567 / 198328320 : ℝ)) =
      tensor4 coefficients_0228 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0228, p_variance] <;> ring

private theorem negative_0228 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0228 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0228] at hp
  linarith only [hp]

private theorem node_0236 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0227 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0228 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0235 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0226 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0236 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0232 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (9 / 32 : ℝ)
  · exact node_0233 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0235 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0229 : List (List (List (List ℕ))) :=
  [[[[960285329,712374929],[876615569,628705169]],[[1460386978,964566178],[1293047458,797226658]],[[465239249,217328849],[381569489,133659089]]],[[[1879864866,1384044066],[1711363266,1215542466]],[[2838781332,1847139732],[2501778132,1510136532]],[[889191666,393370866],[720690066,224869266]]],[[[919254719,671344319],[834422879,586512479]],[[1377744718,881923918],[1208081038,712260238]],[[423627599,175717199],[338795759,90885359]]]]

private theorem identity_0229 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(90885359 / 991641600 : ℝ)) =
      tensor4 coefficients_0229 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0229, p_headsq] <;> ring

private theorem negative_0229 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0229 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0229] at hp
  linarith only [hp]

private def coefficients_0230 : List (List (List (List ℕ))) :=
  [[[[107052299,431026198,308479499],[23382539,263686678,224809739]],[[148887179,514695958,350314379],[65217419,347356438,266644619]]],[[[201869766,837582732,604724166],[33368166,500579532,436222566]],[[286120566,1006084332,688974966],[117618966,669081132,520473366]]],[[[94637909,406197418,296065109],[9806069,236533738,211233269]],[[137053829,491029258,338481029],[52221989,321365578,253649189]]]]

private theorem identity_0230 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(9806069 / 991641600 : ℝ)) =
      tensor4 coefficients_0230 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0230, p_coupled] <;> ring

private theorem negative_0230 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0230 ((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0230] at hp
  linarith only [hp]

private theorem node_0238 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0229 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0230 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0231 : List (List (List (List ℕ))) :=
  [[[[470483201,346528001],[428067281,304112081]],[[710584042,462673642],[625752202,377841802]],[[222669641,98714441],[180253721,56298521]]],[[[920288688,672378288],[834875808,586965408]],[[1379522136,883701336],[1208696376,712875576]],[[424371048,176460648],[338958168,91047768]]],[[[449643078,325687878],[406646118,282690918]],[[668613276,420702876],[582619356,334708956]],[[201538998,77583798],[158542038,34586838]]]]

private theorem identity_0231 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1921491 / 27545600 : ℝ)) =
      tensor4 coefficients_0231 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0231, p_headsq] <;> ring

private theorem negative_0231 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0231 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0231] at hp
  linarith only [hp]

private def coefficients_0232 : List (List (List (List ℕ))) :=
  [[[[50802851,210066502,151516451],[8386931,125234662,109100531]],[[72010811,252482422,172724411],[29594891,167650582,130308491]]],[[[95308728,407539056,296735928],[9895848,236713296,211323048]],[[138015168,492951936,339442368],[52602288,322126176,254029488]]],[[[44416098,197292996,145129698],[1419138,111299076,102132738]],[[65914578,240289956,166628178],[22917618,154296036,123631218]]]]

private theorem identity_0232 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(78841 / 27545600 : ℝ)) =
      tensor4 coefficients_0232 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0232, p_coupled] <;> ring

private theorem negative_0232 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0232 ((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0232] at hp
  linarith only [hp]

private theorem node_0239 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0231 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0232 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0237 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (9 / 32 : ℝ)
  · exact node_0238 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0239 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0231 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0232 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0237 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0233 : List (List (List (List ℕ))) :=
  [[[[17859208,42650248],[262324016,311906096],[251437288,276228328]],[[262324016,311906096],[994128352,1093292512],[745749296,795331376]],[[251437288,276228328],[745749296,795331376],[501284488,526075528]]],[[[86260648,135842728],[629509256,728673416],[557193568,606775648]],[[629509256,728673416],[2205532672,2403860992],[1603913336,1703077496]],[[557193568,606775648],[1603913336,1703077496],[1060664728,1110246808]]],[[[68747441,93538481],[367877242,417459322],[306102281,330893321]],[[367877242,417459322],[1212788324,1311952484],[858856042,908438122]],[[306102281,330893321],[858856042,908438122],[559726241,584517281]]]]

private theorem identity_0233 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(2232401 / 21692160 : ℝ)) =
      tensor4 coefficients_0233 ((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0233, p_variance] <;> ring

private theorem negative_0233 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0233 ((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0233] at hp
  linarith only [hp]

private theorem node_0230 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0231 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0233 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0229 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0222 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0230 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0234 : List (List (List (List ℕ))) :=
  [[[[221288777,159311177],[199790297,137812697]],[[362103514,238148314],[319106554,195151354]],[[123383537,61405937],[101885057,39907457]]],[[[432366808,308411608],[388788808,264833608]],[[703495016,455584616],[616339016,368428616]],[[236265808,112310608],[192687808,68732608]]],[[[210915622,148938022],[188836102,126858502]],[[341066684,217111484],[296907644,172952444]],[[112719862,50742262],[90640342,28662742]]]]

private theorem identity_0234 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(14331371 / 61977600 : ℝ)) =
      tensor4 coefficients_0234 ((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0234, p_headsq] <;> ring

private theorem negative_0234 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0234 ((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0234] at hp
  linarith only [hp]

private def coefficients_0235 : List (List (List (List ℕ))) :=
  [[[[1045277857,797367457],[959283937,711373537]],[[1629209954,1133389154],[1457222114,961401314]],[[549069697,301159297],[463075777,215165377]]],[[[2048550650,1552729850],[1875400730,1379579930]],[[3173828740,2182187140],[2827528900,1835887300]],[[1055553290,559732490],[882403370,386582570]]],[[[1002947975,755037575],[915791975,667881575]],[[1543969150,1048148350],[1369657150,873836350]],[[506158775,258248375],[419002775,171092375]]]]

private theorem identity_0235 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(6843695 / 39665664 : ℝ)) =
      tensor4 coefficients_0235 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0235, p_headsq] <;> ring

private theorem negative_0235 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0235 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0235] at hp
  linarith only [hp]

private def coefficients_0236 : List (List (List (List ℕ))) :=
  [[[[59254972207453,15939075477853],[51742371368413,8426474638813]],[[119361948932666,32730155473466],[104336747254586,17704953795386]],[[54015678747613,10699782018013],[46503077908573,3187181178973]]],[[[236490390487540,63848562852340],[206446301874100,33804474238900]],[[475344151878440,130060496608040],[415255974651560,69972319381160]],[[214576004379700,41934176744500],[184531915766260,11890088131060]]],[[[353887823149150,95855489427550],[308832232618750,50799898897150]],[[709759485359900,193694817916700],[619648304299100,103583636855900]],[[319585865281150,61553531559550],[274530274750750,16497941029150]]],[[[235324277908500,63921506452500],[205294954102500,33892182646500]],[[470934151503000,128128608591000],[410875503891000,68069960979000]],[[211506358858500,40103587402500],[181477035052500,10074263596500]]],[[[58671869631875,15975500991875],[51166648581875,8470279941875]],[[117156862273750,31764124993750],[102146420173750,16753682893750]],[[52480815801875,9784447161875],[44975594751875,2279226111875]]]]

private theorem identity_0236 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(3646761779 / 162470559744 : ℝ)) =
      tensor4 coefficients_0236 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0236, p_headbox] <;> ring

private theorem negative_0236 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0236 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0236] at hp
  linarith only [hp]

private def coefficients_0237 : List (List (List (List ℕ))) :=
  [[[[172051218,221633298],[807191316,906355476],[642112578,691694658]],[[802542996,901707156],[2547532872,2745861192],[1758934836,1858098996]],[[637464258,687046338],[1754286516,1853450676],[1123794738,1173376818]]],[[[446570904,545735064],[1823096328,2021424648],[1390470384,1489634544]],[[1813799688,2012128008],[5520046656,5916703296],[3734136888,3932465208]],[[1381173744,1480337904],[3724840248,3923168568],[2357611464,2456775624]]],[[[274865687,324447767],[1016597014,1115761174],[748703807,798285887]],[[1011948694,1111112854],[2973897788,3172226108],[1975894054,2075058214]],[[744055487,793637567],[1971245734,2070409894],[1234162727,1283744807]]]]

private theorem identity_0237 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(9558401 / 38563840 : ℝ)) =
      tensor4 coefficients_0237 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0237, p_variance] <;> ring

private theorem negative_0237 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0237 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0237] at hp
  linarith only [hp]

private theorem node_0245 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0236 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0237 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0244 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0235 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0245 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0238 : List (List (List (List ℕ))) :=
  [[[[512654647,388699447],[469076647,345121447]],[[794345894,546435494],[707189894,459279494]],[[264260047,140304847],[220682047,96726847]]],[[[1003981944,756071544],[916244904,668334504]],[[1545746568,1049925768],[1370272488,874451688]],[[506902224,258991824],[419165184,171254784]]],[[[491164888,367209688],[447005848,323050648]],[[751075856,503165456],[662757776,414847376]],[[242479768,118524568],[198320728,74365528]]]]

private theorem identity_0238 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(9295691 / 61977600 : ℝ)) =
      tensor4 coefficients_0238 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0238, p_headsq] <;> ring

private theorem negative_0238 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0238 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0238] at hp
  linarith only [hp]

private def coefficients_0239 : List (List (List (List ℕ))) :=
  [[[[29587671831043,8239487511043],[25835061306043,4486876986043]],[[59081905167086,16385536527086],[51576684117086,8880315477086]],[[26492144916043,5143960596043],[22739534391043,1391350071043]]],[[[118032287633672,32948198801672],[103026065336672,17941976504672]],[[235174269464344,65006091800344],[205161824870344,34993647206344]],[[105177031838672,20092943006672],[90170809541672,5086720709672]]],[[[176543935522208,49379659349408],[154041459075008,26877182902208]],[[350980479637216,96651927291616],[305975526742816,51646974397216]],[[156554067778208,29389791605408],[134051591331008,6887315158208]]],[[[117341645773952,32872622644352],[102344915055872,17875891926272]],[[232765678263424,63827632004224],[202772216827264,33834170568064]],[[103545576111872,19076552982272],[88548845393792,4079822264192]]],[[[29242324350592,8201672881792],[25494458307712,4453806838912]],[[57877559515904,15796256578304],[50381827430144,8300524492544]],[[25676393552512,4635742083712],[21928527509632,887876040832]]]]

private theorem identity_0239 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6936531569 / 396656640000 : ℝ)) =
      tensor4 coefficients_0239 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0239, p_headbox] <;> ring

private theorem negative_0239 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0239 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0239] at hp
  linarith only [hp]

private def coefficients_0240 : List (List (List (List ℕ))) :=
  [[[[446916905,546081065],[1827565090,2025893410],[1394593145,1493757305]],[[1818268450,2016596770],[5536537700,5933194340],[3746159170,3944487490]],[[1385296505,1484460665],[3736862530,3935190850],[2365510985,2464675145]]],[[[1100154750,1298483070],[4075325580,4471982220],[3003060750,3201389070]],[[4056732300,4453388940],[11928573240,12721886520],[7927620780,8324277420]],[[2984467470,3182795790],[7909027500,8305684140],[4952449950,5150778270]]],[[[653929847,753094007],[2249144494,2447472814],[1609159607,1708323767]],[[2239847854,2438176174],[6394803548,6791460188],[4182845614,4381173934]],[[1599862967,1699027127],[4173548974,4371877294],[2587630967,2686795127]]]]

private theorem identity_0240 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(89383381 / 277659648 : ℝ)) =
      tensor4 coefficients_0240 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0240, p_variance] <;> ring

private theorem negative_0240 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0240 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0240] at hp
  linarith only [hp]

private theorem node_0247 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0239 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0240 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0246 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0238 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0247 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0243 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 32 : ℝ)
  · exact node_0244 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0246 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0241 : List (List (List (List ℕ))) :=
  [[[[921322657,673412257],[835328737,587418337]],[[1381299554,885478754],[1209311714,713490914]],[[425114497,177204097],[339120577,91210177]]],[[[1800640250,1304819450],[1627490330,1131669530]],[[2678007940,1686366340],[2331708100,1340066500]],[[807642890,311822090],[634492970,138672170]]],[[[878992775,631082375],[791836775,543926375]],[[1296058750,800237950],[1121746750,625925950]],[[382203575,134293175],[295047575,47137175]]]]

private theorem identity_0241 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(1885487 / 39665664 : ℝ)) =
      tensor4 coefficients_0241 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0241, p_headsq] <;> ring

private theorem negative_0241 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0241 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0241] at hp
  linarith only [hp]

private def coefficients_0242 : List (List (List (List ℕ))) :=
  [[[[74190547,365302694,275617747],[31193587,279308774,232620787]],[[117187507,451296614,318614707],[74190547,365302694,275617747]]],[[[135428030,704699260,538282430],[48853070,531549340,451707470]],[[222002990,877849180,624857390],[135428030,704699260,538282430]]],[[[61057925,339037450,262485125],[17479925,251881450,218907125]],[[104635925,426193450,306063125],[61057925,339037450,262485125]]]]

private theorem identity_0242 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(699197 / 39665664 : ℝ)) =
      tensor4 coefficients_0242 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0242, p_coupled] <;> ring

private theorem negative_0242 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0242 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0242] at hp
  linarith only [hp]

private def coefficients_0243 : List (List (List (List ℕ))) :=
  [[[[196842258,246424338],[856773396,955937556],[666903618,716485698]],[[852125076,951289236],[2646697032,2845025352],[1808516916,1907681076]],[[662255298,711837378],[1803868596,1903032756],[1148585778,1198167858]]],[[[496152984,595317144],[1922260488,2120588808],[1440052464,1539216624]],[[1912963848,2111292168],[5718374976,6115031616],[3833301048,4031629368]],[[1430755824,1529919984],[3824004408,4022332728],[2407193544,2506357704]]],[[[299656727,349238807],[1066179094,1165343254],[773494847,823076927]],[[1061530774,1160694934],[3073061948,3271390268],[2025476134,2124640294]],[[768846527,818428607],[2020827814,2119991974],[1258953767,1308535847]]]]

private theorem identity_0243 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(10935681 / 38563840 : ℝ)) =
      tensor4 coefficients_0243 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0243, p_variance] <;> ring

private theorem negative_0243 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0243 ((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0243] at hp
  linarith only [hp]

private theorem node_0250 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0242 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0243 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0249 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0241 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0250 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0244 : List (List (List (List ℕ))) :=
  [[[[450677047,326721847],[407099047,283143847]],[[670390694,422480294],[583234694,335324294]],[[202282447,78327247],[158704447,34749247]]],[[[880026744,632116344],[792289704,544379304]],[[1297836168,802015368],[1122362088,626541288]],[[382947024,135036624],[295209984,47299584]]],[[[429187288,305232088],[385028248,261073048]],[[627120656,379210256],[538802576,290892176]],[[180502168,56546968],[136343128,12387928]]]]

private theorem identity_0244 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1548491 / 61977600 : ℝ)) =
      tensor4 coefficients_0244 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0244, p_headsq] <;> ring

private theorem negative_0244 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0244 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0244] at hp
  linarith only [hp]

private def coefficients_0245 : List (List (List (List ℕ))) :=
  [[[[36605825,135769985],[1884894370,2083222690],[1904068385,2003232545]],[[965108050,1163436370],[5618658020,6015314660],[4765109650,4963437970]],[[942447185,1041611345],[3761653570,3959981890],[2874986225,2974150385]]],[[[271979070,470307390],[4182430620,4579087260],[4022011230,4220339550]],[[2335304460,2731961100],[12077706840,12871020120],[9965521740,10362178380]],[[2091215310,2289543630],[7951056060,8347712700],[5971400430,6169728750]]],[[[236065247,335229407],[2298920254,2497248574],[2118634847,2217799007]],[[1371580414,1569908734],[6461816828,6858473468],[5201796094,5400124414]],[[1149460127,1248624287],[4190786494,4389114814],[3097106207,3196270367]]]]

private theorem identity_0245 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(7321165 / 277659648 : ℝ)) =
      tensor4 coefficients_0245 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0245, p_variance] <;> ring

private theorem negative_0245 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0245 ((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0245] at hp
  linarith only [hp]

private theorem node_0251 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0244 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0245 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0248 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 32 : ℝ)
  · exact node_0249 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0251 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0242 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0243 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0248 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0246 : List (List (List (List ℕ))) :=
  [[[[86606649,136188729],[633978018,733142178],[561316329,610898409]],[[633978018,733142178],[2222023716,2420352036],[1615935618,1715099778]],[[561316329,610898409],[1615935618,1715099778],[1068564249,1118146329]]],[[[275681766,374845926],[1480446492,1678774812],[1232654646,1331818806]],[[1480446492,1678774812],[4884135384,5280792024],[3459468732,3657797052]],[[1232654646,1331818806],[3459468732,3657797052],[2254704006,2353868166]]],[[[189767119,239349199],[847852478,947016638],[672030319,721612399]],[[847852478,947016638],[2664879676,2863207996],[1844917118,1944081278]],[[672030319,721612399],[1844917118,1944081278],[1186831759,1236413839]]]]

private theorem identity_0246 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(9622961 / 38563840 : ℝ)) =
      tensor4 coefficients_0246 ((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0246, p_variance] <;> ring

private theorem negative_0246 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0246 ((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0246] at hp
  linarith only [hp]

private theorem node_0241 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0242 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0246 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0240 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0234 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0241 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 16 : ℝ)
  · exact node_0229 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0240 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part06Node0228
