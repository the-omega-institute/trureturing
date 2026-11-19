/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part13
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part13
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part13.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part13Node0556
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part13Node0535
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part13
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0513 : List (List (List (List ℕ))) :=
  [[[[417268129,293312929],[368460769,244505569]],[[670682978,422772578],[573068258,325157858]],[[218552449,94597249],[169745089,45789889]]],[[[812028666,564118266],[713251866,465341466]],[[1295769732,799948932],[1098216132,602395332]],[[414016266,166105866],[315239466,67329066]]],[[[394435719,270480519],[344466279,220511079]],[[624437118,376526718],[524498238,276587838]],[[195138999,71183799],[145169559,21214359]]]]

private theorem identity_0513 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(2357151 / 27545600 : ℝ)) =
      tensor4 coefficients_0513 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0513, p_headsq] <;> ring

private theorem negative_0513 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0513 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0513] at hp
  linarith only [hp]

private def coefficients_0514 : List (List (List (List ℕ))) :=
  [[[[4940406745309,2607817791709],[4021949844829,1689360891229]],[[10067029838138,5401851930938],[8230116037178,3564938129978]],[[3814541806429,1481952852829],[2896084905949,563495952349]]],[[[19669541264372,10411327376372],[16002251524532,6744037636532]],[[39811888721704,21295460945704],[32477309242024,13960881466024]],[[14934602145332,5676388257332],[11267312405492,2009098517492]]],[[[29349128528734,15569462787934],[23858457409534,10078791668734]],[[59002751069468,31443419587868],[48021408831068,20462077349468]],[[21902560561534,8122894820734],[16411889442334,2632223701534]]],[[[19451153573652,10336107941652],[15797847723492,6682802091492]],[[38837754184344,20607662920344],[31531142484024,13301051220024]],[[14259387442692,5144341810692],[10606081592532,1491035960532]]],[[[4831156156419,2570151330819],[3919688586099,1658683760499]],[[9579855183318,5057845532118],[7756920042678,3234910391478]],[[3476883812499,1215878986899],[2565416242179,304411416579]]]]

private theorem identity_0514 (x0 x1 x2 x3 : ℝ) :
    (6346506240000 : ℝ)*(-p_headbox x0 x1 x2 x3-(33823490731 / 705167360000 : ℝ)) =
      tensor4 coefficients_0514 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0514, p_headbox] <;> ring

private theorem negative_0514 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0514 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0514] at hp
  linarith only [hp]

private def coefficients_0515 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0515 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0515 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0515, p_qmass] <;> ring

private theorem negative_0515 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0515 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0515] at hp
  linarith only [hp]

private theorem node_0522 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0514 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0515 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0516 : List (List (List (List ℕ))) :=
  [[[[260900769281,164711534081],[223026257921,126837022721]],[[149415462401,53226227201],[111540951041,15351715841]]],[[[769838361635,482014387235],[656056784675,368232810275]],[[437278955555,149454981155],[323497378595,35673404195]]],[[[757007835275,469927592075],[643071701675,355991458475]],[[426349592075,139269348875],[312413458475,25333215275]]],[[[248071217375,152625713375],[210042149375,114596645375]],[[138487073375,43041569375],[100458005375,5012501375]]]]

private theorem identity_0516 (x0 x1 x2 x3 : ℝ) :
    (317325312000 : ℝ)*(-p_headcap x0 x1 x2 x3-(40100011 / 2538602496 : ℝ)) =
      tensor4 coefficients_0516 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0516, p_headcap] <;> ring

private theorem negative_0516 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headcap x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0516 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0516] at hp
  linarith only [hp]

private def coefficients_0517 : List (List (List (List ℕ))) :=
  [[[[63188059505213,25866636247613],[55840404301373,18518981043773]],[[117369199499386,42726352984186],[102673889091706,28031042576506]],[[48932814848573,11611391590973],[41585159644733,4263736387133]]],[[[251060778061300,102352220442100],[221696308694260,72987751075060]],[[465167960624360,167750845385960],[406439021890280,109021906651880]],[[193195041647860,44486484028660],[163830572280820,15122014661620]]],[[[373994018047150,151794653541550],[329987454563950,107788090058350]],[[691174886179100,246776157167900],[603161759212700,158763030201500]],[[285934082498350,63734717992750],[241927519015150,19728154509550]]],[[[247557728330500,99998979146500],[218247383420500,70688634236500]],[[456322277483000,161204779115000],[397701587663000,102584089295000]],[[188014100048500,40455350864500],[158703755138500,11145005954500]]],[[[61436425431875,24689906391875],[54115829841875,17369310801875]],[[112946145613750,39453107533750],[98304954433750,24811916353750]],[[46342240941875,9595721901875],[39021645351875,2275126311875]]]]

private theorem identity_0517 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(3640202099 / 162470559744 : ℝ)) =
      tensor4 coefficients_0517 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0517, p_headbox] <;> ring

private theorem negative_0517 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0517 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0517] at hp
  linarith only [hp]

private def coefficients_0518 : List (List (List (List ℕ))) :=
  [[[[214782088,264364168],[902530736,1001694896],[694721128,744303208]],[[893234096,992398256],[2748670432,2946998752],[1869381296,1968545456]],[[685424488,735006568],[1860084656,1959248816],[1181632648,1231214728]]],[[[531399144,630563304],[2012508168,2210836488],[1495053984,1594218144]],[[1993914888,2192243208],[5919787776,6316444416],[3953762808,4152091128]],[[1476460704,1575624864],[3935169528,4133497848],[2472653784,2571817944]]],[[[316963057,366545137],[1110669434,1209833594],[800678857,850260937]],[[1101372794,1200536954],[3172501348,3370829668],[2085073514,2184237674]],[[791382217,840964297],[2075776874,2174941034],[1291367137,1340949217]]]]

private theorem identity_0518 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(26847761 / 86768640 : ℝ)) =
      tensor4 coefficients_0518 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0518, p_variance] <;> ring

private theorem negative_0518 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0518 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0518] at hp
  linarith only [hp]

private theorem node_0526 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0517 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0518 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0525 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headcap) (negative_0516 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0526 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0519 : List (List (List (List ℕ))) :=
  [[[[31465607923283,13092348403283],[24145012333283,5771752813283]],[[63135342461566,26388823421566],[48494151281566,11747632241566]],[[29085994918283,10712735398283],[21765399328283,3392139808283]]],[[[125453505374632,52246803806632],[96199085564632,22992383996632]],[[251186164154264,104772761018264],[192677324534264,46263921398264]],[[115437966371632,42231264803632],[86183546561632,12976844993632]]],[[[187533326467448,78151663286648],[143694538284248,34312875103448]],[[374682745280896,155919418919296],[287005168914496,68241842552896]],[[171767622428648,62385959247848],[127928834245448,18547171064648]]],[[[124568449787712,51932190050112],[95371745261952,22735485524352]],[[248348136613344,103075617138144],[189954727561824,44682208086624]],[[113565212800032,40928953062432],[84368508274272,11732248536672]]],[[[31023019067832,12934980463032],[23731278505272,5643239900472]],[[61716209617584,25540132407984],[47132728492464,10956651282864]],[[28149560120952,10061521516152],[20857819558392,2769780953592]]]]

private theorem identity_0519 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(38469179911 / 705167360000 : ℝ)) =
      tensor4 coefficients_0519 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0519, p_headbox] <;> ring

private theorem negative_0519 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0519 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0519] at hp
  linarith only [hp]

private def coefficients_0520 : List (List (List (List ℕ))) :=
  [[[[61974305,161138465],[1975142050,2173470370],[1968947585,2068111745]],[[1026303730,1224632050],[5820070820,6216727460],[4905326770,5103655090]],[[978274385,1077438545],[3872818690,4071147010],[2950324145,3049488305]]],[[[321449030,519777350],[4360391980,4757048620],[4150502630,4348830950]],[[2455161820,2851818460],[12475464440,13268777720],[10243421980,10640078620]],[[2161602710,2359931030],[8170852300,8567508940],[6120809270,6319137590]]],[[[260166727,359330887],[2386633934,2584962254],[2182247047,2281411207]],[[1430242094,1628570414],[6658161628,7054818268],[5339479214,5537807534]],[[1184020327,1283184487],[4299417614,4497745934],[3171177127,3270341287]]]]

private theorem identity_0520 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(12394861 / 277659648 : ℝ)) =
      tensor4 coefficients_0520 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0520, p_variance] <;> ring

private theorem negative_0520 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0520 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0520] at hp
  linarith only [hp]

private theorem node_0527 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0519 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0520 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0524 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (21 / 32 : ℝ)
  · exact node_0525 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0527 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0521 : List (List (List (List ℕ))) :=
  [[[[31264768128053,12604056499253],[23917112924213,5256401295413]],[[64019267036266,26697843778666],[49323956628586,12002533370986]],[[27506173762613,8845462133813],[20158518558773,1497806929973]]],[[[124951825085140,50597546275540],[95587355718100,21233076908500]],[[254774336502440,106065778883240],[196045397768360,47336840149160]],[[108910370502100,34556091692500],[79545901135060,5191622325460]]],[[[187198242913150,76098560660350],[143191679429950,32091997177150]],[[380076907178300,157877542672700],[292063780211900,69864415706300]],[[161631878631550,50532196378750],[117625315148350,6525632895550]]],[[[124599859280500,50820484688500],[95289514370500,21510139778500]],[[251907437591000,104348688407000],[193286747771000,45727998587000]],[[106557129206500,32777754614500],[77246784296500,3467409704500]]],[[[31088669916875,12715410396875],[23768074326875,5394814806875]],[[62585593063750,25839074023750],[47944401883750,11197882843750]],[[26329443906875,7956184386875],[19008848316875,635588796875]]]]

private theorem identity_0521 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1016942075 / 162470559744 : ℝ)) =
      tensor4 coefficients_0521 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0521, p_headbox] <;> ring

private theorem negative_0521 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0521 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0521] at hp
  linarith only [hp]

private def coefficients_0522 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0522 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0522 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0522, p_qmass] <;> ring

private theorem negative_0522 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0522 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0522] at hp
  linarith only [hp]

private theorem node_0531 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0521 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0522 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0523 : List (List (List (List ℕ))) :=
  [[[[11224408,60806488],[479146256,578310416],[474894328,524476408]],[[472173776,571337936],[1874011552,2072339872],[1415782736,1514946896]],[[467921848,517503928],[1408810256,1507974416],[947860888,997442968]]],[[[120507024,219671184],[1158185688,1356514008],[1051623624,1150787784]],[[1144240728,1342569048],[4155362976,4552019616],[3039012168,3237340488]],[[1037678664,1136842824],[3025067208,3223395528],[2001333504,2100497664]]],[[[109628617,159210697],[679731434,778895594],[577075297,626657377]],[[672758954,771923114],[2282735428,2481063748],[1623921434,1723085594]],[[570102817,619684897],[1616948954,1716113114],[1053818617,1103400697]]]]

private theorem identity_0523 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(1403051 / 86768640 : ℝ)) =
      tensor4 coefficients_0523 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0523, p_variance] <;> ring

private theorem negative_0523 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0523 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0523] at hp
  linarith only [hp]

private theorem node_0530 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0531 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0523 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0524 : List (List (List (List ℕ))) :=
  [[[[6576088,56158168],[931195376,1030359536],[952509208,1002091288]],[[460552976,559717136],[2789730592,2988058912],[2384957456,2484121616]],[[460949368,510531448],[1872480176,1971644336],[1439420728,1489002808]]],[[[111210384,210374544],[2066060688,2264389008],[2010630144,2109794304]],[[1120999128,1319327448],[5994354576,6391011216],[4984915128,5183243448]],[[1023733704,1122897864],[3956183808,4154512128],[2988229944,3087394104]]],[[[104980297,154562377],[1135557314,1234721474],[1058466937,1108049017]],[[661138154,760302314],[3206007988,3404336308],[2600649674,2699813834]],[[563130337,612712417],[2084395634,2183559794],[1549155217,1598737297]]]]

private theorem identity_0524 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(822011 / 86768640 : ℝ)) =
      tensor4 coefficients_0524 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0524, p_variance] <;> ring

private theorem negative_0524 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0524 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0524] at hp
  linarith only [hp]

private theorem node_0529 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0530 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0524 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0525 : List (List (List (List ℕ))) :=
  [[[[15791422913843,6604793153843],[12131125118843,2944495358843]],[[31786972442686,13413712922686],[24466376852686,6093117332686]],[[13411809908843,4225180148843],[9751512113843,564882353843]]],[[[63043101848872,26439751064872],[48415891943872,11812541159872]],[[126365357102744,53158655534744],[97110937292744,23904235724744]],[[53027562845872,16424212061872],[38400352940872,1797002156872]]],[[[94346110350008,39655278759608],[72426716258408,17735884668008]],[[188308313046016,78926649865216],[144469524862816,35087861682016]],[[78580406311208,23889574720808],[56661012219608,1970180629208]]],[[[62728488092352,26410358223552],[48130135829472,11812005960672]],[[124668213222624,52031953485024],[95471508696864,22835248959264]],[[51725251104672,15407121235872],[37126898841792,808768972992]]],[[[15634054973592,6590035671192],[11988184692312,2944165389912]],[[30938281429104,12850242824304],[23646540866544,5558502261744]],[[12760596026712,3716576724312],[9114725745432,70706443032]]]]

private theorem identity_0525 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(982033931 / 705167360000 : ℝ)) =
      tensor4 coefficients_0525 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0525, p_headbox] <;> ring

private theorem negative_0525 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0525 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0525] at hp
  linarith only [hp]

private def coefficients_0526 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0526 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0526 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0526, p_qmass] <;> ring

private theorem negative_0526 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0526 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0526] at hp
  linarith only [hp]

private theorem node_0534 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0525 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0526 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0527 : List (List (List (List ℕ))) :=
  [[[[120853025,220017185],[1162654450,1360982770],[1055746385,1154910545]],[[1148709490,1347037810],[4171854020,4568510660],[3051034450,3249362770]],[[1041801425,1140965585],[3037089490,3235417810],[2009233025,2108397185]]],[[[439206470,637534790],[2727863260,3124519900],[2316546710,2514875030]],[[2699973340,3096629980],[9163923800,9957237080],[6519730300,6916386940]],[[2288656790,2486985110],[6491840380,6888497020],[4231073510,4429401830]]],[[[319045447,418209607],[1566592814,1764921134],[1261492327,1360656487]],[[1552647854,1750976174],[4994837788,5391494428],[3470079854,3668408174]],[[1247547367,1346711527],[3456134894,3654463214],[2222532487,2321696647]]]]

private theorem identity_0527 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(24170605 / 277659648 : ℝ)) =
      tensor4 coefficients_0527 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0527, p_variance] <;> ring

private theorem negative_0527 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0527 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0527] at hp
  linarith only [hp]

private theorem node_0533 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0534 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0527 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0528 : List (List (List (List ℕ))) :=
  [[[[111556385,210720545],[2074306210,2272634530],[2018529665,2117693825]],[[1125467890,1323796210],[6018399140,6415055780],[5004490930,5202819250]],[[1027856465,1127020625],[3971982850,4170311170],[2999906225,3099070385]]],[[[420613190,618941510],[4558720300,4955376940],[4249666790,4447995110]],[[2653490140,3050146780],[12872121080,13665434360],[10441750300,10838406940]],[[2260766870,2459095190],[8369180620,8765837260],[6219973430,6418301750]]],[[[309748807,408912967],[2485798094,2684126414],[2231829127,2330993287]],[[1529406254,1727734574],[6856489948,7253146588],[5438643374,5636971694]],[[1233602407,1332766567],[4398581774,4596910094],[3220759207,3319923367]]]]

private theorem identity_0528 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(22311277 / 277659648 : ℝ)) =
      tensor4 coefficients_0528 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0528, p_variance] <;> ring

private theorem negative_0528 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0528 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0528] at hp
  linarith only [hp]

private theorem node_0532 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0533 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0528 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0528 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (21 / 32 : ℝ)
  · exact node_0529 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0532 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0523 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0524 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0528 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0521 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0522 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0523 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0520 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0513 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0521 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0519 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0520 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact SixRowMiddleCertificate.Subtrees.Part13Node0535.exclude x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0519 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact SixRowMiddleCertificate.Subtrees.Part13Node0556.exclude x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part13
