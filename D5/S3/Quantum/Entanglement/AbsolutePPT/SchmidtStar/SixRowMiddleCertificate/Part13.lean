/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part13
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part13
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part13.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
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

private def coefficients_0529 : List (List (List (List ℕ))) :=
  [[[[203524151,141546551],[178539431,116561831]],[[324831142,200875942],[274861702,150906502]],[[103875791,41898191],[78891071,16913471]]],[[[395469688,271514488],[344919208,220964008]],[[626214536,378304136],[525113576,277203176]],[[195882448,71927248],[145331968,21376768]]],[[[191783128,129805528],[166217368,104239768]],[[301058576,177103376],[249927056,125971856]],[[91844248,29866648],[66278488,4300888]]]]

private theorem identity_0529 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(537611 / 15494400 : ℝ)) =
      tensor4 coefficients_0529 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0529, p_headsq] <;> ring

private theorem negative_0529 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0529 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0529] at hp
  linarith only [hp]

private def coefficients_0530 : List (List (List (List ℕ))) :=
  [[[[2487558756227,1357056343427],[2031824971067,901322558267]],[[4933888947694,2672884122094],[4022421377374,1761416551774]],[[1810422584267,679920171467],[1354688799107,224186386307]]],[[[9886970550920,5400474064520],[8067753194720,3581256708320]],[[19476389065240,10503396092440],[15837954352840,6864961380040]],[[7065764240720,2579267754320],[5246546884520,760050398120]]],[[[14726861488544,8050107606944],[12003832635584,5327078753984]],[[28810143317728,15456635554528],[23364085611808,10010577848608]],[[10327607770784,3650853889184],[7604578917824,927825036224]]],[[[9742986198144,5326958242944],[7931642805504,3515614850304]],[[18926561029248,10094505118848],[15303874243968,6471818333568]],[[6699559106304,2283531151104],[4888215713664,472187758464]]],[[[2415534800512,1320266653312],[1963736689792,868468542592]],[[4658914421504,2468378127104],[3755318200064,1564781905664]],[[1627291288192,532023140992],[1175493177472,80225030272]]]]

private theorem identity_0530 (x0 x1 x2 x3 : ℝ) :
    (3173253120000 : ℝ)*(-p_headbox x0 x1 x2 x3-(626758049 / 24791040000 : ℝ)) =
      tensor4 coefficients_0530 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0530, p_headbox] <;> ring

private theorem negative_0530 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0530 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0530] at hp
  linarith only [hp]

private def coefficients_0531 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0531 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0531 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0531, p_qmass] <;> ring

private theorem negative_0531 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0531 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0531] at hp
  linarith only [hp]

private theorem node_0537 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0530 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0531 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0532 : List (List (List (List ℕ))) :=
  [[[[62730178045549,26554100835949],[48146696920429,11970619710829]],[[124800699054938,52448544635738],[95633736804698,23281582385498]],[[56983260151789,20807182942189],[42399779026669,6223701817069]]],[[[249967965149428,105831866947828],[191693525199988,47557426998388]],[[496236199933736,207964003530536],[379687320034856,91415123631656]],[[225999095974708,81862997773108],[167724656025268,23588557823668]]],[[[373455010197598,158100947656798],[286134341137438,70780278596638]],[[739775591764316,309067466682716],[565134253643996,134426128562396]],[[336036416521918,120682353981118],[248715747461758,33361684920958]]],[[[247926586066020,104922446750820],[189774632834820,46770493519620]],[[490044890022840,204036611392440],[373740983560440,87732704930040]],[[222008346865620,79004207550420],[163856393634420,20852254319220]]],[[[61709359564739,26099261798339],[47187116569379,11577018802979]],[[121704792322198,50484596789398],[92660306331478,21440110798678]],[[54987762759059,19377664992659],[40465519763699,4855421997299]]]]

private theorem identity_0532 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(4855421997299 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0532 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0532, p_headbox] <;> ring

private theorem negative_0532 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0532 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0532] at hp
  linarith only [hp]

private def coefficients_0533 : List (List (List (List ℕ))) :=
  [[[[80535258,130117338],[1094220756,1193384916],[1041575418,1091157498]],[[616024836,715188996],[3130888392,3329216712],[2570643396,2669807556]],[[542462058,592044138],[2050612596,2149776756],[1536040458,1585622538]]],[[[260512728,359676888],[2394879456,2593207776],[2190146568,2289310728]],[[1434710856,1633039176],[6682206192,7078862832],[5359055016,5557383336]],[[1188143088,1287307248],[4315216656,4513544976],[3182853408,3282017568]]],[[[180323471,229905551],[1301350702,1400514862],[1148917151,1198499231]],[[819378022,918542182],[3552701804,3751030124],[2789103622,2888267782]],[[646027031,695609111],[2265296062,2364460222],[1647158951,1696741031]]]]

private theorem identity_0533 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(4474181 / 38563840 : ℝ)) =
      tensor4 coefficients_0533 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0533, p_variance] <;> ring

private theorem negative_0533 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0533 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0533] at hp
  linarith only [hp]

private theorem node_0540 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0532 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0533 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0534 : List (List (List (List ℕ))) :=
  [[[[31228024467547,13422975584347],[23966902969867,6161854086667]],[[61599085531454,25988987765054],[47076842536094,11466744769694]],[[27867226064707,10062177181507],[20606104567027,2801055683827]]],[[[124367523966656,53429202558656],[95354528600816,24416207192816]],[[244783481758792,102906838942792],[186757491027112,44880848211112]],[[110440256344136,39501934936136],[81427260978296,10488939570296]]],[[[185700129788672,79714343267072],[142228739007872,36242952486272]],[[364690769902144,152719196858944],[277747988340544,65776415297344]],[[164086388883872,58100602362272],[120614998103072,14629211581472]]],[[[123209653200896,52832848848896],[94261366516736,23884562164736]],[[241427178061312,100673569357312],[183530604692992,42776995988992]],[[108320786748416,37943982396416],[79372500064256,8995695712256]]],[[[30649021207552,13124730852352],[23420251436032,5895961080832]],[[59920800978944,24872220268544],[45463261435904,10414680725504]],[[26807426440192,9283136084992],[19578656668672,2054366313472]]]]

private theorem identity_0534 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(2006217103 / 49582080000 : ℝ)) =
      tensor4 coefficients_0534 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0534, p_headbox] <;> ring

private theorem negative_0534 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0534 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0534] at hp
  linarith only [hp]

private def coefficients_0535 : List (List (List (List ℕ))) :=
  [[[[260858729,360022889],[2403124978,2601453298],[2198046089,2297210249]],[[1439179618,1637507938],[6706250756,7102907396],[5378630818,5576959138]],[[1192265849,1291430009],[4331015698,4529344018],[3194529689,3293693849]]],[[[721985886,920314206],[5221893852,5618550492],[4611467646,4809795966]],[[3286449612,3683106252],[14258896344,15052209624],[11195566092,11592222732]],[[2592353646,2790681966],[9092782332,9489438972],[6611988366,6810316686]]],[[[461819159,560983319],[2820152878,3018481198],[2414113559,2513277719]],[[1848653998,2046982318],[7555413596,7952070236],[5818319278,6016647598]],[[1400779799,1499943959],[4763150638,4961478958],[3418150679,3517314839]]]]

private theorem identity_0535 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(260858729 / 1388298240 : ℝ)) =
      tensor4 coefficients_0535 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0535, p_variance] <;> ring

private theorem negative_0535 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0535 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0535] at hp
  linarith only [hp]

private theorem node_0541 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0534 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0535 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0539 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0540 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0541 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0536 : List (List (List (List ℕ))) :=
  [[[[1918399609,1422578809],[1718521849,1222701049]],[[2900162738,1908521138],[2500407218,1508765618]],[[946900729,451079929],[747022969,251202169]]],[[[3739521986,2747880386],[3338604386,2346962786]],[[5605189972,3621906772],[4803354772,2820071572]],[[1795943186,804301586],[1395025586,403383986]]],[[[1820797559,1324976759],[1619757719,1123936919]],[[2704377598,1712735998],[2302297918,1310656318]],[[848717639,352896839],[647677799,151856999]]]]

private theorem identity_0536 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(151856999 / 3966566400 : ℝ)) =
      tensor4 coefficients_0536 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0536, p_headsq] <;> ring

private theorem negative_0536 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0536 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0536] at hp
  linarith only [hp]

private def coefficients_0537 : List (List (List (List ℕ))) :=
  [[[[193,449],[242,754],[31,287]]]]

private theorem identity_0537 (x0 x1 x2 x3 : ℝ) :
    (2048 : ℝ)*(-p_qmass x0 x1 x2 x3-(31 / 2048 : ℝ)) =
      tensor4 coefficients_0537 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0537, p_qmass] <;> ring

private theorem negative_0537 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 32 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0537 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0537] at hp
  linarith only [hp]

private def coefficients_0538 : List (List (List (List ℕ))) :=
  [[[[431763912,530928072],[1794353904,1992682224],[1369562472,1468726632]],[[1775760624,1974088944],[5429442528,5826099168],[3667626864,3865955184]],[[1350969192,1450133352],[3649033584,3847361904],[2305036872,2404201032]]],[[[1062412248,1260740568],[3990253416,4386910056],[2941786128,3140114448]],[[3953066856,4349723496],[11669529792,12462843072],[7744352856,8141009496]],[[2904599568,3102927888],[7707166296,8103822936],[4816511688,5014840008]]],[[[630994337,730158497],[2196591514,2394919834],[1572569657,1671733817]],[[2177998234,2376326554],[6241471268,6638127908],[4077417994,4275746314]],[[1553976377,1653140537],[4058824714,4257153034],[2511820817,2610984977]]]]

private theorem identity_0538 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(5996721 / 38563840 : ℝ)) =
      tensor4 coefficients_0538 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0538, p_variance] <;> ring

private theorem negative_0538 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 32 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0538 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0538] at hp
  linarith only [hp]

private theorem node_0548 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 32 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0537 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0538 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0547 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0536 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0548 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0539 : List (List (List (List ℕ))) :=
  [[[[935397481,687487081],[834877561,586967161]],[[1402186202,906365402],[1201146362,705325562]],[[449357521,201447121],[348837601,100927201]]],[[[1821831528,1326010728],[1620210648,1124389848]],[[2706155016,1714513416],[2302913256,1311271656]],[[849461088,353640288],[647840208,152019408]]],[[[886271638,638361238],[785170678,537260278]],[[1303643996,807823196],[1101442076,605621276]],[[399941158,152030758],[298840198,50929798]]]]

private theorem identity_0539 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(25464899 / 991641600 : ℝ)) =
      tensor4 coefficients_0539 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0539, p_headsq] <;> ring

private theorem negative_0539 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0539 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0539] at hp
  linarith only [hp]

private def coefficients_0540 : List (List (List (List ℕ))) :=
  [[[[135127889,333456209],[3952887298,4349543938],[3873539249,4071867569]],[[2069736658,2466393298],[11569812836,12363126116],[9611635858,10008292498]],[[1948553729,2146882049],[7644815458,8041472098],[5752041569,5950369889]]],[[[661855110,1058511750],[8704080300,9497393580],[8153784870,8550441510]],[[4930225500,5723538780],[24751344120,26337970680],[20044237980,20837551260]],[[4296260310,4692916950],[16103043660,16896356940],[11918343030,12314999670]]],[[[527419223,725747543],[4752577006,5149233646],[4280937623,4479265943]],[[2861872846,3258529486],[13184299292,13977612572],[10433986126,10830642766]],[[2348398583,2546726903],[8459612206,8856268846],[6166993463,6365321783]]]]

private theorem identity_0540 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(135127889 / 5553192960 : ℝ)) =
      tensor4 coefficients_0540 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0540, p_variance] <;> ring

private theorem negative_0540 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0540 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0540] at hp
  linarith only [hp]

private theorem node_0549 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0539 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0540 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0546 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (45 / 64 : ℝ)
  · exact node_0547 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0549 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0541 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0541 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0541 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0541, p_qmass] <;> ring

private theorem negative_0541 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0541 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0541] at hp
  linarith only [hp]

private theorem node_0545 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact node_0546 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0541 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0542 : List (List (List (List ℕ))) :=
  [[[[109974618,159556698],[684200196,783364356],[581198058,630780138]],[[677227716,776391876],[2299226472,2497554792],[1635943716,1735107876]],[[574225578,623807658],[1628971236,1728135396],[1061718138,1111300218]]],[[[319391448,418555608],[1571061576,1769389896],[1265615088,1364779248]],[[1557116616,1755444936],[5011328832,5407985472],[3482102136,3680430456]],[[1251670128,1350834288],[3468157176,3666485496],[2230432008,2329596168]]],[[[209762831,259344911],[887553382,986717542],[684763031,734345111]],[[880580902,979745062],[2713486364,2911814684],[1846850422,1946014582]],[[677790551,727372631],[1839877942,1939042102],[1169059871,1218641951]]]]

private theorem identity_0542 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(6109701 / 38563840 : ℝ)) =
      tensor4 coefficients_0542 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0542, p_variance] <;> ring

private theorem negative_0542 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0542 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0542] at hp
  linarith only [hp]

private theorem node_0544 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0545 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0542 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0543 : List (List (List (List ℕ))) :=
  [[[[105326298,154908378],[1143802836,1242966996],[1066366458,1115948538]],[[665606916,764771076],[3230052552,3428380872],[2620225476,2719389636]],[[567253098,616835178],[2100194676,2199358836],[1560831498,1610413578]]],[[[310094808,409258968],[2494043616,2692371936],[2239728648,2338892808]],[[1533875016,1732203336],[6880534512,7277191152],[5458219176,5656547496]],[[1237725168,1336889328],[4414380816,4612709136],[3232435488,3331599648]]],[[[205114511,254696591],[1350932782,1450096942],[1173708191,1223290271]],[[868960102,968124262],[3651865964,3850194284],[2838685702,2937849862]],[[670818071,720400151],[2314878142,2414042302],[1671949991,1721532071]]]]

private theorem identity_0543 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(835923 / 5509120 : ℝ)) =
      tensor4 coefficients_0543 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0543, p_variance] <;> ring

private theorem negative_0543 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0543 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0543] at hp
  linarith only [hp]

private theorem node_0543 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0544 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0543 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0544 : List (List (List (List ℕ))) :=
  [[[[1822865497,1327044697],[1620663577,1124842777]],[[2707932434,1716290834],[2303528594,1311886994]],[[850204537,354383737],[648002617,152181817]]],[[[3547154490,2555512890],[3141588570,2149946970]],[[5218130820,3234847620],[4406998980,2423715780]],[[1601251530,609609930],[1195685610,204044010]]],[[[1723964175,1228143375],[1520600175,1024779375]],[[2509548750,1517907150],[2102820750,1111179150]],[[750722175,254901375],[547358175,51537375]]]]

private theorem identity_0544 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(229055 / 17629184 : ℝ)) =
      tensor4 coefficients_0544 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0544, p_headsq] <;> ring

private theorem negative_0544 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0544 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0544] at hp
  linarith only [hp]

private def coefficients_0545 : List (List (List (List ℕ))) :=
  [[[[165636778,264800938],[2180142836,2378471156],[2042395978,2141560138]],[[1234790756,1433119076],[6199858312,6596514952],[5020847396,5219175716]],[[1076126458,1175290618],[4033660436,4231988756],[2985423898,3084588058]]],[[[527765224,726093544],[4760822528,5157479168],[4288837144,4487165464]],[[2866341608,3262998248],[13208343856,14001657136],[10453561928,10850218568]],[[2352521344,2550849664],[8475411248,8872067888],[6178669744,6376998064]]],[[[362474447,461638607],[2581371694,2779700014],[2246787167,2345951327]],[[1632242854,1830571174],[7009869548,7406526188],[5433406534,5631734854]],[[1276740887,1375905047],[4442442814,4640771134],[3193591847,3292756007]]]]

private theorem identity_0545 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(82818389 / 1388298240 : ℝ)) =
      tensor4 coefficients_0545 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0545, p_variance] <;> ring

private theorem negative_0545 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0545 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0545] at hp
  linarith only [hp]

private theorem node_0554 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0544 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0545 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0546 : List (List (List (List ℕ))) :=
  [[[[887305607,639395207],[785623607,537713207]],[[1305421414,809600614],[1102057414,606236614]],[[400684607,152774207],[299002607,51092207]]],[[[1724998144,1229177344],[1521053104,1025232304]],[[2511326168,1519684568],[2103436088,1111794488]],[[751465624,255644824],[547520584,51699784]]],[[[837530128,589619728],[735267088,487356688]],[[1205579936,709759136],[1001053856,505233056]],[[350618608,102708208],[248355568,445168]]]]

private theorem identity_0546 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(27823 / 123955200 : ℝ)) =
      tensor4 coefficients_0546 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0546, p_headsq] <;> ring

private theorem negative_0546 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0546 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0546] at hp
  linarith only [hp]

private def coefficients_0547 : List (List (List (List ℕ))) :=
  [[[[528111225,726439545],[4769068050,5165724690],[4296736665,4495064985]],[[2870810370,3267467010],[13232388420,14025701700],[10473137730,10869794370]],[[2356644105,2554972425],[8491210290,8887866930],[6190346025,6388674345]]],[[[1450589790,1847246430],[10341977820,11135291100],[9002947710,9399604350]],[[6537908940,7331222220],[28087567320,29674193880],[21772777740,22566091020]],[[5115209070,5511865710],[17801369340,18594682620],[12797719950,13194376590]]],[[[923170567,1121498887],[5574293774,5970950414],[4706903047,4905231367]],[[3668482574,4065139214],[14857946908,15651260188],[11301024014,11697680654]],[[2759256967,2957585287],[9311543054,9708199694],[6608065927,6806394247]]]]

private theorem identity_0547 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(11735805 / 123404288 : ℝ)) =
      tensor4 coefficients_0547 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0547, p_variance] <;> ring

private theorem negative_0547 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0547 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0547] at hp
  linarith only [hp]

private theorem node_0555 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0546 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0547 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0553 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (47 / 64 : ℝ)
  · exact node_0554 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0555 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0548 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0548 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0548 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0548, p_qmass] <;> ring

private theorem negative_0548 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0548 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0548] at hp
  linarith only [hp]

private theorem node_0552 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact node_0553 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0548 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0549 : List (List (List (List ℕ))) :=
  [[[[319737449,418901609],[1575530338,1773858658],[1269737849,1368902009]],[[1561585378,1759913698],[5027819876,5424476516],[3494124418,3692452738]],[[1255792889,1354957049],[3480179458,3678507778],[2238331529,2337495689]]],[[[839743326,1038071646],[3559151052,3955807692],[2747297646,2945625966]],[[3531261132,3927917772],[10886927544,11680240824],[7411446252,7808102892]],[[2719407726,2917736046],[7383556332,7780212972],[4692038526,4890366846]]],[[[520697879,619862039],[1985004718,2183333038],[1478251799,1577415959]],[[1971059758,2169388078],[5861875676,6258532316],[3918705838,4117034158]],[[1464306839,1563470999],[3904760878,4103089198],[2454398999,2553563159]]]]

private theorem identity_0549 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(319737449 / 1388298240 : ℝ)) =
      tensor4 coefficients_0549 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0549, p_variance] <;> ring

private theorem negative_0549 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0549 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0549] at hp
  linarith only [hp]

private theorem node_0551 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0552 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0549 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0550 : List (List (List (List ℕ))) :=
  [[[[310440809,409604969],[2502289138,2700617458],[2247628169,2346792329]],[[1538343778,1736672098],[6904579076,7301235716],[5477794978,5676123298]],[[1241847929,1341012089],[4430179858,4628508178],[3244111769,3343275929]]],[[[821150046,1019478366],[5420222172,5816878812],[4710631806,4908960126]],[[3484777932,3881434572],[14655552984,15448866264],[11393894412,11790551052]],[[2691517806,2889846126],[9291110652,9687767292],[6711152526,6909480846]]],[[[511401239,610565399],[2919317038,3117645358],[2463695639,2562859799]],[[1947818158,2146146478],[7753741916,8150398556],[5917483438,6115811758]],[[1450361879,1549526039],[4862314798,5060643118],[3467732759,3566896919]]]]

private theorem identity_0550 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(44348687 / 198328320 : ℝ)) =
      tensor4 coefficients_0550 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0550, p_variance] <;> ring

private theorem negative_0550 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0550 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0550] at hp
  linarith only [hp]

private theorem node_0550 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0551 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0550 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0542 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0543 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0550 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0538 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0539 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0542 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0536 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0537 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0538 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0535 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0529 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0536 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0519 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0520 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0535 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0551 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0551 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0551 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0551, p_qbox] <;> ring

private theorem negative_0551 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0551 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0551] at hp
  linarith only [hp]

private def coefficients_0552 : List (List (List (List ℕ))) :=
  [[[[958416857,710506457],[860802137,612891737]],[[1589127154,1093306354],[1393897714,898076914]],[[595847897,347937497],[498233177,250322777]]],[[[1870656450,1374835650],[1674264930,1178444130]],[[3085318740,2093677140],[2692535700,1700894100]],[[1144937490,649116690],[948545970,452725170]]],[[[911914775,664004375],[813137975,565227575]],[[1495541950,999721150],[1297988350,802167550]],[[548764775,300854375],[449987975,202077575]]]]

private theorem identity_0552 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(8083103 / 39665664 : ℝ)) =
      tensor4 coefficients_0552 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0552, p_headsq] <;> ring

private theorem negative_0552 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0552 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0552] at hp
  linarith only [hp]

private def coefficients_0553 : List (List (List (List ℕ))) :=
  [[[[130555907,447044614,300994307],[32941187,251815174,203379587]],[[179363267,544659334,349801667],[81748547,349429894,252186947]]],[[[244567590,861000780,585444390],[48176070,468217740,389052870]],[[342763350,1057392300,683640150],[146371830,664609260,487248630]]],[[[113832125,413597050,284270525],[15055325,216043450,185493725]],[[163220525,512373850,333658925],[64443725,314820250,234882125]]]]

private theorem identity_0553 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(602213 / 39665664 : ℝ)) =
      tensor4 coefficients_0553 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0553, p_coupled] <;> ring

private theorem negative_0553 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0553 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0553] at hp
  linarith only [hp]

private theorem node_0561 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0552 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0553 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0554 : List (List (List (List ℕ))) :=
  [[[[468181097,344225897],[418792697,294837497]],[[772218394,524307994],[673441594,425531194]],[[286606097,162650897],[237217697,113262497]]],[[[912948744,665038344],[813590904,565680504]],[[1497319368,1001498568],[1298603688,802782888]],[[549508224,301597824],[450150384,202239984]]],[[[444605238,320650038],[394635798,270680598]],[[724776156,476865756],[624837276,376926876]],[[262739718,138784518],[212770278,88815078]]]]

private theorem identity_0554 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(4934171 / 27545600 : ℝ)) =
      tensor4 coefficients_0554 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0554, p_headsq] <;> ring

private theorem negative_0554 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0554 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0554] at hp
  linarith only [hp]

private def coefficients_0555 : List (List (List (List ℕ))) :=
  [[[[61477307,215921014,146696507],[12088907,117144214,97308107]],[[86171507,265309414,171390707],[36783107,166532614,122002307]]],[[[114502944,414938688,284941344],[15145104,216223008,185583504]],[[164181864,514296528,334620264],[64824024,315580848,235262424]]],[[[52935858,198838116,138155058],[2966418,98899236,88185618]],[[77920578,248807556,163139778],[27951138,148868676,113170338]]]]

private theorem identity_0555 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(164801 / 27545600 : ℝ)) =
      tensor4 coefficients_0555 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0555, p_coupled] <;> ring

private theorem negative_0555 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0555 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0555] at hp
  linarith only [hp]

private theorem node_0562 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0554 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0555 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0560 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (21 / 32 : ℝ)
  · exact node_0561 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0562 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0556 : List (List (List (List ℕ))) :=
  [[[[33,49],[48,80],[6,22]]]]

private theorem identity_0556 (x0 x1 x2 x3 : ℝ) :
    (64 : ℝ)*(-p_qmass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0556 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0556, p_qmass] <;> ring

private theorem negative_0556 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0556 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0556] at hp
  linarith only [hp]

private theorem node_0559 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0560 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0556 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0558 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0551 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0559 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0557 : List (List (List (List ℕ))) :=
  [[[[65278939,223524278,142750939],[16471579,125909558,93943579]],[[89682619,272331638,167154619],[40875259,174716918,118347259]]],[[[123157326,432247452,278101326],[24380526,234693852,179324526]],[[172545726,531024252,327489726],[73768926,333470652,228712926]]],[[[57698829,208364058,135170829],[7729389,108425178,85201389]],[[82683549,258333498,160155549],[32714109,158394618,110186109]]]]

private theorem identity_0557 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(858821 / 27545600 : ℝ)) =
      tensor4 coefficients_0557 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0557, p_coupled] <;> ring

private theorem negative_0557 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0557 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0557] at hp
  linarith only [hp]

private theorem node_0557 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0558 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0557 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0558 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0558 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0558 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0558, p_qbox] <;> ring

private theorem negative_0558 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0558 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0558] at hp
  linarith only [hp]

private def coefficients_0559 : List (List (List (List ℕ))) :=
  [[[[913982713,666072313],[814043833,566133433]],[[1499096786,1003275986],[1299219026,803398226]],[[550251673,302341273],[450312793,202402393]]],[[[1780488890,1284668090],[1579449050,1083628250]],[[2902659460,1911017860],[2500579780,1508938180]],[[1052445770,556624970],[851405930,355585130]]],[[[866181359,618270959],[765080399,517169999]],[[1402913038,907092238],[1200711118,704890318]],[[501869279,253958879],[400768319,152857919]]]]

private theorem identity_0559 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(152857919 / 991641600 : ℝ)) =
      tensor4 coefficients_0559 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0559, p_headsq] <;> ring

private theorem negative_0559 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0559 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0559] at hp
  linarith only [hp]

private def coefficients_0560 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0560 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0560 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0560, p_qmass] <;> ring

private theorem negative_0560 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0560 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0560] at hp
  linarith only [hp]

private def coefficients_0561 : List (List (List (List ℕ))) :=
  [[[[2571004369,2075183569],[2371126609,1875305809]],[[3547634978,2555993378],[3147879458,2156237858]],[[837181009,341360209],[637303249,141482449]]],[[[5044731506,4053089906],[4643813906,3652172306]],[[6899553412,4916270212],[6097718212,4114435012]],[[1575922706,584281106],[1175005106,183363506]]],[[[2473402319,1977581519],[2272362479,1776541679]],[[3351268798,2359627198],[2949189118,1957547518]],[[738416879,242596079],[537377039,41556239]]]]

private theorem identity_0561 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(41556239 / 3966566400 : ℝ)) =
      tensor4 coefficients_0561 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0561, p_headsq] <;> ring

private theorem negative_0561 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0561 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0561] at hp
  linarith only [hp]

private def coefficients_0562 : List (List (List (List ℕ))) :=
  [[[[1036111081,788200681],[935591161,687680761]],[[1673338202,1177517402],[1472298362,976477562]],[[619795921,371885521],[519276001,271365601]]],[[[2023258728,1527437928],[1821637848,1325817048]],[[3248459016,2256817416],[2845217256,1853575656]],[[1190337888,694517088],[988717008,492896208]]],[[[986985238,739074838],[885884278,637973878]],[[1574795996,1078975196],[1372594076,876773276]],[[570379558,322469158],[469278598,221368198]]]]

private theorem identity_0562 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(110684099 / 991641600 : ℝ)) =
      tensor4 coefficients_0562 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0562, p_headsq] <;> ring

private theorem negative_0562 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (11 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0562 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0562] at hp
  linarith only [hp]

private def coefficients_0563 : List (List (List (List ℕ))) :=
  [[[[137460091,460852982,315645691],[36940171,259813142,215125771]],[[187720051,561372902,365905651],[87200131,360333062,265385731]]],[[[257187648,886240896,613558848],[55566768,482999136,411937968]],[[357998088,1087861776,714369288],[156377208,684620016,512748408]]],[[[119637778,425208356,297823378],[18536818,223006436,196722418]],[[170188258,526309316,348373858],[69087298,324107396,247272898]]]]

private theorem identity_0563 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(9268409 / 991641600 : ℝ)) =
      tensor4 coefficients_0563 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0563, p_coupled] <;> ring

private theorem negative_0563 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (11 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0563 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0563] at hp
  linarith only [hp]

private theorem node_0571 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (11 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0562 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0563 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0570 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (45 / 64 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0561 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0571 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0564 : List (List (List (List ℕ))) :=
  [[[[71,103],[88,152],[8,40]]]]

private theorem identity_0564 (x0 x1 x2 x3 : ℝ) :
    (256 : ℝ)*(-p_qmass x0 x1 x2 x3-(1 / 32 : ℝ)) =
      tensor4 coefficients_0564 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0564, p_qmass] <;> ring

private theorem negative_0564 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (5 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0564 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0564] at hp
  linarith only [hp]

private theorem node_0569 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 16 : ℝ)
  · exact node_0570 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0564 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0568 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0560 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0569 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0567 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0559 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0568 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0565 : List (List (List (List ℕ))) :=
  [[[[445639207,321684007],[395088727,271133527]],[[726553574,478643174],[625452614,377542214]],[[263483167,139527967],[212932687,88977487]]],[[[867215328,619304928],[765533328,517622928]],[[1404690456,908869656],[1201326456,705505656]],[[502612728,254702328],[400930728,153020328]]],[[[421413712,297458512],[370282192,246326992]],[[677812064,429901664],[575549024,327638624]],[[238967152,115011952],[187835632,63880432]]]]

private theorem identity_0565 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(3992527 / 30988800 : ℝ)) =
      tensor4 coefficients_0565 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0565, p_headsq] <;> ring

private theorem negative_0565 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0565 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0565] at hp
  linarith only [hp]

private def coefficients_0566 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0566 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0566 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0566, p_qmass] <;> ring

private theorem negative_0566 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0566 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0566] at hp
  linarith only [hp]

private def coefficients_0567 : List (List (List (List ℕ))) :=
  [[[[2024292697,1528471897],[1822090777,1326269977]],[[3250236434,2258594834],[2845832594,1854190994]],[[1191081337,695260537],[988879417,493058617]]],[[[3950008890,2958367290],[3544442970,2552801370]],[[6302738820,4319455620],[5491606980,3508323780]],[[2283005130,1291363530],[1877439210,885797610]]],[[[1925391375,1429570575],[1722027375,1226206575]],[[3051852750,2060211150],[2645124750,1653483150]],[[1091598975,595778175],[888234975,392414175]]]]

private theorem identity_0567 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(1744063 / 17629184 : ℝ)) =
      tensor4 coefficients_0567 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0567, p_headsq] <;> ring

private theorem negative_0567 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (11 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0567 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0567] at hp
  linarith only [hp]

private def coefficients_0568 : List (List (List (List ℕ))) :=
  [[[[257858467,887582534,614229667],[55656547,483178694,412027747]],[[358959427,1089784454,715330627],[156757507,685380614,513128707]]],[[[479892750,1703516700,1192635150],[74326830,892384860,787069230]],[[682675710,2109082620,1395418110],[277109790,1297950780,989852190]]],[[[221854725,815575050,578225925],[18490725,408847050,374861925]],[[323536725,1018939050,679907925],[120172725,612211050,476543925]]]]

private theorem identity_0568 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(82181 / 17629184 : ℝ)) =
      tensor4 coefficients_0568 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0568, p_coupled] <;> ring

private theorem negative_0568 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (11 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0568 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0568] at hp
  linarith only [hp]

private theorem node_0576 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (11 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0567 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0568 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0569 : List (List (List (List ℕ))) :=
  [[[[988019207,740108807],[886337207,638426807]],[[1576573414,1080752614],[1373209414,877388614]],[[571123007,323212607],[469441007,221530607]]],[[[1926425344,1430604544],[1722480304,1226659504]],[[3053630168,2061988568],[2645740088,1654098488]],[[1092342424,596521624],[888397384,392576584]]],[[[938243728,690333328],[835980688,588070288]],[[1476731936,980911136],[1272205856,776385056]],[[521057008,273146608],[418793968,170883568]]]]

private theorem identity_0569 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(10680223 / 123955200 : ℝ)) =
      tensor4 coefficients_0569 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0569, p_headsq] <;> ring

private theorem negative_0569 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (11 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0569 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0569] at hp
  linarith only [hp]

private def coefficients_0570 : List (List (List (List ℕ))) :=
  [[[[758977785,957306105],[5212207890,5608864530],[4509009945,4707338265]],[[3341840130,3738496770],[14137261380,14930574660],[10906980930,11303637570]],[[2596807305,2795135625],[8952943410,9349600050],[6411915945,6610244265]]],[[[1912322910,2308979550],[11228257500,12021570780],[9427494270,9824150910]],[[7479968460,8273281740],[29897313240,31483939800],[22640464140,23433777420]],[[5595535470,5992192110],[18724835580,19518148860],[13240859790,13637516430]]],[[[1154037127,1352365447],[6017433614,6414090254],[4919176327,5117504647]],[[4139512334,4536168974],[15762819868,16556133148],[11734867214,12131523854]],[[2999420167,3197748487],[9773276174,10169932814],[6829635847,7027964167]]]]

private theorem identity_0570 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(16866173 / 123404288 : ℝ)) =
      tensor4 coefficients_0570 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0570, p_variance] <;> ring

private theorem negative_0570 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (11 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0570 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(11 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0570] at hp
  linarith only [hp]

private theorem node_0577 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (11 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0569 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0570 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0575 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (47 / 64 : ℝ)
  · exact node_0576 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0577 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0571 : List (List (List (List ℕ))) :=
  [[[[71,103],[88,152],[8,40]]]]

private theorem identity_0571 (x0 x1 x2 x3 : ℝ) :
    (256 : ℝ)*(-p_qmass x0 x1 x2 x3-(1 / 32 : ℝ)) =
      tensor4 coefficients_0571 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0571, p_qmass] <;> ring

private theorem negative_0571 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (5 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0571 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0571] at hp
  linarith only [hp]

private theorem node_0574 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 16 : ℝ)
  · exact node_0575 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0571 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0573 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0566 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0574 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0572 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0565 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0573 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0566 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0567 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0572 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0572 : List (List (List (List ℕ))) :=
  [[[[33,49],[48,80],[6,22]]]]

private theorem identity_0572 (x0 x1 x2 x3 : ℝ) :
    (64 : ℝ)*(-p_qmass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0572 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0572, p_qmass] <;> ring

private theorem negative_0572 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0572 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0572] at hp
  linarith only [hp]

private theorem node_0565 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0566 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0572 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0564 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0558 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0565 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0573 : List (List (List (List ℕ))) :=
  [[[[31124741,108732682,69860741],[6140021,58763242,44876021]],[[43617101,133717402,82353101],[18632381,83747962,57368381]]],[[[58369648,209705696,135841648],[7819168,108604736,85291168]],[[83644888,260256176,161116888],[33094408,159155216,110566408]]],[[[27155128,100793456,65891128],[1589368,49661936,40325368]],[[39938008,126359216,78674008],[14372248,75227696,53108248]]]]

private theorem identity_0573 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(198671 / 15494400 : ℝ)) =
      tensor4 coefficients_0573 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0573, p_coupled] <;> ring

private theorem negative_0573 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0573 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0573] at hp
  linarith only [hp]

private theorem node_0563 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0564 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0573 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0556 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0557 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0563 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0519 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0556 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part13
