/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part22Node0985
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part22Node0985
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part22Node0985.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part22Node0985
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0982 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0982 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0982 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0982, p_qbox] <;> ring

private theorem negative_0982 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0982 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0982] at hp
  linarith only [hp]

private def coefficients_0983 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0983 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0983 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0983, p_qbox] <;> ring

private theorem negative_0983 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0983 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0983] at hp
  linarith only [hp]

private def coefficients_0984 : List (List (List (List ℕ))) :=
  [[[[58545432,108127512],[562167504,661331664],[510594552,560176632]],[[578436624,677600784],[2063295648,2261623968],[1498803984,1597968144]],[[526863672,576445752],[1515073104,1614237264],[995181912,1044763992]]],[[[213131568,312295728],[1320193176,1518521496],[1121006568,1220170728]],[[1352731416,1551059736],[4525861152,4922517792],[3201019656,3399347976]],[[1153544808,1252708968],[3233557896,3431886216],[2093958048,2193122208]]],[[[154932137,204514217],[758717674,857881834],[610758017,660340097]],[[774986794,874150954],[2463949508,2662277828],[1702907674,1802071834]],[[627027137,676609217],[1719176794,1818340954],[1099122137,1148704217]]]]

private theorem identity_0984 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(813131 / 9640960 : ℝ)) =
      tensor4 coefficients_0984 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0984, p_variance] <;> ring

private theorem negative_0984 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0984 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0984] at hp
  linarith only [hp]

private theorem node_0991 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0983 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0984 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0985 : List (List (List (List ℕ))) :=
  [[[[65517912,115099992],[1025837424,1125001584],[988209432,1037791512]],[[590057424,689221584],[3002256288,3200584608],[2467978704,2567142864]],[[531511992,581094072],[1990363824,2089527984],[1486741752,1536323832]]],[[[227076528,326240688],[2251309776,2449638096],[2080013088,2179177248]],[[1375973016,1574301336],[6411335952,6807992592],[5146922616,5345250936]],[[1162841448,1262005608],[4187916096,4386244416],[3080854488,3180018648]]],[[[161904617,211486697],[1226164354,1325328514],[1092149657,1141731737]],[[786607594,885771754],[3410463668,3608791988],[2679635914,2778800074]],[[631675457,681257537],[2198244274,2297408434],[1594458737,1644040817]]]]

private theorem identity_0985 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(909971 / 9640960 : ℝ)) =
      tensor4 coefficients_0985 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0985, p_variance] <;> ring

private theorem negative_0985 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0985 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0985] at hp
  linarith only [hp]

private theorem node_0990 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0991 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0985 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0986 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0986 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0986 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0986, p_qbox] <;> ring

private theorem negative_0986 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0986 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0986] at hp
  linarith only [hp]

private def coefficients_0987 : List (List (List (List ℕ))) :=
  [[[[213477569,312641729],[1324661938,1522990258],[1125129329,1224293489]],[[1357200178,1555528498],[4542352196,4939008836],[3213041938,3411370258]],[[1157667569,1256831729],[3245580178,3443908498],[2101857569,2201021729]]],[[[620420550,818748870],[3043808220,3440464860],[2451277590,2649605910]],[[3108884700,3505541340],[9888780120,10682093400],[6835675260,7232331900]],[[2516354070,2714682390],[6900751740,7297408380],[4412287590,4610615910]]],[[[407634983,506799143],[1720530286,1918858606],[1326840263,1426004423]],[[1753068526,1951396846],[5349195932,5745852572],[3624017326,3822345646]],[[1359378503,1458542663],[3656555566,3854883886],[2311122023,2410286183]]]]

private theorem identity_0987 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(213477569 / 1388298240 : ℝ)) =
      tensor4 coefficients_0987 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0987, p_variance] <;> ring

private theorem negative_0987 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0987 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0987] at hp
  linarith only [hp]

private theorem node_0993 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0986 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0987 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0988 : List (List (List (List ℕ))) :=
  [[[[227422529,326586689],[2259555298,2457883618],[2087912609,2187076769]],[[1380441778,1578770098],[6435380516,6832037156],[5166498418,5364826738]],[[1166964209,1266128369],[4203715138,4402043458],[3092530769,3191694929]]],[[[648310470,846638790],[4921148460,5317805100],[4384397670,4582725990]],[[3155367900,3552024540],[13689943800,14483257080],[10757695260,11154351900]],[[2534947350,2733275670],[8824575180,9221231820],[6401187510,6599515830]]],[[[421579943,520744103],[2662977166,2861305486],[2297177063,2396341223]],[[1776310126,1974638446],[7257331292,7653987932],[5592580846,5790909166]],[[1368675143,1467839303],[4622244046,4820572366],[3309348743,3408512903]]]]

private theorem identity_0988 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(227422529 / 1388298240 : ℝ)) =
      tensor4 coefficients_0988 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0988, p_variance] <;> ring

private theorem negative_0988 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0988 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0988] at hp
  linarith only [hp]

private theorem node_0992 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0993 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0988 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0989 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 32 : ℝ)
  · exact node_0990 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0992 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0989 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0989 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0989 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0989, p_qbox] <;> ring

private theorem negative_0989 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0989 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0989] at hp
  linarith only [hp]

private theorem node_0988 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0989 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0989 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0987 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0982 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0988 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0990 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0990 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0990 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0990, p_qbox] <;> ring

private theorem negative_0990 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0990 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0990] at hp
  linarith only [hp]

private def coefficients_0991 : List (List (List (List ℕ))) :=
  [[[[74628738,99419778],[381092436,430674516],[313436178,338227218]],[[385740756,435322836],[1251420552,1350584712],[879624756,929206836]],[[318084498,342875538],[884273076,933855156],[573161058,597952098]]],[[[199166208,248748288],[865779096,964943256],[680557848,730139928]],[[875075736,974239896],[2717583072,2915911392],[1870397256,1969561416]],[[689854488,739436568],[1879693896,1978858056],[1203784368,1253366448]]],[[[124883471,149674511],[485378662,534960742],[367467671,392258711]],[[490026982,539609062],[1467546524,1566710684],[991464502,1041046582]],[[372115991,396907031],[996112822,1045694902],[630969311,655760351]]]]

private theorem identity_0991 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(4146041 / 9640960 : ℝ)) =
      tensor4 coefficients_0991 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0991, p_variance] <;> ring

private theorem negative_0991 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0991 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0991] at hp
  linarith only [hp]

private theorem node_0994 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0990 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0991 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0986 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0987 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0994 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0992 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0992 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0992 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0992, p_qbox] <;> ring

private theorem negative_0992 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0992 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0992] at hp
  linarith only [hp]

private def coefficients_0993 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0993 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0993 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0993, p_qbox] <;> ring

private theorem negative_0993 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0993 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0993] at hp
  linarith only [hp]

private def coefficients_0994 : List (List (List (List ℕ))) :=
  [[[[155278138,204860218],[763186436,862350596],[614880778,664462858]],[[779455556,878619716],[2480440552,2678768872],[1714929956,1814094116]],[[631149898,680731978],[1731199076,1830363236],[1107021658,1156603738]]],[[[407980984,507145144],[1724999048,1923327368],[1330963024,1430127184]],[[1757537288,1955865608],[5365686976,5762343616],[3636039608,3834367928]],[[1363501264,1462665424],[3668577848,3866906168],[2319021544,2418185704]]],[[[253048847,302630927],[962504614,1061668774],[716428247,766010327]],[[978773734,1077937894],[2886630428,3084958748],[1921801654,2020965814]],[[732697367,782279447],[1938070774,2037234934],[1212345887,1261927967]]]]

private theorem identity_0994 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(77639069 / 347074560 : ℝ)) =
      tensor4 coefficients_0994 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0994, p_variance] <;> ring

private theorem negative_0994 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0994 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0994] at hp
  linarith only [hp]

private theorem node_1000 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0993 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0994 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0995 : List (List (List (List ℕ))) :=
  [[[[162250618,211832698],[1234409876,1333574036],[1100049178,1149631258]],[[791076356,890240516],[3434508232,3632836552],[2699211716,2798375876]],[[635798218,685380298],[2214043316,2313207476],[1606135018,1655717098]]],[[[421925944,521090104],[2671222688,2869551008],[2305076584,2404240744]],[[1780778888,1979107208],[7281375856,7678032496],[5612156648,5810484968]],[[1372797904,1471962064],[4638043088,4836371408],[3321025024,3420189184]]],[[[260021327,309603407],[1437504814,1536668974],[1205373407,1254955487]],[[990394534,1089558694],[3848251628,4046579948],[2913636934,3012801094]],[[737345687,786927767],[2424691774,2523855934],[1715236007,1764818087]]]]

private theorem identity_0995 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(81125309 / 347074560 : ℝ)) =
      tensor4 coefficients_0995 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0995, p_variance] <;> ring

private theorem negative_0995 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0995 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0995] at hp
  linarith only [hp]

private theorem node_0999 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_1000 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0995 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0996 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0996 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0996 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0996, p_qbox] <;> ring

private theorem negative_0996 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0996 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0996] at hp
  linarith only [hp]

private def coefficients_0997 : List (List (List (List ℕ))) :=
  [[[[408326985,507491145],[1729467810,1927796130],[1335085785,1434249945]],[[1762006050,1960334370],[5382178020,5778834660],[3648061890,3846390210]],[[1367624025,1466788185],[3680600130,3878928450],[2326921065,2426085225]]],[[[1012887390,1211215710],[3858955980,4255612620],[2873958510,3072286830]],[[3924032460,4320689100],[11579503800,12372817080],[7711251180,8107907820]],[[2939034990,3137363310],[7776327660,8172984300],[4865182590,5063510910]]],[[[605252407,704416567],[2130872174,2329200494],[1539564727,1638728887]],[[2163410414,2361738734],[6200093788,6596750428],[4064573294,4262901614]],[[1572102967,1671267127],[4097111534,4295439854],[2538953527,2638117687]]]]

private theorem identity_0997 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(9073933 / 30851072 : ℝ)) =
      tensor4 coefficients_0997 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0997, p_variance] <;> ring

private theorem negative_0997 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0997 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0997] at hp
  linarith only [hp]

private theorem node_1002 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0996 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0997 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0998 : List (List (List (List ℕ))) :=
  [[[[422271945,521436105],[2679468210,2877796530],[2312976105,2412140265]],[[1785247650,1983575970],[7305420420,7702077060],[5631732450,5830060770]],[[1376920665,1476084825],[4653842130,4852170450],[3332701305,3431865465]]],[[[1040777310,1239105630],[5766510300,6163166940],[4837292670,5035620990]],[[3970515660,4367172300],[15441095640,16234408920],[11693699340,12090355980]],[[2957628270,3155956590],[9730365180,10127021820],[6884296590,7082624910]]],[[[619197367,718361527],[3088426094,3286754414],[2525008567,2624172727]],[[2186652014,2384980334],[8138443228,8535099868],[6063350894,6261679214]],[[1581399607,1680563767],[5077907054,5276235374],[3552287287,3651451447]]]]

private theorem identity_0998 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(9383821 / 30851072 : ℝ)) =
      tensor4 coefficients_0998 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0998, p_variance] <;> ring

private theorem negative_0998 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0998 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0998] at hp
  linarith only [hp]

private theorem node_1001 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_1002 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0998 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0998 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 32 : ℝ)
  · exact node_0999 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_1001 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0999 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0999 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0999 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0999, p_qbox] <;> ring

private theorem negative_0999 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0999 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0999] at hp
  linarith only [hp]

private theorem node_0997 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0998 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0999 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0996 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0992 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0997 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_1000 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_1000 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_1000 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1000, p_qbox] <;> ring

private theorem negative_1000 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1000 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1000] at hp
  linarith only [hp]

private def coefficients_1001 : List (List (List (List ℕ))) :=
  [[[[199512209,249094289],[870247858,969412018],[684680609,734262689]],[[879544498,978708658],[2734074116,2932402436],[1882419538,1981583698]],[[693977249,743559329],[1891716178,1990880338],[1211683889,1261265969]]],[[[500225886,599390046],[1950452172,2148780492],[1478116206,1577280366]],[[1969045452,2167373772],[5903168184,6299824824],[3989902572,4188230892]],[[1496709486,1595873646],[4008495852,4206824172],[2539676286,2638840446]]],[[[301405679,350987759],[1081588318,1180752478],[794127599,843709679]],[[1090884958,1190049118],[3171862076,3370190396],[2108867038,2208031198]],[[803424239,853006319],[2118163678,2217327838],[1328684399,1378266479]]]]

private theorem identity_1001 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(199512209 / 347074560 : ℝ)) =
      tensor4 coefficients_1001 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1001, p_variance] <;> ring

private theorem negative_1001 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1001 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1001] at hp
  linarith only [hp]

private theorem node_1003 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_1000 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_1001 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0995 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0996 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_1003 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 16 : ℝ)
  · exact node_0986 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0995 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part22Node0985
