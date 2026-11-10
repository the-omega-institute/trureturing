/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part23
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part23
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part23.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part23
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_1012 : List (List (List (List ℕ))) :=
  [[[[867935574573029,587546928889829],[752275258228709,471886612545509]],[[1376362196795338,815584905428938],[1145041564106698,584264272740298]],[[429567315623909,149178669940709],[313906999279589,33518353596389]]],[[[3447371872239508,2328054432956308],[2984996267646868,1865678828363668]],[[5450955322990376,3212320444423976],[4526204113805096,2287569235238696]],[[1688775420952468,569457981669268],[1226399816359828,107082377076628]]],[[[5134267871073118,3458642964935518],[4441106357931358,2765481451793758]],[[8094246745433276,4742996933158076],[6707923719149756,3356673906874556]],[[2488709369508958,813084463371358],[1795547856367198,119922950229598]]],[[[3398161936797460,2283309859639060],[2936324448455860,1821472371297460]],[[5341075359635720,3111371205318920],[4417400382952520,2187696228635720]],[[1629361276137460,514509198979060],[1167523787795860,52671710637460]]],[[[843330359983259,565174395362459],[727939096535099,449783131914299]],[[1321421733582358,765109804340758],[1090639206686038,534327277444438]],[[399860008549499,121704043928699],[284468745101339,6312780480539]]]]

private theorem identity_1012 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6312780480539 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_1012 ((x0-(3 / 4 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1012, p_headbox] <;> ring

private theorem negative_1012 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (49 / 64 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1012 ((x0-(3 / 4 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1012] at hp
  linarith only [hp]

private def coefficients_1013 : List (List (List (List ℕ))) :=
  [[[[367657740988067,228579758677667],[309962109263987,170884126953587]],[[644005735380094,365849770759294],[528614471931934,250458507311134]],[[266569073760827,127491091450427],[208873442036747,69795459726347]]],[[[1458210715520056,903012895616056],[1227564405898216,672366585994216]],[[2549755586761592,1439359946953592],[2088462967517912,978067327709912]],[[1052507524529536,497309704625536],[821861214907696,266663395003696]]],[[[2168567810921912,1337440013878712],[1822804357997912,991676560954712]],[[3785002225299424,2122746631213024],[3093475319451424,1431219725365024]],[[1557995741147912,726867944104712],[1212232288223912,381104491180712]]],[[[1433134188959616,880160125343616],[1202763679851456,649789616235456]],[[2496760137382752,1390812010150752],[2036019119166432,930070991934432]],[[1024744959575136,471770895959136],[794374450466976,241400386850976]]],[[[355119350865912,217153246699512],[297561616783992,159595512617592]],[[617507760057264,341575551724464],[502392291893424,226460083560624]],[[252687667492152,114721563325752],[195129933410232,57163829243832]]]]

private theorem identity_1013 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(793942072831 / 11282677760000 : ℝ)) =
      tensor4 coefficients_1013 ((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1013, p_headbox] <;> ring

private theorem negative_1013 (x0 x1 x2 x3 : ℝ)
    (h0l : (49 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (17 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1013 ((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1013] at hp
  linarith only [hp]

private def coefficients_1014 : List (List (List (List ℕ))) :=
  [[[[604677929,803006249],[4989602098,5386258738],[4440704009,4639032329]],[[3020457538,3417114178],[13666484036,14459797316],[10757586178,11154242818]],[[2429724569,2628052889],[8704771858,9101428498],[6330827129,6529155449]]],[[[1606491206,2003147846],[10788581932,11581895212],[9293650406,9690307046]],[[6842739292,7636052572],[28966830584,30553457144],[22347210652,23140523932]],[[5264138006,5660794646],[18234028492,19027341772],[13081450166,13478106806]]],[[[1002505279,1200833599],[5800363838,6197020478],[4853638399,5051966719]],[[3823665758,4220322398],[15303114556,16096427836],[11591008478,11987665118]],[[2835105439,3033433759],[9530640638,9927297278],[6751315039,6949643359]]]]

private theorem identity_1014 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(604677929 / 5553192960 : ℝ)) =
      tensor4 coefficients_1014 ((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1014, p_variance] <;> ring

private theorem negative_1014 (x0 x1 x2 x3 : ℝ)
    (h0l : (49 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (17 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1014 ((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(49 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1014] at hp
  linarith only [hp]

private theorem node_1027 (x0 x1 x2 x3 : ℝ)
    (h0l : (49 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (17 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_1013 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_1014 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_1026 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (49 / 64 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_1012 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_1027 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_1015 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_1015 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_1015 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1015, p_qmass] <;> ring

private theorem negative_1015 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1015 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1015] at hp
  linarith only [hp]

private theorem node_1025 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_1026 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_1015 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_1016 : List (List (List (List ℕ))) :=
  [[[[173696992,223279072],[823846784,923010944],[657122272,706704352]],[[807577664,906741824],[2584330048,2782658368],[1790697344,1889861504]],[[640853152,690435232],[1774428224,1873592384],[1140547552,1190129632]]],[[[448220200,547384360],[1853122760,2051451080],[1418847520,1518011680]],[[1820584520,2018912840],[5587072000,5983728640],[3794377400,3992705720]],[[1386309280,1485473440],[3761839160,3960167480],[2389474840,2488639000]]],[[[274869209,324451289],[1029967978,1129132138],[762071249,811653329]],[[1013698858,1112863018],[3004125956,3202454276],[2004372058,2103536218]],[[745802129,795384209],[1988102938,2087267098],[1249273289,1298855369]]]]

private theorem identity_1016 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(775433 / 3098880 : ℝ)) =
      tensor4 coefficients_1016 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1016, p_variance] <;> ring

private theorem negative_1016 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1016 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1016] at hp
  linarith only [hp]

private theorem node_1024 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_1025 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1016 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_1017 : List (List (List (List ℕ))) :=
  [[[[164400352,213982432],[1286354624,1385518784],[1149844192,1199426272]],[[786660224,885824384],[3520966528,3719294848],[2790086144,2889250304]],[[629232352,678814432],[2248556864,2347721024],[1647214432,1696796512]]],[[[429626920,528791080],[2781915200,2980243520],[2408068120,2507232280]],[[1778749640,1977077960],[7467898480,7864555120],[5800708520,5999036840]],[[1363067680,1462231840],[4713873200,4912201520],[3406585360,3505749520]]],[[[265572569,315154649],[1496252578,1595416738],[1258569929,1308152009]],[[992781418,1091945578],[3948315956,4146644276],[3011314378,3110478538]],[[734181329,783763409],[2466008338,2565172498],[1759716929,1809299009]]]]

private theorem identity_1017 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(5137511 / 21692160 : ℝ)) =
      tensor4 coefficients_1017 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1017, p_variance] <;> ring

private theorem negative_1017 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1017 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1017] at hp
  linarith only [hp]

private theorem node_1023 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_1024 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1017 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_1018 : List (List (List (List ℕ))) :=
  [[[[723097723440349,447165515107549],[607982255276509,332050046943709]],[[1260733563531578,708869146865978],[1030502627203898,478638210538298]],[[518234356692829,242302148360029],[403118888528989,127186680196189]]],[[[2867077322769460,1765567783339060],[2406894595675060,1305385056244660]],[[4989476059818920,2786456980958120],[4069110605630120,1866091526769320]],[[2044948847558260,943439308127860],[1584766120463860,483256581033460]]],[[[4262408326143358,2613468495461758],[3572556293661118,1923616462979518]],[[7403563545256796,4105683883893596],[6023859480292316,2725979818929116]],[[3025214137268638,1376274306587038],[2335362104786398,686422274104798]]],[[[2815975063556868,1718895187153668],[2356357296761508,1259277420358308]],[[4881632149019256,2687472396212856],[3962396615428536,1768236862622136]],[[1988518656652788,891438780249588],[1528900889857428,431821013454228]]],[[[697546333335059,423828956515859],[582713340091379,308995963272179]],[[1206811093234678,659376339596278],[977145106747318,429710353108918]],[[490019006842019,216301630022819],[375186013598339,101468636779139]]]]

private theorem identity_1018 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(101468636779139 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_1018 ((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1018, p_headbox] <;> ring

private theorem negative_1018 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (51 / 64 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (17 / 32 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1018 ((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1018] at hp
  linarith only [hp]

private def coefficients_1019 : List (List (List (List ℕ))) :=
  [[[[401795802,500959962],[2701268244,2899596564],[2327362362,2426526522]],[[1712919204,1911247524],[7253729928,7650386568],[5596590564,5794918884]],[[1318095882,1417260042],[4566406644,4764734964],[3276200682,3375364842]]],[[[1002851280,1201179600],[5808609360,6205266000],[4861537920,5059866240]],[[3828134520,4224791160],[15327159120,16120472400],[11610584280,12007240920]],[[2839228200,3037556520],[9546439680,9943096320],[6762991320,6961319640]]],[[[601401479,700565639],[3108033118,3306361438],[2534521559,2633685719]],[[2115907318,2314235638],[8074813196,8471469836],[6014685718,6213014038]],[[1521478319,1620642479],[4980725038,5179053358],[3487136639,3586300799]]]]

private theorem identity_1019 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(22321989 / 154255360 : ℝ)) =
      tensor4 coefficients_1019 ((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1019, p_variance] <;> ring

private theorem negative_1019 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (51 / 64 : ℝ))
    (h1l : (17 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1019 ((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1019] at hp
  linarith only [hp]

private theorem node_1032 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (51 / 64 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (17 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_1018 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_1019 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_1020 : List (List (List (List ℕ))) :=
  [[[[97065401,295393721],[3939514642,4336171282],[3898229081,4096557401]],[[3790768402,4187425042],[15202457444,15995770724],[11523248722,11919905362]],[[3749482841,3947811161],[11374502482,11771159122],[7680799481,7879127801]]],[[[586480638,983137278],[8678835996,9472149276],[8203915038,8600571678]],[[8381343516,9174656796],[32034742392,33621368952],[23876518236,24669831516]],[[7906422558,8303079198],[23579025756,24372339036],[15784162878,16180819518]]],[[[490107239,688435559],[4740705358,5137361998],[4306377959,4504706279]],[[4591959118,4988615758],[16835052956,17628366236],[12354653518,12751310158]],[[4157631719,4355960039],[12205907278,12602563918],[8104055399,8302383719]]]]

private theorem identity_1020 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(97065401 / 5553192960 : ℝ)) =
      tensor4 coefficients_1020 ((x0-(51 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(51 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1020, p_variance] <;> ring

private theorem negative_1020 (x0 x1 x2 x3 : ℝ)
    (h0l : (51 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1020 ((x0-(51 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(51 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1020] at hp
  linarith only [hp]

private theorem node_1031 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (51 / 64 : ℝ)
  · exact node_1032 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1020 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_1021 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_1021 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_1021 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1021, p_qmass] <;> ring

private theorem negative_1021 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1021 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1021] at hp
  linarith only [hp]

private theorem node_1030 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_1031 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_1021 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_1022 : List (List (List (List ℕ))) :=
  [[[[448566201,547730361],[1857591522,2055919842],[1422970281,1522134441]],[[1825053282,2023381602],[5603563044,6000219684],[3806399682,4004728002]],[[1390432041,1489596201],[3773861442,3972189762],[2397374361,2496538521]]],[[[1100168838,1298497158],[4128809436,4525466076],[3056530518,3254858838]],[[4063732956,4460389596],[12049485912,12842799192],[8041532796,8438189436]],[[2991454038,3189782358],[7976456316,8373112956],[5012892198,5211220518]]],[[[652294639,751458799],[2272601918,2470930238],[1634252239,1733416399]],[[2240063678,2438391998],[6448690876,6845347516],[4236517118,4434845438]],[[1601713999,1700878159],[4203978878,4402307198],[2616209839,2715373999]]]]

private theorem identity_1022 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(49840689 / 154255360 : ℝ)) =
      tensor4 coefficients_1022 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1022, p_variance] <;> ring

private theorem negative_1022 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1022 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1022] at hp
  linarith only [hp]

private theorem node_1029 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_1030 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1022 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_1023 : List (List (List (List ℕ))) :=
  [[[[429972921,529137081],[2790160722,2988489042],[2415967641,2515131801]],[[1783218402,1981546722],[7491943044,7888599684],[5820284322,6018612642]],[[1367190441,1466354601],[4729672242,4928000562],[3418261641,3517425801]]],[[[1062982278,1261310598],[6001501356,6398157996],[5050078758,5248407078]],[[3980063196,4376719836],[15841352952,16634666232],[12084409116,12481065756]],[[2944970838,3143299158],[9895631436,10292288076],[7062220278,7260548598]]],[[[633701359,732865519],[3212724638,3411052958],[2634803119,2733967279]],[[2198228798,2396557118],[8352177916,8748834556],[6265508798,6463837118]],[[1578472399,1677636559],[5167343198,5365671518],[3644650639,3743814799]]]]

private theorem identity_1023 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(6824967 / 22036480 : ℝ)) =
      tensor4 coefficients_1023 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1023, p_variance] <;> ring

private theorem negative_1023 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1023 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1023] at hp
  linarith only [hp]

private theorem node_1028 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_1029 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1023 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_1022 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (25 / 32 : ℝ)
  · exact node_1023 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_1028 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_1024 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_1024 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_1024 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1024, p_qmass] <;> ring

private theorem negative_1024 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1024 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1024] at hp
  linarith only [hp]

private theorem node_1021 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_1022 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_1024 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_1025 : List (List (List (List ℕ))) :=
  [[[[103852408,128643448],[452903696,502485776],[356023768,380814808]],[[445931216,495513296],[1398529312,1497693472],[966543056,1016125136]],[[349051288,373842328],[959570576,1009152656],[617491768,642282808]]],[[[260006304,309588384],[1014187128,1113351288],[768125784,817707864]],[[1000242168,1099406328],[3021371616,3219699936],[2049019368,2148183528]],[[754180824,803762904],[2035074408,2134238568],[1294838544,1344420624]]],[[[156499897,181290937],[561975434,611557514],[412448017,437239057]],[[555002954,604585034],[1624226308,1723390468],[1083168314,1132750394]],[[405475537,430266577],[1076195834,1125777914],[677692777,702483817]]]]

private theorem identity_1025 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(12981551 / 21692160 : ℝ)) =
      tensor4 coefficients_1025 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1025, p_variance] <;> ring

private theorem negative_1025 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1025 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1025] at hp
  linarith only [hp]

private theorem node_1020 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_1021 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1025 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_1026 : List (List (List (List ℕ))) :=
  [[[[99204088,123995128],[693454256,743036336],[622140088,646931128]],[[434310416,483892496],[1891251232,1990415392],[1512720656,1562302736]],[[342078808,366869848],[1211741936,1261324016],[897553048,922344088]]],[[[250709664,300291744],[1499065008,1598229168],[1304135184,1353717264]],[[977000568,1076164728],[4014368976,4212697296],[3148928088,3248092248]],[[740235864,789817944],[2543193888,2642358048],[1858737864,1908319944]]],[[[151851577,176642617],[806302754,855884834],[682341097,707132137]],[[543382154,592964234],[2124501748,2223665908],[1636899434,1686481514]],[[398503057,423294097],[1332143954,1381726034],[961530817,986321857]]]]

private theorem identity_1026 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(12400511 / 21692160 : ℝ)) =
      tensor4 coefficients_1026 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1026, p_variance] <;> ring

private theorem negative_1026 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1026 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1026] at hp
  linarith only [hp]

private theorem node_1019 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_1020 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1026 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_1027 : List (List (List (List ℕ))) :=
  [[[[18349145,67931225],[976821010,1075985170],[1014251705,1063833785]],[[939634450,1038798610],[3889667300,4087995620],[3061592530,3160756690]],[[977065145,1026647225],[3024405970,3123570130],[2103120665,2152702745]]],[[[135131750,234295910],[2165615980,2363944300],[2142043910,2241208070]],[[2091242860,2289571180],[8233496600,8630153240],[6365373100,6563701420]],[[2067670790,2166834950],[6290999980,6489328300],[4334888870,4434053030]]],[[[117474607,167056687],[1190178974,1289343134],[1128484207,1178066287]],[[1152992414,1252156574],[4346597308,4544925628],[3305164574,3404328734]],[[1091297647,1140879727],[3267978014,3367142174],[2232460207,2282042287]]]]

private theorem identity_1027 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(3669829 / 69414912 : ℝ)) =
      tensor4 coefficients_1027 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1027, p_variance] <;> ring

private theorem negative_1027 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1027 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1027] at hp
  linarith only [hp]

private theorem node_1018 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 16 : ℝ)
  · exact node_1019 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1027 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_1028 : List (List (List (List ℕ))) :=
  [[[[19038019,61317638,38406019],[6255139,35751878,25623139]],[[31820899,86883398,51188899],[19038019,61317638,38406019]]],[[[34307166,115097532,73043166],[8160366,62803932,46896366]],[[60453966,167391132,99189966],[34307166,115097532,73043166]]],[[[15089589,53420778,34457589],[1725669,26692938,21093669]],[[28453509,80148618,47821509],[15089589,53420778,34457589]]]]

private theorem identity_1028 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(191741 / 6886400 : ℝ)) =
      tensor4 coefficients_1028 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1028, p_coupled] <;> ring

private theorem negative_1028 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1028 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1028] at hp
  linarith only [hp]

private theorem node_1017 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_1018 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_1028 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_1029 : List (List (List (List ℕ))) :=
  [[[[3],[15]],[[15],[27]]],[[[6],[18]],[[18],[30]]]]

private theorem identity_1029 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_1029 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1029, p_mass] <;> ring

private theorem negative_1029 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1029 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1029] at hp
  linarith only [hp]

private theorem node_1016 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_1017 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_1029 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_1030 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[15],[39]]],[[[6],[30]],[[18],[42]]]]

private theorem identity_1030 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_1030 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1030, p_mass] <;> ring

private theorem negative_1030 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1030 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1030] at hp
  linarith only [hp]

private theorem node_1015 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 4 : ℝ)
  · exact node_1016 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_1030 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_1031 : List (List (List (List ℕ))) :=
  [[[[16977969,41769009],[511570818,561152898],[550372689,575163729]],[[492977538,542559618],[2071337796,2170501956],[1689919938,1739502018]],[[531779409,556570449],[1671326658,1720908738],[1195327089,1220118129]]],[[[83864670,133446750],[1138066140,1237230300],[1165761150,1215343230]],[[1100879580,1200043740],[4402738680,4601067000],[3524978460,3624142620]],[[1128574590,1178156670],[3487791900,3586956060],[2470776990,2520359070]]],[[[67578703,92369743],[627879326,677461406],[616080463,640871503]],[[609286046,658868126],[2334168892,2433333052],[1836442526,1886024606]],[[597487183,622278223],[1817849246,1867431326],[1276141903,1300932943]]]]

private theorem identity_1031 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(1886441 / 9640960 : ℝ)) =
      tensor4 coefficients_1031 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1031, p_variance] <;> ring

private theorem negative_1031 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1031 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1031] at hp
  linarith only [hp]

private theorem node_1014 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 8 : ℝ)
  · exact node_1015 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1031 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_1032 : List (List (List (List ℕ))) :=
  [[[[4767349,13408298,6704149],[1571629,7016858,3508429]],[[7963069,19799738,9899869],[4767349,13408298,6704149]]],[[[8592480,24932160,12466080],[1910520,11568240,5784120]],[[15274440,38296080,19148040],[8592480,24932160,12466080]]],[[[3735352,11344304,5672152],[249112,4371824,2185912]],[[7221592,18316784,9158392],[3735352,11344304,5672152]]]]

private theorem identity_1032 (x0 x1 x2 x3 : ℝ) :
    (7747200 : ℝ)*(-p_coupled x0 x1 x2 x3-(31139 / 968400 : ℝ)) =
      tensor4 coefficients_1032 ((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1032, p_coupled] <;> ring

private theorem negative_1032 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1032 ((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1032] at hp
  linarith only [hp]

private theorem node_1013 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 2 : ℝ)
  · exact node_1014 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_1032 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_1033 : List (List (List (List ℕ))) :=
  [[[[9],[33]],[[33],[57]]],[[[15],[39]],[[39],[63]]]]

private theorem identity_1033 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_mass x0 x1 x2 x3-(9 / 16 : ℝ)) =
      tensor4 coefficients_1033 ((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1)) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1033, p_mass] <;> ring

private theorem negative_1033 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1033 ((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1033] at hp
  linarith only [hp]

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 2 : ℝ)
  · exact node_1013 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_1033 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part23
