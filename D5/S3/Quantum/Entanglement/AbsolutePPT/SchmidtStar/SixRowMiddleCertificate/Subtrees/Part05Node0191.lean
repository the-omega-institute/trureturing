/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part05Node0191
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part05Node0191
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part05Node0191.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part05Node0191
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0186 : List (List (List (List ℕ))) :=
  [[[[54303306920629,30739919221429],[46792477091509,23229089392309]],[[102676584677738,55549809279338],[87654925019498,40528149621098]],[[41746074966709,18182687267509],[34235245137589,10671857438389]]],[[[216298421716180,122369137722580],[186248009063380,92318725069780]],[[407946755989160,220088188001960],[347845930683560,159987362696360]],[[165230723149780,71301439156180],[135180310496980,41251026503380]]],[[[323027936211838,182619294829438],[277942841632318,137534200249918]],[[607690691376956,326873408612156],[517520502217916,236703219453116]],[[245172824776318,104764183393918],[200087730196798,59679088814398]]],[[[214373843183988,121090861603188],[184311567437508,91028585856708]],[[402247482151896,215681518990296],[342122930658936,155556967497336]],[[161637800398308,68354818817508],[131575524651828,38292543071028]]],[[[53341018360139,30100781867339],[45824254369499,22584017876699]],[[99826955271238,53346482285638],[84793427289958,38312954304358]],[[39949620397499,16709383904699],[32432856406859,9192619914059]]]]

private theorem identity_0186 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(9192619914059 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0186 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0186, p_headbox] <;> ring

private theorem negative_0186 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0186 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0186] at hp
  linarith only [hp]

private def coefficients_0187 : List (List (List (List ℕ))) :=
  [[[[70294867,256797734,182629267],[30784147,177776294,143118547]],[[109805587,335819174,222139987],[70294867,256797734,182629267]]],[[[130372406,493160812,355041206],[50769926,333955852,275438726]],[[209974886,652365772,434643686],[130372406,493160812,355041206]]],[[[59897981,236003962,172232381],[19806221,155820442,132140621]],[[99989741,316187482,212324141],[59897981,236003962,172232381]]]]

private theorem identity_0187 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(19806221 / 991641600 : ℝ)) =
      tensor4 coefficients_0187 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0187, p_coupled] <;> ring

private theorem negative_0187 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0187 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0187] at hp
  linarith only [hp]

private theorem node_0199 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0186 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0187 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0188 : List (List (List (List ℕ))) :=
  [[[[92250072,141832152],[641197584,740361744],[555919992,605502072]],[[634225104,733389264],[2198114208,2396442528],[1577834064,1676998224]],[[548947512,598529592],[1570861584,1670025744],[1028886552,1078468632]]],[[[286593360,385757520],[1490358360,1688686680],[1217709960,1316874120]],[[1476413400,1674741720],[4819708320,5216364960],[3371184840,3569513160]],[[1203765000,1302929160],[3357239880,3555568200],[2167419840,2266584000]]],[[[194689289,244271369],[849852778,949016938],[662135969,711718049]],[[842880298,942044458],[2622978116,2821306436],[1794042778,1893206938]],[[655163489,704745569],[1787070298,1886234458],[1138879289,1188461369]]]]

private theorem identity_0188 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(1281251 / 9640960 : ℝ)) =
      tensor4 coefficients_0188 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0188, p_variance] <;> ring

private theorem negative_0188 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0188 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0188] at hp
  linarith only [hp]

private theorem node_0198 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0199 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0188 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0189 : List (List (List (List ℕ))) :=
  [[[[87601752,137183832],[1093246704,1192410864],[1033534872,1083116952]],[[622604304,721768464],[3113833248,3312161568],[2547008784,2646172944]],[[541975032,591557112],[2034531504,2133695664],[1520446392,1570028472]]],[[[277296720,376460880],[2398233360,2596561680],[2176716480,2275880640]],[[1453171800,1651500120],[6658699920,7055356560],[5317087800,5515416120]],[[1189820040,1288984200],[4288356480,4486684800],[3154316280,3253480440]]],[[[190040969,239623049],[1305678658,1404842818],[1143527609,1193109689]],[[831259498,930423658],[3546250676,3744578996],[2770771018,2869935178]],[[648191009,697773089],[2254516978,2353681138],[1634215889,1683797969]]]]

private theorem identity_0189 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(173813 / 1377280 : ℝ)) =
      tensor4 coefficients_0189 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0189, p_variance] <;> ring

private theorem negative_0189 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0189 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0189] at hp
  linarith only [hp]

private theorem node_0197 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0198 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0189 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0190 : List (List (List (List ℕ))) :=
  [[[[27061730722099,15441612475699],[23303348726779,11683230480379]],[[50695920719678,27455684226878],[43179156729038,19938920236238]],[[20366031740779,8745913494379],[16607649745459,4987531499059]]],[[[107742038016680,61422582835880],[92706119927360,46386664746560]],[[201313852345240,108674941983640],[171242016166600,78603105805000]],[[80544467558960,34225012378160],[65508549469640,19189094288840]]],[[[160831988127800,91593774265400],[138275100189800,69036886327400]],[[299721020992000,161244593267200],[254607245116000,116130817391200]],[[119415785215400,50177571353000],[96858897277400,27620683415000]]],[[[106684782392000,60686247224000],[91645230188000,45646695020000]],[[198284168524000,106287098188000],[168205064116000,76207993780000]],[[78662298116000,32663762948000],[63622745912000,17624210744000]]],[[[26533099855000,15073441615000],[22772899495000,11313241255000]],[[49181075750000,26261759270000],[41660675030000,18741358550000]],[[19424947015000,7965288775000],[15664746655000,4205088415000]]]]

private theorem identity_0190 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(841017683 / 10154409984 : ℝ)) =
      tensor4 coefficients_0190 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0190, p_headbox] <;> ring

private theorem negative_0190 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0190 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0190] at hp
  linarith only [hp]

private def coefficients_0191 : List (List (List (List ℕ))) :=
  [[[[32783251,123670502,88950451],[12737371,83578742,68904571]],[[52829131,163762262,108996331],[32783251,123670502,88950451]]],[[[60278280,236764560,172612680],[19896000,156000000,132230400]],[[100660560,317529120,212994960],[60278280,236764560,172612680]]],[[[27405250,112914500,83572450],[7068850,72241700,63236050]],[[47741650,153587300,103908850],[27405250,112914500,83572450]]]]

private theorem identity_0191 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(141377 / 9916416 : ℝ)) =
      tensor4 coefficients_0191 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0191, p_coupled] <;> ring

private theorem negative_0191 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0191 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0191] at hp
  linarith only [hp]

private theorem node_0202 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0190 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0191 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0192 : List (List (List (List ℕ))) :=
  [[[[286939361,386103521],[1494827122,1693155442],[1221832721,1320996881]],[[1480882162,1679210482],[4836199364,5232856004],[3383207122,3581535442]],[[1207887761,1307051921],[3369262162,3567590482],[2175319361,2274483521]]],[[[779449158,977777478],[3408348636,3805005276],[2656789398,2855117718]],[[3380458716,3777115356],[10524894552,11318207832],[7200215676,7596872316]],[[2628899478,2827227798],[7172325756,7568982396],[4571316198,4769644518]]],[[[493201799,592365959],[1914905518,2113233838],[1435648679,1534812839]],[[1900960558,2099288878],[5691463196,6088119836],[3818392558,4016720878]],[[1421703719,1520867879],[3804447598,4002775918],[2396688839,2495852999]]]]

private theorem identity_0192 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(286939361 / 1388298240 : ℝ)) =
      tensor4 coefficients_0192 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0192, p_variance] <;> ring

private theorem negative_0192 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0192 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0192] at hp
  linarith only [hp]

private theorem node_0201 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0202 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0192 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0193 : List (List (List (List ℕ))) :=
  [[[[277642721,376806881],[2406478882,2604807202],[2184616001,2283780161]],[[1457640562,1655968882],[6682744484,7079401124],[5336663602,5534991922]],[[1193942801,1293106961],[4304155522,4502483842],[3165992561,3265156721]]],[[[760855878,959184198],[5239205676,5635862316],[4589909478,4788237798]],[[3333975516,3730632156],[14233091832,15026405112],[11122235676,11518892316]],[[2601009558,2799337878],[9049665996,9446322636],[6560216118,6758544438]]],[[[483905159,583069319],[2834110798,3032439118],[2405985479,2505149639]],[[1877718958,2076047278],[7553115356,7949771996],[5786956078,5985284398]],[[1407758759,1506922919],[4746894478,4945222798],[3394915559,3494079719]]]]

private theorem identity_0193 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(277642721 / 1388298240 : ℝ)) =
      tensor4 coefficients_0193 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0193, p_variance] <;> ring

private theorem negative_0193 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0193 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0193] at hp
  linarith only [hp]

private theorem node_0200 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0201 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0193 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0196 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 32 : ℝ)
  · exact node_0197 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0200 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0194 : List (List (List (List ℕ))) :=
  [[[[38116747,130463894,88473547],[18361387,90953174,68718187]],[[57872107,169974614,108228907],[38116747,130463894,88473547]]],[[[71124830,250710460,171838430],[31033070,170526940,131746670]],[[111216590,330893980,211930190],[71124830,250710460,171838430]]],[[[32828525,119887450,83185325],[12492125,79214650,62848925]],[[53164925,160560250,103521725],[32828525,119887450,83185325]]]]

private theorem identity_0194 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(499685 / 9916416 : ℝ)) =
      tensor4 coefficients_0194 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0194, p_coupled] <;> ring

private theorem negative_0194 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0194 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0194] at hp
  linarith only [hp]

private theorem node_0195 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0196 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0194 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0195 : List (List (List (List ℕ))) :=
  [[[[81021258,105812298],[397363716,446945796],[323314938,348105978]],[[395039556,444621636],[1276990632,1376154792],[895896036,945478116]],[[320990778,345781818],[893571876,943153956],[579553578,604344618]]],[[[214977504,264559584],[904374168,1003538328],[703341624,752923704]],[[899725848,998890008],[2780828256,2979156576],[1908992328,2008156488]],[[698693304,748275384],[1904344008,2003508168],[1219595664,1269177744]]],[[[134302247,159093287],[507702454,557284534],[380372687,405163727]],[[505378294,554960374],[1505221628,1604385788],[1013788294,1063370374]],[[378048527,402839567],[1011464134,1061046214],[640388087,665179127]]]]

private theorem identity_0195 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(4501181 / 9640960 : ℝ)) =
      tensor4 coefficients_0195 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0195, p_variance] <;> ring

private theorem negative_0195 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0195 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0195] at hp
  linarith only [hp]

private theorem node_0194 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0195 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0195 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0196 : List (List (List (List ℕ))) :=
  [[[[78697098,103488138],[632684916,682266996],[581877738,606668778]],[[388067076,437649156],[1759253832,1858417992],[1426966596,1476548676]],[[316342458,341133498],[1140513876,1190095956],[852061338,876852378]]],[[[210329184,259911264],[1378793328,1477957488],[1224243984,1273826064]],[[885780888,984945048],[3752908176,3951236496],[2978686968,3077851128]],[[689396664,738978744],[2402004768,2501168928],[1768387944,1817970024]]],[[[131978087,156769127],[746800414,796382494],[642712247,667503287]],[[498405814,547987894],[1995038348,2094202508],[1552412374,1601994454]],[[373400207,398191247],[1262182894,1311764974],[916672607,941463647]]]]

private theorem identity_0196 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(4372061 / 9640960 : ℝ)) =
      tensor4 coefficients_0196 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0196, p_variance] <;> ring

private theorem negative_0196 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0196 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0196] at hp
  linarith only [hp]

private theorem node_0193 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0194 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0196 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0197 : List (List (List (List ℕ))) :=
  [[[[53891482855621,30972166375621],[46371082135621,23451765655621]],[[100012717791242,54174084831242],[84971916351242,39133283391242]],[[39675177175621,16755860695621],[32154776455621,9235459975621]]],[[[214461165478484,123103703974484],[184377064126484,93019602622484]],[[396931140116968,214216217108968],[336762937412968,154048014404968]],[[156775688590484,65418227086484],[126691587238484,35334125734484]]],[[[319987079465326,183429478236526],[274858312757326,138300711528526]],[[590627053443452,317511850985852],[500369520027452,227254317569852]],[[232233148632526,95675547403726],[187104381924526,50546780695726]]],[[[212156574883524,121436491017924],[182069737414164,91349653548564]],[[390511531834488,209071364103288],[330337856895768,148897689164568]],[[152839933363764,62119849498164],[122753095894404,32033012028804]]],[[[52739174633499,30138546972699],[45217403240139,22616775579339]],[[96802893901638,51601638580038],[81759351114918,36558095793318]],[[37707292738539,15106665077739],[30185521345179,7584893684379]]]]

private theorem identity_0197 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(842765964931 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0197 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0197, p_headbox] <;> ring

private theorem negative_0197 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0197 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0197] at hp
  linarith only [hp]

private def coefficients_0198 : List (List (List (List ℕ))) :=
  [[[[60658579,237525158,172992979],[19985779,156179558,132320179]],[[101331379,318870758,213665779],[60658579,237525158,172992979]]],[[[110381598,453179196,335050398],[28454958,289325916,253123758]],[[192308238,617032476,416977038],[110381598,453179196,335050398]]],[[[49543461,215294922,161877861],[8289621,132787242,120624021]],[[90797301,297802602,203131701],[49543461,215294922,161877861]]]]

private theorem identity_0198 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(921069 / 110182400 : ℝ)) =
      tensor4 coefficients_0198 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0198, p_coupled] <;> ring

private theorem negative_0198 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0198 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0198] at hp
  linarith only [hp]

private theorem node_0209 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0197 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0198 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0199 : List (List (List (List ℕ))) :=
  [[[[195035290,244617370],[854321540,953485700],[666258730,715840810]],[[847349060,946513220],[2639469160,2837797480],[1806065060,1905229220]],[[659286250,708868330],[1799092580,1898256740],[1146778810,1196360890]]],[[[493547800,592711960],[1919374280,2117702600],[1439771440,1538935600]],[[1905429320,2103757640],[5707954240,6104610880],[3830414840,4028743160]],[[1425826480,1524990640],[3816469880,4014798200],[2404588360,2503752520]]],[[[298858511,348440591],[1065744742,1164908902],[773858711,823440791]],[[1058772262,1157936422],[3069869084,3268197404],[2025041782,2124205942]],[[766886231,816468311],[2018069302,2117233462],[1258155551,1307737631]]]]

private theorem identity_0199 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(19503529 / 69414912 : ℝ)) =
      tensor4 coefficients_0199 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0199, p_variance] <;> ring

private theorem negative_0199 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0199 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0199] at hp
  linarith only [hp]

private theorem node_0208 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0209 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0199 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0200 : List (List (List (List ℕ))) :=
  [[[[190386970,239969050],[1313924180,1413088340],[1151427130,1201009210]],[[835728260,934892420],[3570295240,3768623560],[2790346820,2889510980]],[[652313770,701895850],[2270316020,2369480180],[1645892170,1695474250]]],[[[484251160,583415320],[2842356320,3040684640],[2413885000,2513049160]],[[1882187720,2080516040],[7577159920,7973816560],[5806531880,6004860200]],[[1411881520,1511045680],[4762693520,4961021840],[3406591840,3505756000]]],[[[294210191,343792271],[1529124142,1628288302],[1262803871,1312385951]],[[1047151462,1146315622],[4008248684,4206577004],[3016877062,3116041222]],[[759913751,809495831],[2493069502,2592233662],[1761045671,1810627751]]]]

private theorem identity_0200 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(19038697 / 69414912 : ℝ)) =
      tensor4 coefficients_0200 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0200, p_variance] <;> ring

private theorem negative_0200 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0200 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0200] at hp
  linarith only [hp]

private theorem node_0207 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0208 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0200 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0201 : List (List (List (List ℕ))) :=
  [[[[32838561,132002721],[1882008162,2080336482],[1904949441,2004113601]],[[1844821602,2043149922],[7452458244,7849114884],[5719196322,5917524642]],[[1867762881,1966927041],[5682009762,5880338082],[3870026721,3969190881]]],[[[266462046,464790366],[4180693212,4577349852],[4025790846,4224119166]],[[4106320092,4502976732],[15768484344,16561797624],[11885283612,12281940252]],[[3951417726,4149746046],[11810910492,12207567132],[7971052446,8169380766]]],[[[234315487,333479647],[2300069054,2498397374],[2121533407,2220697567]],[[2262882494,2461210814],[8318794108,8715450748],[6167471294,6365799614]],[[2084346847,2183511007],[6130284734,6328613054],[4101717727,4200881887]]]]

private theorem identity_0201 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(521247 / 22036480 : ℝ)) =
      tensor4 coefficients_0201 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0201, p_variance] <;> ring

private theorem negative_0201 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0201 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0201] at hp
  linarith only [hp]

private theorem node_0206 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 32 : ℝ)
  · exact node_0207 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0201 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0202 : List (List (List (List ℕ))) :=
  [[[[17971357,63057914,43149757],[7803157,42721514,32981557]],[[28139557,83394314,53317957],[17971357,63057914,43149757]]],[[[33208824,120648048,83565624],[12581904,79394208,62938704]],[[53835744,161901888,104192544],[33208824,120648048,83565624]]],[[[15147688,57410576,40326088],[4688968,36493136,29867368]],[[25606408,78328016,50784808],[15147688,57410576,40326088]]]]

private theorem identity_0202 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(586121 / 15494400 : ℝ)) =
      tensor4 coefficients_0202 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0202, p_coupled] <;> ring

private theorem negative_0202 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0202 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0202] at hp
  linarith only [hp]

private theorem node_0205 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0206 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0202 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0203 : List (List (List (List ℕ))) :=
  [[[[215323505,264905585],[908842930,1008007090],[707464385,757046465]],[[904194610,1003358770],[2797319300,2995647620],[1921014610,2020178770]],[[702816065,752398145],[1916366290,2015530450],[1227495185,1277077265]]],[[[537900990,637065150],[2039747340,2238075660],[1529736270,1628900430]],[[2030450700,2228779020],[6053868600,6450525240],[4079197740,4277526060]],[[1520439630,1619603790],[4069901100,4268229420],[2577351390,2676515550]]],[[[323269487,372851567],[1132288414,1231452574],[822963887,872545967]],[[1127640094,1226804254],[3259317308,3457645628],[2159567134,2258731294]],[[818315567,867897647],[2154918814,2254082974],[1350548207,1400130287]]]]

private theorem identity_0203 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(43064701 / 69414912 : ℝ)) =
      tensor4 coefficients_0203 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0203, p_variance] <;> ring

private theorem negative_0203 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0203 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0203] at hp
  linarith only [hp]

private theorem node_0204 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0205 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0203 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0204 : List (List (List (List ℕ))) :=
  [[[[210675185,260257265],[1387038850,1486203010],[1232143505,1281725585]],[[890249650,989413810],[3776952740,3975281060],[2998262770,3097426930]],[[693519425,743101505],[2417803810,2516967970],[1780064225,1829646305]]],[[[528604350,627768510],[3003692700,3202021020],[2586648030,2685812190]],[[2002560780,2200889100],[8028242520,8424899160],[6248801100,6447129420]],[[1501846350,1601010510],[5080329660,5278657980],[3690042990,3789207150]]],[[[318621167,368203247],[1618037854,1717202014],[1355196527,1404778607]],[[1113695134,1212859294],[4254057788,4452386108],[3251922334,3351086494]],[[809018927,858601007],[2663909854,2763074014],[1910670767,1960252847]]]]

private theorem identity_0204 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(6019291 / 9916416 : ℝ)) =
      tensor4 coefficients_0204 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0204, p_variance] <;> ring

private theorem negative_0204 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0204 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0204] at hp
  linarith only [hp]

private theorem node_0203 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0204 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0204 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0192 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 16 : ℝ)
  · exact node_0193 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0203 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0205 : List (List (List (List ℕ))) :=
  [[[[9608507,30837814,19292507],[4669667,20960134,14353667]],[[14547347,40715494,24231347],[9608507,30837814,19292507]]],[[[17939848,59121296,37307848],[7771648,38784896,27139648]],[[28108048,79457696,47476048],[17939848,59121296,37307848]]],[[[8241562,28103924,17925562],[3012202,17645204,12696202]],[[13470922,38562644,23154922],[8241562,28103924,17925562]]]]

private theorem identity_0205 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(1506101 / 15494400 : ℝ)) =
      tensor4 coefficients_0205 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0205, p_coupled] <;> ring

private theorem negative_0205 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0205 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0205] at hp
  linarith only [hp]

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0192 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0205 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part05Node0191
