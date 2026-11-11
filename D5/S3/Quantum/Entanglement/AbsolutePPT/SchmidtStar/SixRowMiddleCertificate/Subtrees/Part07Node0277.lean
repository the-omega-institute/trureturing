/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part07Node0277
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part07Node0277
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part07.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part07Node0277.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part07Node0277
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0272 : List (List (List (List ℕ))) :=
  [[[[433400777,309445577],[389241737,265286537]],[[705272434,457362034],[616954354,369043954]],[[237009257,113054057],[192850217,68895017]]],[[[845730426,597820026],[756250266,508339866]],[[1367821572,872000772],[1188861252,693040452]],[[452366346,204455946],[362886186,114975786]]],[[[412004831,288049631],[366683711,242728511]],[[661899502,413989102],[571257262,323346862]],[[215032271,91077071],[169711151,45755951]]]]

private theorem identity_0272 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(45755951 / 247910400 : ℝ)) =
      tensor4 coefficients_0272 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0272, p_headsq] <;> ring

private theorem negative_0272 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0272 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0272] at hp
  linarith only [hp]

private def coefficients_0273 : List (List (List (List ℕ))) :=
  [[[[1005015913,757105513],[916697833,668787433]],[[1547523986,1051703186],[1370887826,875067026]],[[507645673,259735273],[419327593,171417193]]],[[[1966727490,1470906690],[1788929250,1293108450]],[[3007858260,2016216660],[2652261780,1660620180]],[[971405970,475585170],[793607730,297786930]]],[[[961386759,713476359],[871906599,623996199]],[[1459684638,963863838],[1280724318,784903518]],[[463435479,215525079],[373955319,126044919]]]]

private theorem identity_0273 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(14004991 / 110182400 : ℝ)) =
      tensor4 coefficients_0273 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0273, p_headsq] <;> ring

private theorem negative_0273 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0273 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0273] at hp
  linarith only [hp]

private def coefficients_0274 : List (List (List (List ℕ))) :=
  [[[[43376728,92958808],[1000148336,1099312496],[984661528,1034243608]],[[536478416,635642576],[2932284832,3130613152],[2451586256,2550750416]],[[500074168,549656248],[1946081456,2045245616],[1473897208,1523479288]]],[[[186829168,285993328],[2208001616,2406329936],[2076952288,2176116448]],[[1276885016,1475213336],[6287533072,6684189712],[5122207736,5320536056]],[[1104000808,1203164968],[4107421376,4305749696],[3059200408,3158364568]]],[[[143798441,193380521],[1208545282,1307709442],[1092636761,1142218841]],[[741098602,840262762],[3356632244,3554960564],[2671313482,2770477642]],[[604272641,653854721],[2162031922,2261196082],[1585649201,1635231281]]]]

private theorem identity_0274 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(5422091 / 86768640 : ℝ)) =
      tensor4 coefficients_0274 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0274, p_variance] <;> ring

private theorem negative_0274 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0274 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0274] at hp
  linarith only [hp]

private theorem node_0282 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0273 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0274 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0275 : List (List (List (List ℕ))) :=
  [[[[492198857,368243657],[447458777,323503577]],[[752853274,504942874],[663373114,415462714]],[[243223217,119268017],[198483137,74527937]]],[[[962420728,714510328],[872359528,624449128]],[[1461462056,965641256],[1281339656,785518856]],[[464178928,216268528],[374117728,126207328]]],[[[470059462,346104262],[424738342,300783142]],[[708283964,460373564],[617641724,369731324]],[[220793302,96838102],[175472182,51516982]]]]

private theorem identity_0275 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(25758491 / 247910400 : ℝ)) =
      tensor4 coefficients_0275 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0275, p_headsq] <;> ring

private theorem negative_0275 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0275 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0275] at hp
  linarith only [hp]

private def coefficients_0276 : List (List (List (List ℕ))) :=
  [[[[187175169,286339329],[2216247138,2414575458],[2084851809,2184015969]],[[1281353778,1479682098],[6311577636,6708234276],[5141783538,5340111858]],[[1108123569,1207287729],[4123220418,4321548738],[3070876689,3170040849]]],[[[575885766,774214086],[4850672172,5247328812],[4386346086,4584674406]],[[2973331932,3369988572],[13474618104,14267931384],[10724405532,11121062172]],[[2425336086,2623664406],[8679725772,9076382412],[6365949366,6564277686]]],[[[389402599,488566759],[2635809038,2834137358],[2302186279,2401350439]],[[1693362158,1891690478],[7165808476,7562465116],[5584005998,5782334318]],[[1317904519,1417068679],[4557889358,4756217678],[3295764679,3394928839]]]]

private theorem identity_0276 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(20797241 / 154255360 : ℝ)) =
      tensor4 coefficients_0276 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0276, p_variance] <;> ring

private theorem negative_0276 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0276 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0276] at hp
  linarith only [hp]

private theorem node_0283 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0275 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0276 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0281 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 32 : ℝ)
  · exact node_0282 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0283 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0277 : List (List (List (List ℕ))) :=
  [[[[881060713,633150313],[792742633,544832233]],[[1299613586,803792786],[1122977426,627156626]],[[383690473,135780073],[295372393,47461993]]],[[[1718817090,1222996290],[1541018850,1045198050]],[[2512037460,1520395860],[2156440980,1164799380]],[[723495570,227674770],[545697330,49876530]]],[[[837431559,589521159],[747951399,500040999]],[[1211774238,715953438],[1032813918,536993118]],[[339480279,91569879],[250000119,2089719]]]]

private theorem identity_0277 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(232191 / 110182400 : ℝ)) =
      tensor4 coefficients_0277 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0277, p_headsq] <;> ring

private theorem negative_0277 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0277 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0277] at hp
  linarith only [hp]

private def coefficients_0278 : List (List (List (List ℕ))) :=
  [[[[68167768,117749848],[1049730416,1148894576],[1009452568,1059034648]],[[586060496,685224656],[3031448992,3229777312],[2501168336,2600332496]],[[524865208,574447288],[1995663536,2094827696],[1498688248,1548270328]]],[[[236411248,335575408],[2307165776,2505494096],[2126534368,2225698528]],[[1376049176,1574377496],[6485861392,6882518032],[5221371896,5419700216]],[[1153582888,1252747048],[4206585536,4404913856],[3108782488,3207946648]]],[[[168589481,218171561],[1258127362,1357291522],[1117427801,1167009881]],[[790680682,889844842],[3455796404,3654124724],[2720895562,2820059722]],[[629063681,678645761],[2211614002,2310778162],[1610440241,1660022321]]]]

private theorem identity_0278 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(8520971 / 86768640 : ℝ)) =
      tensor4 coefficients_0278 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0278, p_variance] <;> ring

private theorem negative_0278 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0278 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0278] at hp
  linarith only [hp]

private theorem node_0285 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0277 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0278 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0279 : List (List (List (List ℕ))) :=
  [[[[418890977,294935777],[396520937,272565737]],[[606237514,358327114],[561497434,313587034]],[[169915337,45960137],[147545297,23590097]]],[[[815804968,567894568],[770774368,522863968]],[[1168230536,672409736],[1078169336,582348536]],[[317563168,69652768],[272532568,24622168]]],[[[396751582,272796382],[374091022,250135822]],[[561668204,313757804],[516347084,268436684]],[[147485422,23530222],[124824862,869662]]]]

private theorem identity_0279 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(434831 / 247910400 : ℝ)) =
      tensor4 coefficients_0279 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0279, p_headsq] <;> ring

private theorem negative_0279 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0279 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0279] at hp
  linarith only [hp]

private def coefficients_0280 : List (List (List (List ℕ))) :=
  [[[[241405569,340569729],[1399111218,1597439538],[1171650609,1270814769]],[[1394462898,1592791218],[4654064196,5050720836],[3287491218,3485819538]],[[1167002289,1266166449],[3282842898,3481171218],[2129785569,2228949729]]],[[[684346566,882674886],[3208846812,3605503452],[2552390166,2750718486]],[[3199550172,3596206812],[10144484184,10937797464],[7000713852,7397370492]],[[2543093526,2741421846],[6991417212,7388073852],[4476213606,4674541926]]],[[[443632999,542797159],[1811119598,2009447918],[1381431559,1480595719]],[[1806471278,2004799598],[5493187996,5889844636],[3714606638,3912934958]],[[1376783239,1475947399],[3709958318,3908286638],[2347120039,2446284199]]]]

private theorem identity_0280 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(26822841 / 154255360 : ℝ)) =
      tensor4 coefficients_0280 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0280, p_variance] <;> ring

private theorem negative_0280 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0280 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0280] at hp
  linarith only [hp]

private theorem node_0287 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0279 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0280 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0281 : List (List (List (List ℕ))) :=
  [[[[236757249,335921409],[2315411298,2513739618],[2134433889,2233598049]],[[1380517938,1578846258],[6509905956,6906562596],[5240947698,5439276018]],[[1157705649,1256869809],[4222384578,4420712898],[3120458769,3219622929]]],[[[675049926,873378246],[5049000492,5445657132],[4485510246,4683838566]],[[3171660252,3568316892],[13871274744,14664588024],[10922733852,11319390492]],[[2524500246,2722828566],[8878054092,9274710732],[6465113526,6663441846]]],[[[438984679,538148839],[2734973198,2933301518],[2351768359,2450932519]],[[1792526318,1990854638],[7364136796,7760793436],[5683170158,5881498478]],[[1367486599,1466650759],[4657053518,4855381838],[3345346759,3444510919]]]]

private theorem identity_0281 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(26306361 / 154255360 : ℝ)) =
      tensor4 coefficients_0281 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0281, p_variance] <;> ring

private theorem negative_0281 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0281 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0281] at hp
  linarith only [hp]

private theorem node_0286 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0287 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0281 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0284 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 32 : ℝ)
  · exact node_0285 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0286 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0280 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0281 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0284 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0282 : List (List (List (List ℕ))) :=
  [[[[69093442,93884482],[372346004,421928084],[310225042,335016082]],[[372346004,421928084],[1229279368,1328443528],[870878324,920460404]],[[310225042,335016082],[870878324,920460404],[567625762,592416802]]],[[[190113120,239695200],[852321240,951485400],[676153080,725735160]],[[852321240,951485400],[2681370720,2879699040],[1856939400,1956103560]],[[676153080,725735160],[1856939400,1956103560],[1194731280,1244313360]]],[[[121365679,146156719],[480667238,530249318],[366274039,391065079]],[[480667238,530249318],[1453475356,1552639516],[986753078,1036335158]],[[366274039,391065079],[986753078,1036335158],[627451519,652242559]]]]

private theorem identity_0282 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(34546721 / 86768640 : ℝ)) =
      tensor4 coefficients_0282 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0282, p_variance] <;> ring

private theorem negative_0282 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0282 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0282] at hp
  linarith only [hp]

private theorem node_0279 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0280 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0282 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0278 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0272 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0279 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0283 : List (List (List (List ℕ))) :=
  [[[[211949591,149971991],[189289031,127311431]],[[342844102,218888902],[297522982,173567782]],[[113463311,51485711],[90802751,28825151]]],[[[413038800,289083600],[367136640,243181440]],[[663676920,415766520],[571872600,323962200]],[[215775720,91820520],[169873560,45918360]]],[[[200926800,138949200],[177685200,115707600]],[[320508000,196552800],[274024800,150069600]],[[102150000,40172400],[78908400,16930800]]]]

private theorem identity_0283 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(4703 / 34432 : ℝ)) =
      tensor4 coefficients_0283 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0283, p_headsq] <;> ring

private theorem negative_0283 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0283 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0283] at hp
  linarith only [hp]

private def coefficients_0284 : List (List (List (List ℕ))) :=
  [[[[963454697,715544297],[872812457,624902057]],[[1463239474,967418674],[1281954994,786134194]],[[464922377,217011977],[374280137,126369737]]],[[[1882305786,1386484986],[1699859226,1204038426]],[[2836690692,1845049092],[2471797572,1480155972]],[[884660106,388839306],[702213546,206392746]]],[[[918526271,670615871],[826721951,578811551]],[[1372801582,876980782],[1189192942,693372142]],[[419412911,171502511],[327608591,79698191]]]]

private theorem identity_0284 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(79698191 / 991641600 : ℝ)) =
      tensor4 coefficients_0284 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0284, p_headsq] <;> ring

private theorem negative_0284 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0284 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0284] at hp
  linarith only [hp]

private def coefficients_0285 : List (List (List (List ℕ))) :=
  [[[[144144442,193726522],[1216790804,1315954964],[1100536282,1150118362]],[[745567364,844731524],[3380676808,3579005128],[2690889284,2790053444]],[[608395402,657977482],[2177830964,2276995124],[1597325482,1646907562]]],[[[389748600,488912760],[2644054560,2842382880],[2310085800,2409249960]],[[1697830920,1896159240],[7189853040,7586509680],[5603581800,5801910120]],[[1322027280,1421191440],[4573688400,4772016720],[3307440960,3406605120]]],[[[245950159,295532239],[1427955758,1527119918],[1209895519,1259477599]],[[952955558,1052119718],[3810560236,4008888556],[2913384518,3012548678]],[[713977879,763559959],[2396549438,2495713598],[1710461479,1760043559]]]]

private theorem identity_0285 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(72072221 / 347074560 : ℝ)) =
      tensor4 coefficients_0285 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0285, p_variance] <;> ring

private theorem negative_0285 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0285 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0285] at hp
  linarith only [hp]

private theorem node_0292 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0284 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0285 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0286 : List (List (List (List ℕ))) :=
  [[[[471093431,347138231],[425191271,301236071]],[[710061382,462150982],[618257062,370346662]],[[221536751,97581551],[175634591,51679391]]],[[[919560240,671649840],[827174880,579264480]],[[1374579000,878758200],[1189808280,693987480]],[[420156360,172245960],[327771000,79860600]]],[[[448304400,324349200],[401821200,277866000]],[[664192800,416282400],[571226400,323316000]],[[198457200,74502000],[151974000,28018800]]]]

private theorem identity_0286 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(7783 / 137728 : ℝ)) =
      tensor4 coefficients_0286 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0286, p_headsq] <;> ring

private theorem negative_0286 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0286 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0286] at hp
  linarith only [hp]

private def coefficients_0287 : List (List (List (List ℕ))) :=
  [[[[390094601,489258761],[2652300082,2850628402],[2317985321,2417149481]],[[1702299682,1900628002],[7213897604,7610554244],[5623157602,5821485922]],[[1326150041,1425314201],[4589487442,4787815762],[3319117241,3418281401]]],[[[984492638,1182820958],[5728314076,6124970716],[4855381118,5053709438]],[[3820759756,4217416396],[15290330072,16083643352],[11692689676,12089346316]],[[2864157038,3062485358],[9617795836,10014452476],[6865198478,7063526798]]],[[[595090039,694254199],[3077397998,3275726318],[2538087799,2637251959]],[[2119844078,2318172398],[8079200476,8475857116],[6070916078,6269244398]],[[1538698999,1637863159],[5029692398,5228020718],[3546773239,3645937399]]]]

private theorem identity_0287 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(390094601 / 1388298240 : ℝ)) =
      tensor4 coefficients_0287 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0287, p_variance] <;> ring

private theorem negative_0287 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0287 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0287] at hp
  linarith only [hp]

private theorem node_0293 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0286 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0287 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0291 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 32 : ℝ)
  · exact node_0292 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0293 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0288 : List (List (List (List ℕ))) :=
  [[[[754570817,630615617],[709249697,585294497]],[[1045471714,797561314],[954829474,706919074]],[[256038497,132083297],[210717377,86762177]]],[[[1464538026,1216627626],[1373314746,1125404346]],[[2001155172,1505334372],[1818708612,1322887812]],[[466892346,218981946],[375669066,127758666]]],[[[709642391,585687191],[663740231,539785031]],[[955033822,707123422],[863229502,615319102]],[[210529031,86573831],[164626871,40671671]]]]

private theorem identity_0288 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(40671671 / 991641600 : ℝ)) =
      tensor4 coefficients_0288 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0288, p_headsq] <;> ring

private theorem negative_0288 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0288 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0288] at hp
  linarith only [hp]

private def coefficients_0289 : List (List (List (List ℕ))) :=
  [[[[78651827,258017254,175491827],[33330707,167375014,130170707]],[[123972947,348659494,220812947],[78651827,258017254,175491827]]],[[[142333086,486093372,336013086],[51109806,303646812,244789806]],[[233556366,668539932,427236366],[142333086,486093372,336013086]]],[[[63501701,227717002,160341701],[17599541,135912682,114439541]],[[109403861,319521322,206243861],[63501701,227717002,160341701]]]]

private theorem identity_0289 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(17599541 / 991641600 : ℝ)) =
      tensor4 coefficients_0289 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0289, p_coupled] <;> ring

private theorem negative_0289 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0289 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0289] at hp
  linarith only [hp]

private theorem node_0297 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0288 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0289 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0290 : List (List (List (List ℕ))) :=
  [[[[171259642,220841722],[804446084,903610244],[640158922,689741002]],[[802121924,901286084],[2544366568,2742694888],[1756189604,1855353764]],[[637834762,687416842],[1753865444,1853029604],[1123003162,1172585242]]],[[[443979000,543143160],[1815588360,2013916680],[1385554320,1484718480]],[[1810940040,2009268360],[5509679040,5906335680],[3726628920,3924957240]],[[1380906000,1480070160],[3721980600,3920308920],[2355019560,2454183720]]],[[[273065359,322647439],[1011834278,1110998438],[745741399,795323479]],[[1009510118,1108674278],[2966696476,3165024796],[1971131318,2070295478]],[[743417239,792999319],[1968807158,2067971318],[1232362399,1281944479]]]]

private theorem identity_0290 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(85629821 / 347074560 : ℝ)) =
      tensor4 coefficients_0290 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0290, p_variance] <;> ring

private theorem negative_0290 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0290 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0290] at hp
  linarith only [hp]

private theorem node_0296 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0297 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0290 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0291 : List (List (List (List ℕ))) :=
  [[[[168935482,218517562],[1266372884,1365537044],[1125327322,1174909402]],[[795149444,894313604],[3479840968,3678169288],[2740471364,2839635524]],[[633186442,682768522],[2227413044,2326577204],[1622116522,1671698602]]],[[[439330680,538494840],[2743218720,2941547040],[2359667880,2458832040]],[[1796995080,1995323400],[7388181360,7784838000],[5702745960,5901074280]],[[1371609360,1470773520],[4672852560,4871180880],[3357023040,3456187200]]],[[[270741199,320323279],[1477537838,1576701998],[1234686559,1284268639]],[[1002537638,1101701798],[3909724396,4108052716],[2962966598,3062130758]],[[738768919,788350999],[2446131518,2545295678],[1735252519,1784834599]]]]

private theorem identity_0291 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(84467741 / 347074560 : ℝ)) =
      tensor4 coefficients_0291 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0291, p_variance] <;> ring

private theorem negative_0291 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0291 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0291] at hp
  linarith only [hp]

private theorem node_0295 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0296 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0291 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0292 : List (List (List (List ℕ))) :=
  [[[[366506231,304528631],[343555151,281577551]],[[500886982,376931782],[454984822,331029622]],[[116949551,54971951],[93998471,32020871]]],[[[710385840,586430640],[664193160,540237960]],[[956230200,708319800],[863844840,615934440]],[[210981960,87026760],[164789280,40834080]]],[[[343717200,281739600],[320475600,258498000]],[[455018400,331063200],[408535200,284580000]],[[93870000,31892400],[70628400,8650800]]]]

private theorem identity_0292 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(2403 / 137728 : ℝ)) =
      tensor4 coefficients_0292 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0292, p_headsq] <;> ring

private theorem negative_0292 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0292 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0292] at hp
  linarith only [hp]

private def coefficients_0293 : List (List (List (List ℕ))) :=
  [[[[35773421,121903642,84193421],[12822341,76001482,61242341]],[[58724501,167805802,107144501],[35773421,121903642,84193421]]],[[[63882000,228477600,160722000],[17689320,136092240,114529320]],[[110074680,320862960,206914680],[63882000,228477600,160722000]]],[[[28018800,106394400,76438800],[4777200,59911200,53197200]],[[51260400,152877600,99680400],[28018800,106394400,76438800]]]]

private theorem identity_0293 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(1327 / 137728 : ℝ)) =
      tensor4 coefficients_0293 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0293, p_coupled] <;> ring

private theorem negative_0293 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0293 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0293] at hp
  linarith only [hp]

private theorem node_0300 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0292 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0293 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0294 : List (List (List (List ℕ))) :=
  [[[[444325001,543489161],[1820057122,2018385442],[1389677081,1488841241]],[[1815408802,2013737122],[5526170084,5922826724],[3738651202,3936979522]],[[1385028761,1484192921],[3734002882,3932331202],[2362919081,2462083241]]],[[[1092953438,1291281758],[4056274636,4452931276],[2991211118,3189539438]],[[4046977996,4443634636],[11899767992,12693081272],[7908569836,8305226476]],[[2981914478,3180242798],[7899273196,8295929836],[4945248638,5143576958]]],[[[649320439,748484599],[2237601518,2435929838],[1602226039,1701390199]],[[2232953198,2431281518],[6376365916,6773022556],[4171302638,4369630958]],[[1597577719,1696741879],[4166654318,4364982638],[2583021559,2682185719]]]]

private theorem identity_0294 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(444325001 / 1388298240 : ℝ)) =
      tensor4 coefficients_0294 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0294, p_variance] <;> ring

private theorem negative_0294 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0294 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0294] at hp
  linarith only [hp]

private theorem node_0299 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0300 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0294 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0295 : List (List (List (List ℕ))) :=
  [[[[439676681,538840841],[2751464242,2949792562],[2367567401,2466731561]],[[1801463842,1999792162],[7412225924,7808882564],[5722321762,5920650082]],[[1375732121,1474896281],[4688651602,4886979922],[3368699321,3467863481]]],[[[1083656798,1281985118],[5926642396,6323299036],[4954545278,5152873598]],[[4019088076,4415744716],[15686986712,16480299992],[11891017996,12287674636]],[[2963321198,3161649518],[9816124156,10212780796],[6964362638,7162690958]]],[[[644672119,743836279],[3176562158,3374890478],[2587669879,2686834039]],[[2219008238,2417336558],[8277528796,8674185436],[6170080238,6368408558]],[[1588281079,1687445239],[5128856558,5327184878],[3596355319,3695519479]]]]

private theorem identity_0295 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(439676681 / 1388298240 : ℝ)) =
      tensor4 coefficients_0295 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0295, p_variance] <;> ring

private theorem negative_0295 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0295 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0295] at hp
  linarith only [hp]

private theorem node_0298 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0299 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0295 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0294 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 32 : ℝ)
  · exact node_0295 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0298 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0290 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0291 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0294 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0296 : List (List (List (List ℕ))) :=
  [[[[190459121,240041201],[856790002,955954162],[680275841,729857921]],[[856790002,955954162],[2697861764,2896190084],[1868961682,1968125842]],[[680275841,729857921],[1868961682,1968125842],[1202630801,1252212881]]],[[[486154718,585318878],[1931606476,2129934796],[1473341678,1572505838]],[[1931606476,2129934796],[5846883512,6243540152],[3971056876,4169385196]],[[1473341678,1572505838],[3971056876,4169385196],[2525605118,2624769278]]],[[[296387599,345969679],[1076200478,1175364638],[793757839,843339919]],[[1076200478,1175364638],[3151789756,3350118076],[2103479198,2202643358]],[[793757839,843339919],[2103479198,2202643358],[1323666319,1373248399]]]]

private theorem identity_0296 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(190459121 / 347074560 : ℝ)) =
      tensor4 coefficients_0296 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0296, p_variance] <;> ring

private theorem negative_0296 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0296 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0296] at hp
  linarith only [hp]

private theorem node_0289 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0290 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0296 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0288 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0283 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0289 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 16 : ℝ)
  · exact node_0278 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0288 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part07Node0277
