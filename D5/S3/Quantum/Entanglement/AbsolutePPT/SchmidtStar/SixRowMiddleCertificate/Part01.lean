/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part01
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part01
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part01.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part01
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0000 : List (List (List (List ℕ))) :=
  [[[[168075313,106097713],[149482033,87504433]],[[326853986,202898786],[289667426,165712226]],[[123916273,61938673],[105322993,43345393]]],[[[328726050,204770850],[290377410,166422210]],[[638277780,390367380],[561580500,313670100]],[[239826930,115871730],[201478290,77523090]]],[[[160325919,98348319],[140570559,78592959]],[[310774158,186818958],[271263438,147308238]],[[115585839,53608239],[95830479,33852879]]]]

private theorem identity_0000 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(3761431 / 6886400 : ℝ)) =
      tensor4 coefficients_0000 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0000, p_headsq] <;> ring

private theorem negative_0000 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0000 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0000] at hp
  linarith only [hp]

private def coefficients_0001 : List (List (List (List ℕ))) :=
  [[[[501601409,377646209],[464414849,340459649]],[[845159938,597249538],[770786818,522876418]],[[308696129,184740929],[271509569,147554369]]],[[[987191586,739281186],[911656386,663745986]],[[1657716372,1161895572],[1506645972,1010825172]],[[600799986,352889586],[525264786,277354386]]],[[[485265359,361310159],[446916719,322961519]],[[811906798,563996398],[735209518,487299118]],[[291779039,167823839],[253430399,129475199]]]]

private theorem identity_0001 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(129475199 / 247910400 : ℝ)) =
      tensor4 coefficients_0001 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0001, p_headsq] <;> ring

private theorem negative_0001 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0001 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0001] at hp
  linarith only [hp]

private def coefficients_0002 : List (List (List (List ℕ))) :=
  [[[[430714529,306759329],[412121249,288166049]],[[633661378,385750978],[596474818,348564418]],[[168084449,44129249],[149491169,25535969]]],[[[844836786,596926386],[807069186,559158786]],[[1233557172,737736372],[1158021972,662201172]],[[318995586,71085186],[281227986,33317586]]],[[[413797439,289842239],[394623119,270667919]],[[599246158,351335758],[560897518,312987118]],[[150586319,26631119],[131411999,7456799]]]]

private theorem identity_0002 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(7456799 / 247910400 : ℝ)) =
      tensor4 coefficients_0002 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0002, p_headsq] <;> ring

private theorem negative_0002 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0002 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0002] at hp
  linarith only [hp]

private def coefficients_0003 : List (List (List (List ℕ))) :=
  [[[[390719609,328742009],[372126329,310148729]],[[553671538,429716338],[516484978,392529778]],[[128089529,66111929],[109496249,47518649]]],[[[764265906,640310706],[726498306,602543106]],[[1072415412,824505012],[996880212,748969812]],[[238424706,114469506],[200657106,76701906]]],[[[373221479,311243879],[354047159,292069559]],[[518094238,394139038],[479745598,355790398]],[[110010359,48032759],[90836039,28858439]]]]

private theorem identity_0003 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(28858439 / 247910400 : ℝ)) =
      tensor4 coefficients_0003 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0003, p_headsq] <;> ring

private theorem negative_0003 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0003 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0003] at hp
  linarith only [hp]

private def coefficients_0004 : List (List (List (List ℕ))) :=
  [[[[41926139,138082678,92282939],[23332859,100896118,73689659]],[[60519419,175269238,110876219],[41926139,138082678,92282939]]],[[[79461846,267384492,180175446],[41694246,191849292,142407846]],[[117229446,342919692,217943046],[79461846,267384492,180175446]]],[[[37356149,128942698,87712949],[18181829,90594058,68538629]],[[56530469,167291338,106887269],[37356149,128942698,87712949]]]]

private theorem identity_0004 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(18181829 / 247910400 : ℝ)) =
      tensor4 coefficients_0004 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0004, p_coupled] <;> ring

private theorem negative_0004 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0004 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0004] at hp
  linarith only [hp]

private theorem node_0012 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0003 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0004 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0011 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0002 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0012 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0010 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0001 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0011 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0005 : List (List (List (List ℕ))) :=
  [[[[247314881,185337281],[228140561,166162961]],[[415317802,291362602],[376969162,253013962]],[[150571721,88594121],[131397401,69419801]]],[[[486299328,362344128],[447369648,323414448]],[[813684216,565773816],[735824856,487914456]],[[292522488,168567288],[253592808,129637608]]],[[[238822038,176844438],[219066678,157089078]],[[398041596,274086396],[358530876,234575676]],[[141788358,79810758],[122032998,60055398]]]]

private theorem identity_0005 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(3336411 / 6886400 : ℝ)) =
      tensor4 coefficients_0005 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0005, p_headsq] <;> ring

private theorem negative_0005 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0005 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0005] at hp
  linarith only [hp]

private def coefficients_0006 : List (List (List (List ℕ))) :=
  [[[[196086521,165097721],[186499361,155510561]],[[277998682,216021082],[258824362,196846762]],[[64480961,33492161],[54893801,23905001]]],[[[383552088,321574488],[364087248,302109648]],[[538464936,414509736],[499535256,375580056]],[[120050448,58072848],[100585608,38608008]]],[[[187303158,156314358],[177425478,146436678]],[[260141436,198163836],[240386076,178408476]],[[55407078,24418278],[45529398,14540598]]]]

private theorem identity_0006 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(807811 / 6886400 : ℝ)) =
      tensor4 coefficients_0006 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0006, p_headsq] <;> ring

private theorem negative_0006 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0006 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0006] at hp
  linarith only [hp]

private def coefficients_0007 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0007 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0007 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0007, p_qmass] <;> ring

private theorem negative_0007 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0007 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0007] at hp
  linarith only [hp]

private theorem node_0015 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0006 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0007 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0008 : List (List (List (List ℕ))) :=
  [[[[191438201,160449401],[181851041,150862241]],[[268702042,206724442],[249527722,187550122]],[[59832641,28843841],[50245481,19256681]]],[[[373964928,311987328],[354500088,292522488]],[[519290616,395335416],[480360936,356405736]],[[110463288,48485688],[90998448,29020848]]],[[[182364318,151375518],[172486638,141497838]],[[250263756,188286156],[230508396,168530796]],[[50468238,19479438],[40590558,9601758]]]]

private theorem identity_0008 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(533431 / 6886400 : ℝ)) =
      tensor4 coefficients_0008 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0008, p_headsq] <;> ring

private theorem negative_0008 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0008 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0008] at hp
  linarith only [hp]

private def coefficients_0009 : List (List (List (List ℕ))) :=
  [[[[20055611,67226422,45234011],[10468451,48052102,35646851]],[[29642771,86400742,54821171],[20055611,67226422,45234011]]],[[[37736448,129703296,88093248],[18271608,90773616,68628408]],[[57201288,168632976,107558088],[37736448,129703296,88093248]]],[[[17591058,62297316,42769458],[7713378,42541956,32891778]],[[27468738,82052676,52647138],[17591058,62297316,42769458]]]]

private theorem identity_0009 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(428521 / 6886400 : ℝ)) =
      tensor4 coefficients_0009 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0009, p_coupled] <;> ring

private theorem negative_0009 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0009 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0009] at hp
  linarith only [hp]

private theorem node_0016 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0008 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0009 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0014 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0015 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0016 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0013 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0005 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0014 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0009 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 16 : ℝ)
  · exact node_0010 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0013 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0010 : List (List (List (List ℕ))) :=
  [[[[19934323,63110246,39302323],[10637683,44516966,30005683]],[[29230963,81703526,48598963],[19934323,63110246,39302323]]],[[[37673430,121830060,76409430],[18499110,83481420,57235110]],[[56847750,160178700,95583750],[37673430,121830060,76409430]]],[[[17559549,58360698,36927549],[7681869,38605338,27049869]],[[27437229,78116058,46805229],[17559549,58360698,36927549]]]]

private theorem identity_0010 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(853541 / 6886400 : ℝ)) =
      tensor4 coefficients_0010 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0010, p_coupled] <;> ring

private theorem negative_0010 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0010 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0010] at hp
  linarith only [hp]

private theorem node_0008 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0009 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0010 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0011 : List (List (List (List ℕ))) :=
  [[[[483589169,359633969],[446402609,322447409]],[[809135458,561225058],[734762338,486851938]],[[290683889,166728689],[253497329,129542129]]],[[[950005026,702094626],[874469826,626559426]],[[1583343252,1087522452],[1432272852,936452052]],[[563613426,315703026],[488078226,240167826]]],[[[466091039,342135839],[427742399,303787199]],[[773558158,525647758],[696860878,448950478]],[[272604719,148649519],[234256079,110300879]]]]

private theorem identity_0011 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(110300879 / 247910400 : ℝ)) =
      tensor4 coefficients_0011 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0011, p_headsq] <;> ring

private theorem negative_0011 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0011 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0011] at hp
  linarith only [hp]

private def coefficients_0012 : List (List (List (List ℕ))) :=
  [[[[381713489,319735889],[363120209,301142609]],[[535659298,411704098],[498472738,374517538]],[[119083409,57105809],[100490129,38512529]]],[[[745672626,621717426],[707905026,583949826]],[[1035228852,787318452],[959693652,711783252]],[[219831426,95876226],[182063826,58108626]]],[[[363634319,301656719],[344459999,282482399]],[[498919918,374964718],[460571278,336616078]],[[100423199,38445599],[81248879,19271279]]]]

private theorem identity_0012 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(19271279 / 247910400 : ℝ)) =
      tensor4 coefficients_0012 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0012, p_headsq] <;> ring

private theorem negative_0012 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0012 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0012] at hp
  linarith only [hp]

private def coefficients_0013 : List (List (List (List ℕ))) :=
  [[[[32920019,120070438,83276819],[14326739,82883878,64683539]],[[51513299,157256998,101870099],[32920019,120070438,83276819]]],[[[60868566,230197932,161582166],[23100966,154662732,123814566]],[[98636166,305733132,199349766],[60868566,230197932,161582166]]],[[[27768989,109768378,78125789],[8594669,71419738,58951469]],[[46943309,148117018,97300109],[27768989,109768378,78125789]]]]

private theorem identity_0013 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(8594669 / 247910400 : ℝ)) =
      tensor4 coefficients_0013 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0013, p_coupled] <;> ring

private theorem negative_0013 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0013 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0013] at hp
  linarith only [hp]

private theorem node_0021 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0012 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0013 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0014 : List (List (List (List ℕ))) :=
  [[[[372707369,310729769],[354114089,292136489]],[[517647058,393691858],[480460498,356505298]],[[110077289,48099689],[91484009,29506409]]],[[[727079346,603124146],[689311746,565356546]],[[998042292,750131892],[922507092,674596692]],[[201238146,77282946],[163470546,39515346]]],[[[354047159,292069559],[334872839,272895239]],[[479745598,355790398],[441396958,317441758]],[[90836039,28858439],[71661719,9684119]]]]

private theorem identity_0014 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(9684119 / 247910400 : ℝ)) =
      tensor4 coefficients_0014 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0014, p_headsq] <;> ring

private theorem negative_0014 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0014 ((x0-0)/(1 / 16 : ℝ)) (1-((x0-0)/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0014] at hp
  linarith only [hp]

private def coefficients_0015 : List (List (List (List ℕ))) :=
  [[[[89252707,395427014,290679907],[14879587,246680774,216306787]],[[163625827,544173254,365053027],[89252707,395427014,290679907]]],[[[167400390,768643980,570254790],[17492070,468827340,420346470]],[[317308710,1068460620,720163110],[167400390,768643980,570254790]]],[[[77968125,372857850,279395325],[2432925,221787450,203860125]],[[153503325,523928250,354930525],[77968125,372857850,279395325]]]]

private theorem identity_0015 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(10813 / 4407296 : ℝ)) =
      tensor4 coefficients_0015 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0015, p_coupled] <;> ring

private theorem negative_0015 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0015 ((x0-0)/(1 / 32 : ℝ)) (1-((x0-0)/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0015] at hp
  linarith only [hp]

private def coefficients_0016 : List (List (List (List ℕ))) :=
  [[[[524618177,400662977],[486850577,362895377]],[[821178154,573267754],[745642954,497732554]],[[279128777,155173577],[241361177,117405977]]],[[[1030576144,782665744],[954459904,706549504]],[[1604745368,1108924568],[1452512888,956692088]],[[539306824,291396424],[463190584,215280184]]],[[[505795558,381840358],[467446918,343491718]],[[783242396,535331996],[706545116,458634716]],[[260015638,136060438],[221666998,97711798]]]]

private theorem identity_0016 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(48855899 / 247910400 : ℝ)) =
      tensor4 coefficients_0016 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0016, p_headsq] <;> ring

private theorem negative_0016 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0016 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0016] at hp
  linarith only [hp]

private def coefficients_0017 : List (List (List (List ℕ))) :=
  [[[[51482147,211425094,152195747],[13714547,135889894,114428147]],[[70365947,249192694,171079547],[32598347,173657494,133311947]]],[[[97522744,411967088,298949944],[21406504,259734608,222833704]],[[135580864,488083328,337008064],[59464624,335850848,260891824]]],[[[45950818,200362436,146664418],[7602178,123665156,108315778]],[[65125138,238711076,165838738],[26776498,162013796,127490098]]]]

private theorem identity_0017 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(3801089 / 247910400 : ℝ)) =
      tensor4 coefficients_0017 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0017, p_coupled] <;> ring

private theorem negative_0017 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0017 ((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0017] at hp
  linarith only [hp]

private theorem node_0024 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0016 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0017 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0023 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 32 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0015 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0024 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0022 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0014 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0023 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0020 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0021 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0022 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0019 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0011 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0020 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0018 : List (List (List (List ℕ))) :=
  [[[[238018241,176040641],[218843921,156866321]],[[396724522,272769322],[358375882,234420682]],[[141275081,79297481],[122100761,60123161]]],[[[467125008,343169808],[428195328,304240128]],[[775335576,527425176],[697476216,449565816]],[[273348168,149392968],[234418488,110463288]]],[[[228944358,166966758],[209188998,147211398]],[[378286236,254331036],[338775516,214820316]],[[131910678,69933078],[112155318,50177718]]]]

private theorem identity_0018 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(2787651 / 6886400 : ℝ)) =
      tensor4 coefficients_0018 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0018, p_headsq] <;> ring

private theorem negative_0018 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0018 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0018] at hp
  linarith only [hp]

private def coefficients_0019 : List (List (List (List ℕ))) :=
  [[[[186789881,155801081],[177202721,146213921]],[[259405402,197427802],[240231082,178253482]],[[55184321,24195521],[45597161,14608361]]],[[[364377768,302400168],[344912928,282935328]],[[500116296,376161096],[461186616,337231416]],[[100876128,38898528],[81411288,19433688]]],[[[177425478,146436678],[167547798,136558998]],[[240386076,178408476],[220630716,158653116]],[[45529398,14540598],[35651718,4662918]]]]

private theorem identity_0019 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(259051 / 6886400 : ℝ)) =
      tensor4 coefficients_0019 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0019, p_headsq] <;> ring

private theorem negative_0019 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0019 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0019] at hp
  linarith only [hp]

private def coefficients_0020 : List (List (List (List ℕ))) :=
  [[[[15407291,57929782,40585691],[5820131,38755462,30998531]],[[24994451,77104102,50172851],[15407291,57929782,40585691]]],[[[28149288,110528976,78506088],[8684448,71599296,59041248]],[[47614128,149458656,97970928],[28149288,110528976,78506088]]],[[[12652218,52419636,37830618],[2774538,32664276,27952938]],[[22529898,72174996,47708298],[12652218,52419636,37830618]]]]

private theorem identity_0020 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(154141 / 6886400 : ℝ)) =
      tensor4 coefficients_0020 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0020, p_coupled] <;> ring

private theorem negative_0020 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0020 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0020] at hp
  linarith only [hp]

private theorem node_0027 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0019 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0020 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0021 : List (List (List (List ℕ))) :=
  [[[[1436498153,1188587753],[1359800873,1111890473]],[[1959601426,1463780626],[1806206866,1310386066]],[[383653673,135743273],[306956393,59045993]]],[[[2835026250,2339205450],[2680469610,2184648810]],[[3842100660,2850459060],[3532987380,2541345780]],[[728175210,232354410],[573618570,77797770]]],[[[1398203279,1150292879],[1320343919,1072433519]],[[1881849598,1386028798],[1726130878,1230310078]],[[344196719,96286319],[266337359,18426959]]]]

private theorem identity_0021 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(18426959 / 991641600 : ℝ)) =
      tensor4 coefficients_0021 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0021, p_headsq] <;> ring

private theorem negative_0021 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0021 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0021] at hp
  linarith only [hp]

private def coefficients_0022 : List (List (List (List ℕ))) :=
  [[[[568807127,444851927],[529877447,405922247]],[[908975014,661064614],[831115654,583205254]],[[322736687,198781487],[283807007,159851807]]],[[[1118304408,870394008],[1039864008,791953608]],[[1779039816,1283219016],[1622159016,1126338216]],[[625873008,377962608],[547432608,299522208]]],[[[549334872,425379672],[509824152,385868952]],[[869739984,621829584],[790718544,542808144]],[[302973912,179018712],[263463192,139507992]]]]

private theorem identity_0022 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1937611 / 6886400 : ℝ)) =
      tensor4 coefficients_0022 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0022, p_headsq] <;> ring

private theorem negative_0022 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0022 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0022] at hp
  linarith only [hp]

private def coefficients_0023 : List (List (List (List ℕ))) :=
  [[[[87401249,186565409],[1977188578,2175516898],[1945567169,2044731329]],[[1071347218,1269675538],[5812543076,6209199716],[4852755538,5051083858]],[[997890929,1097055089],[3863244418,4061572738],[2921133329,3020297489]]],[[[377604926,575933246],[4375089052,4771745692],[4109043806,4307372126]],[[2555852812,2952509452],[12481616984,13274930264],[10148883532,10545540172]],[[2206137806,2404466126],[8162307772,8558964412],[6067729646,6266057966]]],[[[290895679,390059839],[2399284478,2597612798],[2164168639,2263332799]],[[1485889598,1684217918],[6671841916,7068498556],[5297511998,5495840318]],[[1208938879,1308103039],[4300447358,4498775678],[3147288319,3246452479]]]]

private theorem identity_0023 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(87401249 / 1388298240 : ℝ)) =
      tensor4 coefficients_0023 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0023, p_variance] <;> ring

private theorem negative_0023 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0023 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0023] at hp
  linarith only [hp]

private theorem node_0030 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0022 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0023 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0029 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0021 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0030 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0024 : List (List (List (List ℕ))) :=
  [[[[1031610113,783699713],[954912833,707002433]],[[1606522786,1110701986],[1453128226,957307426]],[[540050273,292139873],[463352993,215442593]]],[[[2025250170,1529429370],[1870693530,1374872730]],[[3136524420,2144882820],[2827411140,1835769540]],[[1041549450,545728650],[886992810,391172010]]],[[[993315239,745404839],[915455879,667545479]],[[1529351998,1033531198],[1373633278,877812478]],[[501174359,253263959],[423314999,175404599]]]]

private theorem identity_0024 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(175404599 / 991641600 : ℝ)) =
      tensor4 coefficients_0024 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0024, p_headsq] <;> ring

private theorem negative_0024 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0024 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0024] at hp
  linarith only [hp]

private def coefficients_0025 : List (List (List (List ℕ))) :=
  [[[[98193563,413308726,299620763],[21496283,259914166,222923483]],[[136542203,490006006,337969403],[59844923,336611446,261272123]]],[[[185144910,804133020,587999310],[30588270,495019740,433442670]],[[262423230,958689660,665277630],[107866590,649576380,510720990]]],[[[86771789,390465178,288198989],[8912429,234746458,210339629]],[[125701469,468324538,327128669],[47842109,312605818,249269309]]]]

private theorem identity_0025 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(8912429 / 991641600 : ℝ)) =
      tensor4 coefficients_0025 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0025, p_coupled] <;> ring

private theorem negative_0025 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0025 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0025] at hp
  linarith only [hp]

private theorem node_0032 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0024 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0025 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0026 : List (List (List (List ℕ))) :=
  [[[[506829527,382874327],[467899847,343944647]],[[785019814,537109414],[707160454,459250054]],[[260759087,136803887],[221829407,97874207]]],[[[994349208,746438808],[915908808,667998408]],[[1531129416,1035308616],[1374248616,878427816]],[[501917808,254007408],[423477408,175567008]]],[[[487357272,363402072],[447846552,323891352]],[[745784784,497874384],[666763344,418852944]],[[240996312,117041112],[201485592,77530392]]]]

private theorem identity_0026 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1076811 / 6886400 : ℝ)) =
      tensor4 coefficients_0026 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0026, p_headsq] <;> ring

private theorem negative_0026 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0026 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0026] at hp
  linarith only [hp]

private def coefficients_0027 : List (List (List (List ℕ))) :=
  [[[[46621637,201704074,147335237],[7691957,123844714,108405557]],[[66086477,240633754,166800077],[27156797,162774394,127870397]]],[[[87442608,391806816,288869808],[9002208,234926016,210429408]],[[126662808,470247216,328090008],[48222408,313366416,249649608]]],[[[40731192,189923184,141444792],[1220472,110901744,101934072]],[[60486552,229433904,161200152],[20975832,150412464,121689432]]]]

private theorem identity_0027 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(16951 / 6886400 : ℝ)) =
      tensor4 coefficients_0027 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0027, p_coupled] <;> ring

private theorem negative_0027 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0027 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0027] at hp
  linarith only [hp]

private theorem node_0033 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0026 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0027 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0031 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 32 : ℝ)
  · exact node_0032 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0033 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0028 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0029 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0031 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0026 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0027 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0028 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0025 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0018 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0026 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0018 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (1 / 16 : ℝ)
  · exact node_0019 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0025 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0028 : List (List (List (List ℕ))) :=
  [[[[15576523,54394646,34944523],[6279883,35801366,25647883]],[[24873163,72987926,44241163],[15576523,54394646,34944523]]],[[[28376790,103236780,67112790],[9202470,64888140,47938470]],[[47551110,141585420,86287110],[28376790,103236780,67112790]]],[[[12620709,48483018,31988709],[2743029,28727658,22111029]],[[22498389,68238378,41866389],[12620709,48483018,31988709]]]]

private theorem identity_0028 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(304781 / 6886400 : ℝ)) =
      tensor4 coefficients_0028 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0028, p_coupled] <;> ring

private theorem negative_0028 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0028 ((x0-0)/(1 / 8 : ℝ)) (1-((x0-0)/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0028] at hp
  linarith only [hp]

private theorem node_0017 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0018 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0028 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0007 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0008 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0017 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0000 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0007 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part01
