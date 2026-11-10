/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part14
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part14
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.middle_strict; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part14.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part14
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0574 : List (List (List (List ℕ))) :=
  [[[[380953129,256997929],[356549449,232594249]],[[598052978,350142578],[549245618,301335218]],[[182237449,58282249],[157833769,33878569]]],[[[738236586,490326186],[688848186,440937786]],[[1148185572,652364772],[1049408772,553587972]],[[340224186,92313786],[290835786,42925386]]],[[[356958639,233003439],[331973919,208018719]],[[549482958,301572558],[499513518,251603118]],[[157661919,33706719],[132677199,8721999]]]]

private theorem identity_0574 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(969111 / 27545600 : ℝ)) =
      tensor4 coefficients_0574 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0574, p_headsq] <;> ring

private theorem negative_0574 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0574 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0574] at hp
  linarith only [hp]

private def coefficients_0575 : List (List (List (List ℕ))) :=
  [[[[54567082,79358122],[342131204,391713284],[294536602,319327642]],[[344455364,394037444],[1171173928,1270338088],[840663524,890245604]],[[296860762,321651802],[842987684,892569764],[553099402,577890442]]],[[[160051648,209633728],[789874136,889038296],[643767448,693349528]],[[794522456,893686616],[2561124832,2759453152],[1794492296,1893656456]],[[648415768,697997848],[1799140616,1898304776],[1164669808,1214251888]]],[[[105830567,130621607],[448434934,498017014],[349576847,374367887]],[[450759094,500341174],[1391334908,1490499068],[954520774,1004102854]],[[351901007,376692047],[956844934,1006427014],[611916407,636707447]]]]

private theorem identity_0575 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(27283541 / 86768640 : ℝ)) =
      tensor4 coefficients_0575 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0575, p_variance] <;> ring

private theorem negative_0575 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0575 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0575] at hp
  linarith only [hp]

private theorem node_0581 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0574 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0575 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0576 : List (List (List (List ℕ))) :=
  [[[[54567082,79358122],[579776564,629358644],[553099402,577890442]],[[342131204,391713284],[1658085448,1757249608],[1371734084,1421316164]],[[294536602,319327642],[1092253844,1141835924],[825607162,850398202]]],[[[160051648,209633728],[1268941616,1368105776],[1164669808,1214251888]],[[789874136,889038296],[3542501392,3740829712],[2864186936,2963351096]],[[643767448,693349528],[2301449696,2400613856],[1713462088,1763044168]]],[[[105830567,130621607],[689857054,739439134],[611916407,636707447]],[[448434934,498017014],[1885799948,1984964108],[1493144854,1542726934]],[[349576847,374367887],[1209887854,1259469934],[888200927,912991967]]]]

private theorem identity_0576 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(27283541 / 86768640 : ℝ)) =
      tensor4 coefficients_0576 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0576, p_variance] <;> ring

private theorem negative_0576 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0576 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0576] at hp
  linarith only [hp]

private theorem node_0580 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0581 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0576 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0577 : List (List (List (List ℕ))) :=
  [[[[169436471,138447671],[156944111,125955311]],[[256655782,194678182],[231671062,169693462]],[[69788111,38799311],[57295751,26306951]]],[[[326713288,264735688],[301438048,239460448]],[[488701736,364746536],[438151256,314196056]],[[127126048,65148448],[101850808,39873208]]],[[[157114408,126125608],[144331528,113342728]],[[231721136,169743536],[206155376,144177776]],[[57175528,26186728],[44392648,13403848]]]]

private theorem identity_0577 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(1675481 / 15494400 : ℝ)) =
      tensor4 coefficients_0577 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0577, p_headsq] <;> ring

private theorem negative_0577 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0577 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0577] at hp
  linarith only [hp]

private def coefficients_0578 : List (List (List (List ℕ))) :=
  [[[[1205567953,957657553],[1105629073,857718673]],[[1753398626,1257577826],[1553520866,1057700066]],[[408381073,160470673],[308442193,60531793]]],[[[2362497290,1866676490],[2161457450,1665636650]],[[3408357940,2416716340],[3006278260,2014636660]],[[766961450,271140650],[565921610,70100810]]],[[[1156604519,908694119],[1055503559,807593159]],[[1654309678,1158488878],[1452107758,956286958]],[[358255559,110345159],[257154599,9244199]]]]

private theorem identity_0578 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(9244199 / 991641600 : ℝ)) =
      tensor4 coefficients_0578 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0578, p_headsq] <;> ring

private theorem negative_0578 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0578 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0578] at hp
  linarith only [hp]

private def coefficients_0579 : List (List (List (List ℕ))) :=
  [[[[482632087,358676887],[432081607,308126407]],[[800539334,552628934],[699438374,451527974]],[[300476047,176520847],[249925567,125970367]]],[[[940620048,692709648],[838938048,591027648]],[[1551499896,1055679096],[1348135896,852315096]],[[576017448,328107048],[474335448,226425048]]],[[[457825552,333870352],[406694032,282738832]],[[750635744,502725344],[648372704,400462304]],[[275378992,151423792],[224247472,100292272]]]]

private theorem identity_0579 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(6268267 / 30988800 : ℝ)) =
      tensor4 coefficients_0579 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0579, p_headsq] <;> ring

private theorem negative_0579 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0579 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0579] at hp
  linarith only [hp]

private def coefficients_0580 : List (List (List (List ℕ))) :=
  [[[[324385769,423549929],[2511585778,2709914098],[2242979849,2342144009]],[[1575530338,1773858658],[6941765636,7338422276],[5477794978,5676123298]],[[1265089529,1364253689],[4458069778,4656398098],[3248760089,3347924249]]],[[[849039966,1047368286],[5438815452,5835472092],[4701335166,4899663486]],[[3559151052,3955807692],[14729926104,15523239384],[11393894412,11790551052]],[[2738001006,2936329326],[9346890492,9743547132],[6720449166,6918777486]]],[[[525346199,624510359],[2928613678,3126941998],[2459047319,2558211479]],[[1985004718,2183333038],[7790928476,8187585116],[5917483438,6115811758]],[[1473603479,1572767639],[4890204718,5088533038],[3472381079,3571545239]]]]

private theorem identity_0580 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(324385769 / 1388298240 : ℝ)) =
      tensor4 coefficients_0580 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0580, p_variance] <;> ring

private theorem negative_0580 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0580 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0580] at hp
  linarith only [hp]

private theorem node_0586 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0579 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0580 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0585 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0578 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0586 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0584 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0577 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0585 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0581 : List (List (List (List ℕ))) :=
  [[[[160397649,209979729],[794342898,893507058],[647890209,697472289]],[[798991218,898155378],[2577615876,2775944196],[1806514578,1905678738]],[[652538529,702120609],[1811162898,1910327058],[1172569329,1222151409]]],[[[424014270,523178430],[1802677260,2001005580],[1406552910,1505717070]],[[1811973900,2010302220],[5598321720,5994978360],[3842127660,4040455980]],[[1415849550,1515013710],[3851424300,4049752620],[2463464670,2562628830]]],[[[264308623,313890703],[1009718366,1108882526],[759354703,808936783]],[[1014366686,1113530846],[3023473852,3221802172],[2036997086,2136161246]],[[764003023,813585103],[2041645406,2140809566],[1291587343,1341169423]]]]

private theorem identity_0581 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(17821961 / 38563840 : ℝ)) =
      tensor4 coefficients_0581 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0581, p_variance] <;> ring

private theorem negative_0581 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0581 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0581] at hp
  linarith only [hp]

private theorem node_0583 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0584 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0581 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0582 : List (List (List (List ℕ))) :=
  [[[[160397649,209979729],[1277187138,1376351298],[1172569329,1222151409]],[[794342898,893507058],[3566545956,3764874276],[2883762738,2982926898]],[[647890209,697472289],[2317248738,2416412898],[1725138369,1774720449]]],[[[424014270,523178430],[2775919260,2974247580],[2463464670,2562628830]],[[1802677260,2001005580],[7591288920,7987945560],[6011731020,6210059340]],[[1406552910,1505717070],[4871149500,5069477820],[3576156270,3675320430]]],[[[264308623,313890703],[1500116126,1599280286],[1291587343,1341169423]],[[1009718366,1108882526],[4027510972,4225839292],[3129352286,3228516446]],[[759354703,808936783],[2555284766,2654448926],[1851709903,1901291983]]]]

private theorem identity_0582 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(17821961 / 38563840 : ℝ)) =
      tensor4 coefficients_0582 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0582, p_variance] <;> ring

private theorem negative_0582 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0582 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0582] at hp
  linarith only [hp]

private theorem node_0582 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0583 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0582 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0579 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0580 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0582 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0583 : List (List (List (List ℕ))) :=
  [[[[910190537,662280137],[812575817,564665417]],[[1492674514,996853714],[1297445074,801624274]],[[547621577,299711177],[450006857,202096457]]],[[[1773041730,1277220930],[1576650210,1080829410]],[[2890089300,1898447700],[2497306260,1505664660]],[[1047322770,551501970],[850931250,355110450]]],[[[862526375,614615975],[763749575,515839175]],[[1396765150,900944350],[1199211550,703390750]],[[499376375,251465975],[400599575,152689175]]]]

private theorem identity_0583 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(6107567 / 39665664 : ℝ)) =
      tensor4 coefficients_0583 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0583, p_headsq] <;> ring

private theorem negative_0583 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0583 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0583] at hp
  linarith only [hp]

private def coefficients_0584 : List (List (List (List ℕ))) :=
  [[[[38339608,87921688],[985425776,1084589936],[974976088,1024558168]],[[528728336,627892496],[2907488032,3105816352],[2434539536,2533703696]],[[497361208,546943288],[1936007216,2035171376],[1466535928,1516118008]]],[[[174737424,273901584],[2174521488,2372849808],[2055563904,2154728064]],[[1257349848,1455678168],[6229869456,6626526096],[5084079288,5282407608]],[[1096557384,1195721544],[4083237888,4281566208],[3042460344,3141624504]]],[[[136743817,186325897],[1189787714,1288951874],[1080933817,1130515897]],[[729313514,828477674],[3323765428,3522093748],[2650231754,2749395914]],[[599542177,649124257],[2147922674,2247086834],[1576270417,1625852497]]]]

private theorem identity_0584 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(4792451 / 86768640 : ℝ)) =
      tensor4 coefficients_0584 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0584, p_variance] <;> ring

private theorem negative_0584 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0584 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0584] at hp
  linarith only [hp]

private theorem node_0592 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0583 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0584 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0585 : List (List (List (List ℕ))) :=
  [[[[443777417,319822217],[394389017,270433817]],[[723411034,475500634],[624634234,376723834]],[[262202417,138247217],[212814017,88858817]]],[[[863560344,615649944],[764202504,516292104]],[[1398542568,902721768],[1199826888,704006088]],[[500119824,252209424],[400761984,152851584]]],[[[419620518,295665318],[369651078,245695878]],[[674806716,426896316],[574867836,326957436]],[[237754998,113799798],[187785558,63830358]]]]

private theorem identity_0585 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(3546131 / 27545600 : ℝ)) =
      tensor4 coefficients_0585 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0585, p_headsq] <;> ring

private theorem negative_0585 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0585 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0585] at hp
  linarith only [hp]

private def coefficients_0586 : List (List (List (List ℕ))) :=
  [[[[175083425,274247585],[2182767010,2381095330],[2063463425,2162627585]],[[1261818610,1460146930],[6253914020,6650570660],[5103655090,5301983410]],[[1100680145,1199844305],[4099036930,4297365250],[3054136625,3153300785]]],[[[547667270,745995590],[4775641900,5172298540],[4339534310,4537862630]],[[2926191580,3322848220],[13343150840,14136464120],[10640078620,11036735260]],[[2406414230,2604742550],[8623288780,9019945420],[6328434230,6526762550]]],[[[373275847,472440007],[2594258894,2792587214],[2276762887,2375927047]],[[1665756974,1864085294],[7092004828,7488661468],[5537807534,5736135854]],[[1306426087,1405590247],[4525635854,4723964174],[3274989607,3374153767]]]]

private theorem identity_0586 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(35016685 / 277659648 : ℝ)) =
      tensor4 coefficients_0586 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0586, p_variance] <;> ring

private theorem negative_0586 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0586 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0586] at hp
  linarith only [hp]

private theorem node_0593 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0585 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0586 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0591 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (21 / 32 : ℝ)
  · exact node_0592 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0593 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0587 : List (List (List (List ℕ))) :=
  [[[[38357419,115450838,73219819],[13953739,66643478,48816139]],[[62761099,164258198,97623499],[38357419,115450838,73219819]]],[[[67571166,212614332,137295966],[18182766,113837532,87907566]],[[116959566,311391132,186684366],[67571166,212614332,137295966]]],[[[29034189,96804378,63896589],[4049469,46834938,38911869]],[[54018909,146773818,88881309],[29034189,96804378,63896589]]]]

private theorem identity_0587 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(449941 / 27545600 : ℝ)) =
      tensor4 coefficients_0587 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0587, p_coupled] <;> ring

private theorem negative_0587 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0587 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0587] at hp
  linarith only [hp]

private theorem node_0590 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0591 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0587 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0588 : List (List (List (List ℕ))) :=
  [[[[66962602,91753642],[366922244,416504324],[306932122,331723162]],[[369246404,418828484],[1220756008,1319920168],[865454564,915036644]],[[309256282,334047322],[867778724,917360804],[565494922,590285962]]],[[[184842688,234424768],[839456216,938620376],[668558488,718140568]],[[844104536,943268696],[2660288992,2858617312],[1844074376,1943238536]],[[673206808,722788888],[1848722696,1947886856],[1189460848,1239042928]]],[[[118226087,143017127],[473225974,522808054],[361972367,386763407]],[[475550134,525132214],[1440916988,1540081148],[979311814,1028893894]],[[364296527,389087567],[981635974,1031218054],[624311927,649102967]]]]

private theorem identity_0588 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(4783043 / 12395520 : ℝ)) =
      tensor4 coefficients_0588 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0588, p_variance] <;> ring

private theorem negative_0588 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0588 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0588] at hp
  linarith only [hp]

private theorem node_0589 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0590 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0588 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0589 : List (List (List (List ℕ))) :=
  [[[[66962602,91753642],[604567604,654149684],[565494922,590285962]],[[366922244,416504324],[1707667528,1806831688],[1396525124,1446107204]],[[306932122,331723162],[1117044884,1166626964],[838002682,862793722]]],[[[184842688,234424768],[1318523696,1417687856],[1189460848,1239042928]],[[839456216,938620376],[3641665552,3839993872],[2913769016,3012933176]],[[668558488,718140568],[2351031776,2450195936],[1738253128,1787835208]]],[[[118226087,143017127],[714648094,764230174],[624311927,649102967]],[[473225974,522808054],[1935382028,2034546188],[1517935894,1567517974]],[[361972367,386763407],[1234678894,1284260974],[900596447,925387487]]]]

private theorem identity_0589 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(4783043 / 12395520 : ℝ)) =
      tensor4 coefficients_0589 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0589, p_variance] <;> ring

private theorem negative_0589 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0589 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0589] at hp
  linarith only [hp]

private theorem node_0588 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0589 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0589 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0590 : List (List (List (List ℕ))) :=
  [[[[864594313,616683913],[764655433,516745033]],[[1400319986,904499186],[1200442226,704621426]],[[500863273,252952873],[400924393,153013993]]],[[[1680550010,1184729210],[1479510170,983689370]],[[2702781700,1711140100],[2300702020,1309060420]],[[952506890,456686090],[751467050,255646250]]],[[[815630879,567720479],[714529919,466619519]],[[1301812078,805991278],[1099610158,603789358]],[[451318799,203408399],[350217839,102307439]]]]

private theorem identity_0590 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(102307439 / 991641600 : ℝ)) =
      tensor4 coefficients_0590 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0590, p_headsq] <;> ring

private theorem negative_0590 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0590 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0590] at hp
  linarith only [hp]

private def coefficients_0591 : List (List (List (List ℕ))) :=
  [[[[137089818,186671898],[1198033236,1297197396],[1088833338,1138415418]],[[733782276,832946436],[3347809992,3546138312],[2669807556,2768971716]],[[603664938,653247018],[2163721716,2262885876],[1587946698,1637528778]]],[[[373621848,472786008],[2602504416,2800832736],[2284662408,2383826568]],[[1670225736,1868554056],[7116049392,7512706032],[5557383336,5755711656]],[[1310548848,1409713008],[4541434896,4739763216],[3286665888,3385830048]]],[[[236878031,286460111],[1405163182,1504327342],[1196175071,1245757151]],[[937135462,1036299622],[3769623404,3967951724],[2888267782,2987431942]],[[707229911,756811991],[2378405182,2477569342],[1699065191,1748647271]]]]

private theorem identity_0591 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(7616101 / 38563840 : ℝ)) =
      tensor4 coefficients_0591 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0591, p_variance] <;> ring

private theorem negative_0591 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0591 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0591] at hp
  linarith only [hp]

private theorem node_0598 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0590 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0591 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0592 : List (List (List (List ℕ))) :=
  [[[[420654487,296699287],[370104007,246148807]],[[676584134,428673734],[575483174,327572774]],[[238498447,114543247],[187947967,63992767]]],[[[816664848,568754448],[714982848,467072448]],[[1303589496,807768696],[1100225496,604404696]],[[452062248,204151848],[350380248,102469848]]],[[[395847952,271892752],[344716432,220761232]],[[626680544,378770144],[524417504,276507104]],[[213401392,89446192],[162269872,38314672]]]]

private theorem identity_0592 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(2394667 / 30988800 : ℝ)) =
      tensor4 coefficients_0592 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0592, p_headsq] <;> ring

private theorem negative_0592 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0592 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0592] at hp
  linarith only [hp]

private def coefficients_0593 : List (List (List (List ℕ))) :=
  [[[[373967849,473132009],[2610749938,2809078258],[2292561929,2391726089]],[[1674694498,1873022818],[7140093956,7536750596],[5576959138,5775287458]],[[1314671609,1413835769],[4557233938,4755562258],[3298342169,3397506329]]],[[[948204126,1146532446],[5637143772,6033800412],[4800499326,4998827646]],[[3757479372,4154136012],[15126582744,15919896024],[11592222732,11988879372]],[[2837165166,3035493486],[9545218812,9941875452],[6819613326,7017941646]]],[[[574928279,674092439],[3027777838,3226106158],[2508629399,2607793559]],[[2084168878,2282497198],[7989256796,8385913436],[6016647598,6214975918]],[[1523185559,1622349719],[4989368878,5187697198],[3521963159,3621127319]]]]

private theorem identity_0593 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(373967849 / 1388298240 : ℝ)) =
      tensor4 coefficients_0593 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0593, p_variance] <;> ring

private theorem negative_0593 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0593 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0593] at hp
  linarith only [hp]

private theorem node_0599 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0592 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0593 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0597 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0598 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0599 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0594 : List (List (List (List ℕ))) :=
  [[[[126310363,407564726,265759963],[26371483,207686966,165821083]],[[226249243,607442486,365698843],[126310363,407564726,265759963]]],[[[233615150,777118300,512514350],[32575310,375038620,311474510]],[[434654990,1179197980,713554190],[233615150,777118300,512514350]]],[[[107125229,369194458,246574829],[6024269,166992538,145473869]],[[208226189,571396378,347675789],[107125229,369194458,246574829]]]]

private theorem identity_0594 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(6024269 / 991641600 : ℝ)) =
      tensor4 coefficients_0594 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0594, p_coupled] <;> ring

private theorem negative_0594 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0594 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0594] at hp
  linarith only [hp]

private def coefficients_0595 : List (List (List (List ℕ))) :=
  [[[[45956317,169384634,115681117],[20681077,118834154,90405877]],[[71231557,219935114,140956357],[45956317,169384634,115681117]]],[[[82230288,319404576,221679888],[31389288,217722576,170838888]],[[133071288,421086576,272520888],[82230288,319404576,221679888]]],[[[36184192,149840384,105908992],[10618432,98708864,80343232]],[[61749952,200971904,131474752],[36184192,149840384,105908992]]]]

private theorem identity_0595 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(165913 / 7747200 : ℝ)) =
      tensor4 coefficients_0595 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0595, p_coupled] <;> ring

private theorem negative_0595 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0595 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0595] at hp
  linarith only [hp]

private def coefficients_0596 : List (List (List (List ℕ))) :=
  [[[[423549929,522714089],[1773858658,1972186978],[1364253689,1463417849]],[[1778506978,1976835298],[5443069796,5839726436],[3692452738,3890781058]],[[1368902009,1468066169],[3697101058,3895429378],[2342144009,2441308169]]],[[[1047368286,1245696606],[3955807692,4352464332],[2936329326,3134657646]],[[3965104332,4361760972],[11717427384,12510740664],[7808102892,8204759532]],[[2945625966,3143954286],[7817399532,8214056172],[4899663486,5097991806]]],[[[624510359,723674519],[2183333038,2381661358],[1572767639,1671931799]],[[2187981358,2386309678],[6277125596,6673782236],[4117034158,4315362478]],[[1577415959,1676580119],[4121682478,4320010798],[2558211479,2657375639]]]]

private theorem identity_0596 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(423549929 / 1388298240 : ℝ)) =
      tensor4 coefficients_0596 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0596, p_variance] <;> ring

private theorem negative_0596 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0596 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0596] at hp
  linarith only [hp]

private theorem node_0602 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0595 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0596 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0597 : List (List (List (List ℕ))) :=
  [[[[71231557,219935114,140956357],[20681077,118834154,90405877]],[[96506797,270485594,166231597],[45956317,169384634,115681117]]],[[[133071288,421086576,272520888],[31389288,217722576,170838888]],[[183912288,522768576,323361888],[82230288,319404576,221679888]]],[[[61749952,200971904,131474752],[10618432,98708864,80343232]],[[87315712,252103424,157040512],[36184192,149840384,105908992]]]]

private theorem identity_0597 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(165913 / 7747200 : ℝ)) =
      tensor4 coefficients_0597 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0597, p_coupled] <;> ring

private theorem negative_0597 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0597 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0597] at hp
  linarith only [hp]

private theorem node_0601 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact node_0602 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0597 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0600 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0594 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0601 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0596 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0597 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0600 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0598 : List (List (List (List ℕ))) :=
  [[[[185188689,234770769],[843924978,943089138],[672681249,722263329]],[[848573298,947737458],[2676780036,2875108356],[1856096658,1955260818]],[[677329569,726911649],[1860744978,1959909138],[1197360369,1246942449]]],[[[473596350,572760510],[1901841420,2100169740],[1456134990,1555299150]],[[1911138060,2109466380],[5796650040,6193306680],[3941291820,4139620140]],[[1465431630,1564595790],[3950588460,4148916780],[2513046750,2612210910]]],[[[289099663,338681743],[1059300446,1158464606],[784145743,833727823]],[[1063948766,1163112926],[3122638012,3320966332],[2086579166,2185743326]],[[788794063,838376143],[2091227486,2190391646],[1316378383,1365960463]]]]

private theorem identity_0598 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(2939503 / 5509120 : ℝ)) =
      tensor4 coefficients_0598 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0598, p_variance] <;> ring

private theorem negative_0598 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0598 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0598] at hp
  linarith only [hp]

private theorem node_0595 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0596 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0598 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0599 : List (List (List (List ℕ))) :=
  [[[[185188689,234770769],[1326769218,1425933378],[1197360369,1246942449]],[[843924978,943089138],[3665710116,3864038436],[2933344818,3032508978]],[[672681249,722263329],[2366830818,2465994978],[1749929409,1799511489]]],[[[473596350,572760510],[2875083420,3073411740],[2513046750,2612210910]],[[1901841420,2100169740],[7789617240,8186273880],[6110895180,6309223500]],[[1456134990,1555299150],[4970313660,5168641980],[3625738350,3724902510]]],[[[289099663,338681743],[1549698206,1648862366],[1316378383,1365960463]],[[1059300446,1158464606],[4126675132,4325003452],[3178934366,3278098526]],[[784145743,833727823],[2604866846,2704031006],[1876500943,1926083023]]]]

private theorem identity_0599 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(2939503 / 5509120 : ℝ)) =
      tensor4 coefficients_0599 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0599, p_variance] <;> ring

private theorem negative_0599 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0599 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0599] at hp
  linarith only [hp]

private theorem node_0594 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0595 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0599 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0587 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0588 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0594 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0579 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0587 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0600 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0600 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0600 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0600, p_qbox] <;> ring

private theorem negative_0600 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0600 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0600] at hp
  linarith only [hp]

private def coefficients_0601 : List (List (List (List ℕ))) :=
  [[[[312778129,188822929],[266294929,142339729]],[[602314658,354404258],[509348258,261437858]],[[254674129,130718929],[208190929,84235729]]],[[[604347938,356437538],[510219458,262309058]],[[1161631636,665810836],[973374676,477553876]],[[487558898,239648498],[393430418,145520018]]],[[[291244991,167289791],[243599711,119644511]],[[558667342,310756942],[463376782,215466382]],[[232559951,108604751],[184914671,60959471]]]]

private theorem identity_0601 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(60959471 / 247910400 : ℝ)) =
      tensor4 coefficients_0601 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0601, p_headsq] <;> ring

private theorem negative_0601 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0601 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0601] at hp
  linarith only [hp]

private def coefficients_0602 : List (List (List (List ℕ))) :=
  [[[[64214059,190405718,110697259],[17730859,97439318,64214059]],[[87455659,236888918,133938859],[40972459,143922518,87455659]]],[[[119421638,362798476,212388038],[25293158,174541516,118259558]],[[166485878,456926956,259452278],[72357398,268669996,165323798]]],[[[55028021,172033642,101511221],[7382741,76743082,53865941]],[[78850661,219678922,125333861],[31205381,124388362,77688581]]]]

private theorem identity_0602 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(7382741 / 247910400 : ℝ)) =
      tensor4 coefficients_0602 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0602, p_coupled] <;> ring

private theorem negative_0602 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0602 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0602] at hp
  linarith only [hp]

private theorem node_0608 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0601 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0602 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0603 : List (List (List (List ℕ))) :=
  [[[[151603969,89626369],[127781329,65803729]],[[291296618,167341418],[243651338,119696138]],[[122261449,60283849],[98438809,36461209]]],[[[292278960,168323760],[244052640,120097440]],[[560444760,312534360],[463992120,216081720]],[[233303400,109348200],[185077080,61121880]]],[[[140512582,78534982],[116108902,54131302]],[[268823324,144868124],[220015964,96060764]],[[110879542,48901942],[86475862,24498262]]]]

private theorem identity_0603 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(12249131 / 61977600 : ℝ)) =
      tensor4 coefficients_0603 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0603, p_headsq] <;> ring

private theorem negative_0603 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0603 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0603] at hp
  linarith only [hp]

private def coefficients_0604 : List (List (List (List ℕ))) :=
  [[[[30190819,91370438,53432419],[6368179,43725158,29609779]],[[42102139,115193078,65343739],[18279499,67547798,41521099]]],[[[55698840,173375280,102182040],[7472520,76922640,53955720]],[[79812000,221601600,126295200],[31585680,125148960,78068880]]],[[[25418242,81825284,48659842],[1014562,33017924,24256162]],[[37620082,106228964,60861682],[13216402,57421604,36458002]]]]

private theorem identity_0604 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(507281 / 61977600 : ℝ)) =
      tensor4 coefficients_0604 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0604, p_coupled] <;> ring

private theorem negative_0604 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0604 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0604] at hp
  linarith only [hp]

private theorem node_0609 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0603 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0604 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0607 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (9 / 16 : ℝ)
  · exact node_0608 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0609 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0605 : List (List (List (List ℕ))) :=
  [[[[20442379,48631958,24315979],[8821579,25390358,12695179]],[[32063179,71873558,35936779],[20442379,48631958,24315979]]],[[[36090998,87676396,43838198],[12268358,40031116,20015558]],[[59913638,135321676,67660838],[36090998,87676396,43838198]]],[[[15469061,38685322,19342661],[3267221,14281642,7140821]],[[27670901,63089002,31544501],[15469061,38685322,19342661]]]]

private theorem identity_0605 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(3267221 / 61977600 : ℝ)) =
      tensor4 coefficients_0605 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0605, p_coupled] <;> ring

private theorem negative_0605 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0605 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0605] at hp
  linarith only [hp]

private theorem node_0606 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0607 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0605 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0605 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0600 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0606 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0606 : List (List (List (List ℕ))) :=
  [[[[31772659,94534118,47267059],[8531059,48050918,24025459]],[[43393459,117775718,58887859],[20151859,71292518,35646259]]],[[[59913638,181804876,90902438],[12268358,86514316,43257158]],[[83736278,229450156,114725078],[36090998,134159596,67079798]]],[[[27961421,86911642,43455821],[3557741,38104282,19052141]],[[40163261,111315322,55657661],[15759581,62507962,31253981]]]]

private theorem identity_0606 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(3557741 / 61977600 : ℝ)) =
      tensor4 coefficients_0606 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0606, p_coupled] <;> ring

private theorem negative_0606 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0606 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0606] at hp
  linarith only [hp]

private theorem node_0604 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0605 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0606 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0607 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0607 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0607 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0607, p_qbox] <;> ring

private theorem negative_0607 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0607 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0607] at hp
  linarith only [hp]

private def coefficients_0608 : List (List (List (List ℕ))) :=
  [[[[293312929,169357729],[244505569,120550369]],[[562222178,314311778],[464607458,216697058]],[[234046849,110091649],[185239489,61284289]]],[[[564118266,316207866],[465341466,217431066]],[[1078848132,583027332],[881294532,385473732]],[[445005066,197094666],[346228266,98317866]]],[[[270480519,146525319],[220511079,96555879]],[[515976318,268065918],[416037438,168127038]],[[210633399,86678199],[160663959,36708759]]]]

private theorem identity_0608 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(4078751 / 27545600 : ℝ)) =
      tensor4 coefficients_0608 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0608, p_headsq] <;> ring

private theorem negative_0608 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0608 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0608] at hp
  linarith only [hp]

private def coefficients_0609 : List (List (List (List ℕ))) :=
  [[[[43877299,149732198,90360499],[19473619,100924838,65956819]],[[68280979,198539558,114764179],[43877299,149732198,90360499]]],[[[78029886,280014972,170996286],[28641486,181238172,121607886]],[[127418286,378791772,220384686],[78029886,280014972,170996286]]],[[[33973029,129923658,80456229],[8988309,79954218,55471509]],[[58957749,179893098,105440949],[33973029,129923658,80456229]]]]

private theorem identity_0609 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(998701 / 27545600 : ℝ)) =
      tensor4 coefficients_0609 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0609, p_coupled] <;> ring

private theorem negative_0609 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0609 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0609] at hp
  linarith only [hp]

private def coefficients_0610 : List (List (List (List ℕ))) :=
  [[[[243440329,181462729],[219036649,157059049]],[[392752178,268796978],[343944818,219989618]],[[114449449,52471849],[90045769,28068169]]],[[[463210986,339255786],[413822586,289867386]],[[737583972,489673572],[638807172,390896772]],[[204648186,80692986],[155259786,31304586]]],[[[219445839,157468239],[194461119,132483519]],[[344182158,220226958],[294212718,170257518]],[[89873919,27896319],[64889199,2911599]]]]

private theorem identity_0610 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(323511 / 27545600 : ℝ)) =
      tensor4 coefficients_0610 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0610, p_headsq] <;> ring

private theorem negative_0610 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0610 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0610] at hp
  linarith only [hp]

private def coefficients_0611 : List (List (List (List ℕ))) :=
  [[[[45523579,114288758,64891579],[21119899,65481398,40487899]],[[69927259,163096118,89295259],[45523579,114288758,64891579]]],[[[80741406,207966012,119477406],[31353006,109189212,70089006]],[[130129806,306742812,168865806],[80741406,207966012,119477406]]],[[[35038269,93318138,54406269],[10053549,43348698,29421549]],[[60022989,143287578,79390989],[35038269,93318138,54406269]]]]

private theorem identity_0611 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(1117061 / 27545600 : ℝ)) =
      tensor4 coefficients_0611 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0611, p_coupled] <;> ring

private theorem negative_0611 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0611 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0611] at hp
  linarith only [hp]

private theorem node_0616 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0610 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0611 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0615 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0609 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0616 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0614 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0608 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0615 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0612 : List (List (List (List ℕ))) :=
  [[[[141546551,79568951],[116561831,54584231]],[[270600742,146645542],[220631302,96676102]],[[111622991,49645391],[86638271,24660671]]],[[[271514488,147559288],[220964008,97008808]],[[517753736,269843336],[416652776,168742376]],[[211376848,87421648],[160826368,36871168]]],[[[129805528,67827928],[104239768,42262168]],[[246828176,122872976],[195696656,71741456]],[[99591448,37613848],[74025688,12048088]]]]

private theorem identity_0612 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(1506011 / 15494400 : ℝ)) =
      tensor4 coefficients_0612 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0612, p_headsq] <;> ring

private theorem negative_0612 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0612 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0612] at hp
  linarith only [hp]

private def coefficients_0613 : List (List (List (List ℕ))) :=
  [[[[19697621,70384042,42939221],[7205261,45399322,30446861]],[[32189981,95368762,55431581],[19697621,70384042,42939221]]],[[[34353328,130684256,80836528],[9078088,80133776,55561288]],[[59628568,181234736,106111768],[34353328,130684256,80836528]]],[[[14565928,60120656,37807528],[1783048,34554896,25024648]],[[27348808,85686416,50590408],[14565928,60120656,37807528]]]]

private theorem identity_0613 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(222881 / 15494400 : ℝ)) =
      tensor4 coefficients_0613 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0613, p_coupled] <;> ring

private theorem negative_0613 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0613 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0613] at hp
  linarith only [hp]

private def coefficients_0614 : List (List (List (List ℕ))) :=
  [[[[756133513,508223113],[656194633,408284233]],[[1322847986,827027186],[1122970226,627149426]],[[531852073,283941673],[431913193,184002793]]],[[[1463628410,967807610],[1262588570,766767770]],[[2547837700,1556196100],[2145758020,1154116420]],[[1014484490,518663690],[813444650,317623850]]],[[[707170079,459259679],[606069119,358158719]],[[1224340078,728519278],[1022138158,526317358]],[[482307599,234397199],[381206639,133296239]]]]

private theorem identity_0614 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(133296239 / 991641600 : ℝ)) =
      tensor4 coefficients_0614 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0614, p_headsq] <;> ring

private theorem negative_0614 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0614 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0614] at hp
  linarith only [hp]

private def coefficients_0615 : List (List (List (List ℕ))) :=
  [[[[184347738,233929818],[1283252436,1382416596],[1126794618,1176376698]],[[832946436,932110596],[3527545032,3725873352],[2750378436,2849542596]],[[655571178,705153258],[2258237556,2357401716],[1630556298,1680138378]]],[[[468137688,567301848],[2772942816,2971271136],[2360584968,2459749128]],[[1868554056,2066882376],[7475519472,7872176112],[5718525096,5916853416]],[[1414361328,1513525488],[4730466576,4928794896],[3371885088,3471049248]]],[[[284135951,333718031],[1490382382,1589546542],[1234136351,1283718431]],[[1036299622,1135463782],[3949358444,4147686764],[2968838662,3068002822]],[[759136151,808718231],[2472921022,2572085182],[1741674791,1791256871]]]]

private theorem identity_0615 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(10241541 / 38563840 : ℝ)) =
      tensor4 coefficients_0615 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0615, p_variance] <;> ring

private theorem negative_0615 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0615 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0615] at hp
  linarith only [hp]

private theorem node_0621 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0614 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0615 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0616 : List (List (List (List ℕ))) :=
  [[[[7428449,106592609],[1794001378,1992329698],[1842352769,1941516929]],[[1831187938,2029516258],[7350817796,7747474436],[5631189538,5829517858]],[[1879539329,1978703489],[5668376098,5866704418],[3844616609,3943780769]]],[[[207571806,405900126],[3988539612,4385196252],[3892527486,4090855806]],[[4062912732,4459569372],[15532923384,16326236664],[11693130012,12089786652]],[[3966900606,4165228926],[11767503132,12164159772],[7912162206,8110490526]]],[[[200835359,299999519],[2195922238,2394250558],[2050866719,2150030879]],[[2233108798,2431437118],[8184873596,8581530236],[6063324478,6261652798]],[[2088053279,2187217439],[6100511038,6298839358],[4068237599,4167401759]]]]

private theorem identity_0616 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(1061207 / 198328320 : ℝ)) =
      tensor4 coefficients_0616 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0616, p_variance] <;> ring

private theorem negative_0616 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0616 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0616] at hp
  linarith only [hp]

private theorem node_0620 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0621 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0616 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0617 : List (List (List (List ℕ))) :=
  [[[[20375501,52371802,30059501],[7883141,27387082,17567141]],[[32867861,77356522,42551861],[20375501,52371802,30059501]]],[[[35418568,94078736,54786568],[10143328,43528256,29511328]],[[60693808,144629216,80061808],[35418568,94078736,54786568]]],[[[14953288,41527376,24637288],[2170408,15961616,11854408]],[[27736168,67093136,37420168],[14953288,41527376,24637288]]]]

private theorem identity_0617 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(271301 / 15494400 : ℝ)) =
      tensor4 coefficients_0617 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0617, p_coupled] <;> ring

private theorem negative_0617 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0617 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0617] at hp
  linarith only [hp]

private theorem node_0619 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact node_0620 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0617 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0618 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0613 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0619 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0617 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0612 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0618 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0613 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0614 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0617 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0618 : List (List (List (List ℕ))) :=
  [[[[9212899,22299398,11149699],[3111979,10097558,5048779]],[[15313819,34501238,17250619],[9212899,22299398,11149699]]],[[[15849360,39445920,19722960],[3357000,14461200,7230600]],[[28341720,64430640,32215320],[15849360,39445920,19722960]]],[[[6546682,16966964,8483482],[155242,4184084,2092042]],[[12938122,29749844,14874922],[6546682,16966964,8483482]]]]

private theorem identity_0618 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(77621 / 15494400 : ℝ)) =
      tensor4 coefficients_0618 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0618, p_coupled] <;> ring

private theorem negative_0618 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0618 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0618] at hp
  linarith only [hp]

private theorem node_0612 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0613 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0618 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0611 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0607 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0612 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0619 : List (List (List (List ℕ))) :=
  [[[[15313819,46122038,23061019],[3111979,21718358,10859179]],[[21414739,58323878,29161939],[9212899,33920198,16960099]]],[[[28632240,88253280,44126640],[3647520,38283840,19141920]],[[41124600,113238000,56619000],[16139880,63268560,31634280]]],[[[13228642,41951684,20975842],[445762,16385924,8192962]],[[19620082,54734564,27367282],[6837202,29168804,14584402]]]]

private theorem identity_0619 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(222881 / 15494400 : ℝ)) =
      tensor4 coefficients_0619 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0619, p_coupled] <;> ring

private theorem negative_0619 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0619 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0619] at hp
  linarith only [hp]

private theorem node_0610 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0611 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0619 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 8 : ℝ)
  · exact node_0604 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0610 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part14
