/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part15
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part15
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part15.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part15
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0620 : List (List (List (List ℕ))) :=
  [[[[138272449,76294849],[126651649,64674049]],[[264924098,140968898],[241682498,117727298]],[[91789249,29811649],[80168449,18190849]]],[[[265359698,141404498],[241537058,117581858]],[[506896756,258986356],[459251476,211341076]],[[171812258,47857058],[147989618,24034418]]],[[[126762431,64784831],[114560591,52582991]],[[241323022,117367822],[216919342,92964142]],[[79698191,17720591],[67496351,5518751]]]]

private theorem identity_0620 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(5518751 / 61977600 : ℝ)) =
      tensor4 coefficients_0620 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0620, p_headsq] <;> ring

private theorem negative_0620 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0620 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0620] at hp
  linarith only [hp]

private def coefficients_0621 : List (List (List (List ℕ))) :=
  [[[[27813240,40208760],[172996560,197787600],[152155800,164551320]],[[179969040,204760080],[610947360,660529440],[444923280,469714320]],[[159128280,171523800],[451895760,476686800],[299739960,312135480]]],[[[82281600,107072640],[403080120,452662200],[334743480,359534520]],[[417025080,466607160],[1343622240,1442786400],[954487080,1004069160]],[[348688440,373479480],[968432040,1018014120],[633688560,658479600]]],[[[54814361,67209881],[230775562,255566602],[182933681,195329201]],[[237748042,262539082],[734058884,783640964],[510255802,535046842]],[[189906161,202301681],[517228282,542019322],[334294601,346690121]]]]

private theorem identity_0621 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(11037 / 17216 : ℝ)) =
      tensor4 coefficients_0621 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0621, p_variance] <;> ring

private theorem negative_0621 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0621 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0621] at hp
  linarith only [hp]

private theorem node_0625 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0620 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0621 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0622 : List (List (List (List ℕ))) :=
  [[[[30137400,42532920],[299663280,324454320],[297415800,309811320]],[[182293200,207084240],[875901600,925483680],[749388240,774179280]],[[159128280,171523800],[590183280,614974320],[458944920,471340440]]],[[[86929920,111720960],[660190320,709772400],[629040240,653831280]],[[421673400,471255480],[1881084240,1980248400],[1570970520,1620552600]],[[348688440,373479480],[1248783840,1298365920],[955875240,980666280]]],[[[57138521,69534041],[361219042,386010082],[331970441,344365961]],[[240072202,264863242],[1006566644,1056148724],[822274282,847065322]],[[189906161,202301681],[659292562,684083602],[497276321,509671841]]]]

private theorem identity_0622 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(83715 / 120512 : ℝ)) =
      tensor4 coefficients_0622 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0622, p_variance] <;> ring

private theorem negative_0622 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0622 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0622] at hp
  linarith only [hp]

private theorem node_0624 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0625 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0622 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0623 : List (List (List (List ℕ))) :=
  [[[[58964449,43470049],[52863529,37369129]],[[111827978,80839178],[99626138,68637338]],[[35432329,19937929],[29331409,13837009]]],[[[112011480,81022680],[99519120,68530320]],[[211530600,149553000],[186545880,124568280]],[[64656720,33667920],[52164360,21175560]]],[[[52884622,37390222],[46493182,30998782]],[[99377804,68389004],[86594924,55606124]],[[29061982,13567582],[22670542,7176142]]]]

private theorem identity_0623 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_headsq x0 x1 x2 x3-(3588071 / 15494400 : ℝ)) =
      tensor4 coefficients_0623 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0623, p_headsq] <;> ring

private theorem negative_0623 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0623 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0623] at hp
  linarith only [hp]

private def coefficients_0624 : List (List (List (List ℕ))) :=
  [[[[396253849,272298649],[347446489,223491289]],[[743700338,495789938],[646085618,398175218]],[[207996889,84041689],[159189529,35234329]]],[[[768838026,520927626],[670061226,422150826]],[[1438899252,943078452],[1241345652,745524852]],[[391162026,143251626],[292385226,44474826]]],[[[372259359,248304159],[322289919,198334719]],[[694549278,446638878],[594610398,346699998]],[[182840319,58885119],[132870879,8915679]]]]

private theorem identity_0624 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(990631 / 27545600 : ℝ)) =
      tensor4 coefficients_0624 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0624, p_headsq] <;> ring

private theorem negative_0624 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0624 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0624] at hp
  linarith only [hp]

private def coefficients_0625 : List (List (List (List ℕ))) :=
  [[[[160333511,98355911],[135348791,73371191]],[[308174662,184219462],[258205222,134250022]],[[130409951,68432351],[105425231,43447631]]],[[[308507368,184552168],[257956888,134001688]],[[591739496,343829096],[490638536,242728136]],[[248369728,124414528],[197819248,73864048]]],[[[148011448,86033848],[122445688,60468088]],[[283240016,159284816],[232108496,108153296]],[[117797368,55819768],[92231608,30254008]]]]

private theorem identity_0625 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(3781751 / 15494400 : ℝ)) =
      tensor4 coefficients_0625 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0625, p_headsq] <;> ring

private theorem negative_0625 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0625 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0625] at hp
  linarith only [hp]

private def coefficients_0626 : List (List (List (List ℕ))) :=
  [[[[180540369,230122449],[1298879298,1398043458],[1174118769,1223700849]],[[843924978,943089138],[3628523556,3826851876],[2896158258,2995322418]],[[677329569,726911649],[2357534178,2456698338],[1735984449,1785566529]]],[[[464299710,563463870],[2819303580,3017631900],[2466563550,2565727710]],[[1901841420,2100169740],[7715244120,8111900760],[6036522060,6234850380]],[[1465431630,1564595790],[4951720380,5150048700],[3597848430,3697012590]]],[[[284451343,334033423],[1521808286,1620972446],[1293136783,1342718863]],[[1059300446,1158464606],[4089488572,4287816892],[3141747806,3240911966]],[[788794063,838376143],[2595570206,2694734366],[1862555983,1912138063]]]]

private theorem identity_0626 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(20060041 / 38563840 : ℝ)) =
      tensor4 coefficients_0626 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0626, p_variance] <;> ring

private theorem negative_0626 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0626 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0626] at hp
  linarith only [hp]

private theorem node_0630 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0625 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0626 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0629 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0624 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0630 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0628 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0623 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0629 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0627 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[27],[51]]],[[[9],[33]],[[33],[57]]]]

private theorem identity_0627 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0627 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0627, p_mass] <;> ring

private theorem negative_0627 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0627 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0627] at hp
  linarith only [hp]

private theorem node_0627 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 4 : ℝ)
  · exact node_0628 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_0627 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0628 : List (List (List (List ℕ))) :=
  [[[[3],[51]],[[27],[75]]],[[[9],[57]],[[33],[81]]]]

private theorem identity_0628 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0628 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0628, p_mass] <;> ring

private theorem negative_0628 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0628 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0628] at hp
  linarith only [hp]

private theorem node_0626 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0627 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_0628 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0623 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 8 : ℝ)
  · exact node_0624 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0626 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0629 : List (List (List (List ℕ))) :=
  [[[[290117569,166162369],[243634369,119679169]],[[556993538,309083138],[464027138,216116738]],[[232013569,108058369],[185530369,61575169]]],[[[557864738,309954338],[463736258,215825858]],[[1068665236,572844436],[880408276,384587476]],[[441075698,193165298],[346947218,99036818]]],[[[267422351,143467151],[219777071,95821871]],[[511022062,263111662],[415731502,167821102]],[[208737311,84782111],[161092031,37136831]]]]

private theorem identity_0629 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(37136831 / 247910400 : ℝ)) =
      tensor4 coefficients_0629 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0629, p_headsq] <;> ring

private theorem negative_0629 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0629 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0629] at hp
  linarith only [hp]

private def coefficients_0630 : List (List (List (List ℕ))) :=
  [[[[26808480,51599520],[499855680,549437760],[500937120,525728160]],[[283708800,333290880],[1492433280,1591597440],[1264504320,1314086400]],[[263872800,288663840],[1006522560,1056104640],[770539680,795330720]]],[[[103150440,152732520],[1106331840,1205496000],[1058961240,1108543320]],[[670261320,769425480],[3205661040,3403989360],[2646959400,2746123560]],[[581055840,630637920],[2127219120,2226383280],[1601943120,1651525200]]],[[[76687961,101479001],[607168162,656750242],[558370121,583161161]],[[387244522,436826602],[1714611764,1813775924],[1383147082,1432729162]],[[317529041,342320081],[1121388562,1170970642],[831749441,856540481]]]]

private theorem identity_0630 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(18617 / 120512 : ℝ)) =
      tensor4 coefficients_0630 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0630, p_variance] <;> ring

private theorem negative_0630 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0630 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0630] at hp
  linarith only [hp]

private theorem node_0636 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0629 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0630 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0631 : List (List (List (List ℕ))) :=
  [[[[139983169,78005569],[116160529,54182929]],[[268055018,144099818],[220409738,96454538]],[[110640649,48663049],[86818009,24840409]]],[[[268456320,144501120],[220230000,96274800]],[[512799480,264889080],[416346840,168436440]],[[209480760,85525560],[161254440,37299240]]],[[[128310742,66333142],[103907062,41929462]],[[244419644,120464444],[195612284,71657084]],[[98677702,36700102],[74274022,12296422]]]]

private theorem identity_0631 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(6148211 / 61977600 : ℝ)) =
      tensor4 coefficients_0631 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0631, p_headsq] <;> ring

private theorem negative_0631 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0631 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0631] at hp
  linarith only [hp]

private def coefficients_0632 : List (List (List (List ℕ))) :=
  [[[[103496441,153078521],[1114577362,1213741522],[1066860761,1116442841]],[[674730082,773894242],[3229705604,3428033924],[2666535202,2765699362]],[[585178601,634760681],[2143018162,2242182322],[1613619401,1663201481]]],[[[307443846,406608006],[2445163692,2643492012],[2249279526,2348443686]],[[1557915612,1756243932],[6906536184,7303192824],[5571739932,5770068252]],[[1278361686,1377525846],[4517152332,4715480652],[3350350326,3449514486]]],[[[204639407,254221487],[1331970334,1431134494],[1183110767,1232692847]],[[884569534,983733694],[3679598588,3877926908],[2906588734,3005752894]],[[693875087,743457167],[2375518174,2474682334],[1737422927,1787005007]]]]

private theorem identity_0632 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(103496441 / 347074560 : ℝ)) =
      tensor4 coefficients_0632 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0632, p_variance] <;> ring

private theorem negative_0632 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0632 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0632] at hp
  linarith only [hp]

private theorem node_0637 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0631 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0632 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0635 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (9 / 16 : ℝ)
  · exact node_0636 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0637 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0633 : List (List (List (List ℕ))) :=
  [[[[41553499,114095798,57047899],[18311899,67612598,33806299]],[[64795099,160578998,80289499],[41553499,114095798,57047899]]],[[[72357398,206692396,103346198],[25293158,112563916,56281958]],[[119421638,300820876,150410438],[72357398,206692396,103346198]]],[[[30624341,92237482,46118741],[6801701,44592202,22296101]],[[54446981,139882762,69941381],[30624341,92237482,46118741]]]]

private theorem identity_0633 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(6801701 / 247910400 : ℝ)) =
      tensor4 coefficients_0633 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0633, p_coupled] <;> ring

private theorem negative_0633 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0633 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0633] at hp
  linarith only [hp]

private def coefficients_0634 : List (List (List (List ℕ))) :=
  [[[[34555680,59346720],[289906560,339488640],[262323360,287114400]],[[301527360,351109440],[1060914240,1160078400],[773331840,822913920]],[[273944160,298735200],[784952640,834534720],[517980960,542772000]]],[[[118644840,168226920],[682656840,781821000],[577956960,627539040]],[[705898440,805062600],[2335069440,2533397760],[1657060920,1756225080]],[[601198560,650780640],[1680302520,1779466680],[1093048920,1142631000]]],[[[84435161,109226201],[393442282,443024362],[315979601,340770641]],[[405063082,454645162],[1275539204,1374703364],[884421082,934003162]],[[327600401,352391441],[896041882,945623962],[575413961,600205001]]]]

private theorem identity_0634 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(23997 / 120512 : ℝ)) =
      tensor4 coefficients_0634 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0634, p_variance] <;> ring

private theorem negative_0634 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (5 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0634 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0634] at hp
  linarith only [hp]

private theorem node_0640 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0633 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0634 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0635 : List (List (List (List ℕ))) :=
  [[[[64795099,160578998,80289499],[18311899,67612598,33806299]],[[88036699,207062198,103531099],[41553499,114095798,57047899]]],[[[119421638,300820876,150410438],[25293158,112563916,56281958]],[[166485878,394949356,197474678],[72357398,206692396,103346198]]],[[[54446981,139882762,69941381],[6801701,44592202,22296101]],[[78269621,187528042,93764021],[30624341,92237482,46118741]]]]

private theorem identity_0635 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(6801701 / 247910400 : ℝ)) =
      tensor4 coefficients_0635 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0635, p_coupled] <;> ring

private theorem negative_0635 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0635 ((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0635] at hp
  linarith only [hp]

private theorem node_0639 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0640 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0635 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0636 : List (List (List (List ℕ))) :=
  [[[[18279499,52053398,26026699],[6368179,28230758,14115379]],[[30190819,75876038,37938019],[18279499,52053398,26026699]]],[[[31004640,92998080,46499040],[6891480,44771760,22385880]],[[55117800,141224400,70612200],[31004640,92998080,46499040]]],[[[12635362,40765124,20382562],[433522,16361444,8180722]],[[24837202,65168804,32584402],[12635362,40765124,20382562]]]]

private theorem identity_0636 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(216761 / 61977600 : ℝ)) =
      tensor4 coefficients_0636 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0636, p_coupled] <;> ring

private theorem negative_0636 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0636 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0636] at hp
  linarith only [hp]

private def coefficients_0637 : List (List (List (List ℕ))) :=
  [[[[118990841,168572921],[687125602,786289762],[582079721,631661801]],[[710367202,809531362],[2351560484,2549888804],[1669083202,1768247362]],[[605321321,654903401],[1692324802,1791488962],[1100948441,1150530521]]],[[[338432646,437596806],[1582706652,1781034972],[1272163926,1371328086]],[[1629189852,1827518172],[5135138904,5531795544],[3561728892,3760057212]],[[1318647126,1417811286],[3608212092,3806540412],[2317454886,2416619046]]],[[[220133807,269715887],[896965054,996129214],[690776207,740358287]],[[920206654,1019370814],[2786346428,2984674748],[1894029694,1993193854]],[[714017807,763599887],[1917271294,2016435454],[1217198447,1266780527]]]]

private theorem identity_0637 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(118990841 / 347074560 : ℝ)) =
      tensor4 coefficients_0637 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0637, p_variance] <;> ring

private theorem negative_0637 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (5 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0637 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0637] at hp
  linarith only [hp]

private theorem node_0642 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0636 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0637 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0638 : List (List (List (List ℕ))) :=
  [[[[30190819,75876038,37938019],[6368179,28230758,14115379]],[[42102139,99698678,49849339],[18279499,52053398,26026699]]],[[[55117800,141224400,70612200],[6891480,44771760,22385880]],[[79230960,189450720,94725360],[31004640,92998080,46499040]]],[[[24837202,65168804,32584402],[433522,16361444,8180722]],[[37039042,89572484,44786242],[12635362,40765124,20382562]]]]

private theorem identity_0638 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(216761 / 61977600 : ℝ)) =
      tensor4 coefficients_0638 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0638, p_coupled] <;> ring

private theorem negative_0638 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0638 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0638] at hp
  linarith only [hp]

private theorem node_0641 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0642 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0638 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0638 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (9 / 16 : ℝ)
  · exact node_0639 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0641 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0634 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0635 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0638 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0639 : List (List (List (List ℕ))) :=
  [[[[34011000,46406520],[185392080,210183120],[158353560,170749080]],[[192364560,217155600],[635738400,685320480],[457318800,482109840]],[[165326040,177721560],[464291280,489082320],[305937720,318333240]]],[[[94677120,119468160],[427871160,477453240],[347139000,371930040]],[[441816120,491398200],[1393204320,1492368480],[979278120,1028860200]],[[361083960,385875000],[993223080,1042805160],[646084080,670875120]]],[[[61012121,73407641],[243171082,267962122],[189131441,201526961]],[[250143562,274934602],[758849924,808432004],[522651322,547442362]],[[196103921,208499441],[529623802,554414842],[340492361,352887881]]]]

private theorem identity_0639 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(94475 / 120512 : ℝ)) =
      tensor4 coefficients_0639 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0639, p_variance] <;> ring

private theorem negative_0639 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0639 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0639] at hp
  linarith only [hp]

private theorem node_0633 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 4 : ℝ)
  · exact node_0634 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0639 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0640 : List (List (List (List ℕ))) :=
  [[[[36335160,48730680],[312058800,336849840],[303613560,316009080]],[[194688720,219479760],[900692640,950274720],[761783760,786574800]],[[165326040,177721560],[602578800,627369840],[465142680,477538200]]],[[[99325440,124116480],[684981360,734563440],[641435760,666226800]],[[446464440,496046520],[1930666320,2029830480],[1595761560,1645343640]],[[361083960,385875000],[1273574880,1323156960],[968270760,993061800]]],[[[63336281,75731801],[373614562,398405602],[338168201,350563721]],[[252467722,277258762],[1031357684,1080939764],[834669802,859460842]],[[196103921,208499441],[671688082,696479122],[503474081,515869601]]]]

private theorem identity_0640 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(100931 / 120512 : ℝ)) =
      tensor4 coefficients_0640 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0640, p_variance] <;> ring

private theorem negative_0640 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0640 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0640] at hp
  linarith only [hp]

private theorem node_0632 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0633 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0640 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0641 : List (List (List (List ℕ))) :=
  [[[[269490289,145535089],[220682929,96727729]],[[514576898,266666498],[416962178,169051778]],[[210224209,86269009],[161416849,37461649]]],[[[515310906,267400506],[416534106,168623706]],[[981233412,485412612],[783679812,287859012]],[[396197706,148287306],[297420906,49510506]]],[[[245495799,121540599],[195526359,71571159]],[[466006878,218096478],[366067998,118157598]],[[185648679,61693479],[135679239,11724039]]]]

private theorem identity_0641 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(1302671 / 27545600 : ℝ)) =
      tensor4 coefficients_0641 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0641, p_headsq] <;> ring

private theorem negative_0641 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0641 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0641] at hp
  linarith only [hp]

private def coefficients_0642 : List (List (List (List ℕ))) :=
  [[[[77033962,101825002],[615413684,664995764],[566269642,591060682]],[[391713284,441295364],[1738656328,1837820488],[1402722884,1452304964]],[[321651802,346442842],[1137187604,1186769684],[843425722,868216762]]],[[[204985408,254567488],[1340215856,1439380016],[1191010288,1240592368]],[[889038296,988202456],[3703643152,3901971472],[2926164536,3025328696]],[[697997848,747579928],[2391317216,2490481376],[1749099208,1798681288]]],[[[128297447,153088487],[725494174,775076254],[625086647,649877687]],[[498017014,547599094],[1966370828,2065534988],[1524133654,1573715734]],[[376692047,401483087],[1254821614,1304403694],[906019487,930810527]]]]

private theorem identity_0642 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(38516981 / 86768640 : ℝ)) =
      tensor4 coefficients_0642 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0642, p_variance] <;> ring

private theorem negative_0642 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0642 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0642] at hp
  linarith only [hp]

private theorem node_0647 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0641 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0642 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0643 : List (List (List (List ℕ))) :=
  [[[[122953271,60975671],[110460911,48483311]],[[233414182,109458982],[208429462,84474262]],[[93029711,31052111],[80537351,18559751]]],[[[233746888,109791688],[208471648,84516448]],[[442218536,194308136],[391668056,143757656]],[[173609248,49654048],[148334008,24378808]]],[[[110631208,48653608],[97848328,35870728]],[[208479536,84524336],[182913776,58958576]],[[80417128,18439528],[67634248,5656648]]]]

private theorem identity_0643 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(707081 / 15494400 : ℝ)) =
      tensor4 coefficients_0643 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0643, p_headsq] <;> ring

private theorem negative_0643 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0643 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0643] at hp
  linarith only [hp]

private def coefficients_0644 : List (List (List (List ℕ))) :=
  [[[[196034769,245616849],[856320498,955484658],[674230689,723812769]],[[879562098,978726258],[2720164356,2918492676],[1868492178,1967656338]],[[697472289,747054369],[1891733778,1990897938],[1208206449,1257788529]]],[[[495288510,594452670],[1926632460,2124960780],[1459233870,1558398030]],[[1973115660,2171443980],[5883418680,6280075320],[3966082860,4164411180]],[[1505717070,1604881230],[4012566060,4210894380],[2534738910,2633903070]]],[[[299945743,349527823],[1071695966,1170860126],[785695183,835277263]],[[1094937566,1194101726],[3166022332,3364350652],[2098974686,2198138846]],[[808936783,858518863],[2122216286,2221380446],[1327224463,1376806543]]]]

private theorem identity_0644 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(3111663 / 5509120 : ℝ)) =
      tensor4 coefficients_0644 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0644, p_variance] <;> ring

private theorem negative_0644 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (5 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0644 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0644] at hp
  linarith only [hp]

private theorem node_0649 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0643 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0644 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0645 : List (List (List (List ℕ))) :=
  [[[[205331409,254913489],[1348461378,1447625538],[1198909809,1248491889]],[[893507058,992671218],[3727687716,3926016036],[2945740338,3044904498]],[[702120609,751702689],[2407116258,2506280418],[1760775489,1810357569]]],[[[513881790,613045950],[2918467740,3116796060],[2516145630,2615309790]],[[2001005580,2199333900],[7913572440,8310229080],[6135686220,6334014540]],[[1515013710,1614177870],[5050884540,5249212860],[3647430510,3746594670]]],[[[309242383,358824463],[1571390366,1670554526],[1317927823,1367509903]],[[1108882526,1208046686],[4188652732,4386981052],[3191329886,3290494046]],[[813585103,863167183],[2645152286,2744316446],[1887347023,1936929103]]]]

private theorem identity_0645 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(22814601 / 38563840 : ℝ)) =
      tensor4 coefficients_0645 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0645, p_variance] <;> ring

private theorem negative_0645 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0645 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0645] at hp
  linarith only [hp]

private theorem node_0648 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0649 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0645 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0646 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0647 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0648 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0646 : List (List (List (List ℕ))) :=
  [[[[553819337,305908937],[456204617,208294217]],[[1058831314,563010514],[863601874,367781074]],[[470149577,222239177],[372534857,124624457]]],[[[1060299330,564478530],[863907810,368087010]],[[2022402900,1030761300],[1629619860,637978260]],[[892378770,396557970],[695987250,200166450]]],[[[506155175,258244775],[407378375,159467975]],[[962921950,467101150],[765368350,269547550]],[[421904375,173993975],[323127575,75217175]]]]

private theorem identity_0646 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(3008687 / 39665664 : ℝ)) =
      tensor4 coefficients_0646 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0646, p_headsq] <;> ring

private theorem negative_0646 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0646 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0646] at hp
  linarith only [hp]

private def coefficients_0647 : List (List (List (List ℕ))) :=
  [[[[137334707,336647014,183817907],[39719987,141417574,86203187]],[[186142067,434261734,232625267],[88527347,239032294,135010547]]],[[[252314790,628584780,345281190],[55923270,235801740,148889670]],[[350510550,824976300,443476950],[154119030,432193260,247085430]]],[[[114800525,291578650,161283725],[16023725,94025050,62506925]],[[164188925,390355450,210672125],[65412125,192801850,111895325]]]]

private theorem identity_0647 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(640949 / 39665664 : ℝ)) =
      tensor4 coefficients_0647 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0647, p_coupled] <;> ring

private theorem negative_0647 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0647 ((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0647] at hp
  linarith only [hp]

private theorem node_0655 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (21 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0646 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0647 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0648 : List (List (List (List ℕ))) :=
  [[[[265591817,141636617],[216203417,92248217]],[[506489434,258579034],[407712634,159802234]],[[223466417,99511217],[174078017,50122817]]],[[[507189144,259278744],[407831304,159920904]],[[964699368,468878568],[765983688,270162888]],[[422647824,174737424],[323289984,75379584]]],[[[241434918,117479718],[191465478,67510278]],[[457885116,209974716],[357946236,110035836]],[[199018998,75063798],[149049558,25094358]]]]

private theorem identity_0648 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1394131 / 27545600 : ℝ)) =
      tensor4 coefficients_0648 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0648, p_headsq] <;> ring

private theorem negative_0648 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0648 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0648] at hp
  linarith only [hp]

private def coefficients_0649 : List (List (List (List ℕ))) :=
  [[[[63414107,157817014,86655707],[14025707,59040214,37267307]],[[88108307,207205414,111349907],[38719907,108428614,61961507]]],[[[115471344,292920288,161954544],[16113504,94204608,62596704]],[[165150264,392278128,211633464],[65792424,193562448,112275624]]],[[[51967458,134923716,75209058],[1998018,34984836,25239618]],[[76952178,184893156,100193778],[26982738,84954276,50224338]]]]

private theorem identity_0649 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(111001 / 27545600 : ℝ)) =
      tensor4 coefficients_0649 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0649, p_coupled] <;> ring

private theorem negative_0649 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0649 ((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(21 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0649] at hp
  linarith only [hp]

private theorem node_0656 (x0 x1 x2 x3 : ℝ)
    (h0l : (21 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0648 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0649 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0654 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (21 / 32 : ℝ)
  · exact node_0655 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0656 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0650 : List (List (List (List ℕ))) :=
  [[[[37195339,82137878,41068939],[12791659,33330518,16665259]],[[61599019,130945238,65472619],[37195339,82137878,41068939]]],[[[62922846,141340092,70670046],[13534446,42563292,21281646]],[[112311246,240116892,120058446],[62922846,141340092,70670046]]],[[[25547949,58843098,29421549],[563229,8873658,4436829]],[[50532669,108812538,54406269],[25547949,58843098,29421549]]]]

private theorem identity_0650 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(62581 / 27545600 : ℝ)) =
      tensor4 coefficients_0650 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0650, p_coupled] <;> ring

private theorem negative_0650 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0650 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0650] at hp
  linarith only [hp]

private theorem node_0653 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0654 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0650 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0651 : List (List (List (List ℕ))) :=
  [[[[84781162,109572202],[397911044,447493124],[320102362,344893402]],[[409531844,459113924],[1292030248,1391194408],[896443364,946025444]],[[331723162,356514202],[908064164,957646244],[583313482,608104522]]],[[[220479808,270061888],[901433816,1000597976],[694898968,744481048]],[[924675416,1023839576],[2802837472,3001165792],[1906051976,2005216136]],[[718140568,767722648],[1929293576,2028457736],[1225097968,1274680048]]],[[[136044647,160835687],[504214774,553796854],[375142607,399933647]],[[515835574,565417654],[1512191228,1611355388],[1010300614,1059882694]],[[386763407,411554447],[1021921414,1071503494],[642130487,666921527]]]]

private theorem identity_0651 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(42390581 / 86768640 : ℝ)) =
      tensor4 coefficients_0651 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0651, p_variance] <;> ring

private theorem negative_0651 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (5 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0651 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0651] at hp
  linarith only [hp]

private theorem node_0652 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 8 : ℝ)
  · exact node_0653 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0651 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0652 : List (List (List (List ℕ))) :=
  [[[[89429482,114220522],[640204724,689786804],[578665162,603456202]],[[416504324,466086404],[1788238408,1887402568],[1427513924,1477096004]],[[334047322,358838362],[1161978644,1211560724],[855821242,880612282]]],[[[229776448,279358528],[1389797936,1488962096],[1215801328,1265383408]],[[938620376,1037784536],[3802807312,4001135632],[2975746616,3074910776]],[[722788888,772370968],[2440899296,2540063456],[1773890248,1823472328]]],[[[140692967,165484007],[750285214,799867294],[637482167,662273207]],[[522808054,572390134],[2015952908,2115117068],[1548924694,1598506774]],[[389087567,413878607],[1279612654,1329194734],[918415007,943206047]]]]

private theorem identity_0652 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(44714741 / 86768640 : ℝ)) =
      tensor4 coefficients_0652 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0652, p_variance] <;> ring

private theorem negative_0652 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0652 ((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0652] at hp
  linarith only [hp]

private theorem node_0651 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0652 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0652 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0653 : List (List (List (List ℕ))) :=
  [[[[508223113,260312713],[408284233,160373833]],[[966476786,470655986],[766599026,270778226]],[[423391273,175480873],[323452393,75541993]]],[[[967807610,471986810],[766767770,270946970]],[[1835095300,843453700],[1433015620,441374020]],[[797562890,301742090],[596523050,100702250]]],[[[459259679,211349279],[358158719,110248319]],[[867968878,372148078],[665766958,169946158]],[[373846799,125936399],[272745839,24835439]]]]

private theorem identity_0653 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(24835439 / 991641600 : ℝ)) =
      tensor4 coefficients_0653 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0653, p_headsq] <;> ring

private theorem negative_0653 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0653 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0653] at hp
  linarith only [hp]

private def coefficients_0654 : List (List (List (List ℕ))) :=
  [[[[222309018,271891098],[1349878356,1449042516],[1155459258,1205041338]],[[913517316,1012681476],[3670093512,3868421832],[2812356036,2911520196]],[[698180778,747762858],[2334160116,2433324276],[1663869258,1713451338]]],[[[544060248,643224408],[2906194656,3104522976],[2417914248,2517078408]],[[2029695816,2228024136],[7760616432,8157273072],[5842480296,6040808616]],[[1499580528,1598744688],[4882311696,5080640016],[3438511008,3537675168]]],[[[322097231,371679311],[1557008302,1656172462],[1262800991,1312383071]],[[1116870502,1216034662],[4091906924,4290235244],[3030816262,3129980422]],[[801745751,851327831],[2548843582,2648007742],[1774987751,1824569831]]]]

private theorem identity_0654 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(12350501 / 38563840 : ℝ)) =
      tensor4 coefficients_0654 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0654, p_variance] <;> ring

private theorem negative_0654 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0654 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0654] at hp
  linarith only [hp]

private theorem node_0661 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0653 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0654 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0655 : List (List (List (List ℕ))) :=
  [[[[78702689,177866849],[1917956578,2116284898],[1895033729,1994197889]],[[1992329698,2190658018],[7635914756,8032571396],[5755144738,5953473058]],[[1969406849,2068571009],[5829517858,6027846178],[3915890849,4015055009]]],[[[350120286,548448606],[4236450012,4633106652],[3997889406,4196217726]],[[4385196252,4781852892],[16103117304,16896430584],[11941040412,12337697052]],[[4146635646,4344963966],[12089786652,12486443292],[8054710686,8253039006]]],[[[272109599,371273759],[2319877438,2518205758],[2103547679,2202711839]],[[2394250558,2592578878],[8469970556,8866627196],[6187279678,6385607998]],[[2177920799,2277084959],[6261652798,6459981118],[4139511839,4238675999]]]]

private theorem identity_0655 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(78702689 / 1388298240 : ℝ)) =
      tensor4 coefficients_0655 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0655, p_variance] <;> ring

private theorem negative_0655 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0655 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0655] at hp
  linarith only [hp]

private theorem node_0660 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0661 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0655 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0656 : List (List (List (List ℕ))) :=
  [[[[8068329,32859369],[452497698,502079778],[458374329,483165369]],[[471090978,520673058],[1847442276,1946606436],[1404241218,1453823298]],[[476967609,501758649],[1422834498,1472416578],[959811849,984602889]]],[[[111802110,161384190],[1103879820,1203043980],[1019967630,1069549710]],[[1141066380,1240230540],[4107760440,4306088760],[3022473900,3121638060]],[[1057154190,1106736270],[3059660460,3158824620],[2030396190,2079978270]]],[[[104425783,129216823],[652766126,702348206],[562285303,587076343]],[[671359406,720941486],[2263086172,2362250332],[1619616686,1669198766]],[[580878583,605669623],[1638209966,1687792046],[1071276343,1096067383]]]]

private theorem identity_0656 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(896481 / 38563840 : ℝ)) =
      tensor4 coefficients_0656 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0656, p_variance] <;> ring

private theorem negative_0656 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0656 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0656] at hp
  linarith only [hp]

private theorem node_0659 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0660 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.variance) (negative_0656 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0657 : List (List (List (List ℕ))) :=
  [[[[220825809,270407889],[905902578,1005066738],[699021729,748603809]],[[929144178,1028308338],[2819328516,3017656836],[1918074258,2017238418]],[[722263329,771845409],[1941315858,2040480018],[1232997489,1282579569]]],[[[544870590,644034750],[2025796620,2224124940],[1508815950,1607980110]],[[2072279820,2270608140],[6081747000,6478403640],[4065247020,4263575340]],[[1555299150,1654463310],[4111730220,4310058540],[2584320990,2683485150]]],[[[324736783,374318863],[1121278046,1220442206],[810486223,860068303]],[[1144519646,1243683806],[3265186492,3463514812],[2148556766,2247720926]],[[833727823,883309903],[2171798366,2270962526],[1352015503,1401597583]]]]

private theorem identity_0657 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(24536201 / 38563840 : ℝ)) =
      tensor4 coefficients_0657 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0657, p_variance] <;> ring

private theorem negative_0657 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (5 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0657 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0657] at hp
  linarith only [hp]

private theorem node_0658 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 8 : ℝ)
  · exact node_0659 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0657 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0658 : List (List (List (List ℕ))) :=
  [[[[230122449,279704529],[1398043458,1497207618],[1223700849,1273282929]],[[943089138,1042253298],[3826851876,4025180196],[2995322418,3094486578]],[[726911649,776493729],[2456698338,2555862498],[1785566529,1835148609]]],[[[563463870,662628030],[3017631900,3215960220],[2565727710,2664891870]],[[2100169740,2298498060],[8111900760,8508557400],[6234850380,6433178700]],[[1564595790,1663759950],[5150048700,5348377020],[3697012590,3796176750]]],[[[334033423,383615503],[1620972446,1720136606],[1342718863,1392300943]],[[1158464606,1257628766],[4287816892,4486145212],[3240911966,3340076126]],[[838376143,887958223],[2694734366,2793898526],[1912138063,1961720143]]]]

private theorem identity_0658 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(25569161 / 38563840 : ℝ)) =
      tensor4 coefficients_0658 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0658, p_variance] <;> ring

private theorem negative_0658 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0658 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0658] at hp
  linarith only [hp]

private theorem node_0657 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0658 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0658 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0650 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 16 : ℝ)
  · exact node_0651 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0657 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0645 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0646 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0650 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0659 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[27],[51]]],[[[9],[33]],[[33],[57]]]]

private theorem identity_0659 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0659 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0659, p_mass] <;> ring

private theorem negative_0659 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0659 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0659] at hp
  linarith only [hp]

private theorem node_0644 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 4 : ℝ)
  · exact node_0645 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_0659 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0660 : List (List (List (List ℕ))) :=
  [[[[3],[51]],[[27],[75]]],[[[9],[57]],[[33],[81]]]]

private theorem identity_0660 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0660 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0660, p_mass] <;> ring

private theorem negative_0660 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0660 ((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0660] at hp
  linarith only [hp]

private theorem node_0643 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0644 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_0660 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0631 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 8 : ℝ)
  · exact node_0632 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0643 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 2 : ℝ)
  · exact node_0623 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0631 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part15
