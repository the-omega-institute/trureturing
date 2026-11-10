/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part10
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part10
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.middle_strict; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part10.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part10
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0378 : List (List (List (List ℕ))) :=
  [[[[80525374588909,38444071651309],[65533910417389,23452607479789]],[[148001204356058,63838598480858],[118018276013018,33855670137818]],[[61558146541549,19476843603949],[46566682370029,4485379432429]]],[[[320379362179508,152666984937908],[260434571679668,92722194438068]],[[587711417864296,252286663381096],[467821836864616,132397082381416]],[[243747502635188,76035125393588],[183802712135348,16090334893748]]],[[[477933084922318,227281539629518],[388049576250958,137398030958158]],[[875026718436956,373723627851356],[695259701094236,193956610508636]],[[361845759957838,111194214665038],[271962251286478,21310705993678]]],[[[316829501763540,150338331152340],[256930988775540,90439818164340]],[[578923853110680,245941511888280],[459126827134680,126144485912280]],[[238681530479940,72190359868740],[178783017491940,12291846880740]]],[[[78750401024259,37279701401859],[63782070379299,22311370756899]],[[143607341366838,60665942122038],[113670680076918,30729280832118]],[[59025123208179,17554423585779],[44056792563219,2586092940819]]]]

private theorem identity_0378 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(287343660091 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0378 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0378, p_headbox] <;> ring

private theorem negative_0378 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0378 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0378] at hp
  linarith only [hp]

private def coefficients_0379 : List (List (List (List ℕ))) :=
  [[[[76344523,400599446,308760523],[32185483,312281366,264601483]],[[120503563,488917526,352919563],[76344523,400599446,308760523]]],[[[142503990,780828780,607335990],[53604870,603030540,518436870]],[[231403110,958627020,696235110],[142503990,780828780,607335990]]],[[[65979909,379870218,298395909],[21239829,290390058,253655829]],[[110719989,469350378,343135989],[65979909,379870218,298395909]]]]

private theorem identity_0379 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(2359981 / 110182400 : ℝ)) =
      tensor4 coefficients_0379 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0379, p_coupled] <;> ring

private theorem negative_0379 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0379 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0379] at hp
  linarith only [hp]

private def coefficients_0380 : List (List (List (List ℕ))) :=
  [[[[206605619,909032038,686932019],[29969459,555759718,510295859]],[[383241779,1262304358,863568179],[206605619,909032038,686932019]]],[[[391679046,1774999692,1352331846],[37244646,1066130892,997897446]],[[746113446,2483868492,1706766246],[391679046,1774999692,1352331846]]],[[[184893869,865608538,665220269],[7095629,510012058,487422029]],[[362692109,1221205018,843018509],[184893869,865608538,665220269]]]]

private theorem identity_0380 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(7095629 / 3966566400 : ℝ)) =
      tensor4 coefficients_0380 ((x0-(3 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0380, p_coupled] <;> ring

private theorem negative_0380 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0380 ((x0-(3 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0380] at hp
  linarith only [hp]

private def coefficients_0381 : List (List (List (List ℕ))) :=
  [[[[396511987457987,229410213531587],[336590335714067,169488561787667]],[[692135372543614,357931824690814],[572292069055774,238088521202974]],[[283874041606427,116772267680027],[223952389862507,56850615936107]]],[[[1575962203292440,908776314217240],[1336321868599240,669135979524040]],[[2747025623639480,1412653845489080],[2267744954253080,933373176102680]],[[1124151912521440,456966023446240],[884511577828240,217325688753040]]],[[[2348720796531704,1349771541670904],[1989331765026584,990382510165784]],[[4088081448386848,2090182938665248],[3369303385376608,1371404875655008]],[[1669122032372744,670172777511944],[1309733000867624,310783746006824]]],[[[1555602853277184,890854915075584],[1316059182141504,651311243939904]],[[2703627362648928,1374131486245728],[2224540020377568,895044143974368]],[[1101284419966944,436536481765344],[861740748831264,196992810629664]]],[[[386332270876152,220449472386552],[326458948296312,160576149806712]],[[670436161950384,338670564971184],[550689516790704,218923919811504]],[[272440256805432,106557458315832],[212566934225592,46684135735992]]]]

private theorem identity_0381 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(648390774111 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0381 ((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0381, p_headbox] <;> ring

private theorem negative_0381 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0381 ((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0381] at hp
  linarith only [hp]

private def coefficients_0382 : List (List (List (List ℕ))) :=
  [[[[120334691,488579782,360497891],[31435571,310781542,271598771]],[[164784251,577478902,404947451],[75885131,399680662,316048331]]],[[[230014248,955849296,710340648],[51634968,599090736,531961368]],[[319203888,1134228576,799530288],[140824608,777470016,621151008]]],[[[109589778,467089956,349752978],[20109618,288129636,260272818]],[[154329858,556570116,394493058],[64849698,377609796,305012898]]]]

private theorem identity_0382 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(1117201 / 110182400 : ℝ)) =
      tensor4 coefficients_0382 ((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0382, p_coupled] <;> ring

private theorem negative_0382 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0382 ((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(25 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0382] at hp
  linarith only [hp]

private theorem node_0393 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0381 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0382 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0392 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (25 / 64 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0380 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0393 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0383 : List (List (List (List ℕ))) :=
  [[[[114596323,345400646,226930723],[70437283,257082566,182771683]],[[158755363,433718726,271089763],[114596323,345400646,226930723]]],[[[218426550,669269100,443095350],[129527430,491470860,354196230]],[[307325670,847067340,531994470],[218426550,669269100,443095350]]],[[[103650669,323509338,215985069],[58910589,234029178,171244989]],[[148390749,412989498,260725149],[103650669,323509338,215985069]]]]

private theorem identity_0383 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(6545621 / 110182400 : ℝ)) =
      tensor4 coefficients_0383 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0383, p_coupled] <;> ring

private theorem negative_0383 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0383 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0383] at hp
  linarith only [hp]

private theorem node_0391 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0392 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0383 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0390 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0379 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0391 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0389 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0378 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0390 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0384 : List (List (List (List ℕ))) :=
  [[[[39874162340627,19138812529427],[32389997018147,11654647206947]],[[72801594340414,31330894718014],[57833263695454,16362564073054]],[[30011523432587,9276173621387],[22527358110107,1792008298907]]],[[[158582700529256,75945487345256],[128658634443416,46021421259416]],[[288959133539992,123684707171992],[229111001368312,63836575000312]],[[118755574906736,36118361722736],[88831508820896,6194295636896]]],[[[236476620432632,112975964151032],[191610437321432,68109781039832]],[[430017438230464,183016125667264],[340285072008064,93283759444864]],[[176173538008232,52672881726632],[131307354897032,7806698615432]]],[[[156701741875776,74670669619776],[126804907391616,44773835135616]],[[284363765775072,120301621263072],[224570096806752,60507952294752]],[[116126404363296,34095332107296],[86229569879136,4198497623136]]],[[[38933657927992,18501378580792],[31463105791672,11030826444472]],[[70503863336624,29639304642224],[55562759063984,14698200369584]],[[28696916125432,8264636778232],[21226363989112,794084641912]]]]

private theorem identity_0384 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(99260580239 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0384 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0384, p_headbox] <;> ring

private theorem negative_0384 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0384 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0384] at hp
  linarith only [hp]

private def coefficients_0385 : List (List (List (List ℕ))) :=
  [[[[35816147,195587494,152024147],[13446107,150847414,129654107]],[[58186187,240327574,174394187],[35816147,195587494,152024147]]],[[[66360208,380630816,298776208],[21329608,290569616,253745608]],[[111390808,470692016,343806808],[66360208,380630816,298776208]]],[[[30454282,184863764,146662282],[7793722,139542644,124001722]],[[53114842,230184884,169322842],[30454282,184863764,146662282]]]]

private theorem identity_0385 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(3896861 / 247910400 : ℝ)) =
      tensor4 coefficients_0385 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0385, p_coupled] <;> ring

private theorem negative_0385 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0385 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0385] at hp
  linarith only [hp]

private def coefficients_0386 : List (List (List (List ℕ))) :=
  [[[[783010768292413,451245171313213],[663264123132733,331498526153533]],[[1361564776980986,698033583022586],[1122071486661626,458540292703226]],[[555226740150973,223461143171773],[435480094991293,103714498012093]]],[[[3111495533624500,1786866634194100],[2632609714618420,1307980815188020]],[[5402493678229160,2753235879368360],[4444722040217000,1795464241356200]],[[2197860175113460,873231275683060],[1718974356107380,394345456676980]]],[[[4636233715033150,2652936136229950],[3918060221818750,1934762643015550]],[[8037725037086300,4071129879479900],[6601378050657500,2634782893051100]],[[3262040711043550,1278743132240350],[2543867217829150,560569639025950]]],[[[3070023729250500,1750252882018500],[2591347608742500,1271576761510500]],[[5314227813387000,2674686118923000],[4356875572371000,1717333877907000]],[[2151407696440500,831636849208500],[1672731575932500,352960728700500]]],[[[762274776141875,432938205261875],[642632975001875,313296404121875]],[[1317431670733750,658758528973750],[1078148068453750,419474926693750]],[[532000416951875,202663846071875],[412358615811875,83022044931875]]]]

private theorem identity_0386 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(132835271891 / 2599528955904 : ℝ)) =
      tensor4 coefficients_0386 ((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0386, p_headbox] <;> ring

private theorem negative_0386 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0386 ((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0386] at hp
  linarith only [hp]

private def coefficients_0387 : List (List (List (List ℕ))) :=
  [[[[230685067,957190934,711011467],[51724747,599270294,532051147]],[[320165227,1136151254,800491627],[141204907,778230614,621531307]]],[[[439700750,1871043100,1400353550],[80618030,1152877660,1041270830]],[[619242110,2230125820,1579894910],[260159390,1511960380,1220812190]]],[[[208836125,913493050,689162525],[28713725,553248250,509040125]],[[298897325,1093615450,779223725],[118774925,733370650,599101325]]]]

private theorem identity_0387 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(1148549 / 158662656 : ℝ)) =
      tensor4 coefficients_0387 ((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0387, p_coupled] <;> ring

private theorem negative_0387 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0387 ((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0387] at hp
  linarith only [hp]

private theorem node_0398 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0386 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0387 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0388 : List (List (List (List ℕ))) :=
  [[[[386400641786923,221732356346923],[326579741216923,161911455776923]],[[669242342798846,339905771918846],[549600541658846,220263970778846]],[[271263462191923,106595176751923],[211442561621923,46774276181923]]],[[[1535140254806192,877679394902192],[1295911110500192,638450250596192]],[[2654718805969384,1339797086161384],[2176260517357384,861338797549384]],[[1073350834451192,415889974547192],[834121690145192,176660830241192]]],[[[2286922505763488,1302547407497888],[1928162507000288,943787408734688]],[[3948518171778976,1979767975247776],[3230998174252576,1262247977721376]],[[1592381791918688,608006693653088],[1233621793155488,249246694889888]]],[[[1514026720884992,858985962305792],[1274910548767232,619869790188032]],[[2609849116203904,1299767599045504],[2131616771968384,821535254809984]],[[1049764841981312,394724083402112],[810648669863552,155607911284352]]],[[[375843826436992,212385591659392],[316079409346432,152621174568832]],[[646807404187904,319890934632704],[527278570006784,200362100451584]],[[259470420618112,96012185840512],[199706003527552,36247768749952]]]]

private theorem identity_0388 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(283185693359 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0388 ((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0388, p_headbox] <;> ring

private theorem negative_0388 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0388 ((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0388] at hp
  linarith only [hp]

private def coefficients_0389 : List (List (List (List ℕ))) :=
  [[[[110260597,468431594,350423797],[20199397,288309194,260362597]],[[155291197,558492794,395454397],[65229997,378370394,305393197]]],[[[209506944,914834688,689833344],[28803504,553427808,509129904]],[[299858664,1095538128,780185064],[119155224,734131248,599481624]]],[[[99156568,446223536,339319768],[8514328,264939056,248677528]],[[144477688,536865776,384640888],[53835448,355581296,293998648]]]]

private theorem identity_0389 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(1064291 / 247910400 : ℝ)) =
      tensor4 coefficients_0389 ((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0389, p_coupled] <;> ring

private theorem negative_0389 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0389 ((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(27 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0389] at hp
  linarith only [hp]

private theorem node_0399 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0388 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0389 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0397 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (27 / 64 : ℝ)
  · exact node_0398 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0399 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0390 : List (List (List (List ℕ))) :=
  [[[[54796787,167697574,110963987],[32426747,122957494,88593947]],[[77166827,212437654,133334027],[54796787,167697574,110963987]]],[[[104030968,324269936,216365368],[59000368,234208736,171334768]],[[149061568,414331136,261395968],[104030968,324269936,216365368]]],[[[49144402,156392804,105311602],[26483842,111071684,82651042]],[[71804962,201713924,127972162],[49144402,156392804,105311602]]]]

private theorem identity_0390 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(13241921 / 247910400 : ℝ)) =
      tensor4 coefficients_0390 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0390, p_coupled] <;> ring

private theorem negative_0390 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0390 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0390] at hp
  linarith only [hp]

private theorem node_0396 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0397 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0390 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0395 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0385 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0396 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0394 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0384 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0395 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0388 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 32 : ℝ)
  · exact node_0389 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0394 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0391 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0391 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0391 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0391, p_qmass] <;> ring

private theorem negative_0391 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0391 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0391] at hp
  linarith only [hp]

private theorem node_0387 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0388 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0391 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0392 : List (List (List (List ℕ))) :=
  [[[[58908318173029,37867666704229],[51412586087269,30371934618469]],[[104767091524298,62685788586698],[89775627352778,47694324415178]],[[39941090125669,18900438656869],[32445358039909,11404706571109]]],[[[233932202702228,150076014081428],[203959807452308,120103618831508]],[[414817098909736,247104721668136],[354872308409896,187159931168296]],[[157300343157908,73444154537108],[127327947907988,43471759287188]]],[[[348296022784798,222970250138398],[303354268449118,178028495802718]],[[615752594161916,365101048869116],[525869085490556,275217540197756]],[[232208697820318,106882925173918],[187266943484638,61941170838238]]],[[[230428619798100,147183034492500],[200479363304100,117233777998500]],[[406122089179800,239630918568600],[346223576191800,179732405580600]],[[152280648514500,69035063208900],[122331392020500,39085806714900]]],[[[57156478134939,36421128323739],[49672312812459,28936963001259]],[[100419495588198,58948795965798],[85451164943238,43980465320838]],[[37431200318859,16695850507659],[29947034996379,9211685185179]]]]

private theorem identity_0392 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1023520576131 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0392 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0392, p_headbox] <;> ring

private theorem negative_0392 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0392 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0392] at hp
  linarith only [hp]

private def coefficients_0393 : List (List (List (List ℕ))) :=
  [[[[71018323,258244646,183352723],[26859283,169926566,139193683]],[[115177363,346562726,227511763],[71018323,258244646,183352723]]],[[[130108470,492632940,354777270],[41209350,314834700,265878150]],[[219007590,670431180,443676390],[130108470,492632940,354777270]]],[[[58910589,234029178,171244989],[14170509,144549018,126504909]],[[103650669,323509338,215985069],[58910589,234029178,171244989]]]]

private theorem identity_0393 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(1574501 / 110182400 : ℝ)) =
      tensor4 coefficients_0393 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0393, p_coupled] <;> ring

private theorem negative_0393 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0393 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0393] at hp
  linarith only [hp]

private theorem node_0404 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0392 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0393 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0394 : List (List (List (List ℕ))) :=
  [[[[38728408,88310488],[536478416,635642576],[504722488,554304568]],[[524857616,624021776],[1984027552,2182355872],[1473114896,1572279056]],[[493101688,542683768],[1461494096,1560658256],[975364888,1024946968]]],[[[177532528,276696688],[1276885016,1475213336],[1113297448,1212461608]],[[1253643416,1451971736],[4383464992,4780121632],[3157711496,3356039816]],[[1090055848,1189220008],[3134469896,3332798216],[2058359008,2157523168]]],[[[139150121,188732201],[741098602,840262762],[608920961,658503041]],[[729477802,828641962],[2400821444,2599149764],[1685288602,1784452762]],[[597300161,646882241],[1673667802,1772831962],[1083340121,1132922201]]]]

private theorem identity_0394 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(4841051 / 86768640 : ℝ)) =
      tensor4 coefficients_0394 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0394, p_variance] <;> ring

private theorem negative_0394 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0394 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0394] at hp
  linarith only [hp]

private theorem node_0403 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0404 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0394 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0395 : List (List (List (List ℕ))) :=
  [[[[31755928,81338008],[986203376,1085367536],[982337368,1031919448]],[[508588496,607752656],[2895098272,3093426592],[2442289616,2541453776]],[[483805048,533387128],[1922839856,2022004016],[1466924728,1516506808]]],[[[163587568,262751728],[2180111696,2378440016],[2072303968,2171468128]],[[1221105176,1419433496],[6213159952,6609816592],[5103614456,5301942776]],[[1071462568,1170626728],[4060938176,4259266496],[3045255448,3144419608]]],[[[132177641,181759721],[1194600322,1293764482],[1090312601,1139894681]],[[713208682,812372842],[3319445684,3517774004],[2662016842,2761181002]],[[588003521,637585601],[2138790322,2237954482],[1578676721,1628258801]]]]

private theorem identity_0395 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(3969491 / 86768640 : ℝ)) =
      tensor4 coefficients_0395 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0395, p_variance] <;> ring

private theorem negative_0395 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0395 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0395] at hp
  linarith only [hp]

private theorem node_0402 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0403 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0395 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0396 : List (List (List (List ℕ))) :=
  [[[[29149565215427,18781890309827],[25407482554187,15039807648587]],[[51352400090014,30617050278814],[43868234767534,23132884956334]],[[19286926307387,8919251401787],[15544843646147,5177168740547]]],[[[115696907232536,74378300640536],[100734874189616,59416267597616]],[[203187546946552,120550333762552],[173263480860712,90626267676712]],[[75869781610016,34551175018016],[60907748567096,19589141975096]]],[[[172167846505112,110417518364312],[149734754949512,87984426808712]],[[301399890375424,177899234093824],[256533707264224,133033050982624]],[[111864764080712,50114435939912],[89431672525112,27681344384312]]],[[[113843180180736,72827644052736],[98894762938656,57879226810656]],[[198646642384992,116615570128992],[168749807900832,86718735644832]],[[73267842668256,32252306540256],[58319425426176,17303889298176]]],[[[28222673988952,18006534315352],[24487397920792,14271258247192]],[[49081895458544,28649616111344],[41611343322224,21179063975024]],[[17985932186392,7769792512792],[14250656118232,4034516444632]]]]

private theorem identity_0396 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(504314555579 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0396 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0396, p_headbox] <;> ring

private theorem negative_0396 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0396 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0396] at hp
  linarith only [hp]

private def coefficients_0397 : List (List (List (List ℕ))) :=
  [[[[32717267,123538534,88884467],[10347227,78798454,66514427]],[[55087307,168278614,111254507],[32717267,123538534,88884467]]],[[[59290888,234789776,171625288],[14260288,144728576,126594688]],[[104321488,324850976,216655888],[59290888,234789776,171625288]]],[[[26483842,111071684,82651042],[3823282,65750564,59990482]],[[49144402,156392804,105311602],[26483842,111071684,82651042]]]]

private theorem identity_0397 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(1911641 / 247910400 : ℝ)) =
      tensor4 coefficients_0397 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0397, p_coupled] <;> ring

private theorem negative_0397 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0397 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0397] at hp
  linarith only [hp]

private theorem node_0407 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0396 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0397 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0398 : List (List (List (List ℕ))) :=
  [[[[177878529,277042689],[1281353778,1479682098],[1117420209,1216584369]],[[1258112178,1456440498],[4399956036,4796612676],[3169733778,3368062098]],[[1094178609,1193342769],[3146492178,3344820498],[2066258529,2165422689]]],[[[557292486,755620806],[2973331932,3369988572],[2443929366,2642257686]],[[2926848732,3323505372],[9636267864,10429581144],[6765198972,7161855612]],[[2397446166,2595774486],[6718715772,7115372412],[4349159526,4547487846]]],[[[380105959,479270119],[1693362158,1891690478],[1327201159,1426365319]],[[1670120558,1868448878],[5239079836,5635736476],[3596849198,3795177518]],[[1303959559,1403123719],[3573607598,3771935918],[2283592999,2382757159]]]]

private theorem identity_0398 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(19764281 / 154255360 : ℝ)) =
      tensor4 coefficients_0398 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0398, p_variance] <;> ring

private theorem negative_0398 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0398 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0398] at hp
  linarith only [hp]

private theorem node_0406 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0407 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0398 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0399 : List (List (List (List ℕ))) :=
  [[[[163933569,263097729],[2188357218,2386685538],[2080203489,2179367649]],[[1225573938,1423902258],[6237204516,6633861156],[5123190258,5321518578]],[[1075585329,1174749489],[4076737218,4275065538],[3056931729,3156095889]]],[[[529402566,727730886],[4794892332,5191548972],[4377049446,4575377766]],[[2861772252,3258428892],[13325871864,14119185144],[10687218972,11083875612]],[[2360259606,2558587926],[8586759372,8983416012],[6338059446,6536387766]]],[[[366160999,465325159],[2607919118,2806247438],[2297537959,2396702119]],[[1637582318,1835910638],[7091435356,7488091996],[5565412718,5763741038]],[[1285366279,1384530439],[4511406158,4709734478],[3281819719,3380983879]]]]

private theorem identity_0399 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(18214841 / 154255360 : ℝ)) =
      tensor4 coefficients_0399 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0399, p_variance] <;> ring

private theorem negative_0399 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0399 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0399] at hp
  linarith only [hp]

private theorem node_0405 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0406 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0399 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0401 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 32 : ℝ)
  · exact node_0402 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0405 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0400 : List (List (List (List ℕ))) :=
  [[[[39092507,132415414,89449307],[17012987,88256374,67369787]],[[61172027,176574454,111528827],[39092507,132415414,89449307]]],[[[72220926,252902652,172934526],[27480846,163422492,128194446]],[[116961006,342382812,217674606],[72220926,252902652,172934526]]],[[[32948861,120128122,83305661],[10288301,74807002,60645101]],[[55609421,165449242,105966221],[32948861,120128122,83305661]]]]

private theorem identity_0400 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(10288301 / 247910400 : ℝ)) =
      tensor4 coefficients_0400 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0400, p_coupled] <;> ring

private theorem negative_0400 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0400 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0400] at hp
  linarith only [hp]

private theorem node_0400 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0401 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0400 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0386 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0387 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0400 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0401 : List (List (List (List ℕ))) :=
  [[[[31538987,187033174,139999787],[9459467,142874134,117920267]],[[53618507,231192214,162079307],[31538987,187033174,139999787]]],[[[58275966,364462332,275197566],[13535886,274982172,230457486]],[[103016046,453942492,319937646],[58275966,364462332,275197566]]],[[[26557421,177070042,135018221],[3896861,131748922,112357661]],[[49217981,222391162,157678781],[26557421,177070042,135018221]]]]

private theorem identity_0401 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(3896861 / 247910400 : ℝ)) =
      tensor4 coefficients_0401 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0401, p_coupled] <;> ring

private theorem negative_0401 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0401 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0401] at hp
  linarith only [hp]

private def coefficients_0402 : List (List (List (List ℕ))) :=
  [[[[64445122,89236162],[367697684,417279764],[310225042,335016082]],[[358401044,407983124],[1210686088,1309850248],[866230004,915812084]],[[300928402,325719442],[856933364,906515444],[562977442,587768482]]],[[[180816480,230398560],[843024600,942188760],[676153080,725735160]],[[824431320,923595480],[2644184160,2842512480],[1847642760,1946806920]],[[657559800,707141880],[1829049480,1928213640],[1185434640,1235016720]]],[[[116717359,141508399],[476018918,525600998],[366274039,391065079]],[[466722278,516304358],[1434882076,1534046236],[982104758,1031686838]],[[356977399,381768439],[972808118,1022390198],[622803199,647594239]]]]

private theorem identity_0402 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(4603223 / 12395520 : ℝ)) =
      tensor4 coefficients_0402 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0402, p_variance] <;> ring

private theorem negative_0402 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0402 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0402] at hp
  linarith only [hp]

private theorem node_0408 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0401 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0402 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0385 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0386 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0408 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0403 : List (List (List (List ℕ))) :=
  [[[[78913815725549,38049257031149],[63972711452909,23108152758509]],[[143100726412378,61371609023578],[113218517867098,31489400478298]],[[58440332120429,17575773426029],[43499227847789,2634669153389]]],[[[313721042574580,150866717531380],[253985877361780,91131552318580]],[[567706280792360,241997630705960],[448235950366760,122527300280360]],[[231083848758580,68229523715380],[171348683545780,8494358502580]]],[[[467626918116958,224249063960158],[378070063161118,134692209004318]],[[844413125752796,357657417439196],[665299415841116,178543707527516]],[[342561196895038,99183342738238],[253004341939198,9626487782398]]],[[[309745864253668,148094896292068],[250073222431108,88422254469508]],[[558110112662456,234808176739256],[438764829017336,115462893094136]],[[225632081039188,63981113077588],[165959439216628,4308471255028]]],[[[76926169578179,36663289424579],[62016321771299,21753441617699]],[[138302534474518,57776774167318],[108482838860758,27957078553558]],[[55714397374739,15451517221139],[40804549567859,541669414259]]]]

private theorem identity_0403 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(541669414259 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0403 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0403, p_headbox] <;> ring

private theorem negative_0403 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0403 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0403] at hp
  linarith only [hp]

private def coefficients_0404 : List (List (List (List ℕ))) :=
  [[[[66740507,381391414,299156507],[21419387,290749174,253835387]],[[112061627,472033654,344477627],[66740507,381391414,299156507]]],[[[122577726,740976252,587409726],[31354446,558529692,496186446]],[[213801006,923422812,678633006],[122577726,740976252,587409726]]],[[[55657661,359225722,288073661],[9755501,267421402,242171501]],[[101559821,451030042,333975821],[55657661,359225722,288073661]]]]

private theorem identity_0404 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(9755501 / 991641600 : ℝ)) =
      tensor4 coefficients_0404 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0404, p_coupled] <;> ring

private theorem negative_0404 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0404 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0404] at hp
  linarith only [hp]

private def coefficients_0405 : List (List (List (List ℕ))) :=
  [[[[762395016640429,435478547085229],[642866182459309,315949712904109]],[[1315029535908698,661196596798298],[1075971867546458,422138928436058]],[[529648205002669,202731735447469],[410119370821549,83202901266349]]],[[[3028277236287668,1723026997004468],[2550278907074228,1245028667791028]],[[5214879144730216,2604378666163816],[4258882486303336,1648382007736936]],[[2094826500992948,789576261709748],[1616828171779508,311577932496308]]],[[[4510272212481358,2556015849575758],[3793454260021198,1839197897115598]],[[7754090715327836,3845577989516636],[6320454810407516,2411942084596316]],[[3106409852329678,1152153489424078],[2389591899869518,435335536963918]]],[[[2985292582288980,1684864696106580],[2507536317825780,1207108431643380]],[[5123661751556760,2522805979191960],[4168149222630360,1567293450265560]],[[2046932833520580,746504947338180],[1569176569057380,268748682874980]]],[[[740902586047299,416397293042499],[621494779011939,296989486007139]],[[1269420638235318,620410052225718],[1030605024164598,381594438154998]],[[505701273773619,181195980768819],[386293466738259,61788173733459]]]]

private theorem identity_0405 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6865352637051 / 180522844160000 : ℝ)) =
      tensor4 coefficients_0405 ((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0405, p_headbox] <;> ring

private theorem negative_0405 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0405 ((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0405] at hp
  linarith only [hp]

private def coefficients_0406 : List (List (List (List ℕ))) :=
  [[[[210177763,916176326,690504163],[28893283,553607366,509219683]],[[300820003,1097460806,781146403],[119535523,734891846,599861923]]],[[[397967910,1787577420,1358620710],[34236870,1060115340,994889670]],[[579833430,2151308460,1540486230],[216102390,1423846380,1176755190]]],[[[187610589,871041978,667936989],[5164029,506148858,485490429]],[[278833869,1053488538,759160269],[96387309,688595418,576713709]]]]

private theorem identity_0406 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(573781 / 440729600 : ℝ)) =
      tensor4 coefficients_0406 ((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0406, p_coupled] <;> ring

private theorem negative_0406 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0406 ((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0406] at hp
  linarith only [hp]

private theorem node_0417 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0405 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0406 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0407 : List (List (List (List ℕ))) :=
  [[[[375895711240787,213643064738387],[316191807723107,153939161220707]],[[645599155551934,321093862547134],[526191348516574,201686055511774]],[[258295055103947,96042408601547],[198591151586267,36338505083867]]],[[[1492741725913256,844934496985256],[1253988630003416,606181401075416]],[[2559407022899992,1263792565043992],[2081900831080312,786286373224312]],[[1021116351202736,373309122274736],[782363255292896,134556026364896]]],[[[2222755901244152,1252847862280952],[1864722033979352,894813995016152]],[[3804440780423104,1864624702496704],[3088373045893504,1148556967967104]],[[1513488220189352,543580181226152],[1155454352924552,185546313961352]]],[[[1470869362710336,825464385558336],[1232245296610176,586840319458176]],[[2513056906452192,1222246952148192],[2035808774251872,744998819947872]],[[996807506285856,351402529133856],[758183440185696,112778463033696]]],[[[364959474434872,203907953820472],[305320083207352,144268562592952]],[[622423989969584,300320948740784],[503145207514544,181042166285744]],[[246140580491512,85089059877112],[186501189263992,25449668649592]]]]

private theorem identity_0407 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(3181208581199 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0407 ((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0407, p_headbox] <;> ring

private theorem negative_0407 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0407 ((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0407] at hp
  linarith only [hp]

private def coefficients_0408 : List (List (List (List ℕ))) :=
  [[[[291665169,489993489],[4303148418,4699805058],[4067263089,4265591409]],[[2364217938,2760874578],[12233148516,13026461796],[9980490258,10377146898]],[[2086497729,2284826049],[7957890018,8354546658],[5927172129,6125500449]]],[[[982999686,1379656326],[9420742572,10214055852],[8549302566,8945959206]],[[5535328092,6328641372],[26110295544,27696922104],[20798086812,21591400092]],[[4580218326,4976874966],[16745332812,17538646092],[12276674166,12673330806]]],[[[692026519,890354839],[5118978158,5515634798],[4482731479,4681059799]],[[3172494158,3569150798],[13879915036,14673228316],[10818980558,11215637198]],[[2494412599,2692740919],[8788826798,9185483438],[6350194039,6548522359]]]]

private theorem identity_0408 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(32407241 / 617021440 : ℝ)) =
      tensor4 coefficients_0408 ((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0408, p_variance] <;> ring

private theorem negative_0408 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0408 ((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(29 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0408] at hp
  linarith only [hp]

private theorem node_0418 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0407 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0408 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0416 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 64 : ℝ)
  · exact node_0417 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0418 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0409 : List (List (List (List ℕ))) :=
  [[[[104411267,325030534,216745667],[59090147,234388294,171424547]],[[149732387,415672774,262066787],[104411267,325030534,216745667]]],[[[197338206,627092412,422007006],[106114926,444645852,330783726]],[[288561486,809538972,513230286],[197338206,627092412,422007006]]],[[[92747381,301702762,205081781],[46845221,209898442,159179621]],[[138649541,393507082,250983941],[92747381,301702762,205081781]]]]

private theorem identity_0409 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(46845221 / 991641600 : ℝ)) =
      tensor4 coefficients_0409 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0409, p_coupled] <;> ring

private theorem negative_0409 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0409 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0409] at hp
  linarith only [hp]

private theorem node_0415 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0416 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0409 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0414 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0404 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0415 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0413 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0403 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0414 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0410 : List (List (List (List ℕ))) :=
  [[[[37151463176219,17020023099419],[33424001224499,13292561147699]],[[66528024011518,26265143857918],[59073100108078,18810219954478]],[[26545577074499,6414136997699],[22818115122779,2686675045979]]],[[[147585259734400,67359223100800],[132683724576280,52457687942680]],[[263662108663880,103210035396680],[233859038347640,73406965080440]],[[104795062527880,24569025894280],[89893527369760,9667490736160]]],[[[219820171558400,99929586521600],[197480833712000,77590248675200]],[[391767179228800,151986009155200],[347088503536000,107307333462400]],[[155087394149600,35196809112800],[132748056303200,12857471266400]]],[[[145490356224000,65861535744000],[130606435584000,50977615104000]],[[258660013824000,99402372864000],[228892172544000,69634531584000]],[[101971854720000,22343034240000],[87087934080000,7459113600000]]],[[[36103979520000,16271147520000],[32385323520000,12552491520000]],[[64026915840000,24361251840000],[56589603840000,16923939840000]],[[25133944320000,5301112320000],[21415288320000,1582456320000]]]]

private theorem identity_0410 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(68683 / 2203648 : ℝ)) =
      tensor4 coefficients_0410 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0410, p_headbox] <;> ring

private theorem negative_0410 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0410 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0410] at hp
  linarith only [hp]

private def coefficients_0411 : List (List (List (List ℕ))) :=
  [[[[30325121224499,20259401186099],[26597659272779,16531939234379]],[[52875340108078,32743900031278],[45420416204638,25288976127838]],[[19719235122779,9653515084379],[15991773171059,5926053132659]]],[[[120288204576280,80175186259480],[105386669418160,65273651101360]],[[209067998347640,128841961714040],[179264928031400,99038891397800]],[[77498007369760,37384989052960],[62596472211640,22483453894840]]],[[[178887553712000,118942261193600],[156548215865600,96602923347200]],[[309901943536000,190011358499200],[265223267843200,145332682806400]],[[114154776303200,54209483784800],[91815438456800,31870145938400]]],[[[118210915584000,78396505344000],[103326994944000,63512584704000]],[[204101132544000,124472312064000],[174333291264000,94704470784000]],[[74692414080000,34878003840000],[59808493440000,19994083200000]]],[[[29286443520000,19370027520000],[25567787520000,15651371520000]],[[50391843840000,30559011840000],[42954531840000,23121699840000]],[[18316408320000,8399992320000],[14597752320000,4681336320000]]]]

private theorem identity_0411 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(203183 / 2203648 : ℝ)) =
      tensor4 coefficients_0411 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0411, p_headbox] <;> ring

private theorem negative_0411 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0411 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0411] at hp
  linarith only [hp]

private def coefficients_0412 : List (List (List (List ℕ))) :=
  [[[[38194421,134492842,94361621],[15243341,88590682,71410541]],[[61145501,180395002,117312701],[38194421,134492842,94361621]]],[[[70176600,256561200,182511000],[23983920,164175840,136318320]],[[116369280,348946560,228703680],[70176600,256561200,182511000]]],[[[31892400,121888800,88059600],[8650800,75405600,64818000]],[[55134000,168372000,111301200],[31892400,121888800,88059600]]]]

private theorem identity_0412 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(2403 / 137728 : ℝ)) =
      tensor4 coefficients_0412 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0412, p_coupled] <;> ring

private theorem negative_0412 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0412 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0412] at hp
  linarith only [hp]

private theorem node_0421 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0411 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0412 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0420 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0410 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0421 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0413 : List (List (List (List ℕ))) :=
  [[[[30834581,185624362,147042581],[7883501,139722202,124091501]],[[53785661,231526522,169993661],[30834581,185624362,147042581]]],[[[56037960,359986320,288453960],[9845280,267600960,242261280]],[[102230640,452371680,334646640],[56037960,359986320,288453960]]],[[[25113600,174182400,141321600],[1872000,127699200,118080000]],[[48355200,220665600,164563200],[25113600,174182400,141321600]]]]

private theorem identity_0413 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(65 / 17216 : ℝ)) =
      tensor4 coefficients_0413 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0413, p_coupled] <;> ring

private theorem negative_0413 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0413 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0413] at hp
  linarith only [hp]

private def coefficients_0414 : List (List (List (List ℕ))) :=
  [[[[740989915195949,418886873967149],[621711132740909,299608091512109]],[[1266989912591578,622783830133978],[1028432347681498,384226265223898]],[[503352127309229,181249086080429],[384073344854189,61970303625389]]],[[[2941896730842100,1655882355315700],[2464914603402100,1178900227875700]],[[5021237757218600,2449209006165800],[4067273502338600,1495244751285800]],[[1988918140597300,702903765070900],[1511936013157300,225921637630900]]],[[[4379560020795358,2454130679201758],[3664290300546718,1738860958953118]],[[7461401797874396,3610543114687196],[6030862357377116,2180003674189916]],[[2946460026498238,1021030684904638],[2231190306249598,305760964655998]]],[[[2897389282215268,1616161560692068],[2420681083759108,1139453362235908]],[[4927049531395256,2364594088348856],[3973633134482936,1411177691436536]],[[1939573925010388,658346203487188],[1462865726554228,181638005031028]]],[[[718736073658499,399026359431299],[599594250466019,279884536238819]],[[1219895571332758,580476142878358],[981611924947798,342192496493398]],[[478679908392659,158970194165459],[359538085200179,39828370972979]]]]

private theorem identity_0414 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(39828370972979 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_0414 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0414, p_headbox] <;> ring

private theorem negative_0414 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0414 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0414] at hp
  linarith only [hp]

private def coefficients_0415 : List (List (List (List ℕ))) :=
  [[[[245922922,345087082],[2359308404,2557636724],[2141275402,2240439562]],[[1386066404,1584394724],[6539596168,6936252808],[5209309604,5407637924]],[[1147115962,1246280122],[4194232724,4392561044],[3075006682,3174170842]]],[[[692372520,890700840],[5127223680,5523880320],[4490631000,4688959320]],[[3176962920,3573619560],[13903959600,14697272880],[10838556360,11235213000]],[[2498535360,2696863680],[8804625840,9201282480],[6361870320,6560198640]]],[[[446795599,545959759],[2768607278,2966935598],[2349701599,2448865759]],[[1791588518,1989916838],[7365747436,7762404076],[5629938758,5828267078]],[[1351765399,1450929559],[4611085118,4809413438],[3287209639,3386373799]]]]

private theorem identity_0415 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(17565923 / 198328320 : ℝ)) =
      tensor4 coefficients_0415 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0415, p_variance] <;> ring

private theorem negative_0415 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0415 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0415] at hp
  linarith only [hp]

private theorem node_0425 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0414 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0415 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0416 : List (List (List (List ℕ))) :=
  [[[[364994933995739,205140076882139],[305424022399499,145569165285899]],[[621201579999358,301491865772158],[502059756806878,182350042579678]],[[244966851362819,85111994249219],[185395939766579,25541082652979]]],[[[1448757242192320,810532246045120],[1210544048650480,572319052503280]],[[2461072696965320,1184622704670920],[1984646309881640,708196317587240]],[[967440259731400,329215263584200],[729227066189560,91002070042360]]],[[[2156206430652800,1200658353699200],[1798994287587200,843446210633600]],[[3655821926742400,1744725772835200],[2941397640611200,1030301486704000]],[[1432428521928800,476880444975200],[1075216378863200,119668301909600]]],[[[1426120750080000,790280156160000],[1188052392960000,552211799040000]],[[2413231847424000,1141550659584000],[1937095133184000,665413945344000]],[[942403555584000,306562961664000],[704335198464000,68494604544000]]],[[[353676625920000,195013969920000],[294178129920000,135515473920000]],[[597281034240000,279955722240000],[478284042240000,160958730240000]],[[232448440320000,73785784320000],[172949944320000,14287288320000]]]]

private theorem identity_0416 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(155027 / 8814592 : ℝ)) =
      tensor4 coefficients_0416 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0416, p_headbox] <;> ring

private theorem negative_0416 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0416 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0416] at hp
  linarith only [hp]

private def coefficients_0417 : List (List (List (List ℕ))) :=
  [[[[692718521,891046841],[5135469202,5532125842],[4498530521,4696858841]],[[3181431682,3578088322],[13928004164,14721317444],[10858132162,11254788802]],[[2502658121,2700986441],[8820424882,9217081522],[6373546601,6571874921]]],[[[1787874398,2184531038],[11090920156,11884233436],[9414605438,9811262078]],[[7175291596,7968604876],[29511078872,31097705432],[22558906636,23352219916]],[[5415307118,5811963758],[18475938556,19269251836],[13172191118,13568847758]]],[[[1095847879,1294176199],[5956834958,6353491598],[4916766919,5115095239]],[[3995243918,4391900558],[15585842716,16379155996],[11702158478,12098815118]],[[2913340999,3111669319],[9656897678,10053554318],[6799336519,6997664839]]]]

private theorem identity_0417 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(692718521 / 5553192960 : ℝ)) =
      tensor4 coefficients_0417 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0417, p_variance] <;> ring

private theorem negative_0417 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0417 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0417] at hp
  linarith only [hp]

private theorem node_0426 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0416 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0417 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0424 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 64 : ℝ)
  · exact node_0425 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0426 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0418 : List (List (List (List ℕ))) :=
  [[[[49524701,157153402,105691901],[26573621,111251242,82740821]],[[72475781,203055562,128642981],[49524701,157153402,105691901]]],[[[93127680,302463360,205462080],[46935000,210078000,159269400]],[[139320360,394848720,251654760],[93127680,302463360,205462080]]],[[[43513200,145130400,99680400],[20271600,98647200,76438800]],[[66754800,191613600,122922000],[43513200,145130400,99680400]]]]

private theorem identity_0418 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(5631 / 137728 : ℝ)) =
      tensor4 coefficients_0418 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0418, p_coupled] <;> ring

private theorem negative_0418 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0418 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0418] at hp
  linarith only [hp]

private theorem node_0423 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0424 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0418 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0422 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0413 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0423 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0419 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0420 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0422 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0412 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 32 : ℝ)
  · exact node_0413 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0419 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0419 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0419 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0419 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0419, p_qmass] <;> ring

private theorem negative_0419 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0419 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0419] at hp
  linarith only [hp]

private theorem node_0411 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0412 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0419 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0420 : List (List (List (List ℕ))) :=
  [[[[57634453366229,37202174019029],[50163901229909,29731621882709]],[[100542001693738,59677442999338],[85600897421098,44736338726698]],[[37160969761109,16728690413909],[29690417624789,9258138277589]]],[[[228632845015060,147205682493460],[198765262408660,117338099887060]],[[397529885673320,234675560630120],[337794720460520,174940395417320]],[[145995651199060,64568488677460],[116128068592660,34700906071060]]],[[[340040514641038,218351587562638],[295262087163118,173573160084718]],[[589240318800956,345862464644156],[499683463845116,256305609688316]],[[214974793419118,93285866340718],[170196365941198,48507438862798]]],[[[224720190084388,143894706103588],[194883869173108,114058385192308]],[[388058764323896,226407796362296],[328386122501336,166735154539736]],[[140606406869908,59780922889108],[110770085958628,29944601977828]]],[[[55678063684619,35546623607819],[48223139781179,28091699704379]],[[95806322687398,55543442533798],[80896474880518,40633594726918]],[[34466291481179,14334851404379],[27011367577739,6879927500939]]]]

private theorem identity_0420 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6879927500939 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0420 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0420, p_headbox] <;> ring

private theorem negative_0420 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0420 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0420] at hp
  linarith only [hp]

private def coefficients_0421 : List (List (List (List ℕ))) :=
  [[[[59671187,235550374,172005587],[14350067,144908134,126684467]],[[104992307,326192614,217326707],[59671187,235550374,172005587]]],[[[106695966,445807932,331364766],[15472686,263361372,240141486]],[[197919246,628254492,422588046],[106695966,445807932,331364766]]],[[[46845221,209898442,159179621],[943061,118094122,113277461]],[[92747381,301702762,205081781],[46845221,209898442,159179621]]]]

private theorem identity_0421 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(943061 / 991641600 : ℝ)) =
      tensor4 coefficients_0421 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0421, p_coupled] <;> ring

private theorem negative_0421 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0421 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0421] at hp
  linarith only [hp]

private theorem node_0431 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0420 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0421 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0422 : List (List (List (List ℕ))) :=
  [[[[139496122,189078202],[745567364,844731524],[613043722,662625802]],[[733946564,833110724],[2417312488,2615640808],[1697310884,1796475044]],[[601422922,651005002],[1685690084,1784854244],[1091239642,1140821722]]],[[[380451960,479616120],[1697830920,1896159240],[1331323920,1430488080]],[[1674589320,1872917640],[5255570880,5652227520],[3608871480,3807199800]],[[1308082320,1407246480],[3585629880,3783958200],[2291492520,2390656680]]],[[[241301839,290883919],[952955558,1052119718],[718626199,768208279]],[[941334758,1040498918],[2839642396,3037970716],[1912252598,2011416758]],[[707005399,756587479],[1900631798,1999795958],[1200598879,1250180959]]]]

private theorem identity_0422 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(69748061 / 347074560 : ℝ)) =
      tensor4 coefficients_0422 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0422, p_variance] <;> ring

private theorem negative_0422 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0422 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0422] at hp
  linarith only [hp]

private theorem node_0430 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0431 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0422 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0423 : List (List (List (List ℕ))) :=
  [[[[132523642,182105722],[1202845844,1302010004],[1098212122,1147794202]],[[717677444,816841604],[3343490248,3541818568],[2681592644,2780756804]],[[592126282,641708362],[2154589364,2253753524],[1590353002,1639935082]]],[[[366507000,465671160],[2616164640,2814492960],[2305437480,2404601640]],[[1642051080,1840379400],[7115479920,7512136560],[5584988520,5783316840]],[[1289489040,1388653200],[4527205200,4725533520],[3293496000,3392660160]]],[[[234329359,283911439],[1414010798,1513174958],[1207571359,1257153439]],[[925065638,1024229798],[3773373676,3971701996],[2904087878,3003252038]],[[697708759,747290839],[2373307838,2472471998],[1703488999,1753071079]]]]

private theorem identity_0423 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(66261821 / 347074560 : ℝ)) =
      tensor4 coefficients_0423 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0423, p_variance] <;> ring

private theorem negative_0423 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0423 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0423] at hp
  linarith only [hp]

private theorem node_0429 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0430 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0423 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0424 : List (List (List (List ℕ))) :=
  [[[[28456987272779,18391267234379],[24729525321059,14663805282659]],[[49139072204638,29007632127838],[41684148301198,21552708224398]],[[17851101171059,7785381132659],[14123639219339,4057919180939]]],[[[112823981418160,72710963101360],[97922446260040,57809427943240]],[[194139552031400,113913515397800],[164336481715160,84110445081560]],[[70033784211640,29920765894840],[55132249053520,15019230736720]]],[[[167704183865600,107758891347200],[145364846019200,85419553500800]],[[287535203843200,167644618806400],[242856528150400,122965943113600]],[[102971406456800,43026113938400],[80632068610400,20686776092000]]],[[[110764306944000,70949896704000],[95880386304000,56065976064000]],[[189207915264000,109579094784000],[159440073984000,79811253504000]],[[67245805440000,27431395200000],[52361884800000,12547474560000]]],[[[27427115520000,17510699520000],[23708459520000,13792043520000]],[[46673187840000,26840355840000],[39235875840000,19403043840000]],[[16457080320000,6540664320000],[12738424320000,2822008320000]]]]

private theorem identity_0424 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(122483 / 2203648 : ℝ)) =
      tensor4 coefficients_0424 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0424, p_headbox] <;> ring

private theorem negative_0424 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0424 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0424] at hp
  linarith only [hp]

private def coefficients_0425 : List (List (List (List ℕ))) :=
  [[[[640845639492749,318742598263949],[521566857037709,199463815808909]],[[1157292841530778,513086759073178],[918735276620698,274529194163098]],[[493799331951629,171696290722829],[374520549496589,52417508267789]]],[[[2549716864592500,1263702489066100],[2072734737152500,786720361626100]],[[4598569567836200,2026540816783400],[3644605312956200,1072576561903400]],[[1958429817464500,672415441938100],[1481447690024500,195433314498100]]],[[[3803865600416158,1878436258822558],[3088595880167518,1163166538573918]],[[6851539959439196,3000681276251996],[5421000518941916,1570141835754716]],[[2912292608442238,986863266848638],[2197022888193598,271593546599998]]],[[[2521962902530468,1240735181007268],[2045254704074308,764026982551108]],[[4536542068704056,1974086625657656],[3583125671791736,1020670228745336]],[[1924492842003988,643265120480788],[1447784643547828,166556922024628]]],[[[626968523806499,307258809579299],[507826700614019,188116986386819]],[[1126278828755158,486859400300758],[887995182370198,248575753915798]],[[476830715667059,157121001439859],[357688892474579,37979178247379]]]]

private theorem identity_0425 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(37979178247379 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_0425 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0425, p_headbox] <;> ring

private theorem negative_0425 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 64 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (17 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0425 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0425] at hp
  linarith only [hp]

private def coefficients_0426 : List (List (List (List ℕ))) :=
  [[[[246668867,958169734,696006467],[63060227,590952454,512397827]],[[338473187,1141778374,787810787],[154864547,774561094,604202147]]],[[[467907726,1865479452,1366582926],[99528366,1128720732,998203566]],[[652097406,2233858812,1550772606],[283718046,1497100092,1182393246]]],[[[221059301,906950602,670396901],[36288581,537409162,485626181]],[[313444661,1091721322,762782261],[128673941,722179882,578011541]]]]

private theorem identity_0426 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(36288581 / 3966566400 : ℝ)) =
      tensor4 coefficients_0426 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0426, p_coupled] <;> ring

private theorem negative_0426 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 64 : ℝ))
    (h1l : (17 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0426 ((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0426] at hp
  linarith only [hp]

private theorem node_0436 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 64 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (17 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0425 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0426 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0427 : List (List (List (List ℕ))) :=
  [[[[317194921106939,157340063993339],[257624009510699,97769152397099]],[[570560732784958,250851018557758],[451418909592478,131709195365278]],[[242126017037219,82271159923619],[182555105440979,22700248327379]]],[[[1261735280775520,623510284628320],[1023522087233680,385297091086480]],[[2266529554298120,990079562003720],[1790103167214440,513653174920040]],[[959919078481000,321694082333800],[721705884939160,83480888791960]]],[[[1881930333516800,926382256563200],[1524718190451200,569170113497600]],[[3376017629113600,1464921475206400],[2661593342982400,750497189075200]],[[1426900321436000,471352244482400],[1069688178370400,114140101416800]]],[[[1247434371072000,611593777152000],[1009366013952000,373525420032000]],[[2234689256448000,963008068608000],[1758552542208000,486871354368000]],[[942547343616000,306706749696000],[704478986496000,68638392576000]]],[[[310044395520000,151381739520000],[250545899520000,91883243520000]],[[554640445440000,237315133440000],[435643453440000,118318141440000]],[[233440081920000,74777425920000],[173941585920000,15278929920000]]]]

private theorem identity_0427 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(165787 / 8814592 : ℝ)) =
      tensor4 coefficients_0427 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0427, p_headbox] <;> ring

private theorem negative_0427 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (17 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0427 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0427] at hp
  linarith only [hp]

private def coefficients_0428 : List (List (List (List ℕ))) :=
  [[[[117312341,467040682,341981141],[24926981,282269962,249595781]],[[163505021,559426042,388173821],[71119661,374655322,295788461]]],[[[221730120,908292240,671067720],[36378360,537588720,485715960]],[[314406000,1093644000,763743600],[129054240,722940480,578391840]]],[[[104328000,441072000,328996800],[11361600,255139200,236030400]],[[150811200,534038400,375480000],[57844800,348105600,282513600]]]]

private theorem identity_0428 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(789 / 137728 : ℝ)) =
      tensor4 coefficients_0428 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0428, p_coupled] <;> ring

private theorem negative_0428 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (17 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0428 ((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(31 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(17 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0428] at hp
  linarith only [hp]

private theorem node_0437 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (17 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0427 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0428 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0435 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 64 : ℝ)
  · exact node_0436 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0437 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0434 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0424 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0435 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0429 : List (List (List (List ℕ))) :=
  [[[[380797961,479962121],[1702299682,1900628002],[1335446681,1434610841]],[[1679058082,1877386402],[5272061924,5668718564],[3620893762,3819222082]],[[1312205081,1411369241],[3597652162,3795980482],[2299392041,2398556201]]],[[[965899358,1164227678],[3820759756,4217416396],[2882750318,3081078638]],[[3774276556,4170933196],[11391551672,12184864952],[7673054956,8069711596]],[[2836267118,3034595438],[7626571756,8023228396],[4818194558,5016522878]]],[[[585793399,684957559],[2119844078,2318172398],[1547995639,1647159799]],[[2096602478,2294930798],[6122257756,6518914396],[4053545198,4251873518]],[[1524754039,1623918199],[4030303598,4228631918],[2519494519,2618658679]]]]

private theorem identity_0429 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(380797961 / 1388298240 : ℝ)) =
      tensor4 coefficients_0429 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0429, p_variance] <;> ring

private theorem negative_0429 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0429 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0429] at hp
  linarith only [hp]

private theorem node_0433 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0434 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0429 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0430 : List (List (List (List ℕ))) :=
  [[[[366853001,466017161],[2624410162,2822738482],[2313337001,2412501161]],[[1646519842,1844848162],[7139524484,7536181124],[5604564322,5802892642]],[[1293611801,1392775961],[4543004242,4741332562],[3305172281,3404336441]]],[[[938009438,1136337758],[5672534236,6069190876],[4846084478,5044412798]],[[3709200076,4105856716],[15141583832,15934897112],[11655503116,12052159756]],[[2799080558,2997408878],[9524829436,9921486076],[6837308558,7035636878]]],[[[571848439,671012599],[3049508078,3247836398],[2533439479,2632603639]],[[2064064238,2262392558],[8004827356,8401483996],[6052322798,6250651118]],[[1506160759,1605324919],[4983209198,5181537518],[3532828279,3631992439]]]]

private theorem identity_0430 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(366853001 / 1388298240 : ℝ)) =
      tensor4 coefficients_0430 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0430, p_variance] <;> ring

private theorem negative_0430 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0430 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0430] at hp
  linarith only [hp]

private theorem node_0432 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0433 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0430 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0428 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 32 : ℝ)
  · exact node_0429 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0432 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0431 : List (List (List (List ℕ))) :=
  [[[[18245381,63605962,43423781],[6915101,40945402,32093501]],[[29575661,86266522,54754061],[18245381,63605962,43423781]]],[[[33329160,120888720,83685960],[10378080,74986560,60734880]],[[56280240,166790880,106637040],[33329160,120888720,83685960]]],[[[14994000,57103200,40172400],[3373200,33861600,28551600]],[[26614800,80344800,51793200],[14994000,57103200,40172400]]]]

private theorem identity_0431 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(937 / 34432 : ℝ)) =
      tensor4 coefficients_0431 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0431, p_coupled] <;> ring

private theorem negative_0431 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0431 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0431] at hp
  linarith only [hp]

private theorem node_0427 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0428 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0431 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0410 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0411 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0427 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0432 : List (List (List (List ℕ))) :=
  [[[[14759141,91495882,68989541],[3428861,68835322,57659261]],[[26089421,114156442,80319821],[14759141,91495882,68989541]]],[[[26937720,177830640,135398520],[3986640,131928480,112447440]],[[49888800,223732800,158349600],[26937720,177830640,135398520]]],[[[12088800,86155200,66319200],[468000,62913600,54698400]],[[23709600,109396800,77940000],[12088800,86155200,66319200]]]]

private theorem identity_0432 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(65 / 17216 : ℝ)) =
      tensor4 coefficients_0432 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0432, p_coupled] <;> ring

private theorem negative_0432 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0432 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0432] at hp
  linarith only [hp]

private def coefficients_0433 : List (List (List (List ℕ))) :=
  [[[[181162481,230744561],[847493362,946657522],[680275841,729857921]],[[828900082,928064242],[2660675204,2859003524],[1859665042,1958829202]],[[661682561,711264641],[1841071762,1940235922],[1193334161,1242916241]]],[[[467561438,566725598],[1913013196,2111341516],[1473341678,1572505838]],[[1875826636,2074154956],[5772510392,6169167032],[3952463596,4150791916]],[[1436155118,1535319278],[3915277036,4113605356],[2507011838,2606175998]]],[[[287090959,336673039],[1066903838,1166067998],[793757839,843339919]],[[1048310558,1147474718],[3114603196,3312931516],[2094182558,2193346718]],[[775164559,824746639],[2075589278,2174753438],[1314369679,1363951759]]]]

private theorem identity_0433 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(181162481 / 347074560 : ℝ)) =
      tensor4 coefficients_0433 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0433, p_variance] <;> ring

private theorem negative_0433 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0433 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0433] at hp
  linarith only [hp]

private theorem node_0438 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0432 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0433 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0409 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0410 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0438 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0384 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 16 : ℝ)
  · exact node_0385 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0409 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0434 : List (List (List (List ℕ))) :=
  [[[[11236541,34093882,20920541],[5716661,23054122,15400661]],[[16756421,45133642,26440421],[11236541,34093882,20920541]]],[[[21127320,65496240,40495320],[9797040,42835680,29165040]],[[32457600,88156800,51825600],[21127320,65496240,40495320]]],[[[9801000,31222800,19485000],[3990600,19602000,13674600]],[[15611400,42843600,25295400],[9801000,31222800,19485000]]]]

private theorem identity_0434 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(2217 / 17216 : ℝ)) =
      tensor4 coefficients_0434 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0434, p_coupled] <;> ring

private theorem negative_0434 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0434 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0434] at hp
  linarith only [hp]

private theorem node_0383 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0384 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0434 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0435 : List (List (List (List ℕ))) :=
  [[[[33965681,58756721],[304414642,353996722],[284393921,309184961]],[[299766322,349348402],[1105037444,1204201604],[833161042,882743122]],[[279745601,304536641],[828512722,878094802],[562712081,587503121]]],[[[119857598,169439678],[720235276,819399436],[628267598,677849678]],[[710938636,810102796],[2447993912,2646322232],[1792835116,1891999276]],[[618970958,668553038],[1783538476,1882702636],[1192457438,1242039518]]],[[[86583919,111374959],[417204638,466786718],[344565679,369356719]],[[412556318,462138398],[1345724476,1444888636],[961058078,1010640158]],[[339917359,364708399],[956409758,1005991838],[630437359,655228399]]]]

private theorem identity_0435 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(33965681 / 86768640 : ℝ)) =
      tensor4 coefficients_0435 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0435, p_variance] <;> ring

private theorem negative_0435 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0435 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0435] at hp
  linarith only [hp]

private theorem node_0382 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0383 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0435 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0436 : List (List (List (List ℕ))) :=
  [[[[29317361,54108401],[540897922,590480002],[567360401,592151441]],[[285821362,335403442],[1601245604,1700409764],[1426983922,1476566002]],[[270448961,295240001],[1088237602,1137819682],[873568481,898359521]]],[[[110560958,160143038],[1200755356,1299919516],[1201754078,1251336158]],[[683048716,782212876],[3455517272,3653845592],[2995587916,3094752076]],[[600377678,649959758],[2310541756,2409705916],[1821723758,1871305838]]],[[[81935599,106726639],[661241438,710823518],[635085679,659876719]],[[398611358,448193438],[1857039676,1956203836],[1569987998,1619570078]],[[330620719,355411759],[1223688158,1273270238],[948847279,973638319]]]]

private theorem identity_0436 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(29317361 / 86768640 : ℝ)) =
      tensor4 coefficients_0436 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0436, p_variance] <;> ring

private theorem negative_0436 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0436 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0436] at hp
  linarith only [hp]

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 4 : ℝ)
  · exact node_0382 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0436 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0437 : List (List (List (List ℕ))) :=
  [[[[5059931,13993462,6996731],[2445251,8764102,4382051]],[[7674611,19222822,9611411],[5059931,13993462,6996731]]],[[[9536760,26820720,13410360],[4016880,15780960,7890480]],[[15056640,37860480,18930240],[9536760,26820720,13410360]]],[[[4387050,12647700,6323850],[1481850,6837300,3418650]],[[7292250,18458100,9229050],[4387050,12647700,6323850]]]]

private theorem identity_0437 (x0 x1 x2 x3 : ℝ) :
    (7747200 : ℝ)*(-p_coupled x0 x1 x2 x3-(3293 / 17216 : ℝ)) =
      tensor4 coefficients_0437 ((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0437, p_coupled] <;> ring

private theorem negative_0437 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0437 ((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0437] at hp
  linarith only [hp]

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.coupled) (negative_0437 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0438 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[27],[51]]],[[[9],[33]],[[33],[57]]]]

private theorem identity_0438 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0438 ((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1)) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0438, p_mass] <;> ring

private theorem negative_0438 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0438 ((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0438] at hp
  linarith only [hp]

theorem exclude_02 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.mass) (negative_0438 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0439 : List (List (List (List ℕ))) :=
  [[[[155413129,93435529],[132171529,70193929]],[[299205458,175250258],[252722258,128767058]],[[108929929,46952329],[85688329,23710729]]],[[[300803138,176847938],[253157858,129202658]],[[577783636,329873236],[482493076,234582676]],[[207255698,83300498],[159610418,35655218]]],[[[145065191,83087591],[120661511,58683911]],[[277928542,153973342],[229121182,105165982]],[[98000951,36023351],[73597271,11619671]]]]

private theorem identity_0439 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(11619671 / 61977600 : ℝ)) =
      tensor4 coefficients_0439 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0439, p_headsq] <;> ring

private theorem negative_0439 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0439 ((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0439] at hp
  linarith only [hp]

theorem exclude_03 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 2 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.headsq) (negative_0439 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part10
