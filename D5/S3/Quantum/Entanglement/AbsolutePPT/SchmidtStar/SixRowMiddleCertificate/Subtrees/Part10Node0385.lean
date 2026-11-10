/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part10Node0385
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part10Node0385
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part10.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part10Node0385.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part10Node0385
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

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0386 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0408 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part10Node0385
