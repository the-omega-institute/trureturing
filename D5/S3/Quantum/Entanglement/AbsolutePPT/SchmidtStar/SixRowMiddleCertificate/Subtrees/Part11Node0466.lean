/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part11Node0466
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part11Node0466
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part11.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part11Node0466.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part11Node0466
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0459 : List (List (List (List ℕ))) :=
  [[[[2442999333067,1240354993867],[1980732915187,778088575987]],[[5116817096654,2711528418254],[4192284260894,1786995582494]],[[1997330322787,794685983587],[1535063904907,332419565707]]],[[[9742856073584,4968907478384],[7896594791624,3122646196424]],[[20269601055208,10721703864808],[16577078491288,7029181300888]],[[7841398896824,3067450301624],[5995137614864,1221189019664]]],[[[14562194611304,7455935961704],[11797245465464,4690986815864]],[[30092813819968,15880296520768],[24562915528288,10350398229088]],[[11533348718264,4427090068664],[8768399572424,1662140922824]]],[[[9667771813280,4966522942880],[7827589081280,3126340210880]],[[19844005920160,10441508179360],[16163640456160,6761142715360]],[[7531781617280,2830532746880],[5691598885280,990350014880]]],[[[2405432238712,1239137761912],[1946203788472,779909311672]],[[4903972651184,2571383697584],[3985515750704,1652926797104]],[[1842499769272,676205292472],[1383271319032,216976842232]]]]

private theorem identity_0459 (x0 x1 x2 x3 : ℝ) :
    (3173253120000 : ℝ)*(-p_headbox x0 x1 x2 x3-(27122105279 / 396656640000 : ℝ)) =
      tensor4 coefficients_0459 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0459, p_headbox] <;> ring

private theorem negative_0459 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0459 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0459] at hp
  linarith only [hp]

private def coefficients_0460 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0460 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0460 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0460, p_qmass] <;> ring

private theorem negative_0460 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0460 ((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0460] at hp
  linarith only [hp]

private theorem node_0467 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0459 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0460 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0461 : List (List (List (List ℕ))) :=
  [[[[69804894424309,31320275569909],[55012369052149,16527750197749]],[[146995978625258,70026740916458],[117410927880938,40441690172138]],[[55543486095349,17058867240949],[40750960723189,2266341868789]]],[[[278798187791252,125445772559252],[219672956535572,66320541303572]],[[584910977664424,278206147200424],[466660515153064,159955684689064]],[[219852056305172,66499641073172],[160726825049492,7374409817492]]],[[[417500065481614,188348301718414],[328881413489614,99729649726414]],[[872640146200028,414336618673628],[695402842216028,237099314689628]],[[326242213601614,97090449838414],[237623561609614,8471797846414]]],[[[277824948744612,125640191496612],[218793226580292,66608469332292]],[[578530905227304,274161390731304],[460467460898664,156097946402664]],[[215102030530692,62917273282692],[156070308366372,3885551118372]]],[[[69318173222379,31417383359979],[54572397166539,16671607304139]],[[143805751251318,68004171526518],[114314199139638,38512619414838]],[[53168383731339,15267593868939],[38422607675499,521817813099]]]]

private theorem identity_0461 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(57979757011 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0461 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0461, p_headbox] <;> ring

private theorem negative_0461 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0461 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0461] at hp
  linarith only [hp]

private def coefficients_0462 : List (List (List (List ℕ))) :=
  [[[[450756311,326801111],[402529991,278574791]],[[668225062,420314662],[571772422,323862022]],[[200037551,76082351],[151811231,27856031]]],[[[878167768,630257368],[781134088,533223688]],[[1289469896,793649096],[1095402536,599581736]],[[376439728,128529328],[279406048,31495648]]],[[[427249048,303293848],[378441688,254486488]],[[620920016,373009616],[523305296,275394896]],[[176239768,52284568],[127432408,3477208]]]]

private theorem identity_0462 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(434651 / 61977600 : ℝ)) =
      tensor4 coefficients_0462 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0462, p_headsq] <;> ring

private theorem negative_0462 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0462 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0462] at hp
  linarith only [hp]

private def coefficients_0463 : List (List (List (List ℕ))) :=
  [[[[31912731757427,12962336826227],[28226287743467,9275892812267]],[[59788016142094,21887226279694],[52415128114174,14514338251774]],[[25210385097467,6259990166267],[21523941083507,2573546152307]]],[[[126864845569400,51354064743800],[112131223998800,36620443173200]],[[237110841710200,86089280059000],[207643598569000,56622036917800]],[[99627292587200,24116511761600],[84893671016600,9382890191000]]],[[[189088473789344,76257385302944],[167006737702784,54175649216384]],[[352548124983328,126885948010528],[308384652810208,82722475837408]],[[147592779375584,34761690889184],[125511043289024,12679954802624]]],[[[125233238914944,50301824694144],[110524852783104,35593438562304]],[[232915597534848,83052769093248],[203498825271168,53635996829568]],[[97145128495104,22213714274304],[82436742363264,7505328142464]]],[[[31096877233792,12436165604992],[27423049631872,8762338003072]],[[57690294712064,20368871454464],[50342639508224,13021216250624]],[[23969254905472,5308543276672],[20295427303552,1634715674752]]]]

private theorem identity_0463 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(12771216209 / 396656640000 : ℝ)) =
      tensor4 coefficients_0463 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0463, p_headbox] <;> ring

private theorem negative_0463 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0463 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0463] at hp
  linarith only [hp]

private def coefficients_0464 : List (List (List (List ℕ))) :=
  [[[[328075209,427239369],[1594530018,1792858338],[1280399769,1379563929]],[[1575936738,1774265058],[5061170916,5457827556],[3513124098,3711452418]],[[1261806489,1360970649],[3494530818,3692859138],[2246669289,2345833449]]],[[[858436350,1056764670],[3601185420,3997842060],[2770638990,2968967310]],[[3563998860,3960655500],[10961699640,11755012920],[7453480620,7850137260]],[[2733452430,2931780750],[7416294060,7812950700],[4710731550,4909059870]]],[[[531053143,630217303],[2008039406,2206367726],[1490931223,1590095383]],[[1989446126,2187774446],[5903296732,6299953372],[3941740526,4140068846]],[[1472337943,1571502103],[3923147246,4121475566],[2464754263,2563918423]]]]

private theorem identity_0464 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(5207543 / 22036480 : ℝ)) =
      tensor4 coefficients_0464 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0464, p_variance] <;> ring

private theorem negative_0464 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0464 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0464] at hp
  linarith only [hp]

private theorem node_0471 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0463 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0464 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0470 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0462 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0471 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0469 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0461 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0470 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0465 : List (List (List (List ℕ))) :=
  [[[[193502075023,144663726223],[174729834703,125891485903]],[[78242332303,29403983503],[59470091983,10631743183]]],[[[568264024117,422120843317],[511861309237,365718128437]],[[224362717237,78219536437],[167960002357,21816821557]]],[[[556049396289,410278081089],[499562430609,353791115409]],[[214030659009,68259343809],[157543693329,11772378129]]],[[[181288421649,132821938449],[162431930529,113965447329]],[[67911248529,19444765329],[49054757409,588274209]]]]

private theorem identity_0465 (x0 x1 x2 x3 : ℝ) :
    (317325312000 : ℝ)*(-p_headcap x0 x1 x2 x3-(65363801 / 35258368000 : ℝ)) =
      tensor4 coefficients_0465 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0465, p_headcap] <;> ring

private theorem negative_0465 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headcap x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0465 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0465] at hp
  linarith only [hp]

private def coefficients_0466 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0466 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0466 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0466, p_qmass] <;> ring

private theorem negative_0466 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0466 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0466] at hp
  linarith only [hp]

private theorem node_0475 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headcap) (negative_0465 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0466 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0467 : List (List (List (List ℕ))) :=
  [[[[2192833817,1697013017],[2002252697,1506431897]],[[3453679474,2462037874],[3072517234,2080875634]],[[1225983257,730162457],[1035402137,539581337]]],[[[4292425410,3300783810],[3910101090,2918459490]],[[6720293460,4737010260],[5955644820,3972361620]],[[2358143250,1366501650],[1975818930,984177330]]],[[[2099266775,1603445975],[1907523575,1411702775]],[[3265964350,2274322750],[2882477950,1890836350]],[[1131835175,636014375],[940091975,444271175]]]]

private theorem identity_0467 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(17770847 / 158662656 : ℝ)) =
      tensor4 coefficients_0467 ((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0467, p_headsq] <;> ring

private theorem negative_0467 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (37 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0467 ((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0467] at hp
  linarith only [hp]

private def coefficients_0468 : List (List (List (List ℕ))) :=
  [[[[101090488,200254648],[2031294896,2229623216],[1958094328,2057258488]],[[1100468816,1298797136],[5891703712,6288360352],[4847014736,5045343056]],[[1006350808,1105514968],[3874353776,4072682096],[2895892888,2995057048]]],[[[399306144,597634464],[4464393648,4861050288],[4120867344,4319195664]],[[2598964728,2995621368],[12594568656,13387881936],[10107163608,10503820248]],[[2213603544,2411931864],[8158064928,8554721568],[6000241224,6198569544]]],[[[298561657,397725817],[2433790754,2632119074],[2163119017,2262283177]],[[1499187914,1697516234],[6704248948,7100905588],[5260840874,5459169194]],[[1207598737,1306762897],[4284403154,4482731474],[3104694337,3203858497]]]]

private theorem identity_0468 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(12636311 / 347074560 : ℝ)) =
      tensor4 coefficients_0468 ((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0468, p_variance] <;> ring

private theorem negative_0468 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (37 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0468 ((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0468] at hp
  linarith only [hp]

private theorem node_0478 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (37 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0467 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0468 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0469 : List (List (List (List ℕ))) :=
  [[[[1073623337,825712937],[977751737,729841337]],[[1680962074,1185141274],[1489218874,993398074]],[[589907537,341997137],[494035937,246125537]]],[[[2100300744,1604479944],[1907976504,1412155704]],[[3267741768,2276100168],[2883093288,1891451688]],[[1132578624,636757824],[940254384,444433584]]],[[[1026514998,778604598],[930062358,682151958]],[[1586454876,1090634076],[1393549596,897728796]],[[542508678,294598278],[446056038,198145638]]]]

private theorem identity_0469 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(11008091 / 110182400 : ℝ)) =
      tensor4 coefficients_0469 ((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0469, p_headsq] <;> ring

private theorem negative_0469 (x0 x1 x2 x3 : ℝ)
    (h0l : (37 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0469 ((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0469] at hp
  linarith only [hp]

private def coefficients_0470 : List (List (List (List ℕ))) :=
  [[[[399652145,597980465],[4472639170,4869295810],[4128766865,4327095185]],[[2603433490,3000090130],[12618613220,13411926500],[10126739410,10523396050]],[[2217726305,2416054625],[8173863970,8570520610],[6011917505,6210245825]]],[[[1194938630,1591595270],[9751654060,10544967340],[8668275110,9064931750]],[[6005689180,6799002460],[26865084920,28451711480],[21082515100,21875828380]],[[4838640470,5235297110],[17169210700,17962523980],[12442129910,12838786550]]],[[[795978487,994306807],[5280398894,5677055534],[4540200247,4738528567]],[[3403639694,3800296334],[14249239708,15042552988],[10957159694,11353816334]],[[2621606167,2819934487],[8996730734,9393387374],[6430904407,6629232727]]]]

private theorem identity_0470 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(79930429 / 1110638592 : ℝ)) =
      tensor4 coefficients_0470 ((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0470, p_variance] <;> ring

private theorem negative_0470 (x0 x1 x2 x3 : ℝ)
    (h0l : (37 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0470 ((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(37 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0470] at hp
  linarith only [hp]

private theorem node_0479 (x0 x1 x2 x3 : ℝ)
    (h0l : (37 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0469 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0470 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0477 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (37 / 64 : ℝ)
  · exact node_0478 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0479 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0471 : List (List (List (List ℕ))) :=
  [[[[72686659,246086918,169526659],[25041379,150796358,121881379]],[[120331939,341377478,217171939],[72686659,246086918,169526659]]],[[[129547326,460521852,323227326],[33675726,268778652,227355726]],[[225418926,652265052,419098926],[129547326,460521852,323227326]]],[[[56681109,214075818,153521109],[8454789,117623178,105294789]],[[104907429,310528458,201747429],[56681109,214075818,153521109]]]]

private theorem identity_0471 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(939421 / 110182400 : ℝ)) =
      tensor4 coefficients_0471 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0471, p_coupled] <;> ring

private theorem negative_0471 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0471 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0471] at hp
  linarith only [hp]

private theorem node_0476 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact node_0477 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0471 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0474 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0475 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0476 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0472 : List (List (List (List ℕ))) :=
  [[[[67457299,351836198,268884499],[19812019,256545638,221239219]],[[115102579,447126758,316529779],[67457299,351836198,268884499]]],[[[120250686,674344572,523105086],[24379086,482601372,427233486]],[[216122286,866087772,618976686],[120250686,674344572,523105086]]],[[[52613829,322149258,254041029],[4387509,225696618,205814709]],[[100840149,418601898,302267349],[52613829,322149258,254041029]]]]

private theorem identity_0472 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(487501 / 110182400 : ℝ)) =
      tensor4 coefficients_0472 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0472, p_coupled] <;> ring

private theorem negative_0472 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0472 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0472] at hp
  linarith only [hp]

private def coefficients_0473 : List (List (List (List ℕ))) :=
  [[[[138430162,188012242],[742273364,841437524],[610815682,660397762]],[[732976724,832140884],[2413048648,2611376968],[1694016884,1793181044]],[[601519042,651101122],[1684720244,1783884404],[1090173682,1139755762]]],[[[377311288,476475448],[1689225416,1887553736],[1325859088,1425023248]],[[1670632136,1868960456],[5243008192,5639664832],[3600265976,3798594296]],[[1307265808,1406429968],[3581672696,3780001016],[2288351848,2387516008]]],[[[239227127,288809207],[947644054,1046808214],[715389407,764971487]],[[938347414,1037511574],[2831343548,3029671868],[1906941094,2006105254]],[[706092767,755674847],[1897644454,1996808614],[1198524167,1248106247]]]]

private theorem identity_0473 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(69215081 / 347074560 : ℝ)) =
      tensor4 coefficients_0473 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0473, p_variance] <;> ring

private theorem negative_0473 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0473 ((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0473] at hp
  linarith only [hp]

private theorem node_0480 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0472 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0473 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0473 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (19 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0474 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0480 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0474 : List (List (List (List ℕ))) :=
  [[[[15436251654827,5961054189227],[11749807640867,2274610175267]],[[32164854511294,13214459580094],[24791966483374,5841571552174]],[[14063703569267,4588506103667],[10377259555307,902062089707]]],[[[61759677590960,24004287178160],[47026056020360,9270665607560]],[[128137912860520,52627132034920],[98670669719320,23159888893720]],[[55759531715960,18004141303160],[41025910145360,3270519732560]]],[[[92627536538144,36211992294944],[70545800451584,14130256208384]],[[191359994117728,78528905631328],[147196521944608,34365433458208]],[[82865585761184,26450041517984],[60783849674624,4368305431424]]],[[[61720941836544,24255234726144],[47012555704704,9546848594304]],[[126965463627648,52034049406848],[97548691363968,22617277143168]],[[54707291666304,17241584555904],[39998905534464,2533198424064]]],[[[15416829530752,6086473716352],[11743001928832,2412646114432]],[[31578524451584,12917812822784],[24230869247744,5570157618944]],[[13537532348032,4207176533632],[9863704746112,533348931712]]]]

private theorem identity_0474 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(4166788529 / 396656640000 : ℝ)) =
      tensor4 coefficients_0474 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0474, p_headbox] <;> ring

private theorem negative_0474 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0474 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0474] at hp
  linarith only [hp]

private def coefficients_0475 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0475 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0475 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0475, p_qmass] <;> ring

private theorem negative_0475 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0475 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0475] at hp
  linarith only [hp]

private theorem node_0483 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0474 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0475 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0476 : List (List (List (List ℕ))) :=
  [[[[2101334713,1605513913],[1908429433,1412608633]],[[3269519186,2277877586],[2883708626,1892067026]],[[1133322073,637501273],[940416793,444595993]]],[[[4108127930,3116486330],[3721155290,2729513690]],[[6349374340,4366091140],[5575429060,3592145860]],[[2171521610,1179880010],[1784548970,792907370]]],[[[2006468399,1510647599],[1812401039,1316580239]],[[3079205518,2087563918],[2691070798,1699429198]],[[1037874719,542053919],[843807359,347986559]]]]

private theorem identity_0476 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(347986559 / 3966566400 : ℝ)) =
      tensor4 coefficients_0476 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0476, p_headsq] <;> ring

private theorem negative_0476 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (39 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0476 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0476] at hp
  linarith only [hp]

private def coefficients_0477 : List (List (List (List ℕ))) :=
  [[[[298907658,398071818],[2442036276,2640364596],[2171018538,2270182698]],[[1503656676,1701984996],[6728293512,7124950152],[5280416676,5478744996]],[[1211721498,1310885658],[4300202196,4498530516],[3116370618,3215534778]]],[[[796324488,994652808],[5288644416,5685301056],[4548099768,4746428088]],[[3408108456,3804765096],[14273284272,15066597552],[10976735496,11373392136]],[[2625728928,2824057248],[9012529776,9409186416],[6442580688,6640909008]]],[[[497762831,596926991],[2847300142,3045628462],[2377427231,2476591391]],[[1905143782,2103472102],[7546374764,7943031404],[5697010822,5895339142]],[[1414353431,1513517591],[4713019582,4911347902],[3326556071,3425720231]]]]

private theorem identity_0477 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(2372283 / 22036480 : ℝ)) =
      tensor4 coefficients_0477 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0477, p_variance] <;> ring

private theorem negative_0477 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (39 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0477 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0477] at hp
  linarith only [hp]

private theorem node_0486 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (39 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0476 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0477 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0478 : List (List (List (List ℕ))) :=
  [[[[1027548967,779638567],[930515287,682604887]],[[1588232294,1092411494],[1394164934,898344134]],[[543252127,295341727],[446218447,198308047]]],[[[2007502368,1511681568],[1812853968,1317033168]],[[3080982936,2089341336],[2691686136,1700044536]],[[1038618168,542797368],[843969768,348148968]]],[[[979790992,731880592],[882176272,634265872]],[[1492425824,996605024],[1297196384,801375584]],[[495203632,247293232],[397588912,149678512]]]]

private theorem identity_0478 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(9354907 / 123955200 : ℝ)) =
      tensor4 coefficients_0478 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0478, p_headsq] <;> ring

private theorem negative_0478 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0478 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0478] at hp
  linarith only [hp]

private def coefficients_0479 : List (List (List (List ℕ))) :=
  [[[[796670489,994998809],[5296889938,5693546578],[4555999289,4754327609]],[[3412577218,3809233858],[14297328836,15090642116],[10996311298,11392967938]],[[2629851689,2828180009],[9028328818,9424985458],[6454256969,6652585289]]],[[[1991743326,2388399966],[11405691612,12199004892],[9525507966,9922164606]],[[7629512652,8422825932],[30233588184,31820214744],[22827194892,23620508172]],[[5665659246,6062315886],[18883676412,19676989692],[13329576846,13726233486]]],[[[1195764839,1394093159],[6110185678,6506842318],[4970200679,5168528999]],[[4218319438,4614976078],[15939027356,16732340636],[11832267598,12228924238]],[[3036499559,3234827879],[9856731598,10253388238],[6876011879,7074340199]]]]

private theorem identity_0479 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(796670489 / 5553192960 : ℝ)) =
      tensor4 coefficients_0479 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0479, p_variance] <;> ring

private theorem negative_0479 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0479 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0479] at hp
  linarith only [hp]

private theorem node_0487 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0478 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0479 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0485 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (39 / 64 : ℝ)
  · exact node_0486 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0487 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0480 : List (List (List (List ℕ))) :=
  [[[[243580363,890015126,630940363],[50675083,504204566,438035083]],[[436485643,1275825686,823845643],[243580363,890015126,630940363]]],[[[454790510,1715289820,1229510510],[67817870,941344540,842537870]],[[841763150,2489235100,1616483150],[454790510,1715289820,1229510510]]],[[[211030589,824915578,598390589],[16963229,436780858,404323229]],[[405097949,1213050298,792457949],[211030589,824915578,598390589]]]]

private theorem identity_0480 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(16963229 / 3966566400 : ℝ)) =
      tensor4 coefficients_0480 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0480, p_coupled] <;> ring

private theorem negative_0480 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (39 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0480 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0480] at hp
  linarith only [hp]

private def coefficients_0481 : List (List (List (List ℕ))) :=
  [[[[903593767,655683367],[806560087,558649687]],[[1340321894,844501094],[1146254534,650433734]],[[419296927,171386527],[322263247,74352847]]],[[[1759591968,1263771168],[1564943568,1069122768]],[[2585162136,1593520536],[2195865336,1204223736]],[[790707768,294886968],[596059368,100238568]]],[[[855835792,607925392],[758221072,510310672]],[[1244515424,748694624],[1049285984,553465184]],[[371248432,123338032],[273633712,25723312]]]]

private theorem identity_0481 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(1607707 / 123955200 : ℝ)) =
      tensor4 coefficients_0481 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0481, p_headsq] <;> ring

private theorem negative_0481 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0481 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0481] at hp
  linarith only [hp]

private def coefficients_0482 : List (List (List (List ℕ))) :=
  [[[[138146197,477719594,331826197],[41112517,283652234,234792517]],[[186663037,574753274,380343037],[89629357,380685914,283309357]]],[[[260218248,923290896,647578248],[65569848,533994096,452929848]],[[357542448,1117939296,744902448],[162894048,728642496,550254048]]],[[[121982272,445391744,315662272],[24367552,250162304,218047552]],[[170789632,543006464,364469632],[73174912,347777024,266854912]]]]

private theorem identity_0482 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(380743 / 30988800 : ℝ)) =
      tensor4 coefficients_0482 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0482, p_coupled] <;> ring

private theorem negative_0482 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0482 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0482] at hp
  linarith only [hp]

private theorem node_0489 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0481 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0482 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0488 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (39 / 64 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0480 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0489 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0484 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact node_0485 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0488 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0482 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0483 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0484 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0483 : List (List (List (List ℕ))) :=
  [[[[226149163,886141526,644497963],[33243883,500330966,451592683]],[[419054443,1271952086,837403243],[226149163,886141526,644497963]]],[[[422252270,1712190940,1258949870],[35279630,938245660,871977230]],[[809224910,2486136220,1645922510],[422252270,1712190940,1258949870]]],[[[195923549,825690298,614272349],[1856189,437555578,420204989]],[[389990909,1213825018,808339709],[195923549,825690298,614272349]]]]

private theorem identity_0483 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(1856189 / 3966566400 : ℝ)) =
      tensor4 coefficients_0483 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0483, p_coupled] <;> ring

private theorem negative_0483 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (39 / 64 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0483 ((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0483] at hp
  linarith only [hp]

private def coefficients_0484 : List (List (List (List ℕ))) :=
  [[[[193,449],[242,754],[31,287]]]]

private theorem identity_0484 (x0 x1 x2 x3 : ℝ) :
    (2048 : ℝ)*(-p_qmass x0 x1 x2 x3-(31 / 2048 : ℝ)) =
      tensor4 coefficients_0484 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0484, p_qmass] <;> ring

private theorem negative_0484 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (15 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 32 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0484 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0484] at hp
  linarith only [hp]

private def coefficients_0485 : List (List (List (List ℕ))) :=
  [[[[778077209,976405529],[3412577218,3809233858],[2648444969,2846773289]],[[3370742338,3767398978],[10486868516,11280181796],[7144016098,7540672738]],[[2606610089,2804938409],[7102181218,7498837858],[4509516089,4707844409]]],[[[1954556766,2351213406],[7629512652,8422825932],[5702845806,6099502446]],[[7545842892,8339156172],[22597560504,24184187064],[15107497452,15900810732]],[[5619176046,6015832686],[15023827692,15817140972],[9432541566,9829198206]]],[[[1177171559,1375499879],[4218319438,4614976078],[3055092839,3253421159]],[[4176484558,4573141198],[12113459996,12906773276],[7964865358,8361521998]],[[3013257959,3211586279],[7923030478,8319687118],[4923717479,5122045799]]]]

private theorem identity_0485 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(111153887 / 793313280 : ℝ)) =
      tensor4 coefficients_0485 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0485, p_variance] <;> ring

private theorem negative_0485 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (15 / 32 : ℝ))
    (h2l : (5 / 32 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0485 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0485] at hp
  linarith only [hp]

private theorem node_0494 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (15 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 32 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0484 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0485 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0486 : List (List (List (List ℕ))) :=
  [[[[130011637,476944874,339186037],[32977957,282877514,242152357]],[[178528477,573978554,387702877],[81494797,379911194,290669197]]],[[[245111208,924065616,663460008],[50462808,534768816,468811608]],[[342435408,1118714016,760784208],[147787008,729417216,566135808]]],[[[115009792,446941184,324184192],[17395072,251711744,226569472]],[[163817152,544555904,372991552],[66202432,349326464,275376832]]]]

private theorem identity_0486 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(135899 / 15494400 : ℝ)) =
      tensor4 coefficients_0486 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0486, p_coupled] <;> ring

private theorem negative_0486 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (15 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0486 ((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(39 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0486] at hp
  linarith only [hp]

private theorem node_0493 (x0 x1 x2 x3 : ℝ)
    (h0l : (39 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (15 / 32 : ℝ)
  · exact node_0494 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0486 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0492 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (39 / 64 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0483 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0493 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0487 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0487 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0487 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0487, p_qmass] <;> ring

private theorem negative_0487 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0487 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0487] at hp
  linarith only [hp]

private theorem node_0491 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact node_0492 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0487 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0488 : List (List (List (List ℕ))) :=
  [[[[377657289,476821449],[1693694178,1892022498],[1329981849,1429146009]],[[1675100898,1873429218],[5259499236,5656155876],[3612288258,3810616578]],[[1311388569,1410552729],[3593694978,3792023298],[2296251369,2395415529]]],[[[957600510,1155928830],[3799513740,4196170380],[2869803150,3068131470]],[[3762327180,4158983820],[11358356280,12151669560],[7651808940,8048465580]],[[2832616590,3030944910],[7614622380,8011279020],[4809895710,5008224030]]],[[[580635223,679799383],[2107203566,2305531886],[1540513303,1639677463]],[[2088610286,2286938606],[6101625052,6498281692],[4040904686,4239233006]],[[1521920023,1621084183],[4022311406,4220639726],[2514336343,2613500503]]]]

private theorem identity_0488 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(41961921 / 154255360 : ℝ)) =
      tensor4 coefficients_0488 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0488, p_variance] <;> ring

private theorem negative_0488 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0488 ((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0488] at hp
  linarith only [hp]

private theorem node_0490 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0491 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0488 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0481 (x0 x1 x2 x3 : ℝ)
    (h0l : (19 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0482 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0490 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0472 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (19 / 32 : ℝ)
  · exact node_0473 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0481 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0468 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0469 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0472 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0467 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0468 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part11Node0466
