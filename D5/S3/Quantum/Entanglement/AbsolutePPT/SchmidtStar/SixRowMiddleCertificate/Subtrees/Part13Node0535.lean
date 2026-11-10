/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part13Node0535
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part13Node0535
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part13.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part13Node0535.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part13Node0535
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0529 : List (List (List (List ℕ))) :=
  [[[[203524151,141546551],[178539431,116561831]],[[324831142,200875942],[274861702,150906502]],[[103875791,41898191],[78891071,16913471]]],[[[395469688,271514488],[344919208,220964008]],[[626214536,378304136],[525113576,277203176]],[[195882448,71927248],[145331968,21376768]]],[[[191783128,129805528],[166217368,104239768]],[[301058576,177103376],[249927056,125971856]],[[91844248,29866648],[66278488,4300888]]]]

private theorem identity_0529 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(537611 / 15494400 : ℝ)) =
      tensor4 coefficients_0529 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0529, p_headsq] <;> ring

private theorem negative_0529 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0529 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0529] at hp
  linarith only [hp]

private def coefficients_0530 : List (List (List (List ℕ))) :=
  [[[[2487558756227,1357056343427],[2031824971067,901322558267]],[[4933888947694,2672884122094],[4022421377374,1761416551774]],[[1810422584267,679920171467],[1354688799107,224186386307]]],[[[9886970550920,5400474064520],[8067753194720,3581256708320]],[[19476389065240,10503396092440],[15837954352840,6864961380040]],[[7065764240720,2579267754320],[5246546884520,760050398120]]],[[[14726861488544,8050107606944],[12003832635584,5327078753984]],[[28810143317728,15456635554528],[23364085611808,10010577848608]],[[10327607770784,3650853889184],[7604578917824,927825036224]]],[[[9742986198144,5326958242944],[7931642805504,3515614850304]],[[18926561029248,10094505118848],[15303874243968,6471818333568]],[[6699559106304,2283531151104],[4888215713664,472187758464]]],[[[2415534800512,1320266653312],[1963736689792,868468542592]],[[4658914421504,2468378127104],[3755318200064,1564781905664]],[[1627291288192,532023140992],[1175493177472,80225030272]]]]

private theorem identity_0530 (x0 x1 x2 x3 : ℝ) :
    (3173253120000 : ℝ)*(-p_headbox x0 x1 x2 x3-(626758049 / 24791040000 : ℝ)) =
      tensor4 coefficients_0530 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0530, p_headbox] <;> ring

private theorem negative_0530 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0530 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0530] at hp
  linarith only [hp]

private def coefficients_0531 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0531 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0531 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0531, p_qmass] <;> ring

private theorem negative_0531 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0531 ((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0531] at hp
  linarith only [hp]

private theorem node_0537 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0530 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0531 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0532 : List (List (List (List ℕ))) :=
  [[[[62730178045549,26554100835949],[48146696920429,11970619710829]],[[124800699054938,52448544635738],[95633736804698,23281582385498]],[[56983260151789,20807182942189],[42399779026669,6223701817069]]],[[[249967965149428,105831866947828],[191693525199988,47557426998388]],[[496236199933736,207964003530536],[379687320034856,91415123631656]],[[225999095974708,81862997773108],[167724656025268,23588557823668]]],[[[373455010197598,158100947656798],[286134341137438,70780278596638]],[[739775591764316,309067466682716],[565134253643996,134426128562396]],[[336036416521918,120682353981118],[248715747461758,33361684920958]]],[[[247926586066020,104922446750820],[189774632834820,46770493519620]],[[490044890022840,204036611392440],[373740983560440,87732704930040]],[[222008346865620,79004207550420],[163856393634420,20852254319220]]],[[[61709359564739,26099261798339],[47187116569379,11577018802979]],[[121704792322198,50484596789398],[92660306331478,21440110798678]],[[54987762759059,19377664992659],[40465519763699,4855421997299]]]]

private theorem identity_0532 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(4855421997299 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0532 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0532, p_headbox] <;> ring

private theorem negative_0532 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0532 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0532] at hp
  linarith only [hp]

private def coefficients_0533 : List (List (List (List ℕ))) :=
  [[[[80535258,130117338],[1094220756,1193384916],[1041575418,1091157498]],[[616024836,715188996],[3130888392,3329216712],[2570643396,2669807556]],[[542462058,592044138],[2050612596,2149776756],[1536040458,1585622538]]],[[[260512728,359676888],[2394879456,2593207776],[2190146568,2289310728]],[[1434710856,1633039176],[6682206192,7078862832],[5359055016,5557383336]],[[1188143088,1287307248],[4315216656,4513544976],[3182853408,3282017568]]],[[[180323471,229905551],[1301350702,1400514862],[1148917151,1198499231]],[[819378022,918542182],[3552701804,3751030124],[2789103622,2888267782]],[[646027031,695609111],[2265296062,2364460222],[1647158951,1696741031]]]]

private theorem identity_0533 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(4474181 / 38563840 : ℝ)) =
      tensor4 coefficients_0533 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0533, p_variance] <;> ring

private theorem negative_0533 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0533 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0533] at hp
  linarith only [hp]

private theorem node_0540 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0532 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0533 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0534 : List (List (List (List ℕ))) :=
  [[[[31228024467547,13422975584347],[23966902969867,6161854086667]],[[61599085531454,25988987765054],[47076842536094,11466744769694]],[[27867226064707,10062177181507],[20606104567027,2801055683827]]],[[[124367523966656,53429202558656],[95354528600816,24416207192816]],[[244783481758792,102906838942792],[186757491027112,44880848211112]],[[110440256344136,39501934936136],[81427260978296,10488939570296]]],[[[185700129788672,79714343267072],[142228739007872,36242952486272]],[[364690769902144,152719196858944],[277747988340544,65776415297344]],[[164086388883872,58100602362272],[120614998103072,14629211581472]]],[[[123209653200896,52832848848896],[94261366516736,23884562164736]],[[241427178061312,100673569357312],[183530604692992,42776995988992]],[[108320786748416,37943982396416],[79372500064256,8995695712256]]],[[[30649021207552,13124730852352],[23420251436032,5895961080832]],[[59920800978944,24872220268544],[45463261435904,10414680725504]],[[26807426440192,9283136084992],[19578656668672,2054366313472]]]]

private theorem identity_0534 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(2006217103 / 49582080000 : ℝ)) =
      tensor4 coefficients_0534 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0534, p_headbox] <;> ring

private theorem negative_0534 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0534 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0534] at hp
  linarith only [hp]

private def coefficients_0535 : List (List (List (List ℕ))) :=
  [[[[260858729,360022889],[2403124978,2601453298],[2198046089,2297210249]],[[1439179618,1637507938],[6706250756,7102907396],[5378630818,5576959138]],[[1192265849,1291430009],[4331015698,4529344018],[3194529689,3293693849]]],[[[721985886,920314206],[5221893852,5618550492],[4611467646,4809795966]],[[3286449612,3683106252],[14258896344,15052209624],[11195566092,11592222732]],[[2592353646,2790681966],[9092782332,9489438972],[6611988366,6810316686]]],[[[461819159,560983319],[2820152878,3018481198],[2414113559,2513277719]],[[1848653998,2046982318],[7555413596,7952070236],[5818319278,6016647598]],[[1400779799,1499943959],[4763150638,4961478958],[3418150679,3517314839]]]]

private theorem identity_0535 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(260858729 / 1388298240 : ℝ)) =
      tensor4 coefficients_0535 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0535, p_variance] <;> ring

private theorem negative_0535 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0535 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0535] at hp
  linarith only [hp]

private theorem node_0541 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0534 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0535 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0539 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0540 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0541 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0536 : List (List (List (List ℕ))) :=
  [[[[1918399609,1422578809],[1718521849,1222701049]],[[2900162738,1908521138],[2500407218,1508765618]],[[946900729,451079929],[747022969,251202169]]],[[[3739521986,2747880386],[3338604386,2346962786]],[[5605189972,3621906772],[4803354772,2820071572]],[[1795943186,804301586],[1395025586,403383986]]],[[[1820797559,1324976759],[1619757719,1123936919]],[[2704377598,1712735998],[2302297918,1310656318]],[[848717639,352896839],[647677799,151856999]]]]

private theorem identity_0536 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(151856999 / 3966566400 : ℝ)) =
      tensor4 coefficients_0536 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0536, p_headsq] <;> ring

private theorem negative_0536 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0536 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0536] at hp
  linarith only [hp]

private def coefficients_0537 : List (List (List (List ℕ))) :=
  [[[[193,449],[242,754],[31,287]]]]

private theorem identity_0537 (x0 x1 x2 x3 : ℝ) :
    (2048 : ℝ)*(-p_qmass x0 x1 x2 x3-(31 / 2048 : ℝ)) =
      tensor4 coefficients_0537 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0537, p_qmass] <;> ring

private theorem negative_0537 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 32 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0537 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0537] at hp
  linarith only [hp]

private def coefficients_0538 : List (List (List (List ℕ))) :=
  [[[[431763912,530928072],[1794353904,1992682224],[1369562472,1468726632]],[[1775760624,1974088944],[5429442528,5826099168],[3667626864,3865955184]],[[1350969192,1450133352],[3649033584,3847361904],[2305036872,2404201032]]],[[[1062412248,1260740568],[3990253416,4386910056],[2941786128,3140114448]],[[3953066856,4349723496],[11669529792,12462843072],[7744352856,8141009496]],[[2904599568,3102927888],[7707166296,8103822936],[4816511688,5014840008]]],[[[630994337,730158497],[2196591514,2394919834],[1572569657,1671733817]],[[2177998234,2376326554],[6241471268,6638127908],[4077417994,4275746314]],[[1553976377,1653140537],[4058824714,4257153034],[2511820817,2610984977]]]]

private theorem identity_0538 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(5996721 / 38563840 : ℝ)) =
      tensor4 coefficients_0538 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0538, p_variance] <;> ring

private theorem negative_0538 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 32 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0538 ((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x2-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0538] at hp
  linarith only [hp]

private theorem node_0548 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 32 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0537 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0538 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0547 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (45 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0536 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0548 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0539 : List (List (List (List ℕ))) :=
  [[[[935397481,687487081],[834877561,586967161]],[[1402186202,906365402],[1201146362,705325562]],[[449357521,201447121],[348837601,100927201]]],[[[1821831528,1326010728],[1620210648,1124389848]],[[2706155016,1714513416],[2302913256,1311271656]],[[849461088,353640288],[647840208,152019408]]],[[[886271638,638361238],[785170678,537260278]],[[1303643996,807823196],[1101442076,605621276]],[[399941158,152030758],[298840198,50929798]]]]

private theorem identity_0539 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(25464899 / 991641600 : ℝ)) =
      tensor4 coefficients_0539 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0539, p_headsq] <;> ring

private theorem negative_0539 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0539 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0539] at hp
  linarith only [hp]

private def coefficients_0540 : List (List (List (List ℕ))) :=
  [[[[135127889,333456209],[3952887298,4349543938],[3873539249,4071867569]],[[2069736658,2466393298],[11569812836,12363126116],[9611635858,10008292498]],[[1948553729,2146882049],[7644815458,8041472098],[5752041569,5950369889]]],[[[661855110,1058511750],[8704080300,9497393580],[8153784870,8550441510]],[[4930225500,5723538780],[24751344120,26337970680],[20044237980,20837551260]],[[4296260310,4692916950],[16103043660,16896356940],[11918343030,12314999670]]],[[[527419223,725747543],[4752577006,5149233646],[4280937623,4479265943]],[[2861872846,3258529486],[13184299292,13977612572],[10433986126,10830642766]],[[2348398583,2546726903],[8459612206,8856268846],[6166993463,6365321783]]]]

private theorem identity_0540 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(135127889 / 5553192960 : ℝ)) =
      tensor4 coefficients_0540 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0540, p_variance] <;> ring

private theorem negative_0540 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0540 ((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(45 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0540] at hp
  linarith only [hp]

private theorem node_0549 (x0 x1 x2 x3 : ℝ)
    (h0l : (45 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0539 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0540 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0546 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (45 / 64 : ℝ)
  · exact node_0547 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0549 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0541 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0541 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0541 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0541, p_qmass] <;> ring

private theorem negative_0541 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0541 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0541] at hp
  linarith only [hp]

private theorem node_0545 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact node_0546 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0541 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0542 : List (List (List (List ℕ))) :=
  [[[[109974618,159556698],[684200196,783364356],[581198058,630780138]],[[677227716,776391876],[2299226472,2497554792],[1635943716,1735107876]],[[574225578,623807658],[1628971236,1728135396],[1061718138,1111300218]]],[[[319391448,418555608],[1571061576,1769389896],[1265615088,1364779248]],[[1557116616,1755444936],[5011328832,5407985472],[3482102136,3680430456]],[[1251670128,1350834288],[3468157176,3666485496],[2230432008,2329596168]]],[[[209762831,259344911],[887553382,986717542],[684763031,734345111]],[[880580902,979745062],[2713486364,2911814684],[1846850422,1946014582]],[[677790551,727372631],[1839877942,1939042102],[1169059871,1218641951]]]]

private theorem identity_0542 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(6109701 / 38563840 : ℝ)) =
      tensor4 coefficients_0542 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0542, p_variance] <;> ring

private theorem negative_0542 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0542 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0542] at hp
  linarith only [hp]

private theorem node_0544 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0545 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0542 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0543 : List (List (List (List ℕ))) :=
  [[[[105326298,154908378],[1143802836,1242966996],[1066366458,1115948538]],[[665606916,764771076],[3230052552,3428380872],[2620225476,2719389636]],[[567253098,616835178],[2100194676,2199358836],[1560831498,1610413578]]],[[[310094808,409258968],[2494043616,2692371936],[2239728648,2338892808]],[[1533875016,1732203336],[6880534512,7277191152],[5458219176,5656547496]],[[1237725168,1336889328],[4414380816,4612709136],[3232435488,3331599648]]],[[[205114511,254696591],[1350932782,1450096942],[1173708191,1223290271]],[[868960102,968124262],[3651865964,3850194284],[2838685702,2937849862]],[[670818071,720400151],[2314878142,2414042302],[1671949991,1721532071]]]]

private theorem identity_0543 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(835923 / 5509120 : ℝ)) =
      tensor4 coefficients_0543 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0543, p_variance] <;> ring

private theorem negative_0543 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0543 ((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(11 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0543] at hp
  linarith only [hp]

private theorem node_0543 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (23 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0544 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0543 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0544 : List (List (List (List ℕ))) :=
  [[[[1822865497,1327044697],[1620663577,1124842777]],[[2707932434,1716290834],[2303528594,1311886994]],[[850204537,354383737],[648002617,152181817]]],[[[3547154490,2555512890],[3141588570,2149946970]],[[5218130820,3234847620],[4406998980,2423715780]],[[1601251530,609609930],[1195685610,204044010]]],[[[1723964175,1228143375],[1520600175,1024779375]],[[2509548750,1517907150],[2102820750,1111179150]],[[750722175,254901375],[547358175,51537375]]]]

private theorem identity_0544 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_headsq x0 x1 x2 x3-(229055 / 17629184 : ℝ)) =
      tensor4 coefficients_0544 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0544, p_headsq] <;> ring

private theorem negative_0544 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0544 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0544] at hp
  linarith only [hp]

private def coefficients_0545 : List (List (List (List ℕ))) :=
  [[[[165636778,264800938],[2180142836,2378471156],[2042395978,2141560138]],[[1234790756,1433119076],[6199858312,6596514952],[5020847396,5219175716]],[[1076126458,1175290618],[4033660436,4231988756],[2985423898,3084588058]]],[[[527765224,726093544],[4760822528,5157479168],[4288837144,4487165464]],[[2866341608,3262998248],[13208343856,14001657136],[10453561928,10850218568]],[[2352521344,2550849664],[8475411248,8872067888],[6178669744,6376998064]]],[[[362474447,461638607],[2581371694,2779700014],[2246787167,2345951327]],[[1632242854,1830571174],[7009869548,7406526188],[5433406534,5631734854]],[[1276740887,1375905047],[4442442814,4640771134],[3193591847,3292756007]]]]

private theorem identity_0545 (x0 x1 x2 x3 : ℝ) :
    (2776596480 : ℝ)*(-p_variance x0 x1 x2 x3-(82818389 / 1388298240 : ℝ)) =
      tensor4 coefficients_0545 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0545, p_variance] <;> ring

private theorem negative_0545 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0545 ((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0545] at hp
  linarith only [hp]

private theorem node_0554 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (47 / 64 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0544 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0545 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0546 : List (List (List (List ℕ))) :=
  [[[[887305607,639395207],[785623607,537713207]],[[1305421414,809600614],[1102057414,606236614]],[[400684607,152774207],[299002607,51092207]]],[[[1724998144,1229177344],[1521053104,1025232304]],[[2511326168,1519684568],[2103436088,1111794488]],[[751465624,255644824],[547520584,51699784]]],[[[837530128,589619728],[735267088,487356688]],[[1205579936,709759136],[1001053856,505233056]],[[350618608,102708208],[248355568,445168]]]]

private theorem identity_0546 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_headsq x0 x1 x2 x3-(27823 / 123955200 : ℝ)) =
      tensor4 coefficients_0546 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0546, p_headsq] <;> ring

private theorem negative_0546 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (13 / 32 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0546 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0546] at hp
  linarith only [hp]

private def coefficients_0547 : List (List (List (List ℕ))) :=
  [[[[528111225,726439545],[4769068050,5165724690],[4296736665,4495064985]],[[2870810370,3267467010],[13232388420,14025701700],[10473137730,10869794370]],[[2356644105,2554972425],[8491210290,8887866930],[6190346025,6388674345]]],[[[1450589790,1847246430],[10341977820,11135291100],[9002947710,9399604350]],[[6537908940,7331222220],[28087567320,29674193880],[21772777740,22566091020]],[[5115209070,5511865710],[17801369340,18594682620],[12797719950,13194376590]]],[[[923170567,1121498887],[5574293774,5970950414],[4706903047,4905231367]],[[3668482574,4065139214],[14857946908,15651260188],[11301024014,11697680654]],[[2759256967,2957585287],[9311543054,9708199694],[6608065927,6806394247]]]]

private theorem identity_0547 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(11735805 / 123404288 : ℝ)) =
      tensor4 coefficients_0547 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0547, p_variance] <;> ring

private theorem negative_0547 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (13 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0547 ((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(47 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0547] at hp
  linarith only [hp]

private theorem node_0555 (x0 x1 x2 x3 : ℝ)
    (h0l : (47 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0546 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0547 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0553 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (47 / 64 : ℝ)
  · exact node_0554 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0555 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0548 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0548 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0548 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0548, p_qmass] <;> ring

private theorem negative_0548 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0548 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0548] at hp
  linarith only [hp]

private theorem node_0552 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact node_0553 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0548 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0549 : List (List (List (List ℕ))) :=
  [[[[319737449,418901609],[1575530338,1773858658],[1269737849,1368902009]],[[1561585378,1759913698],[5027819876,5424476516],[3494124418,3692452738]],[[1255792889,1354957049],[3480179458,3678507778],[2238331529,2337495689]]],[[[839743326,1038071646],[3559151052,3955807692],[2747297646,2945625966]],[[3531261132,3927917772],[10886927544,11680240824],[7411446252,7808102892]],[[2719407726,2917736046],[7383556332,7780212972],[4692038526,4890366846]]],[[[520697879,619862039],[1985004718,2183333038],[1478251799,1577415959]],[[1971059758,2169388078],[5861875676,6258532316],[3918705838,4117034158]],[[1464306839,1563470999],[3904760878,4103089198],[2454398999,2553563159]]]]

private theorem identity_0549 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(319737449 / 1388298240 : ℝ)) =
      tensor4 coefficients_0549 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0549, p_variance] <;> ring

private theorem negative_0549 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0549 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0549] at hp
  linarith only [hp]

private theorem node_0551 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0552 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0549 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0550 : List (List (List (List ℕ))) :=
  [[[[310440809,409604969],[2502289138,2700617458],[2247628169,2346792329]],[[1538343778,1736672098],[6904579076,7301235716],[5477794978,5676123298]],[[1241847929,1341012089],[4430179858,4628508178],[3244111769,3343275929]]],[[[821150046,1019478366],[5420222172,5816878812],[4710631806,4908960126]],[[3484777932,3881434572],[14655552984,15448866264],[11393894412,11790551052]],[[2691517806,2889846126],[9291110652,9687767292],[6711152526,6909480846]]],[[[511401239,610565399],[2919317038,3117645358],[2463695639,2562859799]],[[1947818158,2146146478],[7753741916,8150398556],[5917483438,6115811758]],[[1450361879,1549526039],[4862314798,5060643118],[3467732759,3566896919]]]]

private theorem identity_0550 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(44348687 / 198328320 : ℝ)) =
      tensor4 coefficients_0550 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0550, p_variance] <;> ring

private theorem negative_0550 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0550 ((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(23 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0550] at hp
  linarith only [hp]

private theorem node_0550 (x0 x1 x2 x3 : ℝ)
    (h0l : (23 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0551 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0550 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0542 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (23 / 32 : ℝ)
  · exact node_0543 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0550 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0538 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0539 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0542 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0536 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0537 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0538 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0529 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0536 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part13Node0535
