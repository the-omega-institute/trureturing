/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part04Node0142
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part04Node0142
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part04.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part04Node0142.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part04Node0142
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0135 : List (List (List (List ℕ))) :=
  [[[[54506460818549,30290077125749],[47014517113589,22798133420789]],[[104962361644138,56529594258538],[89978474234218,41545706848618]],[[43645042911989,19428659219189],[36153099207029,11936715514229]]],[[[217301194717588,120764389136788],[187321606192468,90784800611668]],[[417450699889256,224377088727656],[357491522839016,164417911677416]],[[172998528602068,76461723021268],[143018940076948,46482134496148]]],[[[324817200689038,180503970506638],[279831293123758,135518062941358]],[[622487525788796,333861065423996],[532515710658236,243889250293436]],[[257082229110958,112768998928558],[212096321545678,67783091363278]]],[[[215756695986340,119875117592740],[185755866381940,89874287988340]],[[412472481661880,220709324874680],[352470822453080,160707665665880]],[[169749091752340,73867513358740],[139748262147940,43866683754340]]],[[[53734225788779,29845455689579],[46231658929499,22342888830299]],[[102473287303078,54695747104678],[87468153584518,39690613386118]],[[42020344923899,18131574824699],[34517778064619,10629007965419]]]]

private theorem identity_0135 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(10629007965419 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0135 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0135, p_headbox] <;> ring

private theorem negative_0135 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0135 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0135] at hp
  linarith only [hp]

private def coefficients_0136 : List (List (List (List ℕ))) :=
  [[[[79212923,274633846,191547323],[40864283,197936566,153198683]],[[117561563,351331126,229895963],[79212923,274633846,191547323]]],[[[148926750,530269500,373595550],[71648430,375712860,296317230]],[[226205070,684826140,450873870],[148926750,530269500,373595550]]],[[[69534269,255276538,181868669],[30604589,177417178,142938989]],[[108463949,333135898,220798349],[69534269,255276538,181868669]]]]

private theorem identity_0136 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(30604589 / 991641600 : ℝ)) =
      tensor4 coefficients_0136 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0136, p_coupled] <;> ring

private theorem negative_0136 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0136 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0136] at hp
  linarith only [hp]

private theorem node_0148 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0135 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0136 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0137 : List (List (List (List ℕ))) :=
  [[[[50765800543229,26549416850429],[43273856838269,19057473145469]],[[97481041093498,49048273707898],[82497153683578,34064386297978]],[[39904382636669,15687998943869],[32412438931709,8196055238909]]],[[[202326739911028,105789934330228],[172347151385908,75810345805108]],[[387501790276136,194428179114536],[327542613225896,134469002064296]],[[158024073795508,61487268214708],[128044485270388,31507679689588]]],[[[302338993701598,158025763519198],[257353086136318,113039855953918]],[[577531111813916,288904651449116],[487559296683356,198932836318556]],[[234604022123518,90290791941118],[189618114558238,45304884375838]]],[[[200761000100500,104879421706900],[170760170496100,74878592102500]],[[382481089890200,190717933103000],[322479430681400,130716273894200]],[[154753395866500,58871817472900],[124752566262100,28870987868500]]],[[[49982942359139,26094172259939],[42480375499859,18591605400659]],[[94970720443798,47193180245398],[79965586725238,32188046526838]],[[38269061494259,14380291395059],[30766494634979,6877724535779]]]]

private theorem identity_0137 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6877724535779 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0137 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0137, p_headbox] <;> ring

private theorem negative_0137 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0137 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0137] at hp
  linarith only [hp]

private def coefficients_0138 : List (List (List (List ℕ))) :=
  [[[[60329123,236866246,172663523],[21980483,160168966,134314883]],[[98677763,313563526,211012163],[60329123,236866246,172663523]]],[[[110578110,453572220,335246910],[33299790,299015580,257968590]],[[187856430,608128860,412525230],[110578110,453572220,335246910]]],[[[50069429,216346858,162403829],[11139749,138487498,123474149]],[[88999109,294206218,201333509],[50069429,216346858,162403829]]]]

private theorem identity_0138 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(11139749 / 991641600 : ℝ)) =
      tensor4 coefficients_0138 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0138, p_coupled] <;> ring

private theorem negative_0138 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0138 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0138] at hp
  linarith only [hp]

private theorem node_0149 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0137 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0138 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0147 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0148 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0149 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0139 : List (List (List (List ℕ))) :=
  [[[[778747321812829,391285182728029],[658876222533469,271414083448669]],[[1416116437064378,641192158894778],[1176374238505658,401449960336058]],[[610125683597149,222663544512349],[490254584317789,102792445232989]]],[[[3102336142884212,1555117420068212],[2622757236124532,1075538513308532]],[[5636101301905384,2541663856273384],[4676943488386024,1582506042754024]],[[2424976342573172,877757619757172],[1945397435813492,398178712997492]]],[[[4634352100882414,2317464304556014],[3914846759400814,1597958963074414]],[[8411268900678428,3777493308025628],[6972258217715228,2338482625062428]],[[3614010626616814,1297122830290414],[2894505285135214,577617488808814]]],[[[3076685155740852,1534717175196852],[2596926785480532,1054958804936532]],[[5578699846854744,2494763885766744],[4619183106334104,1535247145246104]],[[2393595067481892,851627086937892],[1913836697221572,371868716677572]]],[[[765921872522259,381085104573459],[645961036263219,261124268314419]],[[1387415804202198,617742268304598],[1147494131684118,377820595786518]],[[594435096433539,209598328484739],[474474260174499,89637492225699]]]]

private theorem identity_0139 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(9959721358411 / 180522844160000 : ℝ)) =
      tensor4 coefficients_0139 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0139, p_headbox] <;> ring

private theorem negative_0139 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0139 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0139] at hp
  linarith only [hp]

private def coefficients_0140 : List (List (List (List ℕ))) :=
  [[[[180513379,856847558,660839779],[27118819,550058438,507445219]],[[257210659,1010242118,737537059],[103816099,703452998,584142499]]],[[[343771686,1679184972,1304424486],[35820486,1063282572,996473286]],[[497747286,1987136172,1458400086],[189796086,1371233772,1150448886]]],[[[163078749,821978298,643405149],[8522109,512865018,488848509]],[[240357069,976534938,720683469],[85800429,667421658,566126829]]]]

private theorem identity_0140 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(946901 / 440729600 : ℝ)) =
      tensor4 coefficients_0140 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0140, p_coupled] <;> ring

private theorem negative_0140 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0140 ((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0140] at hp
  linarith only [hp]

private theorem node_0153 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0139 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0140 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0141 : List (List (List (List ℕ))) :=
  [[[[91368729,289697049],[3809589138,4206245778],[3774000249,3972328569]],[[3716622738,4113279378],[14817101796,15610415076],[11212038738,11608695378]],[[3681033849,3879362169],[11119072338,11515728978],[7493818329,7692146649]]],[[[586958310,983614950],[8442727020,9236040300],[7967328390,8363985030]],[[8256794220,9050107500],[31311515160,32898141720],[23277840300,24071153580]],[[7781395590,8178052230],[23091907500,23885220780],[15422071590,15818728230]]],[[[496281583,694609903],[4634521886,5031178526],[4194020143,4392348463]],[[4541555486,4938212126],[16497181372,17290494652],[12067185566,12463842206]],[[4101053743,4299382063],[11974219166,12370875806],[7928945263,8127273583]]]]

private theorem identity_0141 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(10152081 / 617021440 : ℝ)) =
      tensor4 coefficients_0141 ((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0141, p_variance] <;> ring

private theorem negative_0141 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0141 ((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0141] at hp
  linarith only [hp]

private theorem node_0152 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 64 : ℝ)
  · exact node_0153 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0141 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0142 : List (List (List (List ℕ))) :=
  [[[[98096723,312401446,210431123],[59748083,235704166,172082483]],[[136445363,389098726,248779763],[98096723,312401446,210431123]]],[[[187275390,606966780,411944190],[109997070,452410140,334665870]],[[264553710,761523420,489222510],[187275390,606966780,411944190]]],[[[88999109,294206218,201333509],[50069429,216346858,162403829]],[[127928789,372065578,240263189],[88999109,294206218,201333509]]]]

private theorem identity_0142 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(50069429 / 991641600 : ℝ)) =
      tensor4 coefficients_0142 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0142, p_coupled] <;> ring

private theorem negative_0142 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0142 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0142] at hp
  linarith only [hp]

private theorem node_0151 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0152 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0142 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0143 : List (List (List (List ℕ))) :=
  [[[[215420818,265002898],[896254676,995418836],[687806338,737388418]],[[886958036,986122196],[2721011272,2919339592],[1847998196,1947162356]],[[678509698,728091778],[1838701556,1937865716],[1167164338,1216746418]]],[[[535327608,634491768],[2005258056,2203586376],[1483875408,1583039568]],[[1986664776,2184993096],[5875073472,6271730112],[3916298616,4114626936]],[[1465282128,1564446288],[3897705336,4096033656],[2446368168,2545532328]]],[[[320252791,369834871],[1109695382,1208859542],[796415071,845997151]],[[1100398742,1199562902],[3155446204,3353774524],[2068992422,2168156582]],[[787118431,836700511],[2059695782,2158859942],[1279549831,1329131911]]]]

private theorem identity_0143 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(107710409 / 347074560 : ℝ)) =
      tensor4 coefficients_0143 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0143, p_variance] <;> ring

private theorem negative_0143 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0143 ((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0143] at hp
  linarith only [hp]

private theorem node_0150 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0151 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0143 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0146 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0147 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0150 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0144 : List (List (List (List ℕ))) :=
  [[[[27215497538987,15271112489387],[23464214109347,11519829059747]],[[51933412940734,28044642841534],[44430846081454,20542075982254]],[[21358557106547,9414172056947],[17607273676907,5662888627307]]],[[[108452093740336,60837802540336],[93442241105416,45827949905416]],[[206443985538152,111215403138152],[176424280268312,81195697868312]],[[84600372397816,36986081197816],[69590519762896,21976228562896]]],[[[162039529718432,90862408617632],[139518262437632,68341141336832]],[[307686381280864,165332139079264],[262643846719264,120289604517664]],[[125628286252832,54451165152032],[103107018972032,31929897871232]]],[[[107584779300096,60295870500096],[92566666310016,45277757510016]],[[203774485667712,109196668067712],[173738259687552,79160442087552]],[[82889700767616,35600791967616],[67871587777536,20582678977536]]],[[[26781844079232,15000150229632],[23026429164672,11244735315072]],[[50598673576704,27035285877504],[43087843747584,19524456048384]],[[20503228102272,8721534252672],[16747813187712,4966119338112]]]]

private theorem identity_0144 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(4310867481 / 44072960000 : ℝ)) =
      tensor4 coefficients_0144 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0144, p_headbox] <;> ring

private theorem negative_0144 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0144 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0144] at hp
  linarith only [hp]

private def coefficients_0145 : List (List (List (List ℕ))) :=
  [[[[37421837,132947674,93589037],[17956997,94017994,74124197]],[[56886677,171877354,113053877],[37421837,132947674,93589037]]],[[[69914568,256037136,182248968],[30694368,177596736,143028768]],[[109134768,334477536,221469168],[69914568,256037136,182248968]]],[[[32402952,122909904,88570152],[12647592,83399184,68814792]],[[52158312,162420624,108325512],[32402952,122909904,88570152]]]]

private theorem identity_0145 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(175661 / 6886400 : ℝ)) =
      tensor4 coefficients_0145 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0145, p_coupled] <;> ring

private theorem negative_0145 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0145 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0145] at hp
  linarith only [hp]

private theorem node_0156 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0144 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0145 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0146 : List (List (List (List ℕ))) :=
  [[[[82752929,181917089],[1071347218,1269675538],[1002539249,1101703409]],[[1057402258,1255730578],[3959025476,4355682116],[2929513138,3127841458]],[[988594289,1087758449],[2915568178,3113896498],[1940918849,2040083009]]],[[[368308286,566636606],[2555852812,2952509452],[2215434446,2413762766]],[[2527962892,2924619532],[8759474744,9552788024],[6287291692,6683948332]],[[2187544526,2385872846],[6259401772,6656058412],[4099747166,4298075486]]],[[[286247359,385411519],[1485889598,1684217918],[1213587199,1312751359]],[[1471944638,1670272958],[4803217276,5199873916],[3359162558,3557490878]],[[1199642239,1298806399],[3345217598,3543545918],[2159520319,2258684479]]]]

private theorem identity_0146 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(11821847 / 198328320 : ℝ)) =
      tensor4 coefficients_0146 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0146, p_variance] <;> ring

private theorem negative_0146 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0146 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0146] at hp
  linarith only [hp]

private theorem node_0155 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0156 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0146 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0147 : List (List (List (List ℕ))) :=
  [[[[73456289,172620449],[1967891938,2166220258],[1950215489,2049379649]],[[1034160658,1232488978],[5775356516,6172013156],[4852755538,5051083858]],[[974649329,1073813489],[3835354498,4033682818],[2916485009,3015649169]]],[[[349715006,548043326],[4356495772,4753152412],[4118340446,4316668766]],[[2481479692,2878136332],[12407243864,13200557144],[10148883532,10545540172]],[[2159654606,2357982926],[8106527932,8503184572],[6058433006,6256761326]]],[[[276950719,376114879],[2389987838,2588316158],[2168816959,2267981119]],[[1448703038,1647031358],[6634655356,7031311996],[5297511998,5495840318]],[[1185697279,1284861439],[4272557438,4470885758],[3142639999,3241804159]]]]

private theorem identity_0147 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(73456289 / 1388298240 : ℝ)) =
      tensor4 coefficients_0147 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0147, p_variance] <;> ring

private theorem negative_0147 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0147 ((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0147] at hp
  linarith only [hp]

private theorem node_0154 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0155 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0147 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0145 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 32 : ℝ)
  · exact node_0146 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0154 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0148 : List (List (List (List ℕ))) :=
  [[[[20055611,67226422,45234011],[10468451,48052102,35646851]],[[29642771,86400742,54821171],[20055611,67226422,45234011]]],[[[37736448,129703296,88093248],[18271608,90773616,68628408]],[[57201288,168632976,107558088],[37736448,129703296,88093248]]],[[[17591058,62297316,42769458],[7713378,42541956,32891778]],[[27468738,82052676,52647138],[17591058,62297316,42769458]]]]

private theorem identity_0148 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(428521 / 6886400 : ℝ)) =
      tensor4 coefficients_0148 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0148, p_coupled] <;> ring

private theorem negative_0148 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0148 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0148] at hp
  linarith only [hp]

private theorem node_0144 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0145 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0148 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0149 : List (List (List (List ℕ))) :=
  [[[[109453529,159035609],[681995938,781160098],[586487369,636069449]],[[677347618,776511778],[2313411236,2511739556],[1663953538,1763117698]],[[581839049,631421129],[1659305218,1758469378],[1091411129,1140993209]]],[[[323393030,422557190],[1580517340,1778845660],[1285014230,1384178390]],[[1571220700,1769549020],[5074980440,5471637080],[3559539580,3757867900]],[[1275717590,1374881750],[3550242940,3748571260],[2302415270,2401579430]]],[[[214631503,264213583],[899905406,999069566],[699218863,748800943]],[[895257086,994421246],[2764337212,2962665532],[1896970046,1996134206]],[[694570543,744152623],[1892321726,1991485886],[1211696143,1261278223]]]]

private theorem identity_0149 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(109453529 / 347074560 : ℝ)) =
      tensor4 coefficients_0149 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0149, p_variance] <;> ring

private theorem negative_0149 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0149 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0149] at hp
  linarith only [hp]

private theorem node_0143 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0144 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0149 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0150 : List (List (List (List ℕ))) :=
  [[[[104805209,154387289],[1145084818,1244248978],[1096059449,1145641529]],[[663402658,762566818],[3262830596,3461158916],[2710987618,2810151778]],[[572542409,622124489],[2145635698,2244799858],[1628873129,1678455209]]],[[[314096390,413260550],[2514248620,2712576940],[2311711910,2410876070]],[[1543330780,1741659100],[6988926200,7385582840],[5668714780,5867043100]],[[1257124310,1356288470],[4530457420,4728785740],[3384892790,3484056950]]],[[[209983183,259565263],[1370547806,1469711966],[1216344463,1265926543]],[[881312126,980476286],[3728863612,3927191932],[2959111166,3058275326]],[[685273903,734855983],[2386205726,2485369886],[1756711663,1806293743]]]]

private theorem identity_0150 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(104805209 / 347074560 : ℝ)) =
      tensor4 coefficients_0150 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0150, p_variance] <;> ring

private theorem negative_0150 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0150 ((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0150] at hp
  linarith only [hp]

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 8 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0143 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0150 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part04Node0142
