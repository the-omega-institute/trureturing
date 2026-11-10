/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.middle_strict; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part05
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0154 : List (List (List (List ℕ))) :=
  [[[[28239067,180433334,136699867],[8483707,140922614,116944507]],[[47994427,219944054,156455227],[28239067,180433334,136699867]]],[[[52531550,352973500,269453150],[12439790,272789980,229361390]],[[92623310,433157020,309544910],[52531550,352973500,269453150]]],[[[24112925,172181050,132573725],[3776525,131508250,112237325]],[[44449325,212853850,152910125],[24112925,172181050,132573725]]]]

private theorem identity_0154 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(151061 / 9916416 : ℝ)) =
      tensor4 coefficients_0154 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0154, p_coupled] <;> ring

private theorem negative_0154 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0154 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0154] at hp
  linarith only [hp]

private def coefficients_0155 : List (List (List (List ℕ))) :=
  [[[[77186702829949,30059927431549],[62165043171709,15038267773309]],[[148443376496378,54189825699578],[118400057179898,24146506383098]],[[64629470876029,17502695477629],[49607811217789,2481035819389]]],[[[307846192026100,119987624038900],[247745366720500,59886798733300]],[[591042296609000,215325160634600],[470840645997800,95123510023400]],[[256778493459700,68919925472500],[196677668154100,8819100166900]]],[[[460368542877358,179551260112558],[370198353718318,89381070953518]],[[882371904707996,320737339178396],[702031526389916,140396960860316]],[[382513431441838,101696148677038],[292343242282798,11525959517998]]],[[[305945339681268,119379376519668],[245820788188308,59254825026708]],[[585390475146456,212258548823256],[465141372160536,92009445837336]],[[253209296895588,66643333733988],[193084745402628,6518782241028]]],[[[76236282592499,29755809606899],[61202754611219,14722281625619]],[[145617483735958,52656537764758],[115550427773398,22589481802198]],[[62844884629859,16364411644259],[47811356648579,1330883662979]]]]

private theorem identity_0155 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1330883662979 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0155 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0155, p_headbox] <;> ring

private theorem negative_0155 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0155 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0155] at hp
  linarith only [hp]

private def coefficients_0156 : List (List (List (List ℕ))) :=
  [[[[68648587,385207574,301064587],[29137867,306186134,261553867]],[[108159307,464229014,340575307],[68648587,385207574,301064587]]],[[[128822966,753466732,593654966],[49220486,594261772,514052486]],[[208425446,912671692,673257446],[128822966,753466732,593654966]]],[[[59994821,367900042,292410821],[19903061,287716522,252319061]],[[100086581,448083562,332502581],[59994821,367900042,292410821]]]]

private theorem identity_0156 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(19903061 / 991641600 : ℝ)) =
      tensor4 coefficients_0156 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0156, p_coupled] <;> ring

private theorem negative_0156 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0156 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0156] at hp
  linarith only [hp]

private def coefficients_0157 : List (List (List (List ℕ))) :=
  [[[[931105820513509,554091617326309],[810932543247589,433918340060389]],[[1555260685117898,801232278743498],[1314914130586058,560885724211658]],[[518119619957989,141105416770789],[397946342692069,20932139504869]]],[[[3710451415008148,2204988736684948],[3229701559253908,1724238880930708]],[[6187118440681256,3176193084034856],[5225618729172776,2214693372526376]],[[2053255647394708,547792969071508],[1572505791640468,67043113317268]]],[[[5544543084835678,3290235806602078],[4823337838785118,2569030560551518]],[[9229455852235196,4720841295767996],[7787045360134076,3278430803666876]],[[3050888845396318,796581567162718],[2329683599345758,75376321112158]]],[[[3682155258016020,2181871923769620],[3201301213655220,1701017879408820]],[[6118599249932040,3118032581439240],[5156891161210440,2156324492717640]],[[2014489304159220,514205969912820],[1533635259798420,33351925552020]]],[[[916957764267419,542533233118619],[796732387468859,422307856320059]],[[1521001146445078,772152084147478],[1280550392847958,531701330550358]],[[498736482792059,124311951643259],[378511105993499,4086574844699]]]]

private theorem identity_0157 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(4086574844699 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_0157 ((x0-(1 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0157, p_headbox] <;> ring

private theorem negative_0157 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (9 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0157 ((x0-(1 / 8 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0157] at hp
  linarith only [hp]

private def coefficients_0158 : List (List (List (List ℕ))) :=
  [[[[403305899747107,216093634172707],[343193211347827,155980945773427]],[[728383203971774,353958672822974],[608157827173214,233733296024414]],[[311913941801467,124701676227067],[251801253402187,64588987827787]]],[[[1606061498515256,858505041043256],[1365587013501416,618030556029416]],[[2897722049375992,1402609134431992],[2416773079348312,921660164404312]],[[1239097987444736,491541529972736],[998623502430896,251067044958896]]],[[[2398261045259192,1278863035095992],[2037516033733592,918118023570392]],[[4322695117770784,2083899097444384],[3601205094719584,1362409074393184]],[[1845726399921992,726328389758792],[1484981388396392,365583378233192]]],[[[1591561212803456,846585502595456],[1351043885967296,606068175759296]],[[2865756947086432,1375805526670432],[2384722293414112,894770872998112]],[[1221814629658976,476838919450976],[981297302822816,236321592614816]]],[[[396055764608632,210133872666232],[335921652683512,149999760741112]],[[712400671312304,340556887427504],[592132447462064,220288663577264]],[[303272273676472,117350381734072],[243138161751352,57216269808952]]]]

private theorem identity_0158 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(7152033726119 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0158 ((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0158, p_headbox] <;> ring

private theorem negative_0158 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0158 ((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0158] at hp
  linarith only [hp]

private def coefficients_0159 : List (List (List (List ℕ))) :=
  [[[[108977827,465866054,349141027],[29375347,306661094,269538547]],[[148779067,545468534,388942267],[69176587,386263574,309339787]]],[[[209011368,913843536,689337768],[49225368,594271536,529551768]],[[288904368,1073629536,769230768],[129118368,754057536,609444768]]],[[[99943762,447797924,340106962],[19760242,287430884,259923442]],[[140035522,527981444,380198722],[59852002,367614404,300015202]]]]

private theorem identity_0159 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(9880121 / 991641600 : ℝ)) =
      tensor4 coefficients_0159 ((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0159, p_coupled] <;> ring

private theorem negative_0159 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0159 ((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(9 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0159] at hp
  linarith only [hp]

private theorem node_0170 (x0 x1 x2 x3 : ℝ)
    (h0l : (9 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0158 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0159 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0169 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (9 / 64 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0157 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0170 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0160 : List (List (List (List ℕ))) :=
  [[[[109224547,334657094,221558947],[69713827,255635654,182048227]],[[148735267,413678534,261069667],[109224547,334657094,221558947]]],[[[209393846,651203692,434062646],[129791366,491998732,354460166]],[[288996326,810408652,513665126],[209393846,651203692,434062646]]],[[[99989741,316187482,212324141],[59897981,236003962,172232381]],[[140081501,396371002,252415901],[99989741,316187482,212324141]]]]

private theorem identity_0160 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(59897981 / 991641600 : ℝ)) =
      tensor4 coefficients_0160 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0160, p_coupled] <;> ring

private theorem negative_0160 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0160 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0160] at hp
  linarith only [hp]

private theorem node_0168 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0169 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0160 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0167 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0156 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0168 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0166 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0155 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0167 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0161 : List (List (List (List ℕ))) :=
  [[[[38428223652739,15187987159939],[30911459662099,7671223169299]],[[73428906580958,26948433595358],[58395378599678,11914905614078]],[[31732524671419,8492288178619],[24215760680779,975524187979]]],[[[153212789955320,60573879593720],[123140953776680,30502043415080]],[[292255356222520,106977535499320],[232111683865240,46833863142040]],[[126015219497600,33376309136000],[95943383318960,3304472957360]]],[[[229044137643800,90567709919000],[183930361767800,45453934043000]],[[436145320024000,159192464574400],[345917768272000,68964912822400]],[[187627934731400,49151507006600],[142514158855400,4037731130600]]],[[[152162802560000,60165732224000],[122083698152000,30086627816000]],[[289240208860000,105246068188000],[229082000044000,45087859372000]],[[124140318284000,32143247948000],[94061213876000,2064143540000]]],[[[37903229515000,14983913035000],[30382828795000,7463512315000]],[[71921335070000,26082702110000],[56880533630000,11041900670000]],[[30795076675000,7875760195000],[23274675955000,355359475000]]]]

private theorem identity_0161 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(71071895 / 10154409984 : ℝ)) =
      tensor4 coefficients_0161 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0161, p_headbox] <;> ring

private theorem negative_0161 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0161 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0161] at hp
  linarith only [hp]

private def coefficients_0162 : List (List (List (List ℕ))) :=
  [[[[32395891,188746982,148603891],[12350011,148655222,128558011]],[[52441771,228838742,168649771],[32395891,188746982,148603891]]],[[[60375120,368660640,292791120],[19992840,287896080,252408840]],[[100757400,449425200,333173400],[60375120,368660640,292791120]]],[[[27889450,179734100,144097450],[7553050,139061300,123761050]],[[48225850,220406900,164433850],[27889450,179734100,144097450]]]]

private theorem identity_0162 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(151061 / 9916416 : ℝ)) =
      tensor4 coefficients_0162 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0162, p_coupled] <;> ring

private theorem negative_0162 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0162 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0162] at hp
  linarith only [hp]

private def coefficients_0163 : List (List (List (List ℕ))) :=
  [[[[799651812158749,427808028273949],[679383588308509,307539804423709]],[[1439881908507578,696194340737978],[1199345460807098,455657893037498]],[[614084830294429,242241046409629],[493816606444189,121972822559389]]],[[[3183930939897140,1699132089234740],[2702819802767540,1218020952105140]],[[5727219110355880,2757621409031080],[4764996836096680,1795399134771880]],[[2438888251271540,954089400609140],[1957777114141940,472978263479540]]],[[[4753705935740158,2530367624674558],[4031986462317118,1808648151251518]],[[8542022488792796,4095345866661596],[7098583541946716,2651906919815516]],[[3631988078055838,1408649766990238],[2910268604632798,686930293567198]]],[[[3154226324478468,1674571118795268],[2673047883161508,1193392677478308]],[[5661915340859256,2702604929492856],[4699558458225336,1740248046858936]],[[2403650759731188,923995554047988],[1922472318414228,442817112731028]]],[[[784799513069139,415527551673939],[664497631895859,295225670500659]],[[1407230047099638,668686124309238],[1166626284753078,428082361962678]],[[596466099244899,227194137849699],[476164218071619,106892256676419]]]]

private theorem identity_0163 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(11876917408491 / 180522844160000 : ℝ)) =
      tensor4 coefficients_0163 ((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0163, p_headbox] <;> ring

private theorem negative_0163 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0163 ((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0163] at hp
  linarith only [hp]

private def coefficients_0164 : List (List (List (List ℕ))) :=
  [[[[209682187,915185174,690008587],[49315147,594451094,529641547]],[[289865707,1075552214,770192107],[129498667,754818134,609825067]]],[[[401116686,1793874972,1361769486],[79220526,1150082652,1039873326]],[[562064766,2115771132,1522717566],[240168606,1471978812,1200821406]]],[[[191254941,878330682,671581341],[29725821,555272442,510052221]],[[272019501,1039859802,752345901],[110490381,716801562,590816781]]]]

private theorem identity_0164 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(3302869 / 440729600 : ℝ)) =
      tensor4 coefficients_0164 ((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0164, p_coupled] <;> ring

private theorem negative_0164 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0164 ((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0164] at hp
  linarith only [hp]

private theorem node_0175 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (11 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0163 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0164 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0165 : List (List (List (List ℕ))) :=
  [[[[396253651992779,211617671295179],[336102711406139,151466730708539]],[[711322814466238,342050853071038],[591020933292958,221748971897758]],[[302086945080659,117450964383059],[241936004494019,57300023796419]]],[[[1577500471870160,840240229130960],[1336882167835520,599621925096320]],[[2828793681634600,1354273196156200],[2347557073565320,873036588086920]],[[1199454598946840,462194356207640],[958836294912200,221576052173000]]],[[[2354891524013600,1250924448788000],[1993944537173600,889977461948000]],[[4218272532512800,2010338382061600],[3496378558832800,1288444408381600]],[[1785758323522400,681791248296800],[1424811336682400,320844261456800]]],[[[1562296245600000,827598900576000],[1321653416448000,586956071424000]],[[2795455294512000,1326060604464000],[2314169636208000,844774946160000]],[[1181500641840000,446803296816000],[940857812688000,206160467664000]]],[[[388651539760000,205297007920000],[328488334000000,145133802160000]],[[694653625760000,327944562080000],[574327214240000,207618150560000]],[[293109970480000,109755438640000],[232946764720000,49592232880000]]]]

private theorem identity_0165 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(619902911 / 10154409984 : ℝ)) =
      tensor4 coefficients_0165 ((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0165, p_headbox] <;> ring

private theorem negative_0165 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0165 ((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0165] at hp
  linarith only [hp]

private def coefficients_0166 : List (List (List (List ℕ))) :=
  [[[[100614581,449139562,340777781],[19850021,287610442,260013221]],[[140996861,529904122,381160061],[60232301,368375002,300395501]]],[[[191925760,879672320,672252160],[29815600,555452000,510142000]],[[272980840,1041782480,753307240],[110870680,717562160,591197080]]],[[[91221400,430353200,331384600],[9875800,267662000,250039000]],[[131894200,511698800,372057400],[50548600,349007600,290711800]]]]

private theorem identity_0166 (x0 x1 x2 x3 : ℝ) :
    (1983283200 : ℝ)*(-p_coupled x0 x1 x2 x3-(49379 / 9916416 : ℝ)) =
      tensor4 coefficients_0166 ((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0166, p_coupled] <;> ring

private theorem negative_0166 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0166 ((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(11 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0166] at hp
  linarith only [hp]

private theorem node_0176 (x0 x1 x2 x3 : ℝ)
    (h0l : (11 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0165 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0166 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0174 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (11 / 64 : ℝ)
  · exact node_0175 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0176 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0167 : List (List (List (List ℕ))) :=
  [[[[52538611,163181222,108705811],[32492731,123089462,88659931]],[[72584491,203272982,128751691],[52538611,163181222,108705811]]],[[[100370040,316948080,212704440],[59987760,236183520,172322160]],[[140752320,397712640,253086720],[100370040,316948080,212704440]]],[[[47741650,153587300,103908850],[27405250,112914500,83572450]],[[68078050,194260100,124245250],[47741650,153587300,103908850]]]]

private theorem identity_0167 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(548105 / 9916416 : ℝ)) =
      tensor4 coefficients_0167 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0167, p_coupled] <;> ring

private theorem negative_0167 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0167 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0167] at hp
  linarith only [hp]

private theorem node_0173 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0174 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0167 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0172 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0162 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0173 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0171 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0161 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0172 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0165 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 32 : ℝ)
  · exact node_0166 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0171 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0168 : List (List (List (List ℕ))) :=
  [[[[47703907,149638214,98060707],[27948547,110127494,78305347]],[[67459267,189148934,117816067],[47703907,149638214,98060707]]],[[[90880190,290221180,191593790],[50788430,210037660,151502030]],[[130971950,370404700,231685550],[90880190,290221180,191593790]]],[[[42996725,140223850,93353525],[22660325,99551050,73017125]],[[63333125,180896650,113689925],[42996725,140223850,93353525]]]]

private theorem identity_0168 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(906413 / 9916416 : ℝ)) =
      tensor4 coefficients_0168 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0168, p_coupled] <;> ring

private theorem negative_0168 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0168 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0168] at hp
  linarith only [hp]

private theorem node_0164 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0165 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0168 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0163 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0154 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0164 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0169 : List (List (List (List ℕ))) :=
  [[[[47994427,219944054,156455227],[8483707,140922614,116944507]],[[67749787,259454774,176210587],[28239067,180433334,136699867]]],[[[92623310,433157020,309544910],[12439790,272789980,229361390]],[[132715070,513340540,349636670],[52531550,352973500,269453150]]],[[[44449325,212853850,152910125],[3776525,131508250,112237325]],[[64785725,253526650,173246525],[24112925,172181050,132573725]]]]

private theorem identity_0169 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(151061 / 9916416 : ℝ)) =
      tensor4 coefficients_0169 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0169, p_coupled] <;> ring

private theorem negative_0169 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0169 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0169] at hp
  linarith only [hp]

private theorem node_0162 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0163 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0169 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0170 : List (List (List (List ℕ))) :=
  [[[[13323037,88623674,67553437],[3154837,68287274,57385237]],[[23491237,108960074,77721637],[13323037,88623674,67553437]]],[[[24493224,172941648,132954024],[3866304,131687808,112327104]],[[45120144,214195488,153580944],[24493224,172941648,132954024]]],[[[11080408,84138416,65310808],[621688,63220976,54852088]],[[21539128,105055856,75769528],[11080408,84138416,65310808]]]]

private theorem identity_0170 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(77711 / 15494400 : ℝ)) =
      tensor4 coefficients_0170 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0170, p_coupled] <;> ring

private theorem negative_0170 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0170 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0170] at hp
  linarith only [hp]

private def coefficients_0171 : List (List (List (List ℕ))) :=
  [[[[76471712429341,30633079469341],[61430910989341,15592278029341]],[[145173176938682,53495911018682],[115091574058682,23414308138682]],[[62255406749341,16416773789341],[47214605309341,1375972349341]]],[[[304787080717364,122072157709364],[244618878013364,61903955005364]],[[577582970594728,212153124578728],[457246565186728,91816719170728]],[[247101603829364,64386680821364],[186933401125364,4218478117364]]],[[[455481181683646,182365979226046],[365223648267646,92108445810046]],[[861615257880092,315384852964892],[681100191048092,134869786132892]],[[367727250850846,94612048393246],[277469717434846,4354514977246]]],[[[302487962357124,121047794625924],[242314287418404,60874119687204]],[[571174306781688,208293971319288],[450826956904248,87946621441848]],[[243171320837364,61731153106164],[182997645898644,1557478167444]]],[[[75322145553939,30120890232339],[60278602767219,15077347445619]],[[141968835742518,51566325099318],[111881750169078,21479239525878]],[[60290263658979,15089008337379],[45246720872259,45465550659]]]]

private theorem identity_0171 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(5051727851 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0171 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0171, p_headbox] <;> ring

private theorem negative_0171 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0171 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0171] at hp
  linarith only [hp]

private def coefficients_0172 : List (List (List (List ℕ))) :=
  [[[[60755419,369421238,293171419],[20082619,288075638,252498619]],[[101428219,450766838,333844219],[60755419,369421238,293171419]]],[[[112318398,720457596,577150398],[30391758,556604316,495223758]],[[194245038,884310876,659077038],[112318398,720457596,577150398]]],[[[51383421,350677242,283799421],[10129581,268169562,242545581]],[[92637261,433184922,325053261],[51383421,350677242,283799421]]]]

private theorem identity_0172 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(1125509 / 110182400 : ℝ)) =
      tensor4 coefficients_0172 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0172, p_coupled] <;> ring

private theorem negative_0172 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0172 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0172] at hp
  linarith only [hp]

private def coefficients_0173 : List (List (List (List ℕ))) :=
  [[[[785178362354381,418469298674381],[664851950834381,298142887154381]],[[1405057817188762,671639689828762],[1164404994148762,430986866788762]],[[594095223794381,227386160114381],[473768812274381,107059748594381]]],[[[3125333276297524,1661055456905524],[2644007642441524,1179729823049524]],[[5586549685811048,2657994047027048],[4623898418099048,1695342779315048]],[[2358259375337524,893981555945524],[1876933741481524,412655922089524]]],[[[4664753706313486,2472170167830286],[3942739805977486,1750156267494286]],[[8328958961374172,3943791884407772],[6884931160702172,2499764083735772]],[[3510039225011086,1317455686527886],[2788025324675086,595441786191886]]],[[[3094221029946004,1635051156435604],[2612864474303284,1153694600792884]],[[5518500139860248,2600160392839448],[4555787028574808,1637447281554008]],[[2321681228183044,862511354672644],[1840324672540324,381154799029924]]],[[[769622234168099,405467143428899],[649280356525379,285125265786179]],[[1371033040293238,642722858814838],[1130349285007798,402039103529398]],[[575806151307539,211651060568339],[455464273664819,91309182925619]]]]

private theorem identity_0173 (x0 x1 x2 x3 : ℝ) :
    (1624705597440000 : ℝ)*(-p_headbox x0 x1 x2 x3-(91309182925619 / 1624705597440000 : ℝ)) =
      tensor4 coefficients_0173 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0173, p_headbox] <;> ring

private theorem negative_0173 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0173 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0173] at hp
  linarith only [hp]

private def coefficients_0174 : List (List (List (List ℕ))) :=
  [[[[192596579,881013958,672922979],[29905379,555631558,510231779]],[[273942179,1043705158,754268579],[111250979,718322758,591577379]]],[[[366227238,1724096076,1326880038],[39682758,1071007116,1000335558]],[[529499478,2050640556,1490152278],[202954998,1397551596,1163607798]]],[[[173451101,842723002,653777501],[9597821,515016442,489924221]],[[255377741,1006576282,735704141],[91524461,678869722,571850861]]]]

private theorem identity_0174 (x0 x1 x2 x3 : ℝ) :
    (3966566400 : ℝ)*(-p_coupled x0 x1 x2 x3-(9597821 / 3966566400 : ℝ)) =
      tensor4 coefficients_0174 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0174, p_coupled] <;> ring

private theorem negative_0174 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 64 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0174 ((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0174] at hp
  linarith only [hp]

private theorem node_0185 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 64 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0173 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0174 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0175 : List (List (List (List ℕ))) :=
  [[[[388832516877107,206754971507507],[328661578055747,146584032686147]],[[693559319732734,329404228993534],[573217442090014,209062351350814]],[[291924475446827,109846930077227],[231753536625467,49675991255867]]],[[[1547464020871624,820428594670024],[1306774788122104,579739361920504]],[[2757053289587288,1302982437184088],[2275674824088248,821603971685048]],[[1158469590310864,431434164109264],[917780357561344,190744931359744]]],[[[2309308972094264,1220665734513464],[1948269157141784,859625919560984]],[[4109632342141888,1932345866980288],[3387552712236928,1210266237075328]],[[1723778142405224,635134904824424],[1362738327452744,274095089871944]]],[[[1531555940664000,807065562628800],[1290860248492800,566369870457600]],[[2722342083717600,1273361327647200],[2240950699375200,791969943304800]],[[1139845413348000,415355035312800],[899149721176800,174659343141600]]],[[[380878470860472,200073449574072],[320704299713592,139899278427192]],[[676203708022704,314593665449904],[555855365728944,194245323156144]],[[282612384103032,101807362816632],[222438212956152,41633191669752]]]]

private theorem identity_0175 (x0 x1 x2 x3 : ℝ) :
    (812352798720000 : ℝ)*(-p_headbox x0 x1 x2 x3-(578238773191 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0175 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0175, p_headbox] <;> ring

private theorem negative_0175 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (19 / 32 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0175 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0175] at hp
  linarith only [hp]

private def coefficients_0176 : List (List (List (List ℕ))) :=
  [[[[772551761,970880081],[5246328322,5642984962],[4529556401,4727884721]],[[3335287762,3731944402],[14138101604,14931414884],[10914373522,11311030162]],[[2576680961,2775009281],[8919663202,9316319842],[6398762081,6597090401]]],[[[1952842886,2349499526],[11323242412,12116555692],[9481959206,9878615846]],[[7493607772,8286921052],[29952481784,31539108344],[22681993372,23475306652]],[[5568654806,5965311446],[18685019212,19478332492],[13227924086,13624580726]]],[[[1180983127,1379311447],[6078298094,6474954734],[4953094807,5151423127]],[[4159704014,4556360654],[15817148188,16610461468],[11769003854,12165660494]],[[2992665847,3190994167],[9766740014,10163396654],[6829854007,7028182327]]]]

private theorem identity_0176 (x0 x1 x2 x3 : ℝ) :
    (5553192960 : ℝ)*(-p_variance x0 x1 x2 x3-(772551761 / 5553192960 : ℝ)) =
      tensor4 coefficients_0176 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0176, p_variance] <;> ring

private theorem negative_0176 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (19 / 32 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0176 ((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ)) (1-((x0-(13 / 64 : ℝ))/(1 / 64 : ℝ))) ((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x1-(19 / 32 : ℝ))/(1 / 32 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0176] at hp
  linarith only [hp]

private theorem node_0186 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 64 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (19 / 32 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0175 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0176 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0184 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 64 : ℝ)
  · exact node_0185 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0186 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0177 : List (List (List (List ℕ))) :=
  [[[[100750339,317708678,213084739],[60077539,236363078,172411939]],[[141423139,399054278,253757539],[100750339,317708678,213084739]]],[[[191727198,615870396,416395998],[109800558,452017116,334469358]],[[273653838,779723676,498322638],[191727198,615870396,416395998]]],[[[90797301,297802602,203131701],[49543461,215294922,161877861]],[[132051141,380310282,244385541],[90797301,297802602,203131701]]]]

private theorem identity_0177 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(5504829 / 110182400 : ℝ)) =
      tensor4 coefficients_0177 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0177, p_coupled] <;> ring

private theorem negative_0177 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0177 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0177] at hp
  linarith only [hp]

private theorem node_0183 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact node_0184 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0177 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0182 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0172 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0183 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0181 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0171 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0182 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0178 : List (List (List (List ℕ))) :=
  [[[[36136037444267,13535409783467],[32375151747587,9774524086787]],[[67934347205854,22733091884254],[60412575812494,15211320490894]],[[28620096496787,6019468835987],[24859210800107,2258583139307]]],[[[143944459706384,53859522285584],[128900792867624,38815855446824]],[[270087906917608,89918032076008],[240000573240088,59830698398488]],[[113475252886424,23390315465624],[98431586047664,8346648626864]]],[[[214992238421504,80340076527104],[192427110755264,57774948860864]],[[402610313512768,133305989723968],[357480058180288,88175734391488]],[[168682614824864,34030452930464],[146117487158624,11465325264224]]],[[[142695236398080,53243214228480],[127652436180480,38200414010880]],[[266694278991360,87790234652160],[236608678556160,57704634216960]],[[111419851975680,21967829806080],[96377051758080,6925029588480]]],[[[35511418534912,13227248499712],[31750964841472,9466794806272]],[[66237521782784,21669181712384],[58716614395904,14148274325504]],[[27592391836672,5308221801472],[23831938143232,1547768108032]]]]

private theorem identity_0178 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(1511492293 / 49582080000 : ℝ)) =
      tensor4 coefficients_0178 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0178, p_headbox] <;> ring

private theorem negative_0178 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0178 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0178] at hp
  linarith only [hp]

private def coefficients_0179 : List (List (List (List ℕ))) :=
  [[[[28684336085507,17384022255107],[24923450388827,13623136558427]],[[53030944488334,30430316827534],[45509173094974,22908545434174]],[[21168395138027,9868081307627],[17407509441347,6107195610947]]],[[[114137530219304,69095061508904],[99093863380544,54051394670144]],[[210474047943448,120389110522648],[180386714265928,90301776845128]],[[83668323399344,38625854688944],[68624656560584,23582187850184]]],[[[170282216782784,102956135835584],[147717089116544,80391008169344]],[[313190270235328,178538108340928],[268060014902848,133407853008448]],[[123972593186144,56646512238944],[101407465519904,34081384572704]]],[[[112889173532160,68163162447360],[97846373314560,53120362229760]],[[207082153259520,117630131089920],[176996552824320,87544530654720]],[[81613789109760,36887778024960],[66570988892160,21844977807360]]],[[[28060149179392,16918064161792],[24299695485952,13157610468352]],[[51334983071744,29050813036544],[43814075684864,21529905649664]],[[20141122481152,8999037463552],[16380668787712,5238583770112]]]]

private theorem identity_0179 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(5115804463 / 49582080000 : ℝ)) =
      tensor4 coefficients_0179 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0179, p_headbox] <;> ring

private theorem negative_0179 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0179 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0179] at hp
  linarith only [hp]

private def coefficients_0180 : List (List (List (List ℕ))) :=
  [[[[37953749,134011498,94120949],[17326829,92757658,73494029]],[[58580669,175265338,114747869],[37953749,134011498,94120949]]],[[[70550680,257309360,182885080],[29006320,174220640,141340720]],[[112095040,340398080,224429440],[70550680,257309360,182885080]]],[[[32507152,123118304,88674352],[11589712,81283424,67756912]],[[53424592,164953184,109591792],[32507152,123118304,88674352]]]]

private theorem identity_0180 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(724357 / 30988800 : ℝ)) =
      tensor4 coefficients_0180 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0180, p_coupled] <;> ring

private theorem negative_0180 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0180 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0180] at hp
  linarith only [hp]

private theorem node_0189 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0179 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0180 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0188 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (9 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0178 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0189 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0181 : List (List (List (List ℕ))) :=
  [[[[28269749,180494698,144477749],[7642829,139240858,123850829]],[[48896669,221748538,165104669],[28269749,180494698,144477749]]],[[[51763720,351437840,284179720],[10219360,268349120,242635360]],[[93308080,434526560,325724080],[51763720,351437840,284179720]]],[[[23404192,170763584,139612192],[2486752,128928704,118694752]],[[44321632,212598464,160529632],[23404192,170763584,139612192]]]]

private theorem identity_0181 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(77711 / 15494400 : ℝ)) =
      tensor4 coefficients_0181 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0181, p_coupled] <;> ring

private theorem negative_0181 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0181 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0181] at hp
  linarith only [hp]

private def coefficients_0182 : List (List (List (List ℕ))) :=
  [[[[21217761,120381921],[955249362,1153577682],[947976561,1047140721]],[[927359442,1125687762],[3712884804,4109541444],[2813415282,3011743602]],[[920086641,1019250801],[2785525362,2983853682],[1879383681,1978547841]]],[[[243220446,441548766],[2319622092,2716278732],[2104291566,2302619886]],[[2263842252,2660498892],[8259123384,9052436664],[6051060972,6447717612]],[[2048511726,2246840046],[5995281132,6391937772],[3974659326,4172987646]]],[[[222694687,321858847],[1365756734,1564085054],[1157007007,1256171167]],[[1337866814,1536195134],[4549006588,4945663228],[3239029694,3437358014]],[[1129117087,1228281247],[3211139774,3409468094],[2095967647,2195131807]]]]

private theorem identity_0182 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(2357529 / 154255360 : ℝ)) =
      tensor4 coefficients_0182 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0182, p_variance] <;> ring

private theorem negative_0182 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0182 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(9 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0182] at hp
  linarith only [hp]

private theorem node_0190 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (9 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0181 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0182 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0187 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (9 / 16 : ℝ)
  · exact node_0188 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0190 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0180 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 32 : ℝ)
  · exact node_0181 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0187 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0183 : List (List (List (List ℕ))) :=
  [[[[22910197,72935594,48088597],[12741997,52599194,37920397]],[[33078397,93271994,58256797],[22910197,72935594,48088597]]],[[[43377024,140984448,93733824],[22750104,99730608,73106904]],[[64003944,182238288,114360744],[43377024,140984448,93733824]]],[[[20377048,67869296,45555448],[9918328,46951856,35096728]],[[30835768,88786736,56014168],[20377048,67869296,45555448]]]]

private theorem identity_0183 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(1239791 / 15494400 : ℝ)) =
      tensor4 coefficients_0183 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0183, p_coupled] <;> ring

private theorem negative_0183 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0183 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0183] at hp
  linarith only [hp]

private theorem node_0179 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0180 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0183 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0178 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0170 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0179 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0184 : List (List (List (List ℕ))) :=
  [[[[23491237,108960074,77721637],[3154837,68287274,57385237]],[[33659437,129296474,87889837],[13323037,88623674,67553437]]],[[[45120144,214195488,153580944],[3866304,131687808,112327104]],[[65747064,255449328,174207864],[24493224,172941648,132954024]]],[[[21539128,105055856,75769528],[621688,63220976,54852088]],[[31997848,125973296,86228248],[11080408,84138416,65310808]]]]

private theorem identity_0184 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(77711 / 15494400 : ℝ)) =
      tensor4 coefficients_0184 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0184, p_coupled] <;> ring

private theorem negative_0184 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (5 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0184 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0184] at hp
  linarith only [hp]

private theorem node_0177 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0178 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0184 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0161 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 16 : ℝ)
  · exact node_0162 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0177 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0185 : List (List (List (List ℕ))) :=
  [[[[11932667,35486134,21616667],[6993827,25608454,16677827]],[[16871507,45363814,26555507],[11932667,35486134,21616667]]],[[[22878688,68998976,42246688],[12710488,48662576,32078488]],[[33046888,89335376,52414888],[22878688,68998976,42246688]]],[[[10856242,33333284,20540242],[5626882,22874564,15310882]],[[16085602,43792004,25769602],[10856242,33333284,20540242]]]]

private theorem identity_0185 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(2813441 / 15494400 : ℝ)) =
      tensor4 coefficients_0185 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0185, p_coupled] <;> ring

private theorem negative_0185 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0185 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0185] at hp
  linarith only [hp]

private theorem node_0160 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0161 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0185 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

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

private theorem node_0191 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0192 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0205 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0159 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0160 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0191 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0206 : List (List (List (List ℕ))) :=
  [[[[7478027,45944854,30719627],[2539187,36067174,25780787]],[[12416867,55822534,35658467],[7478027,45944854,30719627]]],[[[14259928,90497456,60743128],[4091728,70161056,50574928]],[[24428128,110833856,70911328],[14259928,90497456,60743128]]],[[[6692122,44373044,29933722],[1462762,33914324,24704362]],[[11921482,54831764,35163082],[6692122,44373044,29933722]]]]

private theorem identity_0206 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(731381 / 15494400 : ℝ)) =
      tensor4 coefficients_0206 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0206, p_coupled] <;> ring

private theorem negative_0206 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0206 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0206] at hp
  linarith only [hp]

private def coefficients_0207 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[27],[51]]],[[[9],[33]],[[33],[57]]]]

private theorem identity_0207 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0207 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0207, p_mass] <;> ring

private theorem negative_0207 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0207 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0207] at hp
  linarith only [hp]

private theorem node_0210 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0206 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.mass) (negative_0207 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 4 : ℝ)
  · exact node_0159 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0210 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0208 : List (List (List (List ℕ))) :=
  [[[[10143107,28033414,14016707],[5494787,18736774,9368387]],[[14791427,37330054,18665027],[10143107,28033414,14016707]]],[[[19479126,54452652,27226326],[9601446,34697292,17348646]],[[29356806,74208012,37104006],[19479126,54452652,27226326]]],[[[9156461,26060122,13030061],[3927101,15601402,7800701]],[[14385821,36518842,18259421],[9156461,26060122,13030061]]]]

private theorem identity_0208 (x0 x1 x2 x3 : ℝ) :
    (15494400 : ℝ)*(-p_coupled x0 x1 x2 x3-(3927101 / 15494400 : ℝ)) =
      tensor4 coefficients_0208 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0208, p_coupled] <;> ring

private theorem negative_0208 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0208 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0208] at hp
  linarith only [hp]

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.coupled) (negative_0208 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0209 : List (List (List (List ℕ))) :=
  [[[[9134272,15332032],[78696704,91092224],[76534912,82732672]],[[78696704,91092224],[294518848,319309888],[229767104,242162624]],[[76534912,82732672],[229767104,242162624],[160204672,166402432]]],[[[32100480,44496000],[188834040,213625080],[170678520,183074040]],[[188834040,213625080],[659472480,709054560],[498528360,523319400]],[[170678520,183074040],[498528360,523319400],[341794800,354190320]]],[[[23312209,29509969],[110829338,123224858],[94489609,100687369]],[[110829338,123224858],[366337636,391128676],[269453258,281848778]],[[94489609,100687369],[269453258,281848778],[181936129,188133889]]]]

private theorem identity_0209 (x0 x1 x2 x3 : ℝ) :
    (10846080 : ℝ)*(-p_variance x0 x1 x2 x3-(20389 / 24210 : ℝ)) =
      tensor4 coefficients_0209 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1)) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0209, p_variance] <;> ring

private theorem negative_0209 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0209 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x1-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/1) (1-((x3-0)/1))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0209] at hp
  linarith only [hp]

theorem exclude_02 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ 1)
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.variance) (negative_0209 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part05
