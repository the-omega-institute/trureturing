/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part05Node0162
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part05Node0162
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part05.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part05Node0162.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part05Node0162
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

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 2 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 8 : ℝ)
  · exact node_0163 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0169 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part05Node0162
