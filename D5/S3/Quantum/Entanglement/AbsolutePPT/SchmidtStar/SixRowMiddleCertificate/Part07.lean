/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part07
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part07
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part07.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part07
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0253 : List (List (List (List ℕ))) :=
  [[[[79532951,48544151],[68493191,37504391]],[[153546022,91568422],[131466502,69488902]],[[56581871,25593071],[45542111,14553311]]],[[[154379160,92401560],[131718600,69741000]],[[297428040,173472840],[252106920,128151720]],[[108186480,46208880],[85525920,23548320]]],[[[74683800,43695000],[63063000,32074200]],[[143557200,81579600],[120315600,58338000]],[[51442200,20453400],[39821400,8832600]]]]

private theorem identity_0253 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_headsq x0 x1 x2 x3-(4907 / 17216 : ℝ)) =
      tensor4 coefficients_0253 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0253, p_headsq] <;> ring

private theorem negative_0253 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0253 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0253] at hp
  linarith only [hp]

private def coefficients_0254 : List (List (List (List ℕ))) :=
  [[[[454899257,330944057],[410740217,286785017]],[[748269394,500358994],[659951314,412040914]],[[258507737,134552537],[214348697,90393497]]],[[[889889466,641979066],[800409306,552498906]],[[1456139652,960318852],[1277179332,781358532]],[[496525386,248614986],[407045226,159134826]]],[[[434665391,310710191],[389344271,265389071]],[[707220622,459310222],[616578382,368667982]],[[237692831,113737631],[192371711,68416511]]]]

private theorem identity_0254 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(68416511 / 247910400 : ℝ)) =
      tensor4 coefficients_0254 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0254, p_headsq] <;> ring

private theorem negative_0254 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0254 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0254] at hp
  linarith only [hp]

private def coefficients_0255 : List (List (List (List ℕ))) :=
  [[[[4607182074029,1977100640429],[3670215563309,1040134129709]],[[10542012658138,5281849790938],[8668079636698,3407916769498]],[[4455409777709,1825328344109],[3518443266989,888361833389]]],[[[18468833002420,8025111581620],[14723600232820,4279878812020]],[[41949798390440,21062355548840],[34459332851240,13571890009640]],[[17606372088820,7162650668020],[13861139319220,3417417898420]]],[[[27747304707838,12196071248638],[22133924913118,6582691453918]],[[62568342608156,31465875689756],[51341583018716,20239116100316]],[[26073469079518,10522235620318],[20460089284798,4908855825598]]],[[[18516786553588,8225158163188],[14777854000708,4486225610308]],[[41455248577496,20871991796696],[33977383471736,13394126690936]],[[17149421054308,6857792663908],[13410488501428,3118860111028]]],[[[4631129366579,2077094448179],[3697310349539,1143275431139]],[[10294684886518,5186615049718],[8427046852438,3318977015638]],[[4226910878339,1672875959939],[3293091861299,739056942899]]]]

private theorem identity_0255 (x0 x1 x2 x3 : ℝ) :
    (6346506240000 : ℝ)*(-p_headbox x0 x1 x2 x3-(739056942899 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0255 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0255, p_headbox] <;> ring

private theorem negative_0255 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0255 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0255] at hp
  linarith only [hp]

private def coefficients_0256 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0256 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0256 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0256, p_qmass] <;> ring

private theorem negative_0256 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0256 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0256] at hp
  linarith only [hp]

private theorem node_0263 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0255 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0256 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0257 : List (List (List (List ℕ))) :=
  [[[[4137125071829,1507043638229],[3200158561109,570077127509]],[[9601898653738,4341735786538],[7727965632298,2467802765098]],[[3985352775509,1355271341909],[3048386264789,418304831189]]],[[[16591238266900,6147516846100],[12846005497300,2402284076500]],[[38194608919400,17307166077800],[30704143380200,9816700538600]],[[15728777353300,5285055932500],[11983544583700,1539823162900]]],[[[24935381964238,9384148505038],[19322002169518,3770768710318]],[[56944497120956,25842030202556],[45717737531516,14615270613116]],[[23261546335918,7710312876718],[17648166541198,2096933081998]]],[[[16645492034788,6353863644388],[12906559481908,2614931091508]],[[37712659539896,17129402759096],[30234794434136,9651537653336]],[[15278126535508,4986498145108],[11539193982628,1247565592228]]],[[[4164219858059,1610184939659],[3230400841019,676365922619]],[[9360865869478,4252796032678],[7493227835398,2385157998598]],[[3760001369819,1205966451419],[2826182352779,272147434379]]]]

private theorem identity_0257 (x0 x1 x2 x3 : ℝ) :
    (6346506240000 : ℝ)*(-p_headbox x0 x1 x2 x3-(272147434379 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0257 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0257, p_headbox] <;> ring

private theorem negative_0257 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0257 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0257] at hp
  linarith only [hp]

private def coefficients_0258 : List (List (List (List ℕ))) :=
  [[[[105977563,428876726,307404763],[17659483,252240566,219086683]],[[194295643,605512886,395722843],[105977563,428876726,307404763]]],[[[198864870,831572940,601719270],[21066630,475976460,423921030]],[[376663110,1187169420,779517510],[198864870,831572940,601719270]]],[[[92707749,402337098,294134949],[3227589,223376778,204654789]],[[182187909,581297418,383615109],[92707749,402337098,294134949]]]]

private theorem identity_0258 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(358621 / 110182400 : ℝ)) =
      tensor4 coefficients_0258 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0258, p_coupled] <;> ring

private theorem negative_0258 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0258 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0258] at hp
  linarith only [hp]

private def coefficients_0259 : List (List (List (List ℕ))) :=
  [[[[452300777,328345577],[407560697,283605497]],[[673057114,425146714],[583576954,335666554]],[[203325137,79369937],[158585057,34629857]]],[[[883205608,635295208],[793144408,545234008]],[[1303031816,807211016],[1122909416,627088616]],[[384963808,137053408],[294902608,46992208]]],[[[430742422,306787222],[385421302,261466102]],[[629649884,381739484],[539007644,291097244]],[[181476262,57521062],[136155142,12199942]]]]

private theorem identity_0259 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(6099971 / 247910400 : ℝ)) =
      tensor4 coefficients_0259 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0259, p_headsq] <;> ring

private theorem negative_0259 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0259 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0259] at hp
  linarith only [hp]

private def coefficients_0260 : List (List (List (List ℕ))) :=
  [[[[61091387,230643574,161804987],[16351307,141163414,117064907]],[[83461427,275383654,184175027],[38721347,185903494,139434947]]],[[[115748608,448418816,317175808],[25687408,268296416,227114608]],[[160779208,538480016,362206408],[70718008,358357616,272145208]]],[[[54567442,217595684,155281042],[9246322,126953444,109959922]],[[77228002,262916804,177941602],[31906882,172274564,132620482]]]]

private theorem identity_0260 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(4623161 / 247910400 : ℝ)) =
      tensor4 coefficients_0260 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0260, p_coupled] <;> ring

private theorem negative_0260 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0260 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0260] at hp
  linarith only [hp]

private theorem node_0266 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0259 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0260 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0265 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 32 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0258 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0266 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0264 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0257 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0265 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0262 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0263 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0264 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0261 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0254 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0262 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0261 : List (List (List (List ℕ))) :=
  [[[[222989351,161011751],[200328791,138351191]],[[364923622,240968422],[319602502,195647302]],[[124503071,62525471],[101842511,39864911]]],[[[435699360,311744160],[389797200,265842000]],[[708998040,461087640],[617193720,369283320]],[[238436280,114481080],[192534120,68578920]]],[[[212547600,150570000],[189306000,127328400]],[[343749600,219794400],[297266400,173311200]],[[113770800,51793200],[90529200,28551600]]]]

private theorem identity_0261 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(7931 / 34432 : ℝ)) =
      tensor4 coefficients_0261 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0261, p_headsq] <;> ring

private theorem negative_0261 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0261 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0261] at hp
  linarith only [hp]

private def coefficients_0262 : List (List (List (List ℕ))) :=
  [[[[2359584034739,1082566575539],[1892674526219,615657067019]],[[5235381146158,2681346227758],[4301562129118,1747527210718]],[[2157474790619,880457331419],[1690565282099,413547822899]]],[[[9442201595320,4371876116920],[7576391803600,2506066325200]],[[20803270068920,10662619112120],[17071650485480,6930999528680]],[[8509010392000,3438684913600],[6643200600280,1572875121880]]],[[[14160961200800,6611810621600],[11365240757600,3816090178400]],[[30982876427200,15884575268800],[25391435540800,10293134382400]],[[12575518025600,5026367446400],[9779797582400,2230647003200]]],[[[9433620864000,4438226304000],[7571968704000,2576574144000]],[[20497407552000,10506618432000],[16774103232000,6783314112000]],[[8253877248000,3258482688000],[6392225088000,1396830528000]]],[[[2355275520000,1115723520000],[1890443520000,650891520000]],[[5082416640000,2603312640000],[4152752640000,1673648640000]],[[2029893120000,790341120000],[1565061120000,325509120000]]]]

private theorem identity_0262 (x0 x1 x2 x3 : ℝ) :
    (3173253120000 : ℝ)*(-p_headbox x0 x1 x2 x3-(883 / 8608 : ℝ)) =
      tensor4 coefficients_0262 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0262, p_headbox] <;> ring

private theorem negative_0262 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0262 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0262] at hp
  linarith only [hp]

private def coefficients_0263 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0263 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0263 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0263, p_qmass] <;> ring

private theorem negative_0263 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0263 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0263] at hp
  linarith only [hp]

private theorem node_0269 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0262 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0263 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0264 : List (List (List (List ℕ))) :=
  [[[[2125090526219,848073067019],[1658181017699,381163558499]],[[4766394129118,2212359210718],[3832575112078,1278540193678]],[[1922981282099,645963822899],[1456071773579,179054314379]]],[[[8506055803600,3435730325200],[6640246011880,1569920533480]],[[18930978485480,8790327528680],[15199358902040,5058707945240]],[[7572864600280,2502539121880],[5707054808560,636729330160]]],[[[12759736757600,5210586178400],[9964016314400,2414865735200]],[[28180427540800,13082126382400],[22588986654400,7490685496000]],[[11174293582400,3625143003200],[8378573139200,829422560000]]],[[[8501632704000,3506238144000],[6639980544000,1644585984000]],[[18633431232000,8642642112000],[14910126912000,4919337792000]],[[7321889088000,2326494528000],[5460236928000,464842368000]]],[[[2122859520000,883307520000],[1658027520000,418475520000]],[[4617584640000,2138480640000],[3687920640000,1208816640000]],[[1797477120000,557925120000],[1332645120000,93093120000]]]]

private theorem identity_0264 (x0 x1 x2 x3 : ℝ) :
    (3173253120000 : ℝ)*(-p_headbox x0 x1 x2 x3-(8081 / 275456 : ℝ)) =
      tensor4 coefficients_0264 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0264, p_headbox] <;> ring

private theorem negative_0264 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0264 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0264] at hp
  linarith only [hp]

private def coefficients_0265 : List (List (List (List ℕ))) :=
  [[[[884239577,636329177],[793597337,545686937]],[[1304809234,808988434],[1123524754,627703954]],[[385707257,137796857],[295065017,47154617]]],[[[1725037626,1229216826],[1542591066,1046770266]],[[2522154372,1530512772],[2157261252,1165619652]],[[727391946,231571146],[544945386,49124586]]],[[[840473231,592562831],[748668911,500758511]],[[1216695502,720874702],[1033086862,537266062]],[[341359871,93449471],[249555551,1645151]]]]

private theorem identity_0265 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(1645151 / 991641600 : ℝ)) =
      tensor4 coefficients_0265 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0265, p_headsq] <;> ring

private theorem negative_0265 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0265 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0265] at hp
  linarith only [hp]

private def coefficients_0266 : List (List (List (List ℕ))) :=
  [[[[116419427,449760454,317846627],[25777187,268475974,227204387]],[[161740547,540402694,363167747],[71098307,359118214,272525507]]],[[[219611406,873066012,622465806],[37164846,508172892,440019246]],[[310834686,1055512572,713689086],[128388126,690619452,531242526]]],[[[103012421,422946442,304439621],[11208101,239337802,212635301]],[[148914581,514750762,350341781],[57110261,331142122,258537461]]]]

private theorem identity_0266 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(11208101 / 991641600 : ℝ)) =
      tensor4 coefficients_0266 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0266, p_coupled] <;> ring

private theorem negative_0266 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0266 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0266] at hp
  linarith only [hp]

private theorem node_0272 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0265 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0266 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0267 : List (List (List (List ℕ))) :=
  [[[[420155591,296200391],[397204511,273249311]],[[608185702,360275302],[562283542,314373142]],[[170598911,46643711],[147647831,23692631]]],[[[818265600,570355200],[772072920,524162520]],[[1171989720,676168920],[1079604360,583783560]],[[318861720,70951320],[272669040,24758640]]],[[[397947600,273992400],[374706000,250750800]],[[563479200,315568800],[516996000,269085600]],[[148100400,24145200],[124858800,903600]]]]

private theorem identity_0267 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(251 / 137728 : ℝ)) =
      tensor4 coefficients_0267 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0267, p_headsq] <;> ring

private theorem negative_0267 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0267 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0267] at hp
  linarith only [hp]

private def coefficients_0268 : List (List (List (List ℕ))) :=
  [[[[377836511,315858911],[354885431,292907831]],[[523547542,399592342],[477645382,353690182]],[[128279831,66302231],[105328751,43351151]]],[[[733336920,609381720],[687144240,563189040]],[[1002132360,754221960],[909747000,661836600]],[[233933040,109977840],[187740360,63785160]]],[[[355338000,293360400],[332096400,270118800]],[[478260000,354304800],[431776800,307821600]],[[105490800,43513200],[82249200,20271600]]]]

private theorem identity_0268 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(5631 / 137728 : ℝ)) =
      tensor4 coefficients_0268 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0268, p_headsq] <;> ring

private theorem negative_0268 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0268 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0268] at hp
  linarith only [hp]

private def coefficients_0269 : List (List (List (List ℕ))) :=
  [[[[47103701,144564202,95523701],[24152621,98662042,72572621]],[[70054781,190466362,118474781],[47103701,144564202,95523701]]],[[[86833080,274379760,183673080],[40640400,181994400,137480400]],[[133025760,366765120,229865760],[86833080,274379760,183673080]]],[[[39639600,129636000,88059600],[16398000,83152800,64818000]],[[62881200,176119200,111301200],[39639600,129636000,88059600]]]]

private theorem identity_0269 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(4555 / 137728 : ℝ)) =
      tensor4 coefficients_0269 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0269, p_coupled] <;> ring

private theorem negative_0269 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0269 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0269] at hp
  linarith only [hp]

private theorem node_0275 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0268 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0269 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0274 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0267 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0275 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0270 : List (List (List (List ℕ))) :=
  [[[[55238261,218937322,155951861],[9336101,127133002,110049701]],[[78189341,264839482,178902941],[32287181,173035162,133000781]]],[[[103683240,424288080,305110440],[11297880,239517360,212725080]],[[149875920,516673440,351303120],[57490560,331902720,258917760]]],[[[48355200,205171200,149068800],[1872000,112204800,102585600]],[[71596800,251654400,172310400],[25113600,158688000,125827200]]]]

private theorem identity_0270 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(65 / 17216 : ℝ)) =
      tensor4 coefficients_0270 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0270, p_coupled] <;> ring

private theorem negative_0270 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0270 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0270] at hp
  linarith only [hp]

private theorem node_0273 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0274 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0270 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0271 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 32 : ℝ)
  · exact node_0272 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0273 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0270 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0264 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0271 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0268 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0269 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0270 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0267 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0261 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0268 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0260 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 16 : ℝ)
  · exact node_0261 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0267 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0271 : List (List (List (List ℕ))) :=
  [[[[8621861,28864522,18305861],[3101981,17824762,12785981]],[[14141741,39904282,23825741],[8621861,28864522,18305861]]],[[[15607440,54456480,34975440],[4277160,31795920,23645160]],[[26937720,77117040,46305720],[15607440,54456480,34975440]]],[[[6895800,25412400,16579800],[1085400,13791600,10769400]],[[12706200,37033200,22390200],[6895800,25412400,16579800]]]]

private theorem identity_0271 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(603 / 17216 : ℝ)) =
      tensor4 coefficients_0271 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0271, p_coupled] <;> ring

private theorem negative_0271 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0271 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0271] at hp
  linarith only [hp]

private theorem node_0259 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0260 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0271 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0272 : List (List (List (List ℕ))) :=
  [[[[433400777,309445577],[389241737,265286537]],[[705272434,457362034],[616954354,369043954]],[[237009257,113054057],[192850217,68895017]]],[[[845730426,597820026],[756250266,508339866]],[[1367821572,872000772],[1188861252,693040452]],[[452366346,204455946],[362886186,114975786]]],[[[412004831,288049631],[366683711,242728511]],[[661899502,413989102],[571257262,323346862]],[[215032271,91077071],[169711151,45755951]]]]

private theorem identity_0272 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(45755951 / 247910400 : ℝ)) =
      tensor4 coefficients_0272 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0272, p_headsq] <;> ring

private theorem negative_0272 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0272 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0272] at hp
  linarith only [hp]

private def coefficients_0273 : List (List (List (List ℕ))) :=
  [[[[1005015913,757105513],[916697833,668787433]],[[1547523986,1051703186],[1370887826,875067026]],[[507645673,259735273],[419327593,171417193]]],[[[1966727490,1470906690],[1788929250,1293108450]],[[3007858260,2016216660],[2652261780,1660620180]],[[971405970,475585170],[793607730,297786930]]],[[[961386759,713476359],[871906599,623996199]],[[1459684638,963863838],[1280724318,784903518]],[[463435479,215525079],[373955319,126044919]]]]

private theorem identity_0273 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(14004991 / 110182400 : ℝ)) =
      tensor4 coefficients_0273 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0273, p_headsq] <;> ring

private theorem negative_0273 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0273 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0273] at hp
  linarith only [hp]

private def coefficients_0274 : List (List (List (List ℕ))) :=
  [[[[43376728,92958808],[1000148336,1099312496],[984661528,1034243608]],[[536478416,635642576],[2932284832,3130613152],[2451586256,2550750416]],[[500074168,549656248],[1946081456,2045245616],[1473897208,1523479288]]],[[[186829168,285993328],[2208001616,2406329936],[2076952288,2176116448]],[[1276885016,1475213336],[6287533072,6684189712],[5122207736,5320536056]],[[1104000808,1203164968],[4107421376,4305749696],[3059200408,3158364568]]],[[[143798441,193380521],[1208545282,1307709442],[1092636761,1142218841]],[[741098602,840262762],[3356632244,3554960564],[2671313482,2770477642]],[[604272641,653854721],[2162031922,2261196082],[1585649201,1635231281]]]]

private theorem identity_0274 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(5422091 / 86768640 : ℝ)) =
      tensor4 coefficients_0274 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0274, p_variance] <;> ring

private theorem negative_0274 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0274 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0274] at hp
  linarith only [hp]

private theorem node_0282 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0273 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0274 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0275 : List (List (List (List ℕ))) :=
  [[[[492198857,368243657],[447458777,323503577]],[[752853274,504942874],[663373114,415462714]],[[243223217,119268017],[198483137,74527937]]],[[[962420728,714510328],[872359528,624449128]],[[1461462056,965641256],[1281339656,785518856]],[[464178928,216268528],[374117728,126207328]]],[[[470059462,346104262],[424738342,300783142]],[[708283964,460373564],[617641724,369731324]],[[220793302,96838102],[175472182,51516982]]]]

private theorem identity_0275 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(25758491 / 247910400 : ℝ)) =
      tensor4 coefficients_0275 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0275, p_headsq] <;> ring

private theorem negative_0275 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0275 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0275] at hp
  linarith only [hp]

private def coefficients_0276 : List (List (List (List ℕ))) :=
  [[[[187175169,286339329],[2216247138,2414575458],[2084851809,2184015969]],[[1281353778,1479682098],[6311577636,6708234276],[5141783538,5340111858]],[[1108123569,1207287729],[4123220418,4321548738],[3070876689,3170040849]]],[[[575885766,774214086],[4850672172,5247328812],[4386346086,4584674406]],[[2973331932,3369988572],[13474618104,14267931384],[10724405532,11121062172]],[[2425336086,2623664406],[8679725772,9076382412],[6365949366,6564277686]]],[[[389402599,488566759],[2635809038,2834137358],[2302186279,2401350439]],[[1693362158,1891690478],[7165808476,7562465116],[5584005998,5782334318]],[[1317904519,1417068679],[4557889358,4756217678],[3295764679,3394928839]]]]

private theorem identity_0276 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(20797241 / 154255360 : ℝ)) =
      tensor4 coefficients_0276 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0276, p_variance] <;> ring

private theorem negative_0276 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0276 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0276] at hp
  linarith only [hp]

private theorem node_0283 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0275 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0276 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0281 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 32 : ℝ)
  · exact node_0282 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0283 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0277 : List (List (List (List ℕ))) :=
  [[[[881060713,633150313],[792742633,544832233]],[[1299613586,803792786],[1122977426,627156626]],[[383690473,135780073],[295372393,47461993]]],[[[1718817090,1222996290],[1541018850,1045198050]],[[2512037460,1520395860],[2156440980,1164799380]],[[723495570,227674770],[545697330,49876530]]],[[[837431559,589521159],[747951399,500040999]],[[1211774238,715953438],[1032813918,536993118]],[[339480279,91569879],[250000119,2089719]]]]

private theorem identity_0277 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(232191 / 110182400 : ℝ)) =
      tensor4 coefficients_0277 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0277, p_headsq] <;> ring

private theorem negative_0277 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0277 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0277] at hp
  linarith only [hp]

private def coefficients_0278 : List (List (List (List ℕ))) :=
  [[[[68167768,117749848],[1049730416,1148894576],[1009452568,1059034648]],[[586060496,685224656],[3031448992,3229777312],[2501168336,2600332496]],[[524865208,574447288],[1995663536,2094827696],[1498688248,1548270328]]],[[[236411248,335575408],[2307165776,2505494096],[2126534368,2225698528]],[[1376049176,1574377496],[6485861392,6882518032],[5221371896,5419700216]],[[1153582888,1252747048],[4206585536,4404913856],[3108782488,3207946648]]],[[[168589481,218171561],[1258127362,1357291522],[1117427801,1167009881]],[[790680682,889844842],[3455796404,3654124724],[2720895562,2820059722]],[[629063681,678645761],[2211614002,2310778162],[1610440241,1660022321]]]]

private theorem identity_0278 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(8520971 / 86768640 : ℝ)) =
      tensor4 coefficients_0278 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0278, p_variance] <;> ring

private theorem negative_0278 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0278 ((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0278] at hp
  linarith only [hp]

private theorem node_0285 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0277 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0278 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0279 : List (List (List (List ℕ))) :=
  [[[[418890977,294935777],[396520937,272565737]],[[606237514,358327114],[561497434,313587034]],[[169915337,45960137],[147545297,23590097]]],[[[815804968,567894568],[770774368,522863968]],[[1168230536,672409736],[1078169336,582348536]],[[317563168,69652768],[272532568,24622168]]],[[[396751582,272796382],[374091022,250135822]],[[561668204,313757804],[516347084,268436684]],[[147485422,23530222],[124824862,869662]]]]

private theorem identity_0279 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(434831 / 247910400 : ℝ)) =
      tensor4 coefficients_0279 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0279, p_headsq] <;> ring

private theorem negative_0279 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0279 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0279] at hp
  linarith only [hp]

private def coefficients_0280 : List (List (List (List ℕ))) :=
  [[[[241405569,340569729],[1399111218,1597439538],[1171650609,1270814769]],[[1394462898,1592791218],[4654064196,5050720836],[3287491218,3485819538]],[[1167002289,1266166449],[3282842898,3481171218],[2129785569,2228949729]]],[[[684346566,882674886],[3208846812,3605503452],[2552390166,2750718486]],[[3199550172,3596206812],[10144484184,10937797464],[7000713852,7397370492]],[[2543093526,2741421846],[6991417212,7388073852],[4476213606,4674541926]]],[[[443632999,542797159],[1811119598,2009447918],[1381431559,1480595719]],[[1806471278,2004799598],[5493187996,5889844636],[3714606638,3912934958]],[[1376783239,1475947399],[3709958318,3908286638],[2347120039,2446284199]]]]

private theorem identity_0280 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(26822841 / 154255360 : ℝ)) =
      tensor4 coefficients_0280 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0280, p_variance] <;> ring

private theorem negative_0280 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0280 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0280] at hp
  linarith only [hp]

private theorem node_0287 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0279 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0280 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0281 : List (List (List (List ℕ))) :=
  [[[[236757249,335921409],[2315411298,2513739618],[2134433889,2233598049]],[[1380517938,1578846258],[6509905956,6906562596],[5240947698,5439276018]],[[1157705649,1256869809],[4222384578,4420712898],[3120458769,3219622929]]],[[[675049926,873378246],[5049000492,5445657132],[4485510246,4683838566]],[[3171660252,3568316892],[13871274744,14664588024],[10922733852,11319390492]],[[2524500246,2722828566],[8878054092,9274710732],[6465113526,6663441846]]],[[[438984679,538148839],[2734973198,2933301518],[2351768359,2450932519]],[[1792526318,1990854638],[7364136796,7760793436],[5683170158,5881498478]],[[1367486599,1466650759],[4657053518,4855381838],[3345346759,3444510919]]]]

private theorem identity_0281 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(26306361 / 154255360 : ℝ)) =
      tensor4 coefficients_0281 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0281, p_variance] <;> ring

private theorem negative_0281 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0281 ((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0281] at hp
  linarith only [hp]

private theorem node_0286 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0287 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0281 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0284 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 32 : ℝ)
  · exact node_0285 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0286 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0280 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0281 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0284 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0282 : List (List (List (List ℕ))) :=
  [[[[69093442,93884482],[372346004,421928084],[310225042,335016082]],[[372346004,421928084],[1229279368,1328443528],[870878324,920460404]],[[310225042,335016082],[870878324,920460404],[567625762,592416802]]],[[[190113120,239695200],[852321240,951485400],[676153080,725735160]],[[852321240,951485400],[2681370720,2879699040],[1856939400,1956103560]],[[676153080,725735160],[1856939400,1956103560],[1194731280,1244313360]]],[[[121365679,146156719],[480667238,530249318],[366274039,391065079]],[[480667238,530249318],[1453475356,1552639516],[986753078,1036335158]],[[366274039,391065079],[986753078,1036335158],[627451519,652242559]]]]

private theorem identity_0282 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(34546721 / 86768640 : ℝ)) =
      tensor4 coefficients_0282 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0282, p_variance] <;> ring

private theorem negative_0282 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0282 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0282] at hp
  linarith only [hp]

private theorem node_0279 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0280 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0282 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0278 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0272 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0279 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0283 : List (List (List (List ℕ))) :=
  [[[[211949591,149971991],[189289031,127311431]],[[342844102,218888902],[297522982,173567782]],[[113463311,51485711],[90802751,28825151]]],[[[413038800,289083600],[367136640,243181440]],[[663676920,415766520],[571872600,323962200]],[[215775720,91820520],[169873560,45918360]]],[[[200926800,138949200],[177685200,115707600]],[[320508000,196552800],[274024800,150069600]],[[102150000,40172400],[78908400,16930800]]]]

private theorem identity_0283 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(4703 / 34432 : ℝ)) =
      tensor4 coefficients_0283 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0283, p_headsq] <;> ring

private theorem negative_0283 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0283 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0283] at hp
  linarith only [hp]

private def coefficients_0284 : List (List (List (List ℕ))) :=
  [[[[963454697,715544297],[872812457,624902057]],[[1463239474,967418674],[1281954994,786134194]],[[464922377,217011977],[374280137,126369737]]],[[[1882305786,1386484986],[1699859226,1204038426]],[[2836690692,1845049092],[2471797572,1480155972]],[[884660106,388839306],[702213546,206392746]]],[[[918526271,670615871],[826721951,578811551]],[[1372801582,876980782],[1189192942,693372142]],[[419412911,171502511],[327608591,79698191]]]]

private theorem identity_0284 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(79698191 / 991641600 : ℝ)) =
      tensor4 coefficients_0284 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0284, p_headsq] <;> ring

private theorem negative_0284 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0284 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0284] at hp
  linarith only [hp]

private def coefficients_0285 : List (List (List (List ℕ))) :=
  [[[[144144442,193726522],[1216790804,1315954964],[1100536282,1150118362]],[[745567364,844731524],[3380676808,3579005128],[2690889284,2790053444]],[[608395402,657977482],[2177830964,2276995124],[1597325482,1646907562]]],[[[389748600,488912760],[2644054560,2842382880],[2310085800,2409249960]],[[1697830920,1896159240],[7189853040,7586509680],[5603581800,5801910120]],[[1322027280,1421191440],[4573688400,4772016720],[3307440960,3406605120]]],[[[245950159,295532239],[1427955758,1527119918],[1209895519,1259477599]],[[952955558,1052119718],[3810560236,4008888556],[2913384518,3012548678]],[[713977879,763559959],[2396549438,2495713598],[1710461479,1760043559]]]]

private theorem identity_0285 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(72072221 / 347074560 : ℝ)) =
      tensor4 coefficients_0285 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0285, p_variance] <;> ring

private theorem negative_0285 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0285 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0285] at hp
  linarith only [hp]

private theorem node_0292 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0284 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0285 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0286 : List (List (List (List ℕ))) :=
  [[[[471093431,347138231],[425191271,301236071]],[[710061382,462150982],[618257062,370346662]],[[221536751,97581551],[175634591,51679391]]],[[[919560240,671649840],[827174880,579264480]],[[1374579000,878758200],[1189808280,693987480]],[[420156360,172245960],[327771000,79860600]]],[[[448304400,324349200],[401821200,277866000]],[[664192800,416282400],[571226400,323316000]],[[198457200,74502000],[151974000,28018800]]]]

private theorem identity_0286 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(7783 / 137728 : ℝ)) =
      tensor4 coefficients_0286 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0286, p_headsq] <;> ring

private theorem negative_0286 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0286 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0286] at hp
  linarith only [hp]

private def coefficients_0287 : List (List (List (List ℕ))) :=
  [[[[390094601,489258761],[2652300082,2850628402],[2317985321,2417149481]],[[1702299682,1900628002],[7213897604,7610554244],[5623157602,5821485922]],[[1326150041,1425314201],[4589487442,4787815762],[3319117241,3418281401]]],[[[984492638,1182820958],[5728314076,6124970716],[4855381118,5053709438]],[[3820759756,4217416396],[15290330072,16083643352],[11692689676,12089346316]],[[2864157038,3062485358],[9617795836,10014452476],[6865198478,7063526798]]],[[[595090039,694254199],[3077397998,3275726318],[2538087799,2637251959]],[[2119844078,2318172398],[8079200476,8475857116],[6070916078,6269244398]],[[1538698999,1637863159],[5029692398,5228020718],[3546773239,3645937399]]]]

private theorem identity_0287 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(390094601 / 1388298240 : ℝ)) =
      tensor4 coefficients_0287 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0287, p_variance] <;> ring

private theorem negative_0287 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0287 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0287] at hp
  linarith only [hp]

private theorem node_0293 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0286 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0287 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0291 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 32 : ℝ)
  · exact node_0292 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0293 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0288 : List (List (List (List ℕ))) :=
  [[[[754570817,630615617],[709249697,585294497]],[[1045471714,797561314],[954829474,706919074]],[[256038497,132083297],[210717377,86762177]]],[[[1464538026,1216627626],[1373314746,1125404346]],[[2001155172,1505334372],[1818708612,1322887812]],[[466892346,218981946],[375669066,127758666]]],[[[709642391,585687191],[663740231,539785031]],[[955033822,707123422],[863229502,615319102]],[[210529031,86573831],[164626871,40671671]]]]

private theorem identity_0288 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(40671671 / 991641600 : ℝ)) =
      tensor4 coefficients_0288 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0288, p_headsq] <;> ring

private theorem negative_0288 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0288 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0288] at hp
  linarith only [hp]

private def coefficients_0289 : List (List (List (List ℕ))) :=
  [[[[78651827,258017254,175491827],[33330707,167375014,130170707]],[[123972947,348659494,220812947],[78651827,258017254,175491827]]],[[[142333086,486093372,336013086],[51109806,303646812,244789806]],[[233556366,668539932,427236366],[142333086,486093372,336013086]]],[[[63501701,227717002,160341701],[17599541,135912682,114439541]],[[109403861,319521322,206243861],[63501701,227717002,160341701]]]]

private theorem identity_0289 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(17599541 / 991641600 : ℝ)) =
      tensor4 coefficients_0289 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0289, p_coupled] <;> ring

private theorem negative_0289 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0289 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0289] at hp
  linarith only [hp]

private theorem node_0297 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0288 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0289 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0290 : List (List (List (List ℕ))) :=
  [[[[171259642,220841722],[804446084,903610244],[640158922,689741002]],[[802121924,901286084],[2544366568,2742694888],[1756189604,1855353764]],[[637834762,687416842],[1753865444,1853029604],[1123003162,1172585242]]],[[[443979000,543143160],[1815588360,2013916680],[1385554320,1484718480]],[[1810940040,2009268360],[5509679040,5906335680],[3726628920,3924957240]],[[1380906000,1480070160],[3721980600,3920308920],[2355019560,2454183720]]],[[[273065359,322647439],[1011834278,1110998438],[745741399,795323479]],[[1009510118,1108674278],[2966696476,3165024796],[1971131318,2070295478]],[[743417239,792999319],[1968807158,2067971318],[1232362399,1281944479]]]]

private theorem identity_0290 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(85629821 / 347074560 : ℝ)) =
      tensor4 coefficients_0290 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0290, p_variance] <;> ring

private theorem negative_0290 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0290 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0290] at hp
  linarith only [hp]

private theorem node_0296 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0297 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0290 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0291 : List (List (List (List ℕ))) :=
  [[[[168935482,218517562],[1266372884,1365537044],[1125327322,1174909402]],[[795149444,894313604],[3479840968,3678169288],[2740471364,2839635524]],[[633186442,682768522],[2227413044,2326577204],[1622116522,1671698602]]],[[[439330680,538494840],[2743218720,2941547040],[2359667880,2458832040]],[[1796995080,1995323400],[7388181360,7784838000],[5702745960,5901074280]],[[1371609360,1470773520],[4672852560,4871180880],[3357023040,3456187200]]],[[[270741199,320323279],[1477537838,1576701998],[1234686559,1284268639]],[[1002537638,1101701798],[3909724396,4108052716],[2962966598,3062130758]],[[738768919,788350999],[2446131518,2545295678],[1735252519,1784834599]]]]

private theorem identity_0291 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(84467741 / 347074560 : ℝ)) =
      tensor4 coefficients_0291 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0291, p_variance] <;> ring

private theorem negative_0291 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0291 ((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0291] at hp
  linarith only [hp]

private theorem node_0295 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0296 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0291 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0292 : List (List (List (List ℕ))) :=
  [[[[366506231,304528631],[343555151,281577551]],[[500886982,376931782],[454984822,331029622]],[[116949551,54971951],[93998471,32020871]]],[[[710385840,586430640],[664193160,540237960]],[[956230200,708319800],[863844840,615934440]],[[210981960,87026760],[164789280,40834080]]],[[[343717200,281739600],[320475600,258498000]],[[455018400,331063200],[408535200,284580000]],[[93870000,31892400],[70628400,8650800]]]]

private theorem identity_0292 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(2403 / 137728 : ℝ)) =
      tensor4 coefficients_0292 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0292, p_headsq] <;> ring

private theorem negative_0292 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0292 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0292] at hp
  linarith only [hp]

private def coefficients_0293 : List (List (List (List ℕ))) :=
  [[[[35773421,121903642,84193421],[12822341,76001482,61242341]],[[58724501,167805802,107144501],[35773421,121903642,84193421]]],[[[63882000,228477600,160722000],[17689320,136092240,114529320]],[[110074680,320862960,206914680],[63882000,228477600,160722000]]],[[[28018800,106394400,76438800],[4777200,59911200,53197200]],[[51260400,152877600,99680400],[28018800,106394400,76438800]]]]

private theorem identity_0293 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(1327 / 137728 : ℝ)) =
      tensor4 coefficients_0293 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0293, p_coupled] <;> ring

private theorem negative_0293 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0293 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0293] at hp
  linarith only [hp]

private theorem node_0300 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0292 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0293 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0294 : List (List (List (List ℕ))) :=
  [[[[444325001,543489161],[1820057122,2018385442],[1389677081,1488841241]],[[1815408802,2013737122],[5526170084,5922826724],[3738651202,3936979522]],[[1385028761,1484192921],[3734002882,3932331202],[2362919081,2462083241]]],[[[1092953438,1291281758],[4056274636,4452931276],[2991211118,3189539438]],[[4046977996,4443634636],[11899767992,12693081272],[7908569836,8305226476]],[[2981914478,3180242798],[7899273196,8295929836],[4945248638,5143576958]]],[[[649320439,748484599],[2237601518,2435929838],[1602226039,1701390199]],[[2232953198,2431281518],[6376365916,6773022556],[4171302638,4369630958]],[[1597577719,1696741879],[4166654318,4364982638],[2583021559,2682185719]]]]

private theorem identity_0294 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(444325001 / 1388298240 : ℝ)) =
      tensor4 coefficients_0294 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0294, p_variance] <;> ring

private theorem negative_0294 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0294 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0294] at hp
  linarith only [hp]

private theorem node_0299 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact node_0300 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0294 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0295 : List (List (List (List ℕ))) :=
  [[[[439676681,538840841],[2751464242,2949792562],[2367567401,2466731561]],[[1801463842,1999792162],[7412225924,7808882564],[5722321762,5920650082]],[[1375732121,1474896281],[4688651602,4886979922],[3368699321,3467863481]]],[[[1083656798,1281985118],[5926642396,6323299036],[4954545278,5152873598]],[[4019088076,4415744716],[15686986712,16480299992],[11891017996,12287674636]],[[2963321198,3161649518],[9816124156,10212780796],[6964362638,7162690958]]],[[[644672119,743836279],[3176562158,3374890478],[2587669879,2686834039]],[[2219008238,2417336558],[8277528796,8674185436],[6170080238,6368408558]],[[1588281079,1687445239],[5128856558,5327184878],[3596355319,3695519479]]]]

private theorem identity_0295 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(439676681 / 1388298240 : ℝ)) =
      tensor4 coefficients_0295 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0295, p_variance] <;> ring

private theorem negative_0295 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0295 ((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0295] at hp
  linarith only [hp]

private theorem node_0298 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact node_0299 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0295 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0294 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 32 : ℝ)
  · exact node_0295 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0298 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0290 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0291 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0294 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0296 : List (List (List (List ℕ))) :=
  [[[[190459121,240041201],[856790002,955954162],[680275841,729857921]],[[856790002,955954162],[2697861764,2896190084],[1868961682,1968125842]],[[680275841,729857921],[1868961682,1968125842],[1202630801,1252212881]]],[[[486154718,585318878],[1931606476,2129934796],[1473341678,1572505838]],[[1931606476,2129934796],[5846883512,6243540152],[3971056876,4169385196]],[[1473341678,1572505838],[3971056876,4169385196],[2525605118,2624769278]]],[[[296387599,345969679],[1076200478,1175364638],[793757839,843339919]],[[1076200478,1175364638],[3151789756,3350118076],[2103479198,2202643358]],[[793757839,843339919],[2103479198,2202643358],[1323666319,1373248399]]]]

private theorem identity_0296 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(190459121 / 347074560 : ℝ)) =
      tensor4 coefficients_0296 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0296, p_variance] <;> ring

private theorem negative_0296 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0296 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0296] at hp
  linarith only [hp]

private theorem node_0289 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0290 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0296 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0288 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0283 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0289 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0277 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 16 : ℝ)
  · exact node_0278 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0288 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0297 : List (List (List (List ℕ))) :=
  [[[[32023187,157012774,109495187],[9943667,112853734,87415667]],[[54102707,201171814,131574707],[32023187,157012774,109495187]]],[[[56339166,298611132,211283166],[11599086,209130972,166543086]],[[101079246,388091292,256023246],[56339166,298611132,211283166]]],[[[24136421,141239242,101608421],[1475861,95918122,78947861]],[[46796981,186560362,124268981],[24136421,141239242,101608421]]]]

private theorem identity_0297 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(1475861 / 247910400 : ℝ)) =
      tensor4 coefficients_0297 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0297, p_coupled] <;> ring

private theorem negative_0297 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0297 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0297] at hp
  linarith only [hp]

private def coefficients_0298 : List (List (List (List ℕ))) :=
  [[[[318354857,256377257],[296275337,234297737]],[[475180594,351225394],[431021554,307066354]],[[121963337,59985737],[99883817,37906217]]],[[[615057546,491102346],[570317466,446362266]],[[906475812,658565412],[816995652,569085252]],[[221693466,97738266],[176953386,52998186]]],[[[296377871,234400271],[273717311,211739711]],[[430645582,306690382],[385324462,261369262]],[[99405311,37427711],[76744751,14767151]]]]

private theorem identity_0298 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(14767151 / 247910400 : ℝ)) =
      tensor4 coefficients_0298 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0298, p_headsq] <;> ring

private theorem negative_0298 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0298 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0298] at hp
  linarith only [hp]

private def coefficients_0299 : List (List (List (List ℕ))) :=
  [[[[42578747,123893494,77441147],[20499227,79734454,55361627]],[[64658267,168052534,99520667],[42578747,123893494,77441147]]],[[[76869246,231210492,146594046],[32129166,141730332,101853966]],[[121609326,320690652,191334126],[76869246,231210492,146594046]]],[[[34110941,106957882,68973341],[11450381,61636762,46312781]],[[56771501,152279002,91633901],[34110941,106957882,68973341]]]]

private theorem identity_0299 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(11450381 / 247910400 : ℝ)) =
      tensor4 coefficients_0299 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0299, p_coupled] <;> ring

private theorem negative_0299 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0299 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0299] at hp
  linarith only [hp]

private theorem node_0304 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0298 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0299 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0303 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0297 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0304 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0300 : List (List (List (List ℕ))) :=
  [[[[54102707,201171814,131574707],[9943667,112853734,87415667]],[[76182227,245330854,153654227],[32023187,157012774,109495187]]],[[[101079246,388091292,256023246],[11599086,209130972,166543086]],[[145819326,477571452,300763326],[56339166,298611132,211283166]]],[[[46796981,186560362,124268981],[1475861,95918122,78947861]],[[69457541,231881482,146929541],[24136421,141239242,101608421]]]]

private theorem identity_0300 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(1475861 / 247910400 : ℝ)) =
      tensor4 coefficients_0300 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0300, p_coupled] <;> ring

private theorem negative_0300 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0300 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0300] at hp
  linarith only [hp]

private theorem node_0302 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0303 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0300 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0301 : List (List (List (List ℕ))) :=
  [[[[159655991,128667191],[148325711,117336911]],[[238256902,176279302],[215596342,153618742]],[[61169711,30180911],[49839431,18850631]]],[[[308451600,246474000],[285500520,223522920]],[[454502520,330547320],[408600360,284645160]],[[111188520,49210920],[88237440,26259840]]],[[[148633200,117644400],[137012400,106023600]],[[215920800,153943200],[192679200,130701600]],[[49856400,18867600],[38235600,7246800]]]]

private theorem identity_0301 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(2013 / 34432 : ℝ)) =
      tensor4 coefficients_0301 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0301, p_headsq] <;> ring

private theorem negative_0301 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0301 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0301] at hp
  linarith only [hp]

private def coefficients_0302 : List (List (List (List ℕ))) :=
  [[[[24927341,69222682,42358541],[13597061,46562122,31028261]],[[36257621,91883242,53688821],[24927341,69222682,42358541]]],[[[45821520,130379040,80683920],[22870440,84476880,57732840]],[[68772600,176281200,103635000],[45821520,130379040,80683920]]],[[[20804400,60976800,38235600],[9183600,37735200,26614800]],[[32425200,84218400,49856400],[20804400,60976800,38235600]]]]

private theorem identity_0302 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(2551 / 34432 : ℝ)) =
      tensor4 coefficients_0302 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0302, p_coupled] <;> ring

private theorem negative_0302 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0302 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0302] at hp
  linarith only [hp]

private theorem node_0307 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0301 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0302 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0303 : List (List (List (List ℕ))) :=
  [[[[154136111,123147311],[142805831,111817031]],[[227217142,165239542],[204556582,142578982]],[[55649831,24661031],[44319551,13330751]]],[[[297121320,235143720],[274170240,212192640]],[[431841960,307886760],[385939800,261984600]],[[99858240,37880640],[76907160,14929560]]],[[[142822800,111834000],[131202000,100213200]],[[204300000,142322400],[181058400,119080800]],[[44046000,13057200],[32425200,1436400]]]]

private theorem identity_0303 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(399 / 34432 : ℝ)) =
      tensor4 coefficients_0303 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0303, p_headsq] <;> ring

private theorem negative_0303 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0303 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0303] at hp
  linarith only [hp]

private def coefficients_0304 : List (List (List (List ℕ))) :=
  [[[[19407461,58182922,36838661],[8077181,35522362,25508381]],[[30737741,80843482,48168941],[19407461,58182922,36838661]]],[[[34491240,107718480,69353640],[11540160,61816320,46402560]],[[57442320,153620640,92304720],[34491240,107718480,69353640]]],[[[14994000,49356000,32425200],[3373200,26114400,20804400]],[[26614800,72597600,44046000],[14994000,49356000,32425200]]]]

private theorem identity_0304 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(937 / 34432 : ℝ)) =
      tensor4 coefficients_0304 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0304, p_coupled] <;> ring

private theorem negative_0304 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0304 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0304] at hp
  linarith only [hp]

private theorem node_0308 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0303 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0304 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0306 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0307 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0308 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0305 : List (List (List (List ℕ))) :=
  [[[[19794821,86072842,58530821],[8464541,63412282,47200541]],[[31125101,108733402,69861101],[19794821,86072842,58530821]]],[[[35847000,164660400,113319000],[12895920,118758240,90367920]],[[58798080,210562560,136270080],[35847000,164660400,113319000]]],[[[15962400,78408000,54698400],[4341600,55166400,43077600]],[[27583200,101649600,66319200],[15962400,78408000,54698400]]]]

private theorem identity_0305 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(603 / 17216 : ℝ)) =
      tensor4 coefficients_0305 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0305, p_coupled] <;> ring

private theorem negative_0305 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0305 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0305] at hp
  linarith only [hp]

private def coefficients_0306 : List (List (List (List ℕ))) :=
  [[[[215250161,264832241],[906372082,1005536242],[705066881,754648961]],[[906372082,1005536242],[2797025924,2995354244],[1918543762,2017707922]],[[705066881,754648961],[1918543762,2017707922],[1227421841,1277003921]]],[[[535736798,634900958],[2030770636,2229098956],[1522923758,1622087918]],[[2030770636,2229098956],[6045211832,6441868472],[4070221036,4268549356]],[[1522923758,1622087918],[4070221036,4268549356],[2575187198,2674351358]]],[[[321178639,370760719],[1125782558,1224946718],[818548879,868130959]],[[1125782558,1224946718],[3250953916,3449282236],[2153061278,2252225438]],[[818548879,868130959],[2153061278,2252225438],[1348457359,1398039439]]]]

private theorem identity_0306 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(30750023 / 49582080 : ℝ)) =
      tensor4 coefficients_0306 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0306, p_variance] <;> ring

private theorem negative_0306 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0306 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0306] at hp
  linarith only [hp]

private theorem node_0309 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0305 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0306 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0305 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0306 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0309 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0301 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 16 : ℝ)
  · exact node_0302 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0305 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0276 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0277 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0301 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0258 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0259 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0276 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0253 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0258 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0307 : List (List (List (List ℕ))) :=
  [[[[3897851,11669302,5834651],[1283171,6439942,3219971]],[[6512531,16898662,8449331],[3897851,11669302,5834651]]],[[[6922080,21591360,10795680],[1402200,10551600,5275800]],[[12441960,32631120,16315560],[6922080,21591360,10795680]]],[[[2934450,9742500,4871250],[29250,3932100,1966050]],[[5839650,15552900,7776450],[2934450,9742500,4871250]]]]

private theorem identity_0307 (x0 x1 x2 x3 : ℝ) :
    (7747200 : ℝ)*(-p_coupled x0 x1 x2 x3-(65 / 17216 : ℝ)) =
      tensor4 coefficients_0307 ((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0307, p_coupled] <;> ring

private theorem negative_0307 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0307 ((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0307] at hp
  linarith only [hp]

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.coupled) (negative_0307 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part07
