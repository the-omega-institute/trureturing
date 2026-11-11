/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part22Node0968
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part22Node0968
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part22Node0968.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part22Node0968
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0964 : List (List (List (List ℕ))) :=
  [[[[97015927,66027127],[83361487,52372687]],[[180377414,118399814],[153068534,91090934]],[[65930287,34941487],[52275847,21287047]]],[[[181153968,119176368],[153554568,91576968]],[[334708536,210753336],[279509736,155554536]],[[118692168,56714568],[91092768,29115168]]],[[[83975632,52986832],[70030672,39041872]],[[154006304,92028704],[126116384,64138784]],[[52599472,21610672],[38654512,7665712]]]]

private theorem identity_0964 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(479107 / 7747200 : ℝ)) =
      tensor4 coefficients_0964 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0964, p_headsq] <;> ring

private theorem negative_0964 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0964 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0964] at hp
  linarith only [hp]

private def coefficients_0965 : List (List (List (List ℕ))) :=
  [[[[7,11],[1,5]]]]

private theorem identity_0965 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0965 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0965, p_qbox] <;> ring

private theorem negative_0965 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0965 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0965] at hp
  linarith only [hp]

private theorem node_0970 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0964 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qbox) (negative_0965 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0966 : List (List (List (List ℕ))) :=
  [[[[90333967,59345167],[76679527,45690727]],[[167013494,105035894],[139704614,77727014]],[[59248327,28259527],[45593887,14605087]]],[[[167499528,105521928],[139900128,77922528]],[[307399656,183444456],[252200856,128245656]],[[105037728,43060128],[77438328,15460728]]],[[[77003152,46014352],[63058192,32069392]],[[140061344,78083744],[112171424,50193824]],[[45626992,14638192],[31682032,693232]]]]

private theorem identity_0966 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(43327 / 7747200 : ℝ)) =
      tensor4 coefficients_0966 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0966, p_headsq] <;> ring

private theorem negative_0966 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0966 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0966] at hp
  linarith only [hp]

private def coefficients_0967 : List (List (List (List ℕ))) :=
  [[[[463238017,215327617],[408620257,160709857]],[[871858274,376037474],[762622754,266801954]],[[373757857,125847457],[319140097,71229697]]],[[[873802410,377981610],[763985850,268165050]],[[1637788260,646146660],[1418155140,426513540]],[[694261050,198440250],[584444490,88623690]]],[[[410239575,162329175],[355040775,107130375]],[[765280350,269459550],[654882750,159061950]],[[320178375,72267975],[264979575,17069175]]]]

private theorem identity_0967 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(75863 / 4407296 : ℝ)) =
      tensor4 coefficients_0967 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0967, p_headsq] <;> ring

private theorem negative_0967 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0967 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0967] at hp
  linarith only [hp]

private def coefficients_0968 : List (List (List (List ℕ))) :=
  [[[[130487098,180069178],[713604356,812768516],[590089738,639671818]],[[729873476,829037636],[2381276392,2579604712],[1665347876,1764512036]],[[606358858,655940938],[1681616996,1780781156],[1082230618,1131812698]]],[[[358398904,457563064],[1625834888,1824163208],[1281380944,1380545104]],[[1658373128,1856701448],[5167358656,5564015296],[3536875448,3735203768]],[[1313919184,1413083344],[3569413688,3767742008],[2269439464,2368603624]]],[[[228257807,277839887],[912922534,1012086694],[691637207,741219287]],[[929191654,1028355814],[2787466268,2985794588],[1872219574,1971383734]],[[707906327,757488407],[1888488694,1987652854],[1187554847,1237136927]]]]

private theorem identity_0968 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(9320507 / 49582080 : ℝ)) =
      tensor4 coefficients_0968 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0968, p_variance] <;> ring

private theorem negative_0968 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0968 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0968] at hp
  linarith only [hp]

private theorem node_0974 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0967 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0968 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0969 : List (List (List (List ℕ))) :=
  [[[[137459578,187041658],[1184827796,1283991956],[1075258138,1124840218]],[[741494276,840658436],[3335344072,3533672392],[2649629636,2748793796]],[[611007178,660589258],[2164461236,2263625396],[1581343978,1630926058]]],[[[372343864,471508024],[2572058528,2770386848],[2255494504,2354658664]],[[1681614728,1879943048],[7083047536,7479704176],[5512992488,5711320808]],[[1323215824,1422379984],[4538878928,4737207248],[3271442944,3370607104]]],[[[235230287,284812367],[1387922734,1487086894],[1180582367,1230164447]],[[940812454,1039976614],[3749087468,3947415788],[2864054854,2963219014]],[[712554647,762136727],[2375109694,2474273854],[1690444967,1740027047]]]]

private theorem identity_0969 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(68729789 / 347074560 : ℝ)) =
      tensor4 coefficients_0969 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0969, p_variance] <;> ring

private theorem negative_0969 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0969 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0969] at hp
  linarith only [hp]

private theorem node_0973 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0974 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0969 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0970 : List (List (List (List ℕ))) :=
  [[[[187833527,125855927],[160234127,98256527]],[[348067654,224112454],[292868854,168913654]],[[142802927,80825327],[115203527,53225927]]],[[[349005424,225050224],[293516104,169560904]],[[642521528,394611128],[531542888,283632488]],[[258653704,134698504],[203164384,79209184]]],[[[161009488,99031888],[133119568,71141968]],[[294129056,170173856],[238349216,114394016]],[[115688368,53710768],[87798448,25820848]]]]

private theorem identity_0970 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1613803 / 30988800 : ℝ)) =
      tensor4 coefficients_0970 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0970, p_headsq] <;> ring

private theorem negative_0970 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (11 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0970 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0970] at hp
  linarith only [hp]

private def coefficients_0971 : List (List (List (List ℕ))) :=
  [[[[7,11],[1,5]]]]

private theorem identity_0971 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 32 : ℝ)) =
      tensor4 coefficients_0971 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(11 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0971, p_qbox] <;> ring

private theorem negative_0971 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (11 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0971 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(11 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(11 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0971] at hp
  linarith only [hp]

private theorem node_0977 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (11 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0970 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qbox) (negative_0971 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0972 : List (List (List (List ℕ))) :=
  [[[[358744905,457909065],[1630303650,1828631970],[1285503705,1384667865]],[[1662841890,1861170210],[5183849700,5580506340],[3548897730,3747226050]],[[1318041945,1417206105],[3581435970,3779764290],[2277338985,2376503145]]],[[[913723230,1112051550],[3660627660,4057284300],[2774794350,2973122670]],[[3725704140,4122360780],[11182847160,11976160440],[7512922860,7909579500]],[[2839870830,3038199150],[7577999340,7974655980],[4766018430,4964346750]]],[[[555670327,654834487],[2031708014,2230036334],[1489982647,1589146807]],[[2064246254,2262574574],[6001765468,6398422108],[3965409134,4163737454]],[[1522520887,1621685047],[3997947374,4196275694],[2489371447,2588535607]]]]

private theorem identity_0972 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(7972109 / 30851072 : ℝ)) =
      tensor4 coefficients_0972 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0972, p_variance] <;> ring

private theorem negative_0972 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0972 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0972] at hp
  linarith only [hp]

private theorem node_0976 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact node_0977 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0972 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0973 : List (List (List (List ℕ))) :=
  [[[[372689865,471854025],[2580304050,2778632370],[2263394025,2362558185]],[[1686083490,1884411810],[7107092100,7503748740],[5532568290,5730896610]],[[1327338585,1426502745],[4554677970,4753006290],[3283119225,3382283385]]],[[[941613150,1139941470],[5568181980,5964838620],[4738128510,4936456830]],[[3772187340,4168843980],[15044439000,15837752280],[11495371020,11892027660]],[[2858464110,3056792430],[9532036860,9928693500],[6785132430,6983460750]]],[[[569615287,668779447],[2989261934,3187590254],[2475426487,2574590647]],[[2087487854,2285816174],[7940114908,8336771548],[5964186734,6162515054]],[[1531817527,1630981687],[4978742894,5177071214],[3502705207,3601869367]]]]

private theorem identity_0973 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(8281997 / 30851072 : ℝ)) =
      tensor4 coefficients_0973 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0973, p_variance] <;> ring

private theorem negative_0973 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0973 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0973] at hp
  linarith only [hp]

private theorem node_0975 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0976 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0973 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0972 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 32 : ℝ)
  · exact node_0973 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0975 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0971 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0966 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0972 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0969 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0970 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0971 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0974 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0974 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 32 : ℝ)) =
      tensor4 coefficients_0974 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0974, p_qbox] <;> ring

private theorem negative_0974 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0974 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0974] at hp
  linarith only [hp]

private def coefficients_0975 : List (List (List (List ℕ))) :=
  [[[[117316858,166898938],[691912196,791076356],[581567818,631149898]],[[698884676,798048836],[2328595432,2526923752],[1643655716,1742819876]],[[588540298,638122378],[1650628196,1749792356],[1069060378,1118642458]]],[[[332058424,431222584],[1582450568,1780778888],[1264337104,1363501264]],[[1596395528,1794723848],[5061996736,5458653376],[3493491128,3691819448]],[[1278282064,1377446224],[3507436088,3705764408],[2243098984,2342263144]]],[[[215087567,264669647],[891230374,990394534],[683115287,732697367]],[[898202854,997367014],[2734785308,2933113628],[1850527414,1949691574]],[[690087767,739669847],[1857499894,1956664054],[1174384607,1223966687]]]]

private theorem identity_0975 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(58658429 / 347074560 : ℝ)) =
      tensor4 coefficients_0975 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0975, p_variance] <;> ring

private theorem negative_0975 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0975 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0975] at hp
  linarith only [hp]

private theorem node_0982 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0974 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0975 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0976 : List (List (List (List ℕ))) :=
  [[[[119641018,169223098],[1158487316,1257651476],[1066736218,1116318298]],[[701208836,800372996],[3273366472,3471694792],[2627937476,2727101636]],[[588540298,638122378],[2128824116,2227988276],[1568173738,1617755818]]],[[[336706744,435870904],[2519377568,2717705888],[2238450664,2337614824]],[[1601043848,1799372168],[6959092336,7355748976],[5469608168,5667936488]],[[1278282064,1377446224],[4467604688,4665933008],[3245102464,3344266624]]],[[[217411727,266993807],[1361582254,1460746414],[1172060447,1221642527]],[[900527014,999691174],[3687109868,3885438188],[2842362694,2941526854]],[[690087767,739669847],[2339472574,2438636734],[1677274727,1726856807]]]]

private theorem identity_0976 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(8545787 / 49582080 : ℝ)) =
      tensor4 coefficients_0976 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0976, p_variance] <;> ring

private theorem negative_0976 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0976 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0976] at hp
  linarith only [hp]

private theorem node_0981 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact node_0982 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0976 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0977 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0977 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 32 : ℝ)) =
      tensor4 coefficients_0977 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0977, p_qbox] <;> ring

private theorem negative_0977 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0977 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0977] at hp
  linarith only [hp]

private def coefficients_0978 : List (List (List (List ℕ))) :=
  [[[[332404425,431568585],[1586919330,1785247650],[1268459865,1367624025]],[[1600864290,1799192610],[5078487780,5475144420],[3505513410,3703841730]],[[1282404825,1381568985],[3519458370,3717786690],[2250998505,2350162665]]],[[[861042270,1059370590],[3573859020,3970515660],[2740706670,2939034990]],[[3601748940,3998405580],[10972123320,11765436600],[7426154220,7822810860]],[[2768596590,2966924910],[7454044140,7850700780],[4713337470,4911665790]]],[[[529329847,628494007],[1988323694,2186652014],[1472938807,1572102967]],[[2002268654,2200596974],[5896403548,6293060188],[3922024814,4120353134]],[[1486883767,1586047927],[3935969774,4134298094],[2463030967,2562195127]]]]

private theorem identity_0978 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(7386765 / 30851072 : ℝ)) =
      tensor4 coefficients_0978 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0978, p_variance] <;> ring

private theorem negative_0978 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0978 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0978] at hp
  linarith only [hp]

private theorem node_0984 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0977 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0978 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0979 : List (List (List (List ℕ))) :=
  [[[[337052745,436216905],[2527623090,2725951410],[2246350185,2345514345]],[[1605512610,1803840930],[6983136900,7379793540],[5489183970,5687512290]],[[1282404825,1381568985],[4483403730,4681732050],[3256778745,3355942905]]],[[[870338910,1068667230],[5462820060,5859476700],[4704040830,4902369150]],[[3611045580,4007702220],[14796528600,15589841880],[11408602380,11805259020]],[[2768596590,2966924910],[9389488380,9786145020],[6732451470,6930779790]]],[[[533978167,633142327],[2936580974,3134909294],[2458382647,2557546807]],[[2006916974,2205245294],[7816159708,8212816348],[5920802414,6119130734]],[[1486883767,1586047927],[4907468654,5105796974],[3476364727,3575528887]]]]

private theorem identity_0979 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(7490061 / 30851072 : ℝ)) =
      tensor4 coefficients_0979 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0979, p_variance] <;> ring

private theorem negative_0979 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0979 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0979] at hp
  linarith only [hp]

private theorem node_0983 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact node_0984 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0979 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0980 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 32 : ℝ)
  · exact node_0981 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0983 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0980 : List (List (List (List ℕ))) :=
  [[[[7,11],[1,5]]]]

private theorem identity_0980 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0980 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0980, p_qbox] <;> ring

private theorem negative_0980 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0980 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0980] at hp
  linarith only [hp]

private theorem node_0979 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact node_0980 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0980 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0981 : List (List (List (List ℕ))) :=
  [[[[174721169,224303249],[820665778,919829938],[659889569,709471649]],[[829962418,929126578],[2634909956,2833238276],[1832837458,1932001618]],[[669186209,718768289],[1842134098,1941298258],[1186892849,1236474929]]],[[[450643806,549807966],[1851288012,2049616332],[1428534126,1527698286]],[[1869881292,2068209612],[5704839864,6101496504],[3890738412,4089066732]],[[1447127406,1546291566],[3909331692,4107660012],[2490094206,2589258366]]],[[[276614639,326196719],[1032006238,1131170398],[769336559,818918639]],[[1041302878,1140467038],[3072697916,3271026236],[2059284958,2158449118]],[[778633199,828215279],[2068581598,2167745758],[1303893359,1353475439]]]]

private theorem identity_0981 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(24960167 / 49582080 : ℝ)) =
      tensor4 coefficients_0981 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0981, p_variance] <;> ring

private theorem negative_0981 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0981 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0981] at hp
  linarith only [hp]

private theorem node_0978 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0979 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0981 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0969 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0978 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part22Node0968
