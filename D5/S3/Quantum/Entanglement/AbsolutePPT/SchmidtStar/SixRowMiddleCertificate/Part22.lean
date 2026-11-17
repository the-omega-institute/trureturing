/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part22Node0985
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part22Node0968
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part22
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0950 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0950 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0950 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0950, p_qbox] <;> ring

private theorem negative_0950 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0950 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0950] at hp
  linarith only [hp]

private def coefficients_0951 : List (List (List (List ℕ))) :=
  [[[[205841473,143863873],[179113633,117136033]],[[384955106,260999906],[331499426,207544226]],[[144251233,82273633],[117523393,55545793]]],[[[386576810,262621610],[332540090,208584890]],[[719116900,471206500],[611043460,363133060]],[[262815290,138860090],[208778570,84823370]]],[[[180410519,118432919],[153101639,91124039]],[[333512158,209556958],[278894398,154939198]],[[118239239,56261639],[90930359,28952759]]]]

private theorem identity_0951 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(28952759 / 247910400 : ℝ)) =
      tensor4 coefficients_0951 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0951, p_headsq] <;> ring

private theorem negative_0951 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0951 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0951] at hp
  linarith only [hp]

private def coefficients_0952 : List (List (List (List ℕ))) :=
  [[[[7,11],[1,5]]]]

private theorem identity_0952 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0952 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0952, p_qbox] <;> ring

private theorem negative_0952 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0952 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0952] at hp
  linarith only [hp]

private theorem node_0958 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0951 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qbox) (negative_0952 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0953 : List (List (List (List ℕ))) :=
  [[[[192768073,130790473],[166040233,104062633]],[[358808306,234853106],[305352626,181397426]],[[131177833,69200233],[104449993,42472393]]],[[[359848970,235893770],[305812250,181857050]],[[665661220,417750820],[557587780,309677380]],[[236087450,112132250],[182050730,58095530]]],[[[166756079,104778479],[139447199,77469599]],[[306203278,182248078],[251585518,127630318]],[[104584799,42607199],[77275919,15298319]]]]

private theorem identity_0953 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(15298319 / 247910400 : ℝ)) =
      tensor4 coefficients_0953 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0953, p_headsq] <;> ring

private theorem negative_0953 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0953 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0953] at hp
  linarith only [hp]

private def coefficients_0954 : List (List (List (List ℕ))) :=
  [[[[540468649,292558249],[433557289,185646889]],[[1027481618,531660818],[813658898,317838098]],[[452150569,204240169],[345239209,97328809]]],[[[1029562946,533742146],[814578146,318757346]],[[1951633492,959991892],[1521663892,530022292]],[[852345746,356524946],[637360946,141540146]]],[[[488769479,240859079],[380696039,132785639]],[[923502238,427681438],[707355358,211534558]],[[399870359,151959959],[291796919,43886519]]]]

private theorem identity_0954 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(43886519 / 991641600 : ℝ)) =
      tensor4 coefficients_0954 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0954, p_headsq] <;> ring

private theorem negative_0954 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0954 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0954] at hp
  linarith only [hp]

private def coefficients_0955 : List (List (List (List ℕ))) :=
  [[[[40726872,90308952],[976255344,1075419504],[963418392,1013000472]],[[540475344,639639504],[2903092128,3101420448],[2418396624,2517560784]],[[506720952,556303032],[1940781744,2039945904],[1461950712,1511532792]]],[[[177494448,276658608],[2152145616,2350473936],[2030431008,2129595168]],[[1276808856,1475137176],[6213007632,6609664272],[5047758456,5246086776]],[[1113259368,1212423528],[4088751936,4287080256],[3031272408,3130436568]]],[[[137113577,186695657],[1176582274,1275746434],[1067358617,1116940697]],[[737025514,836189674],[3311299508,3509627828],[2630053834,2729217994]],[[606884417,656466497],[2148662194,2247826354],[1569667697,1619249777]]]]

private theorem identity_0955 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(565651 / 9640960 : ℝ)) =
      tensor4 coefficients_0955 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0955, p_variance] <;> ring

private theorem negative_0955 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0955 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0955] at hp
  linarith only [hp]

private theorem node_0961 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0954 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0955 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0956 : List (List (List (List ℕ))) :=
  [[[[257907721,133952521],[203871001,79915801]],[[488797082,240886682],[380723642,132813242]],[[213458161,89502961],[159421441,35466241]]],[[[489803448,241893048],[381148968,133238568]],[[925279656,429458856],[707970696,212149896]],[[400613808,152703408],[291959328,44048928]]],[[[231733318,107778118],[177115558,53160358]],[[436157756,188247356],[326922236,79011836]],[[186993238,63038038],[132375478,8420278]]]]

private theorem identity_0956 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(4210139 / 247910400 : ℝ)) =
      tensor4 coefficients_0956 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0956, p_headsq] <;> ring

private theorem negative_0956 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0956 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0956] at hp
  linarith only [hp]

private def coefficients_0957 : List (List (List (List ℕ))) :=
  [[[[177840449,277004609],[2160391138,2358719458],[2038330529,2137494689]],[[1281277618,1479605938],[6237052196,6633708836],[5067334258,5265662578]],[[1117382129,1216546289],[4104550978,4302879298],[3042948689,3142112849]]],[[[549146310,747474630],[4722820140,5119476780],[4285233510,4483561830]],[[2957039580,3353696220],[13293287160,14086600440],[10559366940,10956023580]],[[2435783190,2634111510],[8626246860,9022903500],[6302023350,6500351670]]],[[[371997863,471162023],[2563813006,2762141326],[2247594983,2346759143]],[[1677145966,1875474286],[7059002972,7455659612],[5493416686,5691745006]],[[1319093063,1418257223],[4523079886,4721408206],[3259766663,3358930823]]]]

private theorem identity_0957 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(177840449 / 1388298240 : ℝ)) =
      tensor4 coefficients_0957 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0957, p_variance] <;> ring

private theorem negative_0957 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0957 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0957] at hp
  linarith only [hp]

private theorem node_0962 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0956 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0957 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0960 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 32 : ℝ)
  · exact node_0961 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0962 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0959 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0953 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0960 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0957 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0958 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0959 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0958 : List (List (List (List ℕ))) :=
  [[[[664423849,416513449],[557512489,309602089]],[[1135942418,640121618],[922119698,426298898]],[[436656169,188745769],[329744809,81834409]]],[[[1277473346,781652546],[1062488546,566667746]],[[2168555092,1176913492],[1738585492,746943892]],[[821356946,325536146],[606372146,110551346]]],[[[612724679,364814279],[504651239,256740839]],[[1031963038,536142238],[815816158,319995358]],[[384375959,136465559],[276302519,28392119]]]]

private theorem identity_0958 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(28392119 / 991641600 : ℝ)) =
      tensor4 coefficients_0958 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0958, p_headsq] <;> ring

private theorem negative_0958 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0958 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0958] at hp
  linarith only [hp]

private def coefficients_0959 : List (List (List (List ℕ))) :=
  [[[[22908312,72490392],[949914864,1049079024],[954896472,1004478552]],[[500189904,599354064],[2841114528,3039442848],[2396704464,2495868624]],[[484254072,533836152],[1905144624,2004308784],[1448780472,1498362552]]],[[[141857328,241021488],[2099464656,2297792976],[2013387168,2112551328]],[[1196237976,1394566296],[6089052432,6485709072],[5004374136,5202702456]],[[1068325608,1167489768],[4017477696,4215806016],[3004931928,3104096088]]],[[[119295017,168877097],[1150241794,1249405954],[1058836697,1108418777]],[[696740074,795904234],[3249321908,3447650228],[2608361674,2707525834]],[[584417537,633999617],[2113025074,2212189234],[1556497457,1606079537]]]]

private theorem identity_0959 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(45453 / 1377280 : ℝ)) =
      tensor4 coefficients_0959 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0959, p_variance] <;> ring

private theorem negative_0959 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0959 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0959] at hp
  linarith only [hp]

private theorem node_0966 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0958 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0959 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0960 : List (List (List (List ℕ))) :=
  [[[[319885321,195930121],[265848601,141893401]],[[543027482,295117082],[434954042,187043642]],[[205710961,81755761],[151674241,27719041]]],[[[613758648,365848248],[505104168,257193768]],[[1033740456,537919656],[816431496,320610696]],[[385119408,137209008],[276464928,28554528]]],[[[293710918,169755718],[239093158,115137958]],[[490388156,242477756],[381152636,133242236]],[[179246038,55290838],[124628278,673078]]]]

private theorem identity_0960 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(336539 / 247910400 : ℝ)) =
      tensor4 coefficients_0960 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0960, p_headsq] <;> ring

private theorem negative_0960 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0960 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0960] at hp
  linarith only [hp]

private def coefficients_0961 : List (List (List (List ℕ))) :=
  [[[[142203329,241367489],[2107710178,2306038498],[2021286689,2120450849]],[[1200706738,1399035058],[6113096996,6509753636],[5023949938,5222278258]],[[1072448369,1171612529],[4033276738,4231605058],[3016608209,3115772369]]],[[[477872070,676200390],[4617458220,5014114860],[4251145830,4449474150]],[[2795897820,3192554460],[13045376760,13838690040],[10472598300,10869254940]],[[2345915670,2544243990],[8483698380,8880355020],[6249342390,6447670710]]],[[[336360743,435524903],[2511132046,2709460366],[2230551143,2329715303]],[[1596575086,1794903406],[6935047772,7331704412],[5450032366,5648360686]],[[1274159303,1373323463],[4451805646,4650133966],[3233426183,3332590343]]]]

private theorem identity_0961 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(142203329 / 1388298240 : ℝ)) =
      tensor4 coefficients_0961 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0961, p_variance] <;> ring

private theorem negative_0961 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0961 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0961] at hp
  linarith only [hp]

private theorem node_0967 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0960 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0961 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0965 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 32 : ℝ)
  · exact node_0966 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0967 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0962 : List (List (List (List ℕ))) :=
  [[[[7,11],[1,5]]]]

private theorem identity_0962 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0962 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0962, p_qbox] <;> ring

private theorem negative_0962 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0962 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0962] at hp
  linarith only [hp]

private theorem node_0964 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact node_0965 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0962 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0963 : List (List (List (List ℕ))) :=
  [[[[62233218,87024258],[356301396,405883476],[301040658,325831698]],[[360949716,410531796],[1201838472,1301002632],[854833716,904415796]],[[305688978,330480018],[859482036,909064116],[560765538,585556578]]],[[[174375168,223957248],[816197016,915361176],[655766808,705348888]],[[825493656,924657816],[2618418912,2816747232],[1820815176,1919979336]],[[665063448,714645528],[1830111816,1929275976],[1178993328,1228575408]]],[[[112487951,137278991],[460587622,510169702],[355072151,379863191]],[[465235942,514818022],[1417964444,1517128604],[966673462,1016255542]],[[359720471,384511511],[971321782,1020903862],[618573791,643364831]]]]

private theorem identity_0963 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(3457401 / 9640960 : ℝ)) =
      tensor4 coefficients_0963 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0963, p_variance] <;> ring

private theorem negative_0963 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0963 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0963] at hp
  linarith only [hp]

private theorem node_0963 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0964 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0963 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0956 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0957 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0963 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0955 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 16 : ℝ)
  · exact node_0956 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact SixRowMiddleCertificate.Subtrees.Part22Node0968.exclude x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0954 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0955 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact SixRowMiddleCertificate.Subtrees.Part22Node0985.exclude x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0953 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0950 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0954 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_1002 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_1002 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_1002 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1002, p_qbox] <;> ring

private theorem negative_1002 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1002 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1002] at hp
  linarith only [hp]

private def coefficients_1003 : List (List (List (List ℕ))) :=
  [[[[31697649,56488689],[297554418,347136498],[279801729,304592769]],[[297554418,347136498],[1095965316,1195129476],[826300818,875882898]],[[279801729,304592769],[826300818,875882898],[560444049,585235089]]],[[[113304030,162886110],[702479820,801643980],[617065710,666647790]],[[702479820,801643980],[2421779640,2620107960],[1775079660,1874243820]],[[617065710,666647790],[1775079660,1874243820],[1185903870,1235485950]]],[[[82298383,107089423],[406309406,455891486],[337955983,362747023]],[[406309406,455891486],[1328582332,1427746492],[950162846,999744926]],[[337955983,362747023],[950162846,999744926],[626151823,650942863]]]]

private theorem identity_1003 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(3521961 / 9640960 : ℝ)) =
      tensor4 coefficients_1003 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1003, p_variance] <;> ring

private theorem negative_1003 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1003 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1003] at hp
  linarith only [hp]

private theorem node_1004 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_1002 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_1003 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0953 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_1004 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_1004 : List (List (List (List ℕ))) :=
  [[[[112754929,81766129],[99972049,68983249]],[[212726978,150749378],[187161218,125183618]],[[65109649,34120849],[52326769,21337969]]],[[[213025386,151047786],[186878586,124900986]],[[399903972,275948772],[347610372,223655172]],[[117153786,55176186],[91006986,29029386]]],[[[99945639,68956839],[86581719,55592919]],[[186527358,124549758],[159799518,97821918]],[[51719319,20730519],[38355399,7366599]]]]

private theorem identity_1004 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(818511 / 6886400 : ℝ)) =
      tensor4 coefficients_1004 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1004, p_headsq] <;> ring

private theorem negative_1004 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1004 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1004] at hp
  linarith only [hp]

private def coefficients_1005 : List (List (List (List ℕ))) :=
  [[[[309541337,185586137],[258409817,134454617]],[[593516914,345606514],[491253874,243343474]],[[249113177,125157977],[197981657,74026457]]],[[[594113730,346203330],[490688610,242778210]],[[1136514900,640694100],[929664660,433843860]],[[472676370,224765970],[369251250,121340850]]],[[[284247575,160292375],[231953975,107998775]],[[542348350,294437950],[437761150,189850750]],[[223238375,99283175],[170944775,46989575]]]]

private theorem identity_1005 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(1879583 / 9916416 : ℝ)) =
      tensor4 coefficients_1005 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1005, p_headsq] <;> ring

private theorem negative_1005 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1005 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1005] at hp
  linarith only [hp]

private def coefficients_1006 : List (List (List (List ℕ))) :=
  [[[[116247928,141038968],[708948656,758530736],[620590648,645381688]],[[477694736,527276816],[1940833312,2039997472],[1518918416,1568500496]],[[368419288,393210328],[1245829616,1295411696],[905300248,930091288]]],[[[284797344,334379424],[1530053808,1629217968],[1301036304,1350618384]],[[1063769208,1162933368],[4113533136,4311861456],[3161323608,3260487768]],[[792916824,842498904],[2611369248,2710533408],[1874232264,1923814344]]],[[[168895417,193686457],[821797154,871379234],[680791657,705582697]],[[586766474,636348554],[2174083828,2273247988],[1643097194,1692679274]],[[424843537,449634577],[1366231634,1415813714],[969278017,994069057]]]]

private theorem identity_1006 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(14530991 / 21692160 : ℝ)) =
      tensor4 coefficients_1006 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1006, p_variance] <;> ring

private theorem negative_1006 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1006 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1006] at hp
  linarith only [hp]

private theorem node_1011 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_1005 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_1006 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_1007 : List (List (List (List ℕ))) :=
  [[[[43140185,92722265],[989216530,1088380690],[1001856185,1051438265]],[[1026403090,1125567250],[3988831460,4187159780],[3073988050,3173152210]],[[1039042745,1088624825],[3111174610,3210338770],[2127911705,2177493785]]],[[[184713830,283877990],[2190407020,2388735340],[2117252870,2216417030]],[[2264780140,2463108460],[8431824920,8828481560],[6390164140,6588492460]],[[2191625990,2290790150],[6464537260,6662865580],[4384470950,4483635110]]],[[[142265647,191847727],[1202574494,1301738654],[1116088687,1165670767]],[[1239761054,1338925214],[4445761468,4644089788],[3317560094,3416724254]],[[1153275247,1202857327],[3354746654,3453910814],[2257251247,2306833327]]]]

private theorem identity_1007 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(8628037 / 69414912 : ℝ)) =
      tensor4 coefficients_1007 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1007, p_variance] <;> ring

private theorem negative_1007 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1007 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1007] at hp
  linarith only [hp]

private theorem node_1010 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 16 : ℝ)
  · exact node_1011 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1007 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private theorem node_1009 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_1004 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_1010 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_1008 : List (List (List (List ℕ))) :=
  [[[[3],[15]],[[15],[27]]],[[[6],[18]],[[18],[30]]]]

private theorem identity_1008 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_1008 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1008, p_mass] <;> ring

private theorem negative_1008 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1008 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1008] at hp
  linarith only [hp]

private theorem node_1008 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 4 : ℝ)
  · exact node_1009 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_1008 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_1009 : List (List (List (List ℕ))) :=
  [[[[3],[27]],[[15],[39]]],[[[6],[30]],[[18],[42]]]]

private theorem identity_1009 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_mass x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_1009 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1009, p_mass] <;> ring

private theorem negative_1009 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_mass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1009 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1009] at hp
  linarith only [hp]

private theorem node_1007 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_1008 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.mass) (negative_1009 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_1010 : List (List (List (List ℕ))) :=
  [[[[16977969,41769009],[492977538,542559618],[531779409,556570449]],[[511570818,561152898],[2071337796,2170501956],[1671326658,1720908738]],[[550372689,575163729],[1689919938,1739502018],[1195327089,1220118129]]],[[[83864670,133446750],[1100879580,1200043740],[1128574590,1178156670]],[[1138066140,1237230300],[4402738680,4601067000],[3487791900,3586956060]],[[1165761150,1215343230],[3524978460,3624142620],[2470776990,2520359070]]],[[[67578703,92369743],[609286046,658868126],[597487183,622278223]],[[627879326,677461406],[2334168892,2433333052],[1817849246,1867431326]],[[616080463,640871503],[1836442526,1886024606],[1276141903,1300932943]]]]

private theorem identity_1010 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(1886441 / 9640960 : ℝ)) =
      tensor4 coefficients_1010 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1010, p_variance] <;> ring

private theorem negative_1010 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1010 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1010] at hp
  linarith only [hp]

private theorem node_1006 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 8 : ℝ)
  · exact node_1007 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_1010 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_1011 : List (List (List (List ℕ))) :=
  [[[[1191281,7389041],[113361202,125756722],[126114881,132312641]],[[118009522,130405042],[490514564,515305604],[400394962,412790482]],[[130763201,136960961],[405043282,417438802],[288225041,294422801]]],[[[26644926,39040446],[282800652,307591692],[284045646,296441166]],[[292097292,316888332],[1108292664,1157874744],[871975212,896766252]],[[293342286,305737806],[881271852,906062892],[615819486,628215006]]],[[[26145647,32343407],[170823454,183218974],[158622767,164820527]],[[175471774,187867294],[620546108,645337148],[472964254,485359774]],[[163271087,169468847],[477612574,490008094],[328286447,334484207]]]]

private theorem identity_1011 (x0 x1 x2 x3 : ℝ) :
    (21692160 : ℝ)*(-p_variance x0 x1 x2 x3-(170183 / 3098880 : ℝ)) =
      tensor4 coefficients_1011 ((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1011, p_variance] <;> ring

private theorem negative_1011 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1011 ((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1011] at hp
  linarith only [hp]

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 2 : ℝ)
  · exact node_1006 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.variance) (negative_1011 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part22
