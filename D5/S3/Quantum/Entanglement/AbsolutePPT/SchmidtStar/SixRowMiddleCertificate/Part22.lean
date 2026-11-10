/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part22.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
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

private theorem node_0968 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0969 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0978 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0955 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 16 : ℝ)
  · exact node_0956 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0968 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0982 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0982 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0982 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0982, p_qbox] <;> ring

private theorem negative_0982 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0982 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0982] at hp
  linarith only [hp]

private def coefficients_0983 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0983 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0983 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0983, p_qbox] <;> ring

private theorem negative_0983 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0983 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0983] at hp
  linarith only [hp]

private def coefficients_0984 : List (List (List (List ℕ))) :=
  [[[[58545432,108127512],[562167504,661331664],[510594552,560176632]],[[578436624,677600784],[2063295648,2261623968],[1498803984,1597968144]],[[526863672,576445752],[1515073104,1614237264],[995181912,1044763992]]],[[[213131568,312295728],[1320193176,1518521496],[1121006568,1220170728]],[[1352731416,1551059736],[4525861152,4922517792],[3201019656,3399347976]],[[1153544808,1252708968],[3233557896,3431886216],[2093958048,2193122208]]],[[[154932137,204514217],[758717674,857881834],[610758017,660340097]],[[774986794,874150954],[2463949508,2662277828],[1702907674,1802071834]],[[627027137,676609217],[1719176794,1818340954],[1099122137,1148704217]]]]

private theorem identity_0984 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(813131 / 9640960 : ℝ)) =
      tensor4 coefficients_0984 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0984, p_variance] <;> ring

private theorem negative_0984 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0984 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0984] at hp
  linarith only [hp]

private theorem node_0991 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0983 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0984 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0985 : List (List (List (List ℕ))) :=
  [[[[65517912,115099992],[1025837424,1125001584],[988209432,1037791512]],[[590057424,689221584],[3002256288,3200584608],[2467978704,2567142864]],[[531511992,581094072],[1990363824,2089527984],[1486741752,1536323832]]],[[[227076528,326240688],[2251309776,2449638096],[2080013088,2179177248]],[[1375973016,1574301336],[6411335952,6807992592],[5146922616,5345250936]],[[1162841448,1262005608],[4187916096,4386244416],[3080854488,3180018648]]],[[[161904617,211486697],[1226164354,1325328514],[1092149657,1141731737]],[[786607594,885771754],[3410463668,3608791988],[2679635914,2778800074]],[[631675457,681257537],[2198244274,2297408434],[1594458737,1644040817]]]]

private theorem identity_0985 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(909971 / 9640960 : ℝ)) =
      tensor4 coefficients_0985 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0985, p_variance] <;> ring

private theorem negative_0985 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0985 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0985] at hp
  linarith only [hp]

private theorem node_0990 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0991 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0985 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0986 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0986 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0986 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0986, p_qbox] <;> ring

private theorem negative_0986 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0986 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0986] at hp
  linarith only [hp]

private def coefficients_0987 : List (List (List (List ℕ))) :=
  [[[[213477569,312641729],[1324661938,1522990258],[1125129329,1224293489]],[[1357200178,1555528498],[4542352196,4939008836],[3213041938,3411370258]],[[1157667569,1256831729],[3245580178,3443908498],[2101857569,2201021729]]],[[[620420550,818748870],[3043808220,3440464860],[2451277590,2649605910]],[[3108884700,3505541340],[9888780120,10682093400],[6835675260,7232331900]],[[2516354070,2714682390],[6900751740,7297408380],[4412287590,4610615910]]],[[[407634983,506799143],[1720530286,1918858606],[1326840263,1426004423]],[[1753068526,1951396846],[5349195932,5745852572],[3624017326,3822345646]],[[1359378503,1458542663],[3656555566,3854883886],[2311122023,2410286183]]]]

private theorem identity_0987 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(213477569 / 1388298240 : ℝ)) =
      tensor4 coefficients_0987 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0987, p_variance] <;> ring

private theorem negative_0987 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0987 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0987] at hp
  linarith only [hp]

private theorem node_0993 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0986 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0987 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0988 : List (List (List (List ℕ))) :=
  [[[[227422529,326586689],[2259555298,2457883618],[2087912609,2187076769]],[[1380441778,1578770098],[6435380516,6832037156],[5166498418,5364826738]],[[1166964209,1266128369],[4203715138,4402043458],[3092530769,3191694929]]],[[[648310470,846638790],[4921148460,5317805100],[4384397670,4582725990]],[[3155367900,3552024540],[13689943800,14483257080],[10757695260,11154351900]],[[2534947350,2733275670],[8824575180,9221231820],[6401187510,6599515830]]],[[[421579943,520744103],[2662977166,2861305486],[2297177063,2396341223]],[[1776310126,1974638446],[7257331292,7653987932],[5592580846,5790909166]],[[1368675143,1467839303],[4622244046,4820572366],[3309348743,3408512903]]]]

private theorem identity_0988 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(227422529 / 1388298240 : ℝ)) =
      tensor4 coefficients_0988 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0988, p_variance] <;> ring

private theorem negative_0988 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0988 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0988] at hp
  linarith only [hp]

private theorem node_0992 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0993 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0988 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0989 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 32 : ℝ)
  · exact node_0990 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0992 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0989 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0989 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0989 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0989, p_qbox] <;> ring

private theorem negative_0989 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0989 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0989] at hp
  linarith only [hp]

private theorem node_0988 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0989 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0989 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0987 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0982 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0988 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0990 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0990 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0990 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0990, p_qbox] <;> ring

private theorem negative_0990 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0990 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0990] at hp
  linarith only [hp]

private def coefficients_0991 : List (List (List (List ℕ))) :=
  [[[[74628738,99419778],[381092436,430674516],[313436178,338227218]],[[385740756,435322836],[1251420552,1350584712],[879624756,929206836]],[[318084498,342875538],[884273076,933855156],[573161058,597952098]]],[[[199166208,248748288],[865779096,964943256],[680557848,730139928]],[[875075736,974239896],[2717583072,2915911392],[1870397256,1969561416]],[[689854488,739436568],[1879693896,1978858056],[1203784368,1253366448]]],[[[124883471,149674511],[485378662,534960742],[367467671,392258711]],[[490026982,539609062],[1467546524,1566710684],[991464502,1041046582]],[[372115991,396907031],[996112822,1045694902],[630969311,655760351]]]]

private theorem identity_0991 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(4146041 / 9640960 : ℝ)) =
      tensor4 coefficients_0991 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0991, p_variance] <;> ring

private theorem negative_0991 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0991 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0991] at hp
  linarith only [hp]

private theorem node_0994 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0990 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0991 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0986 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0987 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0994 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0992 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0992 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0992 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0992, p_qbox] <;> ring

private theorem negative_0992 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0992 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0992] at hp
  linarith only [hp]

private def coefficients_0993 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0993 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0993 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0993, p_qbox] <;> ring

private theorem negative_0993 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0993 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0993] at hp
  linarith only [hp]

private def coefficients_0994 : List (List (List (List ℕ))) :=
  [[[[155278138,204860218],[763186436,862350596],[614880778,664462858]],[[779455556,878619716],[2480440552,2678768872],[1714929956,1814094116]],[[631149898,680731978],[1731199076,1830363236],[1107021658,1156603738]]],[[[407980984,507145144],[1724999048,1923327368],[1330963024,1430127184]],[[1757537288,1955865608],[5365686976,5762343616],[3636039608,3834367928]],[[1363501264,1462665424],[3668577848,3866906168],[2319021544,2418185704]]],[[[253048847,302630927],[962504614,1061668774],[716428247,766010327]],[[978773734,1077937894],[2886630428,3084958748],[1921801654,2020965814]],[[732697367,782279447],[1938070774,2037234934],[1212345887,1261927967]]]]

private theorem identity_0994 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(77639069 / 347074560 : ℝ)) =
      tensor4 coefficients_0994 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0994, p_variance] <;> ring

private theorem negative_0994 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0994 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0994] at hp
  linarith only [hp]

private theorem node_1000 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0993 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0994 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0995 : List (List (List (List ℕ))) :=
  [[[[162250618,211832698],[1234409876,1333574036],[1100049178,1149631258]],[[791076356,890240516],[3434508232,3632836552],[2699211716,2798375876]],[[635798218,685380298],[2214043316,2313207476],[1606135018,1655717098]]],[[[421925944,521090104],[2671222688,2869551008],[2305076584,2404240744]],[[1780778888,1979107208],[7281375856,7678032496],[5612156648,5810484968]],[[1372797904,1471962064],[4638043088,4836371408],[3321025024,3420189184]]],[[[260021327,309603407],[1437504814,1536668974],[1205373407,1254955487]],[[990394534,1089558694],[3848251628,4046579948],[2913636934,3012801094]],[[737345687,786927767],[2424691774,2523855934],[1715236007,1764818087]]]]

private theorem identity_0995 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(81125309 / 347074560 : ℝ)) =
      tensor4 coefficients_0995 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0995, p_variance] <;> ring

private theorem negative_0995 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0995 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0995] at hp
  linarith only [hp]

private theorem node_0999 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_1000 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0995 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0996 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0996 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0996 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0996, p_qbox] <;> ring

private theorem negative_0996 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0996 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0996] at hp
  linarith only [hp]

private def coefficients_0997 : List (List (List (List ℕ))) :=
  [[[[408326985,507491145],[1729467810,1927796130],[1335085785,1434249945]],[[1762006050,1960334370],[5382178020,5778834660],[3648061890,3846390210]],[[1367624025,1466788185],[3680600130,3878928450],[2326921065,2426085225]]],[[[1012887390,1211215710],[3858955980,4255612620],[2873958510,3072286830]],[[3924032460,4320689100],[11579503800,12372817080],[7711251180,8107907820]],[[2939034990,3137363310],[7776327660,8172984300],[4865182590,5063510910]]],[[[605252407,704416567],[2130872174,2329200494],[1539564727,1638728887]],[[2163410414,2361738734],[6200093788,6596750428],[4064573294,4262901614]],[[1572102967,1671267127],[4097111534,4295439854],[2538953527,2638117687]]]]

private theorem identity_0997 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(9073933 / 30851072 : ℝ)) =
      tensor4 coefficients_0997 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0997, p_variance] <;> ring

private theorem negative_0997 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0997 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0997] at hp
  linarith only [hp]

private theorem node_1002 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0996 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0997 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0998 : List (List (List (List ℕ))) :=
  [[[[422271945,521436105],[2679468210,2877796530],[2312976105,2412140265]],[[1785247650,1983575970],[7305420420,7702077060],[5631732450,5830060770]],[[1376920665,1476084825],[4653842130,4852170450],[3332701305,3431865465]]],[[[1040777310,1239105630],[5766510300,6163166940],[4837292670,5035620990]],[[3970515660,4367172300],[15441095640,16234408920],[11693699340,12090355980]],[[2957628270,3155956590],[9730365180,10127021820],[6884296590,7082624910]]],[[[619197367,718361527],[3088426094,3286754414],[2525008567,2624172727]],[[2186652014,2384980334],[8138443228,8535099868],[6063350894,6261679214]],[[1581399607,1680563767],[5077907054,5276235374],[3552287287,3651451447]]]]

private theorem identity_0998 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(9383821 / 30851072 : ℝ)) =
      tensor4 coefficients_0998 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0998, p_variance] <;> ring

private theorem negative_0998 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0998 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0998] at hp
  linarith only [hp]

private theorem node_1001 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_1002 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0998 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0998 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 32 : ℝ)
  · exact node_0999 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_1001 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0999 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0999 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0999 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0999, p_qbox] <;> ring

private theorem negative_0999 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0999 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0999] at hp
  linarith only [hp]

private theorem node_0997 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0998 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0999 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0996 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0992 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0997 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_1000 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_1000 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_1000 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1000, p_qbox] <;> ring

private theorem negative_1000 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1000 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1000] at hp
  linarith only [hp]

private def coefficients_1001 : List (List (List (List ℕ))) :=
  [[[[199512209,249094289],[870247858,969412018],[684680609,734262689]],[[879544498,978708658],[2734074116,2932402436],[1882419538,1981583698]],[[693977249,743559329],[1891716178,1990880338],[1211683889,1261265969]]],[[[500225886,599390046],[1950452172,2148780492],[1478116206,1577280366]],[[1969045452,2167373772],[5903168184,6299824824],[3989902572,4188230892]],[[1496709486,1595873646],[4008495852,4206824172],[2539676286,2638840446]]],[[[301405679,350987759],[1081588318,1180752478],[794127599,843709679]],[[1090884958,1190049118],[3171862076,3370190396],[2108867038,2208031198]],[[803424239,853006319],[2118163678,2217327838],[1328684399,1378266479]]]]

private theorem identity_1001 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(199512209 / 347074560 : ℝ)) =
      tensor4 coefficients_1001 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_1001, p_variance] <;> ring

private theorem negative_1001 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_1001 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_1001] at hp
  linarith only [hp]

private theorem node_1003 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_1000 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_1001 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0995 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0996 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_1003 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0985 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 16 : ℝ)
  · exact node_0986 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0995 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0954 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0955 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0985 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

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
