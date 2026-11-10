/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part02
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part02
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part02.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part02
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0029 : List (List (List (List ℕ))) :=
  [[[[82698497,51709697],[72820817,41832017]],[[160458154,98480554],[140702794,78725194]],[[60328457,29339657],[50450777,19461977]]],[[[161359888,99382288],[141023488,79045888]],[[312551576,188596376],[271878776,147923576]],[[116329288,54351688],[95992888,34015288]]],[[[78498982,47510182],[68040262,37051462]],[[151768604,89791004],[130851164,68873564]],[[55838422,24849622],[45379702,14390902]]]]

private theorem identity_0029 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_headsq x0 x1 x2 x3-(7195451 / 15494400 : ℝ)) =
      tensor4 coefficients_0029 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0029, p_headsq] <;> ring

private theorem negative_0029 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0029 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0029] at hp
  linarith only [hp]

private def coefficients_0030 : List (List (List (List ℕ))) :=
  [[[[487333297,363378097],[447822577,323867377]],[[815461634,567551234],[736440194,488529794]],[[293265937,169310737],[253755217,129800017]]],[[[957356090,709445690],[877172570,629262170]],[[1595721220,1099900420],[1435354180,939533380]],[[568640330,320729930],[488456810,240546410]]],[[[469697975,345742775],[429025175,305069975]],[[779609950,531699550],[698264350,450353950]],[[275049575,151094375],[234376775,110421575]]]]

private theorem identity_0030 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(4416863 / 9916416 : ℝ)) =
      tensor4 coefficients_0030 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0030, p_headsq] <;> ring

private theorem negative_0030 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0030 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0030] at hp
  linarith only [hp]

private def coefficients_0031 : List (List (List (List ℕ))) :=
  [[[[384295537,322317937],[364540177,302562577]],[[539661314,415706114],[500150594,376195394]],[[120503377,58525777],[100748017,38770417]]],[[[750699530,626744330],[710607770,586652570]],[[1042958500,795048100],[962774980,714864580]],[[222534170,98578970],[182442410,58487210]]],[[[366079175,304101575],[345742775,283765175]],[[502647550,378692350],[461974750,338019550]],[[101705975,39728375],[81369575,19391975]]]]

private theorem identity_0031 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(775679 / 9916416 : ℝ)) =
      tensor4 coefficients_0031 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0031, p_headsq] <;> ring

private theorem negative_0031 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0031 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0031] at hp
  linarith only [hp]

private def coefficients_0032 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0032 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0032 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0032, p_qmass] <;> ring

private theorem negative_0032 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0032 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0032] at hp
  linarith only [hp]

private theorem node_0040 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0031 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0032 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0033 : List (List (List (List ℕ))) :=
  [[[[374708377,312730777],[354953017,292975417]],[[520486994,396531794],[480976274,357021074]],[[110916217,48938617],[91160857,29183257]]],[[[730944170,606988970],[690852410,566897210]],[[1003447780,755537380],[923264260,675353860]],[[202778810,78823610],[162687050,38731850]]],[[[355910975,293933375],[335574575,273596975]],[[482311150,358355950],[441638350,317683150]],[[91537775,29560175],[71201375,9223775]]]]

private theorem identity_0033 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(368951 / 9916416 : ℝ)) =
      tensor4 coefficients_0033 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0033, p_headsq] <;> ring

private theorem negative_0033 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0033 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0033] at hp
  linarith only [hp]

private def coefficients_0034 : List (List (List (List ℕ))) :=
  [[[[38116747,130463894,88473547],[18361387,90953174,68718187]],[[57872107,169974614,108228907],[38116747,130463894,88473547]]],[[[71124830,250710460,171838430],[31033070,170526940,131746670]],[[111216590,330893980,211930190],[71124830,250710460,171838430]]],[[[32828525,119887450,83185325],[12492125,79214650,62848925]],[[53164925,160560250,103521725],[32828525,119887450,83185325]]]]

private theorem identity_0034 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(499685 / 9916416 : ℝ)) =
      tensor4 coefficients_0034 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0034, p_coupled] <;> ring

private theorem negative_0034 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0034 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0034] at hp
  linarith only [hp]

private theorem node_0041 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0033 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0034 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0039 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0040 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0041 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0038 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0030 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0039 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0035 : List (List (List (List ℕ))) :=
  [[[[239856007,177878407],[219519607,157542007]],[[399819014,275863814],[359146214,235191014]],[[142531807,80554207],[122195407,60217807]]],[[[470731944,346776744],[429478104,305522904]],[[781387368,533476968],[698879688,450969288]],[[275793024,151837824],[234539184,110583984]]],[[[230713528,168735928],[209796088,147818488]],[[381243536,257288336],[339408656,215453456]],[[133098808,71121208],[112181368,50203768]]]]

private theorem identity_0035 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(6275471 / 15494400 : ℝ)) =
      tensor4 coefficients_0035 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0035, p_headsq] <;> ring

private theorem negative_0035 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0035 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0035] at hp
  linarith only [hp]

private def coefficients_0036 : List (List (List (List ℕ))) :=
  [[[[188046607,157057807],[177878407,146889607]],[[261337814,199360214],[241001414,179023814]],[[55860007,24871207],[45691807,14703007]]],[[[366822624,304845024],[346195704,284218104]],[[503843928,379888728],[462590088,338634888]],[[102158904,40181304],[81531984,19554384]]],[[[178613608,147624808],[168154888,137166088]],[[242181296,180203696],[221263856,159286256]],[[46136488,15147688],[35677768,4688968]]]]

private theorem identity_0036 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(586121 / 15494400 : ℝ)) =
      tensor4 coefficients_0036 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0036, p_headsq] <;> ring

private theorem negative_0036 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0036 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0036] at hp
  linarith only [hp]

private def coefficients_0037 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0037 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0037 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0037, p_qmass] <;> ring

private theorem negative_0037 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0037 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0037] at hp
  linarith only [hp]

private theorem node_0044 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0036 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0037 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0038 : List (List (List (List ℕ))) :=
  [[[[27628088129,20965496129],[25441925129,18779333129]],[[10487408129,3824816129],[8301245129,1638653129]]],[[[81230924012,61336114412],[74640477812,54745668212]],[[30250474412,10355664812],[23660028212,3765218612]]],[[[79575706832,59773863632],[72954174992,53152331792]],[[29039171792,9237328592],[22417639952,2615796752]]],[[[25973358176,19403732576],[23756109536,17186483936]],[[9276592736,2706967136],[7059344096,489718496]]]]

private theorem identity_0038 (x0 x1 x2 x3 : ℝ) :
    (19832832000 : ℝ)*(-p_headcap x0 x1 x2 x3-(15303703 / 619776000 : ℝ)) =
      tensor4 coefficients_0038 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0038, p_headcap] <;> ring

private theorem negative_0038 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headcap x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0038 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0038] at hp
  linarith only [hp]

private def coefficients_0039 : List (List (List (List ℕ))) :=
  [[[[17971357,63057914,43149757],[7803157,42721514,32981557]],[[28139557,83394314,53317957],[17971357,63057914,43149757]]],[[[33208824,120648048,83565624],[12581904,79394208,62938704]],[[53835744,161901888,104192544],[33208824,120648048,83565624]]],[[[15147688,57410576,40326088],[4688968,36493136,29867368]],[[25606408,78328016,50784808],[15147688,57410576,40326088]]]]

private theorem identity_0039 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(586121 / 15494400 : ℝ)) =
      tensor4 coefficients_0039 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0039, p_coupled] <;> ring

private theorem negative_0039 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0039 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0039] at hp
  linarith only [hp]

private theorem node_0045 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headcap) (negative_0038 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0039 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0043 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0044 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0045 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0042 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0035 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0043 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0037 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 16 : ℝ)
  · exact node_0038 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0042 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0040 : List (List (List (List ℕ))) :=
  [[[[9608507,30837814,19292507],[4669667,20960134,14353667]],[[14547347,40715494,24231347],[9608507,30837814,19292507]]],[[[17939848,59121296,37307848],[7771648,38784896,27139648]],[[28108048,79457696,47476048],[17939848,59121296,37307848]]],[[[8241562,28103924,17925562],[3012202,17645204,12696202]],[[13470922,38562644,23154922],[8241562,28103924,17925562]]]]

private theorem identity_0040 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(1506101 / 15494400 : ℝ)) =
      tensor4 coefficients_0040 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0040, p_coupled] <;> ring

private theorem negative_0040 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0040 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0040] at hp
  linarith only [hp]

private theorem node_0036 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0037 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0040 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0041 : List (List (List (List ℕ))) :=
  [[[[468158977,344203777],[428648257,304693057]],[[777112994,529202594],[698091554,450181154]],[[274091617,150136417],[234580897,110625697]]],[[[917845370,669934970],[837661850,589751450]],[[1516699780,1020878980],[1356332740,860511940]],[[529129610,281219210],[448946090,201035690]]],[[[449361575,325406375],[408688775,284733575]],[[738937150,491026750],[657591550,409681150]],[[254713175,130757975],[214040375,90085175]]]]

private theorem identity_0041 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(3603407 / 9916416 : ℝ)) =
      tensor4 coefficients_0041 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0041, p_headsq] <;> ring

private theorem negative_0041 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0041 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0041] at hp
  linarith only [hp]

private def coefficients_0042 : List (List (List (List ℕ))) :=
  [[[[1439781937,1191871537],[1360760497,1112850097]],[[1963844834,1468024034],[1805801954,1309981154]],[[384613297,136702897],[305591857,57681457]]],[[[2841456626,2345635826],[2682251666,2186430866]],[[3850313092,2858671492],[3531903172,2540261572]],[[729957266,234136466],[570752306,74931506]]],[[[1401349871,1153439471],[1321166351,1073255951]],[[1885818622,1389997822],[1725451582,1229630782]],[[345019151,97108751],[264835631,16925231]]]]

private theorem identity_0042 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(16925231 / 991641600 : ℝ)) =
      tensor4 coefficients_0042 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0042, p_headsq] <;> ring

private theorem negative_0042 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0042 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0042] at hp
  linarith only [hp]

private def coefficients_0043 : List (List (List (List ℕ))) :=
  [[[[570124201,446169001],[530032441,406077241]],[[911028122,663117722],[830844602,582934202]],[[323472721,199517521],[283380961,159425761]]],[[[1120869960,872959560],[1040105400,792195000]],[[1783008840,1287188040],[1621479720,1125658920]],[[627276480,379366080],[546511920,298601520]]],[[[550583350,426628150],[509910550,385955350]],[[871655900,623745500],[790310300,542399900]],[[303641350,179686150],[262968550,139013350]]]]

private theorem identity_0043 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(2780267 / 9916416 : ℝ)) =
      tensor4 coefficients_0043 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0043, p_headsq] <;> ring

private theorem negative_0043 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0043 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0043] at hp
  linarith only [hp]

private def coefficients_0044 : List (List (List (List ℕ))) :=
  [[[[31276966069819,8036729577019],[23760202079179,519965586379]],[[65662707928718,19182234943118],[50629179947438,4148706961838]],[[31117583602099,7877347109299],[23600819611459,360583118659]]],[[[125108326455200,32469416093600],[95036490276560,2397579914960]],[[262101122761480,76823302038280],[201957450404200,16679629681000]],[[123965449536680,31326539175080],[93893613358040,1254702996440]]],[[[187636813022600,49160385297800],[142523037146600,4046609421800]],[[392277166079200,115324310629600],[302049614327200,25096758877600]],[[185167105407800,46690677683000],[140053329531800,1576901807000]]],[[[125056502156000,33059431820000],[94977397748000,2980327412000]],[[260901784084000,76907643412000],[200743575268000,16749434596000]],[[122908193912000,30911123576000],[92829089504000,832019168000]]],[[[31251047815000,8331731335000],[23730647095000,811330615000]],[[65063029430000,19224396470000],[50022227990000,4183595030000]],[[30588952735000,7669636255000],[23068552015000,149235535000]]]]

private theorem identity_0044 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(29847107 / 10154409984 : ℝ)) =
      tensor4 coefficients_0044 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0044, p_headbox] <;> ring

private theorem negative_0044 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0044 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0044] at hp
  linarith only [hp]

private theorem node_0052 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0043 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.headbox) (negative_0044 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0051 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0042 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0052 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0045 : List (List (List (List ℕ))) :=
  [[[[28529587,111289574,78886387],[8774227,71778854,59131027]],[[48284947,150800294,98641747],[28529587,111289574,78886387]]],[[[51369470,211199740,152083070],[11277710,131016220,111991310]],[[91461230,291383260,192174830],[51369470,211199740,152083070]]],[[[22660325,99551050,73017125],[2323925,58878250,52680725]],[[42996725,140223850,93353525],[22660325,99551050,73017125]]]]

private theorem identity_0045 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(92957 / 9916416 : ℝ)) =
      tensor4 coefficients_0045 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0045, p_coupled] <;> ring

private theorem negative_0045 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0045 ((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0045] at hp
  linarith only [hp]

private theorem node_0050 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0051 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0045 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0046 : List (List (List (List ℕ))) :=
  [[[[1119338377,871427977],[1040316937,792406537]],[[1780817234,1284996434],[1622774354,1126953554]],[[626616457,378706057],[547595017,299684617]]],[[[2199407426,1703586626],[2040202466,1544381666]],[[3482514772,2490873172],[3164104852,2172463252]],[[1213382546,717561746],[1054177586,558356786]]],[[[1079744231,831833831],[999560711,751650311]],[[1701047902,1205227102],[1540680862,1044860062]],[[586441271,338530871],[506257751,258347351]]]]

private theorem identity_0046 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(258347351 / 991641600 : ℝ)) =
      tensor4 coefficients_0046 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0046, p_headsq] <;> ring

private theorem negative_0046 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0046 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0046] at hp
  linarith only [hp]

private def coefficients_0047 : List (List (List (List ℕ))) :=
  [[[[94574232,144156312],[1097895024,1197059184],[1031210712,1080792792]],[[641197584,740361744],[3132426528,3330754848],[2547008784,2646172944]],[[553595832,603177912],[2048476464,2147640624],[1522770552,1572352632]]],[[[291241680,390405840],[2407530000,2605858320],[2172068160,2271232320]],[[1490358360,1688686680],[6695886480,7092543120],[5317087800,5515416120]],[[1213061640,1312225800],[4316246400,4514574720],[3158964600,3258128760]]],[[[197013449,246595529],[1310326978,1409491138],[1141203449,1190785529]],[[849852778,949016938],[3564843956,3763172276],[2770771018,2869935178]],[[659811809,709393889],[2268461938,2367626098],[1636540049,1686122129]]]]

private theorem identity_0047 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(1313531 / 9640960 : ℝ)) =
      tensor4 coefficients_0047 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0047, p_variance] <;> ring

private theorem negative_0047 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0047 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0047] at hp
  linarith only [hp]

private theorem node_0055 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0046 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0047 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0048 : List (List (List (List ℕ))) :=
  [[[[550368841,426413641],[510277081,386321881]],[[871517402,623607002],[791333882,543423482]],[[303717361,179762161],[263625601,139670401]]],[[[1080778200,832867800],[1000013640,752103240]],[[1702825320,1207004520],[1541296200,1045475400]],[[587184720,339274320],[506420160,258509760]]],[[[530246950,406291750],[489574150,365618950]],[[830983100,583072700],[749637500,501727100]],[[283304950,159349750],[242632150,118676950]]]]

private theorem identity_0048 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(2373539 / 9916416 : ℝ)) =
      tensor4 coefficients_0048 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0048, p_headsq] <;> ring

private theorem negative_0048 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0048 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0048] at hp
  linarith only [hp]

private def coefficients_0049 : List (List (List (List ℕ))) :=
  [[[[291587681,390751841],[2415775522,2614103842],[2179967681,2279131841]],[[1494827122,1693155442],[6719931044,7116587684],[5336663602,5534991922]],[[1217184401,1316348561],[4332045442,4530373762],[3170640881,3269805041]]],[[[788745798,987074118],[5257798956,5654455596],[4580612838,4778941158]],[[3408348636,3805005276],[14307464952,15100778232],[11122235676,11518892316]],[[2647492758,2845821078],[9105445836,9502102476],[6569512758,6767841078]]],[[[497850119,597014279],[2843407438,3041735758],[2401337159,2500501319]],[[1914905518,2113233838],[7590301916,7986958556],[5786956078,5985284398]],[[1431000359,1530164519],[4774784398,4973112718],[3399563879,3498728039]]]]

private theorem identity_0049 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(41655383 / 198328320 : ℝ)) =
      tensor4 coefficients_0049 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0049, p_variance] <;> ring

private theorem negative_0049 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0049 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0049] at hp
  linarith only [hp]

private theorem node_0056 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0048 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0049 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0054 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 32 : ℝ)
  · exact node_0055 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0056 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0050 : List (List (List (List ℕ))) :=
  [[[[995383177,747472777],[916361737,668451337]],[[1532906834,1037086034],[1374863954,879043154]],[[502661257,254750857],[423639817,175729417]]],[[[1951497026,1455676226],[1792292066,1296471266]],[[2986693972,1995052372],[2668284052,1676642452]],[[965472146,469651346],[806267186,310446386]]],[[[955789031,707878631],[875605511,627695111]],[[1453137502,957316702],[1292770462,796949662]],[[462486071,214575671],[382302551,134392151]]]]

private theorem identity_0050 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(134392151 / 991641600 : ℝ)) =
      tensor4 coefficients_0050 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0050, p_headsq] <;> ring

private theorem negative_0050 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0050 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0050] at hp
  linarith only [hp]

private def coefficients_0051 : List (List (List (List ℕ))) :=
  [[[[119365272,168947352],[1147477104,1246641264],[1056001752,1105583832]],[[690779664,789943824],[3231590688,3429919008],[2596590864,2695755024]],[[578386872,627968952],[2098058544,2197222704],[1547561592,1597143672]]],[[[340823760,439987920],[2506694160,2705022480],[2221650240,2320814400]],[[1589522520,1787850840],[6894214800,7290871440],[5416251960,5614580280]],[[1262643720,1361807880],[4415410560,4613738880],[3208546680,3307710840]]],[[[221804489,271386569],[1359909058,1459073218],[1165994489,1215576569]],[[899434858,998599018],[3664008116,3862336436],[2820353098,2919517258]],[[684602849,734184929],[2318044018,2417208178],[1661331089,1710913169]]]]

private theorem identity_0051 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(1657851 / 9640960 : ℝ)) =
      tensor4 coefficients_0051 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0051, p_variance] <;> ring

private theorem negative_0051 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0051 ((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0051] at hp
  linarith only [hp]

private theorem node_0058 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (5 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0050 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0051 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0052 : List (List (List (List ℕ))) :=
  [[[[488391241,364436041],[448299481,324344281]],[[747562202,499651802],[667378682,419468282]],[[241739761,117784561],[201648001,77692801]]],[[[956823000,708912600],[876058440,628148040]],[[1454914920,959094120],[1293385800,797565000]],[[463229520,215319120],[382464960,134554560]]],[[[468269350,344314150],[427596550,303641350]],[[707027900,459117500],[625682300,377771900]],[[221327350,97372150],[180654550,56699350]]]]

private theorem identity_0052 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1133987 / 9916416 : ℝ)) =
      tensor4 coefficients_0052 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0052, p_headsq] <;> ring

private theorem negative_0052 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0052 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0052] at hp
  linarith only [hp]

private def coefficients_0053 : List (List (List (List ℕ))) :=
  [[[[341169761,440333921],[2514939682,2713268002],[2229549761,2328713921]],[[1593991282,1792319602],[6918259364,7314916004],[5435827762,5634156082]],[[1266766481,1365930641],[4431209602,4629537922],[3220222961,3319387121]]],[[[887909958,1086238278],[5456127276,5852783916],[4679776998,4878105318]],[[3606676956,4003333596],[14704121592,15497434872],[11320563996,11717220636]],[[2746656918,2944985238],[9303774156,9700430796],[6668676918,6867005238]]],[[[547432199,646596359],[2942571598,3140899918],[2450919239,2550083399]],[[2014069678,2212397998],[7788630236,8185286876],[5886120238,6084448558]],[[1480582439,1579746599],[4873948558,5072276878],[3449145959,3548310119]]]]

private theorem identity_0053 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(341169761 / 1388298240 : ℝ)) =
      tensor4 coefficients_0053 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0053, p_variance] <;> ring

private theorem negative_0053 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0053 ((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(5 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0053] at hp
  linarith only [hp]

private theorem node_0059 (x0 x1 x2 x3 : ℝ)
    (h0l : (5 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0052 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0053 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0057 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (5 / 32 : ℝ)
  · exact node_0058 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0059 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0053 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0054 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0057 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0049 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0050 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0053 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0048 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0041 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0049 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0054 : List (List (List (List ℕ))) :=
  [[[[229978327,168000727],[209641927,147664327]],[[380063654,256108454],[339390854,215435654]],[[132654127,70676527],[112317727,50340127]]],[[[450395544,326440344],[409141704,285186504]],[[740714568,492804168],[658206888,410296488]],[[255456624,131501424],[214202784,90247584]]],[[[220254808,158277208],[199337368,137359768]],[[360326096,236370896],[318491216,194536016]],[[122640088,60662488],[101722648,39745048]]]]

private theorem identity_0054 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(4968131 / 15494400 : ℝ)) =
      tensor4 coefficients_0054 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0054, p_headsq] <;> ring

private theorem negative_0054 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0054 ((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0054] at hp
  linarith only [hp]

private def coefficients_0055 : List (List (List (List ℕ))) :=
  [[[[1121903929,873993529],[1040558329,792647929]],[[1784786258,1288965458],[1622095058,1126274258]],[[628019929,380109529],[546674329,298763929]]],[[[2204401338,1708580538],[2040548058,1544727258]],[[3490178436,2498536836],[3162471876,2170830276]],[[1216052298,720231498],[1052199018,556378218]]],[[[1082172591,834262191],[999664911,751754511]],[[1704742542,1208921742],[1539727182,1043906382]],[[587707551,339797151],[505199871,257289471]]]]

private theorem identity_0055 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(28587719 / 110182400 : ℝ)) =
      tensor4 coefficients_0055 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0055, p_headsq] <;> ring

private theorem negative_0055 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0055 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0055] at hp
  linarith only [hp]

private def coefficients_0056 : List (List (List (List ℕ))) :=
  [[[[62760931595221,16922298635221],[47720130155221,1881497195221]],[[130643730790442,38966464870442],[100562127910442,8884861990442]],[[61436741435221,15598108475221],[46395939995221,557307035221]]],[[[250939104588884,68224181580884],[190770901884884,8055978876884]],[[521275590433768,155845744417768],[400939185025768,35509339009768]],[[244642199796884,61927276788884],[184473997092884,1759074084884]]],[[[376198911084526,103083708626926],[285941377668526,12826175210926]],[[779864367373052,233633962457852],[599349300541052,53118895625852]],[[365258630942926,92143428485326],[275001097526926,1885895069326]]],[[[250624203547284,69184035816084],[190450528608564,9010360877364]],[[518476836336408,155596500874008],[398129486458968,35249150996568]],[[242337609201924,60897441470724],[182163934263204,723766532004]]],[[[62603462048859,17402206727259],[47559919262139,2358663940539]],[[129244321791558,38841811148358],[99157236218118,8754725574918]],[[60284433213099,15083177891499],[45240890426379,39635104779]]]]

private theorem identity_0056 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(4403900531 / 11282677760000 : ℝ)) =
      tensor4 coefficients_0056 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0056, p_headbox] <;> ring

private theorem negative_0056 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0056 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0056] at hp
  linarith only [hp]

private theorem node_0064 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0055 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.headbox) (negative_0056 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0057 : List (List (List (List ℕ))) :=
  [[[[551617319,427662119],[510363479,386408279]],[[873433318,625522918],[790925638,543015238]],[[304384799,180429599],[263130959,139175759]]],[[[1083206560,835296160],[1000117840,752207440]],[[1706519960,1210699160],[1540342520,1044521720]],[[588451000,340540600],[505362280,257451880]]],[[[531426832,407471632],[489591952,365636752]],[[832761824,584851424],[749092064,501181664]],[[283903792,159948592],[242068912,118113712]]]]

private theorem identity_0057 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(7382107 / 30988800 : ℝ)) =
      tensor4 coefficients_0057 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0057, p_headsq] <;> ring

private theorem negative_0057 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0057 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0057] at hp
  linarith only [hp]

private def coefficients_0058 : List (List (List (List ℕ))) :=
  [[[[29574720813107,6974093152307],[25813835116427,3213207455627]],[[61168140473134,15966885151534],[53646369079774,8445113758174]],[[28415206395227,5814578734427],[24654320698547,2053693037747]]],[[[118193705576504,28108768155704],[103150038737744,13065101316944]],[[243922787307448,63752912465848],[213835453629928,33665578788328]],[[113060887406144,22975949985344],[98017220567384,7932283146584]]],[[[177106328218784,42454166324384],[154541200552544,19889038658144]],[[364709413640128,95405089851328],[319579158307648,50274834518848]],[[168667625154944,34015463260544],[146102497488704,11450335594304]]],[[[117930400527360,28478378357760],[102887600309760,13435578140160]],[[242322988485120,63418944145920],[212237388049920,33333343710720]],[[111813397340160,22361375170560],[96770597122560,7318574952960]]],[[[29443055368192,7158885332992],[25682601674752,3398431639552]],[[60368218271744,15799878201344],[52847310884864,8278970814464]],[[27791451492352,5507281457152],[24030997798912,1746827763712]]]]

private theorem identity_0058 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(213235811 / 6197760000 : ℝ)) =
      tensor4 coefficients_0058 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0058, p_headbox] <;> ring

private theorem negative_0058 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0058 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0058] at hp
  linarith only [hp]

private def coefficients_0059 : List (List (List (List ℕ))) :=
  [[[[39811041,138975201],[983139282,1181467602],[957273201,1056437361]],[[973842642,1172170962],[3787257924,4183914564],[2841305202,3039633522]],[[947976561,1047140721],[2832008562,3030336882],[1897976961,1997141121]]],[[[280407006,478735326],[2375401932,2772058572],[2122884846,2321213166]],[[2356808652,2753465292],[8407869624,9201182904],[6106840812,6503497452]],[[2104291566,2302619886],[6088247532,6484904172],[4011845886,4210174206]]],[[[241287967,340452127],[1393646654,1591974974],[1166303647,1265467807]],[[1384350014,1582678334],[4623379708,5020036348],[3266919614,3465247934]],[[1157007007,1256171167],[3257622974,3455951294],[2114560927,2213725087]]]]

private theorem identity_0059 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(4423449 / 154255360 : ℝ)) =
      tensor4 coefficients_0059 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0059, p_variance] <;> ring

private theorem negative_0059 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0059 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0059] at hp
  linarith only [hp]

private theorem node_0066 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0058 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0059 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0065 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0057 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0066 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0063 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 32 : ℝ)
  · exact node_0064 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0065 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0060 : List (List (List (List ℕ))) :=
  [[[[97360939,411643478,298788139],[16015339,248952278,217442539]],[[178706539,574334678,380133739],[97360939,411643478,298788139]]],[[[182624238,799091676,585478638],[18770958,471385116,421625358]],[[346477518,1126798236,749331918],[182624238,799091676,585478638]]],[[[85083741,387089082,286510941],[2576061,222073722,204003261]],[[167591421,552104442,369018621],[85083741,387089082,286510941]]]]

private theorem identity_0060 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(286229 / 110182400 : ℝ)) =
      tensor4 coefficients_0060 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0060, p_coupled] <;> ring

private theorem negative_0060 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0060 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0060] at hp
  linarith only [hp]

private def coefficients_0061 : List (List (List (List ℕ))) :=
  [[[[489639719,365684519],[448385879,324430679]],[[749478118,501567718],[666970438,419060038]],[[242407199,118451999],[201153359,77198159]]],[[[959251360,711340960],[876162640,628252240]],[[1458609560,962788760],[1292432120,796611320]],[[464495800,216585400],[381407080,133496680]]],[[[469449232,345494032],[427614352,303659152]],[[708806624,460896224],[625136864,377226464]],[[221926192,97970992],[180091312,56136112]]]]

private theorem identity_0061 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(3508507 / 30988800 : ℝ)) =
      tensor4 coefficients_0061 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0061, p_headsq] <;> ring

private theorem negative_0061 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0061 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0061] at hp
  linarith only [hp]

private def coefficients_0062 : List (List (List (List ℕ))) :=
  [[[[56159669,220780138,156873269],[14905829,138272458,115619429]],[[76786589,262033978,177500189],[35532749,179526298,136246349]]],[[[106381480,429684560,307808680],[23292760,263507120,224719960]],[[147925840,512773280,349353040],[64837120,346595840,266264320]]],[[[50132032,208724864,150845632],[8297152,125055104,109010752]],[[71049472,250559744,171763072],[29214592,166889984,129928192]]]]

private theorem identity_0062 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(129643 / 7747200 : ℝ)) =
      tensor4 coefficients_0062 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0062, p_coupled] <;> ring

private theorem negative_0062 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0062 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0062] at hp
  linarith only [hp]

private theorem node_0068 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0061 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0062 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0067 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 32 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0060 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0068 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0062 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0063 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0067 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0063 : List (List (List (List ℕ))) :=
  [[[[1081812169,833901769],[1000466569,752556169]],[[1704602738,1208781938],[1541911538,1046090738]],[[587928169,340017769],[506582569,258672169]]],[[[2123055738,1627234938],[1959202458,1463381658]],[[3327487236,2335845636],[2999780676,2008139076]],[[1134706698,638885898],[970853418,475032618]]],[[[1040918751,793008351],[958411071,710500671]],[[1622234862,1126414062],[1457219502,961398702]],[[546453711,298543311],[463946031,216035631]]]]

private theorem identity_0063 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(24003959 / 110182400 : ℝ)) =
      tensor4 coefficients_0063 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0063, p_headsq] <;> ring

private theorem negative_0063 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0063 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0063] at hp
  linarith only [hp]

private def coefficients_0064 : List (List (List (List ℕ))) :=
  [[[[197359450,246941530],[1318572500,1417736660],[1149102970,1198685050]],[[854321540,953485700],[3588888520,3787216840],[2790346820,2889510980]],[[663934570,713516650],[2284260980,2383425140],[1648216330,1697798410]]],[[[498196120,597360280],[2851652960,3049981280],[2409236680,2508400840]],[[1919374280,2117702600],[7614346480,8011003120],[5806531880,6004860200]],[[1435123120,1534287280],[4790583440,4988911760],[3411240160,3510404320]]],[[[301182671,350764751],[1533772462,1632936622],[1260479711,1310061791]],[[1065744742,1164908902],[4026841964,4225170284],[3016877062,3116041222]],[[771534551,821116631],[2507014462,2606178622],[1763369831,1812951911]]]]

private theorem identity_0064 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(19735945 / 69414912 : ℝ)) =
      tensor4 coefficients_0064 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0064, p_variance] <;> ring

private theorem negative_0064 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0064 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0064] at hp
  linarith only [hp]

private theorem node_0071 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0063 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0064 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0065 : List (List (List (List ℕ))) :=
  [[[[42135201,141299361],[1882008162,2080336482],[1895652801,1994816961]],[[1882008162,2080336482],[7489644804,7886301444],[5719196322,5917524642]],[[1895652801,1994816961],[5719196322,5917524642],[3879323361,3978487521]]],[[[285055326,483383646],[4180693212,4577349852],[4007197566,4205525886]],[[4180693212,4577349852],[15842857464,16636170744],[11885283612,12281940252]],[[4007197566,4205525886],[11885283612,12281940252],[7989645726,8187974046]]],[[[243612127,342776287],[2300069054,2498397374],[2112236767,2211400927]],[[2300069054,2498397374],[8355980668,8752637308],[6167471294,6365799614]],[[2112236767,2211400927],[6167471294,6365799614],[4111014367,4210178527]]]]

private theorem identity_0065 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(4681689 / 154255360 : ℝ)) =
      tensor4 coefficients_0065 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0065, p_variance] <;> ring

private theorem negative_0065 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0065 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0065] at hp
  linarith only [hp]

private theorem node_0070 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 32 : ℝ)
  · exact node_0071 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0065 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private def coefficients_0066 : List (List (List (List ℕ))) :=
  [[[[957856969,709946569],[876511369,628600969]],[[1456692338,960871538],[1294001138,798180338]],[[463972969,216062569],[382627369,134716969]]],[[[1875145338,1379324538],[1711292058,1215471258]],[[2831666436,1840024836],[2503959876,1512318276]],[[886796298,390975498],[722943018,227122218]]],[[[916963551,669053151],[834455871,586545471]],[[1374324462,878503662],[1209309102,713488302]],[[422498511,174588111],[339990831,92080431]]]]

private theorem identity_0066 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(10231159 / 110182400 : ℝ)) =
      tensor4 coefficients_0066 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0066, p_headsq] <;> ring

private theorem negative_0066 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0066 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0066] at hp
  linarith only [hp]

private def coefficients_0067 : List (List (List (List ℕ))) :=
  [[[[222150490,271732570],[1368154580,1467318740],[1173894010,1223476090]],[[903903620,1003067780],[3688052680,3886381000],[2839928900,2939093060]],[[688725610,738307690],[2333843060,2433007220],[1673007370,1722589450]]],[[[547778200,646942360],[2950817120,3149145440],[2458818760,2557982920]],[[2018538440,2216866760],[7812674800,8209331440],[5905696040,6104024360]],[[1484705200,1583869360],[4889747600,5088075920],[3460822240,3559986400]]],[[[325973711,375555791],[1583354542,1682518702],[1285270751,1334852831]],[[1115326822,1214490982],[4126006124,4324334444],[3066459142,3165623302]],[[796325591,845907671],[2556596542,2655760702],[1788160871,1837742951]]]]

private theorem identity_0067 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(22215049 / 69414912 : ℝ)) =
      tensor4 coefficients_0067 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0067, p_variance] <;> ring

private theorem negative_0067 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0067 ((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0067] at hp
  linarith only [hp]

private theorem node_0073 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0066 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0067 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0068 : List (List (List (List ℕ))) :=
  [[[[91717281,190881441],[1981172322,2179500642],[1945234881,2044399041]],[[1981172322,2179500642],[7687973124,8084629764],[5818360482,6016688802]],[[1945234881,2044399041],[5818360482,6016688802],[3928905441,4028069601]]],[[[384219486,582547806],[4379021532,4775678172],[4106361726,4304690046]],[[4379021532,4775678172],[16239514104,17032827384],[12083611932,12480268572]],[[4106361726,4304690046],[12083611932,12480268572],[8088809886,8287138206]]],[[[293194207,392358367],[2399233214,2597561534],[2161818847,2260983007]],[[2399233214,2597561534],[8554308988,8950965628],[6266635454,6464963774]],[[2161818847,2260983007],[6266635454,6464963774],[4160596447,4259760607]]]]

private theorem identity_0068 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(10190809 / 154255360 : ℝ)) =
      tensor4 coefficients_0068 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0068, p_variance] <;> ring

private theorem negative_0068 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0068 ((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0068] at hp
  linarith only [hp]

private theorem node_0072 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 32 : ℝ)
  · exact node_0073 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0068 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u)

private theorem node_0069 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0070 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0072 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0061 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0062 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0069 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private theorem node_0060 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0054 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0061 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0047 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 16 : ℝ)
  · exact node_0048 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0060 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0069 : List (List (List (List ℕ))) :=
  [[[[7284347,26189494,16968347],[2345507,16311814,12029507]],[[12223187,36067174,21907187],[7284347,26189494,16968347]]],[[[13001008,49243616,32369008],[2832808,28907216,22200808]],[[23169208,69580016,42537208],[13001008,49243616,32369008]]],[[[5626882,22874564,15310882],[397522,12415844,10081522]],[[10856242,33333284,20540242],[5626882,22874564,15310882]]]]

private theorem identity_0069 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(198761 / 15494400 : ℝ)) =
      tensor4 coefficients_0069 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0069, p_coupled] <;> ring

private theorem negative_0069 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0069 ((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0069] at hp
  linarith only [hp]

private theorem node_0046 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0047 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0069 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0035 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0036 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0046 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0029 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0035 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0070 : List (List (List (List ℕ))) :=
  [[[[8109467,23966134,11983067],[3461147,14669494,7334747]],[[12757787,33262774,16631387],[8109467,23966134,11983067]]],[[[14830806,45156012,22578006],[4953126,25400652,12700326]],[[24708486,64911372,32455686],[14830806,45156012,22578006]]],[[[6541781,20830762,10415381],[1312421,10372042,5186021]],[[11771141,31289482,15644741],[6541781,20830762,10415381]]]]

private theorem identity_0070 (x0 x1 x2 x3 : ℝ) :
    (15494400 : ℝ)*(-p_coupled x0 x1 x2 x3-(1312421 / 15494400 : ℝ)) =
      tensor4 coefficients_0070 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0070, p_coupled] <;> ring

private theorem negative_0070 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0070 ((x0-0)/(1 / 4 : ℝ)) (1-((x0-0)/(1 / 4 : ℝ))) ((x1-0)/(1 / 2 : ℝ)) (1-((x1-0)/(1 / 2 : ℝ))) ((x2-0)/(1 / 2 : ℝ)) (1-((x2-0)/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0070] at hp
  linarith only [hp]

theorem exclude_01 (x0 x1 x2 x3 : ℝ)
    (h0l : 0 ≤ x0) (h0u : x0 ≤ (1 / 4 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  exact (not_lt_of_ge h.coupled) (negative_0070 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part02
