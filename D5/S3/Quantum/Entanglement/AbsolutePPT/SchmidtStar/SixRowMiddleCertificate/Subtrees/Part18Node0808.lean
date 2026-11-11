/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part18Node0808
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part18Node0808
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part18.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part18Node0808.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part18Node0808
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0803 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0803 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0803 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0803, p_qbox] <;> ring

private theorem negative_0803 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0803 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0803] at hp
  linarith only [hp]

private def coefficients_0804 : List (List (List (List ℕ))) :=
  [[[[868249297,620338897],[765986257,518075857]],[[1406467874,910647074],[1201941794,706120994]],[[503356177,255445777],[401093137,153182737]]],[[[1687722786,1191901986],[1482034626,986213826]],[[2714803092,1723161492],[2303426772,1311785172]],[[957355506,461534706],[751667346,255846546]]],[[[819148671,571238271],[715723551,467813151]],[[1307685582,811864782],[1100835342,605014542]],[[453674511,205764111],[350249391,102338991]]]]

private theorem identity_0804 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(11370999 / 110182400 : ℝ)) =
      tensor4 coefficients_0804 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0804, p_headsq] <;> ring

private theorem negative_0804 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0804 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0804] at hp
  linarith only [hp]

private def coefficients_0805 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0805 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0805 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0805, p_qmass] <;> ring

private theorem negative_0805 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0805 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0805] at hp
  linarith only [hp]

private def coefficients_0806 : List (List (List (List ℕ))) :=
  [[[[5970112,55552192],[467475584,566639744],[468477952,518060032]],[[462827264,561991424],[1852994368,2051322688],[1404112064,1503276224]],[[463829632,513411712],[1399463744,1498627904],[942606592,992188672]]],[[[108989680,208153840],[1132826840,1331155160],[1037782120,1136946280]],[[1123530200,1321858520],[4109293600,4505950240],[3013653320,3211981640]],[[1028485480,1127649640],[3004356680,3202685000],[1989816160,2088980320]]],[[[103365569,152947649],[666043258,765207418],[569650169,619232249]],[[661394938,760559098],[2257683236,2456011556],[1610233258,1709397418]],[[565001849,614583929],[1605584938,1704749098],[1047555569,1097137649]]]]

private theorem identity_0806 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(93283 / 10846080 : ℝ)) =
      tensor4 coefficients_0806 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0806, p_variance] <;> ring

private theorem negative_0806 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0806 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0806] at hp
  linarith only [hp]

private theorem node_0814 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0805 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0806 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0813 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0804 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0814 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0807 : List (List (List (List ℕ))) :=
  [[[[422447681,298492481],[370735121,246779921]],[[679589482,431679082],[576164362,328253962]],[[239710601,115755401],[187998041,64042841]]],[[[820182640,572272240],[716176480,468266080]],[[1309463000,813642200],[1101450680,605629880]],[[454417960,206507560],[350411800,102501400]]],[[[397572550,273617350],[345278950,221323750]],[[629548700,381638300],[524961500,277051100]],[[214544950,90589750],[162251350,38296150]]]]

private theorem identity_0807 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(765923 / 9916416 : ℝ)) =
      tensor4 coefficients_0807 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0807, p_headsq] <;> ring

private theorem negative_0807 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0807 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0807] at hp
  linarith only [hp]

private def coefficients_0808 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0808 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0808 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0808, p_qmass] <;> ring

private theorem negative_0808 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0808 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0808] at hp
  linarith only [hp]

private def coefficients_0809 : List (List (List (List ℕ))) :=
  [[[[109335681,208499841],[1137295602,1335623922],[1041904881,1141069041]],[[1127998962,1326327282],[4125784644,4522441284],[3025675602,3224003922]],[[1032608241,1131772401],[3016378962,3214707282],[1997715681,2096879841]]],[[[414154278,612482598],[2673110556,3069767196],[2286846198,2485174518]],[[2654517276,3051173916],[9063715032,9857028312],[6464977596,6861634236]],[[2268252918,2466581238],[6446384316,6843040956],[4206021318,4404349638]]],[[[305510599,404674759],[1537198958,1735527278],[1245633319,1344797479]],[[1527902318,1726230638],[4940698396,5337355036],[3440685998,3639014318]],[[1236336679,1335500839],[3431389358,3629717678],[2208997639,2308161799]]]]

private theorem identity_0809 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(1735487 / 22036480 : ℝ)) =
      tensor4 coefficients_0809 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0809, p_variance] <;> ring

private theorem negative_0809 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0809 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0809] at hp
  linarith only [hp]

private theorem node_0816 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0808 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0809 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0815 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0807 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0816 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0812 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (25 / 32 : ℝ)
  · exact node_0813 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0815 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0810 : List (List (List (List ℕ))) :=
  [[[[33,49],[48,80],[6,22]]]]

private theorem identity_0810 (x0 x1 x2 x3 : ℝ) :
    (64 : ℝ)*(-p_qmass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0810 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0810, p_qmass] <;> ring

private theorem negative_0810 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0810 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0810] at hp
  linarith only [hp]

private theorem node_0811 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0812 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0810 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0810 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0803 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0811 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0811 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0811 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0811 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0811, p_qbox] <;> ring

private theorem negative_0811 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0811 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0811] at hp
  linarith only [hp]

private def coefficients_0812 : List (List (List (List ℕ))) :=
  [[[[620968,25412008],[230171696,279753776],[236523208,261314248]],[[225523376,275105456],[925175392,1024339552],[713596976,763179056]],[[231874888,256665928],[708948656,758530736],[484046248,508837288]]],[[[49766664,99348744],[561169608,660333768],[525347904,574929984]],[[551872968,651037128],[2059556736,2257885056],[1535573688,1634737848]],[[516051264,565633344],[1526277048,1625441208],[1024170744,1073752824]]],[[[49491697,74282737],[331689914,381271994],[289170697,313961737]],[[327041594,376623674],[1135765348,1234929508],[822668714,872250794]],[[284522377,309313417],[818020394,867602474],[540470497,565261537]]]]

private theorem identity_0812 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(77621 / 21692160 : ℝ)) =
      tensor4 coefficients_0812 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0812, p_variance] <;> ring

private theorem negative_0812 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0812 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0812] at hp
  linarith only [hp]

private theorem node_0817 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0811 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0812 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0809 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0810 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0817 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0813 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0813 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0813 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0813, p_qbox] <;> ring

private theorem negative_0813 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0813 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0813] at hp
  linarith only [hp]

private def coefficients_0814 : List (List (List (List ℕ))) :=
  [[[[821216609,573306209],[716629409,468719009]],[[1311240418,815419618],[1102066018,606245218]],[[455161409,207251009],[350574209,102663809]]],[[[1592358138,1096537338],[1382021658,886200858]],[[2521749636,1530108036],[2101076676,1109435076]],[[859666698,363845898],[649330218,153509418]]],[[[770816711,522906311],[665067431,417157031]],[[1209859582,714038782],[998361022,502540222]],[[404180471,156270071],[298431191,50520791]]]]

private theorem identity_0814 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(50520791 / 991641600 : ℝ)) =
      tensor4 coefficients_0814 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0814, p_headsq] <;> ring

private theorem negative_0814 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0814 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0814] at hp
  linarith only [hp]

private def coefficients_0815 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0815 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0815 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0815, p_qmass] <;> ring

private theorem negative_0815 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0815 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0815] at hp
  linarith only [hp]

private def coefficients_0816 : List (List (List (List ℕ))) :=
  [[[[103711570,153293650],[670512020,769676180],[573772930,623355010]],[[665863700,765027860],[2274174280,2472502600],[1622255540,1721419700]],[[569124610,618706690],[1617607220,1716771380],[1055455090,1105037170]]],[[[305856600,405020760],[1541667720,1739996040],[1249756080,1348920240]],[[1532371080,1730699400],[4957189440,5353846080],[3452708280,3651036600]],[[1240459440,1339623600],[3443411640,3641739960],[2216897160,2316061320]]],[[[202491031,252073111],[871847702,971011862],[676329151,725911231]],[[867199382,966363542],[2684399164,2882727484],[1831144742,1930308902]],[[671680831,721262911],[1826496422,1925660582],[1161788071,1211370151]]]]

private theorem identity_0816 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(10371157 / 69414912 : ℝ)) =
      tensor4 coefficients_0816 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0816, p_variance] <;> ring

private theorem negative_0816 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0816 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0816] at hp
  linarith only [hp]

private theorem node_0823 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0815 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0816 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0822 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0814 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0823 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0817 : List (List (List (List ℕ))) :=
  [[[[398606519,274651319],[345731879,221776679]],[[631326118,383415718],[525576838,277666438]],[[215288399,91333199],[162413759,38458559]]],[[[771850680,523940280],[665520360,417609960]],[[1211637000,715816200],[998976360,503155560]],[[404923920,157013520],[298593600,50683200]]],[[[373081752,249126552],[319626072,195670872]],[[579986064,332075664],[473074704,225164304]],[[189473112,65517912],[136017432,12062232]]]]

private theorem identity_0817 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(167531 / 6886400 : ℝ)) =
      tensor4 coefficients_0817 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0817, p_headsq] <;> ring

private theorem negative_0817 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0817 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0817] at hp
  linarith only [hp]

private def coefficients_0818 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0818 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0818 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0818, p_qmass] <;> ring

private theorem negative_0818 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0818 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0818] at hp
  linarith only [hp]

private def coefficients_0819 : List (List (List (List ℕ))) :=
  [[[[306202601,405366761],[1546136482,1744464802],[1253878841,1353043001]],[[1536839842,1735168162],[4973680484,5370337124],[3464730562,3663058882]],[[1244582201,1343746361],[3455433922,3653762242],[2224796681,2323960841]]],[[[810656126,1008984446],[3496328332,3892984972],[2713562126,2911890446]],[[3477735052,3874391692],[10770578744,11563892024],[7348623532,7745280172]],[[2694968846,2893297166],[7330030252,7726686892],[4662951326,4861279646]]],[[[505145527,604309687],[1951575854,2149904174],[1460375287,1559539447]],[[1942279214,2140607534],[5799666268,6196322908],[3885276974,4083605294]],[[1451078647,1550242807],[3875980334,4074308654],[2438846647,2538010807]]]]

private theorem identity_0819 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(306202601 / 1388298240 : ℝ)) =
      tensor4 coefficients_0819 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0819, p_variance] <;> ring

private theorem negative_0819 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0819 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0819] at hp
  linarith only [hp]

private theorem node_0825 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0818 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0819 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0824 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0817 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0825 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0821 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (27 / 32 : ℝ)
  · exact node_0822 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0824 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0820 : List (List (List (List ℕ))) :=
  [[[[33,49],[48,80],[6,22]]]]

private theorem identity_0820 (x0 x1 x2 x3 : ℝ) :
    (64 : ℝ)*(-p_qmass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0820 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0820, p_qmass] <;> ring

private theorem negative_0820 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0820 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0820] at hp
  linarith only [hp]

private theorem node_0820 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0821 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0820 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0819 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0813 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0820 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0821 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0821 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0821 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0821, p_qbox] <;> ring

private theorem negative_0821 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0821 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0821] at hp
  linarith only [hp]

private def coefficients_0822 : List (List (List (List ℕ))) :=
  [[[[50112665,99694745],[565638370,664802530],[529470665,579052745]],[[556341730,655505890],[2076047780,2274376100],[1547595970,1646760130]],[[520174025,569756105],[1538299330,1637463490],[1032070265,1081652345]]],[[[198658790,297822950],[1335697180,1534025500],[1164928310,1264092470]],[[1317103900,1515432220],[4576043480,4972700120],[3314719420,3513047740]],[[1146335030,1245499190],[3296126140,3494454460],[2177681030,2276845190]]],[[[149238127,198820207],[771442814,870606974],[636149647,685731727]],[[762146174,861310334],[2502763708,2701092028],[1768507454,1867671614]],[[626853007,676435087],[1759210814,1858374974],[1146302767,1195884847]]]]

private theorem identity_0822 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(10022533 / 69414912 : ℝ)) =
      tensor4 coefficients_0822 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0822, p_variance] <;> ring

private theorem negative_0822 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0822 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0822] at hp
  linarith only [hp]

private theorem node_0826 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0821 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0822 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0818 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0819 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0826 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 16 : ℝ)
  · exact node_0809 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0818 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part18Node0808
