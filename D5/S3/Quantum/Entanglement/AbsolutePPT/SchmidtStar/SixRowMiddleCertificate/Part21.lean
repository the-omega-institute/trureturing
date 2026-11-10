/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part21
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part21
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleScalar.middle_strict; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part21.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part21
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0908 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0908 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0908 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0908, p_qbox] <;> ring

private theorem negative_0908 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0908 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0908] at hp
  linarith only [hp]

private def coefficients_0909 : List (List (List (List ℕ))) :=
  [[[[272548457,148593257],[221416937,97461737]],[[519531154,271620754],[417268114,169357714]],[[212120297,88165097],[160988777,37033577]]],[[[521290050,273379650],[417864930,169954530]],[[990867540,495046740],[784017300,288196500]],[[399852690,151942290],[296427570,48517170]]],[[[248416775,124461575],[196123175,72167975]],[[470686750,222776350],[366099550,118189150]],[[187407575,63452375],[135113975,11158775]]]]

private theorem identity_0909 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(446351 / 9916416 : ℝ)) =
      tensor4 coefficients_0909 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0909, p_headsq] <;> ring

private theorem negative_0909 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0909 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0909] at hp
  linarith only [hp]

private def coefficients_0910 : List (List (List (List ℕ))) :=
  [[[[127641187,379237574,236101987],[25378147,174711494,133838947]],[[229904227,583763654,338365027],[127641187,379237574,236101987]]],[[[234396486,716703372,451318086],[28708326,305327052,245629926]],[[440084646,1128079692,657006246],[234396486,716703372,451318086]]],[[[106575741,337106682,215036541],[3150621,130256442,111611421]],[[210000861,543956922,318461661],[106575741,337106682,215036541]]]]

private theorem identity_0910 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(350069 / 110182400 : ℝ)) =
      tensor4 coefficients_0910 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0910, p_coupled] <;> ring

private theorem negative_0910 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0910 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0910] at hp
  linarith only [hp]

private def coefficients_0911 : List (List (List (List ℕ))) :=
  [[[[368217281,244262081],[316504721,192549521]],[[640853482,392943082],[537428362,289517962]],[[255205001,131249801],[203492441,79537241]]],[[[711721840,463811440],[607715680,359805280]],[[1231991000,736170200],[1023978680,528157880]],[[485406760,237496360],[381400600,133490200]]],[[[343342150,219386950],[291048550,167093350]],[[590812700,342902300],[486225500,238315100]],[[230039350,106084150],[177745750,53790550]]]]

private theorem identity_0911 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1075811 / 9916416 : ℝ)) =
      tensor4 coefficients_0911 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0911, p_headsq] <;> ring

private theorem negative_0911 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0911 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0911] at hp
  linarith only [hp]

private def coefficients_0912 : List (List (List (List ℕ))) :=
  [[[[71717411,205412422,125947811],[20004851,101987302,74235251]],[[97573691,257124982,151804091],[45861131,153699862,100091531]]],[[[133102840,390160880,241563640],[29096680,182148560,137557480]],[[185105920,494167040,293566720],[81099760,286154720,189560560]]],[[[61295650,184568900,115526050],[9002050,79981700,63232450]],[[87442450,236862500,141672850],[35148850,132275300,89379250]]]]

private theorem identity_0912 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(180041 / 9916416 : ℝ)) =
      tensor4 coefficients_0912 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0912, p_coupled] <;> ring

private theorem negative_0912 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0912 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0912] at hp
  linarith only [hp]

private theorem node_0919 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0911 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0912 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0918 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (25 / 32 : ℝ)
  · exact (not_lt_of_ge h.coupled) (negative_0910 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0919 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0913 : List (List (List (List ℕ))) :=
  [[[[7,11],[1,5]]]]

private theorem identity_0913 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0913 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0913, p_qbox] <;> ring

private theorem negative_0913 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0913 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0913] at hp
  linarith only [hp]

private theorem node_0917 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact node_0918 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0913 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0914 : List (List (List (List ℕ))) :=
  [[[[13016488,37807528],[250314416,299896496],[244270408,269061448]],[[254962736,304544816],[974757472,1073921632],[733739696,783321776]],[[248918728,273709768],[738388016,787970096],[496441768,521232808]]],[[[74557704,124139784],[601455048,700619208],[540842304,590424384]],[[610751688,709915848],[2158720896,2357049216],[1575859128,1675023288]],[[550138944,599721024],[1585155768,1684319928],[1048961784,1098543864]]],[[[61887217,86678257],[351832634,401414714],[296917897,321708937]],[[356480954,406063034],[1185347428,1284511588],[842811434,892393514]],[[301566217,326357257],[847459754,897041834],[552866017,577657057]]]]

private theorem identity_0914 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(1627061 / 21692160 : ℝ)) =
      tensor4 coefficients_0914 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0914, p_variance] <;> ring

private theorem negative_0914 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0914 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0914] at hp
  linarith only [hp]

private theorem node_0916 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0917 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0914 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0915 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0909 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0916 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0915 : List (List (List (List ℕ))) :=
  [[[[124157537,62179937],[111084137,49106537]],[[235241674,111286474],[209094874,85139674]],[[93652937,31675337],[80579537,18601937]]],[[[236086824,112131624],[209649504,85694304]],[[445736328,197825928],[392861688,144951288]],[[174787104,50831904],[148349784,24394584]]],[[[111766878,49789278],[98402958,36425358]],[[210169836,86214636],[183441996,59486796]],[[80971758,18994158],[67607838,5630238]]]]

private theorem identity_0915 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(312791 / 6886400 : ℝ)) =
      tensor4 coefficients_0915 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0915, p_headsq] <;> ring

private theorem negative_0915 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0915 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0915] at hp
  linarith only [hp]

private def coefficients_0916 : List (List (List (List ℕ))) :=
  [[[[102271697,71282897],[89198297,58209497]],[[191469994,129492394],[165323194,103345594]],[[71767097,40778297],[58693697,27704897]]],[[[192024624,130047024],[165587304,103609704]],[[357611928,233656728],[304737288,180782088]],[[130724904,68747304],[104287584,42309984]]],[[[89590518,58601718],[76226598,45237798]],[[165817116,103839516],[139089276,77111676]],[[58795398,27806598],[45431478,14442678]]]]

private theorem identity_0916 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(802371 / 6886400 : ℝ)) =
      tensor4 coefficients_0916 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0916, p_headsq] <;> ring

private theorem negative_0916 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0916 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0916] at hp
  linarith only [hp]

private def coefficients_0917 : List (List (List (List ℕ))) :=
  [[[[667531529,419621129],[562944329,315033929]],[[1230475858,734655058],[1021301458,525480658]],[[423494729,175584329],[318907529,70997129]]],[[[1284987978,789167178],[1074651498,578830698]],[[2359639476,1367997876],[1938966516,947324916]],[[795752298,299931498],[585415818,89595018]]],[[[617131631,369221231],[511382351,263471951]],[[1128513982,632693182],[917015422,421194622]],[[371932751,124022351],[266183471,18273071]]]]

private theorem identity_0917 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(18273071 / 991641600 : ℝ)) =
      tensor4 coefficients_0917 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0917, p_headsq] <;> ring

private theorem negative_0917 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0917 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0917] at hp
  linarith only [hp]

private def coefficients_0918 : List (List (List (List ℕ))) :=
  [[[[282398519,158443319],[229523879,105568679]],[[538359718,290449318],[432610438,184700038]],[[238529999,114574799],[185655359,61700159]]],[[[539434680,291524280],[433104360,185193960]],[[1025704200,529883400],[813043560,317222760]],[[451407120,203496720],[345076800,97166400]]],[[[256873752,132918552],[203418072,79462872]],[[487019664,239109264],[380108304,132197904]],[[212714712,88759512],[159259032,35303832]]]]

private theorem identity_0918 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(490331 / 6886400 : ℝ)) =
      tensor4 coefficients_0918 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0918, p_headsq] <;> ring

private theorem negative_0918 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0918 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0918] at hp
  linarith only [hp]

private def coefficients_0919 : List (List (List (List ℕ))) :=
  [[[[264676799,140721599],[238239479,114284279]],[[468053878,220143478],[415179238,167268838]],[[185945879,61990679],[159508559,35553359]]],[[[503700720,255790320],[450535560,202625160]],[[884511480,388690680],[778181160,282360360]],[[345948360,98037960],[292783200,44872800]]],[[[238861512,114906312],[212133672,88178472]],[[416132784,168222384],[362677104,114766704]],[[159840072,35884872],[133112232,9157032]]]]

private theorem identity_0919 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(127181 / 6886400 : ℝ)) =
      tensor4 coefficients_0919 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0919, p_headsq] <;> ring

private theorem negative_0919 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0919 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0919] at hp
  linarith only [hp]

private def coefficients_0920 : List (List (List (List ℕ))) :=
  [[[[436355561,535519721],[1787849122,1986177442],[1365438521,1464602681]],[[1815739042,2014067362],[5494292324,5890948964],[3706443202,3904771522]],[[1393328441,1492492601],[3734333122,3932661442],[2354949641,2454113801]]],[[[1070962046,1269290366],[3979753612,4376410252],[2936681486,3135009806]],[[4035533452,4432190092],[11811802424,12605115704],[7832048812,8228705452]],[[2992461326,3190789646],[7887828652,8284485292],[4923257246,5121585566]]],[[[635298487,734462647],[2193288494,2391616814],[1571934967,1671099127]],[[2221178414,2419506734],[6320278108,6716934748],[4126989614,4325317934]],[[1599824887,1698989047],[4154879534,4353207854],[2568999607,2668163767]]]]

private theorem identity_0920 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(436355561 / 1388298240 : ℝ)) =
      tensor4 coefficients_0920 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0920, p_variance] <;> ring

private theorem negative_0920 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0920 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0920] at hp
  linarith only [hp]

private theorem node_0925 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0919 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0920 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0924 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0918 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0925 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0923 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (27 / 32 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0917 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u)
  · exact node_0924 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0922 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0916 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0923 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0921 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0915 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0922 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0921 : List (List (List (List ℕ))) :=
  [[[[712755809,464845409],[608168609,360258209]],[[1233768418,737947618],[1024594018,528773218]],[[486150209,238239809],[381563009,133652609]]],[[[1375436538,879615738],[1165100058,669279258]],[[2366805636,1375164036],[1946132676,954491076]],[[921644298,425823498],[711307818,215487018]]],[[[662355911,414445511],[556606631,308696231]],[[1132387582,636566782],[920889022,425068222]],[[435169271,187258871],[329419991,81509591]]]]

private theorem identity_0921 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(81509591 / 991641600 : ℝ)) =
      tensor4 coefficients_0921 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0921, p_headsq] <;> ring

private theorem negative_0921 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0921 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0921] at hp
  linarith only [hp]

private def coefficients_0922 : List (List (List (List ℕ))) :=
  [[[[133773659,391502518,242234459],[29186459,182328118,137647259]],[[186067259,496089718,294528059],[81480059,286915318,189940859]]],[[[246524238,740958876,463445838],[36187758,320285916,253109358]],[[351692478,951295356,568614078],[141355998,530622396,358277598]]],[[[112571021,349097242,221031821],[6821741,137598682,115282541]],[[165445661,454846522,273906461],[59696381,243347962,168157181]]]]

private theorem identity_0922 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(6821741 / 991641600 : ℝ)) =
      tensor4 coefficients_0922 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0922, p_coupled] <;> ring

private theorem negative_0922 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0922 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0922] at hp
  linarith only [hp]

private theorem node_0929 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0921 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0922 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0923 : List (List (List (List ℕ))) :=
  [[[[344376119,220420919],[291501479,167546279]],[[592590118,344679718],[486840838,238930438]],[[230782799,106827599],[177908159,53952959]]],[[[663389880,415479480],[557059560,309149160]],[[1134165000,638344200],[921504360,425683560]],[[435912720,188002320],[329582400,81672000]]],[[[318851352,194896152],[265395672,141440472]],[[541250064,293339664],[434338704,186428304]],[[204967512,81012312],[151511832,27556632]]]]

private theorem identity_0923 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(382731 / 6886400 : ℝ)) =
      tensor4 coefficients_0923 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0923, p_headsq] <;> ring

private theorem negative_0923 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 16 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0923 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0923] at hp
  linarith only [hp]

private def coefficients_0924 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0924 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 32 : ℝ)) =
      tensor4 coefficients_0924 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0924, p_qbox] <;> ring

private theorem negative_0924 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 16 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0924 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0924] at hp
  linarith only [hp]

private def coefficients_0925 : List (List (List (List ℕ))) :=
  [[[[405366761,504530921],[1735168162,1933496482],[1343746361,1442910521]],[[1744464802,1942793122],[5370337124,5766993764],[3653762242,3852090562]],[[1353043001,1452207161],[3663058882,3861387202],[2323960841,2423125001]]],[[[1008984446,1207312766],[3874391692,4271048332],[2893297166,3091625486]],[[3892984972,4289641612],[11563892024,12357205304],[7726686892,8123343532]],[[2911890446,3110218766],[7745280172,8141936812],[4861279646,5059607966]]],[[[604309687,703473847],[2140607534,2338935854],[1550242807,1649406967]],[[2149904174,2348232494],[6196322908,6592979548],[4074308654,4272636974]],[[1559539447,1658703607],[4083605294,4281933614],[2538010807,2637174967]]]]

private theorem identity_0925 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(405366761 / 1388298240 : ℝ)) =
      tensor4 coefficients_0925 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0925, p_variance] <;> ring

private theorem negative_0925 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (5 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0925 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0925] at hp
  linarith only [hp]

private theorem node_0931 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (3 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0924 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0925 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0930 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0923 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0931 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0928 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (27 / 32 : ℝ)
  · exact node_0929 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0930 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0926 : List (List (List (List ℕ))) :=
  [[[[7,11],[1,5]]]]

private theorem identity_0926 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0926 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0926, p_qbox] <;> ring

private theorem negative_0926 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (5 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0926 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(5 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0926] at hp
  linarith only [hp]

private theorem node_0927 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 8 : ℝ)
  · exact node_0928 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0926 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0927 : List (List (List (List ℕ))) :=
  [[[[74903705,124485785],[605923810,705087970],[544965065,594547145]],[[615220450,714384610],[2175211940,2373540260],[1587881410,1687045570]],[[554261705,603843785],[1597178050,1696342210],[1056861305,1106443385]]],[[[248240870,347405030],[1416268060,1614596380],[1195917110,1295081270]],[[1434861340,1633189660],[4774371800,5171028440],[3395290300,3593618620]],[[1214510390,1313674550],[3413883580,3612211900],[2227263110,2326427270]]],[[[174029167,223611247],[811728254,910892414],[651644047,701226127]],[[821024894,920189054],[2601927868,2800256188],[1808792894,1907957054]],[[660940687,710522767],[1818089534,1917253694],[1171093807,1220675887]]]]

private theorem identity_0927 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(14980741 / 69414912 : ℝ)) =
      tensor4 coefficients_0927 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0927, p_variance] <;> ring

private theorem negative_0927 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0927 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0927] at hp
  linarith only [hp]

private theorem node_0926 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact node_0927 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0927 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0920 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0921 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0926 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0914 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 16 : ℝ)
  · exact node_0915 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0920 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0928 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0928 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0928 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0928, p_qbox] <;> ring

private theorem negative_0928 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0928 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0928] at hp
  linarith only [hp]

private def coefficients_0929 : List (List (List (List ℕ))) :=
  [[[[511878097,263967697],[409615057,161704657]],[[972624674,476803874],[768098594,272277794]],[[425884177,177973777],[323621137,75710737]]],[[[974980386,479159586],[769292226,273471426]],[[1847116692,855475092],[1435740372,444098772]],[[802411506,306590706],[596723346,100902546]]],[[[462777471,214867071],[359352351,111441951]],[[873842382,378021582],[666992142,171171342]],[[376202511,128292111],[272777391,24866991]]]]

private theorem identity_0929 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(2762999 / 110182400 : ℝ)) =
      tensor4 coefficients_0929 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0929, p_headsq] <;> ring

private theorem negative_0929 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0929 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0929] at hp
  linarith only [hp]

private def coefficients_0930 : List (List (List (List ℕ))) :=
  [[[[144781867,351541334,191265067],[42518827,147015254,89002027]],[[195913387,453804374,242396587],[93650347,249278294,140133547]]],[[[266934726,657824652,359901126],[61246566,246448332,154212966]],[[369778806,863512812,462745206],[164090646,452136492,257057046]]],[[[121973301,305924202,168456501],[18548181,99073962,65031381]],[[173685861,409349322,220169061],[70260741,202499082,116743941]]]]

private theorem identity_0930 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_coupled x0 x1 x2 x3-(2060909 / 110182400 : ℝ)) =
      tensor4 coefficients_0930 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0930, p_coupled] <;> ring

private theorem negative_0930 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0930 ((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0930] at hp
  linarith only [hp]

private theorem node_0937 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (25 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0929 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.coupled) (negative_0930 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0931 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0931 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0931 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0931, p_qbox] <;> ring

private theorem negative_0931 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0931 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0931] at hp
  linarith only [hp]

private def coefficients_0932 : List (List (List (List ℕ))) :=
  [[[[187417001,125439401],[161560721,99583121]],[[348977722,225022522],[297265162,173309962]],[[144129521,82151921],[118273241,56295641]]],[[[349830760,225875560],[297827680,173872480]],[[647658440,399748040],[543652280,295741880]],[[262965280,139010080],[210962200,87007000]]],[[[162251350,100273750],[136104550,74126950]],[[298355900,174400700],[246062300,122107100]],[[118673350,56695750],[92526550,30548950]]]]

private theorem identity_0932 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(610979 / 9916416 : ℝ)) =
      tensor4 coefficients_0932 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0932, p_headsq] <;> ring

private theorem negative_0932 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (13 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0932 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0932] at hp
  linarith only [hp]

private def coefficients_0933 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0933 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0933 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0933, p_qbox] <;> ring

private theorem negative_0933 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (13 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0933 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0933] at hp
  linarith only [hp]

private theorem node_0940 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (13 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0932 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qbox) (negative_0933 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0939 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0931 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0940 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0934 : List (List (List (List ℕ))) :=
  [[[[67069091,165126982,90310691],[15356531,61701862,38598131]],[[92925371,216839542,116166971],[41212811,113414422,64454411]]],[[[122644120,307265840,169127320],[18637960,99253520,65121160]],[[174647200,411272000,221130400],[70641040,203259680,117124240]]],[[[55485250,141959300,78726850],[3191650,37372100,26433250]],[[81632050,194252900,104873650],[29338450,89665700,52580050]]]]

private theorem identity_0934 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_coupled x0 x1 x2 x3-(63833 / 9916416 : ℝ)) =
      tensor4 coefficients_0934 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0934, p_coupled] <;> ring

private theorem negative_0934 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0934 ((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(25 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0934] at hp
  linarith only [hp]

private theorem node_0938 (x0 x1 x2 x3 : ℝ)
    (h0l : (25 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0939 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0934 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0936 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (25 / 32 : ℝ)
  · exact node_0937 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0938 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0935 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0935 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0935 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0935, p_qbox] <;> ring

private theorem negative_0935 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0935 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0935] at hp
  linarith only [hp]

private theorem node_0935 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0936 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0935 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0934 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0928 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0935 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0936 : List (List (List (List ℕ))) :=
  [[[[71048627,173086054,86543027],[19917107,70823014,35411507]],[[96614387,224217574,112108787],[45482867,121954534,60977267]]],[[[131654310,325286220,162643110],[28229190,118435980,59217990]],[[183366870,428711340,214355670],[79941750,221861100,110930550]]],[[[60426125,151841050,75920525],[8132525,47253850,23626925]],[[86572925,204134650,102067325],[34279325,99547450,49773725]]]]

private theorem identity_0936 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_coupled x0 x1 x2 x3-(325301 / 9916416 : ℝ)) =
      tensor4 coefficients_0936 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0936, p_coupled] <;> ring

private theorem negative_0936 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0936 ((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0936] at hp
  linarith only [hp]

private theorem node_0933 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (13 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0934 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0936 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0937 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0937 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 16 : ℝ)) =
      tensor4 coefficients_0937 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0937, p_qbox] <;> ring

private theorem negative_0937 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 8 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0937 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0937] at hp
  linarith only [hp]

private def coefficients_0938 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0938 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0938 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0938, p_qbox] <;> ring

private theorem negative_0938 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0938 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0938] at hp
  linarith only [hp]

private def coefficients_0939 : List (List (List (List ℕ))) :=
  [[[[350574209,226619009],[298280609,174325409]],[[648854818,400944418],[544267618,296357218]],[[263418209,139463009],[211124609,87169409]]],[[[650492298,402581898],[545324058,297413658]],[[1195816356,699995556],[985479876,489659076]],[[475599258,227688858],[370431018,122520618]]],[[[299593271,175638071],[246718631,122763431]],[[546311902,298401502],[440562622,192652222]],[[211856231,87901031],[158981591,35026391]]]]

private theorem identity_0939 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(35026391 / 991641600 : ℝ)) =
      tensor4 coefficients_0939 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0939, p_headsq] <;> ring

private theorem negative_0939 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (13 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0939 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0939] at hp
  linarith only [hp]

private def coefficients_0940 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0940 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0940 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0940, p_qbox] <;> ring

private theorem negative_0940 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (13 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0940 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(13 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0940] at hp
  linarith only [hp]

private theorem node_0947 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (13 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0939 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qbox) (negative_0940 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0946 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0938 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0947 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0941 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0941 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0941 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0941, p_qbox] <;> ring

private theorem negative_0941 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0941 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0941] at hp
  linarith only [hp]

private def coefficients_0942 : List (List (List (List ℕ))) :=
  [[[[193579090,243161170],[840950420,940114580],[654343810,703925890]],[[854895380,954059540],[2633644360,2831972680],[1792693940,1891858100]],[[668288770,717870850],[1806638900,1905803060],[1145322610,1194904690]]],[[[485591640,584755800],[1882544520,2080872840],[1410897840,1510062000]],[[1910434440,2108762760],[5676129600,6072786240],[3793585080,3991913400]],[[1438787760,1537951920],[3821475000,4019803320],[2396632200,2495796360]]],[[[292358551,341940631],[1042286102,1141450262],[756900031,806482111]],[[1056231062,1155395222],[3043869244,3242197564],[2001583142,2100747302]],[[770844991,820427071],[2015528102,2114692262],[1251655591,1301237671]]]]

private theorem identity_0942 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(19357909 / 69414912 : ℝ)) =
      tensor4 coefficients_0942 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0942, p_variance] <;> ring

private theorem negative_0942 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0942 ((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0942] at hp
  linarith only [hp]

private theorem node_0948 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0941 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0942 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0945 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (27 / 32 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0946 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0948 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0943 : List (List (List (List ℕ))) :=
  [[[[9,17],[3,11]]]]

private theorem identity_0943 (x0 x1 x2 x3 : ℝ) :
    (32 : ℝ)*(-p_qbox x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0943 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0943, p_qbox] <;> ring

private theorem negative_0943 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (7 / 16 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0943 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0943] at hp
  linarith only [hp]

private def coefficients_0944 : List (List (List (List ℕ))) :=
  [[[[21396161,120560321],[925392082,1123720402],[917940881,1017105041]],[[957930322,1156258642],[3713598404,4110255044],[2783558002,2981886322]],[[950479121,1049643281],[2816096242,3014424562],[1879562081,1978726241]]],[[[233489726,431818046],[2239732492,2636389132],[2034132686,2232461006]],[[2304808972,2701465612],[8220200504,9013513784],[5971171372,6367828012]],[[2099209166,2297537486],[6036247852,6432904492],[3964928606,4163256926]]],[[[212785567,311949727],[1315724414,1514052734],[1116883807,1216047967]],[[1348262654,1546590974],[4509370108,4906026748],[3188997374,3387325694]],[[1149422047,1248586207],[3221535614,3419863934],[2086058527,2185222687]]]]

private theorem identity_0944 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(21396161 / 1388298240 : ℝ)) =
      tensor4 coefficients_0944 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0944, p_variance] <;> ring

private theorem negative_0944 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (7 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0944 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-0)/(1 / 16 : ℝ)) (1-((x1-0)/(1 / 16 : ℝ))) ((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0944] at hp
  linarith only [hp]

private theorem node_0950 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 16 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0943 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0944 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0945 : List (List (List (List ℕ))) :=
  [[[[35341121,134505281],[1845178402,2043506722],[1865617121,1964781281]],[[981171922,1179500242],[5576412644,5973069284],[4706800402,4905128722]],[[959775761,1058939921],[3759124162,3957452482],[2855128241,2954292401]]],[[[261379646,459707966],[4086858652,4483515292],[3937038686,4135367006]],[[2351292172,2747948812],[11960936024,12754249304],[9832763212,10229419852]],[[2117802446,2316130766],[7929857212,8326513852],[5923614446,6121942766]]],[[[226730527,325894687],[2243064254,2441392574],[2072113567,2171277727]],[[1371504254,1569832574],[6387291388,6783948028],[5127346814,5325675134]],[[1158718687,1257882847],[4172117054,4370445374],[3069178207,3168342367]]]]

private theorem identity_0945 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(35341121 / 1388298240 : ℝ)) =
      tensor4 coefficients_0945 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0945, p_variance] <;> ring

private theorem negative_0945 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0945 ((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(27 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0945] at hp
  linarith only [hp]

private theorem node_0949 (x0 x1 x2 x3 : ℝ)
    (h0l : (27 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 16 : ℝ)
  · exact node_0950 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0945 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0944 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (7 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (27 / 32 : ℝ)
  · exact node_0945 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0949 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0946 : List (List (List (List ℕ))) :=
  [[[[4,6],[1,3]]]]

private theorem identity_0946 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0946 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0946, p_qbox] <;> ring

private theorem negative_0946 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (7 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0946 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(7 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0946] at hp
  linarith only [hp]

private theorem node_0943 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (3 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (7 / 8 : ℝ)
  · exact node_0944 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qbox) (negative_0946 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0942 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0937 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0943 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0947 : List (List (List (List ℕ))) :=
  [[[[33248987,81992374,40996187],[7102187,29698774,14849387]],[[46322387,108139174,54069587],[20175587,55845574,27922787]]],[[[61096944,153182688,76591344],[8222304,47433408,23716704]],[[87534264,206057328,103028664],[34659624,100308048,50154024]]],[[[27758178,71010756,35505378],[1030338,17555076,8777538]],[[41122098,97738596,48869298],[14394258,44282916,22141458]]]]

private theorem identity_0947 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_coupled x0 x1 x2 x3-(57241 / 6886400 : ℝ)) =
      tensor4 coefficients_0947 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0947, p_coupled] <;> ring

private theorem negative_0947 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0947 ((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(13 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0947] at hp
  linarith only [hp]

private theorem node_0941 (x0 x1 x2 x3 : ℝ)
    (h0l : (13 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact node_0942 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.coupled) (negative_0947 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0932 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (13 / 16 : ℝ)
  · exact node_0933 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0941 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0913 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0914 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0932 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0912 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0908 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0913 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0948 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0948 (x0 x1 x2 x3 : ℝ) :
    (8 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 8 : ℝ)) =
      tensor4 coefficients_0948 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0948, p_qbox] <;> ring

private theorem negative_0948 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0948 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-0)/(1 / 4 : ℝ)) (1-((x2-0)/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0948] at hp
  linarith only [hp]

private def coefficients_0949 : List (List (List (List ℕ))) :=
  [[[[3544642,15940162],[120392084,145183124],[123819922,136215442]],[[120392084,145183124],[483658888,533240968],[377211764,402002804]],[[123819922,136215442],[377211764,402002804],[260364322,272759842]]],[[[31351648,56142688],[293085656,342667736],[275678968,300470008]],[[293085656,342667736],[1079474272,1178638432],[814278536,863860616]],[[275678968,300470008],[814278536,863860616],[552544528,577335568]]],[[[28153007,40548527],[173385574,198176614],[152205047,164600567]],[[173385574,198176614],[597199388,646781468],[437758774,462549814]],[[152205047,164600567],[437758774,462549814],[292526207,304921727]]]]

private theorem identity_0949 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(1772321 / 21692160 : ℝ)) =
      tensor4 coefficients_0949 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0949, p_variance] <;> ring

private theorem negative_0949 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0949 ((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0949] at hp
  linarith only [hp]

private theorem node_0951 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0948 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0949 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0912 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0951 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part21
