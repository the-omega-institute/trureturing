/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part20Node0889
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part20Node0889
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part20.exclude_00; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Subtrees/Part20Node0889.exclude
   digest: Exact closed-subtree exclusion by the original Nat coefficient identities. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part20Node0889
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0885 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0885 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0885 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0885, p_qbox] <;> ring

private theorem negative_0885 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0885 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0885] at hp
  linarith only [hp]

private def coefficients_0886 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0886 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0886 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0886, p_qmass] <;> ring

private theorem negative_0886 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0886 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0886] at hp
  linarith only [hp]

private def coefficients_0887 : List (List (List (List ℕ))) :=
  [[[[657451369,533496169],[603995689,480040489]],[[982547858,734637458],[875636498,627726098]],[[290234089,166278889],[236778409,112823209]]],[[[1262947346,1015036946],[1155454946,907544546]],[[1860603892,1364783092],[1645619092,1149798292]],[[527931746,280021346],[420439346,172528946]]],[[[605171159,481215959],[551134439,427179239]],[[877406398,629495998],[769332958,521422558]],[[237372839,113417639],[183336119,59380919]]]]

private theorem identity_0887 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(59380919 / 991641600 : ℝ)) =
      tensor4 coefficients_0887 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0887, p_headsq] <;> ring

private theorem negative_0887 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (5 / 16 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0887 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0887] at hp
  linarith only [hp]

private def coefficients_0888 : List (List (List (List ℕ))) :=
  [[[[71,103],[88,152],[8,40]]]]

private theorem identity_0888 (x0 x1 x2 x3 : ℝ) :
    (256 : ℝ)*(-p_qmass x0 x1 x2 x3-(1 / 32 : ℝ)) =
      tensor4 coefficients_0888 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0888, p_qmass] <;> ring

private theorem negative_0888 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (5 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0888 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(5 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0888] at hp
  linarith only [hp]

private theorem node_0896 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0887 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0888 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0895 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0886 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0896 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0889 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0889 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0889 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0889, p_qmass] <;> ring

private theorem negative_0889 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0889 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0889] at hp
  linarith only [hp]

private def coefficients_0890 : List (List (List (List ℕ))) :=
  [[[[202837032,252419112],[876316464,975480624],[680451912,730033992]],[[871668144,970832304],[2700890208,2899218528],[1843167024,1942331184]],[[675803592,725385672],[1838518704,1937682864],[1169687592,1219269672]]],[[[505491528,604655688],[1956044616,2154372936],[1464498048,1563662208]],[[1946747976,2145076296],[5816157312,6212813952],[3897299256,4095627576]],[[1455201408,1554365568],[3888002616,4086330936],[2446746168,2545910328]]],[[[303000497,352582577],[1080420154,1179584314],[784392137,833974217]],[[1075771834,1174935994],[3116651108,3314979428],[2054824234,2153988394]],[[779743817,829325897],[2050175914,2149340074],[1277404577,1326986657]]]]

private theorem identity_0890 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(2817181 / 9640960 : ℝ)) =
      tensor4 coefficients_0890 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0890, p_variance] <;> ring

private theorem negative_0890 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0890 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0890] at hp
  linarith only [hp]

private theorem node_0897 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0889 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0890 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0894 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact node_0895 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0897 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0891 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0891 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0891 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0891, p_qmass] <;> ring

private theorem negative_0891 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0891 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0891] at hp
  linarith only [hp]

private def coefficients_0892 : List (List (List (List ℕ))) :=
  [[[[43039169,142203329],[1002378418,1200706738],[973284209,1072448369]],[[997730098,1196058418],[3860598596,4257255236],[2890758418,3089086738]],[[968635889,1067800049],[2886110098,3084438418],[1931419169,2030583329]]],[[[279543750,477872070],[2399241180,2795897820],[2147587350,2345915670]],[[2389944540,2786601180],[8525272920,9318586200],[6191108220,6587764860]],[[2138290710,2336619030],[6181811580,6578468220],[4071410790,4269739110]]],[[[237196583,336360743],[1398246766,1596575086],[1174995143,1274159303]],[[1393598446,1591926766],[4667442332,5064098972],[3301733806,3500062126]],[[1170346823,1269510983],[3297085486,3495413806],[2140683623,2239847783]]]]

private theorem identity_0892 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(43039169 / 1388298240 : ℝ)) =
      tensor4 coefficients_0892 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0892, p_variance] <;> ring

private theorem negative_0892 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0892 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0892] at hp
  linarith only [hp]

private theorem node_0899 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0891 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0892 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0893 : List (List (List (List ℕ))) :=
  [[[[38390849,137555009],[1918678498,2117006818],[1936067489,2035231649]],[[983785138,1182113458],[5716440356,6113096996],[4844214898,5042543218]],[[959339249,1058503409],[3825651778,4023980098],[2922092369,3021256529]]],[[[270247110,468575430],[4239394860,4636051500],[4080707430,4279035750]],[[2362054620,2758711260],[12252063480,13045376760],[10113128220,10509784860]],[[2119697430,2318025750],[8068448460,8465105100],[6060310710,6258639030]]],[[[232548263,331712423],[2322100366,2520428686],[2145331943,2244496103]],[[1379653486,1577981806],[6538391132,6935047772],[5270297326,5468625646]],[[1161050183,1260214343],[4244180686,4442509006],[3138910343,3238074503]]]]

private theorem identity_0893 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(5484407 / 198328320 : ℝ)) =
      tensor4 coefficients_0893 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0893, p_variance] <;> ring

private theorem negative_0893 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0893 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0893] at hp
  linarith only [hp]

private theorem node_0898 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact node_0899 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0893 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0893 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 32 : ℝ)
  · exact node_0894 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0898 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0894 : List (List (List (List ℕ))) :=
  [[[[33,49],[48,80],[6,22]]]]

private theorem identity_0894 (x0 x1 x2 x3 : ℝ) :
    (64 : ℝ)*(-p_qmass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0894 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0894, p_qmass] <;> ring

private theorem negative_0894 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0894 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0894] at hp
  linarith only [hp]

private theorem node_0892 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0893 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0894 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0891 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0885 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0892 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0895 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0895 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0895 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0895, p_qbox] <;> ring

private theorem negative_0895 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0895 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0895] at hp
  linarith only [hp]

private def coefficients_0896 : List (List (List (List ℕ))) :=
  [[[[49837698,74628738],[336158676,385740756],[293293458,318084498]],[[331510356,381092436],[1152256392,1251420552],[834690996,884273076]],[[288645138,313436178],[830042676,879624756],[548370018,573161058]]],[[[149584128,199166208],[775911576,875075736],[640272408,689854488]],[[766614936,865779096],[2519254752,2717583072],[1780529736,1879693896]],[[630975768,680557848],[1771233096,1870397256],[1154202288,1203784368]]],[[[100092431,124883471],[440444902,490026982],[347324951,372115991]],[[435796582,485378662],[1368382364,1467546524],[946530742,996112822]],[[342676631,367467671],[941882422,991464502],[606178271,630969311]]]]

private theorem identity_0896 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(2768761 / 9640960 : ℝ)) =
      tensor4 coefficients_0896 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0896, p_variance] <;> ring

private theorem negative_0896 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0896 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0896] at hp
  linarith only [hp]

private theorem node_0900 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0895 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0896 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0890 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0891 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0900 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0897 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0897 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0897 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0897, p_qbox] <;> ring

private theorem negative_0897 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0897 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0897] at hp
  linarith only [hp]

private def coefficients_0898 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0898 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0898 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0898, p_qmass] <;> ring

private theorem negative_0898 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0898 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0898] at hp
  linarith only [hp]

private def coefficients_0899 : List (List (List (List ℕ))) :=
  [[[[70058938,119641018],[602044676,701208836],[538958218,588540298]],[[599720516,698884676],[2139563752,2337892072],[1553788196,1652952356]],[[536634058,586216138],[1551464036,1650628196],[1021802458,1071384538]]],[[[237542584,336706744],[1402715528,1601043848],[1179117904,1278282064]],[[1398067208,1596395528],[4683933376,5080590016],[3313756088,3512084408]],[[1174469584,1273633744],[3309107768,3507436088],[2148583144,2247747304]]],[[[167829647,217411727],[801362854,900527014],[640505687,690087767]],[[799038694,898202854],[2545753628,2744081948],[1760659894,1859824054]],[[638181527,687763607],[1758335734,1857499894],[1127126687,1176708767]]]]

private theorem identity_0899 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(35029469 / 347074560 : ℝ)) =
      tensor4 coefficients_0899 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0899, p_variance] <;> ring

private theorem negative_0899 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0899 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0899] at hp
  linarith only [hp]

private theorem node_0906 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0898 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0899 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0900 : List (List (List (List ℕ))) :=
  [[[[67734778,117316858],[1063971476,1163135636],[1024126618,1073708698]],[[592748036,691912196],[3075038152,3273366472],[2538069956,2637234116]],[[531985738,581567818],[2025011636,2124175796],[1520915818,1570497898]]],[[[232894264,332058424],[2330345888,2528674208],[2153231464,2252395624]],[[1384122248,1582450568],[6562435696,6959092336],[5289873128,5488201448]],[[1165172944,1264337104],[4259979728,4458308048],[3150586624,3249750784]]],[[[165505487,215087567],[1267066414,1366230574],[1129450847,1179032927]],[[792066214,891230374],[3488781548,3687109868],[2752495174,2851659334]],[[633533207,683115287],[2235660094,2334824254],[1630016807,1679598887]]]]

private theorem identity_0900 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(33867389 / 347074560 : ℝ)) =
      tensor4 coefficients_0900 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0900, p_variance] <;> ring

private theorem negative_0900 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0900 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0900] at hp
  linarith only [hp]

private theorem node_0905 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact node_0906 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0900 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0901 : List (List (List (List ℕ))) :=
  [[[[137,265],[202,458],[47,175]]]]

private theorem identity_0901 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(47 / 512 : ℝ)) =
      tensor4 coefficients_0901 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0901, p_qmass] <;> ring

private theorem negative_0901 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0901 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0901] at hp
  linarith only [hp]

private def coefficients_0902 : List (List (List (List ℕ))) :=
  [[[[237888585,337052745],[1407184290,1605512610],[1183240665,1282404825]],[[1402535970,1600864290],[4700424420,5097081060],[3325778370,3524106690]],[[1178592345,1277756505],[3321130050,3519458370],[2156482665,2255646825]]],[[[672010590,870338910],[3214388940,3611045580],[2570268270,2768596590]],[[3205092300,3601748940],[10215996600,11009309880],[7066684140,7463340780]],[[2560971630,2759299950],[7057387500,7454044140],[4524305790,4722634110]]],[[[434814007,533978167],[1808588654,2006916974],[1387719607,1486883767]],[[1803940334,2002268654],[5518340188,5914996828],[3742289774,3940618094]],[[1383071287,1482235447],[3737641454,3935969774],[2368515127,2467679287]]]]

private theorem identity_0902 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(5286413 / 30851072 : ℝ)) =
      tensor4 coefficients_0902 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0902, p_variance] <;> ring

private theorem negative_0902 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0902 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0902] at hp
  linarith only [hp]

private theorem node_0908 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.qmass) (negative_0901 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0902 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0903 : List (List (List (List ℕ))) :=
  [[[[233240265,332404425],[2338591410,2536919730],[2161130985,2260295145]],[[1388591010,1586919330],[6586480260,6983136900],[5309448930,5507777250]],[[1169295705,1268459865],[4275778770,4474107090],[3162262905,3261427065]]],[[[662713950,861042270],[5084756700,5481413340],[4533602430,4731930750]],[[3177202380,3573859020],[14003215320,14796528600],[11049132300,11445788940]],[[2542378350,2740706670],[8974238460,9370895100],[6543419790,6741748110]]],[[[430165687,529329847],[2747549294,2945877614],[2373163447,2472327607]],[[1789995374,1988323694],[7419503068,7816159708],[5741067374,5939395694]],[[1373774647,1472938807],[4699843694,4898172014],[3381848887,3481013047]]]]

private theorem identity_0903 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(5183117 / 30851072 : ℝ)) =
      tensor4 coefficients_0903 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0903, p_variance] <;> ring

private theorem negative_0903 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0903 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0903] at hp
  linarith only [hp]

private theorem node_0907 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact node_0908 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0903 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0904 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 32 : ℝ)
  · exact node_0905 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0907 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0904 : List (List (List (List ℕ))) :=
  [[[[33,49],[48,80],[6,22]]]]

private theorem identity_0904 (x0 x1 x2 x3 : ℝ) :
    (64 : ℝ)*(-p_qmass x0 x1 x2 x3-(3 / 32 : ℝ)) =
      tensor4 coefficients_0904 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0904, p_qmass] <;> ring

private theorem negative_0904 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (3 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0904 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(3 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0904] at hp
  linarith only [hp]

private theorem node_0903 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 8 : ℝ)
  · exact node_0904 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0904 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private theorem node_0902 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0897 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact node_0903 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0905 : List (List (List (List ℕ))) :=
  [[[[7,15],[1,9]]]]

private theorem identity_0905 (x0 x1 x2 x3 : ℝ) :
    (16 : ℝ)*(-p_qbox x0 x1 x2 x3-(1 / 16 : ℝ)) =
      tensor4 coefficients_0905 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0905, p_qbox] <;> ring

private theorem negative_0905 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_qbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0905 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0905] at hp
  linarith only [hp]

private def coefficients_0906 : List (List (List (List ℕ))) :=
  [[[[149930129,199512209],[780380338,879544498],[644395169,693977249]],[[771083698,870247858],[2535745796,2734074116],[1792552018,1891716178]],[[635098529,684680609],[1783255378,1882419538],[1162101809,1211683889]]],[[[401061726,500225886],[1770717132,1969045452],[1397545326,1496709486]],[[1752123852,1950452172],[5506511544,5903168184],[3810167532,4008495852]],[[1378952046,1478116206],[3791574252,3989902572],[2440512126,2539676286]]],[[[251823599,301405679],[991720798,1090884958],[753842159,803424239]],[[982424158,1081588318],[2973533756,3171862076],[2018999518,2118163678]],[[744545519,794127599],[2009702878,2108867038],[1279102319,1328684399]]]]

private theorem identity_0906 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(149930129 / 347074560 : ℝ)) =
      tensor4 coefficients_0906 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0906, p_variance] <;> ring

private theorem negative_0906 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0906 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0906] at hp
  linarith only [hp]

private theorem node_0909 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.qbox) (negative_0905 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0906 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0901 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0902 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0909 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

theorem exclude (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 16 : ℝ)
  · exact node_0890 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0901 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Subtrees.Part20Node0889
