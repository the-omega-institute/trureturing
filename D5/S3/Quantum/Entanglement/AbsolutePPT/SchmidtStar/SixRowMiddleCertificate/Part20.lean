/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part20
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part20
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part20.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part20
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0851 : List (List (List (List ℕ))) :=
  [[[[329796673,267819073],[303068833,241091233]],[[493415906,369460706],[439960226,316005026]],[[128756833,66779233],[102028993,40051393]]],[[[634487210,510532010],[580450490,456495290]],[[936038500,688128100],[827965060,580054660]],[[231826490,107871290],[177789770,53834570]]],[[[304365719,242388119],[277056839,215079239]],[[441972958,318017758],[387355198,263399998]],[[102744839,40767239],[75435959,13458359]]]]

private theorem identity_0851 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(13458359 / 247910400 : ℝ)) =
      tensor4 coefficients_0851 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0851, p_headsq] <;> ring

private theorem negative_0851 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0851 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0851] at hp
  linarith only [hp]

private def coefficients_0852 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0852 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0852 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0852, p_qmass] <;> ring

private theorem negative_0852 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0852 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0852] at hp
  linarith only [hp]

private theorem node_0859 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0851 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0852 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0853 : List (List (List (List ℕ))) :=
  [[[[43850610443,32570687243],[38986143563,27706220363]],[[19846685963,8566762763],[14982219083,3702295883]]],[[[127530854121,93877017321],[112911887721,79258050921]],[[56504524521,22850687721],[41885558121,8231721321]]],[[[123533631965,90065727965],[108890842925,75422938925]],[[53497394525,20029490525],[38854605485,5386701485]]],[[[39854362741,28760372341],[34966073221,23872082821]],[[16840530421,5746540021],[11952240901,858250501]]]]

private theorem identity_0853 (x0 x1 x2 x3 : ℝ) :
    (39665664000 : ℝ)*(-p_headcap x0 x1 x2 x3-(858250501 / 39665664000 : ℝ)) =
      tensor4 coefficients_0853 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0853, p_headcap] <;> ring

private theorem negative_0853 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headcap x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0853 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0853] at hp
  linarith only [hp]

private def coefficients_0854 : List (List (List (List ℕ))) :=
  [[[[896839849,648929449],[789928489,542018089]],[[1461324818,965504018],[1247502098,751681298]],[[529622569,281712169],[422711209,174800809]]],[[[1742305346,1246484546],[1527320546,1031499746]],[[2819319892,1827678292],[2389350292,1397708692]],[[1007289746,511468946],[792304946,296484146]]],[[[845140679,597230279],[737067239,489156839]],[[1357345438,861524638],[1141198558,645377758]],[[477342359,229431959],[369268919,121358519]]]]

private theorem identity_0854 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(121358519 / 991641600 : ℝ)) =
      tensor4 coefficients_0854 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0854, p_headsq] <;> ring

private theorem negative_0854 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0854 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0854] at hp
  linarith only [hp]

private def coefficients_0855 : List (List (List (List ℕ))) :=
  [[[[27683388534349,11259820355149],[20600724757069,4177156577869]],[[57826928318618,24979791960218],[43661600764058,10814464405658]],[[25524411233869,9100843054669],[18441747456589,2018179277389]]],[[[110532461675572,45108907115572],[82241568295732,16818013735732]],[[229775307936104,98928198816104],[173193521176424,42346412056424]],[[100842471540532,35418916980532],[72551578160692,7128023600692]]],[[[165414396838414,67684026636814],[123038487252814,25308117051214]],[[342206707336028,146745966932828],[257454888164828,61994147761628]],[[149305643878414,51575273676814],[106929734292814,9199364091214]]],[[[109964617741092,45080268301092],[81754818370932,16870468930932]],[[226394526247224,96625827367224],[169974927506904,40206228626904]],[[98181185226132,33296835786132],[69971385855972,5087036415972]]],[[[27399290636339,11245325017139],[20357171249219,4203205630019]],[[56136191713558,23828260475158],[42051952939318,9744021700918]],[[24193598246819,8039632627619],[17151478859699,997513240499]]]]

private theorem identity_0855 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(997513240499 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0855 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0855, p_headbox] <;> ring

private theorem negative_0855 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0855 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0855] at hp
  linarith only [hp]

private def coefficients_0856 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0856 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0856 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0856, p_qmass] <;> ring

private theorem negative_0856 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0856 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0856] at hp
  linarith only [hp]

private theorem node_0864 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0855 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0856 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0857 : List (List (List (List ℕ))) :=
  [[[[178045992,227628072],[826734384,925898544],[655660872,705242952]],[[822086064,921250224],[2601726048,2800054368],[1793584944,1892749104]],[[651012552,700594632],[1788936624,1888100784],[1144896552,1194478632]]],[[[455909448,555073608],[1856880456,2055208776],[1414915968,1514080128]],[[1847583816,2045912136],[5617828992,6014485632],[3798135096,3996463416]],[[1405619328,1504783488],[3788838456,3987166776],[2397164088,2496328248]]],[[[278209457,327791537],[1030838074,1130002234],[759601097,809183177]],[[1026189754,1125353914],[3017486948,3215815268],[2005242154,2104406314]],[[754952777,804534857],[2000593834,2099757994],[1252613537,1302195617]]]]

private theorem identity_0857 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(2472861 / 9640960 : ℝ)) =
      tensor4 coefficients_0857 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0857, p_variance] <;> ring

private theorem negative_0857 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0857 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0857] at hp
  linarith only [hp]

private theorem node_0863 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0864 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0857 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0862 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0854 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0863 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0858 : List (List (List (List ℕ))) :=
  [[[[436093321,312138121],[382056601,258101401]],[[705718682,457808282],[597645242,349734842]],[[252194161,128238961],[198157441,74202241]]],[[[846174648,598264248],[737520168,489609768]],[[1359122856,863302056],[1141813896,645993096]],[[478085808,230175408],[369431328,121520928]]],[[[409918918,285963718],[355301158,231345958]],[[653079356,405168956],[543843836,295933436]],[[225729238,101774038],[171111478,47156278]]]]

private theorem identity_0858 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(23578139 / 247910400 : ℝ)) =
      tensor4 coefficients_0858 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0858, p_headsq] <;> ring

private theorem negative_0858 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0858 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0858] at hp
  linarith only [hp]

private def coefficients_0859 : List (List (List (List ℕ))) :=
  [[[[13993146388027,5916163578427],[10472086694467,2395103884867]],[[28655097996494,12501132377294],[21612978609374,5459012990174]],[[12390300193267,4313317383667],[8869240499707,792257690107]]],[[[55788857954240,23615170197440],[41725280090840,9551592334040]],[[113695512289480,49348136775880],[85568356562680,21220981049080]],[[48857804653640,16684116896840],[34794226790240,2620539033440]]],[[[83365839251144,35306115039944],[62301849923384,14242125712184]],[[169076088327328,72956639904928],[126948109671808,30828661249408]],[[72193451641784,24133727430584],[51129462314024,3069738102824]]],[[[55337510853344,23431194462944],[41316024399104,9409708008704]],[[111685679196448,47873046415648],[83642706287968,19830073507168]],[[47374516858304,15468200467904],[33353030404064,1446714013664]]],[[[13767381464632,5824084338232],[10267366168312,2324069041912]],[[27650001754544,11763407501744],[20649971161904,4763376909104]],[[11648567973112,3705270846712],[8148552676792,205255550392]]]]

private theorem identity_0859 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(25656943799 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0859 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0859, p_headbox] <;> ring

private theorem negative_0859 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0859 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0859] at hp
  linarith only [hp]

private def coefficients_0860 : List (List (List (List ℕ))) :=
  [[[[105,169],[138,266],[15,79]]]]

private theorem identity_0860 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(15 / 512 : ℝ)) =
      tensor4 coefficients_0860 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0860, p_qmass] <;> ring

private theorem negative_0860 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (3 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0860 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 16 : ℝ))) ((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(3 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0860] at hp
  linarith only [hp]

private theorem node_0867 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 16 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0859 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0860 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0861 : List (List (List (List ℕ))) :=
  [[[[456255449,555419609],[1861349218,2059677538],[1419038729,1518202889]],[[1852052578,2050380898],[5634320036,6030976676],[3810157378,4008485698]],[[1409742089,1508906249],[3800860738,3999189058],[2405063609,2504227769]]],[[[1113529830,1311858150],[4132289820,4528946460],[3046649910,3244978230]],[[4113696540,4510353180],[12102929880,12896243160],[8045013180,8441669820]],[[3028056630,3226384950],[8026419900,8423076540],[5026253190,5224581510]]],[[[657966383,757130543],[2272324606,2470652926],[1628303183,1727467343]],[[2263027966,2461356286],[6471377852,6868034492],[4236239806,4434568126]],[[1619006543,1718170703],[4226943166,4425271486],[2621881583,2721045743]]]]

private theorem identity_0861 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(456255449 / 1388298240 : ℝ)) =
      tensor4 coefficients_0861 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0861, p_variance] <;> ring

private theorem negative_0861 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (3 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0861 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(3 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0861] at hp
  linarith only [hp]

private theorem node_0866 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 16 : ℝ)
  · exact node_0867 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0861 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0865 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0858 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0866 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0861 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 32 : ℝ)
  · exact node_0862 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0865 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0860 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headcap) (negative_0853 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0861 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0858 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0859 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0860 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0862 : List (List (List (List ℕ))) :=
  [[[[67084981668829,34237845310429],[52919654114269,20072517755869]],[[127391857486778,61697584769978],[99061202377658,33366929660858]],[[55687747267549,22840610909149],[41522419712989,8675283354589]]],[[[266463793508212,135616684388212],[209882006748532,79034897628532]],[[504837222161384,243143003921384],[391673648642024,129979430402024]],[[219973053933172,89125944813172],[163391267173492,32544158053492]]],[[[396806842584814,201346102181614],[312055023413614,116594283010414]],[[750018265590428,359096784784028],[580514627248028,189593146441628]],[[325724756386414,130264015983214],[240972937215214,45512196812014]]],[[[262561908934452,132793210054452],[206142310194132,76373611314132]],[[495091662073944,235554264313944],[382252464593304,122715066833304]],[[214281029859492,84512330979492],[157861431119172,28092732239172]]],[[[65133874781459,32825943543059],[51049636007219,18741704768819]],[[122518754342998,57902891866198],[94350276794518,29734414317718]],[[52841576731139,20533645492739],[38757337956899,6449406718499]]]]

private theorem identity_0862 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(6449406718499 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0862 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0862, p_headbox] <;> ring

private theorem negative_0862 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0862 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0862] at hp
  linarith only [hp]

private def coefficients_0863 : List (List (List (List ℕ))) :=
  [[[[54779156619949,38355588440749],[47696492842669,31272924663469]],[[93541950288218,60694813929818],[79376622733658,46529486375258]],[[34143665117869,17720096938669],[27061001340589,10637433161389]]],[[[216338691342772,150915136782772],[188047797962932,122624243402932]],[[367786268390504,236939159270504],[311204481630824,180357372510824]],[[133047202327732,67623647767732],[104756308947892,39332754387892]]],[[[320273212500814,222542842299214],[277897302915214,180166932713614]],[[541977672184028,346516931780828],[457225853012828,261765112609628]],[[194217793064014,96487422862414],[151841883478414,54111513276814]]],[[[210646667269092,145762317829092],[182436867898932,117552518458932]],[[354763732183224,224995033303224],[298344133442904,168575434562904]],[[125868341634132,60983992194132],[97658542263972,32774192823972]]],[[[51932986083539,35779020464339],[44890866696419,28736901077219]],[[87030371286358,54722440047958],[72946132512118,40638201273718]],[[30554082372419,14400116753219],[23511962985299,7357997366099]]]]

private theorem identity_0863 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(7357997366099 / 101544099840000 : ℝ)) =
      tensor4 coefficients_0863 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0863, p_headbox] <;> ring

private theorem negative_0863 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0863 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0863] at hp
  linarith only [hp]

private def coefficients_0864 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_0864 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_0864 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0864, p_qmass] <;> ring

private theorem negative_0864 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0864 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0864] at hp
  linarith only [hp]

private theorem node_0873 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0863 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0864 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0865 : List (List (List (List ℕ))) :=
  [[[[143958312,193540392],[763207344,862371504],[626221512,675803592]],[[749262384,848426544],[2465375328,2663703648],[1730057904,1829222064]],[[612276552,661858632],[1716112944,1815277104],[1110808872,1160390952]]],[[[387734088,486898248],[1729826376,1928154696],[1356037248,1455201408]],[[1701936456,1900264776],[5345127552,5741784192],[3671081016,3869409336]],[[1328147328,1427311488],[3643191096,3841519416],[2328988728,2428152888]]],[[[244121777,293703857],[967311034,1066475194],[730161737,779743817]],[[953366074,1052530234],[2881136228,3079464548],[1941715114,2040879274]],[[716216777,765798857],[1927770154,2026934314],[1218525857,1268107937]]]]

private theorem identity_0865 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(1999421 / 9640960 : ℝ)) =
      tensor4 coefficients_0865 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0865, p_variance] <;> ring

private theorem negative_0865 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0865 ((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0865] at hp
  linarith only [hp]

private theorem node_0872 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_0873 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0865 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0871 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (29 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0862 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0872 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0866 : List (List (List (List ℕ))) :=
  [[[[33158188050787,17004222431587],[26116068663667,9962103044467]],[[62441878491614,30133947253214],[48357639717374,16049708478974]],[[27012039025627,10858073406427],[19969919638507,3815954019307]]],[[[131619547298840,67272171785240],[103492391572040,39145016058440]],[[247259191615480,118564440588280],[191004880161880,62310129134680]],[[106590794635040,42243419121440],[78463638908240,14116263394640]]],[[[195871695826904,99752247404504],[153743717171384,57624268748984]],[[367054206610048,174815309765248],[282798249299008,90559352454208]],[[157665713348744,61546264926344],[115537734693224,19418286270824]]],[[[129517333952384,65704701171584],[101474361043904,37661728263104]],[[242098022424928,114472756863328],[186012076607968,58386811046368]],[[103607036987744,39794404206944],[75564064079264,11751431298464]]],[[[32106995669752,16220401416952],[25106965077112,9220370824312]],[[59861125531184,28087937025584],[45861064345904,14087875840304]],[[25520077544632,9633483291832],[18520046951992,2633452699192]]]]

private theorem identity_0866 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(329181587399 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0866 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0866, p_headbox] <;> ring

private theorem negative_0866 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0866 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0866] at hp
  linarith only [hp]

private def coefficients_0867 : List (List (List (List ℕ))) :=
  [[[[26817894193627,18740911384027],[23296834500067,15219851690467]],[[45217987946894,29064022327694],[38175868559774,22021902940574]],[[16128442338067,8051459528467],[12607382644507,4530399834907]]],[[[105814215307040,73640527550240],[91750637443640,59576949686840]],[[177550828268680,113203452755080],[149423672541880,85076297028280]],[[62687763280040,30514075523240],[48624185416640,16450497659840]]],[[[156500844356744,108441120145544],[135436855028984,87377130817784]],[[261278908800928,165159460378528],[219150930145408,123031481723008]],[[91261267009784,43201542798584],[70197277682024,22137553470824]]],[[[102830457659744,70924141269344],[88808971205504,56902654815104]],[[170776966870048,106964334089248],[142733993961568,78921361180768]],[[58972857725504,27066541335104],[44951371271264,13045054880864]]],[[[25325932712632,17382635586232],[21825917416312,13882620289912]],[[41830894983344,25944300730544],[34830864390704,18944270137904]],[[14270909953912,6327612827512],[10770894657592,2827597531192]]]]

private theorem identity_0867 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(353449691399 / 6346506240000 : ℝ)) =
      tensor4 coefficients_0867 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0867, p_headbox] <;> ring

private theorem negative_0867 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 16 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0867 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-0)/(1 / 16 : ℝ)) (1-((x3-0)/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0867] at hp
  linarith only [hp]

private def coefficients_0868 : List (List (List (List ℕ))) :=
  [[[[41,105],[82,210],[23,87]]]]

private theorem identity_0868 (x0 x1 x2 x3 : ℝ) :
    (512 : ℝ)*(-p_qmass x0 x1 x2 x3-(23 / 512 : ℝ)) =
      tensor4 coefficients_0868 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0868, p_qmass] <;> ring

private theorem negative_0868 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : (1 / 16 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0868 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 16 : ℝ)) (1-((x2-0)/(1 / 16 : ℝ))) ((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x3-(1 / 16 : ℝ))/(1 / 16 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0868] at hp
  linarith only [hp]

private theorem node_0876 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 16 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0867 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0868 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0869 : List (List (List (List ℕ))) :=
  [[[[388080089,487244249],[1734295138,1932623458],[1360160009,1459324169]],[[1706405218,1904733538],[5361618596,5758275236],[3683103298,3881431618]],[[1332270089,1431434249],[3655213378,3853541698],[2336888249,2436052409]]],[[[977179110,1175507430],[3878181660,4274838300],[2928892470,3127220790]],[[3822401820,4219058460],[11557527000,12350840280],[7790905020,8187561660]],[[2873112630,3071440950],[7735125180,8131781820],[4889902470,5088230790]]],[[[589791023,688955183],[2145270526,2343598846],[1569424463,1668588623]],[[2117380606,2315708926],[6198676412,6595333052],[4109185726,4307514046]],[[1541534543,1640698703],[4081295806,4279624126],[2553706223,2652870383]]]]

private theorem identity_0869 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(388080089 / 1388298240 : ℝ)) =
      tensor4 coefficients_0869 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0869, p_variance] <;> ring

private theorem negative_0869 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 16 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0869 ((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(29 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x2-(1 / 16 : ℝ))/(1 / 16 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0869] at hp
  linarith only [hp]

private theorem node_0875 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 16 : ℝ)
  · exact node_0876 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0869 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0874 (x0 x1 x2 x3 : ℝ)
    (h0l : (29 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0866 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0875 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0870 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (29 / 32 : ℝ)
  · exact node_0871 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0874 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0870 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0870 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0870 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0870, p_qmass] <;> ring

private theorem negative_0870 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0870 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0870] at hp
  linarith only [hp]

private theorem node_0869 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0870 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0870 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0871 : List (List (List (List ℕ))) :=
  [[[[37442178,62233218],[311367636,360949716],[280897938,305688978]],[[306719316,356301396],[1102674312,1201838472],[809899956,859482036]],[[276249618,301040658],[805251636,854833716],[535974498,560765538]]],[[[124793088,174375168],[726329496,825493656],[615481368,665063448]],[[717032856,816197016],[2420090592,2618418912],[1730947656,1830111816]],[[606184728,655766808],[1721651016,1820815176],[1129411248,1178993328]]],[[[87696911,112487951],[415653862,465235942],[334929431,359720471]],[[411005542,460587622],[1318800284,1417964444],[921739702,971321782]],[[330281111,355072151],[917091382,966673462],[593782751,618573791]]]]

private theorem identity_0871 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(2080121 / 9640960 : ℝ)) =
      tensor4 coefficients_0871 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0871, p_variance] <;> ring

private theorem negative_0871 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0871 ((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0871] at hp
  linarith only [hp]

private theorem node_0868 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0869 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0871 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0857 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (15 / 16 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0858 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0868 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0872 : List (List (List (List ℕ))) :=
  [[[[21838646069,16291650869],[19394501309,13847506109]],[[10331729909,4784734709],[7887585149,2340589949]]],[[[63541706096,46993686896],[56198232056,39650212856]],[[29518327856,12970308656],[22174853816,5626834616]]],[[[61579941632,45124888832],[54226299392,37771246592]],[[28056257792,11601204992],[20702615552,4247562752]]],[[[19877368832,14423340032],[17423055872,11969027072]],[[8870147072,3416118272],[6415834112,961805312]]]]

private theorem identity_0872 (x0 x1 x2 x3 : ℝ) :
    (19832832000 : ℝ)*(-p_headcap x0 x1 x2 x3-(939263 / 19368000 : ℝ)) =
      tensor4 coefficients_0872 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0872, p_headcap] <;> ring

private theorem negative_0872 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headcap x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0872 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0872] at hp
  linarith only [hp]

private def coefficients_0873 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0873 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0873 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0873, p_qmass] <;> ring

private theorem negative_0873 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0873 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0873] at hp
  linarith only [hp]

private theorem node_0879 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headcap) (negative_0872 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.qmass) (negative_0873 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0874 : List (List (List (List ℕ))) :=
  [[[[1618566375427,625654234627],[1181064463387,188152322587]],[[3810050683214,1824226401614],[2935046859134,949222577534]],[[1632971228587,640059087787],[1195469316547,202557175747]]],[[[6480878456936,2542511864936],[4736227126016,797860534016]],[[15097281987352,7220548803352],[11607979325512,3731246141512]],[[6401072322416,2462705730416],[4656420991496,718054399496]]],[[[9719908090112,3862002259712],[7111154698112,1253248867712]],[[22410975841024,10695164180224],[17193469057024,5477657396224]],[[9395995721312,3538089890912],[6787242329312,929336498912]]],[[[6471350183936,2598989735936],[4737787129856,865426681856]],[[14770122299392,7025401403392],[11302996191232,3558275295232]],[[6120569363456,2248208915456],[4387006309376,514645861376]]],[[[1613752471552,653843402752],[1181793390592,221884321792]],[[3646374354944,1726556217344],[2782456193024,862638055424]],[[1492673032192,532763963392],[1060713951232,100804882432]]]]

private theorem identity_0874 (x0 x1 x2 x3 : ℝ) :
    (3173253120000 : ℝ)*(-p_headbox x0 x1 x2 x3-(24610567 / 774720000 : ℝ)) =
      tensor4 coefficients_0874 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0874, p_headbox] <;> ring

private theorem negative_0874 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0874 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0874] at hp
  linarith only [hp]

private def coefficients_0875 : List (List (List (List ℕ))) :=
  [[[[847208617,599298217],[737973097,490062697]],[[1360900274,865079474],[1142429234,646608434]],[[478829257,230918857],[369593737,121683337]]],[[[1641743610,1145922810],[1422110490,926289690]],[[2615872260,1624230660],[2176606020,1184964420]],[[904403850,408583050],[684770730,188949930]]],[[[794210175,546299775],[683812575,435902175]],[[1254322350,758501550],[1033527150,537706350]],[[425249775,177339375],[314852175,66941775]]]]

private theorem identity_0875 (x0 x1 x2 x3 : ℝ) :
    (991641600 : ℝ)*(-p_headsq x0 x1 x2 x3-(297519 / 4407296 : ℝ)) =
      tensor4 coefficients_0875 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0875, p_headsq] <;> ring

private theorem negative_0875 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0875 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0875] at hp
  linarith only [hp]

private def coefficients_0876 : List (List (List (List ℕ))) :=
  [[[[42943738,92525818],[1014389396,1113553556],[999335578,1048917658]],[[543165956,642330116],[2975873992,3174202312],[2488487876,2587652036]],[[507194698,556776778],[1975429556,2074593716],[1496124778,1545706858]]],[[[183312184,282476344],[2231181728,2429510048],[2103649384,2202813544]],[[1284958088,1483286408],[6364107376,6760764016],[5190708968,5389037288]],[[1115590864,1214755024],[4160815568,4359143888],[3101004544,3200168704]]],[[[140714447,190296527],[1217484334,1316648494],[1104659807,1154241887]],[[742484134,841648294],[3389617388,3587945708],[2702913094,2802077254]],[[608742167,658324247],[2186078014,2285242174],[1605225767,1654807847]]]]

private theorem identity_0876 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(21471869 / 347074560 : ℝ)) =
      tensor4 coefficients_0876 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0876, p_variance] <;> ring

private theorem negative_0876 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0876 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0876] at hp
  linarith only [hp]

private theorem node_0882 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0875 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0876 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0877 : List (List (List (List ℕ))) :=
  [[[[410952887,286997687],[355754087,231798887]],[[654856774,406946374],[544459174,296548774]],[[226472687,102517487],[171273887,47318687]]],[[[795244144,547333744],[684265504,436355104]],[[1256099768,760278968],[1034142488,538321688]],[[425993224,178082824],[315014584,67104184]]],[[[384128848,260173648],[328349008,204393808]],[[600918176,353007776],[489358496,241448096]],[[199358128,75402928],[143578288,19623088]]]]

private theorem identity_0877 (x0 x1 x2 x3 : ℝ) :
    (495820800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1226443 / 30988800 : ℝ)) =
      tensor4 coefficients_0877 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0877, p_headsq] <;> ring

private theorem negative_0877 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (5 / 16 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0877 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0877] at hp
  linarith only [hp]

private def coefficients_0878 : List (List (List (List ℕ))) :=
  [[[[183658185,282822345],[2239427250,2437755570],[2111548905,2210713065]],[[1289426850,1487755170],[6388151940,6784808580],[5210284770,5408613090]],[[1119713625,1218877785],[4176614610,4374942930],[3112680825,3211844985]]],[[[563549790,761878110],[4886428380,5283085020],[4434438270,4632766590]],[[2978874060,3375530700],[13606558680,14399871960],[10850803980,11247460620]],[[2443214190,2641542510],[8775910140,9172566780],[6444255630,6642583950]]],[[[380583607,479747767],[2648385134,2846713454],[2323581367,2422745527]],[[1690831214,1889159534],[7221174748,7617831388],[5641903214,5840231534]],[[1324192567,1423356727],[4600679534,4799007854],[3332266807,3431430967]]]]

private theorem identity_0878 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(4081293 / 30851072 : ℝ)) =
      tensor4 coefficients_0878 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0878, p_variance] <;> ring

private theorem negative_0878 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (5 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0878 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(5 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0878] at hp
  linarith only [hp]

private theorem node_0883 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (5 / 16 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0877 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0878 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0881 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 32 : ℝ)
  · exact node_0882 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0883 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0880 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0874 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact node_0881 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private theorem node_0878 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (3 / 8 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0879 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact node_0880 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u h

private def coefficients_0879 : List (List (List (List ℕ))) :=
  [[[[65467078926013,33693890420413],[51467017740733,19693829235133]],[[122228426235386,58682049224186],[94228303864826,30681926853626]],[[52293242675773,20520054170173],[38293181490493,6519992984893]]],[[[259689613157300,133129370674100],[203775069492020,77214827008820]],[[483606664341160,230486179374760],[371777577010600,118657092044200]],[[206119517084660,79559274601460],[150204973419380,23644730936180]]],[[[386189701892350,197145874282750],[302447951036350,113404123426750]],[[717303220655900,339215565436700],[549819718943900,171732063724700]],[[304529230505950,115485402896350],[220787479649950,31743652040350]]],[[[255178530370500,129678848578500],[199438404454500,73938722662500]],[[472699466139000,221700102555000],[361219214307000,110219850723000]],[[199872543016500,74372861224500],[144132417100500,18632735308500]]],[[[63211359301875,31968451141875],[49298501761875,18055593601875]],[[116774476773750,54288660453750],[88948761693750,26462945373750]],[[49169583511875,17926675351875],[35256725971875,4013817811875]]]]

private theorem identity_0879 (x0 x1 x2 x3 : ℝ) :
    (101544099840000 : ℝ)*(-p_headbox x0 x1 x2 x3-(713567611 / 18052284416 : ℝ)) =
      tensor4 coefficients_0879 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0879, p_headbox] <;> ring

private theorem negative_0879 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0879 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0879] at hp
  linarith only [hp]

private def coefficients_0880 : List (List (List (List ℕ))) :=
  [[[[6531898,56113978],[950862356,1050026516],[972220378,1021802458]],[[465693956,564858116],[2839523272,3037851592],[2429609156,2528773316]],[[466134538,515716618],[1902605876,2001770036],[1464361258,1513943338]]],[[[110488504,209652664],[2104127648,2302455968],[2049418984,2148583144]],[[1130014088,1328342408],[6091405936,6488062576],[5072951528,5271279848]],[[1033470544,1132634704],[4015168208,4213496528],[3037477504,3136641664]]],[[[104302607,153884687],[1153957294,1253121454],[1077544607,1127126687]],[[665012134,764176294],[3253266668,3451594988],[2644034374,2743198534]],[[567682007,617264087],[2113254334,2212418494],[1573462247,1623044327]]]]

private theorem identity_0880 (x0 x1 x2 x3 : ℝ) :
    (694149120 : ℝ)*(-p_variance x0 x1 x2 x3-(3265949 / 347074560 : ℝ)) =
      tensor4 coefficients_0880 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0880, p_variance] <;> ring

private theorem negative_0880 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0880 ((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0880] at hp
  linarith only [hp]

private theorem node_0887 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (31 / 32 : ℝ))
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0879 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0880 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0881 : List (List (List (List ℕ))) :=
  [[[[32268048654923,16646594574923],[25311619884923,9690165804923]],[[59711976394846,28469068234846],[45799118854846,14556210694846]],[[25247160759923,9625706679923],[18290731989923,2669277909923]]],[[[127905648038192,65683856294192],[100124280836192,37902489092192]],[[236047126057384,111603542569384],[180484391653384,56040808165384]],[[99391538555192,37169746811192],[71610171353192,9388379609192]]],[[[190069785481088,97132019132288],[148464997321088,55527230972288]],[[349795361243776,163919828546176],[266585784923776,80710252226176]],[[146656202369888,53718436021088],[105051414209888,12113647861088]]],[[[125494639828992,63798666043392],[97803444805632,36107471020032]],[[230296892719104,106904945147904],[174914502672384,51522555101184]],[[96126256576512,34430282790912],[68435061553152,6739087767552]]],[[[31062452027392,15703906926592],[24151106732032,8792561631232]],[[56836677730304,26119587528704],[43013987139584,12296896937984]],[[23614430298112,8255885197312],[16703085002752,1344539901952]]]]

private theorem identity_0881 (x0 x1 x2 x3 : ℝ) :
    (50772049920000 : ℝ)*(-p_headbox x0 x1 x2 x3-(82064203 / 3098880000 : ℝ)) =
      tensor4 coefficients_0881 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0881, p_headbox] <;> ring

private theorem negative_0881 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (7 / 16 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_headbox x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0881 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0881] at hp
  linarith only [hp]

private def coefficients_0882 : List (List (List (List ℕ))) :=
  [[[[110834505,209998665],[2112373170,2310701490],[2057318505,2156482665]],[[1134482850,1332811170],[6115450500,6512107140],[5092527330,5290855650]],[[1037593305,1136757465],[4030967250,4229295570],[3049153785,3148317945]]],[[[417902430,616230750],[4632320220,5028976860],[4325977470,4524305790]],[[2668986060,3065642700],[13061155800,13854469080],[10615289100,11011945740]],[[2278973550,2477301870],[8484615420,8881272060],[6317201550,6515529870]]],[[[307759927,406924087],[2521331054,2719659374],[2269350967,2368515127]],[[1535887214,1734215534],[6948473308,7345129948],[5524145774,5722474094]],[[1242072247,1341236407],[4455032174,4653360494],[3268739767,3367903927]]]]

private theorem identity_0882 (x0 x1 x2 x3 : ℝ) :
    (1388298240 : ℝ)*(-p_variance x0 x1 x2 x3-(2462989 / 30851072 : ℝ)) =
      tensor4 coefficients_0882 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0882, p_variance] <;> ring

private theorem negative_0882 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (7 / 16 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0882 ((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ)) (1-((x0-(31 / 32 : ℝ))/(1 / 32 : ℝ))) ((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x1-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-0)/(1 / 8 : ℝ)) (1-((x3-0)/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0882] at hp
  linarith only [hp]

private theorem node_0888 (x0 x1 x2 x3 : ℝ)
    (h0l : (31 / 32 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (7 / 16 : ℝ)
  · exact (not_lt_of_ge h.headbox) (negative_0881 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0882 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0886 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 8 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (31 / 32 : ℝ)
  · exact node_0887 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0888 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0883 : List (List (List (List ℕ))) :=
  [[[[25,57],[50,114],[7,39]]]]

private theorem identity_0883 (x0 x1 x2 x3 : ℝ) :
    (128 : ℝ)*(-p_qmass x0 x1 x2 x3-(7 / 128 : ℝ)) =
      tensor4 coefficients_0883 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0883, p_qmass] <;> ring

private theorem negative_0883 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : (1 / 8 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_qmass x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0883 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-0)/(1 / 8 : ℝ)) (1-((x2-0)/(1 / 8 : ℝ))) ((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x3-(1 / 8 : ℝ))/(1 / 8 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0883] at hp
  linarith only [hp]

private theorem node_0885 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 8 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 8 : ℝ)
  · exact node_0886 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.qmass) (negative_0883 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0884 : List (List (List (List ℕ))) :=
  [[[[125139089,174721169],[730798258,829962418],[619604129,669186209]],[[721501618,820665778],[2436581636,2634909956],[1742969938,1842134098]],[[610307489,659889569],[1733673298,1832837458],[1137310769,1186892849]]],[[[351479646,450643806],[1671552972,1869881292],[1347963246,1447127406]],[[1652959692,1851288012],[5308183224,5704839864],[3711003372,3909331692]],[[1329369966,1428534126],[3692410092,3890738412],[2390930046,2490094206]]],[[[227032559,276614639],[942138718,1041302878],[729051119,778633199]],[[932842078,1032006238],[2874369596,3072697916],[1969417438,2068581598]],[[719754479,769336559],[1960120798,2059284958],[1254311279,1303893359]]]]

private theorem identity_0884 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(125139089 / 347074560 : ℝ)) =
      tensor4 coefficients_0884 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0884, p_variance] <;> ring

private theorem negative_0884 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0884 ((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(15 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-0)/(1 / 4 : ℝ)) (1-((x3-0)/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0884] at hp
  linarith only [hp]

private theorem node_0884 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (3 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 8 : ℝ)
  · exact node_0885 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0884 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0877 (x0 x1 x2 x3 : ℝ)
    (h0l : (15 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (3 / 8 : ℝ)
  · exact node_0878 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact node_0884 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private theorem node_0856 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 16 : ℝ)
  · exact node_0857 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0877 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

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

private theorem node_0889 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : (1 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (15 / 16 : ℝ)
  · exact node_0890 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0901 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private theorem node_0855 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 4 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 4 : ℝ)
  · exact node_0856 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0889 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h

private def coefficients_0907 : List (List (List (List ℕ))) :=
  [[[[19302129,44093169],[272763378,322345458],[267406209,292197249]],[[272763378,322345458],[1046383236,1145547396],[801509778,851091858]],[[267406209,292197249],[801509778,851091858],[548048529,572839569]]],[[[88512990,138095070],[652897740,752061900],[592274670,641856750]],[[652897740,752061900],[2322615480,2520943800],[1725497580,1824661740]],[[592274670,641856750],[1725497580,1824661740],[1161112830,1210694910]]],[[[69902863,94693903],[381518366,431100446],[325560463,350351503]],[[381518366,431100446],[1279000252,1378164412],[925371806,974953886]],[[325560463,350351503],[925371806,974953886],[613756303,638547343]]]]

private theorem identity_0907 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(306383 / 1377280 : ℝ)) =
      tensor4 coefficients_0907 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0907, p_variance] <;> ring

private theorem negative_0907 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0907 ((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(7 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0907] at hp
  linarith only [hp]

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ 1)
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : 0 ≤ x2) (h2u : x2 ≤ (1 / 2 : ℝ))
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (1 / 4 : ℝ)
  · exact node_0855 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0907 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part20
