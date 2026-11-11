/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part08
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part08
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate/Part08.exclude_00
   digest: Exact strict negative identities on closed middle-interval subtrees. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part08
noncomputable section

open SixRowMiddlePolynomial

private def coefficients_0308 : List (List (List (List ℕ))) :=
  [[[[152516177,90538577],[131598737,69621137]],[[294573634,170618434],[252738754,128783554]],[[107195057,45217457],[86277617,24300017]]],[[[295146426,171191226],[252149466,128194266]],[[568794372,320883972],[482800452,234890052]],[[203923146,79967946],[160926186,36970986]]],[[[142305431,80327831],[120225911,58248311]],[[273571102,149615902],[229412062,105456862]],[[96403271,34425671],[74323751,12346151]]]]

private theorem identity_0308 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(12346151 / 61977600 : ℝ)) =
      tensor4 coefficients_0308 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0308, p_headsq] <;> ring

private theorem negative_0308 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0308 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0308] at hp
  linarith only [hp]

private def coefficients_0309 : List (List (List (List ℕ))) :=
  [[[[4174282,16569802],[232630004,257421044],[256345642,268741162]],[[122813444,147604484],[726728008,776310088],[659694404,684485444]],[[125611642,138007162],[508042964,532834004],[410321242,422716762]]],[[[33619680,58410720],[523355760,572937840],[545515920,570306960]],[[299945880,349527960],[1577201040,1676365200],[1388814840,1438396920]],[[280271160,305062200],[1081735200,1131317280],[857243880,882034920]]],[[[29791399,42186919],[291417758,316208798],[289516279,301911799]],[[177824438,202615478],[851857036,901439116],[729812438,754603478]],[[155005519,167401039],[574384238,599175278],[447268639,459664159]]]]

private theorem identity_0309 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(298163 / 3098880 : ℝ)) =
      tensor4 coefficients_0309 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0309, p_variance] <;> ring

private theorem negative_0309 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0309 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0309] at hp
  linarith only [hp]

private theorem node_0312 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0308 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0309 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0310 : List (List (List (List ℕ))) :=
  [[[[74303591,43314791],[63263831,32275031]],[[143087302,81109702],[121007782,59030182]],[[51352511,20363711],[40312751,9323951]]],[[[143339400,81361800],[120678840,58701240]],[[275348520,151393320],[230027400,106072200]],[[97146720,35169120],[74486160,12508560]]],[[[68873400,37884600],[57252600,26263800]],[[131936400,69958800],[108694800,46717200]],[[45631800,14643000],[34011000,3022200]]]]

private theorem identity_0310 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_headsq x0 x1 x2 x3-(1679 / 17216 : ℝ)) =
      tensor4 coefficients_0310 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0310, p_headsq] <;> ring

private theorem negative_0310 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0310 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0310] at hp
  linarith only [hp]

private def coefficients_0311 : List (List (List (List ℕ))) :=
  [[[[33965681,58756721],[531601282,581183362],[553415441,578206481]],[[304414642,353996722],[1601245604,1700409764],[1408390642,1457972722]],[[284393921,309184961],[1097534242,1147116322],[868920161,893711201]]],[[[119857598,169439678],[1182162076,1281326236],[1173864158,1223446238]],[[720235276,819399436],[3455517272,3653845592],[2958401356,3057565516]],[[628267598,677849678],[2329135036,2428299196],[1812427118,1862009198]]],[[[86583919,111374959],[651944798,701526878],[621140719,645931759]],[[417204638,466786718],[1857039676,1956203836],[1551394718,1600976798]],[[344565679,369356719],[1232984798,1282566878],[944198959,968989999]]]]

private theorem identity_0311 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(33965681 / 86768640 : ℝ)) =
      tensor4 coefficients_0311 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0311, p_variance] <;> ring

private theorem negative_0311 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0311 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-0)/(1 / 2 : ℝ)) (1-((x3-0)/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0311] at hp
  linarith only [hp]

private theorem node_0313 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0310 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0311 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0311 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ (1 / 2 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 8 : ℝ)
  · exact node_0312 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0313 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0312 : List (List (List (List ℕ))) :=
  [[[[100513097,69524297],[90054377,59065577]],[[190567474,128589874],[169650034,107672434]],[[55191977,24203177],[44733257,13744457]]],[[[191140266,129162666],[169641786,107664186]],[[360782052,236826852],[317785092,193829892]],[[99916986,37939386],[78418506,16440906]]],[[[90302351,59313551],[79262591,48273791]],[[169564942,107587342],[147485422,85507822]],[[44400191,13411391],[33360431,2371631]]]]

private theorem identity_0312 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_headsq x0 x1 x2 x3-(2371631 / 61977600 : ℝ)) =
      tensor4 coefficients_0312 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0312, p_headsq] <;> ring

private theorem negative_0312 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0312 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0312] at hp
  linarith only [hp]

private def coefficients_0313 : List (List (List (List ℕ))) :=
  [[[[18998027,45743254,22871627],[8539307,24825814,12412907]],[[29456747,66660694,33330347],[18998027,45743254,22871627]]],[[[33339486,82173372,41086686],[11841006,39176412,19588206]],[[54837966,125170332,62585166],[33339486,82173372,41086686]]],[[[14161901,36071002,18035501],[3122141,13991482,6995741]],[[25201661,58150522,29075261],[14161901,36071002,18035501]]]]

private theorem identity_0313 (x0 x1 x2 x3 : ℝ) :
    (61977600 : ℝ)*(-p_coupled x0 x1 x2 x3-(3122141 / 61977600 : ℝ)) =
      tensor4 coefficients_0313 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0313, p_coupled] <;> ring

private theorem negative_0313 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0313 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0313] at hp
  linarith only [hp]

private theorem node_0317 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0312 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm)
  · exact (not_lt_of_ge h.coupled) (negative_0313 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0314 : List (List (List (List ℕ))) :=
  [[[[8047882,20443402],[125912324,150703364],[124836922,137232442]],[[132884804,157675844],[501671848,551253928],[382732004,407523044]],[[131809402,144204922],[389704484,414495524],[264867562,277263082]]],[[[41366880,66157920],[306143640,355725720],[278721720,303512760]],[[320088600,369670680],[1119535200,1218699360],[827336520,876918600]],[[292666680,317457720],[841281480,890863560],[562559760,587350800]]],[[[33664999,46060519],[180923318,205714358],[154230799,166626319]],[[187895798,212686838],[619247356,668829436],[445296518,470087558]],[[161203279,173598799],[452268998,477060038],[298038199,310433719]]]]

private theorem identity_0314 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(4023941 / 21692160 : ℝ)) =
      tensor4 coefficients_0314 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0314, p_variance] <;> ring

private theorem negative_0314 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0314 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0314] at hp
  linarith only [hp]

private theorem node_0316 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 4 : ℝ)
  · exact node_0317 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0314 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0315 : List (List (List (List ℕ))) :=
  [[[[10372042,22767562],[245025524,269816564],[262543402,274938922]],[[135208964,160000004],[751519048,801101128],[672089924,696880964]],[[131809402,144204922],[520438484,545229524],[416519002,428914522]]],[[[46015200,70806240],[548146800,597728880],[557911440,582702480]],[[324736920,374319000],[1626783120,1725947280],[1413605880,1463187960]],[[292666680,317457720],[1106526240,1156108320],[869639400,894430440]]],[[[35989159,48384679],[303813278,328604318],[295714039,308109559]],[[190219958,215010998],[876648076,926230156],[742207958,766998998]],[[161203279,173598799],[586779758,611570798],[453466399,465861919]]]]

private theorem identity_0315 (x0 x1 x2 x3 : ℝ) :
    (43384320 : ℝ)*(-p_variance x0 x1 x2 x3-(5186021 / 21692160 : ℝ)) =
      tensor4 coefficients_0315 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0315, p_variance] <;> ring

private theorem negative_0315 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0315 ((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(1 / 4 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0315] at hp
  linarith only [hp]

private theorem node_0315 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (3 / 8 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0316 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0315 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private def coefficients_0316 : List (List (List (List ℕ))) :=
  [[[[309445577,185490377],[265286537,141331337]],[[596811634,348901234],[508493554,260583154]],[[252503657,128548457],[208344617,84389417]]],[[[597820026,349909626],[508339866,260429466]],[[1150899972,655079172],[971939652,476118852]],[[483355146,235444746],[393874986,145964586]]],[[[288049631,164094431],[242728511,118773311]],[[553438702,305528302],[462796462,214886062]],[[230526671,106571471],[185205551,61250351]]]]

private theorem identity_0316 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(61250351 / 247910400 : ℝ)) =
      tensor4 coefficients_0316 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0316, p_headsq] <;> ring

private theorem negative_0316 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0316 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0316] at hp
  linarith only [hp]

private def coefficients_0317 : List (List (List (List ℕ))) :=
  [[[[304797257,180842057],[282717737,158762537]],[[517790194,269879794],[473631154,225720754]],[[178130537,54175337],[156051017,32095817]]],[[[587942346,340031946],[543202266,295291866]],[[991695012,495874212],[902214852,406394052]],[[334027866,86117466],[289287786,41377386]]],[[[282820271,158865071],[260159711,136204511]],[[473255182,225344782],[427934062,180023662]],[[155572511,31617311],[132911951,8956751]]]]

private theorem identity_0317 (x0 x1 x2 x3 : ℝ) :
    (247910400 : ℝ)*(-p_headsq x0 x1 x2 x3-(8956751 / 247910400 : ℝ)) =
      tensor4 coefficients_0317 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0317, p_headsq] <;> ring

private theorem negative_0317 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (5 / 8 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0317 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0317] at hp
  linarith only [hp]

private def coefficients_0318 : List (List (List (List ℕ))) :=
  [[[[89236162,114027202],[407983124,457565204],[325719442,350510482]],[[417279764,466861844],[1309850248,1409014408],[906515444,956097524]],[[335016082,359807122],[915812084,965394164],[587768482,612559522]]],[[[230398560,279980640],[923595480,1022759640],[707141880,756723960]],[[942188760,1041352920],[2842512480,3040840800],[1928213640,2027377800]],[[725735160,775317240],[1946806920,2045971080],[1235016720,1284598800]]],[[[141508399,166299439],[516304358,565886438],[381768439,406559479]],[[525600998,575183078],[1534046236,1633210396],[1022390198,1071972278]],[[391065079,415856119],[1031686838,1081268918],[647594239,672385279]]]]

private theorem identity_0318 (x0 x1 x2 x3 : ℝ) :
    (173537280 : ℝ)*(-p_variance x0 x1 x2 x3-(44618081 / 86768640 : ℝ)) =
      tensor4 coefficients_0318 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0318, p_variance] <;> ring

private theorem negative_0318 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (5 / 8 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0318 ((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x2-(5 / 8 : ℝ))/(1 / 8 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0318] at hp
  linarith only [hp]

private theorem node_0323 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (5 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0317 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0318 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private theorem node_0322 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (7 / 16 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0316 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact node_0323 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u h

private def coefficients_0319 : List (List (List (List ℕ))) :=
  [[[[149971991,87994391],[127311431,65333831]],[[288613702,164658502],[243292582,119337382]],[[121210511,59232911],[98549951,36572351]]],[[[289083600,165128400],[243181440,119226240]],[[555216120,307305720],[463411800,215501400]],[[231270120,107314920],[185367960,61412760]]],[[[138949200,76971600],[115707600,53730000]],[[266277600,142322400],[219794400,95839200]],[[109897200,47919600],[86655600,24678000]]]]

private theorem identity_0319 (x0 x1 x2 x3 : ℝ) :
    (123955200 : ℝ)*(-p_headsq x0 x1 x2 x3-(6855 / 34432 : ℝ)) =
      tensor4 coefficients_0319 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0319, p_headsq] <;> ring

private theorem negative_0319 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 8 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_headsq x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0319 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-0)/(1 / 8 : ℝ)) (1-((x1-0)/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0319] at hp
  linarith only [hp]

private def coefficients_0320 : List (List (List (List ℕ))) :=
  [[[[4429481,54011561],[886229362,985393522],[937579721,987161801]],[[461489122,560653282],[2742795524,2941123844],[2392866082,2492030242]],[[471004601,520586681],[1884456082,1983620242],[1469231321,1518813401]]],[[[106541918,205706078],[1982931676,2181259996],[1987949438,2087113598]],[[1125897676,1324225996],[5921643992,6318300632],[5018865676,5217193996]],[[1047245678,1146409838],[3994492156,4192820476],[3058806158,3157970318]]],[[[102804439,152386519],[1098086318,1197250478],[1051061719,1100643799]],[[665792558,764956718],[3181616476,3379944796],[2627383598,2726547758]],[[576933079,626515159],[2111420078,2210584238],[1590266839,1639848919]]]]

private theorem identity_0320 (x0 x1 x2 x3 : ℝ) :
    (347074560 : ℝ)*(-p_variance x0 x1 x2 x3-(632783 / 49582080 : ℝ)) =
      tensor4 coefficients_0320 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0320, p_variance] <;> ring

private theorem negative_0320 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 8 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ)) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0320 ((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ)) (1-((x0-(7 / 16 : ℝ))/(1 / 16 : ℝ))) ((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x1-(1 / 8 : ℝ))/(1 / 8 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0320] at hp
  linarith only [hp]

private theorem node_0324 (x0 x1 x2 x3 : ℝ)
    (h0l : (7 / 16 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 8 : ℝ)
  · exact (not_lt_of_ge h.headsq) (negative_0319 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u)
  · exact (not_lt_of_ge h.variance) (negative_0320 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0321 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ (3 / 4 : ℝ))
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (7 / 16 : ℝ)
  · exact node_0322 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0324 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

private def coefficients_0321 : List (List (List (List ℕ))) :=
  [[[[8525021,20923642,10461821],[3005141,9883882,4941941]],[[14044901,31963402,15981701],[8525021,20923642,10461821]]],[[[14542200,36831600,18415800],[3211920,14171040,7085520]],[[25872480,59492160,29746080],[14542200,36831600,18415800]]],[[[5927400,15728400,7864200],[117000,4107600,2053800]],[[11737800,27349200,13674600],[5927400,15728400,7864200]]]]

private theorem identity_0321 (x0 x1 x2 x3 : ℝ) :
    (30988800 : ℝ)*(-p_coupled x0 x1 x2 x3-(65 / 17216 : ℝ)) =
      tensor4 coefficients_0321 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0321, p_coupled] <;> ring

private theorem negative_0321 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (3 / 4 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_coupled x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0321 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 4 : ℝ))) ((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x3-(3 / 4 : ℝ))/(1 / 4 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0321] at hp
  linarith only [hp]

private theorem node_0320 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ (3 / 4 : ℝ))
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (3 / 4 : ℝ)
  · exact node_0321 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact (not_lt_of_ge h.coupled) (negative_0321 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u)

private def coefficients_0322 : List (List (List (List ℕ))) :=
  [[[[41712881,66503921],[310612402,360194482],[282844481,307635521]],[[324557362,374139442],[1136026244,1235190404],[839358802,888940882]],[[296789441,321580481],[853303762,902885842],[570459281,595250321]]],[[[135351998,184934078],[732630796,831794956],[625168718,674750798]],[[760520716,859684876],[2509971512,2708299832],[1805230636,1904394796]],[[653058638,702640718],[1833120556,1932284716],[1207951838,1257533918]]],[[[94331119,119122159],[423402398,472984478],[343016239,367807279]],[[437347358,486929438],[1376713276,1475877436],[967255838,1016837918]],[[356961199,381752239],[981200798,1030782878],[638184559,662975599]]]]

private theorem identity_0322 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(5958983 / 12395520 : ℝ)) =
      tensor4 coefficients_0322 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0322, p_variance] <;> ring

private theorem negative_0322 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (3 / 4 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0322 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-0)/(1 / 4 : ℝ)) (1-((x1-0)/(1 / 4 : ℝ))) ((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x2-(3 / 4 : ℝ))/(1 / 4 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0322] at hp
  linarith only [hp]

private theorem node_0319 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 4 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x2 ≤ (3 / 4 : ℝ)
  · exact node_0320 x0 x1 x2 x3 h0l h0u h1l h1u h2l hm h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0322 x0 x1 x2 x3 h0l h0u h1l h1u (le_of_not_ge hm) h2u h3l h3u)

private def coefficients_0323 : List (List (List (List ℕ))) :=
  [[[[46361201,71152241],[556392322,605974402],[565810961,590602001]],[[329205682,378787762],[1650827684,1749991844],[1433181682,1482763762]],[[296789441,321580481],[1122325282,1171907362],[881315681,906106721]]],[[[144648638,194230718],[1231744156,1330908316],[1198655198,1248237278]],[[769817356,868981516],[3554681432,3753009752],[3007983436,3107147596]],[[653058638,702640718],[2378717116,2477881276],[1837218158,1886800238]]],[[[98979439,123770479],[676735838,726317918],[633536239,658327279]],[[441995678,491577758],[1906621756,2005785916],[1576185758,1625767838]],[[356961199,381752239],[1257775838,1307357918],[956594479,981385519]]]]

private theorem identity_0323 (x0 x1 x2 x3 : ℝ) :
    (86768640 : ℝ)*(-p_variance x0 x1 x2 x3-(46361201 / 86768640 : ℝ)) =
      tensor4 coefficients_0323 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ))) := by
  norm_num [tensor4, SixRowHeadPolynomial.tensor, SixRowHeadPolynomial.row,
    coefficients_0323, p_variance] <;> ring

private theorem negative_0323 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : (1 / 4 : ℝ) ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1) : p_variance x0 x1 x2 x3 < 0 := by
  have hp := tensor4_nonneg coefficients_0323 ((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ)) (1-((x0-(3 / 8 : ℝ))/(1 / 8 : ℝ))) ((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ)) (1-((x1-(1 / 4 : ℝ))/(1 / 4 : ℝ))) ((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x2-(1 / 2 : ℝ))/(1 / 2 : ℝ))) ((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)) (1-((x3-(1 / 2 : ℝ))/(1 / 2 : ℝ)))
    (by linarith only [h0l]) (by linarith only [h0u])
    (by linarith only [h1l]) (by linarith only [h1u])
    (by linarith only [h2l]) (by linarith only [h2u])
    (by linarith only [h3l]) (by linarith only [h3u])
  rw [← identity_0323] at hp
  linarith only [hp]

private theorem node_0318 (x0 x1 x2 x3 : ℝ)
    (h0l : (3 / 8 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x1 ≤ (1 / 4 : ℝ)
  · exact node_0319 x0 x1 x2 x3 h0l h0u h1l hm h2l h2u h3l h3u h
  · exact (not_lt_of_ge h.variance) (negative_0323 x0 x1 x2 x3 h0l h0u (le_of_not_ge hm) h1u h2l h2u h3l h3u)

private theorem node_0314 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : (1 / 2 : ℝ) ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x0 ≤ (3 / 8 : ℝ)
  · exact node_0315 x0 x1 x2 x3 h0l hm h1l h1u h2l h2u h3l h3u h
  · exact node_0318 x0 x1 x2 x3 (le_of_not_ge hm) h0u h1l h1u h2l h2u h3l h3u h

theorem exclude_00 (x0 x1 x2 x3 : ℝ)
    (h0l : (1 / 4 : ℝ) ≤ x0) (h0u : x0 ≤ (1 / 2 : ℝ))
    (h1l : 0 ≤ x1) (h1u : x1 ≤ (1 / 2 : ℝ))
    (h2l : (1 / 2 : ℝ) ≤ x2) (h2u : x2 ≤ 1)
    (h3l : 0 ≤ x3) (h3u : x3 ≤ 1)
    (h : Necessary x0 x1 x2 x3) : False := by
  by_cases hm : x3 ≤ (1 / 2 : ℝ)
  · exact node_0311 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u h3l hm h
  · exact node_0314 x0 x1 x2 x3 h0l h0u h1l h1u h2l h2u (le_of_not_ge hm) h3u h


end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddleCertificate.Part08
