/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part09
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part09
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part09.certificate175
   digest: Order-four certificate decisions for chunks 157 through 175. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part01
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part02
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part06
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part07
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part08

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed3 : Closed.{u} state3 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed6 : Closed.{u} state6 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed15 : Closed.{u} state15 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed24 : Closed.{u} state24 :=
  known_of_mem boundary02.{u} (by decide)

private theorem closed112 : Closed.{u} state112 :=
  known_of_mem boundary06.{u} (by decide)

private theorem closed113 : Closed.{u} state113 :=
  known_of_mem boundary06.{u} (by decide)

private theorem closed127 : Closed.{u} state127 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed133 : Closed.{u} state133 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed134 : Closed.{u} state134 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed146 : Closed.{u} state146 :=
  known_of_mem boundary08.{u} (by decide)

private theorem closed147 : Closed.{u} state147 :=
  known_of_mem boundary08.{u} (by decide)

private theorem closed149 : Closed.{u} state149 :=
  known_of_mem boundary08.{u} (by decide)

private theorem closed155 : Closed.{u} state155 :=
  known_of_mem boundary08.{u} (by decide)

private theorem closed156 : Closed.{u} state156 :=
  known_of_mem boundary08.{u} (by decide)

private def state157 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 10, 6, 12, 10, 5, 0]
private def certificate157 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 2, 0, 3]
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (2, 0))
      (.clash (0, 0) (0, 1))
      (.clash (2, 0) (2, 3))
      (.clash (2, 3) (3, 3))
      (.clash (0, 0) (2, 0)))
    (.clash (0, 1) (3, 1))
    (.clash (0, 0) (0, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (0, 1) (3, 1))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (2, 3))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 3))
        (.transversal ![2, 0, 1, 3]
          (.clash (0, 2) (2, 2))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (0, 2))
            (.clash (0, 1) (3, 1))
            (.motif 1 3 0 1 0 2
              (.clash (0, 2) (2, 2)))
            (.clash (0, 2) (2, 2))
            (.motif 2 3 0 2 0 1
              (.clash (0, 1) (1, 1)))
            (.clash (1, 0) (3, 0)))
          (.clash (0, 0) (0, 2))
          (.clash (1, 0) (1, 3))
          (.clash (0, 0) (1, 0))
          (.clash (1, 3) (3, 3))))
      (.clash (0, 1) (1, 1))
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (1, 2)))
    (.clash (0, 0) (1, 0))
    (.clash (3, 1) (3, 3))
private theorem check157 : check [] state157 certificate157 = true := by
  decide +kernel
private theorem closed157 : Closed.{u} state157 :=
  sound (known := []) trivial check157

private def state158 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 10, 11, 12, 10, 5, 0]
private def certificate158 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 3))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 1) (3, 1))
          (.clash (1, 0) (3, 0))
          (.clash (2, 1) (2, 2))
          (.motif 2 3 1 1 2 0
            (.clash (0, 1) (3, 1)))
          (.clash (3, 0) (3, 1))))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.transversal ![2, 0, 1, 3]
        (.clash (0, 2) (2, 2))
        (.transversal ![2, 1, 0, 3]
          (.clash (0, 2) (3, 2))
          (.clash (2, 0) (2, 1))
          (.clash (0, 0) (0, 2))
          (.transversal ![1, 0, 3, 2]
            (.clash (0, 1) (3, 1))
            (.reuse 0)
            (.clash (0, 1) (1, 1))
            (.clash (2, 2) (2, 3))
            (.clash (1, 0) (1, 1))
            (.clash (2, 0) (2, 3)))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (2, 0)))
        (.clash (0, 0) (0, 2))
        (.clash (1, 0) (1, 3))
        (.clash (0, 0) (1, 0))
        (.clash (1, 2) (1, 3)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 2) (2, 2)))
    (.clash (2, 3) (3, 3))
    (.clash (3, 1) (3, 3))
    (.reuse 1)
    (.clash (1, 2) (2, 2))
    (.clash (2, 2) (2, 3))
private theorem check158 : check [state156, state157] state158 certificate158 = true := by
  decide +kernel
private theorem closed158 : Closed.{u} state158 :=
  sound (known := [state156, state157]) ⟨closed156.{u}, ⟨closed157.{u}, trivial⟩⟩ check158

private def state159 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 10, 11, 12, 13, 5, 0]
private def certificate159 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 3) (3, 3))
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 1) (2, 1))
      (.transversal ![2, 1, 0, 3]
        (.clash (0, 2) (3, 2))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (1, 1))
        (.clash (2, 2) (3, 2))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 1) (1, 1))
      (.clash (2, 0) (2, 1))
      (.clash (1, 1) (1, 3))
      (.transversal ![1, 2, 0, 3]
        (.transversal ![0, 2, 3, 1]
          (.clash (0, 0) (0, 1))
          (.clash (2, 2) (2, 3))
          (.clash (3, 1) (3, 3))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (2, 1))
            (.clash (0, 0) (0, 1))
            (.motif 2 3 0 0 3 2
              (.clash (0, 1) (0, 2)))
            (.clash (1, 3) (3, 3))
            (.transversal ![2, 1, 3, 0]
              (.clash (0, 2) (3, 2))
              (.clash (0, 1) (0, 2))
              (.reuse 0)
              (.clash (0, 1) (1, 1))
              (.clash (1, 1) (1, 3))
              (.clash (0, 1) (2, 1)))
            (.clash (0, 0) (3, 0)))
          (.clash (0, 1) (3, 1))
          (.reuse 1))
        (.clash (0, 1) (1, 1))
        (.clash (0, 0) (0, 1))
        (.clash (1, 1) (1, 2))
        (.clash (1, 2) (2, 2))
        (.clash (0, 0) (2, 0))))
    (.clash (3, 1) (3, 3))
    (.clash (2, 1) (2, 2))
    (.clash (2, 1) (3, 1))
    (.reuse 2)
private theorem check159 : check [state112, state113, state158] state159 certificate159 = true := by
  decide +kernel
private theorem closed159 : Closed.{u} state159 :=
  sound (known := [state112, state113, state158]) ⟨closed112.{u}, ⟨closed113.{u}, ⟨closed158.{u}, trivial⟩⟩⟩ check159

private def state160 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 5, 0]
private def certificate160 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 3) (3, 3))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 2) (3, 2))
      (.transversal ![1, 2, 0, 3]
        (.transversal ![1, 0, 2, 3]
          (.clash (1, 0) (1, 2))
          (.clash (1, 2) (2, 2))
          (.clash (0, 0) (0, 1))
          (.transversal ![1, 3, 0, 2]
            (.clash (1, 2) (1, 3))
            (.clash (0, 1) (0, 2))
            (.clash (0, 1) (1, 1))
            (.transversal ![1, 3, 2, 0]
              (.clash (0, 1) (0, 2))
              (.clash (1, 0) (1, 2))
              (.transversal ![0, 2, 3, 1]
                (.clash (0, 0) (0, 1))
                (.clash (2, 1) (2, 3))
                (.clash (2, 1) (3, 1))
                (.motif 1 2 3 0 3 2
                  (.clash (0, 2) (3, 2)))
                (.clash (0, 1) (3, 1))
                (.reuse 0))
              (.clash (0, 2) (2, 2))
              (.clash (2, 0) (3, 0))
              (.clash (1, 0) (3, 0)))
            (.clash (1, 1) (1, 3))
            (.clash (0, 2) (3, 2)))
          (.clash (0, 0) (1, 0))
          (.clash (2, 1) (2, 2)))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 1))
        (.clash (0, 2) (1, 2))
        (.reuse 1)
        (.clash (0, 0) (0, 2)))
      (.clash (0, 0) (0, 2))
      (.reuse 2)
      (.clash (1, 1) (2, 1))
      (.clash (0, 0) (2, 0)))
    (.clash (3, 2) (3, 3))
    (.reuse 3)
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
private theorem check160 : check [state147, state149, state155, state159] state160 certificate160 = true := by
  decide +kernel
private theorem closed160 : Closed.{u} state160 :=
  sound (known := [state147, state149, state155, state159]) ⟨closed147.{u}, ⟨closed149.{u}, ⟨closed155.{u}, ⟨closed159.{u}, trivial⟩⟩⟩⟩ check160

private def state161 : Partition := #v[0, 1, 2, 3, 1, 5, 0, 7, 5, 0, 7, 1, 2, 13, 1, 0]
private def certificate161 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (0, 2) (2, 2))
    (.clash (2, 0) (3, 0))
    (.clash (3, 0) (3, 1))
    (.clash (1, 1) (1, 3))
    (.motif 2 3 0 1 2 3
      (.clash (0, 3) (1, 3)))
    (.clash (1, 1) (3, 1))
private theorem check161 : check [] state161 certificate161 = true := by
  decide +kernel
private theorem closed161 : Closed.{u} state161 :=
  sound (known := []) trivial check161

private def state162 : Partition := #v[0, 1, 2, 3, 1, 5, 0, 7, 8, 0, 10, 1, 12, 7, 1, 0]
private def certificate162 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (3, 1))
    (.clash (2, 2) (2, 3))
    (.clash (1, 0) (3, 0))
    (.motif 2 3 0 1 2 3
      (.clash (0, 3) (1, 3)))
    (.clash (3, 0) (3, 1))
    (.transversal ![2, 3, 1, 0]
      (.transversal ![2, 1, 3, 0]
        (.clash (1, 1) (1, 3))
        (.clash (0, 1) (0, 2))
        (.clash (0, 2) (2, 2))
        (.clash (0, 1) (1, 1))
        (.transversal ![2, 1, 0, 3]
          (.clash (0, 2) (2, 2))
          (.transversal ![3, 0, 2, 1]
            (.clash (0, 1) (0, 3))
            (.columns)
            (.clash (0, 2) (0, 3))
            (.clash (0, 1) (1, 1))
            (.clash (0, 1) (0, 2))
            (.clash (0, 2) (2, 2)))
          (.clash (0, 0) (0, 2))
          (.clash (2, 0) (2, 2))
          (.clash (0, 0) (3, 0))
          (.clash (0, 0) (2, 0)))
        (.clash (1, 0) (3, 0)))
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (2, 2))
      (.clash (1, 2) (1, 3))
      (.clash (3, 0) (3, 1))
      (.clash (0, 0) (3, 0)))
private theorem check162 : check [] state162 certificate162 = true := by
  decide +kernel
private theorem closed162 : Closed.{u} state162 :=
  sound (known := []) trivial check162

private def state163 : Partition := #v[0, 1, 2, 3, 1, 5, 0, 7, 8, 0, 10, 1, 12, 10, 1, 0]
private def certificate163 : Certificate :=
  .motif 2 3 1 2 3 1
    (.clash (0, 1) (1, 1))
private theorem check163 : check [] state163 certificate163 = true := by
  decide +kernel
private theorem closed163 : Closed.{u} state163 :=
  sound (known := []) trivial check163

private def state164 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 0, 4, 1, 12, 13, 1, 0]
private def certificate164 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
    (.clash (3, 0) (3, 2))
    (.clash (1, 0) (1, 3))
    (.transversal ![0, 3, 2, 1]
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (1, 0))
      (.clash (2, 1) (3, 1))
      (.clash (1, 0) (1, 3))
      (.clash (3, 0) (3, 1))
      (.motif 2 3 1 2 3 1
        (.clash (0, 1) (1, 1))))
    (.clash (1, 0) (3, 0))
private theorem check164 : check [] state164 certificate164 = true := by
  decide +kernel
private theorem closed164 : Closed.{u} state164 :=
  sound (known := []) trivial check164

private def state165 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 7, 0, 1, 11, 1, 7, 11, 0]
private def certificate165 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.motif 0 2 1 2 1 0
      (.clash (1, 0) (3, 0)))
    (.clash (0, 0) (0, 2))
    (.clash (0, 1) (0, 2))
    (.clash (0, 0) (2, 0))
    (.clash (0, 1) (3, 1))
    (.clash (0, 0) (0, 1))
private theorem check165 : check [] state165 certificate165 = true := by
  decide +kernel
private theorem closed165 : Closed.{u} state165 :=
  sound (known := []) trivial check165

private def state166 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 0, 4, 11, 1, 13, 11, 0]
private def certificate166 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 2) (1, 3))
      (.clash (0, 0) (0, 3))
      (.clash (2, 1) (3, 1))
      (.clash (0, 3) (1, 3))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (3, 0))
        (.clash (3, 0) (3, 2))
        (.transversal ![2, 0, 3, 1]
          (.clash (0, 2) (0, 3))
          (.clash (0, 2) (3, 2))
          (.motif 0 1 2 2 0 3
            (.clash (1, 2) (3, 2)))
          (.clash (0, 3) (2, 3))
          (.clash (0, 3) (1, 3))
          (.clash (1, 3) (2, 3)))
        (.clash (1, 3) (2, 3))
        (.clash (2, 0) (2, 3)))
      (.motif 0 3 2 1 3 0
        (.clash (1, 0) (2, 0))))
    (.clash (0, 0) (0, 3))
    (.clash (0, 3) (2, 3))
    (.clash (0, 0) (1, 0))
    (.clash (2, 2) (2, 3))
    (.clash (1, 2) (3, 2))
private theorem check166 : check [] state166 certificate166 = true := by
  decide +kernel
private theorem closed166 : Closed.{u} state166 :=
  sound (known := []) trivial check166

private def state167 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 0, 10, 11, 1, 13, 11, 0]
private def certificate167 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (3, 0))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 2) (1, 3))
      (.clash (0, 0) (0, 1))
      (.clash (2, 1) (3, 1))
      (.transversal ![2, 1, 3, 0]
        (.transversal ![2, 0, 3, 1]
          (.clash (1, 0) (1, 1))
          (.clash (0, 2) (3, 2))
          (.clash (1, 1) (3, 1))
          (.motif 1 3 0 0 3 2
            (.clash (0, 1) (0, 2)))
          (.transversal ![2, 3, 0, 1]
            (.clash (0, 1) (0, 2))
            (.motif 0 2 1 2 1 0
              (.clash (0, 1) (3, 1)))
            (.clash (1, 0) (1, 1))
            (.clash (2, 0) (2, 2))
            (.clash (0, 1) (3, 1))
            (.clash (1, 0) (2, 0)))
          (.clash (3, 1) (3, 2)))
        (.clash (0, 2) (3, 2))
        (.clash (0, 1) (0, 2))
        (.motif 1 2 0 1 2 3
          (.clash (0, 0) (0, 3)))
        (.clash (0, 1) (1, 1))
        (.clash (1, 3) (2, 3)))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 2) (2, 3))
        (.reuse 0)
        (.clash (1, 3) (2, 3))
        (.clash (2, 0) (2, 3)))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 0) (0, 1))
    (.reuse 1)
    (.clash (0, 0) (1, 0))
    (.clash (1, 2) (2, 2))
private theorem check167 : check [state165, state166] state167 certificate167 = true := by
  decide +kernel
private theorem closed167 : Closed.{u} state167 :=
  sound (known := [state165, state166]) ⟨closed165.{u}, ⟨closed166.{u}, trivial⟩⟩ check167

private def state168 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 2, 5, 2, 4, 1, 12, 4, 1, 0]
private def certificate168 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (3, 1))
    (.clash (3, 0) (3, 2))
    (.clash (0, 2) (2, 2))
    (.transversal ![3, 0, 1, 2]
      (.motif 0 1 2 2 0 3
        (.clash (0, 0) (0, 1)))
      (.clash (0, 2) (0, 3))
      (.clash (0, 1) (0, 3))
      (.clash (0, 2) (2, 2))
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (0, 2)))
    (.clash (1, 0) (3, 0))
private theorem check168 : check [] state168 certificate168 = true := by
  decide +kernel
private theorem closed168 : Closed.{u} state168 :=
  sound (known := []) trivial check168

private def state169 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 7, 10, 11, 12, 13, 11, 0]
private def certificate169 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 2) (1, 3))
    (.clash (1, 2) (2, 2))
    (.clash (3, 1) (3, 3))
    (.clash (2, 1) (2, 2))
    (.clash (2, 1) (3, 1))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 1) (3, 1))
          (.clash (1, 0) (3, 0))
          (.clash (2, 1) (2, 2))
          (.motif 1 3 2 3 2 0
            (.clash (0, 0) (2, 0)))
          (.clash (3, 0) (3, 1)))
        (.clash (1, 0) (3, 0))
        (.clash (1, 2) (3, 2))
        (.clash (0, 0) (3, 0))
        (.clash (3, 0) (3, 2)))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.transversal ![2, 0, 1, 3]
        (.clash (0, 2) (2, 2))
        (.transversal ![2, 1, 0, 3]
          (.clash (1, 1) (1, 3))
          (.clash (2, 0) (2, 1))
          (.clash (0, 0) (0, 2))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (0, 2))
            (.clash (0, 1) (1, 1))
            (.reuse 0)
            (.clash (1, 1) (1, 3))
            (.clash (0, 2) (3, 2))
            (.clash (2, 0) (2, 3)))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (2, 0)))
        (.clash (0, 0) (0, 2))
        (.clash (1, 0) (1, 3))
        (.clash (0, 0) (1, 0))
        (.clash (1, 2) (1, 3)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 2) (2, 2)))
private theorem check169 : check [state168] state169 certificate169 = true := by
  decide +kernel
private theorem closed169 : Closed.{u} state169 :=
  sound (known := [state168]) ⟨closed168.{u}, trivial⟩ check169

private def state170 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 1, 6, 0, 1, 11, 1, 6, 11, 0]
private def certificate170 : Certificate :=
  .transversal ![2, 1, 0, 3]
    (.transversal ![2, 0, 3, 1]
      (.clash (1, 0) (1, 1))
      (.clash (0, 2) (3, 2))
      (.clash (0, 2) (1, 2))
      (.motif 1 2 3 0 2 3
        (.clash (0, 0) (2, 0)))
      (.clash (1, 0) (1, 2))
      (.clash (1, 2) (3, 2)))
    (.clash (0, 2) (1, 2))
    (.clash (0, 0) (0, 2))
    (.clash (1, 1) (1, 2))
    (.clash (1, 1) (2, 1))
    (.clash (0, 0) (2, 0))
private theorem check170 : check [] state170 certificate170 = true := by
  decide +kernel
private theorem closed170 : Closed.{u} state170 :=
  sound (known := []) trivial check170

private def state171 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 10, 11, 12, 6, 11, 0]
private def certificate171 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 3) (3, 3))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 1) (3, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 3))
        (.clash (2, 0) (3, 0))
        (.clash (1, 2) (3, 2))
        (.clash (3, 0) (3, 1))
        (.clash (3, 0) (3, 2)))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.clash (0, 1) (3, 1))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.clash (3, 0) (3, 2))
          (.clash (1, 3) (3, 3))
          (.transversal ![2, 0, 1, 3]
            (.transversal ![2, 1, 3, 0]
              (.clash (1, 0) (1, 1))
              (.clash (0, 1) (0, 2))
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (1, 1))
              (.clash (1, 1) (1, 3))
              (.clash (0, 1) (2, 1)))
            (.reuse 0)
            (.clash (0, 0) (0, 2))
            (.clash (1, 0) (1, 3))
            (.clash (0, 0) (1, 0))
            (.clash (0, 0) (3, 0)))
          (.clash (0, 0) (3, 0)))
        (.clash (1, 2) (1, 3))
        (.clash (1, 3) (2, 3))
        (.clash (1, 2) (3, 2)))
      (.clash (1, 2) (2, 2))
      (.clash (0, 0) (2, 0)))
    (.clash (3, 1) (3, 3))
    (.clash (2, 1) (2, 2))
    (.clash (1, 2) (1, 3))
    (.clash (1, 2) (2, 2))
private theorem check171 : check [state127] state171 certificate171 = true := by
  decide +kernel
private theorem closed171 : Closed.{u} state171 :=
  sound (known := [state127]) ⟨closed127.{u}, trivial⟩ check171

private def state172 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 6, 11, 0]
private def certificate172 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 3) (3, 3))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 3) (3, 3))
      (.clash (2, 1) (2, 2))
      (.clash (2, 1) (3, 1))
      (.transversal ![1, 0, 2, 3]
        (.transversal ![1, 2, 0, 3]
          (.clash (0, 1) (3, 1))
          (.clash (1, 0) (2, 0))
          (.clash (0, 0) (0, 1))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (3, 1))
            (.motif 2 1 3 2 0 3
              (.clash (0, 0) (2, 0)))
            (.clash (1, 0) (3, 0))
            (.clash (1, 2) (3, 2))
            (.clash (2, 0) (3, 0))
            (.clash (3, 0) (3, 2)))
          (.clash (2, 1) (3, 1))
          (.clash (0, 0) (2, 0)))
        (.transversal ![1, 2, 0, 3]
          (.clash (0, 1) (3, 1))
          (.clash (2, 0) (2, 2))
          (.clash (0, 0) (0, 1))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (3, 1))
            (.clash (1, 3) (2, 3))
            (.reuse 0)
            (.clash (1, 2) (3, 2))
            (.clash (2, 0) (3, 0))
            (.clash (3, 0) (3, 2)))
          (.clash (2, 1) (3, 1))
          (.clash (0, 0) (2, 0)))
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (1, 3))
        (.clash (0, 0) (1, 0))
        (.clash (1, 3) (3, 3)))
      (.clash (1, 2) (1, 3))
      (.clash (1, 2) (2, 2)))
    (.clash (2, 3) (3, 3))
    (.reuse 1)
    (.clash (1, 3) (2, 3))
    (.clash (2, 1) (2, 3))
private theorem check172 : check [state170, state171] state172 certificate172 = true := by
  decide +kernel
private theorem closed172 : Closed.{u} state172 :=
  sound (known := [state170, state171]) ⟨closed170.{u}, ⟨closed171.{u}, trivial⟩⟩ check172

private def state173 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 11, 0]
private def certificate173 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 2) (1, 3))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 0, 2, 3]
          (.transversal ![0, 3, 2, 1]
            (.clash (1, 2) (1, 3))
            (.clash (1, 2) (2, 2))
            (.clash (2, 1) (3, 1))
            (.transversal ![2, 3, 1, 0]
              (.clash (0, 2) (2, 2))
              (.clash (0, 0) (0, 2))
              (.transversal ![2, 1, 0, 3]
                (.motif 0 1 2 1 2 0
                  (.clash (2, 0) (3, 0)))
                (.clash (2, 0) (3, 0))
                (.clash (0, 0) (0, 2))
                (.reuse 0)
                (.clash (1, 1) (1, 2))
                (.clash (0, 0) (2, 0)))
              (.clash (1, 2) (1, 3))
              (.motif 1 3 0 0 3 2
                (.clash (0, 2) (2, 2)))
              (.clash (0, 0) (3, 0)))
            (.reuse 1)
            (.reuse 2))
          (.clash (2, 2) (2, 3))
          (.clash (0, 0) (0, 1))
          (.reuse 3)
          (.clash (0, 0) (1, 0))
          (.clash (1, 2) (2, 2)))
        (.reuse 4)
        (.clash (1, 2) (3, 2))
        (.clash (0, 0) (3, 0))
        (.clash (3, 0) (3, 2)))
      (.clash (1, 2) (3, 2))
      (.reuse 5)
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (2, 3)))
    (.clash (2, 3) (3, 3))
    (.clash (3, 1) (3, 3))
    (.clash (1, 2) (3, 2))
    (.reuse 6)
    (.clash (3, 1) (3, 2))
private theorem check173 : check [state161, state162, state163, state164, state167, state169, state172] state173 certificate173 = true := by
  decide +kernel
private theorem closed173 : Closed.{u} state173 :=
  sound (known := [state161, state162, state163, state164, state167, state169, state172]) ⟨closed161.{u}, ⟨closed162.{u}, ⟨closed163.{u}, ⟨closed164.{u}, ⟨closed167.{u}, ⟨closed169.{u}, ⟨closed172.{u}, trivial⟩⟩⟩⟩⟩⟩⟩ check173

def state174 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 0]
private def certificate174 : Certificate :=
  .transversal ![0, 1, 3, 2]
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 1) (1, 2))
      (.clash (2, 3) (3, 3))
      (.clash (1, 1) (3, 1))
      (.transversal ![1, 2, 0, 3]
        (.transversal ![1, 0, 2, 3]
          (.clash (1, 0) (1, 2))
          (.clash (1, 2) (2, 2))
          (.clash (0, 0) (0, 1))
          (.transversal ![2, 0, 1, 3]
            (.clash (0, 2) (2, 2))
            (.transversal ![2, 0, 3, 1]
              (.clash (0, 2) (2, 2))
              (.clash (0, 1) (0, 2))
              (.clash (2, 1) (3, 1))
              (.clash (1, 0) (1, 2))
              (.transversal ![0, 3, 1, 2]
                (.clash (1, 1) (1, 3))
                (.clash (0, 0) (0, 2))
                (.clash (3, 2) (3, 3))
                (.reuse 0)
                (.reuse 1)
                (.clash (0, 2) (3, 2)))
              (.clash (0, 1) (3, 1)))
            (.clash (0, 0) (0, 2))
            (.clash (2, 1) (2, 2))
            (.clash (0, 0) (1, 0))
            (.clash (1, 1) (2, 1)))
          (.clash (0, 0) (1, 0))
          (.reuse 2))
        (.reuse 3)
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (2, 3))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (2, 0)))
      (.reuse 4)
      (.reuse 5))
    (.clash (2, 3) (3, 3))
    (.clash (3, 2) (3, 3))
    (.reuse 6)
    (.reuse 7)
    (.reuse 8)
private theorem check174 : check [state133, state134, state3, state6, state15, state24, state146, state160, state173] state174 certificate174 = true := by
  decide +kernel
private theorem closed174 : Closed.{u} state174 :=
  sound (known := [state133, state134, state3, state6, state15, state24, state146, state160, state173]) ⟨closed133.{u}, ⟨closed134.{u}, ⟨closed3.{u}, ⟨closed6.{u}, ⟨closed15.{u}, ⟨closed24.{u}, ⟨closed146.{u}, ⟨closed160.{u}, ⟨closed173.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩ check174

def state175 : Partition := #v[0, 1, 7, 3, 4, 5, 1, 7, 1, 9, 5, 0, 7, 0, 4, 9]
private def certificate175 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (0, 0) (0, 2))
    (.clash (2, 1) (2, 3))
    (.clash (0, 0) (1, 0))
    (.clash (1, 3) (3, 3))
    (.clash (0, 2) (3, 2))
    (.clash (3, 2) (3, 3))
private theorem check175 : check [] state175 certificate175 = true := by
  decide +kernel
private theorem closed175 : Closed.{u} state175 :=
  sound (known := []) trivial check175

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary09 : Known.{u} [state174, state175] :=
  ⟨closed174.{u}, ⟨closed175.{u}, trivial⟩⟩

end MaLatin.OrderFourChecker
