/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part07
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part07
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part07.certificate138
   digest: Order-four certificate decisions for chunks 118 through 138. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part04
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part05
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part06

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed73 : Closed.{u} state73 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed74 : Closed.{u} state74 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed75 : Closed.{u} state75 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed77 : Closed.{u} state77 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed78 : Closed.{u} state78 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed81 : Closed.{u} state81 :=
  known_of_mem boundary05.{u} (by decide)

private theorem closed87 : Closed.{u} state87 :=
  known_of_mem boundary05.{u} (by decide)

private theorem closed103 : Closed.{u} state103 :=
  known_of_mem boundary06.{u} (by decide)

private theorem closed104 : Closed.{u} state104 :=
  known_of_mem boundary06.{u} (by decide)

private theorem closed105 : Closed.{u} state105 :=
  known_of_mem boundary06.{u} (by decide)

private theorem closed106 : Closed.{u} state106 :=
  known_of_mem boundary06.{u} (by decide)

private theorem closed111 : Closed.{u} state111 :=
  known_of_mem boundary06.{u} (by decide)

private theorem closed117 : Closed.{u} state117 :=
  known_of_mem boundary06.{u} (by decide)

private def state118 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 13, 5, 15]
private def certificate118 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 0, 2, 3]
        (.clash (1, 0) (2, 0))
        (.clash (0, 0) (0, 1))
        (.transversal ![0, 2, 1, 3]
          (.clash (1, 2) (1, 3))
          (.clash (2, 1) (2, 2))
          (.clash (0, 0) (0, 1))
          (.transversal ![2, 0, 1, 3]
            (.transversal ![2, 3, 1, 0]
              (.clash (0, 0) (0, 2))
              (.clash (0, 2) (1, 2))
              (.clash (1, 0) (3, 0))
              (.clash (1, 2) (1, 3))
              (.clash (0, 0) (3, 0))
              (.transversal ![0, 2, 3, 1]
                (.clash (0, 0) (3, 0))
                (.clash (1, 3) (2, 3))
                (.reuse 0)
                (.clash (2, 1) (2, 3))
                (.clash (2, 1) (3, 1))
                (.motif 2 3 0 1 3 0
                  (.clash (1, 3) (2, 3)))))
            (.clash (0, 2) (1, 2))
            (.clash (0, 1) (0, 2))
            (.clash (1, 0) (1, 2))
            (.clash (1, 0) (2, 0))
            (.clash (0, 1) (2, 1)))
          (.reuse 1)
          (.clash (0, 1) (2, 1)))
        (.clash (0, 0) (1, 0))
        (.reuse 2)
        (.clash (1, 3) (3, 3)))
      (.clash (0, 1) (1, 1))
      (.clash (0, 0) (2, 0))
      (.clash (1, 1) (1, 3))
      (.reuse 3))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (3, 2))
    (.reuse 4)
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
private theorem check118 : check [state104, state105, state106, state111, state117] state118 certificate118 = true := by
  decide +kernel
private theorem closed118 : Closed.{u} state118 :=
  sound (known := [state104, state105, state106, state111, state117]) ⟨closed104.{u}, ⟨closed105.{u}, ⟨closed106.{u}, ⟨closed111.{u}, ⟨closed117.{u}, trivial⟩⟩⟩⟩⟩ check118

private def state119 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 0, 1, 6, 0, 11, 6, 0, 11, 1]
private def certificate119 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (1, 0) (1, 1))
    (.clash (0, 2) (3, 2))
    (.clash (0, 2) (1, 2))
    (.motif 1 2 3 1 2 3
      (.clash (0, 1) (2, 1)))
    (.clash (1, 1) (1, 2))
    (.clash (1, 2) (3, 2))
private theorem check119 : check [] state119 certificate119 = true := by
  decide +kernel
private theorem closed119 : Closed.{u} state119 :=
  sound (known := []) trivial check119

private def state120 : Partition := #v[0, 6, 2, 3, 4, 5, 6, 0, 6, 9, 0, 11, 12, 0, 11, 6]
private def certificate120 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.transversal ![2, 1, 3, 0]
      (.clash (1, 0) (1, 1))
      (.clash (0, 2) (3, 2))
      (.clash (1, 0) (3, 0))
      (.motif 1 3 0 1 3 2
        (.clash (0, 0) (0, 2)))
      (.transversal ![2, 3, 1, 0]
        (.clash (0, 0) (0, 2))
        (.motif 0 2 1 2 0 1
          (.clash (0, 0) (3, 0)))
        (.clash (1, 0) (1, 1))
        (.clash (2, 1) (2, 2))
        (.clash (0, 0) (3, 0))
        (.clash (1, 1) (2, 1)))
      (.clash (3, 0) (3, 2)))
    (.clash (0, 2) (3, 2))
    (.clash (0, 0) (0, 2))
    (.motif 1 2 0 0 2 3
      (.clash (0, 1) (0, 3)))
    (.clash (0, 0) (1, 0))
    (.clash (1, 3) (2, 3))
private theorem check120 : check [] state120 certificate120 = true := by
  decide +kernel
private theorem closed120 : Closed.{u} state120 :=
  sound (known := []) trivial check120

private def state121 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 1, 9, 0, 11, 12, 0, 11, 4]
private def certificate121 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 2) (1, 3))
      (.clash (2, 1) (2, 2))
      (.clash (0, 0) (0, 2))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (2, 3))
        (.clash (2, 0) (3, 0))
        (.clash (1, 2) (3, 2))
        (.transversal ![2, 1, 3, 0]
          (.clash (1, 0) (1, 1))
          (.clash (0, 2) (3, 2))
          (.clash (0, 2) (1, 2))
          (.motif 1 2 3 1 2 3
            (.clash (0, 2) (1, 2)))
          (.clash (1, 1) (1, 2))
          (.clash (1, 2) (3, 2)))
        (.clash (3, 0) (3, 2)))
      (.clash (0, 2) (1, 2))
      (.motif 0 2 3 1 2 0
        (.clash (1, 0) (3, 0))))
    (.clash (0, 2) (3, 2))
    (.clash (0, 0) (0, 2))
    (.clash (2, 3) (3, 3))
    (.clash (0, 0) (1, 0))
    (.clash (1, 3) (2, 3))
private theorem check121 : check [] state121 certificate121 = true := by
  decide +kernel
private theorem closed121 : Closed.{u} state121 :=
  sound (known := []) trivial check121

private def state122 : Partition := #v[0, 1, 2, 3, 1, 5, 6, 0, 8, 9, 0, 1, 12, 0, 1, 6]
private def certificate122 : Certificate :=
  .transversal ![2, 0, 1, 3]
    (.clash (0, 1) (0, 2))
    (.transversal ![2, 1, 0, 3]
      (.clash (1, 1) (2, 1))
      (.clash (2, 0) (2, 1))
      (.clash (0, 2) (1, 2))
      (.transversal ![2, 1, 3, 0]
        (.clash (1, 1) (2, 1))
        (.clash (0, 1) (0, 2))
        (.motif 0 3 1 0 2 1
          (.clash (1, 1) (2, 1)))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (3, 0))
        (.clash (1, 0) (3, 0)))
      (.clash (1, 1) (1, 2))
      (.motif 1 2 0 0 2 3
        (.clash (0, 3) (3, 3))))
    (.clash (0, 2) (1, 2))
    (.clash (0, 1) (2, 1))
    (.clash (1, 0) (1, 2))
    (.motif 2 3 0 1 2 3
      (.clash (0, 0) (0, 3)))
private theorem check122 : check [] state122 certificate122 = true := by
  decide +kernel
private theorem closed122 : Closed.{u} state122 :=
  sound (known := []) trivial check122

private def state123 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 0, 1, 12, 0, 1, 4]
private def certificate123 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (1, 2) (3, 2))
    (.clash (2, 0) (2, 3))
    (.clash (2, 3) (3, 3))
    (.transversal ![0, 2, 1, 3]
      (.clash (0, 0) (2, 0))
      (.clash (2, 1) (2, 2))
      (.clash (0, 0) (1, 0))
      (.clash (2, 0) (2, 1))
      (.clash (1, 0) (1, 2))
      (.motif 2 3 0 1 2 3
        (.clash (0, 0) (0, 3))))
    (.clash (1, 0) (1, 2))
    (.clash (1, 0) (2, 0))
private theorem check123 : check [] state123 certificate123 = true := by
  decide +kernel
private theorem closed123 : Closed.{u} state123 :=
  sound (known := []) trivial check123

private def state124 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 0, 1, 12, 0, 1, 15]
private def certificate124 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 2) (1, 3))
      (.clash (2, 1) (2, 2))
      (.clash (1, 3) (3, 3))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (2, 0))
        (.clash (2, 3) (3, 3))
        (.clash (2, 0) (2, 1))
        (.motif 2 3 0 1 2 3
          (.clash (0, 0) (0, 3)))
        (.transversal ![2, 0, 1, 3]
          (.clash (0, 1) (0, 2))
          (.clash (0, 2) (1, 2))
          (.transversal ![2, 3, 1, 0]
            (.clash (0, 0) (0, 2))
            (.clash (0, 2) (1, 2))
            (.clash (2, 0) (3, 0))
            (.clash (1, 2) (1, 3))
            (.clash (0, 0) (3, 0))
            (.transversal ![2, 1, 3, 0]
              (.transversal ![3, 1, 2, 0]
                (.clash (0, 2) (0, 3))
                (.clash (0, 0) (0, 3))
                (.columns)
                (.clash (0, 0) (0, 2))
                (.clash (0, 2) (1, 2))
                (.clash (0, 0) (3, 0)))
              (.clash (0, 1) (0, 2))
              (.clash (0, 2) (1, 2))
              (.clash (0, 1) (1, 1))
              (.clash (1, 1) (1, 2))
              (.clash (0, 1) (2, 1))))
          (.clash (0, 1) (2, 1))
          (.clash (1, 0) (2, 0))
          (.clash (2, 0) (2, 1))))
      (.reuse 0)
      (.motif 2 3 0 1 2 3
        (.clash (0, 0) (0, 3))))
    (.clash (0, 0) (0, 1))
    (.clash (2, 3) (3, 3))
    (.clash (0, 0) (1, 0))
    (.reuse 1)
    (.clash (1, 3) (3, 3))
private theorem check124 : check [state122, state123] state124 certificate124 = true := by
  decide +kernel
private theorem closed124 : Closed.{u} state124 :=
  sound (known := [state122, state123]) ⟨closed122.{u}, ⟨closed123.{u}, trivial⟩⟩ check124

private def state125 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 0, 11, 12, 0, 11, 15]
private def certificate125 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (2, 2))
    (.clash (2, 1) (2, 2))
    (.clash (3, 1) (3, 3))
    (.clash (1, 2) (1, 3))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 2, 3, 0]
        (.clash (1, 0) (1, 2))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.clash (1, 0) (3, 0))
          (.clash (2, 1) (2, 2))
          (.motif 3 1 2 3 0 2
            (.clash (0, 0) (3, 0)))
          (.clash (0, 0) (3, 0)))
        (.clash (1, 0) (3, 0))
        (.clash (1, 2) (3, 2))
        (.clash (3, 0) (3, 3))
        (.clash (3, 0) (3, 2)))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.clash (2, 0) (3, 0))
          (.clash (2, 1) (2, 2))
          (.transversal ![2, 3, 0, 1]
            (.motif 0 2 1 2 0 1
              (.clash (1, 1) (3, 1)))
            (.clash (0, 1) (0, 2))
            (.clash (0, 0) (0, 2))
            (.clash (0, 1) (2, 1))
            (.clash (0, 0) (3, 0))
            (.clash (0, 0) (0, 1)))
          (.clash (0, 0) (3, 0)))
        (.clash (1, 2) (3, 2))
        (.clash (2, 0) (2, 1))
        (.clash (1, 3) (2, 3))
        (.clash (2, 0) (2, 3)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 2))
      (.clash (1, 2) (2, 2)))
    (.clash (1, 3) (3, 3))
private theorem check125 : check [] state125 certificate125 = true := by
  decide +kernel
private theorem closed125 : Closed.{u} state125 :=
  sound (known := []) trivial check125

private def state126 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 7, 6, 7, 0, 1, 7, 6, 1, 0]
private def certificate126 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (1, 0) (1, 1))
    (.clash (0, 1) (0, 2))
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (1, 1))
    (.clash (1, 1) (1, 3))
    (.clash (0, 1) (2, 1))
private theorem check126 : check [] state126 certificate126 = true := by
  decide +kernel
private theorem closed126 : Closed.{u} state126 :=
  sound (known := []) trivial check126

def state127 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 2, 6, 2, 0, 1, 2, 6, 1, 0]
private def certificate127 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (0, 2))
    (.clash (0, 2) (1, 2))
    (.transversal ![2, 1, 0, 3]
      (.clash (1, 1) (1, 3))
      (.clash (0, 2) (1, 2))
      (.clash (0, 0) (0, 2))
      (.clash (1, 1) (1, 2))
      (.transversal ![3, 0, 2, 1]
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 3))
        (.columns)
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (2, 0)))
      (.clash (0, 0) (2, 0)))
    (.clash (1, 0) (1, 2))
    (.clash (0, 1) (3, 1))
private theorem check127 : check [] state127 certificate127 = true := by
  decide +kernel
private theorem closed127 : Closed.{u} state127 :=
  sound (known := []) trivial check127

private def state128 : Partition := #v[0, 1, 2, 3, 2, 5, 8, 0, 8, 2, 0, 1, 12, 8, 1, 2]
private def certificate128 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (1, 0) (1, 1))
    (.clash (0, 1) (0, 2))
    (.clash (1, 0) (3, 0))
    (.clash (0, 1) (1, 1))
    (.transversal ![3, 0, 2, 1]
      (.clash (0, 2) (0, 3))
      (.clash (0, 0) (0, 3))
      (.motif 0 1 2 0 2 3
        (.clash (0, 1) (0, 2)))
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (1, 2))
      (.clash (0, 0) (2, 0)))
    (.clash (3, 0) (3, 2))
private theorem check128 : check [] state128 certificate128 = true := by
  decide +kernel
private theorem closed128 : Closed.{u} state128 :=
  sound (known := []) trivial check128

private def state129 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 6, 11, 9]
private def certificate129 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (2, 1))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (3, 1))
          (.motif 1 2 3 2 3 0
            (.clash (0, 0) (3, 0)))
          (.clash (1, 0) (3, 0))
          (.clash (1, 2) (3, 2))
          (.clash (2, 0) (3, 0))
          (.clash (3, 0) (3, 2)))
        (.clash (2, 1) (3, 1))
        (.clash (2, 0) (2, 1)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![2, 0, 3, 1]
        (.transversal ![2, 3, 0, 1]
          (.clash (0, 0) (0, 2))
          (.clash (1, 0) (2, 0))
          (.clash (0, 2) (1, 2))
          (.clash (0, 0) (2, 0))
          (.clash (1, 2) (1, 3))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 0) (0, 1))
            (.clash (0, 1) (3, 1))
            (.reuse 0)
            (.clash (0, 0) (2, 0))
            (.clash (1, 3) (2, 3))
            (.clash (1, 2) (3, 2))))
        (.clash (0, 2) (3, 2))
        (.clash (0, 2) (1, 2))
        (.clash (2, 1) (2, 3))
        (.clash (1, 0) (1, 2))
        (.clash (1, 2) (3, 2)))
      (.clash (1, 3) (3, 3)))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (2, 3))
    (.clash (1, 3) (3, 3))
    (.clash (1, 3) (2, 3))
    (.clash (2, 1) (2, 3))
private theorem check129 : check [state128] state129 certificate129 = true := by
  decide +kernel
private theorem closed129 : Closed.{u} state129 :=
  sound (known := [state128]) ⟨closed128.{u}, trivial⟩ check129

private def state130 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 6, 11, 15]
private def certificate130 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (2, 2))
    (.clash (2, 1) (2, 2))
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 3) (3, 3))
      (.clash (2, 1) (2, 2))
      (.clash (2, 2) (2, 3))
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
              (.reuse 0)
              (.reuse 1)
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
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (2, 3)))
    (.clash (2, 1) (3, 1))
    (.clash (3, 1) (3, 3))
    (.reuse 2)
private theorem check130 : check [state126, state127, state129] state130 certificate130 = true := by
  decide +kernel
private theorem closed130 : Closed.{u} state130 :=
  sound (known := [state126, state127, state129]) ⟨closed126.{u}, ⟨closed127.{u}, ⟨closed129.{u}, trivial⟩⟩⟩ check130

private def state131 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 13, 11, 15]
private def certificate131 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 2) (2, 2))
    (.clash (2, 2) (2, 3))
    (.transversal ![0, 3, 1, 2]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 0, 2, 3]
          (.clash (1, 0) (2, 0))
          (.clash (0, 0) (0, 1))
          (.transversal ![0, 2, 1, 3]
            (.clash (1, 2) (1, 3))
            (.clash (2, 1) (2, 2))
            (.clash (0, 0) (0, 1))
            (.transversal ![1, 2, 3, 0]
              (.clash (0, 1) (2, 1))
              (.clash (2, 0) (2, 3))
              (.clash (2, 0) (3, 0))
              (.clash (1, 2) (3, 2))
              (.transversal ![2, 0, 1, 3]
                (.reuse 0)
                (.clash (0, 2) (1, 2))
                (.clash (0, 1) (0, 2))
                (.clash (1, 0) (1, 2))
                (.clash (1, 0) (2, 0))
                (.clash (0, 1) (2, 1)))
              (.clash (3, 0) (3, 2)))
            (.reuse 1)
            (.clash (0, 1) (2, 1)))
          (.clash (0, 0) (1, 0))
          (.reuse 2)
          (.clash (1, 3) (3, 3)))
        (.reuse 3)
        (.clash (0, 0) (2, 0))
        (.clash (1, 3) (2, 3))
        (.clash (2, 0) (2, 3)))
      (.clash (2, 1) (2, 2))
      (.clash (2, 2) (2, 3))
      (.reuse 4)
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (2, 3)))
    (.clash (1, 2) (3, 2))
    (.reuse 5)
    (.clash (3, 1) (3, 2))
private theorem check131 : check [state119, state120, state121, state124, state125, state130] state131 certificate131 = true := by
  decide +kernel
private theorem closed131 : Closed.{u} state131 :=
  sound (known := [state119, state120, state121, state124, state125, state130]) ⟨closed119.{u}, ⟨closed120.{u}, ⟨closed121.{u}, ⟨closed124.{u}, ⟨closed125.{u}, ⟨closed130.{u}, trivial⟩⟩⟩⟩⟩⟩ check131

def state132 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 13, 14, 15]
private def certificate132 : Certificate :=
  .transversal ![0, 1, 3, 2]
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 1) (1, 2))
      (.clash (2, 2) (2, 3))
      (.clash (1, 1) (3, 1))
      (.transversal ![0, 2, 1, 3]
        (.clash (1, 1) (1, 2))
        (.clash (1, 1) (2, 1))
        (.transversal ![1, 2, 0, 3]
          (.transversal ![1, 3, 2, 0]
            (.clash (1, 2) (1, 3))
            (.clash (0, 0) (0, 1))
            (.transversal ![0, 3, 1, 2]
              (.clash (1, 1) (1, 3))
              (.clash (1, 1) (2, 1))
              (.clash (2, 2) (3, 2))
              (.motif 1 2 3 3 2 1
                (.clash (0, 1) (3, 1)))
              (.transversal ![2, 3, 1, 0]
                (.clash (0, 2) (3, 2))
                (.reuse 0)
                (.clash (0, 1) (0, 2))
                (.motif 1 2 0 1 3 2
                  (.clash (0, 2) (3, 2)))
                (.clash (1, 2) (1, 3))
                (.clash (0, 1) (2, 1)))
              (.reuse 1))
            (.clash (1, 1) (1, 3))
            (.reuse 2)
            (.clash (0, 0) (3, 0)))
          (.reuse 3)
          (.clash (0, 0) (0, 1))
          (.clash (2, 0) (2, 3))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (2, 0)))
        (.clash (2, 1) (2, 3))
        (.clash (2, 3) (3, 3))
        (.reuse 4))
      (.reuse 5)
      (.reuse 6))
    (.clash (2, 2) (2, 3))
    (.clash (2, 2) (3, 2))
    (.reuse 7)
    (.reuse 8)
    (.reuse 9)
private theorem check132 : check [state73, state74, state75, state77, state78, state81, state87, state103, state118, state131] state132 certificate132 = true := by
  decide +kernel
private theorem closed132 : Closed.{u} state132 :=
  sound (known := [state73, state74, state75, state77, state78, state81, state87, state103, state118, state131]) ⟨closed73.{u}, ⟨closed74.{u}, ⟨closed75.{u}, ⟨closed77.{u}, ⟨closed78.{u}, ⟨closed81.{u}, ⟨closed87.{u}, ⟨closed103.{u}, ⟨closed118.{u}, ⟨closed131.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ check132

def state133 : Partition := #v[0, 1, 7, 3, 4, 0, 1, 7, 8, 7, 4, 1, 12, 4, 14, 0]
private def certificate133 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (0, 2))
    (.clash (2, 0) (2, 3))
    (.clash (1, 2) (3, 2))
    (.clash (2, 0) (2, 1))
    (.clash (0, 2) (3, 2))
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 1) (0, 2))
      (.clash (0, 1) (3, 1))
      (.transversal ![3, 1, 2, 0]
        (.clash (0, 0) (0, 3))
        (.motif 0 2 1 2 3 1
          (.clash (0, 0) (0, 3)))
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (1, 0))
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (3, 1)))
      (.clash (0, 2) (2, 2))
      (.motif 1 3 0 0 3 1
        (.clash (0, 1) (0, 2)))
      (.clash (1, 0) (3, 0)))
private theorem check133 : check [] state133 certificate133 = true := by
  decide +kernel
private theorem closed133 : Closed.{u} state133 :=
  sound (known := []) trivial check133

def state134 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 2, 4, 1, 12, 4, 7, 0]
private def certificate134 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (1, 2) (1, 3))
    (.clash (0, 1) (3, 1))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 2) (3, 2))
      (.clash (2, 0) (2, 1))
      (.clash (0, 2) (2, 2))
      (.motif 1 2 3 2 0 3
        (.clash (0, 0) (1, 0)))
      (.clash (1, 0) (1, 3))
      (.clash (1, 0) (2, 0)))
    (.clash (1, 0) (1, 3))
    (.clash (3, 0) (3, 2))
    (.clash (1, 0) (3, 0))
private theorem check134 : check [] state134 certificate134 = true := by
  decide +kernel
private theorem closed134 : Closed.{u} state134 :=
  sound (known := []) trivial check134

def state135 : Partition := #v[0, 1, 2, 3, 3, 5, 0, 7, 8, 9, 1, 5, 1, 7, 14, 0]
private def certificate135 : Certificate :=
  .transversal ![3, 2, 0, 1]
    (.clash (0, 0) (0, 3))
    (.clash (1, 0) (2, 0))
    (.clash (0, 3) (1, 3))
    (.clash (0, 0) (2, 0))
    (.clash (1, 2) (1, 3))
    (.transversal ![0, 3, 1, 2]
      (.clash (0, 0) (2, 0))
      (.transversal ![2, 3, 1, 0]
        (.motif 0 1 2 0 3 2
          (.clash (0, 1) (0, 3)))
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (2, 0))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1)))
      (.clash (1, 2) (3, 2))
      (.clash (2, 0) (2, 1))
      (.clash (3, 1) (3, 2))
      (.motif 3 2 0 1 2 0
        (.clash (1, 2) (3, 2))))
private theorem check135 : check [] state135 certificate135 = true := by
  decide +kernel
private theorem closed135 : Closed.{u} state135 :=
  sound (known := []) trivial check135

def state136 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 4, 5, 1, 13, 14, 0]
private def certificate136 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (1, 0) (3, 0))
    (.clash (0, 1) (1, 1))
    (.clash (3, 0) (3, 2))
    (.clash (1, 0) (1, 1))
    (.clash (2, 2) (3, 2))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 2) (3, 2))
      (.transversal ![2, 0, 1, 3]
        (.clash (0, 2) (2, 2))
        (.clash (2, 0) (2, 1))
        (.clash (0, 0) (0, 2))
        (.clash (2, 1) (2, 2))
        (.clash (0, 0) (1, 0))
        (.transversal ![3, 0, 1, 2]
          (.transversal ![0, 3, 2, 1]
            (.clash (1, 2) (1, 3))
            (.clash (0, 0) (0, 3))
            (.clash (2, 1) (3, 1))
            (.clash (0, 3) (1, 3))
            (.motif 1 3 2 1 3 2
              (.clash (0, 3) (1, 3)))
            (.motif 0 3 2 1 3 0
              (.clash (0, 2) (0, 3))))
          (.clash (0, 0) (0, 3))
          (.clash (0, 3) (2, 3))
          (.clash (0, 0) (1, 0))
          (.clash (1, 0) (1, 1))
          (.clash (1, 1) (1, 2))))
      (.clash (0, 0) (0, 2))
      (.clash (2, 0) (2, 3))
      (.clash (1, 1) (1, 2))
      (.clash (0, 0) (2, 0)))
private theorem check136 : check [] state136 certificate136 = true := by
  decide +kernel
private theorem closed136 : Closed.{u} state136 :=
  sound (known := []) trivial check136

def state137 : Partition := #v[9, 1, 2, 3, 4, 2, 9, 7, 8, 9, 1, 2, 2, 7, 14, 9]
private def certificate137 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.motif 0 1 2 1 2 0
      (.clash (2, 0) (2, 3)))
    (.clash (0, 1) (0, 2))
    (.clash (2, 2) (3, 2))
    (.clash (1, 0) (1, 1))
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 1) (3, 1))
      (.clash (2, 0) (2, 2))
      (.clash (2, 2) (3, 2))
      (.motif 2 3 0 0 3 1
        (.clash (0, 1) (0, 2)))
      (.clash (1, 0) (1, 3))
      (.clash (1, 0) (2, 0)))
    (.clash (0, 2) (3, 2))
private theorem check137 : check [] state137 certificate137 = true := by
  decide +kernel
private theorem closed137 : Closed.{u} state137 :=
  sound (known := []) trivial check137

def state138 : Partition := #v[9, 1, 2, 3, 4, 2, 9, 7, 8, 9, 7, 2, 2, 7, 14, 9]
private def certificate138 : Certificate :=
  .motif 1 2 0 2 3 1
    (.clash (0, 1) (3, 1))
private theorem check138 : check [] state138 certificate138 = true := by
  decide +kernel
private theorem closed138 : Closed.{u} state138 :=
  sound (known := []) trivial check138

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary07 : Known.{u} [state127, state132, state133, state134, state135, state136, state137, state138] :=
  ⟨closed127.{u}, ⟨closed132.{u}, ⟨closed133.{u}, ⟨closed134.{u}, ⟨closed135.{u}, ⟨closed136.{u}, ⟨closed137.{u}, ⟨closed138.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
