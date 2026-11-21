/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part05
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part05
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part05.certificate99
   digest: Order-four certificate decisions for chunks 81 through 99. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part01
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part04

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed7 : Closed.{u} state7 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed8 : Closed.{u} state8 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed12 : Closed.{u} state12 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed16 : Closed.{u} state16 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed17 : Closed.{u} state17 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed18 : Closed.{u} state18 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed19 : Closed.{u} state19 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed80 : Closed.{u} state80 :=
  known_of_mem boundary04.{u} (by decide)

def state81 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 11, 12, 6, 14, 15]
private def certificate81 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 1) (1, 2))
    (.clash (1, 1) (2, 1))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 1) (3, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 3))
        (.clash (2, 0) (3, 0))
        (.transversal ![2, 1, 3, 0]
          (.clash (0, 0) (0, 2))
          (.clash (0, 2) (1, 2))
          (.transversal ![3, 0, 2, 1]
            (.transversal ![1, 0, 3, 2]
              (.clash (0, 1) (0, 3))
              (.clash (0, 1) (3, 1))
              (.transversal ![0, 3, 1, 2]
                (.clash (1, 1) (1, 3))
                (.clash (1, 1) (2, 1))
                (.clash (0, 0) (0, 1))
                (.motif 1 2 3 1 3 2
                  (.clash (0, 1) (2, 1)))
                (.motif 0 1 3 3 1 0
                  (.clash (0, 1) (0, 2)))
                (.clash (0, 1) (2, 1)))
              (.clash (0, 3) (2, 3))
              (.reuse 0)
              (.clash (1, 2) (3, 2)))
            (.clash (0, 0) (0, 3))
            (.clash (0, 3) (2, 3))
            (.clash (0, 0) (1, 0))
            (.clash (1, 0) (1, 2))
            (.clash (1, 1) (1, 2)))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (3, 0))
          (.clash (3, 0) (3, 1)))
        (.clash (3, 0) (3, 1))
        (.reuse 1))
      (.clash (0, 0) (0, 1))
      (.reuse 2)
      (.clash (1, 1) (1, 2))
      (.clash (0, 0) (2, 0)))
    (.clash (2, 1) (3, 1))
    (.clash (3, 1) (3, 3))
    (.reuse 3)
private theorem check81 : check [state7, state8, state12, state80] state81 certificate81 = true := by
  decide +kernel
private theorem closed81 : Closed.{u} state81 :=
  sound (known := [state7, state8, state12, state80]) ⟨closed7.{u}, ⟨closed8.{u}, ⟨closed12.{u}, ⟨closed80.{u}, trivial⟩⟩⟩⟩ check81

private def state82 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 2, 12, 2, 14, 8]
private def certificate82 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.clash (0, 0) (0, 3))
    (.clash (0, 3) (3, 3))
    (.transversal ![3, 2, 0, 1]
      (.clash (1, 2) (3, 2))
      (.clash (0, 3) (3, 3))
      (.clash (0, 2) (0, 3))
      (.transversal ![0, 3, 1, 2]
        (.clash (1, 1) (1, 3))
        (.clash (1, 1) (2, 1))
        (.clash (0, 0) (0, 3))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (2, 1))
          (.motif 0 3 1 2 3 1
            (.clash (0, 0) (0, 3)))
          (.clash (0, 1) (0, 3))
          (.clash (1, 2) (1, 3))
          (.clash (0, 3) (1, 3))
          (.clash (0, 3) (3, 3)))
        (.clash (0, 3) (1, 3))
        (.transversal ![2, 3, 1, 0]
          (.clash (1, 3) (2, 3))
          (.clash (0, 2) (0, 3))
          (.clash (3, 0) (3, 1))
          (.clash (0, 3) (1, 3))
          (.transversal ![1, 0, 2, 3]
            (.transversal ![1, 2, 3, 0]
              (.clash (1, 0) (1, 2))
              (.clash (0, 1) (0, 2))
              (.clash (1, 0) (1, 3))
              (.clash (0, 2) (1, 2))
              (.clash (1, 2) (1, 3))
              (.clash (1, 3) (2, 3)))
            (.clash (0, 0) (0, 1))
            (.motif 0 3 1 2 3 1
              (.clash (0, 0) (0, 3)))
            (.clash (0, 0) (1, 0))
            (.clash (1, 0) (1, 2))
            (.clash (0, 0) (2, 0)))
          (.clash (3, 0) (3, 2))))
      (.clash (0, 2) (1, 2))
      (.clash (2, 0) (2, 3)))
    (.clash (0, 0) (2, 0))
    (.clash (2, 2) (3, 2))
    (.clash (3, 2) (3, 3))
private theorem check82 : check [] state82 certificate82 = true := by
  decide +kernel
private theorem closed82 : Closed.{u} state82 :=
  sound (known := []) trivial check82

private def state83 : Partition := #v[0, 8, 7, 3, 4, 0, 8, 7, 8, 7, 0, 11, 7, 11, 14, 8]
private def certificate83 : Certificate :=
  .motif 0 2 1 1 2 0
    (.clash (1, 0) (1, 3))
private theorem check83 : check [] state83 certificate83 = true := by
  decide +kernel
private theorem closed83 : Closed.{u} state83 :=
  sound (known := []) trivial check83

private def state84 : Partition := #v[0, 1, 7, 3, 4, 0, 1, 7, 8, 9, 0, 11, 7, 11, 9, 15]
private def certificate84 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (0, 2))
    (.transversal ![3, 1, 0, 2]
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3))
      (.transversal ![0, 2, 1, 3]
        (.clash (0, 0) (0, 1))
        (.clash (0, 0) (0, 3))
        (.motif 0 3 1 3 0 2
          (.clash (0, 0) (0, 1)))
        (.clash (0, 1) (0, 3))
        (.transversal ![2, 0, 1, 3]
          (.clash (1, 0) (1, 3))
          (.clash (0, 2) (0, 3))
          (.clash (0, 1) (0, 2))
          (.motif 1 2 0 1 0 2
            (.clash (0, 2) (0, 3)))
          (.clash (1, 0) (1, 2))
          (.clash (0, 1) (0, 3)))
        (.clash (0, 3) (3, 3)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 1) (2, 1))
      (.clash (0, 1) (2, 1)))
    (.clash (0, 1) (2, 1))
    (.clash (2, 0) (3, 0))
    (.clash (0, 2) (3, 2))
    (.clash (2, 0) (2, 1))
private theorem check84 : check [] state84 certificate84 = true := by
  decide +kernel
private theorem closed84 : Closed.{u} state84 :=
  sound (known := []) trivial check84

private def state85 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 6, 2, 6, 14, 15]
private def certificate85 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 1) (1, 2))
      (.clash (1, 1) (2, 1))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (3, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (0, 3))
          (.clash (0, 1) (3, 1))
          (.transversal ![0, 3, 1, 2]
            (.clash (1, 1) (1, 3))
            (.clash (1, 1) (2, 1))
            (.clash (0, 0) (0, 1))
            (.motif 1 2 3 1 3 2
              (.clash (0, 1) (2, 1)))
            (.motif 0 1 3 3 1 0
              (.clash (0, 1) (0, 2)))
            (.clash (0, 1) (2, 1)))
          (.clash (0, 3) (2, 3))
          (.motif 0 3 2 2 3 0
            (.clash (0, 1) (0, 3)))
          (.clash (1, 2) (3, 2)))
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (2, 3))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (2, 0)))
      (.clash (2, 1) (2, 3))
      (.clash (2, 3) (3, 3))
      (.transversal ![1, 0, 2, 3]
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 3))
        (.clash (0, 3) (3, 3))
        (.clash (1, 1) (2, 1))))
    (.clash (0, 0) (0, 3))
    (.clash (0, 3) (2, 3))
    (.clash (0, 0) (1, 0))
    (.clash (1, 0) (1, 2))
    (.clash (1, 1) (1, 2))
private theorem check85 : check [] state85 certificate85 = true := by
  decide +kernel
private theorem closed85 : Closed.{u} state85 :=
  sound (known := []) trivial check85

private def state86 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 11, 2, 11, 14, 15]
private def certificate86 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.transversal ![1, 3, 2, 0]
      (.clash (1, 2) (1, 3))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (0, 2))
      (.clash (1, 1) (1, 3))
      (.transversal ![0, 3, 1, 2]
        (.clash (0, 0) (0, 2))
        (.clash (1, 1) (2, 1))
        (.clash (2, 2) (3, 2))
        (.transversal ![0, 2, 1, 3]
          (.clash (0, 0) (0, 1))
          (.clash (0, 0) (0, 2))
          (.transversal ![1, 0, 3, 2]
            (.clash (1, 0) (1, 2))
            (.clash (0, 1) (3, 1))
            (.clash (1, 2) (3, 2))
            (.motif 1 3 0 0 3 1
              (.clash (0, 1) (0, 2)))
            (.transversal ![1, 3, 0, 2]
              (.clash (0, 1) (0, 2))
              (.motif 0 2 1 1 2 0
                (.clash (0, 2) (3, 2)))
              (.clash (1, 0) (1, 2))
              (.clash (2, 0) (2, 1))
              (.clash (0, 2) (3, 2))
              (.clash (1, 0) (2, 0)))
            (.clash (3, 1) (3, 2)))
          (.clash (0, 1) (0, 2))
          (.transversal ![2, 1, 0, 3]
            (.clash (0, 0) (0, 2))
            (.clash (2, 0) (2, 1))
            (.clash (0, 1) (0, 2))
            (.clash (0, 0) (2, 0))
            (.clash (0, 0) (0, 1))
            (.reuse 0))
          (.clash (1, 3) (3, 3)))
        (.clash (0, 2) (3, 2))
        (.reuse 1))
      (.clash (0, 0) (0, 2)))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (0, 2))
    (.reuse 2)
    (.clash (0, 2) (1, 2))
    (.clash (3, 0) (3, 1))
private theorem check86 : check [state83, state84, state85] state86 certificate86 = true := by
  decide +kernel
private theorem closed86 : Closed.{u} state86 :=
  sound (known := [state83, state84, state85]) ⟨closed83.{u}, ⟨closed84.{u}, ⟨closed85.{u}, trivial⟩⟩⟩ check86

def state87 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 11, 12, 11, 14, 15]
private def certificate87 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 0) (0, 2))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 0) (0, 2))
      (.clash (2, 0) (2, 3))
      (.clash (2, 3) (3, 3))
      (.clash (0, 0) (2, 0))
      (.transversal ![2, 0, 1, 3]
        (.transversal ![0, 3, 1, 2]
          (.clash (1, 1) (1, 3))
          (.clash (1, 1) (2, 1))
          (.clash (2, 2) (3, 2))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (2, 1))
            (.clash (0, 0) (0, 1))
            (.transversal ![1, 2, 0, 3]
              (.motif 0 1 2 2 1 0
                (.clash (2, 0) (3, 0)))
              (.clash (2, 0) (3, 0))
              (.clash (0, 0) (0, 1))
              (.transversal ![1, 3, 0, 2]
                (.clash (0, 1) (2, 1))
                (.clash (2, 0) (3, 0))
                (.clash (3, 0) (3, 2))
                (.clash (1, 2) (1, 3))
                (.motif 2 3 0 2 1 3
                  (.clash (0, 3) (1, 3)))
                (.clash (1, 2) (3, 2)))
              (.clash (1, 1) (1, 2))
              (.clash (0, 0) (2, 0)))
            (.clash (1, 1) (1, 3))
            (.reuse 0)
            (.clash (0, 0) (3, 0)))
          (.reuse 1)
          (.reuse 2))
        (.clash (2, 1) (2, 3))
        (.clash (0, 0) (0, 2))
        (.reuse 3)
        (.clash (0, 0) (1, 0))
        (.clash (1, 1) (2, 1)))
      (.reuse 4))
    (.reuse 5)
    (.clash (1, 1) (3, 1))
    (.clash (0, 0) (3, 0))
    (.clash (3, 0) (3, 1))
private theorem check87 : check [state16, state17, state18, state19, state82, state86] state87 certificate87 = true := by
  decide +kernel
private theorem closed87 : Closed.{u} state87 :=
  sound (known := [state16, state17, state18, state19, state82, state86]) ⟨closed16.{u}, ⟨closed17.{u}, ⟨closed18.{u}, ⟨closed19.{u}, ⟨closed82.{u}, ⟨closed86.{u}, trivial⟩⟩⟩⟩⟩⟩ check87

private def state88 : Partition := #v[0, 1, 9, 3, 9, 5, 6, 0, 8, 9, 0, 5, 12, 0, 14, 9]
private def certificate88 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (1, 1))
    (.transversal ![1, 2, 0, 3]
      (.clash (1, 2) (3, 2))
      (.motif 0 2 1 0 1 2
        (.clash (1, 2) (3, 2)))
      (.clash (0, 1) (0, 2))
      (.transversal ![1, 2, 3, 0]
        (.clash (1, 2) (3, 2))
        (.clash (0, 1) (1, 1))
        (.clash (3, 0) (3, 2))
        (.clash (1, 1) (1, 2))
        (.clash (2, 0) (3, 0))
        (.motif 1 3 0 0 1 3
          (.clash (0, 3) (2, 3))))
      (.clash (0, 2) (1, 2))
      (.clash (1, 0) (2, 0)))
    (.clash (1, 0) (1, 1))
    (.clash (0, 2) (3, 2))
    (.motif 2 3 0 2 3 1
      (.clash (0, 1) (1, 1)))
private theorem check88 : check [] state88 certificate88 = true := by
  decide +kernel
private theorem closed88 : Closed.{u} state88 :=
  sound (known := []) trivial check88

private def state89 : Partition := #v[0, 1, 9, 3, 9, 5, 6, 7, 8, 9, 0, 5, 12, 0, 7, 9]
private def certificate89 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (1, 1))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 1) (0, 2))
      (.clash (1, 0) (2, 0))
      (.clash (0, 0) (0, 2))
      (.motif 0 2 1 0 1 2
        (.clash (1, 2) (1, 3)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 0) (2, 0)))
    (.clash (1, 0) (1, 1))
    (.clash (0, 2) (3, 2))
    (.clash (1, 1) (1, 3))
private theorem check89 : check [] state89 certificate89 = true := by
  decide +kernel
private theorem closed89 : Closed.{u} state89 :=
  sound (known := []) trivial check89

def state90 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 7, 8, 9, 0, 5, 12, 0, 14, 2]
private def certificate90 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (2, 2))
    (.clash (2, 1) (2, 2))
    (.clash (0, 0) (0, 2))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 1) (2, 1))
      (.transversal ![3, 2, 0, 1]
        (.transversal ![0, 3, 1, 2]
          (.motif 0 1 2 2 3 0
            (.clash (0, 1) (0, 3)))
          (.clash (0, 0) (0, 3))
          (.clash (2, 2) (3, 2))
          (.clash (0, 3) (1, 3))
          (.transversal ![1, 0, 3, 2]
            (.clash (0, 1) (0, 2))
            (.clash (0, 1) (1, 1))
            (.transversal ![2, 3, 1, 0]
              (.clash (0, 1) (0, 2))
              (.clash (0, 2) (0, 3))
              (.clash (1, 0) (3, 0))
              (.clash (0, 1) (0, 3))
              (.clash (2, 0) (3, 0))
              (.motif 1 3 0 2 3 0
                (.clash (0, 0) (0, 1))))
            (.clash (1, 0) (1, 1))
            (.clash (0, 2) (3, 2))
            (.clash (1, 1) (1, 3)))
          (.clash (1, 2) (3, 2)))
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (2, 1))
        (.clash (1, 2) (2, 2))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 1) (0, 2))
      (.clash (2, 0) (2, 1))
      (.clash (0, 2) (1, 2))
      (.clash (1, 0) (2, 0)))
    (.clash (0, 2) (1, 2))
    (.transversal ![0, 3, 1, 2]
      (.reuse 0)
      (.clash (0, 0) (0, 2))
      (.clash (2, 2) (3, 2))
      (.clash (1, 0) (1, 3))
      (.reuse 1)
      (.clash (0, 2) (3, 2)))
private theorem check90 : check [state88, state89] state90 certificate90 = true := by
  decide +kernel
private theorem closed90 : Closed.{u} state90 :=
  sound (known := [state88, state89]) ⟨closed88.{u}, ⟨closed89.{u}, trivial⟩⟩ check90

private def state91 : Partition := #v[0, 1, 2, 3, 4, 2, 3, 7, 7, 9, 0, 2, 12, 0, 7, 9]
private def certificate91 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (0, 3))
    (.motif 0 1 2 3 1 2
      (.clash (0, 0) (0, 1)))
    (.clash (0, 1) (2, 1))
    (.clash (0, 3) (1, 3))
    (.clash (0, 3) (3, 3))
    (.clash (1, 3) (3, 3))
private theorem check91 : check [] state91 certificate91 = true := by
  decide +kernel
private theorem closed91 : Closed.{u} state91 :=
  sound (known := []) trivial check91

private def state92 : Partition := #v[7, 1, 2, 3, 4, 2, 1, 7, 1, 4, 7, 2, 2, 7, 4, 1]
private def certificate92 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.clash (0, 2) (0, 3))
    (.clash (0, 1) (0, 3))
    (.columns)
    (.clash (0, 1) (0, 2))
    (.clash (0, 2) (3, 2))
    (.clash (0, 1) (2, 1))
private theorem check92 : check [] state92 certificate92 = true := by
  decide +kernel
private theorem closed92 : Closed.{u} state92 :=
  sound (known := []) trivial check92

private def state93 : Partition := #v[7, 1, 2, 3, 4, 2, 6, 7, 8, 9, 7, 2, 2, 7, 14, 9]
private def certificate93 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 2, 0, 3]
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (2, 0))
      (.clash (0, 1) (2, 1))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (1, 2))
        (.motif 0 3 1 1 0 2
          (.clash (0, 0) (2, 0)))
        (.clash (0, 0) (2, 0))
        (.clash (2, 2) (3, 2))
        (.clash (1, 2) (3, 2)))
      (.motif 1 2 0 2 3 1
        (.clash (0, 0) (0, 1)))
      (.clash (2, 0) (2, 1)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (1, 0))
    (.motif 1 3 0 0 1 3
      (.clash (0, 2) (0, 3)))
    (.clash (1, 3) (3, 3))
private theorem check93 : check [] state93 certificate93 = true := by
  decide +kernel
private theorem closed93 : Closed.{u} state93 :=
  sound (known := []) trivial check93

private def state94 : Partition := #v[7, 1, 2, 3, 4, 2, 6, 7, 8, 9, 7, 2, 9, 7, 14, 15]
private def certificate94 : Certificate :=
  .transversal ![2, 0, 1, 3]
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (2, 1))
    (.clash (2, 3) (3, 3))
    (.clash (1, 0) (3, 0))
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 2) (1, 3))
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (1, 0))
      (.motif 1 2 0 2 3 1
        (.clash (0, 0) (0, 1)))
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (3, 0)))
    (.clash (3, 0) (3, 3))
private theorem check94 : check [] state94 certificate94 = true := by
  decide +kernel
private theorem closed94 : Closed.{u} state94 :=
  sound (known := []) trivial check94

private def state95 : Partition := #v[7, 1, 2, 3, 4, 2, 6, 7, 8, 9, 7, 2, 12, 7, 14, 15]
private def certificate95 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.clash (0, 0) (0, 2))
    (.clash (1, 1) (2, 1))
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 2) (1, 3))
      (.clash (2, 1) (2, 2))
      (.clash (1, 3) (3, 3))
      (.motif 1 2 0 2 3 1
        (.clash (0, 0) (0, 1)))
      (.transversal ![1, 0, 2, 3]
        (.transversal ![2, 0, 1, 3]
          (.clash (0, 1) (0, 2))
          (.clash (1, 1) (2, 1))
          (.clash (0, 2) (1, 2))
          (.clash (0, 1) (2, 1))
          (.clash (1, 0) (1, 2))
          (.motif 1 2 0 2 3 1
            (.clash (0, 0) (0, 1))))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (1, 0) (1, 2))
          (.clash (0, 1) (0, 2))
          (.clash (1, 2) (3, 2))
          (.clash (1, 0) (1, 1))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 0) (0, 1))
            (.transversal ![2, 0, 1, 3]
              (.clash (0, 2) (3, 2))
              (.clash (1, 1) (2, 1))
              (.clash (0, 1) (0, 2))
              (.reuse 0)
              (.clash (1, 0) (1, 2))
              (.clash (0, 1) (2, 1)))
            (.clash (1, 0) (1, 2))
            (.clash (0, 0) (2, 0))
            (.clash (0, 0) (1, 0))
            (.clash (1, 0) (2, 0)))
          (.clash (0, 2) (3, 2)))
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 2))
        (.clash (1, 2) (1, 3)))
      (.reuse 1))
    (.clash (2, 1) (2, 2))
    (.clash (0, 0) (3, 0))
    (.reuse 2)
private theorem check95 : check [state92, state93, state94] state95 certificate95 = true := by
  decide +kernel
private theorem closed95 : Closed.{u} state95 :=
  sound (known := [state92, state93, state94]) ⟨closed92.{u}, ⟨closed93.{u}, ⟨closed94.{u}, trivial⟩⟩⟩ check95

def state96 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 8, 9, 0, 2, 12, 0, 14, 15]
private def certificate96 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (1, 1) (1, 3))
    (.clash (2, 0) (2, 3))
    (.clash (0, 0) (0, 2))
    (.transversal ![3, 2, 0, 1]
      (.transversal ![3, 1, 0, 2]
        (.clash (0, 2) (0, 3))
        (.clash (0, 3) (1, 3))
        (.clash (1, 2) (3, 2))
        (.clash (1, 1) (1, 3))
        (.clash (0, 2) (3, 2))
        (.transversal ![0, 2, 1, 3]
          (.clash (0, 0) (0, 3))
          (.clash (2, 1) (2, 2))
          (.clash (3, 1) (3, 3))
          (.transversal ![2, 0, 1, 3]
            (.clash (1, 0) (1, 1))
            (.clash (0, 2) (0, 3))
            (.clash (2, 3) (3, 3))
            (.clash (1, 0) (1, 2))
            (.transversal ![1, 0, 3, 2]
              (.transversal ![1, 3, 2, 0]
                (.clash (1, 0) (1, 3))
                (.clash (0, 0) (0, 1))
                (.clash (1, 0) (3, 0))
                (.clash (0, 0) (2, 0))
                (.clash (2, 0) (3, 0))
                (.clash (0, 0) (3, 0)))
              (.clash (0, 1) (0, 2))
              (.motif 0 1 2 3 1 2
                (.clash (0, 0) (0, 1)))
              (.clash (1, 0) (1, 1))
              (.clash (1, 0) (1, 3))
              (.clash (0, 2) (3, 2)))
            (.clash (0, 3) (3, 3)))
          (.clash (0, 3) (3, 3))
          (.reuse 0)))
      (.clash (0, 3) (1, 3))
      (.clash (0, 0) (0, 3))
      (.clash (1, 2) (1, 3))
      (.clash (1, 2) (2, 2))
      (.clash (0, 0) (2, 0)))
    (.reuse 1)
    (.clash (0, 0) (2, 0))
private theorem check96 : check [state91, state95] state96 certificate96 = true := by
  decide +kernel
private theorem closed96 : Closed.{u} state96 :=
  sound (known := [state91, state95]) ⟨closed91.{u}, ⟨closed95.{u}, trivial⟩⟩ check96

private def state97 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 1, 6, 4, 0, 2, 1, 6, 4, 0]
private def certificate97 : Certificate :=
  .transversal ![3, 1, 2, 0]
    (.clash (0, 2) (0, 3))
    (.clash (0, 0) (0, 3))
    (.clash (0, 1) (0, 3))
    (.clash (0, 0) (0, 2))
    (.clash (0, 1) (0, 2))
    (.clash (0, 0) (0, 1))
private theorem check97 : check [] state97 certificate97 = true := by
  decide +kernel
private theorem closed97 : Closed.{u} state97 :=
  sound (known := []) trivial check97

def state98 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 6, 9, 0, 2, 12, 6, 14, 0]
private def certificate98 : Certificate :=
  .transversal ![2, 0, 1, 3]
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (2, 1))
    (.clash (0, 0) (0, 2))
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 3) (3, 3))
      (.clash (0, 0) (1, 0))
      (.clash (2, 2) (3, 2))
      (.clash (1, 0) (1, 3))
      (.transversal ![1, 0, 3, 2]
        (.clash (0, 1) (2, 1))
        (.clash (0, 1) (0, 2))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (0, 2))
          (.clash (3, 0) (3, 2))
          (.clash (0, 2) (1, 2))
          (.clash (2, 0) (3, 0))
          (.transversal ![3, 1, 0, 2]
            (.clash (0, 2) (0, 3))
            (.motif 0 1 2 3 1 2
              (.clash (0, 0) (0, 1)))
            (.clash (0, 1) (0, 3))
            (.clash (0, 2) (1, 2))
            (.clash (0, 1) (0, 2))
            (.clash (0, 1) (3, 1))))
        (.clash (1, 0) (1, 1))
        (.clash (1, 0) (1, 3))
        (.clash (0, 2) (3, 2)))
      (.transversal ![1, 3, 0, 2]
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (0, 2))
          (.reuse 0)
          (.clash (0, 2) (1, 2))
          (.clash (2, 0) (3, 0))
          (.motif 1 3 0 2 0 1
            (.clash (0, 1) (2, 1))))
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (2, 1))
        (.clash (1, 2) (1, 3))
        (.clash (1, 0) (1, 3))
        (.clash (1, 0) (1, 2))))
    (.clash (0, 0) (1, 0))
    (.clash (2, 1) (2, 2))
private theorem check98 : check [state97] state98 certificate98 = true := by
  decide +kernel
private theorem closed98 : Closed.{u} state98 :=
  sound (known := [state97]) ⟨closed97.{u}, trivial⟩ check98

def state99 : Partition := #v[0, 1, 2, 3, 4, 5, 3, 0, 8, 4, 0, 5, 5, 3, 1, 4]
private def certificate99 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (0, 3))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 0) (0, 2))
      (.clash (0, 1) (0, 2))
      (.clash (0, 2) (0, 3))
      (.clash (0, 0) (0, 1))
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3)))
    (.clash (0, 1) (2, 1))
    (.motif 2 3 0 3 1 0
      (.clash (0, 0) (1, 0)))
    (.clash (0, 3) (3, 3))
    (.clash (1, 0) (2, 0))
private theorem check99 : check [] state99 certificate99 = true := by
  decide +kernel
private theorem closed99 : Closed.{u} state99 :=
  sound (known := []) trivial check99

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary05 : Known.{u} [state81, state87, state90, state96, state98, state99] :=
  ⟨closed81.{u}, ⟨closed87.{u}, ⟨closed90.{u}, ⟨closed96.{u}, ⟨closed98.{u}, ⟨closed99.{u}, trivial⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
