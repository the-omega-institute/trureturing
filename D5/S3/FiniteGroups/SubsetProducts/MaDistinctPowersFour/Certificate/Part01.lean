/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part01
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part01
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part01.certificate20
   digest: Order-four certificate decisions for chunks 0 through 20. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

def state0 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 2, 4, 1, 12, 4, 14, 0]
private def certificate0 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 1) (1, 3))
    (.clash (0, 0) (0, 2))
    (.clash (3, 2) (3, 3))
    (.transversal ![1, 3, 0, 2]
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
        (.clash (1, 0) (3, 0))))
    (.transversal ![1, 3, 2, 0]
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
      (.clash (1, 0) (3, 0)))
    (.clash (0, 2) (3, 2))
private theorem check0 : check [] state0 certificate0 = true := by
  decide +kernel
private theorem closed0 : Closed.{u} state0 :=
  sound (known := []) trivial check0

private def state1 : Partition := #v[10, 1, 2, 3, 4, 10, 1, 7, 7, 9, 10, 1, 1, 13, 9, 10]
private def certificate1 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.transversal ![2, 0, 1, 3]
      (.clash (1, 0) (1, 3))
      (.clash (0, 2) (3, 2))
      (.clash (0, 0) (0, 2))
      (.transversal ![2, 0, 3, 1]
        (.clash (0, 2) (3, 2))
        (.clash (0, 1) (0, 2))
        (.transversal ![3, 0, 2, 1]
          (.columns)
          (.clash (0, 0) (0, 3))
          (.clash (0, 2) (0, 3))
          (.clash (0, 0) (1, 0))
          (.clash (0, 2) (3, 2))
          (.clash (0, 0) (0, 2)))
        (.clash (0, 1) (2, 1))
        (.clash (2, 1) (3, 1))
        (.clash (0, 1) (3, 1)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 1) (2, 1)))
    (.clash (0, 2) (3, 2))
    (.clash (0, 1) (0, 2))
    (.clash (2, 0) (2, 1))
    (.clash (1, 2) (1, 3))
    (.clash (0, 1) (2, 1))
private theorem check1 : check [] state1 certificate1 = true := by
  decide +kernel
private theorem closed1 : Closed.{u} state1 :=
  sound (known := []) trivial check1

private def state2 : Partition := #v[10, 1, 2, 3, 4, 10, 1, 7, 8, 9, 10, 1, 7, 13, 14, 10]
private def certificate2 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (1, 2) (1, 3))
    (.clash (2, 0) (2, 3))
    (.clash (1, 2) (3, 2))
    (.clash (2, 0) (3, 0))
    (.clash (3, 0) (3, 2))
    (.transversal ![0, 3, 1, 2]
      (.clash (0, 0) (3, 0))
      (.clash (1, 1) (2, 1))
      (.clash (0, 0) (2, 0))
      (.motif 1 2 3 3 2 1
        (.clash (0, 1) (3, 1)))
      (.clash (2, 0) (3, 0))
      (.clash (2, 0) (2, 1)))
private theorem check2 : check [] state2 certificate2 = true := by
  decide +kernel
private theorem closed2 : Closed.{u} state2 :=
  sound (known := []) trivial check2

def state3 : Partition := #v[10, 1, 2, 3, 4, 10, 1, 7, 8, 9, 10, 1, 12, 13, 14, 10]
private def certificate3 : Certificate :=
  .transversal ![1, 3, 2, 0]
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
        (.transversal ![2, 0, 3, 1]
          (.motif 0 1 2 2 1 0
            (.clash (2, 0) (2, 3)))
          (.clash (0, 1) (0, 2))
          (.clash (2, 1) (3, 1))
          (.clash (1, 0) (1, 2))
          (.transversal ![2, 3, 0, 1]
            (.clash (0, 2) (3, 2))
            (.clash (2, 0) (2, 1))
            (.clash (2, 1) (3, 1))
            (.motif 2 3 0 0 3 2
              (.clash (0, 1) (0, 2)))
            (.clash (1, 0) (1, 3))
            (.clash (1, 0) (2, 0)))
          (.clash (0, 1) (3, 1)))
        (.clash (0, 1) (0, 2))
        (.motif 1 2 0 1 3 2
          (.clash (0, 2) (3, 2)))
        (.clash (1, 2) (1, 3))
        (.clash (0, 1) (2, 1)))
      (.transversal ![1, 3, 0, 2]
        (.clash (1, 2) (1, 3))
        (.clash (2, 0) (2, 3))
        (.clash (0, 1) (2, 1))
        (.reuse 0)
        (.motif 1 2 0 1 3 2
          (.clash (0, 2) (3, 2)))
        (.clash (2, 0) (2, 1))))
    (.clash (1, 1) (1, 3))
    (.reuse 1)
    (.clash (0, 0) (3, 0))
private theorem check3 : check [state1, state2] state3 certificate3 = true := by
  decide +kernel
private theorem closed3 : Closed.{u} state3 :=
  sound (known := [state1, state2]) ⟨closed1.{u}, ⟨closed2.{u}, trivial⟩⟩ check3

private def state4 : Partition := #v[10, 1, 2, 3, 3, 10, 6, 7, 1, 9, 10, 6, 12, 13, 3, 10]
private def certificate4 : Certificate :=
  .transversal ![3, 2, 0, 1]
    (.clash (0, 3) (2, 3))
    (.clash (0, 1) (0, 3))
    (.clash (3, 1) (3, 2))
    (.clash (2, 0) (2, 3))
    (.transversal ![2, 1, 3, 0]
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (1, 2))
      (.motif 0 3 2 2 3 0
        (.clash (0, 1) (0, 3)))
      (.clash (1, 1) (1, 2))
      (.clash (0, 0) (3, 0))
      (.clash (3, 0) (3, 1)))
    (.clash (0, 1) (3, 1))
private theorem check4 : check [] state4 certificate4 = true := by
  decide +kernel
private theorem closed4 : Closed.{u} state4 :=
  sound (known := []) trivial check4

private def state5 : Partition := #v[10, 1, 2, 3, 4, 10, 6, 7, 1, 9, 10, 6, 12, 13, 14, 10]
private def certificate5 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (1, 0) (2, 0))
    (.clash (2, 0) (2, 3))
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 1) (1, 3))
      (.clash (1, 1) (2, 1))
      (.clash (0, 0) (0, 1))
      (.motif 2 1 3 3 1 2
        (.clash (0, 1) (2, 1)))
      (.transversal ![2, 1, 3, 0]
        (.clash (0, 0) (0, 2))
        (.clash (0, 2) (1, 2))
        (.transversal ![2, 0, 1, 3]
          (.clash (1, 0) (3, 0))
          (.motif 0 2 1 1 2 0
            (.clash (1, 0) (3, 0)))
          (.clash (0, 0) (0, 2))
          (.transversal ![2, 0, 3, 1]
            (.clash (1, 0) (3, 0))
            (.clash (0, 2) (1, 2))
            (.clash (3, 0) (3, 1))
            (.clash (1, 0) (1, 2))
            (.clash (2, 1) (3, 1))
            (.motif 1 3 0 1 2 3
              (.clash (0, 3) (2, 3))))
          (.clash (0, 0) (1, 0))
          (.clash (1, 1) (2, 1)))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (3, 0))
        (.motif 2 3 0 0 3 2
          (.clash (0, 2) (1, 2))))
      (.clash (0, 1) (2, 1)))
    (.clash (1, 0) (1, 2))
    (.transversal ![3, 1, 0, 2]
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3))
      (.reuse 0)
      (.clash (0, 0) (0, 1))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (2, 0)))
    (.clash (1, 2) (3, 2))
private theorem check5 : check [state4] state5 certificate5 = true := by
  decide +kernel
private theorem closed5 : Closed.{u} state5 :=
  sound (known := [state4]) ⟨closed4.{u}, trivial⟩ check5

def state6 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 1, 9, 10, 6, 12, 13, 14, 0]
private def certificate6 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (2, 0))
    (.clash (2, 0) (2, 2))
    (.clash (0, 0) (0, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (2, 0))
      (.clash (2, 0) (2, 3))
      (.transversal ![2, 0, 1, 3]
        (.clash (0, 2) (2, 2))
        (.transversal ![3, 0, 1, 2]
          (.transversal ![0, 3, 1, 2]
            (.clash (1, 1) (1, 3))
            (.clash (0, 0) (0, 2))
            (.clash (0, 0) (0, 1))
            (.transversal ![0, 3, 2, 1]
              (.clash (0, 0) (0, 2))
              (.clash (0, 0) (0, 3))
              (.clash (1, 1) (3, 1))
              (.clash (0, 2) (0, 3))
              (.clash (2, 1) (3, 1))
              (.transversal ![1, 3, 2, 0]
                (.clash (0, 1) (0, 2))
                (.clash (0, 1) (0, 3))
                (.clash (2, 0) (3, 0))
                (.clash (0, 2) (0, 3))
                (.motif 1 3 0 0 3 1
                  (.clash (0, 1) (0, 2)))
                (.clash (1, 0) (3, 0))))
            (.motif 0 1 2 0 3 1
              (.clash (0, 2) (0, 3)))
            (.clash (0, 1) (0, 2)))
          (.clash (0, 2) (0, 3))
          (.clash (0, 1) (0, 3))
          (.clash (0, 2) (2, 2))
          (.clash (1, 0) (2, 0))
          (.clash (0, 1) (0, 2)))
        (.clash (0, 0) (0, 2))
        (.clash (2, 1) (2, 2))
        (.clash (0, 0) (1, 0))
        (.clash (1, 1) (2, 1)))
      (.clash (1, 0) (1, 2))
      (.clash (2, 2) (3, 2))
      (.clash (1, 2) (3, 2)))
    (.clash (0, 0) (1, 0))
    (.reuse 0)
private theorem check6 : check [state5] state6 certificate6 = true := by
  decide +kernel
private theorem closed6 : Closed.{u} state6 :=
  sound (known := [state5]) ⟨closed5.{u}, trivial⟩ check6

def state7 : Partition := #v[0, 1, 2, 3, 3, 0, 6, 7, 1, 9, 0, 6, 2, 6, 3, 0]
private def certificate7 : Certificate :=
  .motif 0 3 2 2 3 0
    (.clash (0, 1) (0, 3))
private theorem check7 : check [] state7 certificate7 = true := by
  decide +kernel
private theorem closed7 : Closed.{u} state7 :=
  sound (known := []) trivial check7

def state8 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 1, 9, 0, 11, 11, 6, 14, 0]
private def certificate8 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.transversal ![0, 3, 1, 2]
      (.clash (0, 0) (0, 1))
      (.clash (1, 1) (2, 1))
      (.clash (2, 2) (3, 2))
      (.clash (0, 1) (2, 1))
      (.motif 1 3 2 2 3 1
        (.clash (0, 1) (2, 1)))
      (.transversal ![1, 0, 3, 2]
        (.clash (1, 0) (1, 3))
        (.clash (1, 3) (2, 3))
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (3, 0))
        (.transversal ![2, 0, 3, 1]
          (.clash (0, 2) (3, 2))
          (.transversal ![3, 1, 0, 2]
            (.clash (0, 0) (0, 3))
            (.clash (0, 1) (0, 3))
            (.motif 0 1 2 1 0 3
              (.clash (0, 0) (0, 2)))
            (.clash (0, 0) (0, 1))
            (.clash (0, 0) (1, 0))
            (.clash (0, 1) (2, 1)))
          (.clash (0, 2) (1, 2))
          (.clash (1, 0) (3, 0))
          (.clash (1, 0) (1, 2))
          (.clash (3, 0) (3, 1)))
        (.clash (2, 1) (2, 3))))
    (.clash (0, 0) (0, 1))
    (.clash (2, 0) (2, 3))
    (.clash (1, 1) (1, 3))
    (.clash (1, 3) (2, 3))
    (.clash (0, 0) (3, 0))
private theorem check8 : check [] state8 certificate8 = true := by
  decide +kernel
private theorem closed8 : Closed.{u} state8 :=
  sound (known := []) trivial check8

private def state9 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 7, 3, 7, 0, 1, 7, 3, 1, 0]
private def certificate9 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 0) (0, 2))
    (.clash (0, 1) (0, 2))
    (.transversal ![2, 0, 3, 1]
      (.clash (1, 0) (1, 3))
      (.clash (0, 1) (0, 2))
      (.clash (0, 2) (0, 3))
      (.columns)
      (.clash (1, 0) (1, 2))
      (.clash (0, 1) (0, 3)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 0) (3, 0))
    (.clash (0, 1) (2, 1))
private theorem check9 : check [] state9 certificate9 = true := by
  decide +kernel
private theorem closed9 : Closed.{u} state9 :=
  sound (known := []) trivial check9

private def state10 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 7, 3, 9, 0, 11, 12, 3, 7, 0]
private def certificate10 : Certificate :=
  .motif 1 3 0 3 1 2
    (.clash (0, 0) (0, 2))
private theorem check10 : check [] state10 certificate10 = true := by
  decide +kernel
private theorem closed10 : Closed.{u} state10 :=
  sound (known := []) trivial check10

private def state11 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 7, 3, 9, 0, 11, 12, 3, 9, 0]
private def certificate11 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 3))
      (.clash (1, 3) (2, 3))
      (.clash (0, 1) (2, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (0, 3))
        (.clash (1, 0) (1, 3))
        (.motif 0 3 1 1 3 0
          (.clash (0, 3) (2, 3)))
        (.clash (0, 3) (2, 3))
        (.clash (2, 0) (3, 0))
        (.clash (1, 0) (3, 0)))
      (.motif 1 2 0 0 2 1
        (.clash (0, 1) (0, 3)))
      (.clash (2, 1) (2, 3)))
    (.clash (0, 1) (0, 3))
    (.clash (0, 1) (2, 1))
    (.clash (0, 3) (1, 3))
    (.motif 1 3 0 3 1 2
      (.clash (0, 0) (0, 2)))
    (.clash (1, 2) (3, 2))
private theorem check11 : check [] state11 certificate11 = true := by
  decide +kernel
private theorem closed11 : Closed.{u} state11 :=
  sound (known := []) trivial check11

def state12 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 6, 9, 0, 11, 12, 6, 14, 0]
private def certificate12 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.transversal ![2, 0, 3, 1]
      (.clash (0, 2) (0, 3))
      (.transversal ![2, 0, 1, 3]
        (.clash (0, 2) (0, 3))
        (.clash (2, 1) (2, 3))
        (.clash (0, 0) (0, 2))
        (.motif 1 2 0 0 2 1
          (.clash (0, 1) (3, 1)))
        (.clash (0, 0) (0, 3))
        (.clash (1, 1) (2, 1)))
      (.clash (0, 2) (1, 2))
      (.clash (0, 3) (2, 3))
      (.clash (1, 0) (1, 2))
      (.clash (2, 0) (2, 3)))
    (.clash (0, 0) (0, 3))
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 1) (1, 3))
      (.clash (1, 1) (2, 1))
      (.clash (2, 2) (3, 2))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.clash (0, 1) (0, 3))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.clash (3, 0) (3, 2))
          (.clash (1, 1) (1, 3))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (0, 3))
            (.reuse 0)
            (.clash (0, 1) (2, 1))
            (.clash (0, 3) (2, 3))
            (.clash (0, 3) (1, 3))
            (.clash (1, 3) (2, 3)))
          (.clash (0, 0) (3, 0)))
        (.clash (0, 3) (1, 3))
        (.motif 1 3 0 3 1 2
          (.clash (0, 0) (0, 2)))
        (.clash (1, 2) (3, 2)))
      (.reuse 1)
      (.reuse 2))
    (.clash (0, 0) (1, 0))
    (.clash (1, 0) (1, 2))
    (.clash (0, 0) (2, 0))
private theorem check12 : check [state9, state10, state11] state12 certificate12 = true := by
  decide +kernel
private theorem closed12 : Closed.{u} state12 :=
  sound (known := [state9, state10, state11]) ⟨closed9.{u}, ⟨closed10.{u}, ⟨closed11.{u}, trivial⟩⟩⟩ check12

private def state13 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 1, 6, 4, 1, 2, 12, 6, 4, 0]
private def certificate13 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (0, 2))
    (.motif 2 3 0 1 0 2
      (.clash (0, 2) (1, 2)))
    (.clash (0, 2) (1, 2))
    (.clash (2, 0) (3, 0))
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3))
      (.clash (0, 2) (0, 3))
      (.clash (0, 0) (0, 1))
      (.clash (0, 0) (0, 2))
      (.clash (0, 1) (0, 2)))
private theorem check13 : check [] state13 certificate13 = true := by
  decide +kernel
private theorem closed13 : Closed.{u} state13 :=
  sound (known := []) trivial check13

private def state14 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 7, 11, 12, 6, 14, 0]
private def certificate14 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
    (.clash (3, 2) (3, 3))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (3, 2))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 3, 0, 2]
        (.clash (1, 0) (1, 3))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 1) (2, 2))
        (.clash (2, 0) (2, 1)))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 2))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (1, 0) (1, 3))
          (.clash (1, 3) (2, 3))
          (.clash (0, 1) (2, 1))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (3, 1))
            (.clash (1, 0) (1, 3))
            (.motif 1 2 3 0 2 3
              (.clash (0, 0) (2, 0)))
            (.clash (1, 0) (1, 2))
            (.clash (2, 0) (3, 0))
            (.clash (1, 0) (3, 0)))
          (.transversal ![2, 0, 3, 1]
            (.clash (0, 2) (3, 2))
            (.reuse 0)
            (.clash (0, 2) (1, 2))
            (.clash (2, 1) (2, 3))
            (.clash (1, 0) (1, 2))
            (.clash (2, 0) (2, 3)))
          (.clash (2, 1) (2, 3)))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (2, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (1, 3))
      (.clash (0, 0) (1, 0))
      (.clash (1, 1) (1, 3)))
private theorem check14 : check [state13] state14 certificate14 = true := by
  decide +kernel
private theorem closed14 : Closed.{u} state14 :=
  sound (known := [state13]) ⟨closed13.{u}, trivial⟩ check14

def state15 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 11, 12, 6, 14, 0]
private def certificate15 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 1) (1, 3))
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
    (.clash (1, 1) (1, 2))
    (.reuse 3)
    (.clash (1, 2) (1, 3))
    (.clash (1, 2) (2, 2))
private theorem check15 : check [state7, state8, state12, state14] state15 certificate15 = true := by
  decide +kernel
private theorem closed15 : Closed.{u} state15 :=
  sound (known := [state7, state8, state12, state14]) ⟨closed7.{u}, ⟨closed8.{u}, ⟨closed12.{u}, ⟨closed14.{u}, trivial⟩⟩⟩⟩ check15

def state16 : Partition := #v[0, 1, 2, 3, 2, 0, 6, 7, 8, 7, 0, 2, 7, 2, 14, 0]
private def certificate16 : Certificate :=
  .motif 1 3 0 0 3 1
    (.clash (0, 1) (2, 1))
private theorem check16 : check [] state16 certificate16 = true := by
  decide +kernel
private theorem closed16 : Closed.{u} state16 :=
  sound (known := []) trivial check16

def state17 : Partition := #v[0, 1, 2, 3, 2, 0, 6, 7, 8, 9, 0, 2, 12, 2, 7, 0]
private def certificate17 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.transversal ![1, 2, 3, 0]
      (.clash (1, 2) (1, 3))
      (.clash (0, 1) (0, 2))
      (.clash (3, 0) (3, 2))
      (.clash (0, 2) (1, 2))
      (.transversal ![1, 2, 0, 3]
        (.clash (1, 2) (1, 3))
        (.transversal ![2, 3, 1, 0]
          (.clash (0, 1) (0, 2))
          (.clash (2, 1) (2, 3))
          (.clash (0, 2) (1, 2))
          (.clash (0, 1) (2, 1))
          (.clash (1, 2) (1, 3))
          (.transversal ![3, 0, 1, 2]
            (.clash (0, 2) (0, 3))
            (.columns)
            (.clash (0, 1) (0, 3))
            (.clash (0, 2) (1, 2))
            (.clash (0, 1) (0, 2))
            (.clash (0, 1) (2, 1))))
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (3, 0))
        (.clash (0, 0) (3, 0))
        (.clash (0, 0) (2, 0)))
      (.clash (1, 0) (3, 0)))
    (.clash (0, 0) (0, 1))
    (.transversal ![2, 3, 1, 0]
      (.clash (0, 2) (3, 2))
      (.clash (2, 1) (2, 3))
      (.clash (0, 1) (0, 2))
      (.motif 2 3 0 2 1 3
        (.clash (0, 3) (1, 3)))
      (.clash (3, 0) (3, 2))
      (.clash (0, 1) (2, 1)))
    (.clash (1, 1) (1, 3))
    (.clash (3, 0) (3, 2))
    (.clash (0, 0) (3, 0))
private theorem check17 : check [] state17 certificate17 = true := by
  decide +kernel
private theorem closed17 : Closed.{u} state17 :=
  sound (known := []) trivial check17

def state18 : Partition := #v[0, 1, 2, 3, 2, 0, 6, 7, 8, 9, 0, 2, 12, 2, 9, 0]
private def certificate18 : Certificate :=
  .motif 2 3 1 1 3 2
    (.clash (0, 2) (1, 2))
private theorem check18 : check [] state18 certificate18 = true := by
  decide +kernel
private theorem closed18 : Closed.{u} state18 :=
  sound (known := []) trivial check18

def state19 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 4, 0, 2, 12, 2, 14, 0]
private def certificate19 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.clash (1, 3) (2, 3))
    (.clash (2, 1) (2, 3))
    (.clash (3, 0) (3, 1))
    (.clash (1, 0) (1, 3))
    (.transversal ![0, 3, 1, 2]
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (1, 0))
      (.clash (2, 2) (3, 2))
      (.clash (1, 0) (1, 3))
      (.clash (3, 0) (3, 2))
      (.motif 2 3 1 1 3 2
        (.clash (0, 2) (1, 2))))
    (.clash (1, 0) (3, 0))
private theorem check19 : check [] state19 certificate19 = true := by
  decide +kernel
private theorem closed19 : Closed.{u} state19 :=
  sound (known := []) trivial check19

def state20 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 1, 9, 0, 6, 2, 6, 14, 0]
private def certificate20 : Certificate :=
  .transversal ![3, 0, 2, 1]
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
    (.clash (0, 0) (0, 3))
    (.clash (0, 3) (2, 3))
    (.clash (0, 0) (1, 0))
    (.clash (1, 0) (1, 2))
    (.clash (1, 1) (1, 2))
private theorem check20 : check [] state20 certificate20 = true := by
  decide +kernel
private theorem closed20 : Closed.{u} state20 :=
  sound (known := []) trivial check20

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary01 : Known.{u} [state0, state3, state6, state7, state8, state12, state15, state16, state17, state18, state19, state20] :=
  ⟨closed0.{u}, ⟨closed3.{u}, ⟨closed6.{u}, ⟨closed7.{u}, ⟨closed8.{u}, ⟨closed12.{u}, ⟨closed15.{u}, ⟨closed16.{u}, ⟨closed17.{u}, ⟨closed18.{u}, ⟨closed19.{u}, ⟨closed20.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
