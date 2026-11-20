/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part03
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part03
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 42 through 63. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part02

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed39 : Closed.{u} state39 :=
  known_of_mem boundary02.{u} (by decide)

private theorem closed40 : Closed.{u} state40 :=
  known_of_mem boundary02.{u} (by decide)

private theorem closed41 : Closed.{u} state41 :=
  known_of_mem boundary02.{u} (by decide)

private def state42 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 7, 9, 10, 0, 12, 13, 0, 1]
private def certificate42 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (1, 2) (1, 3))
    (.clash (1, 2) (2, 2))
    (.clash (3, 0) (3, 3))
    (.clash (2, 0) (2, 2))
    (.clash (2, 0) (3, 0))
    (.transversal ![0, 3, 2, 1]
      (.clash (0, 0) (2, 0))
      (.clash (0, 0) (3, 0))
      (.clash (1, 1) (3, 1))
      (.clash (2, 0) (2, 2))
      (.motif 1 3 2 3 2 1
        (.clash (0, 1) (2, 1)))
      (.clash (3, 0) (3, 1)))
private theorem check42 : check [] state42 certificate42 = true := by
  decide +kernel
private theorem closed42 : Closed.{u} state42 :=
  sound (known := []) trivial check42

private def state43 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 9, 10, 0, 12, 13, 0, 1]
private def certificate43 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (1, 2) (1, 3))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 1) (1, 3))
      (.clash (2, 2) (2, 3))
      (.clash (1, 1) (3, 1))
      (.transversal ![2, 3, 0, 1]
        (.clash (0, 2) (2, 2))
        (.clash (0, 1) (0, 2))
        (.transversal ![2, 0, 1, 3]
          (.motif 0 1 2 0 2 1
            (.clash (2, 1) (3, 1)))
          (.clash (2, 1) (3, 1))
          (.clash (0, 1) (0, 2))
          (.transversal ![2, 3, 1, 0]
            (.clash (0, 2) (2, 2))
            (.clash (2, 1) (3, 1))
            (.clash (3, 0) (3, 1))
            (.clash (1, 0) (1, 3))
            (.motif 2 3 0 0 2 3
              (.clash (0, 3) (1, 3)))
            (.clash (1, 0) (3, 0)))
          (.clash (1, 0) (1, 2))
          (.clash (0, 1) (2, 1)))
        (.clash (1, 2) (1, 3))
        (.motif 1 3 0 1 3 2
          (.clash (0, 2) (2, 2)))
        (.clash (0, 1) (3, 1)))
      (.motif 1 3 2 3 2 1
        (.clash (0, 1) (2, 1)))
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 2) (1, 3))
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (3, 0))
        (.motif 1 3 0 1 3 2
          (.clash (0, 2) (2, 2)))
        (.reuse 0)
        (.clash (3, 0) (3, 1))))
    (.clash (0, 0) (0, 1))
    (.reuse 1)
    (.clash (1, 1) (1, 3))
    (.clash (0, 0) (2, 0))
private theorem check43 : check [state41, state42] state43 certificate43 = true := by
  decide +kernel
private theorem closed43 : Closed.{u} state43 :=
  sound (known := [state41, state42]) ⟨closed41.{u}, ⟨closed42.{u}, trivial⟩⟩ check43

private def state44 : Partition := #v[0, 7, 2, 3, 4, 0, 6, 7, 8, 9, 7, 0, 7, 13, 9, 6]
private def certificate44 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (1, 0) (1, 3))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (1, 0))
    (.motif 1 3 2 2 0 3
      (.clash (0, 0) (1, 0)))
    (.clash (1, 1) (2, 1))
private theorem check44 : check [] state44 certificate44 = true := by
  decide +kernel
private theorem closed44 : Closed.{u} state44 :=
  sound (known := []) trivial check44

private def state45 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 1, 0, 1, 7, 14, 6]
private def certificate45 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.transversal ![2, 0, 3, 1]
      (.clash (0, 2) (0, 3))
      (.clash (0, 0) (0, 2))
      (.transversal ![0, 3, 1, 2]
        (.clash (0, 0) (0, 2))
        (.clash (1, 1) (2, 1))
        (.motif 0 3 1 1 2 0
          (.clash (0, 2) (0, 3)))
        (.clash (2, 1) (3, 1))
        (.clash (0, 2) (3, 2))
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (0, 3))
          (.clash (0, 0) (0, 1))
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 3))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (0, 2))
            (.clash (2, 0) (2, 2))
            (.clash (0, 1) (0, 3))
            (.motif 1 2 0 0 3 1
              (.clash (0, 1) (0, 2)))
            (.clash (0, 2) (0, 3))
            (.clash (1, 0) (2, 0)))
          (.clash (1, 1) (2, 1))))
      (.clash (0, 0) (0, 3))
      (.clash (0, 3) (1, 3))
      (.clash (1, 1) (1, 3)))
    (.clash (0, 1) (0, 3))
    (.clash (0, 3) (1, 3))
    (.clash (1, 0) (3, 0))
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (3, 1))
private theorem check45 : check [] state45 certificate45 = true := by
  decide +kernel
private theorem closed45 : Closed.{u} state45 :=
  sound (known := []) trivial check45

private def state46 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 4, 0, 1, 13, 14, 6]
private def certificate46 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (1, 0) (3, 0))
    (.clash (0, 0) (0, 1))
    (.clash (3, 0) (3, 2))
    (.clash (0, 0) (1, 0))
    (.clash (2, 2) (3, 2))
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 0) (0, 3))
      (.transversal ![3, 2, 1, 0]
        (.clash (0, 3) (3, 3))
        (.clash (2, 1) (2, 2))
        (.clash (0, 1) (0, 3))
        (.transversal ![2, 1, 0, 3]
          (.clash (0, 0) (0, 2))
          (.motif 0 2 3 2 3 0
            (.clash (0, 1) (0, 3)))
          (.clash (0, 2) (1, 2))
          (.clash (0, 0) (2, 0))
          (.clash (1, 1) (1, 2))
          (.clash (2, 0) (2, 1)))
        (.clash (3, 0) (3, 3))
        (.clash (0, 1) (2, 1)))
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (1, 0))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (3, 0)))
private theorem check46 : check [] state46 certificate46 = true := by
  decide +kernel
private theorem closed46 : Closed.{u} state46 :=
  sound (known := []) trivial check46

private def state47 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 0, 1, 13, 14, 6]
private def certificate47 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (3, 0))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 1) (1, 3))
      (.clash (0, 0) (0, 1))
      (.clash (1, 1) (3, 1))
      (.transversal ![0, 3, 1, 2]
        (.clash (0, 0) (0, 1))
        (.clash (1, 1) (2, 1))
        (.transversal ![2, 1, 0, 3]
          (.clash (0, 0) (0, 2))
          (.transversal ![2, 0, 1, 3]
            (.clash (1, 0) (2, 0))
            (.clash (2, 0) (2, 1))
            (.clash (0, 2) (1, 2))
            (.transversal ![2, 0, 3, 1]
              (.clash (1, 0) (2, 0))
              (.clash (0, 0) (0, 2))
              (.motif 0 3 1 1 2 0
                (.clash (1, 0) (2, 0)))
              (.clash (0, 0) (1, 0))
              (.clash (2, 1) (3, 1))
              (.clash (1, 1) (3, 1)))
            (.clash (1, 0) (1, 2))
            (.motif 1 2 0 1 2 3
              (.clash (0, 3) (3, 3))))
          (.clash (0, 2) (1, 2))
          (.clash (0, 0) (2, 0))
          (.clash (1, 1) (1, 2))
          (.motif 2 3 0 0 2 3
            (.clash (0, 1) (0, 3))))
        (.clash (0, 1) (2, 1))
        (.clash (2, 2) (3, 2))
        (.reuse 0))
      (.reuse 1)
      (.clash (0, 1) (3, 1)))
    (.clash (3, 0) (3, 3))
    (.reuse 2)
    (.clash (1, 0) (1, 2))
    (.clash (1, 2) (2, 2))
private theorem check47 : check [state44, state45, state46] state47 certificate47 = true := by
  decide +kernel
private theorem closed47 : Closed.{u} state47 :=
  sound (known := [state44, state45, state46]) ⟨closed44.{u}, ⟨closed45.{u}, ⟨closed46.{u}, trivial⟩⟩⟩ check47

private def state48 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 7, 0, 4, 7, 4, 3, 1]
private def certificate48 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (2, 1))
    (.motif 2 3 0 1 3 0
      (.clash (0, 0) (1, 0)))
    (.clash (0, 1) (0, 3))
    (.clash (2, 0) (2, 1))
    (.clash (0, 3) (1, 3))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (0, 3))
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (0, 3))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (0, 3)))
private theorem check48 : check [] state48 certificate48 = true := by
  decide +kernel
private theorem closed48 : Closed.{u} state48 :=
  sound (known := []) trivial check48

private def state49 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 7, 0, 11, 7, 11, 4, 1]
private def certificate49 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (2, 1))
    (.motif 1 3 2 0 3 2
      (.clash (0, 0) (3, 0)))
    (.clash (1, 0) (1, 2))
    (.clash (2, 0) (2, 1))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (2, 0))
private theorem check49 : check [] state49 certificate49 = true := by
  decide +kernel
private theorem closed49 : Closed.{u} state49 :=
  sound (known := []) trivial check49

private def state50 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 9, 0, 11, 7, 11, 9, 1]
private def certificate50 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (1, 2) (1, 3))
    (.transversal ![3, 1, 0, 2]
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3))
      (.transversal ![1, 0, 3, 2]
        (.clash (1, 0) (1, 2))
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (0, 3))
        (.transversal ![2, 0, 1, 3]
          (.motif 0 1 2 0 2 1
            (.clash (0, 2) (0, 3)))
          (.clash (0, 2) (0, 3))
          (.clash (0, 1) (0, 2))
          (.clash (0, 3) (2, 3))
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (0, 3)))
        (.motif 1 2 0 1 0 2
          (.clash (0, 2) (0, 3)))
        (.clash (0, 3) (2, 3)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 1) (2, 1))
      (.clash (0, 1) (2, 1)))
    (.clash (0, 1) (2, 1))
    (.clash (2, 0) (3, 0))
    (.clash (3, 0) (3, 2))
    (.clash (2, 0) (2, 1))
private theorem check50 : check [] state50 certificate50 = true := by
  decide +kernel
private theorem closed50 : Closed.{u} state50 :=
  sound (known := []) trivial check50

private def state51 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 9, 7, 11, 12, 11, 9, 1]
private def certificate51 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (1, 2) (1, 3))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 2) (2, 2))
      (.clash (0, 1) (0, 2))
      (.transversal ![2, 3, 1, 0]
        (.clash (0, 2) (2, 2))
        (.clash (0, 2) (3, 2))
        (.clash (3, 0) (3, 1))
        (.clash (2, 1) (2, 2))
        (.transversal ![3, 1, 0, 2]
          (.clash (0, 0) (0, 3))
          (.clash (0, 1) (0, 3))
          (.motif 0 3 1 2 3 1
            (.clash (0, 0) (0, 3)))
          (.clash (0, 0) (0, 1))
          (.clash (1, 1) (2, 1))
          (.clash (0, 1) (2, 1)))
        (.clash (3, 0) (3, 2)))
      (.clash (1, 2) (1, 3))
      (.clash (1, 3) (2, 3))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 1) (2, 1))
    (.clash (2, 0) (2, 2))
    (.clash (2, 1) (2, 2))
    (.clash (2, 0) (2, 1))
private theorem check51 : check [] state51 certificate51 = true := by
  decide +kernel
private theorem closed51 : Closed.{u} state51 :=
  sound (known := []) trivial check51

private def state52 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 7, 11, 1, 11, 9, 6]
private def certificate52 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (3, 0))
    (.transversal ![2, 1, 3, 0]
      (.clash (0, 0) (0, 2))
      (.transversal ![2, 1, 0, 3]
        (.clash (0, 0) (0, 2))
        (.clash (2, 0) (2, 3))
        (.clash (0, 2) (1, 2))
        (.clash (0, 0) (2, 0))
        (.clash (1, 1) (1, 2))
        (.transversal ![3, 1, 0, 2]
          (.clash (0, 0) (0, 3))
          (.clash (0, 3) (3, 3))
          (.motif 0 2 1 3 2 1
            (.clash (0, 0) (0, 2)))
          (.clash (0, 0) (2, 0))
          (.clash (1, 1) (2, 1))
          (.clash (1, 2) (3, 2))))
      (.clash (0, 1) (0, 2))
      (.clash (1, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (3, 1)))
    (.clash (3, 0) (3, 3))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (1, 2))
    (.clash (1, 2) (1, 3))
private theorem check52 : check [] state52 certificate52 = true := by
  decide +kernel
private theorem closed52 : Closed.{u} state52 :=
  sound (known := []) trivial check52

private def state53 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 7, 11, 12, 11, 14, 6]
private def certificate53 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 2, 3, 0]
        (.clash (1, 0) (1, 2))
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (3, 0))
        (.clash (2, 3) (3, 3))
        (.clash (3, 0) (3, 3))
        (.clash (3, 0) (3, 1)))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.transversal ![3, 0, 1, 2]
        (.clash (0, 3) (2, 3))
        (.transversal ![2, 0, 1, 3]
          (.transversal ![2, 1, 0, 3]
            (.clash (0, 0) (0, 2))
            (.clash (1, 0) (2, 0))
            (.clash (0, 2) (1, 2))
            (.clash (0, 0) (2, 0))
            (.clash (1, 1) (1, 2))
            (.motif 1 2 0 2 3 0
              (.clash (1, 1) (1, 3))))
          (.clash (0, 2) (0, 3))
          (.clash (0, 2) (1, 2))
          (.clash (0, 3) (2, 3))
          (.clash (1, 0) (1, 2))
          (.clash (0, 3) (3, 3)))
        (.clash (0, 0) (0, 3))
        (.clash (2, 1) (2, 3))
        (.clash (0, 0) (1, 0))
        (.clash (1, 1) (2, 1)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 1) (3, 1)))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (3, 2))
    (.transversal ![1, 2, 3, 0]
      (.reuse 0)
      (.clash (0, 1) (3, 1))
      (.reuse 1)
      (.clash (2, 3) (3, 3))
      (.clash (3, 0) (3, 3))
      (.clash (3, 0) (3, 1)))
private theorem check53 : check [state51, state52] state53 certificate53 = true := by
  decide +kernel
private theorem closed53 : Closed.{u} state53 :=
  sound (known := [state51, state52]) ⟨closed51.{u}, ⟨closed52.{u}, trivial⟩⟩ check53

private def state54 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 11, 12, 11, 14, 6]
private def certificate54 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 1) (1, 3))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 2, 3, 0]
        (.clash (1, 0) (1, 2))
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (3, 0))
        (.clash (2, 3) (3, 3))
        (.clash (3, 0) (3, 3))
        (.clash (3, 0) (3, 1)))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 2) (1, 3))
        (.clash (0, 0) (0, 1))
        (.clash (3, 0) (3, 3))
        (.clash (1, 1) (1, 3))
        (.transversal ![0, 3, 1, 2]
          (.clash (0, 0) (3, 0))
          (.clash (1, 1) (2, 1))
          (.clash (2, 2) (3, 2))
          (.transversal ![1, 0, 3, 2]
            (.clash (1, 0) (1, 2))
            (.clash (0, 1) (3, 1))
            (.clash (1, 2) (3, 2))
            (.transversal ![3, 0, 1, 2]
              (.clash (0, 3) (2, 3))
              (.clash (0, 3) (1, 3))
              (.reuse 0)
              (.clash (1, 0) (1, 3))
              (.clash (3, 1) (3, 2))
              (.clash (3, 0) (3, 2)))
            (.reuse 1)
            (.clash (3, 1) (3, 2)))
          (.clash (3, 0) (3, 2))
          (.reuse 2))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 2))
      (.clash (1, 1) (1, 2)))
    (.clash (1, 1) (3, 1))
    (.reuse 3)
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
private theorem check54 : check [state48, state49, state50, state53] state54 certificate54 = true := by
  decide +kernel
private theorem closed54 : Closed.{u} state54 :=
  sound (known := [state48, state49, state50, state53]) ⟨closed48.{u}, ⟨closed49.{u}, ⟨closed50.{u}, ⟨closed53.{u}, trivial⟩⟩⟩⟩ check54

def state55 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 6]
private def certificate55 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 1) (1, 2))
    (.transversal ![1, 2, 3, 0]
      (.transversal ![1, 0, 3, 2]
        (.clash (1, 0) (1, 2))
        (.clash (0, 0) (0, 1))
        (.clash (1, 2) (3, 2))
        (.clash (0, 0) (1, 0))
        (.transversal ![2, 0, 3, 1]
          (.clash (0, 2) (3, 2))
          (.clash (0, 0) (0, 2))
          (.transversal ![2, 0, 1, 3]
            (.clash (0, 2) (3, 2))
            (.clash (2, 1) (3, 1))
            (.clash (0, 1) (0, 2))
            (.transversal ![0, 3, 2, 1]
              (.clash (1, 1) (1, 3))
              (.clash (2, 2) (2, 3))
              (.clash (0, 0) (0, 2))
              (.transversal ![1, 3, 0, 2]
                (.clash (1, 2) (1, 3))
                (.reuse 0)
                (.clash (0, 1) (2, 1))
                (.clash (2, 0) (2, 2))
                (.clash (1, 0) (1, 3))
                (.clash (1, 0) (2, 0)))
              (.reuse 1)
              (.clash (0, 2) (2, 2)))
            (.clash (1, 0) (1, 2))
            (.clash (0, 1) (2, 1)))
          (.clash (0, 0) (1, 0))
          (.clash (3, 1) (3, 2))
          (.clash (1, 1) (3, 1)))
        (.reuse 2))
      (.clash (0, 0) (0, 1))
      (.reuse 3)
      (.clash (1, 1) (1, 2))
      (.clash (3, 0) (3, 3))
      (.clash (0, 0) (3, 0)))
    (.clash (1, 1) (3, 1))
    (.clash (2, 3) (3, 3))
    (.clash (3, 1) (3, 3))
    (.reuse 4)
private theorem check55 : check [state39, state40, state43, state47, state54] state55 certificate55 = true := by
  decide +kernel
private theorem closed55 : Closed.{u} state55 :=
  sound (known := [state39, state40, state43, state47, state54]) ⟨closed39.{u}, ⟨closed40.{u}, ⟨closed43.{u}, ⟨closed47.{u}, ⟨closed54.{u}, trivial⟩⟩⟩⟩⟩ check55

def state56 : Partition := #v[0, 1, 7, 3, 4, 0, 1, 7, 7, 9, 4, 0, 12, 7, 0, 9]
private def certificate56 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (0, 2))
    (.clash (1, 0) (1, 2))
    (.motif 0 3 1 1 2 0
      (.clash (0, 2) (2, 2)))
    (.clash (0, 2) (2, 2))
    (.clash (2, 0) (3, 0))
    (.clash (1, 0) (3, 0))
private theorem check56 : check [] state56 certificate56 = true := by
  decide +kernel
private theorem closed56 : Closed.{u} state56 :=
  sound (known := []) trivial check56

def state57 : Partition := #v[0, 1, 7, 3, 4, 0, 1, 7, 7, 9, 10, 1, 12, 7, 0, 9]
private def certificate57 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 0) (0, 2))
    (.clash (0, 1) (0, 2))
    (.clash (2, 0) (3, 0))
    (.clash (0, 0) (0, 1))
    (.clash (0, 0) (3, 0))
    (.motif 0 3 1 1 2 0
      (.clash (1, 0) (1, 3)))
private theorem check57 : check [] state57 certificate57 = true := by
  decide +kernel
private theorem closed57 : Closed.{u} state57 :=
  sound (known := []) trivial check57

def state58 : Partition := #v[0, 1, 7, 3, 4, 0, 1, 7, 7, 9, 10, 11, 12, 10, 0, 9]
private def certificate58 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (3, 1))
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 0) (0, 3))
      (.transversal ![0, 2, 3, 1]
        (.clash (0, 0) (0, 1))
        (.motif 0 2 1 3 0 2
          (.clash (0, 0) (0, 1)))
        (.clash (0, 0) (0, 3))
        (.transversal ![2, 0, 3, 1]
          (.clash (1, 0) (1, 3))
          (.clash (0, 1) (0, 2))
          (.clash (0, 2) (0, 3))
          (.clash (1, 0) (1, 2))
          (.motif 1 2 0 3 2 0
            (.clash (0, 0) (0, 1)))
          (.clash (0, 1) (0, 3)))
        (.clash (0, 1) (0, 3))
        (.clash (0, 3) (2, 3)))
      (.clash (0, 1) (0, 3))
      (.clash (1, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 2) (2, 2))
    (.clash (2, 0) (3, 0))
    (.clash (3, 0) (3, 1))
private theorem check58 : check [] state58 certificate58 = true := by
  decide +kernel
private theorem closed58 : Closed.{u} state58 :=
  sound (known := []) trivial check58

def state59 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 2, 6, 10, 11, 12, 13, 0, 6]
private def certificate59 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 1) (1, 2))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 0, 2, 3]
          (.clash (0, 1) (0, 3))
          (.transversal ![0, 3, 2, 1]
            (.clash (1, 1) (1, 3))
            (.clash (0, 0) (0, 1))
            (.clash (1, 1) (3, 1))
            (.motif 0 1 2 3 1 0
              (.clash (0, 1) (0, 2)))
            (.motif 1 3 2 1 3 2
              (.clash (0, 1) (3, 1)))
            (.clash (0, 1) (3, 1)))
          (.clash (0, 1) (2, 1))
          (.motif 0 2 3 2 3 0
            (.clash (0, 1) (0, 3)))
          (.clash (0, 3) (3, 3))
          (.clash (1, 2) (2, 2)))
        (.clash (1, 1) (1, 2))
        (.clash (3, 0) (3, 3))
        (.clash (0, 0) (3, 0)))
      (.clash (1, 1) (3, 1))
      (.clash (2, 1) (2, 3))
      (.clash (2, 1) (3, 1))
      (.transversal ![1, 0, 3, 2]
        (.clash (0, 1) (0, 3))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1))
        (.clash (0, 3) (2, 3))
        (.clash (0, 0) (0, 3))
        (.clash (1, 1) (3, 1))))
    (.clash (0, 3) (3, 3))
    (.clash (0, 0) (0, 3))
    (.clash (1, 0) (1, 2))
    (.clash (0, 0) (1, 0))
    (.clash (1, 1) (1, 2))
private theorem check59 : check [] state59 certificate59 = true := by
  decide +kernel
private theorem closed59 : Closed.{u} state59 :=
  sound (known := []) trivial check59

def state60 : Partition := #v[0, 1, 2, 3, 2, 0, 6, 1, 6, 2, 1, 0, 1, 6, 0, 2]
private def certificate60 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.clash (0, 2) (0, 3))
    (.clash (0, 1) (0, 3))
    (.columns)
    (.clash (0, 1) (0, 2))
    (.clash (0, 2) (1, 2))
    (.clash (0, 1) (3, 1))
private theorem check60 : check [] state60 certificate60 = true := by
  decide +kernel
private theorem closed60 : Closed.{u} state60 :=
  sound (known := []) trivial check60

def state61 : Partition := #v[0, 1, 2, 3, 2, 0, 6, 7, 1, 2, 7, 0, 12, 13, 0, 2]
private def certificate61 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (0, 2) (2, 2))
    (.clash (0, 1) (0, 2))
    (.clash (2, 1) (3, 1))
    (.clash (2, 0) (2, 2))
    (.motif 2 3 0 2 3 1
      (.clash (0, 0) (0, 1)))
    (.clash (0, 1) (3, 1))
private theorem check61 : check [] state61 certificate61 = true := by
  decide +kernel
private theorem closed61 : Closed.{u} state61 :=
  sound (known := []) trivial check61

def state62 : Partition := #v[0, 1, 2, 3, 2, 0, 6, 7, 8, 2, 10, 0, 12, 7, 0, 2]
private def certificate62 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (3, 1))
    (.transversal ![1, 2, 3, 0]
      (.motif 0 1 2 1 0 2
        (.clash (2, 2) (2, 3)))
      (.clash (0, 0) (0, 1))
      (.clash (2, 0) (3, 0))
      (.clash (1, 1) (1, 2))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 0) (3, 0))
        (.motif 2 3 0 2 3 1
          (.clash (0, 0) (0, 1)))
        (.clash (1, 2) (1, 3))
        (.clash (1, 2) (2, 2)))
      (.clash (0, 0) (3, 0)))
    (.clash (0, 0) (0, 1))
    (.motif 1 2 0 0 3 1
      (.clash (0, 1) (3, 1)))
    (.clash (1, 1) (1, 3))
    (.clash (0, 0) (2, 0))
private theorem check62 : check [] state62 certificate62 = true := by
  decide +kernel
private theorem closed62 : Closed.{u} state62 :=
  sound (known := []) trivial check62

def state63 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 2, 10, 0, 12, 4, 0, 2]
private def certificate63 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (1, 3) (3, 3))
    (.clash (2, 0) (2, 1))
    (.clash (2, 1) (3, 1))
    (.transversal ![0, 3, 2, 1]
      (.clash (0, 0) (2, 0))
      (.clash (2, 2) (2, 3))
      (.clash (0, 0) (1, 0))
      (.clash (2, 0) (2, 2))
      (.clash (1, 0) (1, 3))
      (.motif 2 3 0 2 3 1
        (.clash (0, 0) (0, 1))))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (2, 0))
private theorem check63 : check [] state63 certificate63 = true := by
  decide +kernel
private theorem closed63 : Closed.{u} state63 :=
  sound (known := []) trivial check63

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary03 : Known.{u} [state55, state56, state57, state58, state59, state60, state61, state62, state63] :=
  ⟨closed55.{u}, ⟨closed56.{u}, ⟨closed57.{u}, ⟨closed58.{u}, ⟨closed59.{u}, ⟨closed60.{u}, ⟨closed61.{u}, ⟨closed62.{u}, ⟨closed63.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
