/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part02
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part02
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 21 through 41. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part01

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed16 : Closed.{u} state16 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed17 : Closed.{u} state17 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed18 : Closed.{u} state18 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed19 : Closed.{u} state19 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed20 : Closed.{u} state20 :=
  known_of_mem boundary01.{u} (by decide)

def state21 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 11, 2, 11, 14, 0]
private def certificate21 : Certificate :=
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
        (.clash (0, 2) (3, 2))
        (.motif 2 3 1 1 3 2
          (.clash (0, 1) (3, 1))))
      (.clash (0, 0) (0, 2)))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (0, 2))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 1) (3, 1))
      (.reuse 0)
      (.clash (0, 0) (0, 1))
      (.clash (2, 0) (2, 3))
      (.clash (1, 1) (1, 2))
      (.clash (0, 0) (2, 0)))
    (.clash (0, 2) (1, 2))
    (.clash (3, 0) (3, 1))
private theorem check21 : check [state20] state21 certificate21 = true := by
  decide +kernel
private theorem closed21 : Closed.{u} state21 :=
  sound (known := [state20]) ⟨closed20.{u}, trivial⟩ check21

private def state22 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 1, 6, 4, 1, 2, 1, 2, 4, 0]
private def certificate22 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.motif 0 1 2 1 0 3
      (.clash (0, 0) (0, 2)))
    (.clash (0, 1) (0, 3))
    (.clash (0, 2) (0, 3))
    (.clash (0, 1) (2, 1))
    (.clash (0, 2) (3, 2))
    (.clash (0, 1) (0, 2))
private theorem check22 : check [] state22 certificate22 = true := by
  decide +kernel
private theorem closed22 : Closed.{u} state22 :=
  sound (known := []) trivial check22

private def state23 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 7, 11, 12, 11, 14, 0]
private def certificate23 : Certificate :=
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
        (.clash (1, 2) (1, 3))
        (.clash (2, 0) (2, 2))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 2, 3, 0]
          (.clash (1, 2) (1, 3))
          (.clash (0, 1) (3, 1))
          (.transversal ![2, 1, 3, 0]
            (.clash (0, 0) (0, 2))
            (.transversal ![1, 0, 3, 2]
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (0, 2))
              (.clash (0, 1) (2, 1))
              (.motif 1 2 0 2 3 0
                (.clash (0, 0) (0, 1)))
              (.reuse 0)
              (.clash (0, 2) (3, 2)))
            (.clash (0, 1) (0, 2))
            (.clash (1, 1) (3, 1))
            (.clash (0, 0) (0, 1))
            (.clash (0, 1) (3, 1)))
          (.clash (2, 0) (2, 3))
          (.clash (2, 0) (3, 0))
          (.clash (3, 0) (3, 1)))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (2, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (1, 3))
      (.clash (0, 0) (1, 0))
      (.clash (1, 1) (1, 3)))
private theorem check23 : check [state22] state23 certificate23 = true := by
  decide +kernel
private theorem closed23 : Closed.{u} state23 :=
  sound (known := [state22]) ⟨closed22.{u}, trivial⟩ check23

def state24 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 11, 12, 11, 14, 0]
private def certificate24 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 1) (1, 3))
    (.transversal ![2, 1, 3, 0]
      (.clash (0, 0) (0, 2))
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
      (.reuse 4)
      (.clash (1, 1) (3, 1))
      (.clash (0, 0) (3, 0))
      (.clash (3, 0) (3, 1)))
    (.clash (1, 1) (3, 1))
    (.reuse 5)
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
private theorem check24 : check [state16, state17, state18, state19, state21, state23] state24 certificate24 = true := by
  decide +kernel
private theorem closed24 : Closed.{u} state24 :=
  sound (known := [state16, state17, state18, state19, state21, state23]) ⟨closed16.{u}, ⟨closed17.{u}, ⟨closed18.{u}, ⟨closed19.{u}, ⟨closed21.{u}, ⟨closed23.{u}, trivial⟩⟩⟩⟩⟩⟩ check24

private def state25 : Partition := #v[0, 1, 2, 3, 3, 0, 6, 7, 2, 6, 1, 0, 1, 13, 0, 6]
private def certificate25 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 1) (1, 3))
    (.clash (0, 0) (0, 1))
    (.clash (1, 1) (3, 1))
    (.motif 0 1 2 3 1 0
      (.clash (0, 1) (0, 2)))
    (.motif 1 3 2 1 3 2
      (.clash (0, 1) (3, 1)))
    (.clash (0, 1) (3, 1))
private theorem check25 : check [] state25 certificate25 = true := by
  decide +kernel
private theorem closed25 : Closed.{u} state25 :=
  sound (known := []) trivial check25

private def state26 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 6, 10, 0, 1, 13, 0, 8]
private def certificate26 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.transversal ![0, 3, 2, 1]
      (.clash (0, 0) (0, 1))
      (.clash (2, 2) (2, 3))
      (.clash (1, 1) (3, 1))
      (.motif 1 2 3 2 3 1
        (.clash (0, 1) (3, 1)))
      (.clash (0, 1) (3, 1))
      (.transversal ![1, 0, 2, 3]
        (.clash (1, 0) (1, 3))
        (.clash (0, 1) (3, 1))
        (.clash (1, 3) (3, 3))
        (.transversal ![2, 0, 1, 3]
          (.clash (0, 2) (2, 2))
          (.clash (0, 2) (1, 2))
          (.transversal ![3, 1, 2, 0]
            (.clash (0, 0) (0, 3))
            (.motif 0 1 2 3 1 0
              (.clash (0, 1) (0, 2)))
            (.clash (0, 1) (0, 3))
            (.clash (0, 0) (1, 0))
            (.clash (0, 0) (0, 1))
            (.clash (0, 1) (3, 1)))
          (.clash (1, 0) (1, 2))
          (.clash (1, 0) (2, 0))
          (.clash (2, 0) (2, 1)))
        (.clash (1, 0) (2, 0))
        (.clash (2, 0) (2, 2))))
    (.clash (2, 0) (3, 0))
    (.clash (0, 0) (0, 1))
    (.clash (1, 3) (3, 3))
    (.clash (1, 1) (1, 3))
    (.clash (0, 0) (2, 0))
private theorem check26 : check [] state26 certificate26 = true := by
  decide +kernel
private theorem closed26 : Closed.{u} state26 :=
  sound (known := []) trivial check26

private def state27 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 7, 7, 3, 10, 0, 3, 7, 0, 1]
private def certificate27 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (3, 1))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 0) (0, 2))
      (.transversal ![2, 0, 1, 3]
        (.clash (1, 0) (1, 3))
        (.clash (0, 2) (0, 3))
        (.clash (0, 1) (0, 2))
        (.clash (1, 0) (1, 2))
        (.columns)
        (.clash (0, 1) (0, 3)))
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (2, 0))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 1) (0, 3))
    (.clash (2, 0) (2, 2))
    (.clash (0, 3) (1, 3))
    (.clash (1, 2) (2, 2))
private theorem check27 : check [] state27 certificate27 = true := by
  decide +kernel
private theorem closed27 : Closed.{u} state27 :=
  sound (known := []) trivial check27

private def state28 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 7, 8, 3, 10, 0, 3, 10, 0, 15]
private def certificate28 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.transversal ![1, 0, 2, 3]
      (.clash (1, 0) (1, 3))
      (.clash (0, 1) (3, 1))
      (.clash (1, 3) (3, 3))
      (.motif 1 3 0 0 2 1
        (.clash (0, 1) (0, 3)))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (0, 3))
        (.motif 0 2 1 1 3 0
          (.clash (0, 3) (3, 3)))
        (.clash (1, 0) (1, 3))
        (.clash (2, 0) (2, 1))
        (.clash (0, 3) (3, 3))
        (.clash (1, 0) (2, 0)))
      (.clash (3, 1) (3, 3)))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (0, 3))
    (.motif 1 2 0 3 1 2
      (.clash (0, 0) (0, 2)))
    (.clash (0, 3) (1, 3))
    (.clash (1, 2) (2, 2))
private theorem check28 : check [] state28 certificate28 = true := by
  decide +kernel
private theorem closed28 : Closed.{u} state28 :=
  sound (known := []) trivial check28

private def state29 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 6, 10, 0, 6, 13, 0, 15]
private def certificate29 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.transversal ![2, 0, 1, 3]
      (.clash (0, 2) (0, 3))
      (.clash (0, 2) (1, 2))
      (.transversal ![2, 0, 3, 1]
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (0, 2))
        (.clash (3, 1) (3, 3))
        (.clash (0, 0) (0, 3))
        (.motif 1 3 0 0 2 1
          (.clash (0, 1) (2, 1)))
        (.clash (1, 1) (3, 1)))
      (.clash (1, 0) (1, 2))
      (.clash (0, 3) (3, 3))
      (.clash (3, 0) (3, 3)))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 1) (1, 3))
      (.clash (2, 2) (2, 3))
      (.clash (1, 1) (3, 1))
      (.motif 1 2 0 3 1 2
        (.clash (0, 0) (0, 2)))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.motif 0 2 1 1 3 0
          (.clash (1, 0) (1, 2)))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 2, 0, 3]
          (.clash (0, 1) (0, 3))
          (.clash (0, 1) (3, 1))
          (.reuse 0)
          (.clash (0, 3) (1, 3))
          (.clash (0, 3) (3, 3))
          (.clash (1, 3) (3, 3)))
        (.clash (1, 1) (1, 3))
        (.clash (0, 0) (2, 0)))
      (.reuse 1))
    (.clash (0, 0) (0, 3))
    (.clash (1, 0) (1, 2))
    (.clash (0, 0) (1, 0))
    (.clash (0, 0) (3, 0))
private theorem check29 : check [state27, state28] state29 certificate29 = true := by
  decide +kernel
private theorem closed29 : Closed.{u} state29 :=
  sound (known := [state27, state28]) ⟨closed27.{u}, ⟨closed28.{u}, trivial⟩⟩ check29

private def state30 : Partition := #v[0, 1, 8, 3, 4, 0, 6, 1, 8, 6, 4, 0, 6, 4, 1, 8]
private def certificate30 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.clash (0, 0) (0, 3))
    (.clash (0, 2) (0, 3))
    (.clash (0, 1) (0, 3))
    (.clash (0, 0) (0, 2))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (0, 2))
private theorem check30 : check [] state30 certificate30 = true := by
  decide +kernel
private theorem closed30 : Closed.{u} state30 :=
  sound (known := []) trivial check30

private def state31 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 1, 8, 6, 10, 0, 6, 10, 1, 4]
private def certificate31 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (2, 1))
    (.motif 1 3 2 0 2 3
      (.clash (0, 0) (3, 0)))
    (.clash (1, 0) (1, 3))
    (.clash (2, 0) (2, 1))
    (.clash (1, 0) (1, 2))
    (.clash (1, 0) (2, 0))
private theorem check31 : check [] state31 certificate31 = true := by
  decide +kernel
private theorem closed31 : Closed.{u} state31 :=
  sound (known := []) trivial check31

private def state32 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 6, 10, 0, 12, 13, 7, 15]
private def certificate32 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 1) (1, 3))
    (.clash (2, 2) (2, 3))
    (.clash (1, 1) (3, 1))
    (.clash (2, 2) (3, 2))
    (.clash (3, 1) (3, 2))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 0) (1, 3))
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (3, 0))
        (.clash (2, 2) (3, 2))
        (.clash (3, 0) (3, 2))
        (.clash (3, 0) (3, 1)))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 1))
        (.clash (3, 0) (3, 2))
        (.clash (1, 1) (1, 2))
        (.transversal ![1, 0, 2, 3]
          (.clash (1, 0) (1, 3))
          (.clash (0, 1) (3, 1))
          (.clash (1, 3) (3, 3))
          (.transversal ![2, 0, 1, 3]
            (.clash (0, 2) (2, 2))
            (.clash (0, 2) (1, 2))
            (.transversal ![1, 2, 0, 3]
              (.clash (0, 1) (2, 1))
              (.motif 2 3 0 1 2 0
                (.clash (0, 0) (1, 0)))
              (.clash (0, 1) (0, 2))
              (.clash (2, 0) (2, 1))
              (.clash (0, 2) (1, 2))
              (.reuse 0))
            (.clash (1, 0) (1, 2))
            (.clash (3, 1) (3, 3))
            (.clash (3, 0) (3, 3)))
          (.reuse 1)
          (.clash (3, 1) (3, 3)))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 3))
      (.clash (1, 1) (1, 3)))
private theorem check32 : check [state30, state31] state32 certificate32 = true := by
  decide +kernel
private theorem closed32 : Closed.{u} state32 :=
  sound (known := [state30, state31]) ⟨closed30.{u}, ⟨closed31.{u}, trivial⟩⟩ check32

private def state33 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 1, 8, 3, 1, 4, 12, 4, 0, 8]
private def certificate33 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (0, 3))
    (.clash (0, 1) (3, 1))
    (.transversal ![2, 1, 3, 0]
      (.clash (0, 0) (0, 2))
      (.motif 0 2 1 3 2 1
        (.clash (0, 0) (0, 2)))
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (1, 0))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 3) (2, 3))
    (.motif 1 3 0 0 2 1
      (.clash (0, 1) (0, 3)))
    (.clash (1, 0) (3, 0))
private theorem check33 : check [] state33 certificate33 = true := by
  decide +kernel
private theorem closed33 : Closed.{u} state33 :=
  sound (known := []) trivial check33

private def state34 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 7, 8, 3, 7, 4, 12, 4, 0, 1]
private def certificate34 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (0, 3))
    (.clash (0, 1) (3, 1))
    (.clash (3, 0) (3, 3))
    (.clash (0, 3) (2, 3))
    (.motif 1 3 0 0 2 1
      (.clash (0, 1) (0, 3)))
    (.clash (1, 0) (3, 0))
private theorem check34 : check [] state34 certificate34 = true := by
  decide +kernel
private theorem closed34 : Closed.{u} state34 :=
  sound (known := []) trivial check34

private def state35 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 1, 8, 6, 0, 2, 6, 2, 1, 0]
private def certificate35 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (2, 1))
    (.transversal ![2, 0, 1, 3]
      (.transversal ![3, 0, 1, 2]
        (.clash (0, 2) (0, 3))
        (.columns)
        (.clash (0, 1) (0, 3))
        (.clash (0, 2) (1, 2))
        (.clash (0, 1) (0, 2))
        (.clash (0, 1) (2, 1)))
      (.clash (0, 2) (1, 2))
      (.clash (0, 0) (0, 2))
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (1, 0))
      (.clash (0, 0) (3, 0)))
    (.clash (0, 0) (0, 1))
    (.clash (2, 0) (2, 1))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (2, 0))
private theorem check35 : check [] state35 certificate35 = true := by
  decide +kernel
private theorem closed35 : Closed.{u} state35 :=
  sound (known := []) trivial check35

private def state36 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 6, 10, 11, 12, 11, 7, 15]
private def certificate36 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 1) (1, 3))
    (.transversal ![1, 2, 3, 0]
      (.clash (0, 1) (2, 1))
      (.clash (0, 1) (3, 1))
      (.transversal ![2, 3, 1, 0]
        (.clash (0, 2) (3, 2))
        (.clash (0, 2) (1, 2))
        (.clash (0, 1) (0, 2))
        (.clash (1, 2) (1, 3))
        (.clash (3, 0) (3, 2))
        (.clash (0, 1) (2, 1)))
      (.clash (2, 1) (2, 3))
      (.transversal ![1, 3, 2, 0]
        (.transversal ![2, 1, 3, 0]
          (.clash (0, 0) (0, 2))
          (.transversal ![1, 0, 2, 3]
            (.clash (1, 0) (1, 3))
            (.clash (0, 0) (0, 1))
            (.clash (1, 3) (3, 3))
            (.clash (0, 0) (1, 0))
            (.transversal ![2, 1, 0, 3]
              (.clash (0, 0) (0, 2))
              (.clash (2, 0) (2, 3))
              (.clash (2, 3) (3, 3))
              (.clash (0, 0) (2, 0))
              (.clash (0, 0) (1, 0))
              (.clash (1, 0) (2, 0)))
            (.reuse 0))
          (.clash (0, 2) (1, 2))
          (.clash (1, 1) (3, 1))
          (.clash (0, 0) (3, 0))
          (.clash (2, 1) (2, 3)))
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (2, 1))
        (.clash (1, 1) (1, 3))
        (.clash (1, 2) (1, 3))
        (.clash (0, 0) (3, 0)))
      (.clash (3, 0) (3, 1)))
    (.clash (1, 1) (3, 1))
    (.clash (2, 2) (3, 2))
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
private theorem check36 : check [state35] state36 certificate36 = true := by
  decide +kernel
private theorem closed36 : Closed.{u} state36 :=
  sound (known := [state35]) ⟨closed35.{u}, trivial⟩ check36

private def state37 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 6, 10, 11, 12, 11, 14, 15]
private def certificate37 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (1, 2))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 1) (1, 3))
      (.clash (2, 2) (3, 2))
      (.clash (1, 1) (3, 1))
      (.transversal ![1, 0, 3, 2]
        (.transversal ![1, 3, 0, 2]
          (.clash (1, 0) (1, 3))
          (.clash (1, 0) (2, 0))
          (.clash (0, 0) (0, 1))
          (.clash (2, 0) (2, 2))
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (2, 0)))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1))
        (.transversal ![3, 0, 1, 2]
          (.clash (0, 3) (2, 3))
          (.transversal ![1, 0, 2, 3]
            (.clash (0, 1) (3, 1))
            (.transversal ![1, 2, 0, 3]
              (.clash (0, 1) (0, 3))
              (.clash (2, 0) (2, 2))
              (.clash (1, 3) (3, 3))
              (.clash (2, 0) (2, 1))
              (.clash (0, 3) (3, 3))
              (.reuse 0))
            (.reuse 1)
            (.clash (1, 0) (1, 3))
            (.clash (2, 3) (3, 3))
            (.clash (1, 3) (3, 3)))
          (.clash (0, 0) (0, 3))
          (.clash (1, 0) (1, 2))
          (.clash (0, 0) (1, 0))
          (.clash (1, 1) (1, 2)))
        (.clash (0, 0) (1, 0))
        (.clash (1, 1) (3, 1)))
      (.clash (1, 3) (2, 3))
      (.clash (2, 2) (2, 3)))
    (.clash (1, 2) (1, 3))
    (.reuse 2)
    (.clash (1, 2) (3, 2))
private theorem check37 : check [state33, state34, state36] state37 certificate37 = true := by
  decide +kernel
private theorem closed37 : Closed.{u} state37 :=
  sound (known := [state33, state34, state36]) ⟨closed33.{u}, ⟨closed34.{u}, ⟨closed36.{u}, trivial⟩⟩⟩ check37

def state38 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 6, 10, 11, 12, 13, 14, 15]
private def certificate38 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 1) (1, 2))
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 1) (1, 3))
      (.clash (1, 1) (1, 2))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 2, 0, 3]
          (.clash (0, 1) (2, 1))
          (.clash (2, 0) (3, 0))
          (.clash (3, 0) (3, 3))
          (.clash (2, 0) (2, 1))
          (.transversal ![2, 1, 0, 3]
            (.clash (0, 0) (0, 2))
            (.transversal ![3, 0, 1, 2]
              (.transversal ![1, 0, 2, 3]
                (.clash (0, 1) (0, 3))
                (.reuse 0)
                (.clash (0, 1) (2, 1))
                (.motif 0 2 3 2 3 0
                  (.clash (0, 1) (0, 3)))
                (.clash (0, 3) (3, 3))
                (.clash (1, 2) (2, 2)))
              (.clash (0, 3) (3, 3))
              (.clash (0, 0) (0, 3))
              (.clash (1, 0) (1, 2))
              (.clash (0, 0) (1, 0))
              (.clash (1, 1) (1, 2)))
            (.clash (0, 2) (1, 2))
            (.clash (0, 0) (2, 0))
            (.clash (1, 1) (1, 2))
            (.clash (2, 0) (2, 1)))
          (.reuse 1))
        (.clash (1, 1) (1, 2))
        (.reuse 2)
        (.clash (0, 0) (3, 0)))
      (.clash (1, 2) (1, 3))
      (.reuse 3)
      (.clash (1, 2) (3, 2)))
    (.clash (1, 1) (3, 1))
    (.clash (2, 1) (2, 3))
    (.clash (2, 1) (3, 1))
    (.reuse 4)
private theorem check38 : check [state25, state26, state29, state32, state37] state38 certificate38 = true := by
  decide +kernel
private theorem closed38 : Closed.{u} state38 :=
  sound (known := [state25, state26, state29, state32, state37]) ⟨closed25.{u}, ⟨closed26.{u}, ⟨closed29.{u}, ⟨closed32.{u}, ⟨closed37.{u}, trivial⟩⟩⟩⟩⟩ check38

def state39 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 1, 4, 7, 0, 12, 2, 4, 1]
private def certificate39 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.clash (0, 2) (2, 2))
    (.clash (0, 2) (3, 2))
    (.clash (3, 0) (3, 1))
    (.clash (1, 0) (1, 3))
    (.motif 1 3 2 2 0 3
      (.clash (0, 0) (1, 0)))
    (.clash (1, 0) (3, 0))
private theorem check39 : check [] state39 certificate39 = true := by
  decide +kernel
private theorem closed39 : Closed.{u} state39 :=
  sound (known := []) trivial check39

def state40 : Partition := #v[0, 1, 7, 3, 4, 0, 1, 7, 8, 4, 10, 0, 12, 7, 4, 1]
private def certificate40 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (0, 2))
    (.clash (1, 2) (2, 2))
    (.clash (3, 0) (3, 3))
    (.clash (0, 2) (2, 2))
    (.clash (3, 0) (3, 1))
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 1) (0, 2))
      (.transversal ![3, 1, 0, 2]
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (0, 3))
        (.motif 0 2 1 0 1 3
          (.clash (0, 1) (0, 2)))
        (.clash (0, 0) (0, 1))
        (.clash (0, 0) (1, 0))
        (.clash (0, 1) (2, 1)))
      (.clash (0, 1) (2, 1))
      (.motif 1 2 0 0 3 1
        (.clash (0, 1) (0, 2)))
      (.clash (0, 2) (3, 2))
      (.clash (1, 0) (2, 0)))
private theorem check40 : check [] state40 certificate40 = true := by
  decide +kernel
private theorem closed40 : Closed.{u} state40 :=
  sound (known := []) trivial check40

def state41 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 1, 9, 10, 0, 7, 10, 0, 1]
private def certificate41 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.transversal ![2, 0, 3, 1]
      (.clash (1, 0) (1, 3))
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (2, 2))
      (.clash (0, 0) (1, 0))
      (.transversal ![2, 0, 1, 3]
        (.clash (0, 2) (2, 2))
        (.transversal ![3, 0, 1, 2]
          (.columns)
          (.clash (0, 2) (0, 3))
          (.clash (0, 0) (0, 3))
          (.clash (0, 2) (2, 2))
          (.clash (0, 0) (1, 0))
          (.clash (0, 0) (0, 2)))
        (.clash (0, 1) (0, 2))
        (.clash (2, 1) (2, 2))
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (2, 1)))
      (.clash (1, 1) (3, 1)))
    (.clash (0, 1) (0, 2))
    (.clash (0, 2) (2, 2))
    (.clash (1, 2) (1, 3))
    (.clash (3, 0) (3, 1))
    (.clash (0, 1) (3, 1))
private theorem check41 : check [] state41 certificate41 = true := by
  decide +kernel
private theorem closed41 : Closed.{u} state41 :=
  sound (known := []) trivial check41

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary02 : Known.{u} [state21, state24, state38, state39, state40, state41] :=
  ⟨closed21.{u}, ⟨closed24.{u}, ⟨closed38.{u}, ⟨closed39.{u}, ⟨closed40.{u}, ⟨closed41.{u}, trivial⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
