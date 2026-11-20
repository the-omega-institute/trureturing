/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part04
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part04
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 64 through 80. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part03

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed56 : Closed.{u} state56 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed57 : Closed.{u} state57 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed58 : Closed.{u} state58 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed59 : Closed.{u} state59 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed60 : Closed.{u} state60 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed61 : Closed.{u} state61 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed62 : Closed.{u} state62 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed63 : Closed.{u} state63 :=
  known_of_mem boundary03.{u} (by decide)

private def state64 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 2, 10, 11, 11, 13, 0, 2]
private def certificate64 : Certificate :=
  .transversal ![3, 1, 2, 0]
    (.clash (0, 0) (0, 3))
    (.transversal ![3, 2, 1, 0]
      (.clash (1, 2) (2, 2))
      (.clash (0, 2) (0, 3))
      (.clash (0, 3) (2, 3))
      (.clash (0, 2) (1, 2))
      (.transversal ![0, 3, 2, 1]
        (.clash (1, 1) (1, 3))
        (.clash (0, 0) (0, 3))
        (.clash (1, 1) (3, 1))
        (.clash (0, 3) (1, 3))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (0, 3))
          (.motif 0 2 1 2 3 1
            (.clash (0, 0) (0, 3)))
          (.clash (0, 3) (1, 3))
          (.clash (1, 2) (1, 3))
          (.clash (0, 3) (2, 3)))
        (.transversal ![2, 3, 0, 1]
          (.clash (1, 3) (3, 3))
          (.clash (2, 0) (2, 1))
          (.clash (0, 2) (0, 3))
          (.transversal ![1, 0, 3, 2]
            (.transversal ![1, 2, 0, 3]
              (.clash (1, 0) (1, 2))
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (0, 2))
              (.clash (1, 2) (1, 3))
              (.clash (0, 2) (1, 2))
              (.clash (1, 3) (3, 3)))
            (.motif 0 2 1 2 3 1
              (.clash (0, 0) (0, 3)))
            (.clash (0, 0) (0, 1))
            (.clash (1, 0) (1, 2))
            (.clash (0, 0) (1, 0))
            (.clash (0, 0) (3, 0)))
          (.clash (0, 3) (1, 3))
          (.clash (2, 0) (2, 2))))
      (.clash (2, 1) (2, 3)))
    (.clash (0, 3) (2, 3))
    (.clash (2, 2) (3, 2))
    (.clash (0, 0) (3, 0))
    (.clash (2, 2) (2, 3))
private theorem check64 : check [] state64 certificate64 = true := by
  decide +kernel
private theorem closed64 : Closed.{u} state64 :=
  sound (known := []) trivial check64

private def state65 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 2, 10, 11, 12, 13, 0, 2]
private def certificate65 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 0) (0, 2))
    (.clash (2, 1) (2, 3))
    (.clash (3, 0) (3, 3))
    (.transversal ![2, 0, 3, 1]
      (.transversal ![0, 3, 2, 1]
        (.clash (1, 1) (1, 3))
        (.clash (2, 2) (2, 3))
        (.clash (1, 1) (3, 1))
        (.transversal ![1, 3, 0, 2]
          (.transversal ![1, 2, 0, 3]
            (.clash (1, 2) (1, 3))
            (.clash (2, 0) (2, 2))
            (.clash (0, 1) (0, 2))
            (.transversal ![1, 2, 3, 0]
              (.clash (1, 2) (1, 3))
              (.clash (0, 0) (0, 1))
              (.transversal ![2, 3, 0, 1]
                (.clash (0, 1) (0, 2))
                (.clash (0, 2) (1, 2))
                (.clash (2, 1) (3, 1))
                (.clash (1, 2) (1, 3))
                (.clash (0, 1) (3, 1))
                (.reuse 0))
              (.clash (0, 0) (2, 0))
              (.clash (2, 0) (3, 0))
              (.clash (0, 0) (3, 0)))
            (.clash (0, 2) (1, 2))
            (.clash (1, 0) (2, 0)))
          (.reuse 1)
          (.clash (0, 0) (0, 1))
          (.clash (2, 0) (2, 2))
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (2, 0)))
        (.reuse 2)
        (.motif 2 3 0 2 3 1
          (.clash (0, 0) (0, 1))))
      (.clash (0, 0) (0, 2))
      (.clash (2, 1) (3, 1))
      (.clash (0, 0) (1, 0))
      (.reuse 3)
      (.clash (1, 1) (3, 1)))
    (.clash (0, 0) (3, 0))
    (.reuse 4)
private theorem check65 : check [state60, state61, state62, state63, state64] state65 certificate65 = true := by
  decide +kernel
private theorem closed65 : Closed.{u} state65 :=
  sound (known := [state60, state61, state62, state63, state64]) ⟨closed60.{u}, ⟨closed61.{u}, ⟨closed62.{u}, ⟨closed63.{u}, ⟨closed64.{u}, trivial⟩⟩⟩⟩⟩ check65

private def state66 : Partition := #v[0, 1, 2, 6, 4, 0, 6, 7, 8, 4, 0, 11, 12, 6, 7, 4]
private def certificate66 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (0, 1) (2, 1))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 1) (0, 3))
      (.clash (2, 0) (2, 3))
      (.clash (0, 1) (2, 1))
      (.motif 1 2 0 0 2 1
        (.clash (0, 1) (0, 3)))
      (.clash (0, 3) (3, 3))
      (.clash (1, 0) (2, 0)))
    (.transversal ![1, 2, 3, 0]
      (.clash (0, 1) (0, 3))
      (.clash (1, 3) (2, 3))
      (.clash (3, 0) (3, 2))
      (.clash (0, 3) (2, 3))
      (.clash (3, 0) (3, 1))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (0, 3))
        (.transversal ![2, 1, 0, 3]
          (.clash (0, 0) (0, 2))
          (.clash (0, 1) (0, 2))
          (.motif 0 2 1 0 1 2
            (.clash (0, 1) (0, 3)))
          (.clash (0, 0) (0, 1))
          (.clash (0, 0) (1, 0))
          (.clash (0, 1) (2, 1)))
        (.clash (0, 1) (2, 1))
        (.motif 1 2 0 0 2 1
          (.clash (0, 1) (0, 3)))
        (.clash (0, 3) (3, 3))
        (.clash (1, 0) (2, 0))))
    (.clash (2, 1) (2, 3))
    (.clash (1, 0) (1, 3))
    (.clash (1, 3) (2, 3))
private theorem check66 : check [] state66 certificate66 = true := by
  decide +kernel
private theorem closed66 : Closed.{u} state66 :=
  sound (known := []) trivial check66

private def state67 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 1, 1, 2, 4, 0, 6, 4, 1, 2]
private def certificate67 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.motif 0 1 2 0 3 1
      (.clash (0, 2) (0, 3)))
    (.clash (0, 2) (0, 3))
    (.clash (0, 1) (0, 3))
    (.clash (0, 2) (2, 2))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (0, 2))
private theorem check67 : check [] state67 certificate67 = true := by
  decide +kernel
private theorem closed67 : Closed.{u} state67 :=
  sound (known := []) trivial check67

private def state68 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 1, 1, 2, 10, 6, 12, 10, 1, 2]
private def certificate68 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 0) (0, 2))
    (.clash (0, 2) (1, 2))
    (.clash (3, 0) (3, 3))
    (.clash (1, 1) (1, 2))
    (.clash (0, 0) (3, 0))
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 0) (0, 3))
      (.motif 0 3 1 3 2 1
        (.clash (0, 0) (0, 2)))
      (.clash (0, 3) (2, 3))
      (.clash (1, 1) (3, 1))
      (.clash (0, 0) (3, 0))
      (.clash (1, 2) (2, 2)))
private theorem check68 : check [] state68 certificate68 = true := by
  decide +kernel
private theorem closed68 : Closed.{u} state68 :=
  sound (known := []) trivial check68

private def state69 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 6, 12, 10, 7, 9]
private def certificate69 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.transversal ![1, 3, 2, 0]
      (.clash (1, 2) (1, 3))
      (.clash (0, 1) (3, 1))
      (.transversal ![2, 3, 1, 0]
        (.clash (0, 2) (3, 2))
        (.transversal ![2, 3, 0, 1]
          (.clash (0, 2) (3, 2))
          (.clash (2, 0) (2, 1))
          (.clash (0, 2) (2, 2))
          (.transversal ![3, 1, 2, 0]
            (.clash (0, 0) (0, 3))
            (.motif 0 2 1 2 3 1
              (.clash (0, 0) (0, 3)))
            (.clash (0, 1) (0, 3))
            (.clash (1, 1) (3, 1))
            (.clash (0, 0) (0, 1))
            (.clash (0, 1) (3, 1)))
          (.clash (2, 2) (3, 2))
          (.clash (2, 0) (2, 2)))
        (.clash (0, 1) (0, 2))
        (.clash (1, 3) (3, 3))
        (.clash (1, 2) (1, 3))
        (.clash (0, 1) (2, 1)))
      (.clash (2, 2) (3, 2))
      (.clash (3, 0) (3, 2))
      (.clash (3, 0) (3, 1)))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (2, 0))
      (.clash (2, 0) (2, 3))
      (.transversal ![2, 1, 0, 3]
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2))
        (.reuse 0)
        (.clash (0, 0) (0, 1))
        (.clash (1, 1) (2, 1))
        (.clash (0, 1) (2, 1)))
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (1, 3))
      (.clash (1, 2) (1, 3)))
    (.clash (0, 1) (2, 1))
    (.clash (2, 0) (2, 3))
    (.clash (2, 1) (2, 3))
    (.clash (2, 0) (2, 1))
private theorem check69 : check [state68] state69 certificate69 = true := by
  decide +kernel
private theorem closed69 : Closed.{u} state69 :=
  sound (known := [state68]) ⟨closed68.{u}, trivial⟩ check69

private def state70 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 11, 12, 10, 7, 9]
private def certificate70 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 1) (1, 2))
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
        (.clash (1, 2) (1, 3))
        (.clash (0, 0) (0, 1))
        (.clash (3, 0) (3, 2))
        (.clash (1, 1) (1, 2))
        (.transversal ![1, 2, 0, 3]
          (.clash (1, 2) (1, 3))
          (.transversal ![2, 1, 0, 3]
            (.clash (0, 0) (0, 2))
            (.clash (0, 1) (0, 2))
            (.transversal ![1, 0, 2, 3]
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (3, 1))
              (.clash (0, 1) (0, 2))
              (.reuse 0)
              (.motif 1 2 0 1 0 3
                (.clash (0, 2) (0, 3)))
              (.clash (0, 2) (2, 2)))
            (.clash (0, 0) (0, 1))
            (.clash (1, 1) (2, 1))
            (.clash (0, 1) (2, 1)))
          (.clash (0, 1) (2, 1))
          (.clash (2, 0) (3, 0))
          (.clash (3, 0) (3, 3))
          (.clash (2, 0) (2, 1)))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 3))
      (.clash (1, 1) (1, 3)))
    (.clash (1, 1) (3, 1))
    (.reuse 1)
    (.clash (1, 2) (2, 2))
    (.clash (2, 2) (2, 3))
private theorem check70 : check [state67, state69] state70 certificate70 = true := by
  decide +kernel
private theorem closed70 : Closed.{u} state70 :=
  sound (known := [state67, state69]) ⟨closed67.{u}, ⟨closed69.{u}, trivial⟩⟩ check70

private def state71 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 11, 12, 13, 7, 9]
private def certificate71 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 1) (1, 3))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 0) (1, 3))
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (3, 0))
        (.clash (1, 1) (1, 3))
        (.clash (3, 0) (3, 2))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![3, 0, 2, 1]
        (.clash (0, 3) (3, 3))
        (.clash (0, 0) (0, 3))
        (.transversal ![0, 2, 3, 1]
          (.clash (1, 1) (1, 2))
          (.clash (2, 2) (2, 3))
          (.clash (0, 0) (0, 3))
          (.transversal ![2, 0, 3, 1]
            (.transversal ![2, 1, 3, 0]
              (.clash (0, 0) (0, 2))
              (.clash (0, 2) (1, 2))
              (.clash (1, 0) (3, 0))
              (.clash (1, 1) (1, 2))
              (.clash (0, 0) (3, 0))
              (.motif 1 3 0 2 3 0
                (.clash (1, 1) (1, 3))))
            (.clash (0, 2) (1, 2))
            (.clash (0, 2) (0, 3))
            (.clash (1, 0) (1, 2))
            (.clash (0, 3) (3, 3))
            (.clash (0, 3) (2, 3)))
          (.reuse 0)
          (.clash (0, 3) (2, 3)))
        (.clash (0, 0) (1, 0))
        (.clash (2, 1) (3, 1))
        (.clash (1, 1) (3, 1)))
      (.clash (1, 1) (2, 1)))
    (.clash (1, 1) (3, 1))
    (.clash (2, 2) (3, 2))
    (.clash (3, 1) (3, 2))
    (.reuse 1)
private theorem check71 : check [state66, state70] state71 certificate71 = true := by
  decide +kernel
private theorem closed71 : Closed.{u} state71 :=
  sound (known := [state66, state70]) ⟨closed66.{u}, ⟨closed70.{u}, trivial⟩⟩ check71

def state72 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 9]
private def certificate72 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 0) (0, 2))
      (.transversal ![1, 2, 0, 3]
        (.transversal ![1, 3, 0, 2]
          (.clash (1, 2) (1, 3))
          (.clash (0, 1) (0, 2))
          (.clash (0, 0) (0, 1))
          (.transversal ![0, 3, 2, 1]
            (.clash (0, 0) (0, 2))
            (.clash (2, 2) (3, 2))
            (.clash (1, 1) (3, 1))
            (.clash (0, 2) (2, 2))
            (.transversal ![0, 2, 3, 1]
              (.clash (0, 0) (0, 1))
              (.transversal ![1, 0, 2, 3]
                (.clash (1, 0) (1, 2))
                (.clash (1, 2) (2, 2))
                (.clash (0, 1) (2, 1))
                (.reuse 0)
                (.motif 1 2 0 0 3 1
                  (.clash (0, 1) (0, 2)))
                (.clash (2, 1) (2, 2)))
              (.clash (0, 0) (0, 2))
              (.reuse 1)
              (.clash (0, 1) (0, 2))
              (.clash (1, 3) (2, 3)))
            (.reuse 2))
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (0, 2)))
        (.clash (0, 1) (0, 2))
        (.clash (0, 1) (2, 1))
        (.clash (0, 2) (1, 2))
        (.reuse 3)
        (.clash (2, 0) (2, 1)))
      (.reuse 4)
      (.clash (0, 0) (2, 0))
      (.clash (1, 1) (2, 1))
      (.clash (2, 0) (2, 1)))
    (.clash (1, 3) (3, 3))
    (.reuse 5)
    (.clash (3, 2) (3, 3))
private theorem check72 : check [state56, state57, state58, state59, state65, state71] state72 certificate72 = true := by
  decide +kernel
private theorem closed72 : Closed.{u} state72 :=
  sound (known := [state56, state57, state58, state59, state65, state71]) ⟨closed56.{u}, ⟨closed57.{u}, ⟨closed58.{u}, ⟨closed59.{u}, ⟨closed65.{u}, ⟨closed71.{u}, trivial⟩⟩⟩⟩⟩⟩ check72

def state73 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 2, 0, 1, 1, 13, 7, 0]
private def certificate73 : Certificate :=
  .transversal ![2, 0, 3, 1]
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
    (.clash (0, 1) (3, 1))
private theorem check73 : check [] state73 certificate73 = true := by
  decide +kernel
private theorem closed73 : Closed.{u} state73 :=
  sound (known := []) trivial check73

def state74 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 9, 0, 1, 1, 13, 9, 0]
private def certificate74 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (1, 2) (1, 3))
    (.clash (2, 0) (2, 3))
    (.clash (0, 1) (2, 1))
    (.transversal ![2, 3, 1, 0]
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
      (.clash (0, 1) (2, 1)))
    (.motif 1 2 0 1 3 2
      (.clash (0, 2) (3, 2)))
    (.clash (2, 0) (2, 1))
private theorem check74 : check [] state74 certificate74 = true := by
  decide +kernel
private theorem closed74 : Closed.{u} state74 :=
  sound (known := []) trivial check74

def state75 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 9, 0, 1, 7, 13, 14, 0]
private def certificate75 : Certificate :=
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
private theorem check75 : check [] state75 certificate75 = true := by
  decide +kernel
private theorem closed75 : Closed.{u} state75 :=
  sound (known := []) trivial check75

private def state76 : Partition := #v[0, 1, 2, 3, 3, 0, 6, 7, 1, 9, 0, 6, 12, 13, 3, 0]
private def certificate76 : Certificate :=
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
private theorem check76 : check [] state76 certificate76 = true := by
  decide +kernel
private theorem closed76 : Closed.{u} state76 :=
  sound (known := []) trivial check76

def state77 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 1, 9, 0, 6, 12, 13, 14, 0]
private def certificate77 : Certificate :=
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
private theorem check77 : check [state76] state77 certificate77 = true := by
  decide +kernel
private theorem closed77 : Closed.{u} state77 :=
  sound (known := [state76]) ⟨closed76.{u}, trivial⟩ check77

def state78 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 6, 12, 13, 14, 9]
private def certificate78 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
    (.clash (2, 2) (3, 2))
    (.clash (1, 3) (3, 3))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 2, 0, 3]
        (.clash (1, 0) (1, 2))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (2, 3))
        (.clash (2, 1) (2, 3))
        (.clash (2, 0) (2, 1)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![3, 0, 2, 1]
        (.clash (0, 3) (3, 3))
        (.clash (0, 0) (0, 3))
        (.transversal ![2, 0, 3, 1]
          (.transversal ![2, 1, 3, 0]
            (.clash (0, 0) (0, 2))
            (.clash (0, 2) (1, 2))
            (.clash (1, 0) (3, 0))
            (.clash (1, 1) (1, 2))
            (.clash (0, 0) (3, 0))
            (.motif 1 3 0 2 3 0
              (.clash (1, 1) (1, 3))))
          (.clash (0, 2) (1, 2))
          (.clash (0, 2) (0, 3))
          (.clash (1, 0) (1, 2))
          (.clash (0, 3) (3, 3))
          (.clash (0, 3) (2, 3)))
        (.clash (0, 0) (1, 0))
        (.clash (2, 1) (3, 1))
        (.clash (1, 1) (3, 1)))
      (.clash (1, 1) (2, 1)))
    (.clash (3, 2) (3, 3))
private theorem check78 : check [] state78 certificate78 = true := by
  decide +kernel
private theorem closed78 : Closed.{u} state78 :=
  sound (known := []) trivial check78

private def state79 : Partition := #v[0, 1, 2, 3, 4, 0, 3, 1, 8, 4, 0, 11, 11, 3, 1, 4]
private def certificate79 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (0, 3))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 0) (0, 2))
      (.clash (0, 1) (0, 2))
      (.motif 0 2 1 0 1 2
        (.clash (0, 1) (0, 3)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 0) (1, 0))
      (.clash (0, 1) (2, 1)))
    (.clash (0, 1) (2, 1))
    (.motif 1 2 0 0 2 1
      (.clash (0, 1) (0, 3)))
    (.clash (0, 3) (3, 3))
    (.clash (1, 0) (2, 0))
private theorem check79 : check [] state79 certificate79 = true := by
  decide +kernel
private theorem closed79 : Closed.{u} state79 :=
  sound (known := []) trivial check79

def state80 : Partition := #v[0, 1, 2, 3, 4, 0, 6, 7, 8, 9, 0, 11, 12, 6, 14, 9]
private def certificate80 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
    (.clash (2, 2) (3, 2))
    (.clash (1, 3) (3, 3))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 0) (1, 3))
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (3, 0))
        (.clash (1, 1) (1, 3))
        (.clash (3, 0) (3, 2))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![3, 0, 2, 1]
        (.clash (0, 3) (3, 3))
        (.clash (0, 0) (0, 3))
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (2, 1))
          (.transversal ![1, 2, 0, 3]
            (.clash (0, 1) (0, 3))
            (.clash (2, 0) (2, 3))
            (.clash (0, 1) (2, 1))
            (.motif 1 2 0 0 2 1
              (.clash (0, 1) (0, 3)))
            (.clash (0, 3) (3, 3))
            (.clash (1, 0) (2, 0)))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (0, 3))
            (.clash (1, 3) (2, 3))
            (.clash (3, 0) (3, 2))
            (.clash (0, 3) (2, 3))
            (.clash (3, 0) (3, 1))
            (.reuse 0))
          (.clash (2, 1) (2, 3))
          (.clash (1, 0) (1, 3))
          (.clash (1, 3) (2, 3)))
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 2))
        (.clash (1, 1) (1, 2)))
      (.clash (1, 1) (2, 1)))
    (.clash (3, 2) (3, 3))
private theorem check80 : check [state79] state80 certificate80 = true := by
  decide +kernel
private theorem closed80 : Closed.{u} state80 :=
  sound (known := [state79]) ⟨closed79.{u}, trivial⟩ check80

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary04 : Known.{u} [state72, state73, state74, state75, state77, state78, state80] :=
  ⟨closed72.{u}, ⟨closed73.{u}, ⟨closed74.{u}, ⟨closed75.{u}, ⟨closed77.{u}, ⟨closed78.{u}, ⟨closed80.{u}, trivial⟩⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
