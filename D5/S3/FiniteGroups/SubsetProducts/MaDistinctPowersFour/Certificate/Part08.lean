/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part08
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part08
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 139 through 156. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part05
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part07

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed98 : Closed.{u} state98 :=
  known_of_mem boundary05.{u} (by decide)

private theorem closed135 : Closed.{u} state135 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed136 : Closed.{u} state136 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed137 : Closed.{u} state137 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed138 : Closed.{u} state138 :=
  known_of_mem boundary07.{u} (by decide)

private def state139 : Partition := #v[9, 1, 2, 3, 4, 2, 9, 7, 8, 9, 10, 2, 2, 10, 14, 9]
private def certificate139 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.motif 0 1 2 1 2 0
      (.clash (2, 0) (2, 3)))
    (.clash (0, 1) (3, 1))
    (.clash (0, 0) (0, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (0, 2))
      (.transversal ![1, 3, 2, 0]
        (.transversal ![2, 3, 0, 1]
          (.clash (0, 1) (0, 2))
          (.clash (2, 0) (2, 3))
          (.clash (0, 2) (2, 2))
          (.transversal ![3, 0, 1, 2]
            (.columns)
            (.clash (0, 0) (0, 3))
            (.clash (0, 1) (0, 3))
            (.clash (0, 0) (1, 0))
            (.clash (0, 1) (3, 1))
            (.clash (0, 0) (0, 1)))
          (.clash (0, 1) (3, 1))
          (.clash (1, 0) (2, 0)))
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (0, 2))
        (.clash (1, 0) (1, 3))
        (.clash (1, 1) (1, 3))
        (.clash (0, 2) (2, 2)))
      (.clash (0, 2) (2, 2))
      (.clash (2, 2) (3, 2))
      (.clash (0, 2) (3, 2)))
    (.clash (0, 0) (1, 0))
    (.clash (1, 2) (2, 2))
private theorem check139 : check [] state139 certificate139 = true := by
  decide +kernel
private theorem closed139 : Closed.{u} state139 :=
  sound (known := []) trivial check139

private def state140 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 2, 9, 10, 5, 5, 13, 14, 0]
private def certificate140 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.clash (0, 3) (2, 3))
    (.clash (0, 2) (0, 3))
    (.transversal ![3, 2, 0, 1]
      (.clash (0, 0) (0, 3))
      (.clash (0, 2) (0, 3))
      (.clash (3, 1) (3, 2))
      (.clash (0, 0) (0, 2))
      (.clash (3, 1) (3, 3))
      (.transversal ![0, 3, 2, 1]
        (.clash (1, 2) (1, 3))
        (.clash (1, 2) (2, 2))
        (.clash (0, 0) (0, 2))
        (.transversal ![2, 3, 1, 0]
          (.clash (0, 2) (2, 2))
          (.clash (2, 0) (2, 1))
          (.clash (1, 1) (3, 1))
          (.clash (2, 1) (2, 2))
          (.clash (1, 1) (1, 3))
          (.clash (1, 1) (2, 1)))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (0, 2))
          (.transversal ![0, 3, 1, 2]
            (.clash (0, 0) (0, 2))
            (.motif 0 2 3 1 0 2
              (.clash (0, 0) (0, 3)))
            (.clash (0, 0) (0, 3))
            (.clash (2, 0) (2, 1))
            (.clash (0, 2) (0, 3))
            (.transversal ![2, 0, 1, 3]
              (.clash (1, 0) (1, 3))
              (.clash (0, 2) (0, 3))
              (.clash (0, 0) (0, 2))
              (.motif 0 1 2 0 3 2
                (.clash (0, 1) (0, 3)))
              (.clash (0, 0) (1, 0))
              (.clash (0, 0) (0, 3))))
          (.clash (0, 1) (1, 1))
          (.clash (0, 2) (2, 2))
          (.clash (1, 1) (1, 3))
          (.clash (2, 2) (2, 3)))
        (.clash (0, 2) (2, 2))))
    (.clash (2, 0) (2, 3))
    (.clash (3, 0) (3, 2))
    (.clash (0, 2) (3, 2))
private theorem check140 : check [] state140 certificate140 = true := by
  decide +kernel
private theorem closed140 : Closed.{u} state140 :=
  sound (known := []) trivial check140

private def state141 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 5, 5, 13, 14, 0]
private def certificate141 : Certificate :=
  .transversal ![2, 1, 0, 3]
    (.transversal ![2, 0, 1, 3]
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (2, 1))
      (.clash (0, 0) (0, 2))
      (.transversal ![1, 0, 2, 3]
        (.clash (0, 1) (2, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (2, 1))
          (.clash (0, 1) (0, 2))
          (.clash (2, 2) (3, 2))
          (.clash (1, 0) (1, 1))
          (.transversal ![3, 2, 1, 0]
            (.clash (0, 0) (0, 3))
            (.motif 0 2 1 1 3 2
              (.clash (0, 0) (0, 3)))
            (.clash (0, 2) (0, 3))
            (.clash (0, 0) (1, 0))
            (.clash (0, 0) (0, 2))
            (.clash (0, 2) (3, 2)))
          (.clash (0, 2) (3, 2)))
        (.clash (0, 0) (0, 1))
        (.clash (2, 1) (2, 2))
        (.clash (0, 0) (1, 0))
        (.clash (1, 2) (2, 2)))
      (.clash (0, 0) (1, 0))
      (.transversal ![0, 3, 2, 1]
        (.clash (1, 2) (1, 3))
        (.clash (1, 2) (2, 2))
        (.clash (2, 1) (3, 1))
        (.motif 1 2 3 3 1 2
          (.clash (0, 2) (3, 2)))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (3, 1))
          (.reuse 0)
          (.clash (0, 1) (0, 2))
          (.reuse 1)
          (.clash (1, 1) (1, 3))
          (.clash (0, 2) (2, 2)))
        (.reuse 2)))
    (.reuse 3)
    (.clash (0, 0) (0, 2))
    (.clash (2, 0) (2, 3))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (2, 0))
private theorem check141 : check [state137, state138, state139, state140] state141 certificate141 = true := by
  decide +kernel
private theorem closed141 : Closed.{u} state141 :=
  sound (known := [state137, state138, state139, state140]) ⟨closed137.{u}, ⟨closed138.{u}, ⟨closed139.{u}, ⟨closed140.{u}, trivial⟩⟩⟩⟩ check141

private def state142 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 1, 6, 0, 1, 2, 12, 6, 4, 0]
private def certificate142 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (0, 2))
    (.transversal ![3, 2, 1, 0]
      (.motif 0 1 2 2 3 1
        (.clash (0, 0) (0, 3)))
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (2, 0))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1)))
    (.clash (0, 2) (1, 2))
    (.clash (2, 0) (3, 0))
    (.motif 1 3 0 2 0 1
      (.clash (1, 0) (1, 3)))
private theorem check142 : check [] state142 certificate142 = true := by
  decide +kernel
private theorem closed142 : Closed.{u} state142 :=
  sound (known := []) trivial check142

private def state143 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 7, 5, 12, 6, 9, 0]
private def certificate143 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 3, 0, 2]
      (.clash (1, 0) (1, 3))
      (.clash (1, 0) (2, 0))
      (.clash (0, 1) (2, 1))
      (.clash (2, 0) (2, 2))
      (.clash (2, 1) (2, 2))
      (.clash (2, 0) (2, 1)))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 3))
      (.clash (0, 1) (1, 1))
      (.clash (0, 1) (2, 1))
      (.clash (1, 0) (1, 1))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 2))
        (.clash (0, 0) (0, 1))
        (.transversal ![2, 0, 3, 1]
          (.clash (0, 2) (3, 2))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (3, 1))
            (.clash (0, 1) (0, 2))
            (.motif 2 3 0 1 0 2
              (.clash (0, 2) (1, 2)))
            (.clash (0, 2) (1, 2))
            (.clash (2, 0) (3, 0))
            (.motif 1 3 0 2 0 1
              (.clash (0, 1) (2, 1))))
          (.clash (0, 2) (1, 2))
          (.clash (1, 0) (1, 1))
          (.clash (1, 0) (1, 2))
          (.clash (1, 1) (1, 2)))
        (.clash (3, 1) (3, 3))
        (.clash (0, 0) (2, 0)))
      (.clash (1, 1) (2, 1)))
    (.clash (0, 0) (0, 1))
    (.clash (1, 0) (1, 3))
    (.clash (0, 0) (1, 0))
    (.clash (1, 3) (3, 3))
private theorem check143 : check [] state143 certificate143 = true := by
  decide +kernel
private theorem closed143 : Closed.{u} state143 :=
  sound (known := []) trivial check143

private def state144 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 7, 5, 12, 6, 14, 0]
private def certificate144 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 3) (3, 3))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (1, 1))
          (.clash (1, 0) (3, 0))
          (.clash (1, 1) (1, 2))
          (.clash (2, 0) (3, 0))
          (.motif 2 3 0 0 3 1
            (.clash (0, 1) (1, 1))))
        (.clash (2, 1) (3, 1))
        (.clash (0, 0) (2, 0)))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 2))
        (.clash (0, 0) (0, 1))
        (.transversal ![2, 1, 0, 3]
          (.transversal ![1, 0, 3, 2]
            (.clash (1, 0) (1, 3))
            (.clash (0, 1) (0, 2))
            (.clash (2, 2) (3, 2))
            (.clash (1, 0) (1, 1))
            (.reuse 0)
            (.clash (0, 2) (3, 2)))
          (.clash (0, 2) (1, 2))
          (.clash (0, 0) (0, 2))
          (.clash (1, 1) (1, 2))
          (.clash (1, 1) (2, 1))
          (.clash (0, 0) (2, 0)))
        (.clash (2, 1) (3, 1))
        (.clash (0, 0) (2, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (1, 3))
      (.clash (0, 0) (1, 0))
      (.clash (1, 3) (3, 3)))
    (.clash (3, 2) (3, 3))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (3, 2))
    (.reuse 1)
private theorem check144 : check [state142, state143] state144 certificate144 = true := by
  decide +kernel
private theorem closed144 : Closed.{u} state144 :=
  sound (known := [state142, state143]) ⟨closed142.{u}, ⟨closed143.{u}, trivial⟩⟩ check144

private def state145 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 5, 12, 6, 14, 0]
private def certificate145 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 3) (3, 3))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 1) (3, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (3, 0))
        (.clash (1, 1) (1, 2))
        (.clash (3, 0) (3, 1))
        (.transversal ![1, 3, 2, 0]
          (.transversal ![2, 1, 0, 3]
            (.transversal ![2, 0, 1, 3]
              (.clash (1, 0) (1, 1))
              (.clash (1, 1) (2, 1))
              (.clash (0, 0) (0, 2))
              (.motif 1 2 3 0 3 1
                (.clash (0, 1) (3, 1)))
              (.clash (0, 0) (1, 0))
              (.clash (2, 1) (2, 2)))
            (.clash (0, 1) (0, 2))
            (.clash (0, 0) (0, 2))
            (.clash (0, 1) (1, 1))
            (.clash (0, 0) (3, 0))
            (.clash (0, 0) (0, 1)))
          (.clash (0, 0) (0, 1))
          (.clash (0, 1) (1, 1))
          (.clash (1, 3) (3, 3))
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (3, 0))))
      (.clash (0, 0) (0, 1))
      (.transversal ![2, 1, 0, 3]
        (.reuse 0)
        (.clash (0, 2) (1, 2))
        (.clash (0, 0) (0, 2))
        (.clash (1, 1) (1, 2))
        (.clash (2, 2) (2, 3))
        (.clash (0, 0) (2, 0)))
      (.clash (1, 2) (2, 2))
      (.clash (0, 0) (2, 0)))
    (.clash (3, 1) (3, 3))
    (.reuse 1)
    (.clash (1, 2) (1, 3))
    (.clash (1, 2) (2, 2))
private theorem check145 : check [state98, state144] state145 certificate145 = true := by
  decide +kernel
private theorem closed145 : Closed.{u} state145 :=
  sound (known := [state98, state144]) ⟨closed98.{u}, ⟨closed144.{u}, trivial⟩⟩ check145

def state146 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 5, 12, 13, 14, 0]
private def certificate146 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.transversal ![1, 2, 3, 0]
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (1, 1))
      (.transversal ![1, 0, 2, 3]
        (.clash (1, 0) (3, 0))
        (.transversal ![0, 3, 2, 1]
          (.clash (1, 2) (1, 3))
          (.clash (0, 0) (0, 1))
          (.clash (3, 1) (3, 3))
          (.transversal ![0, 3, 1, 2]
            (.clash (0, 0) (0, 1))
            (.motif 1 2 0 1 2 3
              (.clash (0, 0) (0, 3)))
            (.clash (1, 2) (3, 2))
            (.clash (0, 1) (2, 1))
            (.clash (2, 2) (3, 2))
            (.transversal ![1, 0, 3, 2]
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (1, 1))
              (.clash (0, 1) (2, 1))
              (.clash (1, 0) (1, 1))
              (.motif 1 3 0 0 3 2
                (.clash (0, 1) (0, 2)))
              (.clash (1, 1) (2, 1))))
          (.transversal ![3, 0, 2, 1]
            (.reuse 0)
            (.clash (0, 1) (0, 3))
            (.clash (0, 3) (1, 3))
            (.clash (1, 0) (3, 0))
            (.clash (1, 0) (1, 3))
            (.clash (0, 1) (3, 1)))
          (.clash (0, 1) (3, 1)))
        (.clash (0, 0) (0, 1))
        (.reuse 1)
        (.clash (0, 0) (1, 0))
        (.clash (1, 2) (2, 2)))
      (.clash (1, 1) (1, 2))
      (.clash (0, 0) (3, 0))
      (.reuse 2))
    (.clash (2, 3) (3, 3))
    (.clash (3, 1) (3, 3))
    (.clash (1, 1) (1, 2))
    (.reuse 3)
    (.clash (1, 1) (3, 1))
private theorem check146 : check [state135, state136, state141, state145] state146 certificate146 = true := by
  decide +kernel
private theorem closed146 : Closed.{u} state146 :=
  sound (known := [state135, state136, state141, state145]) ⟨closed135.{u}, ⟨closed136.{u}, ⟨closed141.{u}, ⟨closed145.{u}, trivial⟩⟩⟩⟩ check146

def state147 : Partition := #v[0, 1, 7, 3, 4, 5, 1, 7, 7, 0, 4, 11, 1, 11, 5, 0]
private def certificate147 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (0, 0) (0, 2))
    (.clash (0, 0) (1, 0))
    (.clash (2, 1) (2, 3))
    (.clash (0, 2) (2, 2))
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
private theorem check147 : check [] state147 certificate147 = true := by
  decide +kernel
private theorem closed147 : Closed.{u} state147 :=
  sound (known := []) trivial check147

private def state148 : Partition := #v[6, 1, 7, 3, 4, 5, 6, 7, 7, 6, 10, 11, 12, 10, 5, 6]
private def certificate148 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (3, 1))
    (.transversal ![1, 0, 2, 3]
      (.clash (1, 0) (3, 0))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.transversal ![3, 2, 0, 1]
        (.clash (0, 0) (0, 3))
        (.clash (0, 2) (0, 3))
        (.motif 0 1 2 2 0 3
          (.clash (2, 1) (2, 3)))
        (.clash (0, 0) (0, 2))
        (.clash (0, 0) (1, 0))
        (.clash (0, 2) (2, 2)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 2) (2, 2)))
    (.clash (0, 2) (2, 2))
    (.clash (2, 0) (3, 0))
    (.clash (3, 0) (3, 1))
private theorem check148 : check [] state148 certificate148 = true := by
  decide +kernel
private theorem closed148 : Closed.{u} state148 :=
  sound (known := []) trivial check148

def state149 : Partition := #v[6, 1, 2, 3, 4, 5, 6, 7, 2, 6, 10, 11, 12, 13, 5, 6]
private def certificate149 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.transversal ![2, 3, 1, 0]
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (0, 2))
      (.clash (2, 0) (3, 0))
      (.clash (0, 0) (0, 1))
      (.transversal ![2, 1, 3, 0]
        (.clash (0, 2) (3, 2))
        (.clash (2, 0) (2, 3))
        (.clash (0, 1) (0, 2))
        (.transversal ![3, 0, 1, 2]
          (.transversal ![0, 3, 2, 1]
            (.clash (0, 0) (0, 1))
            (.clash (1, 2) (2, 2))
            (.clash (2, 1) (3, 1))
            (.motif 0 2 1 2 1 0
              (.clash (0, 1) (0, 3)))
            (.clash (0, 1) (3, 1))
            (.motif 2 3 1 1 2 3
              (.clash (0, 1) (3, 1))))
          (.clash (0, 0) (0, 3))
          (.clash (0, 3) (2, 3))
          (.clash (0, 0) (1, 0))
          (.clash (1, 0) (1, 1))
          (.clash (1, 1) (1, 2)))
        (.clash (0, 1) (1, 1))
        (.clash (1, 3) (2, 3)))
      (.clash (0, 0) (3, 0)))
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (1, 1))
    (.transversal ![0, 3, 2, 1]
      (.clash (0, 0) (0, 2))
      (.clash (1, 2) (2, 2))
      (.clash (2, 1) (3, 1))
      (.clash (0, 2) (2, 2))
      (.motif 1 3 2 1 3 2
        (.clash (0, 2) (2, 2)))
      (.reuse 0))
    (.clash (1, 1) (1, 3))
    (.clash (0, 2) (3, 2))
private theorem check149 : check [state148] state149 certificate149 = true := by
  decide +kernel
private theorem closed149 : Closed.{u} state149 :=
  sound (known := [state148]) ⟨closed148.{u}, trivial⟩ check149

private def state150 : Partition := #v[0, 1, 2, 3, 4, 5, 1, 7, 5, 0, 4, 1, 12, 4, 5, 0]
private def certificate150 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 1) (0, 2))
      (.clash (0, 1) (3, 1))
      (.motif 1 3 0 1 0 2
        (.clash (0, 2) (2, 2)))
      (.clash (0, 2) (2, 2))
      (.transversal ![3, 2, 1, 0]
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 2)))
      (.clash (1, 0) (3, 0)))
    (.clash (0, 2) (3, 2))
    (.clash (0, 2) (2, 2))
    (.clash (1, 1) (1, 3))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (1, 1))
private theorem check150 : check [] state150 certificate150 = true := by
  decide +kernel
private theorem closed150 : Closed.{u} state150 :=
  sound (known := []) trivial check150

private def state151 : Partition := #v[6, 1, 2, 3, 4, 3, 6, 1, 3, 6, 1, 4, 12, 13, 3, 6]
private def certificate151 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 0) (0, 1))
    (.clash (1, 0) (1, 3))
    (.transversal ![2, 1, 3, 0]
      (.clash (0, 2) (0, 3))
      (.transversal ![2, 3, 0, 1]
        (.clash (0, 1) (0, 2))
        (.clash (0, 2) (0, 3))
        (.columns)
        (.clash (0, 1) (0, 3))
        (.clash (0, 1) (3, 1))
        (.clash (1, 1) (3, 1)))
      (.clash (0, 1) (0, 2))
      (.clash (0, 3) (2, 3))
      (.clash (0, 1) (0, 3))
      (.clash (1, 0) (1, 3)))
    (.clash (0, 0) (1, 0))
    (.clash (0, 0) (3, 0))
    (.clash (1, 0) (3, 0))
private theorem check151 : check [] state151 certificate151 = true := by
  decide +kernel
private theorem closed151 : Closed.{u} state151 :=
  sound (known := []) trivial check151

private def state152 : Partition := #v[6, 1, 2, 3, 4, 3, 6, 7, 3, 6, 10, 11, 12, 7, 3, 6]
private def certificate152 : Certificate :=
  .motif 1 3 0 3 2 1
    (.clash (0, 0) (0, 1))
private theorem check152 : check [] state152 certificate152 = true := by
  decide +kernel
private theorem closed152 : Closed.{u} state152 :=
  sound (known := []) trivial check152

private def state153 : Partition := #v[6, 1, 2, 3, 4, 3, 6, 7, 3, 6, 10, 11, 12, 10, 3, 6]
private def certificate153 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 2, 3, 0]
      (.clash (0, 0) (0, 1))
      (.motif 0 2 1 1 0 3
        (.clash (1, 2) (1, 3)))
      (.clash (1, 0) (3, 0))
      (.clash (2, 1) (2, 3))
      (.clash (0, 0) (3, 0))
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 0) (1, 3))
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (3, 0))
        (.motif 1 3 0 3 2 1
          (.clash (0, 0) (0, 1)))
        (.clash (1, 3) (2, 3))
        (.clash (2, 2) (2, 3))))
    (.clash (0, 1) (3, 1))
    (.clash (0, 0) (0, 1))
    (.motif 1 2 0 0 1 2
      (.clash (0, 2) (0, 3)))
    (.clash (0, 0) (1, 0))
    (.clash (1, 2) (2, 2))
private theorem check153 : check [] state153 certificate153 = true := by
  decide +kernel
private theorem closed153 : Closed.{u} state153 :=
  sound (known := []) trivial check153

private def state154 : Partition := #v[6, 1, 2, 3, 4, 5, 6, 7, 5, 6, 10, 11, 12, 13, 5, 6]
private def certificate154 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.transversal ![1, 0, 3, 2]
      (.clash (0, 1) (0, 3))
      (.transversal ![1, 0, 2, 3]
        (.clash (0, 1) (0, 3))
        (.clash (2, 2) (2, 3))
        (.clash (0, 0) (0, 1))
        (.motif 1 2 0 0 1 2
          (.clash (0, 2) (3, 2)))
        (.clash (0, 0) (0, 3))
        (.clash (1, 2) (2, 2)))
      (.clash (0, 1) (1, 1))
      (.clash (0, 3) (2, 3))
      (.clash (1, 0) (1, 1))
      (.clash (2, 0) (2, 3)))
    (.clash (0, 0) (0, 3))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 2) (1, 3))
      (.clash (1, 2) (2, 2))
      (.clash (2, 1) (3, 1))
      (.transversal ![1, 0, 2, 3]
        (.transversal ![3, 0, 2, 1]
          (.clash (0, 1) (0, 3))
          (.clash (0, 3) (1, 3))
          (.clash (1, 1) (3, 1))
          (.clash (1, 0) (1, 3))
          (.clash (0, 1) (3, 1))
          (.motif 1 3 0 3 2 1
            (.clash (0, 0) (0, 1))))
        (.transversal ![1, 0, 3, 2]
          (.clash (1, 0) (1, 3))
          (.clash (1, 3) (2, 3))
          (.clash (0, 1) (0, 3))
          (.reuse 0)
          (.clash (1, 0) (1, 1))
          (.clash (0, 3) (2, 3)))
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (1, 3))
        (.clash (0, 0) (1, 0))
        (.clash (1, 2) (1, 3)))
      (.reuse 1)
      (.reuse 2))
    (.clash (0, 0) (1, 0))
    (.clash (1, 0) (1, 1))
    (.clash (0, 0) (2, 0))
private theorem check154 : check [state151, state152, state153] state154 certificate154 = true := by
  decide +kernel
private theorem closed154 : Closed.{u} state154 :=
  sound (known := [state151, state152, state153]) ⟨closed151.{u}, ⟨closed152.{u}, ⟨closed153.{u}, trivial⟩⟩⟩ check154

def state155 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 5, 0, 10, 11, 12, 13, 5, 0]
private def certificate155 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.transversal ![1, 0, 2, 3]
      (.clash (1, 0) (1, 2))
      (.clash (1, 2) (2, 2))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 0, 3, 2]
        (.clash (1, 0) (1, 2))
        (.transversal ![0, 3, 2, 1]
          (.clash (1, 3) (3, 3))
          (.clash (0, 0) (1, 0))
          (.clash (2, 1) (3, 1))
          (.clash (1, 0) (1, 3))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (3, 1))
            (.clash (1, 0) (1, 2))
            (.transversal ![2, 0, 3, 1]
              (.clash (0, 2) (2, 2))
              (.clash (0, 1) (0, 2))
              (.transversal ![3, 2, 0, 1]
                (.clash (0, 1) (0, 3))
                (.motif 0 1 2 3 2 1
                  (.clash (0, 0) (0, 2)))
                (.clash (0, 2) (0, 3))
                (.clash (0, 1) (1, 1))
                (.clash (0, 1) (0, 2))
                (.clash (0, 2) (3, 2)))
              (.clash (1, 0) (1, 2))
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (3, 1)))
            (.clash (1, 0) (1, 3))
            (.clash (3, 0) (3, 1))
            (.clash (1, 0) (3, 0)))
          (.reuse 0))
        (.clash (0, 1) (1, 1))
        (.clash (2, 2) (2, 3))
        (.clash (1, 0) (1, 1))
        (.clash (2, 0) (2, 3)))
      (.clash (0, 0) (1, 0))
      (.clash (2, 1) (2, 2)))
    (.clash (0, 1) (1, 1))
    (.clash (0, 0) (0, 1))
    (.clash (1, 1) (1, 2))
    (.reuse 1)
    (.clash (0, 0) (2, 0))
private theorem check155 : check [state150, state154] state155 certificate155 = true := by
  decide +kernel
private theorem closed155 : Closed.{u} state155 :=
  sound (known := [state150, state154]) ⟨closed150.{u}, ⟨closed154.{u}, trivial⟩⟩ check155

def state156 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 2, 5, 2, 4, 1, 12, 4, 5, 0]
private def certificate156 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (3, 1))
    (.transversal ![3, 2, 1, 0]
      (.clash (0, 0) (0, 3))
      (.clash (0, 2) (0, 3))
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (0, 2))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (0, 2)))
    (.clash (0, 2) (2, 2))
    (.motif 2 3 0 2 0 1
      (.clash (0, 1) (1, 1)))
    (.clash (1, 0) (3, 0))
private theorem check156 : check [] state156 certificate156 = true := by
  decide +kernel
private theorem closed156 : Closed.{u} state156 :=
  sound (known := []) trivial check156

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary08 : Known.{u} [state146, state147, state149, state155, state156] :=
  ⟨closed146.{u}, ⟨closed147.{u}, ⟨closed149.{u}, ⟨closed155.{u}, ⟨closed156.{u}, trivial⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
