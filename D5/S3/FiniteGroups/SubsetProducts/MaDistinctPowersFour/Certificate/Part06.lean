/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part06
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part06
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 100 through 117. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part05

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed90 : Closed.{u} state90 :=
  known_of_mem boundary05.{u} (by decide)

private theorem closed96 : Closed.{u} state96 :=
  known_of_mem boundary05.{u} (by decide)

private theorem closed98 : Closed.{u} state98 :=
  known_of_mem boundary05.{u} (by decide)

private theorem closed99 : Closed.{u} state99 :=
  known_of_mem boundary05.{u} (by decide)

private def state100 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 5, 12, 6, 7, 9]
private def certificate100 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 3, 2, 0]
      (.clash (1, 0) (1, 3))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (3, 0))
      (.clash (2, 2) (3, 2))
      (.clash (3, 0) (3, 2))
      (.clash (0, 0) (3, 0)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (1, 0))
    (.transversal ![1, 0, 3, 2]
      (.clash (0, 1) (2, 1))
      (.clash (0, 1) (1, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (1, 1))
        (.clash (3, 0) (3, 2))
        (.clash (1, 1) (1, 2))
        (.clash (3, 0) (3, 1))
        (.transversal ![3, 0, 2, 1]
          (.clash (0, 3) (3, 3))
          (.clash (0, 0) (0, 3))
          (.transversal ![1, 2, 0, 3]
            (.clash (0, 1) (0, 3))
            (.motif 1 2 0 1 0 3
              (.clash (0, 3) (3, 3)))
            (.clash (0, 1) (2, 1))
            (.motif 2 3 0 3 1 0
              (.clash (0, 0) (1, 0)))
            (.clash (0, 3) (3, 3))
            (.clash (1, 0) (2, 0)))
          (.clash (0, 0) (1, 0))
          (.clash (1, 0) (1, 2))
          (.clash (1, 2) (2, 2))))
      (.clash (1, 0) (1, 1))
      (.clash (1, 0) (1, 3))
      (.clash (1, 1) (1, 3)))
    (.clash (2, 1) (2, 2))
private theorem check100 : check [] state100 certificate100 = true := by
  decide +kernel
private theorem closed100 : Closed.{u} state100 :=
  sound (known := []) trivial check100

private def state101 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 5, 12, 6, 14, 9]
private def certificate101 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (2, 1))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (1, 1))
          (.clash (1, 0) (3, 0))
          (.clash (1, 1) (1, 2))
          (.clash (2, 0) (3, 0))
          (.motif 2 3 1 1 0 3
            (.clash (0, 0) (2, 0))))
        (.clash (2, 1) (3, 1))
        (.clash (2, 0) (2, 1)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![3, 0, 2, 1]
        (.clash (0, 3) (3, 3))
        (.clash (0, 0) (0, 3))
        (.transversal ![3, 1, 2, 0]
          (.clash (0, 3) (2, 3))
          (.clash (0, 0) (0, 3))
          (.clash (3, 0) (3, 1))
          (.clash (1, 1) (1, 3))
          (.transversal ![1, 0, 3, 2]
            (.clash (0, 1) (2, 1))
            (.clash (0, 1) (1, 1))
            (.reuse 0)
            (.clash (1, 0) (1, 1))
            (.clash (3, 2) (3, 3))
            (.clash (3, 0) (3, 2)))
          (.clash (0, 0) (3, 0)))
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 2))
        (.clash (1, 2) (1, 3)))
      (.clash (1, 3) (3, 3)))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (3, 2))
    (.clash (1, 3) (3, 3))
    (.reuse 1)
    (.clash (3, 2) (3, 3))
private theorem check101 : check [state99, state100] state101 certificate101 = true := by
  decide +kernel
private theorem closed101 : Closed.{u} state101 :=
  sound (known := [state99, state100]) ⟨closed99.{u}, ⟨closed100.{u}, trivial⟩⟩ check101

private def state102 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 5, 12, 6, 14, 15]
private def certificate102 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (2, 2))
    (.clash (2, 1) (2, 2))
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
    (.clash (2, 1) (3, 1))
    (.clash (3, 1) (3, 3))
    (.reuse 1)
private theorem check102 : check [state98, state101] state102 certificate102 = true := by
  decide +kernel
private theorem closed102 : Closed.{u} state102 :=
  sound (known := [state98, state101]) ⟨closed98.{u}, ⟨closed101.{u}, trivial⟩⟩ check102

def state103 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 5, 12, 13, 14, 15]
private def certificate103 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 2) (2, 2))
    (.clash (2, 2) (2, 3))
    (.transversal ![2, 0, 3, 1]
      (.transversal ![1, 0, 2, 3]
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (0, 2))
          (.clash (0, 1) (1, 1))
          (.clash (3, 2) (3, 3))
          (.clash (1, 0) (1, 1))
          (.clash (0, 2) (3, 2))
          (.transversal ![2, 1, 0, 3]
            (.clash (0, 2) (3, 2))
            (.clash (1, 0) (2, 0))
            (.clash (0, 1) (0, 2))
            (.clash (2, 0) (2, 3))
            (.clash (0, 1) (1, 1))
            (.transversal ![2, 3, 0, 1]
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (0, 2))
              (.clash (0, 0) (0, 2))
              (.clash (1, 3) (3, 3))
              (.transversal ![3, 1, 2, 0]
                (.clash (0, 3) (2, 3))
                (.clash (0, 0) (0, 3))
                (.motif 0 3 1 3 1 0
                  (.clash (0, 1) (0, 2)))
                (.clash (1, 1) (1, 3))
                (.clash (3, 0) (3, 2))
                (.clash (0, 0) (3, 0)))
              (.clash (0, 0) (0, 1)))))
        (.clash (0, 0) (0, 2))
        (.reuse 0)
        (.clash (3, 1) (3, 3)))
      (.reuse 1)
      (.clash (0, 0) (0, 2))
      (.clash (1, 0) (1, 1))
      (.clash (0, 0) (1, 0))
      (.clash (1, 1) (3, 1)))
    (.clash (1, 1) (1, 2))
    (.reuse 2)
    (.clash (1, 1) (3, 1))
private theorem check103 : check [state90, state96, state102] state103 certificate103 = true := by
  decide +kernel
private theorem closed103 : Closed.{u} state103 :=
  sound (known := [state90, state96, state102]) ⟨closed90.{u}, ⟨closed96.{u}, ⟨closed102.{u}, trivial⟩⟩⟩ check103

def state104 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 0, 1, 6, 0, 11, 6, 0, 5, 1]
private def certificate104 : Certificate :=
  .transversal ![3, 2, 0, 1]
    (.motif 0 1 2 2 3 0
      (.clash (0, 1) (0, 3)))
    (.clash (0, 1) (0, 3))
    (.clash (0, 0) (0, 3))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (0, 1))
private theorem check104 : check [] state104 certificate104 = true := by
  decide +kernel
private theorem closed104 : Closed.{u} state104 :=
  sound (known := []) trivial check104

def state105 : Partition := #v[0, 6, 2, 3, 4, 5, 6, 0, 6, 9, 0, 11, 12, 13, 5, 6]
private def certificate105 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (0, 0) (0, 1))
    (.clash (1, 3) (2, 3))
    (.motif 1 3 0 1 3 2
      (.clash (0, 0) (0, 2)))
    (.clash (2, 0) (2, 3))
    (.clash (0, 1) (3, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 2))
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (1, 1))
      (.motif 1 2 0 0 2 3
        (.clash (0, 1) (0, 3)))
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (3, 1)))
private theorem check105 : check [] state105 certificate105 = true := by
  decide +kernel
private theorem closed105 : Closed.{u} state105 :=
  sound (known := []) trivial check105

def state106 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 1, 9, 0, 11, 12, 13, 5, 4]
private def certificate106 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (1, 0) (2, 0))
    (.clash (2, 0) (2, 3))
    (.clash (0, 1) (1, 1))
    (.clash (2, 3) (3, 3))
    (.clash (1, 0) (1, 1))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 2) (3, 2))
      (.clash (0, 1) (0, 2))
      (.transversal ![2, 3, 0, 1]
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2))
        (.clash (3, 1) (3, 3))
        (.clash (0, 0) (0, 1))
        (.transversal ![3, 1, 2, 0]
          (.clash (0, 3) (2, 3))
          (.clash (0, 0) (0, 3))
          (.transversal ![0, 2, 1, 3]
            (.clash (1, 2) (1, 3))
            (.clash (2, 1) (2, 2))
            (.clash (0, 0) (0, 2))
            (.motif 1 2 3 1 2 3
              (.clash (0, 2) (1, 2)))
            (.clash (0, 2) (1, 2))
            (.motif 0 2 3 1 2 0
              (.clash (0, 2) (0, 3))))
          (.clash (1, 1) (1, 3))
          (.clash (3, 0) (3, 2))
          (.clash (0, 0) (3, 0)))
        (.clash (0, 1) (3, 1)))
      (.clash (0, 1) (1, 1))
      (.clash (1, 0) (1, 1))
      (.clash (1, 0) (2, 0)))
private theorem check106 : check [] state106 certificate106 = true := by
  decide +kernel
private theorem closed106 : Closed.{u} state106 :=
  sound (known := []) trivial check106

private def state107 : Partition := #v[0, 1, 2, 3, 4, 8, 6, 0, 8, 9, 0, 2, 9, 2, 8, 6]
private def certificate107 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 2))
      (.clash (0, 1) (0, 2))
      (.clash (0, 1) (1, 1))
      (.transversal ![3, 2, 0, 1]
        (.clash (0, 1) (0, 3))
        (.motif 0 2 1 0 3 2
          (.clash (0, 1) (0, 3)))
        (.clash (0, 2) (0, 3))
        (.clash (0, 1) (1, 1))
        (.clash (0, 1) (0, 2))
        (.clash (0, 2) (3, 2)))
      (.clash (1, 0) (1, 1))
      (.clash (0, 2) (3, 2)))
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (2, 1))
    (.clash (0, 2) (1, 2))
    (.clash (3, 0) (3, 3))
    (.clash (2, 1) (2, 3))
private theorem check107 : check [] state107 certificate107 = true := by
  decide +kernel
private theorem closed107 : Closed.{u} state107 :=
  sound (known := []) trivial check107

private def state108 : Partition := #v[0, 1, 2, 3, 4, 3, 6, 0, 3, 4, 0, 11, 12, 0, 3, 4]
private def certificate108 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (0, 1) (2, 1))
    (.transversal ![1, 2, 0, 3]
      (.transversal ![2, 0, 3, 1]
        (.transversal ![2, 1, 3, 0]
          (.clash (0, 2) (0, 3))
          (.clash (0, 1) (0, 2))
          (.clash (1, 0) (3, 0))
          (.clash (0, 1) (0, 3))
          (.clash (2, 0) (3, 0))
          (.columns))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (1, 0))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 1) (0, 3))
      (.clash (0, 1) (2, 1))
      (.clash (1, 1) (1, 2))
      (.clash (1, 0) (1, 2))
      (.clash (0, 3) (3, 3)))
    (.clash (0, 1) (0, 3))
    (.clash (2, 1) (2, 3))
    (.clash (0, 3) (3, 3))
    (.clash (0, 3) (2, 3))
private theorem check108 : check [] state108 certificate108 = true := by
  decide +kernel
private theorem closed108 : Closed.{u} state108 :=
  sound (known := []) trivial check108

private def state109 : Partition := #v[0, 1, 2, 3, 4, 8, 6, 0, 8, 9, 0, 11, 3, 0, 8, 15]
private def certificate109 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 2) (3, 2))
    (.transversal ![2, 3, 1, 0]
      (.clash (0, 0) (0, 2))
      (.clash (2, 1) (2, 3))
      (.clash (0, 2) (0, 3))
      (.clash (2, 1) (2, 2))
      (.clash (0, 0) (0, 3))
      (.motif 2 3 0 0 1 2
        (.clash (0, 2) (0, 3))))
    (.clash (0, 2) (0, 3))
    (.clash (2, 0) (2, 3))
    (.clash (2, 0) (3, 0))
    (.clash (0, 3) (2, 3))
private theorem check109 : check [] state109 certificate109 = true := by
  decide +kernel
private theorem closed109 : Closed.{u} state109 :=
  sound (known := []) trivial check109

private def state110 : Partition := #v[0, 1, 2, 3, 4, 8, 6, 0, 8, 9, 0, 11, 12, 0, 8, 15]
private def certificate110 : Certificate :=
  .transversal ![3, 1, 2, 0]
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 2) (1, 3))
      (.clash (2, 1) (2, 2))
      (.clash (1, 3) (3, 3))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (2, 1))
        (.clash (0, 1) (0, 3))
        (.transversal ![1, 0, 3, 2]
          (.motif 0 1 2 0 1 3
            (.clash (2, 3) (3, 3)))
          (.clash (2, 3) (3, 3))
          (.clash (0, 1) (0, 3))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (2, 1))
            (.clash (2, 3) (3, 3))
            (.clash (3, 0) (3, 3))
            (.clash (1, 0) (1, 2))
            (.motif 2 3 0 0 1 2
              (.clash (0, 2) (1, 2)))
            (.clash (1, 0) (3, 0)))
          (.clash (1, 0) (1, 1))
          (.clash (0, 3) (2, 3)))
        (.clash (1, 1) (1, 2))
        (.motif 1 3 0 3 2 1
          (.clash (0, 1) (2, 1)))
        (.clash (0, 3) (3, 3)))
      (.motif 1 3 2 2 1 3
        (.clash (0, 3) (2, 3)))
      (.transversal ![1, 0, 2, 3]
        (.motif 0 1 3 1 3 0
          (.clash (2, 0) (3, 0)))
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (1, 0))
        (.reuse 0)
        (.clash (1, 3) (3, 3))))
    (.clash (0, 0) (0, 3))
    (.reuse 1)
    (.clash (0, 0) (2, 0))
    (.clash (2, 0) (3, 0))
    (.clash (0, 0) (3, 0))
private theorem check110 : check [state108, state109] state110 certificate110 = true := by
  decide +kernel
private theorem closed110 : Closed.{u} state110 :=
  sound (known := [state108, state109]) ⟨closed108.{u}, ⟨closed109.{u}, trivial⟩⟩ check110

def state111 : Partition := #v[0, 1, 2, 3, 4, 8, 6, 0, 8, 9, 0, 11, 12, 13, 8, 15]
private def certificate111 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (0, 0) (0, 2))
    (.clash (0, 2) (3, 2))
    (.transversal ![2, 3, 1, 0]
      (.clash (0, 0) (0, 2))
      (.clash (2, 1) (3, 1))
      (.clash (3, 0) (3, 1))
      (.clash (2, 1) (2, 2))
      (.clash (0, 0) (3, 0))
      (.transversal ![2, 1, 3, 0]
        (.clash (0, 2) (3, 2))
        (.transversal ![0, 2, 1, 3]
          (.clash (1, 2) (1, 3))
          (.clash (0, 0) (3, 0))
          (.clash (1, 3) (3, 3))
          (.transversal ![1, 2, 0, 3]
            (.clash (0, 1) (2, 1))
            (.clash (0, 1) (1, 1))
            (.transversal ![1, 0, 3, 2]
              (.transversal ![3, 0, 2, 1]
                (.clash (0, 1) (0, 3))
                (.clash (0, 0) (0, 3))
                (.clash (0, 2) (0, 3))
                (.clash (0, 0) (0, 1))
                (.clash (0, 1) (0, 2))
                (.clash (0, 0) (0, 2)))
              (.clash (0, 1) (0, 2))
              (.clash (0, 1) (1, 1))
              (.motif 1 3 0 2 1 0
                (.clash (0, 0) (2, 0)))
              (.clash (1, 0) (1, 1))
              (.clash (0, 2) (3, 2)))
            (.clash (1, 1) (1, 2))
            (.clash (3, 0) (3, 3))
            (.clash (3, 2) (3, 3)))
          (.reuse 0)
          (.clash (3, 0) (3, 3)))
        (.clash (2, 1) (3, 1))
        (.clash (2, 0) (2, 3))
        (.clash (1, 1) (2, 1))
        (.clash (2, 1) (2, 3))))
    (.clash (0, 0) (2, 0))
    (.reuse 1)
    (.clash (1, 1) (3, 1))
private theorem check111 : check [state107, state110] state111 certificate111 = true := by
  decide +kernel
private theorem closed111 : Closed.{u} state111 :=
  sound (known := [state107, state110]) ⟨closed107.{u}, ⟨closed110.{u}, trivial⟩⟩ check111

def state112 : Partition := #v[0, 1, 2, 3, 4, 8, 1, 2, 8, 2, 0, 1, 2, 13, 8, 0]
private def certificate112 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (0, 2))
    (.clash (2, 1) (3, 1))
    (.clash (1, 0) (1, 2))
    (.transversal ![3, 1, 2, 0]
      (.motif 0 1 2 1 3 2
        (.clash (0, 0) (0, 3)))
      (.clash (0, 0) (0, 3))
      (.clash (0, 2) (0, 3))
      (.clash (0, 0) (2, 0))
      (.clash (0, 2) (3, 2))
      (.clash (0, 0) (0, 2)))
    (.clash (0, 1) (3, 1))
private theorem check112 : check [] state112 certificate112 = true := by
  decide +kernel
private theorem closed112 : Closed.{u} state112 :=
  sound (known := []) trivial check112

def state113 : Partition := #v[0, 1, 2, 3, 4, 8, 1, 7, 8, 7, 0, 11, 12, 11, 8, 0]
private def certificate113 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (1, 0) (1, 2))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (1, 1))
    (.motif 2 1 3 1 0 3
      (.clash (0, 0) (2, 0)))
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (3, 1))
private theorem check113 : check [] state113 certificate113 = true := by
  decide +kernel
private theorem closed113 : Closed.{u} state113 :=
  sound (known := []) trivial check113

private def state114 : Partition := #v[0, 1, 2, 3, 4, 3, 1, 7, 8, 7, 0, 4, 7, 0, 3, 1]
private def certificate114 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (2, 1))
    (.transversal ![2, 3, 0, 1]
      (.motif 0 1 2 1 3 2
        (.clash (0, 0) (0, 3)))
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (0, 2))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (0, 1)))
    (.clash (0, 1) (0, 3))
    (.clash (2, 0) (2, 1))
    (.clash (0, 3) (1, 3))
    (.motif 1 2 0 3 0 1
      (.clash (1, 0) (1, 2)))
private theorem check114 : check [] state114 certificate114 = true := by
  decide +kernel
private theorem closed114 : Closed.{u} state114 :=
  sound (known := []) trivial check114

private def state115 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 0, 11, 12, 11, 5, 6]
private def certificate115 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 2, 3, 0]
      (.clash (1, 0) (1, 2))
      (.clash (0, 1) (3, 1))
      (.clash (1, 0) (3, 0))
      (.clash (2, 3) (3, 3))
      (.clash (3, 0) (3, 3))
      (.clash (3, 0) (3, 1)))
    (.clash (0, 0) (0, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 2))
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (1, 1))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 1))
        (.clash (3, 0) (3, 3))
        (.clash (2, 1) (2, 2))
        (.transversal ![3, 0, 1, 2]
          (.clash (0, 3) (2, 3))
          (.clash (0, 3) (1, 3))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (2, 1))
            (.motif 2 3 0 1 3 0
              (.clash (0, 0) (1, 0)))
            (.clash (0, 1) (0, 3))
            (.clash (2, 0) (2, 1))
            (.clash (0, 3) (1, 3))
            (.motif 1 2 0 3 0 1
              (.clash (0, 1) (3, 1))))
          (.clash (1, 0) (1, 3))
          (.clash (1, 0) (1, 1))
          (.clash (1, 1) (1, 3)))
        (.clash (0, 0) (3, 0)))
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (3, 1)))
    (.clash (0, 0) (1, 0))
    (.clash (1, 0) (1, 2))
    (.clash (1, 2) (2, 2))
private theorem check115 : check [] state115 certificate115 = true := by
  decide +kernel
private theorem closed115 : Closed.{u} state115 :=
  sound (known := []) trivial check115

private def state116 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 0, 11, 12, 13, 5, 6]
private def certificate116 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 2) (2, 2))
    (.clash (2, 2) (2, 3))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 3))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.clash (1, 0) (3, 0))
          (.clash (2, 1) (2, 2))
          (.motif 2 3 1 1 2 0
            (.clash (0, 0) (0, 1)))
          (.clash (0, 0) (3, 0))))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 1))
        (.clash (3, 0) (3, 3))
        (.clash (2, 1) (2, 2))
        (.transversal ![3, 1, 2, 0]
          (.transversal ![1, 0, 3, 2]
            (.clash (1, 0) (1, 2))
            (.clash (2, 3) (3, 3))
            (.clash (0, 1) (0, 3))
            (.reuse 0)
            (.clash (1, 0) (1, 1))
            (.clash (0, 3) (2, 3)))
          (.clash (0, 0) (0, 3))
          (.clash (0, 3) (1, 3))
          (.clash (1, 1) (3, 1))
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (3, 0)))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 2))
      (.clash (1, 2) (2, 2)))
    (.clash (2, 3) (3, 3))
    (.clash (3, 1) (3, 3))
    (.reuse 1)
private theorem check116 : check [state114, state115] state116 certificate116 = true := by
  decide +kernel
private theorem closed116 : Closed.{u} state116 :=
  sound (known := [state114, state115]) ⟨closed114.{u}, ⟨closed115.{u}, trivial⟩⟩ check116

def state117 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 7, 0, 11, 12, 13, 5, 15]
private def certificate117 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (2, 2))
    (.clash (2, 1) (2, 2))
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
    (.clash (1, 2) (1, 3))
    (.reuse 2)
    (.clash (1, 3) (3, 3))
private theorem check117 : check [state112, state113, state116] state117 certificate117 = true := by
  decide +kernel
private theorem closed117 : Closed.{u} state117 :=
  sound (known := [state112, state113, state116]) ⟨closed112.{u}, ⟨closed113.{u}, ⟨closed116.{u}, trivial⟩⟩⟩ check117

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary06 : Known.{u} [state103, state104, state105, state106, state111, state112, state113, state117] :=
  ⟨closed103.{u}, ⟨closed104.{u}, ⟨closed105.{u}, ⟨closed106.{u}, ⟨closed111.{u}, ⟨closed112.{u}, ⟨closed113.{u}, ⟨closed117.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
