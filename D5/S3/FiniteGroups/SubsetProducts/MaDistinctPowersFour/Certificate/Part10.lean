/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part10
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part10
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 176 through 193. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part09

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed175 : Closed.{u} state175 :=
  known_of_mem boundary09.{u} (by decide)

private def state176 : Partition := #v[6, 1, 7, 3, 4, 5, 6, 7, 8, 9, 5, 6, 7, 6, 9, 15]
private def certificate176 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (0, 2))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (2, 0))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![3, 2, 1, 0]
        (.clash (0, 0) (0, 3))
        (.motif 0 1 2 3 2 0
          (.clash (0, 1) (0, 2)))
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (1, 0))
        (.clash (0, 0) (0, 2))
        (.clash (0, 2) (3, 2)))
      (.clash (1, 2) (3, 2)))
    (.clash (0, 1) (2, 1))
    (.clash (2, 0) (3, 0))
    (.clash (0, 2) (3, 2))
    (.clash (2, 0) (2, 1))
private theorem check176 : check [] state176 certificate176 = true := by
  decide +kernel
private theorem closed176 : Closed.{u} state176 :=
  sound (known := []) trivial check176

private def state177 : Partition := #v[6, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 6, 2, 6, 14, 15]
private def certificate177 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 1) (0, 2))
      (.clash (2, 0) (3, 0))
      (.clash (0, 0) (0, 2))
      (.transversal ![2, 1, 0, 3]
        (.clash (0, 2) (2, 2))
        (.clash (0, 1) (0, 2))
        (.clash (3, 0) (3, 3))
        (.clash (0, 1) (1, 1))
        (.transversal ![3, 0, 2, 1]
          (.transversal ![0, 3, 1, 2]
            (.clash (0, 0) (0, 1))
            (.clash (2, 1) (2, 3))
            (.clash (1, 2) (3, 2))
            (.clash (0, 1) (2, 1))
            (.motif 0 3 1 2 1 0
              (.clash (0, 1) (0, 3)))
            (.motif 2 3 1 2 1 3
              (.clash (0, 1) (2, 1))))
          (.clash (0, 3) (3, 3))
          (.clash (0, 0) (0, 3))
          (.clash (1, 0) (1, 1))
          (.clash (0, 0) (1, 0))
          (.clash (1, 1) (1, 2)))
        (.clash (1, 3) (3, 3)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 0) (2, 0)))
    (.clash (0, 1) (1, 1))
    (.clash (0, 1) (0, 2))
    (.clash (1, 1) (1, 3))
    (.transversal ![0, 3, 1, 2]
      (.clash (0, 0) (0, 2))
      (.clash (2, 1) (2, 3))
      (.clash (1, 2) (3, 2))
      (.motif 1 2 3 1 3 2
        (.clash (0, 2) (3, 2)))
      (.clash (0, 2) (3, 2))
      (.reuse 0))
    (.clash (0, 2) (2, 2))
private theorem check177 : check [state176] state177 certificate177 = true := by
  decide +kernel
private theorem closed177 : Closed.{u} state177 :=
  sound (known := [state176]) ⟨closed176.{u}, trivial⟩ check177

private def state178 : Partition := #v[0, 1, 2, 3, 9, 5, 1, 7, 8, 9, 5, 0, 5, 0, 9, 1]
private def certificate178 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 1) (0, 2))
      (.motif 1 2 0 1 0 2
        (.clash (0, 2) (3, 2)))
      (.clash (0, 1) (2, 1))
      (.transversal ![3, 2, 0, 1]
        (.clash (0, 1) (0, 3))
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 1))
        (.clash (0, 0) (0, 2)))
      (.clash (0, 2) (3, 2))
      (.clash (1, 0) (2, 0)))
    (.clash (0, 2) (3, 2))
    (.clash (0, 2) (2, 2))
    (.clash (1, 0) (1, 3))
    (.clash (1, 1) (1, 3))
    (.clash (1, 0) (1, 1))
private theorem check178 : check [] state178 certificate178 = true := by
  decide +kernel
private theorem closed178 : Closed.{u} state178 :=
  sound (known := []) trivial check178

private def state179 : Partition := #v[6, 1, 2, 3, 4, 3, 6, 1, 8, 9, 3, 6, 3, 6, 1, 15]
private def certificate179 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (0, 3))
    (.clash (1, 3) (3, 3))
    (.clash (1, 0) (1, 1))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 0) (0, 1))
      (.transversal ![2, 1, 0, 3]
        (.clash (0, 2) (0, 3))
        (.clash (0, 1) (0, 2))
        (.transversal ![2, 3, 1, 0]
          (.clash (0, 1) (0, 2))
          (.columns)
          (.clash (0, 2) (0, 3))
          (.clash (0, 1) (2, 1))
          (.clash (0, 1) (0, 3))
          (.clash (1, 1) (2, 1)))
        (.clash (0, 1) (0, 3))
        (.clash (0, 3) (3, 3))
        (.clash (1, 0) (1, 3)))
      (.clash (1, 0) (1, 3))
      (.clash (0, 0) (2, 0))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (2, 0)))
    (.clash (0, 3) (3, 3))
private theorem check179 : check [] state179 certificate179 = true := by
  decide +kernel
private theorem closed179 : Closed.{u} state179 :=
  sound (known := []) trivial check179

private def state180 : Partition := #v[6, 1, 2, 3, 4, 3, 6, 7, 8, 9, 3, 6, 3, 6, 9, 15]
private def certificate180 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (2, 0))
      (.motif 0 3 1 1 0 3
        (.clash (1, 2) (1, 3)))
      (.clash (0, 0) (2, 0))
      (.clash (2, 3) (3, 3))
      (.transversal ![1, 3, 0, 2]
        (.clash (1, 0) (1, 3))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (2, 1))
        (.clash (1, 3) (3, 3))
        (.motif 1 2 0 3 2 1
          (.clash (0, 0) (0, 1)))
        (.clash (2, 0) (2, 1))))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (1, 0))
    (.motif 1 3 0 0 1 2
      (.clash (0, 2) (0, 3)))
    (.clash (1, 2) (3, 2))
private theorem check180 : check [] state180 certificate180 = true := by
  decide +kernel
private theorem closed180 : Closed.{u} state180 :=
  sound (known := []) trivial check180

private def state181 : Partition := #v[6, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 6, 5, 6, 14, 15]
private def certificate181 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.transversal ![1, 0, 2, 3]
      (.clash (0, 1) (0, 3))
      (.clash (0, 1) (1, 1))
      (.transversal ![1, 0, 3, 2]
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 1))
        (.clash (3, 2) (3, 3))
        (.clash (0, 0) (0, 3))
        (.motif 1 3 0 0 1 2
          (.clash (0, 2) (2, 2)))
        (.clash (1, 2) (3, 2)))
      (.clash (1, 0) (1, 1))
      (.clash (0, 3) (3, 3))
      (.clash (3, 0) (3, 3)))
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 2) (1, 3))
      (.clash (2, 1) (2, 3))
      (.clash (1, 2) (3, 2))
      (.motif 1 2 0 3 2 1
        (.clash (0, 0) (0, 1)))
      (.transversal ![1, 0, 3, 2]
        (.transversal ![3, 0, 1, 2]
          (.clash (0, 1) (0, 3))
          (.clash (1, 1) (2, 1))
          (.clash (0, 3) (1, 3))
          (.clash (0, 1) (2, 1))
          (.clash (1, 0) (1, 3))
          (.motif 1 2 0 3 2 1
            (.clash (0, 0) (0, 1))))
        (.clash (0, 0) (0, 1))
        (.reuse 0)
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 3))
        (.clash (1, 2) (1, 3)))
      (.reuse 1))
    (.clash (0, 0) (0, 3))
    (.clash (1, 0) (1, 1))
    (.clash (0, 0) (1, 0))
    (.clash (0, 0) (3, 0))
private theorem check181 : check [state179, state180] state181 certificate181 = true := by
  decide +kernel
private theorem closed181 : Closed.{u} state181 :=
  sound (known := [state179, state180]) ⟨closed179.{u}, ⟨closed180.{u}, trivial⟩⟩ check181

private def state182 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 0, 5, 0, 14, 15]
private def certificate182 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (0, 1))
      (.clash (1, 2) (3, 2))
      (.clash (0, 0) (1, 0))
      (.transversal ![1, 0, 2, 3]
        (.clash (1, 0) (1, 2))
        (.clash (0, 1) (1, 1))
        (.transversal ![0, 3, 1, 2]
          (.clash (1, 3) (2, 3))
          (.clash (2, 1) (2, 3))
          (.clash (0, 0) (1, 0))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (2, 1))
            (.transversal ![2, 0, 1, 3]
              (.clash (0, 2) (3, 2))
              (.transversal ![3, 2, 1, 0]
                (.clash (0, 1) (0, 3))
                (.clash (0, 2) (0, 3))
                (.motif 0 1 2 2 1 3
                  (.clash (0, 0) (0, 1)))
                (.clash (0, 1) (0, 2))
                (.clash (0, 1) (1, 1))
                (.clash (0, 2) (2, 2)))
              (.clash (0, 1) (0, 2))
              (.clash (1, 0) (1, 3))
              (.clash (1, 0) (1, 2))
              (.clash (0, 1) (2, 1)))
            (.clash (1, 0) (1, 2))
            (.clash (2, 0) (2, 1))
            (.clash (1, 0) (1, 3))
            (.clash (1, 0) (2, 0)))
          (.clash (1, 0) (1, 3))
          (.reuse 0))
        (.clash (1, 0) (1, 1))
        (.clash (3, 2) (3, 3))
        (.clash (3, 0) (3, 3)))
      (.clash (3, 1) (3, 2)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (1, 1))
    (.reuse 1)
    (.clash (1, 1) (1, 2))
    (.clash (0, 0) (3, 0))
private theorem check182 : check [state178, state181] state182 certificate182 = true := by
  decide +kernel
private theorem closed182 : Closed.{u} state182 :=
  sound (known := [state178, state181]) ⟨closed178.{u}, ⟨closed181.{u}, trivial⟩⟩ check182

private def state183 : Partition := #v[0, 1, 2, 3, 4, 3, 1, 7, 7, 4, 3, 0, 1, 7, 0, 4]
private def certificate183 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 2) (0, 3))
    (.clash (0, 0) (0, 2))
    (.clash (0, 1) (0, 2))
    (.clash (0, 0) (0, 3))
    (.clash (0, 1) (0, 3))
    (.clash (0, 0) (0, 1))
private theorem check183 : check [] state183 certificate183 = true := by
  decide +kernel
private theorem closed183 : Closed.{u} state183 :=
  sound (known := []) trivial check183

def state184 : Partition := #v[0, 1, 2, 3, 4, 3, 6, 7, 7, 9, 3, 0, 12, 7, 0, 15]
private def certificate184 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (2, 1))
    (.clash (0, 0) (0, 3))
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 2) (3, 2))
      (.clash (0, 0) (1, 0))
      (.clash (2, 3) (3, 3))
      (.clash (1, 0) (1, 2))
      (.transversal ![1, 0, 2, 3]
        (.clash (0, 1) (2, 1))
        (.clash (0, 1) (0, 3))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (0, 3))
          (.clash (3, 0) (3, 3))
          (.clash (0, 3) (1, 3))
          (.clash (2, 0) (3, 0))
          (.transversal ![2, 1, 0, 3]
            (.clash (0, 2) (0, 3))
            (.motif 0 1 2 2 1 3
              (.clash (0, 0) (0, 1)))
            (.clash (0, 1) (0, 2))
            (.clash (0, 3) (1, 3))
            (.clash (0, 1) (0, 3))
            (.clash (0, 1) (3, 1))))
        (.clash (1, 0) (1, 1))
        (.clash (1, 0) (1, 2))
        (.clash (0, 3) (3, 3)))
      (.transversal ![1, 2, 0, 3]
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (3, 1))
          (.clash (0, 1) (0, 3))
          (.reuse 0)
          (.clash (0, 3) (1, 3))
          (.clash (2, 0) (3, 0))
          (.motif 1 3 0 3 0 1
            (.clash (0, 1) (2, 1))))
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (2, 1))
        (.clash (1, 2) (1, 3))
        (.clash (1, 0) (1, 2))
        (.clash (1, 0) (1, 3))))
    (.clash (0, 0) (1, 0))
    (.clash (2, 1) (2, 3))
private theorem check184 : check [state183] state184 certificate184 = true := by
  decide +kernel
private theorem closed184 : Closed.{u} state184 :=
  sound (known := [state183]) ⟨closed183.{u}, trivial⟩ check184

private def state185 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 2, 8, 4, 5, 0, 5, 2, 4, 15]
private def certificate185 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (0, 1) (2, 1))
    (.clash (0, 1) (1, 1))
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 1) (0, 2))
      (.transversal ![3, 2, 0, 1]
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (0, 3))
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (0, 1))
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2)))
      (.clash (0, 1) (2, 1))
      (.motif 2 3 0 2 1 0
        (.clash (0, 0) (1, 0)))
      (.clash (0, 2) (3, 2))
      (.clash (1, 0) (2, 0)))
    (.clash (1, 0) (1, 1))
    (.clash (3, 2) (3, 3))
    (.clash (3, 0) (3, 3))
private theorem check185 : check [] state185 certificate185 = true := by
  decide +kernel
private theorem closed185 : Closed.{u} state185 :=
  sound (known := []) trivial check185

private def state186 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 0, 12, 7, 9, 6]
private def certificate186 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 2, 3, 0]
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (3, 0))
      (.clash (2, 3) (3, 3))
      (.clash (3, 0) (3, 3))
      (.clash (0, 0) (3, 0)))
    (.clash (0, 1) (1, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (1, 1))
        (.clash (3, 0) (3, 3))
        (.clash (1, 1) (1, 3))
        (.clash (3, 0) (3, 1))
        (.transversal ![2, 0, 3, 1]
          (.clash (0, 2) (3, 2))
          (.clash (0, 0) (0, 2))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (0, 2))
            (.motif 1 2 0 1 0 2
              (.clash (0, 2) (3, 2)))
            (.clash (0, 1) (2, 1))
            (.motif 2 3 0 2 1 0
              (.clash (0, 0) (1, 0)))
            (.clash (0, 2) (3, 2))
            (.clash (1, 0) (2, 0)))
          (.clash (0, 0) (1, 0))
          (.clash (1, 0) (1, 3))
          (.clash (1, 3) (2, 3))))
      (.clash (2, 1) (2, 3)))
    (.clash (1, 0) (1, 1))
    (.clash (1, 0) (1, 2))
    (.clash (1, 1) (1, 2))
private theorem check186 : check [] state186 certificate186 = true := by
  decide +kernel
private theorem closed186 : Closed.{u} state186 :=
  sound (known := []) trivial check186

private def state187 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 0, 12, 7, 9, 15]
private def certificate187 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (2, 1))
        (.transversal ![1, 2, 0, 3]
          (.clash (0, 0) (0, 1))
          (.clash (0, 1) (3, 1))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (3, 1))
            (.clash (0, 1) (1, 1))
            (.clash (1, 0) (3, 0))
            (.clash (1, 1) (1, 3))
            (.clash (2, 0) (3, 0))
            (.motif 1 3 0 1 3 0
              (.clash (0, 0) (2, 0))))
          (.clash (0, 0) (2, 0))
          (.clash (2, 3) (3, 3))
          (.clash (1, 3) (3, 3)))
        (.clash (2, 1) (3, 1))
        (.clash (2, 0) (2, 1)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![2, 0, 3, 1]
        (.clash (0, 2) (3, 2))
        (.clash (0, 0) (0, 2))
        (.transversal ![2, 1, 3, 0]
          (.clash (0, 2) (2, 2))
          (.clash (0, 0) (0, 2))
          (.clash (3, 0) (3, 1))
          (.clash (1, 1) (1, 2))
          (.reuse 0)
          (.clash (0, 0) (3, 0)))
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 3))
        (.clash (1, 2) (1, 3)))
      (.clash (1, 2) (3, 2)))
    (.clash (2, 1) (2, 3))
    (.clash (2, 3) (3, 3))
    (.clash (1, 2) (3, 2))
    (.reuse 1)
    (.clash (3, 2) (3, 3))
private theorem check187 : check [state185, state186] state187 certificate187 = true := by
  decide +kernel
private theorem closed187 : Closed.{u} state187 :=
  sound (known := [state185, state186]) ⟨closed185.{u}, ⟨closed186.{u}, trivial⟩⟩ check187

private def state188 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 0, 12, 7, 14, 15]
private def certificate188 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 3) (2, 3))
    (.clash (2, 1) (2, 3))
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 1) (3, 1))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (3, 0))
        (.clash (1, 1) (1, 3))
        (.clash (3, 0) (3, 1))
        (.transversal ![1, 2, 3, 0]
          (.transversal ![3, 1, 0, 2]
            (.transversal ![3, 0, 1, 2]
              (.clash (1, 0) (1, 1))
              (.clash (1, 1) (2, 1))
              (.clash (0, 0) (0, 3))
              (.motif 1 2 3 0 2 1
                (.clash (0, 1) (3, 1)))
              (.clash (0, 0) (1, 0))
              (.clash (2, 1) (2, 3)))
            (.clash (0, 1) (0, 3))
            (.clash (0, 0) (0, 3))
            (.clash (0, 1) (1, 1))
            (.clash (0, 0) (3, 0))
            (.clash (0, 0) (0, 1)))
          (.clash (0, 0) (0, 1))
          (.clash (0, 1) (1, 1))
          (.clash (1, 2) (3, 2))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (3, 0))))
      (.clash (0, 0) (0, 1))
      (.transversal ![3, 1, 0, 2]
        (.reuse 0)
        (.clash (0, 3) (1, 3))
        (.clash (0, 0) (0, 3))
        (.clash (1, 1) (1, 3))
        (.clash (2, 2) (2, 3))
        (.clash (0, 0) (2, 0)))
      (.clash (1, 3) (2, 3))
      (.clash (0, 0) (2, 0)))
    (.clash (2, 1) (3, 1))
    (.clash (3, 1) (3, 2))
    (.reuse 1)
private theorem check188 : check [state184, state187] state188 certificate188 = true := by
  decide +kernel
private theorem closed188 : Closed.{u} state188 :=
  sound (known := [state184, state187]) ⟨closed184.{u}, ⟨closed187.{u}, trivial⟩⟩ check188

def state189 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 0, 12, 13, 14, 15]
private def certificate189 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
    (.transversal ![2, 1, 3, 0]
      (.clash (0, 2) (2, 2))
      (.clash (0, 0) (0, 2))
      (.transversal ![1, 2, 3, 0]
        (.transversal ![1, 0, 3, 2]
          (.clash (1, 0) (1, 2))
          (.clash (0, 0) (0, 1))
          (.clash (1, 2) (3, 2))
          (.clash (0, 0) (1, 0))
          (.transversal ![1, 3, 2, 0]
            (.clash (1, 2) (1, 3))
            (.clash (0, 1) (1, 1))
            (.clash (0, 1) (0, 2))
            (.clash (1, 1) (1, 3))
            (.transversal ![1, 3, 0, 2]
              (.clash (0, 1) (0, 2))
              (.transversal ![0, 2, 1, 3]
                (.clash (0, 0) (0, 1))
                (.clash (2, 1) (2, 3))
                (.clash (2, 3) (3, 3))
                (.clash (0, 1) (2, 1))
                (.motif 1 3 2 0 3 2
                  (.clash (0, 2) (2, 2)))
                (.reuse 0))
              (.clash (1, 0) (1, 2))
              (.clash (2, 0) (3, 0))
              (.clash (0, 2) (3, 2))
              (.clash (1, 0) (2, 0)))
            (.clash (0, 2) (2, 2)))
          (.clash (3, 1) (3, 2)))
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (0, 2))
        (.reuse 1)
        (.clash (0, 2) (1, 2))
        (.clash (0, 0) (0, 2)))
      (.clash (1, 1) (3, 1))
      (.reuse 2)
      (.clash (0, 0) (3, 0)))
    (.clash (1, 1) (1, 3))
    (.reuse 3)
    (.clash (1, 1) (3, 1))
private theorem check189 : check [state175, state177, state182, state188] state189 certificate189 = true := by
  decide +kernel
private theorem closed189 : Closed.{u} state189 :=
  sound (known := [state175, state177, state182, state188]) ⟨closed175.{u}, ⟨closed177.{u}, ⟨closed182.{u}, ⟨closed188.{u}, trivial⟩⟩⟩⟩ check189

def state190 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 0, 6, 9, 5, 1, 1, 6, 0, 2]
private def certificate190 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (0, 0) (2, 0))
    (.transversal ![3, 2, 1, 0]
      (.motif 0 1 2 0 2 3
        (.clash (0, 1) (0, 2)))
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (2, 0))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1)))
    (.clash (0, 0) (0, 2))
    (.clash (2, 0) (2, 1))
    (.clash (0, 2) (1, 2))
    (.motif 1 2 0 2 1 0
      (.clash (1, 1) (1, 3)))
private theorem check190 : check [] state190 certificate190 = true := by
  decide +kernel
private theorem closed190 : Closed.{u} state190 :=
  sound (known := []) trivial check190

def state191 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 5, 11, 1, 13, 0, 5]
private def certificate191 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.clash (0, 3) (3, 3))
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 2) (1, 3))
      (.transversal ![2, 0, 1, 3]
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (0, 2))
          (.motif 0 2 1 3 1 0
            (.clash (0, 1) (0, 2)))
          (.clash (0, 0) (0, 1))
          (.transversal ![0, 2, 3, 1]
            (.clash (1, 2) (1, 3))
            (.clash (0, 0) (0, 2))
            (.clash (2, 1) (3, 1))
            (.clash (0, 2) (1, 2))
            (.motif 1 3 2 1 2 3
              (.clash (0, 2) (1, 2)))
            (.motif 0 3 2 1 2 0
              (.clash (0, 2) (0, 3))))
          (.clash (0, 0) (0, 2))
          (.clash (1, 3) (2, 3)))
        (.clash (0, 0) (0, 2))
        (.clash (0, 2) (2, 2))
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 1))
        (.clash (1, 1) (1, 3)))
      (.clash (1, 1) (1, 3))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (2, 1))
        (.clash (0, 1) (0, 3))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 2))
        (.clash (0, 3) (3, 3)))
      (.clash (1, 1) (1, 2))
      (.clash (1, 1) (2, 1)))
    (.clash (0, 0) (0, 3))
    (.clash (2, 0) (2, 2))
    (.clash (1, 1) (1, 3))
    (.clash (0, 0) (2, 0))
private theorem check191 : check [] state191 certificate191 = true := by
  decide +kernel
private theorem closed191 : Closed.{u} state191 :=
  sound (known := []) trivial check191

def state192 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 6, 2, 5, 11, 5, 6, 0, 2]
private def certificate192 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (3, 1))
    (.transversal ![1, 0, 2, 3]
      (.transversal ![3, 0, 1, 2]
        (.clash (0, 1) (0, 3))
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 1))
        (.clash (0, 0) (0, 2)))
      (.clash (0, 1) (1, 1))
      (.clash (0, 1) (0, 2))
      (.clash (1, 0) (1, 1))
      (.motif 1 2 0 2 1 0
        (.clash (0, 0) (3, 0)))
      (.clash (0, 2) (2, 2)))
    (.clash (0, 1) (1, 1))
    (.clash (2, 0) (2, 3))
    (.clash (1, 1) (1, 2))
    (.clash (2, 2) (2, 3))
private theorem check192 : check [] state192 certificate192 = true := by
  decide +kernel
private theorem closed192 : Closed.{u} state192 :=
  sound (known := []) trivial check192

def state193 : Partition := #v[0, 1, 2, 3, 4, 3, 6, 0, 8, 0, 3, 4, 3, 4, 0, 15]
private def certificate193 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (0, 3))
    (.transversal ![1, 2, 3, 0]
      (.transversal ![2, 0, 1, 3]
        (.transversal ![2, 1, 0, 3]
          (.clash (0, 2) (0, 3))
          (.clash (1, 0) (2, 0))
          (.clash (0, 1) (0, 2))
          (.clash (2, 0) (2, 2))
          (.clash (0, 1) (0, 3))
          (.columns))
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (1, 0))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (0, 3))
      (.clash (1, 0) (1, 2))
      (.clash (1, 1) (1, 2))
      (.clash (0, 3) (2, 3)))
    (.clash (0, 3) (2, 3))
    (.clash (2, 3) (3, 3))
    (.clash (0, 3) (3, 3))
private theorem check193 : check [] state193 certificate193 = true := by
  decide +kernel
private theorem closed193 : Closed.{u} state193 :=
  sound (known := []) trivial check193

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary10 : Known.{u} [state184, state189, state190, state191, state192, state193] :=
  ⟨closed184.{u}, ⟨closed189.{u}, ⟨closed190.{u}, ⟨closed191.{u}, ⟨closed192.{u}, ⟨closed193.{u}, trivial⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
