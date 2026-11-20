/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part12
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part12
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 214 through 231. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part04
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part05
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part10
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part11

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

private theorem closed189 : Closed.{u} state189 :=
  known_of_mem boundary10.{u} (by decide)

private theorem closed201 : Closed.{u} state201 :=
  known_of_mem boundary11.{u} (by decide)

private theorem closed202 : Closed.{u} state202 :=
  known_of_mem boundary11.{u} (by decide)

private theorem closed203 : Closed.{u} state203 :=
  known_of_mem boundary11.{u} (by decide)

private theorem closed213 : Closed.{u} state213 :=
  known_of_mem boundary11.{u} (by decide)

private def state214 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 11, 12, 13, 11, 15]
private def certificate214 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 2) (2, 2))
    (.clash (0, 2) (3, 2))
    (.transversal ![1, 2, 3, 0]
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 2) (1, 3))
        (.clash (0, 1) (1, 1))
        (.clash (0, 1) (0, 2))
        (.clash (1, 1) (1, 3))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (0, 2))
          (.transversal ![3, 1, 0, 2]
            (.motif 0 1 2 2 1 3
              (.clash (1, 2) (3, 2)))
            (.clash (0, 1) (0, 3))
            (.clash (0, 3) (2, 3))
            (.clash (0, 1) (1, 1))
            (.clash (2, 2) (2, 3))
            (.clash (1, 2) (3, 2)))
          (.clash (1, 2) (3, 2))
          (.clash (2, 0) (3, 0))
          (.clash (0, 2) (3, 2))
          (.clash (2, 0) (2, 3)))
        (.clash (0, 2) (2, 2)))
      (.transversal ![1, 3, 2, 0]
        (.clash (1, 3) (2, 3))
        (.clash (0, 1) (1, 1))
        (.clash (0, 1) (0, 2))
        (.clash (1, 1) (1, 3))
        (.transversal ![0, 3, 1, 2]
          (.clash (0, 0) (0, 2))
          (.reuse 0)
          (.clash (0, 0) (0, 1))
          (.reuse 1)
          (.clash (0, 1) (0, 2))
          (.clash (0, 1) (2, 1)))
        (.clash (0, 2) (2, 2)))
      (.clash (0, 1) (0, 2))
      (.clash (1, 2) (3, 2))
      (.clash (0, 2) (1, 2))
      (.clash (0, 2) (3, 2)))
    (.clash (2, 2) (2, 3))
    (.reuse 2)
    (.clash (3, 0) (3, 2))
private theorem check214 : check [state202, state203, state213] state214 certificate214 = true := by
  decide +kernel
private theorem closed214 : Closed.{u} state214 :=
  sound (known := [state202, state203, state213]) ⟨closed202.{u}, ⟨closed203.{u}, ⟨closed213.{u}, trivial⟩⟩⟩ check214

def state215 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 11, 12, 13, 14, 15]
private def certificate215 : Certificate :=
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
    (.reuse 7)
    (.reuse 8)
    (.clash (2, 2) (2, 3))
    (.clash (2, 2) (3, 2))
    (.reuse 9)
private theorem check215 : check [state73, state74, state75, state77, state78, state81, state87, state189, state201, state214] state215 certificate215 = true := by
  decide +kernel
private theorem closed215 : Closed.{u} state215 :=
  sound (known := [state73, state74, state75, state77, state78, state81, state87, state189, state201, state214]) ⟨closed73.{u}, ⟨closed74.{u}, ⟨closed75.{u}, ⟨closed77.{u}, ⟨closed78.{u}, ⟨closed81.{u}, ⟨closed87.{u}, ⟨closed189.{u}, ⟨closed201.{u}, ⟨closed214.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ check215

private def state216 : Partition := #v[0, 1, 2, 3, 3, 5, 0, 7, 1, 7, 3, 0, 7, 13, 1, 5]
private def certificate216 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (0, 3))
    (.transversal ![2, 3, 0, 1]
      (.motif 0 1 2 3 2 0
        (.clash (0, 1) (0, 2)))
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (0, 2))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (0, 1)))
    (.clash (0, 3) (1, 3))
    (.clash (2, 1) (3, 1))
    (.motif 1 3 0 3 1 0
      (.clash (1, 1) (1, 2)))
private theorem check216 : check [] state216 certificate216 = true := by
  decide +kernel
private theorem closed216 : Closed.{u} state216 :=
  sound (known := []) trivial check216

private def state217 : Partition := #v[0, 1, 2, 3, 4, 10, 0, 7, 1, 9, 10, 0, 12, 13, 14, 10]
private def certificate217 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (0, 2) (2, 2))
    (.clash (0, 0) (0, 2))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 2) (1, 3))
      (.clash (1, 1) (1, 2))
      (.transversal ![3, 0, 2, 1]
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (0, 3))
          (.clash (0, 0) (0, 1))
          (.motif 0 3 1 2 1 0
            (.clash (0, 1) (0, 3)))
          (.clash (0, 0) (0, 3))
          (.transversal ![0, 3, 1, 2]
            (.clash (1, 2) (1, 3))
            (.clash (2, 1) (2, 3))
            (.clash (0, 0) (0, 3))
            (.motif 1 2 3 1 3 2
              (.clash (0, 3) (1, 3)))
            (.clash (0, 3) (1, 3))
            (.motif 0 2 3 1 3 0
              (.clash (0, 2) (0, 3))))
          (.clash (1, 2) (3, 2)))
        (.clash (0, 3) (3, 3))
        (.clash (0, 0) (0, 3))
        (.clash (1, 0) (1, 1))
        (.clash (0, 0) (1, 0))
        (.clash (1, 1) (1, 2)))
      (.clash (1, 1) (1, 3))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (1, 1))
        (.clash (0, 1) (0, 2))
        (.clash (1, 1) (1, 3))
        (.clash (3, 0) (3, 1))
        (.clash (0, 2) (2, 2)))
      (.clash (1, 1) (3, 1)))
    (.clash (1, 1) (1, 2))
    (.clash (3, 0) (3, 3))
    (.clash (0, 0) (3, 0))
private theorem check217 : check [] state217 certificate217 = true := by
  decide +kernel
private theorem closed217 : Closed.{u} state217 :=
  sound (known := []) trivial check217

private def state218 : Partition := #v[0, 1, 2, 3, 4, 2, 0, 7, 2, 7, 10, 0, 12, 0, 1, 2]
private def certificate218 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.motif 0 1 2 0 1 2
      (.clash (2, 2) (3, 2)))
    (.clash (2, 2) (3, 2))
    (.clash (0, 1) (0, 2))
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 1) (2, 1))
      (.clash (2, 2) (3, 2))
      (.clash (3, 0) (3, 2))
      (.clash (1, 0) (1, 3))
      (.motif 2 3 0 0 1 3
        (.clash (0, 3) (1, 3)))
      (.clash (1, 0) (3, 0)))
    (.clash (1, 0) (1, 1))
    (.clash (0, 2) (2, 2))
private theorem check218 : check [] state218 certificate218 = true := by
  decide +kernel
private theorem closed218 : Closed.{u} state218 :=
  sound (known := []) trivial check218

private def state219 : Partition := #v[0, 1, 2, 3, 4, 2, 0, 7, 2, 9, 10, 0, 12, 0, 7, 2]
private def certificate219 : Certificate :=
  .motif 1 3 2 3 1 2
    (.clash (0, 2) (2, 2))
private theorem check219 : check [] state219 certificate219 = true := by
  decide +kernel
private theorem closed219 : Closed.{u} state219 :=
  sound (known := []) trivial check219

private def state220 : Partition := #v[0, 1, 2, 3, 4, 2, 0, 7, 2, 9, 10, 0, 12, 0, 9, 2]
private def certificate220 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.motif 0 1 3 1 2 0
      (.clash (2, 0) (3, 0)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (1, 0))
    (.transversal ![1, 0, 2, 3]
      (.clash (0, 1) (2, 1))
      (.transversal ![1, 3, 0, 2]
        (.transversal ![2, 3, 1, 0]
          (.clash (0, 1) (0, 2))
          (.clash (0, 2) (3, 2))
          (.clash (2, 0) (3, 0))
          (.clash (0, 1) (2, 1))
          (.transversal ![3, 0, 2, 1]
            (.columns)
            (.clash (0, 1) (0, 3))
            (.clash (0, 0) (0, 3))
            (.clash (0, 1) (2, 1))
            (.clash (0, 0) (1, 0))
            (.clash (0, 0) (0, 1)))
          (.clash (1, 0) (3, 0)))
        (.clash (0, 1) (0, 2))
        (.clash (0, 1) (2, 1))
        (.clash (1, 1) (1, 3))
        (.clash (1, 0) (1, 3))
        (.clash (0, 2) (3, 2)))
      (.clash (0, 1) (0, 2))
      (.clash (2, 1) (2, 2))
      (.clash (0, 2) (3, 2))
      (.clash (0, 2) (2, 2)))
    (.clash (1, 2) (3, 2))
private theorem check220 : check [] state220 certificate220 = true := by
  decide +kernel
private theorem closed220 : Closed.{u} state220 :=
  sound (known := []) trivial check220

private def state221 : Partition := #v[0, 1, 2, 3, 4, 8, 0, 7, 8, 9, 10, 0, 2, 13, 14, 8]
private def certificate221 : Certificate :=
  .transversal ![3, 1, 2, 0]
    (.clash (0, 3) (3, 3))
    (.transversal ![3, 2, 1, 0]
      (.clash (0, 0) (0, 3))
      (.clash (2, 1) (2, 2))
      (.clash (0, 2) (0, 3))
      (.clash (2, 1) (2, 3))
      (.clash (0, 0) (0, 2))
      (.transversal ![0, 3, 1, 2]
        (.clash (1, 2) (1, 3))
        (.clash (0, 0) (0, 2))
        (.clash (1, 2) (3, 2))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (0, 2))
          (.clash (0, 1) (1, 1))
          (.transversal ![0, 3, 2, 1]
            (.clash (0, 0) (0, 2))
            (.clash (0, 0) (0, 3))
            (.motif 0 3 2 1 0 2
              (.clash (0, 0) (0, 3)))
            (.clash (0, 2) (0, 3))
            (.clash (2, 1) (3, 1))
            (.transversal ![2, 0, 3, 1]
              (.clash (1, 0) (1, 3))
              (.clash (0, 0) (0, 2))
              (.clash (0, 2) (0, 3))
              (.clash (0, 0) (1, 0))
              (.motif 0 1 2 3 2 0
                (.clash (1, 1) (1, 3)))
              (.clash (0, 0) (0, 3))))
          (.clash (1, 1) (1, 3))
          (.clash (0, 2) (3, 2))
          (.clash (3, 2) (3, 3)))
        (.transversal ![2, 3, 0, 1]
          (.clash (0, 2) (3, 2))
          (.clash (1, 1) (2, 1))
          (.clash (2, 1) (3, 1))
          (.clash (1, 1) (1, 3))
          (.clash (3, 1) (3, 2))
          (.clash (1, 1) (3, 1)))
        (.clash (0, 2) (3, 2))))
    (.clash (0, 2) (0, 3))
    (.clash (2, 0) (2, 2))
    (.clash (2, 0) (3, 0))
    (.clash (0, 2) (2, 2))
private theorem check221 : check [] state221 certificate221 = true := by
  decide +kernel
private theorem closed221 : Closed.{u} state221 :=
  sound (known := []) trivial check221

private def state222 : Partition := #v[0, 1, 2, 3, 4, 8, 0, 7, 8, 9, 10, 0, 12, 13, 14, 8]
private def certificate222 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.transversal ![2, 0, 3, 1]
      (.clash (1, 0) (1, 1))
      (.clash (0, 0) (0, 2))
      (.clash (1, 1) (3, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![1, 0, 3, 2]
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 0, 2, 3]
          (.clash (0, 1) (3, 1))
          (.clash (2, 2) (3, 2))
          (.clash (0, 1) (0, 2))
          (.transversal ![3, 2, 0, 1]
            (.clash (0, 0) (0, 3))
            (.clash (0, 2) (0, 3))
            (.motif 0 2 1 0 2 3
              (.clash (1, 1) (1, 3)))
            (.clash (0, 0) (0, 2))
            (.clash (0, 0) (1, 0))
            (.clash (0, 2) (2, 2)))
          (.clash (1, 0) (1, 1))
          (.clash (0, 2) (2, 2)))
        (.clash (0, 0) (1, 0))
        (.clash (3, 1) (3, 2))
        (.clash (1, 2) (3, 2)))
      (.transversal ![0, 3, 1, 2]
        (.clash (1, 2) (1, 3))
        (.clash (2, 1) (2, 3))
        (.clash (1, 2) (3, 2))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (2, 1))
          (.clash (0, 1) (0, 2))
          (.reuse 0)
          (.clash (1, 1) (1, 3))
          (.motif 1 3 0 2 3 1
            (.clash (0, 1) (2, 1)))
          (.clash (0, 2) (3, 2)))
        (.reuse 1)
        (.reuse 2)))
    (.clash (0, 0) (0, 2))
    (.reuse 3)
    (.clash (0, 0) (2, 0))
    (.clash (2, 0) (3, 0))
    (.clash (0, 0) (3, 0))
private theorem check222 : check [state218, state219, state220, state221] state222 certificate222 = true := by
  decide +kernel
private theorem closed222 : Closed.{u} state222 :=
  sound (known := [state218, state219, state220, state221]) ⟨closed218.{u}, ⟨closed219.{u}, ⟨closed220.{u}, ⟨closed221.{u}, trivial⟩⟩⟩⟩ check222

def state223 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 1, 2, 6, 1, 0, 6, 13, 0, 2]
private def certificate223 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.clash (1, 0) (1, 1))
    (.clash (0, 0) (0, 2))
    (.clash (1, 1) (3, 1))
    (.clash (0, 0) (1, 0))
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 2) (0, 3))
      (.clash (0, 1) (0, 3))
      (.motif 0 1 2 1 2 3
        (.clash (0, 0) (0, 2)))
      (.clash (0, 1) (0, 2))
      (.clash (0, 2) (1, 2))
      (.clash (0, 1) (2, 1)))
    (.clash (3, 1) (3, 2))
private theorem check223 : check [] state223 certificate223 = true := by
  decide +kernel
private theorem closed223 : Closed.{u} state223 :=
  sound (known := []) trivial check223

def state224 : Partition := #v[0, 1, 2, 3, 4, 8, 6, 1, 8, 6, 10, 0, 12, 10, 0, 8]
private def certificate224 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (1, 1))
    (.motif 2 1 3 1 0 2
      (.clash (0, 0) (2, 0)))
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (3, 1))
private theorem check224 : check [] state224 certificate224 = true := by
  decide +kernel
private theorem closed224 : Closed.{u} state224 :=
  sound (known := []) trivial check224

private def state225 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 1, 8, 6, 4, 0, 6, 0, 1, 2]
private def certificate225 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (2, 1))
    (.transversal ![3, 2, 0, 1]
      (.motif 0 1 2 1 2 3
        (.clash (0, 0) (0, 2)))
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (0, 1)))
    (.clash (0, 1) (0, 2))
    (.clash (2, 0) (2, 1))
    (.clash (0, 2) (1, 2))
    (.motif 1 2 0 2 0 1
      (.clash (1, 0) (1, 3)))
private theorem check225 : check [] state225 certificate225 = true := by
  decide +kernel
private theorem closed225 : Closed.{u} state225 :=
  sound (known := []) trivial check225

private def state226 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 10, 0, 12, 10, 7, 5]
private def certificate226 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 3, 2, 0]
      (.clash (1, 0) (1, 3))
      (.clash (0, 1) (3, 1))
      (.clash (1, 0) (3, 0))
      (.clash (2, 2) (3, 2))
      (.clash (3, 0) (3, 2))
      (.clash (3, 0) (3, 1)))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (1, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 1))
        (.clash (3, 0) (3, 2))
        (.clash (2, 1) (2, 3))
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
            (.motif 1 2 0 2 0 1
              (.clash (0, 1) (3, 1))))
          (.clash (1, 0) (1, 2))
          (.clash (1, 0) (1, 1))
          (.clash (1, 1) (1, 2)))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 3))
      (.clash (1, 3) (2, 3)))
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (3, 1))
private theorem check226 : check [] state226 certificate226 = true := by
  decide +kernel
private theorem closed226 : Closed.{u} state226 :=
  sound (known := []) trivial check226

private def state227 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 10, 0, 12, 13, 7, 5]
private def certificate227 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 2))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.clash (1, 0) (3, 0))
          (.clash (2, 1) (2, 3))
          (.motif 2 3 1 1 3 0
            (.clash (0, 0) (0, 1)))
          (.clash (0, 0) (3, 0))))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (2, 1))
        (.clash (0, 0) (0, 1))
        (.clash (3, 0) (3, 2))
        (.clash (2, 1) (2, 3))
        (.transversal ![2, 1, 3, 0]
          (.transversal ![1, 0, 2, 3]
            (.clash (1, 0) (1, 3))
            (.clash (2, 2) (3, 2))
            (.clash (0, 1) (0, 2))
            (.reuse 0)
            (.clash (1, 0) (1, 1))
            (.clash (0, 2) (2, 2)))
          (.clash (0, 0) (0, 2))
          (.clash (0, 2) (1, 2))
          (.clash (1, 1) (3, 1))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (3, 0)))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 3))
      (.clash (1, 3) (2, 3)))
    (.clash (2, 2) (3, 2))
    (.clash (3, 1) (3, 2))
    (.reuse 1)
private theorem check227 : check [state225, state226] state227 certificate227 = true := by
  decide +kernel
private theorem closed227 : Closed.{u} state227 :=
  sound (known := [state225, state226]) ⟨closed225.{u}, ⟨closed226.{u}, trivial⟩⟩ check227

private def state228 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 10, 0, 12, 13, 14, 5]
private def certificate228 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 3) (2, 3))
    (.clash (2, 1) (2, 3))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 1) (2, 1))
      (.transversal ![3, 1, 0, 2]
        (.clash (0, 3) (3, 3))
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (1, 1))
        (.clash (2, 3) (3, 3))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 1) (1, 1))
      (.clash (2, 0) (2, 1))
      (.clash (1, 1) (1, 2))
      (.transversal ![1, 3, 0, 2]
        (.transversal ![0, 3, 2, 1]
          (.clash (0, 0) (0, 1))
          (.clash (2, 2) (2, 3))
          (.clash (3, 1) (3, 2))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (2, 1))
            (.clash (0, 0) (0, 1))
            (.motif 2 3 0 0 2 3
              (.clash (0, 1) (0, 3)))
            (.clash (1, 2) (3, 2))
            (.transversal ![2, 1, 3, 0]
              (.reuse 0)
              (.clash (0, 0) (0, 2))
              (.clash (0, 2) (1, 2))
              (.clash (0, 0) (2, 0))
              (.clash (1, 1) (1, 2))
              (.clash (0, 0) (3, 0)))
            (.clash (0, 0) (3, 0)))
          (.clash (0, 1) (3, 1))
          (.reuse 1))
        (.clash (0, 1) (1, 1))
        (.clash (0, 0) (0, 1))
        (.clash (1, 1) (1, 3))
        (.clash (1, 3) (2, 3))
        (.clash (0, 0) (2, 0))))
    (.clash (1, 2) (1, 3))
    (.reuse 2)
    (.clash (1, 2) (3, 2))
private theorem check228 : check [state223, state224, state227] state228 certificate228 = true := by
  decide +kernel
private theorem closed228 : Closed.{u} state228 :=
  sound (known := [state223, state224, state227]) ⟨closed223.{u}, ⟨closed224.{u}, ⟨closed227.{u}, trivial⟩⟩⟩ check228

def state229 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 5]
private def certificate229 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 0, 2, 3]
        (.clash (1, 0) (2, 0))
        (.clash (2, 0) (2, 2))
        (.clash (0, 1) (1, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (1, 0) (2, 0))
          (.clash (0, 0) (0, 1))
          (.transversal ![0, 3, 1, 2]
            (.clash (1, 2) (1, 3))
            (.clash (2, 1) (2, 3))
            (.clash (0, 0) (0, 1))
            (.transversal ![1, 3, 2, 0]
              (.clash (0, 1) (2, 1))
              (.clash (1, 0) (2, 0))
              (.clash (2, 0) (3, 0))
              (.clash (1, 0) (1, 3))
              (.transversal ![3, 0, 1, 2]
                (.reuse 0)
                (.clash (0, 3) (1, 3))
                (.clash (0, 1) (0, 3))
                (.clash (1, 0) (1, 3))
                (.clash (1, 0) (2, 0))
                (.clash (0, 1) (2, 1)))
              (.clash (1, 0) (3, 0)))
            (.motif 1 2 0 0 3 2
              (.clash (0, 1) (0, 2)))
            (.clash (0, 1) (2, 1)))
          (.clash (0, 0) (1, 0))
          (.clash (2, 2) (3, 2))
          (.clash (1, 2) (3, 2)))
        (.clash (1, 0) (1, 1))
        (.reuse 1))
      (.clash (0, 1) (1, 1))
      (.clash (0, 0) (2, 0))
      (.clash (1, 1) (1, 2))
      (.reuse 2))
    (.clash (2, 1) (2, 3))
    (.clash (2, 3) (3, 3))
    (.reuse 3)
    (.clash (1, 1) (1, 2))
    (.clash (1, 1) (2, 1))
private theorem check229 : check [state216, state217, state222, state228] state229 certificate229 = true := by
  decide +kernel
private theorem closed229 : Closed.{u} state229 :=
  sound (known := [state216, state217, state222, state228]) ⟨closed216.{u}, ⟨closed217.{u}, ⟨closed222.{u}, ⟨closed228.{u}, trivial⟩⟩⟩⟩ check229

def state230 : Partition := #v[0, 1, 2, 3, 2, 5, 3, 7, 8, 0, 1, 2, 1, 3, 0, 5]
private def certificate230 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.motif 0 1 2 3 0 2
      (.clash (0, 0) (0, 1)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 0) (0, 3))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 1) (0, 2))
      (.clash (1, 0) (2, 0))
      (.clash (0, 2) (0, 3))
      (.clash (2, 0) (2, 2))
      (.clash (0, 1) (0, 3))
      (.motif 1 2 0 2 3 0
        (.clash (0, 0) (0, 1))))
    (.clash (0, 3) (1, 3))
    (.clash (0, 1) (0, 3))
private theorem check230 : check [] state230 certificate230 = true := by
  decide +kernel
private theorem closed230 : Closed.{u} state230 :=
  sound (known := []) trivial check230

def state231 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 7, 8, 0, 1, 2, 12, 2, 0, 5]
private def certificate231 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.transversal ![1, 2, 0, 3]
      (.clash (1, 2) (2, 2))
      (.clash (2, 0) (2, 2))
      (.clash (0, 1) (1, 1))
      (.transversal ![1, 2, 3, 0]
        (.clash (1, 2) (2, 2))
        (.clash (0, 1) (0, 2))
        (.motif 0 3 1 0 1 2
          (.clash (1, 2) (2, 2)))
        (.clash (0, 2) (1, 2))
        (.clash (2, 0) (3, 0))
        (.clash (1, 0) (3, 0)))
      (.clash (1, 1) (1, 2))
      (.motif 1 2 0 0 1 3
        (.clash (0, 3) (3, 3))))
    (.clash (0, 0) (0, 1))
    (.clash (0, 0) (0, 2))
    (.transversal ![2, 3, 1, 0]
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (0, 2))
      (.clash (1, 0) (3, 0))
      (.clash (0, 0) (0, 1))
      (.motif 0 3 1 0 1 2
        (.clash (1, 2) (1, 3)))
      (.clash (0, 0) (3, 0)))
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (0, 2))
private theorem check231 : check [] state231 certificate231 = true := by
  decide +kernel
private theorem closed231 : Closed.{u} state231 :=
  sound (known := []) trivial check231

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary12 : Known.{u} [state215, state223, state224, state229, state230, state231] :=
  ⟨closed215.{u}, ⟨closed223.{u}, ⟨closed224.{u}, ⟨closed229.{u}, ⟨closed230.{u}, ⟨closed231.{u}, trivial⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
