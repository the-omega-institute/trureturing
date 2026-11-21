/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part13
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part13
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part13.certificate250
   digest: Order-four certificate decisions for chunks 232 through 250. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part12

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed223 : Closed.{u} state223 :=
  known_of_mem boundary12.{u} (by decide)

private theorem closed224 : Closed.{u} state224 :=
  known_of_mem boundary12.{u} (by decide)

private theorem closed230 : Closed.{u} state230 :=
  known_of_mem boundary12.{u} (by decide)

private theorem closed231 : Closed.{u} state231 :=
  known_of_mem boundary12.{u} (by decide)

private def state232 : Partition := #v[0, 1, 2, 3, 2, 10, 6, 7, 8, 0, 10, 11, 12, 13, 0, 10]
private def certificate232 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.clash (0, 3) (3, 3))
    (.transversal ![0, 3, 2, 1]
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (1, 1))
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
        (.clash (1, 1) (1, 3))
        (.clash (0, 0) (3, 0))
        (.clash (3, 0) (3, 3)))
      (.clash (1, 1) (2, 1))
      (.clash (2, 1) (3, 1))
      (.clash (1, 1) (1, 3))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 1))
        (.clash (0, 3) (1, 3))
        (.clash (2, 1) (3, 1))
        (.clash (0, 0) (0, 3)))
      (.clash (1, 1) (3, 1)))
    (.clash (0, 0) (0, 3))
    (.clash (2, 0) (2, 2))
    (.clash (1, 1) (2, 1))
    (.clash (0, 0) (2, 0))
private theorem check232 : check [] state232 certificate232 = true := by
  decide +kernel
private theorem closed232 : Closed.{u} state232 :=
  sound (known := []) trivial check232

private def state233 : Partition := #v[7, 1, 2, 3, 4, 2, 1, 7, 2, 7, 4, 1, 1, 13, 7, 2]
private def certificate233 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.clash (0, 2) (2, 2))
    (.clash (0, 1) (0, 2))
    (.clash (1, 1) (3, 1))
    (.clash (1, 0) (1, 2))
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 2) (0, 3))
      (.columns)
      (.clash (0, 1) (0, 3))
      (.clash (0, 2) (2, 2))
      (.clash (0, 1) (0, 2))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 1) (3, 1))
private theorem check233 : check [] state233 certificate233 = true := by
  decide +kernel
private theorem closed233 : Closed.{u} state233 :=
  sound (known := []) trivial check233

private def state234 : Partition := #v[7, 1, 2, 3, 4, 2, 6, 7, 2, 7, 10, 11, 12, 11, 7, 2]
private def certificate234 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.transversal ![1, 2, 3, 0]
      (.clash (1, 0) (1, 2))
      (.clash (0, 1) (3, 1))
      (.clash (1, 0) (3, 0))
      (.motif 1 3 0 2 3 1
        (.clash (0, 0) (0, 1)))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 0) (0, 1))
        (.motif 0 2 1 1 0 2
          (.clash (0, 0) (3, 0)))
        (.clash (1, 0) (1, 2))
        (.clash (2, 1) (2, 2))
        (.clash (0, 0) (3, 0))
        (.clash (1, 2) (2, 2)))
      (.clash (3, 0) (3, 1)))
    (.clash (0, 1) (3, 1))
    (.clash (0, 0) (0, 1))
    (.motif 1 2 0 0 1 3
      (.clash (0, 2) (0, 3)))
    (.clash (0, 0) (1, 0))
    (.clash (1, 3) (2, 3))
private theorem check234 : check [] state234 certificate234 = true := by
  decide +kernel
private theorem closed234 : Closed.{u} state234 :=
  sound (known := []) trivial check234

private def state235 : Partition := #v[7, 1, 2, 3, 4, 2, 6, 7, 8, 7, 10, 11, 12, 8, 7, 2]
private def certificate235 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.clash (1, 0) (1, 1))
    (.clash (2, 3) (3, 3))
    (.clash (1, 1) (3, 1))
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 2) (1, 3))
      (.clash (0, 0) (1, 0))
      (.clash (0, 0) (2, 0))
      (.clash (1, 0) (1, 2))
      (.motif 1 3 0 2 3 1
        (.clash (0, 0) (0, 1)))
      (.clash (1, 0) (2, 0)))
    (.clash (1, 0) (2, 0))
    (.clash (2, 0) (2, 3))
private theorem check235 : check [] state235 certificate235 = true := by
  decide +kernel
private theorem closed235 : Closed.{u} state235 :=
  sound (known := []) trivial check235

private def state236 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 8, 0, 10, 11, 7, 13, 0, 2]
private def certificate236 : Certificate :=
  .transversal ![3, 2, 1, 0]
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 2) (0, 3))
      (.clash (1, 2) (2, 2))
      (.clash (0, 3) (1, 3))
      (.clash (0, 2) (2, 2))
      (.clash (1, 1) (1, 3))
      (.transversal ![0, 2, 3, 1]
        (.clash (0, 0) (0, 3))
        (.clash (2, 1) (2, 3))
        (.clash (2, 1) (3, 1))
        (.clash (0, 3) (2, 3))
        (.transversal ![2, 0, 3, 1]
          (.clash (1, 0) (1, 1))
          (.clash (2, 3) (3, 3))
          (.clash (0, 2) (0, 3))
          (.transversal ![1, 0, 2, 3]
            (.transversal ![1, 3, 0, 2]
              (.clash (1, 0) (1, 3))
              (.clash (1, 0) (2, 0))
              (.clash (0, 0) (0, 1))
              (.clash (2, 0) (2, 2))
              (.clash (0, 0) (3, 0))
              (.clash (0, 0) (2, 0)))
            (.motif 0 1 2 2 3 1
              (.clash (0, 0) (0, 3)))
            (.clash (0, 1) (0, 2))
            (.clash (1, 0) (1, 3))
            (.clash (1, 0) (1, 1))
            (.clash (0, 2) (2, 2)))
          (.clash (1, 0) (1, 2))
          (.clash (0, 3) (2, 3)))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (0, 3))
          (.clash (0, 1) (3, 1))
          (.motif 0 1 2 2 3 1
            (.clash (0, 0) (0, 3)))
          (.clash (0, 3) (2, 3))
          (.clash (0, 3) (1, 3))
          (.clash (1, 3) (2, 3)))))
    (.clash (0, 0) (0, 3))
    (.clash (0, 3) (1, 3))
    (.clash (1, 2) (3, 2))
    (.clash (1, 2) (1, 3))
    (.clash (0, 0) (3, 0))
private theorem check236 : check [] state236 certificate236 = true := by
  decide +kernel
private theorem closed236 : Closed.{u} state236 :=
  sound (known := []) trivial check236

private def state237 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 8, 0, 10, 11, 12, 13, 0, 2]
private def certificate237 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.clash (1, 1) (1, 3))
    (.clash (0, 0) (0, 2))
    (.clash (3, 0) (3, 3))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 0) (0, 2))
      (.transversal ![0, 2, 3, 1]
        (.clash (1, 2) (1, 3))
        (.clash (1, 3) (2, 3))
        (.clash (2, 1) (3, 1))
        (.transversal ![1, 0, 3, 2]
          (.transversal ![2, 0, 3, 1]
            (.clash (0, 1) (0, 2))
            (.clash (0, 2) (1, 2))
            (.clash (1, 1) (3, 1))
            (.clash (1, 0) (1, 2))
            (.clash (0, 1) (3, 1))
            (.motif 1 3 0 2 3 1
              (.clash (0, 0) (0, 1))))
          (.transversal ![1, 0, 2, 3]
            (.clash (1, 0) (1, 2))
            (.clash (1, 2) (2, 2))
            (.clash (0, 1) (0, 2))
            (.transversal ![1, 3, 2, 0]
              (.clash (0, 0) (0, 1))
              (.clash (1, 0) (1, 2))
              (.reuse 0)
              (.clash (0, 0) (1, 0))
              (.clash (0, 0) (3, 0))
              (.clash (1, 0) (3, 0)))
            (.clash (1, 0) (1, 1))
            (.clash (0, 2) (2, 2)))
          (.clash (0, 0) (0, 1))
          (.clash (1, 0) (1, 2))
          (.clash (0, 0) (1, 0))
          (.clash (1, 2) (1, 3)))
        (.motif 1 3 0 2 3 1
          (.clash (0, 0) (0, 1)))
        (.reuse 1))
      (.clash (1, 1) (3, 1))
      (.clash (0, 0) (2, 0))
      (.clash (2, 1) (3, 1))
      (.reuse 2))
    (.reuse 3)
    (.clash (0, 0) (3, 0))
private theorem check237 : check [state233, state234, state235, state236] state237 certificate237 = true := by
  decide +kernel
private theorem closed237 : Closed.{u} state237 :=
  sound (known := [state233, state234, state235, state236]) ⟨closed233.{u}, ⟨closed234.{u}, ⟨closed235.{u}, ⟨closed236.{u}, trivial⟩⟩⟩⟩ check237

private def state238 : Partition := #v[0, 1, 2, 3, 4, 5, 3, 0, 5, 3, 1, 4, 12, 4, 0, 5]
private def certificate238 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (0, 3))
    (.clash (0, 1) (3, 1))
    (.transversal ![2, 3, 1, 0]
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (0, 3))
      (.clash (0, 1) (0, 2))
      (.clash (0, 0) (0, 3))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (0, 3)))
    (.clash (0, 3) (2, 3))
    (.motif 2 3 0 3 0 1
      (.clash (0, 1) (1, 1)))
    (.clash (1, 0) (3, 0))
private theorem check238 : check [] state238 certificate238 = true := by
  decide +kernel
private theorem closed238 : Closed.{u} state238 :=
  sound (known := []) trivial check238

private def state239 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 7, 11, 12, 11, 0, 5]
private def certificate239 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 3, 0, 2]
      (.clash (1, 0) (1, 3))
      (.clash (1, 0) (2, 0))
      (.clash (0, 0) (0, 1))
      (.clash (2, 0) (2, 2))
      (.clash (2, 2) (3, 2))
      (.clash (0, 0) (2, 0)))
    (.transversal ![1, 0, 3, 2]
      (.clash (1, 0) (1, 3))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (2, 2))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 2))
        (.transversal ![3, 0, 1, 2]
          (.clash (0, 3) (2, 3))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (0, 3))
            (.clash (0, 1) (3, 1))
            (.motif 1 3 0 1 0 3
              (.clash (0, 3) (2, 3)))
            (.clash (0, 3) (2, 3))
            (.motif 2 3 0 3 0 1
              (.clash (0, 1) (1, 1)))
            (.clash (1, 0) (3, 0)))
          (.clash (0, 0) (0, 3))
          (.clash (1, 0) (1, 2))
          (.clash (0, 0) (1, 0))
          (.clash (1, 2) (3, 2))))
      (.clash (0, 0) (1, 0))
      (.clash (3, 1) (3, 2)))
    (.clash (0, 1) (1, 1))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (1, 3))
private theorem check239 : check [] state239 certificate239 = true := by
  decide +kernel
private theorem closed239 : Closed.{u} state239 :=
  sound (known := []) trivial check239

private def state240 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 10, 11, 12, 11, 0, 5]
private def certificate240 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 2))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 1) (3, 1))
          (.clash (1, 0) (3, 0))
          (.clash (2, 1) (2, 3))
          (.motif 2 3 1 1 3 0
            (.clash (0, 1) (3, 1)))
          (.clash (3, 0) (3, 1))))
      (.clash (0, 1) (3, 1))
      (.clash (0, 0) (0, 1))
      (.transversal ![3, 0, 1, 2]
        (.clash (0, 3) (2, 3))
        (.transversal ![3, 1, 0, 2]
          (.clash (0, 3) (3, 3))
          (.clash (2, 0) (2, 1))
          (.clash (0, 0) (0, 3))
          (.transversal ![1, 0, 2, 3]
            (.clash (0, 1) (3, 1))
            (.reuse 0)
            (.clash (0, 1) (1, 1))
            (.clash (2, 2) (2, 3))
            (.clash (1, 0) (1, 1))
            (.clash (2, 0) (2, 2)))
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (2, 0)))
        (.clash (0, 0) (0, 3))
        (.clash (1, 0) (1, 2))
        (.clash (0, 0) (1, 0))
        (.clash (1, 2) (1, 3)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 3) (2, 3)))
    (.clash (2, 2) (3, 2))
    (.clash (3, 1) (3, 2))
    (.reuse 1)
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
private theorem check240 : check [state238, state239] state240 certificate240 = true := by
  decide +kernel
private theorem closed240 : Closed.{u} state240 :=
  sound (known := [state238, state239]) ⟨closed238.{u}, ⟨closed239.{u}, trivial⟩⟩ check240

private def state241 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 10, 11, 12, 13, 0, 5]
private def certificate241 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 2) (3, 2))
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
    (.clash (3, 1) (3, 2))
    (.clash (2, 1) (2, 3))
    (.clash (2, 1) (3, 1))
    (.reuse 2)
private theorem check241 : check [state223, state224, state240] state241 certificate241 = true := by
  decide +kernel
private theorem closed241 : Closed.{u} state241 :=
  sound (known := [state223, state224, state240]) ⟨closed223.{u}, ⟨closed224.{u}, ⟨closed240.{u}, trivial⟩⟩⟩ check241

def state242 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 0, 5]
private def certificate242 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (3, 2))
    (.transversal ![2, 0, 1, 3]
      (.transversal ![1, 0, 2, 3]
        (.clash (0, 1) (0, 2))
        (.transversal ![1, 0, 3, 2]
          (.clash (0, 1) (0, 2))
          (.clash (2, 2) (2, 3))
          (.clash (0, 0) (0, 1))
          (.transversal ![0, 2, 3, 1]
            (.clash (1, 2) (3, 2))
            (.clash (0, 0) (0, 2))
            (.clash (2, 1) (3, 1))
            (.clash (0, 2) (1, 2))
            (.transversal ![1, 2, 3, 0]
              (.clash (0, 1) (3, 1))
              (.clash (0, 1) (0, 2))
              (.transversal ![3, 0, 2, 1]
                (.clash (0, 2) (0, 3))
                (.clash (0, 1) (0, 3))
                (.reuse 0)
                (.clash (0, 1) (0, 2))
                (.clash (0, 2) (1, 2))
                (.clash (0, 1) (3, 1)))
              (.clash (0, 2) (1, 2))
              (.clash (3, 0) (3, 1))
              (.clash (1, 0) (3, 0)))
            (.reuse 1))
          (.clash (0, 0) (0, 2))
          (.clash (2, 1) (2, 3)))
        (.clash (0, 1) (1, 1))
        (.clash (0, 2) (2, 2))
        (.clash (1, 0) (1, 1))
        (.reuse 2))
      (.clash (0, 0) (0, 2))
      (.reuse 3)
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (2, 1)))
    (.clash (3, 2) (3, 3))
    (.reuse 4)
    (.clash (1, 1) (1, 2))
    (.clash (1, 1) (2, 1))
private theorem check242 : check [state230, state231, state232, state237, state241] state242 certificate242 = true := by
  decide +kernel
private theorem closed242 : Closed.{u} state242 :=
  sound (known := [state230, state231, state232, state237, state241]) ⟨closed230.{u}, ⟨closed231.{u}, ⟨closed232.{u}, ⟨closed237.{u}, ⟨closed241.{u}, trivial⟩⟩⟩⟩⟩ check242

private def state243 : Partition := #v[0, 1, 8, 3, 1, 8, 6, 0, 8, 6, 10, 1, 12, 0, 1, 8]
private def certificate243 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.clash (0, 0) (0, 2))
    (.clash (0, 2) (1, 2))
    (.clash (2, 0) (3, 0))
    (.clash (1, 2) (1, 3))
    (.clash (0, 0) (3, 0))
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 0) (0, 1))
      (.clash (2, 2) (2, 3))
      (.clash (0, 1) (2, 1))
      (.transversal ![3, 1, 2, 0]
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (0, 3))
        (.columns)
        (.clash (0, 0) (0, 2))
        (.clash (0, 2) (1, 2))
        (.clash (0, 0) (3, 0)))
      (.clash (0, 0) (3, 0))
      (.clash (1, 2) (2, 2)))
private theorem check243 : check [] state243 certificate243 = true := by
  decide +kernel
private theorem closed243 : Closed.{u} state243 :=
  sound (known := []) trivial check243

def state244 : Partition := #v[0, 1, 8, 3, 1, 8, 6, 7, 8, 9, 10, 1, 12, 13, 1, 8]
private def certificate244 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.motif 0 1 2 0 1 2
      (.clash (2, 2) (2, 3)))
    (.transversal ![0, 2, 3, 1]
      (.motif 0 1 2 0 1 2
        (.clash (2, 2) (2, 3)))
      (.clash (0, 0) (0, 1))
      (.clash (2, 1) (3, 1))
      (.clash (1, 0) (1, 2))
      (.transversal ![0, 3, 2, 1]
        (.motif 1 2 0 0 1 3
          (.clash (0, 2) (0, 3)))
        (.clash (2, 1) (2, 2))
        (.clash (2, 1) (3, 1))
        (.transversal ![2, 3, 1, 0]
          (.clash (0, 2) (2, 2))
          (.clash (0, 0) (0, 2))
          (.clash (2, 0) (3, 0))
          (.clash (2, 1) (2, 2))
          (.motif 2 3 0 2 3 0
            (.clash (0, 0) (0, 1)))
          (.clash (0, 0) (3, 0)))
        (.clash (1, 2) (1, 3))
        (.clash (1, 2) (2, 2)))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 0) (0, 2))
    (.transversal ![0, 2, 3, 1]
      (.motif 0 1 2 0 1 2
        (.clash (2, 2) (2, 3)))
      (.clash (0, 0) (0, 1))
      (.transversal ![0, 3, 1, 2]
        (.reuse 0)
        (.clash (2, 1) (3, 1))
        (.clash (0, 0) (0, 1))
        (.clash (1, 2) (1, 3))
        (.clash (1, 0) (1, 3))
        (.clash (0, 1) (2, 1)))
      (.clash (0, 1) (2, 1))
      (.clash (2, 1) (3, 1))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 2) (1, 2))
    (.clash (1, 1) (2, 1))
private theorem check244 : check [state243] state244 certificate244 = true := by
  decide +kernel
private theorem closed244 : Closed.{u} state244 :=
  sound (known := [state243]) ⟨closed243.{u}, trivial⟩ check244

private def state245 : Partition := #v[0, 1, 2, 6, 4, 2, 6, 7, 8, 0, 1, 4, 1, 6, 4, 2]
private def certificate245 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 0) (0, 1))
      (.clash (2, 0) (2, 2))
      (.clash (1, 0) (3, 0))
      (.clash (0, 0) (2, 0))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (2, 0)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 0) (0, 3))
    (.motif 0 1 2 2 3 1
      (.clash (0, 0) (0, 3)))
    (.clash (0, 3) (1, 3))
    (.clash (0, 1) (0, 3))
private theorem check245 : check [] state245 certificate245 = true := by
  decide +kernel
private theorem closed245 : Closed.{u} state245 :=
  sound (known := []) trivial check245

def state246 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 8, 9, 1, 4, 12, 13, 4, 2]
private def certificate246 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.clash (0, 3) (2, 3))
    (.clash (0, 1) (0, 3))
    (.transversal ![3, 1, 2, 0]
      (.clash (0, 2) (0, 3))
      (.clash (0, 1) (0, 3))
      (.clash (3, 0) (3, 1))
      (.clash (0, 1) (0, 2))
      (.clash (3, 0) (3, 3))
      (.transversal ![0, 2, 3, 1]
        (.transversal ![0, 3, 2, 1]
          (.clash (1, 2) (1, 3))
          (.clash (0, 0) (0, 1))
          (.clash (0, 0) (0, 3))
          (.transversal ![0, 3, 1, 2]
            (.clash (0, 0) (0, 1))
            (.transversal ![1, 2, 0, 3]
              (.clash (0, 0) (0, 1))
              (.clash (2, 0) (2, 2))
              (.clash (0, 1) (0, 2))
              (.clash (0, 0) (2, 0))
              (.clash (0, 0) (0, 2))
              (.motif 0 2 1 2 1 0
                (.clash (1, 0) (1, 3))))
            (.clash (0, 0) (1, 0))
            (.clash (0, 1) (2, 1))
            (.clash (1, 0) (1, 3))
            (.clash (2, 1) (2, 3)))
          (.clash (0, 3) (1, 3))
          (.clash (0, 1) (0, 3)))
        (.clash (0, 0) (1, 0))
        (.clash (0, 0) (0, 3))
        (.clash (1, 0) (1, 2))
        (.transversal ![0, 2, 1, 3]
          (.clash (0, 0) (0, 3))
          (.reuse 0)
          (.clash (0, 0) (0, 2))
          (.clash (2, 1) (3, 1))
          (.clash (0, 2) (0, 3))
          (.clash (1, 1) (2, 1)))
        (.clash (0, 3) (2, 3))))
    (.clash (2, 2) (2, 3))
    (.clash (3, 1) (3, 2))
    (.clash (0, 1) (3, 1))
private theorem check246 : check [state245] state246 certificate246 = true := by
  decide +kernel
private theorem closed246 : Closed.{u} state246 :=
  sound (known := [state245]) ⟨closed245.{u}, trivial⟩ check246

def state247 : Partition := #v[0, 1, 2, 3, 10, 2, 0, 7, 2, 7, 10, 1, 12, 10, 1, 2]
private def certificate247 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (0, 1) (2, 1))
    (.clash (0, 1) (3, 1))
    (.clash (3, 0) (3, 2))
    (.clash (1, 0) (1, 3))
    (.motif 1 3 2 1 0 3
      (.clash (0, 1) (3, 1)))
    (.clash (1, 0) (3, 0))
private theorem check247 : check [] state247 certificate247 = true := by
  decide +kernel
private theorem closed247 : Closed.{u} state247 :=
  sound (known := []) trivial check247

private def state248 : Partition := #v[0, 1, 2, 3, 10, 2, 6, 7, 1, 6, 10, 0, 12, 10, 0, 2]
private def certificate248 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.clash (0, 2) (0, 3))
    (.clash (0, 1) (0, 3))
    (.clash (0, 0) (0, 3))
    (.clash (0, 1) (0, 2))
    (.clash (0, 0) (0, 2))
    (.clash (0, 0) (0, 1))
private theorem check248 : check [] state248 certificate248 = true := by
  decide +kernel
private theorem closed248 : Closed.{u} state248 :=
  sound (known := []) trivial check248

private def state249 : Partition := #v[0, 1, 8, 3, 10, 8, 6, 7, 8, 6, 10, 0, 12, 10, 0, 8]
private def certificate249 : Certificate :=
  .motif 1 2 0 2 0 1
    (.clash (0, 1) (3, 1))
private theorem check249 : check [] state249 certificate249 = true := by
  decide +kernel
private theorem closed249 : Closed.{u} state249 :=
  sound (known := []) trivial check249

def state250 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 8, 9, 10, 0, 12, 4, 0, 2]
private def certificate250 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (3, 2))
    (.clash (2, 1) (2, 3))
    (.clash (0, 0) (0, 2))
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 3) (2, 3))
      (.clash (2, 2) (2, 3))
      (.clash (0, 0) (1, 0))
      (.transversal ![1, 0, 2, 3]
        (.clash (0, 1) (3, 1))
        (.transversal ![1, 2, 0, 3]
          (.clash (0, 1) (2, 1))
          (.clash (2, 0) (2, 2))
          (.clash (0, 1) (0, 2))
          (.clash (2, 0) (2, 1))
          (.clash (0, 2) (1, 2))
          (.transversal ![1, 2, 3, 0]
            (.clash (0, 1) (2, 1))
            (.clash (0, 0) (0, 1))
            (.motif 1 3 2 0 3 1
              (.clash (0, 1) (2, 1)))
            (.clash (1, 2) (3, 2))
            (.transversal ![3, 1, 2, 0]
              (.clash (0, 2) (0, 3))
              (.clash (0, 1) (0, 3))
              (.motif 0 1 2 1 2 3
                (.clash (0, 0) (0, 2)))
              (.clash (0, 1) (0, 2))
              (.clash (0, 2) (1, 2))
              (.clash (0, 1) (2, 1)))
            (.clash (0, 0) (3, 0))))
        (.clash (0, 1) (0, 2))
        (.clash (1, 0) (1, 3))
        (.clash (1, 0) (1, 1))
        (.clash (0, 2) (2, 2)))
      (.clash (1, 0) (1, 3))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 1) (2, 1))
        (.reuse 0)
        (.clash (0, 1) (0, 2))
        (.clash (2, 0) (2, 1))
        (.clash (0, 2) (1, 2))
        (.reuse 1)))
    (.clash (0, 2) (1, 2))
    (.clash (1, 1) (2, 1))
private theorem check250 : check [state248, state249] state250 certificate250 = true := by
  decide +kernel
private theorem closed250 : Closed.{u} state250 :=
  sound (known := [state248, state249]) ⟨closed248.{u}, ⟨closed249.{u}, trivial⟩⟩ check250

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary13 : Known.{u} [state242, state244, state246, state247, state250] :=
  ⟨closed242.{u}, ⟨closed244.{u}, ⟨closed246.{u}, ⟨closed247.{u}, ⟨closed250.{u}, trivial⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
