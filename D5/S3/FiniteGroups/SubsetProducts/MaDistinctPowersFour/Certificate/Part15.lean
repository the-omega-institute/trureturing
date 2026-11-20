/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part15
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part15
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Order-four certificate decisions for chunks 270 through 290. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part14

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed267 : Closed.{u} state267 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed268 : Closed.{u} state268 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed269 : Closed.{u} state269 :=
  known_of_mem boundary14.{u} (by decide)

private def state270 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 7, 9, 10]
private def certificate270 : Certificate :=
  .transversal ![0, 1, 3, 2]
    (.clash (1, 1) (1, 2))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (2, 0))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (3, 1))
          (.clash (1, 0) (2, 0))
          (.clash (0, 1) (2, 1))
          (.motif 1 2 3 3 2 0
            (.clash (0, 0) (3, 0)))
          (.clash (2, 1) (3, 1))
          (.clash (2, 0) (2, 1)))
        (.clash (0, 0) (2, 0))
        (.clash (1, 2) (2, 2))
        (.clash (2, 0) (2, 2)))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (2, 1))
      (.clash (0, 0) (1, 0))
      (.transversal ![2, 0, 3, 1]
        (.clash (0, 2) (3, 2))
        (.clash (0, 0) (0, 2))
        (.transversal ![2, 1, 3, 0]
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (0, 2))
          (.clash (3, 0) (3, 1))
          (.clash (1, 1) (1, 2))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (0, 2))
            (.reuse 0)
            (.clash (0, 1) (1, 1))
            (.clash (0, 2) (2, 2))
            (.clash (1, 1) (1, 3))
            (.clash (3, 0) (3, 3)))
          (.clash (0, 0) (3, 0)))
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 3))
        (.clash (1, 2) (1, 3)))
      (.clash (1, 2) (3, 2)))
    (.clash (1, 2) (3, 2))
    (.reuse 1)
    (.clash (1, 1) (2, 1))
    (.clash (2, 1) (2, 3))
private theorem check270 : check [state268, state269] state270 certificate270 = true := by
  decide +kernel
private theorem closed270 : Closed.{u} state270 :=
  sound (known := [state268, state269]) ⟨closed268.{u}, ⟨closed269.{u}, trivial⟩⟩ check270

def state271 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 7, 14, 10]
private def certificate271 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 2) (1, 3))
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 0) (3, 0))
        (.clash (1, 3) (3, 3))
        (.clash (3, 0) (3, 1))
        (.clash (3, 0) (3, 3)))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 0) (0, 1))
        (.clash (2, 2) (2, 3))
        (.clash (3, 0) (3, 3))
        (.clash (2, 1) (2, 3))
        (.clash (0, 0) (3, 0))
        (.transversal ![0, 1, 3, 2]
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (3, 0))
          (.clash (1, 2) (3, 2))
          (.transversal ![1, 0, 3, 2]
            (.motif 1 3 0 1 3 0
              (.clash (1, 2) (1, 3)))
            (.clash (0, 1) (1, 1))
            (.clash (2, 2) (3, 2))
            (.clash (1, 0) (1, 1))
            (.transversal ![2, 0, 1, 3]
              (.clash (0, 2) (3, 2))
              (.clash (0, 0) (0, 2))
              (.clash (0, 1) (0, 2))
              (.clash (0, 0) (1, 0))
              (.clash (2, 2) (3, 2))
              (.clash (0, 0) (0, 1)))
            (.clash (3, 0) (3, 2)))
          (.reuse 0)
          (.clash (3, 0) (3, 2))))
      (.clash (0, 0) (2, 0))
      (.clash (1, 2) (2, 2))
      (.clash (2, 0) (2, 2)))
    (.clash (1, 2) (3, 2))
    (.clash (2, 1) (3, 1))
    (.clash (3, 1) (3, 2))
    (.reuse 1)
private theorem check271 : check [state267, state270] state271 certificate271 = true := by
  decide +kernel
private theorem closed271 : Closed.{u} state271 :=
  sound (known := [state267, state270]) ⟨closed267.{u}, ⟨closed270.{u}, trivial⟩⟩ check271

private def state272 : Partition := #v[0, 1, 2, 3, 1, 5, 6, 0, 5, 0, 1, 6, 12, 2, 0, 1]
private def certificate272 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.clash (1, 1) (3, 1))
    (.clash (0, 2) (1, 2))
    (.clash (3, 0) (3, 1))
    (.clash (1, 1) (1, 2))
    (.clash (2, 0) (3, 0))
    (.motif 1 3 0 0 2 3
      (.clash (0, 3) (2, 3)))
private theorem check272 : check [] state272 certificate272 = true := by
  decide +kernel
private theorem closed272 : Closed.{u} state272 :=
  sound (known := []) trivial check272

private def state273 : Partition := #v[0, 1, 2, 3, 1, 5, 6, 0, 8, 0, 1, 11, 12, 6, 0, 1]
private def certificate273 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (3, 1))
    (.clash (2, 2) (2, 3))
    (.clash (1, 0) (3, 0))
    (.motif 2 3 0 1 3 2
      (.clash (0, 2) (1, 2)))
    (.clash (3, 0) (3, 1))
    (.transversal ![2, 0, 3, 1]
      (.clash (0, 1) (0, 2))
      (.transversal ![2, 3, 0, 1]
        (.clash (0, 0) (0, 2))
        (.clash (2, 0) (2, 3))
        (.clash (0, 2) (1, 2))
        (.clash (0, 0) (2, 0))
        (.clash (1, 2) (1, 3))
        (.transversal ![2, 1, 0, 3]
          (.transversal ![3, 1, 0, 2]
            (.clash (0, 2) (0, 3))
            (.columns)
            (.clash (0, 0) (0, 3))
            (.clash (0, 2) (1, 2))
            (.clash (0, 0) (0, 2))
            (.clash (0, 0) (2, 0)))
          (.clash (0, 2) (1, 2))
          (.clash (0, 1) (0, 2))
          (.clash (1, 1) (1, 2))
          (.clash (0, 1) (1, 1))
          (.clash (0, 1) (3, 1))))
      (.clash (0, 2) (1, 2))
      (.clash (1, 0) (3, 0))
      (.clash (0, 1) (3, 1))
      (.clash (3, 0) (3, 1)))
private theorem check273 : check [] state273 certificate273 = true := by
  decide +kernel
private theorem closed273 : Closed.{u} state273 :=
  sound (known := []) trivial check273

private def state274 : Partition := #v[0, 1, 2, 3, 1, 5, 6, 0, 8, 0, 1, 11, 12, 11, 0, 1]
private def certificate274 : Certificate :=
  .motif 2 3 1 3 2 1
    (.clash (0, 1) (1, 1))
private theorem check274 : check [] state274 certificate274 = true := by
  decide +kernel
private theorem closed274 : Closed.{u} state274 :=
  sound (known := []) trivial check274

private def state275 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 1, 4, 12, 13, 0, 1]
private def certificate275 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (1, 2) (2, 2))
    (.clash (2, 2) (2, 3))
    (.clash (3, 0) (3, 3))
    (.clash (1, 0) (1, 2))
    (.transversal ![0, 2, 3, 1]
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (1, 0))
      (.clash (2, 1) (3, 1))
      (.clash (1, 0) (1, 2))
      (.clash (3, 0) (3, 1))
      (.motif 2 3 1 3 2 1
        (.clash (0, 1) (1, 1))))
    (.clash (1, 0) (3, 0))
private theorem check275 : check [] state275 certificate275 = true := by
  decide +kernel
private theorem closed275 : Closed.{u} state275 :=
  sound (known := []) trivial check275

private def state276 : Partition := #v[0, 1, 11, 3, 1, 5, 6, 0, 5, 0, 1, 11, 6, 11, 5, 1]
private def certificate276 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.clash (0, 1) (0, 3))
    (.clash (0, 0) (0, 3))
    (.motif 0 1 2 0 1 3
      (.clash (0, 1) (0, 2)))
    (.clash (0, 0) (0, 1))
    (.clash (0, 1) (1, 1))
    (.clash (0, 0) (2, 0))
private theorem check276 : check [] state276 certificate276 = true := by
  decide +kernel
private theorem closed276 : Closed.{u} state276 :=
  sound (known := []) trivial check276

private def state277 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 1, 11, 12, 13, 8, 1]
private def certificate277 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (0, 0) (0, 2))
    (.clash (0, 2) (3, 2))
    (.transversal ![2, 1, 0, 3]
      (.clash (1, 1) (3, 1))
      (.clash (0, 2) (3, 2))
      (.clash (0, 1) (0, 2))
      (.transversal ![0, 2, 3, 1]
        (.clash (1, 2) (1, 3))
        (.clash (1, 3) (2, 3))
        (.clash (0, 0) (0, 2))
        (.transversal ![1, 0, 3, 2]
          (.transversal ![2, 1, 3, 0]
            (.clash (0, 2) (3, 2))
            (.clash (0, 2) (1, 2))
            (.clash (3, 0) (3, 1))
            (.clash (1, 1) (1, 2))
            (.clash (2, 0) (3, 0))
            (.motif 2 3 1 2 0 3
              (.clash (0, 0) (2, 0))))
          (.clash (1, 2) (2, 2))
          (.clash (0, 1) (1, 1))
          (.clash (1, 0) (1, 2))
          (.clash (1, 0) (1, 1))
          (.clash (1, 1) (1, 2)))
        (.clash (0, 2) (1, 2))
        (.transversal ![1, 2, 3, 0]
          (.clash (1, 2) (2, 2))
          (.clash (0, 1) (0, 2))
          (.clash (3, 0) (3, 3))
          (.clash (0, 2) (1, 2))
          (.transversal ![1, 0, 3, 2]
            (.reuse 0)
            (.clash (0, 1) (0, 2))
            (.clash (0, 1) (1, 1))
            (.motif 1 2 3 1 3 0
              (.clash (0, 0) (3, 0)))
            (.clash (1, 0) (1, 1))
            (.clash (0, 2) (3, 2)))
          (.clash (3, 0) (3, 1))))
      (.clash (0, 1) (1, 1))
      (.clash (2, 0) (2, 2)))
    (.clash (0, 0) (2, 0))
    (.clash (2, 1) (3, 1))
    (.clash (3, 1) (3, 2))
private theorem check277 : check [state276] state277 certificate277 = true := by
  decide +kernel
private theorem closed277 : Closed.{u} state277 :=
  sound (known := [state276]) ⟨closed276.{u}, trivial⟩ check277

private def state278 : Partition := #v[0, 1, 2, 3, 4, 5, 1, 0, 8, 0, 10, 1, 1, 13, 5, 10]
private def certificate278 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 0) (0, 1))
    (.clash (2, 0) (2, 3))
    (.clash (0, 1) (1, 1))
    (.clash (0, 0) (2, 0))
    (.clash (1, 1) (1, 3))
    (.motif 2 3 1 2 0 3
      (.clash (0, 0) (2, 0)))
private theorem check278 : check [] state278 certificate278 = true := by
  decide +kernel
private theorem closed278 : Closed.{u} state278 :=
  sound (known := []) trivial check278

private def state279 : Partition := #v[0, 1, 2, 3, 4, 5, 1, 0, 8, 0, 10, 11, 1, 11, 14, 10]
private def certificate279 : Certificate :=
  .transversal ![3, 2, 0, 1]
    (.clash (0, 1) (0, 3))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (0, 3))
      (.transversal ![0, 1, 3, 2]
        (.clash (1, 1) (1, 3))
        (.clash (0, 0) (0, 2))
        (.motif 0 3 1 2 0 1
          (.clash (1, 1) (1, 3)))
        (.clash (1, 1) (3, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (1, 0) (1, 2))
          (.clash (0, 1) (0, 2))
          (.clash (0, 1) (1, 1))
          (.motif 1 3 0 2 1 0
            (.clash (1, 1) (1, 3)))
          (.clash (1, 0) (1, 1))
          (.clash (0, 2) (3, 2)))
        (.clash (0, 2) (3, 2)))
      (.clash (0, 0) (0, 3))
      (.clash (1, 3) (2, 3))
      (.clash (0, 3) (2, 3)))
    (.clash (0, 3) (2, 3))
    (.clash (2, 0) (3, 0))
    (.clash (0, 1) (3, 1))
    (.clash (2, 0) (2, 3))
private theorem check279 : check [] state279 certificate279 = true := by
  decide +kernel
private theorem closed279 : Closed.{u} state279 :=
  sound (known := []) trivial check279

private def state280 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 6, 0, 10, 11, 1, 13, 14, 10]
private def certificate280 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 0) (0, 1))
    (.clash (2, 0) (3, 0))
    (.clash (3, 0) (3, 2))
    (.clash (0, 0) (2, 0))
    (.transversal ![3, 2, 1, 0]
      (.transversal ![3, 1, 2, 0]
        (.clash (1, 1) (1, 2))
        (.clash (0, 3) (3, 3))
        (.clash (0, 1) (0, 3))
        (.transversal ![2, 0, 1, 3]
          (.motif 0 1 3 2 3 0
            (.clash (0, 1) (0, 3)))
          (.clash (0, 0) (0, 2))
          (.clash (0, 2) (2, 2))
          (.clash (0, 0) (1, 0))
          (.clash (1, 0) (1, 1))
          (.clash (1, 1) (1, 3)))
        (.clash (0, 1) (1, 1))
        (.clash (3, 0) (3, 3)))
      (.clash (0, 0) (0, 3))
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (2, 0))
      (.clash (2, 0) (3, 0))
      (.clash (0, 0) (0, 1)))
    (.clash (1, 2) (3, 2))
private theorem check280 : check [] state280 certificate280 = true := by
  decide +kernel
private theorem closed280 : Closed.{u} state280 :=
  sound (known := []) trivial check280

private def state281 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 10, 11, 1, 13, 14, 10]
private def certificate281 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.transversal ![0, 2, 3, 1]
      (.clash (0, 0) (0, 1))
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (3, 1))
      (.transversal ![0, 1, 3, 2]
        (.clash (1, 1) (1, 3))
        (.clash (0, 0) (0, 1))
        (.transversal ![2, 0, 1, 3]
          (.transversal ![2, 1, 0, 3]
            (.clash (1, 0) (1, 1))
            (.clash (1, 0) (2, 0))
            (.clash (0, 2) (2, 2))
            (.transversal ![2, 3, 0, 1]
              (.clash (0, 0) (0, 2))
              (.clash (1, 0) (1, 1))
              (.motif 0 3 1 2 0 1
                (.clash (0, 0) (2, 0)))
              (.clash (0, 0) (2, 0))
              (.clash (2, 1) (3, 1))
              (.clash (1, 1) (3, 1)))
            (.motif 1 2 0 1 3 2
              (.clash (0, 0) (0, 2)))
            (.clash (2, 0) (2, 2)))
          (.clash (0, 0) (0, 2))
          (.clash (0, 2) (2, 2))
          (.clash (0, 0) (1, 0))
          (.motif 1 3 0 0 2 3
            (.clash (0, 1) (0, 3)))
          (.clash (1, 3) (3, 3)))
        (.clash (0, 1) (1, 1))
        (.reuse 0)
        (.clash (1, 2) (3, 2)))
      (.clash (0, 1) (3, 1))
      (.reuse 1))
    (.clash (2, 0) (3, 0))
    (.clash (3, 0) (3, 3))
    (.reuse 2)
    (.clash (1, 2) (2, 2))
    (.clash (2, 0) (2, 2))
private theorem check281 : check [state278, state279, state280] state281 certificate281 = true := by
  decide +kernel
private theorem closed281 : Closed.{u} state281 :=
  sound (known := [state278, state279, state280]) ⟨closed278.{u}, ⟨closed279.{u}, ⟨closed280.{u}, trivial⟩⟩⟩ check281

private def state282 : Partition := #v[0, 1, 2, 3, 4, 5, 1, 2, 8, 0, 10, 1, 1, 2, 5, 10]
private def certificate282 : Certificate :=
  .transversal ![2, 0, 1, 3]
    (.clash (1, 0) (1, 3))
    (.clash (0, 0) (0, 2))
    (.clash (0, 2) (2, 2))
    (.clash (0, 0) (1, 0))
    (.transversal ![3, 0, 1, 2]
      (.clash (0, 3) (3, 3))
      (.clash (0, 0) (0, 3))
      (.motif 0 1 2 3 2 1
        (.clash (0, 0) (0, 2)))
      (.clash (0, 0) (1, 0))
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (2, 1)))
    (.clash (2, 1) (2, 2))
private theorem check282 : check [] state282 certificate282 = true := by
  decide +kernel
private theorem closed282 : Closed.{u} state282 :=
  sound (known := []) trivial check282

private def state283 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 6, 12, 7, 5, 10]
private def certificate283 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.transversal ![1, 2, 0, 3]
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (2, 0))
      (.transversal ![2, 0, 3, 1]
        (.clash (0, 1) (0, 2))
        (.clash (0, 2) (1, 2))
        (.transversal ![2, 1, 3, 0]
          (.clash (0, 2) (3, 2))
          (.clash (0, 2) (1, 2))
          (.clash (3, 0) (3, 1))
          (.clash (1, 1) (1, 2))
          (.clash (3, 0) (3, 2))
          (.transversal ![3, 0, 1, 2]
            (.clash (0, 1) (0, 3))
            (.clash (0, 0) (0, 3))
            (.motif 0 3 1 3 1 2
              (.clash (1, 0) (1, 2)))
            (.clash (0, 0) (0, 1))
            (.clash (0, 1) (1, 1))
            (.clash (1, 1) (2, 1))))
        (.clash (1, 0) (1, 2))
        (.clash (0, 1) (3, 1))
        (.clash (1, 2) (1, 3)))
      (.clash (2, 0) (2, 3))
      (.clash (1, 2) (2, 2))
      (.clash (2, 0) (2, 2)))
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 1) (3, 1))
      (.clash (1, 2) (2, 2))
      (.transversal ![2, 3, 1, 0]
        (.reuse 0)
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2))
        (.clash (2, 1) (3, 1))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1)))
      (.clash (1, 3) (3, 3))
      (.clash (3, 0) (3, 1))
      (.clash (3, 0) (3, 3)))
    (.clash (0, 1) (1, 1))
    (.clash (1, 0) (1, 2))
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (1, 2))
private theorem check283 : check [state282] state283 certificate283 = true := by
  decide +kernel
private theorem closed283 : Closed.{u} state283 :=
  sound (known := [state282]) ⟨closed282.{u}, trivial⟩ check283

private def state284 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 6, 12, 7, 14, 10]
private def certificate284 : Certificate :=
  .transversal ![0, 1, 3, 2]
    (.clash (1, 1) (2, 1))
    (.clash (2, 1) (2, 3))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 2, 0, 3]
        (.clash (1, 0) (1, 2))
        (.clash (1, 0) (2, 0))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (3, 1))
          (.clash (1, 0) (2, 0))
          (.clash (0, 0) (0, 1))
          (.motif 2 1 3 3 0 2
            (.clash (0, 0) (2, 0)))
          (.clash (2, 1) (3, 1))
          (.clash (0, 0) (2, 0)))
        (.clash (2, 0) (2, 3))
        (.clash (1, 2) (2, 2))
        (.clash (2, 0) (2, 2)))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 3))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (3, 1))
          (.clash (1, 2) (2, 2))
          (.transversal ![2, 3, 1, 0]
            (.motif 0 3 1 2 0 1
              (.clash (1, 1) (2, 1)))
            (.clash (0, 0) (0, 2))
            (.clash (0, 1) (0, 2))
            (.clash (0, 0) (2, 0))
            (.clash (0, 1) (3, 1))
            (.clash (0, 0) (0, 1)))
          (.clash (1, 3) (3, 3))
          (.clash (2, 0) (3, 0))
          (.clash (3, 0) (3, 3)))
        (.clash (2, 1) (3, 1))
        (.clash (0, 0) (2, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (1, 0))
      (.clash (1, 2) (3, 2)))
    (.clash (1, 1) (1, 2))
    (.reuse 0)
    (.clash (1, 2) (3, 2))
private theorem check284 : check [state283] state284 certificate284 = true := by
  decide +kernel
private theorem closed284 : Closed.{u} state284 :=
  sound (known := [state283]) ⟨closed283.{u}, trivial⟩ check284

private def state285 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 11, 12, 7, 14, 10]
private def certificate285 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 0) (3, 0))
        (.clash (1, 3) (3, 3))
        (.clash (3, 0) (3, 1))
        (.clash (3, 0) (3, 3)))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 0) (0, 1))
        (.clash (2, 2) (2, 3))
        (.clash (3, 0) (3, 3))
        (.clash (2, 1) (2, 3))
        (.clash (0, 0) (3, 0))
        (.transversal ![0, 1, 3, 2]
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (3, 0))
          (.clash (1, 2) (3, 2))
          (.transversal ![1, 0, 3, 2]
            (.motif 1 3 0 1 3 0
              (.clash (1, 2) (1, 3)))
            (.clash (0, 1) (1, 1))
            (.clash (2, 2) (3, 2))
            (.clash (1, 0) (1, 1))
            (.transversal ![2, 0, 1, 3]
              (.clash (0, 2) (3, 2))
              (.clash (0, 0) (0, 2))
              (.clash (0, 1) (0, 2))
              (.clash (0, 0) (1, 0))
              (.clash (2, 2) (3, 2))
              (.clash (0, 0) (0, 1)))
            (.clash (3, 0) (3, 2)))
          (.reuse 0)
          (.clash (3, 0) (3, 2))))
      (.clash (0, 0) (2, 0))
      (.clash (1, 2) (2, 2))
      (.clash (2, 0) (2, 2)))
    (.clash (2, 1) (2, 3))
    (.clash (2, 1) (3, 1))
    (.reuse 1)
    (.clash (1, 2) (1, 3))
    (.clash (1, 3) (2, 3))
private theorem check285 : check [state267, state284] state285 certificate285 = true := by
  decide +kernel
private theorem closed285 : Closed.{u} state285 :=
  sound (known := [state267, state284]) ⟨closed267.{u}, ⟨closed284.{u}, trivial⟩⟩ check285

def state286 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 10, 11, 12, 13, 14, 10]
private def certificate286 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 0) (0, 1))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 2) (3, 2))
        (.clash (0, 0) (2, 0))
        (.transversal ![1, 0, 3, 2]
          (.transversal ![0, 2, 3, 1]
            (.clash (1, 2) (1, 3))
            (.clash (1, 3) (2, 3))
            (.clash (2, 1) (3, 1))
            (.transversal ![2, 0, 3, 1]
              (.clash (0, 1) (0, 2))
              (.clash (0, 2) (1, 2))
              (.transversal ![2, 1, 0, 3]
                (.clash (1, 1) (3, 1))
                (.motif 0 2 1 0 2 1
                  (.clash (1, 1) (3, 1)))
                (.clash (0, 1) (0, 2))
                (.reuse 0)
                (.clash (0, 1) (1, 1))
                (.clash (1, 0) (2, 0)))
              (.clash (1, 0) (1, 2))
              (.clash (0, 1) (3, 1))
              (.motif 2 3 0 1 3 2
                (.clash (0, 2) (1, 2))))
            (.reuse 1)
            (.reuse 2))
          (.clash (2, 2) (2, 3))
          (.clash (0, 0) (0, 1))
          (.reuse 3)
          (.clash (0, 0) (1, 0))
          (.clash (1, 3) (2, 3)))
        (.reuse 4))
      (.reuse 5)
      (.clash (1, 3) (3, 3))
      (.clash (0, 0) (3, 0))
      (.clash (3, 0) (3, 3)))
    (.clash (2, 1) (2, 2))
    (.clash (2, 1) (3, 1))
    (.clash (1, 3) (3, 3))
    (.reuse 6)
    (.clash (3, 1) (3, 3))
private theorem check286 : check [state272, state273, state274, state275, state277, state281, state285] state286 certificate286 = true := by
  decide +kernel
private theorem closed286 : Closed.{u} state286 :=
  sound (known := [state272, state273, state274, state275, state277, state281, state285]) ⟨closed272.{u}, ⟨closed273.{u}, ⟨closed274.{u}, ⟨closed275.{u}, ⟨closed277.{u}, ⟨closed281.{u}, ⟨closed285.{u}, trivial⟩⟩⟩⟩⟩⟩⟩ check286

def state287 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 2, 0, 1, 1, 4, 7, 0]
private def certificate287 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (0, 2) (3, 2))
    (.clash (2, 0) (2, 1))
    (.clash (2, 1) (3, 1))
    (.motif 2 3 0 0 3 2
      (.clash (0, 1) (0, 2)))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (2, 0))
private theorem check287 : check [] state287 certificate287 = true := by
  decide +kernel
private theorem closed287 : Closed.{u} state287 :=
  sound (known := []) trivial check287

def state288 : Partition := #v[0, 1, 2, 3, 4, 0, 1, 7, 8, 7, 0, 1, 1, 13, 7, 0]
private def certificate288 : Certificate :=
  .motif 1 2 0 1 3 2
    (.clash (0, 2) (3, 2))
private theorem check288 : check [] state288 certificate288 = true := by
  decide +kernel
private theorem closed288 : Closed.{u} state288 :=
  sound (known := []) trivial check288

private def state289 : Partition := #v[0, 1, 2, 3, 4, 8, 1, 2, 8, 2, 0, 1, 2, 4, 8, 0]
private def certificate289 : Certificate :=
  .transversal ![3, 1, 2, 0]
    (.motif 0 1 2 1 3 2
      (.clash (0, 0) (0, 3)))
    (.clash (0, 0) (0, 3))
    (.clash (0, 2) (0, 3))
    (.clash (0, 0) (2, 0))
    (.clash (0, 2) (3, 2))
    (.clash (0, 0) (0, 2))
private theorem check289 : check [] state289 certificate289 = true := by
  decide +kernel
private theorem closed289 : Closed.{u} state289 :=
  sound (known := []) trivial check289

def state290 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 6, 12, 13, 5, 0]
private def certificate290 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 3) (3, 3))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (3, 2))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 2, 0, 3]
        (.clash (1, 0) (1, 2))
        (.clash (1, 0) (2, 0))
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (2, 3))
        (.clash (1, 2) (2, 2))
        (.clash (0, 0) (2, 0)))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (2, 3))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 1))
        (.clash (1, 1) (1, 3))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.motif 2 3 0 0 3 2
            (.clash (0, 1) (0, 2)))
          (.clash (1, 3) (3, 3))
          (.transversal ![2, 1, 3, 0]
            (.clash (0, 2) (3, 2))
            (.clash (0, 1) (0, 2))
            (.transversal ![2, 0, 3, 1]
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (0, 2))
              (.clash (2, 1) (3, 1))
              (.clash (1, 0) (1, 2))
              (.reuse 0)
              (.clash (0, 1) (3, 1)))
            (.clash (0, 1) (1, 1))
            (.clash (1, 1) (1, 3))
            (.clash (0, 1) (2, 1)))
          (.clash (0, 0) (3, 0))))
      (.clash (0, 1) (1, 1))
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (1, 2)))
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
private theorem check290 : check [state289] state290 certificate290 = true := by
  decide +kernel
private theorem closed290 : Closed.{u} state290 :=
  sound (known := [state289]) ⟨closed289.{u}, trivial⟩ check290

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary15 : Known.{u} [state271, state286, state287, state288, state290] :=
  ⟨closed271.{u}, ⟨closed286.{u}, ⟨closed287.{u}, ⟨closed288.{u}, ⟨closed290.{u}, trivial⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
