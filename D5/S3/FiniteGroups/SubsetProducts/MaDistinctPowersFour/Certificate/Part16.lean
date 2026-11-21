/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part16
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part16
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part16.certificate310
   digest: Order-four certificate decisions for chunks 291 through 310. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part01
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part02
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part04
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part15

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed7 : Closed.{u} state7 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed16 : Closed.{u} state16 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed17 : Closed.{u} state17 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed18 : Closed.{u} state18 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed19 : Closed.{u} state19 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed21 : Closed.{u} state21 :=
  known_of_mem boundary02.{u} (by decide)

private theorem closed74 : Closed.{u} state74 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed75 : Closed.{u} state75 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed77 : Closed.{u} state77 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed287 : Closed.{u} state287 :=
  known_of_mem boundary15.{u} (by decide)

private theorem closed288 : Closed.{u} state288 :=
  known_of_mem boundary15.{u} (by decide)

private theorem closed290 : Closed.{u} state290 :=
  known_of_mem boundary15.{u} (by decide)

private def state291 : Partition := #v[0, 1, 2, 3, 3, 5, 6, 7, 1, 9, 0, 6, 12, 6, 5, 0]
private def certificate291 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.clash (0, 1) (0, 3))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (1, 1))
    (.clash (0, 3) (2, 3))
    (.clash (1, 0) (1, 1))
    (.clash (1, 1) (1, 2))
private theorem check291 : check [] state291 certificate291 = true := by
  decide +kernel
private theorem closed291 : Closed.{u} state291 :=
  sound (known := []) trivial check291

private def state292 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 1, 9, 0, 11, 11, 6, 14, 0]
private def certificate292 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.transversal ![0, 3, 1, 2]
      (.clash (0, 0) (0, 1))
      (.clash (2, 1) (2, 2))
      (.clash (2, 2) (3, 2))
      (.clash (0, 1) (2, 1))
      (.motif 2 3 1 3 2 0
        (.clash (0, 0) (1, 0)))
      (.transversal ![1, 0, 3, 2]
        (.clash (1, 0) (1, 3))
        (.clash (1, 3) (2, 3))
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (3, 0))
        (.transversal ![2, 0, 3, 1]
          (.clash (0, 2) (3, 2))
          (.transversal ![0, 1, 3, 2]
            (.transversal ![3, 1, 0, 2]
              (.clash (0, 0) (0, 3))
              (.clash (0, 1) (0, 3))
              (.motif 0 1 2 1 0 3
                (.clash (0, 0) (0, 2)))
              (.clash (0, 0) (0, 1))
              (.clash (0, 0) (1, 0))
              (.clash (0, 1) (2, 1)))
            (.clash (0, 0) (0, 2))
            (.clash (0, 0) (1, 0))
            (.motif 1 2 3 0 3 1
              (.clash (0, 1) (3, 1)))
            (.clash (1, 0) (1, 1))
            (.clash (0, 2) (3, 2)))
          (.clash (0, 2) (1, 2))
          (.clash (1, 0) (3, 0))
          (.clash (1, 0) (1, 2))
          (.clash (3, 0) (3, 1)))
        (.clash (2, 1) (2, 3))))
    (.clash (0, 0) (0, 1))
    (.clash (2, 0) (2, 3))
    (.clash (1, 3) (3, 3))
    (.clash (1, 3) (2, 3))
    (.clash (0, 0) (3, 0))
private theorem check292 : check [] state292 certificate292 = true := by
  decide +kernel
private theorem closed292 : Closed.{u} state292 :=
  sound (known := []) trivial check292

private def state293 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 6, 4, 0, 2, 12, 6, 4, 0]
private def certificate293 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.transversal ![1, 2, 3, 0]
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (0, 2))
      (.transversal ![3, 1, 2, 0]
        (.clash (0, 2) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 2) (1, 2))
      (.clash (2, 0) (3, 0))
      (.motif 1 3 0 2 0 1
        (.clash (0, 1) (2, 1))))
    (.clash (0, 1) (3, 1))
    (.clash (0, 1) (2, 1))
    (.clash (1, 2) (1, 3))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (1, 2))
private theorem check293 : check [] state293 certificate293 = true := by
  decide +kernel
private theorem closed293 : Closed.{u} state293 :=
  sound (known := []) trivial check293

private def state294 : Partition := #v[5, 1, 2, 3, 4, 5, 3, 7, 3, 7, 5, 1, 7, 3, 1, 5]
private def certificate294 : Certificate :=
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
private theorem check294 : check [] state294 certificate294 = true := by
  decide +kernel
private theorem closed294 : Closed.{u} state294 :=
  sound (known := []) trivial check294

private def state295 : Partition := #v[5, 1, 2, 3, 4, 5, 3, 7, 3, 9, 5, 11, 12, 3, 7, 5]
private def certificate295 : Certificate :=
  .motif 1 3 0 3 1 2
    (.clash (0, 0) (0, 2))
private theorem check295 : check [] state295 certificate295 = true := by
  decide +kernel
private theorem closed295 : Closed.{u} state295 :=
  sound (known := []) trivial check295

private def state296 : Partition := #v[5, 1, 2, 3, 4, 5, 3, 7, 3, 9, 5, 11, 12, 3, 9, 5]
private def certificate296 : Certificate :=
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
private theorem check296 : check [] state296 certificate296 = true := by
  decide +kernel
private theorem closed296 : Closed.{u} state296 :=
  sound (known := []) trivial check296

private def state297 : Partition := #v[5, 1, 2, 3, 4, 5, 6, 7, 6, 9, 5, 11, 12, 6, 14, 5]
private def certificate297 : Certificate :=
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
private theorem check297 : check [state294, state295, state296] state297 certificate297 = true := by
  decide +kernel
private theorem closed297 : Closed.{u} state297 :=
  sound (known := [state294, state295, state296]) ⟨closed294.{u}, ⟨closed295.{u}, ⟨closed296.{u}, trivial⟩⟩⟩ check297

private def state298 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 6, 9, 0, 11, 12, 6, 14, 0]
private def certificate298 : Certificate :=
  .transversal ![2, 1, 0, 3]
    (.transversal ![2, 0, 1, 3]
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (2, 1))
      (.clash (0, 0) (0, 2))
      (.transversal ![2, 0, 3, 1]
        (.clash (1, 0) (1, 1))
        (.transversal ![0, 3, 1, 2]
          (.clash (1, 3) (3, 3))
          (.clash (0, 0) (1, 0))
          (.clash (2, 2) (3, 2))
          (.clash (1, 0) (1, 3))
          (.transversal ![1, 0, 3, 2]
            (.clash (0, 1) (2, 1))
            (.clash (0, 1) (0, 2))
            (.transversal ![1, 2, 3, 0]
              (.clash (0, 1) (3, 1))
              (.clash (0, 1) (0, 2))
              (.clash (3, 0) (3, 2))
              (.clash (0, 2) (1, 2))
              (.clash (2, 0) (3, 0))
              (.transversal ![3, 1, 0, 2]
                (.clash (0, 2) (0, 3))
                (.motif 0 1 2 3 1 2
                  (.clash (0, 0) (0, 1)))
                (.clash (0, 1) (0, 3))
                (.clash (0, 2) (1, 2))
                (.clash (0, 1) (0, 2))
                (.clash (0, 1) (3, 1))))
            (.clash (1, 0) (1, 1))
            (.clash (1, 0) (1, 3))
            (.clash (0, 2) (3, 2)))
          (.reuse 0))
        (.clash (0, 2) (1, 2))
        (.clash (2, 1) (2, 3))
        (.clash (1, 0) (1, 2))
        (.clash (2, 0) (2, 3)))
      (.clash (0, 0) (1, 0))
      (.clash (2, 1) (2, 2)))
    (.clash (0, 2) (1, 2))
    (.clash (0, 0) (0, 2))
    (.clash (1, 1) (1, 2))
    (.reuse 1)
    (.clash (0, 0) (2, 0))
private theorem check298 : check [state293, state297] state298 certificate298 = true := by
  decide +kernel
private theorem closed298 : Closed.{u} state298 :=
  sound (known := [state293, state297]) ⟨closed293.{u}, ⟨closed297.{u}, trivial⟩⟩ check298

private def state299 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 6, 14, 0]
private def certificate299 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (3, 1))
    (.transversal ![1, 2, 3, 0]
      (.clash (0, 1) (3, 1))
      (.clash (2, 0) (2, 3))
      (.clash (2, 0) (3, 0))
      (.transversal ![3, 0, 2, 1]
        (.transversal ![0, 1, 3, 2]
          (.transversal ![2, 1, 3, 0]
            (.clash (0, 0) (0, 2))
            (.clash (0, 2) (1, 2))
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
            (.clash (1, 1) (1, 2))
            (.clash (0, 0) (3, 0))
            (.clash (3, 0) (3, 1)))
          (.clash (1, 2) (2, 2))
          (.clash (2, 2) (3, 2))
          (.clash (1, 1) (1, 2))
          (.reuse 1)
          (.clash (1, 2) (3, 2)))
        (.clash (0, 0) (0, 3))
        (.clash (0, 3) (2, 3))
        (.clash (0, 0) (1, 0))
        (.clash (1, 0) (1, 2))
        (.clash (1, 2) (2, 2)))
      (.clash (3, 0) (3, 1))
      (.reuse 2))
    (.clash (0, 0) (0, 1))
    (.reuse 3)
    (.clash (1, 2) (2, 2))
    (.clash (0, 0) (2, 0))
private theorem check299 : check [state7, state291, state292, state298] state299 certificate299 = true := by
  decide +kernel
private theorem closed299 : Closed.{u} state299 :=
  sound (known := [state7, state291, state292, state298]) ⟨closed7.{u}, ⟨closed291.{u}, ⟨closed292.{u}, ⟨closed298.{u}, trivial⟩⟩⟩⟩ check299

private def state300 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 11, 5, 0]
private def certificate300 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.clash (1, 3) (3, 3))
    (.clash (2, 1) (2, 2))
    (.clash (2, 2) (3, 2))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![3, 0, 2, 1]
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 3) (2, 3))
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (3, 1))
        (.clash (2, 2) (2, 3)))
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (1, 1))
      (.transversal ![3, 0, 1, 2]
        (.clash (0, 3) (2, 3))
        (.clash (0, 3) (1, 3))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (2, 1))
          (.transversal ![2, 1, 0, 3]
            (.clash (0, 2) (0, 3))
            (.clash (0, 1) (0, 2))
            (.clash (0, 0) (0, 2))
            (.clash (0, 1) (0, 3))
            (.clash (0, 0) (0, 3))
            (.clash (0, 0) (0, 1)))
          (.clash (0, 1) (0, 3))
          (.clash (2, 0) (2, 1))
          (.clash (0, 3) (1, 3))
          (.motif 1 2 0 3 0 1
            (.clash (0, 1) (3, 1))))
        (.clash (1, 0) (1, 3))
        (.clash (1, 0) (1, 1))
        (.clash (1, 1) (1, 3)))
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (3, 1)))
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (2, 1))
private theorem check300 : check [] state300 certificate300 = true := by
  decide +kernel
private theorem closed300 : Closed.{u} state300 :=
  sound (known := []) trivial check300

private def state301 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 11, 14, 0]
private def certificate301 : Certificate :=
  .transversal ![0, 1, 3, 2]
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
    (.clash (2, 2) (2, 3))
    (.clash (2, 2) (3, 2))
    (.clash (1, 1) (3, 1))
    (.reuse 5)
    (.clash (3, 1) (3, 2))
private theorem check301 : check [state16, state17, state18, state19, state21, state300] state301 certificate301 = true := by
  decide +kernel
private theorem closed301 : Closed.{u} state301 :=
  sound (known := [state16, state17, state18, state19, state21, state300]) ⟨closed16.{u}, ⟨closed17.{u}, ⟨closed18.{u}, ⟨closed19.{u}, ⟨closed21.{u}, ⟨closed300.{u}, trivial⟩⟩⟩⟩⟩⟩ check301

def state302 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 11, 12, 13, 14, 0]
private def certificate302 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 2) (2, 2))
    (.clash (2, 2) (2, 3))
    (.clash (3, 1) (3, 3))
    (.transversal ![0, 1, 3, 2]
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
              (.transversal ![2, 0, 3, 1]
                (.motif 0 1 2 2 1 0
                  (.clash (2, 0) (2, 3)))
                (.clash (0, 1) (0, 2))
                (.clash (2, 1) (3, 1))
                (.clash (1, 0) (1, 2))
                (.reuse 0)
                (.clash (0, 1) (3, 1)))
              (.clash (0, 1) (0, 2))
              (.reuse 1)
              (.clash (1, 2) (1, 3))
              (.clash (0, 1) (2, 1)))
            (.reuse 2))
          (.clash (1, 1) (1, 3))
          (.reuse 3)
          (.clash (0, 0) (3, 0)))
        (.reuse 4)
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (2, 3))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (2, 0)))
      (.clash (1, 2) (2, 2))
      (.clash (2, 2) (3, 2))
      (.clash (1, 1) (1, 2))
      (.reuse 5)
      (.clash (1, 2) (3, 2)))
    (.reuse 6)
    (.reuse 7)
private theorem check302 : check [state287, state288, state74, state75, state77, state290, state299, state301] state302 certificate302 = true := by
  decide +kernel
private theorem closed302 : Closed.{u} state302 :=
  sound (known := [state287, state288, state74, state75, state77, state290, state299, state301]) ⟨closed287.{u}, ⟨closed288.{u}, ⟨closed74.{u}, ⟨closed75.{u}, ⟨closed77.{u}, ⟨closed290.{u}, ⟨closed299.{u}, ⟨closed301.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩ check302

def state303 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 1, 1, 6, 0, 11, 6, 11, 1, 0]
private def certificate303 : Certificate :=
  .transversal ![0, 1, 3, 2]
    (.transversal ![2, 0, 1, 3]
      (.transversal ![2, 1, 3, 0]
        (.clash (0, 0) (0, 2))
        (.transversal ![3, 0, 1, 2]
          (.clash (0, 2) (0, 3))
          (.columns)
          (.clash (0, 1) (0, 3))
          (.clash (0, 2) (1, 2))
          (.clash (0, 1) (0, 2))
          (.clash (0, 1) (2, 1)))
        (.clash (0, 2) (1, 2))
        (.clash (1, 1) (3, 1))
        (.clash (0, 0) (3, 0))
        (.clash (2, 1) (2, 3)))
      (.clash (0, 2) (1, 2))
      (.clash (0, 0) (0, 2))
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (1, 0))
      (.clash (0, 0) (3, 0)))
    (.clash (2, 2) (2, 3))
    (.clash (0, 0) (0, 1))
    (.clash (1, 1) (3, 1))
    (.clash (0, 1) (1, 1))
    (.clash (0, 1) (3, 1))
private theorem check303 : check [] state303 certificate303 = true := by
  decide +kernel
private theorem closed303 : Closed.{u} state303 :=
  sound (known := []) trivial check303

def state304 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 1, 1, 6, 10, 11, 6, 0, 1, 10]
private def certificate304 : Certificate :=
  .transversal ![3, 2, 0, 1]
    (.transversal ![3, 0, 2, 1]
      (.clash (1, 0) (1, 2))
      (.clash (0, 3) (3, 3))
      (.clash (0, 0) (0, 3))
      (.motif 1 3 0 3 0 2
        (.clash (0, 2) (2, 2)))
      (.clash (0, 0) (1, 0))
      (.clash (3, 1) (3, 3)))
    (.clash (0, 1) (0, 3))
    (.clash (0, 0) (0, 3))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (0, 1))
private theorem check304 : check [] state304 certificate304 = true := by
  decide +kernel
private theorem closed304 : Closed.{u} state304 :=
  sound (known := []) trivial check304

def state305 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 1, 6, 10, 11, 11, 13, 14, 10]
private def certificate305 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.transversal ![2, 3, 1, 0]
      (.clash (0, 1) (0, 2))
      (.clash (0, 2) (1, 2))
      (.transversal ![2, 0, 1, 3]
        (.clash (1, 0) (3, 0))
        (.clash (0, 2) (1, 2))
        (.clash (0, 2) (2, 2))
        (.clash (1, 0) (1, 2))
        (.transversal ![0, 3, 2, 1]
          (.clash (0, 0) (0, 1))
          (.clash (0, 0) (1, 0))
          (.transversal ![0, 3, 1, 2]
            (.clash (0, 0) (0, 1))
            (.clash (2, 1) (3, 1))
            (.clash (3, 1) (3, 2))
            (.clash (0, 1) (2, 1))
            (.motif 0 3 2 0 2 1
              (.clash (0, 2) (1, 2)))
            (.clash (1, 2) (3, 2)))
          (.clash (1, 0) (1, 3))
          (.clash (0, 1) (3, 1))
          (.clash (3, 1) (3, 3)))
        (.clash (1, 2) (2, 2)))
      (.clash (0, 1) (2, 1))
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (2, 3)))
    (.clash (2, 0) (2, 2))
    (.clash (2, 0) (2, 3))
    (.clash (1, 3) (3, 3))
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
private theorem check305 : check [] state305 certificate305 = true := by
  decide +kernel
private theorem closed305 : Closed.{u} state305 :=
  sound (known := []) trivial check305

def state306 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 0, 5, 6, 1, 2, 6, 2, 0, 1]
private def certificate306 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.clash (0, 2) (0, 3))
    (.motif 0 1 2 3 0 2
      (.clash (0, 0) (0, 1)))
    (.clash (0, 0) (0, 3))
    (.clash (0, 2) (1, 2))
    (.clash (0, 0) (0, 2))
    (.clash (0, 0) (3, 0))
private theorem check306 : check [] state306 certificate306 = true := by
  decide +kernel
private theorem closed306 : Closed.{u} state306 :=
  sound (known := []) trivial check306

def state307 : Partition := #v[0, 1, 2, 3, 2, 5, 6, 7, 5, 6, 1, 2, 6, 13, 5, 1]
private def certificate307 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.transversal ![0, 2, 3, 1]
      (.clash (0, 0) (3, 0))
      (.clash (0, 0) (0, 2))
      (.transversal ![3, 0, 2, 1]
        (.clash (0, 2) (0, 3))
        (.clash (0, 1) (0, 3))
        (.clash (0, 0) (0, 3))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (0, 2))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 2) (1, 2))
      (.clash (2, 1) (3, 1))
      (.motif 1 3 0 2 1 0
        (.clash (0, 0) (2, 0))))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (2, 0))
    (.clash (1, 2) (1, 3))
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (1, 2))
private theorem check307 : check [] state307 certificate307 = true := by
  decide +kernel
private theorem closed307 : Closed.{u} state307 :=
  sound (known := []) trivial check307

private def state308 : Partition := #v[0, 4, 2, 3, 4, 5, 3, 7, 8, 3, 4, 11, 3, 11, 14, 4]
private def certificate308 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.transversal ![0, 1, 3, 2]
      (.clash (1, 1) (1, 3))
      (.clash (1, 3) (2, 3))
      (.motif 1 3 0 3 0 2
        (.clash (0, 1) (0, 2)))
      (.clash (1, 1) (3, 1))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (1, 1))
        (.clash (0, 0) (2, 0))
        (.clash (1, 1) (1, 3))
        (.motif 1 2 0 1 2 0
          (.clash (0, 0) (0, 3))))
      (.clash (3, 1) (3, 2)))
    (.clash (0, 0) (0, 1))
    (.motif 0 3 1 0 3 1
      (.clash (1, 1) (1, 2)))
    (.clash (1, 0) (1, 3))
    (.clash (1, 3) (2, 3))
    (.clash (0, 1) (3, 1))
private theorem check308 : check [] state308 certificate308 = true := by
  decide +kernel
private theorem closed308 : Closed.{u} state308 :=
  sound (known := []) trivial check308

private def state309 : Partition := #v[0, 4, 2, 3, 4, 5, 6, 7, 8, 6, 4, 11, 6, 13, 3, 4]
private def certificate309 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.transversal ![1, 3, 0, 2]
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (2, 0))
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (2, 0))
      (.clash (0, 0) (0, 3))
      (.transversal ![3, 1, 2, 0]
        (.motif 0 1 2 0 1 3
          (.clash (2, 2) (2, 3)))
        (.clash (0, 1) (0, 3))
        (.clash (1, 2) (3, 2))
        (.clash (0, 1) (1, 1))
        (.clash (1, 1) (1, 2))
        (.clash (0, 1) (2, 1))))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (0, 3))
    (.clash (1, 2) (1, 3))
    (.clash (0, 3) (1, 3))
    (.clash (1, 2) (3, 2))
private theorem check309 : check [] state309 certificate309 = true := by
  decide +kernel
private theorem closed309 : Closed.{u} state309 :=
  sound (known := []) trivial check309

def state310 : Partition := #v[0, 4, 2, 3, 4, 5, 6, 7, 8, 6, 4, 11, 6, 13, 14, 4]
private def certificate310 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.clash (0, 1) (0, 3))
    (.transversal ![0, 2, 3, 1]
      (.clash (0, 0) (0, 3))
      (.transversal ![0, 3, 1, 2]
        (.clash (1, 3) (2, 3))
        (.clash (0, 0) (0, 3))
        (.transversal ![0, 3, 2, 1]
          (.clash (1, 3) (2, 3))
          (.clash (0, 0) (0, 1))
          (.clash (3, 1) (3, 2))
          (.clash (1, 0) (1, 3))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (3, 1))
            (.clash (1, 0) (2, 0))
            (.clash (0, 0) (0, 1))
            (.transversal ![2, 0, 3, 1]
              (.clash (0, 1) (0, 2))
              (.clash (0, 0) (0, 2))
              (.transversal ![2, 1, 3, 0]
                (.clash (1, 1) (1, 3))
                (.clash (0, 0) (0, 2))
                (.clash (0, 2) (0, 3))
                (.columns)
                (.clash (1, 1) (1, 2))
                (.clash (0, 0) (0, 3)))
              (.clash (0, 0) (0, 1))
              (.clash (0, 1) (3, 1))
              (.clash (0, 0) (2, 0)))
            (.clash (1, 3) (2, 3))
            (.clash (0, 0) (2, 0)))
          (.clash (0, 1) (3, 1)))
        (.clash (0, 3) (1, 3))
        (.motif 1 3 0 3 0 2
          (.clash (0, 1) (0, 2)))
        (.clash (1, 2) (3, 2)))
      (.motif 0 3 1 0 3 1
        (.clash (1, 1) (1, 2)))
      (.clash (0, 3) (2, 3))
      (.clash (2, 1) (3, 1))
      (.reuse 0))
    (.reuse 1)
    (.clash (0, 1) (2, 1))
    (.clash (2, 2) (3, 2))
    (.clash (1, 2) (3, 2))
private theorem check310 : check [state308, state309] state310 certificate310 = true := by
  decide +kernel
private theorem closed310 : Closed.{u} state310 :=
  sound (known := [state308, state309]) ⟨closed308.{u}, ⟨closed309.{u}, trivial⟩⟩ check310

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary16 : Known.{u} [state302, state303, state304, state305, state306, state307, state310] :=
  ⟨closed302.{u}, ⟨closed303.{u}, ⟨closed304.{u}, ⟨closed305.{u}, ⟨closed306.{u}, ⟨closed307.{u}, ⟨closed310.{u}, trivial⟩⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
