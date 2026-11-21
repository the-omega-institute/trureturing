/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part14
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part14
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part14.certificate269
   digest: Order-four certificate decisions for chunks 251 through 269. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part01
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part02
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part07
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part12
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part13

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed3 : Closed.{u} state3 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed6 : Closed.{u} state6 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed15 : Closed.{u} state15 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed24 : Closed.{u} state24 :=
  known_of_mem boundary02.{u} (by decide)

private theorem closed133 : Closed.{u} state133 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed134 : Closed.{u} state134 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed229 : Closed.{u} state229 :=
  known_of_mem boundary12.{u} (by decide)

private theorem closed242 : Closed.{u} state242 :=
  known_of_mem boundary13.{u} (by decide)

private theorem closed244 : Closed.{u} state244 :=
  known_of_mem boundary13.{u} (by decide)

private theorem closed246 : Closed.{u} state246 :=
  known_of_mem boundary13.{u} (by decide)

private theorem closed247 : Closed.{u} state247 :=
  known_of_mem boundary13.{u} (by decide)

private theorem closed250 : Closed.{u} state250 :=
  known_of_mem boundary13.{u} (by decide)

private def state251 : Partition := #v[0, 1, 2, 3, 4, 2, 6, 7, 8, 9, 10, 11, 12, 4, 11, 2]
private def certificate251 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 2) (1, 3))
      (.transversal ![2, 3, 1, 0]
        (.clash (1, 1) (1, 3))
        (.clash (0, 0) (0, 2))
        (.clash (3, 0) (3, 3))
        (.clash (1, 2) (1, 3))
        (.transversal ![2, 3, 0, 1]
          (.clash (1, 1) (1, 3))
          (.motif 1 3 2 0 3 1
            (.clash (0, 0) (3, 0)))
          (.clash (1, 0) (1, 1))
          (.clash (2, 0) (3, 0))
          (.clash (1, 0) (1, 3))
          (.clash (1, 0) (2, 0)))
        (.clash (0, 0) (3, 0)))
      (.clash (1, 2) (3, 2))
      (.transversal ![0, 3, 2, 1]
        (.clash (1, 2) (1, 3))
        (.clash (1, 2) (2, 2))
        (.clash (0, 0) (1, 0))
        (.clash (2, 1) (2, 2))
        (.clash (1, 0) (1, 3))
        (.transversal ![2, 3, 0, 1]
          (.clash (1, 1) (1, 3))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (2, 1))
            (.clash (0, 1) (0, 2))
            (.reuse 0)
            (.clash (1, 1) (1, 3))
            (.clash (1, 3) (2, 3))
            (.clash (0, 2) (3, 2)))
          (.clash (0, 2) (2, 2))
          (.clash (2, 0) (2, 1))
          (.clash (1, 0) (1, 3))
          (.clash (1, 0) (2, 0))))
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (2, 3)))
    (.reuse 1)
    (.clash (0, 0) (1, 0))
    (.clash (1, 2) (3, 2))
    (.clash (1, 0) (1, 2))
    (.clash (3, 1) (3, 2))
private theorem check251 : check [state247, state250] state251 certificate251 = true := by
  decide +kernel
private theorem closed251 : Closed.{u} state251 :=
  sound (known := [state247, state250]) ⟨closed247.{u}, ⟨closed250.{u}, trivial⟩⟩ check251

private def state252 : Partition := #v[0, 1, 2, 3, 4, 5, 3, 7, 3, 9, 5, 1, 2, 13, 1, 5]
private def certificate252 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.clash (1, 3) (2, 3))
    (.clash (0, 1) (1, 1))
    (.clash (0, 1) (0, 2))
    (.clash (1, 1) (1, 3))
    (.transversal ![0, 2, 1, 3]
      (.clash (0, 0) (0, 3))
      (.transversal ![0, 3, 2, 1]
        (.clash (0, 0) (0, 2))
        (.clash (1, 1) (2, 1))
        (.clash (2, 1) (3, 1))
        (.clash (0, 2) (2, 2))
        (.clash (3, 0) (3, 1))
        (.clash (1, 1) (3, 1)))
      (.transversal ![0, 2, 3, 1]
        (.clash (0, 0) (0, 3))
        (.clash (0, 0) (0, 1))
        (.clash (1, 1) (3, 1))
        (.clash (0, 1) (0, 3))
        (.transversal ![0, 3, 1, 2]
          (.clash (0, 0) (0, 2))
          (.clash (1, 1) (2, 1))
          (.clash (0, 0) (0, 1))
          (.transversal ![2, 0, 3, 1]
            (.clash (1, 0) (1, 3))
            (.clash (0, 1) (0, 2))
            (.clash (0, 2) (0, 3))
            (.columns)
            (.clash (1, 0) (1, 2))
            (.clash (0, 1) (0, 3)))
          (.clash (0, 1) (0, 2))
          (.clash (0, 1) (2, 1)))
        (.clash (0, 1) (3, 1)))
      (.clash (2, 0) (2, 1))
      (.clash (0, 3) (3, 3))
      (.clash (1, 1) (2, 1)))
    (.clash (0, 2) (2, 2))
private theorem check252 : check [] state252 certificate252 = true := by
  decide +kernel
private theorem closed252 : Closed.{u} state252 :=
  sound (known := []) trivial check252

private def state253 : Partition := #v[0, 1, 2, 3, 4, 8, 6, 7, 8, 9, 10, 1, 2, 13, 1, 8]
private def certificate253 : Certificate :=
  .transversal ![3, 1, 2, 0]
    (.clash (0, 3) (3, 3))
    (.transversal ![1, 3, 2, 0]
      (.clash (1, 3) (2, 3))
      (.clash (0, 1) (0, 3))
      (.clash (0, 1) (0, 2))
      (.clash (0, 3) (1, 3))
      (.transversal ![0, 3, 1, 2]
        (.clash (0, 0) (0, 2))
        (.transversal ![2, 0, 1, 3]
          (.clash (1, 0) (1, 3))
          (.clash (0, 0) (0, 2))
          (.clash (1, 1) (1, 3))
          (.clash (0, 0) (1, 0))
          (.clash (1, 0) (1, 1))
          (.clash (0, 0) (2, 0)))
        (.clash (0, 0) (0, 1))
        (.motif 0 2 1 3 1 2
          (.clash (1, 2) (3, 2)))
        (.clash (0, 1) (0, 2))
        (.clash (0, 1) (2, 1)))
      (.clash (0, 2) (0, 3)))
    (.clash (0, 2) (0, 3))
    (.clash (2, 0) (2, 2))
    (.clash (2, 0) (3, 0))
    (.clash (0, 2) (2, 2))
private theorem check253 : check [] state253 certificate253 = true := by
  decide +kernel
private theorem closed253 : Closed.{u} state253 :=
  sound (known := []) trivial check253

private def state254 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 2, 13, 11, 5]
private def certificate254 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.transversal ![0, 2, 1, 3]
      (.clash (0, 0) (0, 1))
      (.transversal ![0, 2, 3, 1]
        (.clash (0, 0) (0, 1))
        (.clash (2, 1) (2, 3))
        (.clash (2, 1) (3, 1))
        (.clash (1, 2) (3, 2))
        (.clash (0, 1) (3, 1))
        (.clash (3, 1) (3, 2)))
      (.transversal ![0, 2, 3, 1]
        (.clash (0, 0) (0, 1))
        (.clash (2, 3) (3, 3))
        (.clash (1, 1) (3, 1))
        (.clash (1, 2) (3, 2))
        (.clash (0, 1) (3, 1))
        (.clash (3, 1) (3, 2)))
      (.clash (0, 1) (2, 1))
      (.clash (0, 1) (1, 1))
      (.clash (1, 1) (2, 1)))
    (.transversal ![1, 2, 0, 3]
      (.clash (1, 2) (3, 2))
      (.clash (2, 0) (2, 3))
      (.clash (0, 1) (1, 1))
      (.transversal ![3, 1, 0, 2]
        (.clash (0, 3) (3, 3))
        (.transversal ![3, 1, 2, 0]
          (.clash (0, 3) (3, 3))
          (.clash (1, 2) (2, 2))
          (.clash (0, 2) (0, 3))
          (.reuse 0)
          (.clash (3, 0) (3, 3))
          (.clash (0, 2) (2, 2)))
        (.clash (0, 1) (0, 3))
        (.clash (1, 1) (1, 2))
        (.clash (0, 1) (1, 1))
        (.clash (1, 2) (3, 2)))
      (.clash (1, 1) (1, 2))
      (.reuse 1))
    (.clash (0, 1) (0, 2))
    (.clash (1, 2) (3, 2))
    (.clash (0, 2) (1, 2))
    (.clash (0, 2) (3, 2))
private theorem check254 : check [state252, state253] state254 certificate254 = true := by
  decide +kernel
private theorem closed254 : Closed.{u} state254 :=
  sound (known := [state252, state253]) ⟨closed252.{u}, ⟨closed253.{u}, trivial⟩⟩ check254

private def state255 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 11, 5]
private def certificate255 : Certificate :=
  .transversal ![2, 1, 3, 0]
    (.transversal ![2, 0, 3, 1]
      (.clash (1, 0) (1, 1))
      (.clash (0, 2) (3, 2))
      (.clash (1, 1) (3, 1))
      (.transversal ![1, 0, 2, 3]
        (.transversal ![1, 2, 0, 3]
          (.clash (1, 0) (1, 2))
          (.clash (1, 0) (2, 0))
          (.clash (0, 1) (0, 2))
          (.transversal ![0, 2, 1, 3]
            (.clash (0, 0) (2, 0))
            (.transversal ![0, 2, 3, 1]
              (.clash (0, 0) (2, 0))
              (.clash (0, 0) (0, 1))
              (.clash (2, 1) (3, 1))
              (.clash (1, 0) (1, 2))
              (.transversal ![3, 1, 0, 2]
                (.clash (0, 2) (0, 3))
                (.motif 0 2 1 0 3 1
                  (.clash (0, 2) (0, 3)))
                (.clash (0, 1) (0, 3))
                (.clash (0, 2) (1, 2))
                (.clash (0, 1) (0, 2))
                (.clash (0, 1) (3, 1)))
              (.clash (0, 1) (3, 1)))
            (.clash (0, 0) (0, 2))
            (.clash (2, 0) (2, 1))
            (.clash (0, 2) (1, 2))
            (.clash (1, 1) (2, 1)))
          (.clash (0, 2) (1, 2))
          (.reuse 0))
        (.reuse 1)
        (.clash (0, 1) (0, 2))
        (.clash (2, 2) (2, 3))
        (.clash (0, 2) (3, 2))
        (.clash (0, 2) (2, 2)))
      (.reuse 2)
      (.clash (3, 1) (3, 2)))
    (.clash (0, 2) (3, 2))
    (.reuse 3)
    (.clash (2, 3) (3, 3))
    (.clash (3, 0) (3, 3))
    (.clash (3, 0) (3, 2))
private theorem check255 : check [state244, state246, state251, state254] state255 certificate255 = true := by
  decide +kernel
private theorem closed255 : Closed.{u} state255 :=
  sound (known := [state244, state246, state251, state254]) ⟨closed244.{u}, ⟨closed246.{u}, ⟨closed251.{u}, ⟨closed254.{u}, trivial⟩⟩⟩⟩ check255

def state256 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 5]
private def certificate256 : Certificate :=
  .transversal ![0, 1, 3, 2]
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 1) (1, 2))
      (.clash (2, 3) (3, 3))
      (.clash (1, 1) (3, 1))
      (.transversal ![1, 2, 0, 3]
        (.transversal ![1, 0, 2, 3]
          (.clash (1, 0) (1, 2))
          (.clash (1, 2) (2, 2))
          (.clash (0, 0) (0, 1))
          (.transversal ![2, 0, 1, 3]
            (.clash (0, 2) (2, 2))
            (.transversal ![2, 0, 3, 1]
              (.clash (0, 2) (2, 2))
              (.clash (0, 1) (0, 2))
              (.clash (2, 1) (3, 1))
              (.clash (1, 0) (1, 2))
              (.transversal ![0, 3, 1, 2]
                (.clash (1, 1) (1, 3))
                (.clash (0, 0) (0, 2))
                (.clash (3, 2) (3, 3))
                (.reuse 0)
                (.reuse 1)
                (.clash (0, 2) (3, 2)))
              (.clash (0, 1) (3, 1)))
            (.clash (0, 0) (0, 2))
            (.clash (2, 1) (2, 2))
            (.clash (0, 0) (1, 0))
            (.clash (1, 1) (2, 1)))
          (.clash (0, 0) (1, 0))
          (.reuse 2))
        (.reuse 3)
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (2, 3))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (2, 0)))
      (.reuse 4)
      (.reuse 5))
    (.reuse 6)
    (.reuse 7)
    (.clash (2, 3) (3, 3))
    (.clash (3, 2) (3, 3))
    (.reuse 8)
private theorem check256 : check [state133, state134, state3, state6, state15, state24, state229, state242, state255] state256 certificate256 = true := by
  decide +kernel
private theorem closed256 : Closed.{u} state256 :=
  sound (known := [state133, state134, state3, state6, state15, state24, state229, state242, state255]) ⟨closed133.{u}, ⟨closed134.{u}, ⟨closed3.{u}, ⟨closed6.{u}, ⟨closed15.{u}, ⟨closed24.{u}, ⟨closed229.{u}, ⟨closed242.{u}, ⟨closed255.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩ check256

def state257 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 1, 7, 10, 0, 7, 0, 1, 10]
private def certificate257 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.motif 0 3 1 2 1 0
      (.clash (1, 0) (2, 0)))
    (.clash (0, 1) (0, 2))
    (.clash (0, 0) (0, 2))
    (.clash (0, 1) (2, 1))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (0, 1))
private theorem check257 : check [] state257 certificate257 = true := by
  decide +kernel
private theorem closed257 : Closed.{u} state257 :=
  sound (known := []) trivial check257

def state258 : Partition := #v[0, 7, 2, 3, 4, 5, 0, 7, 7, 9, 10, 0, 12, 0, 7, 10]
private def certificate258 : Certificate :=
  .transversal ![2, 1, 0, 3]
    (.transversal ![2, 0, 1, 3]
      (.clash (1, 0) (1, 1))
      (.clash (1, 1) (2, 1))
      (.clash (0, 2) (2, 2))
      (.transversal ![2, 3, 1, 0]
        (.clash (0, 1) (0, 2))
        (.clash (1, 0) (1, 1))
        (.motif 0 3 1 2 1 0
          (.clash (0, 1) (2, 1)))
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (3, 0))
        (.clash (1, 0) (3, 0)))
      (.motif 1 2 0 0 3 2
        (.clash (0, 1) (0, 2)))
      (.clash (2, 1) (2, 2)))
    (.clash (0, 1) (0, 2))
    (.clash (0, 2) (2, 2))
    (.clash (0, 1) (1, 1))
    (.motif 1 3 0 1 2 3
      (.clash (0, 0) (0, 3)))
    (.clash (1, 3) (3, 3))
private theorem check258 : check [] state258 certificate258 = true := by
  decide +kernel
private theorem closed258 : Closed.{u} state258 :=
  sound (known := []) trivial check258

def state259 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 1, 9, 10, 0, 12, 0, 4, 10]
private def certificate259 : Certificate :=
  .transversal ![3, 0, 2, 1]
    (.transversal ![0, 3, 1, 2]
      (.clash (1, 2) (1, 3))
      (.clash (2, 1) (2, 3))
      (.clash (0, 0) (0, 3))
      (.transversal ![1, 3, 2, 0]
        (.clash (0, 1) (2, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 0) (3, 0))
        (.clash (1, 3) (3, 3))
        (.transversal ![2, 0, 1, 3]
          (.clash (0, 2) (0, 3))
          (.motif 0 1 2 3 2 0
            (.clash (0, 1) (0, 2)))
          (.clash (0, 2) (2, 2))
          (.clash (0, 3) (1, 3))
          (.clash (0, 3) (3, 3))
          (.clash (1, 3) (3, 3)))
        (.clash (3, 0) (3, 3)))
      (.clash (0, 3) (1, 3))
      (.motif 0 2 3 1 3 0
        (.clash (1, 0) (3, 0))))
    (.clash (0, 3) (3, 3))
    (.clash (0, 0) (0, 3))
    (.clash (2, 2) (3, 2))
    (.clash (0, 0) (1, 0))
    (.clash (1, 2) (2, 2))
private theorem check259 : check [] state259 certificate259 = true := by
  decide +kernel
private theorem closed259 : Closed.{u} state259 :=
  sound (known := []) trivial check259

def state260 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 1, 9, 10, 11, 11, 0, 14, 10]
private def certificate260 : Certificate :=
  .transversal ![1, 3, 2, 0]
    (.transversal ![3, 2, 1, 0]
      (.clash (0, 0) (0, 3))
      (.transversal ![2, 3, 1, 0]
        (.clash (0, 1) (0, 2))
        (.clash (0, 2) (0, 3))
        (.transversal ![0, 1, 3, 2]
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (0, 2))
          (.clash (1, 2) (3, 2))
          (.transversal ![0, 3, 1, 2]
            (.clash (0, 0) (0, 1))
            (.clash (0, 0) (0, 3))
            (.clash (1, 2) (3, 2))
            (.clash (0, 1) (0, 3))
            (.motif 0 3 1 2 1 0
              (.clash (1, 0) (1, 3)))
            (.transversal ![1, 0, 3, 2]
              (.clash (1, 0) (1, 3))
              (.clash (0, 1) (0, 2))
              (.clash (0, 1) (0, 3))
              (.clash (1, 0) (1, 1))
              (.motif 1 2 0 3 1 0
                (.clash (0, 0) (0, 2)))
              (.clash (0, 2) (0, 3))))
          (.transversal ![0, 3, 1, 2]
            (.clash (0, 0) (0, 1))
            (.clash (0, 0) (0, 3))
            (.clash (1, 1) (1, 2))
            (.clash (0, 1) (0, 3))
            (.clash (0, 1) (1, 1))
            (.clash (1, 1) (2, 1)))
          (.clash (0, 2) (3, 2)))
        (.clash (0, 1) (0, 3))
        (.clash (1, 3) (2, 3))
        (.clash (0, 3) (2, 3)))
      (.clash (0, 3) (2, 3))
      (.clash (2, 1) (3, 1))
      (.clash (0, 0) (3, 0))
      (.clash (2, 1) (2, 3)))
    (.clash (2, 0) (2, 2))
    (.clash (2, 0) (2, 3))
    (.clash (1, 3) (3, 3))
    (.clash (1, 3) (2, 3))
    (.clash (2, 2) (2, 3))
private theorem check260 : check [] state260 certificate260 = true := by
  decide +kernel
private theorem closed260 : Closed.{u} state260 :=
  sound (known := []) trivial check260

private def state261 : Partition := #v[0, 1, 2, 3, 1, 5, 0, 2, 5, 2, 1, 0, 2, 0, 5, 1]
private def certificate261 : Certificate :=
  .transversal ![3, 0, 1, 2]
    (.clash (0, 1) (0, 3))
    (.clash (0, 2) (0, 3))
    (.columns)
    (.clash (0, 1) (0, 2))
    (.clash (0, 1) (1, 1))
    (.clash (0, 2) (3, 2))
private theorem check261 : check [] state261 certificate261 = true := by
  decide +kernel
private theorem closed261 : Closed.{u} state261 :=
  sound (known := []) trivial check261

private def state262 : Partition := #v[0, 1, 2, 3, 1, 5, 0, 7, 8, 9, 1, 0, 12, 0, 7, 1]
private def certificate262 : Certificate :=
  .transversal ![2, 3, 0, 1]
    (.clash (0, 2) (3, 2))
    (.transversal ![2, 1, 3, 0]
      (.motif 0 1 2 2 0 1
        (.clash (2, 1) (2, 3)))
      (.clash (0, 0) (0, 2))
      (.clash (2, 0) (3, 0))
      (.clash (1, 1) (1, 2))
      (.transversal ![2, 3, 1, 0]
        (.clash (0, 2) (3, 2))
        (.clash (2, 0) (2, 1))
        (.clash (2, 0) (3, 0))
        (.motif 2 3 0 1 3 2
          (.clash (0, 0) (0, 2)))
        (.clash (1, 1) (1, 3))
        (.clash (1, 1) (2, 1)))
      (.clash (0, 0) (3, 0)))
    (.clash (0, 0) (0, 2))
    (.motif 1 2 0 0 3 2
      (.clash (0, 2) (3, 2)))
    (.clash (1, 2) (1, 3))
    (.clash (0, 0) (2, 0))
private theorem check262 : check [] state262 certificate262 = true := by
  decide +kernel
private theorem closed262 : Closed.{u} state262 :=
  sound (known := []) trivial check262

private def state263 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 1, 0, 12, 0, 4, 1]
private def certificate263 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (1, 3) (3, 3))
    (.clash (2, 0) (2, 2))
    (.clash (2, 2) (3, 2))
    (.transversal ![0, 3, 1, 2]
      (.clash (0, 0) (2, 0))
      (.clash (2, 1) (2, 3))
      (.clash (0, 0) (1, 0))
      (.clash (2, 0) (2, 1))
      (.clash (1, 0) (1, 3))
      (.motif 2 3 0 1 3 2
        (.clash (0, 0) (0, 2))))
    (.clash (1, 0) (1, 3))
    (.clash (1, 0) (2, 0))
private theorem check263 : check [] state263 certificate263 = true := by
  decide +kernel
private theorem closed263 : Closed.{u} state263 :=
  sound (known := []) trivial check263

private def state264 : Partition := #v[0, 1, 2, 3, 1, 5, 0, 7, 7, 3, 1, 5, 5, 0, 3, 1]
private def certificate264 : Certificate :=
  .transversal ![2, 0, 3, 1]
    (.clash (0, 1) (0, 2))
    (.motif 0 1 2 2 0 1
      (.clash (0, 0) (0, 3)))
    (.clash (0, 0) (0, 2))
    (.clash (0, 1) (1, 1))
    (.clash (0, 0) (0, 1))
    (.clash (0, 0) (3, 0))
private theorem check264 : check [] state264 certificate264 = true := by
  decide +kernel
private theorem closed264 : Closed.{u} state264 :=
  sound (known := []) trivial check264

private def state265 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 1, 11, 11, 0, 14, 1]
private def certificate265 : Certificate :=
  .transversal ![3, 2, 1, 0]
    (.clash (0, 0) (0, 3))
    (.transversal ![3, 1, 2, 0]
      (.clash (1, 1) (2, 1))
      (.clash (0, 1) (0, 3))
      (.clash (0, 3) (2, 3))
      (.clash (0, 1) (1, 1))
      (.transversal ![0, 3, 1, 2]
        (.clash (1, 2) (1, 3))
        (.clash (0, 0) (0, 3))
        (.clash (1, 2) (3, 2))
        (.clash (0, 3) (1, 3))
        (.transversal ![1, 0, 3, 2]
          (.transversal ![2, 0, 3, 1]
            (.clash (0, 1) (0, 2))
            (.motif 0 1 2 2 0 1
              (.clash (0, 0) (0, 3)))
            (.clash (0, 0) (0, 2))
            (.clash (0, 1) (1, 1))
            (.clash (0, 0) (0, 1))
            (.clash (0, 0) (3, 0)))
          (.clash (0, 1) (1, 1))
          (.clash (1, 3) (3, 3))
          (.clash (1, 0) (1, 1))
          (.clash (1, 0) (1, 3))
          (.clash (1, 1) (1, 3)))
        (.transversal ![1, 3, 0, 2]
          (.clash (1, 3) (3, 3))
          (.clash (2, 0) (2, 2))
          (.clash (0, 1) (0, 3))
          (.transversal ![1, 0, 3, 2]
            (.reuse 0)
            (.clash (0, 1) (1, 1))
            (.clash (0, 1) (0, 3))
            (.clash (1, 0) (1, 1))
            (.motif 1 2 0 3 1 0
              (.clash (0, 0) (3, 0)))
            (.clash (0, 3) (2, 3)))
          (.clash (0, 3) (1, 3))
          (.clash (2, 0) (2, 1))))
      (.clash (2, 2) (2, 3)))
    (.clash (0, 3) (2, 3))
    (.clash (2, 1) (3, 1))
    (.clash (0, 0) (3, 0))
    (.clash (2, 1) (2, 3))
private theorem check265 : check [state264] state265 certificate265 = true := by
  decide +kernel
private theorem closed265 : Closed.{u} state265 :=
  sound (known := [state264]) ⟨closed264.{u}, trivial⟩ check265

def state266 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 1, 11, 12, 0, 14, 1]
private def certificate266 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 0) (0, 1))
    (.clash (2, 2) (2, 3))
    (.clash (3, 0) (3, 3))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![0, 3, 1, 2]
        (.clash (1, 2) (1, 3))
        (.clash (2, 1) (2, 3))
        (.clash (1, 2) (3, 2))
        (.transversal ![1, 3, 0, 2]
          (.clash (0, 1) (2, 1))
          (.clash (1, 0) (2, 0))
          (.clash (2, 2) (3, 2))
          (.clash (2, 0) (2, 1))
          (.motif 2 3 0 1 3 2
            (.clash (0, 0) (0, 2)))
          (.transversal ![2, 3, 0, 1]
            (.transversal ![2, 1, 0, 3]
              (.clash (1, 1) (1, 3))
              (.clash (0, 2) (3, 2))
              (.clash (0, 1) (0, 2))
              (.transversal ![2, 1, 3, 0]
                (.clash (0, 2) (3, 2))
                (.clash (0, 0) (0, 2))
                (.reuse 0)
                (.clash (0, 0) (2, 0))
                (.clash (2, 0) (3, 0))
                (.clash (0, 0) (3, 0)))
              (.clash (0, 1) (1, 1))
              (.clash (1, 0) (2, 0)))
            (.clash (0, 2) (3, 2))
            (.clash (0, 0) (0, 2))
            (.clash (2, 0) (2, 1))
            (.clash (1, 2) (1, 3))
            (.clash (0, 0) (2, 0))))
        (.reuse 1)
        (.motif 2 3 0 1 3 2
          (.clash (0, 0) (0, 2))))
      (.clash (0, 0) (0, 1))
      (.clash (2, 2) (3, 2))
      (.clash (0, 0) (1, 0))
      (.reuse 2)
      (.clash (1, 2) (3, 2)))
    (.clash (0, 0) (3, 0))
    (.reuse 3)
private theorem check266 : check [state261, state262, state263, state265] state266 certificate266 = true := by
  decide +kernel
private theorem closed266 : Closed.{u} state266 :=
  sound (known := [state261, state262, state263, state265]) ⟨closed261.{u}, ⟨closed262.{u}, ⟨closed263.{u}, ⟨closed265.{u}, trivial⟩⟩⟩⟩ check266

def state267 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 0, 1, 11, 11, 7, 5, 1]
private def certificate267 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.transversal ![3, 0, 1, 2]
      (.clash (0, 1) (0, 3))
      (.clash (0, 0) (0, 3))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (0, 3))
        (.transversal ![2, 1, 0, 3]
          (.clash (0, 2) (0, 3))
          (.motif 0 2 1 0 2 1
            (.clash (0, 2) (0, 3)))
          (.clash (0, 1) (0, 2))
          (.clash (0, 3) (1, 3))
          (.clash (0, 1) (0, 3))
          (.clash (0, 1) (3, 1)))
        (.clash (0, 3) (1, 3))
        (.motif 1 2 0 0 1 2
          (.clash (0, 2) (0, 3))))
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (1, 1))
      (.clash (1, 1) (1, 2)))
    (.clash (2, 2) (2, 3))
    (.clash (0, 1) (1, 1))
    (.clash (1, 0) (3, 0))
    (.clash (1, 0) (1, 1))
    (.clash (3, 0) (3, 2))
private theorem check267 : check [] state267 certificate267 = true := by
  decide +kernel
private theorem closed267 : Closed.{u} state267 :=
  sound (known := []) trivial check267

def state268 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 2, 8, 4, 1, 0, 5, 2, 4, 1]
private def certificate268 : Certificate :=
  .transversal ![1, 3, 0, 2]
    (.clash (0, 1) (0, 2))
    (.clash (2, 0) (2, 2))
    (.clash (0, 1) (2, 1))
    (.transversal ![3, 0, 2, 1]
      (.motif 0 1 2 0 3 2
        (.clash (0, 1) (0, 3)))
      (.clash (0, 1) (0, 3))
      (.clash (0, 2) (0, 3))
      (.clash (0, 1) (2, 1))
      (.clash (0, 2) (3, 2))
      (.clash (0, 1) (0, 2)))
    (.clash (0, 2) (3, 2))
    (.clash (1, 0) (2, 0))
private theorem check268 : check [] state268 certificate268 = true := by
  decide +kernel
private theorem closed268 : Closed.{u} state268 :=
  sound (known := []) trivial check268

def state269 : Partition := #v[0, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 5, 12, 7, 9, 10]
private def certificate269 : Certificate :=
  .transversal ![1, 0, 3, 2]
    (.transversal ![1, 2, 0, 3]
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (2, 0))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 0) (0, 1))
        (.clash (0, 1) (1, 1))
        (.clash (1, 0) (3, 0))
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (3, 0))
        (.motif 1 3 0 1 3 0
          (.clash (1, 2) (1, 3))))
      (.clash (0, 0) (2, 0))
      (.clash (1, 2) (2, 2))
      (.clash (2, 0) (2, 2)))
    (.clash (0, 1) (1, 1))
    (.clash (0, 1) (2, 1))
    (.clash (1, 0) (1, 1))
    (.transversal ![3, 0, 2, 1]
      (.transversal ![3, 1, 2, 0]
        (.clash (0, 3) (2, 3))
        (.clash (0, 3) (3, 3))
        (.clash (1, 0) (3, 0))
        (.clash (2, 2) (2, 3))
        (.transversal ![1, 3, 2, 0]
          (.clash (0, 1) (3, 1))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (3, 1))
            (.clash (2, 0) (2, 2))
            (.clash (0, 1) (0, 3))
            (.motif 1 2 0 3 1 0
              (.clash (0, 0) (3, 0)))
            (.clash (0, 3) (1, 3))
            (.clash (1, 0) (2, 0)))
          (.clash (0, 1) (1, 1))
          (.clash (1, 3) (3, 3))
          (.clash (1, 1) (1, 3))
          (.clash (2, 2) (2, 3)))
        (.clash (3, 0) (3, 3)))
      (.clash (0, 3) (3, 3))
      (.clash (0, 3) (1, 3))
      (.clash (2, 1) (2, 2))
      (.clash (1, 0) (1, 3))
      (.clash (1, 3) (3, 3)))
    (.clash (1, 1) (2, 1))
private theorem check269 : check [] state269 certificate269 = true := by
  decide +kernel
private theorem closed269 : Closed.{u} state269 :=
  sound (known := []) trivial check269

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary14 : Known.{u} [state256, state257, state258, state259, state260, state266, state267, state268, state269] :=
  ⟨closed256.{u}, ⟨closed257.{u}, ⟨closed258.{u}, ⟨closed259.{u}, ⟨closed260.{u}, ⟨closed266.{u}, ⟨closed267.{u}, ⟨closed268.{u}, ⟨closed269.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩

end MaLatin.OrderFourChecker
