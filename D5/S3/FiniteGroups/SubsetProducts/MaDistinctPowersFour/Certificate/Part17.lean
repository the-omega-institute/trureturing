/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part17
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part17
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part17.certificate318
   digest: Order-four certificate decisions for chunks 311 through 318. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part01
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part02
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part03
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part04
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part07
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part09
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part12
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part14
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part15
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part16

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed0 : Closed.{u} state0 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed3 : Closed.{u} state3 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed6 : Closed.{u} state6 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed15 : Closed.{u} state15 :=
  known_of_mem boundary01.{u} (by decide)

private theorem closed24 : Closed.{u} state24 :=
  known_of_mem boundary02.{u} (by decide)

private theorem closed38 : Closed.{u} state38 :=
  known_of_mem boundary02.{u} (by decide)

private theorem closed55 : Closed.{u} state55 :=
  known_of_mem boundary03.{u} (by decide)

private theorem closed72 : Closed.{u} state72 :=
  known_of_mem boundary04.{u} (by decide)

private theorem closed132 : Closed.{u} state132 :=
  known_of_mem boundary07.{u} (by decide)

private theorem closed174 : Closed.{u} state174 :=
  known_of_mem boundary09.{u} (by decide)

private theorem closed215 : Closed.{u} state215 :=
  known_of_mem boundary12.{u} (by decide)

private theorem closed256 : Closed.{u} state256 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed257 : Closed.{u} state257 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed258 : Closed.{u} state258 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed259 : Closed.{u} state259 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed260 : Closed.{u} state260 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed266 : Closed.{u} state266 :=
  known_of_mem boundary14.{u} (by decide)

private theorem closed271 : Closed.{u} state271 :=
  known_of_mem boundary15.{u} (by decide)

private theorem closed286 : Closed.{u} state286 :=
  known_of_mem boundary15.{u} (by decide)

private theorem closed302 : Closed.{u} state302 :=
  known_of_mem boundary16.{u} (by decide)

private theorem closed303 : Closed.{u} state303 :=
  known_of_mem boundary16.{u} (by decide)

private theorem closed304 : Closed.{u} state304 :=
  known_of_mem boundary16.{u} (by decide)

private theorem closed305 : Closed.{u} state305 :=
  known_of_mem boundary16.{u} (by decide)

private theorem closed306 : Closed.{u} state306 :=
  known_of_mem boundary16.{u} (by decide)

private theorem closed307 : Closed.{u} state307 :=
  known_of_mem boundary16.{u} (by decide)

private theorem closed310 : Closed.{u} state310 :=
  known_of_mem boundary16.{u} (by decide)

private def state311 : Partition := #v[0, 1, 2, 3, 1, 3, 0, 7, 8, 0, 1, 11, 11, 7, 3, 1]
private def certificate311 : Certificate :=
  .transversal ![1, 3, 0, 2]
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
      (.clash (0, 2) (0, 3)))
private theorem check311 : check [] state311 certificate311 = true := by
  decide +kernel
private theorem closed311 : Closed.{u} state311 :=
  sound (known := []) trivial check311

private def state312 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 1, 11, 11, 0, 5, 1]
private def certificate312 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 0) (0, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (1, 1))
        (.clash (0, 0) (2, 0))
        (.clash (1, 1) (1, 3))
        (.motif 1 2 0 1 2 0
          (.clash (1, 2) (1, 3))))
      (.clash (2, 2) (2, 3))
      (.clash (0, 1) (1, 1))
      (.clash (1, 0) (3, 0))
      (.clash (1, 0) (1, 1))
      (.clash (3, 0) (3, 2)))
    (.clash (2, 1) (3, 1))
    (.clash (1, 1) (3, 1))
    (.clash (1, 2) (1, 3))
    (.clash (1, 1) (1, 3))
    (.clash (1, 1) (1, 2))
private theorem check312 : check [] state312 certificate312 = true := by
  decide +kernel
private theorem closed312 : Closed.{u} state312 :=
  sound (known := []) trivial check312

private def state313 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 1, 11, 11, 0, 14, 1]
private def certificate313 : Certificate :=
  .transversal ![0, 1, 3, 2]
    (.clash (1, 1) (3, 1))
    (.clash (0, 0) (3, 0))
    (.clash (3, 1) (3, 2))
    (.transversal ![0, 3, 1, 2]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 0) (0, 1))
        (.clash (2, 0) (2, 2))
        (.clash (2, 2) (3, 2))
        (.clash (0, 0) (2, 0))
        (.clash (3, 1) (3, 2))
        (.transversal ![1, 0, 3, 2]
          (.motif 1 3 0 0 1 3
            (.clash (0, 3) (2, 3)))
          (.clash (0, 1) (1, 1))
          (.clash (2, 0) (2, 2))
          (.clash (1, 0) (1, 1))
          (.clash (1, 0) (2, 0))
          (.clash (2, 0) (2, 3))))
      (.clash (2, 1) (3, 1))
      (.clash (3, 1) (3, 2))
      (.clash (1, 2) (1, 3))
      (.transversal ![1, 0, 3, 2]
        (.transversal ![2, 0, 3, 1]
          (.clash (0, 1) (0, 2))
          (.transversal ![2, 3, 0, 1]
            (.clash (0, 2) (3, 2))
            (.clash (2, 0) (2, 3))
            (.clash (0, 0) (0, 2))
            (.motif 2 3 0 2 0 3
              (.clash (0, 3) (1, 3)))
            (.clash (3, 1) (3, 2))
            (.clash (0, 0) (2, 0)))
          (.clash (0, 0) (0, 2))
          (.clash (0, 1) (1, 1))
          (.clash (0, 0) (0, 1))
          (.clash (0, 0) (3, 0)))
        (.clash (0, 1) (1, 1))
        (.clash (1, 3) (3, 3))
        (.clash (1, 0) (1, 1))
        (.clash (1, 0) (1, 3))
        (.clash (1, 1) (1, 3)))
      (.clash (1, 2) (3, 2)))
    (.reuse 0)
    (.clash (3, 0) (3, 2))
private theorem check313 : check [state312] state313 certificate313 = true := by
  decide +kernel
private theorem closed313 : Closed.{u} state313 :=
  sound (known := [state312]) ⟨closed312.{u}, trivial⟩ check313

private def state314 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 1, 11, 11, 13, 14, 1]
private def certificate314 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 2) (1, 3))
      (.clash (0, 0) (0, 1))
      (.clash (2, 1) (3, 1))
      (.clash (1, 3) (3, 3))
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
        (.transversal ![1, 0, 3, 2]
          (.transversal ![3, 0, 1, 2]
            (.clash (0, 1) (0, 3))
            (.clash (0, 0) (0, 3))
            (.reuse 0)
            (.clash (0, 0) (0, 1))
            (.clash (0, 1) (1, 1))
            (.clash (1, 1) (1, 2)))
          (.clash (2, 2) (2, 3))
          (.clash (0, 1) (1, 1))
          (.clash (1, 0) (3, 0))
          (.clash (1, 0) (1, 1))
          (.clash (3, 0) (3, 2)))
        (.clash (3, 0) (3, 2)))
      (.clash (0, 1) (3, 1)))
    (.clash (0, 0) (3, 0))
    (.reuse 1)
    (.clash (2, 1) (2, 3))
    (.clash (2, 1) (3, 1))
    (.clash (3, 0) (3, 1))
private theorem check314 : check [state311, state313] state314 certificate314 = true := by
  decide +kernel
private theorem closed314 : Closed.{u} state314 :=
  sound (known := [state311, state313]) ⟨closed311.{u}, ⟨closed313.{u}, trivial⟩⟩ check314

private def state315 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 1, 11, 12, 13, 14, 1]
private def certificate315 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.clash (0, 1) (2, 1))
    (.clash (2, 2) (2, 3))
    (.clash (3, 0) (3, 3))
    (.clash (2, 1) (2, 3))
    (.transversal ![2, 0, 1, 3]
      (.transversal ![2, 1, 0, 3]
        (.clash (1, 0) (1, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 1) (0, 2))
        (.transversal ![2, 1, 3, 0]
          (.clash (1, 0) (1, 1))
          (.transversal ![0, 1, 3, 2]
            (.clash (0, 0) (2, 0))
            (.clash (0, 0) (0, 2))
            (.transversal ![0, 2, 3, 1]
              (.clash (0, 0) (3, 0))
              (.clash (0, 0) (0, 2))
              (.clash (3, 1) (3, 2))
              (.clash (0, 2) (1, 2))
              (.clash (2, 1) (3, 1))
              (.transversal ![0, 3, 2, 1]
                (.reuse 0)
                (.clash (0, 0) (0, 1))
                (.clash (0, 0) (0, 2))
                (.clash (1, 3) (3, 3))
                (.clash (1, 0) (1, 3))
                (.clash (0, 1) (0, 2))))
            (.clash (1, 0) (1, 1))
            (.reuse 1)
            (.clash (0, 2) (3, 2)))
          (.clash (0, 2) (1, 2))
          (.clash (2, 0) (2, 3))
          (.clash (1, 1) (1, 2))
          (.clash (2, 1) (2, 3)))
        (.clash (0, 1) (1, 1))
        (.clash (2, 0) (2, 2)))
      (.clash (0, 2) (1, 2))
      (.clash (0, 1) (0, 2))
      (.clash (1, 0) (1, 2))
      (.reuse 2)
      (.clash (0, 1) (2, 1)))
    (.reuse 3)
private theorem check315 : check [state306, state307, state310, state314] state315 certificate315 = true := by
  decide +kernel
private theorem closed315 : Closed.{u} state315 :=
  sound (known := [state306, state307, state310, state314]) ⟨closed306.{u}, ⟨closed307.{u}, ⟨closed310.{u}, ⟨closed314.{u}, trivial⟩⟩⟩⟩ check315

private def state316 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 6, 10, 11, 12, 13, 14, 10]
private def certificate316 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (0, 1) (2, 1))
    (.transversal ![1, 2, 3, 0]
      (.clash (0, 1) (2, 1))
      (.clash (2, 0) (2, 3))
      (.clash (2, 0) (3, 0))
      (.clash (2, 1) (2, 3))
      (.transversal ![1, 3, 2, 0]
        (.transversal ![0, 3, 1, 2]
          (.clash (0, 0) (0, 1))
          (.clash (0, 0) (3, 0))
          (.transversal ![0, 3, 2, 1]
            (.clash (0, 0) (0, 1))
            (.clash (2, 2) (3, 2))
            (.clash (3, 1) (3, 2))
            (.clash (1, 3) (3, 3))
            (.clash (0, 1) (3, 1))
            (.clash (3, 1) (3, 3)))
          (.clash (0, 1) (2, 1))
          (.transversal ![0, 3, 2, 1]
            (.clash (0, 0) (0, 1))
            (.transversal ![0, 2, 3, 1]
              (.clash (0, 0) (3, 0))
              (.clash (2, 2) (2, 3))
              (.clash (3, 1) (3, 3))
              (.clash (2, 1) (2, 3))
              (.clash (2, 1) (3, 1))
              (.reuse 0))
            (.reuse 1)
            (.clash (1, 3) (3, 3))
            (.clash (0, 1) (3, 1))
            (.clash (3, 1) (3, 3)))
          (.clash (1, 2) (3, 2)))
        (.clash (2, 0) (2, 2))
        (.clash (0, 1) (2, 1))
        (.clash (1, 3) (3, 3))
        (.clash (1, 2) (1, 3))
        (.clash (1, 2) (2, 2)))
      (.reuse 2))
    (.reuse 3)
    (.clash (2, 0) (2, 1))
    (.clash (1, 2) (2, 2))
    (.clash (2, 0) (2, 2))
private theorem check316 : check [state303, state304, state305, state315] state316 certificate316 = true := by
  decide +kernel
private theorem closed316 : Closed.{u} state316 :=
  sound (known := [state303, state304, state305, state315]) ⟨closed303.{u}, ⟨closed304.{u}, ⟨closed305.{u}, ⟨closed315.{u}, trivial⟩⟩⟩⟩ check316

private def state317 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 10]
private def certificate317 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.transversal ![0, 3, 2, 1]
      (.clash (1, 2) (1, 3))
      (.clash (1, 2) (2, 2))
      (.transversal ![1, 2, 0, 3]
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 2, 3, 0]
          (.clash (0, 0) (0, 1))
          (.clash (2, 0) (2, 3))
          (.clash (2, 0) (3, 0))
          (.transversal ![1, 0, 3, 2]
            (.clash (1, 0) (2, 0))
            (.clash (0, 0) (0, 1))
            (.transversal ![0, 3, 1, 2]
              (.clash (1, 2) (1, 3))
              (.clash (2, 1) (2, 3))
              (.clash (0, 0) (0, 1))
              (.transversal ![1, 3, 2, 0]
                (.clash (0, 1) (2, 1))
                (.clash (2, 0) (2, 2))
                (.clash (2, 0) (3, 0))
                (.clash (1, 3) (3, 3))
                (.reuse 0)
                (.clash (3, 0) (3, 3)))
              (.reuse 1)
              (.clash (0, 1) (2, 1)))
            (.clash (0, 0) (1, 0))
            (.reuse 2)
            (.clash (1, 2) (3, 2)))
          (.clash (0, 0) (3, 0))
          (.reuse 3))
        (.reuse 4)
        (.clash (0, 0) (2, 0))
        (.clash (1, 2) (2, 2))
        (.clash (2, 0) (2, 2)))
      (.clash (1, 3) (3, 3))
      (.reuse 5)
      (.clash (3, 1) (3, 3)))
    (.reuse 6)
    (.reuse 7)
    (.reuse 8)
    (.clash (1, 2) (2, 2))
    (.clash (2, 1) (2, 2))
private theorem check317 : check [state257, state258, state259, state260, state266, state271, state286, state302, state316] state317 certificate317 = true := by
  decide +kernel
private theorem closed317 : Closed.{u} state317 :=
  sound (known := [state257, state258, state259, state260, state266, state271, state286, state302, state316]) ⟨closed257.{u}, ⟨closed258.{u}, ⟨closed259.{u}, ⟨closed260.{u}, ⟨closed266.{u}, ⟨closed271.{u}, ⟨closed286.{u}, ⟨closed302.{u}, ⟨closed316.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩ check317

private def certificate318 : Certificate :=
  .transversal ![0, 1, 2, 3]
    (.transversal ![0, 2, 1, 3]
      (.clash (1, 1) (1, 2))
      (.clash (1, 1) (2, 1))
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
                (.reuse 0)
                (.clash (0, 1) (3, 1)))
              (.clash (0, 0) (0, 2))
              (.clash (2, 1) (2, 2))
              (.clash (0, 0) (1, 0))
              (.clash (1, 1) (2, 1)))
            (.clash (0, 0) (1, 0))
            (.reuse 1))
          (.reuse 2)
          (.clash (0, 0) (0, 1))
          (.clash (2, 0) (2, 3))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (2, 0)))
        (.reuse 3)
        (.reuse 4))
      (.reuse 5)
      (.reuse 6)
      (.reuse 7))
    (.reuse 8)
    (.reuse 9)
    (.reuse 10)
    (.reuse 11)
    (.reuse 12)
private theorem check318 : check [state0, state3, state6, state15, state24, state38, state55, state72, state132, state174, state215, state256, state317] initial certificate318 = true := by
  decide +kernel
private theorem closed318 : Closed.{u} initial :=
  sound (known := [state0, state3, state6, state15, state24, state38, state55, state72, state132, state174, state215, state256, state317]) ⟨closed0.{u}, ⟨closed3.{u}, ⟨closed6.{u}, ⟨closed15.{u}, ⟨closed24.{u}, ⟨closed38.{u}, ⟨closed55.{u}, ⟨closed72.{u}, ⟨closed132.{u}, ⟨closed174.{u}, ⟨closed215.{u}, ⟨closed256.{u}, ⟨closed317.{u}, trivial⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ check318

theorem initial_closed : Closed.{u} initial :=
  closed318.{u}

end MaLatin.OrderFourChecker
