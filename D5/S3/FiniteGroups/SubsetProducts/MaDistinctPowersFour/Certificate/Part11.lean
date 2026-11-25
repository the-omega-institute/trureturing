/- GID: D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part11
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part11
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/OrderFour.orderFour; instance=D5/S3/FiniteGroups/SubsetProducts/MaDistinctPowersFour/Certificate/Part11.certificate213
   digest: Order-four certificate decisions for chunks 194 through 213. -/

/- Escape audit unfinished for 1 supporting theorem. See https://github.com/the-omega-institute/trureturing/issues/32494. -/

import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.OrderFourChecker
import D5.S3.FiniteGroups.SubsetProducts.MaDistinctPowersFour.Certificate.Part10

namespace MaLatin.OrderFourChecker

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

universe u

private theorem closed184 : Closed.{u} state184 :=
  known_of_mem boundary10.{u} (by decide)

private theorem closed190 : Closed.{u} state190 :=
  known_of_mem boundary10.{u} (by decide)

private theorem closed191 : Closed.{u} state191 :=
  known_of_mem boundary10.{u} (by decide)

private theorem closed192 : Closed.{u} state192 :=
  known_of_mem boundary10.{u} (by decide)

private theorem closed193 : Closed.{u} state193 :=
  known_of_mem boundary10.{u} (by decide)

private def state194 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 3, 0, 5, 11, 5, 13, 0, 15]
private def certificate194 : Certificate :=
  .transversal ![2, 1, 0, 3]
    (.clash (0, 2) (2, 2))
    (.clash (0, 2) (0, 3))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 0) (0, 2))
      (.clash (0, 2) (0, 3))
      (.clash (3, 1) (3, 3))
      (.clash (0, 0) (0, 3))
      (.clash (2, 1) (3, 1))
      (.motif 2 3 0 0 2 1
        (.clash (0, 1) (1, 1))))
    (.clash (2, 0) (2, 2))
    (.clash (3, 0) (3, 3))
    (.clash (0, 3) (3, 3))
private theorem check194 : check [] state194 certificate194 = true := by
  decide +kernel
private theorem closed194 : Closed.{u} state194 :=
  sound (known := []) trivial check194

private def state195 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 0, 5, 11, 5, 13, 0, 15]
private def certificate195 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 2) (1, 3))
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (3, 1))
      (.motif 1 2 3 2 1 3
        (.clash (0, 3) (3, 3)))
      (.transversal ![1, 2, 3, 0]
        (.clash (0, 1) (3, 1))
        (.transversal ![1, 0, 2, 3]
          (.motif 0 1 2 1 3 0
            (.clash (2, 0) (2, 2)))
          (.clash (0, 1) (0, 3))
          (.clash (2, 3) (3, 3))
          (.clash (1, 0) (1, 1))
          (.transversal ![1, 2, 0, 3]
            (.clash (0, 1) (3, 1))
            (.clash (2, 0) (2, 3))
            (.clash (2, 3) (3, 3))
            (.motif 2 3 0 0 2 1
              (.clash (0, 1) (0, 3)))
            (.clash (1, 0) (1, 2))
            (.clash (1, 0) (2, 0)))
          (.clash (0, 3) (3, 3)))
        (.clash (0, 1) (0, 3))
        (.motif 1 2 0 3 2 1
          (.clash (0, 1) (3, 1)))
        (.clash (1, 1) (1, 2))
        (.clash (0, 3) (2, 3)))
      (.transversal ![1, 0, 3, 2]
        (.motif 0 1 2 1 3 0
          (.clash (2, 0) (2, 2)))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1))
        (.reuse 0)
        (.clash (0, 0) (1, 0))
        (.clash (1, 3) (2, 3))))
    (.reuse 1)
    (.clash (0, 0) (0, 3))
    (.clash (2, 0) (2, 2))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (2, 0))
private theorem check195 : check [state193, state194] state195 certificate195 = true := by
  decide +kernel
private theorem closed195 : Closed.{u} state195 :=
  sound (known := [state193, state194]) ⟨closed193.{u}, ⟨closed194.{u}, trivial⟩⟩ check195

private def state196 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 0, 8, 9, 5, 11, 5, 13, 0, 15]
private def certificate196 : Certificate :=
  .transversal ![2, 3, 1, 0]
    (.clash (0, 0) (0, 2))
    (.transversal ![2, 3, 0, 1]
      (.clash (0, 0) (0, 2))
      (.clash (2, 0) (2, 1))
      (.clash (2, 1) (3, 1))
      (.clash (0, 0) (2, 0))
      (.clash (3, 1) (3, 2))
      (.transversal ![2, 1, 0, 3]
        (.clash (0, 2) (2, 2))
        (.clash (2, 0) (2, 1))
        (.transversal ![0, 2, 3, 1]
          (.clash (1, 2) (1, 3))
          (.clash (1, 3) (2, 3))
          (.clash (0, 0) (2, 0))
          (.transversal ![1, 2, 0, 3]
            (.transversal ![1, 0, 2, 3]
              (.clash (1, 0) (1, 2))
              (.clash (0, 1) (1, 1))
              (.clash (0, 1) (0, 2))
              (.clash (1, 0) (1, 1))
              (.transversal ![3, 2, 1, 0]
                (.clash (0, 1) (0, 3))
                (.clash (0, 2) (0, 3))
                (.motif 0 2 1 1 2 3
                  (.clash (0, 0) (0, 2)))
                (.clash (0, 1) (0, 2))
                (.clash (0, 1) (1, 1))
                (.clash (0, 2) (2, 2)))
              (.clash (0, 2) (2, 2)))
            (.clash (0, 1) (3, 1))
            (.clash (0, 1) (0, 2))
            (.clash (2, 0) (2, 3))
            (.clash (0, 2) (1, 2))
            (.clash (2, 0) (2, 1)))
          (.reuse 0)
          (.clash (2, 0) (2, 3)))
        (.clash (1, 1) (3, 1))
        (.clash (3, 0) (3, 3))
        (.clash (3, 1) (3, 3))))
    (.clash (0, 2) (2, 2))
    (.reuse 1)
    (.clash (0, 0) (3, 0))
    (.clash (1, 1) (2, 1))
private theorem check196 : check [state192, state195] state196 certificate196 = true := by
  decide +kernel
private theorem closed196 : Closed.{u} state196 :=
  sound (known := [state192, state195]) ⟨closed192.{u}, ⟨closed195.{u}, trivial⟩⟩ check196

private def state197 : Partition := #v[0, 1, 2, 3, 4, 3, 1, 7, 7, 0, 3, 1, 12, 7, 0, 15]
private def certificate197 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (1, 2))
    (.clash (0, 1) (0, 3))
    (.clash (2, 3) (3, 3))
    (.clash (1, 0) (1, 1))
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 1) (3, 1))
      (.clash (0, 1) (0, 3))
      (.transversal ![2, 3, 1, 0]
        (.motif 0 1 2 3 2 1
          (.clash (0, 0) (0, 2)))
        (.clash (0, 0) (0, 2))
        (.clash (0, 1) (0, 2))
        (.clash (0, 0) (2, 0))
        (.clash (0, 1) (3, 1))
        (.clash (0, 0) (0, 1)))
      (.clash (0, 3) (1, 3))
      (.clash (2, 0) (3, 0))
      (.motif 1 3 0 3 0 1
        (.clash (1, 0) (1, 2))))
    (.clash (0, 3) (3, 3))
private theorem check197 : check [] state197 certificate197 = true := by
  decide +kernel
private theorem closed197 : Closed.{u} state197 :=
  sound (known := []) trivial check197

private def state198 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 6, 12, 7, 0, 9]
private def certificate198 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![1, 2, 0, 3]
      (.clash (1, 0) (1, 2))
      (.clash (1, 0) (2, 0))
      (.clash (0, 1) (2, 1))
      (.clash (2, 0) (2, 3))
      (.clash (2, 1) (2, 3))
      (.clash (2, 0) (2, 1)))
    (.clash (0, 1) (1, 1))
    (.clash (0, 1) (2, 1))
    (.clash (1, 0) (1, 1))
    (.transversal ![1, 0, 3, 2]
      (.clash (0, 1) (2, 1))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 3))
        (.clash (0, 0) (0, 1))
        (.transversal ![3, 0, 2, 1]
          (.clash (0, 3) (3, 3))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (3, 1))
            (.clash (0, 1) (0, 3))
            (.motif 2 3 0 1 0 3
              (.clash (0, 3) (1, 3)))
            (.clash (0, 3) (1, 3))
            (.clash (2, 0) (3, 0))
            (.motif 1 3 0 3 0 1
              (.clash (0, 1) (2, 1))))
          (.clash (0, 3) (1, 3))
          (.clash (1, 0) (1, 1))
          (.clash (1, 0) (1, 3))
          (.clash (1, 1) (1, 3)))
        (.clash (3, 1) (3, 2))
        (.clash (0, 0) (2, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (1, 0))
      (.clash (1, 2) (3, 2)))
    (.clash (1, 1) (2, 1))
private theorem check198 : check [] state198 certificate198 = true := by
  decide +kernel
private theorem closed198 : Closed.{u} state198 :=
  sound (known := []) trivial check198

private def state199 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 6, 12, 7, 0, 15]
private def certificate199 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (1, 2) (3, 2))
    (.transversal ![1, 0, 3, 2]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (1, 0) (2, 0))
        (.clash (0, 0) (0, 1))
        (.transversal ![1, 2, 0, 3]
          (.clash (1, 0) (1, 2))
          (.clash (0, 1) (3, 1))
          (.transversal ![1, 3, 2, 0]
            (.clash (0, 1) (3, 1))
            (.clash (0, 1) (1, 1))
            (.clash (1, 0) (3, 0))
            (.clash (1, 1) (1, 3))
            (.clash (2, 0) (3, 0))
            (.motif 1 3 0 1 3 0
              (.clash (0, 0) (2, 0))))
          (.clash (1, 2) (1, 3))
          (.clash (2, 3) (3, 3))
          (.clash (1, 3) (3, 3)))
        (.clash (2, 1) (3, 1))
        (.clash (0, 0) (2, 0)))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (3, 1))
        (.clash (2, 0) (2, 3))
        (.clash (0, 0) (0, 1))
        (.transversal ![3, 1, 0, 2]
          (.reuse 0)
          (.clash (0, 3) (1, 3))
          (.clash (0, 0) (0, 3))
          (.clash (1, 1) (1, 3))
          (.clash (1, 1) (2, 1))
          (.clash (0, 0) (2, 0)))
        (.clash (2, 1) (3, 1))
        (.clash (0, 0) (2, 0)))
      (.clash (0, 0) (0, 1))
      (.clash (1, 0) (1, 2))
      (.clash (0, 0) (1, 0))
      (.clash (1, 2) (3, 2)))
    (.clash (3, 2) (3, 3))
    (.clash (2, 1) (2, 3))
    (.clash (2, 3) (3, 3))
    (.reuse 1)
private theorem check199 : check [state197, state198] state199 certificate199 = true := by
  decide +kernel
private theorem closed199 : Closed.{u} state199 :=
  sound (known := [state197, state198]) ⟨closed197.{u}, ⟨closed198.{u}, trivial⟩⟩ check199

private def state200 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 11, 12, 7, 0, 15]
private def certificate200 : Certificate :=
  .transversal ![0, 2, 3, 1]
    (.clash (1, 2) (3, 2))
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
    (.clash (3, 1) (3, 2))
    (.reuse 1)
    (.clash (1, 2) (1, 3))
    (.clash (1, 3) (2, 3))
private theorem check200 : check [state184, state199] state200 certificate200 = true := by
  decide +kernel
private theorem closed200 : Closed.{u} state200 :=
  sound (known := [state184, state199]) ⟨closed184.{u}, ⟨closed199.{u}, trivial⟩⟩ check200

def state201 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 11, 12, 13, 0, 15]
private def certificate201 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.transversal ![1, 3, 2, 0]
      (.clash (0, 0) (0, 1))
      (.clash (0, 1) (1, 1))
      (.transversal ![1, 0, 2, 3]
        (.clash (1, 0) (3, 0))
        (.clash (0, 1) (1, 1))
        (.clash (3, 0) (3, 3))
        (.clash (1, 0) (1, 1))
        (.transversal ![1, 0, 3, 2]
          (.clash (1, 0) (3, 0))
          (.transversal ![0, 2, 3, 1]
            (.clash (1, 2) (1, 3))
            (.clash (0, 0) (0, 1))
            (.clash (3, 1) (3, 2))
            (.motif 1 3 0 0 2 3
              (.clash (0, 1) (0, 3)))
            (.transversal ![1, 2, 0, 3]
              (.clash (0, 1) (3, 1))
              (.clash (2, 0) (2, 3))
              (.clash (1, 0) (3, 0))
              (.transversal ![2, 0, 3, 1]
                (.reuse 0)
                (.clash (0, 1) (0, 2))
                (.clash (0, 2) (1, 2))
                (.clash (1, 0) (3, 0))
                (.clash (1, 0) (1, 2))
                (.clash (0, 1) (3, 1)))
              (.clash (1, 0) (1, 2))
              (.clash (1, 0) (2, 0)))
            (.clash (0, 1) (3, 1)))
          (.clash (0, 0) (0, 1))
          (.clash (2, 3) (3, 3))
          (.clash (0, 0) (1, 0))
          (.clash (1, 3) (2, 3)))
        (.reuse 1))
      (.clash (1, 1) (1, 3))
      (.clash (0, 0) (3, 0))
      (.reuse 2))
    (.clash (2, 2) (3, 2))
    (.clash (3, 1) (3, 2))
    (.clash (1, 1) (1, 3))
    (.reuse 3)
    (.clash (1, 1) (3, 1))
private theorem check201 : check [state190, state191, state196, state200] state201 certificate201 = true := by
  decide +kernel
private theorem closed201 : Closed.{u} state201 :=
  sound (known := [state190, state191, state196, state200]) ⟨closed190.{u}, ⟨closed191.{u}, ⟨closed196.{u}, ⟨closed200.{u}, trivial⟩⟩⟩⟩ check201

def state202 : Partition := #v[0, 1, 7, 3, 4, 5, 6, 7, 8, 0, 5, 1, 7, 13, 1, 15]
private def certificate202 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (0, 0) (0, 2))
    (.clash (1, 1) (2, 1))
    (.clash (2, 1) (3, 1))
    (.clash (0, 2) (2, 2))
    (.clash (3, 0) (3, 1))
    (.clash (1, 1) (3, 1))
private theorem check202 : check [] state202 certificate202 = true := by
  decide +kernel
private theorem closed202 : Closed.{u} state202 :=
  sound (known := []) trivial check202

def state203 : Partition := #v[0, 1, 7, 3, 4, 5, 6, 7, 8, 7, 5, 1, 7, 13, 1, 15]
private def certificate203 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (0, 0) (0, 2))
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 1) (1, 2))
      (.clash (0, 0) (0, 1))
      (.clash (1, 1) (3, 1))
      (.clash (1, 2) (3, 2))
      (.transversal ![0, 2, 1, 3]
        (.clash (1, 1) (1, 2))
        (.clash (0, 0) (0, 2))
        (.transversal ![1, 2, 0, 3]
          (.clash (0, 1) (3, 1))
          (.clash (2, 0) (2, 3))
          (.clash (0, 0) (0, 1))
          (.transversal ![2, 0, 3, 1]
            (.clash (1, 0) (1, 3))
            (.clash (0, 1) (0, 2))
            (.clash (0, 2) (1, 2))
            (.transversal ![3, 0, 2, 1]
              (.clash (0, 1) (0, 3))
              (.clash (0, 0) (0, 3))
              (.columns)
              (.clash (0, 0) (0, 1))
              (.clash (0, 1) (3, 1))
              (.clash (0, 0) (2, 0)))
            (.clash (1, 0) (1, 2))
            (.clash (0, 1) (3, 1)))
          (.clash (1, 1) (1, 2))
          (.clash (0, 0) (2, 0)))
        (.clash (0, 2) (1, 2))
        (.clash (3, 1) (3, 3))
        (.clash (1, 3) (3, 3)))
      (.clash (0, 1) (3, 1)))
    (.motif 0 3 2 1 0 2
      (.clash (1, 1) (3, 1)))
    (.clash (0, 2) (2, 2))
    (.clash (2, 1) (3, 1))
    (.clash (1, 1) (3, 1))
private theorem check203 : check [] state203 certificate203 = true := by
  decide +kernel
private theorem closed203 : Closed.{u} state203 :=
  sound (known := []) trivial check203

private def state204 : Partition := #v[0, 1, 2, 3, 4, 5, 1, 2, 2, 4, 5, 0, 5, 2, 0, 1]
private def certificate204 : Certificate :=
  .transversal ![3, 1, 0, 2]
    (.motif 0 1 2 2 1 3
      (.clash (0, 0) (0, 1)))
    (.clash (0, 2) (0, 3))
    (.clash (0, 0) (0, 3))
    (.clash (0, 2) (2, 2))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (0, 2))
private theorem check204 : check [] state204 certificate204 = true := by
  decide +kernel
private theorem closed204 : Closed.{u} state204 :=
  sound (known := []) trivial check204

private def state205 : Partition := #v[0, 1, 2, 3, 4, 5, 1, 7, 8, 9, 5, 0, 5, 7, 0, 9]
private def certificate205 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.clash (1, 0) (1, 2))
    (.clash (0, 1) (1, 1))
    (.clash (0, 1) (2, 1))
    (.clash (1, 0) (1, 1))
    (.motif 3 1 2 1 0 3
      (.clash (0, 0) (3, 0)))
    (.clash (1, 1) (2, 1))
private theorem check205 : check [] state205 certificate205 = true := by
  decide +kernel
private theorem closed205 : Closed.{u} state205 :=
  sound (known := []) trivial check205

private def state206 : Partition := #v[0, 1, 2, 3, 4, 5, 1, 7, 8, 9, 5, 11, 5, 0, 11, 15]
private def certificate206 : Certificate :=
  .transversal ![0, 2, 1, 3]
    (.clash (0, 0) (0, 1))
    (.clash (2, 1) (3, 1))
    (.clash (3, 1) (3, 3))
    (.clash (0, 1) (2, 1))
    (.transversal ![0, 3, 1, 2]
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 0) (0, 1))
        (.motif 3 2 1 2 0 3
          (.clash (0, 0) (3, 0)))
        (.clash (1, 2) (3, 2))
        (.clash (0, 0) (2, 0))
        (.clash (1, 3) (2, 3))
        (.clash (2, 0) (2, 3)))
      (.clash (2, 1) (3, 1))
      (.clash (3, 1) (3, 2))
      (.transversal ![1, 3, 0, 2]
        (.clash (0, 1) (2, 1))
        (.motif 3 2 1 2 0 3
          (.clash (1, 1) (1, 3)))
        (.clash (1, 2) (3, 2))
        (.clash (2, 0) (2, 1))
        (.clash (1, 3) (2, 3))
        (.clash (2, 0) (2, 3)))
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (2, 3)))
    (.transversal ![0, 3, 1, 2]
      (.transversal ![1, 0, 2, 3]
        (.clash (1, 0) (1, 2))
        (.clash (0, 1) (1, 1))
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (1, 1))
        (.motif 1 3 2 1 3 0
          (.clash (0, 0) (2, 0)))
        (.clash (1, 1) (2, 1)))
      (.clash (2, 1) (3, 1))
      (.clash (3, 1) (3, 2))
      (.clash (1, 3) (3, 3))
      (.clash (1, 3) (2, 3))
      (.clash (2, 1) (2, 3)))
private theorem check206 : check [] state206 certificate206 = true := by
  decide +kernel
private theorem closed206 : Closed.{u} state206 :=
  sound (known := []) trivial check206

private def state207 : Partition := #v[0, 1, 2, 3, 1, 3, 0, 2, 8, 0, 3, 1, 3, 2, 1, 0]
private def certificate207 : Certificate :=
  .transversal ![2, 1, 0, 3]
    (.clash (0, 2) (0, 3))
    (.columns)
    (.clash (0, 0) (0, 2))
    (.clash (2, 0) (2, 2))
    (.clash (0, 0) (0, 3))
    (.clash (0, 0) (2, 0))
private theorem check207 : check [] state207 certificate207 = true := by
  decide +kernel
private theorem closed207 : Closed.{u} state207 :=
  sound (known := []) trivial check207

private def state208 : Partition := #v[0, 1, 2, 3, 1, 3, 0, 7, 8, 7, 3, 1, 3, 13, 1, 15]
private def certificate208 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.clash (1, 2) (1, 3))
    (.clash (0, 0) (0, 3))
    (.motif 1 3 0 0 1 2
      (.clash (0, 2) (0, 3)))
    (.clash (0, 3) (1, 3))
    (.clash (2, 1) (3, 1))
    (.clash (1, 1) (3, 1))
private theorem check208 : check [] state208 certificate208 = true := by
  decide +kernel
private theorem closed208 : Closed.{u} state208 :=
  sound (known := []) trivial check208

private def state209 : Partition := #v[0, 1, 2, 3, 1, 3, 6, 7, 8, 9, 3, 1, 3, 0, 1, 15]
private def certificate209 : Certificate :=
  .transversal ![0, 3, 1, 2]
    (.motif 0 1 2 3 0 1
      (.clash (2, 1) (3, 1)))
    (.clash (2, 1) (3, 1))
    (.clash (0, 0) (0, 1))
    (.transversal ![0, 2, 1, 3]
      (.motif 1 3 0 0 1 2
        (.clash (0, 2) (0, 3)))
      (.clash (2, 1) (3, 1))
      (.clash (3, 1) (3, 3))
      (.clash (1, 2) (1, 3))
      (.transversal ![2, 0, 1, 3]
        (.clash (0, 1) (0, 2))
        (.motif 0 2 1 3 1 2
          (.clash (1, 0) (1, 2)))
        (.clash (0, 2) (1, 2))
        (.clash (0, 1) (2, 1))
        (.clash (1, 0) (1, 2))
        (.clash (1, 2) (1, 3)))
      (.clash (1, 3) (3, 3)))
    (.clash (1, 0) (1, 3))
    (.clash (0, 1) (2, 1))
private theorem check209 : check [] state209 certificate209 = true := by
  decide +kernel
private theorem closed209 : Closed.{u} state209 :=
  sound (known := []) trivial check209

private def state210 : Partition := #v[0, 1, 2, 3, 1, 5, 6, 7, 8, 9, 5, 1, 5, 3, 1, 15]
private def certificate210 : Certificate :=
  .transversal ![0, 3, 2, 1]
    (.transversal ![0, 2, 3, 1]
      (.clash (1, 2) (1, 3))
      (.clash (0, 0) (0, 1))
      (.clash (0, 0) (0, 3))
      (.clash (1, 0) (1, 2))
      (.motif 1 3 0 1 2 0
        (.clash (0, 0) (0, 3)))
      (.clash (0, 1) (0, 3)))
    (.clash (0, 0) (3, 0))
    (.clash (0, 0) (0, 3))
    (.clash (1, 1) (1, 3))
    (.clash (0, 3) (1, 3))
    (.clash (1, 1) (3, 1))
private theorem check210 : check [] state210 certificate210 = true := by
  decide +kernel
private theorem closed210 : Closed.{u} state210 :=
  sound (known := []) trivial check210

private def state211 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 1, 5, 13, 1, 4]
private def certificate211 : Certificate :=
  .transversal ![1, 2, 0, 3]
    (.clash (1, 2) (3, 2))
    (.clash (2, 0) (2, 3))
    (.clash (2, 3) (3, 3))
    (.transversal ![2, 1, 0, 3]
      (.clash (0, 2) (2, 2))
      (.clash (0, 2) (1, 2))
      (.transversal ![0, 2, 1, 3]
        (.clash (0, 0) (2, 0))
        (.transversal ![3, 0, 1, 2]
          (.clash (0, 2) (0, 3))
          (.clash (0, 0) (0, 3))
          (.clash (0, 1) (0, 3))
          (.clash (0, 0) (0, 2))
          (.clash (0, 1) (0, 2))
          (.clash (0, 0) (0, 1)))
        (.clash (0, 0) (0, 2))
        (.clash (2, 0) (2, 1))
        (.clash (0, 2) (1, 2))
        (.motif 1 2 0 2 1 0
          (.clash (0, 0) (3, 0))))
      (.clash (1, 1) (1, 2))
      (.clash (1, 0) (1, 1))
      (.clash (1, 0) (1, 2)))
    (.clash (1, 0) (1, 2))
    (.clash (1, 0) (2, 0))
private theorem check211 : check [] state211 certificate211 = true := by
  decide +kernel
private theorem closed211 : Closed.{u} state211 :=
  sound (known := []) trivial check211

private def state212 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 1, 5, 13, 1, 15]
private def certificate212 : Certificate :=
  .transversal ![1, 0, 2, 3]
    (.transversal ![3, 0, 2, 1]
      (.clash (0, 1) (0, 3))
      (.transversal ![0, 2, 3, 1]
        (.transversal ![0, 3, 1, 2]
          (.clash (1, 2) (1, 3))
          (.transversal ![0, 3, 2, 1]
            (.clash (1, 2) (1, 3))
            (.clash (0, 0) (0, 3))
            (.clash (2, 1) (3, 1))
            (.clash (0, 3) (1, 3))
            (.transversal ![2, 3, 1, 0]
              (.transversal ![2, 0, 1, 3]
                (.clash (0, 1) (0, 2))
                (.clash (0, 0) (0, 2))
                (.clash (1, 3) (3, 3))
                (.clash (0, 0) (0, 1))
                (.clash (2, 3) (3, 3))
                (.reuse 0))
              (.clash (0, 0) (0, 2))
              (.clash (0, 2) (0, 3))
              (.clash (1, 2) (1, 3))
              (.clash (0, 3) (1, 3))
              (.clash (0, 0) (0, 3)))
            (.clash (1, 1) (3, 1)))
          (.clash (0, 0) (0, 1))
          (.reuse 1)
          (.clash (1, 0) (1, 3))
          (.clash (0, 1) (2, 1)))
        (.clash (0, 0) (0, 1))
        (.reuse 2)
        (.clash (1, 0) (1, 2))
        (.motif 1 3 2 2 0 1
          (.clash (0, 1) (2, 1)))
        (.clash (0, 1) (3, 1)))
      (.reuse 3)
      (.clash (0, 1) (1, 1))
      (.clash (0, 1) (3, 1))
      (.clash (1, 1) (3, 1)))
    (.clash (0, 1) (1, 1))
    (.clash (2, 3) (3, 3))
    (.clash (1, 0) (1, 1))
    (.reuse 4)
    (.clash (3, 0) (3, 3))
private theorem check212 : check [state207, state208, state209, state210, state211] state212 certificate212 = true := by
  decide +kernel
private theorem closed212 : Closed.{u} state212 :=
  sound (known := [state207, state208, state209, state210, state211]) ⟨closed207.{u}, ⟨closed208.{u}, ⟨closed209.{u}, ⟨closed210.{u}, ⟨closed211.{u}, trivial⟩⟩⟩⟩⟩ check212

def state213 : Partition := #v[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 5, 11, 5, 13, 11, 15]
private def certificate213 : Certificate :=
  .transversal ![1, 2, 3, 0]
    (.transversal ![0, 2, 3, 1]
      (.clash (0, 0) (0, 1))
      (.transversal ![0, 3, 2, 1]
        (.clash (1, 3) (2, 3))
        (.clash (0, 0) (3, 0))
        (.clash (3, 1) (3, 2))
        (.clash (1, 1) (1, 3))
        (.transversal ![0, 2, 1, 3]
          (.clash (0, 0) (0, 1))
          (.clash (2, 1) (2, 3))
          (.clash (2, 3) (3, 3))
          (.clash (0, 1) (2, 1))
          (.transversal ![1, 3, 0, 2]
            (.clash (0, 1) (3, 1))
            (.motif 2 3 1 2 3 0
              (.clash (0, 0) (1, 0)))
            (.clash (0, 0) (0, 1))
            (.transversal ![2, 1, 0, 3]
              (.clash (0, 2) (2, 2))
              (.transversal ![2, 0, 1, 3]
                (.clash (1, 0) (1, 3))
                (.clash (2, 0) (2, 1))
                (.clash (0, 1) (0, 2))
                (.reuse 0)
                (.clash (1, 0) (1, 2))
                (.clash (0, 1) (2, 1)))
              (.clash (0, 1) (0, 2))
              (.clash (1, 1) (1, 3))
              (.clash (0, 1) (1, 1))
              (.clash (0, 1) (3, 1)))
            (.clash (1, 3) (2, 3))
            (.clash (0, 0) (2, 0)))
          (.reuse 1))
        (.clash (1, 1) (3, 1)))
      (.reuse 2)
      (.clash (1, 2) (3, 2))
      (.clash (0, 1) (3, 1))
      (.clash (3, 1) (3, 2)))
    (.reuse 3)
    (.clash (0, 1) (1, 1))
    (.clash (1, 2) (3, 2))
    (.clash (1, 1) (1, 2))
    (.clash (2, 2) (2, 3))
private theorem check213 : check [state204, state205, state206, state212] state213 certificate213 = true := by
  decide +kernel
private theorem closed213 : Closed.{u} state213 :=
  sound (known := [state204, state205, state206, state212]) ⟨closed204.{u}, ⟨closed205.{u}, ⟨closed206.{u}, ⟨closed212.{u}, trivial⟩⟩⟩⟩ check213

/-- Checked states in this part consumed by later certificate parts. -/
theorem boundary11 : Known.{u} [state201, state202, state203, state213] :=
  ⟨closed201.{u}, ⟨closed202.{u}, ⟨closed203.{u}, ⟨closed213.{u}, trivial⟩⟩⟩⟩

end MaLatin.OrderFourChecker
