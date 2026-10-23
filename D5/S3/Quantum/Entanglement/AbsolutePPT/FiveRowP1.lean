/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1
   mirror-E: none(waiver:scalar-inequalities-and-exact-kernel-certificates-without-experimental-claims)
   anchors: []
   utility: kind=checker; basis=terminal=gid:D5/S3/Quantum/Entanglement/AbsolutePPT/FiveRowP1.scalar_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/N25A.accepted
   digest: Full P1 scalar bound for every real j in the closed interval for N25 through N90, with both tail branches. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N25B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N30B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N35A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N35B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N40A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N40B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N45A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N45B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N50A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N50B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N55A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N55B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N60A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N60B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N65A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N65B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N70A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N70B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N75A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N75B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N80A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N80B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N85A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N85B
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N90A
import D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.N90B

set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra
open D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Checker
open D5.S3.Quantum.Entanglement.AbsolutePPT

/-- The live full-range scalar consumer. The literal APPT-to-Hyp bridge is
outside this theorem. All 28 closed checks are used, not assumed. -/
theorem scalar_bound (n : Nat) (hn : 5 ≤ n) (hn' : n ≤ 18)
    (j r H D q a : ℝ) (hj : 10 ≤ j) (hj' : j ≤ (5*n : Nat)-15)
    (h : Hyp r H D q a) :
    (5*n : Nat)+2*j*r+j*r^2+2*(1+r)*H-2*D+a+q ≤
      (((5*n : Nat)+8 : ℝ)/((5*n : Nat)+2 : ℝ)^2)*
        ((5*n : Nat)+j*r+H-D)^2 := by
  interval_cases n
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 25 (by decide) (by decide) false
        P1Data.N25A.nodes P1Data.N25A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 25 (by decide) (by decide) true
        P1Data.N25B.nodes P1Data.N25B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 30 (by decide) (by decide) false
        P1Data.N30A.nodes P1Data.N30A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 30 (by decide) (by decide) true
        P1Data.N30B.nodes P1Data.N30B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 35 (by decide) (by decide) false
        P1Data.N35A.nodes P1Data.N35A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 35 (by decide) (by decide) true
        P1Data.N35B.nodes P1Data.N35B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 40 (by decide) (by decide) false
        P1Data.N40A.nodes P1Data.N40A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 40 (by decide) (by decide) true
        P1Data.N40B.nodes P1Data.N40B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 45 (by decide) (by decide) false
        P1Data.N45A.nodes P1Data.N45A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 45 (by decide) (by decide) true
        P1Data.N45B.nodes P1Data.N45B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 50 (by decide) (by decide) false
        P1Data.N50A.nodes P1Data.N50A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 50 (by decide) (by decide) true
        P1Data.N50B.nodes P1Data.N50B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 55 (by decide) (by decide) false
        P1Data.N55A.nodes P1Data.N55A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 55 (by decide) (by decide) true
        P1Data.N55B.nodes P1Data.N55B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 60 (by decide) (by decide) false
        P1Data.N60A.nodes P1Data.N60A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 60 (by decide) (by decide) true
        P1Data.N60B.nodes P1Data.N60B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 65 (by decide) (by decide) false
        P1Data.N65A.nodes P1Data.N65A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 65 (by decide) (by decide) true
        P1Data.N65B.nodes P1Data.N65B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 70 (by decide) (by decide) false
        P1Data.N70A.nodes P1Data.N70A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 70 (by decide) (by decide) true
        P1Data.N70B.nodes P1Data.N70B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 75 (by decide) (by decide) false
        P1Data.N75A.nodes P1Data.N75A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 75 (by decide) (by decide) true
        P1Data.N75B.nodes P1Data.N75B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 80 (by decide) (by decide) false
        P1Data.N80A.nodes P1Data.N80A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 80 (by decide) (by decide) true
        P1Data.N80B.nodes P1Data.N80B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 85 (by decide) (by decide) false
        P1Data.N85A.nodes P1Data.N85A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 85 (by decide) (by decide) true
        P1Data.N85B.nodes P1Data.N85B.accepted r H D q a j h hb hj hj'
  · rcases h.tail with hA | hB
    · have hb : Branch false r H D q a := by simpa [Branch] using hA
      simpa [energy, theta, mass] using checked_scalar_bound 90 (by decide) (by decide) false
        P1Data.N90A.nodes P1Data.N90A.accepted r H D q a j h hb hj hj'
    · have hb : Branch true r H D q a := by simpa [Branch] using hB
      simpa [energy, theta, mass] using checked_scalar_bound 90 (by decide) (by decide) true
        P1Data.N90B.nodes P1Data.N90B.accepted r H D q a j h hb hj hj'
end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1
