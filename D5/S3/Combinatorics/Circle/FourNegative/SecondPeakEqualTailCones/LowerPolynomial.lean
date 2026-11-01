/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowerPolynomial
   generality: I
   mirror-B: none(waiver:private-consumed-ceiling-polynomials)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: Thirteen exact positive polynomials for the unbounded lower cone. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open private heads newHeads delta
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source

private def lowerPolynomial (x y z : ℤ) : Fin 13 → ℤ :=
  let A := heads x y z 0
  let B := heads x y z 1
  let L := heads x y z 2
  let M := heads x y z 3
  let Bn := newHeads x y z 1
  let Ln := newHeads x y z 2
  let Mn := newHeads x y z 3
  ![B+M-2*A, 2*A-B-1, Bn+Mn-4*A, 4*A-Bn-1,
    2*B-A-L, A-B-L, L*(2*Bn-3*A-Ln)+A*z^2,
    L*(3*A-Bn-1-Ln)-A*z^2, A-2*L, A*z^2,
    L*(A-1-2*Ln)-A*z^2, M-L, L*(y-3)-M+1]

-- Each branch is an actual ring identity and positivity proof for y=2*z^2+w.
-- All 373 supplied positive coefficients occur as integer literals; no external truth input.
set_option maxHeartbeats 8000000 in
private theorem lower_polynomials (u v w : ℤ) (hu : 0≤u) (hv : 0≤v) (hw : 0≤w) :
    ∀ i, 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) i := by
  intro i
  fin_cases i
  · -- P1: old1_lower; 21 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (0 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 0 =
        4256 + 33*w + 2725*v +
        13*v*w + 610*v^2 + v^2*w +
        58*v^3 + 2*v^4 + 4176*u +
        16*u*w + 1993*u*v + 3*u*v*w +
        296*u*v^2 + 14*u*v^3 + 1546*u^2 +
        2*u^2*w + 488*u^2*v + 36*u^2*v^2 +
        256*u^3 + 40*u^3*v + 16*u^4 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P2: old1_cap; 19 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (1 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 1 =
        5088 + 40*w + 1787*v +
        4*v*w + 208*v^2 + 8*v^3 +
        4848*u + 18*u*w + 1279*u*v +
        u*v*w + 100*u*v^2 + 2*u*v^3 +
        1726*u^2 + 2*u^2*w + 304*u^2*v +
        12*u^2*v^2 + 272*u^3 + 24*u^3*v +
        16*u^4 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P3: new1_lower; 21 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (2 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 2 =
        7358 + 57*w + 5034*v +
        25*v*w + 1170*v^2 + 2*v^2*w +
        114*v^3 + 4*v^4 + 7520*u +
        30*u*w + 3786*u*v + 6*u*v*w +
        580*u*v^2 + 28*u*v^3 + 2892*u^2 +
        4*u^2*w + 952*u^2*v + 72*u^2*v^2 +
        496*u^3 + 80*u^3*v + 32*u^4 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P4: new1_cap; 19 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (3 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 3 =
        10178 + 80*w + 3574*v +
        8*v*w + 416*v^2 + 16*v^3 +
        9696*u + 36*u*w + 2558*u*v +
        2*u*v*w + 200*u*v^2 + 4*u*v^3 +
        3452*u^2 + 4*u^2*w + 608*u^2*v +
        24*u^2*v^2 + 544*u^3 + 48*u^3*v +
        32*u^4 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P5: old2_lower; 19 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (4 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 4 =
        3332 + 28*w + 1337*v +
        4*v*w + 179*v^2 + 8*v^3 +
        3521*u + 15*u*w + 1054*u*v +
        u*v*w + 93*u*v^2 + 2*u*v^3 +
        1392*u^2 + 2*u^2*w + 276*u^2*v +
        12*u^2*v^2 + 244*u^3 + 24*u^3*v +
        16*u^4 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P6: old2_cap; 11 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (5 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 5 =
        147 + 4*w + 42*v +
        3*v^2 + 141*u + u*w +
        27*u*v + u*v^2 + 42*u^2 +
        4*u^2*v + 4*u^3 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P7: new2_lower_timesL; 51 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (6 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 6 =
        972314 + 8884*w + 679621*v +
        3768*v*w + 188200*v^2 + 524*v^2*w +
        25861*v^3 + 24*v^3*w + 1766*v^4 +
        48*v^5 + 1742735*u + 11037*u*w +
        1024865*u*v + 3614*u*v*w + 231446*u*v^2 +
        359*u*v^2*w + 24721*u*v^3 + 10*u*v^3*w +
        1210*u*v^4 + 20*u*v^5 + 1331554*u^2 +
        5452*u^2*w + 640748*u^2*v + 1292*u^2*v*w +
        113203*u^2*v^2 + 81*u^2*v^2*w + 8788*u^2*v^3 +
        u^2*v^3*w + 272*u^2*v^4 + 2*u^2*v^5 +
        562600*u^3 + 1340*u^3*w + 212672*u^3*v +
        204*u^3*v*w + 27528*u^3*v^2 + 6*u^3*v^2*w +
        1376*u^3*v^3 + 20*u^3*v^4 + 142044*u^4 +
        164*u^4*w + 39536*u^4*v + 12*u^4*v*w +
        3328*u^4*v^2 + 80*u^4*v^3 + 21440*u^5 +
        8*u^5*w + 3904*u^5*v + 160*u^5*v^2 +
        1792*u^6 + 160*u^6*v + 64*u^7 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P8: new2_cap_timesL; 51 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (7 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 7 =
        1322132 + 12172*w + 793313*v +
        4048*v*w + 189986*v^2 + 444*v^2*w +
        22687*v^3 + 16*v^3*w + 1350*v^4 +
        32*v^5 + 2244301*u + 13955*u*w +
        1154825*u*v + 3748*u*v*w + 230766*u*v^2 +
        315*u*v^2*w + 22113*u*v^3 + 8*u*v^3*w +
        994*u*v^4 + 16*u*v^5 + 1630794*u^2 +
        6424*u^2*w + 699636*u^2*v + 1308*u^2*v*w +
        112009*u^2*v^2 + 75*u^2*v^2*w + 8078*u^2*v^3 +
        u^2*v^3*w + 244*u^2*v^4 + 2*u^2*v^5 +
        657704*u^3 + 1484*u^3*w + 225880*u^3*v +
        204*u^3*v*w + 27172*u^3*v^2 + 6*u^3*v^2*w +
        1312*u^3*v^3 + 20*u^3*v^4 + 159028*u^4 +
        172*u^4*w + 41000*u^4*v + 12*u^4*v*w +
        3296*u^4*v^2 + 80*u^4*v^3 + 23056*u^5 +
        8*u^5*w + 3968*u^5*v + 160*u^5*v^2 +
        1856*u^6 + 160*u^6*v + 64*u^7 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P9: old3_cap; 19 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (8 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 8 =
        3955 + 36*w + 1502*v +
        4*v*w + 190*v^2 + 8*v^3 +
        4029*u + 17*u*w + 1144*u*v +
        u*v*w + 96*u*v^2 + 2*u*v^3 +
        1528*u^2 + 2*u^2*w + 288*u^2*v +
        12*u^2*v^2 + 256*u^3 + 24*u^3*v +
        16*u^4 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P10: new3_lower_timesL; 41 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (9 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 9 =
        295232 + 2304*w + 180304*v +
        832*v*w + 44037*v^2 + 100*v^2*w +
        5376*v^3 + 4*v^3*w + 328*v^4 +
        8*v^5 + 434400*u + 2240*u*w +
        221220*u*v + 608*u*v*w + 43265*u*v^2 +
        49*u*v^2*w + 3968*u*v^3 + u*v^3*w +
        162*u*v^4 + 2*u*v^5 + 266292*u^2 +
        816*u^2*w + 108548*u^2*v + 148*u^2*v*w +
        15936*u^2*v^2 + 6*u^2*v^2*w + 976*u^2*v^3 +
        20*u^2*v^4 + 87044*u^3 + 132*u^3*w +
        26624*u^3*v + 12*u^3*v*w + 2608*u^3*v^2 +
        80*u^3*v^3 + 16000*u^4 + 8*u^4*w +
        3264*u^4*v + 160*u^4*v^2 + 1568*u^5 +
        160*u^5*v + 64*u^6 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P11: new3_cap_timesL; 51 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (10 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 10 =
        795074 + 9540*w + 529648*v +
        3400*v*w + 140455*v^2 + 404*v^2*w +
        18546*v^3 + 16*v^3*w + 1220*v^4 +
        32*v^5 + 1492713*u + 11489*u*w +
        844125*u*v + 3298*u*v*w + 184704*u*v^2 +
        297*u*v^2*w + 19294*u*v^3 + 8*u*v^3*w +
        938*u*v^4 + 16*u*v^5 + 1183838*u^2 +
        5556*u^2*w + 553144*u^2*v + 1204*u^2*v*w +
        95957*u^2*v^2 + 73*u^2*v^2*w + 7440*u^2*v^3 +
        u^2*v^3*w + 238*u^2*v^4 + 2*u^2*v^5 +
        515840*u^3 + 1348*u^3*w + 191340*u^3*v +
        196*u^3*v*w + 24688*u^3*v^2 + 6*u^3*v^2*w +
        1264*u^3*v^3 + 20*u^3*v^4 + 133684*u^4 +
        164*u^4*w + 36928*u^4*v + 12*u^4*v*w +
        3152*u^4*v^2 + 80*u^4*v^3 + 20640*u^5 +
        8*u^5*w + 3776*u^5*v + 160*u^5*v^2 +
        1760*u^6 + 160*u^6*v + 64*u^7 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P12: C_nonnegative; 21 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (11 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 11 =
        9016 + 73*w + 4431*v +
        17*v*w + 813*v^2 + v^2*w +
        66*v^3 + 2*v^4 + 8798*u +
        34*u*w + 3236*u*v + 4*u*v*w +
        395*u*v^2 + 16*u*v^3 + 3220*u^2 +
        4*u^2*w + 788*u^2*v + 48*u^2*v^2 +
        524*u^3 + 64*u^3*v + 32*u^4 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity
  · -- P13: C_capacity; 29 positive coefficients.
    change 0<lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) (12 : Fin 13)
    have he : lowerPolynomial (4+u) (2*(2*(4+u)+v)^2+w) (2*(4+u)+v) 12 =
        31781 + 256*w + 16141*v +
        64*v*w + 3057*v^2 + 4*v^2*w +
        256*v^3 + 8*v^4 + 40282*u +
        192*u*w + 16276*u*v + 32*u*v*w +
        2301*u*v^2 + u*v^2*w + 128*u*v^3 +
        2*u*v^4 + 20324*u^2 + 48*u^2*w +
        6132*u^2*v + 4*u^2*v*w + 576*u^2*v^2 +
        16*u^2*v^3 + 5108*u^3 + 4*u^3*w +
        1024*u^3*v + 48*u^3*v^2 + 640*u^4 +
        64*u^4*v + 32*u^5 := by
      dsimp [lowerPolynomial,heads,newHeads,delta]
      ring
    rw [he]
    positivity

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
