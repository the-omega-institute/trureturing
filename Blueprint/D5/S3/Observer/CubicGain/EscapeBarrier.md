# EscapeBarrier

## Abstract

The explicit integer polynomials E₀,E₁,E₂,E₃ are barrier0 through barrier3

The rational boundary curves are R₀(z)=(-3(72z³+746z²+465z+130)/(5(z³-8z-4)),-3(375z³+4431z²+2486z+344)/(5(z³-8z-4))); R₁(z)=(-6(36z⁴+61z³+221z²+181z+30)/(5(z+1)(z³-4z-2)),-3(375z⁴+881z³+2486z²+1706z+266)/(5(z+1)(z³-4z-2))); B₀(z)=(-3(16z²-80z+65)/(10(z-1)),3(45z²+125z-172)/(10(z-1))); B₁(z)=(-6(8z³-24z²-2z+15)/(5(2z²-1)),3(45z³+215z²-33z-133)/(5(2z²-1))). The R branches use z>0 and the B branches use z≥0, with their displayed poles omitted.

The explicit integer polynomials E₀,E₁,E₂,E₃ are barrier0 through barrier3. The escape barrier is E₀E₁E₂E₃((5p+216)²+(v+225)²). The open response set O additionally requires p≠24. Only vanishing on necessary escape responses is claimed, with no converse realization claim.

The polynomial closure consists of the original gain a and the single whole scaled gain h=Ua, together with the drift offset ε and actual fifth and sixth responses. Every actual parent satisfies its identities, as expressed by CompactWorld.closureWorld_actual. These polynomial equations are preserved under limits of actual worlds.

At x=1, the source identities force k=t=1, the gain scaling forces a=0 and ε=-24, and the scaled gain samples at clocks 1,2,3,4 are 48,294/5,48,18. Cubic interpolation gives h(5)=-144/5 and h(6)=-90. The response equations then give (-216/5,-225). The scaling is of one whole gain, with h(0)=66/5 derived from the same polynomial.

At x=0,k=1 the parent forces ε=3/10, a(5)=-24/5, and the finite fifth-response equation is contradictory. At x=k=0 the rate variable u distinguishes the two r endpoints and gives B₀(0)=(39/2,258/5) or B₁(0)=(18,399/5), without division by zero traces.

At x=0 and 0<k<1 set j=k/(1-k)>0. The source forces r=0 or r=1. The drift equation excludes j=1 on the first branch and 2j²=1 on the second. Solving the actual response equations yields B₀(j) or B₁(j). At 0<x<1 with r=0 or r=1 the source gives k=x and the original finite b=x/(1-x) parent is recovered, yielding R₀(b) or R₁(b). All endpoint parent poles are excluded by their parent equations.

Each rational curve annihilates the corresponding displayed integer polynomial by direct substitution and denominator clearing. The boundary cases exhaust r=0, r=1, b→0 and b→∞ in the compactification. The finite-source lift recovers the exact parent equation, original gain and chronological response at every interior closure point.

**Theorem 1.1 (finite closure lift).**

Lean statement: `D5/S3/Observer/CubicGain/EscapeBarrier.finite_closure_lift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/EscapeBarrier.finite_closure_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every ClosureWorld with 0<x<1 and 0<k<1, b=x/(1-x) recovers a solution of the parent equation, the original gain a equals that parent’s gain, and its actual response is exactly (p,v).

**Theorem 1.2 (closure boundary barrier).**

Lean statement: `D5/S3/Observer/CubicGain/EscapeBarrier.closure_boundary_barrier`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/CubicGain/EscapeBarrier.closure_boundary_barrier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ClosureWorld with r=0, r=1, x=0 or x=1 has escapeBarrier(p,v)=0. This is a necessary boundary condition, with no converse realization assertion.

## References

- Truth anchor: `D5/S3/Observer/CubicGain/EscapeBarrier.closure_boundary_barrier`
- Truth anchor: `D5/S3/Observer/CubicGain/EscapeBarrier.finite_closure_lift`
- Dependency: [D5/S3/Observer/CubicGain/BoundedWholeGain](BoundedWholeGain.md)
