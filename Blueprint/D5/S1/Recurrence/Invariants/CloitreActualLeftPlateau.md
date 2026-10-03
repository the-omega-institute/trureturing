# Actual Cloitre Left Fibonacci Platforms

## Abstract

The actual Cloitre sequence has exact maximal left Fibonacci platforms, a simultaneous upper cone, and a prescribed boundary phase under its full source hypotheses.

F denotes the Fibonacci sequence with F(0)=0 and F(1)=1. C, D, T, X, d and g are the actual finite-prefix sequence, legal domain, inner map, orbit, depth and selected point of CloitreActualRightProfile. Every occurrence uses this same actual sequence and prescribed orbit. In particular, T(N,x)=N-C(x), X(N,i) starts at N-1, d(N)=C(N-1), g(N)=X(N,d(N)), and C(N)=C(g(N))+C(N-g(N)) for N at least three.

**Definition 1.1 (Upper-anchor height deficit).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.heightDeficit`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.heightDeficit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

heightDeficit(m,t)=F(m-1)-C(F(m)-t), with natural subtraction. For m at least eight and t at most F(m-2), the theorem also proves C(F(m)-t)<=F(m-1), so the subtraction records the exact nonnegative integer deficit. This differs from C(n)-G(n).

**Definition 1.2 (Left platform width).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.platformWidth`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.platformWidth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

platformWidth(m)=(2*m-9)/3 using natural integer division. On the stated domain this is floor((2*m-9)/3).

**Definition 1.3 (Complete conditional source hypotheses).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.Hyp24_1`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.Hyp24_1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hyp24_1(U) extends the unchanged Hyp21_1(U): its conditional SourceFoundations, global golden and U bounds, piecewise U formula, positive-index monotonicity and unit increment of U, Fibonacci anchor and successor values, all right-collar domain, invariance, capture and periodic containment clauses, and prescribed DepthEntry. It also requires C(F(j)-1)=F(j-1) for j at least five. For j at least six, b at most F(j-1), and N=F(j+1)-b, the negative interval [F(j)-b,F(j)] intersect D(N) is invariant and captures every legal starting point. Each legal periodic point of the same T(N) lies between max(F(j-1),F(j)-b) and min(F(j),F(j)+F(j-3)-b). No inhabitant of these conditional foundations, monotonicity of C, or limiting ratio is asserted.

**Theorem 1.4 (Maximal platforms, upper cone, actual routes and boundary phase).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.full24_3`

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.full24_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every U satisfying Hyp24_1 and every m at least eight, the complete closed block 0<=t<=F(m-2) has zero height deficit exactly when t<=platformWidth(m). Beyond it, 1<=heightDeficit(m,t)<=max(1,t-platformWidth(m)-1). Thus the left platform is maximal and the block has no disconnected platform at the same height.

For every natural W and m>=max(8,(3*W+10)/2), all t<=W satisfy C(F(m)-t)=F(m-1). The threshold equals ceil((3*W+9)/2), and the legal closed-block domain follows from the bound on the platform width.

For j at least nine, b<=F(j-1), and N=F(j+1)-b, put z=F(j)-g(N) and w=F(j-1)-(N-g(N)). The actual children reconstruct as g(N)=F(j)-z and N-g(N)=F(j-1)-w, with z+w=b, z<=F(j-2), and w<=F(j-3). Parent deficit zero is equivalent to either (z,w)=(b,0), b<=platformWidth(j), or (z,w)=(platformWidth(j),1), b=platformWidth(j)+1, and F(j) odd.

At N=F(j+1)-(platformWidth(j)+1), the selected minimal period is exactly two, d(N)=F(j)-1, and g(N)=F(j)-platformWidth(j) when F(j) is odd, or F(j)-platformWidth(j)-1 when it is even. Both branches hold without a zero-deficit assumption.

The proof simultaneously carries the zero set and upper cone from the complete literal base rows at orders eight and nine. Every periodic predecessor is an iterate of the same legal cycle. The adjacent physical row determines the boundary depth. Absolute even orbit times lie strictly above the critical lower endpoint and odd times lie at or below it, which fixes the actual selected phase while keeping interval and periodic entry distinct. The split recurrence and orbit legality directly use actual_foundations; Fibonacci parity directly uses GoldenFibDivisibility.fib_dvd_iff at index three.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.Hyp24_1`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.full24_3`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.heightDeficit`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau.platformWidth`
- Dependency: [D5/S1/Recurrence/Invariants/CloitreActualRightProfile](CloitreActualRightProfile.md)
