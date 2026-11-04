# The complete local phase chart

## Abstract

Trace-deficit coordinates on four actual unit phases.

**Theorem 1.1 (Local inversion and one common scalar).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathPhaseChart.local_phase_chart`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathPhaseChart.local_phase_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A phase vector has four complex entries of modulus one. Its trace modulus A is the modulus of their sum; B is the modulus of w0-w1+i(w2-w3). The linear amplitudes are P=h(w0+w1)+c(w2+w3) and Q=h(w0-w1)+is(w2-w3). For the original four-path feedback, h=1/sqrt(2), c=cos(pi/8), and s=sin(pi/8). The theorem allows all real h, c and s.

Fix 0<delta0<2 and orientation tau equal to 1 or -1. Put x0=1-delta0/2 and y0=sqrt(1-x0^2). The base vector is (x0+tau*i*y0,x0-tau*i*y0,1,1). Coordinates are p=(delta,a,b,m), where m is one common scalar argument. Set X=-cos(b)cos(a)+sqrt((2-delta/2)^2-cos(b)^2 sin(a)^2) and Y=sqrt(1-X^2). The chart is exp(i*m) times (exp(i*a)(X+tau*i*Y),exp(i*a)(X-tau*i*Y),exp(i*tau*b),exp(-i*tau*b)). Both square roots have positive arguments near the base point.

The inverse uses the actual arguments of all four entries. Its coordinates are delta=4-A, a=(arg(w0)+arg(w1)-arg(w2)-arg(w3))/2, b=tau*(arg(w2)-arg(w3))/2 and m=(arg(w2)+arg(w3))/2. All four base entries have positive real part, so these arguments are real analytic on a neighborhood. The recovered oriented half difference theta=tau*(arg(w0)-arg(w1))/2 lies between zero and pi/2. The trace equation gives X=cos(theta) and Y=sin(theta), proving reconstruction for every nearby unit phase vector.

There are open neighborhoods S of (delta0,0,0,0) and V of the base phase vector. Throughout S, 0<X<1, the argument of the square root defining X is positive, and cos(b)>0. On S the chart has unit entries, A=4-delta, and the displayed inverse recovers p. On V the inverse is analytic, maps every unit phase vector into S, and reconstruction recovers that vector. The chart is analytic on S. After restricting S to the preimage of V, the chart is explicitly bijective from S onto the unit phase vectors in V.

At m=0, substitution gives P=2(h*X*exp(i*a)+c*cos(b)), Q=2*tau*(i*h*Y*exp(i*a)-s*sin(b)), and B=2*abs(i*Y*exp(i*a)-sin(b)). All expressions use the same four entries. If two normalized points of S differ by a common complex scalar, multiplying their last two entries forces the scalar's square to be one. The positive real part of their third entries excludes minus one. The inverse law then identifies all coordinates, and the scalar is one.

Write N(delta,a,b,m)=(delta,a,b,0). There is one open neighborhood W of the base vector, contained in V, on which N composed with the displayed inverse is real analytic. For every unit phase vector w in W, put p=inverse(w). The theorem states that N(p) belongs to S, has fourth coordinate zero and first coordinate exactly 4-A(w), and that w=exp(i*p3)*chart(N(p)), with abs(exp(i*p3))=1. If q is any point of S with q3=0 and w=scalar*chart(q), then q=N(p) and scalar=exp(i*p3). This uniqueness quantifies over every complex scalar, without an extra unit-modulus assumption. Thus every nearby actual phase vector is covered after exactly one common scalar identification, and no relative coordinate is removed. To obtain W, continuity of N composed with the inverse gives an open neighborhood whose normalized coordinates remain in the chosen S; intersect it with V. The scalar factorization follows directly from the chart, and normalized uniqueness identifies any other representation.

The reference feedback is diagonal(1,exp(i*pi/4),exp(i*theta),exp(-i*theta)); the original value is theta=pi/8. The actual feedback U=diagonal(w)*Uplus is unitary, and U*star(Uplus)=diagonal(w). The theorem proves this for every real theta. Every common scalar multiple with scalar modulus one also gives a unitary actual feedback. Multiplication of every entry by that scalar preserves A and B and multiplies P and Q by the scalar. Consequently it also preserves their moduli. The fourth coordinate m records that common scalar locally, while the normalized chart has m=0.

The orientation tau distinguishes the two local phase charts. It is separate from the optimizer sign in the original distance. The phase-coordinate argument places no restriction on the positive effect and does not change its ordinary-transpose convention. Quantitative all-effect isolation, comparison of optimizer signs, and Hessian lower bounds require further estimates.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathPhaseChart.local_phase_chart`
