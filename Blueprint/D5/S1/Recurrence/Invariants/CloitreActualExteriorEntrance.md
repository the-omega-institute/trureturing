# Actual Cloitre Exterior Entrance

## Abstract

Under the complete conditional source foundations, the actual Cloitre orbit has a least even exterior entrance, strict joint clocks and distinct physical rows with macroscopic natural caps.

F is Nat.fib, with F(0)=0 and F(1)=1. C, D, T, X, d and g are the unchanged actual finite-prefix construction in CloitreActualRightProfile. C(1)=C(2)=1, D(N)=[1,N-1], T(N,x)=N-C(x), X(N,i)=T(N)^i(N-1), d(N)=C(N-1), g(N)=X(N,d(N)), and C(N)=C(g(N))+C(N-g(N)) for N>=3. The theorem uses precisely this orbit, depth and selected realization. G(n)=floor(alpha*(n+1)), with alpha=1/goldenRatio=(sqrt(5)-1)/2. On 0<=t<=F(j-2), Q(j,t) is the existing heightDeficit(j,t)=F(j-1)-C(F(j)-t). In displays, Hyp31 and Hyp24 abbreviate Hyp31_1 and Hyp24_1. periodic(T(N),x) means membership in Function.periodicPts(T(N)).

**Definition 1.1 (Literal quadratic cap coefficient).**

$$\begin{aligned}\operatorname {P}\left(9\right) = 13\\\forall j, (10 \le j) \implies (\operatorname {P}\left(j\right) = \lfloor \frac {(j - 2)^{2}}{3} \rfloor  + 30 - 3 \cdot j)\\\forall j, (9 \le j) \implies (\operatorname {L}\left(j\right) = \lfloor \frac {2 \cdot j}{3} \rfloor  - 3)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.capBudget` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P(j) denotes capBudget(j). At j=9 the value is 13. For j>=10, the natural implementation adds 30 before subtracting 3*j; it gives P(10)=21 and P(11)=24. The coefficient is used as P=P(k-1), not P(k). The source is Recursive descent C.1 at nested-recurrences commit d9dbad876c0d3c7b46b692241569fcdf36594344.

**Definition 1.2 (Complete inherited conditional foundations).**

$$(\operatorname {Hyp24}\left(U\right)) \land (\forall j, \forall t, ((9 \le j) \land (0 \le t) \land (t \le \operatorname {F}\left(j - 2\right))) \implies ((0 < \operatorname {Q}\left(j, t\right)) \implies (t \le \operatorname {P}\left(j\right) \cdot \operatorname {Q}\left(j, t\right)))) \land (\forall j, \forall t, ((8 \le j) \land (0 \le t) \land (t \le \operatorname {F}\left(j - 2\right))) \implies ((0 \le \operatorname {Q}\left(j, t\right)) \land (\operatorname {Q}\left(j, t\right) \le \lfloor \frac {2 \cdot t}{3} \rfloor )))$$

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.Hyp31_1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hyp31_1(U) extends the entire Hyp24_1(U), including Hyp21_1(U) and SourceFoundations. The ratio seed covers 16384<=n<=131071 with 22877*C(n)<=15225*n. The golden base covers 1<=n<=65535: G(n)<=C(n), and C(n)=G(n) implies n=F(j) or F(j)+1 for j>=2, n+1=F(j) for odd j>=3, or n in {11,24,25,59}. The small-depth premise covers 3<=N<=52. All these foundations remain ASSUMED-UNVERIFIED premises; this theorem proves no inhabitant of the premise bundle. Global positive-index bounds are 1<=C(n) and G(n)<=C(n)<=U(n)<=n. U(1)=1, and U(n)=min(n-F(j-2),F(j)) for j>=3 and F(j)<=n<F(j+1). U is nondecreasing on positive indices and U(n)<=U(n+1)<=U(n)+1. For j>=2, U(F(j))=C(F(j))=G(F(j))=F(j-1); for j>=3, C(F(j)+1)=G(F(j)+1)=F(j-1)+1. For q>=6 and every natural t, the positive collar [F(q-1),F(q-1)+t] is legal, invariant, captures every legal start, and contains every legal periodic point. For every N>=3, DepthEntry(N) supplies the least periodic-entry index mu<=d(N). Hyp24_1 additionally retains C(F(j)-1)=F(j-1) for j>=5; for j>=6 and b<=F(j-1), negative interval invariance and capture in [F(j)-b,F(j)] intersect D(F(j+1)-b); and the complete periodic intersection max(F(j-1),F(j)-b)<=x<=min(F(j),F(j)+F(j-3)-b). The only extensions are the positive-height envelope for j>=9 and the anchor descent bound for j>=8, both on the natural closed block. The latter is the source Fibonacci collars (1.1) condition. The full zero platform Q(j,t)=0 iff t<=platformWidth(j), for j>=8, is reused from full24_3. For j>=9, L(j)=floor(2*j/3)-3 equals platformWidth(j); the proof applies t<=L(j)+P(j)*Q(j,t) internally and checks L(j)+2<=P(j) for all j>=9 to establish L(j)<=P(j) and the positive analytic denominators. No monotonicity of C, extra finite shelf, free comparison orbit or desired clock property is an added premise. The full cited quantitative capture budget of section 23.1 and anchor logarithmic theorem of section 24.6 are not new Lean conclusions here; this proof uses the inherited negativeCapture interface and its own uniform actual-prefix induction.

**Definition 1.3 (Cap of the unique natural Fibonacci block).**

$$\forall y, (1 \le y) \implies (\operatorname {cap}\left(y\right) = \operatorname {F}\left(\operatorname {greatestFib}\left(y\right)\right) - \operatorname {C}\left(y\right))$$

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.naturalCap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every y>=1, j=Nat.greatestFib(y)>=2 uniquely satisfies F(j)<=y<F(j+1). The cap is F(j)-C(y). It differs from the canonical golden defect C(y)-G(y). At a Fibonacci anchor F(j), it is not Q(j,0). The equality with Q(k,F(k)-y) below applies to the actual counted nonanchor rows, whose natural block index is k-1.

**Definition 1.4 (Complete original target proposition).**

Lean statement: `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.full31_3_statement`

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.full31_3_statement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This proposition fixes every quantifier and signed terminal coordinate of (31.5)-(31.8). It includes actual row injectivity and the cardinality of the image of Finset.Ico(1,R). Its analytic inequalities use real casts, including F(k-5)>=N/13 with real division. The following theorem proves the whole proposition.

**Theorem 1.5 (Least actual exterior entrance, joint clock and physical rows).**

$$\forall U, (\operatorname {Hyp31}\left(U\right)) \implies (\forall k, \forall v, ((23 \le k) \land (0 \le v) \land (v \le \lfloor \frac {\operatorname {F}\left(k - 4\right)}{2} \rfloor )) \implies (\exists R, \theta , \mu : \mathbb {N}, (\begin{aligned}N = \operatorname {F}\left(k\right) - v\\A = \operatorname {F}\left(k - 1\right)\\B = \operatorname {F}\left(k - 2\right)\\J = \operatorname {F}\left(k - 4\right)\\\sigma  = \operatorname {Q}\left(k, v + 1\right)\\P = \operatorname {P}\left(k - 1\right)\\L = \operatorname {L}\left(k - 1\right)\\\alpha  = \frac {\sqrt {5} - 1}{2}\\q = \frac {P}{\alpha }\\\gamma  = \frac {L + (P - 1) \cdot v + 1}{\alpha }\\\beta  = \frac {\operatorname {log}\left(1 + \frac {(P - \alpha ) \cdot (J - v)}{L + (P - 1) \cdot v + 1}\right)}{\operatorname {log}\left(\frac {P}{\alpha }\right)}\\\forall r, \operatorname {a}\left(r\right) = \operatorname {X}\left(N, 2 \cdot r\right) - A\\\forall r, ((1 \le r) \land (r < R)) \implies (\operatorname {b}\left(r\right) = A - \operatorname {X}\left(N, 2 \cdot r + 1\right))\end{aligned}) \land ((2 \le R) \land (\theta  = 2 \cdot R) \land (A - v \le \operatorname {X}\left(N, \theta \right)) \land (\operatorname {X}\left(N, \theta \right) \le A) \land (\forall i, (i < \theta ) \implies (\neg ((A - v \le \operatorname {X}\left(N, i\right)) \land (\operatorname {X}\left(N, i\right) \le A)))) \land (\operatorname {periodic}\left(\operatorname {T}\left(N\right), \operatorname {X}\left(N, \mu \right)\right)) \land (\forall i, (i < \mu ) \implies (\neg \operatorname {periodic}\left(\operatorname {T}\left(N\right), \operatorname {X}\left(N, i\right)\right))) \land (\theta  \le \mu ) \land (\mu  \le \operatorname {d}\left(N\right)) \land (\beta  < R - 1) \land (2 + 2 \cdot \beta  < \theta )) \land ((\operatorname {d}\left(N\right) = A - \sigma ) \land (0 \le \sigma ) \land (\sigma  \le v) \land (v + 1 \le B) \land (v - \sigma  \le J) \land (\operatorname {X}\left(N, 1\right) = B - v + \sigma ) \land (\operatorname {X}\left(N, 2\right) = A + \operatorname {a}\left(1\right)) \land (\operatorname {a}\left(1\right) = J - v + \operatorname {Q}\left(k - 2, v - \sigma \right)) \land (J - v \le \operatorname {a}\left(1\right)) \land (\operatorname {a}\left(1\right) \le J)) \land (\forall r, ((1 \le r) \land (r < R)) \implies ((1 \le \operatorname {a}\left(r\right)) \land (\operatorname {a}\left(r\right) \le J) \land (\operatorname {b}\left(r\right) = v + \operatorname {iota}\left(\operatorname {a}\left(r\right)\right)) \land (\operatorname {iota}\left(\operatorname {a}\left(r\right)\right) = \operatorname {C}\left(A + \operatorname {a}\left(r\right)\right) - B) \land (v < \operatorname {b}\left(r\right)) \land (\operatorname {b}\left(r\right) \le v + J) \land (v + J \le \operatorname {F}\left(k - 3\right)) \land (\operatorname {X}\left(N, 2 \cdot r + 1\right) = A - \operatorname {b}\left(r\right)) \land (\operatorname {a}\left(r + 1\right) = \operatorname {Q}\left(k - 1, \operatorname {b}\left(r\right)\right) - v) \land (3 \cdot \operatorname {a}\left(r + 1\right) \le 2 \cdot \operatorname {a}\left(r\right) - v) \land (\operatorname {a}\left(r\right) < q \cdot \operatorname {a}\left(r + 1\right) + \gamma ))) \land ((0 - v \le \operatorname {a}\left(R\right)) \land (\operatorname {a}\left(R\right) \le 0) \land (\forall r, ((1 \le r) \land (r < R - 1)) \implies (v < \operatorname {Q}\left(k - 1, \operatorname {b}\left(r\right)\right))) \land (\operatorname {Q}\left(k - 1, \operatorname {b}\left(R - 1\right)\right) \le v) \land (v < \operatorname {b}\left(R - 1\right)) \land (\operatorname {b}\left(R - 1\right) \le L + P \cdot v) \land (\operatorname {a}\left(R - 1\right) < \gamma ) \land (rzero = A - \operatorname {X}\left(N, \theta \right)) \land (rzero = v - \operatorname {Q}\left(k - 1, \operatorname {b}\left(R - 1\right)\right)) \land (0 \le rzero) \land (rzero \le v)) \land ((Y = \{ \operatorname {X}\left(N, 2 \cdot r\right) \mid (1 \le r) \land (r < R) \}) \land (\forall r, \forall s, (((1 \le r) \land (r < R)) \land ((1 \le s) \land (s < R)) \land (r < s)) \implies (\operatorname {a}\left(s\right) < \operatorname {a}\left(r\right))) \land (\forall r, \forall s, (((1 \le r) \land (r < R)) \land ((1 \le s) \land (s < R)) \land (\operatorname {X}\left(N, 2 \cdot r\right) = \operatorname {X}\left(N, 2 \cdot s\right))) \implies (r = s)) \land (\lvert Y \rvert  = R - 1) \land (\forall r, ((1 \le r) \land (r < R)) \implies ((\forall j, (2 \le j) \implies (\operatorname {X}\left(N, 2 \cdot r\right) \neq \operatorname {F}\left(j\right))) \land (A < \operatorname {X}\left(N, 2 \cdot r\right)) \land (\operatorname {X}\left(N, 2 \cdot r\right) \le A + J) \land (A + J < N - 1) \land (N - 1 < N) \land (\operatorname {cap}\left(\operatorname {X}\left(N, 2 \cdot r\right)\right) = \operatorname {Q}\left(k, \operatorname {F}\left(k\right) - \operatorname {X}\left(N, 2 \cdot r\right)\right)) \land (\operatorname {F}\left(k - 5\right) \le \operatorname {cap}\left(\operatorname {X}\left(N, 2 \cdot r\right)\right)) \land (\frac {N}{13} \le \operatorname {F}\left(k - 5\right)) \land (2 \cdot r < \operatorname {d}\left(N\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.full31_3` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every U:N->N, natural k>=23 and v<=floor(F(k-4)/2), use the displayed N,A,B,J,sigma,P,L,q,gamma,beta. All arithmetic defining P and L is natural floor arithmetic; alpha,q,gamma,beta and the clock inequalities are real. R, theta and mu are natural; rzero denotes the actual entrance gap. Every a(r) is the signed integer X(N,2*r)-A, including a(R). For 1<=r<R it is positive and equals its natural conversion, so iota(a(r))=C(A+a(r))-B is legal. Every b(r)=A-X(N,2*r+1) is an exact nonnegative subtraction on the proved left-side range, and b(r)<=F(k-3) is the closed domain of Q(k-1).

Theta is the first interval-entry time, with membership and exclusion at every earlier index. Mu is separately the least periodic-entry time, with its own leastness condition. The theorem proves theta=2*R, R>=2, and theta<=mu<=d(N). The depth is exactly A-sigma. For v=0 and v=1 the existing zero platform gives sigma=0; the first-pair computation and its domains also cover the maximal allowed v.

For every 1<=r<R the same two actual rows satisfy the signed recurrence, contraction and strict reverse affine inequality. All positive a(r) strictly decrease. For 1<=r<R-1 the next deficit exceeds v; at r=R-1 it is at most v, the odd gap is bounded by L+P*v, and a(R-1)<gamma. The actual entrance gap r0=A-X(N,theta)=v-Q(k-1,b(R-1)) lies in [0,v]. At R=2, the earlier stopping range is empty and the last pair is r=1.

Y is the image of 1<=r<R under the actual map r->X(N,2*r). That map is injective on this interval, so card(Y)=R-1. Every y is nonanchor and A<y<=A+J<N-1<N. Its natural cap equals Q(k,F(k)-y), and is at least F(k-5), which is at least N/13 over the reals. The same R satisfies R-1>beta and theta>2+2*beta, and each input is used at absolute time 2*r<d(N).

The proof transports a joint invariant along the actual inner orbit, excludes odd first entry, and reverses exactly R-1 strict affine inequalities from a(R)<=0. The logarithmic bound, signed stopping pair and distinct row count share those witnesses. This is a conditional theorem about natural caps on these physical rows. It gives no canonical-defect, inner-period, or unrestricted algorithm or information lower bound, and makes no equality claim theta=mu.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.Hyp31_1`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.capBudget`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.full31_3`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.full31_3_statement`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreActualExteriorEntrance.naturalCap`
- Dependency: [D5/S1/Recurrence/Invariants/CloitreActualLeftPlateau](CloitreActualLeftPlateau.md)
