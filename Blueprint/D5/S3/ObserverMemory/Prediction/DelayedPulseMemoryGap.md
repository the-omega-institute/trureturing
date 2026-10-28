# Delayed Pulse Memory Gap

## Abstract

Delayed pulses have exact static and all-time finite-memory minima.

Let m and H be natural numbers. The source state n advances to n+1, and its real output o_m(n) is one when n=m and zero otherwise. Let 0 <= epsilon < 1/2. All correctness conditions quantify over every initial n, and times include zero.

## Static packing and supplied-center covers

For a finite alphabet A and natural H, let W={w:List(A) | length(w)<=H}. The empty word belongs to W, even if A is empty. Mathlib List.finite_length_le supplies finiteness. Use the finite product metric on Y^W, which is exactly the maximum coordinate distance, and define B(x)(w)=o(ControlledBehaviorUniversality.runWord(F,w,x)). No finiteness of X or Y is assumed.

A static encoder e:X->C and decoder D:C->W->Y with d_Y(D(e(x))(w),B(x)(w))<=epsilon give a cover of B[X] by the range of D. The equivalence dist_pi_le_iff' applies because W contains the empty word, so it needs no separately assumed sign of epsilon. If X is inhabited, the error at any input and the empty word implies epsilon>=0. If X is empty, every finite E subset X is empty and the lower bound is vacuous.

Let E be a finite subset of X whose distinct elements have dist(B(x),B(y))>2 epsilon. When X is inhabited, put r=(epsilon,proof of nonnegativity) in the nonnegative reals. B is injective on E, and B[E] is 2r-separated. The existing Mathlib declarations Metric.IsSeparated.encard_le_packingNumber, Metric.packingNumber_two_mul_le_externalCoveringNumber, and Metric.IsCover.externalCoveringNumber_le_encard give |E|=encard(B[E]) <= packingNumber(2r,B[X]) <= externalCoveringNumber(r,B[X]) <= encard(range D) <= encard(C). Here encard takes values in the extended natural numbers, so infinite C remains in scope.

The particular encoder restricted to E is also injective: if e(x)=e(y), dist_pi_le_iff' turns the two coordinate error bounds into product-distance bounds from B(x) and B(y) to the same response D(e(x)); the triangle inequality yields dist(B(x),B(y))<=2 epsilon, contradicting separation. Thus x maps to e(x) as an embedding of the finite subtype E into arbitrary C. Cardinal.mk_le_of_injective expresses its cardinal bound, and Fintype.card_le_of_injective gives the finite-C consequence. Neither the argument nor the cardinal statement assumes a finite label carrier.

Conversely, suppose actual centers c:Fin(s)->(W->Y) satisfy, for every x, existence of i with dist(B(x),c(i))<=epsilon. Choose such an i for e(x), and set D(i)(w)=c(i)(w). The estimate dist_le_pi_dist at w, followed by the chosen covering bound and symmetry, proves the original coordinate error. These are the supplied centers, including any repeated centers, and s is their label budget; surjectivity of e is unnecessary. Classical choice asserts existence of e, not effective computation.

The covering construction includes s=0: the covering premise then forces X empty and the encoder is the empty function. If Y is empty, existence of o forces X empty, while the nonempty coordinate set W forces s=0 whenever the supplied center family exists. Negative epsilon is permitted on a vacuous input domain. There is no extra positivity or nonemptiness premise, and no transition-consistency premise. For nonempty X and negative epsilon, neither a static error guarantee nor a center-cover guarantee can hold.

**Theorem 1.1 (Exact static and all-time memory minima).**

$$\begin{gathered}\forall m,H\in\mathbb{N}, \forall \varepsilon\in\mathbb{R}, 0\leq\varepsilon<\frac{1}{2}\Rightarrow\\\operatorname{StaticCorrect}(m, H, \varepsilon, \operatorname{staticEncode}(m, H), \operatorname{staticDecode}(m, H))\land\\\operatorname{IsLeast}(\operatorname{staticSizes}(m, H, \varepsilon), \operatorname{min}(H, m)+2)\land\\\operatorname{UpdaterCorrect}(m, \varepsilon, \operatorname{machineEncode}(m), \operatorname{machineUpdate}(m), \operatorname{machineReadout}(m))\land\\\operatorname{IsLeast}(\operatorname{updaterSizes}(m, \varepsilon), m+2)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap.delayed_pulse_memory_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

StaticCorrect(m,H,epsilon,e,D) means that |D(e(n),t)-o_m(n+t)| <= epsilon for every n and every t <= H. The set staticSizes consists of card(C) for finite types C admitting such an encoder e and decoder D. There is no requirement to update a static label.

Write K=min(H,m). The attaining carrier is Fin(K+2). The encoder stores m-n when n <= m and m-n <= H; otherwise it stores K+1. The decoder outputs one precisely when its label equals t and t <= K. This reproduces every window response exactly.

For each j from zero through K, the initial state m-j produces a pulse at window time j. The initial state m+1 gives the silent response. Any two of these K+2 responses differ by one at a window time, so their labels cannot coincide: a shared real prediction would force 1 <= 2 epsilon. Injectivity gives the lower bound.

UpdaterCorrect(m,epsilon,e,U,r) means that |r(U^[t](e(n)))-o_m(n+t)| <= epsilon for every n and every natural time t. The set updaterSizes consists of card(Q) for finite types Q admitting one fixed encoder, update and readout satisfying this condition.

The attaining carrier is Fin(m+2). Encode n as min(n,m+1), update q to min(q+1,m+1), and output one exactly at state m. The state m+1 is absorbing. Induction gives the exact invariant U^[t](e(n))=min(n+t,m+1), hence exact outputs at every time.

For any initial states i<j among zero through m+1, continue for m-i steps. The output from i is one and the output from j is zero. If their encodings agreed, the updater would give the same prediction at this time, again contradicting epsilon < 1/2. Thus all m+2 encodings must be distinct.

Both minima include m=0 and epsilon=0; the static result also includes H=0. Keeping H fixed and increasing m makes the difference between the two minimum counts arbitrarily large.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/DelayedPulseMemoryGap.delayed_pulse_memory_gap`
