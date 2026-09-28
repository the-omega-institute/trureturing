# Bounded Cuts and Unbounded Three-Leaf Causal Peak

## Abstract

Modular three-leaf promises have uniformly bounded cut costs and unbounded causal-tree peak.

**Definition 1.1 (The modular promise).**

$$\forall m \in \mathbb{N}, D_{m} = \{ (x, y, z) \in \operatorname{ZMod}(m)^{3} \mid z = x + y \}$$

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.World` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural number m, World m is the subtype of triples (x,y,z) in ZMod m with z=x+y. Write D_m for this type. The equality is in the cyclic ring ZMod m. In the theorem m is twice the square of K, with K at least two, so m is positive, D_m is finite and nonempty, and it has m squared elements.

**Definition 1.2 (Legal triples and coordinate observations).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.point`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m and x,y in ZMod m, point x y is the legal triple (x,y,x+y). The functions xcoord, ycoord and zcoord send a legal triple to its first, second and third coordinate. Every pair (x,y) has this unique completion. The pair (x,z) completes as (x,z-x,z), and (y,z) completes as (z-y,y,z). Thus every two-coordinate projection is the full product.

**Definition 1.3 (One-way encoding of a raw-input cut).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.CutAdmits`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.CutAdmits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary types Omega, L and R, a Boolean function f on Omega, observations l:Omega to L and r:Omega to R, and a natural number n, CutAdmits f l r n means that there exist an arbitrary type A, a total encoder e:L to A and a total decoder d:A to R to Bool such that both Nat.card(range(e composed with l)) is at most n and, for every w in Omega, d(e(l(w)),r(w))=f(w). There is no finiteness hypothesis on A. Only messages reached from Omega enter the cardinality. For positive m the promise D_m and these ranges are finite, even when A is infinite.

**Definition 1.4 (Minimum reachable cut cardinality).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.cutCost`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.cutCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the same f,l,r, cutCost f l r is the natural-number infimum sInf of the set of n satisfying CutAdmits f l r n. For the cuts of D_m below, this set is nonempty, so the infimum is an attained natural minimum. Cardinality counts message values, not bits.

Write c_X(m,f) for cutCost f xcoord (ycoord,zcoord), c_Y(m,f) for cutCost f ycoord (xcoord,zcoord), and c_Z(m,f) for cutCost f zcoord (xcoord,ycoord). Here a pair of coordinate maps sends w to the ordered pair of their values. Write c_XY(m,f) for cutCost f (xcoord,ycoord) zcoord, c_XZ(m,f) for cutCost f (xcoord,zcoord) ycoord, and c_YZ(m,f) for cutCost f (ycoord,zcoord) xcoord. Finally c_XYZ(m,f) is cutCost f id (the constant map to Unit). Its encoder sees the entire legal triple and its decoder receives no complementary input.

**Definition 1.5 (A protocol on the fixed tree ((X,Y),Z)).**

$$\begin{gathered}A, B, C, M: \operatorname{Type},\\\alpha: \operatorname{ZMod}(m) \to A, \beta: \operatorname{ZMod}(m) \to B, \gamma: \operatorname{ZMod}(m) \to C,\\\tau: A \to B \to M, \rho: M \to C \to \operatorname{Bool}\end{gathered}$$

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Protocol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each m, Protocol m consists of four arbitrary types A,B,C,M and the five displayed total maps. Each alphabet may be infinite; no Fintype or finite-alphabet assumption is imposed. The leaf maps alpha, beta and gamma each see only their own raw coordinate. The internal map tau receives only alpha(x) and beta(y), and the root map rho receives only that internal message and gamma(z). Correctness will be required only on legal triples.

**Definition 1.6 (The actual internal message).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.internal`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.internal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m, protocol p and w in World m, internal p w is p.tau(p.alpha(xcoord w),p.beta(ycoord w)). Its range is taken over legal worlds w. It counts jointly reachable outputs of the internal node. For this promise every pair (x,y) is legal after completion, so every pair of reachable alpha and beta messages is jointly reachable.

**Definition 1.7 (Correctness on the promise).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Correct`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Correct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m, protocol p and f:World m to Bool, Correct p f means that for every w in World m, p.rho(internal p w,p.gamma(zcoord w))=f(w). The same legal world supplies all three coordinates in this equation.

**Definition 1.8 (The four reachable message cardinalities).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.peak`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.peak` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m and p:Protocol m, peak p is max(max(Nat.card(range p.alpha),Nat.card(range p.beta)), max(Nat.card(range p.gamma),Nat.card(range(internal p)))). The three leaf ranges are over ZMod m; the internal range is over World m. For positive m all four are finite and nonempty. Ambient alphabet cardinalities and unreachable entries of the total maps do not enter this maximum. The final Boolean output is not an additional term in the peak.

**Definition 1.9 (The attained natural optimum).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.peakOpt`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.peakOpt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every m and f:World m to Bool, peakOpt f is sInf of the set of natural numbers n for which there exists p:Protocol m with Correct p f and peak p at most n. This quantifies over all four alphabet types and all five causal maps. When m is positive, a correct protocol exists: let alpha and beta send their raw coordinates, gamma send a constant, tau send the ordered pair, and rho evaluate f at its unique legal completion. Thus the admissible set is nonempty, its natural infimum belongs to it, and a correct protocol attains the optimal peak. Write P_T(m,f) for this number, with T fixed as ((X,Y),Z).

**Definition 1.10 (Finite labels for reachable messages).**

Lean statement: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Tables`

*Formalization.* `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Tables` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Tables m K is the product of three function types ZMod m to Fin K, one function type Fin K to Fin K to Fin K, and one function type Fin K to Fin K to Bool. For a tuple (a,b,c,t,r), evaluate sends w to r(t(a(xcoord w),b(ycoord w)),c(zcoord w)). When K is at least two and m is twice its square, these finite tables represent all protocols of peak at most K after relabeling their reachable images; they do not restrict the alphabet types in the definition of Protocol.

**Theorem 1.11 (Bounded raw-input cuts and unbounded causal peak).**

$$\begin{gathered}\forall K \in \mathbb{N}, 2 \leq K \Rightarrow\\\operatorname{let} m = 2 K^{2}; \exists f: D_{m} \to \operatorname{Bool},\\c_{X}(m, f) = 1 \land c_{Y}(m, f) = 1 \land c_{Z}(m, f) = 1 \land\\c_{XY}(m, f) = 2 \land c_{XZ}(m, f) \leq 2 \land c_{YZ}(m, f) \leq 2 \land\\c_{XYZ}(m, f) = 2 \land K < P_{T}(m, f)\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Separation/ThreeLeafCausalPeak.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural K at least two, set m to twice the square of K. There exists one Boolean function f on this fixed modular promise for which all eight displayed clauses hold simultaneously. The singleton costs are exactly one, the XY cost is exactly two, the XZ and YZ costs are at most two, the full-input cost is exactly two, and the attained optimal causal peak is strictly greater than K.

A protocol of peak at most K can relabel each of its four reachable images inside Fin K. Because every pair of raw X and Y inputs occurs in a legal world, the internal map on any pair of reachable child messages lands in its actual reachable image. Inverse labels and arbitrary values on unused labels extend these maps to a total finite table with the same Boolean output at every legal world.

There are K to the power (3m+K squared), multiplied by 2 to the power K squared, such finite tables, while there are 2 to the power m squared Boolean functions on D_m. For K at least two, K is at most 2 to the power K and 7K+1 is strictly less than four times the square of K. With m twice the square of K, these inequalities make the table count strictly smaller than the number of Boolean functions. Choose a function outside the image of evaluation. Every correct protocol for it then has peak greater than K, and attainment transfers the strict bound to peakOpt.

Each complementary coordinate pair uniquely reconstructs the legal world, so singleton encoders can be constant. Every two-coordinate encoder can reconstruct that world and send f directly as a Boolean. A function depending only on z has a protocol of peak at most two, so the chosen f cannot have that form. A one-message XY encoding would make f depend only on z; hence the XY cost is exactly two. The same function is nonconstant, which makes its full-input cost exactly two.

All six nonempty proper raw-input cuts therefore have cost at most two. These encoders have access to joint raw coordinates on their own side of the cut. On the causal tree the internal node has access only to the two leaf messages produced by the same protocol. Small separate cut costs thus coexist with an unbounded family of optimal causal peaks.

## References

- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Correct`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.CutAdmits`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Protocol`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.Tables`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.World`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.cutCost`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.internal`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.peak`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.peakOpt`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.point`
- Truth anchor: `D5/S3/Observer/Separation/ThreeLeafCausalPeak.result`
