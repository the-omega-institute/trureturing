# Uniform circles of the finite closed weaving braid

## Abstract

The actual finite closed-braid port quotient has an explicit interval-and-outer-strand classification in either uniform smoothing.

A parameter P consists of integers n at least 2 and m at least 3. There are n generators, indexed from zero, acting at strand positions i and i+1. Crossings in one period occur in increasing generator order. Time is ZMod(m), so the period seam is part of the finite carrier. A dart is (t,i,a), where a is one of tl,tr,bl,br. These are positions outside the crossing disk, irrespective of over-crossing sign.

At position 0 only generator 0 occurs, and at position n only generator n-1 occurs. An internal position j meets generator j-1 on the right and then generator j on the left in each period. Consequently bl(t,0) joins tl(t+1,0); bl(t,i), for i positive, joins tr(t+1,i-1); br(t,i), for i+1 less than n, joins tl(t,i+1); br(t,n-1) joins tr(t+1,n-1). Reverse rules define the same matching on the top inputs.

**Theorem 1.1 (A total external perfect matching).**

$$\forall P \in Parameters,\; Involutive\left(external\left(P\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.external_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

Applying the external matching twice returns every actual dart, including the internal left outputs and both outer seams. The matching is a function, so a port has exactly one external neighbour.

**Theorem 1.2 (No external fixed port).**

$$\forall P \in Parameters,\; \forall x \in Dart\left(P\right),\; external\left(P, x\right) \neq x$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.external_ne_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

Each external arc connects a top input to a bottom output. In particular no arc has a single endpoint port.

Here is the chronological derivation of the external matching. Before cyclic reduction, an occurrence is (q,i), with natural period q and generator 0 <= i < n. Define (q,i) < (s,j) to mean q < s or q=s and i < j. The left output bl has spatial position i, and the right output br has position i+1; a top port tl at generator j has position j, while tr has position j+1. An occurrence at generator j is incident to position a exactly when j=a or j+1=a. Thus at an internal position a, the only incident generators are a-1 and a, in that order in each period; position 0 has only generator 0 and position n only generator n-1.

For br at (q,i) with i+1<n, the next incident occurrence is (q,i+1), entered at tl. Its position is i+1, it is strictly later in the defined order, and no incident occurrence lies strictly between: the only two incident generators are i and i+1, consecutive in this period. For br at i=n-1, position n has only generator i, so its next occurrence is (q+1,i), entered at tr at position i+1=n. No incident occurrence lies between consecutive periods of this sole generator.

For bl at (q,i) with i>0, the next incident occurrence is (q+1,i-1), entered at tr at position (i-1)+1=i. Generator i-1 has already occurred earlier in period q and generator i is the current occurrence. In the next period i-1 precedes i. Hence this successor is strictly later and there is no incident (s,j) with (q,i)<(s,j)<(q+1,i-1). For bl at i=0, position 0 has only generator 0, so the next occurrence is (q+1,0), entered at tl, again with no intervening incident occurrence. These four cases establish a top input at the same spatial position, strict chronological order and the quantified exclusion of every intervening incident occurrence.

Now reduce the natural periods modulo m. Writing t for q in ZMod(m), q+1 becomes t+1. The four successors are precisely the four bottom-output clauses of external above. At q=m-1 this reduction identifies the next period with time zero, including both outer wires and the internal bl wires that cross the closing seam. The top-input clauses reverse these same wires, as external_involutive checks. This derives the positional matching from the repeated braid sequence; crossing signs do not change its wires. The chronological order is on natural occurrences before reduction, with no linear order imposed on cyclic time.

The smoothing parity p is 0 or 1. Cup(p,i) means i mod 2 equals p. Thus p=0 selects printed odd generators and p=1 selects printed even generators. Cup-cap pairs tl with tr and bl with br; vertical pairs tl with bl and tr with br. Reach is the equivalence closure of these local arcs and the external matching. Circle(P,p) is the actual quotient of darts by Reach.

The code of the interval at generator i and time t is (i+1,t). At a cup-cap crossing, both top ports have code (i+1,t-1) and both bottom ports have code (i+1,t). At an internal vertical crossing the left ports have code (i,t) and the right ports code (i+2,t-1). An unpaired left outer strand has code (0,0); an unpaired right outer strand has code (n+1,0). These outer codes occur only when the corresponding boundary generator is vertical.

**Theorem 1.3 (Codes classify the actual connected components).**

$$\forall P \in Parameters,\; \forall p \in Nat,\; p < 2 \Rightarrow \left(\forall x \in Dart\left(P\right),\; \forall y \in Dart\left(P\right),\; Reach\left(P, p, x, y\right) \iff code\left(P, p, x\right) = code\left(P, p, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.reach_iff_code` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

Every generating arc preserves the code. Conversely, a cup-cap top reaches the preceding bottom cap via the intervening vertical crossing, with the left seam handled separately. A vertical left port reaches the preceding generator's bottom cap at the same time; a vertical right port reaches the next generator's bottom cap at time t-1. Local smoothing arcs handle the other ports. Outer vertical strands advance one time step by a local arc followed by an external arc; induction on a natural representative of cyclic time connects each to time zero. Therefore equal codes give actual paths. No enumeration of smoothing states occurs.

**Definition 1.4 (An explicit quotient bijection).**

$$\forall P \in Parameters,\; \forall p \in Nat,\; p < 2 \Rightarrow Equiv\left(Circle\left(P, p\right), Label\left(P, p\right)\right)$$

*Formalization.* `D5/S3/Topology/WeavingDiagramPorts.circleEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

Label is the disjoint union of a paired generator with its cyclic time and a Boolean outer-side label restricted to sides whose boundary crossing is vertical. The quotient map sends a dart to its label; its inverse sends an interval to the bottom-left cap port and an outer side to the time-zero top port. The path theorem proves both inverse identities.

**Theorem 1.5 (Printed odd cup-caps).**

$$\forall P \in Parameters,\; card\left(Circle\left(P, 0\right)\right) = \left(r + d\right) \cdot m\left(P\right) + 1 - d$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.odd_circle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

Put d=n mod 2 and r=(n-d)/2. There are r+d paired generators, each contributing m interval circles, and 1-d unpaired outer strands. The equivalence circleEquiv has inverse taking an interval label to its bottom-left port and an outer label to its time-zero top port.

**Theorem 1.6 (Printed even cup-caps).**

$$\forall P \in Parameters,\; card\left(Circle\left(P, 1\right)\right) = r \cdot m\left(P\right) + 1 + d$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.even_circle_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

There are r paired generators and 1+d unpaired outer strands. The same quotient equivalence applies. These formulas include n=2,m=3 and do not require any coprimality or knot-component condition.

Write C(t,i) for the actual quotient class of (t,i,bl), L for the class of (0,0,tl), and R for the class of (0,n-1,tr). At a cup-cap crossing the crossing edge uses the tl and bl classes; at a vertical crossing it uses the tl and tr classes. These choices select one endpoint from each local smoothing arc.

**Theorem 1.7 (The two interval endpoints).**

$$\forall P \in Parameters,\; \forall p \in Nat,\; p < 2 \Rightarrow \left(\forall t \in ZMod\left(m\left(P\right)\right),\; \forall i \in Fin\left(n\left(P\right)\right),\; cup\left(p, i\right) \Rightarrow edgeEnds\left(P, p, t, i\right) = pair\left(C\left(t - 1, i\right), C\left(t, i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.cup_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

The cup-cap edge joins C(t-1,i) to C(t,i), with subtraction in cyclic time.

**Theorem 1.8 (The internal vertical endpoints).**

$$\forall P \in Parameters,\; \forall p \in Nat,\; p < 2 \Rightarrow \left(\forall t \in ZMod\left(m\left(P\right)\right),\; \forall i \in Fin\left(n\left(P\right)\right),\; \left(\neg cup\left(p, i\right) \land \left(i \neq 0 \land i + 1 < n\left(P\right)\right)\right) \Rightarrow edgeEnds\left(P, p, t, i\right) = pair\left(C\left(t, i - 1\right), C\left(t - 1, i + 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.internal_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

An internal vertical crossing joins the left interval at time t and the right interval at time t-1. Both labels are actually present because adjacent generator parities alternate.

**Theorem 1.9 (The left outer endpoint).**

$$\forall P \in Parameters,\; \forall p \in Nat,\; p < 2 \Rightarrow \left(\forall t \in ZMod\left(m\left(P\right)\right),\; \neg cup\left(p, 0\right) \Rightarrow edgeEnds\left(P, p, t, 0\right) = pair\left(L, C\left(t - 1, 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.left_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

When generator zero is vertical, its left endpoint is the actual unpaired left circle and its right endpoint is the interval at generator one.

**Theorem 1.10 (The right outer endpoint).**

$$\forall P \in Parameters,\; \forall p \in Nat,\; p < 2 \Rightarrow \left(\forall t \in ZMod\left(m\left(P\right)\right),\; \neg cup\left(p, n\left(P\right) - 1\right) \Rightarrow edgeEnds\left(P, p, t, n\left(P\right) - 1\right) = pair\left(C\left(t, n\left(P\right) - 2\right), R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.right_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

When the last generator is vertical, its right endpoint is the actual unpaired right circle and its left endpoint is the preceding interval.

**Theorem 1.11 (Every crossing has distinct circle endpoints).**

$$\forall P \in Parameters,\; \forall p \in Nat,\; p < 2 \Rightarrow \left(\forall t \in ZMod\left(m\left(P\right)\right),\; \forall i \in Fin\left(n\left(P\right)\right),\; fst\left(edgeEnds\left(P, p, t, i\right)\right) \neq snd\left(edgeEnds\left(P, p, t, i\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/WeavingDiagramPorts.edge_endpoints_distinct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Rama Mishra; Hitesh Raundal (2021). *Hecke algebra trace algorithm and some conjectures on weaving knots*. URL: <https://arxiv.org/abs/1908.04152v3>.

*Commentary.*

For a cup-cap crossing, equality would force 1=0 in ZMod(m), which is impossible for m at least 3. For a vertical crossing the interval or outer codes have different first coordinates. This is looplessness at the actual quotient, without deleting loops by definition.

This finite geometry is auxiliary to Mishra and Raundal, Hecke algebra trace algorithm and some conjectures on weaving knots, arXiv:1908.04152v3, Conjecture 5.2. It does not establish that conjecture. The target remains every fixed n at least 2 and k at least 1, for all sufficiently large integer m, including multi-component links: T_k(W(n+1,m))=((r+d)^k+r^k)m^k/k!+O_(n,k)(m^(k-1)). No original-problem or uniqueness claim follows from the circle classification; the scope of the related JIMS publication remains unresolved.

Still required are uniqueness of crossing edge incidences as unordered endpoint pairs, graph connectedness, the actual finite diagram-to-state-sum rank identity for arbitrary smoothing states, connected planar checkerboard realizations and signed planar duality, and transfer to coefficients of the actual normalized integral Jones invariant. The raw Kauffman bracket needs its monomial factor, exponent substitution and writhe normalization before comparison with a signed graph polynomial. The two endpoint magnitudes must each be counted once. Uniform asymptotics require the varying graph family, rather than a fixed graph with a free auxiliary m. Complex Perron paths or Artin traces alone supply none of these geometric and integral coefficient identifications. This module introduces no polynomial under the name Jones and contains no assumed certificate of those unpaid conclusions.

## References

- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.circleEquiv`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.cup_edge`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.edge_endpoints_distinct`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.even_circle_count`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.external_involutive`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.external_ne_self`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.internal_edge`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.left_edge`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.odd_circle_count`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.reach_iff_code`
- Truth anchor: `D5/S3/Topology/WeavingDiagramPorts.right_edge`
