# Actual Fibonacci Sparse Child Law

## Abstract

The actual sparse phase criterion identifies all signed and actual natural gcd futures; its failure produces fixed signed and bounded natural collisions on the complete query table.

N includes zero. Integer division ediv and natural division ndiv are the corresponding Lean quotient operations. F(0)=0 and F(1)=1. The function r(m) is TimeSampling.zeroRank(m), the natural infimum of the positive Fibonacci zero indices modulo m. The infimum is zero when that set is empty; the proof reuses verified nonemptiness for every positive prime power. Coordinates of x in Z times Z are x_1 and x_2. The value y(k,x) is the actual signed recurrence observation for positive k. All queried observations are positive-time readings. Capped-content divisibility also holds at index zero, without supplying a time-zero reading. ZMod(m) denotes Z/mZ, with ZMod(0)=Z. In formulas involving this ring, integers and natural numbers are coerced into it. In particular A and B take values in ZMod(p); c and f take values in ZMod(p^e). The proof-local inverse of c is the ZMod inverse; the affine calculation proves c is a unit for prime p and e>=2. For a in ZMod(p), val(a) is its canonical natural representative. castZMod(r,n) is the natural coercion into ZMod(r). Finset denotes finite sets of distinct values.

**Definition 1.1 (Reduction of an integer pair).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.castState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.castState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For natural m and x in Z times Z, castState(m,x) reduces each coordinate in ZMod(m).

**Theorem 1.2 (The second Fibonacci coordinate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_second`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_second` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any commutative semiring A, natural t and x in A times A, the second coordinate of step^t(x) equals F(t)x_1+F(t+1)x_2.

**Theorem 1.3 (The first positive Fibonacci coordinate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_first`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_first` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any commutative semiring A, positive natural t and x in A times A, the first coordinate of step^t(x) equals F(t-1)x_1+F(t)x_2.

**Theorem 1.4 (The original natural observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_source_value`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_source_value` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k and natural pair v, quantity(step^k(v)) equals F(k+3)v_1+F(k+4)v_2, including k=0.

**Theorem 1.5 (The positive-time signed representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_signed_quantity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_signed_quantity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural k and natural pair v, the integer cast of quantity(step^k(v)) equals y(k,observe(v)), with both observation coordinates cast to integers.

**Theorem 1.6 (Scaling the same natural observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_quantity_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_quantity_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all natural Q,k and natural pairs v, quantity(step^k(Q v_1,Q v_2)) equals Q times quantity(step^k(v)).

**Theorem 1.7 (Positive prime-power entry ranks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.rank_facts`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.rank_facts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural prime p and natural e>=1, zeroRank(p^e)>=3, p^e divides F(zeroRank(p^e)), and for every natural k, p^e divides F(k) exactly when zeroRank(p^e) divides k.

**Theorem 1.8 (Threshold transport along the rank).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.phase_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.phase_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For prime p, d>=1, natural s,t and integer x, equality of s and t modulo zeroRank(p^d) makes p^d dividing y(s+1,x) equivalent to p^d dividing y(t+1,x).

**Theorem 1.9 (The threshold class of a unit parent hit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.phase_from_unit`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.phase_from_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For prime p, d>=1, natural t,k and integer x, assume the first coordinate of step^t(x) is a unit modulo p^d and y(t+1,x) vanishes there. Then p^d divides y(k+1,x) exactly when k and t agree modulo zeroRank(p^d).

**Definition 1.10 (Positive-time signed observation).**

$$\forall k:\mathbb{N}, (\forall x:\mathbb{Z}\times\mathbb{Z}, (\operatorname{y}\left(k, x\right) = (\operatorname{F}\left(k-1\right)) (x_{1})+(\operatorname{F}\left(k\right)) (x_{2})))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.signedValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtraction on the natural index is truncated. Only positive indices are used by the theorem.

**Definition 1.11 (Prime-local primitive state).**

$$\forall p:\mathbb{N}, (\forall x:\mathbb{Z}\times\mathbb{Z}, ((\operatorname{Primitive}\left(p, x\right)) \Leftrightarrow ((\neg(p \mid x_{1})) \lor (\neg(p \mid x_{2})))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.Primitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At least one signed coordinate is not divisible by p; integer coprimality of the coordinates is not required.

**Definition 1.12 (Complete signed gcd answer).**

$$\forall H:\mathbb{N}, (\forall k:\mathbb{N}, (\forall x:\mathbb{Z}\times\mathbb{Z}, (\operatorname{g}\left(H, k, x\right) = \operatorname{gcd}\left(\operatorname{natAbs}\left(\operatorname{y}\left(k, x\right)\right), H\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.gcdValue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The answer includes the zero signed observation and uses its natural absolute value.

**Definition 1.13 (Actual forward-source gcd answer).**

$$\forall H:\mathbb{N}, (\forall k:\mathbb{N}, (\forall v:\mathbb{N} \times \mathbb{N}, (\operatorname{gActual}\left(H, k, v\right) = \operatorname{gcd}\left(\operatorname{quantity}\left(\operatorname{stepIterate}\left(k, v\right)\right), H\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actualGcd` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The imported step is (a,b) maps to (b,a+b), quantity is 2a+3b, and stepIterate(k,v) is k forward steps. Thus this is the actual qM^k source observation, not an independently chosen list of residues.

**Definition 1.14 (Unknown capped common content).**

$$\forall p:\mathbb{N}, (\forall e:\mathbb{N}, (\forall x:\mathbb{Z}\times\mathbb{Z}, (\operatorname{content}\left(p, e, x\right) = \operatorname{gcd}\left(\operatorname{gcd}\left(\operatorname{natAbs}\left(x_{1}\right), \operatorname{natAbs}\left(x_{2}\right)\right), (p)^{e}\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.cappedContent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The natural capped common divisor includes the zero pair. minGcdTable(P,S,x) denotes the minimum of g(P,k,x) over k in the nonempty S.

**Definition 1.15 (Actual affine root base).**

$$\forall p:\mathbb{N}, (\forall e:\mathbb{N}, (\forall t:\mathbb{N}, (\forall x:\mathbb{Z}\times\mathbb{Z}, (\operatorname{A}\left(p, e, t, x\right) = (\operatorname{natCast}\left(\operatorname{F}\left(\operatorname{r}\left((p)^{e-1}\right)-1\right), \operatorname{ZMod}\left(p\right)\right)) (\operatorname{intCast}\left(\operatorname{ediv}\left(\operatorname{y}\left(t+1, x\right), (p)^{e-1}\right), \operatorname{ZMod}\left(p\right)\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.rootBase` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed quotient is taken before coercion to ZMod(p).

**Definition 1.16 (Actual affine root slope).**

$$\forall p:\mathbb{N}, (\forall e:\mathbb{N}, (\forall t:\mathbb{N}, (\forall x:\mathbb{Z}\times\mathbb{Z}, (\operatorname{B}\left(p, e, t, x\right) = (\operatorname{natCast}\left(\operatorname{ndiv}\left(\operatorname{F}\left(\operatorname{r}\left((p)^{e-1}\right)\right), (p)^{e-1}\right), \operatorname{ZMod}\left(p\right)\right)) (\operatorname{intCast}\left(\operatorname{y}\left(t+2, x\right), \operatorname{ZMod}\left(p\right)\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.rootSlope` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Fibonacci quotient is natural division before coercion to ZMod(p).

**Definition 1.17 (Queried children in a shifted parent phase).**

$$\forall p:\mathbb{N}, (\forall e:\mathbb{N}, (\forall t:\mathbb{N}, (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), (\forall a:\operatorname{ZMod}\left(p\right), ((a \in \operatorname{queryChildren}\left(p, e, t, S\right)) \Leftrightarrow ((\exists j:\mathbb{N}, ((j < p) \land (a = \operatorname{natCast}\left(j\right)))) \land (\exists k:\mathbb{N}, ((k \in S) \land (\operatorname{mod}\left(k-1, \operatorname{r}\left((p)^{e}\right)\right) = \operatorname{mod}\left(t+(\operatorname{val}\left(a\right)) (\operatorname{r}\left((p)^{e-1}\right)), \operatorname{r}\left((p)^{e}\right)\right))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.queryChildren` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A child belongs exactly when some positive-table query has its top residue. The finite image of range(p) supplies all residues for p>0; repeated visits count once. The child formula uses k-1 at the terminal rank.

**Definition 1.18 (Actual terminal phase coverage).**

$$\forall p:\mathbb{N}, (\forall e:\mathbb{N}, (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\operatorname{D}\left(p, e, S\right)) \Leftrightarrow (\operatorname{if}\left(e = 1, \operatorname{if}\left(\operatorname{r}\left(p\right) = p+1, \operatorname{r}\left(p\right)-1, \operatorname{r}\left(p\right)\right) \le \operatorname{card}\left(\operatorname{image}\left(k \mapsto \operatorname{mod}\left(k, \operatorname{r}\left(p\right)\right), S\right)\right), \operatorname{if}\left(\operatorname{r}\left((p)^{e}\right) = \operatorname{r}\left((p)^{e-1}\right), \forall t:\mathbb{N}, ((t < \operatorname{r}\left((p)^{e}\right)) \implies (\exists k:\mathbb{N}, ((k \in S) \land (\operatorname{mod}\left(k-1, \operatorname{r}\left((p)^{e}\right)\right) = t)))), \forall t:\mathbb{N}, ((t < \operatorname{r}\left((p)^{e-1}\right)) \implies (p-1 \le \operatorname{card}\left(\operatorname{queryChildren}\left(p, e, t, S\right)\right)))\right)\right)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.D` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At the first layer, the full-orbit case allows one missing phase, whereas the optional-hit case requires every phase. At a higher stagnant layer every phase is required. At a growth layer each parent requires at least p-1 distinct children. These are conditions on actual phase images, not on the number of query times.

**Definition 1.19 (Same-table positive-future identification).**

$$\forall A:Type, (\forall read:\mathbb{N} \to A \to \mathbb{N}, (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\operatorname{Identifies}\left(read, S\right)) \Leftrightarrow (\forall x:A, (\forall y:A, ((\forall k:\mathbb{N}, ((k \in S) \implies (read\left(k, x\right) = read\left(k, y\right)))) \implies (\forall k:\mathbb{N}, ((0 < k) \implies (read\left(k, x\right) = read\left(k, y\right))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.Identifies` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source type A is a Type, read maps N times A to N, and S is a finite set of natural times. The implication compares the same two fixed sources at every queried time and every positive future time.

**Definition 1.20 (Domain-restricted positive-future identification).**

$$\forall A:Type, (\forall domain:A \to Prop, (\forall read:\mathbb{N} \to A \to \mathbb{N}, (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\operatorname{IdentifiesOn}\left(domain, read, S\right)) \Leftrightarrow (\forall x:A, (\forall y:A, (((domain\left(x\right)) \land (domain\left(y\right))) \implies ((\forall k:\mathbb{N}, ((k \in S) \implies (read\left(k, x\right) = read\left(k, y\right)))) \implies (\forall k:\mathbb{N}, ((0 < k) \implies (read\left(k, x\right) = read\left(k, y\right))))))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.IdentifiesOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Both sources satisfy the same domain predicate; table and future still concern the same fixed pair.

**Theorem 1.21 (Affine child decoding and complete-answer collisions).**

$$(\forall p:\mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies (((\forall e:\mathbb{N}, ((1 \le e) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\forall k:\mathbb{N}, ((k \in S) \implies (0 < k))) \implies ((\neg(\operatorname{D}\left(p, e, S\right))) \implies (\exists x:\mathbb{Z}\times\mathbb{Z}, (\exists y:\mathbb{Z}\times\mathbb{Z}, ((\operatorname{Primitive}\left(p, x\right)) \land ((\operatorname{Primitive}\left(p, y\right)) \land ((\forall k:\mathbb{N}, ((k \in S) \implies (\operatorname{g}\left((p)^{e}, k, x\right) = \operatorname{g}\left((p)^{e}, k, y\right)))) \land (\forall Q:\mathbb{N}, ((0 < Q) \implies (\exists v:\mathbb{N} \times \mathbb{N}, (\exists w:\mathbb{N} \times \mathbb{N}, (((v_{1} < (Q) ((p)^{e})) \land (v_{2} < (Q) ((p)^{e}))) \land (((w_{1} < (Q) ((p)^{e})) \land (w_{2} < (Q) ((p)^{e}))) \land (((\neg(p \mid Q)) \implies (((\neg(p \mid v_{1})) \lor (\neg(p \mid v_{2}))) \land ((\neg(p \mid w_{1})) \lor (\neg(p \mid w_{2}))))) \land ((\forall k:\mathbb{N}, ((0 < k) \implies ((\operatorname{gActual}\left((Q) ((p)^{e}), k, v\right) = (Q) (\operatorname{g}\left((p)^{e}, k, x\right))) \land (\operatorname{gActual}\left((Q) ((p)^{e}), k, w\right) = (Q) (\operatorname{g}\left((p)^{e}, k, y\right)))))) \land ((\forall k:\mathbb{N}, ((k \in S) \implies (\operatorname{gActual}\left((Q) ((p)^{e}), k, v\right) = \operatorname{gActual}\left((Q) ((p)^{e}), k, w\right)))) \land (\forall B:\mathbb{N}, (\exists k:\mathbb{N}, ((B < k) \land ((0 < k) \land ((\neg(k \in S)) \land ((\operatorname{g}\left((p)^{e}, k, x\right) = (p)^{e}) \land ((\operatorname{g}\left((p)^{e}, k, y\right) = (p)^{e-1}) \land ((\operatorname{gActual}\left((Q) ((p)^{e}), k, v\right) = (Q) ((p)^{e})) \land (\operatorname{gActual}\left((Q) ((p)^{e}), k, w\right) = (Q) ((p)^{e-1}))))))))))))))))))))))))))))) \land ((\forall e:\mathbb{N}, ((1 \le e) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\operatorname{Nonempty}\left(S\right)) \implies ((\forall k:\mathbb{N}, ((k \in S) \implies (0 < k))) \implies ((\exists s:\mathbb{N}, (\exists t:\mathbb{N}, ((s \in S) \land ((t \in S) \land (\neg(\operatorname{mod}\left(s, \operatorname{r}\left(p\right)\right) = \operatorname{mod}\left(t, \operatorname{r}\left(p\right)\right))))))) \implies (\forall x:\mathbb{Z}\times\mathbb{Z}, (\operatorname{minGcdTable}\left((p)^{e}, S, x\right) = \operatorname{content}\left(p, e, x\right))))))))) \land ((\forall e:\mathbb{N}, ((2 \le e) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\operatorname{D}\left(p, e, S\right)) \implies (\forall j:\mathbb{N}, (((1 \le j) \land (j < e)) \implies (\forall a:\operatorname{ZMod}\left(\operatorname{r}\left((p)^{j}\right)\right), (\forall b:\operatorname{ZMod}\left(\operatorname{r}\left((p)^{j}\right)\right), (\exists k:\mathbb{N}, ((k \in S) \land (\operatorname{castZMod}\left(\operatorname{r}\left((p)^{j}\right), k-1\right)+a = b))))))))))) \land ((\forall e:\mathbb{N}, ((1 \le e) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\forall k:\mathbb{N}, ((k \in S) \implies (0 < k))) \implies (((\operatorname{D}\left(p, e, S\right)) \Leftrightarrow ((\operatorname{D}\left(p, e, S\right)) \land (\forall j:\mathbb{N}, (((1 \le j) \land (j < e)) \implies (\operatorname{D}\left(p, j, S\right)))))) \land (((\operatorname{D}\left(p, e, S\right)) \Leftrightarrow (\forall x:\mathbb{Z}\times\mathbb{Z}, (\forall y:\mathbb{Z}\times\mathbb{Z}, (((\operatorname{Primitive}\left(p, x\right)) \land (\operatorname{Primitive}\left(p, y\right))) \implies ((\forall k:\mathbb{N}, ((k \in S) \implies (\operatorname{g}\left((p)^{e}, k, x\right) = \operatorname{g}\left((p)^{e}, k, y\right)))) \implies (\forall k:\mathbb{N}, ((0 < k) \implies (\operatorname{g}\left((p)^{e}, k, x\right) = \operatorname{g}\left((p)^{e}, k, y\right))))))))) \land (((\operatorname{D}\left(p, e, S\right)) \Leftrightarrow (\operatorname{Identifies}\left(\operatorname{gcdValue}\left((p)^{e}\right), S\right))) \land (((\operatorname{D}\left(p, e, S\right)) \Leftrightarrow (\operatorname{Identifies}\left(\operatorname{actualGcd}\left((p)^{e}\right), S\right))) \land ((\operatorname{D}\left(p, e, S\right)) \Leftrightarrow (\forall v:\mathbb{N} \times \mathbb{N}, (\forall w:\mathbb{N} \times \mathbb{N}, ((((\neg(p \mid v_{1})) \lor (\neg(p \mid v_{2}))) \land ((\neg(p \mid w_{1})) \lor (\neg(p \mid w_{2})))) \implies ((\forall k:\mathbb{N}, ((k \in S) \implies (\operatorname{gActual}\left((p)^{e}, k, v\right) = \operatorname{gActual}\left((p)^{e}, k, w\right)))) \implies (\forall k:\mathbb{N}, ((0 < k) \implies (\operatorname{gActual}\left((p)^{e}, k, v\right) = \operatorname{gActual}\left((p)^{e}, k, w\right))))))))))))))))) \land ((\forall e:\mathbb{N}, ((1 \le e) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), (((\forall k:\mathbb{N}, ((k \in S) \implies (0 < k))) \land (\neg(\operatorname{D}\left(p, e, S\right)))) \implies (\forall H:\mathbb{N}, (((0 < H) \land (((p)^{e} \mid H) \land (\neg((p)^{e+1} \mid H)))) \implies ((\neg(p \mid \operatorname{div}\left(H, (p)^{e}\right))) \land (\exists v:\mathbb{N} \times \mathbb{N}, (\exists w:\mathbb{N} \times \mathbb{N}, ((v_{1} < H) \land ((v_{2} < H) \land ((w_{1} < H) \land ((w_{2} < H) \land ((\forall k:\mathbb{N}, ((k \in S) \implies (\operatorname{gActual}\left(H, k, v\right) = \operatorname{gActual}\left(H, k, w\right)))) \land (\forall B:\mathbb{N}, (\exists k:\mathbb{N}, ((B < k) \land ((0 < k) \land ((\neg(k \in S)) \land ((\operatorname{gActual}\left(H, k, v\right) = H) \land (\operatorname{gActual}\left(H, k, w\right) = \operatorname{div}\left(H, p\right)))))))))))))))))))))) \land (\forall e:\mathbb{N}, ((1 \le e) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), (((\forall k:\mathbb{N}, ((k \in S) \implies (0 < k))) \land (\operatorname{D}\left(p, e, S\right))) \implies ((\operatorname{Nonempty}\left(S\right)) \land ((\exists s:\mathbb{N}, (\exists t:\mathbb{N}, ((s \in S) \land ((t \in S) \land (\neg(\operatorname{mod}\left(s, \operatorname{r}\left(p\right)\right) = \operatorname{mod}\left(t, \operatorname{r}\left(p\right)\right))))))) \land (\forall x:\mathbb{Z}\times\mathbb{Z}, (\operatorname{minGcdTable}\left((p)^{e}, S, x\right) = \operatorname{content}\left(p, e, x\right)))))))))))))) \land (\forall e:\mathbb{N}, ((2 \le e) \implies (\forall t:\mathbb{N}, (\forall x:\mathbb{Z}\times\mathbb{Z}, (((p)^{e-1} \mid \operatorname{y}\left(t+1, x\right)) \implies (\forall j:\mathbb{N}, (((p)^{e} \mid \operatorname{y}\left(t+1+(j) (\operatorname{r}\left((p)^{e-1}\right)), x\right)) \Leftrightarrow (\operatorname{A}\left(p, e, t, x\right)+(\operatorname{natCast}\left(j, \operatorname{ZMod}\left(p\right)\right)) (\operatorname{B}\left(p, e, t, x\right)) = 0))))))))))) \land ((\forall H:\mathbb{N}, ((0 < H) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), ((\forall k:\mathbb{N}, ((k \in S) \implies (0 < k))) \implies ((\operatorname{Identifies}\left(\operatorname{actualGcd}\left(H\right), S\right)) \Leftrightarrow (\forall p:\mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies (\forall e:\mathbb{N}, (((1 \le e) \land (((p)^{e} \mid H) \land (\neg((p)^{e+1} \mid H)))) \implies (\operatorname{D}\left(p, e, S\right))))))))))) \land ((\forall k:\mathbb{N}, (\forall v:\mathbb{N} \times \mathbb{N}, (\operatorname{gActual}\left(1, k, v\right) = 1))) \land (\forall p:\mathbb{N}, ((\operatorname{Prime}\left(p\right)) \implies (\forall e:\mathbb{N}, ((1 \le e) \implies (\forall S:\operatorname{Finset}\left(\mathbb{N}\right), (((\forall k:\mathbb{N}, ((k \in S) \implies (0 < k))) \land (\operatorname{D}\left(p, e, S\right))) \implies ((\operatorname{Nonempty}\left(S\right)) \land (\forall v:\mathbb{N} \times \mathbb{N}, (\operatorname{minActualGcdTable}\left((p)^{e}, S, v\right) = \operatorname{gcd}\left(\operatorname{gcd}\left(v_{1}, v_{2}\right), (p)^{e}\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.sparse_gcd_sampling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite positive query table failing D, two fixed primitive signed states agree on every complete gcd reading in that table. The states are chosen before Q. For each Q>0, two actual natural sources are then fixed before every late cutoff. Both coordinates are below Qp^e, and every positive-time natural answer is exactly Q times its signed answer, including when p divides Q. Source primitiveness is asserted only when p does not divide Q. The late separating answers are p^e and p^(e-1), and Qp^e and Qp^(e-1). At growth, the actual square-zero Fibonacci block calculation decodes affine child hits; inverse-action kernel states realize the two omitted children. At stagnation an inverse-action state exits permanently at the top precision while retaining the lower supports. The same-table minimum recovers capped content whenever two distinct first-layer phases are queried, including zero and saturation. At precision e>=2, terminal coverage also represents every phase at each precision 1<=j<e, after any simultaneous translation in its rank ring. At every positive precision, D identifies the entire positive-time gcd future of any two signed states and any two actual natural sources from their same-table readings, including zero, saturation, and unknown nonprimitive content. The shared actual affine law gives a mandatory unique child hit whenever the slope is nonzero, including p=2. A complement of at most one child forces the two roots to agree, and phase transport handles arbitrary positive query times and parent wrap. Equal lower-precision future readings determine whether the two slopes vanish. In the zero-slope case, one queried child determines the constant affine hit condition. The actual C coordinates and frozen whole-time source transport transfer the signed result to natural sources. For every exact local factor p^e || H, failure of D yields a p-unit quotient H/p^e and bounded actual sources whose complete H-table agrees before a late H versus H/p separation. For every H>0, the same positive table identifies all actual natural futures exactly when D holds at every complete prime-power factor of H. The proof projects each full gcd answer to its local gcd, then recombines the nonzero gcd readings by unique factorization; raw observations need not be nonzero. At H=1 every reading is one, including zero sources and time zero, and the empty table identifies all positive futures. The terminal condition itself gives a nonempty S with two distinct first-layer phases, and its local minimum recovers capped common content on that same S. The terminal condition, its conjunction with every lower-level condition, primitive signed identification, all signed identification, all actual-natural identification, and primitive actual-natural identification are equivalent on the same positive S. For every prime p, e>=2, signed x and natural parent t, divisibility of y(t+1,x) by p^(e-1) implies that the top hit at t+1+j r(p^(e-1)) is equivalent to A(p,e,t,x)+j B(p,e,t,x)=0 in ZMod(p), for every natural j. This native normalized affine law is shared by the sufficiency and fixed-collision proofs. On every sufficient positive table, the minimum of actual-natural local readings equals gcd(gcd(v_1,v_2),p^e), by the same signed minimum and the frozen gcd-preserving C observation. This includes zero sources and saturation. minActualGcdTable(P,S,v) denotes the numerical minimum of gActual(P,k,v) over nonempty S. This closed unit asserts the sparse criterion, fixed collisions, affine decoding and local content recovery; sharp horizon, query cardinality, common exponent, global content meet and phase-carry formulas are outside this theorem.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.D`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.Identifies`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.IdentifiesOn`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.Primitive`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actualGcd`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_quantity_scaling`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_signed_quantity`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.actual_source_value`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.cappedContent`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.castState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.gcdValue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_first`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.iterate_second`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.phase_from_unit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.phase_transport`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.queryChildren`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.rank_facts`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.rootBase`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.rootSlope`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.signedValue`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.sparse_gcd_sampling`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GraftAffineClosure](GraftAffineClosure.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/PrimePhaseGcdSampling](PrimePhaseGcdSampling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/PrimePowerGcdHorizon](PrimePowerGcdHorizon.md)
