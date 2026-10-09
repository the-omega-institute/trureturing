# Sharp Entrance Ratios on Entire Actual Geometry Fibers

## Abstract

Entire same-word geometry fibers include every ordered shape and every pure substitution entrance.

T is FreeMagma Bool. True is alpha and false is beta. Pairing retains both children in order. The substitution rho sends alpha to beta, beta to (beta,alpha), and a pair to the pair of substituted children. The word wd(t) lists every leaf of t from left to right. G is the five-coordinate endpoint, signed area and two centered moments of that same word, with unit steps (1,0) and (0,1). Its codomain Five is the original real coordinate structure; no separate coordinate representatives are chosen.

**Definition 1.1 (Whole word fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.WordFiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.WordFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

WordFiber(g) is the subtype of all nonempty Boolean lists w with G(w)=g.

**Definition 1.2 (Whole ordered tree fiber).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.TreeFiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.TreeFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

TreeFiber(g) is the subtype of all actual trees t:T with G(wd(t))=g. Every ordered shape is included.

**Definition 1.3 (All pure entrances).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.EntranceFiber`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.EntranceFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

EntranceFiber(g) consists of all triples (y,x,k):T times T times Nat with G(wd(y))=g and rho^k(x)=y. All natural k are permitted.

**Definition 1.4 (Actual leaf number).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.N`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(g) is the natural floor of g.u+g.v. On any nonempty actual fiber it equals the positive word and tree length.

**Definition 1.5 (Forward geometry).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.L`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.L` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(u,v,d,e,f)=(v,u+v,-d-v,v-f,-v-3d-e-f).

**Definition 1.6 (Inverse candidate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.Linv`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.Linv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Linv(u,v,d,e,f)=(v-u,u,-d-u,u+3d+e-f,u-e). This is an inverse on the ambient coordinates; membership still requires an actual word or tree.

**Definition 1.7 (Letter substitution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.letter`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.letter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

letter(true)=[false], and letter(false)=[false,true].

**Definition 1.8 (Actual word substitution).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.sigma`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sigma(w) is the concatenation of letter(c) for every letter occurrence c of w, in order.

**Definition 1.9 (Word cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.m`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.m` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

m(g)=Nat.card(WordFiber(g)). The actual word carrier is proved finite before this definition.

**Definition 1.10 (Tree cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.M`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M(g)=Nat.card(TreeFiber(g)). The actual ordered tree carrier is proved finite before this definition.

**Definition 1.11 (Entrance cardinality).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.H`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H(g)=Nat.card(EntranceFiber(g)). Finiteness follows from a proved cutoff k<2N(g) for every legal entrance, together with finite current trees and finite possible source trees.

**Definition 1.12 (Pure-word geometry).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.pure`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.pure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pure(true,n)=(n,0,0,0,0), and pure(false,n)=(0,n,0,0,0). These are exactly the geometries of the corresponding repeated-letter words.

**Definition 1.13 (Sharp bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.B`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B(n) is three at n=2, five halves at n=3, and two otherwise. In particular B(1)=2 and B(n)=2 for n>=4.

**Definition 1.14 (Two-leaf maximizer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.ba`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.ba` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ba=(1,1,-1,1,-1) is the exact geometry of [false,true].

**Definition 1.15 (Three-leaf maximizer).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.bab`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.bab` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

bab=(1,2,0,2,2) is the exact geometry of [false,true,false].

**Definition 1.16 (Prefix odd moment).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.prefixMoment`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.prefixMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

prefixMoment([])=0 and prefixMoment(a::l)=a+prefixMoment(l)+2 sum(l). For the reverse of the original descending rows, it is the sum of (2j-1)x(j) over the same word's ascending prefix counts.

**Definition 1.17 (Same-word arithmetic guards).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.SourceGuards`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.SourceGuards` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SourceGuards(g) asserts one actual nonempty word w in WordFiber(g) and natural numbers k,q,t. They are, respectively, the sum of its original rows, the sum of the squared rows, and prefixMoment of the reverse rows. It includes k<=count(true,w) count(false,w), N(g)>0, g.u=count(true,w), g.v=count(false,w), and simultaneous integer d,e,f representing g.d,g.e,g.f. It also includes (g.d+g.u g.v)/2=k, (g.e+6g.u k-g.u^2 g.v)/6=q, and (g.f+6g.v k+g.u g.v^2)/6=t. Thus endpoints and all joint-moment guards belong to the same word, including pure words.

**Definition 1.18 (Whole-fiber maximizer at every size).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.upper`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

upper(n)=ba at n=2, bab at n=3, and pure(false,n) otherwise.

**Theorem 1.19 (Actual Count Factorization and Recursion).**

$$\forall g: \operatorname{Five}\left(\right), (((0 < \operatorname{N}\left(g\right)) \implies (\operatorname{M}\left(g\right) = \operatorname{Cat}\left(\operatorname{N}\left(g\right) - 1\right) \cdot \operatorname{m}\left(g\right))) \land (\operatorname{H}\left(g\right) = \operatorname{M}\left(g\right) + \operatorname{H}\left(\operatorname{Linv}\left(g\right)\right)) \land (\operatorname{m}\left(\operatorname{Linv}\left(g\right)\right) \leq \operatorname{m}\left(g\right)) \land (\operatorname{M}\left(g\right) \leq \operatorname{H}\left(g\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.actual_fiber_counting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real candidate g, positive N gives the full ordered-shape factor Cat(N-1) times the whole word count. Independently of candidate validity, the all-entrance count splits into depth zero and the inverse candidate's all-entrance count. Applying sigma injects that inverse candidate's whole word fiber into the current one. Empty carriers contribute zero.

**Theorem 1.20 (Uniform Bounds on Entire Actual Fibers).**

$$\forall g: \operatorname{Five}\left(\right), ((\operatorname{M}\left(g\right) \leq \operatorname{H}\left(g\right)) \land ((\operatorname{N}\left(g\right) = 1) \implies (\operatorname{H}\left(g\right) \leq 2 \cdot \operatorname{M}\left(g\right))) \land ((\operatorname{N}\left(g\right) = 2) \implies (\operatorname{H}\left(g\right) \leq 3 \cdot \operatorname{M}\left(g\right))) \land ((\operatorname{N}\left(g\right) = 3) \implies (2 \cdot \operatorname{H}\left(g\right) \leq 5 \cdot \operatorname{M}\left(g\right))) \land ((4 \leq \operatorname{N}\left(g\right)) \implies (\operatorname{H}\left(g\right) \leq 2 \cdot \operatorname{M}\left(g\right))) \land (\operatorname{H}\left(g\right) \leq 3 \cdot \operatorname{M}\left(g\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.uniform_actual_entrance_estimate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inequalities hold for all real candidates, hence for every nonempty actual geometry fiber. At one leaf the factor is two; at two leaves it is three; at three leaves the integer inequality 2H<=5M gives factor five halves; from four leaves onward the factor is two. The common factor three and the lower bound are included. These statements count all trees and all pure entrances; they impose no probability law on physical sources.

The induction uses literal entrance recursion and injection of actual whole word fibers. A pure beta fiber has the same leaf count as its pure alpha inverse and has twice its tree count in entrances. Every other nonempty inverse has fewer leaves. The two distinct endpoint terms of the nonnegative Catalan recurrence show that adjacent positive indices at least double, leaving only the one-, two- and three-leaf inverse cases for direct arithmetic comparison.

**Theorem 1.21 (Complete Sharp Ratios and Full-Fiber Attainment).**

$$(\forall g: \operatorname{Five}\left(\right), ((\operatorname{Nonempty}\left(\operatorname{TreeFiber}\left(g\right)\right)) \implies ((\operatorname{SourceGuards}\left(g\right)) \land (0 < \operatorname{N}\left(g\right)) \land (0 < \operatorname{M}\left(g\right)) \land (1 \leq \frac{\operatorname{H}\left(g\right)}{\operatorname{M}\left(g\right)}) \land (\frac{\operatorname{H}\left(g\right)}{\operatorname{M}\left(g\right)} \leq \operatorname{B}\left(\operatorname{N}\left(g\right)\right)) \land (\operatorname{M}\left(g\right) \leq \operatorname{H}\left(g\right)) \land (\operatorname{H}\left(g\right) \leq 3 \cdot \operatorname{M}\left(g\right))))) \land (\forall n: \mathbb{N}, ((0 < n) \implies ((\operatorname{Nonempty}\left(\operatorname{TreeFiber}\left(\operatorname{pure}\left(true, n\right)\right)\right)) \land (\operatorname{Nonempty}\left(\operatorname{TreeFiber}\left(\operatorname{pure}\left(false, n\right)\right)\right)) \land (\operatorname{N}\left(\operatorname{pure}\left(true, n\right)\right) = n) \land (\operatorname{N}\left(\operatorname{pure}\left(false, n\right)\right) = n) \land (\operatorname{m}\left(\operatorname{pure}\left(true, n\right)\right) = 1) \land (\operatorname{m}\left(\operatorname{pure}\left(false, n\right)\right) = 1) \land (\operatorname{M}\left(\operatorname{pure}\left(true, n\right)\right) = \operatorname{Cat}\left(n - 1\right)) \land (\operatorname{H}\left(\operatorname{pure}\left(true, n\right)\right) = \operatorname{M}\left(\operatorname{pure}\left(true, n\right)\right)) \land (\operatorname{M}\left(\operatorname{pure}\left(false, n\right)\right) = \operatorname{Cat}\left(n - 1\right)) \land (\operatorname{H}\left(\operatorname{pure}\left(false, n\right)\right) = 2 \cdot \operatorname{M}\left(\operatorname{pure}\left(false, n\right)\right)) \land (\frac{\operatorname{H}\left(\operatorname{pure}\left(true, n\right)\right)}{\operatorname{M}\left(\operatorname{pure}\left(true, n\right)\right)} = 1) \land (\frac{\operatorname{H}\left(\operatorname{pure}\left(false, n\right)\right)}{\operatorname{M}\left(\operatorname{pure}\left(false, n\right)\right)} = 2) \land (\operatorname{Nonempty}\left(\operatorname{TreeFiber}\left(\operatorname{upper}\left(n\right)\right)\right)) \land (\operatorname{N}\left(\operatorname{upper}\left(n\right)\right) = n) \land (\frac{\operatorname{H}\left(\operatorname{upper}\left(n\right)\right)}{\operatorname{M}\left(\operatorname{upper}\left(n\right)\right)} = \operatorname{B}\left(n\right))))) \land ((\operatorname{Nonempty}\left(\operatorname{TreeFiber}\left(\operatorname{ba}\left(\right)\right)\right)) \land (\operatorname{N}\left(\operatorname{ba}\left(\right)\right) = 2) \land (\forall w: \operatorname{WordFiber}\left(\operatorname{ba}\left(\right)\right), (\operatorname{val}\left(w\right) = [false, true])) \land (\operatorname{m}\left(\operatorname{ba}\left(\right)\right) = 1) \land (\operatorname{M}\left(\operatorname{ba}\left(\right)\right) = 1) \land (\operatorname{H}\left(\operatorname{ba}\left(\right)\right) = 3) \land (\operatorname{Nonempty}\left(\operatorname{TreeFiber}\left(\operatorname{bab}\left(\right)\right)\right)) \land (\operatorname{N}\left(\operatorname{bab}\left(\right)\right) = 3) \land (\forall w: \operatorname{WordFiber}\left(\operatorname{bab}\left(\right)\right), (\operatorname{val}\left(w\right) = [false, true, false])) \land (\operatorname{m}\left(\operatorname{bab}\left(\right)\right) = 1) \land (\operatorname{M}\left(\operatorname{bab}\left(\right)\right) = 2) \land (\operatorname{H}\left(\operatorname{bab}\left(\right)\right) = 5)) \land (\forall c: \mathbb{R}, ((\forall g: \operatorname{Five}\left(\right), ((\operatorname{Nonempty}\left(\operatorname{TreeFiber}\left(g\right)\right)) \implies (\frac{\operatorname{H}\left(g\right)}{\operatorname{M}\left(g\right)} \leq c))) \implies (3 \leq c)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.sharp_geometry_entrance_ratio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty actual tree fiber supplies the same-word arithmetic guards, positive leaf and tree counts, the exact ratio bounds, and M<=H<=3M. No additional guard hypothesis is imposed on actual trees. The proof of the upper bound uses the entire inverse word fiber and every inverse tree entrance.

At each positive n, the complete pure alpha and pure beta fibers each have one leaf word and Cat(n-1) ordered shapes. Their entrance ratios are one and two. The whole fiber at upper(n) attains B(n). At ba the unique word is beta alpha, with M=1 and H=3; at bab the unique word is beta alpha beta, with M=2 and H=5. The inverse chain bab, ba, beta, alpha counts all entrances by the proved recursion, including the primitive three-leaf shape. Consequently every uniform real upper bound on the ratios is at least three.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.B`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.EntranceFiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.H`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.L`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.Linv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.M`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.N`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.SourceGuards`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.TreeFiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.WordFiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.actual_fiber_counting`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.ba`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.bab`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.letter`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.m`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.prefixMoment`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.pure`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.sharp_geometry_entrance_ratio`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.sigma`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.uniform_actual_entrance_estimate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio.upper`
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer](../SourceTransportCentralizer.md)
- Dependency: [D5/S3/Combinatorics/Partitions/WordPartitionInverse](../../../Combinatorics/Partitions/WordPartitionInverse.md)
