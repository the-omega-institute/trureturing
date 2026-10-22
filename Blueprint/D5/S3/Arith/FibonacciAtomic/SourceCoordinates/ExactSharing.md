# Exact Sharing and Pure Fibonacci Evaluation

## Abstract

Exact expanded size, rooted sharing and binary-call count of the Fibonacci source.

S is the existing FreeMagma Bool of nonempty ordered binary trees. Alpha is of(true), beta is of(false), and pair(s,t) retains both ordered ports and all brackets. The existing substitution rho sends alpha to beta and beta to pair(beta,alpha), preserving pairs. T(n)=rho^n(alpha), so T(0)=alpha, T(1)=beta and T(n+2)=pair(T(n+1),T(n)). The leaf count ell is FreeMagma.length. Composition c records the two labelled leaf counts, and B(n)=atomicBlock(n) is the existing iterated composition step (a,b) to (b,a+b). All indices are natural numbers, subtraction is truncated natural subtraction, and fib(0)=0, fib(1)=1.

**Definition 1.1 (Expanded Node Count).**

$$(\forall b: \operatorname{Bool}\left(\right), (\operatorname{N}\left(\operatorname{of}\left(b\right)\right) = 1)) \land (\forall s: S, (\forall t: S, (\operatorname{N}\left(\operatorname{pair}\left(s, t\right)\right) = \operatorname{N}\left(s\right) + \operatorname{N}\left(t\right) + 1)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.expandedNodes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(t)=expandedNodes(t) counts every leaf and every internal node of the expanded tree.

**Definition 1.2 (Rooted Fringe Set).**

$$(\forall b: \operatorname{Bool}\left(\right), (\operatorname{Sub}\left(\operatorname{of}\left(b\right)\right) = \operatorname{singleton}\left(\operatorname{of}\left(b\right)\right))) \land (\forall s: S, (\forall t: S, (\operatorname{Sub}\left(\operatorname{pair}\left(s, t\right)\right) = \operatorname{insert}\left(\operatorname{pair}\left(s, t\right), \operatorname{union}\left(\operatorname{Sub}\left(s\right), \operatorname{Sub}\left(t\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.fringes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sub(t)=fringes(t) is a finite set of actual rooted fringe trees. It contains the root and recursively both children's fringes, identifying only exactly equal trees. It is the exact distinct-fringe set used below for the source-level sharing count. Every retained node occurs below the root; orbit terms absent from the tree are excluded. Labels, ports and brackets participate in equality. A separate DAG object or minimality theorem is outside this declaration.

**Definition 1.3 (One Counted Binary Call).**

$$\forall A: \operatorname{Type}\left(\right), (\forall m: A \to A \to A, (\forall s: A \times A \times \operatorname{Nat}\left(\right), (\operatorname{step}\left(m, s\right) = (\operatorname{current}\left(s\right), \operatorname{apply}\left(m, \operatorname{current}\left(s\right), \operatorname{previous}\left(s\right)\right), \operatorname{calls}\left(s\right) + 1))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.evalStep` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A is any type in an arbitrary universe. A state is a triple (previous,current,calls). Step(m,s)=evalStep(m,s) reads the two saved values, invokes m(current,previous) once, retains current as the next previous value and increments calls by one. No associativity or commutativity is assumed of the binary operation.

**Definition 1.4 (Evaluation from Supplied Leaf Values).**

$$\forall A: \operatorname{Type}\left(\right), (\forall m: A \to A \to A, (\forall a: A, (\forall b: A, (\forall n: \operatorname{Nat}\left(\right), (\operatorname{sharedEval}\left(m, a, b, n\right) = \operatorname{ite}\left(n = 0, (a, 0), (\operatorname{current}\left(\operatorname{run}\left(m, a, b, n\right)\right), \operatorname{calls}\left(\operatorname{run}\left(m, a, b, n\right)\right))\right))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.sharedEval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Shared(m,a,b,n)=sharedEval(m,a,b,n). In the formula, run(m,a,b,n) means the (n-1)-fold iterate of step(m,-) on (a,b,0). At n=0 the result is (a,0); otherwise it is the current value and counter from that run. The input leaf values a and b are already supplied. The run stores only the two consecutive values and a counter.

**Theorem 1.5 (Exact Expanded Size, Rooted Fringe Size, and Pure Evaluation).**

$$(\forall n: \operatorname{Nat}\left(\right), ((\operatorname{c}\left(\operatorname{T}\left(n\right)\right) = \operatorname{B}\left(n\right)) \land (\operatorname{ell}\left(\operatorname{T}\left(n\right)\right) = \operatorname{fib}\left(n + 1\right)) \land (\operatorname{N}\left(\operatorname{T}\left(n\right)\right) = 2 \cdot \operatorname{fib}\left(n + 1\right) - 1) \land ((n < 2) \implies ((\operatorname{Sub}\left(\operatorname{T}\left(n\right)\right) = \operatorname{singleton}\left(\operatorname{T}\left(n\right)\right)) \land (\operatorname{card}\left(\operatorname{Sub}\left(\operatorname{T}\left(n\right)\right)\right) = 1))) \land ((2 \le n) \implies ((\operatorname{Sub}\left(\operatorname{T}\left(n\right)\right) = \operatorname{image}\left(T, \operatorname{range}\left(n + 1\right)\right)) \land (\operatorname{card}\left(\operatorname{Sub}\left(\operatorname{T}\left(n\right)\right)\right) = n + 1))))) \land (\forall A: \operatorname{Type}\left(\right), (\forall m: A \to A \to A, (\forall E: S \to A, ((\forall s: S, (\forall t: S, (\operatorname{E}\left(\operatorname{pair}\left(s, t\right)\right) = \operatorname{apply}\left(m, \operatorname{E}\left(s\right), \operatorname{E}\left(t\right)\right)))) \implies (\forall n: \operatorname{Nat}\left(\right), (\operatorname{sharedEval}\left(m, \operatorname{E}\left(alpha\right), \operatorname{E}\left(beta\right), n\right) = (\operatorname{E}\left(\operatorname{T}\left(n\right)\right), n - 1)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.exact_sharing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n, the source composition equals B(n), its leaf count is fib(n+1), and its expanded node count is 2 fib(n+1)-1. Its complete fringe set is the singleton {T(n)} when n<2, and the image of range(n+1) under T otherwise. Thus the formal source-level fringe count is one at n=0,1 and n+1 at every n>=2. In particular the other labelled leaf is absent at each singleton stage.

The source centralizer supplies the ordered orbit recurrence, and the existing iterate_length theorem supplies its leaf count. Structural induction gives N(t)=2 ell(t)-1 for every nonempty full binary source. The intrinsic primitive-root uniqueness theorem makes the orbit T injective, retaining the distinction between the two initial one-leaf trees. For T(2), all three orbit terms occur. For larger trees the larger child already contains every fringe of the smaller child. Adding the new root extends precisely the initial segment of the orbit, so its cardinality is n+1. Composition is the existing CliffordLeafOrbit.result observation.

For any total interpretation E:S to A preserving pairs by a fixed binary operation m, k iterations of the counted step have state (E(T(k)),E(T(k+1)),k). Induction uses the same ordered recurrence, without any algebraic law on m. The resulting shared evaluation equals (E(T(n)),n-1) for every n, including zero calls at n=0,1. This is an achievable call count; no claim of optimality is made for interpretations with additional identities or constant values.

Purity is expressed by one function E and one fixed operation m on the whole source. Position, changing environments, histories and side effects are not supplied by this interface. The counter is not a bit-time bound: obtaining leaf values, reading operands, representing intermediate values, storage and writing the requested output have separate costs. Polynomial bit time needs bounds on those encoding and operation costs. A linear count in n is not a polynomial bound in the length of a binary encoding of n. Requesting the expanded tree still requires its full expanded output. These resource qualifications do not follow from the call counter.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.evalStep`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.exact_sharing`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.expandedNodes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.fringes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/ExactSharing.sharedEval`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit](../CliffordLeafOrbit.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap](NativeRotationDepthGap.md)
