# Minimum Rational Dimension of the Fibonacci Parity Lift

## Abstract

The five-window parity task, lifted to rational outputs, has minimum linear dimension four.

The five windows null, [2], [3], [25], [5] have printed bits 000, 100, 010, 101, 001, respectively. Words arrive high to low. A seam records the low bit of the previous higher window; it cannot be one when the new window's high bit is one. The unit bit is zero. Empty words, leading null windows and all finite prefixes belong to the task, and an illegal seam remains an absorbing error.

**Definition 1.1 (Linear representations of words).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.WordRepresentation`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.WordRepresentation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Over a field K, a representation consists of a K-vector space V, a designated initial vector, a linear endomorphism for each letter and a linear output map to a K-vector space Y. No reachability or observability hypothesis is imposed. The dimension of a finite-dimensional representation is dim_K(V).

**Definition 1.2 (Chronological products).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.wordMap`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.wordMap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word acts by the identity. For a word beginning with a letter b and followed by w, the operator is the operator for w composed with the operator for b. Thus letters act in input order.

**Definition 1.3 (Full word responses).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.wordBehavior`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.wordBehavior` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The behavior of R on w is its output map applied to the word operator acting on its initial vector. R realizes a task when these responses agree on every finite word.

**Definition 1.4 (Rational encoding after reduction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.parityEncode`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.parityEncode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An error maps to (0,0). A residue b in ZMod(2) maps to (1,val(b)), where val(b) is the standard representative zero or one, then embedded into the rational numbers.

**Definition 1.5 (The rational parity task).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.parityTask`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.parityTask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

g(w) applies parityEncode to the immediate mod-two Fibonacci quantity task. Legal zero quantity yields (1,0), distinct from error. This encoding takes the residue representative before passing to rational coordinates.

**Definition 1.6 (The integer response).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerTask`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerTask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the existing immediate quantity reader at modulus zero, whose carrier ZMod(0) is Z. A legal quantity q yields (1,q) in Z^2, and an illegal word yields (0,0). This response is computed before a coefficient field is selected.

**Definition 1.7 (Natural change of coefficient field).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerFieldTask`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerFieldTask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any field K, f_K applies the natural map from Z to K to both coordinates of integerTask. It retains the legality coordinate separately from quantity.

**Definition 1.8 (The integer-induced rational task).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerRationalTask`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerRationalTask` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

f_Q(w) starts with seam zero and integer composition (0,0). A legal final composition (a,b) yields (1,2a+3b) in Q^2. Error yields (0,0). No mod-two reduction is taken.

**Definition 1.9 (Two homogeneous seam blocks).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.BlockState`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.BlockState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V=Q^4 has coordinates (b_0,c_0,b_1,c_1). An actual legal state occupies only its current seam block with c=1 and b in {0,1}; error is the zero vector.

**Definition 1.10 (Linear parity flips and seam routing).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockUpdate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockUpdate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Null and [2] preserve parity, while [3], [25] and [5] flip it using J(b,c)=(c-b,c). Allowed source blocks are sent to the new seam, with contributions added when both source blocks have the same destination. Disallowed blocks map to zero. These formulas define linear maps on all of Q^4.

**Definition 1.11 (The letter operators).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockTransition`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockTransition` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each blockUpdate is regarded as a rational linear endomorphism of the four-dimensional state space.

**Definition 1.12 (Two output channels).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockOutput`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output is (c_0+c_1,b_0+b_1).

**Definition 1.13 (The initialized four-dimensional representation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.fourDimensional`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.fourDimensional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The initial vector is (0,1,0,0), each letter uses blockTransition, and the output is blockOutput.

**Definition 1.14 (Actual mod-two states).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.embed`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.embed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Embed a legal mod-two raw state by retaining the standard representative of its second composition coordinate in its seam block, with homogeneous coordinate one. Embed error as zero.

**Definition 1.15 (Four actual histories).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.prefixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.prefixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The histories are the empty word, [3], [2], and [3][2], in that order.

**Definition 1.16 (Actual continuation tests).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.suffixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.suffixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The four row tests use [5], [5], null[5], null[5], respectively.

**Definition 1.17 (Scalar row observations).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.selectOutput`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.selectOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows zero and two observe legality, the first output coordinate. Rows one and three observe parity, the second output coordinate.

**Definition 1.18 (The actual response matrix).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.responseMinor`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.responseMinor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The entry in row i and column j is the selected scalar response of g to prefix j followed by suffix i. Denote this fixed matrix by H. Its rows are (1,1,0,0), (1,0,0,0), (1,1,1,1), (1,0,1,0); its determinant is one.

**Theorem 1.19 (Attained minimum dimension four).**

$$(\operatorname{Realizes}\left(F, g\right)) \land \\(\operatorname{dim}\left(Q4\right) = 4) \land \\(\forall V, \forall R, ((\operatorname{FiniteQSpace}\left(V\right)) \land \\(\operatorname{LinearWordRep}\left(R, V\right))) \implies ((\operatorname{Realizes}\left(R, g\right)) \implies (4 \leq \operatorname{dim}\left(V\right)))) \land \\(\operatorname{g}\left(word3\right) = \operatorname{pair}\left(1, 1\right)) \land \\(\operatorname{fQ}\left(word3\right) = \operatorname{pair}\left(1, 3\right)) \land \\(responseMinor = H) \land \\(\operatorname{det}\left(responseMinor\right) = 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here F denotes fourDimensional, g denotes parityTask, and f_Q denotes integerRationalTask. Q4 denotes BlockState=Q^4, word3 denotes the singleton word [3], and pair(a,b) denotes the ordered output pair. Realizes(R,g) means equality on every finite word. V ranges over all finite-dimensional rational vector spaces, and R ranges over all rational linear word representations on V with outputs in Q^2. No bound on word length is imposed.

Embedding the actual mod-two state commutes with every letter operator. Word induction therefore identifies the four-dimensional representation with g on every finite input, including error continuations. The parity flip uses ordinary rational subtraction on Boolean states; it does not identify the rational field with a field of characteristic two.

For any representation R that realizes g, let its four reached prefix vectors be P_j. Continuing a vector by each suffix and selecting the specified output coordinate defines a linear observation O into Q^4. Chronological composition and equality of all word responses give O(P_j) equal to column j of the actual response matrix. The determinant one makes these columns linearly independent, so the four P_j are linearly independent in V. Thus every such V has dimension at least four.

The four-dimensional representation attains this lower bound. On [3], the parity lift is (1,1), while the integer-induced rational task is (1,3). Their coefficient carrier is the same, but their complete word response tasks differ.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.BlockState`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.WordRepresentation`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockOutput`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockTransition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.blockUpdate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.embed`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.fourDimensional`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerFieldTask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerRationalTask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.integerTask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.parityEncode`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.parityTask`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.prefixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.responseMinor`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.selectOutput`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.suffixes`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.wordBehavior`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/ParityLiftRationalMinimum.wordMap`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ImmediateWindowStateCapacity](ImmediateWindowStateCapacity.md)
