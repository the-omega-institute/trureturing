# Symbolic finite coordinates of native joint solutions

## Abstract

NativeSymbolicFiniteForcing

**Theorem 1.1 (Finite original values are independent of free solutions).**

$$\forall k: Nat, (\forall m: Nat, (\forall r: Nat, (\forall S: \operatorname{FunctionalSystem}\left(k, m\right), (\forall b: \operatorname{Modes}\left(k\right), (\forall R: \operatorname{Reconstructions}\left(k, m, r\right), ((\forall p: \operatorname{Parameters}\left(k\right), (\operatorname{satisfies}\left(S, b, p, \operatorname{canonicalSolution}\left(S, b, p\right)\right))) \land (\forall p: \operatorname{Parameters}\left(k\right), (\forall i: \operatorname{Fin}\left(r\right), (((\operatorname{IsFinite}\left(\operatorname{value}\left(b, p, \operatorname{canonicalSolution}\left(S, b, p\right), \operatorname{at}\left(R, i\right)\right)\right)) \iff (i \in \operatorname{finiteOriginals}\left(S, b, R\right))) \land (\forall f: \operatorname{FiniteExpression}\left(k\right), ((\operatorname{finiteExpressions}\left(S, b, R, i\right) = \operatorname{some}\left(f\right)) \implies ((\operatorname{value}\left(b, p, \operatorname{canonicalSolution}\left(S, b, p\right), \operatorname{at}\left(R, i\right)\right) = \operatorname{embed}\left(\operatorname{finiteValue}\left(p, f\right)\right)) \land (\forall v: \operatorname{NativeValues}\left(m\right), ((\operatorname{satisfies}\left(S, b, p, v\right)) \implies (\operatorname{value}\left(b, p, v, \operatorname{at}\left(R, i\right)\right) = \operatorname{embed}\left(\operatorname{finiteValue}\left(p, f\right)\right))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicFiniteForcing.symbolic_finite_forcing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let k, m and r be arbitrary natural numbers. A functional system S gives each of its m states either one native expression or no equation. An expression is a finite native ground, a shared parameter atom with a fixed offset, a state with a fixed nonnegative power of the native substitution, or an ordered pair. A fixed Boolean mode chooses whether each token denotes its finite atomic value or the leafless tree Omega. In particular, an explicit Omega can use a token in the divergent mode. The parameter tuple p assigns arbitrary natural numbers to all token names; divergent token values ignore their corresponding entries. Each of the r original coordinates has an arbitrary expression R(i) in these same states and tokens. Repeated occurrences retain the same values.

The canonical joint assignment K(S,mode,p) is the original native leaf limit of simultaneous equation iteration from Omega. An extra undefined state represents the explicit leafless terminal. Native specialization evaluates only the finite parameter terminals; it retains every state occurrence, power and pair. Undefined states and free zero-power alias cycles start and remain at Omega. All equations are satisfied by one common assignment, including equations for unused auxiliaries. No finiteness condition is imposed on those auxiliaries.

To obtain the finite expressions, start with no known state values. A symbolic evaluation succeeds at a finite ground or a finite-mode token; it succeeds at a powered state precisely when that state has a known expression, and at a pair precisely when both children succeed. Each simultaneous pass evaluates every defined right side against the preceding pass. Once obtained, an expression persists unchanged. If a pass changes, its finite support strictly grows. There are m states, so after m passes no further finite expression can appear. Evaluate each original reconstruction against that pass. The resulting option is finiteExpressions(S,mode,R,i); F(S,mode,R) is exactly the finite set of successful original indices. These objects contain no parameter values.

For every p the canonical reconstruction is finite exactly at the indices in F. Whenever finiteExpressions returns f, the reconstruction equals embed(finiteValue(p,f)) in the canonical assignment and in every joint solution of S at that same p. Here f is the existing finite native expression syntax: grounds, shared parameter atoms, fixed powers and ordered pairs. finiteValue evaluates the parameter atoms as the actual finite native iterates of alpha. Equal parameter atoms and native atomic pair collapses do not change the finite support test.

The semantic argument uses the native leaf order. Every finite tree is maximal in this order. Each finite leaf in an increasing native limit appears at some finite stage; a finite tree has only finitely many leaves, so a common stage contains all of them. Hence a finite canonical reconstruction is already finite at some simultaneous iteration. The symbolic pass describes exactly the finite values at each such iteration, and support stabilization brings that expression back to the m-th pass. Every iteration lies below every whole-system solution. Maximality therefore forces every solution's corresponding reconstruction to have the same finite value.

The statement is uniform in the number of states, parameters and original reconstructions. It includes empty tuples, arbitrary recursive equations, and finite original coordinates beside infinite auxiliary coordinates. Restriction to any guard on the same parameter tuple follows immediately. A canonical infinite coordinate may be finite in another solution. The result gives neither an effective prefix bound for infinite coordinates nor an algorithm recognizing which raw input reductions are accepted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicFiniteForcing.symbolic_finite_forcing`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFunctionalObstruction](NativeFunctionalObstruction.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeSimultaneousPrefixSeparation](../NativeSimultaneousPrefixSeparation.md)
