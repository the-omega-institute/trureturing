# Literal canonical endpoint and joint resources

## Abstract

Literal canonical endpoint and joint resources.

RegisterRep requires a head at origin, literal little-endian bits with no high zero padding except a single zero bit for zero, the exact natural value, the explicit end marker and blanks elsewhere. It is a tape relation, rather than an arithmetic service premise.

The persistent charge covers all eight tracks, the finite control and fixed code, supplied input and origin cells, every visited cell and every head description. Every prefix of one run is bounded through the same common head interval.

**Theorem 1.1 (register rep).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterResources.register_rep`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterResources.register_rep` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: register_rep (w : List Window) (e : Bool) (j : Lane) : RegisterRep (registerEnd w e) j (bitValue (select j) (Original.finalColumns w e))

**Theorem 1.2 (charged bound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterResources.charged_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterResources.charged_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With all declared parameters and hypotheses, the exact statement is: charged_bound (w : List Window) (e : Bool) (T : ℕ) (hf : ∀ n ≤ T, ∀ t, 0 ≤ (run (initial w e) n).head t ∧ (run (initial w e) n).head t ≤ 3*w.length+6) : ∀ n ≤ T, charged w e n ≤ (code.length + Fintype.card State + 80*(Fintype.card Symbol+1)) * (w.length+1)

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterResources.charged_bound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterResources.register_rep`
- Dependency: [D5/S3/Arith/FibonacciAtomic/NativeContinuation/Acquisition/WindowRegisterProgram](WindowRegisterProgram.md)
