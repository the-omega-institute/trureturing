# Effective atomic observations of guarded completed systems

## Abstract

NativeEffectiveAtomicGuard

**Theorem 1.1 (Boolean constants in finite Presburger syntax).**

$$\forall b: Bool, (\forall x: \operatorname{List}\left(Int\right), ((\operatorname{holds}\left(\operatorname{constant}\left(b\right), x\right)) \iff (b = true)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard.constant_holds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant constructor produces the quantifier-free truth or falsity formula according to its Boolean argument. Its semantics is used by the atomic and image formula constructors, including empty conjunctions and disjunctions.

**Theorem 1.2 (A total finite formula for each exact atomic observation).**

$$\forall n: Nat, (\forall k: Nat, (\forall m: Nat, (\forall s: Nat, (\forall I: \operatorname{Input}\left(n, k, m\right), (\forall guarded: \operatorname{Guarded}\left(\operatorname{equations}\left(I\right)\right), (\forall mode: \operatorname{Mode}\left(s, m\right), (\forall p: \operatorname{Fin}\left(n\right) \to Nat, ((\operatorname{Legal}\left(I, p\right)) \implies (\forall E: \operatorname{Expression}\left(k, m\right), (\forall j: Nat, ((\operatorname{holds}\left(\operatorname{atomicGuard}\left(I, mode, E, j\right), \operatorname{environment}\left(p\right)\right)) \iff (\operatorname{evaluate}\left(\operatorname{ranks}\left(I, p\right), \operatorname{canonical}\left(\operatorname{equations}\left(I\right), \operatorname{ranks}\left(I, p\right), guarded, mode\right), E\right) = \operatorname{atomic}\left(j\right)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard.atomic_guard_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An input I retains its original natural parameter tuple p, integer affine indices, Presburger guard, optional state definitions and repeated expression occurrences. Legal inputs satisfy the original guard and the nonnegativity of every affine index. The terminal-rank map is exactly toNat of those same affine expressions, so every repeated terminal shares its original rank.

The definitions are pair-guarded: a state-dependent defining right side has a pair root. A mode fixes an undefined state to its specified small atom or assigns the leafless Omega. The canonical completed tuple is the unique extension of that free assignment. All finite and infinite completed values are permitted, including non-rational outputs.

For a fixed natural target rank j, atomicGuard constructs finite Presburger syntax expressing equality of an arbitrary expression value with the actual atomic iterate T(j). A ground is compared with the finite native tree for T(j). A parameter token at offset c uses two affine inequalities expressing q(p)+c=j. Omega gives falsity. A decorated state rho(a)Y has an atomic value T(j) exactly when a is at most j and Y has value T(j-a); subtraction occurs only under that explicit inequality.

A pair can equal T(j) only for j at least two, when its ordered children must equal T(j-1) and T(j-2). State formulas unfold a defining right side. Every recursive state query below such a pair has strictly smaller target rank. A well-founded recursive definition therefore constructs total finite syntax without selecting a semantic normal form. Its correctness follows by induction on the target rank and on finite expression syntax, using the exact native atomic predecessor and pair-parse laws.

The displayed equivalence concerns an exact finite terminal observation of a whole completed value. It is the terminal test used in the image-language construction of Proposition 4.3. It imposes neither a finite-depth restriction nor a rationality restriction on the canonical value. The theorem alone does not assert simultaneous image-filter acceptance.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard.atomic_guard_correct`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeEffectiveAtomicGuard.constant_holds`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeAffineImageSaturation](NativeAffineImageSaturation.md)
