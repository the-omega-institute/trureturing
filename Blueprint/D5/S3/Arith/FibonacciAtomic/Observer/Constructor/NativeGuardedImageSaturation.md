# Joint actual-image saturation for guarded native systems

## Abstract

NativeGuardedImageSaturation

**Theorem 1.1 (One canonical same-mode extension tests all retained image filters).**

$$\forall k: Nat, (\forall m: Nat, (\forall S: \operatorname{System}\left(k, m\right), (\forall p: \operatorname{Fin}\left(k\right) \to Nat, (\forall guarded: \operatorname{Guarded}\left(S\right), (\forall filters: \operatorname{List}\left(\operatorname{Filter}\left(k, m\right)\right), (\forall mode: \operatorname{Mode}\left(\operatorname{threshold}\left(filters\right), m\right), ((\operatorname{Satisfies}\left(S, p, \operatorname{canonical}\left(S, p, guarded, mode\right)\right)) \land ((\operatorname{InMode}\left(S, \operatorname{threshold}\left(filters\right), mode, \operatorname{canonical}\left(S, p, guarded, mode\right)\right)) \land ((\exists v: \operatorname{Fin}\left(m\right) \to CompletionTree, ((\operatorname{Satisfies}\left(S, p, v\right)) \land ((\operatorname{InMode}\left(S, \operatorname{threshold}\left(filters\right), mode, v\right)) \land (\operatorname{Passes}\left(p, v, filters\right))))) \iff (\operatorname{Passes}\left(p, \operatorname{canonical}\left(S, p, guarded, mode\right), filters\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedImageSaturation.normalized_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let S be an arbitrary finite optional-definition system in the actual native completion. All state-dependent right sides have explicit pair roots. Expressions retain finite grounds, finite parameter atoms with fixed natural offsets, Omega, nonnegative powers of states and ordered pairs. The parameter tuple p is fixed and arbitrary. A filter is any expression C together with a natural threshold t, interpreted as membership of its whole actual value in range(rho(t)). The finite filter list retains every conjunct, including repetitions.

Set s to the maximum of zero and all thresholds in that list. A free-state mode chooses, for each undefined state, either one actual exceptional atom atomic(j) with j in Fin(s+2), or the requirement that its value is unequal to every atomic(j) with j at most s+1. These are fixed and live conditions on whole unrestricted completed values, rather than on token labels or finite prefixes. A mode entry at a defined state has no effect.

The canonical free assignment retains each selected fixed atom and assigns the actual leafless Omega to every live state. The previously established unique guarded extension defines its entire state tuple K. The theorem proves that K satisfies all definitions and its specified mode, and proves the joint equivalence: there exists a simultaneous solution of S in that mode passing the entire filter list if and only if that same canonical tuple K passes the entire list. The right-to-left implication uses K itself. This concerns existence in a mode; different live solutions need not be equal.

For the forward implication, compare the given solution and K at the same p. Any free value that is atomic(j) with j at most s+1 must be in the fixed alternative, and is preserved. The bounded atomic replacement theorem then preserves every expression terminal atomic(t) or atomic(t+1) used at a threshold t at most s. At an explicit pair, the exact native image decomposition either selects one of those unchanged terminals or sends image obligations to both actual children.

A positive decorator a at threshold t either supplies an image immediately when a is at least t, or cancels injectively to threshold t-a. Strong induction on the threshold handles this decrease. A zero-decorated state unfolds its actual defining equation, whose guarded root is constant or a pair; an undefined state is unchanged or replaced by Omega. Omega belongs to every actual image because it is fixed by every native iterate.

The collected canonical obligations form a post-fixed relation for the actual image grammar. A corecursor chooses source leaves for its two terminal alternatives and source pairs for its pair alternatives. Induction at every cutoff depth proves that applying rho(t) to this unrestricted source tree gives the stipulated canonical value. Equality of all four-valued replies proves exact completed equality. Thus infinite parses have actual preimages, including non-rational ones; they are not replaced by finite-depth acceptance.

This theorem starts with a normalized pair-guarded system. It does not construct root-link normalization, its original-state reconstruction maps, the two original-to-normalized solution correspondences, or the transport of additional original filters and affine parameter guards. Applying the result to an unnormalized system requires those correspondences with every filter and reconstruction retained. No bound on source size, depth, rank or rationality is imposed by the guarded result itself.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedImageSaturation.normalized_saturation`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedAtomicReplacement](NativeGuardedAtomicReplacement.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeImageSaturationInterface](NativeImageSaturationInterface.md)
