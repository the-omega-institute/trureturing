# Canonical coding of the native completion

## Abstract

CompletedNativeCanonicalCoding

**Theorem 1.1 (Maximal atomic collapse and independent expansion are inverse).**

$$(\forall X: CompletionTree, ((\operatorname{Reduced}\left(\operatorname{collapse}\left(X\right)\right)) \land (\operatorname{expansion}\left(\operatorname{collapse}\left(X\right)\right) = X))) \land (\forall C: Code, ((\operatorname{Reduced}\left(C\right)) \implies (\operatorname{collapse}\left(\operatorname{expansion}\left(C\right)\right) = C))) \land ((\operatorname{Injective}\left(collapse\right)) \land (\forall C: Code, ((\operatorname{Reduced}\left(C\right)) \implies (\exists X: CompletionTree, (\operatorname{collapse}\left(X\right) = C))))) \land (\forall k: Nat, (\forall C: Code, ((\operatorname{Reduced}\left(C\right)) \implies (\operatorname{Reduced}\left(\operatorname{shift}\left(k, C\right)\right))))) \land (\forall k: Nat, (\forall X: CompletionTree, (\operatorname{collapse}\left(\operatorname{rhoIterate}\left(k, X\right)\right) = \operatorname{shift}\left(k, \operatorname{collapse}\left(X\right)\right)))) \land (\forall C: Code, ((\operatorname{Reduced}\left(C\right)) \implies ((\operatorname{expansion}\left(C\right) = Omega) \iff (C = codeOmega)))) \land (\forall n: Nat, (\operatorname{collapse}\left(\operatorname{atomic}\left(n\right)\right) = \operatorname{primitive}\left(n\right))) \land (\forall l: CompletionTree, (\forall r: CompletionTree, ((\neg(\exists n: Nat, (\operatorname{node}\left(l, r\right) = \operatorname{atomic}\left(n\right)))) \implies (\operatorname{collapse}\left(\operatorname{node}\left(l, r\right)\right) = \operatorname{fork}\left(\operatorname{collapse}\left(l\right), \operatorname{collapse}\left(r\right)\right))))) \land (\forall l: Code, (\forall r: Code, ((\operatorname{fork}\left(l, r\right) \neq codeOmega) \implies (\neg((l = codeOmega) \land (r = codeOmega))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/CompletedNativeCanonicalCoding.canonical_coding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native domain is the existing unrestricted CompletionTree, with equality at every finite address, its actual substitution rho, its finite atomic iterates and its actual leafless Omega. Code is the unrestricted final coalgebra with natural-number leaves and ordered binary branches. In particular it includes nonregular infinite trees and arbitrary mixtures of finite leaves and leafless subtrees. codeOmega is the all-branch value, not a separate leaf label.

Reduced excludes the atomic sibling collision ([n+1],[n]) at every reached address. Since fork codeOmega codeOmega equals codeOmega extensionally, the second collision has no retained pair distinct from that value. The final clause states this exclusion explicitly. Collapse tests whether the entire encountered native subtree is atomic before descending, so primitive occurrences are precisely maximal finite atomic subtrees. At every other native pair, both children and their order are retained.

Expansion is an independent total corecursor: primitive n expands to the existing atomic n, while code branches expand to native ordered branches. Its additional native state copies finite atomic expansions without using collapse or a chosen inverse. The theorem proves that collapse lands in Reduced, both inverse identities on the full indicated domains, injectivity and surjectivity onto all reduced codes, preservation of reduction under every natural shift, intertwining of every actual rho iterate with label addition, and exact uniqueness of the code of Omega.

In the formula, rhoIterate(k,X) denotes (Function.iterate rho k) X, and Injective denotes Function.Injective. CompletionTree and Code retain their unrestricted native meanings.

The arbitrary-code atomic reflection in the proof rules out a reduced branch expanding to a finite atom. The inverse identities use finite-address extensionality and the pinned final-coalgebra bisimulation principle. The theorem supplies a semantic representation, with no algorithm for deciding atomicity of arbitrary infinite inputs and no assertion of integer-code-prefix continuity. Its primary output is an unrestricted structural equivalence, rather than bounded enumeration, a checker, a numeric reduction or a certified finite instance. No external literature novelty is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/CompletedNativeCanonicalCoding.canonical_coding`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints](../CompletionHomogeneousFixedPoints.md)
