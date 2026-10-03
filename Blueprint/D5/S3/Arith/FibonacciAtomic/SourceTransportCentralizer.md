# The Ordered Fibonacci Source Centralizer

## Abstract

Every ordered source endomorphism commuting with Fibonacci substitution is one unique nonnegative iterate.

T is the free magma on the two Boolean generators: alpha is the leaf true and beta is the leaf false. Its elements are actual nonempty finite ordered binary trees. The operation pair(s,t) constructs an internal node with left child s and right child t. There are no associative, commutative or quotient identifications. The substitution rho sends alpha to beta, beta to pair(beta,alpha), and pair(s,t) to pair(rho(s),rho(t)).

All exponents belong to Nat={0,1,2,...}. Write R(k,t)=rho^k(t), so R(0,t)=t, and Rpower(k) denotes the function t to R(k,t). C(F) means that the total function F:T to T preserves every ordered pair and satisfies F(rho(t))=rho(F(t)) for every source t. Pairing preservation and commutation are the only assumptions; injectivity and a unique power representation follow, while bijectivity and inverse domains are classified below.

For each k, I(k) is the actual subtype consisting of trees in the range of R(k,-). Write core(k,t) for R(k,t) regarded as an element of I(k), with t as its preimage witness. A range inverse d:I(k) to T satisfies d(core(k,t))=t for every t and core(k,d(y))=y for every y:I(k); the second equality is an equality in that subtype.

**Theorem 1.1 (Complete Centralizer and Inverse Classification).**

$$\begin{gathered}(\forall u: T, ((\operatorname{R}\left(2, u\right) = \operatorname{pair}\left(\operatorname{R}\left(1, u\right), u\right)) \iff (\exists k: \operatorname{Nat}\left(\right), (\operatorname{R}\left(k, alpha\right) = u)))) \land (\forall F: T \to T, (((\forall s: T, (\forall t: T, (\operatorname{F}\left(\operatorname{pair}\left(s, t\right)\right) = \operatorname{pair}\left(\operatorname{F}\left(s\right), \operatorname{F}\left(t\right)\right)))) \land (\forall t: T, (\operatorname{F}\left(\operatorname{R}\left(1, t\right)\right) = \operatorname{R}\left(1, \operatorname{F}\left(t\right)\right)))) \iff (\exists k: \operatorname{Nat}\left(\right), ((F = \operatorname{Rpower}\left(k\right)) \land (\forall j: \operatorname{Nat}\left(\right), ((F = \operatorname{Rpower}\left(j\right)) \implies (j = k))))))) \land (\forall F: T \to T, (((\forall s: T, (\forall t: T, (\operatorname{F}\left(\operatorname{pair}\left(s, t\right)\right) = \operatorname{pair}\left(\operatorname{F}\left(s\right), \operatorname{F}\left(t\right)\right)))) \land (\forall t: T, (\operatorname{F}\left(\operatorname{R}\left(1, t\right)\right) = \operatorname{R}\left(1, \operatorname{F}\left(t\right)\right)))) \implies (\operatorname{Injective}\left(F\right)))) \land (\forall k: \operatorname{Nat}\left(\right), ((\operatorname{Bijective}\left(\operatorname{Rpower}\left(k\right)\right)) \iff (k = 0))) \land (\forall k: \operatorname{Nat}\left(\right), ((0 < k) \implies ((\exists d: \operatorname{I}\left(k\right) \to T, (((\forall t: T, (\operatorname{d}\left(\operatorname{core}\left(k, t\right)\right) = t)) \land (\forall y: \operatorname{I}\left(k\right), (\operatorname{core}\left(k, \operatorname{d}\left(y\right)\right) = y))) \land (\forall e: \operatorname{I}\left(k\right) \to T, (((\forall t: T, (\operatorname{e}\left(\operatorname{core}\left(k, t\right)\right) = t)) \land (\forall y: \operatorname{I}\left(k\right), (\operatorname{core}\left(k, \operatorname{e}\left(y\right)\right) = y))) \implies (e = d))))) \land (\neg (\exists d: T \to T, ((\forall t: T, (\operatorname{d}\left(\operatorname{R}\left(k, t\right)\right) = t)) \land (\forall t: T, (\operatorname{R}\left(k, \operatorname{d}\left(t\right)\right) = t))))))))\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.source_transport_centralizer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stability equation rho(rho(u))=pair(rho(u),u) holds exactly on the alpha orbit. For every total F, C(F) holds if and only if there is exactly one natural k with F=R(k,-). Every F satisfying C(F) is injective. For each k, R(k,-):T to T is bijective if and only if k=0. For each positive k there is exactly one range inverse with both identities, and there is no total d:T to T satisfying both inverse identities on T.

Composition counts alpha and beta leaves. The public fiber map transports composition by (a,b) to (b,a+b). Equal substituted trees therefore have equal source compositions. Appending alpha to both source trees puts them in one positive composition fiber; the injectivity of its one-step fiber map then cancels their images and the appended pair constructor. The same composition transport excludes alpha from the image of rho.

Both leaves satisfy the stability equation. If pair(s,t) satisfies it, comparison of the two root children gives rho^2(t)=pair(s,t) and rho^2(s)=rho(pair(s,t))=rho^2(rho(t)). Injectivity gives s=rho(t), so t also satisfies the equation. Structural induction on the strictly smaller right subtree gives t=R(j,alpha), hence pair(s,t)=R(j+2,alpha). Conversely, applying the pairing-preserving rho to the equation preserves it, starting from alpha.

Commutation forces F(beta)=rho(F(alpha)) and the stability equation for F(alpha). Its classification determines both generator images. The universal property of the free magma identifies F with the corresponding iterate. Every iterate preserves pairs and commutes with rho. Cancelling injective iterates and excluding alpha from every positive image shows that distinct exponents give distinct alpha images, establishing uniqueness.

Every iterate is injective. Exponent zero gives the identity; every positive exponent omits alpha, so is not surjective. Corestriction to the actual image is a bijection and its inverse satisfies both typed identities. Injectivity makes that inverse unique. An arbitrary whole-source extension can satisfy a left-inverse identity, but cannot satisfy the right-inverse identity at alpha.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer.source_transport_centralizer`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport](GenealogicalFiberTransport.md)
