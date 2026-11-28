# Bounded Real Cocycles and Continuous Potentials

## Abstract

A bounded real cocycle on one dense orbit determines a unique continuous normalized potential.

**Theorem 1.1 (Exact reconstruction from a bounded orbit).**

$$\forall G: \operatorname{Type}, \forall X: \operatorname{Type}, [\operatorname{Mul}\left(G\right)] [\operatorname{TopologicalSpace}\left(X\right)] [\operatorname{CompactSpace}\left(X\right)] [\operatorname{T2Space}\left(X\right)], \forall a: G \to X \to X, \forall c: G \to X \to \mathbb{R}, \forall b: X, \forall C: \mathbb{R}, (\left(\left(\left((\forall g: G, \operatorname{Continuous}\left(\operatorname{slice}\left(a, g\right)\right)) \land (\forall g: G, \forall h: G, \forall x: X, \operatorname{a}\left(g \cdot h, x\right)=\operatorname{a}\left(g, \operatorname{a}\left(h, x\right)\right))\right) \land (\forall x: X, \operatorname{DenseRange}\left(\operatorname{orbit}\left(a, x\right)\right))\right) \land (\forall g: G, \operatorname{Continuous}\left(\operatorname{slice}\left(c, g\right)\right))\right) \land (\forall g: G, \forall h: G, \forall x: X, \operatorname{c}\left(g \cdot h, x\right)=\operatorname{c}\left(g, \operatorname{a}\left(h, x\right)\right)+\operatorname{c}\left(h, x\right))) \Rightarrow ((\forall g: G, |\operatorname{c}\left(g, b\right)| \le C) \Leftrightarrow \exists! phi: X \to \mathbb{R}, \left(\left((\operatorname{Continuous}\left(phi\right)) \land (\operatorname{phi}\left(b\right)=0)\right) \land (\forall g: G, \forall x: X, \operatorname{phi}\left(\operatorname{a}\left(g, x\right)\right)-\operatorname{phi}\left(x\right)=\operatorname{c}\left(g, x\right))\right) \land (\forall x: X, |\operatorname{phi}\left(x\right)| \le C))$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/OrbitClosure/BoundedRealCocycle.bounded_iff_existsUnique_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Daniel Coronel; Andrés Navas; Mario Ponce (2011). *On bounded cocycles of isometries over a minimal dynamics*. URL: <https://arxiv.org/abs/1101.3523v4>.

*Acknowledgement.* Boris Petković (2026). *Classification of some cohomologically C0-stable continuous group actions on metric spaces*. URL: <https://arxiv.org/abs/2607.11171v1>.

*Commentary.*

G and X range over independent universes. G has a multiplication, and X is compact and Hausdorff. The notation slice(a,g) means x mapped to a(g,x); orbit(a,x) means g mapped to a(g,x). Each action slice and each real cocycle slice is continuous. Every G-orbit is dense. The displayed composition equations refer to this one action and this one cocycle.

The point b is specified and C is any real number. The unique potential is continuous, vanishes at b, has the prescribed difference along every action map, and satisfies the same bound C at every point. No identity, inverse, associativity, commutativity, finite generation or topology on G is required. Action maps may be noninvertible. Density and the given b imply that G is inhabited. Negative C makes both sides impossible; C = 0 is included. In particular the result applies to every semigroup acting minimally on a compact metric space.

For F_g(x,t) = (a(g,x), t + c(g,x)), the cocycle identity makes the closure of the actual skew orbit {(a(g,b), c(g,b))} forward invariant. The one-point bound places this closure inside the compact product X times [-C,C]. Intersections of descending chains of nonempty compact sets preserve invariance under every F_g. Zorn's lemma therefore gives a minimal nonempty compact invariant subset K. Its projection to X is compact and closed, contains a dense orbit, and hence equals X.

Suppose a fibre of K contains heights v and w, and put d = w - v. Vertical translation by -d commutes with every F_g. The intersection of K with the inverse image of K under this translation is nonempty, compact and forward invariant. Minimality makes it contain K. The global minimum and maximum heights of K then force d = 0. Thus each fibre has exactly one point. The projection from K to X is a continuous bijection from a compact space to a Hausdorff space, so its inverse is continuous. The second coordinate of that inverse is a continuous transfer psi.

Subtract psi(b) to normalize the transfer. On the dense orbit of b, the resulting phi(a(g,b)) equals c(g,b). Closedness of the scalar bound propagates the original constant C to all of X. This step avoids the weaker 2C estimate obtained by separately bounding two heights. Equality on that same dense orbit proves uniqueness. Conversely, evaluating the transfer equation at b immediately recovers the one-point bound.

Coronel, Navas and Ponce prove the broader invariant-section theorem for bounded isometric cocycles over minimal continuous semigroup dynamics. Real translations supply the mathematical provenance here. The normalized uniqueness, exact same-C estimate and compact Hausdorff interface are the explicit conclusions above, rather than a quotation of their metric-space statement. General CAT(0), Hilbert-valued, matrix and reflection-valued cocycles are outside this result.

For a compatible real cocycle over a minimal Z^k action, this criterion recovers a continuous coboundary from a joint all-elements bound. Petkovic's smooth simultaneous Diophantine stability conjecture supplies a related research problem. Establishing that bound and minimality for a chosen circle action, smooth regularity of the transfer, closed range and the conjectured classification remain separate questions. No smooth-conjecture resolution, recovery algorithm or originality is asserted.

## References

- Truth anchor: `D5/S1/Dynamics/OrbitClosure/BoundedRealCocycle.bounded_iff_existsUnique_transfer`
