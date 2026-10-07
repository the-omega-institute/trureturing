# Near Identity Generators and Nilpotence

## Abstract

A positive identity isolation gap in a normed ring representation forces the subgroup generated near one to be nilpotent.

**Theorem 1.1 (Contraction supplies the uniform commutator depth).**

$$\forall G \in Typeu,\; \forall R \in Typev,\; Group\left(G\right) \Rightarrow \left(NormedRingWithNormOne\left(R\right) \Rightarrow \left(\forall f \in GroupHom\left(G, Units\left(R\right)\right),\; \forall e \in Real,\; Gap\left(G, R, f, e\right) \Rightarrow Nilpotent\left(Generated\left(G, Near\left(G, R, f\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/GroupWords/NearIdentityNilpotence.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* FrenzyMath and upstream contributors (2026). *Poincare-Conjecture library prerequisites for hyperbolic rigidity*. URL: <https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a>.

*Commentary.*

G is any group and R any normed ring, in independent type universes. The ring norm is submultiplicative and its identity has norm one. The map f is a group homomorphism from G to the units of R. Gap(G,R,f,e) means that e is a positive real number and, for every g in G, norm(f(g)-one) less than e implies g=one. This is an actual isolation premise, not merely continuity or a chosen topology on G.

Near(G,R,f) consists of every g with norm(f(g)-one) at most 1/16. Generated(G,Near) is its actual subgroup closure inside G. Neither finite generation, normality of Near, nor completeness of R is required. Nilpotence and the uniform commutator depth are conclusions, not hypotheses.

For a unit u within 1/16 of one, rewrite its inverse as one minus (u-one) times its inverse. The triangle inequality and submultiplicativity bound the inverse norm by two. The normed ring commutator estimate then shows that commutation with a near generator contracts a near root's distance from one by at most one half. The new root stays within the same near region.

Induction on arbitrary lists bounds the iterated commutator norm by (1/2) to the list length times the initial root norm. Geometric convergence supplies one natural depth N with (1/2)^N/16 less than the given positive gap. Consequently every length-N list of near generators annihilates every near root. The uniform generator word criterion promotes this conclusion to nilpotence of the entire generated subgroup.

The isolation gap has to be proved for each application. This theorem does not construct a hyperbolic covering, a Lorentz representation or a geometric small displacement bound. It alone establishes neither virtual nilpotence of small displacement groups nor Mostow-Prasad rigidity.

## References

- Truth anchor: `D5/S3/Combinatorics/GroupWords/NearIdentityNilpotence.result`
- Dependency: [D5/S3/Combinatorics/GroupWords/UniformCommutatorNilpotence](UniformCommutatorNilpotence.md)
