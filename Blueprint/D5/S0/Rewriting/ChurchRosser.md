# Church-Rosser Equivalence

## Abstract

Global confluence is equivalent to the Church-Rosser characterization that convertibility is exactly joinability.

**Theorem 1.1 (Confluence iff convertibility is joinability).**

$$\begin{aligned}
&\left(\forall h,a,b,\;\operatorname{ReflTransGen}(r)(h,a)\land\operatorname{ReflTransGen}(r)(h,b)\Rightarrow\\
&\qquad\exists c,\;\operatorname{ReflTransGen}(r)(a,c)\land\operatorname{ReflTransGen}(r)(b,c)\right)\\
&\quad\Longleftrightarrow\quad
\left(\forall a,b,\;\operatorname{EqvGen}(r)(a,b)\Longleftrightarrow
\operatorname{Join}(\operatorname{ReflTransGen}(r))(a,b)\right).
\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/ChurchRosser.confluent_iff_church_rosser` (`✓ std3`). ∎

**Theorem 1.2 (Newman to Church-Rosser).**

Termination of `r` together with local confluence implies
`EqvGen(r)(a,b) ↔ Join(ReflTransGen(r))(a,b)` for every `a,b`.

*Proof.* This is the composition of Theorem 1.1 with the frozen
`D5/S0/Rewriting/NewmanConfluence.newman_confluent` theorem. ∎

**Theorem 1.3 (Mathlib sufficient route).**

Mathlib's ReflGen/ReflTransGen diamond condition implies global confluence;
it is a sufficient condition rather than the biconditional above.

*Proof.* Machine-checked as `D5/S0/Rewriting/ChurchRosser.mathlib_church_rosser_confluent`,
using `Relation.church_rosser`. ∎

## Commentary

The forward proof sends every reflexive-transitive reduction into `EqvGen`,
uses `Relation.equivalence_join` to obtain the equivalence structure on
joinability, and eliminates the equivalence closure by its rel/refl/symm/trans
constructors. For the reverse direction, two reductions from a common source
give a convertibility path through that source. The generic equivalence needs no
termination hypothesis.

## References

- Truth anchor: `D5/S0/Rewriting/ChurchRosser.confluent_iff_church_rosser`
- Newman corollary: `D5/S0/Rewriting/ChurchRosser.newman_church_rosser`
- Dependency: `D5/S0/Rewriting/NewmanConfluence`
- Mathlib anchor: `Mathlib.Logic.Relation`
