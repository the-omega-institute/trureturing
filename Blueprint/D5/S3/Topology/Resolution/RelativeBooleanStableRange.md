# Stable range of the relative Boolean lift

## Abstract

The actual relative Boolean lift has exactly the inverse-image stable range and carries the continuous core section equivariantly.

**Theorem 1.1 (Continuity, exact stable range and core action).**

$$\begin{aligned}\forall X: \operatorname{Type}\left(u\right), [\operatorname{TopologicalSpace}\left(X\right)]\\\forall f: X \to X, \forall hf: \operatorname{Continuous}\left(f\right),\\\operatorname{Continuous}\left(\operatorname{stableLift}\left(f, hf\right)\right) \land \operatorname{core}\left(\operatorname{stableLift}\left(f, hf\right)\right) = \operatorname{preimage}\left(\operatorname{projection}\left(\operatorname{core}\left(f\right)\right), \operatorname{core}\left(f\right)\right) \land\\\operatorname{Semiconj}\left(\operatorname{sectionC}\left(\operatorname{core}\left(f\right)\right), \operatorname{restriction}\left(f\right), \operatorname{stableLift}\left(f, hf\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/Resolution/RelativeBooleanStableRange.stable_lift_dynamics` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bernhard Banaschewski (1955). *Über nulldimensionale Räume*. DOI: [10.1002/mana.19550130302](https://doi.org/10.1002/mana.19550130302). URL: <https://doi.org/10.1002/mana.19550130302>.

*Commentary.*

K is the actual intersection of range(f^n) over all natural n, including zero. Forward invariance supplies the pair-map hypothesis. stableLift(f,hf) is literally lift(f,hf,mapsTo_core(f)) on Space(K). It uses the same graph closure, membership coordinates and projection as the topology module. Continuity follows from the constructed ambient pair map and its restriction.

For the forward inclusion in the stable-range equality, choose an upstairs n-step preimage and project it. The projection semiconjugacy, iterated with Mathlib's Semiconj.iterate_right, gives an n-step preimage downstairs. For the reverse inclusion, fix n and choose x with f^n(x)=projection(y). Take the actual graph point u=point(K,x). The n-step image of u projects to projection(y), which lies in K. The previously proved singleton fiber over that point therefore identifies this n-step image with y. This is a separate finite-n choice; no backward coherent orbit or ambient surjectivity is assumed.

Semiconj(s,r,g) means s(r(c))=g(s(c)). Here s=sectionC(K), r=StableRange.restriction(f), and g=stableLift(f,hf). The graph-agreement law lift_point gives this equation for the actual continuous section. Its homeomorphism onto the full inverse image of K, together with the stable-range equality, identifies the actual lifted core with K.

The displayed theorem needs only a topological X and continuous f. It includes empty X and K and all natural times. If X is additionally compact Hausdorff and K is zero-dimensional, is_closed_core proves K closed and functorial_resolution makes this same Space(K) compact Hausdorff with a clopen basis and continuous onto projection. compact_surjective_restriction supplies the compact onto source core system. No metric, countability, nonemptiness, positive-period, invertibility or global onto hypothesis is introduced.

This exact construction is a supplier for later period and finite-observation arguments. Those hypotheses and shadowing conclusions are not part of this theorem. The classical Stone/Banaschewski attribution applies to the underlying compactification; the stable-range proof is a repository derivation. Unrestricted Peng Question 5.1 remains outside this result.

## References

- Truth anchor: `D5/S3/Topology/Resolution/RelativeBooleanStableRange.stable_lift_dynamics`
- Dependency: [D5/S1/Dynamics/StableRange](../../../S1/Dynamics/StableRange.md)
- Dependency: [D5/S3/Topology/Resolution/RelativeBoolean](RelativeBoolean.md)
