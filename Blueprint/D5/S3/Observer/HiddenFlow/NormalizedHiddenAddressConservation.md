# Normalized Hidden-Address Conservation

## Abstract

Normalized streamline addresses are conserved on connected time segments.

**Theorem 1.1 (Connected streamline segments conserve their hidden address).**

$$\begin{gathered}\forall x: \operatorname{Continuous}(\mathbb{R} \to \Sigma_{\infty}),\\{}(\exists! (a, k): \operatorname{ContinuousMaps}(\mathbb{R}, \mathbb{R}) \times \ker(\pi), a(0) = \operatorname{base}(x(0)) \land (\forall t, x(t) = \operatorname{realFlow}(a(t)) + k) \land \forall I, \operatorname{IsPreconnected}(I), \forall t_{0}, t_{1}\in I, k_{x}(t_{0}) = k_{x}(t_{1})) \land\\{}(\forall a, \kappa, I, t_{0}, t_{1}, (a(0) = \operatorname{base}(x(0)) \land \operatorname{IsPreconnected}(I) \land t_{0}, t_{1}\in I \land (\forall t\in I, x(t) = \operatorname{realFlow}(a(t)) + \kappa(t)) \land \kappa(t_{0}) \neq \kappa(t_{1})) \Rightarrow \neg\operatorname{ContinuousOn}(\kappa, I)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HiddenFlow/NormalizedHiddenAddressConservation.normalized_streamline_hidden_address_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A continuous universal-solenoid history has unique normalized streamline data: a continuous real lift fixed by the repository's base representative and a hidden kernel coordinate.

The canonical hidden coordinate is constant at any two times in every preconnected segment. This applies the imported normalized streamline construction and its throat-component computation.

The second public clause treats an arbitrary proposed hidden offset under the same normalized visible lift. If it gives different addresses at two times in a preconnected segment, the imported nonconstant-offset theorem rules out continuity on that segment.

The earlier conditional streamline theorem explicitly left normalized existence and canonicity open. The imported family construction supplies those obligations here, so this module contributes only the bridge joining construction, conservation, and obstruction.

## References

- Truth anchor: `D5/S3/Observer/HiddenFlow/NormalizedHiddenAddressConservation.normalized_streamline_hidden_address_conservation`
- Dependency: [D5/S3/Observer/HiddenFlow/StreamlineExistence](StreamlineExistence.md)
