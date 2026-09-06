# Conditional Streamline Rigidity

## Abstract

For a supplied solenoid decomposition, the throat offset is continuous exactly when it is constant.

**Theorem 1.1 (The throat component reconstructs the supplied path).**

$$\forall t\in\mathbb{R},\ \gamma_d(t)=v_d(t)+e_d(c_d(t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/StreamlineTheorem.path_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let d be a supplied StreamlineDecomposition, with path gamma_d, visible lift v_d, and hidden-kernel identification e_d. Applying that identification to its throat component c_d recovers the pointwise difference between the path and its visible lift. This reconstruction requires no continuity hypothesis.

**Theorem 1.2 (A supplied decomposition has a rigid throat offset).**

$$\operatorname{IsPreconnected}(I) \land t_0 \in I \Rightarrow\ \operatorname{ContinuousOn}(c_d, I) \Leftrightarrow \forall t\in I,\ c_d(t) = c_d(t_0)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/StreamlineTheorem.streamline_offset_continuous_iff_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem takes a StreamlineDecomposition as explicit input. It contains a solenoid-valued history, a chosen visible lift with the same visible projection, and an additive identification of the hidden kernel with the product of all prime-adic integer addresses. Their pointwise difference is the supplied decomposition's throat component, and path_decomposition gives its pointwise reconstruction.

On a preconnected real interval, the supplied throat component is continuous if and only if it agrees everywhere with its value at a chosen base point. The forward implication directly applies the frozen hidden-fiber rigidity theorem; the reverse implication is continuity of a constant map.

Residual: this result does not construct a decomposition from an arbitrary continuous solenoid path, choose a canonical visible projection lift, or prove such a choice is canonical. Those existence and canonicity obligations remain open rather than being inferred from the conditional rigidity statement.

**Theorem 1.3 (A changing hidden address is not continuous).**

$$\operatorname{IsPreconnected}(I) \land x, y\in I,\quad k(x) \neq k(y) \Rightarrow \neg\operatorname{ContinuousOn}(k, I)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/StreamlineTheorem.nonconstant_offset_not_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If two times in the connected interval carry different hidden addresses, continuity would force those values to agree. The explicit contradiction is the negative witness excluding a nonconstant candidate throat history.

## References

- Truth anchor: `D5/S3/Observer/StreamlineTheorem.nonconstant_offset_not_continuous`
- Truth anchor: `D5/S3/Observer/StreamlineTheorem.path_decomposition`
- Truth anchor: `D5/S3/Observer/StreamlineTheorem.streamline_offset_continuous_iff_constant`
- Dependency: [D5/S1/Dynamics/UniversalSolenoid](../../S1/Dynamics/UniversalSolenoid.md)
- Dependency: [D5/S3/Arith/HiddenFiberRigidity](../Arith/HiddenFiberRigidity.md)
