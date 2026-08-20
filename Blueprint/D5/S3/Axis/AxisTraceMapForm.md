# Axis Trace Map Form

## Abstract

The four dimensional trace map has the stated form and carries the axis orbit.

The two axis recurrences can be read as a single map on four coordinates: the last two partial sums together with the last two weights. One step of that map produces the next sum, shifts the previous one, multiplies the two weights, and shifts the previous weight.

The orbit statement was already available, but it holds of whatever the map happens to be defined as. Pinning the four coordinates makes the definition checkable against the source line, which is why the form is a conjunct here rather than a comment.

The source also records that the orbit converges doubly exponentially, backed there by a numerical certificate rather than an argument. That half is not claimed.

**Lemma 1.1 (The map has the stated four coordinates).**

$$\operatorname{F}\left(\mathit{w1}, \mathit{w0}, \mathit{t1}, \mathit{t0}\right) = \operatorname{tuple}\left(\mathit{w1} + \mathit{t1} \cdot \mathit{t0} \cdot \mathit{w0}, \mathit{w1}, \mathit{t1} \cdot \mathit{t0}, \mathit{t1}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisTraceMapForm.orbitMap_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coordinate by coordinate against the source line. Changing any one of them makes the module fail to build, so the statement is bound to the definition rather than describing it.

**Theorem 1.2 (The trace map clause packaged).**

$$\operatorname{F}\left(\mathit{w1}, \mathit{w0}, \mathit{t1}, \mathit{t0}\right) = \operatorname{tuple}\left(\mathit{w1} + \mathit{t1} \cdot \mathit{t0} \cdot \mathit{w0}, \mathit{w1}, \mathit{t1} \cdot \mathit{t0}, \mathit{t1}\right) \land \left(\operatorname{F}\left(\operatorname{state}\left(K\right)\right) = \operatorname{state}\left(K + 1\right) \land \operatorname{state}\left(K\right) = \operatorname{iterate}\left(\operatorname{F}\left(K\right), \operatorname{state}\left(0\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Axis/AxisTraceMapForm.axis_trace_map_form_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One conjunction: the map has the stated coordinates, it carries the axis state one depth forward, and every state is an iterate of the initial one. Convergence is not among the conjuncts.

## References

- Truth anchor: `D5/S3/Axis/AxisTraceMapForm.axis_trace_map_form_package`
- Truth anchor: `D5/S3/Axis/AxisTraceMapForm.orbitMap_form`
