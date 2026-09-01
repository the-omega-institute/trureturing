# Golden Observer Events and Null Directions

## Abstract

Golden observer events and their genuine tangents recover two fixed null directions.

**Theorem 1.1 (Observer events and tangents recover the golden null basis).**

$$let uPlus = \operatorname{pair}\left(\varphi, 1\right);\\let uMinus = \operatorname{pair}\left(\varphi', 1\right);\\let Q(w) = \operatorname{fst}\left(w\right)^{2} - \operatorname{fst}\left(w\right) \cdot \operatorname{snd}\left(w\right) - \operatorname{snd}\left(w\right)^{2};\\let \operatorname{h}\left(eta\right) = \operatorname{pair}\left(\frac{\operatorname{exp}\left(eta\right) \cdot \varphi - \operatorname{exp}\left(-eta\right) \cdot \varphi'}{\operatorname{sqrt}\left(5\right)}, \frac{\operatorname{exp}\left(eta\right) - \operatorname{exp}\left(-eta\right)}{\operatorname{sqrt}\left(5\right)}\right);\\let \operatorname{tangent}\left(eta\right) = \operatorname{pair}\left(\frac{\operatorname{exp}\left(eta\right) \cdot \varphi + \operatorname{exp}\left(-eta\right) \cdot \varphi'}{\operatorname{sqrt}\left(5\right)}, \frac{\operatorname{exp}\left(eta\right) + \operatorname{exp}\left(-eta\right)}{\operatorname{sqrt}\left(5\right)}\right);\\\left(\left({\forall v\in \operatorname{Prod}\left(\operatorname{Real}\left(\right), \operatorname{Real}\left(\right)\right),\ \exists ! a, b\in \operatorname{Real}\left(\right),\ v = a \cdot uPlus + b \cdot uMinus} \land \left(\forall a \in \operatorname{Real}\left(\right), b \in \operatorname{Real}\left(\right),\; Q\left(a \cdot uPlus + b \cdot uMinus\right) = -5 \cdot a \cdot b\right)\right) \land \left(Q\left(uPlus\right) = 0 \land Q\left(uMinus\right) = 0\right)\right) \land \left(\forall eta \in \operatorname{Real}\left(\right),\; \left(\left(\left(\left(\left(\left(\operatorname{h}\left(eta\right) = \frac{\operatorname{exp}\left(eta\right)}{\operatorname{sqrt}\left(5\right)} \cdot uPlus + -\frac{\operatorname{exp}\left(-eta\right)}{\operatorname{sqrt}\left(5\right)} \cdot uMinus \land \operatorname{tangent}\left(eta\right) = \frac{\operatorname{exp}\left(eta\right)}{\operatorname{sqrt}\left(5\right)} \cdot uPlus + \frac{\operatorname{exp}\left(-eta\right)}{\operatorname{sqrt}\left(5\right)} \cdot uMinus\right) \land \operatorname{HasDerivAt}\left(h, \operatorname{tangent}\left(eta\right), eta\right)\right) \land Q\left(\operatorname{h}\left(eta\right)\right) = 1\right) \land \operatorname{h}\left(eta\right) + \operatorname{tangent}\left(eta\right) = \frac{2 \cdot \operatorname{exp}\left(eta\right)}{\operatorname{sqrt}\left(5\right)} \cdot uPlus\right) \land \operatorname{tangent}\left(eta\right) - \operatorname{h}\left(eta\right) = \frac{2 \cdot \operatorname{exp}\left(-eta\right)}{\operatorname{sqrt}\left(5\right)} \cdot uMinus\right) \land 0 < \frac{2 \cdot \operatorname{exp}\left(eta\right)}{\operatorname{sqrt}\left(5\right)}\right) \land 0 < \frac{2 \cdot \operatorname{exp}\left(-eta\right)}{\operatorname{sqrt}\left(5\right)}\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/HyperbolicTransport/ObserverEventNullDirections.golden_observer_event_null_directions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two vectors (phi,1) and (phi-prime,1) form a basis of the real plane. Every vector therefore has unique coefficients in this basis, and the golden Lorentz form of a combination is exactly -5ab.

The displayed event and tangent are defined from positive exponential amplitudes divided by sqrt(5). The proof establishes sqrt(5)>0 internally, differentiates both event coordinates, and proves that the event remains on the unit Lorentz hyperbola.

Adding the tangent to the event cancels the conjugate direction; subtracting the event from the tangent cancels the future direction. The remaining amplitudes are strictly positive for every rapidity.

At zero rapidity all eight event laws give a concrete satisfying witness. Replacing the genuine tangent there by the zero vector falsifies the future-null identity, so the derivative clauses are not vacuous.

## References

- Truth anchor: `D5/S3/Observer/HyperbolicTransport/ObserverEventNullDirections.golden_observer_event_null_directions`
