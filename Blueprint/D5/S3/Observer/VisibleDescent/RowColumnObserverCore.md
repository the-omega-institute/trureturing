# Biextensional Observer Core

## Abstract

Quotienting equal evaluation rows and columns produces a canonical observer core that separates both state and protocol classes.

**Theorem 1.1 (The double quotient evaluation separates both carriers).**

$$\begin{aligned}\forall X, P, Lambda: \operatorname{Type},\\e: X \to \left(P \to Lambda\right),\\\operatorname{let} rhoX := \operatorname{ker}\left(e\right),\\rhoP := \operatorname{ker}\left(\operatorname{swap}\left(e\right)\right),\\eBar := \operatorname{QuotientLift2}\left(e, rhoX, rhoP\right) \operatorname{in}\\(\forall x: X, y: X, pi: P, sigma: P, rhoX\left(x, y\right) \Rightarrow rhoP\left(pi, sigma\right) \Rightarrow e\left(x, pi\right) = e\left(y, sigma\right)) \land\\(\forall u: \operatorname{Quotient}\left(rhoX\right), v: \operatorname{Quotient}\left(rhoX\right), u \neq v \Rightarrow \exists pBar: \operatorname{Quotient}\left(rhoP\right), eBar\left(u, pBar\right) \neq eBar\left(v, pBar\right)) \land\\(\forall u: \operatorname{Quotient}\left(rhoP\right), v: \operatorname{Quotient}\left(rhoP\right), u \neq v \Rightarrow \exists xBar: \operatorname{Quotient}\left(rhoX\right), eBar\left(xBar, u\right) \neq eBar\left(xBar, v\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/VisibleDescent/RowColumnObserverCore.row_column_observer_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state relation is the kernel of the curried evaluation, while the protocol relation is the kernel after swapping its two inputs. Thus the two quotients identify exactly duplicate rows and columns.

The displayed descended evaluation is Mathlib's canonical two-quotient lift. The representative-invariance clause supplies its defining compatibility and the lift retains the original evaluation on representative classes by construction.

If two state classes were not separated by any protocol class, their representative rows would agree and the classes would be equal. The same argument with the inputs exchanged separates distinct protocol classes. No finiteness or inhabitation assumption is required.

## References

- Truth anchor: `D5/S3/Observer/VisibleDescent/RowColumnObserverCore.row_column_observer_core`
