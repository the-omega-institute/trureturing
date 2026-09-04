# Hecke-Ostrowski Coboundary

## Abstract

The centered indicator of a fractional-part interval is an explicit finite coboundary for rotation by alpha.

**Theorem 1.1 (The interval discrepancy is an explicit coboundary).**

$$\forall \alpha, x \in \mathbb{R}, q \in \mathbb{N},\ \operatorname{if}(\operatorname{fract}(x) < \operatorname{fract}(q\alpha), 1, 0) - \operatorname{fract}(q\alpha) = \operatorname{transferFunction}(\alpha, q, x) - \operatorname{transferFunction}(\alpha, q, x+\alpha).$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/HeckeOstrowskiCoboundary.hecke_ostrowski_coboundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real alpha and x and natural q, the transfer function is the sum of fract(x - (j + 1) alpha) over j below q. The formula identifies the centered indicator of the interval from zero to fract(q alpha) with the transfer difference between x and x + alpha.

The escape lemma proves the exact two-branch formula for fract(x - t) from Int.fract_eq_iff. The finite transfer difference then telescopes to fract(x - q alpha) - fract(x).

No irrationality assumption on alpha is needed; the endpoint and q = 0 cases are included in the same identity.

## References

- Truth anchor: `D5/S1/Phase/HeckeOstrowskiCoboundary.hecke_ostrowski_coboundary`
