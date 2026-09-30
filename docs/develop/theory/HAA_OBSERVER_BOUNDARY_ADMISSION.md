# HAA Observer-Boundary Admission

## Status

This document is a research and formalization seed. Its propositions below are
proved from the displayed definitions. It does not claim a Lean-checked result,
a new registration, or closure of any open atom.

## Definition 1. Boundary-indexed admissible observation

Let (X) be a type of states, (R) a type of observations, and (A) a
type of admissibility certificates. An HAA observation is a tuple

[
h=(x,r,a)
]

with (x:X), (r:R), (a:A). Let

[
mathsf{law}:X	o R	o A	omathsf{Prop}
]

be the source-law predicate. Define

[
mathsf{Admit}(h)Longleftrightarrow
mathsf{law}(h.x,h.r,h.a).
]

The certificate is part of the observation boundary: two equal readouts with
different certificates are distinct HAA observations.

## Definition 2. Consumer-relative continuation

Let (C) be a type of consumers and

[
mathsf{use}:C	o X	o R	omathsf{Prop}.
]

A continuation (k:C	o X	o R	o R) is lawful at (h) when

[
mathsf{Admit}(h)land
mathsf{use}(c,h.x,h.r)
Longrightarrow
mathsf{Admit}(h.x,h.r,h.a)
]

and the next readout is (k(c,h.x,h.r)). Thus a continuation is not
authorized by a producer alone; it is authorized only relative to a consumer
and an admissible boundary certificate.

## Proposition 3. Fail-closed continuation

If (
egmathsf{Admit}(h)), then no lawful continuation can be derived from
Definition 2.

**Proof.** The antecedent of the lawful-continuation implication contains
(mathsf{Admit}(h)). Therefore Definition 2 supplies no continuation
witness when the boundary certificate is inadmissible. Treating this case as an
empty but successful continuation would add a premise not present in the
definition. (square)

## Theorem 4. Boundary monotonicity

Suppose (h_1=(x,r_1,a_1)) and (h_2=(x,r_2,a_2)) satisfy

[
mathsf{Admit}(h_1),quad mathsf{Admit}(h_2),quad
r_1=r_2,quad a_1=a_2.
]

Then any consumer-relative continuation has identical enabledness at (h_1)
and (h_2).

**Proof.** The hypotheses identify the complete boundary tuple used by
(mathsf{use}) and (mathsf{law}): state, readout, and certificate. Hence
each occurrence of (mathsf{Admit}) and (mathsf{use}) has the same truth
value for the two tuples. The continuation implication therefore has the same
enabledness. (square)

## Proposition 5. Why producer and consumer edges cannot be inverted

There are models in which an artifact is consumed by (c) while its producer
certificate is absent. In such a model, the consumer edge may be recorded, but
Definition 2 cannot derive a lawful continuation.

**Witness.** Take (X={x}), (R={r}), (A={0,1}), set
(mathsf{law}(x,r,0)) true and (mathsf{law}(x,r,1)) false, and let (c)
consume ((x,r)) with certificate (1). The consumer relation exists, but
(mathsf{Admit}(x,r,1)) is false, so Proposition 3 applies.

## Research consequence

HAA's smallest useful unit is therefore not a standalone theorem or a
standalone history edge. It is the quadruple

[
(	ext{source law},	ext{boundary certificate},	ext{consumer},	ext{continuation}).
]

A future Lean bridge should expose these four components as separate fields and
prove the fail-closed lemma before attempting any circulation, probability-lift,
or registration theorem. This is a research direction, not a claim that the
bridge already compiles.
