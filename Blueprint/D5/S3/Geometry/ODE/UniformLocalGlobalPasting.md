# Uniform local solutions and global pasting

## Abstract

A uniform two-sided local solution time yields one solution on all real time.

**Theorem 1.1 (One solution on the whole real time axis).**

Lean statement: `D5/S3/Geometry/ODE/UniformLocalGlobalPasting.exists_global_solution_of_uniform_local`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/ODE/UniformLocalGlobalPasting.exists_global_solution_of_uniform_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let E be any real normed vector space, f any map from E to E, and T a positive real number. Suppose that for every state x there is a curve C from the real numbers to E with C(0)=x and derivative f(C(s)) for every s in the open interval (-T,T). The same T must work for every state. Then for every initial state x0 there is one curve gamma on the whole real time axis with gamma(0)=x0 and derivative f(gamma(t)) at every real t.

Choose a local curve at each state and extend an existing curve at both endpoints of an expanding central interval. Preserve the old curve on that closed interval. At a joining time both one-sided derivatives equal the field evaluated at the common endpoint, so the enlarged curve remains a solution. Successive changes occur outside expanding central intervals. They form a locally finite family, yielding a locally eventual curve whose derivative and initial value agree with a sufficiently late stage.

The theorem requires neither completeness nor finite dimension of E, continuity of f, or uniqueness of local solutions. It assumes local solution witnesses with a common positive time interval. Obtaining those witnesses for a particular field, proving uniqueness, and analyzing asymptotic behavior require separate arguments.

## References

- Truth anchor: `D5/S3/Geometry/ODE/UniformLocalGlobalPasting.exists_global_solution_of_uniform_local`
