# Atomic prefixes, shifted hinges and exponential energy

## Abstract

Zero-mass finite complex atoms have an exact shifted hinge representation, an integrable prefix correlation, and a quantitative exponential energy bound.

Let I be any finite index type in any universe, x:I to R any real nodes, and a:I to C any complex coefficients. All integrals use Lebesgue measure. Empty index types, repeated nodes, coincident nodes and arbitrary orderings are included. Write F(v)=prefix(x,a,v), E=integral over R of norm(F(v)) squared, C(s)=integral over R of conjugate(F(v+s)) times F(v), and H(s)=sum over i,j of conjugate(a(i)) a(j) max(x(i)-x(j)-s,0), with real scalars embedded in C.

The finite atomic prefix argument is drawn from the existing AURIC treatment of prime-power difference coupling, finite-codimension positivity and the root-scale Robin budget, Section 5, Theorem 2. The identities here concern the finite atomic and exponential components of that argument.

**Definition 1.1 (The cumulative atomic mass).**

Lean statement: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.prefix`

*Formalization.* `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.prefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every finite I, x:I to R, a:I to C and real t, prefix(x,a,t) is the sum over all i of a(i) when x(i)<=t and zero otherwise. The endpoint is included. This definition imposes no zero-mass condition. Under sum_i a(i)=0 the prefix vanishes below all nodes and at or above all nodes; for an empty family it is identically zero.

**Theorem 1.2 (The exact shifted hinge identity and energy estimate).**

Lean statement: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.shifted_hinge_prefix_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.shifted_hinge_prefix_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite I, arbitrary x:I to R and a:I to C with sum_i a(i)=0, and every real shift s, the function v to conjugate(F(v+s)) F(v) is integrable, the real function v to norm(F(v)) squared is integrable, H(s)=-C(s), and norm(H(s))<=E. These are all four conclusions. A common upper cutoff rewrites the zero-mass prefix as a finite sum of bounded interval indicators. Integrating their overlaps gives the hinge identity, with the common affine tail canceled by zero mass. At s=0 this also gives square integrability. Translation invariance and 2AB<=A squared+B squared bound the correlation by E without assuming square integrability as a premise.

**Theorem 1.3 (The exact finite-window exponential hinge formula).**

Lean statement: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.finite_window_exponential_hinge`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.finite_window_exponential_hinge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real lam,D,t with lam>0, D>=0 and abs(t)<=D, s to max(t-s,0) exp(-lam abs(s)) is integrable on [-D,D], and exp(-lam abs(t))=exp(-lam D)+lam exp(-lam D)(t+D)+lam squared times the integral from -D to D of max(t-s,0) exp(-lam abs(s)) minus 2 lam max(t,0). Splitting the interval at t and, when needed, at zero reduces the calculation to an affine function times an exponential. The hypotheses include D=0, in which case t=0 and the integral is zero.

**Theorem 1.4 (The exact exponential quadratic energy identity).**

Lean statement: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.exponential_prefix_energy`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.exponential_prefix_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite I, x:I to R, a:I to C with sum_i a(i)=0, and real lam,D with lam>0, D>=0 and abs(x(i)-x(j))<=D for every i,j, the following five conclusions hold: norm(F) squared is integrable on R; each translated correlation integrand is integrable on R for every real shift; C is continuous; s to exp(-lam abs(s)) C(s) is integrable on [-D,D]; and Q=2 lam E-lam squared times the integral from -D to D of exp(-lam abs(s)) C(s), where Q=sum over i,j of conjugate(a(i)) a(j) exp(-lam abs(x(i)-x(j))). This is an identity in C, with E and the real coefficients embedded in C. Continuity and window integrability follow from the finite hinge expression for C. Applying the scalar finite-window formula at each difference x(i)-x(j), summing the finite integrable terms, and canceling the constant and affine terms by zero mass yields the identity. The diameter condition requires no specified origin for the nodes.

**Theorem 1.5 (The exponential coercivity constant).**

Lean statement: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.exponential_prefix_coercivity`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.exponential_prefix_coercivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite I, x:I to R, a:I to C with sum_i a(i)=0, and real lam,D with lam>0, D>=0 and abs(x(i)-x(j))<=D for every i,j, 2 lam exp(-lam D) E<=Re(Q), with F,E,C,H and Q as above. Indeed Re(C(s))<=norm(C(s))<=E, and the exact integral of exp(-lam abs(s)) on [-D,D] is 2(1-exp(-lam D))/lam. Taking real parts in the energy identity gives the stated constant. Empty families and D=0 are included. Repeated nodes may cancel completely, giving E=Q=0; the lower bound is strictly positive whenever E>0.

## References

- Truth anchor: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.exponential_prefix_coercivity`
- Truth anchor: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.exponential_prefix_energy`
- Truth anchor: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.finite_window_exponential_hinge`
- Truth anchor: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.prefix`
- Truth anchor: `D5/S3/Analytic/Interpolation/AtomicPrefixEnergy.shifted_hinge_prefix_energy`
