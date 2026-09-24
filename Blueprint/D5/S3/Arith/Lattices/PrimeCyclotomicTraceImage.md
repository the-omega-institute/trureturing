# Integral Image of the Prime-Cyclotomic Trace Template

## Abstract

The real prime-cyclotomic trace Gram template has an exact integral-image criterion and a unique, explicitly reconstructed integer preimage.

**Definition 1.1 (Actual integer matrix action).**

Lean statement: `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.traceGram`

*Formalization.* `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.traceGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n>=0 write an integer vector as (x0,x), with x indexed by Fin n, and put m=2*n+3. The zeroth output is (n+1)*x0-sum(x); the ith output is m*x(i)-x0-2*sum(x). At a prime m this is the trace Gram matrix of the real m-cyclotomic field. CTG.3 also identifies it with the complete nontrivial p-power tower when m=p^k, including composite m. The definition makes no primality assumption and includes n=0.

**Definition 1.2 (Integer-division reconstruction).**

Lean statement: `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.reconstruct`

*Formalization.* `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.reconstruct` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For y=(y0,y), set z(i)=(y(i)-2*y0)/(2*n+3), using integer division. The reconstructed zeroth coordinate is y0+sum(z), and the ith coordinate is y0+sum(z)+z(i). This is a specified integer vector for every y. The theorem gives exactly the domain on which it is a correct preimage.

**Theorem 1.3 (Exact image and unique constructive inverse).**

$$\forall n \in Nat, \forall y \in \operatorname{Prod}(Int, \operatorname{Function}(\operatorname{Fin}(n), Int)), \operatorname{Iff}(\forall i \in \operatorname{Fin}(n), \operatorname{Dvd}(\operatorname{add}(\operatorname{mul}(2, \operatorname{NatCastInt}(n)), 3), \operatorname{sub}(\operatorname{apply}(\operatorname{snd}(y), i), \operatorname{mul}(2, \operatorname{fst}(y)))), \operatorname{And}(\operatorname{Eq}(\operatorname{traceGram}(n, \operatorname{reconstruct}(n, y)), y), \forall x \in \operatorname{Prod}(Int, \operatorname{Function}(\operatorname{Fin}(n), Int)), \operatorname{Implies}(\operatorname{Eq}(\operatorname{traceGram}(n, x), y), \operatorname{Eq}(x, \operatorname{reconstruct}(n, y)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.integral_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural n and every y in Z x (Fin n -> Z), all differences y(i)-2*y0 are divisible by 2*n+3 exactly when the displayed reconstruction maps to y and every integer preimage equals that reconstruction. Neither an inverse matrix nor a determinant nor a trace-dual basis is supplied as a theorem hypothesis.

The proof derives the coordinate difference identity output(i)-2*output(0)=(2*n+3)*(x(i)-x0). Divisibility therefore determines all differences in a preimage. The zeroth row then determines x0; substitution proves existence, and cancellation by the positive integer 2*n+3 proves uniqueness. The reverse implication reads the same difference identity at the reconstructed vector.

STL.4 identifies the prime-layer coefficient lattice; CTG.3 uses the same template at n=(p^k-3)/2 for the full tower. The product-algebra trace identification and the inter-packet gluing are ordinary proofs in the existing WSS dossier. This formal arithmetic theorem does not construct a golden ring-class character or decide an unknown WSS prime.

Ambient Maass construction and normalization: `D5/L/tanaka2026maass`. CTG retains an existing character and proves the full tower's congruence module Z/p^k. A normalized integral trace combination attains depth k; no primitive vector in that same lattice attains k+1. These are ordinary results, not extra Lean conclusions or an independent WSS witness.

Frontier comparison and the holomorphic weight restriction: `D5/L/fretwellroberts2026eisenstein`. Its weight-at-least-three existence results are not used for the weight-zero family or for the integer-image criterion proved here.

Single-prime reconstruction and its classical inputs: `D5/L/tanaka2026maass`. HCR.1-HCR.5 proves ordinary reconstruction within one existing primitive packet from the first d coefficients at powers of a generator-rotation auxiliary prime. A non-generator of order p^s observes exactly a relative trace and leaves kernel dimension d-d_s. The reciprocal numerator and integer completion do not construct the global golden character from an arbitrary finite prefix.

HCR.6 is an ordinary consumer of this precise integer-image theorem. For a first-layer single-prime prefix y_j, the change of basis D_j=P_j-P_(j-2) converts the displayed trace-image criterion into y_j=(j+1)*y_0 modulo p. No new wrapper declaration or additional kernel theorem is introduced by that application.

Task-relative state completion and the original lift: `D5/L/katz2015goldeninterfaces`. SJC in the same WSS owner uses the repository's contextual spacetime query-sufficiency criterion. The actual norm-one square-level update has phase and Lie coordinates (j,z)->(j+1,z-q_p); two exact delayed traces recover the finite-ring state. These ordinary proofs retain the fixed golden polynomial and actual q_p. They are not conclusions of integral_image, do not identify characteristic p^2 with dual numbers, and do not prove a new WSS prime-family decision.

Actual split-block depths and the solved exponential input: `D5/L/bugeaud2006lebesguenagell`. TBN and DCE in the existing WSS owner identify every prime exponent in L_(3^j)^2+3 with its original h_p, then use the cited no-perfect-power theorem to prove that those depths have gcd one. A covering with all depths at least H>=2 therefore has multiplicity at least 2H+1; equality has exactly two depths H,H+1. This is related ordinary number theory, not a proof dependency or new conclusion of integral_image. Mixed depths such as2,3 remain possible; no WSS example or kernel certificate is introduced by this source reference.

Golden prime clocks and cross-block reciprocity: `D5/L/renault2013periodrankorder`. GPC in the existing WSS owner distinguishes the order of phi^2, the Fibonacci zero rank and the pair period. Its exact identity pi(B_j^a)=2*r_j*B_j^(a-1) allows either initial-depth branch at a factor. The interlevel identity and quadratic reciprocity impose joint conditions on actual depths. A unique odd-depth factor of a later block must split at all earlier-prime quadratic characters. Positive density of the unrestricted comparison classes omits the exact Fibonacci period and does not create a WSS witness. These are ordinary related results, not additional conclusions or proof dependencies of integral_image.

## References

- Truth anchor: `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.integral_image`
- Truth anchor: `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.reconstruct`
- Truth anchor: `D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage.traceGram`
