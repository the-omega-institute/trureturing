# Boundary-preserving spectral insertion and deletion

## Abstract

Actual extremal observers transfer spectral bounds across dimensions.

**Definition 1.1 (Extremal positions).**

$$\forall(n:\mathbb{N}),(\forall(q:Fin\left(9\right)),(boundaryIndex\left(n, q\right)=if\left(q<3, q, n + q\right)))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A vector of length n+9 has boundary positions q for q<3 and n+q for q>=3. These are its top three and bottom six entries, including ties. The parameter n counts middle coordinates. The displayed indices denote their natural values in Fin (n+9).

**Definition 1.2 (Boundary observation).**

$$\forall(n:\mathbb{N}),(\forall(l:Fin\left(n + 9\right)\to \mathbb{R}),(\forall(q:Fin\left(9\right)),(boundaryValues\left(n, l, q\right)=l\left(boundaryIndex\left(n, q\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observation retains the three largest and six smallest coordinates. It does not observe the middle coordinates separately. K1 and K2 are the existing real symmetric three-by-three boundary pencils of QutritSpectralReduction.

**Definition 1.3 (Dimension-dependent purity value).**

$$\forall(N:\mathbb{N}),(purityBound\left(N\right)=\frac{N + 8}{(N + 2)^{2}})$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.purityBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Natural dimensions are cast to the reals before division. The candidate value is f(N)=(N+8)/(N+2)^2.

**Definition 1.4 (A bound for the rank-three relaxation).**

$$\forall(n:\mathbb{N}),(SpectralBound\left(n\right)\iff\forall(l:Fin\left(n + 9\right)\to \mathbb{R}),(((Antitone\left(l\right))\land(\forall(i:Fin\left(n + 9\right)),(0\leq l\left(i\right)))\land(\sum_{i:Fin\left(n + 9\right)}(l\left(i\right))=1)\land(PosSemidef\left(K1\left(boundaryValues\left(n, l\right)\right)\right))\land(PosSemidef\left(K2\left(boundaryValues\left(n, l\right)\right)\right)))\Rightarrow(\sum_{i:Fin\left(n + 9\right)}((l\left(i\right))^{2})\leq purityBound\left(n + 9\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.SpectralBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

SpectralBound n is the universal square-sum upper bound for all antitone nonnegative mass-one vectors of length n+9 whose two boundary pencils are positive semidefinite. This is a spectral relaxation; no sufficiency assertion for literal APPT is included.

**Definition 1.5 (Actual extremal coordinate indices).**

$$\forall(p:\mathbb{N}),(\forall(q:\mathbb{N}),(\forall(N:\mathbb{N}),((p + q\leq N)\Rightarrow(\forall(i:Fin\left(p + q\right)),(observerIndex\left(p, q, N, i\right)=if\left(i<p, i, N - \left(p + q\right) + i\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.observerIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For p+q<=N, this index selects the actual first p and last q coordinates, in that order. The subtraction is on natural indices under the displayed size hypothesis. It does not discard ties or require strict ordering.

**Definition 1.6 (The top and bottom observation).**

$$\forall(p:\mathbb{N}),(\forall(q:\mathbb{N}),(\forall(N:\mathbb{N}),((p + q\leq N)\Rightarrow(\forall(l:Fin\left(N\right)\to \mathbb{R}),(observerValues\left(p, q, N, l\right)=compose\left(l, observerIndex\left(p, q, N\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.observerValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The observer is the original extremal tuple, indexed by Fin(p+q). Its proof argument records p+q<=N. Positive division commutes with observation.

**Definition 1.7 (Faithful positive normalization).**

$$PositiveScaleInvariant\left(C\right)\iff\forall(b:Fin\left(d\right)\to \mathbb{R}),(\forall(s:\mathbb{R}),((0<s)\Rightarrow(C\left(divide\left(b, s\right)\right)\iff C\left(b\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.PositiveScaleInvariant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The boundary condition is preserved in both directions by division by every positive real mass. This is a hypothesis of the shared theorem, separately established for each concrete boundary condition.

**Definition 1.8 (A universal bound for an extremal observer).**

$$ObserverBound\left(p, q, C, N\right)\iff(p + q\leq N)\Rightarrow(\forall(l:Fin\left(N\right)\to \mathbb{R}),(((Antitone\left(l\right))\land(\forall(i:Fin\left(N\right)),(0\leq l\left(i\right)))\land(\sum_{i:Fin\left(N\right)}(l\left(i\right))=1)\land(C\left(observerValues\left(p, q, N, l\right)\right)))\Rightarrow(\sum_{i:Fin\left(N\right)}((l\left(i\right))^{2})\leq purityBound\left(N\right))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.ObserverBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every antitone, nonnegative, mass-one spectrum whose actual top-p/bottom-q observer satisfies C has the stated purity bound. The size-proof quantifier is explicit in Lean; at dimensions below p+q this predicate carries no conclusion about spectra.

**Theorem 1.9 (Transfer through the actual unobserved coordinate).**

$$\forall(p:\mathbb{N}),(\forall(q:\mathbb{N}),(\forall(n:\mathbb{N}),(\forall(a:\mathbb{N}),(\forall(N:\mathbb{N}),(\forall(C:Fin\left(p + q\right)\to \mathbb{R}\to Prop),(\forall(kappa:\mathbb{R}),(((N=p + q + n + 1)\land(10\leq N)\land(1\leq a)\land(PositiveScaleInvariant\left(C\right))\land(1<N - kappa)\land(0\leq multiply\left(10 - kappa, (N)^{2}\right) + multiply\left(6 - multiply\left(15, kappa\right), N\right) - multiply\left(20, kappa\right) - 16)\land(\forall(l:Fin\left(N\right)\to \mathbb{R}),(((Antitone\left(l\right))\land(\forall(i:Fin\left(N\right)),(0\leq l\left(i\right)))\land(\sum_{i:Fin\left(N\right)}(l\left(i\right))=1)\land(C\left(observerValues\left(p, q, N, l\right)\right)))\Rightarrow(multiply\left(N - kappa, l\left(N - q - 1\right)\right)\leq 1))))\Rightarrow((ObserverBound\left(p, q, C, N - 1\right))\Rightarrow((ObserverBound\left(p, q, C, N + a\right))\Rightarrow(ObserverBound\left(p, q, C, N\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.observer_bound_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here N=p+q+n+1, with N>=10 and a>=1. Kappa is real, and guard(N,kappa)=(10-kappa)N^2+(6-15kappa)N-20kappa-16 must be nonnegative, with N-kappa>1. The cap is required for every feasible spectrum at the current dimension. The actual coordinate j=N-q-1 has value t. Inserting a actual copies immediately before j preserves the observed entries, weak order and nonnegativity, with exact mass 1+a*t and squared mass P+a*t^2. Deleting exactly the original coordinate j preserves the observer, with exact mass 1-t and squared mass P-t^2. Both masses are positive in their respective scalar branches. Normalization then uses the same boundary predicate C. The insertion branch uses t<=1/(N+2); the deletion branch uses the opposite inequality and the full guard. No assertion for arbitrary observers without the cap and guards is included. If bottom-q mass is at least top-p mass, order and total mass give (N+p-q)t<=1, so kappa=q-p is a real difference, without saturated natural subtraction. The rank-three specialization p=3,q=6 derives this balance from K1 and retains its original complete theorem and length-twenty application. For the augmented rank-four observer p=6,q=10, select positions 0,1,2,10,11,12,13,14,15 to obtain exactly the original K1 and K2, and additionally impose L4=bottom-ten mass minus top-six mass>=0. The selection commutes with positive division, and L4 scales by the same positive factor. These are exactly the two original pencils and this one balance inequality, with no extra LMIs or rank restrictions. This balance gives (N-4)t<=1 with actual t=l[N-11]. At N>=17, N-4>1 and the guard 6N^2-54N-96>=0 hold, so this precise augmented predicate transfers from N-1 and N+a to N. H28 means the universal augmented bound over ALL such length-28 spectra, at 1/25; it remains an undischarged hypothesis. The length-24 spectral certificate can supply the left endpoint by forgetting L4; its physical 3x8 consequence alone is not that universal spectral statement. With both spectral endpoints supplied, the N=25,a=3 consequence is conditional and has value 11/243. It is not a physical 5x5 acceptance statement; dimensions 26 and 27 are auxiliary dimensions.

**Theorem 1.10 (Transfer from two endpoint dimensions).**

$$\forall(n:\mathbb{N}),(\forall(a:\mathbb{N}),((1\leq a)\Rightarrow((SpectralBound\left(n\right))\Rightarrow((SpectralBound\left(n + 1 + a\right))\Rightarrow(SpectralBound\left(n + 1\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.spectral_bound_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Put N=n+10 and let t be the actual last middle entry. Evaluating K1 at the all-ones vector bounds the bottom-six mass below by the top-three mass, giving (N-3)t<=1. When t<=1/(N+2), insert a copies of t. The ordered tuple retains its boundary and has mass 1+a*t and squared mass P+a*t^2. When t>=1/(N+2), remove only t, retaining the boundary and obtaining mass 1-t>0 and squared mass P-t^2. Positive normalization lets the endpoint bounds apply. The insertion quadratic lies below f(N) on the first interval; the deletion quadratic lies below f(N) between its roots 1/(N+2) and (N^2+15N+20)/((N^2+3N+8)(N+2)). For a cap (N-kappa)*t<=1 with N-kappa>1, the same scalar factorization places the cap below the second root when (10-kappa)*N^2+(6-15*kappa)*N-20*kappa-16>=0. Here kappa=3, and the guard is 7N^2-39N-76>=0 for N>=10. Zero values and ties are included. No preservation hypothesis is assumed.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.ObserverBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.PositiveScaleInvariant`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.SpectralBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.boundaryValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.observerIndex`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.observerValues`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.observer_bound_transfer`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.purityBound`
- Truth anchor: `D5/S3/Quantum/Entanglement/AbsolutePPT/SpectralBoundaryTransfer.spectral_bound_transfer`
- Dependency: [D5/S3/Quantum/Entanglement/AbsolutePPT/QutritSpectralReduction](QutritSpectralReduction.md)
