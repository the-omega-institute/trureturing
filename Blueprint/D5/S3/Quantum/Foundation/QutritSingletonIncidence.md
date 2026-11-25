# Singleton incidence of actual qutrit faces

## Abstract

A shared original pure ray determines the homogeneous intersection of actual qutrits.

**Theorem 1.1 (The homogeneous intersection is one real line).**

$$\forall V \in Type,\; [\mathrm{NormedAddCommGroup}\left(V\right)] [\mathrm{NormedSpace}\left(\mathbb{R}, V\right)] [\mathrm{FiniteDimensional}\left(\mathbb{R}, V\right)] \forall C \in \mathrm{PointedCone}\left(\mathbb{R}, V\right),\; \forall u \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall g \in \mathrm{LinearMap}\left(\mathbb{R}, V, \mathbb{R}\right),\; \forall H \in \mathrm{Face}\left(C\right),\; \forall J \in \mathrm{Face}\left(C\right),\; \forall p \in \mathrm{pure}\left(C, u\right),\; \forall eH \in \mathrm{LinearEquiv}\left(\mathbb{R}, \mathrm{span}\left(\mathbb{R}, H\right), \mathrm{HermitianMat}\left(\mathrm{Fin}\left(3\right), \mathbb{C}\right)\right),\; \forall eJ \in \mathrm{LinearEquiv}\left(\mathbb{R}, \mathrm{span}\left(\mathbb{R}, J\right), \mathrm{HermitianMat}\left(\mathrm{Fin}\left(3\right), \mathbb{C}\right)\right),\; \left(\left(\forall x \in V,\; \left(x \in C \land \left(\neg x = 0\right)\right) \Rightarrow 0 < u\left(x\right)\right) \land \left(\left(\forall x \in V,\; x \in C \Rightarrow \left(0 \le g\left(x\right) \land \left(g\left(x\right) = 0 \Leftrightarrow x \in H\right)\right)\right) \land \left(\mathrm{wholePairBalls}\left(C, u\right) \land \left(\left(\forall x \in V,\; \left(x \in H \land x \in J\right) \Leftrightarrow \left(\exists a \in \mathbb{R},\; 0 \le a \land x = \mathrm{smul}\left(a, \mathrm{val}\left(p\right)\right)\right)\right) \land \left(\left(\forall x \in \mathrm{span}\left(\mathbb{R}, H\right),\; \left(\mathrm{val}\left(x\right) \in H \Leftrightarrow 0 \le eH\left(x\right)\right) \land \mathrm{trace}\left(eH\left(x\right)\right) = u\left(\mathrm{val}\left(x\right)\right)\right) \land \left(\forall x \in \mathrm{span}\left(\mathbb{R}, J\right),\; \left(\mathrm{val}\left(x\right) \in J \Leftrightarrow 0 \le eJ\left(x\right)\right) \land \mathrm{trace}\left(eJ\left(x\right)\right) = u\left(\mathrm{val}\left(x\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \mathrm{inf}\left(\mathrm{span}\left(\mathbb{R}, H\right), \mathrm{span}\left(\mathbb{R}, J\right)\right) = \mathrm{span}\left(\mathbb{R}, \mathrm{singleton}\left(\mathrm{val}\left(p\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/QutritSingletonIncidence.original_qutrit_singleton_incidence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg; Leonardo A. Lessa; Rodolfo Soldati (2026). *Finite density states and strong subadditivity in Physlib*. URL: <https://github.com/leanprover-community/physlib/blob/2725b6f621901d4cd330869e9b77105045c1582e/QuantumInfo/Entropy/SSA.lean>.

*Commentary.*

Let C be a pointed cone in a finite-dimensional real normed vector space V. The real-linear unit u is strictly positive on every nonzero element of C. Original pure states are extreme points of the full u = 1 base, and wholePairBalls supplies the original pair-ball charts. The actual faces H and J admit real-linear coordinates on their entire homogeneous spans identifying their cones with the three-by-three complex Hermitian positive semidefinite cone and their units with the trace. The nonnegative linear support g exposes H, and the intersection of the two faces consists exactly of the nonnegative multiples of an original pure state p.

In J, the positive Hermitian representative of g has exactly one zero eigenvalue. Its trace-one zero-support pivot maps to p. On the remaining two coordinates the weights of the diagonal support are strictly positive. A common-span matrix has weighted complementary diagonal sum zero. The complementary two-by-two determinant is nonpositive. If it is zero, the complementary block vanishes and the matrix is already singular. Otherwise a real multiple of the pivot cancels the three-by-three determinant by its affine dependence on the pivot entry. In both cases the shifted matrix remains in the common span.

A singular Hermitian three-by-three matrix has at most two nonzero spectral atoms. QutritSchurPlane.unit_rankOne_original lifts their unit-normalized rank-one projectors to original pure states. The atoms of zero support lie on p. When both supports are positive, the zero total support allows the atoms to be scaled to support one and their quotient images agree. QutritPureLift.unique_original_pure_lift forces their equality and hence cancellation. Subtracting the pivot shift proves that every common-span vector belongs to the real line of p.

This supplies singleton incidence in the local carrier-dimension sixteen through eighteen arguments. The global carrier-dimension conclusions require the remaining incidence and dimension arguments.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/QutritSingletonIncidence.original_qutrit_singleton_incidence`
- Dependency: [D5/S3/Quantum/Foundation/QutritSchurPlane](QutritSchurPlane.md)
