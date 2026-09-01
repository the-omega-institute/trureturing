

---

## [STANDARD BACKBONE 002] FINITE HERMITIAN AND POINT-GAP SPECTRAL LOCALIZERS

### 1. Finite localizer data

Let `n` be a finite index type. Let

\[
X=X^*\in M_n(\mathbb C)
\]

be a finite Hermitian position or observation matrix, let

\[
H\in M_n(\mathbb C)
\]

be an arbitrary finite operator, let `x` be a real spatial centre, `z` a complex spectral point, and `kappa` a real localization scale. Define

\[
A_z=H-zI,
\qquad
X_x=X-xI.
\]

The finite Hermitian localizer is

\[
\boxed{
L_{\kappa;x,z}(X,H)
=
\begin{pmatrix}
\kappa X_x&A_z\\
A_z^*&-\kappa X_x
\end{pmatrix}.
}
\]

The formalization proves directly that

\[
L_{\kappa;x,z}(X,H)^*
=
L_{\kappa;x,z}(X,H).
\]

Hence a possibly non-Hermitian operator `H` is embedded into a Hermitian problem on the doubled finite space.

### 2. Zero-scale singular-value bridge

At zero localization scale,

\[
L_{0;x,z}
=
\begin{pmatrix}
0&A_z\\
A_z^*&0
\end{pmatrix}.
\]

Squaring gives the exact block decomposition

\[
\boxed{
L_{0;x,z}^2
=
\begin{pmatrix}
A_zA_z^*&0\\
0&A_z^*A_z
\end{pmatrix}.
}
\]

The two diagonal blocks are the left and right singular Gram matrices of `H-zI`. This is the finite algebraic reason singular values give a stable Hermitian readout of a non-Hermitian point gap.

The zero-scale localizer itself vanishes exactly when

\[
H-zI=0.
\]

### 3. Point-gap certificate and explicit localizer inverse

A finite point gap is represented by a concrete two-sided inverse certificate

\[
A_zB=I,
\qquad
BA_z=I.
\]

The formalization proves that existence of this certificate is equivalent to `A_z` being a unit in the finite matrix ring.

From `B` construct

\[
\boxed{
L_{0;x,z}^{-1}
=
\begin{pmatrix}
0&B^*\\
B&0
\end{pmatrix}.
}
\]

Both inverse identities are machine-checked:

\[
L_{0;x,z}L_{0;x,z}^{-1}=I,
\qquad
L_{0;x,z}^{-1}L_{0;x,z}=I.
\]

Therefore

\[
\boxed{
H-zI\text{ invertible}
\Longrightarrow
L_{0;x,z}(X,H)\text{ invertible}.
}
\]

This is an exact finite point-gap-to-Hermitian-gap transport theorem.

### 4. Finite inertia profile

Because the localizer is Hermitian, its real eigenvalues have finite positive and negative inertia counts:

\[
n_+(L),
\qquad
n_-(L).
\]

Define the finite signature

\[
\boxed{
\operatorname{Sig}(L)
=n_+(L)-n_-(L)\in\mathbb Z.
}
\]

The implementation packages

\[
(n_+(L),n_-(L),\operatorname{Sig}(L))
\]

as a finite localizer inertia profile. It proves that the counts do not depend on which proof of Hermitianity is supplied and that

\[
0\le n_+(L)\le2n,
\qquad
0\le n_-(L)\le2n.
\]

A point-gap certificate therefore places the zero-scale localizer in an invertible Hermitian locus carrying a finite, bounded inertia profile.

### 5. What this topology layer currently establishes

The new route is independent of RH. It provides a reusable finite interface:

\[
\boxed{
\text{non-Hermitian spectral defect}
\longrightarrow
\text{Hermitian block localizer}
\longrightarrow
\text{singular Gram square}
\longrightarrow
\text{finite inertia data}.
}
\]

This can be instantiated by Koopman operators, finite graph transport, non-normal transfer matrices, Hankel operators, or finite approximants of aperiodic systems.

### 6. Remaining topological hard layer

This batch does not yet prove norm-perturbation stability, local constancy of the signature on a quantitative gap chamber, half-signature integrality, a K-theory pairing, a mobility-gap theorem, or an infinite-volume bulk-boundary correspondence.

The next localizer theorem should introduce a quantitative Hermitian gap and prove that a perturbation smaller than that gap preserves positive and negative inertia. That result will turn the current finite inertia profile into a genuinely stable topological index.
