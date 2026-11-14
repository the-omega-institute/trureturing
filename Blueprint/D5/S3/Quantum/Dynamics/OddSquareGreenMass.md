# Odd repeated blocks and zero-energy Green mass

## Abstract

A repeated odd hopping block forces quadratic mass in its inverse bidiagonal block.

**Definition 1.1 (Forward-substitution entries).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall l \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{E}\left(t, l, 0\right) = \frac{1}{t\left(2 \cdot l\right)} \land \operatorname{E}\left(t, l, d + 1\right) = \frac{\operatorname{E}\left(t, l, d\right) \cdot t\left(2 \cdot \left(l + d\right) + 1\right)}{t\left(2 \cdot \left(l + d + 1\right)\right)}$$

*Formalization.* `D5/S3/Quantum/Dynamics/OddSquareGreenMass.greenEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an even open path, split the sites into even and odd sublattices. After alternating diagonal sign changes, its off-diagonal block has positive diagonal t(2i) and negative subdiagonal −t(2i+1). The recurrence E is its positive inverse-entry formula, with starting column l and row displacement d. Positive hoppings make every E positive.

**Definition 1.2 (The finite bidiagonal block).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall n \in \mathbb{N},\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{L}\left(t, n\right)\left(i, j\right) = \operatorname{ite}\left(i = j, t\left(2 \cdot \operatorname{val}\left(i\right)\right), \operatorname{ite}\left(\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right), -t\left(2 \cdot \operatorname{val}\left(j\right) + 1\right), 0\right)\right)$$

*Formalization.* `D5/S3/Quantum/Dynamics/OddSquareGreenMass.lowerBlock` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

L(t,n) is a real matrix on Fin n. Its diagonal is t(2i), its subdiagonal is −t(2j+1), and all other entries vanish. The proof verifies its inverse by multiplication; no invertibility premise is supplied by the caller.

**Theorem 1.3 (Quadratic inverse mass in an odd square).**

$$\forall t \in \mathbb{N} \to \mathbb{R},\; \forall q \in \mathbb{N},\; \left(\forall i \in \mathbb{N},\; 0 < t\left(i\right)\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; t\left(i\right) \le 1\right) \Rightarrow \left(\left(\forall i \in \mathbb{N},\; i < 2 \cdot q \Rightarrow t\left(i + 2 \cdot q + 1\right) = t\left(i\right)\right) \Rightarrow q \cdot \left(q + 1\right) \le \sum_{l < q} {\sum_{d < q - l} {\left(\operatorname{L}\left(t, 2 \cdot q + 1\right)^{-1}\right)\left(\langle l + d + 1 \rangle, \langle l \rangle\right) + \left(\operatorname{L}\left(t, 2 \cdot q + 1\right)^{-1}\right)\left(\langle q + l + d + 1 \rangle, \langle q + l + 1 \rangle\right)}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/OddSquareGreenMass.odd_square_inverse_paired_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All indices are zero based. In the sums, l ranges over Fin q and d over Fin(q−l). Each displayed matrix index denotes the Fin(2q+1) element with that natural value. The bounds on l and d prove that every index exists, including the endpoints. Only the repeated bonds with i<2q are required; this is a finite repetition assumption. Forward substitution gives E(t,l,d+1)E(t,q+l+1,d) =1/(t(2l)t(2(l+d+1))). The repeated odd block exchanges numerator and denominator factors in the shifted interval. Since both endpoint hoppings are at most one, each pair has product at least one and sum at least two. There are q(q+1)/2 pairs. The conclusion concerns the actual finite inverse, rather than an assumed Green function. It does not assert the Tribonacci all-prefix spectral-gap statement: that application also needs the exact word-to-hopping correspondence, aligned repeated windows and initial short prefixes. No infinite-volume spectrum, localization, quasimode or filling hypothesis enters this theorem.

## Application: a Euclidean estimate for the full inverse

Let t be a positive real hopping sequence bounded above by one, and let n,a,q be natural numbers with q at least one and a+2q+1 at most n. Assume exactly the 2q repetitions t(2a+i+2q+1)=t(2a+i), for i<2q. Set G=L(t,n) inverse, acting on the Euclidean space R^n, x=(1,...,1) and v=x/sqrt(n). The hypotheses imply n>0. The quadratic mass theorem has the following consequence, without a new mathematical declaration:

$$
\left\lVert v \right\rVert = 1 \land q \cdot \left(q + 1\right) \le 2 \cdot n \cdot \left\lVert G\left(v\right) \right\rVert
$$

The forward-substitution formula transports each local inverse entry to G by adding a to both indices: the defining recursion has the same initial term and step after this index translation. Thus both exterior portions of the full path remain present. All entries of G are nonnegative. Each of the two triangular regions from the mass theorem embeds injectively in the full matrix, so q(q+1) is at most twice the sum of all entries of G. The factor two bounds the regions separately and needs no disjointness premise. The sum equals the Euclidean inner product of x with Gx. Cauchy--Schwarz, norm(x)^2=n and Gx=sqrt(n)Gv give that this sum is at most n times norm(Gv), proving the estimate.

For an even-start repeated word window, the parameter correspondence is m=2q+1, s=2a and N=2n. This supplies the complete-bidiagonal-inverse Euclidean consequence of the mass estimate. The following application supplies the parity reordering, sign conjugation and spectral conversion for a general finite positive open chain. Identifying the actual Tribonacci hopping sequence, assembling its repeated windows under a common index convention and treating the short prefixes remain separate obligations. No all-prefix Tribonacci spectral rate or entropy law is asserted.

## Application: a spectral residual bound for the finite open chain

Let n be a natural number with n at least one, and let t : N -> R be strictly positive at every natural index. No upper bound on t is needed for this conversion. On the actual sites 0,...,2n-1 define the real symmetric open-chain matrix H by:

$$
\forall i \in \operatorname{Fin}\left(2 \cdot n\right),\; \forall j \in \operatorname{Fin}\left(2 \cdot n\right),\; H\left(i, j\right) = \operatorname{ite}\left(\operatorname{val}\left(i\right) + 1 = \operatorname{val}\left(j\right), t\left(\operatorname{val}\left(i\right)\right), \operatorname{ite}\left(\operatorname{val}\left(j\right) + 1 = \operatorname{val}\left(i\right), t\left(\operatorname{val}\left(j\right)\right), 0\right)\right)
$$

The diagonal is zero, the last physical bond is t(2n-2), and there is no closing bond. In particular, n=1 gives two sites joined only by t(0). Put B=L(t,n), the lowerBlock defined above. Its diagonal is t(2i), its subdiagonal in row i is -t(2i-1) for 1<=i<n, and all other entries vanish. Since B is lower triangular with positive diagonal, its determinant is positive and its ordinary inverse G exists:

$$
\begin{aligned}B = \operatorname{L}\left(t, n\right)\\\operatorname{det}\left(B\right) = \prod_{i < n} t\left(2 \cdot i\right) > 0\\G = B^{-1}\\B \cdot G = I\end{aligned}
$$

Reorder the coordinates into even sites followed by odd sites. Write Hpar for the matrix in this order and C(i,j)=H(2i,2j+1), for 0<=i,j<n. Then C has diagonal t(2i), positive subdiagonal t(2i-1) in row i, and zeros elsewhere. The sign matrix D=diag((-1)^i), for 0<=i<n, is orthogonal and satisfies D squared equals I. Conjugation preserves the diagonal of C and reverses its subdiagonal, giving:

$$
\begin{aligned}Hpar = \begin{pmatrix}0&C\\C^{T}&0\end{pmatrix}\\D^{2} = I\\D \cdot C \cdot D = B\\C \cdot D = D \cdot B\end{aligned}
$$

Take any Euclidean unit vector v in R^n, and define u in the original site order by u(2i)=0 and u(2i+1)=(DGv)(i). Since BG=I, the even part of Hu is CDGv=DBGv=Dv and its odd part is zero. Permuting coordinates and changing their signs preserve Euclidean norms. Thus:

$$
\begin{aligned}u_{\mathrm{even}} = 0\\u_{\mathrm{odd}} = D\left(G\left(v\right)\right)\\H\left(u\right)_{\mathrm{even}} = D\left(v\right)\\H\left(u\right)_{\mathrm{odd}} = 0\\\left\lVert u \right\rVert = \left\lVert G\left(v\right) \right\rVert\\\left\lVert H\left(u\right) \right\rVert = 1\end{aligned}
$$

Moreover BGv=v and norm(v)=1 imply Gv is nonzero, hence u is nonzero. The finite real symmetric matrix H has a real orthonormal eigenbasis e(k) with real eigenvalues lambda(k), for 0<=k<2n. Expand u in that basis, with real coefficients c(k), and let alpha be the minimum absolute eigenvalue:

$$
\begin{aligned}H\left(e\left(k\right)\right) = \lambda\left(k\right) \cdot e\left(k\right)\\u = \sum_{k < 2 \cdot n} {c\left(k\right) \cdot e\left(k\right)}\\\alpha = \min_{k < 2 \cdot n} \left|\lambda\left(k\right)\right|\end{aligned}
$$

The index set is finite and nonempty because 2n>0. Each absolute eigenvalue is at least alpha. Parseval applied to u and Hu therefore gives:

$$
\begin{aligned}\alpha^{2} \cdot \left\lVert u \right\rVert^{2} = \alpha^{2} \cdot \sum_{k < 2 \cdot n} {c\left(k\right)^{2}}\\\alpha^{2} \cdot \sum_{k < 2 \cdot n} {c\left(k\right)^{2}} \le \sum_{k < 2 \cdot n} {\lambda\left(k\right)^{2} \cdot c\left(k\right)^{2}}\\\sum_{k < 2 \cdot n} {\lambda\left(k\right)^{2} \cdot c\left(k\right)^{2}} = \left\lVert H\left(u\right) \right\rVert^{2} = 1\end{aligned}
$$

Choose an index k0 attaining the minimum, put lambda=lambda(k0) and z=e(k0). The vector z has norm one and is nonzero. Taking nonnegative square roots in the preceding inequality and substituting norm(u)=norm(Gv) proves:

$$
\begin{aligned}H\left(z\right) = \lambda \cdot z\\z \ne 0\\\left|\lambda\right| = \alpha\\\left|\lambda\right| \cdot \left\lVert G\left(v\right) \right\rVert \le 1\end{aligned}
$$

The selected z is an eigenvector of the actual H. The auxiliary residual vector u need not be an eigenvector. This argument applies to every finite positive open chain and every Euclidean unit v, without repetition or an upper hopping bound.

Now impose the preceding full-inverse estimate's additional hypotheses: t(i)<=1 for every i, q>=1, a+2q+1<=n, and t(2a+i+2q+1)=t(2a+i) for every i<2q. Use the same vector v=(1,...,1)/sqrt(n) as in that estimate. It gives q(q+1)<=2n norm(Gv), while the spectral argument gives an eigenvalue lambda of minimum absolute value with abs(lambda) norm(Gv)<=1. Multiplying the first inequality by the nonnegative abs(lambda), then using the second, yields:

$$
\begin{aligned}\left|\lambda\right| \cdot q \cdot \left(q + 1\right) \le 2 \cdot n \cdot \left|\lambda\right| \cdot \left\lVert G\left(v\right) \right\rVert \le 2 \cdot n\\\delta = \min_{\mu \in \operatorname{Spec}\left(H\right)} \left|\mu\right| = \left|\lambda\right| \le \frac{2 \cdot n}{q \cdot \left(q + 1\right)}\end{aligned}
$$

Here Spec(H) is the finite real spectrum and delta is its distance from zero; division is valid because q>=1. This completes the generic finite positive-path conversion from full-inverse mass to a spectral bound. A quantitative rate along all actual Tribonacci prefixes still requires the exact word hoppings t(i)=t(W(i)), aligned repeated windows and the full-inverse mass estimate under one common index convention, together with the initial short prefixes. Entropy scaling requires a separate argument about physical states and spatial cuts. Neither an all-prefix Tribonacci spectral rate nor a physical entropy law follows from this application alone.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/OddSquareGreenMass.greenEntry`
- Truth anchor: `D5/S3/Quantum/Dynamics/OddSquareGreenMass.lowerBlock`
- Truth anchor: `D5/S3/Quantum/Dynamics/OddSquareGreenMass.odd_square_inverse_paired_mass`
