# Exact all-region RT on a unicyclic arithmetic tensor network

## Status and scope

This note proves a finite-dimensional, deterministic tensor-network theorem. It is an RT identity for a specified state and graph min-cut function. It is not a claim about a continuum gravitational dual, a CFT limit, or arbitrary tensor networks.

The topology is a simple cycle with finite trees attached. Every bulk vertex has degree four after counting boundary legs. All edge capacities are one. The construction works over the odd prime-power rings \(\mathbb Z/3^n\mathbb Z\), with local dimension \(d=3^n\). One internal cycle contraction carries a fixed Fourier-quadratic phase. The phase repairs the arithmetic kernel that otherwise causes an entropy deficit.

## 1. Graph and local tensor

Let \(L\ge 3\), \(d=3^n\), and \(R=\mathbb Z/d\mathbb Z\). Start with cycle vertices \(v_0,\ldots,v_{L-1}\), cycle edges \(e_i=(v_i,v_{i+1})\) (indices modulo \(L\)), and two boundary legs \(a_i,b_i\) at each \(v_i\). Trees may be attached to any boundary legs, preserving degree four; every dangling leg is a boundary terminal. Each edge, including a boundary leg, has capacity one.

At each degree-four vertex place
\[
 T_d=d^{-1}\sum_{x,y\in R}|x,y,x+y,x+2y\rangle .
\]
For any two coordinates among \(x,y,x+y,x+2y\), the \(2\times2\) coefficient determinant is \(1\), \(-1\), \(2\), or \(-2\). Since \(d\) is odd, each is a unit in \(R\), so every two-leg marginal is \(I_{d^2}/d^2\). Thus \(T_d\) is a four-leg perfect tensor over the ring \(R\) (the proof uses only invertibility of these determinants, not that \(R\) is a field).

On one cycle edge replace the usual maximally entangled contraction by
\[
 U_\alpha(u,v)=d^{-1/2}\,\omega^{uv+\alpha v^2},\qquad
 \omega=e^{2\pi i/d},\quad \alpha\in R.
\]
This is a unitary matrix: it is the discrete Fourier matrix multiplied on the right by a diagonal phase. All other contractions are ordinary index identifications. A convenient open-edge expression for the bare cycle state is
\[
 |\Psi^\alpha_{d,L}\rangle
 =d^{-(L+1)/2}\!\!\sum_{x_0,\ldots,x_L\in R}
 \omega^{x_0x_L+\alpha x_0^2}
 \bigotimes_{i=0}^{L-1}
 |x_i+x_{i+1}\rangle_{a_i}
 |x_i+2x_{i+1}\rangle_{b_i}.
 \tag{1}
\]
The boundary label map is injective: from \(b_i-a_i=x_{i+1}\) and \(a_i-x_{i+1}=x_i\), all \(x_i\) are recovered. Hence (1) is normalized.

For attached trees, use the same \(T_d\) tensors and ordinary contractions on every tree edge. The one twisted edge remains on the original cycle.

## 2. Cut upper bound

For any boundary region \(C\), let \(m(C)\) be the minimum number of unit-capacity edges whose removal separates \(C\) from its complement. Cutting \(q\) edges writes the state as a sum over at most \(d^q\) cut-index values. Therefore
\[
 S(\rho_C)\le q\log d,\qquad S(\rho_C)\le m(C)\log d.
 \tag{2}
\]
This is the only direction that follows from a generic tensor-network rank bound; saturation requires the arithmetic argument below.

## 3. The mixed cycle and the unit criterion

First consider a region \(C\) with exactly one of \(a_i,b_i\) selected at every cycle vertex. Write \(w_i=1\) when \(a_i\in C\), \(w_i=2\) when \(b_i\in C\), and \(\bar w_i=3-w_i\). Fixing the selected labels gives the affine recurrence
\[
 x_{i+1}=w_i^{-1}(c_i-x_i).
\]
Thus \(x_0=z\) is the only free variable and
\[
 x_L=s_Cz+f(c),\qquad
 s_C=(-1)^L\left(\prod_i w_i\right)^{-1}. \tag{3}
\]
For a second path contributing to the same complementary labels, the difference satisfies
\[
 \delta x_{i+1}=-(\bar w_i)^{-1}\delta x_i,\qquad
 \delta x_0=t,\quad \delta x_L=s_{\bar C}t. \tag{4}
\]
Because each \(w_i\) and \(\bar w_i\) is a unit, a nonzero \(t\) gives a distinct selected-label string.

The phase in (1) is \(Q(x)=x_0x_L+\alpha x_0^2\). Substituting (3)--(4) gives
\[
 Q(x+\delta x)-Q(x)
 =\bigl(2\alpha+s_C+s_{\bar C}\bigr)tz+\text{(term independent of \(z\))}. \tag{5}
\]
If \(k\) of the selected legs are \(b_i\), then the coefficient in (5) is
\[
 c_k=2\alpha+(-1)^L\bigl(2^{-k}+2^{-(L-k)}\bigr)\in R,\qquad 0\le k\le L.
 \tag{6}
\]
The \(z\)-sum in every off-diagonal density-matrix block is
\[
 \sum_{z\in R}\omega^{c_ktz}.
 \tag{7}
\]
It vanishes for every nonzero \(t\) exactly when \(c_k\) is a unit. In that case \(\rho_C=I_{d^L}/d^L\): the selected-label map is injective, so the diagonal has \(d^L\) equal entries, and (7) removes all cross terms. The mixed cut has cost \(L\), hence \(S(\rho_C)=L\log d=m(C)\log d\).

Conversely, if \(c_k\) is not a unit, choose \(0\ne t\in R\) with \(c_kt=0\). Equation (4) then produces a nonzero off-diagonal block in \(\rho_C\). Therefore \(\rho_C\ne I/d^L\), and its entropy is strictly smaller than \(L\log d\). Consequently, for the cycle the all-region identity is equivalent to
\[
 c_0,c_1,\ldots,c_L\text{ all being units in }R. \tag{8}
\]

## 4. A uniform choice for every \(3^n\)

Modulo \(3\), \(2^{-1}\equiv-1\). If \(L\) is odd and \(\alpha=1\), then
\[
 c_k\equiv 2\pmod 3.
\]
If \(L\) is even and \(\alpha=0\), then
\[
 c_k\equiv 2(-1)^k\pmod 3.
\]
Thus every \(c_k\) is nonzero modulo \(3\), hence a unit in every \(R=\mathbb Z/3^n\mathbb Z\). Define
\[
 \alpha_L=\begin{cases}1,&L\text{ odd},\\0,&L\text{ even}.\end{cases}
 \tag{9}
\]
With this choice, every mixed cycle region saturates the cut bound for all \(n\ge1\).

## 5. All regions and attached trees

We use the following peeling lemma.

**Peeling lemma.** In a graph built from four-leg perfect tensors on a cycle with trees attached, fix a boundary bipartition. If a leaf tensor of the remaining graph has at least two already-labelled legs on the same side, absorb that tensor as a \(2\)-to-\(2\) isometry into that side. The operation removes the leaf and preserves the Schmidt spectrum up to tensoring with a maximally entangled index for each edge cut by the induced partition. Iterating removes every tree. If a cycle vertex is encountered with two same-side effective legs, it is absorbed as well and the residual graph is a forest. Otherwise every cycle vertex has exactly one effective leg on each side, leaving precisely the mixed cycle treated in Section 3.

The lemma is just the defining \(2|2\) isometry property of \(T_d\), applied inductively. A tree leaf has at least three external/effective legs, so two lie on the same side by pigeonhole. In the forest case, continue from leaves; the final state is a tensor product of maximally entangled bonds crossing the induced cut, with entropy equal to that cut size. The peeling operations never increase the number of crossing edges. Conversely, the cut obtained by recording the absorbed crossing bonds is a valid graph cut, so its size is at least \(m(C)\). Combining this lower bound with (2) gives
\[
 S(\rho_C)=m(C)\log d
\]
for every region that peels to a forest. If peeling leaves the cycle, it leaves exactly the mixed pattern and Section 3 applies; its cut cost is \(L\), and the same equality follows. Empty and full regions are included (both sides have entropy zero and min-cut zero).

Therefore, with the phase choice (9), the state (1) and every finite tree decoration satisfy the exact all-region identity
\[
 \boxed{S(\rho_C)=m(C)\log(3^n)\quad\text{for every boundary subset }C.}
 \tag{10}
\]

## 6. Arithmetic obstruction without the twist

Set \(\alpha=0\) on an odd cycle and take \(C=\{a_0,\ldots,a_{L-1}\}\). The graph min-cut is \(L\). The complementary projection has kernel
\[
 (2^L+1)x_0=0\pmod d,
\]
so
\[
 S(\rho_C)=L\log d-\log\gcd(d,2^L+1).
 \tag{11}
\]
For \(d=3^n\), this deficit is \(\min(n,v_3(2^L+1))\log3\). This exhibits why local perfectness alone does not imply all-region RT on a cycle and why the single-edge phase is essential.

## 7. Finite checks and reproducibility

The branch includes an independent direct-amplitude checker,
\`tools/scripts/agent/rt/verify_unicyclic_arithmetic.py\`, which constructs (1), computes all reduced-density spectra by SVD, and compares them with a brute-force graph min-cut. It checks every \(2^{2L}\) boundary region for \(d=3,L=3\) (64 regions) and \(d=3,L=4\) (256 regions), using \(\alpha_L\). The same checker verifies normalization and injectivity. The prior arithmetic certificate in the research record additionally reports \(d=3,L=5,6\), \(d=9,L=3\), and a tree decoration; those larger runs are not needed for the proof.

## 8. Literature status and limits

Relevant established results include perfect-tensor holographic codes (Pastawski--Yoshida--Harlow--Preskill, arXiv:1503.06237), the quantum-error-correction derivation of RT (Harlow, arXiv:1607.03901), random-tensor RT (Hayden--Nezami--Qi--Thomas--Walter--Yang, arXiv:1601.01694), and quantum max-flow/min-cut (Cui--Freedman--Sattath--Stong--Guinton, arXiv:1508.04644). Those works do not state this fixed positive-uniform \(\mathbb Z/3^n\) cycle-with-trees construction or the unit criterion (6). The theorem is a deterministic finite-dimensional tensor-network result; it does not settle arbitrary multicycle graphs, arbitrary phases, arbitrary bond capacities, or gravitational RT. Priority is not claimed: a complete search of stabilizer, convolutional-code, and equivalent arithmetic tensor literature remains open.
