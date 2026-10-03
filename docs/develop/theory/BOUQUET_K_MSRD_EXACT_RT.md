# Arbitrary-k RT on a bouquet from MSRD local composition

## Setup

Fix (k\ge2). Choose an odd prime (p>k), set (K=\\mathbb F_{p^2}), and write (Q=|K|=p^2). Consider the planar bouquet of (k) triangular loops: a central vertex (O), two outer vertices per loop, and two boundary legs at each outer vertex. Every internal and boundary edge has unit cut weight.

Let (D\in K^{k\times 2k}) be an outer MSRD generator with sum-rank block partition ((2,\ldots,2)), and write its (j)-th block as (D_j=(a_j\ b_j)). We obtain (D) explicitly from the linearized Reed–Solomon construction of Martínez-Peñas and Kschischang, arXiv:1809.11158, Construction 1 and Proposition 1, using (g=k), base field (\\mathbb F_p), extension degree (m=2), and locality (r_j=2). Their hypotheses (p>k) and (m\ge2) hold.

At each outer vertex use the ([4,2]) local map
[
A=\begin{pmatrix}1&0&1&1\\0&1&1&-1\end{pmatrix}.
]
The four virtual central directions in loop (j) are (a_j,b_j,a_j+b_j,a_j-b_j). The boundary row map on latent ((\lambda,z)\in K^k\times K^k) is
[
(a_j\lambda+z_j, a_j\lambda-z_j, b_j\lambda+z_j, b_j\lambda-z_j)_{j=1}^k.
]

The central tensor is (Q^{-k/2}\sum_\lambda |D^T\lambda\rangle), which is AME((2k,Q)) because an MSRD generator is MDS. Each outer tensor is (Q^{-1}\sum_{u,v}|u,v,u+v,u-v\rangle), an AME((4,Q)) tensor since (p) is odd. The normalized boundary state is
[
|\Psi\rangle=Q^{-k}\sum_{\lambda,z}|F(\lambda,z)\rangle.
]
The full row map has rank (2k): differences of the (+/-) rows give the (z_j) directions, and sums give the central span.

## Rank criterion

For a boundary region (R), let (r_j) be its selected-leg count in loop (j). Put
[
H_R=|\{j:r_j>0\}|,quad H_{\bar R}=|\{j:r_j<4\}|,quad
p_R=|\{j:0<r_j<4\}|,
]
and (e(0),e(1),e(2),e(3),e(4)=(0,0,1,2,2)), (E_R=\sum_j e(r_j)).

After eliminating the local (z_j) coordinate, a loop with (r_j=0,1,2,3,4) selected legs contributes respectively no central direction, no central direction, one of (a_j,b_j,a_j+b_j,a_j-b_j), or the pair ((a_j,b_j)). Hence
[
\operatorname{rank}F_R=H_R+\operatorname{rank}V_R.
]
For every allowed blockwise collection of exactly (k) virtual directions, MSRD rank-profile decoding gives rank (k). Indeed, represent the collection as (D\operatorname{diag}(B_j)), where (B_j) is a (2\times s_j) submatrix of (A), (s_j\le2), and (sum s_j=k). Every such (B_j) has rank (s_j), and the MSRD distance is (k+1), so the rank-(k) projection is injective. Any collection of fewer than (k) directions extends to one of size (k); any collection of more than (k) contains one of size (k). Therefore
[
\operatorname{rank}V_R=\min(k,E_R).
]
Since (e(4-r)=2-e(r)), (E_{\bar R}=2k-E_R) and
[
\operatorname{rank}F_{\bar R}=H_{\bar R}+\min(k,2k-E_R).
]

For a uniform state on a (d)-dimensional injective linear support, the flattening rank is (Q^{r_R+r_{\bar R}-d}). Here (d=2k), and (H_R+H_{\bar R}=k+p_R), so
[
S(R)/\log Q=p_R+\min(E_R,2k-E_R).
]

The graph cut is the same expression. For one loop, minimizing the three internal/boundary cut contributions with the central vertex fixed on the complement side gives (e(r)+1_{0<r<4}); putting it on the region side gives (e(4-r)+1_{0<r<4}). Summing loops and minimizing the central side yields
[
m(R)=p_R+\min(E_R,2k-E_R).
]
Thus (S(R)=m(R)\log Q) for all (2^{4k}) individual-leg regions, including empty and full regions.

Conversely, if an allowed (k)-direction collection is dependent, realize its per-block multiplicities by (r_j=0) for zero directions, (r_j=2) for one direction, and (r_j=3) for the pair. Then (E_R=k) and the cut is (p_R+k), while the selected projection rank is deficient. The entropy is strictly below the cut regardless of the complement rank. Therefore all-region RT is equivalent to the virtual rank criterion.

## Scope and prior art

The MSRD/MR-LRC composition is established coding theory: see Martínez-Peñas–Kschischang, arXiv:1809.11158, Construction 1, Proposition 1, and Theorem 2. The present statement translates that rank-profile condition into a deterministic positive-uniform tensor realization and proves exact RT for every individual boundary subset of this bouquet topology. Perfect-tensor RT for connected regions and probabilistic random-stabilizer exactness are known, but do not provide this deterministic all-subset finite-field bouquet statement. No claim is made for arbitrary graphs, arbitrary phases, or gravitational duality.

Bertrand's postulate gives a prime (p) with (k<p<2k), so (Q=p^2<4k^2).