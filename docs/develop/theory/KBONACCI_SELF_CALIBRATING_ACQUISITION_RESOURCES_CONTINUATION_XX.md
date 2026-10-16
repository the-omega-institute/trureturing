# KBONACCI self-calibrating acquisition resources XX: conditional replacement tests

## 348. Common objects, rows and the scope of the tests

The source, carrier and consumer are those of [315.1](KBONACCI_SELF_CALIBRATING_ACQUISITION_RESOURCES_CONTINUATION_XVIII.md#315-original-objects-and-the-complete-affine-feasibility-problem). Thus

$$
\begin{aligned}
X&=\{(r,g):r\text{ prime},\ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
N(r,g)&=1+F_rg,
\end{aligned}
$$

where $F_0=0,F_1=1,F_{r+2}=F_{r+1}+F_r$, and the reply to the $i$th prime is
$q_i=[p_i\mid N(r,g)]$. The first zero is $n=\min\{i:q_i=0\}$. The CRT and Fibonacci-window argument in Boundaries 35.2, reused in XVIII 315.3, realizes every finite word, including words with several zeros. It does not introduce a source prior, a source label or an additional observation.

The full Borel carrier is the disjoint union of interval copies $B_j$ and $P_j$. The unchanged consumer returns unknown on $B_j$ and proposes $j$ on $P_j$, and the marked output is $\theta_j=(B_1,1/(j+2))$. The original nonatomic target
$(1-h_0)\nu_x+h_0\pi_{\Omega(x)}$ remains the target of the original problem. The finite marked targets considered here are the separate laws

$$
\lambda_x^a=(1-a_{n(x)})\delta_{\theta_0}+a_{n(x)}\delta_{\theta_{n(x)}},
\qquad 1\ge a_1\ge a_2\ge\cdots>0,\qquad a_n\longrightarrow0.
\tag{348.1}
$$

A finite marked law has total variation one from the unchanged nonatomic target; every accuracy assertion below concerns (348.1) only.

A complete table is selected by one source-independent uniform seed before any reply. Class $N$ preselects its whole schedule and acquires every selected address. Class $O$ preselects an increasing schedule and stops at the first queried zero or exhaustion. Repeated or ignored requests count as actual requests. No second address is selected from a reply, and the hard bound is two actual requests. A proof map used below is a map of Boolean words in a coefficient calculation; it is never an extra observation, reset or copy operation.

For a finite horizon $L$, put $J=\{0,\ldots,L\}$ and write $e_j$ for the label basis vectors. Every complete law is a vector kernel

$$
 p(w)=c+\sum_{i=1}^L\ell_iw_i+\sum_{1\le i<j\le L}Q_{ij}w_iw_j,
 \qquad w\in\{0,1\}^L,
\tag{348.2}
$$

with nonnegative values and constant mass $M$. Thus $m(c)=M$ and
$m(\ell_i)=m(Q_{ij})=0$, where $m(v)=\sum_{r\in J}v(r)$. All labels, all multiple-zero words and the positive word $1^L$ are retained.

For a first-zero word $n$ the three independent rows are

$$
 p_w(0)\ge1-a_n-e,\qquad p_w(n)\ge a_n-e,\qquad p_w(0)+p_w(n)\ge1-e,
\tag{348.3}
$$

and at $1^L$ the positive row is $p_{1^L}(0)\ge1-e$. Negative right-hand sides remain literal. For the affine comparison used by the score consumer, let
$R=O(1,2;1,2,0)$, $\alpha=(1,1,0,\ldots)$, $r=z_R=d(\alpha,0)$, and
$h(b,e)=d(b,e)-r$. A mass-$M$ allocation is required to satisfy

$$
 z\lambda\ \ge\ d(b,e)+(M-1)r,
\tag{348.4}
$$

row by row. Dividing by $M$ changes the profile to
$b'=\alpha+(b-\alpha)/M$ and $e'=e/M$; it is not a normalization at the original $(b,e)$.

For $L\ge3$, the canonical full score $Y=(A_w,C_w,P_w;T)$ has
$QY=(\beta,K)$ with
$\beta_n=\sum_{w:n(w)=n}(C_w-A_w)$ and
$K=\sum_w(A_w+C_w+P_w)+T$. Consequently

$$
F_{QY}(b,e)=\sum_n\beta_n(b_n-\alpha_n)-Ke=Yh(b,e).
\tag{348.5}
$$

The lower-horizon polynomial statements are separate finite lemmas. The score consumer is used only at $L\ge3$, with the same full allocation in every row.

## 349. W: exact raw-mass elimination in the restricted witness cone

The following calculation concerns precisely the $W_N$ cone of VI 190.2 and its conversion in VI 191–197. It is not the affine profile cost and it does not replace the complete $g$ family of XIX 341.2.

For labels $k=1,\ldots,L$, prescribe

$$
 p_k(w)=c_k+\sum_i\ell_{i,k}w_i+\sum_{i<j}Q_{ij,k}w_iw_j,
\tag{349.1}
$$

and set $p_0(w)=M-\sum_{k=1}^Lp_k(w)$. Put $x_+=\max(x,0)$,
$Z_i=-\ell_{i,i}$, $\xi_{ij}=Q_{ij,i}$, and
$d^0_{ij,k}=(-Q_{ij,k})_+$ for $i<k\le j$. Define

$$
\begin{aligned}
t_{ij}&=\max\left\{\sum_{k>i}(Q_{ij,k})_+,\ \sum_{k>i}(-Q_{ij,k})_+\right\},\\
m^0_{ij}&=\max\{|\xi_{ij}|,t_{ij}\},\\
S_{i,k}&=\ell_{i,k}-\sum_{j=k}^Ld^0_{ij,k}\qquad(i<k),\\
A_i&=\left[Z_i-\sum_{j>i}(\xi_{ij})_+-\sum_{j>i}(m^0_{ij}-|\xi_{ij}|)\right]_+,\\
D_i&=\max\left(0,\max_{i<h\le L}\left\{\sum_{k=h}^LS_{i,k}-\sum_{j=h+1}^L(m^0_{ij}-t_{ij})\right\}\right),\\
B_W&=\sum_{k=1}^L(c_k-Z_k)+\sum_{i=1}^L\left(\sum_{j>i}m^0_{ij}+\max\{A_i,D_i\}\right).
\end{aligned}
\tag{349.2}
$$

An empty maximum is zero.

**Theorem 349.1 (Nested-capacity formula).** A $W_N$ complete allocation of total mass exactly $M$ realizes the prescribed entire vector kernel if and only if

$$
\begin{gathered}
Z_k\ge0,\qquad c_k\ge Z_k,\\
\ell_{j,k}=-Q_{kj,k}\quad(k<j),\\
Q_{ij,k}=0\ (k<i),\qquad Q_{ij,j}\le0,\qquad Q_{ij,k}\ge0\ (k>j),\\
Z_i\ge\sum_{j>i}(\xi_{ij})_+,\qquad S_{i,k}\ge0,
\end{gathered}
\tag{349.3}
$$

and $M\ge B_W$. Under these conditions $B_W$ is attained. A minimizing allocation uses pair mass $m^0_{ij}$, singleton mass $\max\{A_i,D_i\}$ and empty label-$k$ mass $c_k-Z_k$, with excess mass put on the empty zero output. Zero-$Q$ pairs can be omitted by this restricted minimizer; the zero-$Q$ variables in the accepted complete $g$ cone are still retained in T below.

*Proof.* In a pair $(i,j)$ let $a,b$ be the label-$i$ masses in cells $00,01$, let $d_k$ be the label-$k$ mass in cell $10$ for $i<k\le j$, and let $e_k$ be its cell-$11$ mass. Then
$\xi_{ij}=a-b$, $Q_{ij,k}=e_k-d_k$ for $i<k<j$,
$Q_{ij,j}=-d_j$, and $Q_{ij,k}=e_k$ for $k>j$. Labels below $i$ are absent. Hence $d_k\ge d^0_{ij,k}$ and the required pair mass is at least $m^0_{ij}$. The only pair contribution to $\ell_{j,k}$, with $j>k$, is $-Q_{kj,k}$; the remaining stock is therefore $S_{i,k}$.

For a fixed root $i$, the first-cell extra label-$i$ capacities are $m_{ij}-|\xi_{ij}|$. The positive-cell capacities for label $k$ are $m_{ij}-t_{ij}$ and are available only in columns $j>k$. Filling the first capacities leaves exactly
$A_i(m)$ as the least singleton-zero stock. The second capacities form nested suffixes: the stock with labels at least $h$ can enter only columns $j>h$. Therefore every allocation leaves at least

$$
\max_{h>i}\left(\sum_{k=h}^LS_{i,k}-\sum_{j>h}(m_{ij}-t_{ij})\right)_+
$$

unmatched. Filling columns in decreasing $k$ attains all these suffix bounds by induction, so the least singleton-positive stock is $D_i(m)$. The two stocks share one singleton schedule and hence require their maximum, not their sum. Increasing a pair mass by $\delta$ enlarges each usable capacity by at most $\delta$ and cannot lower the total pair mass plus this maximum; thus $m_{ij}=m^0_{ij}$ is optimal. The displayed construction fills the two independent cell families, reconstructs every coefficient and puts the remaining $c_k-Z_k$ in the empty schedule. The zero label follows from the same total mass. Finally, normalize each positive schedule cell by one common local uniform coordinate, refine all label intervals together, and use one global uniform seed to select the schedule. Every counterfactual cell is fixed before replies and has the same schedule mass. Degenerate zero masses and $M=0,L=0,1$ require no division and are included. $\square$

**Corollary 349.2 (Conditional original bridge).** Fix $0<e\le1$ and
$L=\max(\{i:a_i>e\}\cup\{0\})$. If one normalized complete $N$ kernel satisfies (348.3), the positive row and all full labels, and its chosen $W_N$ coefficients satisfy (349.3) with $B_W\le1$, then one normalized $O$ allocation satisfies the same rows at the same $(a,e)$. The proof is the already supplied VI 191–197 full-vector conversion and increasing-first-zero induction applied to the single W allocation; it does not preserve an arbitrary input $N$ law or coupling. The finite word at $1^L$ represents a table endpoint, not an infinite all-positive source, and the tail is handled by §354.

**Example 349.3 (Raw mass is a different quantity).** At $L=2$ take
$p_1=(1-w_1)(1-w_2)$ and $p_2=w_1$. Then
$Z_1=1$, $\xi_{12}=1$, $t_{12}=0$, $m^0_{12}=1$, $S_{1,2}=1$, $A_1=0$, $D_1=1$, and $B_W=2$. The input table has mass one but its exact W reconstruction needs mass two. For actual words with $n>2$ it emits a wrong marked label, so this is a law-preservation diagnostic only; it is neither a lower bound for all original $O$ rules nor a strict separator.

## 350. F: current-coefficient first-zero face tests

For $k\in\{1,\ldots,L\}$ let $T_kp(w)=p(w_1,\ldots,w_{k-1},1,w_{k+1},\ldots,w_L)$. For a label $r\in J$, define the current-kernel derivative minimum

$$
\kappa_k(r)=\ell_k(r)+\sum_{i<k}Q_{ik}(r)-\sum_{j>k}(-Q_{kj}(r))_+.
\tag{350.1}
$$

After each restriction all coefficients in (350.1) are recomputed; labels and addresses are not renumbered.

**Theorem 350.1 (Face restriction).** If
$\kappa_k(0)\ge0$ and $\kappa_k(k)\ge0$, then $T_kp$ preserves every row in (348.3), the positive row and the same affine demands. If $p$ has a complete $N$ allocation, folding the reply $1$ into every counterfactual table and deleting the actual request to $k$ realizes $T_kp$ with the same common mass. Any finite sequence of successful restrictions may be followed by the stopped criterion

$$
V_i=\sum_{j>i}(-Q_{ij})_+,\qquad
H=\sum_i(V_i-\ell_i)_+,\qquad c\ge H,
\tag{350.2}
$$

to obtain one complete stopped allocation at the same profile and mass. The scalar schedule budget is then automatic from normalization. An ordered outward-star endpoint may instead use the accepted whole-vector contraction of XIX 343.1, with the attribution and limitations of XV 258.3–258.4.

*Proof.* At a word whose first zero is $k$, all earlier bits are one, and

$$
(T_kp-p)(w)=\ell_k+\sum_{i<k}Q_{ik}+\sum_{j>k}Q_{kj}w_j.
$$

For label $r$, its minimum over the independent suffix cube is (350.1). The two displayed tests therefore make both the base and correct coordinates nondecreasing on the $n=k$ face. Their sum is also nondecreasing, so the independent union row is preserved. If $n<k$, changing bit $k$ leaves the first zero and all three demands unchanged; if $n>k$, bit $k$ was already one. The positive word is fixed. These cases exhaust the cube, and induction gives a whole-kernel statement rather than separate row witnesses. Folding a preselected reply-one table deletes an actual request and leaves all remaining complete cells fixed before replies. Applying the reused 109.1 inverse to (350.2) gives the final stopped allocation, including zero coefficients and zero masses. $\square$

**Example 350.2 (A failed test is not a separator).** The exact profile
$(a_1,a_2,a_3)=(9/10,9/10,1/2)$ with $e=2/5$ and any positive ordered vanishing tail with $a_4\le2/5$ has the cap-feasible non-stopped input allocation

$$
p=\frac35N(1,2;1,1,2,0)+\frac1{10}e_3
  +\frac3{20}N(1,3;1,0,3,0)+\frac3{20}N(2,3;2,0,1,0),
$$

where the pair cells are ordered $00,01,10,11$ and $e_3$ is the empty output $3$. For this input
$H(1)-c(1)=3/20$, while
$\kappa_1(1)=-3/4$, $\kappa_2(2)=-3/4$, and $\kappa_3(3)=-3/20$. Nevertheless restricting coordinate $3$ gives the complete stopped law
$(3/5)O(1,2;1,2,0)+(3/10)e_0+(1/10)e_3$ at the same cap. Thus F is a sufficient route; failure of its first available test is only failure of that route.

## 351. T: one-g triangle certificates with both budgets

The complete coefficient criterion of XIX 341.2 supplies one zero-sum vector $g_{ij}$ for every pair, including pairs with $Q_{ij}=0$. Define

$$
\begin{aligned}
r_{ij}&=(-g_{ij})_+,&s_{ij}&=(-g_{ij}-Q_{ij})_+,&t_{ij}&=\max\{m(r_{ij}),m(s_{ij})\},\\
D_i&=\ell_i-\sum_{h<i}g_{hi},&R_i&=\sum_{j>i}r_{ij},&S_i&=\sum_{j>i}s_{ij},\\
T_i&=\sum_{j>i}t_{ij},&U_i&=\max\{R_i,S_i-D_i\},&u_i&=m(U_i).
\end{aligned}
\tag{351.1}
$$

The same $g$ must satisfy both accepted budgets

$$
 c\ge\sum_iU_i\quad\text{coordinatewise},\qquad
 \sum_i\max\{u_i,T_i\}\le M.
\tag{351.2}
$$

**Theorem 351.1 (Triangle certificate).** Suppose there are zero-sum vectors $B_{ij}$ and $C_{ijk}$ such that

$$
B_{ij}(r)\ge0\ (r\le i),\qquad C_{ijk}(r)\ge0\ (r<k),
\tag{351.3}
$$

and the *same* $g$ in (351.1) is generated by

$$
 g_{ij}=-B_{ij}+\sum_{i<h<j}C_{ihj}-\sum_{k>j}C_{ijk}-\sum_{h<i}C_{hij}.
\tag{351.4}
$$

Then the complete kernel

$$
 q(w)=c+\sum_iD_iw_i+\sum_{i<j}(Q_{ij}+g_{ij})w_iw_j
\tag{351.5}
$$

is a mass-$M$ stopped kernel. On every first-zero word it dominates the base, correct and independent-union coordinates of $p$, and it agrees with $p$ at $1^L$. Hence any complete $N$ allocation satisfying the original rows and (351.2) has one complete $O$ allocation of the same mass satisfying the same rows and the same affine demands.

*Proof.* Set $d_{ij}(w)=(1-w_i)w_j$. Direct coefficient subtraction gives
$p(w)-q(w)=\sum_{i<j}g_{ij}d_{ij}(w)$. The edge term from $-B_{ij}$ is nonpositive in labels $r\le i$ whenever it is active; its first zero is at most $i$. For a triangle $i<j<k$,

$$
 d_{ik}-d_{ij}-d_{jk}
 =-\big((1-w_i)w_j(1-w_k)+w_i(1-w_j)w_k\big)\le0.
\tag{351.6}
$$

When (351.6) is nonzero, some zero occurs before $k$, so the coordinates $0$ and the actual first-zero label are both $<k$ and the $C_{ijk}$ term is nonpositive there. When the first zero is at or after $k$, (351.6) is zero. Summing all edges and triangles yields
$q_w(0)\ge p_w(0)$ and $q_w(n)\ge p_w(n)$; their sum gives the independent union row from the same allocation. All $d_{ij}$ vanish at $1^L$, so the positive row is unchanged. This is a whole-vector comparison and includes multiple zeros, negative literal demands and equality cases.

The negative part of $Q+g$ is $s_{ij}$, and the stopped envelope is
$H=\sum_i(S_i-D_i)_+$. Since $U_i\ge S_i-D_i$, (351.2) gives $c\ge H$. The scalar inequality in (351.2) is retained separately, so the 109.1 inverse gives one complete mass-$M$ stopped allocation. Pairing that same allocation with any full nonnegative score $Y$ gives

$$
F_{QY}(b,e)=Yh(b,e)\le YG_O\lambda\le M\Delta_O(Y).
\tag{351.7}
$$

No score-by-score allocation, marginal budget or universal $Y\mapsto(V,\theta)$ construction is inferred. $\square$

All zero-$Q$ entries remain available in (351.1)–(351.4). A one-parent star is the prior XV 258.3–258.4 mechanism; T credits the extra common edge/triangle certificate and its same-$g$ funding condition, not the star itself.

## 352. P: shared parent gates and whole-vector cancellation

Partition the addresses into roots $R$ and leaves $D$, with every nonzero interaction from a root $i$ to a later leaf $j$. For each leaf choose a nonempty parent set
$P_j\subseteq\{i\in R:i<j\}$ containing every root $i$ with $Q_{ij}\ne0$; roots with $Q_{ij}=0$ may also be included. Choose source-independent numbers $\lambda_{ij}\ge0$ with
$\sum_{i\in P_j}\lambda_{ij}=1$. Require, for distinct parents $i,h\in P_j$,

$$
\lambda_{hj}Q_{ij}+\lambda_{ij}Q_{hj}=0
\tag{352.1}
$$

as an equality of the whole label vector. Put
$B_{ij}=\lambda_{ij}(\ell_j+Q_{ij})$ and require, for each leaf and each output label, that all values $B_{ij}(r)$ have one sign; zero and ties are allowed.

**Theorem 352.1 (Common-parent cancellation).** If a complete normalized $N$ kernel $p$ is feasible at a profile and satisfies (352.1) and the sign condition, then one complete normalized $O$ allocation is feasible at the same profile. More generally, the conclusion holds for a mass-$M$ affine row system (348.4) without dividing its anchor.

*Proof.* Let one common seed choose, independently for every leaf, a parent $K_j$ with probabilities $\lambda_{ij}$. The Boolean proof map is
$\rho_K(w)_i=w_i$ for roots and $\rho_K(w)_j=w_{K_j}w_j$ for leaves. Define
$q(w)=\mathbb E_K p(\rho_K(w))$. Every transformed coordinate is an original bit times an earlier bit, so the first zero and the positive word are preserved. Therefore each row of $p(\rho_K(w))$ is the row at $w$ and averaging preserves all rows simultaneously.

The support condition makes the entire contribution of a leaf $j$, before averaging, $\rho_K(w)_j(\ell_j+\sum_{i\in P_j}Q_{ij}w_i)$. Its average is

$$
w_j\left(\sum_{h\in P_j}\lambda_{hj}w_h\right)
    \left(\ell_j+\sum_{i\in P_j}Q_{ij}w_i\right).
$$

Using $w_i^2=w_i$, its quadratic coefficient on $w_iw_j$ is $B_{ij}$. For distinct parents $i,h$, its cubic coefficient is $\lambda_{hj}Q_{ij}+\lambda_{ij}Q_{hj}$ and vanishes by (352.1), including zero coefficients and zero parent probabilities. Every possible cubic has this unique leaf; there are no omitted incoming terms or leaf-leaf interactions. Hence

$$
q(w)=c+\sum_{i\in R}\ell_iw_i+\sum_{j\in D,\ i\in P_j}B_{ij}w_iw_j.
\tag{352.2}
$$

Fix a label $r$. Because the $B_{ij}(r)$ for a fixed leaf have one sign, choose that leaf bit to be one exactly when its common sign is negative. The contribution of the leaves to root $i$ is then
$-V_i(r)$, where $V_i=\sum_j(-B_{ij})_+$. Choose root bit $i$ to be one when $\ell_i(r)-V_i(r)<0$. At this one word, $q(r)=c(r)-H(r)$ with
$H=\sum_i(V_i-\ell_i)_+$. Since $q$ is nonnegative, $c\ge H$ coordinatewise. Every $\ell_i$ and $B_{ij}$ has zero label sum, so
$m((V_i-\ell_i)_+)\ge m(V_i)$ and $m(H)\le m(c)=M$; the scalar stopped budget is therefore at most $M$ (one in the normalized case). The 109.1 inverse constructs one complete stopped allocation; at $M=0$ all schedule masses vanish. The seed used for the proof map is absorbed into that one finite allocation; no branch is executed as an extra query. The same argument with (348.4) keeps mass $M$ and its literal anchor. $\square$

**Example 352.2 (One consolidated non-star application).** Let $L=3$, $e=4/5$,
$(a_1,a_2,a_3)=(9/10,7/8,17/20)$ and
$a_n=(4/5)/(n-3)$ for $n\ge4$. Set

$$
\begin{aligned}
p_1&=(1-w_1)/10,\\
p_2&=(1-w_2)/10,\\
p_3&=\frac25\bigl(1+w_2+(w_1-1-w_2)w_3\bigr),\qquad p_0=1-p_1-p_2-p_3.
\end{aligned}
\tag{352.3}
$$

The nonzero interactions are $Q_{13}=(-2/5,0,0,2/5)$ and
$Q_{23}=-Q_{13}$, so the leaf has two parents and the graph is not an outward star. The common parent average gives

$$
q_1=p_1,\qquad q_2=p_2,\qquad q_3=\frac25+\frac25w_2-\frac25w_2w_3,\qquad q_0=1-q_1-q_2-q_3.
\tag{352.4}
$$

A complete $N$ allocation has masses $2/5,2/5,1/10,1/10$ on, respectively,
$N(1,3;3,0,3,3)$, $N(2,3;0,0,3,0)$, the singleton $(1;1,0)$ and the singleton $(2;2,0)$ (the pair cells are ordered $00,01,10,11$). A complete $O$ allocation has masses $2/5,1/10,1/10,3/10,1/10$ on the empty output $3$, empty output $0$, singleton $(1;1,0)$, and the pairs $(2,3;0,3,0)$ and $(2,3;2,3,0)$ (cells $0,10,11$). Direct evaluation of all eight words gives the same cap $4/5$; the positive tail has error $\max\{2/5,a_n\}\le4/5$. This is a same-profile law-changing attainer, not a new amplitude region and not a lower bound against arbitrary original $O$ competitors.

The source realization uses the finite-word correspondence of §348, one interval seed and the unchanged handoff. A pair always fixes all cells before replies; $N$ pays both calls, while $O$ stops at the first queried zero. No source reset or evaluation of $\rho_K$ occurs.

## 353. C: a compact cancelling-fork normal form

C is a deterministic companion to P. It is useful when parent averaging is unavailable but the whole kernel contains disjoint cancelling blocks. Let $h$ be a nonnegative vector kernel of mass $m\ge0$ with polynomial

$$
 c+\sum_{(a,b,C)}\left(Aw_a+\ell_bw_b+\sum_{d\in C}C_dw_d+Ew_aw_b
 +\sum_{d\in C}D_d(w_a-w_b)w_d\right)+\sum_{i\in I}\ell_iw_i,
\tag{353.1}
$$

where $a<b<d$ in each block, blocks and isolated coordinates are disjoint, and there are no other interactions in the subkernel. The full-vector identities are
$Q_{ad}=D_d$, $Q_{bd}=-D_d$, and $Q_{de}=0$ for distinct leaves. Put $B=\ell_b+E$. For every output label $r$ define

$$
 u_r=(-A_r)_+,\qquad v_r=(-A_r-B_r)_+,\qquad
 d_r=\sum_{d\in C}(-C_d(r))_+.
\tag{353.2}
$$

Require $d_r=0$ or $v_r\ge u_r$ for every block and every label. Equality is allowed.

**Theorem 353.1 (Cancelling forks with compatible minima).** On each block set

$$
\rho_a=w_a,\qquad \rho_b=w_aw_b,\qquad \rho_d=w_bw_d\quad(d\in C).
\tag{353.3}
$$

Then

$$
 h(\rho(w))=c+\sum_{(a,b,C)}\left(Aw_a+Bw_aw_b+\sum_{d\in C}C_dw_bw_d\right)+\sum_{i\in I}\ell_iw_i.
\tag{353.4}
$$

If the full kernel is $k=k_0+h$ of mass $M$, where $k_0\ge0$ is an already stopped kernel satisfying $k_0(\rho(w))=k_0(w)$, and $k$ satisfies (348.4), then $k(\rho(w))$ has one complete stopped allocation of the same mass $M$ and satisfies the same literal rows. At $M=1$ this is an original same-cap replacement; for $M>1$ it is only an affine mass-$M$ statement.

*Proof.* The two fork terms become
$D_dw_aw_bw_d$ and $-D_dw_aw_bw_d$ and cancel. The $E$ and $\ell_b$ terms combine into $Bw_aw_b$, and the leaf terms become $C_dw_bw_d$, proving (353.4). For one label, the minimum of the block is
$-\max\{u_r,v_r+d_r\}$. The compatibility condition makes this
$-\max\{u_r,v_r\}-d_r$. Thus the coordinate thresholds are
$U_a=\max\{u,v\}$, $U_b=d$, $U_d=0$, and an isolated coordinate contributes $(-\ell_i)_+$. The coordinates of distinct blocks are disjoint, so these minima can be attained simultaneously for each label. Since $h(\rho(w))\ge0$, its constant vector dominates the sum of all thresholds.

Apply the 109.1 inverse to the transformed coefficients. With
$V_i=\sum_{j>i}(-Q_{ij})_+$ and $U_i=(V_i-\ell_i)_+$, the coordinate reserve is $c\ge\sum_iU_i$. Zero-sum coefficient masses give
$m(U_i)\ge\sum_{j>i}m((-Q_{ij})_+)$, so the same coordinate and scalar budgets hold. Use pair vectors in cells $0,10,11$, singleton vectors for the residuals and one empty vector; omit a zero-mass schedule instead of dividing by zero. Mix this allocation with the supplied invariant $k_0$ allocation. Every transformed coordinate is an original bit times an earlier bit, so the first zero and the positive word are fixed. The three independent rows, including the union row, are therefore inherited by the one resulting allocation. A common seed fixes all schedule cells in advance and uses at most two actual calls. $\square$

The C statement keeps every zero coefficient in the polynomial and every literal affine demand. It does not divide a mass-$M$ witness, invoke the mass-one H7 equality slice of XIX 345, or preserve an arbitrary input law. The compatibility condition is a sufficient method condition; failure is not an original obstruction. The cubic term produced by applying (353.3) to an unrelated interaction $Q_{ac}\ne0$ is a degree-three remainder, so the map simply falls outside its stated domain.

## 354. Shared source realization, horizon and tail

The five tests all consume the same operational interface. Given a certificate at a positive cap $e$, choose
$L=\max(\{i:a_i>e\}\cup\{0\})$. Every actual source with $n\le L$ receives the complete finite table for its full word, including all three independent rows. If $n>L$, the table sees $1^L$ and emits no tail mark; the exact error is

$$
\operatorname{TV}(p_{1^L},(1-a_n)e_0+a_ne_n)
 =\max\{1-p_{1^L}(0),a_n\}\le e.
\tag{354.1}
$$

Thus every positive nonincreasing vanishing tail, closed tie $a_{L+1}=e$, and zero coefficient remains in scope, with no summability assumption. The finite positive word is a table endpoint, not an infinite all-positive source. The case $L=0$ is the empty-output rule. The case $e=0$ is separate: the strictly positive marked family has no hard-two exact $N$ attainer by the earlier endpoint result 73.3.

For a mass-one certificate, partition one uniform seed into complete schedule masses and refine all terminal label intervals together. This produces one deterministic complete table before any reply and a finite measurable handoff on every finite construction. A pair uses its increasing addresses; $N$ pays both, while $O$ stops at the first queried zero. Repeats and ignored replies are charged. These are source operations, whereas the word maps in W, F, T, P and C are only proof transformations.

Whenever the relevant test supplies a mass-$M$ affine certificate (F, T, P and C do so; W is stated above as a normalized bridge), (348.4) is retained literally. The same allocation, not separately optimized rows, gives for every full nonnegative score at $L\ge3$

$$
F_{QY}(b,e)\le M\Delta_O(Y).
\tag{354.2}
$$

This is a conditional primal consumer for the displayed certificate. It is not the original requirement that, for every unit-$O$ score $y$, one unrestricted $V\ge0$ and one common $\theta\in[0,1]$ satisfy

$$
\Delta_N(V)+\theta\le1,\qquad
\sigma_{H_L}(Qy-QV)\le\theta.
\tag{354.3}
$$

## 355. Reuse, attribution and external hypotheses

The stopped coefficient criterion and constructive inverse are reused from 109.1; exact original class transport, common-conull source reduction and closed-cap necessity are reused from 110.2. The complete-table coupling is reused from II 140.2–140.3. The finite-word source proof is reused from Boundaries 35.2 and XVIII 315.3. XIX 341.2 supplies the complete $N$ coefficient cone, and XIX 343.1 supplies the aggregated outward-star calculation. No old proof is reproduced as a new theorem.

W credits only the displayed restricted raw-mass elimination; its conversion to a stopped allocation is VI 191–197. F credits current-coefficient face tests. T credits the same-$g$ edge/triangle certificate under both budgets; the star mechanism remains XV 258.3–258.4. P credits whole-vector cancellation among shared parents, and C records the deterministic fork/minimum companion. The H7 normalized equality classification of XIX 344–345 is a mass-one slice only. It cannot be applied to (348.4) by affine division. The earlier 0100 unqueried-label regression remains a method failure, and no arbitrary law-preservation condition is imposed in its place.

Blackwell, *Comparison of Experiments* (1951), §§2–3 and Theorem 2, assumes a finite family of measures on a Borel field, bounded finite-dimensional action/loss sets and comparison of entire attainable risk vectors over all decision problems. It does not provide the reverse factorization into this two-call increasing-stop catalog. Kaniewski–Lee–de Wolf, *Query complexity in expectation* (arXiv:1411.7280v1, Definitions 6 and 8, Theorem 9), treats nonnegative scalar outputs with maximum supported path depth; scalar rescaling does not provide a normalized labelled vector with equal counterfactual cell masses. The oriented-cut triangle identity used in T is the mature finite relation $d_{ik}-d_{ij}-d_{jk}\le0$; it supplies no acquisition or common-budget theorem by itself. These sources are background conditions for the stated comparisons, not premises of the conditional universal goal.

## 356. What remains open and how the evidence is bounded

The five tests prove conditional same-cap replacements whenever their explicit certificates exist. None proves that every feasible original $N$ profile has a representative satisfying one of them. In particular, the original universal alternative (354.3) remains open, and the strict alternative still requires one actual same-profile $N$ attainer together with a uniform strict lower against every original arbitrary-address, full-carrier $O$ competitor. The exact P example supplies an $O$ attainer, so it cannot be a strict separator. A failed W mass test, failed F derivative test, absent T certificate or failed C compatibility condition is failure of a sufficient method, not a lower bound.

The supplied exact rational checks evaluate the displayed finite identities and examples only: W checks the nested capacities and degenerate masses; F checks all $128$ words and eight labels in its seven-coordinate certificate; T checks finite certificates through $L=8$, including zero-$Q$ pairs and mass-zero cases; P checks the complete eight-word fork example; C checks its finite transformed tables. These checks do not establish a universal witness-selection theorem, a new amplitude region, a strict separator, a physical implementation, a current kernel or CI result, or a publication claim. The mathematical proofs above are ordinary finite-dimensional arguments with the explicit hypotheses shown.

## 追加锚（本行以下为增补区）
