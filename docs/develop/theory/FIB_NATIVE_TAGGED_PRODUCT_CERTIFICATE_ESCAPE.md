# Native asymmetrically tagged products and certificate escape

This `generic-v1` theory volume is ordinary mathematical reference input. It studies the ordered native tree model and late-target task of [*Escape from the recursive joint certificate calculus*, §§1–10][RCE]. Its construction pairs two asymmetrically tagged copies of a four-hash native support. The evidence ceiling is ordinary proof conditional on the credited source results; those suppliers are not independently verified here, and no Lean certification is asserted.

[The recursive-certificate volume][RCE] owns the native interface, core and four-hash construction, support-complete joint functional and tensorization, old-calculus acceptance characterization, and sound range extension. [*Native joint potential limits*][JPL] owns the exact restricted-core analysis, separable-language obstruction, and diagonal example already handled by the existing full joint leaf. The additions here are the actual tagged product, its rectangular admissibility theorem for arbitrary whole-block weights, exact pressure and full `V_rec+range` threshold, unbounded pointwise ratio, same-alphabet full-support escape, and charged rectangle realization. Section 8 gives the precise correspondences and their boundaries.

## 1. Native model and the inherited four-state core

Use the actual ordered trees

$$
\mathcal T ::= \alpha\mid\beta\mid\langle u,v\rangle,
\qquad h(\alpha)=h(\beta)=0,
\qquad h(\langle u,v\rangle)=1+\max(h(u),h(v)).
$$

The finite alphabets are

$$
S_1=\{\alpha,\beta,\langle\alpha,\alpha\rangle\},
\qquad
S_{r+1}=\{\alpha,\beta\}\sqcup\{\langle x,y\rangle:x,y\in S_r\}.
$$

Write $\varepsilon$ for the empty word, $|q|$ for word length, and $[m]=\{1,\ldots,m\}$. Every finite word in $L,R$, including $\varepsilon$, is a legal original-root literal. Its reply $r_t(a)$ is the encountered leaf label, $\mathsf{branch}$ at a pair, and $\mathsf{absent}$ after traversal has passed a leaf. Thus the reply alphabet is $\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$. Define

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,
\qquad \rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

For public $D\ge1$, the original source family and request sets are

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
W_D=\{q\in\{L,R\}^*:|q|\le D-1\},\qquad
\mathcal P_D=\{Rq:q\in W_D\}.
$$

One actual initial source $t\in\mathcal F_D$ remains stationary during preparation and acquisition; $\rho^kt$ specifies what is to be predicted. For any tree $u$ and finite word $q$, define its temporal factor $\Gamma_q(u)$ as follows. At a branch endpoint put $\Gamma_q(u)=(0,0)$. Otherwise let the first blocking leaf along $q$ have label $\ell$ at address $a$, and write $q=ab$. Set $e(\alpha)=0$, $e(\beta)=1$, and $s(b)=\#L(b)+2\#R(b)$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&b=\varepsilon,\\
(s(b)+2-e(\ell),\mathbf1_{b\text{ ends in }R}),&b\ne\varepsilon.
\end{cases}
$$

The factor law and the following all-count decoder are credited to [RCE, Convention 1.2][RCE]. For every attained factor $(b,c)$,

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1\text{ and }k=b-1,\\
\alpha,&c=1\text{ and }k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
$$

This is $r_{\rho^ku}(q)$ for every $k\ge0$. Conversely the trajectory determines $b$ as its first branch count and $c$ by whether an alpha stage occurs. Initially absent targets are included.

The credited canonical completion $\pi_D$ fixes $S_D$, preserves all $W_D$ replies and factors, and replaces a branch at depth $D-1$ by $\langle\alpha,\alpha\rangle$. The table of $W_D$ replies determines $\pi_D(v)$ for every $h(v)\le D$. On $S_D$, a length-$D$ reply is alpha exactly when its length-$(D-1)$ parent reply is branch, and is absent otherwise; longer words are absent. Thus every finite literal is a function of one boundary reply in the same actual block, or a constant. These are precisely the canonicalization and every-word premises of [RCE, Convention 1.2][RCE] and [JPL, Convention 1.3][JPL].

Preparation is a deterministic effective procedure initialized source-blind from $D$ and common installed tables, given no later request, terminating on every source, and acquiring source dependence only by charged literal Reads. Its complete export $E(t)$ contains every accessible surviving source distinction. Only after export is a public source-independent $p\in\mathcal P_D$ supplied. Using $E(t),D,p$ and common tables, a deterministic reader chooses zero Reads or one fresh Read of the same stationary source, before its reply and before any authentic count. Its predictor must answer $r_{\rho^kt}(p)$ for every subsequently supplied authentic $k\ge0$, without further Reads. Let $M_1(D)$ be the minimum attained cardinality $|E[\mathcal F_D]|$ over such jointly correct procedures. Handoff, access isolation, lawful entry, source continuity and authentication are the declared paid services of [RCE, Definition 1.1][RCE]. Acquisition, workspace, tables, address costs and physical time remain separate resources, as specified in Section 6.

Set

$$
A=\alpha,\quad B=\beta,\quad C=\langle A,A\rangle,
\quad J=\langle B,A\rangle,
$$

and define the four inherited core trees

$$
(u_0,u_1,u_2,u_3)=
(C,J,\langle C,C\rangle,\langle J,J\rangle)\subseteq S_3.
$$

The relevant native table is

$$
\begin{array}{c|cccc}
 &u_0&u_1&u_2&u_3\\\hline
r_L&\alpha&\beta&\mathsf{branch}&\mathsf{branch}\\
r_{RL}&\mathsf{absent}&\mathsf{absent}&\alpha&\beta\\
\Gamma_{LL}&(3,0)&(2,0)&(2,1)&(1,0)
\end{array}
$$

For completeness, the root reply is constantly branch; the $R$ replies are $(\alpha,\alpha,\mathsf{branch},\mathsf{branch})$; the $LL$ row equals the $RL$ row; and the $LR$ and $RR$ rows are $(\mathsf{absent},\mathsf{absent},\alpha,\alpha)$. Every word of length at least three is absent. These rows exhaust all finite words and prove the three-reply bound. The literal $L$ identifies every triple omitting $u_2$ or $u_3$; $RL$ identifies every triple omitting $u_0$ or $u_1$. Smaller nonempty subsets inherit one of these identifying literals. The four displayed $LL$ factors are distinct by the factor formula. This core and its identification property are inherited from [RCE, Definition 6.1 and Lemma 6.2][RCE], consistently with [JPL, Definition 2.1][JPL]; they are not a new motif.

## 2. Four-hash supports and the tagged product

For $h\ge0$, define the perfect ordered scaffold by $T_0(x)=x$ and

$$
T_{h+1}(x_1,\ldots,x_{2^{h+1}})
=\langle T_h(x_1,\ldots,x_{2^h}),
          T_h(x_{2^h+1},\ldots,x_{2^{h+1}})\rangle.
$$

All its $2^h$ frontier occurrences are actually present, with public addresses of length $h$, and ordered parsing makes its filling map injective. This is the scaffold of [RCE, Definition 4.1][RCE].

Let $m$ be even with $m\ge10$. Choose $h$ and a map

$$
H:[m]\times[2^h]\longrightarrow\{0,1,2,3\}
$$

such that every four distinct rows have a column on which all four symbols occur. A finite explicit choice is the construction of [RCE, Corollary 7.3][RCE]: take one column for each four-element subset of $[m]$, assign its four rows in increasing order the symbols $0,1,2,3$ and all other rows zero, then pad with constant-zero columns to a power of two. Each four-set is separated by its own column. No probabilistic hashing result is needed.

Let `c_j` be the public word of length `h` addressing column `j`, and put

$$
z_s=T_h(u_{H(s,1)},\ldots,u_{H(s,2^h)})\in S_{h+3}.
$$

A pair of different rows differs in a separating column after extending the pair to four rows, so the `z_s` are distinct actual trees. Put

$$
 a_s=\langle z_s,A\rangle,
 \qquad b_s=\langle z_s,B\rangle\in S_{h+4},
$$

and finally

$$
 v_{st}=\langle a_s,b_t\rangle,
 \qquad R=\{v_{st}:s,t\in[m]\}\subseteq S_d,
 \qquad d=h+5.
$$

Name the actual tagged sets

$$
P_A=\{a_s:s\in[m]\}=\{\langle z_s,A\rangle:s\in[m]\},\qquad
P_B=\{b_s:s\in[m]\}=\{\langle z_s,B\rangle:s\in[m]\}.
$$

Both lie in $S_{d-1}$ and have size $m$. They are disjoint because their right children have different leaf labels. The $m^2$ trees $v_{st}$ are distinct by ordered parsing, and $R=\{\langle a,b\rangle:a\in P_A,b\in P_B\}$. Let $\mu$ be uniform on $R$, so $\mu(v_{st})=1/m^2$ and it is zero elsewhere in $S_d$.

Every target on $R$ is constant, a function of the left row $s$, or a function of the right row $t$. A target entering a variable module has public prefix $LLc_j$ or $RLc_j$ and remaining suffix in $W_3$. Removing that prefix of actual branch nodes leaves the same blocking leaf and suffix in the factor formula, so its factor is exactly the core factor. A target stopping in fixed structure has branch factor $(0,0)$; one entering a fixed tag has a fixed factor, including when it passes that tag leaf. Hence every target has at most four values on all of $R$. Every finite literal likewise stops in fixed structure, enters a fixed tag, or returns one core reply, so it has at most three replies on $R$, including the empty word and words beyond a leaf. The four-valued separating targets are

$$
q^L_j=LLc_jLL,
\qquad q^R_j=RLc_jLL,
$$

of length `h+4=d-1`. A core-identifying query is obtained by replacing the final `LL` with `L` or `RL`. In the original source, prefixing by the initial `R` gives a charged original-root literal; no navigation operation is being added.

## 3. Exact rectangular admissibility and arbitrary whole-block weights

Use the full same-tuple admissibility of [RCE, Definition 1.3][RCE]. A nonempty $B\subseteq S_d^n$ is admissible if, for every coordinate $i$ and target $q\in W_d$, $\Gamma_q(x_i)$ is constant on $B$, or some donor $j$, boundary word $a\in W_d$ and total decoder $\delta:\mathcal A\to\Gamma_q(S_d)$ satisfy

$$
\Gamma_q(x_i)=\delta(r_{x_j}(a))\qquad(x\in B).
$$

Every equation holds on the same tuples. Donors may be reused, may equal $i$, and may form arbitrary cycles. Every finite donor word is allowed equivalently by the every-word simulation. A complete template chooses one equation for every target; its full simultaneous solution set contains every relation with those witnesses. Consequently nonnegative mass maxima over admissible relations and complete templates agree, as credited in [RCE, Definition 1.3][RCE]. For $B\subseteq R^n$, write $I_i(B)$ for its left row-index projection at coordinate $i$ and $J_i(B)$ for its right row-index projection.

**Theorem 3.1 (rectangular admissibility).** For every nonempty `B\subseteq R^n`, `B` is natively admissible exactly when

$$
|I_i(B)|\le3\quad\text{and}\quad |J_i(B)|\le3
\qquad(1\le i\le n).
$$

**Proof.** Suppose four left rows occur in coordinate `i`. Choose a separating hash column `j`. The target `q^L_j` takes the four distinct values shown in the core table on those four rows. Every possible donor coordinate ranges inside `R`, and every finite donor literal has at most three replies there. A decoder of one such reply, or a constant, has at most three values. Therefore no admissibility equation for `q^L_j` can hold on all tuples of `B`. The same argument with `q^R_j` proves the right bound. The four witnesses need not occur in one tuple; the target equation is required on the whole relation, so arbitrary correlations, donor reuse, self-donors, cycles, and cross-coordinate donors are covered.

Conversely, suppose both projections have size at most three. A target that ends above a variable module or enters a fixed tag is constant. Otherwise it enters one fixed module on one side. At that module the possible core states form a set of at most three states, and `L` or `RL` identifies that set. Prefix the identifying literal by the actual outer-child, tag-left edge, and hash-column address. Its one reply determines the requested factor on every tuple of `B`; unused reply symbols are assigned arbitrary decoder values. Doing this separately for every target gives a complete simultaneous family of admissibility equations. The witnesses are own-coordinate witnesses, so no factorization of `B` is used. ∎

Let `w_i:S_d\to[0,\infty)` be arbitrary weights supported on `R`, with all correlations between the two sides and all hash modules retained in one original block. Define

$$
Q(w_i)=\max_{\substack{I,J\subseteq[m]\\|I|,|J|\le3}}
\sum_{s\in I,\,t\in J}w_i(v_{st}).
$$

The empty rectangle has mass zero. A maximizing nonempty rectangle can always be chosen: if the maximum is positive this is automatic, and if it is zero any singleton rectangle attains it.

**Theorem 3.2 (exact whole-block pressure).** For every `n\ge1`,

$$
\max_{B\subseteq S_d^n\ \mathrm{admissible}}
\sum_{x\in B}\prod_{i=1}^nw_i(x_i)
=\prod_{i=1}^nQ(w_i).
$$

**Proof.** Delete rows of zero product weight from a competitor. The remaining relation is still admissible and lies in `R^n`. By Theorem 3.1 it is contained in

$$
\prod_i\{v_{st}:s\in I_i,t\in J_i\}
$$

for sets of size at most three. Nonnegativity and finite distributivity bound its mass by $\prod_iQ(w_i)$. If all rows have zero product weight, the same inequality is immediate. Conversely choose a nonempty maximizing rectangle $I_i\times J_i$ for each coordinate and take their Cartesian product. Theorem 3.1 makes this product admissible and its mass is exactly the displayed product. If some $w_i$ is identically zero, the same nonempty product is a zero-mass attainer. Every $w_i$ is used once as a whole-block weight; no marginal product has been substituted. ∎

Define, for any nonnegative whole-block weight $w$,

$$
A_n^{(d)}(w)=\max_{B\text{ admissible in }S_d^n}
                 \sum_{x\in B}\prod_{i=1}^nw(x_i),\qquad
\beta_d(w)=\sup_{n\ge1}A_n^{(d)}(w)^{1/n}.
$$

For the uniform law, a three-by-three rectangle has mass $9/m^2$, and Theorem 3.2 gives

$$
A_n^{(d)}(\mu)=\left(\frac9{m^2}\right)^n
\quad\text{for every }n\ge1,
\qquad
\beta_d(\mu)=\frac9{m^2}.
$$

The same equality holds for complete templates by the same-witness saturation just stated. The probability $\mu$ is normalized because it gives mass $1/m^2$ to exactly $m^2$ actual states.

## 4. The complete `V_rec+range` grammar

First specify the support-complete joint functional of [RCE, Definition 2.1][RCE]. A nonempty $P\subseteq S_d$ is range-feasible if $|\Gamma_q(P)|\le4$ for every $q\in W_d$. A target $q$ is hard on $P$ if no one boundary experiment, including a constant experiment, determines $\Gamma_q$ there. Let $\mathcal H(P)$ be the set of those hard targets and let $U_P(x)=(\Gamma_q(x))_{q\in\mathcal H(P)}$. For nonnegative $w$ put

$$
\kappa(w,P)^2=
\sum_y\left(\sum_{x\in P:U_P(x)=y}w(x)\right)^2,
\qquad
J_d(w)=\max_{\substack{\varnothing\ne P\subseteq S_d\\P\text{ range-feasible}}}
\kappa(w,P).
$$

An empty hard vector has one cell. Zero-weight states can be removed from this maximum: deleting them can only make more targets easy, so the restricted hard partition coarsens and its nonnegative cell norm cannot decrease. A support with no positive states has norm zero. For probabilities define

$$
\operatorname{TV}(\mu,\nu)=\frac12\sum_{x\in S_d}|\mu(x)-\nu(x)|.
$$

The joint-functional bound $|J_d(\mu)-J_d(\nu)|\le\operatorname{TV}(\mu,\nu)$ is [RCE, Lemma 2.2][RCE]. The pressure bound $|\beta_d(\mu)-\beta_d(\nu)|\le\operatorname{TV}(\mu,\nu)$ is the separately credited [RCE, Convention 1.4][RCE].

The grammar considered here is exactly [RCE, Convention 4.3 and Definition 8.1][RCE]: the old recursive grammar together with the finite range leaf. A label is $(d,\nu,C)$, where $\nu$ is a rational probability on the entire $S_d$ and $C>0$ is rational. A certificate is a finite list of justified labels whose last label is its input. Its nodes are:

1. An exhaustive old joint leaf checks $\kappa(\nu,P)^2\le C^2$ on every feasible positive support. A grouped joint leaf of any positive finite size $k$ makes the corresponding exhaustive tests on the product interface against $C^{2k}$, each experiment returning one constituent reply. A bounded-bundle leaf selects a nonempty bundle of hard targets on each feasible support of mass greater than $C$ and checks its squared cell norm against $C^2$; supports of mass at most $C$ need no bundle.
2. A one-parent scaffold node from $(d_0,\nu,C_0)$ has $d=d_0+r$ for $r\ge0$ and output law $\nu^\uparrow$. At $k=2^r$, this law assigns $\prod_{i=1}^k\nu(x_i)$ to $T_r(x_1,\ldots,x_k)$ and zero off that image. Its cap satisfies $C\ge C_0^{2^r}$.
3. A same-depth one-parent stability node from $(d,\nu,C_0)$ to $(d,\mu,C)$ has $C\ge C_0+\operatorname{TV}(\mu,\nu)$.
4. A range leaf has declared finite support $P\subseteq S_d$ and $1\le r\le\min\{4,|P|\}$. Its law vanishes off $P$; every boundary experiment has at most $r$ replies on $P$; every $(r+1)$-subset of $P$ has a target taking more than $r$ values on that subset; and every target has a supplied constant or own-coordinate witness on every $r$-subset of $P$. Its cap is at least the sum $L_r(\nu)$ of the $r$ largest weights on $P$, counting zeros.

All tables, subsets, equations, probabilities, and rational inequalities are checked finitely; incomplete or malformed data are rejected. In particular declared zero-weight and off-$R$ states are still subject to the range leaf's structural conditions. When $|P|=r$, its separation condition is vacuous but its own-coordinate conditions remain. There is no heterogeneous-product, superposition, conditioning, or other unlisted inference rule. The extended grammar is sound for all native lengths and complete templates by [RCE, Theorem 8.2][RCE].

The old-calculus characterization [RCE, Theorem 4.4][RCE] says that its finite derivations accept a rational label exactly when $C\ge J_d(\nu)$; an exhaustive ungrouped leaf already suffices at that same cap. Its tensorization theorem concerns product weights on product interfaces with individual targets and single-constituent experiments, while retaining every correlated feasible support. Those hypotheses will be verified below. It does not assert that arbitrary whole-block weights factor.

**Theorem 4.1 (exact threshold on the tagged product).** For every rational `C>0`, the full finite grammar accepts `(d,mu,C)` if and only if

$$
C\ge\frac1m.
$$

**Proof, acceptance.** Consider first the uniform probability on $\{z_s:s\in[m]\}$. Every subset $Q$ is range-feasible because each target is constant or enters one four-state core module. If $1\le|Q|\le3$, each target is determined by a prefixed core-identifying literal, so the hard vector is empty and its norm is $|Q|/m$.

If $|Q|\ge4$, fix any two distinct rows of $Q$ and choose two further rows in $Q$. A column separating these four makes its $LL$ target four-valued on $Q$. Every experiment has at most three replies on $Q$, so this target is hard on $Q$, and it distinguishes the chosen pair. Repeating this argument for each pair shows that the joint vector of all hard targets is injective on $Q$. Its norm is consequently $\sqrt{|Q|}/m$. The full support attains $1/\sqrt m$, and

$$
\max\{3/m,1/\sqrt m\}=1/\sqrt m
\qquad(m\ge10),
$$

since $9<m$. Adding a fixed right tag only introduces constants and public prefixes of the original interface: every variable target and experiment is realized by prefix $L$, and every new target or experiment is of this form or constant. Thus both uniform tagged marginal laws on the explicitly named sets $P_A=\{\langle z_s,A\rangle:s\in[m]\}$ and $P_B=\{\langle z_s,B\rangle:s\in[m]\}$ have the same joint value $1/\sqrt m$.

The paired support $R$ is exactly the product interface of those two tagged sets. Root targets are constants; every other target or experiment is an individual constituent target or experiment, or a constant. Conversely prefixing by $L$ or $R$ realizes every constituent target and experiment within $W_d$. The chosen uniform law $\mu$ is the product of the two uniform tagged laws. After the zero-weight reduction, [RCE, Theorem 3.4][RCE] therefore applies to every feasible support, including correlated supports on which cross-factor donors can make a marginal hard target easy. It yields

$$
J_d(\mu)=\left(\frac1{\sqrt m}\right)^2=\frac1m.
$$

An actual finite threshold certificate is the following exhaustive ungrouped old leaf. Its label is $(d,\mu,1/m)$; its data contain the full native target and reply tables, and, for every nonempty $Q\subseteq R$, the list of hard targets and their cells, with mass $|\{x\in Q:U_Q(x)=y\}|/m^2$ in cell $y$. These are all positive supports and all are range-feasible. The established joint bound proves every squared cell sum at most $1/m^2$. All entries and squared comparisons are rational and finite. Zero-weight supports outside $R$ are covered by the zero-weight reduction. Hence these specified tables pass exactly the old leaf's tests. This uses tensorization to justify the tables, not as an additional grammar rule. The same leaf accepts every larger rational cap.

**Proof, lower bound.** Every nonleaf rule has one parent, so follow any accepted finite derivation along its unique ancestry to its initial leaf. Height-zero scaffolds preserve the law and cannot lower the cap. Successive stability increments sum to at least the total variation between their endpoint laws. If a positive-height scaffold occurs, take the last one, of height $r\ge1$. Its output $\sigma$ has the final depth $d$, and its two root children are independent with the same law $\eta=\nu^{\uparrow(r-1)}$ on $S_{d-1}$, for its arbitrary parent law $\nu$. Since $P_A$ and $P_B$ are disjoint,

$$
\sigma(R)=\eta(P_A)\eta(P_B)\le\frac14,
$$

Indeed, writing the two factors as $x,y$, one has $4xy\le(x+y)^2\le1$. Since $\mu(R)=1$, $\operatorname{TV}(\mu,\sigma)\ge\mu(R)-\sigma(R)\ge3/4$. After the last positive scaffold only stability and identity nodes remain, so the final cap is at least $3/4$, whatever leaves, rational laws or scaffold heights preceded it.

Assume now that no positive scaffold occurs and the initial leaf is old, with arbitrary law $\nu$ and cap $C_0$. An exhaustive joint leaf directly gives $C_0\ge J_d(\nu)$. For a grouping of any size $k$, [RCE, Theorem 3.4][RCE] gives maximum joint norm $J_d(\nu)^k$, so its squared tests against $C_0^{2k}$ give the same bound. For a bundle leaf, the full hard partition refines the selected bundle partition on every heavy support, and its nonnegative cell norm is no greater than the checked bundle norm. On each light support its norm is at most its mass, which is at most $C_0$. Thus every old leaf has $C_0\ge J_d(\nu)$, with all feasible supports retained. Stability and the triangle inequality give

$$
C\ge J_d(\nu)+\operatorname{TV}(\mu,\nu)\ge J_d(\mu)=1/m.
$$

This includes every rational ancestor law, all zero and off-support states, every grouping size, and every bounded bundle.

It remains to consider a range leaf. Let `P` be its arbitrary declared support and `r\in\{1,2,3,4\}`. We only use necessary range conditions, so retaining its own-coordinate checks can only reduce the possible leaves. For `r=1`, two distinct points of `P\cap R` differ in a hash row and are separated by a prefixed `L` or `RL` literal, contradicting the one-reply condition. Hence `|P\cap R|\le1`.

For $r=2$ or $r=3$, partition each copy of $[m]$ into pairs; here evenness is used. The resulting $m^2/4$ disjoint four-corner rectangles partition $R$. On any one rectangle every target is constant or depends on only one side, hence has at most two values. For $r=2$, three retained corners violate the requirement of more than two target values on that triple. For $r=3$, four retained corners violate the requirement of more than three target values on that four-set. Thus

$$
|P\cap R|\le m^2/2\quad(r=2),
\qquad
|P\cap R|\le3m^2/4\quad(r=3).
$$

For $r=4$, every target has at most four values on all of $R$, so five retained points violate the required separation and $|P\cap R|\le4$. These arguments also cover $|P|=r$ and arbitrary zero-weight or off-$R$ states in $P$: none repairs a violation on a subset lying inside $R$. Since $\nu$ vanishes outside $P$,

$$
\operatorname{TV}(\mu,\nu)\ge1-\frac{|P\cap R|}{m^2}.
$$

The four cases give respectively

$$
1-\frac1{m^2},\quad\frac12,\quad\frac14,\quad1-\frac4{m^2}.
$$

For $m\ge10$, the first and fourth bounds are at least $99/100$ and $24/25$, respectively, while the middle bounds are $1/2$ and $1/4$. Thus each is at least $1/4$. The range-leaf cap is nonnegative, and later stability costs add at least this distance. Every derivation beginning at a range leaf therefore has final cap at least $1/4\ge1/m$. The three ancestry cases exhaust the grammar. ∎

The exact accepted cap is therefore `1/m`, while the true all-length pressure is `9/m^2`. The pointwise ratio is

$$
\frac{1/m}{9/m^2}=\frac m9,
$$

which is unbounded over the even integers $m\ge10$: for any prescribed bound choose an even $m$ greater than nine times that bound and at least ten, and use Section 2's finite construction. This is a pointwise limitation of this precise grammar. It does not refute optimized cofinality, because the optimizer may choose another probability on the same full alphabet.

## 5. Same-alphabet full-support separation

Use the explicit binary construction of [RCE, Proposition 7.1][RCE], identifying $[16]$ with the rows $s\in\mathbb F_2^4$ in binary order. For each two-dimensional subspace $U$ of the dual $(\mathbb F_2^4)^*$ choose its first ordered basis $(\ell_1,\ell_2)$ in the lexicographic binary order, and define its column by

$$
H(s,U)=2\ell_1(s)+\ell_2(s)\in\{0,1,2,3\}.
$$

There are fifteen nonzero dual vectors. After choosing a first one, fourteen lie outside its one-dimensional span and can be the second basis vector. Each two-dimensional subspace has three possible first nonzero vectors and two possible second ones, hence six ordered bases. Every independent ordered pair spans exactly one such subspace, so the column count is

$$
\frac{15\cdot14}{3\cdot2}=35.
$$

To prove separation, translate any four distinct rows so that one is zero and the others are $a,b,c$. Their span has dimension two or three. In dimension two they are its three nonzero vectors; an isomorphism of that span onto $\mathbb F_2^2$ sends them to the three nonzero outputs. In dimension three they are a basis; prescribe those same three distinct nonzero outputs to define a surjective linear map. In either case extend a basis of the span to a basis of $\mathbb F_2^4$ and choose any images for the additional vectors. The resulting map has two independent component functionals, spanning a listed dual subspace $U$. Replacing the components by the selected basis of $U$ applies an invertible linear map to the output and preserves its four distinct values. Undoing the initial translation adds the same output to all four values, also preserving distinctness. Thus the column $U$ separates the original four rows.

Append twenty-nine constant-zero columns. Since $35+29=64=2^6$, this gives a separating hash with $m=16$, $h=6$, and $d=h+5=11$. Section 2 therefore gives $16^2=256$ distinct actual tagged-product states on the same native alphabet $S_{11}$.

Let $u$ be uniform on all of $S_{11}$, set $\delta=1/256$, and define

$$
\mu_\delta=\frac{255}{256}\mu+\frac1{256}u.
$$

Every state has mass at least $1/(256|S_{11}|)>0$. The mixture is rational and normalized since both constituent laws are probabilities and $255/256+1/256=1$. Moreover

$$
\operatorname{TV}(\mu_\delta,\mu)
=\frac1{256}\operatorname{TV}(u,\mu)\le\frac1{256}.
$$

The pressure stability inequality of [RCE, Convention 1.4][RCE] gives

$$
\beta_{11}(\mu_\delta)
\le\frac9{256}+\frac1{256}
=\frac5{128}.
$$

Because $\beta$ is the supremum over all finite lengths, this is the simultaneous bound

$$
A_n^{(11)}(\mu_\delta)\le\left(\frac5{128}\right)^n
\quad(n\ge1).
$$

If the full grammar accepted $(11,\mu_\delta,C)$, append the legal stability node from $\mu_\delta$ back to $\mu$. Its final cap is the positive rational number $C+\operatorname{TV}(\mu_\delta,\mu)$, and the exact threshold above forces

$$
C+\operatorname{TV}(\mu_\delta,\mu)\ge\frac1{16}.
$$

Since $\operatorname{TV}(\mu_\delta,\mu)\le1/256$, every accepted cap satisfies

$$
C\ge\frac1{16}-\frac1{256}=\frac{15}{256}.
$$

The rational inequalities

$$
\frac5{128}=\frac{10}{256}<\frac3{64}=\frac{12}{256}<\frac{15}{256}
$$

show that `C=3/64` is a valid strict all-length pressure cap rejected by every finite `V_rec+range` certificate on this same full-support probability and same `S_{11}`. No support argument has been moved to another alphabet.

The diagonal obstruction of [JPL, Theorem 6.4][JPL] concerns exactly its finite nonnegative separable-majorant language with scalar cap summation; [JPL, Proposition 7.1][JPL] shows that the existing full joint leaf already accepts that diagonal law at its exact pressure. The present obstruction concerns the entire $V_{\mathrm{rec+range}}$ grammar on the tagged product. Its threshold accounts for every old leaf, positive scaffold, arbitrary range support and stability ancestor. Neither obstruction is a statement about every certificate language.

## 6. Charged full-family realization in the original model

Fix three left rows `I\subseteq[m]` and three right rows `J\subseteq[m]`, and write

$$
R_0=\{v_{st}:s\in I,t\in J\}.
$$

For $H\ge0$, let $n=2^H$ and $D=d+H$. The actual scaffold family $T_H(R_0^n)$ has exactly $9^n$ distinct members of $S_D$. For every original source $t=\langle\alpha,v\rangle$ with $h(v)\le D$, preparation submits every original-root word $Rq$ with $q\in W_D$, including replies that are absent. The canonicalization premise stated in Section 1 says this finite table determines $\pi_D(v)$ and preserves every boundary reply and temporal factor, exactly as in [RCE, Theorem 9.1][RCE] and [JPL, Proposition 8.2][JPL].

Assign one complete name to the whole canonical family `T_H(R_0^n)` and a separate complete name to every other canonical state. Every name is attained by an actual canonical source. The attained alphabet is therefore exactly

$$
|S_D|-9^{2^H}+1.
$$

The preparation uses `2^D-1` charged Reads, maximum literal length `D`, and

$$
\sum_{\ell=0}^{D-1}(\ell+1)2^\ell=(D-1)2^D+1
$$

submitted address letters. The Read count sums the $2^\ell$ words at each level. The letter-sum identity has base $D=1$; replacing $D$ by $D+1$ adds $(D+1)2^D$ to $(D-1)2^D+1$ and gives $D2^{D+1}+1$. The installed tables and padded finite computation schedule depend only on public $D$ and the public construction. The complete exported name is fixed width. All accessible selectors, buffers, controls, operands, lengths, allocation distinctions, counters, handles and timing distinctions are functions of that name and public data under the separately paid handoff and access-isolation service of [RCE, Definition 1.1][RCE]. This is a resource accounting statement under those model assumptions, not a derived physical erasure or storage capability.

After export, the public request is supplied before any authentic count. A singleton name answers from its installed canonical table with no Read. On the merged name, a target stopping in the outer scaffold, product/tag wrappers or inner hash scaffold has branch factor $(0,0)$. A target entering a fixed tag has a constant factor, even if it passes the leaf. Every remaining target enters one variable core module. That side has at most three possible rows and therefore at most three possible core states. Choose its identifying $L$ or $RL$ literal before receiving its reply and before every count. Prefix it by the original root $R$, the height-$H$ scaffold address, the selected outer-child edge, the tag-left edge and the hash-column address. Its length is at most

$$
1+H+1+1+h+2=D.
$$

It is one fresh Read of the same stationary source at an actual original-root word. On the canonical merged fiber the queried occurrence is present, and canonicalization preserves the reply and the requested factor for every original source with that name. The factor decoder then answers all later authentic counts, including an initially absent target. Preparation work, temporary storage, common tables, post-request workspace, predictor size, count representation, and physical time remain separate resources. No subtree, identity, equality, copying, reset, age, advice, quantum, or free-navigation port is introduced.

For the lower transport, use the same-source correspondence of [RCE, Corollary 9.2][RCE] and [JPL, Corollary 8.1][JPL] with the new pressure. More explicitly, restrict any correct complete original code at depth $D$ to the actual sources whose right subtrees are $T_H(x_1,\ldots,x_n)$ with $x_i\in R$. Fix one nonempty attained code fiber. Every original-root literal is an outer constant, a scaffold constant, or a function of one boundary reply in one actual block, by the every-word simulation of Section 1. Every block target becomes the legal original request $Ra_iq$, where $a_i$ is its public scaffold address and $q\in W_d$.

For this fixed name and request the reader's zero-Read or one-Read choice is fixed before its reply and every count. Two tuples of the fiber giving the same chosen reply must therefore have the same predicted trajectory for all counts. Correctness and the factor-to-trajectory inverse of Section 1 force their target factors to agree. The factor is consequently a function of that one reply; with zero Reads it is constant. Extend the decoder to unused replies. Thus this same fiber is admissible, with all original donor choices, correlations, repeated donors, cycles and off-target words retained. No fibers are split and no common donor is imposed on different targets.

Under the probability law $\mu^n$, Theorem 3.2 bounds each such fiber by $(9/m^2)^n$. The disjoint restricted fibers have total mass one. Counting unchanged complete names yields, for every original competitor and every $D\ge d$,

$$
M_1(D)\ge
\left\lceil\left(\frac{m^2}{9}\right)^{2^{D-d}}\right\rceil,
\qquad
\lambda\ge2^{-d}\log_2\left(\frac{m^2}{9}\right).
$$

The realization is deliberately nonoptimal. These inequalities follow from the credited native correspondence with the proved new pressure; they give neither an exact formula for $M_1(D)$ nor a sharp value of $\lambda$.

## 7. Ownership and exact remaining targets

The native interface, core and hash family, support-complete $J$, its tensorization, old-grammar collapse and range-leaf soundness belong to [RCE][RCE]. The exact restricted-core and diagonal/separable-language results belong to [JPL][JPL]. The additions here are the actual tagged product, exact rectangular theorem for arbitrary correlated whole-block weights, exact $V_{\mathrm{rec+range}}$ threshold, unbounded pointwise ratio, same-alphabet full-support separation, and charged nine-state realization and transport. Section 8 specifies which hypotheses permit each reuse.

The optimized quantities remain open. Define

$$
 c_+(d)=\inf\{C:\text{some rational probability on }S_d
 \text{ has a finite }V_{\mathrm{rec+range}}\text{ certificate at cap }C\},
$$

Here the infimum is over rational $C>0$ as well. Let $K_d(n)$ be the least number of admissible sets covering $S_d^n$, and define

$$
\sigma_d=\inf_{n\ge1}\frac{\log_2K_d(n)}n,\qquad
b_d=\min_{\nu\in\Delta(S_d)}\beta_d(\nu)=2^{-\sigma_d},\qquad
\lambda=\lim_{D\to\infty}2^{-D}\log_2M_1(D)
       =\sup_{d\ge1}2^{-d}\sigma_d.
$$

Here $\Delta(S_d)$ is the simplex of all probabilities, including irrational ones; logarithms are base two. The attained pressure minimum and rate identities are credited in [RCE, Convention 1.4][RCE]. Soundness gives $b_d\le c_+(d)$; singleton supports also give $b_d\ge1/|S_d|>0$, so the logarithms below are defined. The bad tagged probabilities do not prove $c_+(d)>b_d$, since optimization may select another probability. The exact fixed-depth question $c_+(d)=b_d$ for every $d$, or a genuine optimized counterexample, remains **open**.

Writing

$$
L_+(d)=-2^{-d}\log_2c_+(d),
$$

the exact gap decomposition is

$$
\lambda-L_+(d)
=\bigl(\lambda-2^{-d}\sigma_d\bigr)
 +2^{-d}\log_2\frac{c_+(d)}{b_d}.
$$

For $U_0=1$, $U_{r+1}=1+U_r^2$, and $\phi=\lim_r2^{-r}\log_2U_r\in[0,1]$, the inherited first term lies in $[0,2^{-d}\phi]$. Both terms are nonnegative. Thus $L_+(d)\to\lambda$ holds exactly when the normalized certificate gap $2^{-d}\log_2(c_+(d)/b_d)$ tends to zero. That convergence remains **open**; terminating two-sided original-rate approximation additionally requires effective error control. Pointwise incompleteness supplies neither obligation. Sharp $\lambda$, general exact $M_1(D)$ and that effective approximation remain **open**. The unchanged inherited numerical results, credited in [RCE, §9][RCE] and [JPL, §8][JPL], are

$$
\frac18\log_2(33/13)\le\lambda<\frac3{16},\qquad M_1(3)=4.
$$

No conclusion is drawn about native noncomputability, every possible certificate language, global recoloring, hidden-history recovery, physical storage, empirical machine learning, general neural or kernel conclusions, or completion of the broader internal-observer programme. The operational conclusion remains the one stated in [RCE, Open problem 10.2][RCE]:

$$
(E(t),D,p,\text{at most one actual reply})
\longrightarrow \Gamma_p(t)
\longleftrightarrow (r_{\rho^kt}(p))_{k\ge0}.
$$

## 8. Canonical sources and mathematical correspondence

The results here are `repo-derived` ordinary deductions. The two owning volumes below are credited mathematical suppliers, including the explicitly attributed results they reuse; their nested suppliers are not independently verified here. The stated interface and paid services are hypotheses. Ordinary proof is the evidence ceiling, and no Lean/kernel verification, physical implementation, external-literature novelty or global-priority claim is asserted.

| Canonical owning volume | Exact result and matching hypotheses |
| --- | --- |
| [*Escape from the recursive joint certificate calculus*, §1][RCE] | Definitions 1.1 and 1.3 fix the same stationary $\langle\alpha,v\rangle$ sources, complete paid export, all finite literal queries, all-count correctness and same-tuple arbitrary-donor admissibility used in Sections 1, 3 and 6. Convention 1.2 supplies factors, their inverse trajectory correspondence, canonicalization and every-word simulation on the same actual blocks; Convention 1.4 supplies pressure stability, attained minimization and original rate identities. These statements do not derive the paid services. |
| [*Escape from the recursive joint certificate calculus*, §§2–4][RCE] | Definition 2.1 and Lemma 2.2 supply the support-complete hard-target functional, zero-weight reduction and its probability-TV bound. Theorem 3.4 tensorizes product weights on product interfaces with individual targets and single-constituent experiments, while allowing every correlated feasible support. Section 4 verifies those interface hypotheses on the two tagged sets and uses factorization only for the chosen uniform $\mu$. Convention 4.3 and Theorem 4.4 characterize precisely the old joint/group/bundle, unary scaffold and stability rules. There is no heterogeneous-product rule. |
| [*Escape from the recursive joint certificate calculus*, §§6–8][RCE] | Definition 6.1 and Lemma 6.2 own the four-state core and triple witnesses. Definition 6.3 and Corollary 7.3 own the finite four-hash support construction; Proposition 7.1 owns the sixteen-row dual-plane construction whose count and separation argument are given in Section 5. Definition 8.1 and Theorem 8.2 supply the exact $r=1,2,3,4$ range leaf and its all-length soundness, including zero weights. The new threshold concerns that entire extended grammar. |
| [*Escape from the recursive joint certificate calculus*, §§9–10][RCE] | Theorem 9.1 and Corollary 9.2 supply the paid full-family acquisition and same-source mass-transport pattern used with the new nine-state rectangles. Proposition 10.1 and Open problem 10.2 distinguish pointwise gaps from optimized cofinality and effective original-rate convergence. The numerical interval and $M_1(3)=4$ remain credited results. |
| [*Native joint potential limits*, §§2–4][JPL] | Lemma 2.3 translates selected single donors in both directions at a fixed actual scaffold, preserving the same rows and correlations. Theorems 3.1 and 3.3 give lossless completion and exact pressure for arbitrary once-owned weights supported on its core scaffolds $U_h=T_h(\{u_0,u_1,u_2,u_3\}^{2^h})$. Theorems 4.1 and 4.3 give the optimizer ceiling only for that restricted core atlas and its stated closure rules. They are not universal projection or optimizer theorems for tagged products or arbitrary native supports. Section 3 proves the needed tagged-product rectangle theorem separately. |
| [*Native joint potential limits*, §§5–7][JPL] | Theorem 5.2 gives the exact repeated-motif diagonal pressure. Definition 6.1 and Theorem 6.4 concern only finite nonnegative separable majorants, scalar cap summation, remainder and the listed same-depth closure rules. Proposition 7.1 supplies an exhaustive existing joint leaf at the diagonal law's exact pressure, so that obstruction is already bypassed by the old full joint rule. It is distinct from the whole $V_{\mathrm{rec+range}}$ obstruction of Sections 4–5. |
| [*Native joint potential limits*, §§8–9][JPL] | Corollary 8.1 and Proposition 8.2 retain every original competitor and canonical fiber under charged original-root acquisition; their correspondence uses the same full assignment and the paid complete-export premises. Open problem 9.3 leaves original optimizer-cofinality and effective two-sided convergence unresolved. No physical-storage or broader recovery bridge follows. |

[RCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RECURSIVE_CERTIFICATE_ESCAPE.md
[JPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_JOINT_POTENTIAL_LIMITS.md

## 追加锚（本行以下为增补区）
