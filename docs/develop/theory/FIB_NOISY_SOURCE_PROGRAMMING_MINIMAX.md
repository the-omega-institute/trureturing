# FIB noisy source programming: attained unrestricted minimax for all parameters

For every finite integer $m\ge0$ and every known $t,\eta\in[0,1]$, programming from the four prescribed original source states has the attained unrestricted value

$$
e_m(t,\eta)=[c-D_m(t,\eta)]_+,\qquad c=(1-\eta)t.
$$

One common processor attains this error simultaneously for all four labels. The converse covers every complex CPTP processor on the entire data/program algebra, with every finite complex reference. The programs, original cut, target channels and initial copy/data/reference independence are fixed below. Separate conditional diagonal budgets, certified by a first-occurrence statistic on the actual program words, supply the attainment. Exactness is equivalent to $D_m\ge c$, determining the minimum prescribed-copy threshold. N1–N3 remain useful explicit constructions and special consequences. All proofs are ordinary finite-dimensional mathematics; no Lean or kernel certification is asserted.

## 1. Original sources, targets and unrestricted task

**Definition 1.1 (Original coordinates and four labels).** Retain the original cut $A\mid B$, the ordered labels $B=(0,1,2,3,13)$ and $f=(0\ 13)(1\ 3)$, with $f(2)=2$. Write $e_0,\ldots,e_4$ for coefficient coordinates, $E_{jk}=|e_j\rangle\langle e_k|$, and retain the fixed identifications

$$
Ve_j=|B_j\rangle_A,\qquad We_j=|f(B_j)\rangle_B,\qquad
Je_j=|B_j,f(B_j)\rangle.
$$

Each local support is five-dimensional; their tensor product has dimension $25$. These identifications preserve the original labels and cut. Define

$$
X_a=i(E_{04}-E_{40}),\qquad X_b=i(E_{13}-E_{31}),\qquad
U_4=\{X_a,-X_a,X_b,-X_b\}.
$$

The active coordinate pairs are $(0,4)$ and $(1,3)$, corresponding to the original label pairs $(0,13)$ and $(1,3)$. Each $X$ is Hermitian, has zero diagonal and spectrum $1,-1,0,0,0$.

**Definition 1.2 (Associated target and actual program).** For known $t,\eta\in[0,1]$ and one fixed unknown $X\in U_4$, set

$$
\begin{aligned}
\Phi_{t,\eta,X}(Y)&=(1-\eta)(I_5+tX)\circ Y
                    +\eta\operatorname{tr}(Y)I_5/5,\\
\rho_{t,\eta}(X)&=\frac{1-\eta}{5}J(I_5+tX)J^\dagger+\eta I_{25}/25.
\end{aligned}
\tag{1.1}
$$

Here $\circ$ is entrywise multiplication and $I_{25}$ is the identity on the entire original local-support tensor product, including its twenty-dimensional nonmatching subspace. The target is defined on every $Y\in M_5(\mathbb C)$. The positive matrix $I_5+tX$ has diagonal one, so its Schur multiplier is completely positive and trace preserving (CPTP); the replacement term is CPTP. The source is positive with trace one. Neither assertion requires strict positivity.

The normalized output-first Choi correspondence is

$$
\chi(\Phi)=\frac15\sum_{j,k=0}^4\Phi(E_{jk})\otimes E_{jk},\qquad
(V\otimes W)\chi(\Phi_{t,\eta,X})(V\otimes W)^\dagger=\rho_{t,\eta}(X).
\tag{1.2}
$$

Indeed, the Schur term is $J(I_5+tX)J^\dagger/5$ and the replacement term is $I_{25}/25$. The output partial trace of $\chi$ is $I_5/5$. This identifies the source associated with a target; it does not supply a common simulator for an unknown Choi state.

**Definition 1.3 (Prescribed independent batches and full-algebra processors).** For an integer $m\ge0$, the actual program is exactly $\rho_{t,\eta}(X)^{\otimes m}$ on $P_m=(\mathbb C^5\otimes\mathbb C^5)^{\otimes m}$. Conditional on the same fixed $X$, copies are independent of one another and initially independent of the entire data and reference state. At $m=0$, $P_0=\mathbb C$ and the program is the scalar state $1$. There is no prior distribution on $X$.

A competitor is one label-independent complex CPTP map

$$
\mathcal P_m:M_{5\cdot25^m}(\mathbb C)\longrightarrow M_5(\mathbb C),\qquad
N_X(Y)=\mathcal P_m(Y\otimes\rho_{t,\eta}(X)^{\otimes m}).
$$

It must be valid on the entire joint algebra, including correlated data/program inputs and programs outside the promised family. Only the stipulated independent batches are used in evaluating

$$
e_m(t,\eta)=\inf_{\mathcal P_m\ {\rm CPTP}}\max_{X\in U_4}
 \|N_X-\Phi_{t,\eta,X}\|_\diamond.
\tag{1.3}
$$

The diamond norm is unhalved and includes every finite complex reference, which is never acted on. Equivalently for differences of channels it is the supremum of the output trace norm over all such reference/data states. Competitors have no measurement, Schur, covariance, real-input or product-data restriction. A chosen program curve, selected eigenstate, classical label, postselection or free additional copy cannot replace the actual program.

Program preparation, the joint measurement, exact complex controls and any spatial communication are supplied services with the costs in Sections 9–10. The abstract minimax (1.3) permits a joint processor; it does not itself make separated-party access free.

**Notation 1.4 (Parameters).** Throughout this volume put

$$
\begin{aligned}
c&=(1-\eta)t,&s&=1-4\eta/5,&w&=s/5,&u&=c/5,\\
\nu&=1-4w=w+20\eta/25,&\gamma&=s-c=(1-\eta)(1-t)+\eta/5.
\end{aligned}
\tag{1.4}
$$

Thus $1/5\le s\le1$, $0\le c\le s$, $0\le u\le w$, and $\nu\ge1/5$. Write $[x]_+=\max(x,0)$ and use $0^0=1$ in finite probability formulas.

## 2. The six-outcome original-copy experiment

**Proposition 2.1 (Complete commuting laws and original trace distance).** Define the five matching vectors

$$
|a_\epsilon\rangle=J(e_0-i\epsilon e_4)/\sqrt2,\qquad
|b_\epsilon\rangle=J(e_1-i\epsilon e_3)/\sqrt2,\qquad
|o\rangle=Je_2,\qquad \epsilon\in\{1,-1\},
$$

and the rank-$20$ projection $\Pi_*=I_{25}-JJ^\dagger$. The projections onto these five vectors and $\Pi_*$ form one fixed six-outcome PVM, with outcomes $a_+,a_-,b_+,b_-,o,*$. Under $X=\sigma X_a$ its law is

$$
p_{a,\sigma}=(w+\sigma u,w-\sigma u,w,w,w,20\eta/25).
\tag{2.1}
$$

The law $p_{b,\sigma}$ interchanges the two $a$ entries with the two $b$ entries. Product-copy outcomes have the product law $p_X^{\otimes m}$. The four states commute, and the opposite-source half trace distance is exactly

$$
\begin{aligned}
D_m(t,\eta)
&=\frac12\|\rho_{t,\eta}(X_a)^{\otimes m}
             -\rho_{t,\eta}(-X_a)^{\otimes m}\|_1\\
&=\frac12\sum_{r+q+k=m}\frac{m!}{r!q!k!}(1-2w)^k
 \left|(w+u)^r(w-u)^q-(w-u)^r(w+u)^q\right|.
\end{aligned}
\tag{2.2}
$$

The sum is over nonnegative integers. The opposite-$b$ value is identical. In particular $D_0=0$, $D_1=2c/5$, and for $m\ge1$, $1\ge D_m\ge D_1$.

Proof. The coefficient vectors $(e_0-i\epsilon e_4)/\sqrt2$ are eigenvectors of $X_a$ with eigenvalue $\epsilon$; the corresponding $b$ vectors diagonalize $X_b$. The matrices act on disjoint pairs. On the matching subspace the five eigenvalues of the source are the five matching entries in (2.1). On the orthogonal complement every eigenvalue is $\eta/25$, with multiplicity twenty. This proves the laws and a common complete eigenbasis. On tensor powers the trace norm of the difference is the sum of absolute eigenvalue differences. Inside $*$ all twenty probabilities are identical for every label; summing them retains the trace norm, including for product strings.

For opposite $a$ labels, every nondistinguished outcome has the same probability under both laws, with total mass $1-2w$. Group those outcomes and let $r,q$ count $a_+,a_-$. The multinomial expansion gives (2.2). It includes zero probabilities and the empty string, for which the two products are equal. At one copy only the two distinguished probabilities differ, by $2u,-2u$, giving $D_1=2u$. Summing probabilities after discarding copies cannot increase their total variation: this follows by the triangle inequality inside each marginal sum. Therefore $D_m\ge D_1$ for $m\ge1$; total variation is at most one. The grouping is a probability sum, not rejection of the rank-$20$ outcome. QED.

**Proposition 2.2 (Simultaneous signed expectations).** For a measured string $z$, set

$$
h_a(z)=\operatorname{sgn}(n_{a_+}(z)-n_{a_-}(z)),\qquad
h_b(z)=\operatorname{sgn}(n_{b_+}(z)-n_{b_-}(z)),\qquad \operatorname{sgn}(0)=0.
$$

Writing $D=D_m(t,\eta)$, these two statistics from the same actual experiment satisfy

$$
\mathbb E_{a,\sigma}h_a=\sigma D,\qquad
\mathbb E_{a,\sigma}h_b=0,\qquad
\mathbb E_{b,\sigma}h_b=\sigma D,\qquad
\mathbb E_{b,\sigma}h_a=0.
\tag{2.3}
$$

Proof. If $u>0$ and $w-u>0$, the ratio of opposite-$a$ string probabilities is $((w+u)/(w-u))^{n_{a_+}-n_{a_-}}$, so the sign of their difference, whenever nonzero, is $h_a$. If $w-u=0$, a nonzero difference can occur only on a support with one distinguished count positive and the opposite count zero; its sign is again $h_a$. Strings where both laws vanish contribute nothing. Swapping $a_+,a_-$ exchanges the two laws and negates $h_a$. Hence

$$
\mathbb E_{a,+}h_a
 =\frac12\sum_z\bigl(p_{a,+}^{\otimes m}(z)-p_{a,-}^{\otimes m}(z)\bigr)h_a(z)=D.
$$

The same swap gives the negative-sign identity. Swapping the inactive $b$ pair preserves either $a$ law and negates $h_b$, proving its expectation zero. Exchanging pairs proves the other two identities. If $u=0$, sign swaps preserve each law, so every expectation is zero and $D=0$. The empty string has both signs zero. Thus (2.3) holds on all boundaries without a full-support assumption or an unknown-label-dependent measurement. QED.

**Proposition 2.3 (Actual-word first-occurrence bridge).** Let $H_a(z)$ indicate the presence of at least one $a$ outcome in the measured word, and let $H_b(z)$ indicate the presence of at least one $b$ outcome. Set

$$
Z_m=(1-2w)^m,\qquad T_m=1-Z_m.
\tag{2.4}
$$

Under every one of the four actual source labels,

$$
\Pr_X(H_a=0)=\Pr_X(H_b=0)=Z_m>0,
\qquad D_m\ge\frac{c}{s}T_m.
\tag{2.5}
$$

The two absence events need not be independent. A present pair whose signed count cancels has $H=1$, $h=0$; it is distinguished from an absent pair.

Proof. Each specified pair has total one-copy probability $2w$ under every label. Copy independence therefore gives its absence probability $(1-2w)^m$. Since $w\le1/5$, $Z_m\ge(3/5)^m>0$ for finite $m$, including $Z_0=1$.

On the same actual word, report the sign of the first $a$ outcome, or report an empty symbol if there is none. Under label $a,\sigma$, the empty probability is $Z_m$, and the probability of reporting $\epsilon\in\{1,-1\}$ is

$$
\sum_{\ell=1}^m(1-2w)^{\ell-1}(w+\sigma\epsilon u)
 =T_m\frac{w+\sigma\epsilon u}{2w}.
\tag{2.6}
$$

Here $w\ge1/25>0$. The formula includes the empty sum at $m=0$. The two opposite laws agree on the empty symbol and differ by $T_mu/w$ in absolute value at each sign. Their total variation is consequently $T_mu/w=(c/s)T_m$. For any grouping of word outcomes, the absolute difference of the grouped probabilities is at most the sum of their absolute differences; summing gives contraction of total variation. Applying this to the first-occurrence statistic and using Proposition 2.1 proves (2.5). The same computation remains valid when $u=0$ or $u=w$, so zero noise and zero probabilities require no support assumption. This is a proof statistic on the supplied experiment, not an additional program, a label oracle or postselection. QED.

## 3. Response channels, exact reference norm and unrestricted converse

**Proposition 3.1 (Pair-specific full-algebra responses).** For $q_a,q_b,q_o\in[0,1]$ and real $v_a,v_b$ with $|v_a|\le q_a$, $|v_b|\le q_b$, put

$$
d_0=d_4=q_a,\qquad d_1=d_3=q_b,\qquad d_2=q_o,
$$

and define on all $M_5(\mathbb C)$

$$
\mathsf S(q_a,q_b,q_o;v_a,v_b)(Y)
 =\sum_j d_jY_{jj}E_{jj}
 +\frac14\sum_{j\ne k}(1-d_k)Y_{kk}E_{jj}
 +v_a(X_a\circ Y)+v_b(X_b\circ Y).
\tag{3.1}
$$

This map is CPTP, including all singular endpoints. The wrong-coordinate transition coefficient is indexed by the input coordinate $k$.

Proof. With the unnormalized output-first convention $C(S)=\sum_{j,k}S(E_{jk})\otimes E_{jk}$, the matching subspace $\operatorname{span}\{|j,j\rangle\}$ has matrix

$$
A=\operatorname{diag}(d_j)+v_aX_a+v_bX_b.
$$

Its two disjoint pair blocks are

$$
\begin{pmatrix}q_a&iv_a\\-iv_a&q_a\end{pmatrix},\qquad
\begin{pmatrix}q_b&iv_b\\-iv_b&q_b\end{pmatrix},
$$

and its singleton is $q_o$. The matching eigenvalues are $q_a\pm v_a$, $q_b\pm v_b$, $q_o$. Every unmatched basis vector $|j,k\rangle$, $j\ne k$, is an isolated diagonal block with eigenvalue $(1-d_k)/4$. There are no other entries. All $25$ eigenvalues are nonnegative, so the Choi criterion proves CP on the whole complex algebra. Both pair coherences can be present simultaneously because their Choi blocks are disjoint.

For each input coordinate $k$, the output diagonal sums to $d_k+4(1-d_k)/4=1$. Every matching off-diagonal term $|j,j\rangle\langle k,k|$, $j\ne k$, has zero output partial trace. Thus $\operatorname{tr}_{\rm out}C(S)=I_5$, proving TP. These computations require no inverse or positive lower bound on a Choi eigenvalue. QED.

For the useful scalar-diagonal subfamily write

$$
S(q,v_a,v_b)=\mathsf S(q,q,q;v_a,v_b).
$$

Put

$$
T_\eta(v_a,v_b)(Y)=S(s,v_a,v_b)(Y)
 =(1-\eta)\sum_jY_{jj}E_{jj}+\eta\operatorname{tr}(Y)I_5/5
   +v_a(X_a\circ Y)+v_b(X_b\circ Y),
\tag{3.2}
$$

This notation is used only with $|v_a|,|v_b|\le s$. The targets are $T_\eta(\sigma c,0)$ and $T_\eta(0,\sigma c)$.

**Proposition 3.2 (Exact unhalved diamond norm).** If two maps in (3.2) have coefficient differences $\delta_a,\delta_b$, then

$$
\|T_\eta(v_a,v_b)-T_\eta(v'_a,v'_b)\|_\diamond
 =\max\{|\delta_a|,|\delta_b|\}.
\tag{3.3}
$$

Proof. Their difference vanishes on diagonal entries and between the sectors $\operatorname{span}\{e_0,e_4\}$, $\operatorname{span}\{e_1,e_3\}$, $\operatorname{span}\{e_2\}$. Pinching into these sectors is an average of unitary conjugations and contracts trace norm, also with an arbitrary finite reference. The norm of the pinched operator is the sum of the norms of its blocks. On either two-dimensional sector, off-diagonal extraction is $Z\mapsto(Z-UZU^\dagger)/2$, where $U=\operatorname{diag}(1,-1)$; it contracts trace norm for every complex operator. Multiplying the upper and lower off-diagonals by $i,-i$ is conjugation by $\operatorname{diag}(i,1)$. Thus the sum of the two output-block norms is at most $\max(|\delta_a|,|\delta_b|)$ times the input norm. This proves the stabilized upper bound for arbitrary reference operators, in particular for all reference/data states. A balanced pure state $(e_j+e_k)/\sqrt2$ on a maximizing pair gives a Hermitian off-diagonal output with eigenvalues $\pm|\delta|/2$ and trace norm $|\delta|$. It attains the bound without a reference. QED.

**Proposition 3.3 (Unrestricted converse).** For every $m,t,\eta$ in the stated domains,

$$
e_m(t,\eta)\ge[c-D_m(t,\eta)]_+.
\tag{3.4}
$$

Proof. Fix any competing whole-algebra CPTP processor, any finite complex reference and any reference/data state $\omega$. Appending this fixed $\omega$ and applying the processor while leaving the reference untouched defines a CPTP map from program states to reference/output states. Trace-distance contraction therefore bounds its output difference for the opposite actual $a$ programs by $2D_m$. Taking the supremum in the channel-discrimination norm gives $\|N_{X_a}-N_{-X_a}\|_\diamond\le2D_m$. The opposite targets have distance $2c$ by (3.3). If their respective simulation errors are $\epsilon_+,\epsilon_-$, the triangle inequality gives $2c\le\epsilon_++2D_m+\epsilon_-$. Consequently the worst four-label error is at least $c-D_m$ and at least zero. Taking the infimum proves (3.4). This argument restricts no competitor to the response family or to the PVM. QED.

The lower bound (3.4), the fixed-diagonal construction below and the zero-noise formulas are existing results of the supplied original-source volume, Sections 121–123; they are credited here and proved to keep the present task self-contained.

**Proposition 3.4 (Existing fixed-diagonal upper bound).** There is a simultaneous four-label processor of exact error $[c-sD_m]_+$. At zero noise the unrestricted value is consequently

$$
e_m(t,0)=[t-D_m(t,0)]_+.
\tag{3.5}
$$

Proof. Put $r_{\rm old}=0$ if $D_m=0$, and otherwise $r_{\rm old}=\min(s,c/D_m)$. On each product-PVM outcome use $T_\eta(r_{\rm old}h_a,r_{\rm old}h_b)$. For product projections $M_z$, the instrument

$$
\Omega\longmapsto\sum_z T_\eta(r_{\rm old}h_a(z),r_{\rm old}h_b(z))
 \left(\operatorname{tr}_{P_m}[(I_5\otimes M_z)\Omega(I_5\otimes M_z)]\right)
\tag{3.6}
$$

is CP and is TP by completeness of the PVM and TP of every response. It is one map on the entire joint algebra. Initial batch independence and (2.3) make its induced channels $T_\eta(\sigma r_{\rm old}D_m,0)$ and $T_\eta(0,\sigma r_{\rm old}D_m)$. Formula (3.3) gives error $c-r_{\rm old}D_m=[c-sD_m]_+$. If $D_m=0$, either $m=0$ or $c=0$ by Proposition 2.1, and the same equality holds. At $\eta=0$, $s=1$, so this construction meets (3.4) and proves (3.5). QED.

## 4. Attained unrestricted minimax and the exact copy threshold

**Theorem 4.1 (All parameters, all allowed competitors, simultaneous attainment).** For every finite integer $m\ge0$ and every $t,\eta\in[0,1]$, the task of Definition 1.3 has

$$
\boxed{e_m(t,\eta)=[c-D_m(t,\eta)]_+.}
\tag{4.1}
$$

One label-independent whole-algebra complex CPTP processor attains this value for all four labels simultaneously, with every finite untouched complex reference included.

Proof. Abbreviate $D=D_m$, $Z=Z_m$, $T=T_m$ and set

$$
r=\begin{cases}0,&D=0,\\ \min\{1,c/D\},&D>0,\end{cases}
\qquad Q=\max\{s,r\},\qquad q_{\emptyset}=\frac{s-QT}{Z}.
\tag{4.2}
$$

These are known functions of $m,t,\eta$, independent of the unknown label. By Proposition 2.3, if $D>0$ then $rT\le cT/D\le s$; if $D=0$ then $rT=0$. Also $sT\le s$, hence $QT=\max(sT,rT)\le s$. Thus $q_{\emptyset}\ge0$. Since $Q\ge s$,

$$
s-QT\le s(1-T)=sZ,
$$

so $q_{\emptyset}\le s\le1$. Also $0\le Q\le1$, and $Z>0$ ensures that (4.2) never divides by zero.

On each word define

$$
q_a(z)=\begin{cases}Q,&H_a(z)=1,\\q_{\emptyset},&H_a(z)=0,\end{cases}
\qquad
q_b(z)=\begin{cases}Q,&H_b(z)=1,\\q_{\emptyset},&H_b(z)=0,\end{cases}
\tag{4.3}
$$

and $d_0=d_4=q_a(z)$, $d_1=d_3=q_b(z)$, $d_2=s$. Use the response

$$
S_z=\mathsf S(q_a(z),q_b(z),s;rh_a(z),rh_b(z)).
\tag{4.4}
$$

If $H_a=0$, then $h_a=0$; otherwise $|rh_a|\le r\le Q=q_a$. The identical argument gives $|rh_b|\le q_b$. These inequalities hold simultaneously when both pairs are present. Proposition 3.1 therefore proves complete positivity and trace preservation of every response, including on arbitrary complex inputs. Moreover, the common marginal absence probabilities give under each label

$$
\mathbb E_X q_a=\mathbb E_X q_b=QT+q_{\emptyset}Z=s,
\qquad \mathbb E_X d_j=s\quad(0\le j\le4).
\tag{4.5}
$$

Let $\Pi_z$ be the product of the original six-outcome program projections. Define

$$
\mathcal P_m(\Omega)=\sum_z S_z\left(
 \operatorname{tr}_{P_m}[(I_5\otimes\Pi_z)\Omega(I_5\otimes\Pi_z)]\right).
\tag{4.6}
$$

Projection, partial trace and each response are CP. Since every response is TP and $\sum_z\Pi_z=I_{P_m}$, the trace of the sum is $\operatorname{tr}\Omega$. Thus (4.6) is a single CPTP map on the entire joint algebra, including correlated data/program inputs and arbitrary unpromised programs. It defines a lawful response even on words of zero probability under a promised label; all outcomes are retained.

For the promised initially independent program, $N_X(Y)=\sum_zp_X^{\otimes m}(z)S_z(Y)$. On $E_{kk}$, (4.5) gives

$$
N_X(E_{kk})=sE_{kk}+\frac{1-s}{4}\sum_{j\ne k}E_{jj}
 =(1-\eta)E_{kk}+\eta I_5/5.
\tag{4.7}
$$

The sign identities (2.3) give the mean pair coherences. Every other off-diagonal matrix unit maps to zero. Consequently the exact channel identities on all $M_5(\mathbb C)$ are

$$
N_{\sigma X_a}=T_\eta(\sigma rD,0),\qquad
N_{\sigma X_b}=T_\eta(0,\sigma rD).
\tag{4.8}
$$

They preserve the full target diagonal, including every wrong-output population. Equality of these linear maps remains equality after tensoring any finite reference. Since $rD=\min(c,D)$, with the same identity at $D=0$, Proposition 3.2 gives exact unhalved diamond error $c-rD=[c-D]_+$ for each label. Proposition 3.3 supplies the matching lower bound over every allowed CPTP competitor. This proves (4.1), not merely optimality within a response ansatz.

At $m=0$, $D=T=r=0$, $Z=1$ and $Q=q_{\emptyset}=s$; (4.6) is the common channel $T_\eta(0,0)$ with error $c$. If $c=0$, all source laws and targets coincide, $D=r=0$ and again $Q=q_{\emptyset}=s$, so the common target is exact. For $m\ge1$, $c>0$ implies $D\ge2c/5>0$. At $\eta=0$, $s=1$ and $Q=q_{\emptyset}=1$; (4.4) reduces to the existing zero-noise sign response. Zero source probabilities, $q_{\emptyset}=0$, $Q=1$ and singular Choi blocks were all included in the inequalities and the Choi proof. No inverse program state or limiting construction has been used. QED.

**Corollary 4.2 (Necessary and sufficient exactness and minimum prescribed copies).** Exact simultaneous four-label programming with $m$ prescribed copies is possible if and only if $D_m(t,\eta)\ge c$. The exact minimum prescribed-copy count is

$$
m_{\min}(t,\eta)=\min\{m\in\mathbb N_0:D_m(t,\eta)\ge c\},
\qquad \min\varnothing=\infty.
\tag{4.9}
$$

At $c=0$ this minimum is $0$. For $0<c<1$ it is finite, with sufficient bound

$$
m_{\min}\le
\left\lceil\frac{25}{2c^2}\log\frac{2}{1-c}\right\rceil.
\tag{4.10}
$$

The ceiling is a sufficient bound, not a formula for the minimum. The minimum in (4.9), with the explicit finite sum (2.2), is the exact threshold. At $c=1$, necessarily $(t,\eta)=(1,0)$, and $m_{\min}=\infty$.

Proof. Both directions of the exactness assertion follow from the attained value (4.1). Discarding extra copies is a valid whole-algebra operation, and marginalizing probability laws contracts total variation, so $D_m$ is nondecreasing. At $c=0$ the common target needs no program. For $0<c<1$, the self-contained bounded-variable argument in Proposition 7.3 gives

$$
D_m\ge1-2\exp(-2mc^2/25).
\tag{4.11}
$$

Any integer at least the ceiling in (4.10) makes the exponential at most $(1-c)/2$, so $D_m\ge c$. For $c=1$, the nonnegative identity $1-c=\eta+(1-\eta)(1-t)$ forces $\eta=0,t=1$. The opposite laws then have distinguished probabilities $2/5,0$ and $0,2/5$. Their only common support consists of words avoiding both active-pair outcomes, with common mass $(3/5)^m$. Since $D_m=1-\sum_z\min(p_+(z),p_-(z))$, it follows that

$$
D_m(1,0)=1-(3/5)^m,\qquad e_m(1,0)=(3/5)^m>0
\tag{4.12}
$$

for every finite $m$, including $m=0$. This proves the infinite boundary and covers all parameters. These are source-copy counts under the supplied-service assumptions, not minimum physical acquisition or communication costs. QED.

## 5. A common tie event and its exact probability

**Proposition 5.1 (Joint zero statistics).** Let

$$
C_m=\{z:h_a(z)=h_b(z)=0\},\qquad R_m=\Pr_X(C_m).
$$

The probability $R_m$ is the same under all four actual source laws and equals

$$
R_m=\sum_{2r+2q+k=m}\frac{m!}{(r!)^2(q!)^2k!}
       (w^2-u^2)^r w^{2q}\nu^k.
\tag{5.1}
$$

All indices are nonnegative integers. In particular $R_0=1$, $R_1=\nu$, and

$$
\nu^m\le R_m<1\quad(m\ge1),\qquad R_m>0\quad(m\ge0).
\tag{5.2}
$$

Define

$$
K_0=1,\qquad K_m=\min\left\{1,\frac{s}{1-R_m}\right\}\quad(m\ge1).
\tag{5.3}
$$

Then $s\le K_m\le1$. For $m\ge1$ and $\eta>0$, $K_m>s$.

Proof. Sign exchange within either pair and exchange of the two pairs preserve $C_m$ and take the four laws into one another. Thus its probability is common. Under the $a,+$ law, group $o,*$ into a neutral outcome of total probability $\nu=w+20\eta/25$. A string in $C_m$ has counts $r,r,q,q,k$ for the four signal outcomes and the neutral outcome, with $2r+2q+k=m$. Its probability factor is $(w+u)^r(w-u)^rw^{2q}\nu^k$, and the multinomial coefficient gives (5.1). The rank-$20$ probability is retained in $\nu$; it is never discarded. This derivation remains valid for every zero probability under the convention $0^0=1$.

The empty string gives $R_0=1$. At one copy only $o,*$ have both signs zero. All-neutral strings give $R_m\ge\nu^m>0$. For $m\ge1$, the all-$a_+$ string under $a,+$ has positive probability $(w+u)^m$ and lies outside $C_m$, so $R_m<1$. Formula (5.3) is therefore defined. Since $0<1-R_m<1$, $s/(1-R_m)>s$; also $1\ge s$. This proves $K_m\ge s$. If $\eta>0$, then $s<1$, so both quantities in the minimum are strictly larger than $s$, proving $K_m>s$. At zero noise $K_m=1$, and the separately defined $K_0$ is always one. QED.

## 6. N1: A useful scalar-diagonal noise redistribution

**Theorem 6.1 (N1, scalar-diagonal constructive bound).** For every integer $m\ge0$ and $t,\eta\in[0,1]$,

$$
[c-D_m]_+\ \le\ e_m(t,\eta)\ \le\ [c-K_mD_m]_+\ \le\ [c-sD_m]_+.
\tag{6.1}
$$

The middle upper bound is achieved by one explicit whole-algebra CPTP processor with that same error for all four labels. If $m\ge1$, $\eta>0$, $c>0$ and the fixed-diagonal error $[c-sD_m]_+$ is positive, N1 has strictly smaller error.

Proof. Fix $m,t,\eta$ and abbreviate $D=D_m$, $R=R_m$, $K=K_m$. Set

$$
r=\begin{cases}0,&D=0,\\ \min\{K,c/D\},&D>0,\end{cases}\qquad
Q=\max\{s,r\},\qquad q_C=\frac{s-Q(1-R)}{R}.
\tag{6.2}
$$

At $m=0$, $R=K=1$ and $D=0$, so $r=0$ and $Q=q_C=s$. For $m\ge1$, Proposition 5.1 gives $0<R<1$, $s\le K\le1$ and $K\le s/(1-R)$. Since $r\le K$, also $Q\le K$, and consequently $q_C\ge0$. Further,

$$
s-Q(1-R)\le s-s(1-R)=sR,
$$

so $q_C\le s\le1$. Thus both $Q$ and $q_C$ are lawful response diagonal parameters. For a string $z$, use

$$
q_z=\begin{cases}q_C,&z\in C_m,\\Q,&z\notin C_m,\end{cases}\qquad
S_z=S(q_z,rh_a(z),rh_b(z)).
\tag{6.3}
$$

On $C_m$ both coherence coefficients are zero. Outside $C_m$ their absolute values are at most $r\le Q=q_z$. Every $S_z$ is CPTP by Proposition 3.1, even for arbitrary unpromised data. Because $C_m$ has the same probability under every label,

$$
\mathbb E_X q_z=q_C R+Q(1-R)=s.
\tag{6.4}
$$

Let $M_z$ be the product of the original six-outcome projections and define

$$
\mathcal P_m(\Omega)=\sum_z S_z\left(
 \operatorname{tr}_{P_m}[(I_5\otimes M_z)\Omega(I_5\otimes M_z)]\right).
\tag{6.5}
$$

Projection, partial trace and each response are CP. The trace of this sum equals $\operatorname{tr}\Omega$, since all responses preserve trace and $\sum_zM_z=I$. Hence (6.5) is one label-independent CPTP map on the entire joint complex algebra, including unpromised programs and data/program correlations. No outcome is rejected.

For the promised independent program, the induced channel is the probability average of $S_z$. The scalar subfamily $S(q,v_a,v_b)$ is affine in its three real parameters. Equations (6.4) and (2.3), together with $(1-s)/4=\eta/5$, therefore give the exact full-algebra identities

$$
N_{\sigma X_a}=T_\eta(\sigma rD,0),\qquad
N_{\sigma X_b}=T_\eta(0,\sigma rD).
\tag{6.6}
$$

Both the matching diagonal and every wrong-output diagonal agree with the target. By Proposition 3.2 the error for each label is $c-rD$. If $D>0$, $rD=\min(KD,c)$; if $D=0$, $rD=0$. In either case the error is exactly $[c-KD]_+$. This proves N1's upper bound. Proposition 3.3 gives the unrestricted lower bound, and $K\ge s$ gives the last inequality in (6.1).

For strictness, $m\ge1$ and $c>0$ imply $D\ge2c/5>0$. If also $\eta>0$, Proposition 5.1 gives $K>s$, hence $KD>sD$. When $c-sD>0$, either $c-KD>0$ and is strictly smaller than $c-sD$, or N1's bound is zero and is still strictly smaller. If the fixed-diagonal bound is zero, both upper bounds are zero. No strict gain is asserted at $m=0$, $c=0$ or $\eta=0$. QED.

The scalar-diagonal construction redistributes the conditional diagonal action. The fixed-diagonal processor uses parameter $s$ at every outcome, limiting each conditional coherence to $s$. N1 allows outcomes carrying a nonzero signed response to use diagonal parameter $Q>s$; the common tie event absorbs additional wrong-coordinate noise. Its probability is computed from the actual noisy source, and (6.4) restores exactly the prescribed mean diagonal for every label. The conditional responses need not themselves have the target white-noise diagonal. This remains a useful implementation with at most nine response settings. The pair-specific processor of Theorem 4.1 uses separate absence events and attains the unrestricted optimum everywhere; the target and competitor class are the same for both constructions.

## 7. N2: Simpler exact-regime certificates and the one-copy value

**Theorem 7.1 (N2, regions where N1 attains the unrestricted value).** For every $m\ge0$ and all original parameters, if $R_m\ge1-s$ then

$$
e_m(t,\eta)=[c-D_m(t,\eta)]_+.
\tag{7.1}
$$

The condition $\nu^m\ge1-s$ also certifies attainment by the nine-response N1 processor. At any parameter point, whether or not that condition holds,

$$
c\le K_mD_m\quad\Longrightarrow\quad e_m(t,\eta)=0.
\tag{7.2}
$$

For every $t,\eta\in[0,1]$, the unrestricted one-copy minimax is

$$
e_1(t,\eta)=\frac35(1-\eta)t.
\tag{7.3}
$$

Proof. For $m\ge1$, $R_m\ge1-s$ is equivalent to $s/(1-R_m)\ge1$, hence to $K_m=1$. The upper and lower bounds in (6.1) then agree. At $m=0$, $K_0=1$ by convention and $R_0=1\ge1-s$, so the same conclusion holds. The estimate $R_m\ge\nu^m$ gives the simpler sufficient region. If $R_m=1-s$ and $r=Q=1$, formula (6.2) has $q_C=0$; the response remains CPTP by its Choi eigenvalues. Thus equality on the region boundary is included without a limiting argument.

Whenever $c\le K_mD_m$, the explicit upper bound is zero, which proves (7.2) by nonnegativity. This is a sufficient test for N1. The necessary-and-sufficient unrestricted test is $D_m\ge c$ by Corollary 4.2. If $m=1$, $R_1=\nu=1-4s/5$ and

$$
R_1-(1-s)=s/5>0,\qquad D_1=2c/5.
$$

Equation (7.1) gives (7.3), including $c=0$. Every attainment here is simultaneous for all four targets; the converse still ranges over every allowed CPTP processor. QED.

**Proposition 7.2 (Direct one-copy implementation).** An independent explicit attainment of (7.3) uses $S(1,\epsilon,0)$ on outcome $a_\epsilon$, $S(1,0,\epsilon)$ on $b_\epsilon$, and $S(w/\nu,0,0)$ on either neutral outcome $o,*$.

Proof. Since $5w=s\le1$, $w\le1-4w=\nu$, so $0\le w/\nu\le1$; all responses are CPTP. The total signal mass is $4w$ under every source. The mean matching parameter is

$$
4w+\nu(w/\nu)=5w=s,
$$

and the mean wrong-coordinate parameter for each wrong output is

$$
\nu\frac{1-w/\nu}{4}=\frac{\nu-w}{4}=\frac{1-s}{4}=\eta/5.
$$

Under $a,\sigma$, the mean $a$ coefficient is $\sigma2u$ and the $b$ coefficient is zero; the roles interchange under $b,\sigma$. Thus the induced channels have active coherence $\sigma2c/5$ and the exact target diagonal, giving error $3c/5$ by (3.3). The converse (3.4) at $D_1=2c/5$ proves optimality. The proof applies unchanged at $t=0$, $\eta=0$ and $\eta=1$, retaining every outcome. Compared with the existing one-copy upper bound, the gain is $2c(1-s)/5$, strictly positive when $c,\eta>0$. QED.

**Proposition 7.3 (Credited finite exactness budget).** If $c>0$ and $\gamma=s-c>0$, a sufficient integer budget for simultaneous exactness is

$$
m\ge\left\lceil\frac{25}{2c^2}\log\frac{2s}{\gamma}\right\rceil.
\tag{7.4}
$$

The logarithm is natural. This existing sufficient budget certifies the fixed-diagonal processor, hence N1 as well. It is not the minimum (4.9); the all-parameter theorem also gives the sufficient bound (4.10).

Proof. On one measured copy put $G_a=1,-1,0$ at $a_+,a_-$ and all other outcomes. Under opposite $a$ labels its means are $2u,-2u$. To obtain the needed bounded-variable estimate directly, for any $V\in[-1,1]$ let $F(\lambda)=\log\mathbb E\exp(\lambda(V-\mathbb EV))$. Its second derivative is the variance under a tilted probability law, at most one. Since $F(0)=F'(0)=0$, integration gives $F(\lambda)\le\lambda^2/2$. For independent copies, exponential Markov applied to the centered sum and the choice of tilt magnitude $\alpha$ give each one-sided deviation bound $\exp(-m\alpha^2/2)$.

At $\alpha=2u$, the sign test, breaking ties fairly, has equal-prior error at most $\exp(-2mu^2)$. For two classical laws the optimal equal-prior error is $(1-D)/2$: outcome by outcome choose the larger probability, leaving one half the sum of the smaller probabilities. This applies to the full commuting experiment of Section 2. Therefore

$$
D_m\ge1-2\exp(-2mc^2/25).
\tag{7.5}
$$

Budget (7.4) makes the right-hand side at least $1-\gamma/s=c/s$. Since $K_m\ge s$, this gives $c\le K_mD_m$, and (7.2) proves exactness. The inequality (7.5) may be negative for small $m$ and is only a lower estimate; the exact quantity remains (2.2). The expression $\gamma=(1-\eta)(1-t)+\eta/5$ vanishes only at $(t,\eta)=(1,0)$, so this establishes finite-copy exactness at every other point with $c>0$, including all positive-noise points with distinct targets. No perfect label readout is needed. QED.

**Proposition 7.4 (All boundary conventions and identification).** The preceding results include

$$
\begin{aligned}
D_0&=0,\quad R_0=K_0=1,\quad e_0(t,\eta)=c,\\
e_m(0,\eta)&=0,\qquad e_m(t,1)=0,\\
D_m(1,0)&=1-(3/5)^m,\qquad e_m(1,0)=(3/5)^m.
\end{aligned}
\tag{7.6}
$$

For $m\ge1$, $D_m=0$ exactly when $c=0$. At $\eta>0$ no finite actual batch perfectly identifies the four labels, even though the exact channel regimes above exist.

Proof. With no program, the common channel $T_\eta(0,0)=S(s,0,0)$ has error $c$ on every target; (3.4) proves its unrestricted optimality. If $c=0$, all targets coincide and all source laws coincide, so $D_m=0$ and the common target can be implemented directly with no copies. Conversely, $D_m\ge2c/5$ for $m\ge1$. In the $D=0$ branch of (6.2), $r=0$ and $Q=q_C=s$, so no division by zero occurs.

At $\eta=0$, $s=K_m=1$ and (6.1) reduces to the credited formula (3.5). At $(t,\eta)=(1,0)$ the opposite laws have distinguished probabilities $2/5,0$ versus $0,2/5$. Their common support consists exactly of strings avoiding both distinguished outcomes, of mass $(3/5)^m$ under either law. For probability laws, $D=1-\sum_z\min(p(z),q(z))$; thus $D_m=1-(3/5)^m$. Formula (3.5) gives the last equality of (7.6), including $m=0$, and proves that no finite-copy exactness occurs at this corner.

For $\eta>0$, every program eigenvalue is at least $\eta/25>0$, and finite tensor powers remain positive definite on the same whole space. If a positive measurement effect has zero expectation under one such state, its trace is zero and it is the zero operator. A perfectly identifying outcome for one label would have to vanish on the other full-support states, so it cannot have positive probability on its purported label. No finite POVM perfectly identifies the label. At zero noise and $0<t<1$ the same argument holds on the common matching tensor support, whose source eigenvalues are strictly positive. At the remaining zero-noise corner the common-support overlap just computed also precludes perfect identification of even the opposite pair.

The proofs of Sections 2–6 permit $w-u=0$, vanished probabilities and Kraus branches, $q_C=0$ and conditional $q_z=1$. Channel exactness is obtained by averaging lawful responses, with some conditional coherence larger than the target's coefficient. It concerns equality of channels on every complex input and reference, and does not assert label identification. QED.

## 8. N3: Five-copy exactness beyond the fixed-diagonal test

**Theorem 8.1 (N3, every sufficiently small positive noise).** There exists $\bar\eta>0$ such that for every $0<\eta<\bar\eta$ there is $t_\eta\in(1/2,1)$ satisfying

$$
D_5(t_\eta,\eta)=(1-\eta)t_\eta=c>0,\qquad
R_5(t_\eta,\eta)>1-s,\qquad e_5(t_\eta,\eta)=0.
\tag{8.1}
$$

At each such point the existing fixed-diagonal processor has strictly positive error

$$
[c-sD_5]_+=c(1-s)>0.
\tag{8.2}
$$

These points exhibit exactness where the fixed-diagonal processor has positive error. This is an explicit consequence of the exact threshold, without a continuous selection of $t_\eta$ or a minimal-copy assertion.

Proof. First reconstruct the two credited zero-noise endpoint values by ordinary algebra. At $(t,\eta)=(1/2,0)$, the probabilities of $a_+,a_-$ and all remaining outcomes grouped together are

$$
a=3/10,\qquad b=1/10,\qquad d=3/5.
$$

Let $S_j$ be the signed-count sum of $j$ independent steps with these probabilities for $+1,-1,0$. Reversing all signs in a path shows

$$
b\Pr(S_j=1)=a\Pr(S_j=-1).
$$

Indeed, each path ending at $1$ has one more positive step than negative steps, so its probability is $a/b$ times that of its reversed path ending at $-1$. A new step changes the conditional expected sign by $a-b$ at $S_j=0$, by $-b$ at $S_j=1$, by $a$ at $S_j=-1$, and by zero otherwise. The latter two probabilities cancel by the displayed identity. Hence

$$
\mathbb E\operatorname{sgn}(S_{j+1})-\mathbb E\operatorname{sgn}(S_j)
 =(a-b)\Pr(S_j=0).
\tag{8.3}
$$

Writing $p=ab$, the constant coefficients of $(d+az+bz^{-1})^j$ for $j=0,1,2,3,4$ are, respectively,

$$
1,\quad d,\quad d^2+2p,\quad d^3+6pd,\quad d^4+12pd^2+6p^2.
$$

These formulas follow by choosing equal numbers of $az$ and $bz^{-1}$ in the ordinary multinomial expansion. Summing (8.3) from $j=0$ through $4$, using $\operatorname{sgn}(S_0)=0$ and (2.3), gives

$$
\begin{aligned}
D_5(1/2,0)
 &=(a-b)(1+d+d^2+d^3+d^4+2p+6pd+12pd^2+6p^2)\\
 &=\frac15\,\frac{13043}{5000}=\frac{13043}{25000}.
\end{aligned}
\tag{8.4}
$$

For clarity, the numerator $13043$ in the common denominator $5000$ is the sum $5000+3000+1800+1080+648+300+540+648+27$ from those nine terms. This verifies analytically the endpoint supplied in the original volume. Proposition 7.4 supplies, and proves, the other credited value

$$
D_5(1,0)=1-(3/5)^5.
\tag{8.5}
$$

Now set $F(t,\eta)=D_5(t,\eta)-(1-\eta)t$. Formula (2.2) is a finite sum of absolute values of polynomials in $w,u$, with $w$ affine in $\eta$ and $u=(1-\eta)t/5$. Thus $F$ is continuous on the entire closed parameter square, including all zero probabilities. Equations (8.4)–(8.5) give

$$
F(1/2,0)=543/25000>0,\qquad F(1,0)=-(3/5)^5<0.
$$

Continuity at these two fixed endpoints gives one $\epsilon>0$ such that $F(1/2,\eta)>0$ and $F(1,\eta)<0$ for $0\le\eta<\epsilon$. Take

$$
\bar\eta=\min\{\epsilon,1/(4\cdot5^4),1/2\}>0.
$$

For each $0<\eta<\bar\eta$, the intermediate value theorem in $t$ supplies some $t_\eta\in(1/2,1)$ with $F(t_\eta,\eta)=0$. Then $D_5=c=(1-\eta)t_\eta>0$.

Uniformly in $t$, Proposition 5.1 gives $R_5\ge\nu^5\ge5^{-5}$. Meanwhile $\eta<1/(4\cdot5^4)$ implies $1-s=4\eta/5<5^{-5}$. Therefore $R_5>1-s$ at every selected root. Theorem 7.1 proves $e_5=[c-D_5]_+=0$. More explicitly, the actual processor has $K=r=Q=1$ and

$$
q_C=1-\frac{1-s}{R_5}\in(0,1),
$$

so exactness is achieved by the lawful simultaneous four-source construction, not just an abstract vanishing lower bound. Because $\eta,c>0$, the old processor's exact error is $c(1-s)>0$, proving (8.2). Its test $D_5\ge c/s$ fails since $D_5=c>0$ and $s<1$. The uniform $R_5$ bound avoids any root-continuity assumption. QED.

## 9. Each Kraus operator has rank at most two: a paid route

**Theorem 9.1 (Full Kraus decomposition and fixed decoder).** Every response $\mathsf S(q_a,q_b,q_o;v_a,v_b)$ of Proposition 3.1, including the pair-specific responses (4.4) and scalar responses of N1–N3, has at most $25$ Kraus branches, each individual Kraus operator having rank at most two. It has a complete-instrument factorization through one transmitted qubit and one flag of at most $25$ values, with a decoder independent of source labels, outcomes and parameters.

Proof. Use the fixed orthonormal coefficient eigenvectors

$$
\xi_{a,\epsilon}=(e_0-i\epsilon e_4)/\sqrt2,\qquad
\xi_{b,\epsilon}=(e_1-i\epsilon e_3)/\sqrt2,\qquad \xi_o=e_2.
$$

For $A=\operatorname{diag}(d_j)+v_aX_a+v_bX_b$ their eigenvalues are $q_a+\epsilon v_a$, $q_b+\epsilon v_b$, $q_o$. In (4.4) these are $q_a(z)+\epsilon rh_a(z)$, $q_b(z)+\epsilon rh_b(z)$ and $s$. For the five eigenpairs $(\lambda_\ell,\xi_\ell)$, numbered $\ell=1,\ldots,5$, put

$$
K_\ell=\sqrt{\lambda_\ell}\operatorname{diag}(\xi_\ell).
$$

Add the twenty operators

$$
K_{jk}=\sqrt{(1-d_k)/4}\,E_{jk},\qquad j\ne k.
$$

The first five branch maps have entrywise coefficient matrix $\sum_\ell\lambda_\ell\xi_\ell\xi_\ell^\dagger=A$, so their sum is $A\circ Y$. The other twenty maps sum to $\frac14\sum_{j\ne k}(1-d_k)Y_{kk}E_{jj}$. Together these give exactly (3.1). Further,

$$
\sum_{\ell=1}^{5}K_\ell^\dagger K_\ell=\operatorname{diag}(d_j),\qquad
\sum_{j\ne k}K_{jk}^\dagger K_{jk}=\operatorname{diag}(1-d_j).
\tag{9.1}
$$

Their sum is $I_5$. Each pair-supported diagonal operator has rank at most two, the singleton diagonal operator has rank at most one, and each transition has rank at most one. Zero eigenvalues give zero branches. This bounds each operator's matrix rank; it does not say that the channel's Kraus rank is two. The isometry $\psi\mapsto\sum_\ell K_\ell\psi\otimes|\ell\rangle$, where the index now ranges over all branches, supplies an environment of dimension at most $25$.

Give all $25$ branch labels a fixed ordering. For every label choose once and for all an isometry $V_\ell:\mathbb C^2\to\mathbb C^5$ whose range contains the range of its Kraus matrix. For an $a$ or $b$ diagonal branch use the appropriate original coordinate pair. For a singleton or a transition branch with range in $\mathbb C e_j$, complete $e_j$ with any fixed different original coordinate. These choices depend only on the branch label, not on $q_a,q_b,q_o,v_a,v_b,z,X$. Define

$$
B_\ell=V_\ell^\dagger K_\ell.
$$

Because the range of $K_\ell$ is contained in that of $V_\ell$, $V_\ell B_\ell=K_\ell$ and $B_\ell^\dagger B_\ell=K_\ell^\dagger K_\ell$. Thus $\sum_\ell B_\ell^\dagger B_\ell=I_5$. The sender applies the complete instrument with branch output $B_\ell YB_\ell^\dagger$, transmits that two-dimensional quantum output and the flag $\ell$, and retains every branch. The receiver's branch decoder is $Z\mapsto V_\ell ZV_\ell^\dagger$, CPTP on every qubit input. On an arbitrary operator $Z$ on the entire qubit/flag algebra the common decoder is

$$
\mathcal D(Z)=\sum_\ell V_\ell
 (I_2\otimes\langle\ell|)Z(I_2\otimes|\ell\rangle)V_\ell^\dagger.
\tag{9.2}
$$

This is CP and TP, since $V_\ell^\dagger V_\ell=I_2$ and the flag projectors sum to the identity. Its composite with the sender instrument is $\sum_\ell K_\ell YK_\ell^\dagger=\mathsf S(q_a,q_b,q_o;v_a,v_b)(Y)$ on the entire input algebra. Off-diagonal flag inputs are lawfully dephased by (9.2); the decoder is not defined only on classical promises. If the flag is encoded in five classical bits, define any fixed CPTP output on each of the seven unused binary words; this extends the decoder to the full $32$-valued carrier. Identity with arbitrary untouched references follows from equality of the linear channels. QED.

**Resource statement 9.2 (Original measurement and controls).** For the optimal one-use processor (4.6), the following are sufficient supplied resources, not asserted minimal physical costs.

- A batch consumes $m$ actual original independent copies. Each measured copy uses the original joint six-outcome PVM on its full $25$-dimensional $A\mid B$ carrier. The rank-$20$ complementary outcome remains an ordinary outcome. A six-dimensional pointer is sufficient: $\psi\mapsto\sum_j\Pi_j\psi\otimes|j\rangle$ is an isometry because $\sum_j\Pi_j=I$; it can be implemented with a blank pointer and extended to a unitary on the full finite space. The pointer may be reset between copies.
- The raw six-valued outcomes fit in $3m$ classical bits. Alternatively, update the two signed count differences and two presence bits $H_a,H_b$, using at most $4(2m+1)^2$ memory states. For each pair the final response distinguishes absence, a present tie, a positive count and a negative count, so at most $16$ calibrated responses suffice. Presence bits cannot be omitted: absence uses $q_{\emptyset}$, while a present tie uses $Q$ with zero coherence. Updating this memory does not require identifying the source label. The scalar-diagonal N1 processor separately needs only the two signs and at most nine responses.
- Exact controls supply the known $t,\eta,s,w,D_m,Z_m,T_m,r,Q,q_{\emptyset}$ in (4.2)–(4.4), the required square roots and the fixed complex phases. N1 instead uses its specified $R_m,K_m,q_C$. A finite formula or code naming an exact number is not its physical preparation. Each response uses at most $25$ Kraus branches and an environment of dimension at most $25$, with fresh local environments for independent uses. Blank measurement pointers, memory and response environments, their reset/discard operations and the controlled instruments are supplied ancillary services.
- If the original halves start at separated laboratories, put the processor at $A$ and pay for one noiseless five-dimensional quantum transfer of the $B$ half to $A$ per consumed copy. Joint measurement is then local at $A$. This transport is a supplied quantum service; native local observations do not replace it. Co-located supply is an alternative declared preparation arrangement, not a proof that separated transport is free.
- Each simulated data use from $A$ to $B$ then pays for one forward qubit and one flag with at most $25$ values; five classical bits suffice. The receiver uses the fixed decoder (9.2), so the calibration record need not be transmitted. No additional preshared entanglement beyond the stated actual programs, uncounted data wire, free port, forward/feedback link, return data path or postselection is supplied.

At $m=0$ there is no program measurement or half transfer. At $c=0$ the common target can be directly implemented with no copies; any use of the separated communication route still pays for its controls and forward links. Theorem 9.1 applies to conditional target channels as well, by setting $q_a=q_b=q_o=s$ and the appropriate coherence equal to $\pm c$.

## 10. Fresh batches, shared records and whole-block error

In the fresh-batch and reused-response statements, $S_z$ denotes the optimal pair-specific response (4.4).

**Theorem 10.1 (Independent simulated uses require fresh program batches).** Let $n\ge1$. Conditional on the same unknown fixed $X$, supply $n$ independent batches of $m$ actual copies, initially independent of the entire possibly correlated complex block data and reference. Apply (4.6) to each data factor, with fresh response environments. Put $\varepsilon_m=[c-D_m]_+$. Then the induced channel on the whole block is $N_X^{\otimes n}$ and

$$
\sup_{X\in U_4}\|N_X^{\otimes n}-\Phi_{t,\eta,X}^{\otimes n}\|_\diamond
 \le\min\{2,n\varepsilon_m\}.
\tag{10.1}
$$

This bound also holds after any common whole-block CPTP encoder and decoder. In an exact one-use regime the fresh-batch block is exactly the desired tensor channel.

Proof. The full conditional program is $\rho_{t,\eta}(X)^{\otimes nm}$. The tensor product of the whole-algebra processors, applied to these regrouped independent batches, equals $N_X^{\otimes n}$ on every simple input tensor, hence on the entire block algebra by linearity. Tensoring an identity on a reference preserves that equality. No independence of the data factors is used.

Telescope the tensor-channel difference into $n$ terms, each having one factor $N_X-\Phi_{t,\eta,X}$ and channel factors before and after it. Ancillary stability and CPTP contraction bound each term by $\varepsilon_m$ in diamond norm. Summing gives $n\varepsilon_m$. Two channels have unhalved diamond distance at most two, proving (10.1). Pre- and postcomposition with common CPTP block maps cannot enlarge the bound. In particular, an ideal code with reference-state error $\epsilon_n$ has implemented error at most $\epsilon_n+\min(2,n\varepsilon_m)$. If $\varepsilon_m=0$, equality with the ideal tensor channel is exact. QED.

For the separated route this consumes $nm$ actual copies and $nm$ five-dimensional program-half transfers, together with $n$ forward qubits (aggregate port dimension $2^n$) and at most $25^n$ flag strings ($5n$ classical bits suffice). The product of the fixed isometric decoders, followed by any supplied common block decoder, is CPTP on the full port algebra, including correlated ports. The local block encoder and decoder are additional supplied operations. At the coherent corner the credited error is $\varepsilon_m=(3/5)^m$, so $n(3/5)^m\le\delta$ suffices for added block error at most $\delta$; for $0<\delta<n$, one may take $m\ge\lceil\log(n/\delta)/\log(5/3)\rceil$. These are paid simulation bounds, not a capacity per source copy.

**Proposition 10.2 (Reusing one exact record need not give independent uses).** Measuring one batch once and reusing its outcome $z$ on $n$ data factors gives

$$
\Psi_X^{(n)}=\sum_z p_X^{\otimes m}(z)S_z^{\otimes n},
\tag{10.2}
$$

which need not equal $N_X^{\otimes n}$. This can fail even when every one-use channel is exact.

Proof. Retain the original fixed label $X=X_a$ and take $\eta=0$, $t=1/2$, $m=5$. Equations (8.4) and (4.2) give

$$
D=13043/25000>1/2,\qquad r=12500/13043>0,\qquad Q=q_{\emptyset}=s=1.
$$

Theorem 4.1 gives exact one-use programming. Nevertheless, the inactive statistic $h_b$ has mean zero and positive second moment; the all-$b_+$ event alone has probability $(1/5)^5>0$. On $E_{13}\otimes E_{31}$, a conditional two-use response has multiplier $(irh_b)(-irh_b)=r^2h_b^2$. Averaging gives $r^2\mathbb E_{a,+}h_b^2>0$, while the desired tensor target annihilates this operator.

To witness the failure with a normalized physical input, use the two-data-factor state of the vector

$$
|\zeta\rangle=(e_1\otimes e_3+e_3\otimes e_1)/\sqrt2.
$$

At $q_a=q_b=q_o=1$ all sector populations are preserved. The difference between the reused-record output and the target output has only the two conjugate off-diagonal entries $r^2\mathbb E h_b^2/2$ in this two-dimensional support. Its eigenvalues are $\pm r^2\mathbb E h_b^2/2$, so its trace norm is $r^2\mathbb E h_b^2>0$. This is a shared-record correlation with the same fixed source label, not a varying-label model. QED.

**Proposition 10.3 (The distinct inherited shared-label service).** For $c>0$ and $m\ge1$ there is a different whole-block processor using a single $m$-copy batch with error

$$
\sup_X\|\widetilde\Psi_X^{(n)}-\Phi_{t,\eta,X}^{\otimes n}\|_\diamond
 \le2\delta_m,\qquad \delta_m=\min\{1,4\exp(-mc^2/50)\},
\tag{10.3}
$$

uniformly in $n$. This is the supplied shared-calibration bound, not a finite-copy exact independent-use assertion.

Proof. On each measured copy retain $G_a,G_b\in\{-1,0,1\}$, the signed one-copy pair outcomes. Their four mean vectors are $(2u,0),(-2u,0),(0,2u),(0,-2u)$; distinct vectors have maximum-norm distance at least $2u$. Choose the nearest mean vector to the empirical vector in maximum norm, with a fixed tie rule, and call its label $\widehat X$. If both empirical coordinates differ by less than $u$ from their true means, the true vector is uniquely closest. The two-sided bounded-variable bound proved in Proposition 7.3, followed by the union bound over both coordinates, gives

$$
\Pr_X(\widehat X\ne X)\le4\exp(-mu^2/2)=4\exp(-mc^2/50).
$$

Conditional on the record, use the actual known target $\Phi_{t,\eta,\widehat X}^{\otimes n}$ with fresh local environments. On the correct-record event this is exactly the whole target tensor channel; otherwise its diamond distance from the target is at most two. Program/data independence, convexity and the probability estimate give (10.3), uniformly over every complex block input and reference. Measurement followed by these controlled CPTP maps has the full-algebra instrument form (4.6), with block data in place of one factor; thus it is CPTP on all inputs. Common CPTP block encoding and decoding preserve the bound. At $m=0$, choose any fixed label and use the trivial bound two. At $c=0$ implement the common target with no batch. QED.

This distinct service pays for $m$ program copies and, when separated, $m$ five-dimensional half transfers, plus $n$ forward qubits and their flags if using Section 9's route. It may retain a four-valued calibration record (two bits), after performing the empirical-count measurement. For $0<\delta<2$, $m\ge\lceil50c^{-2}\log(8/\delta)\rceil$ is sufficient for added error at most $\delta$. Neither this error estimate nor exact one-use programming justifies a claim that one finite record gives free independent exact uses. A mathematical channel-use simulation with these charged links is a different resource bundle from an unassisted channel capacity task.

## 11. Two-copy formula, scalar-diagonal comparison and implementation boundaries

**Proposition 11.1 (Explicit two-copy value and the former residual strip).** For all $t,\eta\in[0,1]$,

$$
D_2=4u(1-w),\qquad
 e_2(t,\eta)=\frac{c(1+4w)}5=\frac{c(5+4s)}{25}.
\tag{11.1}
$$

Throughout the scalar-diagonal residual region

$$
c>0,\qquad R_m<1-s,\qquad c>K_mD_m,
\tag{11.2}
$$

the attained value $[c-D_m]_+$ is strictly smaller than N1's positive error $c-K_mD_m$. This region contains the whole strip

$$
m=2,\qquad 5/16<\eta<1,\qquad 0<t\le1.
\tag{11.3}
$$

Thus the residual (11.2) is resolved by Theorem 4.1, including its nonempty two-copy strip. It imposes no restriction on that theorem's all-parameter validity.

Proof. Conditional on an observation belonging to the $a$ pair, its sign probability under $a,+$ is $p=(w+u)/(2w)$ and under $a,-$ is $1-p$. One such observation has total variation $2p-1=u/w$. For two such observations the mixed-sign words agree under the opposite laws. Each equal-sign word has absolute probability difference $p^2-(1-p)^2=2p-1$, so their total variation is again $u/w$. The number and positions of $a$ observations have the same law under both labels, and the other outcomes have identical conditional laws. A word with no $a$ observation contributes zero variation. Hence the two-copy variation is

$$
D_2=\bigl(1-(1-2w)^2\bigr)\frac{u}{w}=4u(1-w).
$$

This includes $u=0$ and $u=w$. For $c>0$, $D_2/c=4(1-w)/5<1$; Theorem 4.1 gives (11.1). At $c=0$ both sides of the final error formula are zero.

At a point of (11.2), $K_m<1$ and $c-K_mD_m>0$. This excludes $m=0$, because $R_0=1$, and $m=1$, because $R_1=1-4s/5>1-s$. Thus $D_m\ge D_1=2c/5>0$. If $D_m<c$, N1's error minus the attained error is $(1-K_m)D_m>0$. If $D_m\ge c$, the attained error is zero while N1's error is positive. This proves strict improvement throughout the region.

For two copies, a joint sign tie consists of two neutral outcomes or an opposite-sign pair in either location. Formula (5.1), or these three disjoint cases directly, gives

$$
R_2=\nu^2+2(w^2-u^2)+2w^2
 =1-8w+20w^2-2u^2,
\qquad (1-s)-R_2=w(3-4s)+2u^2.
\tag{11.4}
$$

On (11.3), $1/5<s<3/4$ and $c>0$, so this last difference is positive. Therefore $R_2<1-s$ and $K_2<1$. Since $D_2<c$, also $c>K_2D_2$. Every point of the strip lies in (11.2), as claimed. No numerical search or hypothesis about completeness of the scalar-diagonal ansatz is involved. QED.

**Scope 11.2 (Preparation, controls and native access).** The original state supply and its independence from the full data/reference are hypotheses. One-copy marginals or source certification records do not establish a tensor-power supply. Actual preparation of $\rho_{t,\eta}(X)^{\otimes m}$, calibration of exact phases and amplitudes, access to the joint PVM, and the paid spatial links are separate obligations. The supplied original volume reports approximate controllability on a single five-dimensional carrier, source-model certification under specified history or iid assumptions, and bounded classical/native preparer synthesis. None is used here as a supplier for the $25$-dimensional joint PVM, exact finite quantum controls or these four actual quantum program states. In particular, closure under approximate single-carrier gates supplies neither an exact finite pulse sequence nor a uniform physical resource bound, and it does not imply joint-carrier control. Native Boolean words, scalar spectral data and finite controller states do not become complex amplitudes, quantum programs or wires by renaming their parameters.

Exact conditional channels in this volume require exact supplied controls. No quantitative joint-PVM approximation or full approximate-control error bound is established here. Nested control, certification, native-observation and literature assertions in the supplied source are not independently verified premises for a new mathematical conclusion. The actual matrices, PVM, ordinary proofs and supplied-service model above suffice for the stated conditional results. No native acquisition, minimal physical implementation cost or physical efficiency theorem follows. No general neural-network, empirical machine-learning, improved-capacity or overall research-objective completion claim is made.

## 12. Sources, mathematical increment and evidence status

**Source statement 12.1 (Reused results and the source-specific increment).** The supplied mathematical source is [Auric FIB-ATOM: compound communication and calibration](AURIC_FIB_ATOM_HIDDEN_RELATIONS_COMPOUND_COMMUNICATION_AND_CALIBRATION.md). The correspondences are:

| Supplied scope | Reused result and present boundary |
| --- | --- |
| C-116.1–C-116.2, C-117.2, C-121.1 | Original coordinates, cut, actual sources, target/Choi correspondence and full-complex program contract; Section 1. |
| C-121.2–C-121.3 | Fixed six-outcome experiment, actual $D_m$, signed expectations, reference norm and whole-algebra instrument form; Sections 2–3. |
| C-122–C-123 | Unrestricted contraction converse, zero-noise optimum, boundary values, fixed-diagonal upper bound and bounded-variable estimate; Sections 3, 4 and 7. |
| C-124 | Fresh-batch tensor law, reused-record failure, shared-calibration service, paid qubit/flag route and five-copy endpoint value; Sections 8–10. |
| C-120, C-125–C-128 | Preparation, exact-control, native-carrier and verification boundaries; Section 11.2. |
| N1, Sections 5–6 | Joint-tie probability $R_m$ and scalar-diagonal redistribution with error $[c-K_mD_m]_+$; a lawful construction with at most nine responses. |
| N2, Section 7 | Simple certificates where N1 is optimal, direct one-copy realization $e_1=3c/5$ and response-specific finite exactness budget. |
| N3, Section 8 | Five-copy exactness points beyond the fixed-diagonal test for every sufficiently small positive noise; an explicit continuity consequence with credited endpoints. |

The source-specific increment in Propositions 2.3 and 3.1 and Theorem 4.1 is the actual-word first-occurrence bridge, separate conditional diagonal budgets for the two disjoint original pairs, and their simultaneous attainment of the unrestricted converse for every finite copy count and all parameters. Section 11.1 gives the explicit two-copy value and strict gain over N1 throughout its residual region. Corollary 4.2 gives the necessary-and-sufficient exactness test, the exact minimum prescribed-copy threshold and a sufficient finite bound. The Kraus implementation and fresh/shared distinction are applied to these pair-specific responses in Sections 9–10. This is `repo-derived` ordinary mathematical synthesis. The supplied contraction lower bound, zero-noise results, concentration estimate, endpoint values, N1–N3 and block/resource distinctions are credited rather than counted again as new results.

**Method statement 12.2 (Mature methods and evidence ceiling).** Choi positivity, Kraus decomposition, trace-norm contraction, diamond-norm ancillary stability and telescoping are standard finite-dimensional channel tools. The probability identities use finite product laws, multinomial algebra and permutation symmetry. The first-occurrence bridge uses only a deterministic grouping of the same actual words. The bounded-mgf argument is the elementary Hoeffding method, with its constants proved here. Continuity and the intermediate value theorem supply N3. These mature methods are credited, not presented as newly invented generic theorems.

No primary literature or nested source is claimed independently verified here, and no exhaustive originality search or global novelty conclusion is asserted. The mathematical claims rest on the complete ordinary proofs in this volume under its stated supplied-service assumptions. They do not carry a Lean/kernel certificate.

**Conclusion 12.3 (Exact scope).** For every finite $m\ge0$ and every known $t,\eta\in[0,1]$, the four original prescribed tensor programs have attained unrestricted minimax $e_m=[c-D_m]_+$. One common whole-algebra complex CPTP processor attains that value simultaneously for the four labels with all finite complex references; the converse covers the entire competitor class. Exactness is equivalent to $D_m\ge c$, and (4.9) is the minimum prescribed-copy threshold. The sufficient closed-form bound (4.10) is distinct from that minimum; the sole infinite boundary is $c=1$.

The program supply and its independence, exact controls and the joint PVM remain supplied services. The route proved here pays all source copies, ancillary pointers and flags, and the declared quantum/classical links. Fresh independent uses obey the error bound $\min\{2,n[c-D_m]_+\}$ at cost $nm$ copies; a reused record has its different mixture law. Native quantum preparation, physical efficiency, optimal physical acquisition/transport cost, improved channel capacity, general neural networks, empirical machine learning and completion of the overall research objective are outside these results.

## 追加锚（本行以下为增补区）
