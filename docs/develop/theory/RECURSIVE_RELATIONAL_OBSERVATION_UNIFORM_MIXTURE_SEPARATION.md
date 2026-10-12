# Uniform full-tail separation from constant-parameter mixtures

## 1. The unchanged experiment and the statement's scope

For a prior with positive mass on at least one depth $k\ge3$, this volume proves a necessary quantitative property of one finite observer approaching the common p-conf and suspended-law minima. The same result therefore applies to the common conf/conf question. Even with arbitrarily many finite configurations, its p decoders cannot approach the entire family of constant-parameter stopped-law mixtures uniformly in configuration-average full-tail TV over positive actual histories.

The result is a structural restriction on the remaining common-model frontier. It supplies a positive risk gap on an explicitly defined neighborhood of that representation family. The unrestricted risk gap and an exact conf/conf attaining table remain undecided.

Keep the source of [ST], [PH] and the full-marker writer clause of [E1]. The fixed parameters are $m=2,d=1,\ell=2,n=4$. One common $K$ is drawn once, before all Reads, from one fixed finite or countable prior $\mu$ with $\mu(1),\mu(2)>0$. That same draw is used for every paid seed rejection and every payload Read. Conditional on this same $K=k$, all paid seed Reads and payload Reads are independent with α probability

$$
r_k=F_{k+1}/F_{k+3},\qquad r_1=1/3,\quad r_2=2/5,\quad r_k\in [3/8,5/13]\ (k\ge 3).
$$

Equal seed pairs are rejected and both Reads remain paid. The unequal pairs accept the two original seeds. At payload p, α completes marker 0 and β suspends. At suspension, α returns to p and β completes marker 1. The third record is written before its latch. Fourth completion enables only its matching original Stop, with unique delivery. Pending and delivered states admit no Read.

The original finite control C₀ contains both seeds, parser, selectors, full marker tree, bare fields, held B,Q⁺,Z records, write/latch flags, permissions and completion/Stop control. Both seeds, every marker triple, and every positive finite rejection and return history remain in the domain. There is no source reset, fresh depth, future-E₁ conditioning, additional observation or controller port.

Put a_r=r(1-r) and

$$
w_{j,0}=(\beta \alpha )^j\alpha ,\qquad w_{j,1}=(\beta \alpha )^j\beta \beta ,\qquad j\ge 0.
$$

The complete p carrier consists of these words and the infinite noncompletion word. The suspended carrier consists of β, the words αw_{j,b}, and its infinite noncompletion word. For any mathematical parameter r∈I:=[1/3,2/5], define

$$
P_{p,r}(w_{j,0})=r a_r^j,\qquad P_{p,r}(w_{j,1})=(1-r)^2a_r^j,
$$

$$
P_{\beta ,r}(\beta )=1-r,\quad P_{\beta ,r}(\alpha w_{j,0})=r^2a_r^j,\quad P_{\beta ,r}(\alpha w_{j,1})=r(1-r)^2a_r^j.
$$

The geometric sums give total mass one; their noncompletion masses are zero. Introducing I as a comparison interval changes no actual depth or source operation.

For the current actual control c, the original map I_c retains every future Read and inserts exactly its original deterministic control, record, permission, completion and Stop events. Reading back the letters is its inverse. On these countable fourth-segment carriers the maps are measurable bijections, preserve TV, and commute with deleting the next operation and its deterministic event block. The acquired suspended β is not a future Read.

At a positive actual history h the target is

$$
\begin{aligned}
T_h^\mu&=(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k},\\
\nu_h(k)&=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
{\sum_t\mu(t)r_t^{A(h)}(1-r_t)^{B(h)}}.
\end{aligned}
$$

All acquired Reads, including rejected and partial pairs, contribute to the counts. These counts and posterior probabilities are analysis quantities.

An observer has one fixed finite COMPLETE carrier, source-independent initialization, fixed time-homogeneous source-independent letter kernels and a decoder reading one actual configuration. COMPLETE includes the entire original control, program/table selectors, workspace, addresses, output indices and persistent randomness. There is no readable distribution vector, continuous hidden register, uncounted tape, clock, archive, advice or source-correlated seed.

Every decoder is the complete law of its own finite generator, using its synthetic letter probabilities and the same acquired-letter kernels. In particular, at a p configuration x and suspended configuration y, write their raw laws Q_x,W_y, their synthetic α probabilities u_x,v_y, and their actual noncompleting kernels B:X→Y and A:Y→X. Exact individual generation requires

$$
\begin{aligned}
Q_x(\beta E)&=(1-u_x)\sum_y B_{xy}W_y(E),\\
W_y(\alpha E)&=v_y\sum_x A_{yx}Q_x(E).
\end{aligned}
\tag{1.1}
$$

These identities do not assume marginalized coherence. They hold on complete futures, including possible predicted noncompletion. No positivity restriction is imposed on u or v.

For the conditional configuration row ρ_h, define

$$
\begin{aligned}
Q_h&=\sum_z\rho_h(z)D_z,\\
e_{\mathrm{law}}(h)&=\operatorname{TV}(Q_h,T_h^\mu),\\
e_{\mathrm{conf}}(h)&=\sum_z\rho_h(z)\operatorname{TV}(D_z,T_h^\mu).
\end{aligned}
$$

Here TV is the event-supremum convention, equivalently half the ℓ¹ distance on the fourth-tail carrier. R_{j,s} is the supremum over all positive histories in H_s, for s=p,β. H_p includes arbitrary fourth-segment returns; H₃ is only the first such p cut.

Retain the original defect. For a legal operation $a$, put $q_h(a)=Q_h([a])$, the predicted probability of its original next-operation cylinder. When $q_h(a)>0$, $\operatorname{res}_aQ_h$ means conditioning on that cylinder and deleting the operation together with its deterministic original event block. Define

$$
\delta (h,a)=\operatorname{TV}(\operatorname{res}_a Q_h,Q_{ha}).
$$

When q_h(a)=0, its defect is zero without defining a conditional law; the actual successor and its risk remain in the domain. Δ₄ and Δ_all take their respective fourth-segment and full original-operation suprema. The pending Stop successor has zero defect and the delivered empty supremum is zero. Exact zero defect means precisely the conditional equalities on positive predicted events. This volume assumes no defect budget, obtains no zero-defect model by taking a limit, and retains exact individual generation throughout.

The supplied separate full-tail minima are

$$
\rho _p=1116529/22781250,\qquad \rho _\beta =239/6750.
$$

The separate terminal projections have the supplied values 13/266 and 9/266. Those projections are not used in place of the complete laws.

## 2. One common actual row

The following is the common paid-history extraction of [NATIVE], §3 and [FLOW], §3, with the additional bounded state statistic recorded explicitly. It is reused machinery, not a new periodicization theorem.

**Lemma 2.1.** Fix one allowed finite observer and one allowed prior. On a fixed original record fibre there are finite p and suspended carriers X,Y, actual kernels B,A and probability rows π,τ such that

$$
\pi B=\tau ,\qquad \tau A=\pi .
$$

For every supported k, simultaneously,

$$
\sum_x\pi _x\operatorname{TV}(Q_x,P_{p,r_k})\le R_{\mathrm{conf},p},\qquad \operatorname{TV}\left(\sum_y\tau _yW_y,P_{\beta ,r_k}\right)\le R_{\mathrm{law},\beta }.\tag{2.1}
$$

For every bounded nonnegative function f of the p configuration,

$$
\pi f\le \sup_{h\in H_p}\sum_z\rho _h(z)f(z),\tag{2.2}
$$

where f on this fibre is the restriction of the corresponding original state function. Every positive-weight state in this row is reachable after a finite positive actual history.

**Proof.** Use the fixed legal suffix S=βα|ββαα. It accepts seed 1, writes markers 100, and reaches the third latch before any fourth Read. At the seed-pair boundary, the two equal-pair updates are finite stochastic matrices. The standard finite-chain decomposition supplies positive integers d_α,d_β such that their powers along multiples of these integers converge to matrices E_α,E_β. Closed-class periods are removed by the common multiples; transient mass tends to zero and each remaining aperiodic finite class has convergent powers.

For each supported $r=r_k$, set

$$
m_n=d_\alpha\left\lfloor\frac{nr}{d_\alpha}\right\rfloor,
\qquad t_n=d_\beta\left\lfloor\frac{n(1-r)}{d_\beta}\right\rfloor,
$$

and consider the original paid histories

$$
(\alpha \alpha )^{m_n}(\beta \beta )^{t_n}S.
$$

Their configuration rows converge to the same λ=η₀E_αE_βP_S, independently of r. Every rejected pair is an actual paid pair. The finite suffix fixes the same original records and permissions.

Relative to the chosen depth r, another supported parameter r_i has rejection likelihood ratio exp(−2n KL(Ber(r)||Ber(r_i))+O(1)). The bounded rounding error is uniform in i because all parameters lie in I. The Fibonacci ratios are distinct: their recurrence r↦(1−r)/(2−r) is a strict contraction with an irrational fixed point, so its rational orbit has no repetition. Hence each competing likelihood ratio tends to zero. Multiplying by the summable prior masses and the positive fixed-suffix likelihoods, dominated convergence shows that the entire posterior concentrates at the chosen depth. This includes countable priors.

Appending any fixed number j of original returns, and optionally the next β, preserves posterior concentration and gives the common rows λ(BA)^j and λ(BA)^jB. Full-tail target convergence is in TV because a mixture with posterior mass at least 1−ζ at k is within ζ of P_{s,r_k}. Configuration risk is 1-Lipschitz in its target. Finite mixing of the fixed decoded measures is continuous in the row. Thus (2.1) holds first for every j with those rows, and (2.2) holds by its defining actual-history bound.

Take a convergent subsequence of the Cesàro rows

$$
\pi_N=\frac1N\sum_{j<N}\lambda(BA)^j.
$$

The telescoping identity π_NBA−π_N=(λ(BA)^N−λ)/N gives πBA=π. Put τ=πB. Configuration loss and f are linear in the row; marginalized loss is convex. Averaging and then taking the finite-row limit preserves all the bounds, for every supported k on the same π. A positive limiting coordinate is positive in some finite λ(BA)^j and hence in a sufficiently late finite paid-history approximant. This proves reachability. No row or limiting history is installed in the observer. ∎

The lemma can retain the other two risk bounds as well. Only the displayed bounds are needed below. Its use of H_p is material; no H₃-only assertion follows.

## 3. A signed change specific to the stopped source

Write δ_p=2ρ_p and δ_β=2ρ_β. Define the complete-word events

$$
E_p=\{w_{0,1},w_{1,1},w_{2,1}\},\qquad E_\beta =\{\beta ,\alpha \beta \beta \}.
$$

They are the positive-difference events of endpoint 1 against endpoint 2. Indeed, for p marker-1 words the endpoint-2/endpoint-1 ratio is (81/100)(27/25)^j, crossing one between j=2 and j=3. For suspended αw_{j,1} the ratio is (243/250)(27/25)^j, crossing between j=0 and j=1. The marker-0 ratios exceed one throughout. Consequently

$$
\delta _p=412/729-7299/15625=1116529/11390625,
$$

$$
\delta _\beta =22/27-93/125=239/3375.
$$

For r∈I, their probabilities are

$$
\varphi _p(r)=(1-r)^2(1+a_r+a_r^2),\qquad \varphi _\beta (r)=1-r+r(1-r)^2.
$$

Use the scaled parameter z=15r−5∈[0,1]. The normalized event scores are

$$
\begin{aligned}
T(z)&=\frac{412/729-\varphi _p((5+z)/15)}{\delta _p}\\
&=\frac{1125000z-1875z^2-6625z^3+30z^5-z^6}{1116529}.
\end{aligned}
$$

$$
\begin{aligned}
S(z)&=\frac{22/27-\varphi _\beta ((5+z)/15)}{\delta _\beta }\\
&=\frac{225z+15z^2-z^3}{239}.
\end{aligned}
\tag{3.1}
$$

Both run from zero to one. For example the numerator derivative of T is at least 1101369 on [0,1], and S′(z)≥225/239.

**Lemma 3.1.** Let ω be any Borel probability distribution of r on the full interval I, and let Z=15r−5 under ω. Put m=E[Z] and

$$
d(\omega )=E[T(Z)]-\frac{E[(10-Z)S(Z)]}{10-E[Z]}.
$$

Then

$$
d(\omega )\ge m(1-m)/16.\tag{3.2}
$$

**Proof.** Direct expansion of (3.1) gives the exact factorization

$$
T(z)-S(z)=\frac{z(1-z)R(z)}{239\cdot 1116529},
$$

$$
R(z)=17655975+459915z-6931z^2-6931z^3+239z^4.
$$

On [0,1], R(z)≥17642113, and

$$
16\cdot 17642113=282273808>266850431=239\cdot 1116529.
$$

Thus T(z)−S(z)≥z(1−z)/16. This sign is a calculation for the two original stopped-source events; it is not an assumption about arbitrary prediction tasks.

The definition of d also gives

$$
d(\omega )=E[T(Z)-S(Z)]+\frac{\operatorname{Cov}(Z,S(Z))}{10-m}.\tag{3.3}
$$

For an independent copy Z′,

$$
\operatorname{Cov}(Z,S(Z))=\tfrac12E[(Z-Z')(S(Z)-S(Z'))]\ge (225/239)\operatorname{Var}(Z),
$$

by the derivative bound. Since 10−m≤10, its contribution in (3.3) is at least (45/478)Var(Z), which is greater than Var(Z)/16. Therefore

$$
d(\omega )\ge [E(Z(1-Z))+\operatorname{Var}(Z)]/16=m(1-m)/16.
$$

All expectations are of bounded functions; arbitrary Borel mixtures are covered. ∎

The second term in $d$ has an exact source meaning. Define the comparison law and its first-$\beta$ probability by

$$
N_\omega=\int_I P_{p,r}\,\omega(dr),\qquad
q_\omega=\int_I(1-r)\,\omega(dr)=\frac{10-m}{15}\ge\frac35.
$$

Conditioning this comparison law on its first β gives the suspended mixture with weights (1−r)ω(dr)/q_ω. Its normalized E_β score is precisely the second term in d.

The measure ω is an analysis comparison. It is neither the actual source posterior nor a register supplied to the observer. Only this comparison law is likelihood-normalized. Actual configuration rows still move by the installed acquired kernel B.

## 4. Small signed change forces a mixture near a pure endpoint

Let

$$
G_p=\left\{\int_I P_{p,r}\,\omega (dr):\omega \text{ is a Borel probability on }I\right\}.
$$

This contains all actual posterior p-tail laws. It also permits a larger comparison parameter interval than [NATIVE], which uses the two endpoints and [3/8,5/13]. Membership in G_p is a semantic comparison property; no arbitrary Borel mixture is being offered as a finite executable decoder.

**Lemma 4.1.** With L=125/57 and C=32L/15=800/171, every ω admits i∈{1,2} such that

$$
\operatorname{TV}(N_\omega ,P_{p,r_i})\le C\,d(\omega ).\tag{4.1}
$$

**Proof.** First prove the full-law bound TV(P_{p,r},P_{p,t})≤L|r−t|. Couple their Bernoulli letters with the same fresh uniforms until the first discrepancy. Before a discrepancy both parsers coincide. At each live Read the discrepancy probability is |r−t|. For parameter r the expected number of remaining Reads is

$$
E_rN=(2-r)/(1-a_r)\le (5/3)/(19/25)=125/57.
$$

The recursion is E_rN=1+(1−r)(1+rE_rN). Summing first-discrepancy hazards is therefore bounded by L|r−t|. If there is no discrepancy, the entire stopped word and every rendered original event agree. Both source laws complete almost surely. The coupling thus bounds TV on the complete carrier, without a future cutoff.

Choose endpoint 1 if m≤1/2 and endpoint 2 otherwise. Mixture convexity gives

$$
\operatorname{TV}(N_\omega ,P_{p,r_i})\le (L/15)\min(m,1-m)\le (2L/15)m(1-m).
$$

Apply Lemma 3.1. ∎

The parameter-continuity estimate is a reused elementary coupling bound, also present in the CLIP/PAID source chain. The new use is its composition with the signed event change (3.2).

## 5. The universal risk–representation inequality

For a p configuration z on current original fibre c, define

$$
g(z)=\inf_{N\in G_p}\operatorname{TV}(D_z,(I_c)_*N).
$$

Define its worst-positive-history configuration-average value

$$
E_G(M)=\sup_{h\in H_p}\sum_z\rho _h(z)g(z).\tag{5.1}
$$

This is not TV after averaging the decoders, an average over random actual histories, or the marginalized-coherence defect.

Assume μ({k≥3})>0. Set

$$
\begin{aligned}
\eta &=(5/13)^3(8/13)^5-(2/5)^3(3/5)^5\\
&=14219478376/318644812890625>0.
\end{aligned}
$$

$$
A_p=1+C/\delta _p,\qquad A_\beta =C/\delta _\beta ,\qquad A_G=A_p+(10/3)A_\beta .\tag{5.2}
$$

**Theorem 5.1.** Let M be any allowed finite COMPLETE same-update observer, with arbitrary finite carrier and arbitrary stochastic entries. For either j_β=law or j_β=conf, put

$$
\varepsilon _p=R_{\mathrm{conf},p}(M)-\rho _p,\qquad \varepsilon _\beta =R_{j_\beta ,\beta }(M)-\rho _\beta .
$$

Then

$$
A_p \varepsilon _p+A_\beta  \varepsilon _\beta +A_G E_G(M)\ge \eta /4.\tag{5.3}
$$

The bound has no state-count, period, prior-mass-floor, regular-emission or marginalized-defect hypothesis.

**Proof.** Use the single common π,τ,B from Lemma 2.1. The suspended law bounds hold with ρ_β+ε_β in either order, by TV convexity. The supplied separate lower bounds, or the common-row endpoint triangle inequality, give ε_p,ε_β≥0.

For each p state x choose a comparison N_x=N_{ω_x}∈G_p and let e_x=TV(Q_x,N_x), $e=\sum_x\pi_xe_x$. Choices may approach the infimum arbitrarily closely; no minimizing mixture or effective description of it is required.

Let $\overline T=\sum_x\pi_x\mathbb E_{\omega_x}[T(Z)]$, and let $\overline S$ be the corresponding average of the likelihood-normalized suspended scores in Lemma 3.1. The p mixture ∑π_xN_x is within e of ∑π_xQ_x. Its E_p probability is 412/729−δ_pT̄. The two pure-endpoint risk bounds therefore imply

$$
|\overline T-1/2|\le (\varepsilon _p+e)/\delta _p.\tag{5.4}
$$

For the suspended comparison, put $R_x=\sum_y B_{xy}W_y$ and let S_x be the β-conditional law of N_x. Write $q_x=N_x([\beta])\ge3/5$ and $\widehat q_x=Q_x([\beta])=1-u_x$. Exact individual generation gives $Q_x(\beta E)=\widehat q_xR_x(E)$, whereas N_x(βE)=q_xS_x(E). For every residual event E,

$$
q_x|R_x(E)-S_x(E)|\le |Q_x(\beta E)-N_x(\beta E)|+|q_x-\widehat q_x|R_x(E)\le 2e_x.
$$

Consequently

$$
\operatorname{TV}(R_x,S_x)\le (10/3)e_x.\tag{5.5}
$$

This argument divides only by the comparison probability q_x. If $\widehat q_x=0$, R_x is still the installed actual successor-law mixture; it is not being called a conditional law of a zero event. Thus (5.5) respects the original zero-probability convention.

Because πB=τ, the actual suspended marginal ∑τ_yW_y equals ∑π_xR_x. Equation (5.5) places it within (10/3)e of ∑π_xS_x. The latter's E_β probability is 22/27−δ_βS̄. The two suspended endpoint bounds give

$$
|\overline S-1/2|\le [\varepsilon _\beta +(10/3)e]/\delta _\beta .\tag{5.6}
$$

Every d(ω_x) is nonnegative. From (5.4)–(5.6),

$$
\begin{aligned}
\sum_x\pi_xd(\omega_x)&=\overline T-\overline S\le D,\\
D&=\frac{\varepsilon_p+e}{\delta_p}
+\frac{\varepsilon_\beta+(10/3)e}{\delta_\beta}.
\end{aligned}
\tag{5.7}
$$

Choose for each x the pure endpoint P_{p,r_{i(x)}} supplied by Lemma 4.1. Their mean distance from the actual Q_x is at most

$$
Z_0:=\sum_x\pi _x\operatorname{TV}(Q_x,P_{p,r_{i(x)}})\le e+CD.\tag{5.8}
$$

This is only an analysis comparison. The observer, its kernels and its decoded laws have not been changed.

Let $q=\sum_{x:i(x)=2}\pi_x$. Comparing configuration losses against each endpoint gives

$$
q\delta _p\le \rho _p+\varepsilon _p+Z_0,\qquad (1-q)\delta _p\le \rho _p+\varepsilon _p+Z_0,
$$

hence |q−1/2|≤(ε_p+Z_0)/δ_p.

Choose any actually supported k₀≥3 and put $r_0=r_{k_0}$. The complete word w_{3,1} has probability J(r)=r³(1−r)⁵. Its derivative has the sign of 3−8r. Therefore, throughout [3/8,5/13],

$$
J(r)\ge J(5/13)=J(2/5)+\eta >J(1/3).
$$

The last endpoint comparison follows also from 1944·6561>32·390625. Write $P_i=P_{p,r_i}$. For any probability law $T$ on this complete carrier, including its infinite noncompletion outcome, the coordinate triangle identity is

$$
\begin{aligned}
&\operatorname{TV}(P_1,T)+\operatorname{TV}(T,P_2)-\operatorname{TV}(P_1,P_2)\\
&\quad=\sum_w \operatorname{dist}\!\left(T(w),[\min(P_1(w),P_2(w)),\max(P_1(w),P_2(w))]\right).
\end{aligned}
$$

Apply it to T=P_{p,r₀}. The single complete word w_{3,1} contributes at least η, so, writing d_i=TV(P_{p,r_i},P_{p,r₀}),

$$
d_1+d_2\ge \delta _p+\eta ,\qquad |d_2-d_1|\le \delta _p.
$$

The same common-row configuration loss against this actual supported depth is thus at least

$$
\begin{aligned}
\sum_x\pi_x\operatorname{TV}(Q_x,P_{p,r_0})
&\ge (1-q)d_1+qd_2-Z_0\\
&\ge \rho_p+\eta/2-\varepsilon_p-2Z_0.
\end{aligned}
$$

Its upper bound is ρ_p+ε_p by Lemma 2.1. It follows that

$$
\varepsilon _p+Z_0\ge \eta /4.
$$

Using (5.7)–(5.8) gives

$$
\varepsilon _p+e+C\{(\varepsilon _p+e)/\delta _p+[\varepsilon _\beta +(10/3)e]/\delta _\beta \}\ge \eta /4.
$$

Let the chosen comparison errors decrease to e_G:=∑π_xg(x). Lemma 2.1 gives e_G≤E_G(M). The expression is increasing in this error, and expanding its coefficients proves (5.3). Every coordinate used belongs to the same observer, prior, record fibre and actual-history domain. ∎

The proof uses the actual p→β flow after common-row extraction. The competitor still has its complete original suspended α update and every other required update. No operation or generation obligation is removed because a particular inequality needs only one edge.

## 6. A closed excluded neighborhood and its limits

Put

$$
e_*:=\eta /(4A_G)>0,\qquad c_*:=\eta /[8(A_p+A_\beta )]>0.
$$

**Corollary 6.1.** Under the additional-depth premise of Theorem 5.1:

1. Every exact common conf/law or conf/conf endpoint observer satisfies E_G(M)≥e_*.
2. Every sequence of finite observers on the same source and prior whose corresponding two excesses tend to zero satisfies liminf E_G(M_n)≥e_*. Their state counts may grow without bound.
3. Every finite observer with E_G(M)≤e_*/2 satisfies max(ε_p,ε_β)≥c_*.

**Proof.** The first two statements follow directly from (5.3). In the third, A_GE_G≤η/8, so A_pε_p+A_βε_β≥η/8; bound this by (A_p+A_β)max(ε_p,ε_β). ∎

Thus the positive gap in item 3 is uniform over all finite shapes satisfying its explicit semantic-distance premise. That premise is not known to hold for unrestricted competitors. The result supplies neither an unrestricted positive gap nor a common attaining table.

The proof also gives the distance bound on the common stationary analysis row itself. For an arbitrary original observer, E_G is a supremum over actual positive histories. For every ζ>0 below e_*, an exact endpoint observer therefore has a positive finite p history with configuration-average distance greater than e_*−ζ. There is no asserted uniform bound on that history's paid length or probability. This is not an average-error statement and does not identify that history on one realized source run.

The four risk combinations retain their distinction:

| p order | Suspended order | Consequence here |
| --- | --- | --- |
| conf | law | Theorem 5.1 and Corollary 6.1 apply |
| conf | conf | The same bounds apply through suspended TV convexity |
| law | law | No representation-separation theorem is asserted |
| law | conf | No representation-separation theorem is asserted |

Reused boundary example. The fair persistent endpoint tag shows why the additional-depth and risk-order clauses matter. Retain C₀ from initialization. In the same third-marker update, after its record write and latch, sample one fair source-independent bit. In the fourth segment keep that bit under both acquired noncompleting letters and use synthetic parameter r₁ or r₂ accordingly. Earlier synthetic letters may be fair; completion clears the tag and preserves the original Stop. Every seed and record fibre uses the same rule.

The effective private kernels are identities on the two tags, so the actual fourth-segment row is fair after every positive history. Each individual p decoder is P_{p,r_i}, giving E_G=0. Its synthetic law is generated by precisely those installed updates. Seed and early-payload survival is geometric, as is fourth-payload survival; all legal infinite outcomes remain in the carrier with zero synthetic mass. Full records and events follow I_c.

If the actual prior has only the two endpoints, every actual target is an endpoint mixture. The fair configuration-average distance equals δ_s/2 in either phase, while the marginalized distance is at most δ_s/2 and approaches it along the supplied paid witnesses. Thus this one finite observer attains all four combinations with E_G=0. The hypothesis μ({k≥3})>0 is essential.

Its marginalized defect is different from E_G. Conditioning its p mixture on β changes the endpoint-2 weight from 1/2 to 9/19, giving defect δ_β/38. Conditioning its suspended mixture on α changes the weight to 6/11, giving defect δ_p/22. Earlier and terminal defects are zero in this latch realization. Hence Δ_all=Δ₄=δ_p/22>0 although E_G=0.

For a supported nonendpoint, the complete-word argument in Theorem 5.1 gives this tag model p-conf risk at least ρ_p+η/2. The original actual three-depth counterexample in [ST], (3.17)–(3.21) remains the more specific finite-history example with prior (1/10000,1/10000,4999/5000) and h₀=βα|ββαα. Neither that example nor the present reused tag calculation is an arbitrary-kernel risk obstruction by itself. The universal content here comes from (5.5), the signed drift and the common-row argument.

## 7. Correspondence, whitebox consequence and the remaining path

The new source-specific ingredients are the signed polynomial comparison of the two complete-word events, its covariance term under the native comparison's β likelihood, and its propagation through the actual acquired B kernel with an explicit full-law error. Together they produce a uniform neighborhood exclusion without installing a replacement decoder. TV convexity, covariance identities, coupling and finite-chain limits are mature tools within this proof.

[NATIVE], §§4–7 proves spectral/recurrence restrictions for exact mixtures on {1/3,2/5}∪[3/8,5/13], and a positive p-conf gap under exact mixture membership and positive suspended emission. The present comparison family uses every r∈[1/3,2/5]. More importantly, the theorem permits completely arbitrary actual decoder laws and bounds their distance from that larger family. Exact membership results do not justify replacing nearby laws while keeping their own generator. Equation (5.5) is the required causal comparison and does not presume that replacement is executable. The additional suspended near-optimality assumption is explicit; this theorem does not replace NATIVE's differently scoped p-only result.

[PAID], §§9–10 already supplies uniform label aggregation, both exact acquired flows, regeneration of each replacement's own law, all-four-risk approximation, soft defect comparison and corrected all-shape certification. [FLOW] and [CLIP] supply the earlier flow, regularization and feasibility framework. No such capability is claimed as new here. The cited PAID §§9–10 are fixed at their scientific supplier pin; the additional published §11 is cited separately below at its full newer pin.

[PAID11], §11 at `f679023d5d0cad505cefbf096b498f6fdf935f88`, supplies an explicit rational common two-label table. Its Definition 11.1 has a fair latch row, a symmetric doubly stochastic acquired $B$ kernel, acquired $A=I$, and separately specified p and suspended emissions. Its Theorem 11.2 proves, for every allowed finite or countable prior, the same-history bounds

$$
0\le R_{\mathrm{conf},s}(M_{\mathrm{paid}})-\rho_s
<\frac{11}{10^8},\qquad s=p,\beta,
$$

and the strictly positive own-witness bound

$$
R_{\mathrm{conf},p}(M_{\mathrm{paid}})-\rho_p
>\frac{109467}{10^{12}}.
$$

Law-order upper bounds follow there for this same table. These are supplied results, not a construction or certificate claimed by this volume.

The source correspondence is literal: both volumes use $m=2,d=1,\ell=2,n=4$, one $K$ drawn once before all Reads from the installed prior, paid equal-pair seed rejection, all original marker fibers and return histories, third-write-before-latch, and the complete $I_c$-rendered tail with pendingStop and deliveredStop. The table's fair actual rows obey $\pi B=\tau$ and $\tau A=\pi$ without synthetic-emission reweighting, exactly as the rows used here. Its two phase laws are generated by its own emissions and these same acquired-letter updates, so the table is a lawful instance of Theorem 5.1 whenever $\mu(\{k\ge3\})>0$. Its Proposition 11.3 charges the finite rational sampler and all original control and service states; the two private labels are not the COMPLETE configuration count. Neither volume treats an analysis row or a posterior vector as runtime input.

PAID11 proves this witness's marginalized suspended-$\alpha$ defect exceeds $3/1000$. That defect is distinct from $E_G$. Its native-mixture nonmembership uses the smaller original depth-mixture family, whereas $G_p$ here allows every parameter in $[1/3,2/5]$. Nonmembership in that smaller family gives no inferred distance from $G_p$. We do not evaluate $E_G(M_{\mathrm{paid}})$ or infer a positive representation distance for this witness from its risk or defect bounds. Substitution into (5.3) yields only the same inequality for its actual risks and its unevaluated $E_G$.

PAID11's positive upper witness and positive own excess select none of exact endpoint attainment, an unattained zero infimum, or a positive unrestricted infimum. The uncovered result retained here is the arbitrary-kernel joint risk–representation inequality (5.3), including perturbations away from the larger interval-mixture family with no positive-emission hypothesis. It neither republishes PAID11's table nor extends its numerical certificate to zero excess.

The boundary geometry [GEOMETRY], §76 concerns unit Euclidean seams, grounded leaf stubs, a height band and planar-width necessity. [KB], §91 concerns matched readers, immutable INITIAL targets, inherited tails and fully paid emitted words. Neither contract supplies the Bernoulli stopped laws, B-pushforward identity or configuration-risk metric used above. No stochastic-risk conclusion is transported from either source. FIB recursive windows remain source syntax and relation structure; they are not labels for arbitrary learned networks.

The primary literature has narrower uses. [COHEN], Theorem 1 records classical likelihood-normalized filtering; the normalization here is a mathematical conditional law of N_ω, never a free online posterior. [CK], Theorem 7 and Corollary 8 supply fixed-chain TV approximation, already relevant to PAID's effectivity. [BOS], §1 and Theorem 1, studies finite-memory Bernoulli estimation under long-run quadratic loss, with a separate randomness convention. None provides the signed original-event comparison (3.2) or this common-history configuration-risk theorem.

For task-relative quality W_{j,s}=1−R_{j,s}, write $W_p^*=1-\rho_p$ and $W_\beta^*=1-\rho_\beta$. The same original model satisfies

$$
A_p(W_p^*-W_{conf,p})+A_\beta (W_\beta ^*-W_{j_\beta ,\beta })+A_GE_G\ge \eta /4.
$$

Under the additional-depth premise of Theorem 5.1, approaching both stated best qualities therefore requires a fixed positive departure of some configuration-level full-tail forecasts from all constant-parameter mixtures on the source interval. Every actual target still belongs to that mixture family. This is a constraint on a task-relative interpretation of the forecasts, not recovery of hidden K, a unique implementation, trained-network architecture or erased chronology. The distance is taken before configuration marginalization.

No resource is supplied by the proof's π,τ,ω, normalized scores, infima or history sequences. Actual decoders retain their finite generated-law descriptions. The analysis mixtures may have continuous support and are not asserted to be implementable as additional finite decoders. Installed real matrices remain mathematical constants; an effective sampler needs its own represented finite program. Original acquired Reads, retained records, description/precision, workspace, synthetic output, random bits, time, energy and physical realization remain separate accounts. No original fixed COMPLETE or total-resource budget is enlarged or optimized. The reused fair-tag example has finite rational rules, but all sampler and service states must still be charged; arbitrary output length and total execution work have no finite worst-case bound.

A concrete next question is whether a nonnative finite return mass kernel can compensate for the signed phase change while maintaining both actual flows, the complete endpoint coordinate boxes and every supported nonendpoint configuration-risk bound. One candidate representation to examine is a genuinely nonnative additional return mode that changes the w_{3,1} response while preserving the two mean event masses. Its stochastic positive realization and all-return inequalities would have to be proved from the same B,A and emissions; signed expansion coefficients would be analysis coordinates, never negative transition probabilities. This volume does not assert that two modes suffice.

Exact finite conf/conf attainment, unattained zero excess, a positive unrestricted gap, sharp defect budgets, H₃-only or actual-history-average variants and fixed-resource optima remain distinct. The continuing research objective remains active.

### Sources

- **ST.** [随机有限保持：可数深度终局价格与两深度完整停止尾律](https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md). Public repository supplier, pin `d54b775b50754d407dd4e39ea1d4c6c7d67d5021`; §§1–4.
- **E1.** [Extending the retained incidence to the full finite accepted cell](https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md). Public repository supplier, pin `d54b775b50754d407dd4e39ea1d4c6c7d67d5021`; §2, full-marker writer clause.
- **PH.** [相位闭合预测：一般深度先验的完整停止律尖锐半径](https://github.com/the-omega-institute/trureturing/blob/6004bfffc63af86a0d9780a092da7c6c34c79e34/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md). Public repository supplier, pin `6004bfffc63af86a0d9780a092da7c6c34c79e34`; §§1–2.
- **NATIVE.** [原深度混合并不足够：同更新返回常返类与配置风险的表示障碍](https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md). Public repository supplier, pin `54dc9a9bd356fe584703022a3a4c0b0978f557de`; §§3–7.
- **FLOW.** [保持实际配置流的有理实现：正缺陷联合前沿的完整尾闭包](https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FLOW_PRESERVING_RATIONAL_FRONTIER.md). Public repository supplier, pin `54dc9a9bd356fe584703022a3a4c0b0978f557de`; §§2–3 and 7–9.
- **CLIP.** [Risk-controlled emission clipping and finite moment feasibility for the unchanged stopped Fibonacci source](https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md). Public repository supplier, pin `54dc9a9bd356fe584703022a3a4c0b0978f557de`; §§1–3 and 6–8.
- **PAID.** [Effective paid-history certificates for the common-model configuration-risk frontier](https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md). Public repository supplier, pin `54dc9a9bd356fe584703022a3a4c0b0978f557de`; §§1–2 and 9–10.
- **PAID11.** [Effective paid-history certificates, §11: One rational common table with uniformly small positive excess](https://github.com/the-omega-institute/trureturing/blob/f679023d5d0cad505cefbf096b498f6fdf935f88/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md). Public repository supplier, pin `f679023d5d0cad505cefbf096b498f6fdf935f88`; Definitions 11.1, Theorem 11.2 and Proposition 11.3.
- **GEOMETRY.** [FIB ATOM recursive holographic boundary geometry, continuation II, §76: Planar grounding width and the minimum universal dimension of the unit skeleton](https://github.com/the-omega-institute/trureturing/blob/8ab8a2d8e588b3c12d11bf8e845d63e6c95319f3/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md). Public repository supplier, pin `8ab8a2d8e588b3c12d11bf8e845d63e6c95319f3`; Definition 76.1 and its source/geometry contract.
- **KB.** [KBonacci full positive-window logarithmic price, §91: Exact positive-child fees, exterior-edge zeros and an incoming endpoint obstruction](https://github.com/the-omega-institute/trureturing/blob/8ab8a2d8e588b3c12d11bf8e845d63e6c95319f3/docs/develop/theory/KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md). Public repository supplier, pin `8ab8a2d8e588b3c12d11bf8e845d63e6c95319f3`; Definition 91.1 and its source/operation/fee contract.
- **COHEN.** Samuel N. Cohen, [*Uncertainty and filtering of hidden Markov models in discrete time*](https://doi.org/10.1186/s41546-020-00046-x), *Probability, Uncertainty and Quantitative Risk* **5**, article 4 (2020), Theorem 1.
- **CK.** Taolue Chen and Stefan Kiefer, [*On the Total Variation Distance of Labelled Markov Chains*](https://arxiv.org/abs/1405.2852v1), arXiv:1405.2852v1 (2014), Theorem 7 and Corollary 8; [CSL–LICS published version](https://doi.org/10.1145/2603088.2603099). The theorem numbering here refers to the pinned arXiv version.
- **BOS.** Tomer Berg, Or Ordentlich and Ofer Shayevitz, [*Deterministic Finite-Memory Bias Estimation*](https://arxiv.org/abs/2206.09390v1), arXiv:2206.09390v1 (2022), §1 and Theorem 1.

[ST]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RANDOMIZED_STOPPED_TAIL_MINIMAX.md
[E1]: https://github.com/the-omega-institute/trureturing/blob/d54b775b50754d407dd4e39ea1d4c6c7d67d5021/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FULL_E1_SCOPE_EXTENSION.md
[PH]: https://github.com/the-omega-institute/trureturing/blob/6004bfffc63af86a0d9780a092da7c6c34c79e34/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PHASE_COHERENT_FULL_TAIL_MINIMAX.md
[NATIVE]: https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_MIXTURE_RECURRENCE_OBSTRUCTION.md
[FLOW]: https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FLOW_PRESERVING_RATIONAL_FRONTIER.md
[CLIP]: https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_RISK_CONTROLLED_EMISSION_MOMENT_FEASIBILITY.md
[PAID]: https://github.com/the-omega-institute/trureturing/blob/54dc9a9bd356fe584703022a3a4c0b0978f557de/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[PAID11]: https://github.com/the-omega-institute/trureturing/blob/f679023d5d0cad505cefbf096b498f6fdf935f88/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[GEOMETRY]: https://github.com/the-omega-institute/trureturing/blob/8ab8a2d8e588b3c12d11bf8e845d63e6c95319f3/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_II.md
[KB]: https://github.com/the-omega-institute/trureturing/blob/8ab8a2d8e588b3c12d11bf8e845d63e6c95319f3/docs/develop/theory/KBONACCI_FULL_POSITIVE_WINDOW_LOGARITHMIC_PRICE.md
[COHEN]: https://doi.org/10.1186/s41546-020-00046-x
[CK]: https://arxiv.org/abs/1405.2852v1
[BOS]: https://arxiv.org/abs/2206.09390v1

## 追加锚（本行以下为增补区）
