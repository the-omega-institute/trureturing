# Predictive thermodynamics of measurable visible protocols

## 1. States, instruments and retained histories

**Definition 1.1 (Finite visible protocol).** Let $A$ and $B$ be finite-dimensional complex Hilbert spaces, with $\dim B=e\ge2$, let $\beta>0$, let $H_A$ be Hermitian, and fix a positive trace-one matrix $\rho_A$. The initial joint state is $\rho_A\otimes\sigma_B$, where $\sigma_B$ ranges over every positive trace-one matrix on $B$, including singular matrices. The joint Hamiltonian is $H_A\otimes I_B$. A protocol has an arbitrary finite horizon $N$, measurable history spaces $F_0,\ldots,F_N$, an initial history $h_0\in F_0$, and the same visible controls for every $\sigma_B$.

For each executed stage $n<N$ and preceding history $h\in F_n$, its outcome carrier $O_{n,h}$ has its own measurable space and a countably additive completely positive instrument $\Phi_{n,h}$ on visible matrices. Empty events have zero operation. The total operation is trace preserving on executed active histories. Classical outcomes and histories need not be finite, countable or standard Borel.

The next history has a declared measurable total space $F_{n+1}$, a measurable preceding projection $p_n:F_{n+1}\to F_n$, and fibre embeddings $\iota_{n,h}:O_{n,h}\to F_{n+1}$ satisfying $p_n(\iota_{n,h}(o))=h$. Every measurable retained event $E\subseteq F_{n+1}$ pulls back to a legal measurable instrument event $\iota_{n,h}^{-1}E$. For every fixed $E$, every matrix entry of the operation $\Phi_{n,h}(\iota_{n,h}^{-1}E)$ on every visible matrix unit is measurable in $h$. These requirements concern the original retained measurable events; specifying measurable spaces on the fibres alone does not ensure measurable history transport.

The waiting time $t_n:F_n\to\mathbb R$ is measurable. Put $U_n(h)=\exp(-it_n(h)H_A)$ and $V_n(h)=\exp(-it_n(h)(H_A\otimes I_B))$. The local physical event action on an arbitrary joint matrix $X$ is

$$
\mathcal T_{n,h}(E)(X)
 =\bigl(\Phi_{n,h}(\iota_{n,h}^{-1}E)\otimes\operatorname{id}_B\bigr)
       \bigl(V_n(h)X V_n(h)^*\bigr).
$$

Here tensor amplification is the tensor product of the actual underlying matrix linear map with the identity. For any finite Kraus family representing the same event map, it equals the sum of conjugations by the corresponding $M_r\otimes I_B$ on every joint matrix. This correspondence does not require a measurable choice of Kraus representations, nor does a finite representing family constrain the classical outcome carrier.

A measurable stop set $S_n\subseteq F_n$ has measurable cemetery continuation $c_n:F_n\to F_{n+1}$ with $p_n(c_n(h))=h$. Stopping persists. The returned measurable record $r_n:F_n\to\mathbb N\times D$ has the same value after stopped continuation, and its first coordinate increases by one on active outcome transport. The stopped transition on event $E$ is $X\mapsto\mathbf1_E(c_n(h))X$. No stopped or failure mass is discarded, conditioned away or renormalized.

**Definition 1.2 (Physical history and estimation).** For each hidden state $\sigma$, the physical history at stage $n$ has probability law $\mu_n^\sigma$ and a measurable integrable matrix density $R_n^\sigma(h)$, positive with trace one everywhere. Its initial law is $\delta_{h_0}$ and $R_0^\sigma=\rho_A\otimes\sigma$ almost everywhere. Its actual transition equation, entry by entry on every measurable next-history event, is

$$
\int_E R_{n+1}^\sigma(k)\,d\mu_{n+1}^\sigma(k)
 =\int_{F_n}\mathcal T_{n,h}(E)(R_n^\sigma(h))\,d\mu_n^\sigma(h),
$$

with the stopped action on $S_n$. Total trace preservation is required almost everywhere on executed active histories separately under each $\mu_n^\sigma$. Neither record independence nor product posterior equality is an assumption. The protocol only imposes these equations for $n<N$.

An estimator is an arbitrary Markov kernel $\kappa$ from the returned record to $\mathbb R$, fixed before the unknown hidden state is chosen. Its output law is $Q^\sigma=((r_N)_*\mu_N^\sigma)\kappa$. For $\theta(\sigma)=\beta^{-1}D(\sigma\Vert I_B/e)$, its risk is the extended nonnegative expectation $\int |z-\theta(\sigma)|\,dQ^\sigma(z)$, with value $+\infty$ permitted. Outputs are not clipped or bounded.

## 2. Complete visible-record law and absolute minimax

**Theorem 2.1 (Measurable visible-protocol thermodynamic sufficiency).** For every finite visible protocol and actual physical history family of Definitions 1.1–1.2, all terminal physical history laws $\mu_N^\sigma$ coincide, and their exact returned-record laws coincide for every hidden density $\sigma$. For every executed stage and measurable returned-record event $C$, stopped-record mass is preserved exactly:

$$
\mu_{n+1}^\sigma\bigl(p_n^{-1}S_n\cap r_{n+1}^{-1}C\bigr)
 =\mu_n^\sigma\bigl(S_n\cap r_n^{-1}C\bigr).
$$

The hidden target satisfies

$$
D(\sigma\Vert I_B/e)=\log e-S(\sigma),\qquad
0\le\theta(\sigma)\le L:=\frac{\log e}{\beta}.
$$

For every such protocol $\mathcal E$, optimizing over every real randomized estimator gives

$$
\inf_\kappa\sup_\sigma
 \int |z-\theta(\sigma)|\,dQ_{\mathcal E,\kappa}^\sigma(z)
 =\frac{\log e}{2\beta}.
$$

The class of legal experiments with the fixed visible preparation and Hamiltonian is nonempty: it contains the zero-step product-preparation experiment. Consequently the additional optimization over all legal experiments has the same value,

$$
\inf_{\mathcal E}\inf_\kappa\sup_\sigma
 \int |z-\theta(\sigma)|\,dQ_{\mathcal E,\kappa}^\sigma(z)
 =\frac{\log e}{2\beta},
$$

and the midpoint estimator attains it. This conclusion applies to arbitrary finite adaptive depth, dependent measurable and uncountable classical outcomes, history-measurable real waits, measurable stopping, singular hidden states and infinite-risk estimators.

Proof. Since the hidden Hamiltonian is zero, the matrix exponential gives $V_n(h)=U_n(h)\otimes I_B$. Tensor amplification acts on a product input by

$$
\mathcal T_{n,h}(E)(X\otimes\sigma)
 =\Phi_{n,h}(\iota_{n,h}^{-1}E)(U_n(h)XU_n(h)^*)\otimes\sigma.
$$

To verify the physical interpretation, apply the representing Kraus identity first to elementary tensors and then expand an arbitrary joint matrix in tensor products of matrix units. Linearity proves equality with the local Kraus sum on all joint inputs; no product-input restriction is needed for this correspondence.

Construct the visible history recursively. Given a finite visible history measure $\mu$ and measurable positive trace-one visible density $\rho(h)$, write $A_h(E)=\Phi_h(\iota_h^{-1}E)(U_h\rho(h)U_h^*)$. For each fixed vector $v$, the quadratic form $q_v(h,E)=\operatorname{Re}(v^*A_h(E)v)$ is a positive finite scalar event measure. Complete positivity and event trace nonincrease imply the uniform bound $q_v(h,E)\le\sum_i|v_i|^2$. Coordinate measurability implies measurable evaluation on every fixed retained event. Thus these actual scalar measures form finite kernels $K_v$ on the total next-history space. The sum $P=\sum_iK_{e_i}$ is a Markov kernel; individual $K_v$ need not be Markov.

Bind $\mu$ with each $K_v$ to obtain finite event measures $\nu_v$. Polarization reconstructs the complex matrix event measure $M$: its $(i,j)$ real coordinate is $(\nu_{e_i+e_j}-\nu_{e_i-e_j})/4$, and its imaginary coordinate is $(\nu_{e_i-ie_j}-\nu_{e_i+ie_j})/4$. These are signed-measure differences. Section integration on each measurable event identifies every arbitrary-vector quadratic form with $\nu_v(E)$, so $M(E)$ is positive. Its trace is the scalar next-history probability law $\mu P$. Finite-dimensional positive matrix-measure density gives an integrable measurable positive trace-one posterior under that law, chosen to be a state on null histories as well. This uses ordinary measure Radon–Nikodym density and competing-density uniqueness, without a parameterized jointly measurable derivative or standard-Borel hypothesis.

The measurable predecessor relation ensures preservation of the scalar preceding marginal. On $p^{-1}B$, every fibre pullback is either the full outcome event or the empty event according as $h\in B$. Total trace preservation therefore gives $P(h,p^{-1}B)=\mathbf1_B(h)$ and $(\mu P)(p^{-1}B)=\mu(B)$. The matrix marginal is the channel's output and is not asserted to equal the preceding matrix marginal. Cemetery continuation is included as an identity event action. If normalization only holds almost everywhere on executed histories, complete the visible instrument by the identity cemetery action outside its measurable normalization domain. For each hidden state this changes no physical event integral, using that state's own normalization null set.

Now induct on the executed depth, starting with the Dirac/product initial history. Suppose the actual physical law equals the constructed visible law and its posterior is the visible density tensored with $\sigma$ almost everywhere. The product action identity equates the next actual joint event integral with the constructed visible event integral tensored with $\sigma$. Taking its trace, using $\operatorname{tr}\sigma=1$ and trace-one physical densities, proves equality of the next physical scalar measure with the constructed visible law on every measurable event. Only after identifying this actual measure does competing-density uniqueness imply equality of the next physical posterior with the visible density tensored with $\sigma$, almost everywhere under that measure. The induction works separately for each hidden state and needs no common null set across states or events. It yields common full history laws at every executed depth, hence common terminal record pushforwards.

On a stopped preceding history the event action is $\mathbf1_E(c_n(h))X$. The predecessor, stop-persistence and unchanged-record identities therefore give the displayed exact stopped-record mass equality. Active history transport retains its length increment. Neither waiting nor stopping introduces a hidden measurement or removes probability mass.

The zero-Hamiltonian Gibbs reference is $I_B/e$. Its logarithm is $-(\log e)I_B$, so relative entropy equals $\log e-S(\sigma)$, including singular $\sigma$ because the reference is full rank. The entropy bounds give the target interval $[0,L]$. The uniform hidden state has target zero; a pure hidden state has target $L$.

For any real randomized estimator, both endpoint states induce the same output law $Q$. The pointwise triangle inequality gives $|z|+|z-L|\ge L$. Its nonnegative integral gives $R_0+R_L\ge L$, also when either risk is infinite. Thus the worst risk is at least $L/2$. The constant estimator $z=L/2$ has loss at most $L/2$ for every target in $[0,L]$, and the endpoints attain that bound. This proves the per-protocol equality without imposing integrability on arbitrary estimators.

Finally the zero-step experiment uses a singleton initial history, product density $\rho_A\otimes\sigma$, Dirac law and constant length-zero record; all executed-stage requirements are vacuous. It belongs to the same legal class for the given preparation and Hamiltonian. Every class member has the proved inner minimax value $L/2$, so the outer infimum over this nonempty class also equals $L/2$. The zero-step experiment and midpoint estimator attain it.

## Appendix A. Scope of the visible observation restriction

The preceding law and minimax deduction concern the original finite visible-experiment model with Hamiltonian $H_A\otimes I_B$ and target relative entropy against $I_B/e$. The assertion is a synthesis of the operational measure construction and entropy endpoint argument. The matrix tensor action, scalar measure density and entropy identities are the standard intermediate identities used in its proof. No algorithmic runtime or hidden partition-function counting assertion is part of Theorem 2.1.

## 追加锚（本行以下为增补区）
