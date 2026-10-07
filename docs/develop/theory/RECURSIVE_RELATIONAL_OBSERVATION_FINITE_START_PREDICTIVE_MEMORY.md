# Recursive relational observation: finite-start predictive memory

## 1. Source, acquired histories and decoder contracts

**Assumption 1.1 (the fixed five-mode source).** The source is exactly the additional stochastic model of [Auric, §§122–123, revision ad512afaf86ab2258ef58a78089f247e190866f4](https://github.com/the-omega-institute/trureturing/blob/ad512afaf86ab2258ef58a78089f247e190866f4/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md). Its states are

$$
s_0=000,\quad s_1=100,\quad s_2=101,\quad
s_3=001,\quad s_4=010,
$$

corresponding respectively to $\mathrm{null},[2],[25],[5],[3]$. Write a state by its index. Assume

$$
p,q,r>0,\qquad p+q+r<1,\qquad
P=\begin{pmatrix}
1-p-q-r&p&0&q&r\\
q&1-p-q&p&0&0\\
0&q&1-p-q&p&0\\
p&0&q&1-p-q&0\\
r&0&0&0&1-r
\end{pmatrix},\qquad
\pi=\frac15(1,1,1,1,1).
$$

Rows are departure states. The chain $(X_t)_{t\ge0}$ starts with $X_0\sim\pi$. The only read is

$$
\chi(0)=0,\quad\chi(1)=1,\quad\chi(3)=3,\quad
\chi(2)=\chi(4)=B,\qquad Y_t=\chi(X_t).
$$

The observation map is $\chi$; $q$ always denotes the scalar transition parameter. Successive symbols are actually acquired in order. The observer has no hidden-state read, discarded-history access, source copy, reset, chosen experiment, additional control or external recording-age input. Its retained word changes using only its previous retained word and the newly acquired symbol. The Markov law is an explicit additional contract, not a consequence of the tree substitution $\rho$ or of the two leaf symbols.

Put $s=p+q$, $a=1-s$, $b=1-r$ and $c=1-s-r$. Thus $0<a,b<1$ and $c>0$. All parameter equalities compatible with the displayed strict inequalities remain in the domain. In particular neither $p\ne q$ nor $r\ne s$ is a standing assumption.

**Definition 1.2 (future laws at the recording boundary).** Let $\mathcal A=\{0,1,3,B\}$, and let $\mathcal H_n$ be the visible words of length $n$ having strictly positive probability under Assumption 1.1. Set

$$
\mathcal H=\{\varnothing\}\cup\bigcup_{n\ge1}\mathcal H_n.
$$

The empty word is a queryable initialized boundary. For $h\in\mathcal H_n$, $n\ge1$, let $F_h^H$ be the joint conditional law of $(Y_n,\ldots,Y_{n+H-1})$ given $h$, for every integer $H\ge1$. At $\varnothing$ the predicted word begins with $Y_0$. A law profile is a family of normalized finite-word laws consistent under deletion of final symbols. On profiles define

$$
d(F,G)=\sup_{H\ge1}\operatorname{TV}(F^H,G^H),\qquad
\operatorname{TV}(\nu,\nu')=\frac12\sum_{w\in\mathcal A^H}|\nu(w)-\nu'(w)|.
$$

For a current hidden distribution $\mu$, write $D_y=\operatorname{diag}(\mathbf1_{\chi(i)=y})$ and

$$
F_\mu^H(y_1\cdots y_H)
=\mu P D_{y_1}P D_{y_2}\cdots P D_{y_H}\mathbf1.
$$

Write $F_i=F_{e_i}$ and $M_x=xF_2+(1-x)F_4$, $0\le x\le1$. At initialization use

$$
F_*^H(y_1\cdots y_H)
=\pi D_{y_1}P D_{y_2}\cdots P D_{y_H}\mathbf1.
$$

The already established double stochasticity in Auric Theorem 122.3 gives $\pi P=\pi$, so $F_*=F_\pi$. This identity changes no acquisition convention: its first requested read is still $Y_0$.

These finite products use the standard HMM path-summation and posterior-mixture construction. The normalization operation is also represented by Mathlib's `PMF.bind` and `bind_apply`, in `Probability.ProbabilityMassFunction.Monad` at revision db584cd6d46c92f209a44c0f1c829460d327499d. For the changing hidden state here, Bayes conditioning uses the joint weight $(\mu P)_j\mathbf1_{\chi(j)=y}$; a likelihood update on $\mu$ without the transition would describe a different source.

**Definition 1.3 (three memory problems).** Exact behavioral equivalence is $h\sim h'$ if $F_h^H=F_{h'}^H$ for every $H\ge1$. A static closed-word encoding is a map $E:\mathcal H\to Z$, with a common decoder assigning a law profile $D(z)$ to each retained word $z\in Z$, satisfying

$$
\sup_{h\in\mathcal H}d(F_h,D(E(h)))\le\epsilon.
$$

Only the retained word and fixed model data are decoder inputs. No recording length, current-symbol side register or old archive is supplied again. The encoding itself is not assumed to admit a finite online update.

A deterministic autonomous observer additionally has a finite configuration set $Z$, an initial configuration $z_*$, and a total map $U:Z\times\mathcal A\to Z$. Its state is defined by

$$
z(\varnothing)=z_*,\qquad z(hy)=U(z(h),y).
$$

The guarantee is required for every $h\in\mathcal H$, jointly with this one update. Post-read configurations are those reached on at least one nonempty actual history; the initialized observer size is $|Z|$, including $z_*$. In the common-law-decoder problem, configurations never reached by actual histories can be deleted, with transitions on impossible actual extensions retargeted arbitrarily. A variant that permits queries only after a read is explicitly distinguished below. All minima concern deterministic retention and pointwise error on every actual positive-probability history. They do not refer to an error averaged over randomized retained states.

The stronger self-generated-law problem imposes, in addition, a probability row $g_z$ on $\mathcal A$ at every configuration. Its decoder is required to be

$$
D_z^H(y_1\cdots y_H)
=\prod_{j=1}^H g_{z_{j-1}}(y_j),\qquad
z_0=z,\quad z_j=U(z_{j-1},y_j).
$$

In the common-law-decoder problem, $D_z$ may instead be any one coherent law profile. Its conditional law after a symbol need not equal $D_{U(z,y)}$. Coherence across horizons and consistency with the observer's own symbol updates are distinct conditions. The self-generated size counts all configurations used by its law, including any reached only on hypothetical generated words; such configurations cannot in general be deleted merely because actual histories do not reach them. In both problems the actual input comes from $P,\chi$, including symbols to which an approximate predictor assigns zero probability.

The behavioral-quotient and realized-image factorization background is reused from [Transport Memory Completion, §27](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), and from the repository's `ObserverMemory.PredictionFactors.CausalStateFactorization` declarations at revision ad512afaf86ab2258ef58a78089f247e190866f4. Its history type here is $\mathcal H$ and its response is the entire profile, rather than one target entropy. Those general results do not assert that the realized image is finite.

## 2. Exact acquired-history classification

**Theorem 2.1 (the complete reachable predictive family).** For every nonempty actual history, its current posterior is either one of the five point masses $e_i$, or

$$
\mu_k=x_ke_2+(1-x_k)e_4,\qquad
x_k=\frac{a^k}{a^k+b^k},\quad k\ge0.
$$

The latter occurs precisely on the initial history $B^{k+1}$, of probability $(a^k+b^k)/5>0$. All five point masses occur. Every distinct posterior in this list has a distinct complete future profile. The empty profile is an additional distinct class. Consequently the exact quotient has six post-read classes and seven initialized classes when $r=p+q$, and countably infinitely many in both conventions otherwise. This conclusion includes $p=q$.

**Proof (2.1).** A singleton symbol $j\in\{0,1,3\}$ identifies $X_t=j$. From a known state, a subsequent $B$ identifies the next state by

$$
0\mapsto4,\qquad1\mapsto2,\qquad3\mapsto2,
\qquad2\mapsto2,\qquad4\mapsto4.
$$

Another singleton again identifies its state. Induction therefore keeps the current posterior pure after the first singleton. The histories $0,1,3,1B,0B$ exhibit all five pure cases. Their probabilities are respectively $1/5,1/5,1/5,p/5,r/5$.

Without a singleton the history is $B^{k+1}$. The only compatible hidden paths stay at $2$ or stay at $4$: there is no transition between these states within $\chi^{-1}(B)$. Their masses are $a^k/5$ and $b^k/5$. Positive conditioning gives the stated posterior. This covers every actual history, without adding hypothetical beliefs to the domain. Markov conditioning and the products of Definition 1.2 give $F_h=F_{\mu(h)}$ at all horizons.

In visible order $(0,1,3,B)$ the one-step rows are

$$
\begin{aligned}
v_0&=(c,p,q,r),&v_1&=(q,a,0,p),\\
v_2&=(0,q,p,a),&v_3&=(p,0,a,q),\\
v_4&=(r,0,0,b),&v_x&=((1-x)r,xq,xp,xa+(1-x)b).
\end{aligned}
$$

The rows $v_x$ are injective in $x$ because $r>0$. Equality with $v_1$ would force $x=0$ through its $3$ coordinate and then contradict its positive $1$ coordinate. Equality with $v_3$ is excluded symmetrically. Equality with $v_0$ would require $xq=p$ and $xp=q$, hence $p=q$ and $x=1$; its $0$ coordinate would then be zero rather than $c>0$. The three singleton rows are pairwise different by their positive and zero singleton coordinates. This separates the whole displayed family, including its endpoints, already at horizon one.

Here is also a quantitative separation of the empty law, to be used again below. For $D=\operatorname{TV}(F_*^1,M_x^1)$, the two events $\{1,3\}$ and $\{0\}$ give

$$
D\ge|2/5-xs|,\qquad D\ge|1/5-(1-x)r|.
$$

Multiplying the first difference by $r$ and the second by $s$, and applying the triangle inequality, yields

$$
D\ge\frac{(2/5)r+(1/5)s-sr}{s+r}.
$$

Put $z=s/(s+r)$. Since $s+r<1$, the right side is strictly greater than or equal to

$$
\frac25-\frac z5-z(1-z)
=\left(z-\frac35\right)^2+\frac1{25}.
$$

Thus $d(F_*,M_x)\ge1/25$ for every $x$.

For a pure start $i$, the first future symbol $B$ can enter only one of $2,4$. Consider two finite-horizon events: the first symbol is $B$ and the first subsequent non-$B$ is respectively $0$ or in $\{1,3\}$. Under $F_*$ their probabilities tend respectively to $1/5$ and $1/5$, by stationarity and the equal initial masses of $2,4$. Under $F_i$ one of these categories is impossible. Hence $d(F_*,F_i)\ge1/5$. This uses finite events and their limits, not conditioning on an infinite all-$B$ history.

Finally $x_k/(1-x_k)=(a/b)^k$. If $a=b$, every $x_k=1/2$; otherwise this sequence is injective and never reaches an endpoint. The reused factorization principle requires distinct exact retained words for distinct profiles. Conversely these profiles themselves provide a sufficient encoding. This establishes the counts. $\square$

**Theorem 2.2 (exact internal updating and the two start conventions).** The exact quotient of Theorem 2.1 admits a legal autonomous update. At $a=b$ the minimum initialized exact observer has seven configurations when the empty boundary is queryable; if queries occur only after reads, a complete six-configuration observer exists. At $a\ne b$ there is no finite exact observer or uniformly bounded exact retained-word alphabet. For a recording-length cap $L\ge2$, the unequal case has $L+5$ exact post-read classes, or $L+6$ with empty history. At a single externally specified length $L\ge2$ there are only six post-read classes.

**Proof (2.2).** Use labels $I$, $R_0,\ldots,R_4$ and $A_k$ for $k\ge0$. Decode them by $F_*,F_i,F_{\mu_k}$. Every singleton input $j$ sends every label to $R_j$. On $B$ use

$$
I\mapsto A_0,\quad A_k\mapsto A_{k+1},\quad
R_0\mapsto R_4,\quad R_1,R_3\mapsto R_2,
\quad R_2\mapsto R_2,\quad R_4\mapsto R_4.
$$

These rules are total and use only the retained label and the new read. The invariant proved in Theorem 2.1 verifies them on every actual prefix. At $a=b$ replace all $A_k$ by one label $A$ with a $B$ self-loop. Keeping $I$ gives seven exact configurations. If no empty query is made, initialize directly in $A$: the first $B$ stays at the required half-mixture and a first singleton resets correctly. The six distinct post-read laws establish minimality there; the distinct empty law establishes seven when it is queried.

At $a\ne b$, the infinite distinct orbit forces infinitely many words by any common exact decoder. Each individual $k$ is finite and can be retained as a tagged integer, but its worst-case size is unbounded. For lengths at most $L$, exactly $k=0,\ldots,L-1$ occur and all pure states have appeared by length two. Adding the empty class gives the stated cap counts. At fixed length $L$ only $\mu_{L-1}$ is mixed; all five pure states occur by padding the exhibited histories with positive self-loops. A six-entry decoder depending on that externally supplied $L$ does not give one internal decoder across all lengths.

Update compatibility is also the familiar positive-conditioning principle of the repository's `ObserverMemory.ContextUpdates.PredictiveStateUnifilarUpdate` declarations at revision ad512afaf86ab2258ef58a78089f247e190866f4: equality of complete laws gives equal next-symbol masses, and division of equal extended-word probabilities on any positive symbol gives equal successor laws. The concrete update above additionally computes the actual reachable classes and their start costs. $\square$

## 3. The all-future metric and a positive separation bound

**Theorem 3.1 (exact geometry of the ambiguous branch).** For all $x,z\in[0,1]$ and $H\ge1$,

$$
\operatorname{TV}(M_x^H,M_z^H)
=|x-z|\bigl(1-\min(a,b)^H\bigr),\qquad
d(M_x,M_z)=|x-z|.
$$

**Proof (3.1).** Before its first non-$B$ symbol, a future from $2$ stays at $2$ and a future from $4$ stays at $4$. Their first exits are in disjoint visible categories: $\{1,3\}$ versus $\{0\}$. Thus the supports of $F_2^H$ and $F_4^H$ overlap only at $B^H$, whose masses are $a^H,b^H$. The finite-law overlap identity gives

$$
\operatorname{TV}(F_2^H,F_4^H)=1-\min(a^H,b^H).
$$

The signed difference of mixtures is $(x-z)(F_2^H-F_4^H)$; homogeneity of the half-$\ell^1$ norm gives the first formula. Since $a,b<1$, its factor tends to one, proving the supremum formula. Every calculation concerns a finite joint word. No observer receives the eventual exit as a present input.

The usual channel-contraction upper bound is an attributed intermediate from the repository's `TotalVariation.DataProcessing` declarations at revision ad512afaf86ab2258ef58a78089f247e190866f4; each horizon supplies a finite stochastic channel from current states to words. The disjoint exit categories give the sharper equality for this source. $\square$

**Definition 3.2 (a sufficient small-error range).** Define the explicit model-dependent number

$$
\kappa=\min\left\{
c,p,q,a,\frac{cs}{s+r},\frac{ap}{s},\frac{aq}{s},\frac1{25}
\right\}>0.
$$

The small-error range used for exact minima is $0<2\epsilon<\kappa$. It is a sufficient separation range; no assertion about the exact crossover at larger errors is included in this definition.

**Theorem 3.3 (separation without generic-parameter exclusions).** Distinct pure laws have $d$-distance at least $\kappa$. Every $F_j$ with $j\in\{0,1,3\}$ has $d$-distance at least $\kappa$ from every $M_x$, $0\le x\le1$. The empty law has distance at least $1/25$ from every $M_x$, and at least $1/5$ from each pure law. These bounds hold also at $p=q$ and $r=s$.

**Proof (3.3).** All pure pairs other than $2,4$ have a one-step singleton-coordinate difference at least $\min(c,p,q,a)$, as the rows in Theorem 2.1 show. The pair $2,4$ has $d$-distance one by Theorem 3.1. For $D=\operatorname{TV}(v_0,v_x)$, the events $\{1,3\}$ and $\{0\}$ imply

$$
D\ge s(1-x),\qquad D\ge|c-r(1-x)|.
$$

Therefore $c\le D+rD/s$ and $D\ge cs/(s+r)$. For comparison with $v_1$ the events $\{3\}$ and $\{1\}$ give $D\ge xp$ and $D\ge|a-xq|$, whence $a\le D+qD/p$ and $D\ge ap/s$. The comparison with $v_3$ similarly gives $aq/s$. The empty bounds were proved in Theorem 2.1. These estimates use only the declared positivity. The event bounds and triangle inequality use the finite half-$\ell^1$ convention of the repository's `TotalVariation.Metric` declarations at revision ad512afaf86ab2258ef58a78089f247e190866f4. $\square$

## 4. Sharp autonomous count for a common complete-law decoder

**Definition 4.1 (minority mass and the two cutoffs).** In this section assume $a\ne b$. Let $d$ be the state in $\{2,4\}$ with larger holding probability and $f$ the other state. Put

$$
u=\min(a,b),\quad v=\max(a,b),\quad
\theta=u/v\in(0,1),\quad \lambda=|\log\theta|,
\quad\delta_k=\frac{\theta^k}{1+\theta^k}.
$$

Thus $d=2,f=4$ if $a>b$, and $d=4,f=2$ if $b>a$. Define $G_z=(1-z)F_d+zF_f$. The initial history $B^{k+1}$ has law $G_{\delta_k}$, and

$$
d(G_z,G_{z'})=|z-z'|.
$$

For $0<\epsilon<1/4$ set

$$
N_2=\min\{m\ge0:\delta_m\le2\epsilon\},\qquad
N_1=\min\{m\ge0:\delta_m\le\epsilon\}.
$$

Both are finite positive integers. For $j=1,2$ their exact expressions are

$$
N_j=\left\lceil
\frac{\log((1-j\epsilon)/(j\epsilon))}{\lambda}
\right\rceil.
$$

The defining non-strict inequalities include cutoff ties; in particular $\delta_{N_j}=j\epsilon$ is permitted. They count indices beginning at zero, while an acquired startup word has length $k+1$.

**Theorem 4.2 (matching initialized lower and upper bounds).** Under $a\ne b$ and $0<2\epsilon<\kappa$, the minimum number of configurations of a deterministic autonomous observer with a common complete-law decoder is exactly

$$
\boxed{6+N_2}.
$$

The minimum number reached after at least one read is $5+N_2$. One update and one decoder attain the bound for every actual finite positive-probability history, uniformly over all future horizons, including the query at empty history.

**Proof (4.2).** For the upper bound retain

$$
I,\quad R_0,\ldots,R_4,\quad A_0,\ldots,A_{N_2-1}.
$$

Set $\beta=\delta_{N_2}/2$. Decode $I$ by $F_*$, $A_k$ by $G_{\delta_k}$, $R_d$ by $G_\beta$, and every other $R_i$ by $F_i$. Every one is a single coherent law profile. Use singleton reset $U(z,j)=R_j$ from every state, and the pure-label $B$ transitions of Theorem 2.2. On startup use

$$
I\mapsto A_0,\qquad
A_k\mapsto A_{k+1}\ (k<N_2-1),\qquad
A_{N_2-1}\mapsto R_d
$$

for input $B$.

Inductively an initial $B^{k+1}$ occupies $A_k$ if $k<N_2$, and $R_d$ otherwise. A history containing a singleton occupies the label for its exactly inferred current hidden state. These two cases exhaust the actual domain and are preserved by every next acquired symbol. On the saturated startup tail, $0<\delta_k\le\delta_{N_2}$, so

$$
d(G_{\delta_k},G_\beta)
=|\delta_k-\beta|\le\delta_{N_2}/2\le\epsilon.
$$

A synchronized dominant state has the same error $\beta\le\epsilon$; all remaining histories and the empty query are exact. Theorem 3.1 supplies the all-horizon guarantee directly. A rare actual exit is a singleton and resets correctly, regardless of its forecast probability. All listed labels are actually reached: each transient by its own initial run, all pure labels by the histories of Theorem 2.1, and $I$ at initialization. This gives $6+N_2$ total and $5+N_2$ post-read.

For the lower bound, consider any competing observer, and write $z_k=z(B^{k+1})$. If $z_i=z_j$ for $i<j$, deterministic iteration of the same $B$ update gives

$$
z_{i+\ell(j-i)}=z_i\qquad(\ell\ge0).
$$

Every corresponding finite history has positive probability. Their true profiles converge to $F_d$ in $d$, since $\delta_{i+\ell(j-i)}\to0$. The common decoder at $z_i$ lies within $\epsilon$ of all these profiles, and therefore within $\epsilon$ of $F_d$. Its distance from $G_{\delta_i}$ is also at most $\epsilon$. The triangle inequality forces

$$
\delta_i\le2\epsilon.
$$

Consequently $z_0,\ldots,z_{N_2-1}$ are distinct and none recurs later on the startup orbit. Each is farther than $2\epsilon$ from $F_d$, farther than $2\epsilon$ from $F_f$ because $1-\delta_i\ge1/2$, and separated from the three singleton laws by Theorem 3.3. It is also separated from $F_*$ by that theorem. Thus these $N_2$ states share with none of the five synchronized laws or the empty law. Those six laws themselves require mutually different states by Theorem 3.3. This forces $N_2+6$ initialized configurations, and $N_2+5$ reached after reads.

The repeated-state argument invokes the standard iteration identity for a deterministic map; the new obstruction is its combination with this source's positive startup histories and exact distance $\delta_i$ to the limiting law. The limit is used to constrain decoders on finite histories. No query or actual observation is made on the probability-zero event of an infinite all-$B$ run. $\square$

**Theorem 4.3 (initialization and the equality stratum).** In the small-error range $0<2\epsilon<\kappa$, the unequal case still requires $6+N_2$ total configurations if queries are permitted only after reads. At $a=b$, the initialized minimum with a queryable empty boundary is exactly seven, both exactly and at this tolerance. With queries only after reads, the complete minimum at $a=b$ is six.

**Proof (4.3).** The unequal post-read lower bound in Theorem 4.2 does not use an empty query. Its initial state cannot coincide with a state reached on a synchronized history: appending $B$ in the two contexts would identify the first-read half-mixture with one of the two pure $B$ laws. Both extensions are actual positive histories and have $d$-distance $1/2>2\epsilon$. Nor can initialization coincide with any $z_k$: that would place $z_0$ on a recurring $B$ orbit, and the same limiting argument would force $\delta_0=1/2\le2\epsilon$. Hence initialization is an additional configuration even without a decoder query there. The construction already has it.

At equality there are only $F_2,M_{1/2},F_4$ on the $B$ fiber. Their pairwise distances are at least $1/2$; Theorem 3.3 separates the singleton and empty classes. Seven distinct queryable laws therefore remain necessary at this tolerance, and the exact seven-state machine attains them. Without the empty query, initialize in the half-mixture as in Theorem 2.2; the six separated post-read laws prove minimality. No limit of the unequal cutoff formula is substituted for this separate equality case. $\square$

## 5. A stronger decoder and its explicitly open optimum

**Theorem 5.1 (self-generated complete laws).** Under $a\ne b$ and $0<2\epsilon<\kappa$, let $N_{\mathrm{gen}}(\epsilon)$ be the initialized minimum for the self-generated-law contract of Definition 1.3. Then

$$
\boxed{6+N_2\ \le\ N_{\mathrm{gen}}(\epsilon)\ \le\ 6+N_1}.
$$

The upper bound has a total update valid on every actual history and a simultaneous all-horizon error bound. At $a=b$ the exact seven-state initialized machine is also self-generated, and seven remains its small-error minimum. If $N_1=N_2$, the bounds coincide and determine the optimum. When the bounds differ, the general exact unequal optimum is open here.

**Proof (5.1).** A self-generated decoder is a special case of a common coherent decoder, so Theorem 4.2 supplies the lower bound. For the upper bound use $I$, the five pure labels and $A_0,\ldots,A_{N_1-1}$, with the same updates except that the cutoff is $N_1$. At $R_i$ emit the true row $v_i$; at $A_k$ emit the true one-step row of $G_{\delta_k}$; at $I$ emit $(1/5,1/5,1/5,2/5)$. Decode by iterating these rows and this very update. The true pure-state visible generator is unifilar under the read: the observed symbol selects the unique next hidden state. Hence its future law is exactly $F_i$ at every pure label.

Consider a current transient $A_k$, $k<N_1$, and put $m=N_1-k$. Until either a singleton occurs or $m$ further $B$ symbols have been read, the finite generator and the true conditional law agree. An earlier singleton resets to a pure state and leaves all further laws identical. The exceptional prefix $B^m$ has the same probability in both laws, namely

$$
S_k=\frac{a^{N_1}+b^{N_1}}{a^k+b^k}.
$$

Conditional on this prefix, the true posterior has law $G_{\delta_{N_1}}$, whereas the generator has replaced it by $F_d$. Thus the error at horizon $H$ is zero if $H\le m$, and if $H>m$ is exactly

$$
S_k\delta_{N_1}\bigl(1-u^{H-m}\bigr).
$$

Only words with that common prefix contribute to the signed difference. Its all-horizon supremum is

$$
S_k\delta_{N_1}
=\frac{u^{N_1}}{a^k+b^k}
\le\frac{u^{N_1}}{a^{N_1}+b^{N_1}}
=\delta_{N_1}\le\epsilon.
$$

After an actually saturated history $B^{k+1}$ with $k\ge N_1$, the generator's law is $F_d$ and the true error is $\delta_k\le\epsilon$. After any singleton-containing actual history its pure label is exact. At $I$ the singleton branches are exact and the first $B$ branch has probability $2/5$ followed by $A_0$; its all-future error is $u^{N_1}/5\le\epsilon$. These cases prove the uniform bound and the online invariant together.

The total singleton overwrite is essential. A saturated pure row may assign zero probability to an exit from the actual minority component. That input is nevertheless legal under the source and must reset the retained state. No division by its approximate zero likelihood is used. The generated law remains well defined on hypothetical words, while the actual-input update remains defined on the larger actual support.

At equality the unsaturated half-mixture has the correct $B$ self-loop and its true one-step row, so the exact construction is self-generated. Theorem 4.3 gives its minimum. Coincident bounds determine the minimum directly. Otherwise this proof supplies no argument that every generator must use the later cutoff $N_1$. $\square$

**Theorem 5.2 (why the midpoint construction does not identify the two contracts).** The attaining common decoder of Theorem 4.2 does not satisfy the self-generated-law condition at its saturated state.

**Proof (5.2).** Its decoded law there is $G_\beta$ with $0<\beta=\delta_{N_2}/2<1$. Conditioning this law on a next $B$ changes its fast-component mass to

$$
\beta'=\frac{\beta u}{(1-\beta)v+\beta u}
=\frac{\beta\theta}{1-\beta+\beta\theta}<\beta.
$$

The state update on $B$ stays at $R_d$ and therefore still decodes $G_\beta$. Theorem 3.1 separates these two residual profiles. A self-generated profile would instead have its conditional tail equal to the decoder at that successor. Thus common-law optimality alone does not settle the stronger optimum. This distinction does not affect the actual-history guarantee already proved for the midpoint observer. $\square$

## 6. Closed-word covers, online closure and parameter nonuniformity

**Definition 6.1 (the reachable scalar cover).** For $a\ne b$, put

$$
T_\theta=\{0\}\cup\{\delta_k:k\ge0\},\qquad
S_\theta=T_\theta\cup\{1\}.
$$

For a bounded scalar set $T$, let $C(T,2\epsilon)$ be the smallest number of closed intervals of length at most $2\epsilon$ covering $T$. Endpoints zero and one represent the dominant and minority pure laws; zero is not claimed to occur as an unresolved finite posterior.

**Theorem 6.2 (the exact static count and its scope).** Under $a\ne b$ and $0<2\epsilon<\kappa$, the exact static closed-word minimum is

$$
4+C(T_\theta,2\epsilon)\quad\text{after reads},\qquad
5+C(T_\theta,2\epsilon)\quad\text{including empty history}.
$$

Equivalently these counts are $3+C(S_\theta,2\epsilon)$ and $4+C(S_\theta,2\epsilon)$. In particular the initialized count is at most $5+\lceil1/(4\epsilon)\rceil$, independent of the holding ratio. This is a one-shot encoding theorem and provides no autonomous update for those code words.

**Proof (6.2).** The laws $F_0,F_1,F_3,F_f$ need four separate post-read labels and cannot share with the laws indexed by $T_\theta$. The singleton separation is Theorem 3.3, and $F_f$ has distance $1-z\ge1/2$ from $G_z$ on $0\le z\le1/2$. The empty law needs a fifth separate label.

If a decoder label serves scalar values $A\subseteq T_\theta$, the triangle inequality and Theorem 3.1 imply $|x-z|\le2\epsilon$ for every $x,z\in A$. Thus $[\inf A,\sup A]$ is a closed interval of length at most $2\epsilon$. The nonempty fibers of any finite encoder give an interval cover, establishing necessity even for decoders outside the mixture family. Conversely take a cover, intersect its nonempty intervals with $[0,1/2]$, and decode each at its midpoint by $G_z$. Assign every scalar to one interval containing it. The exact metric gives error at most $\epsilon$. Decode the isolated laws exactly. This attains the count.

Since $2\epsilon<\kappa\le1/25$, the isolated value $1$ cannot share a covering interval with $T_\theta\subseteq[0,1/2]$. Hence $C(S_\theta,2\epsilon)=1+C(T_\theta,2\epsilon)$, proving the equivalent expressions. Covering the entire interval $[0,1/2]$ by $\lceil1/(4\epsilon)\rceil$ equal closed pieces proves the parameter-independent upper bound. No update congruence for this cover has been assumed or deduced. $\square$

**Theorem 6.3 (fixed-parameter rates and failure of a uniform online bound).** Fix an unequal allowed parameter triple. As $\epsilon\downarrow0$, the static initialized count, common-decoder autonomous minimum and self-generated-law minimum all satisfy

$$
N(\epsilon)=\frac{\log(1/\epsilon)}{|\log\theta|}+O_{p,q,r}(1).
$$

Nevertheless, for fixed sufficiently small positive $\epsilon$, the common-decoder autonomous minimum diverges as $r\to s$ through unequal allowed values with $p,q$ fixed and $s<1/2$. Its asymptotic there is

$$
6+N_2\ \sim\
\frac{1-s}{|r-s|}\log\frac{1-2\epsilon}{2\epsilon}.
$$

The static initialized count remains bounded by Theorem 6.2, while at equality an exact initialized observer has only seven configurations.

**Proof (6.3).** The cutoff formulas immediately give $N_1,N_2=\log(1/\epsilon)/\lambda+O_\theta(1)$. Theorem 5.1 transfers this to the stronger minimum. A static upper bound uses separate intervals for $\delta_0,\ldots,\delta_{N_2-1}$ and one tail interval $[0,\delta_{N_2}]$; thus $C(T_\theta,2\epsilon)\le N_2+1$.

For the lower bound,

$$
\delta_k-\delta_{k+1}
=\frac{(1-\theta)\theta^k}{(1+\theta^k)(1+\theta^{k+1})}
\ge\frac{(1-\theta)\theta^k}{4}.
$$

The number of initial consecutive gaps guaranteed to exceed $2\epsilon$ is $\log(1/\epsilon)/\lambda+O_\theta(1)$. Their ordered endpoints require separate intervals. This proves the matching static rate; all constants are fixed-parameter constants.

For the second claim, $a=1-s$ stays fixed and $b=1-r\to a$. The function $\kappa(p,q,r)$ is continuous and positive at $r=s$ when $s<1/2$. Choose a neighborhood and an $\epsilon$ with a strict $2\epsilon<\kappa$ margin throughout it. On either side,

$$
|\log\theta|\sim\frac{|r-s|}{1-s}.
$$

The exact cutoff expression gives the divergence and the displayed equivalent. For instance $p=q=1/8$, $r\to1/4$ satisfies these assumptions; at equality $\kappa=1/25$, so every fixed $0<\epsilon<1/50$ has such a neighborhood. The static cover bound contains no $\theta$. The equality machine is separately supplied by Theorem 4.3. The discontinuity concerns uniform treatment of arbitrarily long finite startup records, not a singularity of a physical clock or source dynamics. $\square$

## 7. Acquisition and reconstruction boundaries

**Theorem 7.1 (a fixed suffix and the arrow current are insufficient).** For any $L\ge1$, no predictor determined only by the last $L$ visible symbols can meet the uniform all-future requirement with $\epsilon<1/2$. The fixed-path arrow statistic $W$ of Auric §123.2, even paired with the current visible type, is also insufficient for exact future prediction. These obstructions include $p=q$ and $r=s$.

**Proof (7.1).** The histories $1B^L$ and $0B^L$ have probabilities $pa^{L-1}/5$ and $rb^{L-1}/5$. Their suffixes of length $L$ are the same, but their current posteriors are $e_2,e_4$. Their distance is one by Theorem 3.1, so a common suffix decoder has worst error at least $1/2$. Every finite such history is legal, even at very small probabilities.

For $W$, take the acquired histories $B1B$ and $B0B$. They have unique hidden paths $(2,1,2)$ and $(4,0,4)$, with probabilities $qp/5$ and $r^2/5$. Both have current type $B$ and $W=0$: the first has cancelling reverse/forward square steps and the second uses only the leaf branch. Their future laws are again $F_2,F_4$. Thus even when $W$ is known on these records it is not predictive.

Auric Theorem 123.2 is reused at exactly its fixed-model, fixed-path-length direction-discrimination scope,

$$
\log(\mathbb P_N(\gamma)/\mathbb Q_N(\gamma))=W(\gamma)\log(p/q).
$$

It does not make $W$ a supplied four-symbol register. Its range is unbounded: traversing the positive-probability forward square repeatedly gives arbitrarily large $W$. When $p=q$ the likelihood ratio is identically one; the preceding predictive witnesses still differ. The separate equality governing exact finite-start memory is $r=p+q$. $\square$

**Theorem 7.2 (what exact prediction reconstructs).** After at least one read, the exact finite-start predictive class determines the current visible type. On the unresolved startup stratum with $a\ne b$, it also determines the recording length. On that stratum it does not determine the actual hidden component before an exit. At $a=b$ it does not determine startup length. After synchronization it determines the current hidden state but does not determine the old archive or elapsed recording length. A finite saturated approximation does not yield uniformly bounded absolute error in reconstruction of recording age.

**Proof (7.2).** The separated normal forms of Theorem 2.1 identify whether the current class is a singleton or $B$, and which inferred pure state occurs. In a startup law, $x$ is recovered from its next-$0$ probability by $x=1-\Pr(0)/r$. For $a\ne b$,

$$
k=\frac{\log(x/(1-x))}{\log(a/b)},\qquad n=k+1.
$$

This inverts an exact law object or exact retained class, not a sampled future. Both hidden components have positive posterior mass for every finite startup run, so the past acquired word alone does not select its actual component. Their first eventual exit does select that component almost surely by the distinct exit alphabets. At equality $x=1/2$ for every startup length, excluding that age inverse.

The histories $0$ and $00$ are positive, have different lengths, and share the pure current state $0$ and all continuation laws. The equal-length histories $00$ and $10$ have probabilities $c/5,q/5$ and different archives but the same future profile. Hence no archive or general recording-age inverse exists on the predictive quotient. Each saturated tail state in the constructed approximation is reached on startup words with unbounded lengths. Any one finite real-valued age estimate at that state has unbounded absolute error on those words. This does not contradict its uniform predictive error bound. $\square$

**Theorem 7.3 (full acquired records and a single future trajectory).** A visible record containing a singleton determines its entire compatible hidden trajectory. An all-$B$ record of length $n\ge1$ has exactly two compatible trajectories. Consequently, using natural logarithms and $h(x)=-x\log x-(1-x)\log(1-x)$,

$$
H(X_0,\ldots,X_{n-1}\mid Y_0,\ldots,Y_{n-1})
=\frac{a^{n-1}+b^{n-1}}5\,h(x_{n-1})\le\log2.
$$

This bounded hidden-trajectory uncertainty does not bound the number of exact finite-start predictive configurations. Distinct finite unresolved startup ages cannot both be recovered almost surely by one decoder of a single complete future trajectory.

**Proof (7.3).** If the first singleton is $0$, its preceding initial $B$ run, if present, must have stayed at $4$; if it is $1$ or $3$, that run must have stayed at $2$. The singleton identifies its own state and every later symbol has the unique successor described in Theorem 2.1. Thus the whole compatible path is determined. On an all-$B$ word the only two paths and their conditional weights are the ones already computed. Taking conditional entropy over the actual visible histories gives the formula; all other histories contribute zero. Binary entropy is at most $\log2$. In particular the conditional entropy per observation tends to zero, although the unequal exact class count is infinite.

For the final statement, extend the coherent branch profiles to their usual measures on infinite visible streams. Any two finite startup laws are mixtures of the same $F_2,F_4$ with both coefficients strictly positive. A measurable set has zero mass under either mixture exactly when it has zero mass under both branch measures. The two mixtures are therefore mutually absolutely continuous. If a common future-trajectory decoder returned two different old ages almost surely under the two laws, its probability-one event for one output would also have probability one under the other law, contradicting the required distinct output there. The future can reveal a branch without revealing the old posterior weight or old recording boundary. $\square$

**Theorem 7.4 (almost-sure acquisition and the different entire-past contract).** Let $T=\min\{t\ge0:Y_t\ne B\}$. Then

$$
\Pr(T>n)=\frac{a^n+b^n}{5}\quad(n\ge0),\qquad
\mathbb E T=\frac15\left(\frac1{p+q}+\frac1r\right).
$$

Synchronization occurs almost surely with finite expected delay, but no finite worst-case delay. In the different contract where a stationary observer is already supplied its entire two-sided visible past, the exact predictive quotient has five classes almost surely. A five-label finite-start parser guessing the dominant component on its first $B$ has expected all-future error $u^{n-1}/5$ after $n\ge1$ reads; its supremum error over nonempty finite histories is $1/2$. This comparison places no guarantee on a query at empty history. At equality either component may be guessed, with the same conclusions using $u=a=b$.

**Proof (7.4).** The event $T>n$ is exactly $B^{n+1}$, giving its probability from Theorem 2.1. Summing these geometric tails gives the expectation. Their limit is zero, but every finite term is positive. Hence finite almost-sure delay and absence of a deterministic bound coexist. After the first singleton the five pure-state update is exact forever.

For the separately supplied two-sided stationary chain, the probability that the interval $[-m,0]$ is entirely $B$ is $(a^m+b^m)/5$. These decreasing events have limiting probability zero. Almost surely the acquired infinite past therefore contains a most recent singleton at finite distance from the present; updating through its finite suffix determines the current state. Each hidden mode has stationary mass $1/5$, and its distinct profile gives one of five almost-sure classes. This provides no prescribed conditional value on the null all-$B$ past, and does not acquire that past for a finite-start observer.

The finite-start parser can initialize at $R_d$ and use the total pure-state reset table. On its first singleton it resets correctly; on first $B$ it stays at $R_d$. It is exact after any singleton. On $B^n$ its conditional error is $\delta_{n-1}$ in the unequal case, or $1/2$ at equality. Thus the expected error is

$$
\frac{a^{n-1}+b^{n-1}}5\delta_{n-1}=\frac{u^{n-1}}5.
$$

The one-symbol startup history has error $1/2$, proving the asserted supremum across positive lengths. Exponential expectation decay does not remove any of the positive finite witnesses.

The mature causal-state background is Shalizi–Crutchfield, [*Computational Mechanics: Pattern and Prediction, Structure and Simplicity*, Definition 5, Lemma 7 and Theorem 2](https://arxiv.org/html/cond-mat/9907176v2), DOI [10.1023/A:1010388907793](https://doi.org/10.1023/A:1010388907793). Its stationary entire-past, null-set and entropy-minimality conditions are retained here. Travers–Crutchfield, [*Exact Synchronization for Finite-State Sources*, Definitions 4–7 and Theorem 1](https://arxiv.org/html/1008.4182v3), supplies synchronization in probability for finite unifilar, probabilistically distinct sources. The edge matrices here are $T^{(y)}=PD_y$: the graph is strongly connected, each state has at most one successor per symbol, and Theorem 2.1 separates the state laws. Stationarity aligns edge-emitted observations beginning at $Y_1$ with the finite law beginning at $Y_0$, without supplying an observed prehistory. The exact tails and uniform finite-start memory counts above preserve that distinction. $\square$

## 8. Configuration names and represented-law costs

**Assumption 8.1 (separate resource coordinates).** Model parameters are fixed mathematical data. A configuration-naming contract may permit arbitrary fixed-width binary names and one abstract synchronous symbol update. A different optional naming language permits length-$\ell$ binary words with no adjacent $11$, with independent zero seams. Costs for model representation, installed decoder tables, initialization, acquired events, numerical working registers, output, clock maintenance and physical storage are separate coordinates. Only suppliers explicitly named in a contract are available; none of these coordinates is equated with a state count by definition.

**Theorem 8.2 (the precise naming consequences).** Under the unrestricted fixed-width naming contract, $N$ configurations require and admit $\lceil\log_2N\rceil$ naming bits. Hence the sharp small-error initialized observer has naming width $\lceil\log_2(6+N_2)\rceil$; for fixed unequal parameters it is $\log_2\log(1/\epsilon)+O_{p,q,r}(1)$. Seven exact initialized configurations at equality require three such bits. Exact unequal prediction has no uniform naming width; a fixed-width encoding on histories of length at most $L\ge2$ needs initialized width at least $\lceil\log_2(L+6)\rceil$. An internally retained tagged, self-delimiting counter gives $O(\log(L+2))$ worst-case width on that domain. Under the optional no-$11$ language the naming width is instead

$$
\min\{\ell\ge0:F_{\ell+2}\ge N\},\qquad
F_0=0,\quad F_1=1.
$$

These are configuration-name statements, not total executable or physical memory bounds.

**Proof (8.2).** A width-$b$ unrestricted word has $2^b$ values, so injective names require $2^b\ge N$; conversely choose any $N$ such names. The counts and asymptotics follow from Theorems 2.2, 4.2 and 6.3. A tag for synchronization versus unresolved startup, together with a delimited integer $k$, supplies the variable-width exact representation; the delimiter and tag are part of the word. All finite histories admit finite words, while the class count prevents a bounded worst-case word.

For the optional language, the existing independent-seam capacity of [Fiber Calculus, Theorem 2.5](FIB_RELATIONAL_FIBER_CALCULUS.md) is reused: splitting by the first digit gives the recurrence with counts one and two at lengths zero and one, hence $F_{\ell+2}$. Injective naming again gives necessity and sufficiency. Seven labels require $\ell=4$, since $F_5=5<7\le F_6=8$. Neither recurrence prescribes legal physical rewrites or decoder workspace. Startup, current branch and transient position are already contained in the configurations counted above; multiplying by an additional free phase or current-symbol register would count a different representation. $\square$

**Assumption 8.3 (an effective specialization).** An optional effective law-output contract supplies exact rational $p,q,r,\epsilon$ in binary, integer and rational arithmetic, and an output request for either a finite symbolic law descriptor, one finite-word probability, or a full finite-horizon law. Scratch registers, static data and output storage are included in the total represented cost. This assumption does not alter the actual-symbol update or supply the observer with a recording-age clock.

**Theorem 8.4 (finite descriptions and costs beyond state names).** Under Assumption 8.3, the equality stratum, dominant component and both cutoff inequalities are decidable exactly. All decoder and emission coefficients in Theorems 4.2 and 5.1 have finite rational descriptions. If each input rational has at most $B$ bits in its numerator and denominator, a cutoff coefficient at index at most $K$ has $O((K+1)B)$ bits, and a direct table for these constructions has $O((K+1)^2B+(K+1)\log(K+2))$ bits. Those bounds are for one sufficient description, not for the smallest description. A full horizon-$H$ output is indexed by $4^H$ words; its materialization and arithmetic costs are not bounded by the configuration-naming width. Arbitrary real parameters, or generic computable-real approximation names alone, do not supply an exact equality decision or exact cutoff-tie decision.

**Proof (8.4).** Rational equality decides $r=p+q$ and compares $a,b$. Starting from $m=0$, exact rational powers and the defining non-strict inequalities decide a cutoff; termination follows from $\theta^m\to0$. No rounded logarithm is needed, and exact threshold ties are accepted. Rational sums, products and division by positive normalizers give every displayed coefficient. Products of $K$ bounded-description rational factors have numerator and denominator bit lengths $O((K+1)B)$; reduction can only shorten them. A constant number of rows and successors per configuration, summed across indices, gives the table bound, including successor addresses. These are distinct from its $O(\log K)$ retained configuration name.

The matrix formula for a requested word uses growing exact arithmetic and records the request's length and output. Enumeration of the entire law has one address for each element of $\mathcal A^H$. A symbolic law descriptor can avoid this expanded table but supplies no constant-workspace or constant-time numeric evaluation theorem. Already for fixed reduced rational $\theta=A/B_0$, $0<A<B_0$, the minority coefficient is

$$
\delta_k=\frac{A^k}{A^k+B_0^k}.
$$

Its denominator is reduced because $A,B_0$ are coprime, and has $\Theta(k)$ bits, whereas the integer index needs $O(\log(k+2))$ naming bits. Thus materializing an exact belief is a different representation from retaining its symbolic index.

For generic approximation names there is no finite observation of a name that uniformly distinguishes exact equality from an arbitrarily small nonzero perturbation. In particular, an equality decider halting on names of $r=s$ would inspect finitely many approximations; the same approximations can be extended to a sufficiently close allowed unequal $r$, forcing the same answer. Exact cutoff ties pose the analogous comparison problem. Rational data, a stronger certified comparison representation or suitable slack are extra assumptions. A finite table containing arbitrary real constants is therefore only an information-theoretic object until an effective presentation is specified. $\square$

**Theorem 8.5 (law-output slack).** Assume $a\ne b$ and $0<2\epsilon<\kappa$. For the common-law-decoder construction, if each decoded profile is replaced by one whose all-horizon $d$-error is at most $0\le\tau<\epsilon$, a cutoff satisfying $\delta_K/2\le\epsilon-\tau$ preserves the target $\epsilon$ guarantee. A per-entry error bound $\eta$ on a horizon-$H$ law table gives the estimate $\operatorname{TV}\le4^H\eta/2$; this estimate alone is not a horizon-independent $\epsilon$ certificate. These statements assume the exact source kernel $P$.

**Proof (8.5).** Theorem 4.2 with the smaller tolerance gives retained-state error at most $\epsilon-\tau$. One triangle inequality adds at most $\tau$ at every history and horizon. A per-entry error $\eta$ on a horizon-$H$ table yields only the crude half-$\ell^1$ bound $4^H\eta/2$, and without further joint structure cannot give the required uniform profile error.

The profile replacements must themselves be normalized and coherent across horizons. An independent entry-precision choice supplies neither that coherence nor a bound in the profile metric. $\square$

## 9. Source correspondence and remaining mathematical contracts

**Definition 9.1 (source correspondence).** The prediction task is the map $h\mapsto F_h$ on the actual-history domain of Assumption 1.1. Its observer resource is the retained word with the update of Definition 1.3. For unequal holding probabilities, its scalar coordinate on the unresolved startup stratum is $\delta_k$, and its error metric there is the absolute difference of that coordinate by Theorem 3.1. Classical HMM mixtures, realized-image quotients, positive conditioning, finite-law TV, scalar interval covers and deterministic iteration are the attributed intermediate structures used for these correspondences.

The already published [Context Geometry, §15](RECURSIVE_RELATIONAL_OBSERVATION_CONTEXT_GEOMETRY.md) uses $K_{a,y}$ instruments, actual positive conditioning, complete word laws and a real prediction domain. Its passive specialization here has a singleton action menu and $K_y=PD_y$. Its finite real dimension or finite hidden generator does not bound the number of deterministic retained observer words on the particular acquired-start orbit. The word update and retained-capacity distinction is shared with [Fiber Calculus Continuation II, §31](https://github.com/the-omega-institute/trureturing/blob/5ce3c4b236c875f9c46a95013ab05597b9eb7422/docs/develop/theory/FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md): that chapter's complete cyclic source, chosen $R,U$ commands, exact snapshots, acknowledgments, stopping outputs and budget-restricted controller minima are its own contract. None of those source coordinates, commands, delays or minima is an input to the present parser.

**Assumption 9.2 (comparison interfaces remain separate).** In [Auric §§136–143, revision 5ce3c4b236c875f9c46a95013ab05597b9eb7422](https://github.com/the-omega-institute/trureturing/blob/5ce3c4b236c875f9c46a95013ab05597b9eb7422/docs/develop/theory/AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md), §136 declares the actually acquired object–instrument interface; §137 adds its fixed linear read chain; §138 supplies a chosen quadratic metric; §139 supplies unit oriented three-dimensional volume; §140 treats five-mode response algebra and task-relative continuing quotients; §141 supplies classical and quantum retained-record contracts; §142 fixes a finite candidate, permission and task universe; §143 combines those supplied conditions while separating event order from clocks and rates. Its $M,J,K$ and geometric clocks are not the present $P,\chi$, stochastic future-law metric or finite recording age. Its finite candidate count does not replace the countably infinite family in Theorem 2.1. Only the shared requirement to preserve actual source, read, retained record and future-task correspondence is used here.

The [Whole-rho continuation, §55, revision 4f0bf484e86071b2a35edce8025c2285a82a0c8d](https://github.com/the-omega-institute/trureturing/blob/4f0bf484e86071b2a35edce8025c2285a82a0c8d/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md) attaches occurrence domains, a common field, kinetic and spectral operators and a separate clock to retained original ordered-tree histories and INITIAL. Its Hilbert norm, spectral ports and source-domain continuation remain different contracts; retaining those histories is not free acquisition of a finite-start Markov record. No identification of its heat matrix or added geometry with Assumption 1.1 is made.

**Definition 9.3 (unresolved extensions).** When $N_1>N_2$ in the unequal source, determining the exact self-generated-law optimum between $6+N_2$ and $6+N_1$ remains an open minimization problem here. Exact coarse-error minima outside $0<2\epsilon<\kappa$, randomized-retention minima under a different averaged error criterion, minimal total numerical workspace, and effective arbitrary-real law-output representations are not specified by the proved small-error counts. No native physical realization, thermodynamic price, unbounded archive recovery or unified space–time reconstruction contract is supplied by these conditional stochastic theorems. Acquisition and continuing prediction have the explicit scopes of §§1–8; the broader mutual-recovery objective requires its additional source, operation, metric and resource bridges.

## 追加锚（本行以下为增补区）

## 10. Uncertain calibration under the literal finite-start law contract

**Assumption 10.1 (one calibrated common observer).** Let $\Theta$ be a nonempty subset of

$$
\mathfrak A=\{(p,q,r):p,q,r>0,\ p+q+r<1\}.
$$

One actual parameter $\vartheta=(p,q,r)$ stays fixed throughout a run. For each $\vartheta$ the source is the same literal five-mode model of Assumption 1.1:

$$
P_\vartheta=
\begin{pmatrix}
1-p-q-r&p&0&q&r\\
q&1-p-q&p&0&0\\
0&q&1-p-q&p&0\\
p&0&q&1-p-q&0\\
r&0&0&0&1-r
\end{pmatrix},\qquad
X_0\sim\pi=\tfrac15(1,1,1,1,1),\qquad
\chi=(0,1,B,3,B).
$$

There is no probability prior on $\Theta$. Write $\mathbb P_\vartheta$, $M_\vartheta(h)$ and $F_{\vartheta,h}$ for this source law, the mass of an acquired visible word, and its conditional future profile. The first acquired symbol filters $\pi$ at $Y_0$; later acquisitions advance through $P_\vartheta$ and then filter. A nonempty acquired word $h$ of length $n$ predicts $(Y_n,\ldots,Y_{n+H-1})$. When an empty query is allowed it predicts from $Y_0$. Every finite word of positive mass remains in the accuracy domain, without a probability cutoff.

An optional additional calibration supply is a finite alphabet $C$ and an authentic label $\gamma(\vartheta)\in C$. The label depends only on the parameter, so its delivery does not condition or replace the hidden trajectory, initial law or acquired word. Its meaning is bound to that actual source. A supplier, its evidence and its delivery permission are additional assumptions. With no such supply, $C$ is a singleton. One fixed initializer $c:C\to Z$, one total deterministic visible update $U:Z\times\mathcal A\to Z$, and one fixed decoder $D:Z\to\{\text{coherent law profiles}\}$ give

$$
z_\vartheta(\varnothing)=c(\gamma(\vartheta)),\qquad
z_\vartheta(hy)=U(z_\vartheta(h),y).
$$

A fixed boot state followed by a declared label-reception map is another presentation of $c$. The conditional predictive carrier $Z$ includes its installed initial configurations and all retained fields used afterward. Any upstream boot or supply protocol has its own states and costs when it is included in the system boundary. A label still consulted by $U$ or $D$, an installed-program selector, a program counter, recording-age counter, history copy, work register or retained output is part of the complete retained configuration. There is no free parameter, label, clock, recording length or archive port. The horizon $H$ is a future-law request, not a recording-age observation.

For $\epsilon\ge0$, common accuracy means

$$
\operatorname{TV}\bigl(F_{\vartheta,h}^H,D(z_\vartheta(h))^H\bigr)
\le\epsilon
\tag{10.1}
$$

for every $\vartheta\in\Theta$, every positive finite $h$ in the chosen query convention, and every finite $H\ge0$. Each decoded profile is nonnegative, normalized and consistent under deletion of its last symbol; $H=0$ has zero error. As in Definition 1.3, coherence of a profile does not require its conditioned tail to equal $D(U(z,y))$. This is a common-law contract, not the stronger self-generated-law contract.

The fixed-known results in §§2–8 instead permit each installed observer's specification to contain its own fixed $p,q,r$. Label production, authenticity, source/history pairing, acquisition, static catalogue and program installation, numeric law output and physical storage remain separate resource coordinates as in Assumptions 8.1 and 8.3. Finite nominal $Z$ permits mathematical real constants in $D$; it does not by itself give a finite executable presentation of them.

**Theorem 10.2 (literal observable separation after positive acquisition).** All parameters in $\mathfrak A$ have exactly the same positive finite visible-word support. For any distinct $\vartheta,\varphi\in\mathfrak A$ and any respective positive finite histories $h,t$, including empty histories when queried,

$$
\lim_{H\to\infty}
\operatorname{TV}(F_{\vartheta,h}^H,F_{\varphi,t}^H)=1,
\qquad d(F_{\vartheta,h},F_{\varphi,t})=1.
\tag{10.2}
$$

This includes $p=q$, $r=p+q$, and families entirely on the equality stratum.

**Proof (10.2).** A visible word has positive mass exactly when it admits a compatible hidden path with positive initial mass and positive edges. All five initial masses are positive. The zeros of the displayed matrix are parameter independent, and every other entry is strictly positive throughout $\mathfrak A$. Thus the path-existence criterion is independent of the parameter. In particular $[0]$ always has mass $1/5$ and posterior $e_0$.

The columns as well as rows sum to one, preserving $\pi$. The positive-edge graph has the bidirectional cycle $0\leftrightarrow1\leftrightarrow2\leftrightarrow3\leftrightarrow0$ and leaf edge $0\leftrightarrow4$, with a positive self-loop at every state. Its directed diameter is at most three. Every ordered state pair therefore has a positive path of length exactly three, padding shorter paths by self-loops. Put

$$
\eta_\vartheta=\min(p,q,r,1-p-q-r),\qquad
\beta_\vartheta=5\eta_\vartheta^3,\qquad
\rho_\vartheta=1-\beta_\vartheta.
$$

Every positive edge is at least $\eta_\vartheta$, including the diagonal entries $1-p-q$ and $1-r$. Since $p+q+r+(1-p-q-r)=1$, one has $0<\eta_\vartheta\le1/4$, hence $0<\beta_\vartheta<1$. If $J$ has every row equal to $\pi$, then

$$
P_\vartheta^3=\beta_\vartheta J+\rho_\vartheta R
$$

for a stochastic $R$ preserving $\pi$. Iteration, followed by any remaining zero, one or two steps, gives

$$
\sup_i\operatorname{TV}(P_\vartheta^k(i,\cdot),\pi)
\le\rho_\vartheta^{\lfloor k/3\rfloor}.
\tag{10.3}
$$

This is the standard minorization argument of Levin–Peres–Wilmer, [*Markov Chains and Mixing Times*, second edition, Theorem 4.9 and its proof, pp.52–53](https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf), applied here with the explicit three-step minorization.

The stationary probabilities of the three visible pair words $01,03,0B$ are

$$
v_\vartheta=
\bigl(\mathbb P_\vartheta(01),\mathbb P_\vartheta(03),
\mathbb P_\vartheta(0B)\bigr)=\tfrac15(p,q,r).
\tag{10.4}
$$

The last identity uses $P_\vartheta(0,2)=0$ and $P_\vartheta(0,4)=r$. These observable coordinates identify the whole declared triple. The stationary one-symbol law $(1/5,1/5,2/5,1/5)$ in order $(0,1,B,3)$ contains no such distinction.

Here is a finite-event concentration argument for the required conditional laws. For one of those pair words $w$, let $I_j$ be its indicator at positions $j,j+1$ of the stationary source, with mean $u_\vartheta(w)$. Conditional on $X_{j+1}$, the expectation of $I_{j+k}$, $k\ge1$, has the form $P_\vartheta^{k-1}g(X_{j+1})$ for $0\le g\le1$ and $\pi g=u_\vartheta(w)$. Equation (10.3) bounds its difference from that mean by $\rho_\vartheta^{\lfloor(k-1)/3\rfloor}$. The Markov property and $0\le I_j\le1$ therefore give the same bound on $|\operatorname{Cov}(I_j,I_{j+k})|$. No independence of overlapping pairs is used. For the empirical frequency in an $H$-symbol word, $H\ge2$,

$$
\widehat u_H(w)=\frac1{H-1}\sum_{j=0}^{H-2} I_j,\qquad
\operatorname{Var}(\widehat u_H(w))
\le\frac{A_\vartheta}{H-1},\qquad
A_\vartheta=1+\frac6{\beta_\vartheta},
\tag{10.5}
$$

because $\sum_{k\ge1}\rho_\vartheta^{\lfloor(k-1)/3\rfloor}=3/\beta_\vartheta$. Stationarity gives the same bound for a future segment beginning at any fixed time. For the vector $\widehat v_H$ of the three pair frequencies, Chebyshev's inequality and a union bound give

$$
F_{\vartheta,h}^H
\{\|\widehat v_H-v_\vartheta\|_\infty\ge d_0\}
\le
\frac{3A_\vartheta}
 {M_\vartheta(h)(H-1)d_0^2}
\longrightarrow0
\quad(d_0>0).
\tag{10.6}
$$

Indeed the conditional probability of any future deviation is at most its unconditional stationary probability divided by $M_\vartheta(h)>0$. This division does not assume independence from the acquired cylinder. An arbitrarily rare positive history enlarges the required horizon without removing that history; at empty history its mass is one.

For distinct parameters choose $d_0>0$ with $2d_0<\|v_\vartheta-v_\varphi\|_\infty$. The finite-word event $\{\|\widehat v_H-v_\vartheta\|_\infty<d_0\}$ has probability tending to one under $F_{\vartheta,h}^H$ and zero under $F_{\varphi,t}^H$. Finite TV is at least this event gap and at most one, proving (10.2). Coherent prefix marginalization also makes the distances nondecreasing in $H$. Only finite future tests are used; neither an infinite acquired history nor an infinite all-$B$ conditioning event is introduced. $\square$

**Theorem 10.3 (exact calibration-cell radius and finite attainment).** If $m$ distinct parameters share one queried configuration under (10.1), their common error satisfies

$$
m(1-\epsilon)\le1.
\tag{10.7}
$$

In particular this applies to every calibration cell $S=\gamma^{-1}(\lambda)$ by using the same history $[0]$. For a finite cell of size $m\ge2$, the exact minimax all-history, all-finite-horizon radius is $1-1/m$. A common coherent observer attains it using six conditional predictive configurations for post-read-only queries, or seven including an empty query. These numbers are sufficient carrier sizes, not asserted minimum state counts.

For $0\le\epsilon<1$, each calibration cell has size at most

$$
K_\epsilon=\left\lfloor\frac1{1-\epsilon}\right\rfloor.
\tag{10.8}
$$

An infinite family cannot use finitely many labels at any $\epsilon<1$, regardless of the size of its retained-history carrier. At every $\epsilon>0$ below one, a finite-state common observer with a prescribed finite calibration alphabet exists exactly when every nonempty cell has size at most $K_\epsilon$. At $\epsilon=0$, finite-state existence further requires every member to satisfy $r=p+q$. At $\epsilon\ge1$, one fixed coherent profile and one predictive state suffice.

**Proof (10.3).** For distinct $\vartheta_1,\ldots,\vartheta_m$ and respective queried histories $h_i$, choose disjoint fixed $\ell^\infty$ balls about the distinct vectors $v_{\vartheta_i}$. Their inverse images $E_i^H$ under $\widehat v_H$ are disjoint finite-word events. By (10.6), $F_{\vartheta_i,h_i}^H(E_i^H)\to1$. If the common decoder is $Q$, TV accuracy gives

$$
1\ge\sum_{i=1}^m Q^H(E_i^H)
\ge\sum_{i=1}^m F_{\vartheta_i,h_i}^H(E_i^H)-m\epsilon.
$$

Letting $H\to\infty$ proves (10.7). This lower bound requires only nonnegative normalized finite-horizon decoders, and so remains valid under the stipulated coherence and for arbitrarily large $Z$. For $m=1$ it is immediate. A repeated calibration label gives the same initialized state and the same state after $[0]$, which is positive for every parameter. An infinite cell contains arbitrarily large finite subsets; choose $m$ with $m(1-\epsilon)>1$. The limiting inequality then already fails at a sufficiently large finite $H$.

For attainment, fix an installed finite cell $S=\{\vartheta_1,\ldots,\vartheta_m\}$, $m\ge2$. Write $F_{\vartheta_i,j}$ for its pure-state future law and $F_{\vartheta_i,*}$ for its empty law. Let $d_i=2$ if $a_i=1-p_i-q_i\ge b_i=1-r_i$, and $d_i=4$ otherwise. Equality is included by this fixed choice. Use the five pure tags $R_0,\ldots,R_4$ and one startup tag $M$. Initialize at $M$ for post-read-only queries. Every singleton $j\in\{0,1,3\}$ resets every tag to $R_j$. On $B$ use

$$
M\mapsto M,\qquad
R_0,R_4\mapsto R_4,\qquad
R_1,R_2,R_3\mapsto R_2.
\tag{10.9}
$$

Decode by

$$
Q_{R_j}=\frac1m\sum_{i=1}^m F_{\vartheta_i,j},\qquad
Q_M=\frac1m\sum_{i=1}^m F_{\vartheta_i,d_i}.
\tag{10.10}
$$

For an empty-inclusive query add $I$, initialized there, with $B\mapsto M$, singleton resets as above, and $Q_I=m^{-1}\sum_i F_{\vartheta_i,*}$. Each average is a nonnegative normalized coherent profile.

Theorem 2.1 exhausts the positive histories. A history containing a singleton occupies the matching pure tag, so its true profile appears in (10.10) with weight $1/m$; the empty law has the same property. On $B^{k+1}$ the true law under $\vartheta_i$ puts weight

$$
\alpha_i(k)=\frac{\max(a_i,b_i)^k}{a_i^k+b_i^k}\ge\frac12
$$

on $F_{\vartheta_i,d_i}$. Thus both its true law and $Q_M$ dominate the same subprobability profile $m^{-1}F_{\vartheta_i,d_i}$, since $1/m\le1/2$. At each finite $H$ the overlap identity

$$
\operatorname{TV}(P,Q)=1-\sum_w\min(P(w),Q(w))
$$

bounds their distance by $1-1/m$. This verifies every positive history and every horizon, including the endpoint $\alpha_i(0)=1/2$ and equality $a_i=b_i$. The lower bound at $[0]$ proves the radius is exact. The construction need not decode the history-wise mixture $m^{-1}\sum_i F_{\vartheta_i,h}$ on startup; the dominant-branch overlap is what permits finite attainment even for unequal parameters. No Bayesian weights or decoder/update conditioning identity are assumed.

Singleton cells at positive tolerance use an existing finite fixed-parameter observer with a smaller positive tolerance inside its small-error band, by Theorems 4.2–4.3. Equality singletons also have their exact finite observer. For finitely many cells, retain the cell tag and take the disjoint union of these machines and (10.9), with one fixed $c,U,D$. This proves positive-tolerance sufficiency and counts any live selector within $Z$. Necessity is (10.7). At zero tolerance every cell is a singleton, and Theorem 2.2 excludes finite exact prediction of an unequal member; the equality construction suffices for a finite equality menu. At tolerance at least one, the unit TV bound gives the final assertion. $\square$

**Corollary 10.4 (label capacity and a compact equality family).** For a menu of $N$ distinct parameters and $0\le\epsilon<1$, the minimum number of authentic calibration labels, allowing arbitrary retained memory, is

$$
L_\epsilon(N)=\left\lceil\frac{N}{K_\epsilon}\right\rceil.
\tag{10.11}
$$

At positive tolerance this label minimum admits finite conditional predictive memory. At zero tolerance finite memory does so exactly for equality menus. In particular $\epsilon<1/2$ forces an injective label, whereas at $\epsilon=1/2$ two parameters may share one label.

The compact continuum

$$
\Theta_{\rm eq}=\{(t,t,2t):1/10\le t\le1/8\}
\tag{10.12}
$$

has a finite exact observer for each fixed known member, but no common finite-label observer at any $\epsilon<1$, even with unlimited retained memory.

**Proof (10.4).** Equation (10.8) gives the lower label count. Partition the menu into cells of size at most $K_\epsilon$. Theorem 10.3 attains their bounds at positive tolerance. At zero tolerance, retain the whole finite history in each singleton cell and decode its exact law; this proves the arbitrary-memory label assertion, while Theorem 2.2 gives the stated finite-memory boundary. The equality continuum is strictly admissible, with $p=q$ and $r=p+q$ throughout. All its pointwise finite exact realizations are those of Theorem 2.2, but its infinitely many distinct frequency vectors force the finite-label obstruction of Theorem 10.3. For explicit same-transcript witnesses, $(1/8,1/8,1/4)$ and $(1/10,1/10,1/5)$ both give $[0]$ mass $1/5$ and known hidden state $0$, yet their future $01$ frequency limits are $1/40$ and $1/50$. Parameter uncertainty remains after hidden-state synchronization. $\square$

**Theorem 10.5 (finite literal calibration cannot certify a nonconstant class).** Let $g:\Theta\to G$ be a nonconstant required calibration classification. A parameter-independent deterministic protocol acquiring only chronological literal visible reads cannot stop after finitely many reads and certify $g(\vartheta)$ with zero error on every positive terminal transcript. This remains impossible if termination is required only almost surely and every report must still be correct with probability one under each source. The infimum worst-case literal read cost over successful finite protocols has an empty feasible set and therefore equals $+\infty$ for this exact calibration task.

**Proof (10.5).** Each finite terminal word determines the same stop decision and report under every parameter. By Theorem 10.2 it has positive mass under all of them whenever it has positive mass under one. A report correct under one parameter is therefore incorrect on a positive cylinder under another parameter in a different class. For an almost-surely finite protocol, the countably many finite terminal cylinders have total mass one under any fixed source, so at least one has positive mass. Correctness under every source again forces its report to equal every $g(\vartheta)$, contradicting nonconstancy. A calibration summary computed from the word, including its length or a FIB name, is a function of that same transcript and changes none of this support argument. Calibration reads are part of the original history; they do not restart the uniform prior. $\square$

The almost-sure statistical boundary is different. The positive hidden-edge chain $(X_j,X_{j+1})$ is finite and irreducible: connect the second endpoint of one edge to the first endpoint of another and then take that edge. Its stationary edge mass is $\pi_iP_\vartheta(i,j)$. Applying the ordinary finite-chain ergodic theorem to the three visible pair indicators makes their empirical frequencies converge almost surely to (10.4), for every starting distribution. The primary statement is Levin–Peres–Wilmer, Theorem C.1, pp.390–391, in the source cited in Theorem 10.2. This gives an asymptotically consistent parameter statistic; it supplies no finite zero-error certificate, no uniform finite stopping time and no guarantee that a learned law is accurate on every positive history. High-probability or asymptotic learning and a Bayesian-mixture target are separate mathematical contracts, not negated by Theorem 10.5.

**Corollary 10.6 (retained calibration, reused minima and nominal FIB names).** At $\epsilon<1/2$, queried configurations reached under distinct parameters are disjoint even after different positive histories. For a finite menu with authentic labels and

$$
0<2\epsilon<\min_{\vartheta\in\Theta}\kappa(\vartheta),
$$

let $n_\vartheta,m_\vartheta$ be the existing fixed-known total and positive-nonempty reached minima of Theorems 4.2–4.3 for the selected empty-query convention. The calibrated conditional predictive minima are respectively

$$
\sum_{\vartheta\in\Theta}n_\vartheta,\qquad
\sum_{\vartheta\in\Theta}m_\vartheta.
\tag{10.13}
$$

The same sum holds at zero tolerance for finite equality menus. These are conditional predictive counts; they exclude an upstream supplier or boot protocol unless its additional states are included explicitly.

Under the independent zero-seam no-$11$ naming convention of Theorem 8.2 and [Fiber Calculus Continuation II, §24.6](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md), naming a minimum calibration alphabet requires and admits

$$
F_{\ell+2}\ge L_\epsilon(N),
$$

and naming $R$ complete predictive configurations requires and admits $F_{\ell+2}\ge R$. In the small-error menu regime use $R=\sum_\vartheta n_\vartheta$ for the full carrier, or $R=\sum_\vartheta m_\vartheta$ only when naming the positive reached image. These capacity statements name supplied information; they do not acquire it.

**Proof (10.6).** A state shared under two distinct parameters would have one decoded profile within $\epsilon$ of two actual profiles at distance one by (10.2), contradicting $2\epsilon<1$. Thus their positive reached images are disjoint. Distinct installed initial configurations cannot coincide either: their common $[0]$ successors would violate the same conclusion. An initial state for $\vartheta$ cannot coincide with a positive reached state for $\varphi\ne\vartheta$, even if empty queries are disallowed. Choose a symbol $y$ with positive next-read probability after that reached history. The first-read word $[y]$ has positive uniform-prior mass under $\vartheta$. The common $U$ successor would then be queried under both parameters, again a contradiction.

For each parameter restrict to its initialization and its actual positive reached image. On every positive extension $U$ stays in that set; arbitrary transitions on impossible extensions may be retargeted inside it. The restriction is a fixed-known observer with the same actual runs and decoder coherence. The already proved per-parameter minima therefore apply to these pairwise disjoint sets and their reached images. The disjoint union of the known attaining observers selected by the authentic label gives one fixed $c,U,D$ and attains both sums. This reuses the fixed-law minima rather than reproving them. The no-$11$ language has $F_{\ell+2}$ legal names; injection gives necessity, and assignment of distinct legal names gives the nominal sufficiency, exactly as in Theorem 8.2. $\square$

The fixed-known near-equality state divergence is already Theorem 6.3. It remains a separate obstruction to a uniform bound on parameter-specific installed machines, even when calibration is supplied. In contrast (10.12) has bounded pointwise exact state counts and fails solely through missing common-decoder calibration. Neither statement is a replacement for the other.

**Theorem 10.7 (rare-history obstruction with future horizon capped at one).** There is a compact countable subset of $\mathfrak A$ for which finite calibration quantization cannot satisfy (10.1), even with only $H=1$ queried, at $\epsilon\le11/200$. Histories remain all positive finite acquired words, and the observer may retain arbitrarily much history.

**Proof (10.7).** Put $\vartheta_0=(1/8,1/8,1/4)$ and, for $n\ge1$,

$$
\lambda_n=100^{-n},\qquad
r_n=\frac14+\frac34(1-e^{-\lambda_n}),\qquad
\vartheta_n=(1/8,1/8,r_n),\qquad
\Theta_{\rm rare}=\{\vartheta_0,\vartheta_1,\ldots\}.
\tag{10.14}
$$

Here $a=3/4$ and $b_n=(3/4)e^{-\lambda_n}$. Since $1-e^{-\lambda_n}<\lambda_n\le1/100$, all parameters are strictly admissible and bounded away from its boundary. They converge to $\vartheta_0$, so the family is compact.

For $k_n=3\cdot100^n$, use the actual history $h_n=B^{k_n+1}$. Under any member its mass is $(a^{k_n}+b^{k_n})/5>0$, by Theorem 2.1. The state-$2$ posterior under $\vartheta_m$, $m\ge1$, is

$$
x_m(k_n)=\frac1{1+e^{-3\cdot100^{n-m}}}
=\sigma(3\cdot100^{n-m}),\qquad
\sigma(u)=\frac1{1+e^{-u}}.
\tag{10.15}
$$

The next-symbol event $\{1,3\}$ has probability $(p+q)x_m(k_n)=x_m(k_n)/4$. At $m=n$, $\sigma(3)>19/20$: the exponential series gives $e^3>\sum_{j=0}^6 3^j/j!>19$. For $m>n$, its argument is at most $3/100$, and $\sigma(3/100)<51/100$. Indeed $e^{3/100}<1/(1-3/100)=100/97<51/49$. Hence

$$
\operatorname{TV}
 (F_{\vartheta_n,h_n}^1,F_{\vartheta_m,h_n}^1)
\ge\frac{\sigma(3)-\sigma(3\cdot100^{n-m})}{4}
>\frac{11}{100}\qquad(m>n).
\tag{10.16}
$$

A finite label alphabet repeats a label on two of the infinitely many $\vartheta_n$, say $n<m$. Their state after the same $h_n$ is identical. The triangle inequality for its one-step decoder would bound (10.16) by $2\epsilon\le11/100$, a contradiction. Every witness is finite and positive, however rare; no acquired age is supplied to the machine. This proves a second obstruction arising from unbounded acquisition length rather than unbounded future horizon. $\square$

For comparison, if both acquisition length and future horizon are capped on a compact strict parameter set, there are only finitely many relevant words. The common-support positive history masses are continuous positive functions with positive minima on that compact set. Conditional finite-word probabilities are then uniformly continuous quotients, and an authentic finite parameter quantization can satisfy any positive tolerance for that different capped contract. Neither this finite-dimensional continuity nor the law-output slack of Theorem 8.5 justifies calibration rounding in (10.1): Theorem 8.5 keeps the exact source kernel, (10.2) separates every nonzero parameter difference over all horizons, and (10.16) retains a separate rare-history failure at horizon one.

**Definition 10.8 (original-source transfer obligations).** The target throughout §10 is the full conditional future-law profile of the declared passive stochastic source. Its information supply and complete retained state are those of Assumption 10.1. An actual FIB observer or controller can consume these conclusions only through a proved correspondence preserving its actual source, read timing and positive acquisition cylinders, the meaning and lawful delivery of calibration, the original target and the counted resources. A lower bound on every original task controller needs the direction that every successful such controller yields this coherent all-horizon decoder from its counted state, without adding a parameter, program, archive or clock port. A construction in the other direction needs target recovery on the appropriate law/state fibers, and an explicit error implication when only approximate laws are used.

The acquired-history and access contract, calibration already acquired, complete control address and finite recovery–termination certificate are respectively those of [Fiber Calculus Continuation II, §§22–27](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md). The present law-prediction observer supplies no replacement for that certificate's initial coverage, legal actions, actual-response successor closure, strict rank descent and correct original-target stopping. The original ordered trees, actual $\mathrm{Read}/\rho$/context responses and INITIAL labels of [Transport Memory Completion, §72](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), and the matched actual-reader/paid-block INITIAL task of [KBONACCI Initial Target Cost Theory, §§65–67](KBONACCI_INITIAL_TARGET_COST_THEORY.md), retain their own source domains, permissions, authentic paired histories, legal seams, rejection rules, declared fee coordinates, output and closure obligations. No identification of those contracts with $P_\vartheta,\pi,\chi$ and (10.1) is supplied by finite state names or a static decoder. Nominal capacity therefore gives no physical, thermodynamic, runtime, installation, acquisition-fee or universal original-task memory bound.

The literal source definitions, positive-history classification, coherent profiles and fixed-law observer suppliers are `FiniteStartFiveModeSource`, `FiveModePredictiveLawGeometry/Core`, `FiveModePredictiveLawGeometry` and `FiveModeAutonomousSharpCount` in `D5/S3/ObserverMemory/Prediction`, at source revision [05149fa5456f6eb47259bab8138572902863368e](https://github.com/the-omega-institute/trureturing/tree/05149fa5456f6eb47259bab8138572902863368e/D5/S3/ObserverMemory/Prediction). The source-specific separation, calibration-cell overlap realization and finite-acquisition boundary here are deductions for the explicitly declared uncertainty contract; the finite-chain mixing and ergodic intermediates are attributed to the primary source in Theorems 10.2 and 10.5. The original self-generated-law optimum and the coarse-error complete-state minima retain the unresolved scopes in Definition 9.3.

## 追加锚（本行以下为增补区）
