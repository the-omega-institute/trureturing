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

## 11. Conditional updates and the authentic-calibration boundary

**Definition 11.1 (a separate conditional-update contract).** Retain the literal source, parameter family, authentic calibration supply and common observer of Assumption 10.1. In particular one true $\vartheta=(p,q,r)$ stays fixed, $p,q,r>0$ and $p+q+r<1$, the hidden prior is uniform, and there is no probability prior on $\Theta$. Write $Q_z=D(z)$ and let $\mathcal R$ be the set of configurations reached by a positive history at which a query is allowed. For every $z\in\mathcal R$, every report $y\in\mathcal A$, every finite $H\ge0$ and $w\in\mathcal A^H$, impose the additional identity

$$
Q_z^{H+1}(yw)=Q_z^1(y)\,Q_{U(z,y)}^H(w).
\tag{11.1}
$$

The update $U$ is total and deterministic. Every $Q_z$ is nonnegative, normalized and coherent under deletion of final symbols, including $Q_z^0(\varnothing)=1$. Accuracy is still (10.1) on every actual positive finite history and every finite horizon. With empty queries, $c(\gamma(\vartheta))$ is also in $\mathcal R$; with post-read-only queries an initialized configuration is charged but has no pre-read accuracy obligation. Equation (11.1) is required only at actual reachable query configurations. The global row-product condition of Definition 1.3 is a sufficient stronger realization, and its treatment of hypothetical generated configurations is a separate size convention.

If $Q_z^1(y)=0$, prefix marginalization and nonnegativity force $Q_z^{H+1}(yw)=0$ for every $H,w$. Equation (11.1) then says $0=0$, without defining a conditional law by division or prescribing $Q_{U(z,y)}$ on that null branch. An actual report $y$ still passes through the total $U$. Whenever $M_\vartheta(hy)>0$, the successor is still queried and must be accurate, even if its preceding forecast assigned $y$ probability zero. No inclusion of actual support in forecast support is assumed.

Theorem 10.3 concerns prefix coherence alone and retains its radius $1-1/m$ and its six/seven-state finite-cell construction. The equation above adds a relation between different decoded configurations; it is an additional contract, rather than an interpretation of that earlier theorem.

**Lemma 11.2 (source, stream and finite-query correspondence).** A coherent normalized finite-word profile on $\mathcal A$ has a unique probability extension to $\mathcal A^{\mathbb N}$ with its coordinate sigma-field. For two such extensions $P,Q$,

$$
\sup_{E\text{ measurable}}|P(E)-Q(E)|
=\sup_{H\ge0}\operatorname{TV}(P^H,Q^H).
\tag{11.2}
$$

For every positive acquired history $h$, the extension of $F_{\vartheta,h}$ is the actual conditional future law, since

$$
F_{\vartheta,h}^H(w)
=\frac{M_\vartheta(hw)}{M_\vartheta(h)}.
\tag{11.3}
$$

At empty history its first symbol is $Y_0$; at a nonempty history of length $n$ it is $Y_n$. If $h$ is queried, $hv$ is an actual positive extension and $Q_{z_\vartheta(h)}^{|v|}(v)>0$, then conditioning the decoded stream law on $v$ gives precisely the extension of $Q_{z_\vartheta(hv)}$.

There are measurable events $T_\vartheta$ on future streams, invariant under adding or deleting a finite prefix, such that

$$
F_{\vartheta,h}(T_\vartheta)=1
\quad\text{for every positive finite }h,
\qquad
T_\vartheta\cap T_\varphi=\varnothing
\quad(\vartheta\ne\varphi).
\tag{11.4}
$$

Here $T_\vartheta$ is the event that the empirical adjacent-pair frequencies for $01,03,0B$ converge to $v_\vartheta=(p,q,r)/5$. These are events of the visible source, including $p=q$ and $r=p+q$.

**Proof (11.2).** Embed the finite alphabet as four distinct real numbers. Normalization and final-symbol consistency give the hypotheses of the usual probability extension theorem. The resulting measure is supported on $\mathcal A^{\mathbb N}$, and cylinder probabilities determine it uniquely. For completeness, finite-coordinate events form an algebra generating the coordinate sigma-field. For any finite measure $\mu$, every measurable event $E$ can be approximated by an event $B$ in this algebra with $\mu(E\mathbin{\triangle}B)$ arbitrarily small. The approximable class is closed under complements and countable unions: truncate the union by finite-measure continuity, then approximate its finitely many members. It therefore contains the generated sigma-field. Apply this to $\mu=P+Q$. Every such $B$ depends on some finite common horizon, and

$$
|P(E)-Q(E)|
\le |P(B)-Q(B)|+(P+Q)(E\mathbin{\triangle}B).
$$

Let the last term tend to zero. The reverse inequality follows because every finite-coordinate event is measurable. The finite half-$\ell^1$ TV equals the maximum event gap, proving (11.2). In particular a strict stream-event gap greater than $\epsilon$ already has a witness at a finite horizon.

Equation (11.3) is the actual chronological cylinder quotient of Definition 1.2 and the native `all_history_conditional_identity`. It uses the first filter at $Y_0$ and subsequent advance/filter steps. Iterate (11.1) along $v$: each intermediate acquired prefix is positive and queried, giving

$$
Q_{z_\vartheta(h)}^{|v|+H}(vw)
=Q_{z_\vartheta(h)}^{|v|}(v)\,
 Q_{z_\vartheta(hv)}^H(w).
\tag{11.5}
$$

Division is used only when the displayed prefix mass is positive. Equality on all tail cylinders and uniqueness of extension give the asserted conditional stream law.

For (11.4), reuse the common positive support of Theorem 10.2 and the finite-edge-chain ergodic argument following Theorem 10.5. The allowed-edge chain $(i,j)\mapsto(j,k)$ is finite irreducible with stationary mass $P_\vartheta(i,j)/5$. Its observable pairs $01,03,0B$ select respectively the edges $0\to1,0\to3,0\to4$; $P_\vartheta(0,2)=0$ excludes another $0B$ contribution. The occupation limits thus give $(p,q,r)/5$ almost surely. At a positive recording boundary the actual posterior supplies an initial distribution for the same future transition, and the same ergodic statement applies. Finite deletion changes only finitely many pair counts and not their limiting averages. The limit vector is injective on the declared triples, so the events are disjoint. This uses the almost-sure ergodic statement, rather than inferring almost-sure convergence from (10.6) alone. All statements concern extensions of the specified finite laws; no infinite acquired record is supplied to the observer. $\square$

**Theorem 11.3 (unit supremum in every nonsingleton calibration cell).** Suppose a calibration cell contains distinct admissible $\vartheta,\varphi$. Every observer satisfying Definition 11.1, with any cardinality of retained carrier, has

$$
\sup_{\substack{\psi\text{ in the cell},\ M_\psi(h)>0\\
 h\text{ queried},\ H<\infty}}
\operatorname{TV}(F_{\psi,h}^H,Q_{z_\psi(h)}^H)=1.
\tag{11.6}
$$

For each $0\le\epsilon<1$ there are a true parameter in the cell, a positive finite acquired history $h$, and a finite future horizon $H$ with error strictly greater than $\epsilon$. Both query conventions have this obstruction. The same conclusion applies if the two runs share a queried configuration after any one common positive nonempty history, even when their initial labels differ. The value one is a supremum over finite queries; attainment at a particular finite pair $(h,H)$ is not asserted.

**Proof (11.3).** First use $h_0=[0]$, which has mass $1/5$ and posterior $e_0$ under every parameter. A shared label gives a shared configuration there. Let $Q$ be its decoded stream extension and let

$$
S=\{x:M_\vartheta(h_0x_{<n})>0\text{ for every }n\ge0\}.
$$

Theorem 10.2 makes this the same set for $\varphi$. Each true conditional law gives it probability one: its complement is a countable union of zero-mass cylinders. Put $\delta=1-\epsilon>0$. If some finite-horizon error under $\varphi$ at $h_0$ already exceeds $\epsilon$, that is a witness. Otherwise (11.2) and (11.4) give

$$
Q(A)\ge\delta>0,\qquad A=S\cap T_\varphi,
\tag{11.7}
$$

because $F_{\varphi,h_0}(A)=1$.

Let $\mathcal F_n$ be the sigma-field of the first $n$ future symbols and set $m_n=\mathbb E_Q[\mathbf1_{T_\vartheta}\mid\mathcal F_n]$. These bounded conditional expectations converge to $\mathbf1_{T_\vartheta}$ in $L^1(Q)$. An elementary proof suffices here. Approximate $T_\vartheta$ by a finite-coordinate event $B$ with $Q(T_\vartheta\mathbin{\triangle}B)<\eta$. For every $n$ beyond its coordinate horizon, conditional-expectation contraction gives

$$
\|m_n-\mathbf1_{T_\vartheta}\|_1
\le2Q(T_\vartheta\mathbin{\triangle}B)<2\eta.
$$

Let $\eta\downarrow0$. Since $A$ is disjoint from $T_\vartheta$, it follows that $\int_A m_n\,dQ\to0$. Choose a finite $n$ with this integral less than $\delta Q(A)/2$. Among the finitely many length-$n$ cylinders there is therefore a word $v$ with

$$
Q(A\cap[v])>0,\qquad
Q(T_\vartheta\mid[v])=m_n(v)<\delta/2.
\tag{11.8}
$$

This cylinder has positive forecast mass and, since it meets $S$, $h=h_0v$ has positive actual mass under both parameters. Every preceding cylinder also has positive forecast mass and is an actual positive prefix. Equation (11.5) identifies the conditional tail with the decoder at that shared updated configuration. Finite-prefix invariance of $T_\vartheta$ makes (11.8) its probability under this tail decoder. But $F_{\vartheta,h}(T_\vartheta)=1$, so the stream-event gap at $h$ is greater than

$$
1-\delta/2=(1+\epsilon)/2>\epsilon.
$$

Equation (11.2) supplies a finite $H$ with error greater than $\epsilon$ at this positive finite $h$. This proves the claimed finite violation without assuming accuracy at descendant histories in advance. The same proof starts from any shared positive nonempty $h_0$: its continuation support is common and (11.4) holds from its actual posterior. Thus pure histories and every finite startup $B^{k+1}$ remain covered, as do both equality strata and an optional empty query.

Forecast mass outside $S$ and zero-mass forecast cylinders are permitted throughout. Accuracy at $h_0$ forces the positive mass (11.7) on legal source paths; the selected witness conditions only on a positive part of that mass. Other true-positive forecast-zero histories remain queries with their total updates. They are never divided by or deleted from the contract.

TV is at most one for any two normalized finite laws, and a finite violation exists for every smaller proposed bound, proving (11.6). A one-state observer with $U(z,y)=z$ for every report and $Q_z$ concentrated on the constant-$0$ stream is normalized, coherent and satisfies (11.1), including its zero-forecast inputs. It meets tolerance one without calibration. Hence the minimax threshold is also exactly one. $\square$

**Example 11.4 (an equality-menu defect of the prefix-only mixture).** Take

$$
\vartheta=(1/10,1/10,1/5),\qquad
\varphi=(1/5,1/5,2/5).
$$

Both are strictly admissible and satisfy $p=q$ and $r=p+q$. In the two-member construction (10.9)–(10.10), after the actual history $[0]$ the decoded law is $Q_{R_0}=(F_{\vartheta,0}+F_{\varphi,0})/2$ and $U(R_0,B)=R_4$. The actual two-step path $0\to4\to0$ gives

$$
Q_{R_0}^2(B0)=\tfrac12((1/5)^2+(2/5)^2)=\frac1{10},
\qquad
Q_{R_0}^1(B)Q_{R_4}^1(0)
=\left(\tfrac12(1/5+2/5)\right)^2=\frac9{100}.
$$

The defect is exactly $1/100$. Report $B$ has positive true and forecast probability. Correct conditioning of this mixture reweights the two models to $1/3,2/3$, whereas its retained pure-tag decoder reinstalls equal weights. The original prefix-only radius $1/2$ remains Theorem 10.3. Theorem 11.3 excludes every replacement satisfying (11.1) at any tolerance below one in this unresolved cell, including a cell wholly on $r=p+q$.

**Proposition 11.5 (finite realization with authentic exact calibration).** With the finite calibration alphabet of Assumption 10.1 and $0<\epsilon<1$, a common finite nominal observer satisfying Definition 11.1 exists exactly when every nonempty calibration cell is a singleton. At $\epsilon=0$, it exists exactly when every nonempty cell is a singleton and every installed triple satisfies $r=p+q$. At $\epsilon\ge1$, the one-state construction of Theorem 11.3 suffices without calibration. These are conditional existence statements given authentic source-bound supply and the installed model data.

**Proof (11.5).** Singleton cells are necessary by Theorem 11.3, and finitely many labels then imply a finite parameter menu. For sufficiency reuse the fixed-law generator of Theorem 5.1, with its actual-history certificate. For each unequal installed triple choose $\eta=\min(\epsilon/2,\kappa/4)>0$, so $\eta\le\epsilon$ and $2\eta<\kappa$. With the notation of Definition 4.1 put

$$
N=N_1(\eta)=\min\{k:\delta_k\le\eta\}.
$$

The supplied carrier is $I,R_0,\ldots,R_4,A_0,\ldots,A_{N-1}$, with $6+N$ total configurations and $5+N$ reached after reads. Its total update resets every singleton $j$ to $R_j$, uses $R_0,R_4\mapsto R_4$ and $R_1,R_2,R_3\mapsto R_2$ on $B$, and advances startup labels to the cutoff and then to the dominant $R_d$. Its rows at $R_i$ are the literal rows $v_i$, its rows at $A_k$ are the actual startup one-step rows, and its row at $I$ is the first-read law $(1/5,1/5,1/5,2/5)$ in order $(0,1,3,B)$. Its decoder is the product of these normalized rows along this very $U$. Splitting off the first factor proves (11.1) at every configuration, including zero factors; row normalization proves coherence and normalization.

Theorem 2.1 exhausts the actual histories, and Theorem 5.1 proves their errors for this product decoder. Pure histories are exact. At $B^{k+1}$ with $k\ge N$ the error at horizon $H$ is $\delta_k(1-u^H)\le\eta$. For a transient $A_k$, $k<N$, put $m=N-k$. The error is zero for $H\le m$, and for $H>m$ is

$$
\frac{u^N}{a^k+b^k}(1-u^{H-m})\le\delta_N\le\eta.
$$

The empty-law supremum error is $u^N/5\le\eta$. These are the existing estimates of Theorem 5.1: before the cutoff the only altered continuation is the common prefix $B^m$, after which the generator uses $F_d$ instead of the residual startup mixture. Its transient decoder is thus the generated law, not an unchanged exact startup profile past the cutoff. The non-strict cutoff includes equality $\delta_N=\eta$.

If $d=2$, the saturated forecast gives report $0$ probability zero while the actual minority component still gives it positive probability; total $U$ sends it to exact $R_0$. If $d=4$, the analogous true-positive forecast-zero reports are $1,3$, resetting to exact $R_1,R_3$. Equation (11.1) has both sides zero on the preceding null forecast cylinder, and the actual successor has its required exact pure law. No source-positive history is excluded.

At $a=b$, reuse the exact equality construction of Theorems 2.2 and 4.3. Five pure labels and one half-mixture label $A$ suffice for post-read-only queries, with initialization at $A$, a $B$ self-loop there and singleton resets. Equal holding rates make conditioning that half-mixture on $B$ return the same law, and its singleton reports identify their pure successors. With a queryable empty boundary add $I$ with the true first-read row and $B\mapsto A$, giving seven configurations. These machines satisfy (11.1) exactly. Initialization at $A$ in the post-read convention supplies no different hidden prior: the first actual read still filters the stated uniform $\pi$, and its unqueried pre-read forecast is not an actual source generator.

Take the disjoint union of the finitely many supplied machines, keep the model block within the retained configuration, let $c$ install its authentic label's block, and define the one common $U,Q$ blockwise. Accuracy and (11.1) hold blockwise, proving positive-tolerance sufficiency and a finite sufficient carrier bound. At zero tolerance an unequal member is excluded by the infinite exact-law image of Theorem 2.2; finite equality blocks give sufficiency. No optimal sum of compatible state counts is asserted.

For a fixed unequal model in the existing small-error regime, the old common-decoder lower bound and this supplier still bracket the initialized minimum for the actual-query conditional-update contract by $6+N_2(\epsilon)$ and $6+N_1(\epsilon)$. The original global self-generated interval in Theorem 5.1 remains its own result. When these endpoints differ, no new sharp compatible-generator minimum or equality of the two minimization problems is supplied. $\square$

**Corollary 11.6 (acquisition, retention and actual-resource boundaries).** For any observer satisfying Definition 11.1 with error $0\le\epsilon<1$, authentic calibration must identify the exact possible triple, and the configurations $z_\vartheta([0])$ must be distinct for distinct triples. Thus $M$ possible models require at least $M$ complete retained configurations at this common history; even an enlarged label interface cannot put infinitely many models into a finite common carrier. This is a common-history injection, without a claim that all reached images at different histories are disjoint at every subunit tolerance.

**Proof (11.6).** A repeated cell is excluded by Theorem 11.3. A collision after $[0]$ gives its more general shared-configuration obstruction, even for distinct installed labels. Injection into a finite carrier then forces a finite parameter menu. Theorem 10.5 already excludes a finite literal-visible-read, zero-error acquisition of any nonconstant exact calibration partition, including almost-surely finite correct stopping: a positive finite terminal transcript is shared by all admissible triples and has the same deterministic report. A longer acquired prehistory, a transcript-derived label or an archive supplies no exception. Starting the continuing conditional-update proof at that terminal history gives the same finite-query obstruction. The declared infimum worst-case literal-read cost for this exact certificate task has empty feasible set and is $+\infty$; this is not an expected estimation cost. $\square$

An authentic external label or source-bound selection of an installed program is additional supply, with its own production, authentication, delivery, lawful access and installation requirements. Proposition 11.5 does not construct that supplier from visible reads. The block selector and any still-consulted label, clock, phase, retained output or archive belong to the complete retained configuration. Arbitrary exact real model constants permit finite nominal tables but do not supply finite binary code or exact comparison algorithms. Under the separate exact-rational presentation of Assumption 8.3, Theorem 8.4 supplies finite descriptions and exact equality/cutoff decisions. Numeric workspace, expanded $4^H$ law output, runtime and physical storage remain distinct resource coordinates. The fixed-known near-equality divergence in Theorem 6.3 also remains its own result.

The existing FIB consumer is [Fiber Calculus Continuation II, Definitions 22.2 and 26.1–26.2](FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md): $c$ consumes an already acquired class and $v$ updates complete control memory through the actual response. An instance of the present passive prediction interface uses that response update as $U$ and additionally supplies the literal five-mode source and full-law decoder. The independent zero-seam naming capacity of its §24.6 and Theorem 8.2 names supplied distinctions; it authenticates no model and grants no read permission. Its §27 and Proposition 38.80 certify initial coverage, legal actions, same-source successor closure, correct target stopping and strict rank descent for their deterministic recovery tasks. A continuing Markov prediction invariant supplies no such stopping or original-target certificate. The original-tree address/response/INITIAL contracts, KBONACCI tasks and physical costs retain the source, target, action and resource bridges of Definition 10.8; no transfer is supplied by matching state names or report alphabets.

The primary probability references for this section are Durrett, [*Probability: Theory and Examples*, fifth edition, Theorem A.3.1, pp.464–465, and Theorems 4.6.8–4.6.9, p.247](https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf), for extension and upward conditional-expectation convergence; the finite-chain occupation statement is Theorem 5.6.1, pp.310–311, as well as the Levin–Peres–Wilmer source already cited in §10. The elementary finite-event and $L^1$ arguments above give the needed correspondences explicitly. Shalizi–Crutchfield's predictive-state conditioning frame cited in §7 retains its stationary entire-past and almost-sure scope. The source-specific deductions here concern every positive finite acquired history and every finite future horizon under the separate equation (11.1); capped-horizon, averaged, Bayesian-prior and eventual-learning targets have different quantifiers. The finite witness sizes need not have a uniform bound, and no efficient synthesis, effective arbitrary-real implementation or global novelty claim is made.

## 追加锚（本行以下为增补区）

## 12. Checkpointed moving-current acquisition and finite continuation

The static code of the ordered-tree source supplies an exact signature once its
ancestor colours are available, and the companion's Theorem 5.1 supplies the
whole-future diameter of a signature cell. The following controlled sampler
joins actual acquisition of that signature to a forecast from the restored
current source. Its interface is an additional assumption, not a consequence
of the passive unit-seam heat law.

**Definition 12.1 (the checkpointed parent sampler).** Retain the source
$\mathcal P=\{L,R\}^{*}$, the fixed integer $m\ge3$, colour $q$, depth $d$,
and source law of Definition 1.1 in the companion
[FIB-ATOM finite-joint prediction](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_FINITE_JOINT_PREDICTION.md).
Write $\mathbb N_0=\{0,1,\ldots\}$. All budgets, depths, indices and counts
below are integers in $\mathbb N_0$, with positive waiting-call indices in
$\{1,2,\ldots\}$. The recursion and law are fixed public model data.
The observer has a source-independent program and is initially bound to one
actual source at an unknown address $p$. Its sole initial source readout is

$$
O(p)=(q(p),d(p)).
$$

The literal word $p$, unobserved ancestor colours and a precomputed signature
are not inputs. The binding, current permissions, exact readout, finite record
material and workspace are installation premises. During acquisition, return
and prediction the passive heat clock is paused and no other actor changes
the source or revokes these permissions. At a nonroot current address $x$,
one **TryUp** call draws a fresh independent direction

$$
D\in\{\mathsf{up},\mathsf L,\mathsf R\},\qquad
\mathbf P(D=\mathsf{up})=\mathbf P(D=\mathsf L)=\mathbf P(D=\mathsf R)=1/3.
$$

If $D=\mathsf{up}$, the source moves to $\operatorname{par}(x)$ and returns
$O(\operatorname{par}(x))$ together with a one-use reverse token
$\tau_x$. If $D=\mathsf L$ or $\mathsf R$, the source stays at $x$, returns
$O(x)$, and returns no token. Token presence and the one-unit depth decrease
identify acceptance; rejection supplies no new ancestor. The token is bound
to this very traversed edge and this source. It permits exactly one reverse
move from $\operatorname{par}(x)$ to $x$, only while that source is at
$\operatorname{par}(x)$. Consumption revokes the capability and removes its
stack entry; copying a token's description creates no additional right.
The interface has no address query, reset, clone, source-correlated random
seed or future-response oracle. All **TryUp** calls, including accepted and
rejected calls, each count as one charged primitive call; each reverse
consumption also counts as one. These counts are not bit or physical costs.

Fix $k\in\mathbb N_0$ with $k\le n=d(p)$, and write
$a_j=\operatorname{par}^{j}p$, $c_j=q(a_j)$ for $0\le j\le k$.
These are proof notation, not extra observer inputs. **Acquire(k)** repeats
**TryUp** until $k$ acceptances. After $j$ acceptances its data and live stack
are, respectively,

$$
R_j=(n,c_0,\ldots,c_j)=S_j(p),\qquad
K_j=(\tau_1,\ldots,\tau_j).
$$

Here $\tau_i$ reverses the actual move $a_{i-1}\to a_i$. The source is
at $a_j$; colours are retained in acquisition order, and rejected trials
leave $R_j,K_j$ unchanged. **Return(k)** starts with $(R_k,K_k)$ at $a_k$.
At its return stage $i$ the source is at $a_i$ and precisely
$\tau_1,\ldots,\tau_i$ remain live. It consumes $\tau_i$, reaches
$a_{i-1}$ and removes that entry. Thus every consumption is legal, including
when $a_k$ is the root. After the last consumption the prediction state is

$$
M_k:=R_k=S_k(p),\qquad K=\varnothing,\qquad x=p.
$$

No spent-token receipt is retained or used as predictor input. The retained
source binding and pause permission remain current, but all acquired reverse
rights have been spent. At $k=0$ both protocols are empty and
$M_0=(d(p),q(p))$, just the reordered initial readout $O(p)$.
Phase, budget/counter backing, data, live capabilities and transient reply
storage are actual memory while used; discarded trial replies and the full
trial chronology are not an uncharged archive. On resumption the same source
evolves from its restored address under the unchanged heat generator, with
future heat randomness independent of sampler trials. This Markov continuation
is part of the controlled-interface assumption, not a reset or a new source.

**Lemma 12.2 (uniform availability and primitive-call count).** For every
address $p$ and $k\in\mathbb N_0$ with $k\le d(p)$, **Acquire(k)**
terminates almost surely. If $N_k$ is its number of **TryUp** calls, then

$$
N_k=\sum_{j=1}^{k}G_j,\qquad
\mathbf P(G_j=r)=\left(\frac23\right)^{r-1}\frac13\quad(r\ge1),\qquad
\mathbf E_pN_k=3k.
\tag{12.1}
$$

The $G_j$ are independent; $N_0=0$. For fixed $k$, the law of $N_k$ is
independent of the admissible start $p$. **Return(k)** restores that very
source to $p$ and leaves $(M_k,K)=(S_k(p),\varnothing)$. For a fixed
$\ell\in\mathbb N_0$ completed prediction requests at that paused cut, the
charged call/request count is $N_k+k+\ell$, of expectation $4k+\ell$.
In particular acquisition
uses $3k$ calls in expectation, acquisition plus return uses $4k$, and
including one prediction request gives $4k+1$.

**Proof.** At every nonroot address each trial is an independent Bernoulli
success with probability $1/3$. The waiting time $G_j$ for the $j$th
success is therefore geometric with the displayed mass function. Fresh
independent draws after each acceptance make the successive waits independent;
no colour-dependent decision changes their success probability. A finite sum of
such variables is finite almost surely and has expectation $3k$. Before the
$j$th success, $j\le k\le d(p)$, depth is $d(p)-j+1\ge1$; hence every
**TryUp** call is at a nonroot, although its final success can reach the
root. The returned observation at the $j$th success is the
colour of $\operatorname{par}^{j}p$, and the reverse token is bound to that
actual edge. Consuming the tokens in last-in-first-out order reverses the exact
accepted path, removing each right as it is spent. It preserves the acquired
colour data, so the post-return state is the one asserted. Add the actual
$k$ reverse calls and $\ell$ requests. The empty-sum case gives all assertions
at $k=0$ without calling **TryUp** at the root. No deterministic call cap is
asserted for $k>0$. $\square$

**Definition 12.3 (a callable finite prediction task).** Let
$T\in[0,\infty)$ be finite and $H\in\mathbb N_0$. On a future heat path,
let $\sigma_j$ be its $j$th actual jump time, $\sigma_0=0$, and
$W_j=\sigma_j-\sigma_{j-1}$. The finite observed data for a task are $O(X_0)$
and, for $1\le j\le H$, $(O(X_{\sigma_j}),W_j)$ if $\sigma_j\le T$,
or a censoring symbol $\partial$ if $\sigma_j>T$. A requested cylinder $C$
is specified by a finite Boolean combination of tests of initial or uncensored
endpoint equality to specified values in $E=C_m\times\mathbb N_0$,
censoring, and rational waiting-time
intervals for uncensored jumps. It imposes no condition after the first $H$
jumps. Censoring makes $C$ an event of the path restricted to $[0,T]$;
jump times and these tests are measurable by companion Definition 1.2.
At $H=0$ only the initial observation is tested. At $T=0$ all positive-index
entries are $\partial$ almost surely.

After **Acquire(k)** and **Return(k)** the exact legal variable predictor
input is $(M_k,T,H,C)$, with the fixed public recursion and law installed.
It has no token, actual address, discarded reply, old archive or future-read
input. Write $s=M_k$ and infer $k$ from its colour-list length. The answer is

$$
\operatorname{Predict}_{T,H}(C;M_k):=\mathsf L_{r_k(s)}^{T}(C),
\tag{12.2}
$$

where $r_k(s)$ is the lexicographically first address realizing the signature
$s$, as in companion Definition 5.2. It is computed from the acquired data
by enumerating the finite level of depth $n$ in $s$, testing the installed
recursion and selecting the first matching signature. This supplies a
computed representative, not an unobserved actual address.

The answer is a symbolic finite sum of route probabilities and exponential
waiting-time integrals, with the censoring inequalities included. There are
at most $2^n$ candidate addresses and $3^H$ length-$H$ jump routes from a
candidate, since each vertex has at most three neighbours. Conditional on
each such route, the first $H$ waits are independent exponentials with
the actual degree-two or degree-three rates. Integrating unused future
waits includes the censored cases. This is a finite symbolic evaluation,
not a bound on bit complexity or arithmetic runtime. An arbitrary real $T$
is a parameter of that expression; no finite binary encoding, exact
comparison or numerical evaluation of an arbitrary real is supplied.

A request changes only request/work/output storage and leaves the same
source paused at $p$. A finite number of further requests can reuse $M_k$,
each counted separately. Resumption then gives the original heat law from
$p$. Its subsequent realized jumps do not update $M_k$ to a new current
signature: predictions here refer to this returned cut, not to all later cuts.

**Theorem 12.4 (moving-current acquisition-to-forecast bridge).** Let $p$ be
any deterministic source start, let $h\in\mathbb N_0$, and put

$$
k=\min\{h,d(p)\}.
$$

Run the checkpointed sampler, perform **Acquire(k)** and **Return(k)**, and then
answer tasks (12.2) from the post-return $M_k$, with no live reverse tokens.
For every finite $T\ge0$, $H\in\mathbb N_0$ and cylinder $C$ of
Definition 12.3,

$$
\left|\mathsf L_p^T(C)-\operatorname{Predict}_{T,H}(C;M_k)\right|
\le \min\{b_k(T),2^{-k}\},
\tag{12.3}
$$

where $b_k$ is companion (4.1). The same representative law defines a coherent
whole-future predictor and satisfies

$$
\left\|\mathsf L_p^\infty-\mathsf L_{r_k(S_k(p))}^\infty\right\|_{\rm TV}
\le2^{-k}.
\tag{12.4}
$$

If $d(p)\le h$, then $k=d(p)$, the error is zero, and the complete-signature
classification gives $r_k(S_k(p))=p$. At $T=0$ the finite-window error is
zero for every $k$, since the initial observations agree. For arbitrary $p$,
acquisition is almost surely available and the call/request bounds for one
request are

$$
\mathbf E_pN_k=3k\le3h,\qquad
\mathbf E_p(N_k+k+1)=4k+1\le4h+1.
$$

**Proof.** Lemma 12.2 leaves exactly $M_k=S_k(p)$ and an empty reverse stack
at the restored source address $p$. Thus (12.2) can use its stated input
without a further observation or capability. If $d(p)\le h$, the signature
contains the complete ancestor list; companion Theorem 2.1 and
[V Theorem 121.3](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_V.md)
make its realization unique, so $r_k(S_k(p))=p$ and the representative law
is $\mathsf L_p$. If $d(p)>h$, the representative and $p$ lie in one
$S_k$-cell. The companion's
Theorem 5.1 gives whole-future TV at most $2^{-k}$, and its direct
same-signature finite-window bound (4.3) gives $b_k(T)$. Restriction to a
finite cylinder cannot increase TV, proving (12.3); the whole-future statement
is (12.4). At $T=0$, both restricted laws are the same point mass at the
initial observation, also agreeing with $b_k(0)=0$. The resumed conditional
heat law is $\mathsf L_p$ by Definition 12.1; the sampler has restored this
very source, rather than replaced it by the representative. That address
is used only for computation of a law. Lemma 12.2 supplies the call counts.
No independently realized source or post-prefix reset is used. $\square$

**Corollary 12.5 (accuracy target and growing acquired memory).** For a target
$0<\varepsilon<1$, choose

$$
h_\varepsilon=\left\lceil\log_2(1/\varepsilon)\right\rceil,\qquad
k_\varepsilon=\min\{h_\varepsilon,d(p)\}.
$$

The representative whole-future law has error at most $\varepsilon$, and
every task (12.2) inherits that bound. The expected **TryUp** count is at
most $3h_\varepsilon$; acquisition, return and one request together have
expected call/request count at most $4h_\varepsilon+1$.

The post-return data contain $k_\varepsilon$ newly acquired colours in
addition to $O(p)$ and no live reverse token. Acquisition has peak stack
length $k_\varepsilon$, and return reduces it to zero while retaining all
these colours. These are counts of logical entries, not of token bits or
simultaneous total memory. For fixed $m$, the new colour entries use a fixed
finite alphabet. Depth, budget/counter backing, phase, live token material,
current binding/permissions, transient readouts, request representation,
representative-search workspace and symbolic output backing remain separate
memory coordinates. Readout/input encoding, token material, representative
computation, symbolic integration/output arithmetic and scratch clearing are
additional work. These, sampler/clock installation and pause/resume work
are not included in
$4k_\varepsilon+1$; no total tariff or optimality is asserted. In particular
an opaque edge capability is not assumed to occupy a constant number of bits.
For fixed $\varepsilon$ the acquired prefix and peak token count are bounded
by $h_\varepsilon$, but the depth coordinate is unbounded over all starts,
and the displayed enumeration also uses unbounded address workspace.
This is neither a finite total alphabet nor a uniform finite-memory
all-cuts guarantee; companion Theorem 3.2 counts a different, static
auxiliary alphabet with $O$ already supplied.

**Proof.** Since $2^{-h_\varepsilon}\le\varepsilon$, (12.4) gives the claim,
and Lemma 12.2 gives the costs. If $d(p)<h_\varepsilon$, the zero-error case
of Theorem 12.4 applies. During acquisition every success appends one colour
to $R_j$ and one capability to $K_j$. During return every consumption removes
one capability without removing a colour. These exact list transitions prove
the entry counts and the post-return description; they imply no material
width bound for tokens or other fields. $\square$

**Convention 12.6 (independent meanings and exact limits).** In this bridge,
space is the actual ordered-tree current address exposed only through $O$ and
the local edge relation; time is the ordered sampler chronology and its unit
trial clock, distinct from the resumed passive heat time; boundary is the
current-source future-law query (12.2); memory during acquisition is the
actual colour data and live reverse stack, whereas prediction memory is the
post-return $M_k$ with the retained source binding and no reverse rights.
Only the data are arguments of the proved direction

$$
M_k\longrightarrow S_k(p)\longrightarrow\text{current-source forecast},
$$

with operational restoration supplied before prediction by consuming the
actual stack. The forecast does not recover that spent capability. Apart from the
proved exact-depth equality $r_{d(p)}(S_{d(p)}(p))=p$, no address output is part
of the task; for $k<d(p)$ no literal starting-address recovery is claimed. No
inverse from a forecast to $M_k$, no recovery of the full chronology or old
archive, and no mutual recovery of the four views is claimed. The
ordered-tree heat source remains countable and transient; finite
stationary unifilar synchronization and entire-past causal-state results do not
replace this contract. The static UniformSignatureCode and TrueJumpEndpoints
constructions supply signature coding and endpoint laws, not this acquired
sampler or its cost.

**Physical-installation boundary.** The mathematical proof assumes a local
direction sampler with independent $1/3$ trials, exact finite colour/depth
readout, a one-use same-edge return capability, and a quiescent acquisition
window. Installing such a sensor, preserving the token, and implementing its
trial clock are separate physical assumptions and costs. This sampler is an
alternative controlled interface to the source and differs from the original
passive heat apparatus; no claim says that passive heat supplies **TryUp**, a
pause, a return token, or exact online representative evaluation. The theorem
also does not provide a universal $\alpha/\beta$ reduction, a fixed-memory
all-cut guarantee, a full address or chronology archive, or a thermodynamic
price.

**Source and overlap statement.** In
[Geometry Continuation V](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_V.md),
Definition 120.3 supplies the fixed ordered recursion, Proposition 120.4 the
rate-three heat construction, Definition 121.1 the deterministic-start joint
path law, and Theorem 121.3 complete-ancestor address uniqueness. In the
[finite-joint companion](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_FINITE_JOINT_PREDICTION.md),
Definitions 1.1/1.3 fix this same source and $S_h$, Theorem 2.1 classifies
the stopped experiment, Theorem 3.2 supplies its static auxiliary code,
Theorems 4.1/5.1 give the very bounds used in (12.3)--(12.4), and
Definition 5.2 supplies the representative. Its Proposition 6.1's
fixed-budget nonclosure and Proposition 6.3's one-trace nonrecovery remain
unchanged: the present controlled trials are additional access, not one
passive trace. UniformSignatureCode supplies that existing static upper
code, and TrueJumpEndpoints classifies the complete family of finite
true-jump endpoint expectations; neither supplies acquisition, heat-path
query evaluation or a return operation. The exact source correspondences
here use their published statements at revision
3345740d7052863ebbf662b371054295e29e2aa7.

This finite-start volume's §§1--9 separately record their own static decoder,
whole-law bound, nonclosure and one-trace boundary for the five-mode source.
Its §§10--11 retain that finite stationary source, uniform hidden prior and
authentic-calibration/conditional-update contracts. This volume's Theorem 5.1
is a five-mode result; the ordered-tree bound used here is the companion's
Theorem 5.1. The source-specific synthesis here is `repo-derived`;
the elementary geometric waiting calculation, record/return method and
static prediction bounds are credited ingredients, not proposed novelties.

The directly relevant
[Atomic Generation Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md)
suppliers have the following exact overlap and differences.

| Supplier | Existing gain and hypotheses | Difference and remaining obligation in §12 |
| --- | --- | --- |
| AA §§19--21, especially Theorems 19.2, 20.3, 20.5 and 21.2 | On birth-typed LAB, a known actually allocated $\alpha$ seed grows by owned local $P/S$. Actual ancestral tapes record all generation events; framed recall/Next uses current backing and rights, prints a complete reply and returns to Ready. Supplemented geometry, causal/serial time and callable memory have exact task kernels and settled update agreement. | Here the source is the pre-existing infinite address tree at an unknown current placement. The acquired items are ancestor colours, not a journal of the observer's chosen growth. Return undoes the sampled navigation to the same unknown $p$; LAB Return restores service readiness/root cursor while preserving its growth. No implementation of either interface by the other, LAB chronology recovery, or four-way inverse follows. |
| AA §22 and §23 | Same-run located writes, tape/journal alternatives, backed requests, bindings, grants, output, cleanup and variable reference widths are already counted separately. Its own source comparisons credit NCR, PVC, PR57, PG and the storage atlases for acquisition, paid conversion and callable continuation on their installations. AA §23 also credits NativeFullSourceProducer's stationary acquisition of an unknown finite Native tree. | Generic acquired use, unknown-tree traversal and paid return are not missing capabilities invented here. The count $N_k+k+1$ is only this sampler's call/request coordinate, with the other resources expressly separated. Neither a better whole price nor a simulation of those Native menus is proved. |
| AA §35 | Adaptive LAB selection requires acquired local event-membership marks even with all selected side records; its correspondence installs these from the known seed and proves selected recall/Next use at completed marked cuts. | §12 has no event-selection predicate or old selected chronology. Its task input specifies a future-law cylinder, while the predictor's source-dependent data are only the acquired colours and depth. Acquiring a colour prefix does not recover omitted LAB membership, busy controller state or an unknown historical selection. |
| AA §40 | Source-legal residual control on growing LAB has an effective equality criterion when a finite address presentation and exact correspondence are supplied, and a stated undecidability boundary for general total address programs. Full replies, legal source actions and future successors remain part of that task. | The present fixed recursion is public, and a finite-level search selects a representative for an approximate heat-path law. This is not that exact residual-control minimization, an extractor for arbitrary program presentations or a transition-stable update of $M_k$ under resumed heat. AA's effective and negative results retain their original domains. |
| AA §46, with §§41--45 | Known-seed LAB with a finite public candidate installation family already has hidden-installation acquisition, exact self-contained future-task prediction and real subsequent use. Its depth-threshold family has sharp growth/request bounds, and its weaker program-presentation promise has a nonuniformity obstruction. | Unknown placement $p$ on a fixed infinite heat source is different from an unknown selector installation on a grown, known-seed LAB source. The present guarantee is approximate in the observed future-law metric, exact at acquired full depth, and assumes a new pause/local sampler/reverse interface. It proves none of those LAB price bounds anew and neither removes nor solves their unknown-seed, unknown-history, authority or original-Native obligations. |

After removing these supplied methods, the bounded additional correspondence
is precisely the actual-run invariant
$(x,R_j,K_j)=(a_j,S_j(p),K_j)$, its lawful return to
$(p,M_k,\varnothing)$, and the resulting use of the companion's same-cell
law bound for that restored source from only $M_k$. The formerly static
signature input is thereby obtained from one unknown placement under the
declared controlled interface, with an explicit acquisition-depth/error
and call-count relation. It does not assume an answer oracle or a supplied
address to cross that bridge. This is a source-specific acquisition-to-law
join, not a new geometric-waiting theorem, new static decoder, generic
converter or improvement over LAB's stronger exact four-view result on
its different task. It advances one acquisition/retained-use direction of
the common-process question without replacing its mutual-recovery standard.

The literature comparisons likewise preserve their hypotheses:
[Travers--Crutchfield, arXiv:1008.4182v3](https://arxiv.org/pdf/1008.4182v3)
studies synchronization of finite-state stationary unifilar sources by
observed output; [Shalizi--Crutchfield, cond-mat/9907176v2, Theorems 2--3](https://arxiv.org/pdf/cond-mat/9907176v2)
gives causal-state entropy minimality and almost-sure uniqueness in its
stationary entire-past setting. Neither hypothesis set supplies this
unknown-placement controlled tree acquisition; no synchronization rate,
entropy minimum or global novelty assertion is transferred.

The original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer,
unchanged-initialization, terminal and final-no-Ready obligations retain
their exact statements and settlements. Installing the sampler on the
passive or original Native apparatus, acquiring arbitrary unknown initial
archives, recovering chronology or all four views, maintaining bounded
memory at all cuts, and a universal $\alpha/\beta$ reduction remain
unresolved. The present conditional bridge does not complete that programme.

## 追加锚（本行以下为增补区）

## 13. A common acquired start for the original three-axis experiment

The calibration question in §§10–11 has a continuous-source counterpart:
what can one passive observer learn before its actual source dies, and what
true-source future law can it then return? Here the source is the
[three-axis interface, §§24–30](AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md),
not the five-mode chain. The source-specific result consists of the
preparation correspondence below, the complete-lifetime experiment of
§§14–15, and its live continuation consequence in §17. The generic
common-kernel and testing arguments are reused from
[Gaussian adaptive record kernel, §§2–4](RECURSIVE_RELATIONAL_OBSERVATION_GAUSSIAN_ADAPTIVE_RECORD_KERNEL.md).

**Assumption 13.1 (one unchanged source and one passive execution).** Use
three-axis Assumption 24.1 and Definition 27.4 at source revision
`da254d2c64fd05036726203ce2395a4b40f1a59b`. Thus the actual state is
$(q,h,k)\in\mathbb R^3\times\mathbb R^2$, the task reads $q$ with its
original Euclidean metric, the guard is exactly $q_3>0$, and the fields are

$$
\begin{aligned}
X_0&=(ce_2,0,1),&X_1&=(e_1+a\sin h\,e_2,1,0),\\
X_2&=(e_2,0,1),&X_3&=(e_3,0,0).
\end{aligned}
\tag{13.1}
$$

The fixed frequency, the whole-source analytic membership, coordinate
calibration, preparation bounds, read permissions, error $\epsilon>0$,
latencies and charges are premises, exactly as in that assumption. No
finite observation verifies membership. Preparation supplies bounds
$|q_i^p|\le R_0$, $q_3^p\ge H_{\min}>0$, $|h^p|\le\delta_h$ and
$|k^p|\le K_0$; it need not disclose the exact prepared coordinates.

Retain the first-read hold $\ell_0>0$, calibration hold $\tau_0$, named
$X_1$ pulse of duration $\tau_1$ and cumulative effort $U$, and reporting
hold $\Lambda$. They obey the original timing and effort certificates.
Write

$$
L_0=\ell_0,\quad L_1=\ell_0+\tau_0,\quad
L_2=\ell_0+\tau_0+\tau_1,\quad L_*=L_2+\Lambda,
\qquad U_0=U_1=0,\quad U_2=U_*=U.
\tag{13.2}
$$

All read, timing and computation durations remain in these original-clock
intervals. Following this acquisition, execute one fixed permitted SPD
covariance $Q$ from the original menu. It is never changed or selected using
the unknown parameter during this execution. In particular the original
menu permits the correlated setting
$Q=I_3+(E_{23}+E_{32})/2$; none of the proofs requires independent original
noise coordinates. During the passive phase there is no deterministic
hold, pulse, reset, fresh source or intervention on these fields. Permitted
nondestructive observations have the additional common-kernel contract of
§16. They do not pause the original clock or change the guard.

**Proposition 13.2 (an interval in one finite-record feasible set).** Fix
$a\ne0$ with $|a|\le A_0$, an interior $c_0\in(-C_0,C_0)$, common allowed
$q_1^p,z=q_3^p,h^p,k^p$, and an interior second prepared coordinate
$b\in(-R_0,R_0)$. Fix the actual controls and durations in (13.2). There
exist $\eta>0$, a nonempty open interval
$\mathcal C=(c_0-\eta,c_0+\eta)$, and an admissible parameter-independent
finite endpoint-report apparatus such that every $c\in\mathcal C$ has
the same complete acquired finite transcript and the same exact execution
state $(q_*,h_*,k_*)$. Its allowed prepared second coordinate is

$$
q_2^p(c)=b-(c-c_0)L_*.
\tag{13.3}
$$

The transcript includes all three vector reports, their common timing and
effort certificates, preparation-box and permission certificates, reporting
arithmetic and clock records, and original bills. For the billing claim
use the permitted instance $c_{\rm src}=c_Q=1$ with common finite
preparation, read, timing, command, arithmetic, retention and failure
prices. This is an explicit instance of the original contract; an
arbitrary informative price oracle is not covered.

**Proof.** Choose $\eta$ so that

$$
\eta<C_0-|c_0|,\qquad
\eta L_*<\min\{R_0-|b|,\epsilon/2\}.
\tag{13.4}
$$

The original exact acquisition equations give

$$
\begin{aligned}
q_1^{(j)}&=q_1^p+U_j,&q_3^{(j)}&=z,\\
q_2^{(j)}(c)&=b+c_0L_j
 +a[\cos h^p-\cos(h^p+U_j)]
 +(c-c_0)(L_j-L_*).
\end{aligned}
\tag{13.5}
$$

Thus (13.3) stays inside the same preparation box. At execution $L_j=L_*$
and $U_j=U$, so the last term vanishes. Also
$h_*=h^p+U$ and $k_*=k^p+L_*$ are common. The complete deterministic
prefix has $q_3=z>0$, so every sample and reporting hold is lawful.

For each second-coordinate endpoint let $m_j=q_2^{(j)}(c_0)$. Its entire
interval of alternatives has distance less than $\eta L_*<\epsilon/2$
from $m_j$. Choose a finite rational $R_j^2$ with
$|R_j^2-m_j|<\epsilon-\eta L_*$; choose common finite rational first
and third reports within $\epsilon$ of their common endpoints. Shrinking
$\eta$ if needed leaves strict slack in all these choices. One common
sensor can return these same reports on the corresponding endpoint
neighbourhoods. Outside them use a finite rational mesh covering the
original bounded acquisition range, with coordinate error at most
$\epsilon$. The sample index is a common retained apparatus state; no
branch tests $c$. This defines a parameter-independent, finite-output
sensor on the allowed acquisition domain, with the original error bound.
The two uses of the middle report use this one $R_1$.

Keep the same original preparation-box, permission, clock and effort
certificates and the same actual durations. Finite reporting arithmetic
therefore has identical inputs and outputs. Include its latency in
$\Lambda$. The constant-rate service integrals are equal over the common
complete durations; all separate original charges can be identical. No
charge has been dropped. This proves the full-record correspondence.
$\square$

**Boundary 13.3 (what this construction supplies).** This is a family of
allowed preparations, not the same-prepared-state pair of three-axis
Proposition 29.1. That earlier pair has different execution second
coordinates. Here (13.3) makes the execution states identical and varies
an unobserved prepared coordinate within its supplied bound. The
construction describes feasible actual sources; it does not give an
observer who lacks $c$ a preparation algorithm for (13.3). A uniform
claim over all sources permitted by the original bound must include
these sources. An authentic exact prepared-$q_2$ certificate, a sensor
that encodes $c$ in its output error, or an informative billing channel
changes the acquired experiment and must be included explicitly. The
coordinate-error inequality alone neither guarantees a common record for
every installed sensor nor gives the passive common-kernel premise.

## 14. The complete stopped experiment with correlated noise

**Definition 14.1 (the ideal converse observation).** On the family of
Proposition 13.2 put $\theta=h_*-q_{*,1}$ and $P(x)=a\cos(x+\theta)$.
Grant the observer the common exact $q_*,a,\theta,Q$, and the entire raw
path through its original death, including the continuous boundary limit.
This is the ideal observation $\mathcal O$; it is an information
enhancement for a converse. It is not a sensor or a record returned alive.
The execution time $t$ is elapsed time in the same original clock, whose
common preparation/acquisition offset remains retained.

By the source's Theorem 27.2, for Brownian motion with
$\operatorname{Cov}(W_s,W_t)=\min(s,t)Q$,

$$
\begin{aligned}
q_1(t)&=q_{*,1}+W_t^1,\\
q_2(t)&=q_{*,2}+ct+W_t^2+P(q_{*,1})-P(q_1(t)),\\
q_3(t)&=z+W_t^3,\qquad
\tau=\inf\{t\ge0:z+W_t^3=0\}.
\end{aligned}
\tag{14.1}
$$

There is no hidden exit. The actual hidden paths remain
$h(t)=h_*+W_t^1$, $k(t)=k_*+t+W_t^2$ for the original source and its
bill; they are not added observations.

Set $I=(1,3)$ in that order and define

$$
r=Q_{2I}Q_{II}^{-1},\qquad
\nu=Q_{22}-Q_{2I}Q_{II}^{-1}Q_{I2}>0.
\tag{14.2}
$$

For $0\le t\le\tau$ the following is a calculation on the granted path:

$$
X_t=q_2(t)+P(q_1(t))-q_{*,2}-P(q_{*,1})
 -r\binom{q_1(t)-q_{*,1}}{q_3(t)-z}.
\tag{14.3}
$$

Let $\mathbf P_c$ denote the law of $\mathcal O$ on the standard Borel
space of finite-lifetime continuous stopped paths. Probability total
variation is $\operatorname{TV}(P,Q)=\sup_A|P(A)-Q(A)|$.

**Theorem 14.2 (exact residual and complete-lifetime likelihood).** The
ideal experiment is equivalent by a parameter-independent invertible
path calculation to the stopped ancillary path $(W^1,W^3)_{[0,\tau]}$
and

$$
X_t=ct+\sqrt\nu B_t\quad(0\le t\le\tau),
\tag{14.4}
$$

where $B$ is a standard Brownian motion independent of the entire
ancillary Brownian path, hence independent of $\tau$. Almost surely
$0<\tau<\infty$. For every $c,d\in\mathcal C$,

$$
\frac{d\mathbf P_c}{d\mathbf P_d}(\mathcal O)
=\exp\left(\frac{(c-d)X_\tau-\tfrac12(c^2-d^2)\tau}{\nu}\right).
\tag{14.5}
$$

This is a normalized finite positive likelihood on the complete stopped
experiment, so the laws are equivalent. The pair $(\tau,X_\tau)$ is
sufficient; on this open parameter interval it is minimal sufficient up
to completion by common null sets.

**Proof.** Positive definiteness gives the inverse in (14.2) and its
positive Schur complement. The centered Gaussian process
$W^2-r(W^1,W^3)^{\mathsf T}$ has covariance $\nu\min(s,t)$.
Its covariance with either ancillary coordinate at any two times is
zero. Joint Gaussian finite-dimensional distributions and continuity
therefore make it $\sqrt\nu B$ independent of the full ancillary path.
Substitution in (14.1) proves (14.4). Conversely the ancillary path and
$X$ recover all raw coordinates by (14.3); this uses no unknown $c$.
The one-dimensional reflection formula for $W^3$ gives finite positive
$\tau$ almost surely, with its law calculated in §15.

Condition on the ancillary stopped path and its duration $\tau=t$.
Independence supplies a drifted Brownian path over a deterministic
interval of length $t$. Its endpoint has density
$\mathcal N(ct,\nu t)$. Given that endpoint, its centered bridge
$X_{ut}-uX_t$, $0\le u\le1$, is drift independent and independent of
the endpoint. Indeed at deterministic $t$ its mean is zero, its
covariance is $\nu t(\min(u,v)-uv)$, and its covariance with $X_t$
is zero. Thus the conditional path likelihood is just the ratio of the
two endpoint normal densities, namely (14.5). It integrates to one for
every ancillary path; integrating over their common distribution proves
(14.5) on the entire stopped experiment. No optional-stopping assertion
for an unbounded drift likelihood is needed.

Conditionally on $(\tau,X_\tau)$ one can sample the common ancillary
path conditional on $\tau$ and then the centered bridge just described.
These regular conditional laws exist on these standard Borel spaces and
are parameter independent. This proves sufficiency. For minimality fix
$d\in\mathcal C$ and $u>0$ with $d-u,d+u\in\mathcal C$. The two log
likelihoods against $d$ satisfy

$$
\log L_{d+u,d}+\log L_{d-u,d}=-u^2\tau/\nu,\qquad
\log L_{d+u,d}-\log L_{d-u,d}=2u(X_\tau-d\tau)/\nu.
\tag{14.6}
$$

For any sufficient statistic these likelihoods are measurable functions
of that statistic, by the dominated sufficiency criterion. Equations
(14.6) recover both $\tau$ and $X_\tau$. Together with sufficiency this
is the stated minimality. $\square$

**Corollary 14.3 (sufficiency is not archive recovery).** The sufficient
pair does not recover the full raw path. In particular, conditional on it
and on the ancillary stopped path,
$X_{\tau/2}-X_\tau/2$ has variance $\nu\tau/4>0$. A finite-alphabet
record cannot determine $(\tau,X_\tau)$ exactly, since conditional on
$\tau=t$ the latter coordinate has a non-atomic normal law. Its exact
real-valued sufficiency is not a finite-bit representation, a live
terminal report, a callable memory installation or a recovery of the
original chronology.

**Proof.** Use the bridge covariance in Theorem 14.2. Non-atomicity
excludes concentration on the finitely many possible decoded pairs of
any finite alphabet. $\square$

## 15. Exact boundary-dependent discrimination over the complete lifetime

**Lemma 15.1 (the original external killing clock).** For $t>0$ and
$s\ge0$ the common lifetime has

$$
\begin{aligned}
\Pr(\tau>t)&=2\Phi\left(\frac z{\sqrt{Q_{33}t}}\right)-1,\\
f_\tau(t)&=\frac z{\sqrt{2\pi Q_{33}}\,t^{3/2}}
 \exp\left(-\frac{z^2}{2Q_{33}t}\right),\\
\mathbb E e^{-s\tau}&=\exp\left(-z\sqrt{\frac{2s}{Q_{33}}}\right).
\end{aligned}
\tag{15.1}
$$

Also $\mathbb E\tau=\infty$, as already established in three-axis
Proposition 30.1.

Together with Theorem 14.2 this specifies the sufficient experiment
completely: its joint density, for $t>0$ and $x\in\mathbb R$, is

$$
g_c(t,x)=\frac{z}{2\pi\sqrt{Q_{33}\nu}\,t^2}
\exp\left(-\frac{z^2}{2Q_{33}t}-\frac{(x-ct)^2}{2\nu t}\right).
\tag{15.1a}
$$

**Proof.** Reflection of the one-dimensional Brownian coordinate at
$-z$ gives the survival formula; differentiation gives the density.
For the transform, when $s>0$ put $v=\sqrt{2s/Q_{33}}$.
The stopped process
$\exp(-v(z+W^3_{t\wedge\tau})-s(t\wedge\tau))$ is a bounded
martingale: the Brownian exponential has zero drift, and the stopped
vertical coordinate is nonnegative. Its expectation is $e^{-vz}$.
As $t\to\infty$, finite $\tau$ and continuity make it converge to
$e^{-s\tau}$. Bounded convergence proves the last formula; $s=0$ is
immediate. The survival formula tends to zero, proving a.s. finite
lifetime; continuity at zero gives strictly positive lifetime. Its
tail is bounded below by a positive multiple of $t^{-1/2}$ for all
sufficiently large $t$, whose integral diverges. Multiplying its density
by the conditional normal endpoint density in Theorem 14.2 gives
(15.1a). $\square$

**Theorem 15.2 (exact affinity, Bayes risk and minimax risk).** For the
complete ideal experiment the Hellinger affinity is

$$
A(\mathbf P_c,\mathbf P_d)
=\int\sqrt{d\mathbf P_c\,d\mathbf P_d}
=\exp\left(-\frac{z|c-d|}{2\sqrt{Q_{33}\nu}}\right).
\tag{15.2}
$$

For any $c_\pm=c_0\pm\delta\in\mathcal C$, $\delta>0$, put
$\kappa=z\delta/\sqrt{Q_{33}\nu}$. The exact equal-weight testing
risk and the exact binary minimax testing risk are both

$$
\begin{aligned}
e(\kappa)
&=\mathbb E\,\Phi\left(-\delta\sqrt{\tau/\nu}\right)\\
&=\sqrt{\frac2\pi}\int_0^\infty
 e^{-v^2/2}\,\Phi(-\kappa/v)\,dv
=\frac{1-\operatorname{TV}(\mathbf P_{c_+},\mathbf P_{c_-})}{2}.
\end{aligned}
\tag{15.3}
$$

In particular

$$
0<\frac{1-\sqrt{1-e^{-2\kappa}}}{2}
\le e(\kappa)\le\frac{e^{-\kappa}}2<\frac12.
\tag{15.4}
$$

The exact risk is strictly decreasing in $\kappa>0$, tends to $1/2$
as $\kappa\downarrow0$ and to zero as $\kappa\to\infty$.
The equal weights are a two-source decision comparison, not a prior
asserted for the unknown actual source.

**Proof.** Condition as in Theorem 14.2. At duration $t$, the ancillary
path and bridge carry no likelihood, while the normal endpoint affinity
is $\exp(-(c-d)^2t/(8\nu))$. Integrate this over $\tau$ and apply
(15.1), obtaining (15.2).

For the symmetric pair, (14.5) exceeds one precisely when
$X_\tau>c_0\tau$. The likelihood-ratio test therefore chooses plus on
that event. Conditional on $\tau=t$, either error equals
$\Phi(-\delta\sqrt{t/\nu})$. The threshold has zero equality mass.
This test minimizes the equal-weight error by choosing the larger
density pointwise. Its two errors agree, so its maximum error equals
its optimal average; every maximum is at least that optimal average.
This proves both optimalities and the first and last expressions in
(15.3). In the density integral substitute
$v=z/\sqrt{Q_{33}t}$ to obtain its middle expression.

For probability densities $p,q$, write their overlap as
$\int\min(p,q)=1-\operatorname{TV}(P,Q)$. It is at most their
square-root affinity. Cauchy–Schwarz applied to
$|p-q|=|\sqrt p-\sqrt q|(\sqrt p+\sqrt q)$ gives
$\operatorname{TV}(P,Q)\le\sqrt{1-A^2}$. Here $A=e^{-\kappa}$,
which proves (15.4). The integral in (15.3), with a positive half-normal
weight, proves strict monotonicity and both limits by dominated
convergence. $\square$

**Corollary 15.3 (what the boundary controls).** For the concrete original
correlated setting $Q=I_3+(E_{23}+E_{32})/2$, (14.2) gives
$r=(0,1/2)$, $\nu=3/4$ and
$\kappa=2z\delta/\sqrt3$. More generally the exact complete-lifetime
risk depends on $Q,z,\delta$ only through $\kappa$, with $Q$ fixed
throughout the run. A smaller starting boundary distance gives less
complete-lifetime discrimination at fixed $Q,\delta$. This is a
comparison of different allowed starts, not permission to move the
boundary or change covariance during observation.

Even this ideal experiment can meet a binary worst-error target
$0<\beta<1/2$ only if $e(\kappa)\le\beta$; a simpler necessary
condition is

$$
\frac{2z\delta}{\sqrt{Q_{33}\nu}}
\ge\log\frac1{4\beta(1-\beta)}.
\tag{15.5}
$$

**Proof.** Substitute the displayed $Q$ in (14.2); use monotonicity for
the boundary comparison. The lower bound in (15.4), followed by
squaring $\sqrt{1-e^{-2\kappa}}\ge1-2\beta\ge0$, proves (15.5).
$\square$

## 16. Actual passive acquisition, retention and calls

**Assumption 16.1 (the common causal observation contract).** Fix a single
installed observer on the family in Proposition 13.2. Its initial acquired
transcript is the common one constructed there. All of its later
observations, selected settings, reference identities, completed read
values, clocks, memory updates, backing accesses, bills, stopping and
outputs are generated by the same measurable causal rules from the
already elapsed raw path and independent common-law apparatus randomness.
Equivalently their complete record has a parameter-independent Markov
kernel $K$ from $\mathcal O$ to the record space. For live outputs we
require the causal realization of this kernel: decisions and records by
time $t$ use no raw path after $t$ and no future source-correlated random
input. An independent random seed can include future apparatus random
bits; it is independent of the entire source Brownian motion. Use standard
Borel record spaces. Finite physical controllers and their finite or
countably extended records are included when they satisfy this contract.
An arbitrary measurable kernel is an information relaxation, not an
installation assertion.

The contract includes every source-dependent channel used by a later
call, whenever that observation or call is actually permitted. It grants
no new read permission and requires no installed extra sensor for the
converse. In the rate-one instance it includes the integral of the actual
execution time, all fixed fees and any passive costs determined by acquired
history and raw path. Every original charge remains payable. A hidden
$k$-sensor, driver readout, source-bound authentic calibration label,
parameter-dependent read error, exact prepared-$q_2$ label, or a bill
revealing an additional hidden quantity need not satisfy this kernel
contract. Such a channel is additional information, even if named
“memory”, “reference” or “price”. Its presence must be checked on its
actual law. Error bounds and zero hidden metric length do not prove
parameter independence. Observations which perturb the source, active
recalibration, new preparations and covariance switches are other
experiments.

**Proposition 16.2 (complete-record and continued-call floor).** Under
Assumption 16.1, every binary decision made from the actual acquired and
retained record, including any number of permitted passive rereads and
record-only subsequent calls, satisfies

$$
\max\{\Pr_{c_+}(\text{failure}),\Pr_{c_-}(\text{failure})\}
\ge\frac{\Pr_{c_+}(\text{failure})+
          \Pr_{c_-}(\text{failure})}{2}
\ge e(\kappa)
\tag{16.1}
$$

when wrong decisions, death before return, abstention and nonreturn all
count as failure. In particular none can identify the exact $c$ with
zero error throughout $\mathcal C$. Unlimited retention of this one
passive experiment does not remove the floor. The ideal optimum (15.3)
is not asserted attainable by a live installed observer.

**Proof.** The actual record laws are $\mathbf P_{c_+}K$ and
$\mathbf P_{c_-}K$. The existing common-kernel data-processing argument
gives TV at most the input TV. Thus every total binary decision has
average error at least half the input overlap, which is $e(\kappa)$
by (15.3). Complete any failed-return decision by an arbitrary binary
answer; this can only decrease its total failure probability, so the
bound remains. Exact identification would decide this pair exactly,
contradicting the strictly positive floor. Retaining more of the same
path or applying further record-only kernels is still a kernel from
$\mathcal O$. $\square$

**Resource boundary 16.3.** The exact acquisition bill remains three-axis
(26.1), and its elapsed clock remains
$T_{\rm prep}+\ell_0+\tau_0+\tau_1+\Lambda$. Preparation, three actual
reads, timing/effort certificates, all arithmetic workspace and output,
command, source service and retained backing are counted once at their
original prices. Passive read latencies and call/evaluation latencies
continue the source clock; they are not free pauses. The execution bill
contains the original stochastic service integral, observation, command
where applicable, retention and failure charges. At rate one its full
service component is $\tau$, finite a.s. but of infinite expectation.
Consequently no finite expected complete-lifetime price follows from
a.s. death. Conversely paying this full service component still supplies
no installed full-path sensor. The sufficient pair of §14 consists of
exact reals, not a fixed number of physically stored bits. No total-cost
optimum, storage minimum or sensor construction is inferred from (16.1).

## 17. True-source future continuation after a live output

**Definition 17.1 (the returned continuation task).** A policy satisfying
Assumption 16.1 chooses a nonanticipating output time $S$, with
$S=\infty$ allowed, and attempts to return a family of probability
forecasts $D_n$ on the future raw endpoint, one for each integer
$n\ge1$. The successful output event $R$ requires $S<\tau$ and a
completed lawful return with all required backing and permissions.
Anything else is failure. The family is determined by the data acquired
at that output and independent apparatus randomness. A callable symbolic
family is included only insofar as its outputs are functions of that same
data and the request $n$. Future source observations are not arguments
of an already returned family. An observer may start another learning
and prediction episode, with a new live output and its own risk.

As a further converse enhancement grant the exact raw state $x=q_S$ on
$R$. At that state and fixed true $c$, the target for horizon $n$ is

$$
\mu_{c,x,n}(A)
=\frac{K_n^{\lambda_c,Q}(x,A)}{p_Q(n,x_3)},\qquad
\lambda_c=(a\cos\theta,a\sin\theta,c),\qquad
p_Q(n,x_3)=2\Phi\left(\frac{x_3}{\sqrt{Q_{33}n}}\right)-1>0.
\tag{17.1}
$$

Here $K$ is the original killed kernel of three-axis (27.5).
This is the true-source endpoint law conditional on survival for that
future horizon from that actual state. It is neither a posterior mixture
nor an unnormalized killed response. At each law, its own stated future
survival event is used. The source contract supplies fresh fixed-$Q$
Brownian increments at this lawful stopping time, as required by
three-axis Theorem 27.2. This is a Markov continuation premise, not a
reset or independent new source.

Let the all-horizon loss, including actual return failure, be

$$
\mathcal L_c=
\begin{cases}
\displaystyle\sup_{n\ge1}\operatorname{TV}(D_n,\mu_{c,q_S,n}),&R,\\
1,&R^c.
\end{cases}
\tag{17.2}
$$

Forecast kernels are measurable; on these standard Borel endpoint spaces
TV is a measurable supremum over a countable determining algebra, so the
countable supremum in (17.2) defines a measurable loss. No coherence or
self-generated-update requirement is imposed on $D_n$; any more
restricted continuing decoder is included.

**Lemma 17.2 (exact future separation at the same live state).** For every
$x_3>0$, every fixed $n>0$ and $c,d\in\mathcal C$,

$$
\operatorname{TV}(\mu_{c,x,n},\mu_{d,x,n})
=2\Phi\left(\frac{|c-d|\sqrt n}{2\sqrt\nu}\right)-1.
\tag{17.3}
$$

In particular this distance tends to one as $n\to\infty$ whenever
$c\ne d$, at every common live state $x$.

**Proof.** At this actual state use the parameter-independent endpoint
coordinate

$$
\psi_x(y)=y_2+P(y_1)-x_2-P(x_1)
-r\binom{y_1-x_1}{y_3-x_3}.
\tag{17.4}
$$

Under the true continuation it equals $cn+\sqrt\nu B_n$.
The future survival event depends on the entire future $W^3$ prefix,
which is independent of the entire residual $B$. Thus even after
conditioning on survival the transformed endpoint
$(y_1,y_3,\psi_x(y))$ has the product of a common ancillary endpoint
law and $\mathcal N(cn,\nu n)$. This transformation is invertible:
recover $y_2$ by solving (17.4). The TV distance is therefore exactly
that of the two one-dimensional normal shifts. Their densities cross
at $(c+d)n/2$, and integrating on either side gives (17.3).
Strong Markov justifies these same increments from $S$ on each live
output; no independence between $S$ and past source records is used.
$\square$

**Theorem 17.3 (complete-lifetime acquisition limits live continuation).**
For every policy in Definition 17.1 and the pair
$c_\pm=c_0\pm\delta\in\mathcal C$,

$$
\frac{\mathbb E_{c_+}\mathcal L_{c_+}
      +\mathbb E_{c_-}\mathcal L_{c_-}}2\ge e(\kappa),
\qquad
\max_{\varsigma\in\{-,+\}}\mathbb E_{c_\varsigma}\mathcal L_{c_\varsigma}
\ge e(\kappa).
\tag{17.5}
$$

For every $0\le r_0<1/2$ there is also the failure-probability bound

$$
\frac12\sum_{\varsigma\in\{-,+\}}
\Pr_{c_\varsigma}\left(R^c\ \text{or}\
 \sup_{n\ge1}\operatorname{TV}(D_n,\mu_{c_\varsigma,q_S,n})>r_0\right)
\ge e(\kappa).
\tag{17.6}
$$

On the open interval $\mathcal C$, every such common policy satisfies

$$
\sup_{c\in\mathcal C}\mathbb E_c\mathcal L_c\ge\frac12.
\tag{17.7}
$$

These are lower bounds on the declared continuation risks; no equality
with their optimal values for an installed observer is asserted.

**Proof.** Realize the common causal observer using the complete raw
stopped path and a seed $V$ independent of it. Its joint input law is
$\mathbf P_c\otimes\rho$ with the same seed law $\rho$ for all $c$.
All acquisitions, choices, return status, $S$, $x=q_S$ on return, and
the forecasts are the same functions of this canonical input. Compare
the two losses on one such input, not on separately coupled realized
outputs. On $R$, for each $n$ triangle inequality gives

$$
\operatorname{TV}(D_n,\mu_{c_+,x,n})+
\operatorname{TV}(D_n,\mu_{c_-,x,n})
\ge\operatorname{TV}(\mu_{c_+,x,n},\mu_{c_-,x,n}).
$$

Take the limit on the right in (17.3) and bound each term on the left
by its own supremum. Thus $\mathcal L_{c_+}+\mathcal L_{c_-}\ge1$
pointwise. On failed return both losses are one, so this inequality
persists. With $p_+,p_-$ denoting the two densities relative to a common
dominating input measure,

$$
\begin{aligned}
\mathbb E_{c_+}\mathcal L_{c_+}
+\mathbb E_{c_-}\mathcal L_{c_-}
&\ge\int\min(p_+,p_-)\,
           (\mathcal L_{c_+}+\mathcal L_{c_-})\\
&\ge\int\min(p_+,p_-)
=1-\operatorname{TV}(\mathbf P_{c_+},\mathbf P_{c_-})
=2e(\kappa).
\end{aligned}
$$

Tensoring with the common seed preserves input TV. This proves (17.5).
If both returned-family errors were at most $r_0<1/2$ on the same
input, their sum would be less than one, contradicting the pointwise
inequality. Hence at least one of the two failure indicators in (17.6)
is one on every input. Integrating against the same minimum density
proves (17.6). Finally choose symmetric distinct pairs with
$\delta\downarrow0$ inside $\mathcal C$. Their execution state,
height, covariance and observation rules stay fixed by Proposition
13.2. Equations (15.3) and (17.5) give (17.7). $\square$

**Boundary 17.4 (what continuation has and has not been obstructed).**
The theorem concerns a family returned at one lawful live cut and accurate
for the true source at every future integer horizon under each
survival-conditioned normalization. Endpoints alone already force the
bound, so predicting full normalized future paths with these marginals
cannot evade it. No assertion requires observing survival of a future
horizon before making the forecast. Small survival probabilities do not
remove those normalized queries. Death and nonreturn during acquisition
are counted, rather than conditioning them away or keeping only late
successful observers.

This does not contradict three-axis Theorem 28.3's horizon-uniform
unnormalized killed-response bounds or its Corollary 29.3's finite-horizon
conditional certificates. Multiplying (17.3) by the common survival
probability gives the unnormalized endpoint separation, which tends to
zero as the horizon grows. A fixed finite horizon, an error averaged over
survival or horizons, Bayesian posterior prediction, or later forecasts
using newly acquired data are distinct targets. The additional paid
sensor and growing finite-horizon interfaces are not assumed here.
Active recalibration and other generators are not ruled out by a
passive-experiment converse. No finite-memory or physical impossibility
for those different tasks follows.

## 18. Correspondence, attribution and unresolved recovery directions

**Definition 18.1 (independent views in this result).** Space exposes the
actual raw location $q$ and its Euclidean task metric, with the original
nonlinear source fields (13.1). Time is the ordered original acquisition
and execution clock, including all read/report latencies and the actual
killing time. Boundary has two separate meanings kept explicit: the
physical killing guard is $q_3=0$, while a returned predictive boundary is
the probability-family interface $D_n$ for the task (17.1). Memory is the
actually acquired and backed record used by the observer and subsequent
calls under Assumption 16.1. None of these is defined as an unrestricted
copy of the others.

The proved positive statistical direction is
$\mathcal O\longrightarrow(\tau,X_\tau)$ with exactly the same
$c$-likelihood information, and a parameter-independent conditional
reconstruction of its experiment. This is not reconstruction of the
realized path. The proved obstruction is from that maximal passive
acquisition to true-source all-horizon continuation, quantitatively
(15.3), (16.1) and (17.5)–(17.7). It identifies information that more
passive record storage alone cannot supply. No inverse from a future law
to an actually acquired archive, recovery of the hidden $k$, recovery of
the full chronology, four-view mutual recovery, or parsimonious universal
generator is proved.

**Source correspondence 18.2.** The original three-axis supplier is
[the complete volume at the stated source revision](https://github.com/the-omega-institute/trureturing/blob/da254d2c64fd05036726203ce2395a4b40f1a59b/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md).
Its Assumption 24.1 supplies exactly the source, finite preparation/read
contract and actual permissions in (13.1)–(13.2); Definition 26.1 supplies
all the charges retained here. Definition 27.4 and (27.9) supply the joint
acquisition equations used in (13.5). Theorem 27.2 supplies (14.1), fixed
calibration, the original continuous-prefix guard and the true killed
continuation kernel. Its §28 already uses the correlated Schur complement
for smoothing; that algebra is reused, with the whole residual Brownian
path identified here for the stopped acquisition experiment. Proposition
29.1 and Theorem 29.2 already obstruct prediction from the fixed three
reports, with a same-prepared-state pair and $Q=I_3$. They do not analyze
the information in all passive observations until the original death.
The added correspondence (13.3) instead produces a whole feasible drift
interval at one common execution state. The complete-lifetime likelihood,
exact boundary-dependent testing risk and live true-source continuation
risk consume that new correspondence. Proposition 30.1 already supplies
a.s. death with infinite expected rate-one service cost.

The generic full-record/data-processing/return-failure argument is supplied
by [Gaussian adaptive record kernel, §§2–4](RECURSIVE_RELATIONAL_OBSERVATION_GAUSSIAN_ADAPTIVE_RECORD_KERNEL.md),
on its different same-specimen quantum pointer model. No spectral pointer,
fresh mode, QND instrument, adaptive-word Gaussian formula or sensor
installation is transferred. The repository declarations
`EquivalentMeasuresExcludePerfectSeparator.equivalent_probability_laws_exclude_perfect_separator`
and
`EquivalentLawPosteriorInterior.equivalent_law_posterior_stays_interior` in
`D5/S3/Observer/MeasureSeparation/` give the generic measure-equivalence
and posterior-interiority background with their owning Scribes. They
supply no numerical boundary constant or source-specific acquisition law.
The natural ownership/factorization principle is already the three-axis
volume's Definition 1.1 and this volume's calibration/update contracts;
it is not new content here. The natural-time bounded stopping/moment
result `StoppedLikelihoodAbsorption.stopped_likelihood_bounds` and the
strictly positive finite-alphabet `SequentialHellingerLocalization`
trajectory results retain their respective domains; neither substitutes
for (14.5)'s continuous complete stopped-path proof. Reading these sources
is not a current Lean build or certification of this application.

[Stopped-episode calibration unidentifiability, §§1 and 3](RECURSIVE_RELATIONAL_OBSERVATION_STOPPED_EPISODE_CALIBRATION_UNIDENTIFIABILITY.md)
already compares an entire original stopped episode and an enhanced
returned-cut-label experiment, with all legal adaptive prefixes obtained
by common postprocessing. Its source is the once-drawn common Fibonacci
depth and finite-letter native control, and its bound uses repeated
private-label blocks. The full-episode converse method is therefore also
an existing supplier. Its source law, label access and numerical constant
are not this nonlinear diffusion's stopped drift experiment or (15.3).

This volume's §§10–11 concern the finite five-mode chain, common positive
finite-word support and authentic calibration. They give no automatic
identification with the diffusion. The independently published
[§12 at revision 3fde9266017c1b3c3bb5fe90338f86335371f90b](https://github.com/the-omega-institute/trureturing/blob/3fde9266017c1b3c3bb5fe90338f86335371f90b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_FINITE_START_PREDICTIVE_MEMORY.md)
uses a different ordered-tree source with paused heat time, TryUp and
same-edge return rights. Its acquisition and restored-source forecast
are constructive under that additional interface. The
[native central-noise Green volume at revision 7913370b9ad5546da41bfd96c07ffb7179940ad4](https://github.com/the-omega-institute/trureturing/blob/7913370b9ad5546da41bfd96c07ffb7179940ad4/docs/develop/theory/FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md)
uses native fields on a double-wall cylinder, a different noise generator
and a declared acquired paid interface. Its occupation/Green estimates
are not stopped unknown-drift likelihoods. Neither source supplies the
missing sensor or pause to this original three-axis passive apparatus.
The NCR/PVC/PR57/PG/Atlas acquired-service results likewise keep their own
sources, rights and resource orders; this is no new generic conversion,
quotation mechanism or improvement of their prices.

**Literature scope 18.3.** Reflection, Gaussian regression and bridge
sufficiency, Brownian drift likelihoods, affinity, binary testing and
common-kernel contraction are mature suppliers. For the directly used
Brownian facts, see Mörters–Peres,
[*Brownian Motion*](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf),
Chapter 2, Theorems 2.14 and 2.18 for strong Markov and reflection, and
Lalley, [*Brownian Motion* notes](https://galton.uchicago.edu/~lalley/Courses/385/BrownianMotion.pdf),
§§2.1, 2.4 and 4–5, especially §5.3 and formula (59) for first passage.
The transform needed here is also derived in Lemma 15.1 with the explicit
variance rate; no ambiguous extracted coefficient is used as a premise.
The standard Gaussian drift likelihood has the correspondence
$X/\sqrt\nu=(c/\sqrt\nu)t+B$; the stop is the independent external
vertical-boundary time, not a chosen test stopping rule for that signal.

Ekström–Vaicenavicius,
[*Bayesian sequential testing of the drift of a Brownian motion*,
arXiv:1509.00675v1](https://arxiv.org/pdf/1509.00675v1), §§1–2 and
§3.1, Proposition 3.1 and its proof, treats an independent random drift
prior, normal likelihood sufficiency and sequential decision with a time
cost. Those mature likelihood ideas are used; its Bayesian prior,
optimal stopping boundary and cost are not asserted for the present
external killing clock. Brown–George–Xu,
[*Admissible predictive density estimation*, arXiv:0806.2914v1](https://arxiv.org/pdf/0806.2914v1),
§§1–2, uses independent Gaussian prediction and KL risk, a different
future task from (17.1)–(17.2). Campbell–Engelund,
[*Embedding martingale diffusions as binary posteriors in sequential
inference*, arXiv:2607.20373v1](https://arxiv.org/pdf/2607.20373v1),
§2.1, treats observation killed at the signal's own interval exit and
its local likelihood/energy conditions. Here killing depends only on
an independent ancillary coordinate after regression; its likelihood
is proved by conditioning. No theorem from either different prediction
or stopped-signal model is silently applied.

**Status 18.4 (the exact additional result and the remaining programme).**
The source-specific preparation/full-lifetime/continuation join of
§§13–17 is `repo-derived`, with ordinary proofs; the Brownian and
statistical suppliers above are `literature-attested`. The claim is this
explicit application and its quantitative dependence on the original
boundary and covariance, not global mathematical originality. No
physical realization, empirical validation, new Lean result or completed
formalization is claimed.

The common-kernel, nondestructive-sensor, source-membership and fresh
increment premises must be supplied for any actual installation to which
the bounds are applied. Installing live sensors or finite-bit callable
sufficient memory, handling informative hidden channels, constructing
active-learning alternatives and proving their resource guarantees remain
separate obligations. Original fixed-$G_{\rm gc}$, original-$Q$,
parked-consumer, unchanged-initialization, terminal and final-no-Ready
obligations retain their original scopes and settlements. Other sources,
Bayesian tasks and growing finite-horizon tasks are not rejected by this
converse. The four-expression common-process objective, unknown-archive
acquisition, positive mutual recovery and any universal $\alpha/\beta$
reduction remain unresolved. This bounded result does not complete that
programme.

## 追加锚（本行以下为增补区）

## 19. Observable-return acquisition on the original five-mode stream

**Assumption 19.1 (one unknown source and completed-cut queries).** Use precisely Assumptions 1.1 and 10.1 without an authentic parameter label. One fixed unknown $\vartheta=(p,q,r)\in\mathfrak A$ governs the whole run, $X_0\sim\pi$, and every $Y_0,Y_1,\ldots$ is read chronologically through the original $\chi$. There is no prior on $\vartheta$, reset, hidden-state read, chosen transition, independent sampling port or announced true law. Put

$$
c=1-p-q-r,\qquad s=p+q,\qquad
\xi_\vartheta=(c,p,q,r)
\tag{19.1}
$$

in visible order $(0,1,3,B)$. A departure from $0$ means one transition whose departure state is $0$, including the self-transition $0\to0$. Queries in §§20–21 concern completed acquired cuts after the sampling stop, and predict symbols strictly after that cut. They impose no precompletion accuracy requirement. All earlier initialized, every-positive-history and all-horizon contracts keep their original quantifiers.

**Definition 19.2 (observable sampling and the retained parser).** Define

$$
S_1=\inf\{t\ge0:Y_t=0\},\qquad
S_{k+1}=\inf\{t\ge S_k+1:Y_t=0\},\qquad
Z_k=Y_{S_k+1}.
\tag{19.2}
$$

For an installed integer $n\ge1$, stop acquiring calibration samples at $T_n=S_n+1$, immediately after recording $Z_n$. No additional wait or read is imposed to complete the return at $S_{n+1}$. If $Z_n=0$, departure and return already coincide at that final acquired symbol. Read every intervening symbol, including the initial read and every symbol in the search for the first $0$ and in subsequent returns. Retain four category counts $K_y$, incrementing $K_y$ exactly when the previous read was $0$ and the newly read symbol is $y$, until their sum is $n$.

The source-independent pure-mode update is the supplied total parser

$$
u(i,j)=j\quad(j\in\{0,1,3\}),\qquad
u(i,B)=\begin{cases}4&i\in\{0,4\},\\2&i\in\{1,2,3\}.\end{cases}
\tag{19.3}
$$

During acquisition add an unsynchronized tag $\bot$, with $u(\bot,B)=\bot$ and $u(\bot,j)=j$ for singleton $j$. It does not claim a posterior before the first singleton and stores no startup length. The first read has no preceding departure and increments no count. At the stop the mode is pure: it is $0,1,3,4$ when $Z_n$ is respectively $0,1,3,B$. Thereafter use the same $u$ on every actual input, regardless of its forecast probability. This is the pure restriction of Theorem 2.2, not a new source-identification rule.

**Theorem 19.3 (actual categorical samples and the exact mean acquisition clock).** For every strict $\vartheta$ and integer $n\ge1$, all times in (19.2) needed for $T_n$ are finite almost surely, and $(Z_1,\ldots,Z_n)$ has product law $\xi_\vartheta^{\otimes n}$. The literal number of calibration reads and hidden transitions on that same run are

$$
R_n=T_n+1=S_n+2,\qquad R_n-1,
\qquad
\mathbb E_\vartheta R_n=g(\vartheta)+5n-3,
\tag{19.4}
$$

where

$$
g(\vartheta)=\frac15\left(
\frac2{p+q}+\frac{4(p+q)}{p^2+q^2}+\frac1r\right).
\tag{19.5}
$$

The count vector has the ordinary four-category multinomial law with sample size $n$. Neither a finite deterministic deadline nor a uniform mean read bound over $\mathfrak A$ is supplied by a fixed sample size.

*Proof.* The event $Y_t=0$ is exactly $X_t=0$. Thus the $S_k$ are observable stopping times, also stopping times for the hidden chain. Reuse the finite irreducibility and uniform stationarity verified in Theorem 10.2. Finite-state recurrence makes their required visits almost surely finite. The strong Markov property, in Levin–Peres–Wilmer, *Markov Chains and Mixing Times*, second edition, Appendix A.3, Proposition A.19, gives conditional distribution $\xi_\vartheta$ for $Z_k$ given the entire history through $S_k$. Every earlier sampled $Z_l$, $l<k$, is measurable at $S_k$, including the case $S_k=S_{k-1}+1$ after a self-transition. Iterating these conditional probabilities gives the product law. This conclusion does not make the intervening visible symbols independent or make excursion lengths independent of their departure samples.

For the initial wait let $h_i=\mathbb E_i\inf\{t\ge0:X_t=0\}$. The finite irreducible chain has finite hitting means. Its first-step equations, with $h_0=0$, give

$$
s h_1=1+p h_2,\qquad
s h_2=1+q h_1+p h_3,\qquad
s h_3=1+q h_2,\qquad h_4=1/r.
$$

Consequently $h_2=2s/(p^2+q^2)$ and $h_1+h_3=2/s+h_2$. Averaging the five initial states yields $\mathbb E_\vartheta S_1=g(\vartheta)$. Proposition 1.19 of the same primary reference gives mean strictly positive return time $1/\pi(0)=5$, with self-returns included. Apply strong Markov at each $S_k$ and sum the $n-1$ completed return lengths to get $\mathbb E S_n=g+5(n-1)$. The final departure consumes one transition and its read; the initial symbol consumes one read. Hence $R_n=S_n+2$ and (19.4) follows. No $n$th complete-return length is added.

For every finite $L$, the event $X_0=4$ followed by at least $L$ holds at $4$ has positive probability $(1-r)^L/5$ and postpones the first observed $0$. There is therefore no deterministic calibration deadline. Also $g\ge1/(5r)$ diverges as $r\downarrow0$ with fixed admissible $p,q$. This proves the asserted nonuniformity, even though each fixed-source mean in (19.4) is finite. The iid sample law gives the multinomial count law directly. $\square$

## 20. C: finite-catalogue selection and risky exact continuation

**Definition 20.1 (installed catalogue and deterministic selection).** Install an ordered catalogue of $M\ge2$ distinct rational strict triples

$$
\Theta_C=(\vartheta^1,\ldots,\vartheta^M),\qquad
\Delta=\min_{j\ne k}\|\vartheta^j-\vartheta^k\|_\infty>0.
\tag{20.1}
$$

The actual source is promised to be one member $j$, whose index is unknown. Catalogue membership and the common source/read interface are premises, not conclusions of the sampling. For $N\ge1$ samples from Definition 19.2 set

$$
\widehat\vartheta(K)=(K_1,K_3,K_B)/N,\qquad
A_N(K)=\min\mathop{\rm argmin}_{1\le k\le M}
\|\widehat\vartheta(K)-\vartheta^k\|_\infty.
\tag{20.2}
$$

The minimum index resolves every tie. After selection retain only $\widehat j=A_N(K)$ and the current pure mode $i$. Consult the installed rows for $\vartheta^{\widehat j}$, use $u$ for actual mode updates, and decode the complete row-product law $F_{\vartheta^{\widehat j},i}^h$. The selected index stays fixed. Calibration counts can be erased after this installation has completed. No true-member label is received.

**Theorem 20.2 (exact finite risk and one all-future success event).** For each actual member $j$ define the rational finite sum

$$
R_j(N)=
\sum_{\substack{k_0+k_1+k_3+k_B=N\\k_y\ge0}}
\frac{N!}{k_0!k_1!k_3!k_B!}
\prod_{y\in\mathcal A}(\xi_{\vartheta^j,y})^{k_y}
\mathbf1_{\{A_N(k)\ne j\}}.
\tag{20.3}
$$

Then $\mathbb P_j\{\widehat j\ne j\}=R_j(N)$ and

$$
R_j(N)\le\frac3{N\Delta^2}.
\tag{20.4}
$$

For any $0<\delta<1$, the choice $N=\lceil3/(\delta\Delta^2)\rceil$ gives $0<R_j(N)\le\delta$. Write $a_t=Y_0\cdots Y_t$ and let $i_t$ be its retained pure mode after calibration. On almost every completed run,

$$
\begin{aligned}
L_C&=\sup_{t\ge T_N}\ \sup_{h\ge1}
\operatorname{TV}\left(F_{\vartheta^j,a_t}^h,
F_{\vartheta^{\widehat j},i_t}^h\right)
=\mathbf1_{\{\widehat j\ne j\}},\\
\mathbb P_j\{L_C=0\}&=1-R_j(N).
\end{aligned}
\tag{20.5}
$$

On this single success event, laws are exact at every later acquired cut, every finite horizon and every source-legal finite continuation of the completed calibration word. Each decoder is generated by its own normalized rows and the same total retained update.

*Proof.* Theorem 19.3 gives exactly the count masses in (20.3); no chronological-length weighting is added. If all three empirical coordinates differ from their true coordinates by less than $\Delta/2$, the true member is strictly nearer than every other member in (20.2). Thus a wrong selection implies at least one coordinate deviation of size at least $\Delta/2$. Each coordinate is the average of $N$ iid Bernoulli indicators and has variance at most $1/(4N)$. Chebyshev's inequality bounds each such deviation by $1/(N\Delta^2)$, and the union of these three events proves (20.4), including selection ties.

At $T_N$ a $0$ has already been observed. The supplied pure-history classification, conditional-law identity and total parser in §§1–2 identify the true future law after each later positive word as $F_{\vartheta^j,i_t}$. The supplied pure row-product identity gives the installed decoder. If $\widehat j=j$ the two are equal for all modes and all horizons, independently of what later observations occur. If $\widehat j\ne j$, Theorem 10.2 gives profile distance one between the two strict-parameter pure laws at every mode. Its hypotheses apply because each pure mode has a positive witness under each catalogue member, and its conclusion compares any positive acquired histories. Therefore already at $T_N$ the supremum over finite horizons is one. TV never exceeds one, proving (20.5). This is a supremum statement, not a claim of unit distance at a particular finite horizon.

For strict positivity of the residual error fix $k\ne j$. The bound just proved under source $k$, with $\delta<1$, ensures positive probability of selection $k$ there. Since the count set is finite, at least one count vector selecting $k$ has positive mass. All four entries of every $\xi_{\vartheta^j}$ are positive, so that same vector has positive mass under $j$. Hence $R_j(N)>0$. Almost-sure completion and countability of finite terminal words also give an actual finite positive terminal transcript with that wrong selection. No zero-error certificate is produced. $\square$

**Corollary 20.3 (the original worst-history boundary is preserved).** Under the stated sample choice, the observer succeeds in exact continued prediction with probability at least $1-\delta$ separately for each promised member, without a prior. It does not satisfy the initialized uniform requirement of Definition 11.1 at any tolerance below one over this unknown catalogue.

*Proof.* The probability statement is (20.5). A positive terminal history selecting the wrong member exists by Theorem 20.2; at that history the all-finite-horizon error supremum is one. This violates the old every-positive-history requirement, irrespective of how rare the terminal history is. Theorems 10.5 and 11.3–11.6 already supply the general zero-error and compatible-update obstructions; their proofs and their authentic-supply hypotheses are unchanged. $\square$

## 21. D: continuous unknown calibration with a capped future horizon

**Definition 21.1 (retained empirical kernel, including zero entries).** Here the actual $\vartheta$ is any member of the full strict real domain $\mathfrak A$; no catalogue or rationality of the source is assumed. For $m\ge1$ actual departures retain $K=(K_0,K_1,K_3,K_B)$, with sum $m$, and put

$$
v=(v_0,v_1,v_3,v_B)=K/m.
\tag{21.1}
$$

Freeze these counts at $T_m$ and continue updating the pure mode by (19.3). Substitute $(\widehat p,\widehat q,\widehat r)=(v_1,v_3,v_B)$ and $\widehat c=v_0$ into the supplied five pure rows. In visible order $(0,1,3,B)$ these are

$$
\begin{aligned}
g_{v,0}&=(v_0,v_1,v_3,v_B),\\
g_{v,1}&=(v_3,v_0+v_B,0,v_1),\\
g_{v,2}&=(0,v_3,v_1,v_0+v_B),\\
g_{v,3}&=(v_1,0,v_0+v_B,v_3),\\
g_{v,4}&=(v_B,0,0,v_0+v_1+v_3).
\end{aligned}
\tag{21.2}
$$

They are nonnegative and normalized on the whole closed four-simplex. Define $Q_{v,i}^0(\varnothing)=1$ and, for every complete word,

$$
Q_{v,i}^{h+1}(yw)=g_{v,i}(y)Q_{v,u(i,y)}^h(w).
\tag{21.3}
$$

This is the supplied same-update generator applied to these rows. Actual reads with $g_{v,i}(y)=0$ still invoke $u(i,y)$ and still have queried successors. There is no division by an empirical forecast mass and no deletion of such actual inputs.

**Theorem 21.2 (complete-word error from the observable empirical row).** For every strict $\vartheta$, every $v$ in the closed four-simplex, every mode $i\in\{0,1,2,3,4\}$ and every integer $h\ge0$,

$$
\operatorname{TV}(Q_{v,i}^h,F_{\vartheta,i}^h)
\le\sqrt{\frac{hD(v\Vert\xi_\vartheta)}2},\qquad
D(v\Vert\xi)=\sum_{y:v_y>0}v_y\log\frac{v_y}{\xi_y}.
\tag{21.4}
$$

Logarithms are natural, and a zero numerator contributes zero. All $4^h$ word entries, including zero entries, occur in the TV. The right side may be replaced by its minimum with one.

*Proof.* The source-specific correspondence to the mature product-law tools is explicit. Use driver labels $C,P,Q,R$ with law $(c,p,q,r)$, and the following deterministic next-state table, whose rows are current modes and whose columns are driver labels:

$$
\begin{array}{c|rrrr}
&C&P&Q&R\\\hline
0&0&1&3&4\\
1&1&2&0&1\\
2&2&3&1&2\\
3&3&0&2&3\\
4&4&4&4&0
\end{array}.
\tag{21.5}
$$

Following this table from mode $i$ and reading each successor through $\chi$ defines one parameter-independent map $\Phi_{i,h}$ from driver words of length $h$ to visible words of length $h$. With driver law $\xi_\vartheta$, its hidden transitions are the literal matrix of Assumption 1.1. With driver law $v$, its visible rows are (21.2). For every possible table step the visible successor updates the current mode by $u$; thus the pushforwards of $\xi_\vartheta^{\otimes h}$ and $v^{\otimes h}$ are respectively $F_{\vartheta,i}^h$ and (21.3). This verifies the parameter correspondence without asserting that the observer reads the drivers.

Apply the existing finite-channel TV contraction to this deterministic map. Apply the existing finite Pinsker inequality to the driver product distributions. Its absolute-continuity hypothesis holds because every coordinate of $\xi_\vartheta$ is positive; no positivity of $v$ is required. Product KL additivity gives

$$
D(v^{\otimes h}\Vert\xi_\vartheta^{\otimes h})
=hD(v\Vert\xi_\vartheta).
$$

Indeed on the support of $v^{\otimes h}$ the logarithm of the product ratio is the sum of the $h$ coordinate log ratios; summing each coordinate against the normalized remaining factors gives the displayed identity. Outside that support its contribution is zero. The finite Pinsker and channel inequalities now give (21.4), with the same argument at zeros and the trivial empty-word case at $h=0$. The reused declarations are `TotalVariation.DataProcessing.total_variation_channel_le` and `TotalVariation.Pinsker.pinsker_inequality`; their hypotheses, normalization and proofs are not new results here. $\square$

**Theorem 21.3 (one acquisition event controls every later capped query).** Fix an integer $H\ge1$, a real $\epsilon>0$ and a real $0<\delta<1$. Take

$$
m=\left\lceil\frac{3H}{2\delta\epsilon^2}\right\rceil
\tag{21.6}
$$

actual departures using Definition 19.2. For each strict real source $\vartheta$, the acquisition event

$$
E_\vartheta=\left\{D(K/m\Vert\xi_\vartheta)
\le\frac{2\epsilon^2}{H}\right\}
\tag{21.7}
$$

has probability at least $1-\delta$. On that one event, simultaneously for all five modes and all $0\le h\le H$, the error in (21.4) is at most $\epsilon$. In particular, for every later acquired cut $t\ge T_m$ and every source-legal finite continuation of its completed calibration history,

$$
\operatorname{TV}(F_{\vartheta,a_t}^h,Q_{K/m,i_t}^h)
\le\epsilon\qquad(0\le h\le H).
\tag{21.8}
$$

There is no additional failure probability for the number of later queries or for their adaptation to previously acquired reports. This is not an all-horizon or exact-parameter conclusion.

*Proof.* Reuse the iid categorical count law of Theorem 19.3. For a fixed positive four-vector $\xi=\xi_\vartheta$, the elementary log bound $\log x\le x-1$, applied only where $v_y>0$, gives

$$
\begin{aligned}
D(v\Vert\xi)
&\le\sum_y\frac{(v_y-\xi_y)^2}{\xi_y},\\
\mathbb E_\vartheta\sum_y\frac{(K_y/m-\xi_y)^2}{\xi_y}
&=\frac1m\sum_y(1-\xi_y)=\frac3m.
\end{aligned}
\tag{21.9}
$$

For the first line, the sum obtained directly from the log bound is $\sum_y v_y^2/\xi_y-1$, equal to the displayed sum by normalization; zero $v_y$ cause no missing term. For the second line use the Bernoulli variance $\xi_y(1-\xi_y)/m$ separately in each coordinate. Independence between the four coordinates is not asserted or needed. Markov's inequality gives

$$
\mathbb P_\vartheta\left\{D(v\Vert\xi_\vartheta)
>2\epsilon^2/H\right\}
\le\frac{3H}{2m\epsilon^2}\le\delta.
$$

On its complement Theorem 21.2 is a deterministic simultaneous bound for every mode and every capped horizon. The supplied true conditional-law identity and parser identify the actual future at every positive acquired continuation with its pure-mode law. The same $v$ is retained while the mode is updated, so this single deterministic bound applies after every such continuation, including ones assigned zero probability by an earlier empirical forecast. No union over future histories, times or queries is taken. The probability lower bound refers to the original acquisition experiment under each fixed source; it is not a claim of the same probability conditional on every rare acquisition history. Event (21.7) uses the unknown true $\xi$ for analysis and is not an observer-computable certificate. $\square$

## 22. Whole configurations, retained calls and resources on one run

**Definition 22.1 (resource and input conventions).** A calibration run consists of its actual $R_n$ chronological reads, the subsequent selection or empirical installation, and any specified $k$ further chronological reads and requested captured-cut outputs. The integers $n$, the catalogue in C, and the horizon cap $H$ in D are installed static inputs. The formulas for $N$ and $m$ hold for real design tolerances mathematically. An effective installation takes those integers directly, or computes them from rational $\delta,\epsilon$ and, for C, the rational catalogue and its rational separation. Exact ceiling or comparison against an arbitrary real name is not part of the interface. The unknown continuous triple in D is never supplied numerically.

Static programs, tables and input descriptions, mutable complete configurations, temporary arithmetic/query workspace, numeric output, and physical backing are separate coordinates. Charging only configuration names does not make the other coordinates free. The sampling controller and pure parser have a constant-size rule table; installing $n$ takes $O(\log(n+1))$ static bits, and installing D's cap additionally takes $O(\log(H+1))$ bits. C's catalogue storage is charged in Proposition 22.3. Design-tolerance descriptions, if still consulted, are also static backing. They may instead be discarded after the sample-size integer has been installed.

A captured-cut call copies the retained parameter representation and mode at a completed read boundary, and returns that cut's complete law for the requested horizon. At the sampling cut, C can capture $K$ and its mode first and compute (20.2) before answering; after selection it need only capture the selected index and mode. If selection finishes after further actual reads, the live mode continues to update while this captured mode remains fixed. Keeping that extra snapshot is additional query workspace. No law is promised for the physical state at the later instant when computation finishes. The source has not been reset, copied or stopped.

**Proposition 22.2 (sufficient finite retention and literal streaming charges).** For either consumer, at sample size $n$ one sufficient acquisition configuration contains the six-valued parser tag, four counts in $\{0,\ldots,n\}$, a sample-total counter in that same range, and a fixed finite control phase. No chronological-age counter or stored visible archive is needed. With $b_n=\max\{1,\lceil\log_2(n+1)\rceil\}$, this uses at most

$$
5b_n+O(1)
\tag{22.1}
$$

mutable naming bits before selection/query workspace. A sufficient postinstallation C carrier is $(\widehat j,i)\in\{1,\ldots,M\}\times\{0,\ldots,4\}$, with $5M$ nominal configurations. A sufficient postinstallation D carrier is $(K,i)$ with $\sum_y K_y=m$, at most $5\binom{m+3}{3}$ nominal configurations, or $4b_m+O(1)$ bits using four ordinary count registers and a mode tag. These are upper bounds, not sharp whole-system storage minima.

On one realized run through $k$ later acquired symbols the source charges are exactly

$$
\begin{array}{c|c}
\text{chronological reads}&R_n+k\\
\text{hidden transitions since initialization}&R_n+k-1\\
\text{one-symbol streaming updates}&R_n+k\\
\text{category-count increments during calibration}&n\\
\text{sample-total increments during calibration}&n
\end{array}
\tag{22.2}
$$

in addition to selection, calls and physical service charges. In particular their mean calibration read count is (19.4), with $n=N$ or $m$ as appropriate.

*Proof.* Start all counts and the total at zero and the parser at $\bot$. A read increments its category and the total exactly when the previous parser tag is $0$ and the total is below $n$, then updates the parser. The first read, whose previous tag is $\bot$, cannot be counted. The total reaches $n$ exactly at $T_n$. All five integer fields are bounded despite an arbitrarily long wait, proving (22.1). The invariant in Definition 19.2 identifies the actual mode and the sample counts, and the installed stopping comparison uses only the bounded total. Erasing C's counts after selection leaves precisely its index and mode; D freezes its counts. Their stated updates do not consult an erased field. The number of nonnegative quadruples of sum $m$ is $\binom{m+3}{3}$, giving the D bound. Hypothetical generated words also stay in these postinstallation carriers because $u$ is total.

Every actual read invokes exactly one streaming update. Each of the $n$ sampled transitions increments exactly one category and the total; all other observed transitions are still read and processed. A read sequence beginning at $Y_0$ and ending after $R_n+k$ symbols spans $R_n+k-1$ hidden transitions. This proves (22.2). An external analysis counter for those charges is not an input to the observer. If that counter is itself retained for billing, its storage and increments are additional resources. $\square$

**Proposition 22.3 (effective selection and complete rational law output).** Suppose C's catalogue member $j$ is presented as an integer triple $(P_j,Q_j,R_j)/d_j$, with $0<P_j,Q_j,R_j$ and $P_j+Q_j+R_j<d_j$, all of bit length at most $B$. Exact selection (20.2), including all ties, is effective using $O(M)$ integer arithmetic operations on $O(B+b_N)$-bit operands, with $O(B+b_N+\log M)$ temporary bits in addition to acquisition fields and the $O(MB)$ installed catalogue and its derived rows. Streaming acquisition needs $O(R_n+k)$ finite-control operations, $2n$ bounded-counter increments and $n$ sample-total equality checks, with each integer operation implementable in $O(b_n)$ bit operations. D requires no real arithmetic to install (21.2).

For a captured C cut use denominator $d_{\widehat j}$ and for a captured D cut use denominator $m$. Write $b=B$ or $b=b_m$, respectively. For any requested horizon $h$, an explicit complete-law output has exactly $4^h$ entries. It can be generated with $O(h4^h+h)$ integer multiplications, $O(h4^h)$ integer additions and mode/table steps, with operands and streamed probability entries of $O(hb+1)$ bits, and $O(h(b+1)+1)$ temporary bits besides installed data and the captured configuration. Horizon zero directly outputs the single entry one. Materializing the whole array instead needs $O(4^h(hb+1))$ output backing in this representation. These arithmetic-operation counts are not unit-cost bit-time bounds.

*Proof.* For each candidate compute

$$
E_j=\max_{\ell\in\{1,3,B\}}
|d_j K_\ell-N A_{j,\ell}|,
\qquad (A_{j,1},A_{j,3},A_{j,B})=(P_j,Q_j,R_j).
$$

Its distance is $E_j/(Nd_j)$. Compare candidates by the integers $E_jd_l$ and $E_ld_j$ and keep the smaller index on equality. A single catalogue scan needs only a candidate, the incumbent and their arithmetic scratch fields; the displayed operand and workspace bounds follow. This uses exact rational descriptions throughout and needs no test against the unknown true triple. If $\Delta$ is computed rather than supplied for installation, comparing all catalogue pairs uses $O(M^2)$ additional rational-coordinate operations with $O(B)$-bit operands; this preparation is separate from the $O(M)$ terminal selection. Computing a sample-size integer also pays its rational arithmetic and its resulting bit length. No setup-cost optimum is asserted. Counter increments have ordinary bounded binary implementations. D's row numerators are sums of retained counts and have denominator $m$, even when some are zero.

For either captured configuration, all five installed rows have a common integer denominator $d$ ($d=d_{\widehat j}$ or $m$), and numerators between zero and $d$. Enumerate the $4^h$ visible words in a fixed order. For each word, start from the captured mode, multiply its $h$ row numerators while updating that temporary mode by $u$, and output the resulting numerator over $d^h$. Compute $d^h$ once. This is the row-product law, including its zero entries. Each product numerator and the common denominator have $O(hb+1)$ bits. An enumerating word, one accumulator, one temporary mode and the denominator give the asserted streaming workspace and arithmetic bounds; keeping all entries gives the output-backing bound. Query enumeration invokes hypothetical mode steps, not new source reads or new stochastic samples. The emitted laws are nonnegative, normalized and prefix coherent by the supplied generator result.

While selection or a captured-cut call is computed, any continued actual source reads still incur their own streaming updates and (22.2) charges. For one run with an actual finite list of requested horizons $h_1,\ldots,h_q$, output-entry counts add to $\sum_l4^{h_l}$ and the stated arithmetic bounds add over that same list; $k$ includes every source read during those computations. Serial temporary workspace is bounded by the largest individual-call requirement, whereas simultaneously retained arrays or snapshots require their combined backing. An implementation that cannot process reads at source rate needs an explicitly paid queue or a separately supplied timing/service interface; no such uniform physical-rate guarantee follows from these arithmetic bounds. A retained output array, queue, model-table access, selector register, program phase and query workspace all belong within the whole material system boundary whenever present. $\square$

## 23. Supplier correspondence and realization limits of C and D

**Definition 23.1 (the source-relative additional content).** The source matrix, initialization and complete conditional-law meaning are the existing §§1–2 and 10–11, with the published [FiniteStartFiveModeSource declarations](https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.lean) and [owning Scribe](https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/Blueprint/D5/S3/ObserverMemory/Prediction/FiniteStartFiveModeSource.scribe.cs). Their positive-history classification, total `sourceUpdate`, `all_history_conditional_identity`, `actual_positive_conditional_law` and `first_singleton_and_all_later` supply the actual-source bridge used here. The pure generator is supplied by `FiveModeSelfGeneratedLaws.pure_cons`, `pure_generated`, `generated_coherent` and the pure rows recorded in [Self-generated predictive memory, §2, at the fixed source revision](https://github.com/the-omega-institute/trureturing/blob/d5e7fbecb49c0e928696f6857b331b3dbd54d128/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md). No recurrent rigidity, startup-tail minimum or source-law proof is reclassified as new content. In particular C does not solve that volume's remaining unequal-source minimum, and neither C nor D changes this volume's earlier fixed-known or authentic-calibration minima.

The iid stopping-time principle and mean-return identity are `literature-attested` at [Levin–Peres–Wilmer, second edition, Proposition 1.19, p.13, and Proposition A.19, pp.372–373](https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf). Their correspondence here is the observable event $Y=0\iff X=0$, its successive positive returns, the literal row (19.1) and stationary mass $1/5$. They do not provide an extra iid read port. The finite Pinsker and channel inequalities are reused from the [published finite-TV modules](https://github.com/the-omega-institute/trureturing/tree/d5e7fbecb49c0e928696f6857b331b3dbd54d128/D5/S3/TotalVariation) and [their Scribes](https://github.com/the-omega-institute/trureturing/tree/d5e7fbecb49c0e928696f6857b331b3dbd54d128/Blueprint/D5/S3/TotalVariation), with finite driver alphabet, natural logarithms and absolute continuity in the direction $v\ll\xi_\vartheta$. Multinomial variances, Chebyshev, Markov, the elementary KL upper bound and product KL are mature statistical intermediates, not independent novelty claims.

The `repo-derived` application consists of the common original-stream stop and exact clock (19.4)–(19.5), the catalogue selector's exact finite risk and its simultaneous continued-use interpretation (20.3)–(20.5), and the continuous-source driver correspondence giving the zero-safe retained empirical law and single-event guarantee (21.4)–(21.9), together with their same-run material interfaces. The existing parameter-separation and zero-error no-go results of §§10–11 are reused to locate C's residual failure; their proofs are not duplicated. The published `OriginalRectangleSmoothing.finite_record_smoothing_by_original_success_count` treats two-sided center-bit posterior differences for a stationary binary marked presentation with an exact supported rectangle. Its `PositiveRectangleLaw` suppliers concern the actual twelve-state full-erasure law and same-law representations. Neither conclusion is an unknown five-mode departure experiment, a catalogue-selection risk, or the empirical same-update kernel bound here; no rectangle/full-erasure hypothesis is imported into (19.1). These source-relative comparisons assert no global literature priority.

**Assumption 23.2 (material realization and unresolved recovery).** Applying these results to an actual apparatus requires the same persistent five-mode source law, authentic chronological singleton reports, installed effective input data, reliable retention, lawful read access and a mechanism that actually processes every charged read. Uniform sample counts in (20.4) and (21.6) give no uniform tick budget over $\mathfrak A$, and ticks have no asserted conversion to physical duration, energy or storage volume. A finite catalogue supplies candidate descriptions and a membership promise, not the true member. The continuous empirical kernel supplies finite rational probabilities for a capped-horizon prediction task, not exact real calibration; (21.7) is not an acquired truth label.

In this unit the independent source structure is the five-state transition graph and observation fibers; time is the acquired transition order and return clock; the predictive boundary is the conditional complete-word interface at a completed cut; memory is the actually retained selector/counts and mode used by (19.3), (20.2) and (21.3). The proved acquisition-to-memory-to-prediction directions preserve that common source and its actual continuation. They do not reconstruct a discarded archive, the unknown initial hidden path, an independent spatial metric or physical elapsed time from that memory. There is no proved mutual recovery of four unrestricted expressions or common physical realization with atomic, quantum and continuous models. Original fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization and original-tree/FIB recovery obligations retain their stated sources, permissions and open boundaries. C's risky exact all-horizon event and D's approximate capped-horizon event remain separately quantified results; neither is completion of the full common-process objective.

## 追加锚（本行以下为增补区）
