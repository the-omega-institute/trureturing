# A cubic shallow-twist collision

**Definition 1 (Fields, characters, and local-factor conventions).**
Let $k=\mathbf F_7$ and put

$$
F=k((t)),\qquad E=k((u)),\qquad t=u^3.
$$

For either local field $K$, write $\mathcal O_K$ for its valuation ring, $\mathfrak p_K$ for its maximal ideal, and $U_K^j=1+\mathfrak p_K^j$ for $j\geq1$.
Normalize $v_E(u)=v_F(t)=1$ and $|u|_E=|t|_F=7^{-1}$. For $x\in k$, let $e(x)=\exp(2\pi i\widetilde x/7)$, where $\widetilde x$ is any integer lifting $x$.
Define

$$
\psi_F\!\left(\sum_j x_jt^j\right)=e(x_0),
\qquad \psi_E=\psi_F\circ\operatorname{Tr}_{E/F}.
$$

Thus $\psi_F$ is trivial on $\mathfrak p_F$ and nontrivial on $\mathcal O_F$. Use geometric reciprocity
$\operatorname{Art}_K:K^\times\longrightarrow W_K^{\mathrm{ab}}$,
with uniformizers mapping to geometric Frobenius.
A multiplicative quasicharacter $\xi$ corresponds to the Weil character
$\xi\circ\operatorname{Art}_K^{-1}$.
Use self-dual additive Haar measures for $\psi_K$ and multiplicative Haar measures
with $\operatorname{vol}(\mathcal O_K^\times)=1$.
The factors $\gamma(s,\pi\times\chi,\psi_F)$ are the complete original
Rankin–Selberg factors of [Luo–Stevens, arXiv:2505.22357v1, §2.1, Theorem 2.7 and Definition 2.8](https://arxiv.org/html/2505.22357v1), so that

$$
\gamma(s,\pi\times\chi,\psi_F)
=\epsilon(s,\pi\times\chi,\psi_F)
\frac{L(1-s,\pi^\vee\times\chi^{-1})}{L(s,\pi\times\chi)}.
$$

Let $\varepsilon\in\{+1,-1\}\subset k$. Every element of $E^\times$ is uniquely $u^mrv$ with
$m\in\mathbf Z$, $r\in k^\times$, and $v\in U_E^1$.
If $v\equiv1+au+bu^2\pmod{\mathfrak p_E^3}$, define

$$
\theta_\varepsilon(u^mrv)
=e\!\left(\varepsilon a+b-\frac{a^2}{2}\right),
\qquad
R_\varepsilon=\operatorname{Ind}_{W_E}^{W_F}
 (\theta_\varepsilon\circ\operatorname{Art}_E^{-1}).
$$

Let $\pi_\varepsilon$ be the standard local Langlands image of $(R_\varepsilon,N=0)$, with character-twisted local factors preserved.
Depth means the normalized source depth used in Luo–Stevens §2.2.

**Proposition 2 (Complete-response collision).**
The representations $\pi_+$ and $\pi_-$ are nonisomorphic irreducible
supercuspidal representations of $\mathrm{GL}_3(F)$ with trivial central
character and depth $2/3$.
Each $R_\varepsilon$ is irreducible and has multiplicity-free restriction
to wild inertia $P_F$; each $\theta_\varepsilon$ is trivial on $U_E^3$
and nontrivial on $U_E^2$.
For every smooth complex quasicharacter $\chi:F^\times\to\mathbf C^\times$
with $d(\chi)\leq2/3$, and identically in every complex $s$,

$$
\gamma(s,\pi_+\times\chi,\psi_F)
=\gamma(s,\pi_-\times\chi,\psi_F).
$$

More precisely, write $\eta=\chi|_{k^\times}$ and $z=\chi(t)$. Then $\eta$ is arbitrary and $z$ ranges over all of $\mathbf C^\times$.
With the common induction constant $\lambda_{E/F}(\psi_F)$, both complete factors equal

$$
\lambda_{E/F}(\psi_F)\,\eta(-1)z^2
7^{-2(s-1/2)}\,7^{-1/2}
\sum_{a\in k}e\!\left(\frac{a^2}{2}-a\right).
\tag{1}
$$

Proof. The polynomial $X^3-t$ is separable and Eisenstein. Since $7\nmid3$, the extension $E/F$ is totally tamely ramified of degree three.
Choose a primitive cube root $\zeta\in k^\times$.
The extension is cyclic, with automorphisms $\sigma_j(u)=\zeta^ju$,
$j\in\mathbf Z/3\mathbf Z$.
In particular, the field has residue characteristic greater than three.

The principal-unit multiplication law modulo $u^3$ is

$$
(a,b)(a',b')=(a+a',\,b+b'+aa').
$$

Consequently both $a$ and $b-a^2/2$ are additive coordinates. The formula in Definition 1 defines a character of $U_E^1/U_E^3$,
and extends multiplicatively through $u^{\mathbf Z}k^\times U_E^1$.
It is smooth and satisfies

$$
\theta_\varepsilon(u)=1,\qquad
\theta_\varepsilon|_{k^\times}=1,\qquad
\theta_\varepsilon(1+bu^2)=e(b).
$$

Its conductor exponent is therefore exactly three. The two characters vary the first logarithmic coefficient while fixing the second, the residue-unit character, and the uniformizer value.
This is the inducing-character construction of
[Adrian–Liu–Stevens–Tam, §3](https://ueaeprints.uea.ac.uk/id/eprint/65335/4/S2330_1511_2018_00032_X.pdf), specialized here to degree three and conductor three.

The conjugates of $\theta_\varepsilon$ have logarithmic coefficient pairs

$$
(\varepsilon\zeta^j,\zeta^{2j}),\qquad j\in\mathbf Z/3\mathbf Z.
$$
Changing the conjugation convention replaces $j$ by $-j$ and leaves this set unchanged.
Their restrictions to $U_E^2/U_E^3$ are the three distinct nontrivial characters
$b\mapsto e(\zeta^{2j}b)$.
Local reciprocity identifies the image of wild inertia with principal units
in the abelian quotient, and $P_E=P_F$ for a tame extension.
Thus the restriction of $R_\varepsilon$ to $P_F$ is the sum of three distinct
nontrivial character lines.
The normal subgroup $W_E$ has index three in $W_F$,
and $W_F$ acts transitively on these lines.
Any invariant subspace is a sum of character lines and must therefore be zero
or the whole space.
This proves irreducibility and wild multiplicity-freeness.
These uses of reciprocity and tame wild-inertia invariance are the general
local-field inputs also used in
[Bushnell–Henniart, arXiv:1302.4304v1, §§4.1 and 6.2](https://arxiv.org/html/1302.4304v1).

If $R_+\simeq R_-$, restriction to $W_E$ would identify their sets of conjugate inducing characters.
Hence $\theta_-$ would be a Galois conjugate of $\theta_+$.
Equality of their second logarithmic coefficients forces $\zeta^{2j}=1$,
so $j=0$.
Equality of the first coefficients would then give $1=-1$ in $k$, a contradiction.
The injectivity of local Langlands gives $\pi_+\not\simeq\pi_-$.
Irreducible three-dimensional Weil parameters with $N=0$ correspond to supercuspidals.

The different of $E/F$ is generated by $3u^2$ and has exponent two. The conductor-induction formula gives

$$
a_F(R_\varepsilon)
=f(E/F)\bigl(a_E(\theta_\varepsilon)+v_E(\mathfrak D_{E/F})\bigr)
=1(3+2)=5.
$$

There are no inertia invariants, since there are no wild-inertia invariants; thus the Swan conductor is $5-3=2$.
The general nonarchimedean-field conductor-depth formula, with $D=F$ and $m=3$,
and depth preservation under local Langlands give

$$
d(\pi_\varepsilon)=\frac{a_F(R_\varepsilon)-3}{3}=\frac23.
$$

Here the conductor induction is the general formula of [Bushnell–Henniart, §1.3](https://arxiv.org/html/1302.4304v1);
the normalized-level and depth identifications, conductor-depth formula,
and factor and depth compatibility are
[Aubert–Baum–Plymen–Solleveld, arXiv:1311.1606v2, Proposition 2.5 and Theorems 2.7 and 2.9](https://arxiv.org/pdf/1311.1606v2).
Their nonarchimedean-field hypotheses include the positive-characteristic field $F$.

Both $\theta_\varepsilon$ restrict trivially to $F^\times$:
$t=u^3$ has value one, $k^\times$ has value one, and $U_F^1\subset U_E^3$.
For an induced character, the determinant is its transfer character multiplied
by the determinant of the coset permutation representation.
Indeed, in a monomial induced basis the product of the nonzero matrix entries
is the transfer term and the remaining determinant factor is the permutation sign.
The cyclic cubic permutation representation has determinant one.
Under reciprocity, transfer corresponds to the inclusion $F^\times\to E^\times$,
so the transfer character is also trivial.
Consequently $\det R_\varepsilon=1$, and determinant–central-character compatibility
gives $\omega_{\pi_\varepsilon}=1$.
The norm and transfer diagrams apply with geometric reciprocity by inverting both
arithmetic reciprocity maps; see
[Milne, *Class Field Theory*, Chapters I and III](https://jmilne.org/math/CourseNotes/CFT.pdf).

For $\mathrm{GL}_1$, a character of conductor exponent $a\geq2$ has depth $a-1$.
It follows that $d(\chi)\leq2/3$ holds exactly when $\chi$ is trivial on $U_F^1$.
This includes every unramified character.
The decomposition $F^\times=t^{\mathbf Z}k^\times U_F^1$ identifies these characters
with arbitrary pairs

$$
\eta\in\operatorname{Hom}(k^\times,\mathbf C^\times),
\qquad z=\chi(t)\in\mathbf C^\times.
$$

Put $\xi_\varepsilon=\theta_\varepsilon(\chi\circ N_{E/F})$.
Since $N_{E/F}(u)=t$, $N_{E/F}(r)=r^3$ for $r\in k^\times$,
and $N_{E/F}(U_E^1)\subset U_F^1$, one has

$$
\xi_\varepsilon(u)=z,\qquad
\xi_\varepsilon(r)=\eta(r^3),\qquad
\xi_\varepsilon(1+au+bu^2)
=e\!\left(\varepsilon a+b-\frac{a^2}{2}\right).
$$
In particular its conductor exponent remains three, without any unitarity
or finite-order condition on $z$.

For every integer $j$, the trace of $u^j$ is zero unless $3\mid j$,
in which case it is $3t^{j/3}$.
Hence $\psi_E(\sum_jy_ju^j)=e(3y_0)$.
For $K=F,E$, the annihilator of $\mathcal O_K$ under $\psi_K(xy)$ is $\mathfrak p_K$.
Self-duality and $\operatorname{vol}(\mathfrak p_K)=\operatorname{vol}(\mathcal O_K)/7$
therefore give $\operatorname{vol}(\mathcal O_K)=7^{1/2}$.
In particular $\operatorname{vol}(u^3\mathcal O_E)=7^{-5/2}$.

Apply the Tate functional equation with
$\phi_\varepsilon(x)=\xi_\varepsilon(x)^{-1}\mathbf1_{\mathcal O_E^\times}(x)$
and $\widehat\phi(y)=\int_E\phi(x)\psi_E(xy)\,dx$.
The zeta integral $Z(s,\phi_\varepsilon,\xi_\varepsilon)$ equals one.
The Fourier transform vanishes when $v_E(y)\geq-1$:
multiplication by a suitable element of $U_E^2$ leaves the additive phase unchanged
but changes the multiplicative character by a nontrivial scalar.
It also vanishes when $v_E(y)\leq-3$:
translation by a suitable element of $u^3\mathcal O_E$ preserves $\phi_\varepsilon$
but changes the additive phase by a nontrivial scalar.
Thus its support lies in $u^{-2}\mathcal O_E^\times$.
For $v\in\mathcal O_E^\times$, substitution gives

$$
\widehat\phi_\varepsilon(v/u^2)
=\xi_\varepsilon(v)\widehat\phi_\varepsilon(1/u^2),\qquad
\widehat\phi_\varepsilon(1/u^2)=7^{-5/2}S_\varepsilon(\eta),
$$

where the complete unit sum is

$$
S_\varepsilon(\eta)
=\sum_{\substack{r\in k^\times\\ a,b\in k}}
\eta(r^3)^{-1}
e\!\left(\frac{a^2}{2}-\varepsilon a+(3r-1)b\right).
\tag{2}
$$

Indeed, the representatives are $r(1+au+bu^2)$ modulo $u^3\mathcal O_E$,
each of additive volume $7^{-5/2}$, and the additive phase contributes $e(3rb)$.
The dual zeta integral and the functional equation now yield

$$
\begin{aligned}
\gamma_E(s,\xi_\varepsilon,\psi_E)
&=z^2\,7^{2(1-s)}\,7^{-5/2}S_\varepsilon(\eta)\\
&=z^2\,7^{-2(s-1/2)}\,7^{-3/2}S_\varepsilon(\eta).
\end{aligned}
\tag{3}
$$
Both rank-one $L$-factors are one, since $\xi_\varepsilon$ and its inverse are ramified;
thus (3) is also the full epsilon factor.
This is the ramified-character local-constant formula of
[Adrian–Liu–Stevens–Tam, equation (2.1) and Theorem 2.3](https://ueaeprints.uea.ac.uk/id/eprint/65335/4/S2330_1511_2018_00032_X.pdf),
whose stated validity includes positive characteristic.
The Fourier calculation fixes every measure, scalar, and unramified parameter in its present specialization.

Additive orthogonality in $b$ makes (2) vanish termwise after summing in $b$
unless $r=1/3$, and contributes seven for that value.
Since $3^3=-1$ in $k$,

$$
S_\varepsilon(\eta)
=7\eta(-1)\sum_{a\in k}e\!\left(\frac{a^2}{2}-\varepsilon a\right).
\tag{4}
$$
The bijection $a\mapsto-a$ identifies the two sums for $\varepsilon=+1$ and $-1$.
This proves exact scalar equality, without evaluating a Gauss sum or taking absolute values.

The norm diagram for reciprocity and tensor induction identify

$$
R_\varepsilon\otimes\chi
\simeq\operatorname{Ind}_{W_E}^{W_F}
(\xi_\varepsilon\circ\operatorname{Art}_E^{-1}).
$$

Induction of local constants gives

$$
\epsilon_F(s,R_\varepsilon\otimes\chi,\psi_F)
=\lambda_{E/F}(\psi_F)\epsilon_E(s,\xi_\varepsilon,\psi_E);
$$

see [Adrian–Liu–Stevens–Tam, Lemma 2.4](https://ueaeprints.uea.ac.uk/id/eprint/65335/4/S2330_1511_2018_00032_X.pdf).
The same extension and additive character give the same induction constant on both sides;
it is retained explicitly in (1).
The character $\chi$ is trivial on $P_F$, so all three wild constituents of
$R_\varepsilon\otimes\chi$ remain nontrivial, as do those of its dual.
Both inertia-invariant spaces therefore vanish and

$$
L(s,R_\varepsilon\otimes\chi)
=L(1-s,(R_\varepsilon\otimes\chi)^\vee)=1.
$$

Pair-factor preservation by standard local Langlands transfers these identities
to the automorphic factors in Definition 1.
The positive-characteristic Rankin–Selberg and Langlands–Shahidi normalization
comparison, Tate compatibility, and arbitrary complex unramified shifts are supplied by
[Henniart–Lomelí, arXiv:1305.5452v1, Theorem 2.2 and §§2.6–2.9](https://arxiv.org/html/1305.5452v1).
In Luo–Stevens Theorem 2.7 the sign for the character twist is
$\chi(-1)^{3-1}=1$.
Thus no extra sign or dual twist changes (3).
Equations (3) and (4), with the common induction constant, prove (1)
for every $\eta$, every nonzero complex $z$, and every complex $s$.
This completes the proof.

**Corollary 3 (Failure of the depth-restricted converse in rank three).**
The assertion that depth-at-most-$2/3$ character twists separate the uniform
cubic conductor-three family within each central character is false.
In particular, [Luo–Stevens, arXiv:2505.22357v1, Conjecture 1.3](https://arxiv.org/html/2505.22357v1)
is false as literally stated over all nonarchimedean local fields.

Proof. The uniform assertion includes every field of residue characteristic greater than three,
in equal or mixed characteristic, and every totally tamely ramified cubic extension
on either side.
It allows arbitrary residue-unit and uniformizer values for the inducing characters,
while explicitly requiring irreducibility, wild multiplicity-freeness,
source depth $2/3$, and equal central characters.
Proposition 2 verifies all these hypotheses for the particular field $F=k((t))$,
the permitted choice $E_1=E_2=E$, and the characters $\theta_+$ and $\theta_-$.
It proves equality of every required complete response and failure of isomorphism.
One such admissible pair refutes the universal implication;
no positive statement for a restricted family is inferred.

Conjecture 1.3 in the cited version assumes equal central characters and equality
against every supercuspidal twist of ranks $1\leq r\leq\lfloor n/2\rfloor$
with depth at most the depths of the two representations.
At $n=3$ the only twisting rank is one, and every smooth complex character
of $F^\times$ is supercuspidal for $\mathrm{GL}_1(F)$.
The two depths are $2/3$, so its complete twisting range is exactly the range
of Proposition 2.
The field hypothesis in that version does not exclude positive characteristic.
The proposition therefore contradicts precisely its isomorphism conclusion.

The rank and depth restrictions in converse statements are distinct.
[Jacquet–Liu, arXiv:1601.03656v2, Theorem 1.3](https://arxiv.org/html/1601.03656v2)
requires all twists in the indicated ranks, without this depth cutoff.
Its rank-three case includes positive-depth characters absent here.
Likewise, the twisting hypothesis in
[Adrian–Liu–Stevens–Xu, arXiv:1409.4790v1, Proposition 7.2 and Corollary 7.3](https://arxiv.org/html/1409.4790v1)
and in [Jiang–Nien–Stevens, arXiv:1504.02819v1, Theorem 1.5](https://arxiv.org/html/1504.02819v1)
is unrestricted in depth.
These all-depth theorems are not contradicted.

The inducing family and local-constant formulas used above are established inputs.
In [Adrian–Liu–Stevens–Tam, Theorem 3.2](https://ueaeprints.uea.ac.uk/id/eprint/65335/4/S2330_1511_2018_00032_X.pdf),
the prime-degree construction compares twisting ranks: for its permitted index $i$,
equality holds for ranks below $i$ and separation occurs at rank $i$.
At degree three and $i=1$ it does not assert equality against every shallow rank-one twist.
Here the additional identity is the involution $a\mapsto-a$ in the complete sum (2),
together with nonconjugacy of the inducing characters and the precise depth calculation.
It supplies the full-response collision used in this corollary, rather than a new
local-constant formula or a new general construction of tame parameters.
The even-rank middle-supercuspidal hypothesis of Luo–Stevens Theorem 1.1
is not a hypothesis of their Conjecture 1.3 and is not asserted for this pair.

## 追加锚（本行以下为增补区）
