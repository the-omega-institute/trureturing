# 递归关系观察：校准滤波器的完整可达深度谱

## 27. The original depth problem and its orbit interface

**Definition 27.1 (calibrations, lawful comparisons and depth).**
Let $E=\mathbb R^5$ have the fixed oriented orthonormal frame
$e_1,\ldots,e_5$. Put $J_{ij}=e_ie_j^T-e_je_i^T$. For a real skew
matrix $A$, put
$$
 a_A=\sum_{i<j}A_{ij}e_i\wedge e_j,\qquad
 K(A)=-A^2,\qquad b(A)=*_5(a_A\wedge a_A).
 \tag{27.1}
$$
The lawful sources and calibration class are
$$
 \mathcal L=\{(S,A)\in M_5(\mathbb R)^2:S^T=S,\ \operatorname{tr}S=1,\ A^T=-A,
                      \ S+iA\succeq0\},\qquad
 \mathcal C=\{F\in GL_5(\mathbb R):F^TF\preceq I\}.
 \tag{27.2}
$$
For $F\in\mathcal C$, let $A_j=F^jA(F^T)^j$ and define
$$
 \mathcal D_{F,d}(S,A)
   =(S,K(A),b(A),K(A_1),\ldots,K(A_d)),\qquad d\ge0.
 \tag{27.3}
$$
The minimum depth $n(F)$ is the least $d$ for which equality of
(27.3) for any lawful common-$S$ pair implies $B=A$ or $B=-A$;
put $n(F)=\infty$ if no such $d$ exists. The attainable spectrum is
$$
 \mathfrak D=\{n(F):F\in\mathcal C\}.
 \tag{27.4}
$$
This is the depth problem of
[the boundary volume, Sections 6–10 and 19–26](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#19-calibrated-filter-classification-domain-and-intermediate-ingredients).
The frame is fixed; common sign is the entire source quotient. For a
real orthonormal four-frame $f$, write $J^f_{ij}=f_if_j^T-f_jf_i^T$.

**Assumption 27.2 (preparations and the stipulated detector laws).**
Conditional on one fixed source parameter, preparations are independent
copies of $S+iA$. Each local chain uses the success operator $F$ and
failure operator $(I-F^TF)^{1/2}$, and stops at its first failure.
The two specimens assigned to a pair setting execute their local chains
independently, including when the other specimen fails. All prefixes,
failures and preparation charges are retained. The base detector panel
is precisely $S,K,b$; after an all-success prefix it is only $K$.
The terminal detectors are those of Definition 10.1 of the boundary
volume, with the common source binding of its Assumption 6.2.

**Definition 27.3 (planes and runs).**
On $E_{\mathbb C}$ use the complex bilinear forms
$B(x,y)=x^Ty$, $B_G(x,y)=x^TGy$, and set
$$
 \mathscr Q=\{U\subset\mathbb C^5:\dim_{\mathbb C}U=2,
                                  \ B|_{U\times U}=0\},\qquad
 \mathscr S_G=\{U\in\mathscr Q:B_G|_{U\times U}=0\},
 \quad G=F^TF.
 \tag{27.5}
$$
An $L$-position run means $U,FU,\ldots,F^{L-1}U\in\mathscr S_G$.
For $U\in\mathscr Q$, its real four-plane is
$W=(U\oplus\overline U)\cap E$, and its real normal is the line
$W^\perp$. Write $[U]=\{U,\overline U\}$.

The orbit interface used below is exactly Lemmas 20.1–20.2 of the
boundary volume: a lawful non-sign collision through depth $d\ge1$
is equivalent to a $d$-position run. Thus a largest finite run of
length $L$ gives $n(F)=L+1$. The set $\mathscr S_G$ is always nonempty,
so $n(F)\ge2$. Nonemptiness uses Fan–Pall,
[Imbedding Conditions for Hermitian and Normal Matrices, Theorem 1](https://doi.org/10.4153/CJM-1957-036-1),
with the real compression spectra
$(g_2,g_2,g_4,g_4)$ and $(g_1,\ldots,g_5)$; it asserts no
multi-iterate realization. The finite-dimensional isotropic-plane and
orthogonal-complex-structure correspondence is the classical one in
Salamon–Viaclovsky,
[Orthogonal complex structures on domains in $\mathbb R^4$, Section 2.4](https://arxiv.org/html/0704.3422v2#S2.SS4).
The complete point lists, complete hyperplane families and exhaustive
seven-row classification used here are Propositions 22.1 and 23.1 and
Theorem 24.1 of the boundary volume. These results are suppliers for
the spectrum inference, rather than new conclusions of this volume.

**Lemma 27.4 (actual orbits, scaling and reversal).**
The normal of $FU$ is $F^{-T}W^\perp$. A return to $[U]$ along an
isotropic orbit gives an infinite isotropic orbit under that same real
$F$. Multiplication of $F$ by a nonzero real scalar preserves depth.
If depth is extended to every real invertible matrix by (27.3), then
$$
 n(F^{-1})=n(F).
 \tag{27.6}
$$

Proof.
The real four-plane of $FU$ is $FW$, so its normal transforms by
inverse transpose. If $F^kU=U$ or $\overline U$, reality permits the
same orbit segment to be repeated, with conjugation when required.
Scalar multiplication changes none of its complex planes. For reversal,
a collision through $d$ is equivalent to
$U,FU,\ldots,F^dU\in\mathscr Q$ by Lemma 20.1. Reversing this list
is a length-$d$ orbit for $F^{-1}$. The converse is identical, proving
(27.6). The algebraic proof of that lemma uses invertibility, not the
contraction inequality; scaling also transfers its lawful witnesses.
A sufficiently small positive multiple of $F^{-1}$ belongs to
$\mathcal C$. Finally,
$$
 (F^{-1})^TF^{-1}=(FF^T)^{-1}
$$
has the reciprocal spectrum of $F^TF$. Thus reversal exchanges the
largest and smallest extreme triple Gram eigenvalue, without assuming
that these two Gram matrices have the same eigenvectors. $\square$

## 28. Weighted-normal rigidity and the two-state reduction

**Lemma 28.1 (three transitions of weighted tetrahedral normals).**
Let
$$
 T=\{(1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)\},\qquad
 D_w=\operatorname{diag}(\sqrt{w_1},\sqrt{w_2},\sqrt{w_3}),
 \quad w_i>0.
 \tag{28.1}
$$
Suppose $H\in GL_3(\mathbb R)$ has positive diagonal column Gram
matrix $H^TH$. If it sends three distinct $D_ws$ to three distinct
$D_wt$, each up to sign and with no additional magnitude, then
$$
 H=\pm D_wPD_w^{-1},
 \tag{28.2}
$$
where $P$ is a signed coordinate permutation preserving $T$.
In particular $H$ permutes all four normal lines.

Proof.
The 24 signed coordinate permutations whose coordinate-sign product is
$+1$ act faithfully on $T$: fixing its four elements fixes three
independent vectors and hence the whole matrix. Their action is
therefore the full permutation group of $T$. Put $M=D_w^{-1}HD_w$.
Choose signed permutations $Q,P_o$ sending the ordered triple
$$
 s_0=(1,1,1),\quad s_1=(1,-1,-1),\quad s_2=(-1,1,-1)
$$
to the actual input and output triples. If the three signs agree,
independence gives $M=\pm P_oQ^T$. Otherwise reorder the triples and
multiply $M$ by a common sign so that just the third sign is negative.
Then
$$
 P_o^TMQ=N=\begin{pmatrix}1&1&-1\\0&0&1\\0&1&0\end{pmatrix},
 \tag{28.3}
$$
since $N$ fixes $s_0,s_1$ and negates $s_2$.
The matrix $M^TD_w^2M=D_wH^THD_w$ is diagonal. Therefore
$N^TZN$ is diagonal for the positive diagonal matrix
$Z=P_o^TD_w^2P_o$, after conjugating by $Q$. But
$(N^TZN)_{12}=Z_{11}>0$, a contradiction. This uses independent
input and output permutations and requires no equality among the
weights. $\square$

**Lemma 28.2 (normal permutation and two sign states).**
Suppose $E=R\oplus V$ orthogonally, $\dim R=3$, $\dim V=2$;
$G=F^TF$ is diagonal in fixed spectral coordinates respecting this
sum, and $F$ preserves both summands. Suppose a set of allowed normals
in $R$ is (28.1), normalized by $\sum w_i=1$, and
$\rho^{-1}F_R^{-T}=\pm D_wPD_w^{-1}$ for some $\rho>0$ and $P$
as in Lemma 28.1. Suppose the compression to each normal complement
has distinct eigenvalues $\alpha,\beta$, each twice, with one line
of each eigenspace in $R$ and one in $V$. Then a run of three planes
from the corresponding lists (22.3) forces an actual infinite run.

Proof.
Choose unit $\alpha,\beta$ eigenvectors $x_\alpha,x_\beta$ in $V$,
and orthonormal compression eigenvectors $u_0,v_0$ in
$(D_w(1,1,1))^\perp\cap R$. Put
$$
 \Sigma_s=\operatorname{diag}(s),\quad
 E_s=\Sigma_s[u_0,v_0].
$$
These are the compression eigenframes at $n_s=D_ws$ because
$\Sigma_s$ commutes with $G_R$. The listed planes have bases
$$
 [x_\alpha,x_\beta]+iE_sD,
 \qquad D=\operatorname{diag}(\eta,\theta),\quad\eta,\theta\in\{\pm1\}.
 \tag{28.4}
$$
Modulo conjugation $D\sim-D$, there are exactly two states.
Write $P=\Sigma_\epsilon P_\pi$, so the normal map is
$f(s)=\epsilon\pi(s)$. Taking inverse transposes gives
$F_R=\pm\rho^{-1}D_w^{-1}PD_w$, and consequently
$F_R\Sigma_s=\Sigma_{\pi(s)}F_R$. Thus the matrix of
$F_R:n_s^\perp\cap R\to n_{f(s)}^\perp\cap R$ in the displayed
frames is independent of $s$:
$$
 L=E_{f(s)}^TF_RE_s=[u_0,v_0]^T\Sigma_\epsilon F_R[u_0,v_0].
 \tag{28.5}
$$
Let $A$ be the matrix of $F_V$ in $[x_\alpha,x_\beta]$.
Comparison of real parts in (28.4) shows that a transition to the
state $D'$ is exactly
$$
 LD=D'A,
 \tag{28.6}
$$
allowing the common minus sign in $D'$ for conjugation. This defines
a deterministic partial map on the two states, independent of the
normal label. Three positions repeat a state. Repeating that segment
continues the actual plane orbit, since (28.6) still holds at every
normal and $f$ permutes the entire normal set. No independently
assigned graph is substituted for $F$. $\square$

## 29. Bounds in the other Gram strata

**Proposition 29.1 (all rows except the extreme triple).**
If $n(F)<\infty$ and $G$ does not have an extreme triple eigenvalue
with two distinct simple eigenvalues, then $n(F)\le5$. More precisely,
the finite bounds in the rows $4+1$, $3+2$, middle $3+1+1$,
$2+2+1$, $2+1+1+1$ and $1+1+1+1+1$ are respectively
$2,3,3,3,3,5$. The scalar row gives infinity.

Proof.
The scalar and $4+1$ conclusions are Theorem 24.1 and Corollary 25.2
of the boundary volume. Its point list for $2+2+1$ has only two
conjugate-pair vertices, giving finite bound three by Proposition 22.1.
It remains to sharpen the other four rows.

For $3+2$, write $E=A_0\oplus V$, with dimensions three and two,
and $G=aI$ on $A_0$, $bI$ on $V$, $a\ne b$. Every
$U\in\mathscr S_G$ is the sum of a bilinear null line in
$(A_0)_{\mathbb C}$ and one in $V_{\mathbb C}$. To see this directly,
$P_VU$ is isotropic because $B_G-aB$ vanishes on $U$; its dimension
is one. Its kernel is a null line $L$ in $(A_0)_{\mathbb C}$.
The $A_0$ component of the other generator is null and perpendicular
to $L$, so it belongs to $L$: the nondegenerate quotient
$L^\perp/L$ has dimension one. The projection cannot be zero, since
a nondegenerate complex three-space has no isotropic two-plane.
In particular $D=\sqrt G$ fixes each such plane as a subspace.

Write $F=OD$. A three-position run is therefore $U,OU,O^2U$.
On the real four-plane $W$ of $U$, with its orthogonal complex
structure $J$, all three real two-planes
$$
 V_j=O^{-j}V,\qquad j=0,1,2,
 \tag{29.1}
$$
are $J$-invariant. If $V_0=V_1$, all later $V_j$ equal $V_0$,
so the run continues. Otherwise consecutive members of (29.1) are
distinct complex lines for $J$ and span $W$. Hence $O^{-1}W=W$.
Let $R_0=O^{-1}|_W$. If $V_0\perp V_1$, orthogonality gives
$V_2=V_0$, and the $V_j$ alternate forever.

If the two planes are nonorthogonal, they determine $J$ up to sign
among orthogonal complex structures preserving both. Indeed, in
$W=P\oplus P^\perp$, another distinct nonorthogonal $J$-complex line
$Q$ is the graph of an invertible $T:P\to P^\perp$.
The projection onto $P$ is invertible since its kernel is $J$-invariant
and $Q$ is not perpendicular to $P$; $T$ is invertible since
$Q\cap P=0$. A preserving orthogonal complex structure $J'$ is block
diagonal, its restriction to $P$ has just two quarter-turn choices,
and $J'_{P^\perp}T=TJ'_P$ determines the other block. Apply this
uniqueness to $V_1,V_2$: both $J$ and $R_0JR_0^{-1}$ preserve them,
so $R_0JR_0^{-1}=\pm J$. Every later $V_j$ is $J$-invariant.
In every case $O^jU\in\mathscr S_G$ for all $j$, and induction gives
$F^jU=O^jU$. Thus three positions force infinity, proving the bound.

For a middle triple eigenvalue, the two hyperplanes $H_\pm$ in
(23.2) of the boundary volume are real. If $FH_s$ is not a listed
hyperplane, its intersection with either listed target is the
complexification of a positive real three-space, and contains no
isotropic two-plane. By (23.9), $F$ is conformal on $H_s$.
Thus the only transitions are whole-hyperplane transitions on two
vertices. A cycle gives infinity; an acyclic run has at most two
positions, giving the bound three.

For $2+1+1+1$, the point list (22.1)–(22.4) has two real normal lines
spanning a spectral two-space $R$, with two conjugate-pair planes
over each. Put $K=R^\perp$. Its Gram spectrum is $(a,a,t)$, where
$a$ is the double eigenvalue and $t\ne a$ is the other compression
eigenvalue. Suppose three positions occur. If the first two normals
coincide, all three are that same line; two plane vertices force a
return and infinity. Otherwise the normals alternate: injectivity of
$F^{-T}$ forbids the third from equalling the second. Thus $F^{-T}$
preserves $R$, so $F$ preserves $K$. Since $G$ preserves $K$,
Gram orthogonality gives $FR\perp FK=K$, so $F$ also preserves $R$.

Let $p_s$ be a unit vector in $n_s^\perp\cap R$, and let $e_t$ span
the $t$ eigenline in $K$. The two compression eigenspaces are the
$a$-plane $L_a\subset K$ and $\operatorname{span}(p_s,e_t)$.
Every listed complex structure has $J_sp_s=\pm e_t$.
An actual transition satisfies $FJ_s=J_{s'}F$ on its four-plane.
Since $Fp_s$ lies on the target $p$-line, this forces $Fe_t$ to lie
on the line of $e_t$. Gram orthogonality now gives $FL_a=L_a$.
On this plane $F$ is $\sqrt a$ times an orthogonal map; on $e_t$ and
each $p_s$ its absolute factor is $\sqrt t$, because their Gram
Rayleigh values are $t$. It therefore transports every listed complex
structure to a listed structure over the other normal. The two normals
cycle and every arriving plane is still allowed, giving infinity.
Again a finite run has at most two positions.

Finally suppose $G$ has five distinct eigenvalues. Let
$$
 R=E_{g_1}\oplus E_{g_3}\oplus E_{g_5},\qquad
 V=E_{g_2}\oplus E_{g_4},\quad\alpha=g_2,\quad\beta=g_4.
$$
The four normals are $n_s=D_ws$ from (22.1), with all $w_i>0$;
over each are two conjugate-pair plane vertices. The compression
determinant and the cofactor identity give the common norm
$$
 n_s^TG^{-1}n_s
 =\frac{\alpha^2\beta^2}{\det G}
 =\frac{\alpha\beta}{g_1g_3g_5}=\rho^2.
 \tag{29.2}
$$
Thus $H=\rho^{-1}F^{-T}$ sends an actual normal transition to a
unit listed normal up to sign, and $H^TH=\rho^{-2}G^{-1}$.
If three distinct input normals have listed images, their independence
forces $H(R)=R$. Lemma 28.1 applies on $R$. Also $F(V)=V$, and
Gram orthogonality gives $F(R)=R$. The hypotheses of Lemma 28.2 hold
with the compression eigenvalues $\alpha,\beta$. Three plane positions
then force infinity.

Suppose a run has five positions. If its first four normals include
three distinct lines, their outgoing transitions give the preceding
rigidity case. Otherwise the deterministic injective normal trajectory
has repeated among at most two lines and remains on them. Five plane
positions among the four vertices over those lines repeat a vertex,
again giving infinity by Lemma 27.4. A finite run has at most four
positions, so finite $n(F)\le5$. $\square$

## 30. The extreme-triple obstruction to depth six

**Lemma 30.1 (complete exceptional equations for a smallest triple).**
Suppose $G=aI$ on a real three-space $A$, with simple eigenvalues
$0<a<b<c$ on orthonormal $v,w$. Write $F=O\sqrt G$, and set
$$
 p=\sqrt{b-a},\quad q=\sqrt{c-a},\quad\Delta=c-b,
 \quad\kappa=-\Delta,\quad t_0=p/q,\quad s_0=\sqrt\Delta/q,
 \quad z_s=pv+siqw,\quad H_s=\ker z_s^T.
 \tag{30.1}
$$
There are no whole-hyperplane transitions among $H_+,H_-$.
Let
$$
 \mathcal P=\{[U]:U\in\mathscr S_G,\ FU\in\mathscr S_G\}.
 \tag{30.2}
$$
Then $|\mathcal P|$ is $0$, $2$ or $4$. If $|\mathcal P|=4$, the
$[v,w]$ block of $O$, after possibly replacing $F$ by $-F$, is one of
$$
 \mathrm I:\quad
 \begin{pmatrix}x&0\\0&0\end{pmatrix},\quad
 x=\frac{\sqrt a\,\Delta}{p^2\sqrt c};
 \qquad
 \mathrm {II}:\quad
 \begin{pmatrix}0&0\\0&t\end{pmatrix},\quad
 t=\frac{\sqrt a\,\Delta}{q^2\sqrt b}.
 \tag{30.3}
$$

Proof.
The supplier factorization (23.8) says that $\mathscr S_G$ is exactly
the isotropic planes in these two nondegenerate hyperplanes, two
rulings in each. Their common intersection $A_{\mathbb C}$ has no
isotropic two-plane; each conjugate-pair vertex has a unique representative
in $H_+$.

For a nonzero complex normal, the line invariant
$\chi(z)=|z^Tz|/(z^*z)$ is preserved by real orthogonal maps and
conjugation. For $F^{-T}z_s=OG^{-1/2}z_s$, the squared ratio of its
two orthogonal real components changes from
$$
 u=\frac{b-a}{c-a}\quad\hbox{to}\quad u'=\frac cb u,
 \qquad 0<u<u'<1.
$$
Thus $\chi=(1-u)/(1+u)$ changes strictly. No $FH_s$ can be either
target hyperplane.

Put $y=F^Tz_t$, $X=z_t^TOv$, $Y=z_t^TOw$. A plane in $H_s$
has image in $H_t$ exactly when it is contained in
$M=H_s\cap\ker y^T$. Since $H_s$ is nondegenerate and these
hyperplanes are distinct, $B|_M$ is degenerate exactly when
$$
 \kappa y^Ty-(z_s^Ty)^2=0.
$$
Indeed the normal of $M$ within $H_s$ is
$y-(z_s^Ty/\kappa)z_s$; it is nonzero, and its square vanishes
exactly in this equation. In that case $M$ has rank two and exactly
two isotropic two-planes, one from each ruling, by (21.3) and the
intersection-parity rule of Proposition 23.1. Otherwise it has none.
Now
$$
 y^Ty=a\kappa+p^2X^2+q^2Y^2,\qquad
 z_s^Ty=p\sqrt b\,X+siq\sqrt c\,Y,
$$
so the complete exceptional condition is
$$
 \kappa y^Ty-(z_s^Ty)^2
   =a\kappa^2-(p\sqrt c\,X+siq\sqrt b\,Y)^2=0.
 \tag{30.4}
$$
For $U\subset H_s$, (23.9) gives $B(Fu,Fv)=aB(u,v)$.
Thus the isotropic planes just counted really do lie in
$\mathscr S_G$ and have images in $\mathscr S_G$; no additional
isotropy condition has been omitted.

Conjugation pairs $(s,t)$ with $(-s,-t)$. Each active pair gives
two vertices in (30.2), distinct because neither a source nor an image
plane can lie in both listed hyperplanes. There are only two independent
conditions, giving the claimed cardinalities.
Write the $[v,w]$ block of $O$ as
$\left(\begin{smallmatrix}x&y_0\\z_0&t\end{smallmatrix}\right)$.
If both conditions hold, their imaginary parts give
$$
 \sqrt c\,z_0+\sqrt b\,y_0=0,\qquad
 -\sqrt c\,z_0+\sqrt b\,y_0=0,
$$
so $y_0=z_0=0$. Their real parts are
$$
 p^2\sqrt c\,x-q^2\sqrt b\,t=\pm\sqrt a\,\kappa,
 \qquad
 p^2\sqrt c\,x+q^2\sqrt b\,t=\pm\sqrt a\,\kappa.
$$
The signs either agree or differ, so exactly one diagonal entry is zero,
and the absolute value of the other is as in (30.3). A common minus
makes that entry positive and does not change the plane dynamics.
$\square$

**Proposition 30.2 (universal upper bound on the extreme rows).**
If the Gram multiplicities are $3+1+1$ and the triple eigenvalue is
extreme, every finite $n(F)$ is at most five.

Proof.
First let the triple eigenvalue be smallest and use Lemma 30.1.
Every position of a run except its last belongs to $\mathcal P$.
A repeat there gives infinity. Hence $|\mathcal P|\le2$ gives at most
three positions and finite $n(F)\le4$. It remains to treat (30.3).

In case II, $0<t<1$, since
$q^4b-a\Delta^2=(b-a)(c^2-ab)>0$.
Put $h=\sqrt{1-t^2}$. There are orthonormal
frames $a_1,a_2,a_3$ and $c_1,c_2,c_3$ of $A$ such that
$$
 Oa_1=-v,\quad Oa_2=-tc_2+hw,\quad Oa_3=c_3,
 \quad Ov=c_1,\quad Ow=hc_2+tw.
 \tag{30.5}
$$
For example take $a_1=-O^Tv$, $c_1=Ov$,
$c_2=(Ow-tw)/h$, and let $a_2$ be the normalized $A$ component
of $O^Tw$; orthogonality gives the displayed images. Complete the
frames with $c_3=Oa_3$.

Every plane in $H_+\cap\mathscr Q$ is specified by a unit $u\in A$
and a null line in $(u^\perp\cap A)_{\mathbb C}$. It contains
$$
 v-is_0u+it_0w,
 \quad\hbox{and its real normal is}\quad t_0u+s_0w.
 \tag{30.6}
$$
To prove exhaustiveness, let $\nu$ be a unit real normal of such a
plane. Since $U^\perp=U\oplus\mathbb C\nu$ and $z_+\in U^\perp$,
write $z_+=z+\lambda\nu$, $z\in U$. Squaring gives
$\lambda^2=-\Delta$; choose the sign of $\nu$ so that
$\lambda=i\sqrt\Delta$. The equation
$\nu^Tz_+=i\sqrt\Delta$ gives $\nu_v=0$, $\nu_w=s_0$.
Its $A$ component therefore has norm $t_0$, so
$\nu=t_0u+s_0w$. Also
$z_+-i\sqrt\Delta\nu=p(v-is_0u+it_0w)\in U$.
Projection of $U$ to $\operatorname{span}(v,w)_{\mathbb C}$ has
rank one: it lies on the line cut out by $z_+$, and rank zero would
give an isotropic two-plane in $A_{\mathbb C}$. Its kernel is a null
line in $(u^\perp\cap A)_{\mathbb C}$, as follows by pairing with
the displayed generator. Conversely either such null line, together
with that generator, is an isotropic two-plane in $H_+$.
Compression at this normal has eigenspaces $u^\perp\cap A$ and
$\operatorname{span}(v,-s_0u+t_0w)$, with eigenvalues $a,b$.
If its image lies in $H_\tau$, applying $z_\tau^TF$ to this
generator gives
$$
 u_1=0,\qquad
 u_2=\frac{t_0\sqrt c\,t}{s_0\sqrt a\,h}.
 \tag{30.7}
$$
The real part of that equation is
$\tau q(s_0\sqrt a\,h u_2-t_0\sqrt c\,t)=0$ and its
imaginary part is $p s_0\sqrt a\,u_1=0$.
In particular all four exceptional vertices lie over at most two real
normals. There are at most two conjugate-pair planes at each such
normal, by the compression eigenvalues $(a,a,b,b)$; hence both states
at each of these two normals are exceptional. A cycle of these normals
keeps every arriving state exceptional and gives infinity. If no such
cycle occurs, at most two exceptional positions and one final position
can occur. Thus the finite bound in case II is four.

In case I put $h=\sqrt{1-x^2}$. Here $x\le1$ is equivalent to
$b^2\ge ac$, since
$$
 p^4c-a\Delta^2=(c-a)(b^2-ac).
$$
Orthonormal frames of $A$ give the normal form
$$
 Oa_1=-xc_1+hv,\quad Oa_2=-w,\quad Oa_3=c_3,
 \quad Ov=hc_1+xv,\quad Ow=c_2.
 \tag{30.8}
$$
For $h>0$, take $a_2=-O^Tw$, $c_2=Ow$,
$c_1=(Ov-xv)/h$, and $a_1$ the normalized $A$ component of
$O^Tv$. Orthogonality supplies its image in (30.8).
For $h=0$, take any unit $a_1\perp a_2$ in $A$ and set
$c_1=-Oa_1$; complete both frames as above.
Define
$$
 m=\sqrt{\frac{b\Delta}{p^2c}},\qquad
 n=\sqrt{\frac{b^2-ac}{p^2c}},\qquad m^2+n^2=1,
 \qquad n=\frac{ph}{q}.
 \tag{30.9}
$$
The four exceptional vertices have the following representatives in
$H_+$:
$$
 U_{r,\zeta}=\operatorname{span}_{\mathbb C}
 \{a_1+i(-rn a_2+\zeta m a_3),
   v-is_0(rm a_2+\zeta n a_3)+it_0w\},
 \qquad r,\zeta\in\{\pm1\}.
 \tag{30.10}
$$
Their generators are isotropic and perpendicular: the imaginary
vectors have norms one and mutual inner product zero.
They lie in $H_+$. Applying $z_r^TF$ to their two generators gives
respectively
$$
 \sqrt a(ph-qn)=0,\qquad
 p\sqrt b\,x-q\sqrt a\,s_0m=0.
$$
Thus their images lie in $H_r$, and (23.9) makes those images
isotropic. The four planes are distinct, including when $n=0$:
their graph matrices over $\operatorname{span}(a_1,v)$ differ in
$r$ or $\zeta$. Since $H_+$ contains exactly four representatives
by Lemma 30.1, (30.10) is the complete exceptional list.
Their real normal representatives are
$$
 n_{r,\zeta}=t_0(rm a_2+\zeta n a_3)+s_0w.
 \tag{30.11}
$$
If $n=0$, there are two normals, each carrying both exceptional
states. The case-II normal-cycle argument gives the finite bound four.
Suppose henceforth $n>0$. The four normals are distinct.
Put
$$
 \rho^2=\frac b{ac},\qquad
 M=\sqrt{\frac{a\Delta}{bp^2}},\qquad
 N=\sqrt{\frac{b^2-ac}{bp^2}},\qquad M^2+N^2=1.
$$
Since $F^{-T}=OG^{-1/2}$, its image of (30.11), after normalization
to positive $w$ component, is $t_0u'+s_0w$, where
$$
 u'=-r(Mc_2+\zeta Nc_3).
 \tag{30.12}
$$
For completeness, before normalization the image is
$$
 -\frac{rt_0m}{\sqrt a}w
 +\frac{\zeta t_0n}{\sqrt a}c_3
 +\frac{s_0}{\sqrt c}c_2.
$$
Its norm is $\rho$, and multiplying by $-r/\rho$ gives (30.12).

Suppose a finite run had five positions. Its first four positions
would be four distinct exceptional vertices. The first three transitions
between them have three distinct target vectors (30.12). These lie in
both $\operatorname{span}(a_2,a_3)$ and
$\operatorname{span}(c_2,c_3)$. Three distinct unit vectors include
two nonparallel vectors, so these two real planes coincide, and
$c_1=\pm a_1$. Consequently (30.8) makes $F$ block diagonal for
$$
 R=\operatorname{span}(a_2,a_3,w),\qquad
 V=\operatorname{span}(a_1,v).
 \tag{30.13}
$$
These are spectral subspaces of $G$, with spectra $(a,a,c)$ and
$(a,b)$. Up to signs, the four normals (30.11) are the weighted
set (28.1), with squared weights
$t_0^2m^2,t_0^2n^2,s_0^2$, all positive. Their inverse-Gram squared
norm is $\rho^2=b/(ac)$; this follows either directly from (30.11)
or from the compression determinant $a^2b^2$.
Thus $H=\rho^{-1}F_R^{-T}$ has positive diagonal column Gram
and three distinct actual transitions of these normals. Lemma 28.1
makes it permute all four lines. At each normal complement, compression
has eigenvalues $a,b$, twice each, with one eigenline in each of the
two summands (30.13). Lemma 28.2 now gives an actual infinite plane
orbit, contradicting finiteness. This excludes a five-position finite
run and proves $n(F)\le5$.

If the triple eigenvalue is largest, apply Lemma 27.4 to a contractive
positive scalar multiple of $F^{-1}$. Its triple Gram eigenvalue is
smallest, so the same bound transfers to the original $F$.
$\square$

## 31. A legal filter attaining depth four

**Proposition 31.1 (an explicit algebraic depth-four calibration).**
In the original frame set $R=\operatorname{span}(e_1,e_2,e_3)$,
$V=\operatorname{span}(e_4,e_5)$, and define
$$
 \alpha=\frac{127-\sqrt{2257}}{68},\quad
 \beta=\frac{127+\sqrt{2257}}{68},\quad
 r=(1,2,4),\quad w=(3/34,4/17,23/34),\quad
 D_R=\operatorname{diag}(1,\sqrt2,2),\quad
 n_0=(\sqrt{w_1},\sqrt{w_2},\sqrt{w_3})^T.
 \tag{31.1}
$$
Let $u$ be the vector with entries $\sqrt{w_i}/(r_i-\alpha)$,
divided by its positive Euclidean norm, and define $v$ in the same
way with $\beta$. Put
$$
 E=[u,v],\qquad
 \widetilde E=D_RE\operatorname{diag}(\alpha^{-1/2},\beta^{-1/2}),
$$
$$
 S_1=\operatorname{diag}(1,-1,-1),\quad
 S_2=\operatorname{diag}(-1,1,-1),\quad S_3=S_1S_2,
 \quad E_1=S_1E,\quad E_2=S_3E,\quad
 \widetilde E_1=S_1\widetilde E.
 \tag{31.2}
$$
Let $\varepsilon_1,\varepsilon_2$ be the standard columns of
$\mathbb R^2$, and write $e_i^{(3)}$ for those of $\mathbb R^3$.
Define
$$
 a=\widetilde E^Te_1^{(3)},\quad b=E^Te_2^{(3)},\quad
 J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\quad
 A=\frac{[b,Jb][a,Ja]^T}{13/17},
$$
$$
 X=[\widetilde E\varepsilon_1,\widetilde E\varepsilon_2,
                         \widetilde E_1\varepsilon_1],\quad
 Y=[E_1A\varepsilon_1,E_1A\varepsilon_2,E_2A\varepsilon_1],
 \quad B=YX^{-1}.
 \tag{31.3}
$$
Then all displayed inverses exist, $A,B$ are orthogonal, and
$$
 F_4=\frac13(B\oplus A)
       \operatorname{diag}(1,\sqrt2,2,\sqrt\alpha,\sqrt\beta)
 \tag{31.4}
$$
is a real invertible strict contraction with $n(F_4)=4$.

Proof.
The numbers satisfy
$1<\alpha<2<\beta<4$, $\alpha+\beta=127/34$ and
$\alpha\beta=3$. Direct substitution gives
$$
 w_i=\frac{(r_i-\alpha)(r_i-\beta)}{\prod_{j\ne i}(r_i-r_j)}.
$$
Thus (22.6) of the boundary volume makes $\alpha,\beta$ the
compression eigenvalues on $n_0^\perp$. The displayed formulas for
$u,v$ are nonzero eigenvectors: projecting
$(\operatorname{diag}(r)-\alpha I)u$ gives zero, and their inner
products with $n_0$ vanish by the compression resolvent equation.
Distinctness of the compression eigenvalues makes $E$ orthonormal.
Moreover $E^T\operatorname{diag}(r)E=\operatorname{diag}(\alpha,\beta)$,
so $\widetilde E$ is orthonormal too.
Its unit normal is the normalization $\widetilde n$ of $D_R^{-1}n_0$,
with squared coordinates
$$
 \widetilde w=(4/17,16/51,23/51).
 \tag{31.5}
$$
Consequently $\|a\|^2=1-\widetilde w_1=13/17$
and $\|b\|^2=1-w_2=13/17$. The matrices $[a,Ja]$ and $[b,Jb]$
have the same positive scalar column Gram and positive determinant;
$A$ is a rotation satisfying $Aa=b$.

The relative frame Grams are
$$
 \widetilde E^T\widetilde E_1=2aa^T-I_2,\qquad
 E_1^TE_2=E^TS_2E=2bb^T-I_2,
$$
so
$$
 A^T(E_1^TE_2)A=\widetilde E^T\widetilde E_1.
 \tag{31.6}
$$
The first two columns of $X$ are orthonormal. The normal component of
its third column is
$2\widetilde n_1(\widetilde E\varepsilon_1)_1\ne0$, since both
factors are nonzero. Hence $X$ is nonsingular. Equation (31.6)
gives $X^TX=Y^TY$, so $B$ is orthogonal. Its definition gives
$B\widetilde E=E_1A$ and equality on the first column of
$B\widetilde E_1$ and $E_2A$. Equality on the second column follows
by comparing inner products with the three columns of $Y$: the first
two comparisons are (31.6), and the third is orthogonality to their
common first column. Since $Y$ spans, this proves
$$
 B\widetilde E=E_1A,\qquad B\widetilde E_1=E_2A.
 \tag{31.7}
$$
Thus $F_4^TF_4=\operatorname{diag}(1,2,4,\alpha,\beta)/9$,
which is positive definite and strictly below $I$.

Put $E_0=E$ and
$$
 U_j=\operatorname{span}_{\mathbb C}
       \{e_4+iE_j\varepsilon_1,\ e_5+iE_j\varepsilon_2\},
 \qquad j=0,1,2.
 \tag{31.8}
$$
Here the columns of $E_j$ are embedded in $R$. These are listed
planes in $\mathscr S_{F_4^TF_4}$.
Using $D_RE=\widetilde E\operatorname{diag}(\sqrt\alpha,\sqrt\beta)$
and the same identity after $S_1$, (31.7) gives
$F_4U_0=U_1$ and $F_4U_1=U_2$. Their normals form the chain
$$
 \mathbb Rn_0\longrightarrow\mathbb RS_1n_0
                    \longrightarrow\mathbb RS_3n_0.
 \tag{31.9}
$$
They are three distinct lines.

There are no other listed-normal transitions. If a third distinct input
normal had a listed image, Lemma 28.1 applied to
$H=\rho^{-1}F_4^{-T}$ on $R$ would permute the four normals, where
$\rho^2=27/8$ for this scaled Gram matrix.
Taking column Grams in (28.2) would force the multiset
$$
 \left\{\frac{w_i/r_i}{\sum_jw_j/r_j}:i=1,2,3\right\}
$$
to equal $\{w_1,w_2,w_3\}$. The first is (31.5), but
$16/51$ equals none of $3/34,4/17,23/34$.
This contradiction excludes a third input. Each input has at most one
image, so (31.9) is the whole normal graph. It has no cycle and no
path longer than three positions. Equation (31.8) attains that length;
Lemma 20.1 gives $n(F_4)=4$.

An explicit last-failure lawful pair uses the real orthonormal frame
$f_1=e_4,f_2=u,f_3=e_5,f_4=v$ and
$$
 S=I_5/5,\quad
 A_4=\epsilon(J^f_{13}-J^f_{24}),\quad
 B_4=\epsilon(J^f_{14}+J^f_{23}),\qquad0<\epsilon<1/5.
 \tag{31.10}
$$
It is the construction (20.3) for $U_0$. Its strictly positive states
have equal stipulated data through depth three and unequal data at
depth four. $\square$

## 32. A legal filter attaining depth five

**Proposition 32.1 (an explicit calibration attaining the finite maximum).**
Put
$$
 m=\sqrt{2/3},\quad n=1/\sqrt3,\quad
 C=\frac{m-n}{\sqrt2},\quad S=-\frac{m+n}{\sqrt2},\quad
 c_2=Ce_2+Se_3,\quad c_3=-Se_2+Ce_3.
 \tag{32.1}
$$
Define the real matrix $O$ by
$$
 Oe_1=ne_1+me_4,\quad Oe_2=-e_5,\quad Oe_3=c_3,
 \quad Oe_4=-me_1+ne_4,\quad Oe_5=c_2,
$$
and set
$$
 F_5=\frac12O\operatorname{diag}(1,1,1,\sqrt2,\sqrt3).
 \tag{32.2}
$$
Then $F_5$ is an invertible strict contraction and $n(F_5)=5$.

Proof.
The columns of $O$ are orthonormal, using $m^2+n^2=C^2+S^2=1$.
Thus $F_5^TF_5=\operatorname{diag}(1,1,1,2,3)/4$.
Let $T=2F_5$. Scaling preserves depth by Lemma 27.4.
This is case I of Lemma 30.1 with
$$
 a=1,\quad b=2,\quad c=3,\quad x=n,\quad h=m,
 \quad a_j=e_j\ (1\le j\le3),\quad c_1=-e_1.
$$
Here the $m,n$ in (30.9) are exactly those in (32.1).
The complete exceptional list (30.10), with its unique representatives
in $H_+=\ker(e_4^T+i\sqrt2e_5^T)$, is
$$
 U_{r,\zeta}=\operatorname{span}_{\mathbb C}
 \left\{e_1+i(-rn e_2+\zeta m e_3),
 e_4+\frac i{\sqrt2}(-rm e_2-\zeta n e_3+e_5)\right\}.
 \tag{32.3}
$$
Their unit normal parameters in (30.11) are
$u_{r,\zeta}=rm e_2+\zeta n e_3$.
The output parameter (30.12) is
$$
 -\frac r{\sqrt2}(c_2+\zeta c_3).
 \tag{32.4}
$$
Since $(c_2+c_3)/\sqrt2=me_2-ne_3$, the only transitions whose
image normals are exceptional normals are
$$
 (+,+)\longrightarrow(-,+),\qquad
 (-,+)\longrightarrow(+,-).
 \tag{32.5}
$$
For $\zeta=-1$, the two output directions are perpendicular to
$me_2-ne_3$, hence are $\pm(ne_2+me_3)$; neither is an exceptional
parameter because $m\ne n$. This excludes every other exceptional-target
normal transition.

Both arrows (32.5) are actual plane transitions. Here is an explicit
check retaining their conjugation signs. Decompose
$E=V\oplus R$ with
$V=\operatorname{span}(e_1,e_4)$ and
$R=\operatorname{span}(e_2,e_3,e_5)$, and use these ordered bases.
The two matrices of $T$ are
$$
 A_0=\begin{pmatrix}n&-\sqrt2m\\m&\sqrt2n\end{pmatrix},\qquad
 T_R=\begin{pmatrix}0&-S&\sqrt3C\\0&C&\sqrt3S\\-1&0&0\end{pmatrix}.
$$
The imaginary graph matrix of (32.3) is
$$
 K_{r,\zeta}=
 \begin{pmatrix}-rn&-rm/\sqrt2\\
                 \zeta m&-\zeta n/\sqrt2\\
                 0&1/\sqrt2\end{pmatrix}.
$$
Substitution of (32.1), $m=\sqrt2n$ and $n^2=1/3$ gives
$$
 T_RK_{+,+}=K_{-,+}A_0,\qquad
 T_RK_{-,+}=-K_{+,-}A_0.
 \tag{32.6}
$$
For example the columns on the left are, for general $r,\zeta$,
$$
 \zeta m c_3+rn e_5,\qquad
 -\frac{\zeta n}{\sqrt2}c_3+
       \sqrt{\frac32}c_2+\frac{rm}{\sqrt2}e_5;
$$
comparison with the displayed right matrices verifies each equality
coordinate by coordinate. Comparison of real and imaginary graph
parts now gives
$$
 TU_{+,+}=U_{-,+},\qquad TU_{-,+}=\overline{U_{+,-}}.
 \tag{32.7}
$$
Thus the graph on the complete exceptional set is precisely the
three-vertex chain in (32.5), with the fourth vertex having no incident
edge within that set. The vertex $[U_{+,-}]$ is itself exceptional,
so its image is still in $\mathscr S_G$, but that image is not
exceptional by (32.4). The chain therefore yields four positions in
$\mathscr S_G$. Every run with at least two positions starts in the
complete exceptional list, and every position except its last must
remain in that list. Its longest internal chain has three vertices;
therefore no run has five positions. Lemma 20.1 gives $n(F_5)=5$.

For an explicit lawful last-failure pair take
$$
 f_1=e_1,\quad f_2=-ne_2+me_3,\quad f_3=e_4,\quad
 f_4=(-me_2-ne_3+e_5)/\sqrt2.
$$
This four-frame is orthonormal, and
$U_{+,+}=\operatorname{span}(f_1+if_2,f_3+if_4)$.
Hence
$$
 S=I_5/5,\quad
 A_5=\epsilon(J^f_{13}-J^f_{24}),\quad
 B_5=\epsilon(J^f_{14}+J^f_{23}),\qquad0<\epsilon<1/5
 \tag{32.8}
$$
gives strictly positive non-sign sources with equal data through
depth four and unequal data at depth five. $\square$

## 33. The complete spectrum for the original comparison domain

**Theorem 33.1 (complete attained spectrum and sharp finite maximum).**
For Definition 27.1 and Assumption 27.2,
$$
 \boxed{\mathfrak D=\{2,3,4,5,\infty\}}.
 \tag{33.1}
$$
The universal finite maximum is five and is attained by (32.2).
Explicit representatives for the other values are
$$
 F_2=\operatorname{diag}(1,2,3,4,5)/6,\qquad
 F_3=P_\pi\operatorname{diag}(1/2,1/2,1/2,1/3,1/3),
 \quad\pi=(1\ 4)(2\ 5\ 3),
$$
$$
 F_4\text{ of (31.4)},\qquad F_\infty=I_5/2,
 \qquad P_\pi e_i=e_{\pi(i)}.
 \tag{33.2}
$$
For every finite answer, separation holds for every lawful common-$S$
pair, including every singular support. Each representative of depth
$d<\infty$ has a strictly positive common-$I_5/5$ non-sign collision
through $d-1$; the infinity representative has one pair valid at every
depth.

Proof.
The exhaustive seven Gram rows are supplied by Theorem 24.1 of the
boundary volume. Proposition 29.1 bounds every finite case outside
the extreme-triple row by five; Proposition 30.2 covers both extremes.
Lemma 20.2 excludes depths zero and one. Corollary 25.1 supplies
$n(F_2)=2$, Proposition 25.3 supplies $n(F_3)=3$, and the scalar row
of Theorem 24.1 supplies $n(F_\infty)=\infty$. Their attainments and
witnesses are reused with those attributions. Propositions 31.1 and
32.1 prove the two remaining attainments with their actual legal filters.
This proves all memberships and all exclusions in (33.1).

All exclusions begin with a run and rule it out for the actual single
$F$ and its own $G=F^TF$. Lemma 20.1 begins with any lawful non-sign
collision and produces just such a run, without a regular-support
assumption. Conversely (20.3) produces lawful witnesses from the runs;
(31.10) and (32.8) specify the two new ones. Thus no singular source
face is discarded and no graph realizability assumption is used.

Proposition 26.1 of the boundary volume identifies these coordinates
with the original detector laws. In particular, for all-success
probability $p_j=\operatorname{tr}(F^jS(F^T)^j)>0$,
$$
 p_j^2K(A_j/p_j)=K(A_j).
$$
This is valid for singular $S$ too. Branch flag probabilities depend
only on the common $S$; failures remain visible and charged under
Assumption 27.2. All changes of basis above are calculations in the
known calibration, not source identifications or experimental settings.
The target is exactly common sign. No later $b$, new control, tensor
panel or joint acquisition of incompatible histories is assumed.

The conclusion is least depth for exact laws. It makes no finite-record
exactness, physical realization, hardware or sample optimum, or resource
saving assertion. In particular the existing $F_2$ schedule of
Proposition 10.2 and (10.5) retains its supplied $115N$ preparations
and $155N$ padded bits. The new inference is the complete spectrum,
its sharp maximum, and the two actual attainers, using the supplied
per-filter classification and classical ingredients. $\square$

## 追加锚（本行以下为增补区）
