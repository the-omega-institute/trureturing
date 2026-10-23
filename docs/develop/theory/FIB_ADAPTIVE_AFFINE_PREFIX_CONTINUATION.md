# Adaptive continuation after affine calibration

This volume isolates an adaptive continuation gap left by the fixed-path affine recovery results. The calibration prefix is fixed, but the continuation may choose arbitrary finite $M/J$ words, stop, and answer from the acquired history. The exact number of additional reads is

$$
q_{\mathrm{ad}}(0)=2,\qquad q_{\mathrm{ad}}(d)=3\quad(d\ge1).
\tag{0.1}
$$

The result is a continuation theorem only. It does not give the unrestricted adaptive optimum when the initial calibration prefix itself may be chosen adaptively.

All statements are ordinary exact mathematics. No Lean, Scribe, or Reg declaration is added.

## 1. Contract and prefix

Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix}.
$$

The effective relation is

$$
S=\begin{pmatrix}p&q\\r&s\end{pmatrix},
\qquad p,q,r,s>0,\qquad ps=qr,
$$

and the readings are

$$
z_i=(1+\kappa i)\operatorname{tr}(A_iS)+D(i),
\tag{1.1}
$$

with real $\kappa$ and $\deg D\le d$. The source is one fixed positive rank-one source with one fixed positive row, and all cumulative matrices are produced on one forward trajectory. There is no reset, copy, inverse acquisition, or second observation channel. A finite composite $M/J$ word is one continuation action; after a read the clock index advances by one, while an unread atom does not.

Set

$$
B=\max\{d+1,2\}.
$$

The fixed prefix reads $B$ times at $I$, then once at $U$, then once at $U^2$. Thus its total length is $B+2$ and its clock indices are $0,\ldots,B+1$. The continuation starts at index

$$
j=B+2.
\tag{1.2}
$$

Define $q_{\mathrm{ad}}(d)$ to be the least uniform number of further reads after this prefix for which some causal deterministic continuation protocol recovers the complete target $(S,\kappa,D)$ for every legal world. The continuation may use arbitrary history-dependent finite words, stopping and answers, without continuity, measurability, computability, or other regularity assumptions.

The prefix itself produces the polynomial

$$
P(t)=D(t)+a(1+\kappa t),
\qquad a=\operatorname{tr}(S)=p+s.
\tag{1.3}
$$

For $d=0$, the two initial identity reads make $P$ affine and the first two calibration differences recover $r$ and $\kappa$ without dividing by a sampled gain.

## 2. Main theorem

### Theorem 2.1 (exact adaptive continuation count)

Under the contract above,

$$
\boxed{q_{\mathrm{ad}}(0)=2,\qquad q_{\mathrm{ad}}(d)=3\ \text{for every }d\ge1.}
\tag{2.1}
$$

For $d\ge1$, the three-read upper bound is the existing fixed continuation after the same prefix. The new content is that two reads cannot suffice even when the continuation is fully adaptive. For $d=0$, an adaptive two-read continuation is sufficient, and one further read is impossible.

### Proof: the positive-degree lower bound

Assume $d\ge1$ and consider a protocol using at most two continuation reads. Write $j=B+2$ and

$$
g(t)=1-\frac{t}{j}.
$$

For $x>0$ and $0<u<x$ define

$$
S_x(u)=
\begin{pmatrix}
x-u&u(x-u)\\
1&u
\end{pmatrix},
\qquad
D_x(t)=-xg(t).
\tag{2.2}
$$

The matrix is strictly positive and rank one because

$$
S_x(u)=(x-u,1)^{\mathsf T}(1,u).
$$

Also

$$
\operatorname{tr}(S_x(u))=x,\qquad
\operatorname{tr}(US_x(u))=x+1,\qquad
\operatorname{tr}(U^2S_x(u))=x+2.
\tag{2.3}
$$

Use the same gain $1+\kappa t=g(t)$ in every world. At each of the first $B$ identity reads,

$$
g(i)\operatorname{tr}(S_x(u))+D_x(i)=0.
$$

At the two shear reads, (2.3) gives

$$
z_B=g(B)=\frac2j,\qquad
z_{B+1}=2g(B+1)=\frac2j.
\tag{2.4}
$$

Thus every $x,u$ produces the same complete prefix history, including the actions chosen before the continuation.

The first continuation action is therefore fixed by this common history. At index $j$, the gain and drift both vanish, so its read is $z_j=0$ for every cumulative matrix. If the protocol stops there, any two different matrices in the family already give a failure.

Otherwise the second continuation action is also fixed by the same common history. Let its final cumulative matrix be

$$
T=\begin{pmatrix}A&b\\C&E\end{pmatrix}.
$$

Every product of $M$ and $J$ has nonnegative integer entries and determinant $\pm1$. If $C=0$, then $AE=\det T=\pm1$ forces $A=E=1$, and

$$
\operatorname{tr}(TS_x(u))-x=b
\tag{2.5}
$$

is independent of $x,u$. Choose two distinct values of $u$.

Suppose $C>0$. Set

$$
x=1+\frac{|E-A|}{C},
\qquad
u_*=\frac{x+(E-A)/C}{2}.
\tag{2.6}
$$

Then $0<u_*<x$. For

$$
\Phi_x(u)=\operatorname{tr}(TS_x(u))-x
=(A-1)x+b+(E-A)u+C\,u(x-u),
\tag{2.7}
$$

the vertex is $u_*$, so two distinct points $u_*-\varepsilon$ and $u_*+\varepsilon$ in $(0,x)$ have the same value. At index $j+1$ the common drift is $D_x(j+1)=x/j$ and the gain is $-1/j$, hence

$$
z_{j+1}=-\frac{\Phi_x(u)}{j}.
\tag{2.8}
$$

The two worlds therefore have the same second continuation read as well, while their effective relations differ. They also share the same fixed gain and the same fixed affine drift. All parameters were chosen before the run and never changed.

Stopping at any earlier point gives the same answer on two different targets; continuing to the second read gives the collision above. Thus no adaptive continuation with two reads is uniformly correct, and

$$
q_{\mathrm{ad}}(d)\ge3\qquad(d\ge1).
\tag{2.9}
$$

### Proof: the constant-drift lower bound

Now let $d=0$. Use the family

$$
S(p,u)=
\begin{pmatrix}p&pu\\1&u\end{pmatrix},
\qquad p,u>0,
\qquad
\kappa=0,\qquad
D(t)=-(p+u).
\tag{2.10}
$$

It is strictly positive and rank one. The common prefix readings are

$$
(0,0,1,2),
\tag{2.11}
$$

because the two identity readings have signal $p+u$, the $U$ signal is $p+u+1$, and the $U^2$ signal is $p+u+2$.

With only one continuation read, the first word is fixed by this common history. Let its cumulative matrix after the prefix be

$$
T=WU^2=\begin{pmatrix}A&b\\C&E\end{pmatrix},
$$

where $W$ is the chosen finite $M/J$ word. The read at index $4$ is

$$
\Psi_T(p,u)
=\operatorname{tr}(TS(p,u))-(p+u)
=(A-1)p+b+(E-1)u+C\,pu.
\tag{2.12}
$$

If $C=0$, then $AE=\det T=\pm1$ and nonnegativity force $A=E=1$, so $\Psi_T=b$ is constant.

If $C>0$, write $W=\begin{pmatrix}a&b_0\\c&e_0\end{pmatrix}$. Then

$$
T=WU^2=
\begin{pmatrix}a&2a+b_0\\c&2c+e_0\end{pmatrix},
$$

so $E\ge2C$ and $E-1+Cp>0$ for every $p>0$. Fix any positive point $(p_0,u_0)$ and let $h=\Psi_T(p_0,u_0)$. In a neighborhood of $p_0$ the level set $\Psi_T(p,u)=h$ is the graph

$$
u(p)=\frac{h-b-(A-1)p}{E-1+Cp}.
\tag{2.13}
$$

It contains the positive point $(p_0,u_0)$ and remains positive for nearby distinct $p$. Hence two different legal targets have the same complete prefix and the same continuation read. No one-read continuation can recover the target, so

$$
q_{\mathrm{ad}}(0)\ge2.
\tag{2.14}
$$

### Proof: the two-read upper bound when $d=0$

For the fixed prefix, put

$$
P(t)=z_0+(z_1-z_0)t.
\tag{2.15}
$$

At the two shear reads define

$$
v_0=z_2-P(2),\qquad
v_1=\frac{z_3-P(3)}2.
\tag{2.16}
$$

Since the prefix matrices are $U$ and $U^2$,

$$
v_0=r(1+2\kappa),\qquad
v_1=r(1+3\kappa).
$$

Therefore

$$
r=3v_0-2v_1>0,\qquad
\kappa=\frac{v_1-v_0}{r}.
\tag{2.17}
$$

No sampled gain is divided out.

If $\kappa=0$, use the two continuation cumulative matrices

$$
F=M^2U^2=\begin{pmatrix}1&3\\1&4\end{pmatrix},
\qquad
G=JF=\begin{pmatrix}1&4\\1&3\end{pmatrix}.
\tag{2.18}
$$

The gain is one at both continuation indices. From the two residuals

$$
X=\bigl(z_4-P(4)\bigr)-3r=q+3s,
\qquad
Y=\bigl(z_5-P(5)\bigr)-4r=q+2s,
\tag{2.19}
$$

we obtain

$$
s=X-Y,\qquad q=Y-2s,\qquad p=\frac{qr}{s},
\qquad a=p+s.
\tag{2.20}
$$

The positive rank-one identity $ps=qr$ gives the displayed $p$ directly from the recovered $q,r,s$. Finally $D=P-a$ is constant.

If $\kappa\ne0$, then

$$
a=\frac{z_1-z_0}{\kappa}>0,\qquad D=z_0-a.
\tag{2.21}
$$

The remaining relation entry is $s\in(0,a)$, with

$$
p=a-s,\qquad q=\frac{s(a-s)}r.
\tag{2.22}
$$

Choose an integer $n>2+a/r$, let $L=MJ$, and execute the finite word $U^nL$ after the prefix. Its cumulative matrix is

$$
T=U^nLU^2=
\begin{pmatrix}n+1&3n+2\\1&3\end{pmatrix}.
\tag{2.23}
$$

As a function of $s$,

$$
f(s)=\operatorname{tr}(TS)
=(n+1)a+(3n+2)r+(2-n)s+\frac{s(a-s)}r,
\tag{2.24}
$$

and

$$
f'(s)=2-n+\frac{a-2s}{r}<0
\qquad(0<s<a).
\tag{2.25}
$$

If the gain at index $4$ is nonzero, the first continuation read gives $f(s)$ after subtracting $D$ and dividing by that known gain, so strict monotonicity recovers $s$.

If the gain at index $4$ is zero, execute $JJ$ after the first continuation read. The cumulative matrix returns to $T$ at index $5$, while $1+5\kappa\ne0$ because two distinct clock indices cannot both be roots of the nonzero affine gain. The second read then recovers $f(s)$ and hence $S$.

Thus two continuation reads recover $(S,\kappa,D)$ for every constant-drift world, giving

$$
q_{\mathrm{ad}}(0)\le2.
\tag{2.26}
$$

For $d\ge1$, the three-read continuation in Theorem 2.1 of [Shared affine gain and zero-crossing recovery](FIB_SHARED_AFFINE_GAIN_ZERO_CROSSING_RECOVERY.md) applies to this same prefix and gives $q_{\mathrm{ad}}(d)\le3$. Combining (2.9), (2.14), and (2.26) proves (2.1). ∎

## 3. Model validation remains a separate question

Theorem 2.1 is an in-model recovery theorem after a fixed calibration prefix. It does not certify that the drift really has degree at most $d$ outside the acquired clock points. Corollary 39.4 of [FIB self-calibrating relation mathematics](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS.md) already gives the finite-history obstruction: add a nonzero polynomial vanishing at all acquired indices to preserve the transcript and change a future value. The same perturbation preserves an adaptive history because identical past readings force identical causal actions.

Therefore the new adaptive result has three distinct boundaries:

- two continuation reads are enough for target recovery only in the constant-drift prefix contract;
- three are necessary for every $d\ge1$ after that prefix, even with arbitrary adaptive continuation;
- neither recovery statement validates an undeclared larger drift class. A withheld read can falsify one predicted continuation, while a universal model certificate needs a declared finite-determining class and its full compatibility check.

## 4. Relation to existing results and scope

The fixed-path theorem supplies the three-read upper bound and the exact prefix contract. Its two-read obstruction applies only to predetermined continuations. The present lower bound chooses the collision worlds after the first continuation word is fixed by a common actual history; this is the new adaptive quantifier. The constant-drift upper bound uses a data-dependent finite word and a monotone positive fiber, which is not a fixed-path construction.

The result does not settle the unrestricted adaptive problem in which the initial calibration prefix may itself depend on the readings. It does not change the existing fixed-path value $d+5$ for $d\ge1$, the known $d=0$ fixed-path bounds, or the separate polynomial-gain and every-atom cubic contracts. It is not a randomized, noisy, bit-complexity, time, atom-cost, physical-realization, or Lean-certification statement.

The proof uses exact real arithmetic and permits an unbounded data-dependent finite atom count in the $d=0$, $\kappa\ne0$ branch. The lower bounds use fixed parameters throughout each run, strictly positive rank-one sources, and the original single trajectory. No world is changed after observing a response.
