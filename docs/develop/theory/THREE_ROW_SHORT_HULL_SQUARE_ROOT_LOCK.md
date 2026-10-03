# Three-row square-root lock in a common short hull

This reference input uses the `generic-v1` digestion contract. Existing text is preserved after publication; additions and corrections belong after the final append anchor. Ordinary mathematical arguments are not kernel certificates. The formal declarations and their axiom closures, rather than this text, carry formal truth.

## Scope and notation

The offsets and both roots are real. Only the scale and the quotient are integers. Write $N=S^2$, interpreting the integer $S$ as a real number in the norm equations. All three offsets belong to one interval containing zero, not three independently selected intervals. This is a conditional arithmetic estimate, not a solution of Grimm's conjecture or a proof that an original owner system supplies its premises.

The supplied mathematical input is the caller's three-row common-short-hull candidate, with the earlier ordinary integer square-norm argument as context. The argument below is an ordinary derivation using ordered real arithmetic; no external literature or novel-priority assertion is needed. The local implementation and the independent unfrozen review have separate roles; a single implementation does not establish model diversity or consensus.

## The uniform lock

**Proposition 1 (three-row common-short-hull square-root lock).** For every even integer $S\ge8$, every odd integer $k$, and all real numbers $h,l,b,c,d,Q,P,\epsilon$, suppose

$$
\begin{gathered}
0\le h\le S-2,\qquad l\le0\le l+h,\\
l\le b\le l+h,\quad l\le c\le l+h,\quad l\le d\le l+h,\\
1\le |b|,\quad 1\le |c|,\quad 1\le |d|,\quad Q>0,\quad P>0,\\
Q^2=(N+b)(N+c)(N+d),\qquad P^2=bcd,\\
\epsilon\in\{1,-1\},\qquad Q+\epsilon P=Nk,\qquad N=S^2.
\end{gathered}
$$

Then $b>0$, $c>0$, $d>0$, and $k=S+1$.

Proof. The common interval gives $-h\le b,c,d\le h$, so every shifted factor $N+b,N+c,N+d$ is positive. Since $P^2=bcd>0$ and the offsets are nonzero, their signs are either all positive or exactly two negative.

First obtain a bound valid for either sign pattern. The product of the absolute offsets is at most $h^3$, hence $P^2\le h^3<S^3$. Since $S\ge8$, one has $S^3<(9/64)S^4$, and therefore $P<(3/8)N$.

For the two-negative pattern let the negative magnitudes be $s_1,s_2$, set $s=\max(s_1,s_2)$, and let the positive offset be $r$. The absolute-magnitude assumptions give $r\ge1$. The same interval containing these offsets gives $s+r\le h\le S-2$. The norms imply $Q\ge S(N-s)$ and $P\le s\sqrt r\le sr$. Consequently

$$
s(S+r)\le(S-r-2)(S+r)=N-2S-r^2-2r<N,
$$

and $Q-P>N(S-1)$. Also $Q^2\le N^2(N+r)$. Since $r\le S-2<S+1/4$, comparison with $(NS+N/2)^2$ gives $Q<NS+N/2$. Together with $P<(3/8)N$ this puts both $Q+P$ and $Q-P$ strictly between $N(S-1)$ and $N(S+1)$. Thus the integer $k$ must equal $S$, contrary to odd $k$ and even $S$. Symmetry excludes every placement of the two negative offsets.

All offsets are therefore positive. Set $S_1=b+c+d$ and $S_2=bc+bd+cd$. The inequality $(b-c)^2\ge0$ gives $2P\le\sqrt d(b+c)$. Since $d\le h<S<N$, one has $\sqrt d<S$, hence $2SP<N(b+c)<NS_1$. Expansion now yields

$$
Q^2-(NS+P)^2=N(NS_1+S_2-2SP)>0.
$$

Both roots are positive, so $Q-P>NS$. For the other end, $Q^2\le(N+h)^3<(N+S)^3$, while

$$
\left(NS+\frac{13}{8}N\right)^2-(N+S)^3
=\frac{S^3}{64}(16S^2-23S-64)>0.
$$

The last factor is positive for $S\ge8$. Thus $Q<NS+(13/8)N$, and $Q+P<N(S+2)$. Either value of $\epsilon$ gives $S<k<S+2$, whose only integer is $S+1$. QED.

## Inhabited real models and application boundary

For a real nonvacuity model take $S=16$, $k=17$, $h=14$, $l=0$, $d=9$, $t=\sqrt{265}$, $b=c=20t-316$, $Q=(256+b)t$, $P=3b$, and $\epsilon=1$. Squaring bounds on $t$ gives $1<b=c<14$. The identity $t^2=265$ proves both norm equations and $Q+P=5300-948=4352=256\cdot17$. A second real model uses $b=c=14t-214$ and $\epsilon=-1$, with the other parameters unchanged; then $1<b=c<14$ and $Q-P=3710+642=4352$.

Repeated offsets are allowed by Proposition 1. Neither real model is an original integer, distinct-offset, owner, kernel, factor, Hall, saturation, or compositeness instance. An actual Grimm consumer must still establish its integer casts, dyadic scale, complete kernels, odd quotient and linked sign from the same original rows. No premise of that consumer is proved here. The unresolved two-unit equality compensation and offset-junction branch, both nonzero-$K$ orientations, all exterior cofactors, and the complementary whole-Grimm arms remain outside this theorem.

## 追加锚（本行以下为增补区）
