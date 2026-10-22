---
bibkey: trureturing2026nearpricebenefit
authors: trureturing research synthesis
year: 2026
title: Actual CA own-price benefit from full threshold capacity
doi: null
url: https://hal.science/hal-05389053v1
claim: "Existing full prime-power capacity gives a quadratic upper allowance for the own-price defect of actual strict CA products; a source-specific root-scale transfer still retains the complete signed Robin integral."
strata_touched: []
license: citation-only
triage: anchor
---

# Actual CA own-price benefit from full threshold capacity

This is an application of the classical CA benefit and existing project
capacity, not a new prime-distribution theorem. It continues the
[actual strict products and pressure account ACC1–ACC9](nicolas2025comparison.md#a-complete-pressure-balance-at-the-unchanged-observation).
The complete proofs of the external analytic suppliers are not audited
here. No literature priority or Lean certification is claimed.

For $n\ge1$ and $y>1$, use

$$
W(n)=\log\frac{\sigma(n)}n,\qquad
s_y=y\log y,\qquad \lambda(y)=s_y^{-1},
$$

$$
r_{p,j}=\frac1{\log p}
 \log\frac{1-p^{-j-1}}{1-p^{-j}},\qquad
M(q)=\max_{n\ge1}\{W(n)-q\log n\}\quad(q>0).
$$

The actual strict inventory and its own-size clock are

$$
N_x=\prod_p p^{a_p(x)},\qquad
 a_p(x)=\#\{j\ge1:r_{p,j}>\lambda(x)\},\qquad
 A_x=\log N_x.
$$

Every equality layer is excluded, and every positive prime-power layer
is retained. ACC3 gives
$W(N_x)=M(\lambda(x))+\lambda(x)A_x$. Define the full own-price defect

$$
d_A(n)=M(\lambda(A))-W(n)+\lambda(A)\log n\ge0,
\qquad T_A=\sqrt A\log A\quad(A>1).
$$

The existing effective PNT and complete higher inventory give, for
some fixed $a>0$,

$$
A_x=x+O(xe^{-a\sqrt{\log x}}),\qquad A_x\sim x.
\tag{NP0}
$$

Only the full strict integer $N_x$ is used below; no independently
optimized configurations are combined.

## A finite upper benefit bound at the same strict inventory's own price

The existing [arbitrary-host benefit and thin-layer capacity
TC.1](erdosnicolas1975repartition.md#an-explicit-thin-layer-capacity-for-the-same-arbitrary-host)
can bound the complete own-price defect of ACC's actual $N_x$.
This applies a classical benefit calculation to two specified prices;
it introduces no new capacity or prime-distribution theorem. The
capacity's Yamada and Dusart inputs remain external, and this
application has no Lean certification or literature-priority claim.

Use the same strict integer $N_x$, $A=\log N_x$, $s_y=y\log y$ and
$\lambda(y)=1/s_y$. Suppose $x>1$, $A\ge16$, and put

$$
h=\left|\frac{s_A}{s_x}-1\right|\le\frac14.
$$

Let $C_A$ be the **maximal** optimizer at $\lambda(A)$, so it includes
every layer with $r_{p,j}\ge\lambda(A)$. The source $N_x$ includes
exactly the layers with $r_{p,j}>\lambda(x)$. For each prime, let
$\mathscr J$ contain exactly the positive layers lying between these
two actual exponent counts:

$$
\mathscr J=
\{(p,j):p\text{ prime},\
 \min(v_p(C_A),v_p(N_x))<j\le
 \max(v_p(C_A),v_p(N_x))\}.
$$

This is finite. If a layer belongs to $\mathscr J$, its marginal
lies between $\lambda(A)$ and $\lambda(x)$, with the appropriate
endpoint inclusion. Therefore every crossed layer satisfies

$$
|s_A r_{p,j}-1|\le h,\qquad
|r_{p,j}-\lambda(A)|\le h/s_A.
$$

In particular a layer tied at $\lambda(A)$ has zero benefit cost,
while a layer tied at $\lambda(x)$ is still inside the same weak band.
The bound does not require $N_x$ to be superabundant, GA1, GA2,
or optimal at its own-size price.

The classical layerwise benefit identity at the **own-size** price is

$$
\begin{aligned}
d_A(N_x)
&=M(\lambda(A))-W(N_x)+\lambda(A)A\\
&=\sum_{(p,j)\in\mathscr J}
       \log p\,|r_{p,j}-\lambda(A)|.
\end{aligned}
$$

TC.1 with parameter $a=A$ bounds the full weak-band resource by
$24Ah+32\sqrt A$. Since $\mathscr J$ is a subset of that band,

$$
\boxed{
0\le d_A(N_x)
\le\frac{24Ah^2+32\sqrt A\,h}{A\log A},\qquad
T_A d_A(N_x)\le24\sqrt A\,h^2+32h.
}
\tag{NPC1}
$$

This is a finite bound with an explicit hypothesis on the two actual
prices. It accounts for every changed prime-power layer.

For ACC4's unconditional family, $A\sim x$ and the mean-value theorem
for $y\log y$ gives $h=O(e^{-a\sqrt{\log x}})$. Consequently (NPC1)
strengthens ACC5's linear PNT allowance to

$$
d_{A_x}(N_x)=O(e^{-2a\sqrt{\log x}}/\log x).
\tag{NPC1a}
$$

The first term of NPC1 is
$O(e^{-2a\sqrt{\log x}}/\log x)$, and the second is
$O(e^{-a\sqrt{\log x}}/(\sqrt x\log x))$, which is smaller.
The PNT and the constant $a$ are the same as in ACC4. The normalized
allowance still contains $O(\sqrt x e^{-2a\sqrt{\log x}})$;
its growth prevents this allowance from paying a root-scale defect
bound on the whole unconditional family. No lower bound on the
actual defect is inferred from that growth. The original signed
Robin integral remains unpaid.


### A conditional root-scale transfer for the same actual integers

Let $x$ range over any unbounded family of real prices for which

$$
\delta_x:=|A_x-x|=o(x^{3/4}).
\tag{NPC2}
$$

This condition implies $A_x\sim x$. The mean-value theorem for
$y\log y$ on the interval with endpoints $x,A_x$ gives
$h_x=O(\delta_x/x)$, with one common constant once
$A_x\in[x/2,2x]$. In particular the finite hypotheses of (NPC1)
hold eventually along the entire specified family, and

$$
0\le T_{A_x}d_{A_x}(N_x)
=O\!\left(\frac{\delta_x^2}{x^{3/2}}+
                 \frac{\delta_x}{x}\right)=o(1).
\tag{NPC3}
$$

There is no substitution of $x$ for the source's own clock $A_x$ in
the defect or its normalization. The exponent $3/4$ here comes from
the quadratic capacity allowance; it is a sufficient condition, not
a necessity or an optimal exponent.

Use KTO1's existing complete pressure identity and two-candidate
reserve at $A=A_x$:

$$
M(\lambda(A))
=\gamma+\log\log A-\frac1{\log A}-I_\psi(A)-R(A),
\qquad
T_AR(A)=c_R+O(1/\log A),\quad c_R=2(\sqrt2-1).
$$

Since $\lambda(A)\log N_x=1/\log A$, the same integer has the
exact margin account

$$
\Delta(N_x)=d_A(N_x)+I_\psi(A)+R(A),\qquad A=A_x.
$$

Thus (NPC2), with the cited reserve and capacity inputs, gives

$$
\boxed{
T_{A_x}\Delta(N_x)
=T_{A_x}I_\psi(A_x)+c_R+o(1).
}
\tag{NPC4}
$$

For example, on such a family a lower bound
$\liminf T_{A_x}I_\psi(A_x)>-c_R$ would imply eventual strict
Robin there; an upper bound
$\limsup T_{A_x}I_\psi(A_x)<-c_R$ would imply eventual violations
there. Neither signed premise is supplied. An asymptotic comparison
at equality with $-c_R$ does not decide strict Robin.

ACC4's unconditional PNT allowance does not imply (NPC2): its ratio
to $x^{3/4}$ grows. The existing full-real inventory normal form
$A_x=\psi(x)+(\sqrt2-1)\sqrt x+o(\sqrt x)$, cited in
[the workload note](../Analytic/mantovanelli2026primeworkload.md#the-full-real-normal-form-also-controls-strict-inventory-at-events),
identifies (NPC2) with $\psi(x)-x=o(x^{3/4})$ on this same family.
This gives a checkable condition on the actual prime error; it does
not establish that condition at every large price or at the unknown
counterexample-selected prices.

The finite upper benefit estimate and this conditional transfer reuse
the classical CA benefit, the already derived thin-layer capacity,
and the existing reserve and inventory normal form. No new signed
prime estimate or assumption of RH is introduced. The full original
same-source signed budget, strict Robin for every integer above 5040,
and RH remain unresolved; this application has no Lean verification.
