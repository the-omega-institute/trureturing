---
bibkey: alvarezcruz2026colombeau
authors: Amaury Alvarez Cruz; Esteban A. Alvarez Gutierrez
year: 2026
title: Multiplicative Colombeau algebras and the Nyman--Beurling criterion for the Riemann hypothesis
doi: null
url: https://arxiv.org/abs/2606.22562v3
claim: The preprint reformulates Nyman--Beurling using multiplicative Colombeau nets; its specified exponential net has a local second-order obstruction to the stronger negligibility conclusion, while its L2 convergence question remains separate.
strata_touched: []
license: citation-only
triage: anchor
---

# A multiplicative Colombeau formulation of Nyman--Beurling

The inspected source is [arXiv:2606.22562v3](https://arxiv.org/pdf/2606.22562v3),
updated 29 September 2026 and first posted on 21 June 2026, according to the
versioned arXiv metadata. The manuscript heading says May 2025; that is not
the arXiv posting date. Its theorem
statements are recorded as literature input; the proof was not independently
audited here, and no Lean verification is claimed.

The source forms polynomially damped Báez--Duarte sums

$$
f_{\delta,n}(x)=\sum_{k\le n}\mu(k)k^{-\delta}\,\{1/(kx)\}
$$

and regularizes them by Mellin convolution. Theorem 8.1 fixes the polynomially
damped net of Section 4, with
$\delta(\varepsilon)=(\log(1/\varepsilon))^{-\alpha}$, $0<\alpha<1$,
and $n(\varepsilon)=\lfloor\varepsilon^{-M}\rfloor$, $M>0$.
It states that RH holds exactly when this net is moderate, associated with
$-\iota(\mathbf1_{(0,1)})$, and uniformly bounded in $L^2(0,1)$.
The minus sign belongs to this specified Möbius convention. The converse is
obtained through the classical Nyman--Beurling criterion and Mazur's theorem.
The separate power-law estimate in Theorem 9.1 assumes RH as well as simplicity
and the stated separation condition for the nontrivial zeros; the paper leaves
exponential damping error as an open problem. Its separate stronger
negligibility conclusion is subject to the local obstruction below.

## Boundary for the FIB route

This source supplies a modern analytic completion of the discrete Möbius
approximation criterion. It does not identify the project's FIB five-window
addresses, affine family $1+F_rg$, or four-phase operator with the Beurling
generators, and it supplies no bound for $\sigma(N_g)/N_g$. The Mellin
regularization therefore cannot be applied to the FIB geometry without a new
source-preserving embedding and a proof that the induced coefficients are the
same Möbius coefficients.

The reusable interface is the separation between association and uniform
$L^2$ boundedness. Any FIB-to-Nyman construction must prove both properties;
pointwise convergence of a FIB projection alone is insufficient.

## The specified exponential net has a local rate obstruction

The negligibility conclusion in Conjecture 7.1 is stronger than the
$L^2$ convergence asked for in Conjecture 6.2. With the literal exponential
coefficients and the regularizer of Section 2.2, its negligibility
conclusion fails already on one fixed compact interval. The following is a
repo-derived application of elementary floor identities and integral
linearity, rather than a new coefficient-recovery theorem or RH criterion.

Let $n(\varepsilon)\ge1$ be any finite cutoff, and use the source's
unbalanced generators:

$$
f_\varepsilon(x)=\sum_{k\le n(\varepsilon)}
 \mu(k)e^{-k\varepsilon^2}\{1/(kx)\},
\qquad
E_\varepsilon=(f_\varepsilon+\chi)\star\psi_\varepsilon,
\qquad \chi=\mathbf1_{(0,1)}.
\tag{L1}
$$

Both functions are extended by zero before the source's multiplicative
convolution. The regularizer is nonnegative, supported on
$[e^{-\varepsilon},1]$, and satisfies
$\int\psi_\varepsilon(y)\,dy/y=1$.
Set

$$
I=[a,b]=[2/3,3/4],\qquad
A_\varepsilon=\sum_{k\le n(\varepsilon)}
 \frac{\mu(k)e^{-k\varepsilon^2}}k,
\qquad
c_\varepsilon=\int\psi_\varepsilon(y)\,dy.
$$

If $1/2<z<1$, then $\{1/z\}=1/z-1$, while
$\{1/(kz)\}=1/(kz)$ for every integer $k\ge2$. Thus

$$
f_\varepsilon(z)+\chi(z)
 =\frac{A_\varepsilon}{z}+1-e^{-\varepsilon^2}.
\tag{L2}
$$

For $0<\varepsilon<\log(4/3)$, every $x\in I$ and every point in the
regularizer's support satisfy $1/2<x/y<1$. Consequently zero extension
causes no boundary term on $I$, and the literal convolution gives

$$
E_\varepsilon(x)
 =\frac{c_\varepsilon A_\varepsilon}{x}
   +1-e^{-\varepsilon^2}.
\tag{L3}
$$

The two endpoint readings eliminate the unknown Möbius sum:

$$
bE_\varepsilon(b)-aE_\varepsilon(a)
 =(b-a)(1-e^{-\varepsilon^2}).
$$

The triangle inequality, $(b-a)/(a+b)=1/17$, and
$1-e^{-u}\ge u/2$ for $0\le u\le1$ give

$$
\|E_\varepsilon\|_{L^\infty(I)}
 \ge\frac{1-e^{-\varepsilon^2}}{17}
 \ge\frac{\varepsilon^2}{34}.
\tag{L4}
$$

Formula (L3) is continuous on $I$, so the same bound holds for the
essential supremum. In particular the error is not $O(\varepsilon^3)$;
the zero-derivative part of Colombeau negligibility already fails.
Neither RH, zero simplicity, zero separation nor the size of the cutoff
enters this obstruction.

This excludes the specified net's negligibility conclusion, including
under an additional RH assumption. It is not a proof of the literal
negation of the conditional proposition $\mathrm{RH}\Rightarrow P$,
which would require RH as well as $\neg P$. The lower bound tends to
zero and gives no obstruction to $L^2$ convergence in Conjecture 6.2;
it also does not negate the qualitative criterion stated in Theorem 8.1.
The balanced generators in the
[Pyvovarov note](pyvovarov2026baezduarteremarks.md) are different functions
and are not substituted for (L1). No signed Robin bound or RH conclusion
follows from this local rate calculation.
