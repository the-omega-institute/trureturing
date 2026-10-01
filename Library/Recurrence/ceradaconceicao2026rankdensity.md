---
bibkey: ceradaconceicao2026rankdensity
authors: Joaquim Cera Da Conceição
year: 2026
title: "Explicit Prime Densities for Lucas Sequence Rank Divisibility"
doi: null
url: https://arxiv.org/abs/2604.20014v3
claim: "Closed-form densities for primes whose Lucas rank of appearance is divisible by a fixed integer d, completing general cases left by Sanna; the Fibonacci all-d density problem was already solved by Cubre and Rouse, and these densities are not pointwise bounds on divisors of a specified term."
strata_touched: []
license: citation-only
triage: anchor
---

# Lucas rank-divisibility density and specified-term divisibility

The primary source is [arXiv:2604.20014v3](https://arxiv.org/pdf/2604.20014v3),
dated 22 August 2026; the first version appeared in April 2026.
The locators below refer to the introduction, Theorem 1, and Section 2 of
that version.
They do not assert an independent proof audit or Lean verification.

## The predicate and the published counting theorem

The paper takes nonzero integer parameters $a_1,a_2$ and defines $U_0=0$, $U_1=1$,
$U_{n+2}=a_1U_{n+1}-a_2U_n$, and uses
$\rho_U(p)=\min\{n\ge1:p\mid U_n\}$ when it exists.
For characteristic roots $a,b$, put $K=\mathbb Q(a)$,
$\gamma=a/b$, and $\Delta=a_1^2-4a_2$.
Section 2, printed p.4, assumes that $\gamma$ is not a root of unity and
focuses on irreducible $X^2-a_1X+a_2$; the reducible case was settled by
Wiertelak. These hypotheses remain in force for the counting statement
below.
Away from the displayed exceptional primes, the rank equals the order of
$\gamma$ in the appropriate residue field.

For a fixed positive integer $d$, the counting function is

$$
R_\gamma(d;x)
=\#\{p\le x:p\nmid2a_2\Delta,\ d\mid\operatorname{ord}_{\mathfrak p}(\gamma)
\text{ for every }\mathfrak p\mid p\}.
$$

Theorem 1, printed pp.2–3, gives an absolute constant $B>0$ such that
for $x>\exp(Bd^{40})$,

$$
R_\gamma(d;x)=\delta_\gamma(d)\operatorname{Li}(x)
+O_\gamma\!\left(
\frac d{\varphi(d)}
\frac{x(\log\log x)^{\omega(d)}}{(\log x)^{9/8}}
\right).
$$

The source supplies a cyclotomic–Kummer degree series for
$\delta_\gamma(d)$ and evaluates it in closed form in the remaining cases.
The constant in the error term may depend on $\gamma$; it is not a
uniform-in-sequence statement. The $d^{40}$ threshold must be retained
when considering a varying $d$.

## History prevents a duplicate Fibonacci result

The introduction, printed pp.1–2, attributes earlier cases to Hasse,
Wiertelak, Lagarias, Ballot, and Sanna. It explicitly says that the
Fibonacci case for all $d\ge1$ was already completed by Cubre and Rouse,
*Divisibility properties of the Fibonacci entry point*, Proceedings of
the AMS 142 (2014), 3771–3785, DOI
[10.1090/S0002-9939-2014-12269-6](https://doi.org/10.1090/S0002-9939-2014-12269-6).
Its original preprint is [arXiv:1212.6221v1](https://arxiv.org/abs/1212.6221v1).
Sanna's general Lucas predecessor is *On the divisibility of the rank of
appearance of a Lucas sequence*, IJNT 18 (2022), 2145–2156, DOI
[10.1142/S1793042122501093](https://doi.org/10.1142/S1793042122501093).

The 2026 source completes missing general Lucas cases and finite-form
evaluations. Its Theorem 1 also explains which asymptotic parts were
already available from Sanna's argument. Neither the Fibonacci density
statement nor this general counting theorem should be reproved or
presented as a new FIB-project result.

## The order of divisibility is material

For Fibonacci, with $z(p)$ the first zero index, specified-term divisibility
has the predicate $p\mid F_n\Longleftrightarrow z(p)\mid n$.
The density theorem instead counts $d\mid z(p)$ for fixed $d$.
These conditions have opposite divisibility directions. A density for
the infinite prime set in the latter does not by itself bound the finite
set of actual prime divisors of one $F_n$, its reciprocal prime mass, or
its divisor sum. A transport argument would have to preserve the actual
condition and justify its moving parameters and errors.

For the general seed $V_j=aF_{j+3}+bF_{j+4}$, the
[FIB theory's §191.1](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
already supplies the correct zero-set description: when nonempty, it is
one residue class $j\equiv t_v(p)\pmod{z(p)}$. In general
$t_v(p)$ is nonzero. The rank-density theorem does not locate that
seed-dependent residue or prove that different primes' residues are
jointly attained by the same $j$.

The Kummer–Chebotarev construction in FIB §§199–201 already uses
specified-root events for the actual source. Replacing those events by
rank density would lose the target $v'/v$ and its joint constraints.
This note keeps the latest general rank result available for reuse,
without claiming that it fills the unrestricted changing-seed estimate
or the same-candidate divisor-weight budget in §233.5.
